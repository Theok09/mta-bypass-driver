/*
 * mta_bypass.sys — Kernel driver for FairPlay callback neutralization
 * Designed for manual mapping via kdmapper
 *
 * - No IoCreateDevice (fake DriverObject from kdmapper)
 * - No IOCTL (no device object)
 * - ExAllocatePoolWithTag instead of ExAllocatePool2 (compat)
 * - Patches callback bodies with RET instead of zeroing slots (PatchGuard safe)
 * - PsCreateSystemThread for async work, DriverEntry returns fast
 */

#include <ntddk.h>

/* ─── Forward declarations for undocumented APIs ─── */

NTSYSAPI NTSTATUS NTAPI ZwQuerySystemInformation(
    ULONG SystemInformationClass,
    PVOID SystemInformation,
    ULONG SystemInformationLength,
    PULONG ReturnLength
);

NTKERNELAPI NTSTATUS PsLookupProcessByProcessId(
    HANDLE ProcessId,
    PEPROCESS *Process
);

/* ─── Types ─── */

typedef struct _SYSTEM_MODULE_ENTRY {
    HANDLE Section;
    PVOID  MappedBase;
    PVOID  ImageBase;
    ULONG  ImageSize;
    ULONG  Flags;
    USHORT LoadOrderIndex;
    USHORT InitOrderIndex;
    USHORT LoadCount;
    USHORT OffsetToFileName;
    UCHAR  FullPathName[256];
} SYSTEM_MODULE_ENTRY, *PSYSTEM_MODULE_ENTRY;

typedef struct _SYSTEM_MODULE_INFORMATION {
    ULONG                Count;
    SYSTEM_MODULE_ENTRY  Modules[1];
} SYSTEM_MODULE_INFORMATION, *PSYSTEM_MODULE_INFORMATION;

/* ─── Globals ─── */

static ULONG g_CallbacksPatched = 0;

#define MAX_CALLBACKS 64
#define POOL_TAG 'bypM'

/* ─── Ntoskrnl base lookup ─── */

static PVOID GetNtoskrnlBase(PULONG outSize)
{
    ULONG bufSize = 0;

    ZwQuerySystemInformation(11, NULL, 0, &bufSize);
    if (!bufSize) return NULL;

    PSYSTEM_MODULE_INFORMATION modInfo = (PSYSTEM_MODULE_INFORMATION)
        ExAllocatePoolWithTag(NonPagedPool, bufSize, POOL_TAG);
    if (!modInfo) return NULL;

    NTSTATUS status = ZwQuerySystemInformation(11, modInfo, bufSize, &bufSize);
    if (!NT_SUCCESS(status)) {
        ExFreePoolWithTag(modInfo, POOL_TAG);
        return NULL;
    }

    PVOID base = modInfo->Modules[0].ImageBase;
    if (outSize) *outSize = modInfo->Modules[0].ImageSize;
    ExFreePoolWithTag(modInfo, POOL_TAG);
    return base;
}

/* ─── Callback array finder ─── */

static PVOID* FindCallbackArray(PVOID exportAddr, ULONG scanRange)
{
    if (!exportAddr || !MmIsAddressValid(exportAddr)) return NULL;

    UCHAR* scan = (UCHAR*)exportAddr;
    for (ULONG i = 0; i < scanRange - 7; i++) {
        if ((scan[i] == 0x48 || scan[i] == 0x4C) &&
            scan[i+1] == 0x8D &&
            (scan[i+2] & 0xC7) == 0x05) {

            LONG disp = *(LONG*)(&scan[i+3]);
            PVOID* array = (PVOID*)((ULONG_PTR)&scan[i+7] + disp);

            if (MmIsAddressValid(array)) {
                DbgPrint("[MtaBypass] Callback array at %p (export+0x%x)\n", array, i);
                return array;
            }
        }
    }
    return NULL;
}

/*
 * PatchGuard-safe callback neutralization:
 * Instead of zeroing callback array slots (PatchGuard monitors these),
 * we patch the callback function body with a RET instruction.
 * This leaves the array intact but makes the callback a no-op.
 */
static ULONG PatchCallbacks(PVOID* callbackArray, ULONG maxSlots)
{
    ULONG patched = 0;
    PVOID ntBase = NULL;
    ULONG ntSize = 0;

    ntBase = GetNtoskrnlBase(&ntSize);
    if (!ntBase) return 0;

    for (ULONG i = 0; i < maxSlots; i++) {
        PVOID slot = callbackArray[i];
        if (!slot) continue;

        PVOID block = (PVOID)((ULONG_PTR)slot & ~0xF);
        if (!MmIsAddressValid(block)) continue;

        PVOID func = *(PVOID*)((ULONG_PTR)block + 0x8);
        if (!MmIsAddressValid(func)) continue;

        /* Only patch third-party callbacks (outside ntoskrnl) */
        if ((ULONG_PTR)func >= (ULONG_PTR)ntBase &&
            (ULONG_PTR)func < (ULONG_PTR)ntBase + ntSize) {
            continue;
        }

        /*
         * Patch the callback function with RET (0xC3).
         * We need to make the page writable first.
         */
        PMDL mdl = IoAllocateMdl(func, 1, FALSE, FALSE, NULL);
        if (!mdl) continue;

        MmProbeAndLockPages(mdl, KernelMode, IoModifyAccess);
        PVOID mapped = MmMapLockedPagesSpecifyCache(
            mdl, KernelMode, MmNonCached, NULL, FALSE, NormalPagePriority);

        if (mapped) {
            *(UCHAR*)mapped = 0xC3;  /* RET */
            MmUnmapLockedPages(mapped, mdl);
            patched++;
            DbgPrint("[MtaBypass] Patched callback slot %u, func=%p with RET\n", i, func);
        }

        MmUnlockPages(mdl);
        IoFreeMdl(mdl);
    }

    return patched;
}

static VOID NeutralizeFairplay(void)
{
    ULONG patched = 0;
    UNICODE_STRING name;

    RtlInitUnicodeString(&name, L"PsSetLoadImageNotifyRoutine");
    PVOID addr = MmGetSystemRoutineAddress(&name);
    if (addr) {
        PVOID* arr = FindCallbackArray(addr, 0x100);
        if (arr) patched += PatchCallbacks(arr, MAX_CALLBACKS);
    }

    RtlInitUnicodeString(&name, L"PsSetCreateThreadNotifyRoutine");
    addr = MmGetSystemRoutineAddress(&name);
    if (addr) {
        PVOID* arr = FindCallbackArray(addr, 0x100);
        if (arr) patched += PatchCallbacks(arr, MAX_CALLBACKS);
    }

    RtlInitUnicodeString(&name, L"PsSetCreateProcessNotifyRoutine");
    addr = MmGetSystemRoutineAddress(&name);
    if (addr) {
        PVOID* arr = FindCallbackArray(addr, 0x100);
        if (arr) patched += PatchCallbacks(arr, MAX_CALLBACKS);
    }

    g_CallbacksPatched = patched;
    DbgPrint("[MtaBypass] Neutralization done. %u callbacks patched with RET.\n", patched);
}

/* ─── Worker thread ─── */

static VOID WorkerThread(PVOID context)
{
    UNREFERENCED_PARAMETER(context);

    DbgPrint("[MtaBypass] Worker thread started.\n");

    NeutralizeFairplay();

    DbgPrint("[MtaBypass] Worker thread done. Exiting.\n");
    PsTerminateSystemThread(STATUS_SUCCESS);
}

/* ─── Driver Entry ─── */

NTSTATUS DriverEntry(PDRIVER_OBJECT DriverObject, PUNICODE_STRING RegistryPath)
{
    UNREFERENCED_PARAMETER(DriverObject);
    UNREFERENCED_PARAMETER(RegistryPath);

    /*
     * kdmapper passes fake DriverObject. Do NOT use it.
     * Spawn a system thread to do the real work and return immediately.
     */

    HANDLE threadHandle = NULL;
    NTSTATUS status = PsCreateSystemThread(
        &threadHandle,
        THREAD_ALL_ACCESS,
        NULL,
        NULL,
        NULL,
        WorkerThread,
        NULL
    );

    if (NT_SUCCESS(status)) {
        ZwClose(threadHandle);
        DbgPrint("[MtaBypass] Worker thread spawned. Returning from DriverEntry.\n");
    } else {
        DbgPrint("[MtaBypass] Failed to create worker thread: 0x%X. Running inline.\n", status);
        NeutralizeFairplay();
    }

    return STATUS_SUCCESS;
}
