/*
 * mta_bypass.sys — Kernel driver for FairPlay callback neutralization
 * Designed for manual mapping via kdmapper
 *
 * - No IoCreateDevice (fake DriverObject from kdmapper)
 * - ExAllocatePoolWithTag (compat all Windows versions)
 * - Patches callback bodies with RET (PatchGuard safe)
 * - Runs synchronously in DriverEntry (no worker thread — avoids use-after-free)
 */

#include <ntddk.h>

/* ─── Forward declarations ─── */

NTSYSAPI NTSTATUS NTAPI ZwQuerySystemInformation(
    ULONG SystemInformationClass,
    PVOID SystemInformation,
    ULONG SystemInformationLength,
    PULONG ReturnLength
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

/* ─── Ntoskrnl base lookup (with retry) ─── */

static PVOID GetNtoskrnlBase(PULONG outSize)
{
    ULONG bufSize = 0;
    NTSTATUS status;

    ZwQuerySystemInformation(11, NULL, 0, &bufSize);
    if (!bufSize) return NULL;

    /* Add extra space in case modules load between calls */
    bufSize += 4096;

    PSYSTEM_MODULE_INFORMATION modInfo = (PSYSTEM_MODULE_INFORMATION)
        ExAllocatePoolWithTag(NonPagedPool, bufSize, POOL_TAG);
    if (!modInfo) return NULL;

    status = ZwQuerySystemInformation(11, modInfo, bufSize, &bufSize);
    if (!NT_SUCCESS(status)) {
        ExFreePoolWithTag(modInfo, POOL_TAG);
        return NULL;
    }

    if (modInfo->Count == 0) {
        ExFreePoolWithTag(modInfo, POOL_TAG);
        return NULL;
    }

    PVOID base = modInfo->Modules[0].ImageBase;
    if (outSize) *outSize = modInfo->Modules[0].ImageSize;
    ExFreePoolWithTag(modInfo, POOL_TAG);
    return base;
}

/* ─── Callback array finder (bounds-checked) ─── */

static PVOID* FindCallbackArray(PVOID exportAddr, ULONG scanRange,
                                 PVOID ntBase, ULONG ntSize)
{
    if (!exportAddr) return NULL;

    /* Clamp scan range to ntoskrnl image bounds */
    ULONG_PTR exportEnd = (ULONG_PTR)exportAddr + scanRange;
    ULONG_PTR imageEnd = (ULONG_PTR)ntBase + ntSize;
    if (exportEnd > imageEnd) {
        scanRange = (ULONG)(imageEnd - (ULONG_PTR)exportAddr);
    }
    if (scanRange < 7) return NULL;

    UCHAR* scan = (UCHAR*)exportAddr;

    __try {
        for (ULONG i = 0; i < scanRange - 7; i++) {
            if ((scan[i] == 0x48 || scan[i] == 0x4C) &&
                scan[i+1] == 0x8D &&
                (scan[i+2] & 0xC7) == 0x05) {

                LONG disp = *(LONG*)(&scan[i+3]);
                PVOID* array = (PVOID*)((ULONG_PTR)&scan[i+7] + disp);

                /* Validate array is within kernel space */
                if ((ULONG_PTR)array > 0xFFFF800000000000ULL) {
                    DbgPrint("[MtaBypass] Callback array at %p (export+0x%x)\n", array, i);
                    return array;
                }
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        DbgPrint("[MtaBypass] Exception in FindCallbackArray\n");
    }

    return NULL;
}

/*
 * PatchGuard-safe callback neutralization:
 * Patches callback function body with RET (0xC3) instead of zeroing array slots.
 * All memory access wrapped in SEH for safety.
 */
static ULONG PatchCallbacks(PVOID* callbackArray, ULONG maxSlots,
                             PVOID ntBase, ULONG ntSize)
{
    ULONG patched = 0;

    for (ULONG i = 0; i < maxSlots; i++) {
        PVOID slot = NULL;
        PVOID block = NULL;
        PVOID func = NULL;

        __try {
            slot = callbackArray[i];
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            break;
        }

        if (!slot) continue;

        /* Strip ref count bits from EX_CALLBACK fast reference */
        block = (PVOID)((ULONG_PTR)slot & ~0xF);

        __try {
            /* Function pointer at offset 0x8 in EX_CALLBACK_ROUTINE_BLOCK */
            func = *(PVOID*)((ULONG_PTR)block + 0x8);
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            continue;
        }

        if (!func) continue;

        /* Only patch third-party callbacks (outside ntoskrnl) */
        if ((ULONG_PTR)func >= (ULONG_PTR)ntBase &&
            (ULONG_PTR)func < (ULONG_PTR)ntBase + ntSize) {
            continue;
        }

        /* Patch the callback function with RET (0xC3) via MDL */
        PMDL mdl = IoAllocateMdl(func, 1, FALSE, FALSE, NULL);
        if (!mdl) continue;

        BOOLEAN locked = FALSE;
        PVOID mapped = NULL;

        __try {
            MmProbeAndLockPages(mdl, KernelMode, IoModifyAccess);
            locked = TRUE;
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            IoFreeMdl(mdl);
            continue;
        }

        mapped = MmMapLockedPagesSpecifyCache(
            mdl, KernelMode, MmNonCached, NULL, FALSE, NormalPagePriority);

        if (mapped) {
            __try {
                *(UCHAR*)mapped = 0xC3;  /* RET */
            } __except (EXCEPTION_EXECUTE_HANDLER) {
                /* write failed, skip */
            }
            MmUnmapLockedPages(mapped, mdl);
            patched++;
            DbgPrint("[MtaBypass] Patched slot %u, func=%p\n", i, func);
        }

        if (locked) {
            MmUnlockPages(mdl);
        }
        IoFreeMdl(mdl);
    }

    return patched;
}

static VOID NeutralizeFairplay(void)
{
    ULONG patched = 0;
    UNICODE_STRING name;
    PVOID ntBase = NULL;
    ULONG ntSize = 0;

    ntBase = GetNtoskrnlBase(&ntSize);
    if (!ntBase || !ntSize) {
        DbgPrint("[MtaBypass] Failed to get ntoskrnl base.\n");
        return;
    }

    DbgPrint("[MtaBypass] ntoskrnl base=%p size=0x%X\n", ntBase, ntSize);

    RtlInitUnicodeString(&name, L"PsSetLoadImageNotifyRoutine");
    PVOID addr = MmGetSystemRoutineAddress(&name);
    if (addr) {
        PVOID* arr = FindCallbackArray(addr, 0x100, ntBase, ntSize);
        if (arr) patched += PatchCallbacks(arr, MAX_CALLBACKS, ntBase, ntSize);
    }

    RtlInitUnicodeString(&name, L"PsSetCreateThreadNotifyRoutine");
    addr = MmGetSystemRoutineAddress(&name);
    if (addr) {
        PVOID* arr = FindCallbackArray(addr, 0x100, ntBase, ntSize);
        if (arr) patched += PatchCallbacks(arr, MAX_CALLBACKS, ntBase, ntSize);
    }

    RtlInitUnicodeString(&name, L"PsSetCreateProcessNotifyRoutine");
    addr = MmGetSystemRoutineAddress(&name);
    if (addr) {
        PVOID* arr = FindCallbackArray(addr, 0x100, ntBase, ntSize);
        if (arr) patched += PatchCallbacks(arr, MAX_CALLBACKS, ntBase, ntSize);
    }

    g_CallbacksPatched = patched;
    DbgPrint("[MtaBypass] Done. %u callbacks patched with RET.\n", patched);
}

/* ─── Driver Entry ─── */

NTSTATUS DriverEntry(PDRIVER_OBJECT DriverObject, PUNICODE_STRING RegistryPath)
{
    UNREFERENCED_PARAMETER(DriverObject);
    UNREFERENCED_PARAMETER(RegistryPath);

    /*
     * kdmapper passes fake DriverObject — do NOT use it.
     * Run synchronously — no worker thread.
     * Worker thread would execute from mapped memory that kdmapper frees
     * after DriverEntry returns = use-after-free BSOD.
     */

    DbgPrint("[MtaBypass] DriverEntry start.\n");
    NeutralizeFairplay();
    DbgPrint("[MtaBypass] DriverEntry done. Patched %u callbacks.\n", g_CallbacksPatched);

    return STATUS_SUCCESS;
}
