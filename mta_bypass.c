/*
 * mta_bypass.sys — Kernel driver for FairPlay callback neutralization + DLL injection
 * Load via kdmapper or similar manual mapper
 * Build with WDK on Windows
 */

#include <ntddk.h>
#include <ntstrsafe.h>

#define DEVICE_NAME     L"\\Device\\MtaBypass"
#define SYMLINK_NAME    L"\\DosDevices\\MtaBypass"

#define IOCTL_NEUTRALIZE_FAIRPLAY  CTL_CODE(FILE_DEVICE_UNKNOWN, 0x800, METHOD_BUFFERED, FILE_ANY_ACCESS)
#define IOCTL_INJECT_DLL           CTL_CODE(FILE_DEVICE_UNKNOWN, 0x801, METHOD_BUFFERED, FILE_ANY_ACCESS)
#define IOCTL_STATUS               CTL_CODE(FILE_DEVICE_UNKNOWN, 0x802, METHOD_BUFFERED, FILE_ANY_ACCESS)

/* ─── Undocumented APC definitions ─── */

typedef enum _KAPC_ENVIRONMENT {
    OriginalApcEnvironment,
    AttachedApcEnvironment,
    CurrentApcEnvironment,
    InsertApcEnvironment
} KAPC_ENVIRONMENT;

typedef VOID (NTAPI *PKNORMAL_ROUTINE_T)(
    PVOID NormalContext,
    PVOID SystemArgument1,
    PVOID SystemArgument2
);

typedef VOID (NTAPI *PKKERNEL_ROUTINE)(
    struct _KAPC *Apc,
    PKNORMAL_ROUTINE_T *NormalRoutine,
    PVOID *NormalContext,
    PVOID *SystemArgument1,
    PVOID *SystemArgument2
);

typedef VOID (NTAPI *PKRUNDOWN_ROUTINE)(struct _KAPC *Apc);

NTKERNELAPI VOID KeInitializeApc(
    PRKAPC Apc,
    PRKTHREAD Thread,
    KAPC_ENVIRONMENT Environment,
    PKKERNEL_ROUTINE KernelRoutine,
    PKRUNDOWN_ROUTINE RundownRoutine,
    PKNORMAL_ROUTINE_T NormalRoutine,
    KPROCESSOR_MODE ProcessorMode,
    PVOID NormalContext
);

NTKERNELAPI BOOLEAN KeInsertQueueApc(
    PRKAPC Apc,
    PVOID SystemArgument1,
    PVOID SystemArgument2,
    KPRIORITY Increment
);

NTKERNELAPI BOOLEAN KeAlertThread(
    PRKTHREAD Thread,
    KPROCESSOR_MODE AlertMode
);

NTKERNELAPI NTSTATUS PsLookupProcessByProcessId(
    HANDLE ProcessId,
    PEPROCESS *Process
);

NTKERNELAPI PETHREAD PsGetNextProcessThread(
    PEPROCESS Process,
    PETHREAD Thread
);

NTSYSAPI NTSTATUS NTAPI ZwAllocateVirtualMemory(
    HANDLE ProcessHandle,
    PVOID *BaseAddress,
    ULONG_PTR ZeroBits,
    PSIZE_T RegionSize,
    ULONG AllocationType,
    ULONG Protect
);

NTSYSAPI NTSTATUS NTAPI ZwQuerySystemInformation(
    ULONG SystemInformationClass,
    PVOID SystemInformation,
    ULONG SystemInformationLength,
    PULONG ReturnLength
);

/* ─── Types ─── */

typedef NTSTATUS (*PsSetLoadImageNotifyRoutine_t)(PLOAD_IMAGE_NOTIFY_ROUTINE);
typedef NTSTATUS (*PsSetCreateThreadNotifyRoutine_t)(PCREATE_THREAD_NOTIFY_ROUTINE);

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

typedef struct _INJECT_REQUEST {
    ULONG  ProcessId;
    WCHAR  DllPath[260];
} INJECT_REQUEST, *PINJECT_REQUEST;

typedef struct _STATUS_RESPONSE {
    ULONG  FairplayNeutralized;
    ULONG  CallbacksRemoved;
    ULONG  InjectionsPerformed;
} STATUS_RESPONSE, *PSTATUS_RESPONSE;


/* ─── Globals ─── */

static PDEVICE_OBJECT  g_DeviceObject   = NULL;
static ULONG           g_Neutralized    = 0;
static ULONG           g_CallbacksRemoved = 0;
static ULONG           g_Injections     = 0;

/* ─── Callback array walking ─── */

/*
 * PspLoadImageNotifyRoutine and PspCreateThreadNotifyRoutine are kernel arrays
 * of EX_CALLBACK_ROUTINE_BLOCK pointers. We locate them by scanning ntoskrnl
 * near the Ps*NotifyRoutine exports.
 *
 * Each slot: pointer with low bits used as ref count.
 * Real pointer = slot & ~0xF
 * The block contains the callback function pointer at offset 0x8.
 */

#define MAX_CALLBACKS 64

static PVOID FindPatternInRange(PVOID base, ULONG size, const UCHAR* pattern, const CHAR* mask, ULONG patLen)
{
    UCHAR* start = (UCHAR*)base;
    for (ULONG i = 0; i <= size - patLen; i++) {
        BOOLEAN found = TRUE;
        for (ULONG j = 0; j < patLen; j++) {
            if (mask[j] == 'x' && start[i + j] != pattern[j]) {
                found = FALSE;
                break;
            }
        }
        if (found) return &start[i];
    }
    return NULL;
}

static PVOID GetNtoskrnlBase(PULONG outSize)
{
    NTSTATUS status;
    ULONG bufSize = 0;

    ZwQuerySystemInformation(11 /* SystemModuleInformation */, NULL, 0, &bufSize);
    if (!bufSize) return NULL;

    PSYSTEM_MODULE_INFORMATION modInfo = (PSYSTEM_MODULE_INFORMATION)
        ExAllocatePool2(POOL_FLAG_NON_PAGED, bufSize, 'bypM');
    if (!modInfo) return NULL;

    status = ZwQuerySystemInformation(11, modInfo, bufSize, &bufSize);
    if (!NT_SUCCESS(status)) {
        ExFreePoolWithTag(modInfo, 'bypM');
        return NULL;
    }

    PVOID base = modInfo->Modules[0].ImageBase;
    if (outSize) *outSize = modInfo->Modules[0].ImageSize;
    ExFreePoolWithTag(modInfo, 'bypM');
    return base;
}

/* Walk the callback array at a given address, unregister FairPlay entries */
static ULONG WalkAndNeutralize(PVOID* callbackArray, ULONG maxSlots,
                                BOOLEAN isLoadImage)
{
    ULONG removed = 0;

    for (ULONG i = 0; i < maxSlots; i++) {
        PVOID slot = callbackArray[i];
        if (!slot) continue;

        /* Strip ref count bits */
        PVOID block = (PVOID)((ULONG_PTR)slot & ~0xF);
        if (!MmIsAddressValid(block)) continue;

        /* Function pointer at offset 0x8 in the block */
        PVOID func = *(PVOID*)((ULONG_PTR)block + 0x8);
        if (!MmIsAddressValid(func)) continue;

        /* Check if this callback belongs to FairplayKD range */
        /* We null the slot to deregister */
        ULONG modSize = 0;
        /* Simple heuristic: if the callback is outside ntoskrnl, it's a third-party driver */
        PVOID ntBase = GetNtoskrnlBase(&modSize);
        if (ntBase && ((ULONG_PTR)func < (ULONG_PTR)ntBase ||
                       (ULONG_PTR)func >= (ULONG_PTR)ntBase + modSize)) {
            /* Third-party callback — neutralize by zeroing the slot */
            InterlockedExchangePointer(&callbackArray[i], NULL);
            removed++;
            DbgPrint("[MtaBypass] Neutralized callback slot %u, func=%p\n", i, func);
        }
    }

    return removed;
}

/*
 * Locate PspLoadImageNotifyRoutine array by scanning near PsSetLoadImageNotifyRoutine.
 * The function references the array via LEA instruction with RIP-relative addressing.
 * Pattern: 4C 8D 35 xx xx xx xx (lea r14, [rip+disp32])  — varies by build
 * We use a more generic approach: scan for LEA with register + disp32
 */
static PVOID* FindCallbackArray(PVOID exportAddr, ULONG scanRange)
{
    if (!exportAddr || !MmIsAddressValid(exportAddr)) return NULL;

    UCHAR* scan = (UCHAR*)exportAddr;
    for (ULONG i = 0; i < scanRange - 7; i++) {
        /* Look for LEA r??, [rip + disp32]:  48/4C 8D xx (xx xx xx xx) */
        if ((scan[i] == 0x48 || scan[i] == 0x4C) &&
            scan[i+1] == 0x8D &&
            (scan[i+2] & 0xC7) == 0x05) {  /* ModRM: mod=00, r/m=101 (RIP-relative) */

            LONG disp = *(LONG*)(&scan[i+3]);
            PVOID* array = (PVOID*)((ULONG_PTR)&scan[i+7] + disp);

            if (MmIsAddressValid(array)) {
                DbgPrint("[MtaBypass] Found callback array at %p (from export+0x%x)\n",
                         array, i);
                return array;
            }
        }
    }

    return NULL;
}

static NTSTATUS NeutralizeFairplay(void)
{
    ULONG removed = 0;
    UNICODE_STRING name;

    /* LoadImage callbacks */
    RtlInitUnicodeString(&name, L"PsSetLoadImageNotifyRoutine");
    PVOID psSetLoadImage = MmGetSystemRoutineAddress(&name);
    if (psSetLoadImage) {
        PVOID* arr = FindCallbackArray(psSetLoadImage, 0x100);
        if (arr) {
            removed += WalkAndNeutralize(arr, MAX_CALLBACKS, TRUE);
        }
    }

    /* CreateThread callbacks */
    RtlInitUnicodeString(&name, L"PsSetCreateThreadNotifyRoutine");
    PVOID psSetCreateThread = MmGetSystemRoutineAddress(&name);
    if (psSetCreateThread) {
        PVOID* arr = FindCallbackArray(psSetCreateThread, 0x100);
        if (arr) {
            removed += WalkAndNeutralize(arr, MAX_CALLBACKS, FALSE);
        }
    }

    /* CreateProcess callbacks */
    RtlInitUnicodeString(&name, L"PsSetCreateProcessNotifyRoutine");
    PVOID psSetCreateProcess = MmGetSystemRoutineAddress(&name);
    if (psSetCreateProcess) {
        PVOID* arr = FindCallbackArray(psSetCreateProcess, 0x100);
        if (arr) {
            removed += WalkAndNeutralize(arr, MAX_CALLBACKS, FALSE);
        }
    }

    g_CallbacksRemoved += removed;
    g_Neutralized = 1;

    DbgPrint("[MtaBypass] Neutralization complete. %u callbacks removed.\n", removed);
    return STATUS_SUCCESS;
}

/* ─── Manual PE Mapper + APC Injection ─── */

typedef struct _IMAGE_DOS_HEADER_PARTIAL {
    USHORT e_magic;
    UCHAR  pad[58];
    LONG   e_lfanew;
} IMAGE_DOS_HEADER_PARTIAL;

typedef struct _PE_HEADERS {
    ULONG  Signature;
    /* COFF header */
    USHORT Machine;
    USHORT NumberOfSections;
    ULONG  TimeDateStamp;
    ULONG  PointerToSymbolTable;
    ULONG  NumberOfSymbols;
    USHORT SizeOfOptionalHeader;
    USHORT Characteristics;
} PE_HEADERS;

static VOID NTAPI ApcKernelCleanup(
    PKAPC Apc,
    PKNORMAL_ROUTINE_T *NormalRoutine,
    PVOID *NormalContext,
    PVOID *SystemArgument1,
    PVOID *SystemArgument2)
{
    UNREFERENCED_PARAMETER(NormalRoutine);
    UNREFERENCED_PARAMETER(NormalContext);
    UNREFERENCED_PARAMETER(SystemArgument1);
    UNREFERENCED_PARAMETER(SystemArgument2);
    ExFreePoolWithTag(Apc, 'bypM');
}

static NTSTATUS InjectDllViaApc(ULONG processId, PCWSTR dllPath)
{
    NTSTATUS status;
    PEPROCESS process = NULL;

    status = PsLookupProcessByProcessId((HANDLE)(ULONG_PTR)processId, &process);
    if (!NT_SUCCESS(status)) {
        DbgPrint("[MtaBypass] PsLookupProcessByProcessId failed: 0x%X\n", status);
        return status;
    }

    KAPC_STATE apcState;

    KeStackAttachProcess(process, &apcState);

    SIZE_T pathLen = (wcslen(dllPath) + 1) * sizeof(WCHAR);
    SIZE_T allocSize = pathLen;
    PVOID remoteBuf = NULL;

    status = ZwAllocateVirtualMemory(ZwCurrentProcess(), &remoteBuf, 0,
                                     &allocSize, MEM_COMMIT | MEM_RESERVE,
                                     PAGE_READWRITE);
    if (!NT_SUCCESS(status)) {
        KeUnstackDetachProcess(&apcState);
        ObDereferenceObject(process);
        DbgPrint("[MtaBypass] ZwAllocateVirtualMemory failed: 0x%X\n", status);
        return status;
    }

    __try {
        RtlCopyMemory(remoteBuf, dllPath, pathLen);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        KeUnstackDetachProcess(&apcState);
        ObDereferenceObject(process);
        return STATUS_ACCESS_VIOLATION;
    }

    SIZE_T ustrAlloc = sizeof(UNICODE_STRING);
    PVOID ustrBuf = NULL;

    status = ZwAllocateVirtualMemory(ZwCurrentProcess(), &ustrBuf, 0,
                                     &ustrAlloc, MEM_COMMIT | MEM_RESERVE,
                                     PAGE_READWRITE);
    if (NT_SUCCESS(status)) {
        __try {
            PUNICODE_STRING pUstr = (PUNICODE_STRING)ustrBuf;
            pUstr->Length = (USHORT)(pathLen - sizeof(WCHAR));
            pUstr->MaximumLength = (USHORT)pathLen;
            pUstr->Buffer = (PWCH)remoteBuf;
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            status = STATUS_ACCESS_VIOLATION;
        }
    }

    KeUnstackDetachProcess(&apcState);

    if (!NT_SUCCESS(status)) {
        ObDereferenceObject(process);
        return status;
    }

    UNICODE_STRING funcName;
    RtlInitUnicodeString(&funcName, L"LdrLoadDll");
    PVOID ldrLoadDll = MmGetSystemRoutineAddress(&funcName);

    PETHREAD thread = PsGetNextProcessThread(process, NULL);
    if (!thread) {
        ObDereferenceObject(process);
        DbgPrint("[MtaBypass] No thread found in target process\n");
        return STATUS_NOT_FOUND;
    }

    PKAPC apc = (PKAPC)ExAllocatePool2(POOL_FLAG_NON_PAGED, sizeof(KAPC), 'bypM');
    if (!apc) {
        ObDereferenceObject(process);
        return STATUS_INSUFFICIENT_RESOURCES;
    }

    KeInitializeApc(apc,
                    (PRKTHREAD)thread,
                    OriginalApcEnvironment,
                    ApcKernelCleanup,
                    NULL,
                    (PKNORMAL_ROUTINE_T)ldrLoadDll,
                    UserMode,
                    ustrBuf);

    if (!KeInsertQueueApc(apc, NULL, NULL, IO_NO_INCREMENT)) {
        ExFreePoolWithTag(apc, 'bypM');
        ObDereferenceObject(process);
        DbgPrint("[MtaBypass] KeInsertQueueApc failed\n");
        return STATUS_UNSUCCESSFUL;
    }

    KeAlertThread((PRKTHREAD)thread, UserMode);

    g_Injections++;
    ObDereferenceObject(process);
    DbgPrint("[MtaBypass] APC queued for PID %u, DLL: %ws\n", processId, dllPath);
    return STATUS_SUCCESS;
}

/* ─── IOCTL Dispatch ─── */

static NTSTATUS DeviceControl(PDEVICE_OBJECT DeviceObject, PIRP Irp)
{
    UNREFERENCED_PARAMETER(DeviceObject);

    PIO_STACK_LOCATION stack = IoGetCurrentIrpStackLocation(Irp);
    NTSTATUS status = STATUS_SUCCESS;
    ULONG bytesReturned = 0;

    switch (stack->Parameters.DeviceIoControl.IoControlCode) {

    case IOCTL_NEUTRALIZE_FAIRPLAY:
        status = NeutralizeFairplay();
        break;

    case IOCTL_INJECT_DLL: {
        if (stack->Parameters.DeviceIoControl.InputBufferLength < sizeof(INJECT_REQUEST)) {
            status = STATUS_BUFFER_TOO_SMALL;
            break;
        }
        PINJECT_REQUEST req = (PINJECT_REQUEST)Irp->AssociatedIrp.SystemBuffer;
        status = InjectDllViaApc(req->ProcessId, req->DllPath);
        break;
    }

    case IOCTL_STATUS: {
        if (stack->Parameters.DeviceIoControl.OutputBufferLength < sizeof(STATUS_RESPONSE)) {
            status = STATUS_BUFFER_TOO_SMALL;
            break;
        }
        PSTATUS_RESPONSE resp = (PSTATUS_RESPONSE)Irp->AssociatedIrp.SystemBuffer;
        resp->FairplayNeutralized = g_Neutralized;
        resp->CallbacksRemoved = g_CallbacksRemoved;
        resp->InjectionsPerformed = g_Injections;
        bytesReturned = sizeof(STATUS_RESPONSE);
        break;
    }

    default:
        status = STATUS_INVALID_DEVICE_REQUEST;
        break;
    }

    Irp->IoStatus.Status = status;
    Irp->IoStatus.Information = bytesReturned;
    IoCompleteRequest(Irp, IO_NO_INCREMENT);
    return status;
}

static NTSTATUS DeviceCreateClose(PDEVICE_OBJECT DeviceObject, PIRP Irp)
{
    UNREFERENCED_PARAMETER(DeviceObject);
    Irp->IoStatus.Status = STATUS_SUCCESS;
    Irp->IoStatus.Information = 0;
    IoCompleteRequest(Irp, IO_NO_INCREMENT);
    return STATUS_SUCCESS;
}

/* ─── Driver Entry / Unload ─── */

static VOID DriverUnload(PDRIVER_OBJECT DriverObject)
{
    UNICODE_STRING symlink;
    RtlInitUnicodeString(&symlink, SYMLINK_NAME);
    IoDeleteSymbolicLink(&symlink);
    if (g_DeviceObject)
        IoDeleteDevice(g_DeviceObject);
    DbgPrint("[MtaBypass] Driver unloaded.\n");
}

NTSTATUS DriverEntry(PDRIVER_OBJECT DriverObject, PUNICODE_STRING RegistryPath)
{
    UNREFERENCED_PARAMETER(RegistryPath);

    NTSTATUS status;
    UNICODE_STRING devName, symlink;

    RtlInitUnicodeString(&devName, DEVICE_NAME);
    RtlInitUnicodeString(&symlink, SYMLINK_NAME);

    status = IoCreateDevice(DriverObject, 0, &devName, FILE_DEVICE_UNKNOWN,
                            FILE_DEVICE_SECURE_OPEN, FALSE, &g_DeviceObject);
    if (!NT_SUCCESS(status)) return status;

    status = IoCreateSymbolicLink(&symlink, &devName);
    if (!NT_SUCCESS(status)) {
        IoDeleteDevice(g_DeviceObject);
        return status;
    }

    DriverObject->MajorFunction[IRP_MJ_CREATE]         = DeviceCreateClose;
    DriverObject->MajorFunction[IRP_MJ_CLOSE]          = DeviceCreateClose;
    DriverObject->MajorFunction[IRP_MJ_DEVICE_CONTROL] = DeviceControl;
    DriverObject->DriverUnload                          = DriverUnload;

    DbgPrint("[MtaBypass] Driver loaded. Device: %wZ\n", &devName);
    return STATUS_SUCCESS;
}
