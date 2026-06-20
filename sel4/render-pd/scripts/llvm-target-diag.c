// llvm-target-diag.c — MEASURE + DRIVE the LLVM JIT target-registration lever.
//
// The render-PD's wall (WIRING.md): vkCreateDevice faults inside
// `lp_build_create_jit_compiler_for_module` at a NULL-vtable virtual call —
// `EngineBuilder::selectTarget()` returning NULL. selectTarget computes a triple
// (`getProcessTriple()` = LLVM_HOST_TRIPLE = aarch64-unknown-linux-musl in this
// cross build) and asks `TargetRegistry::lookupTarget` for a matching Target. If
// the AArch64 target was never *registered* (LLVMInitializeAArch64Target & friends
// not called) the lookup returns NULL → selectTarget NULL → the fault.
//
// gallivm DOES call `InitializeNativeTarget()` from `lp_set_target_options`
// (lp_bld_misc.cpp), but that path's registration is what we are measuring. This
// shim drives the registration EXPLICITLY (idempotent — re-registering a target is
// a no-op in LLVM's TargetRegistry) and PRINTS what the registry resolves, BEFORE
// the driver calls vkCreateDevice, so the boot serial tells us exactly whether the
// triple lookup now succeeds. Touch only render-pd/.
//
// The LLVM-C entry points are plain C-linkage symbols in the linked static LLVM
// 20.1.8 (verified present: libLLVMAArch64Info/CodeGen/Desc + libLLVMTarget). We
// forward-declare them here — no LLVM headers needed in the render-PD build.

#include <stddef.h>

extern int   puts(const char *s);
extern int   printf(const char *fmt, ...);

// LLVM-C target registration (TargetInfo/Target/TargetMC/AsmPrinter for AArch64).
// These are the expansions of InitializeNativeTarget()/...AsmPrinter() for this
// cross LLVM (LLVM_NATIVE_TARGET = LLVMInitializeAArch64Target, per llvm-config.h).
extern void LLVMInitializeAArch64TargetInfo(void);
extern void LLVMInitializeAArch64Target(void);
extern void LLVMInitializeAArch64TargetMC(void);
extern void LLVMInitializeAArch64AsmPrinter(void);
extern void LLVMInitializeAArch64AsmParser(void);
extern void LLVMInitializeAArch64Disassembler(void);

// LLVM-C target-registry queries (libLLVMTarget / TargetMachineC.cpp).
typedef void *LLVMTargetRef;
typedef int   LLVMBool;
extern char         *LLVMGetDefaultTargetTriple(void);
extern LLVMBool      LLVMGetTargetFromTriple(const char *Triple, LLVMTargetRef *T, char **ErrorMessage);
extern LLVMTargetRef LLVMGetFirstTarget(void);
extern LLVMTargetRef LLVMGetNextTarget(LLVMTargetRef T);
extern const char   *LLVMGetTargetName(LLVMTargetRef T);
extern const char   *LLVMGetTargetDescription(LLVMTargetRef T);
extern LLVMBool      LLVMTargetHasJIT(LLVMTargetRef T);

// LLVM-C MCJIT engine creation — the SAME path gallivm's
// lp_build_create_jit_compiler_for_module drives (EngineBuilder -> selectTarget ->
// MCJIT::createJIT). We replicate it on a fresh empty module to capture the ERROR
// STRING create() produces (gallivm dereferences the NULL engine before reading
// its own *OutError, so the boot serial never showed it). LLVMExecutionEngineRef +
// LLVMModuleRef are opaque pointers in the C ABI.
typedef void *LLVMExecutionEngineRef;
typedef void *LLVMModuleRef;
extern void     LLVMLinkInMCJIT(void);
extern LLVMModuleRef LLVMModuleCreateWithName(const char *ModuleID);
extern void     LLVMSetTarget(LLVMModuleRef M, const char *Triple);
extern LLVMBool LLVMCreateMCJITCompilerForModule(LLVMExecutionEngineRef *OutJIT,
                                                 LLVMModuleRef M, void *Options,
                                                 size_t SizeOfOptions, char **OutError);
extern LLVMBool LLVMCreateExecutionEngineForModule(LLVMExecutionEngineRef *OutEE,
                                                   LLVMModuleRef M, char **OutError);

// Drive + measure the JIT target registration. Returns 0 if a target resolves for
// the process/default triple (i.e. selectTarget should now find one), nonzero if
// the registry is still empty / the triple does not resolve.
int dregg_llvm_target_diag(void) {
    puts("[llvm-diag] --- LLVM JIT target registration lever ---");

    // (1) DRIVE: register the AArch64 target explicitly. Idempotent: LLVM's
    //     RegisterTarget guards against double-registration. This guarantees the
    //     codegen/asmprinter/MC are in the registry regardless of whether
    //     gallivm's InitializeNativeTarget ran for the right arch.
    LLVMInitializeAArch64TargetInfo();
    LLVMInitializeAArch64Target();
    LLVMInitializeAArch64TargetMC();
    LLVMInitializeAArch64AsmPrinter();
    LLVMInitializeAArch64AsmParser();
    LLVMInitializeAArch64Disassembler();
    puts("[llvm-diag] explicit LLVMInitializeAArch64{TargetInfo,Target,TargetMC,AsmPrinter,AsmParser,Disassembler} done");

    // (2) MEASURE: what triple does this cross LLVM compute, and does it resolve?
    char *triple = LLVMGetDefaultTargetTriple();
    printf("[llvm-diag] LLVMGetDefaultTargetTriple() = \"%s\"\n", triple ? triple : "(null)");

    // (3) Enumerate the registered targets (so we SEE whether AArch64 is in).
    int ntargets = 0;
    for (LLVMTargetRef t = LLVMGetFirstTarget(); t; t = LLVMGetNextTarget(t)) {
        printf("[llvm-diag]   registered target[%d]: %-12s hasJIT=%d  (%s)\n",
               ntargets,
               LLVMGetTargetName(t),
               (int) LLVMTargetHasJIT(t),
               LLVMGetTargetDescription(t));
        ntargets++;
    }
    printf("[llvm-diag] %d target(s) registered\n", ntargets);

    // (4) The exact query selectTarget makes: lookupTarget(processTriple).
    int ok = 0;
    if (triple) {
        LLVMTargetRef T = NULL;
        char *err = NULL;
        if (LLVMGetTargetFromTriple(triple, &T, &err) == 0 && T) {
            printf("[llvm-diag] lookupTarget(\"%s\") => \"%s\" hasJIT=%d  ✓\n",
                   triple, LLVMGetTargetName(T), (int) LLVMTargetHasJIT(T));
            ok = 1;
        } else {
            printf("[llvm-diag] lookupTarget(\"%s\") FAILED: %s\n",
                   triple, err ? err : "(no error string)");
        }
    }

    if (!ok && ntargets > 0) {
        // The triple did not resolve but a target IS registered — a triple-string
        // mismatch, not a missing registration. Report it as the precise wall.
        puts("[llvm-diag] WALL: a target is registered but the process triple does "
             "not resolve to it (triple-string mismatch).");
    }

    // (5) REPLICATE gallivm's failing call: build an MCJIT engine for an empty
    //     module and PRINT the error string. gallivm's create() returned NULL and
    //     it then dereferenced the NULL engine (JIT->setObjectCache) before reading
    //     *OutError — so the real reason never reached the serial. Here we read it.
    LLVMLinkInMCJIT(); // idempotent: sets ExecutionEngine::MCJITCtor if unset
    LLVMModuleRef m = LLVMModuleCreateWithName("dregg_jit_probe");
    if (m) {
        // Match gallivm: leave the module triple EMPTY first (selectTarget then
        // falls back to getProcessTriple) — this is EXACTLY gallivm's situation.
        LLVMExecutionEngineRef ee = NULL;
        char *err = NULL;
        if (LLVMCreateMCJITCompilerForModule(&ee, m, NULL, 0, &err) == 0 && ee) {
            puts("[llvm-diag] MCJIT engine CREATED for empty module (no triple) ✓ — "
                 "the JIT init path is sound; gallivm's wall is elsewhere.");
        } else {
            printf("[llvm-diag] MCJIT create FAILED (empty-triple module): %s\n",
                   err ? err : "(NULL error string — create returned NULL with no message)");
            // Retry with the triple set explicitly on a fresh module — the named
            // lever (b): does forcing the triple onto the module make create succeed?
            LLVMModuleRef m2 = LLVMModuleCreateWithName("dregg_jit_probe2");
            if (m2 && triple) {
                LLVMSetTarget(m2, triple);
                LLVMExecutionEngineRef ee2 = NULL;
                char *err2 = NULL;
                if (LLVMCreateMCJITCompilerForModule(&ee2, m2, NULL, 0, &err2) == 0 && ee2) {
                    printf("[llvm-diag] ... but WITH module triple \"%s\" set: MCJIT create ✓ "
                           "→ THE LEVER IS: set the module triple before JIT init.\n", triple);
                } else {
                    printf("[llvm-diag] ... even WITH module triple set, create FAILED: %s\n",
                           err2 ? err2 : "(NULL error string)");
                }
            }
        }
    }
    return ok ? 0 : 1;
}
