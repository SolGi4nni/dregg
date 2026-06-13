/* driver-sel4.c — the seL4-PD one-turn harness.
 *
 * Exposes a single C entry, `dregg_rootserver_run_turn()`, that the Rust root
 * task (src/main.rs) calls after installing the sel4-musl syscall handler. It
 * runs the standard embedded-Lean init for COMPILED Lean (NOT lean_initialize,
 * which would pull the elaborator/kernel — see ../../executor-pd/WALL.md) and
 * drives ONE real turn through the VERIFIED executor entry
 * `dregg_exec_full_forest_auth(String) -> String` (Dregg2/Exec/FFI.lean).
 *
 * This is the same init contract + turn as executor-pd/scripts/driver.c, but
 * (a) packaged as a callable C function (no `main`), and (b) the wire is
 * compiled in (the verified `wideDemoInput`), since an seL4 PD has no argv.
 *
 * Output goes to stderr/stdout via the libc, whose write()/writev() the
 * sel4-musl handler routes to the seL4 debug serial — so the receipt appears in
 * the QEMU boot log, the step-4 boot evidence.
 */
#include <lean/lean.h>
#include <stdio.h>
#include <string.h>

/* The verified production entry (C ABI: lean_object* in/out, a Lean String). */
extern lean_object *dregg_exec_full_forest_auth(lean_object *input);

/* The executor's top module init (emitted by the closure). v4.30.0 ABI: single
 * uint8_t arg, returns an IO result. */
extern lean_object *initialize_Dregg2_Dregg2_Exec_FFI(uint8_t builtin);

/* In runtime/init_module.h, not the shipped lean.h; it is in libleanrt_elf.a. */
extern void lean_initialize_runtime_module(void);

/* The verified demo wire (the same `wideDemoInput` the host-musl run banked: an
 * OFFER that the gated forest turn accepts -> status:2 ok:1). It is a large JSON
 * string, so it is provided as a generated C string constant (`out/demo-wire.c`,
 * emitted by scripts/relink-roottask.sh from out/demo-wire.txt) rather than a -D
 * macro (which can't carry the quotes/colons). A weak fallback to "" (which the
 * entry handles as a fail-closed `rejected` — still a full decode->step->encode
 * round trip) keeps the driver linkable on its own. */
extern const char dregg_demo_wire[];
__attribute__((weak)) const char dregg_demo_wire[] = "";

int dregg_rootserver_run_turn(void) {
    fputs("[exec] lean_initialize_runtime_module()\n", stderr);
    lean_initialize_runtime_module();

    fputs("[exec] initialize_Dregg2_Dregg2_Exec_FFI(builtin=1)\n", stderr);
    lean_object *res = initialize_Dregg2_Dregg2_Exec_FFI(1);
    if (lean_io_result_is_error(res)) {
        fputs("[exec] FATAL: module init returned IO error\n", stderr);
        lean_io_result_show_error(res);
        return 2;
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();

    lean_object *in = lean_mk_string(dregg_demo_wire);

    fputs("[exec] >>> dregg_exec_full_forest_auth(wire)\n", stderr);
    lean_object *out = dregg_exec_full_forest_auth(in);
    const char *outc = lean_string_cstr(out);
    fprintf(stderr, "[exec] <<< receipt (%zu bytes):\n", strlen(outc));
    fputs("---RECEIPT-BEGIN---\n", stdout);
    fputs(outc, stdout);
    fputs("\n---RECEIPT-END---\n", stdout);
    lean_dec_ref(out);
    fputs("[exec] turn complete — the VERIFIED executor ran inside the seL4 PD.\n", stderr);
    return 0;
}
