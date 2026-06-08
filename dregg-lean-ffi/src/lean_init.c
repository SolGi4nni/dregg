/* lean_init.c — a tiny C shim performing the Lean C-embedding init ritual.
 *
 * Many of the runtime entry points the ritual needs (`lean_io_mk_world`,
 * `lean_io_result_is_ok`, `lean_dec_ref`) are `static inline` in <lean/lean.h>
 * and therefore have NO linkable symbol — they can only be used from C that
 * includes the header. So we wrap the whole ritual here and expose a single
 * plain exported function for Rust to call.
 */
#include <stdint.h>
#include <string.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_Dregg2_Dregg2_Exec_FFI(uint8_t builtin);

/* The @[export]ed Lean `String -> String` state-marshalling step. At the C ABI a Lean
 * `String` is a `lean_object*`, so this takes/returns boxed Lean strings — which is why
 * it must be driven from C (the `lean_mk_string`/`lean_string_cstr` helpers below). */
extern lean_object *dregg_record_kernel_step(lean_object *input);

/* The @[export]ed Lean `String -> String` CAPS-bearing step: same shape, but the wire also
 * carries the held-cap table so the cross-vat / held-cap branch of `authorizedB` is exercised. */
extern lean_object *dregg_record_kernel_step_caps(lean_object *input);

/* The @[export]ed Lean `String -> String` FULL-TURN executor: decodes a
 * (RecChainedState, List FullAction), runs the PROVED `execFullTurn` (all-or-nothing), and
 * re-encodes the resulting Option state (post-cells + post-caps + receipt-log length + commit). */
extern lean_object *dregg_exec_full_turn(lean_object *input);

/* The @[export]ed Lean `String -> String` GATED COMPLETE-TURN executor (FILL X): decodes the §WIDE wire
 * (Turn envelope + action-tree node=auth+action+children + the 10-variant Authorization + all 45 effect
 * arms + the escrow/nullifier/commitment/swiss/queue side-tables), runs the PROVED gated tree executor
 * `FullForestAuth.execFullForestG` (the credentialValid ∧ cap-authority ∧ caveat-discharge fail-closed
 * gate in front of `execFullA`, all-or-nothing), and re-encodes the §WIDE output (post-state + receipt-log
 * length + commit; on rollback ok:0 echoes the unchanged pre-state). */
extern lean_object *dregg_exec_full_forest_auth(lean_object *input);

/* The @[export]ed Lean `String -> String` HANDLER-CUTOVER COMPLETE-TURN executor: decodes the §WIDE wire
 * (Turn envelope + action-tree + full state), runs admission ∘ `execHandlerTurn` over the lowered flat
 * action list (`lowerForestA (eraseAuth root)`), and re-encodes the §WIDE output (post-state + receipt-log
 * length + commit; on inadmissible rollback ok:0 echoes the unchanged pre-state).
 *
 * GATED on DREGG_HANDLER_TURN: this secondary export is absent from older archives. build.rs probes the
 * archive and only `#define`s DREGG_HANDLER_TURN when the symbol is present, so a stale archive does not
 * leave a dangling reference that `-dead_strip` would resolve by dropping the entire shim object. */
#ifdef DREGG_HANDLER_TURN
extern lean_object *dregg_exec_handler_turn(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED FINALITY GATE
 * (`Dregg2.Distributed.FinalityGate.finalizeGate`): decodes a wire-encoded
 * (wavelength, participants, lace), runs the VERIFIED `BlocklaceFinality.tauOrder` rule, and
 * re-encodes the finalized `(creator, seq)` order (or the `ERR` sentinel on a malformed wire). The
 * node calls this at the live commit point to compute finality FROM the verified rule, then admits a
 * turn to the executor ONLY when the verified rule finalizes it ("agreement-checked" -> "Lean-gated").
 *
 * GATED on DREGG_FINALIZE_GATE: this export lives in a module NOT in the FFI module's import closure,
 * so (a) build.rs probes the archive and only `#define`s DREGG_FINALIZE_GATE when the symbol is
 * present, and (b) `dregg_ffi_init` must ALSO run the module's own initializer (it is not reached by
 * `initialize_Dregg2_Dregg2_Exec_FFI`). When absent, the bridge is compiled out and the node falls
 * back to the un-gated path with a loud warning. */
#ifdef DREGG_FINALIZE_GATE
extern lean_object *initialize_Dregg2_Dregg2_Distributed_FinalityGate(uint8_t builtin);
extern lean_object *dregg_blocklace_finalize(lean_object *input);
#endif

/* Returns 0 on success, 1 if module initialization reported an IO error. */
int dregg_ffi_init(void) {
    lean_initialize_runtime_module();
    lean_object *res = initialize_Dregg2_Dregg2_Exec_FFI(1);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_dec_ref(res);
#ifdef DREGG_FINALIZE_GATE
    /* The finality-gate module is OUTSIDE the FFI closure, so its initializer is not run above.
     * Initialize it explicitly so `dregg_blocklace_finalize` is callable. Its own dependency
     * closure (Blocklace/ConsensusExec) is re-entrant-safe under Lean's init guards. */
    lean_object *gres = initialize_Dregg2_Dregg2_Distributed_FinalityGate(1);
    if (!lean_io_result_is_ok(gres)) {
        lean_io_result_show_error(gres);
        lean_dec_ref(gres);
        return 1;
    }
    lean_dec_ref(gres);
#endif
    lean_io_mark_end_initialization();
    return 0;
}

/* dregg_record_kernel_step_str — a plain-C string bridge over the Lean `String -> String`
 * record-cell-state step export.
 *
 * `in_utf8` is a NUL-terminated UTF-8 wire string (the JSON `RecordKernelState` + turn).
 * We box it into a Lean string, call the verified `dregg_record_kernel_step`, copy the
 * result into the caller-owned `out` buffer (NUL-terminated, truncated to `out_cap-1`),
 * and decref the Lean objects.
 *
 * Returns the FULL byte length of the result string (excluding the NUL). If that is
 * >= out_cap the output was truncated and the caller should retry with a larger buffer.
 * Returns (size_t)-1 only if `out`/`out_cap` are unusable. */
size_t dregg_record_kernel_step_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);   /* takes ownership semantics: refcount 1 */
    lean_object *res = dregg_record_kernel_step(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_record_kernel_step_caps_str — the caps-bearing analog of the bridge above. Identical
 * marshalling discipline; the only difference is it drives `dregg_record_kernel_step_caps`,
 * whose input wire also carries the `Caps` table. Same return contract (full byte length;
 * (size_t)-1 only on an unusable buffer). */
size_t dregg_record_kernel_step_caps_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_record_kernel_step_caps(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_exec_full_turn_str — the C string bridge over the Lean `String -> String` FULL-TURN
 * executor export. Identical marshalling discipline as the step bridges above; it drives
 * `dregg_exec_full_turn`, whose input wire is `{"cells":CELLS,"caps":CAPS,"actions":ACTIONS}`
 * and whose output is `{"cells":CELLS,"caps":CAPS,"loglen":N,"ok":B}`. Same return contract
 * (full byte length; (size_t)-1 only on an unusable buffer). */
size_t dregg_exec_full_turn_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_exec_full_turn(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_exec_full_forest_auth_str — the C string bridge over the Lean `String -> String` GATED
 * COMPLETE-TURN executor export (FILL X). Identical marshalling discipline as the bridges above; it drives
 * `dregg_exec_full_forest_auth`, whose input wire is the §WIDE `{"state":STATEW,"turn":TURNW}` and whose
 * output is `{"state":STATEW,"loglen":N,"ok":B}`. The executed object is the credential-AWARE
 * `FullForestAuth.execFullForestG` (a forged per-node credential ⇒ whole-turn rollback). Same return
 * contract (full byte length; (size_t)-1 only on an unusable buffer). */
size_t dregg_exec_full_forest_auth_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_exec_full_forest_auth(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

/* dregg_exec_handler_turn_str — the C string bridge over the Lean `String -> String` HANDLER-CUTOVER
 * COMPLETE-TURN executor export. Identical marshalling discipline as the bridges above; it drives
 * `dregg_exec_handler_turn`, whose input wire is the §WIDE `{"state":STATEW,"turn":TURNW}` and whose
 * output is `{"state":STATEW,"loglen":N,"ok":B}`. The executed object is admission ∘ `execHandlerTurn`
 * over the lowered action list (the handler-registry cutover path). Same return contract (full byte
 * length; (size_t)-1 only on an unusable buffer). */
#ifdef DREGG_HANDLER_TURN
size_t dregg_exec_handler_turn_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_exec_handler_turn(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_HANDLER_TURN */

/* dregg_blocklace_finalize_str — the C string bridge over the Lean `String -> String` VERIFIED
 * FINALITY GATE export. Identical marshalling discipline as the bridges above; it drives
 * `dregg_blocklace_finalize`, whose input wire is `"w=<W>;P=<participants>;B=<blocks>"` and whose
 * output is `"F=<creator>:<seq>,..."` (the verified finalized order) or `"ERR"` (fail-closed on a
 * malformed wire). Same return contract (full byte length; (size_t)-1 only on an unusable buffer). */
#ifdef DREGG_FINALIZE_GATE
size_t dregg_blocklace_finalize_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_blocklace_finalize(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_FINALIZE_GATE */
