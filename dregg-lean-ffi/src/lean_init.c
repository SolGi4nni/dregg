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
/* The RAW total-order export, co-located in `Dregg2.Distributed.FinalityGate`: returns the verified
 * `BlocklaceFinality.tauOrder` ITSELF (the ordered BlockId list `"T=<id>,<id>,..."`), proved
 * order-faithfully equal to `tauOrder` by `tau_order_export_eq`. Same module ⇒ same initializer ⇒
 * gated on the same DREGG_FINALIZE_GATE define. */
extern lean_object *dregg_tau_order(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED STRAND-ADMISSION GATE
 * (`Dregg2.Distributed.StrandAdmission.admitGate`): decodes a wire-encoded admission registry +
 * queried strand (`"N=<vouch-threshold>;m=<min-bond>;S=<seeds>;V=<vouches>;Bo=<bonds>;q=<strand>"`),
 * runs the VERIFIED hybrid stake-OR-vouch `admitted` predicate, and returns `"1"` (admitted) / `"0"`
 * (not admitted) / `"ERR"` (fail-closed on a malformed wire). The federation calls this at the
 * admission point to compute the F-4 Sybil verdict FROM the verified rule itself.
 *
 * GATED on DREGG_STRAND_ADMIT: like the finality gate, this export lives in a module OUTSIDE the FFI
 * module's import closure, so (a) build.rs probes the archive and only `#define`s DREGG_STRAND_ADMIT
 * when the symbol is present, and (b) `dregg_ffi_init` must ALSO run the module's own initializer. */
#ifdef DREGG_STRAND_ADMIT
extern lean_object *initialize_Dregg2_Dregg2_Distributed_StrandAdmission(uint8_t builtin);
extern lean_object *dregg_strand_admit(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED CapTP + COORDINATION decision gates
 * (`Dregg2.Exec.DistributedExports`): six wire-in/wire-out exports the captp/coord runtime invokes
 * so it computes its verdict FROM the verified Lean rule itself (dreggrs Rust → differential):
 *   dregg_captp_validate_handoff — §6 non-amplification (handoffNonAmplifyingC granted⊆held);
 *   dregg_captp_process_drop     — GC session-refcount verdict (CapTPGCConcrete.processDrop);
 *   dregg_captp_pipeline_resolve — promise-pipelining FIFO resolve/break drain;
 *   dregg_coord_2pc_decide       — 2PC evaluate_votes (TwoPhaseCommit.evaluate);
 *   dregg_coord_causal_order     — causal-DAG happened_before (CausalOrder via decidable hbBool);
 *   dregg_coord_shared_budget    — shared-budget tau-resolution (SharedBudgetDynamics.resolveOrdered).
 *
 * GATED on DREGG_DISTRIBUTED_EXPORTS: this module is OUTSIDE the FFI module's import closure, so
 * (a) build.rs probes the archive and only `#define`s it when `dregg_captp_validate_handoff` is
 * present, and (b) `dregg_ffi_init` must ALSO run the module's own initializer. When absent the
 * bridges are compiled out and the captp/coord runtime falls back to its native Rust gates. */
#ifdef DREGG_DISTRIBUTED_EXPORTS
extern lean_object *initialize_Dregg2_Dregg2_Exec_DistributedExports(uint8_t builtin);
extern lean_object *dregg_captp_validate_handoff(lean_object *input);
extern lean_object *dregg_captp_process_drop(lean_object *input);
extern lean_object *dregg_captp_pipeline_resolve(lean_object *input);
extern lean_object *dregg_coord_2pc_decide(lean_object *input);
extern lean_object *dregg_coord_causal_order(lean_object *input);
extern lean_object *dregg_coord_shared_budget(lean_object *input);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED FLOW-REFINEMENT DECISION GATE
 * (`Dregg2.Deos.FlowRefine.decideRefinesGate`): decodes a wire-encoded pair of σ-free `Proc`s
 * (`"A=<preorder-tokens>;B=<preorder-tokens>"`), runs the PROVED `decideRefines` (sound+complete for
 * the online-simulation refinement order `≤ᶠ`, per `decideRefines_iff`), and returns `"1"` (A ≤ᶠ B) /
 * `"0"` (A ⋠ B) / `"ERR"` (fail-closed on a malformed wire). `dregg-deploy/src/refine.rs` calls this
 * at the safe-upgrade / intent-conformance gate so it runs the verified procedure, not a mirror.
 *
 * GATED on DREGG_DECIDE_REFINES: this export lives in a module OUTSIDE the FFI module's import
 * closure, so (a) build.rs probes the archive and only `#define`s DREGG_DECIDE_REFINES when the symbol
 * is present, and (b) `dregg_ffi_init` must ALSO run the module's own initializer. When absent the
 * bridge is compiled out and the deploy gate falls back to its in-process σ-free mirror. */
#ifdef DREGG_DECIDE_REFINES
extern lean_object *initialize_Dregg2_Dregg2_Deos_FlowRefine(uint8_t builtin);
extern lean_object *dregg_decide_refines(lean_object *input);
#endif

/* The NO-COPY (`lean_object*`) DIRECT boundary lives in `Dregg2.Exec.FFIDirect`, which IMPORTS
 * `Dregg2.Exec.FFI` — so its initializer is OUTSIDE the FFI module's import closure and is NOT run by
 * `initialize_Dregg2_Dregg2_Exec_FFI`. `dregg_ffi_init` must run it explicitly (like the gate modules
 * above). The builders/readers + `dregg_exec_full_forest_auth_direct` are called DIRECTLY from Rust
 * (plain C-ABI `lean_object*` functions), so no string bridge lives here — only the initializer.
 *
 * GATED on DREGG_DIRECT: build.rs probes the archive and only `#define`s it when the export is
 * present, so a stale archive does not leave a dangling `initialize_…_FFIDirect` reference. */
#ifdef DREGG_DIRECT
extern lean_object *initialize_Dregg2_Dregg2_Exec_FFIDirect(uint8_t builtin);
#endif

/* The @[export]ed Lean `String -> String` VERIFIED STORAGE CONTENT ROOT
 * (`Dregg2.Storage.Deployed.contentRootFFI`): decodes space-separated object int-triples, runs the
 * PROVED `contentRootDeployed` (bound by `contentRootDeployed_injective` over the deployed Poseidon2,
 * called back through `@[extern "dregg_poseidon2_2to1"]` = `circuit::storage_ffi`), returns the root
 * felt as a decimal string. The verified content-root LOGIC is Lean; the hot hash PRIMITIVE is fast
 * Rust — the real "Lean is the runtime" for storage. GATED on DREGG_STORAGE_CONTENT_ROOT (the module
 * is OUTSIDE the FFI closure; build.rs probes + defines it, and dregg_ffi_init runs its initializer). */
#ifdef DREGG_STORAGE_CONTENT_ROOT
extern lean_object *initialize_Dregg2_Dregg2_Storage_Deployed(uint8_t builtin);
extern lean_object *dregg_storage_content_root(lean_object *input);
#endif

/* ── NO-COPY BOUNDARY runtime helpers (linkable wrappers over the `static inline`
 * <lean/lean.h> primitives the no-copy `lean_direct.rs` boundary needs). `lean_inc_ref`,
 * `lean_dec_ref`, `lean_box`, and `lean_string_cstr` are `static inline` in the header (no
 * linkable symbol), so Rust cannot call them directly — exactly the reason this C shim exists.
 * These thin `dregg_rt_*` wrappers give them a linkable C-ABI symbol. (`lean_mk_string` is a real
 * LEAN_EXPORT and is called directly from Rust.) */
/* Use the SCALAR-CHECKING `lean_inc`/`lean_dec` (not `lean_inc_ref`/`lean_dec_ref`): small
 * `Nat`/`Int`/no-field-enum (Auth) values are TAGGED POINTERS, not heap objects, so the `_ref`
 * variants would dereference an invalid address. `lean_inc`/`lean_dec` short-circuit on scalars. */
void dregg_rt_inc(lean_object *o) { lean_inc(o); }
void dregg_rt_dec(lean_object *o) { lean_dec(o); }
lean_object *dregg_rt_box(size_t n) { return lean_box(n); }
const char *dregg_rt_string_cstr(lean_object *s) { return lean_string_cstr(s); }

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
#ifdef DREGG_STRAND_ADMIT
    /* The strand-admission module is also OUTSIDE the FFI closure; initialize it explicitly so
     * `dregg_strand_admit` is callable. Its dependency closure (BlocklaceFinality/StrandIntegrity)
     * is re-entrant-safe under Lean's init guards (shared with the finality gate above). */
    lean_object *ares = initialize_Dregg2_Dregg2_Distributed_StrandAdmission(1);
    if (!lean_io_result_is_ok(ares)) {
        lean_io_result_show_error(ares);
        lean_dec_ref(ares);
        return 1;
    }
    lean_dec_ref(ares);
#endif
#ifdef DREGG_DISTRIBUTED_EXPORTS
    /* The CapTP+coord distributed-exports module is also OUTSIDE the FFI closure; initialize it
     * explicitly so the six `dregg_captp_*` / `dregg_coord_*` exports are callable. Its dependency
     * closure (CapTPConcrete/CapTPGCConcrete/CapTPPipeline/Coord.*) is re-entrant-safe under Lean's
     * init guards. */
    lean_object *dres = initialize_Dregg2_Dregg2_Exec_DistributedExports(1);
    if (!lean_io_result_is_ok(dres)) {
        lean_io_result_show_error(dres);
        lean_dec_ref(dres);
        return 1;
    }
    lean_dec_ref(dres);
#endif
#ifdef DREGG_DECIDE_REFINES
    /* The flow-refinement module is also OUTSIDE the FFI closure; initialize it explicitly so
     * `dregg_decide_refines` is callable. Its dependency closure (Deos.FlowAlgebra) is
     * re-entrant-safe under Lean's init guards. */
    lean_object *rres = initialize_Dregg2_Dregg2_Deos_FlowRefine(1);
    if (!lean_io_result_is_ok(rres)) {
        lean_io_result_show_error(rres);
        lean_dec_ref(rres);
        return 1;
    }
    lean_dec_ref(rres);
#endif
#ifdef DREGG_DIRECT
    /* The no-copy direct boundary module is OUTSIDE the FFI closure (it imports FFI); initialize it
     * explicitly so the `dregg_d_*` builders/readers + `dregg_exec_full_forest_auth_direct` are
     * callable. Its dependency closure (Dregg2.Exec.FFI and below) is re-entrant-safe under Lean's
     * init guards (already initialized by `initialize_Dregg2_Dregg2_Exec_FFI` above). */
    lean_object *fdres = initialize_Dregg2_Dregg2_Exec_FFIDirect(1);
    if (!lean_io_result_is_ok(fdres)) {
        lean_io_result_show_error(fdres);
        lean_dec_ref(fdres);
        return 1;
    }
    lean_dec_ref(fdres);
#endif
#ifdef DREGG_STORAGE_CONTENT_ROOT
    /* The verified-storage content-root module is OUTSIDE the FFI closure; initialize it explicitly
     * so `dregg_storage_content_root` is callable. Its dependency closure (Storage.BucketCommitment /
     * Lightclient.MMR) is re-entrant-safe under Lean's init guards. */
    lean_object *sres = initialize_Dregg2_Dregg2_Storage_Deployed(1);
    if (!lean_io_result_is_ok(sres)) {
        lean_io_result_show_error(sres);
        lean_dec_ref(sres);
        return 1;
    }
    lean_dec_ref(sres);
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

#ifdef DREGG_STORAGE_CONTENT_ROOT
/* dregg_storage_content_root_str — the C string bridge over the VERIFIED Lean `String -> String`
 * storage content-root export (`Dregg2.Storage.Deployed.contentRootFFI`). Input: space-separated
 * object int-triples (`"key ctype body key ctype body …"`). Output: the deployed Poseidon2 content
 * root as a decimal string. Runs the PROVED `contentRootDeployed` (bound by
 * `contentRootDeployed_injective`), calling the fast Rust Poseidon2 through `@[extern]`. Same return
 * contract as the bridges above. */
size_t dregg_storage_content_root_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_storage_content_root(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif

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

/* dregg_tau_order_str — the C string bridge over the Lean `String -> String` RAW TOTAL-ORDER export.
 * Identical marshalling discipline as the bridges above; it drives `dregg_tau_order`, whose input
 * wire is the SAME `"w=<W>;P=<participants>;B=<blocks>"` the finality gate consumes and whose output
 * is `"T=<id>,<id>,..."` (the verified `BlocklaceFinality.tauOrder` total order as the ordered BlockId
 * list) or `"ERR"` (fail-closed on a malformed wire). `tau_order_export_eq` proves the output is the
 * encoding of `tauOrder` order-faithfully. Same return contract (full byte length; (size_t)-1 only on
 * an unusable buffer). Co-located in the FinalityGate module ⇒ gated on the same DREGG_FINALIZE_GATE. */
size_t dregg_tau_order_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_tau_order(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_FINALIZE_GATE */

/* dregg_strand_admit_str — the C string bridge over the Lean `String -> String` VERIFIED
 * STRAND-ADMISSION GATE export. Identical marshalling discipline as the bridges above; it drives
 * `dregg_strand_admit`, whose input wire is
 * `"N=<vouch-threshold>;m=<min-bond>;S=<seeds>;V=<vouches>;Bo=<bonds>;q=<strand>"` and whose output
 * is `"1"` (admitted) / `"0"` (not admitted) / `"ERR"` (fail-closed on a malformed wire). Same return
 * contract (full byte length; (size_t)-1 only on an unusable buffer). */
#ifdef DREGG_STRAND_ADMIT
size_t dregg_strand_admit_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_strand_admit(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_STRAND_ADMIT */

/* dregg_decide_refines_str — the C string bridge over the Lean `String -> String` VERIFIED
 * FLOW-REFINEMENT DECISION GATE export. Identical marshalling discipline as the bridges above; it
 * drives `dregg_decide_refines`, whose input wire is `"A=<preorder-tokens>;B=<preorder-tokens>"` (a
 * pair of σ-free `Proc`s) and whose output is `"1"` (A ≤ᶠ B) / `"0"` (A ⋠ B) / `"ERR"` (fail-closed on
 * a malformed wire). Same return contract (full byte length; (size_t)-1 only on an unusable buffer). */
#ifdef DREGG_DECIDE_REFINES
size_t dregg_decide_refines_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_decide_refines(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_DECIDE_REFINES */

/* dregg_captp_validate_handoff_str / dregg_captp_process_drop_str / dregg_captp_pipeline_resolve_str
 * / dregg_coord_2pc_decide_str / dregg_coord_causal_order_str / dregg_coord_shared_budget_str — the
 * six C string bridges over the VERIFIED CapTP+coord decision exports. Identical marshalling
 * discipline as the bridges above; each drives its `dregg_captp_*` / `dregg_coord_*` Lean export over
 * the compact wire grammar documented in `Dregg2.Exec.DistributedExports`. Same return contract (full
 * byte length; (size_t)-1 only on an unusable buffer). Gated on DREGG_DISTRIBUTED_EXPORTS. */
#ifdef DREGG_DISTRIBUTED_EXPORTS
size_t dregg_captp_validate_handoff_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_captp_validate_handoff(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_captp_process_drop_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_captp_process_drop(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_captp_pipeline_resolve_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_captp_pipeline_resolve(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_coord_2pc_decide_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_coord_2pc_decide(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_coord_causal_order_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_coord_causal_order(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}

size_t dregg_coord_shared_budget_str(const char *in_utf8, char *out, size_t out_cap) {
    if (out == 0 || out_cap == 0) {
        return (size_t)-1;
    }
    lean_object *in_obj = lean_mk_string(in_utf8);
    lean_object *res = dregg_coord_shared_budget(in_obj);
    const char *cstr = lean_string_cstr(res);
    size_t full = strlen(cstr);
    size_t copy = (full < out_cap - 1) ? full : (out_cap - 1);
    memcpy(out, cstr, copy);
    out[copy] = '\0';
    lean_dec_ref(res);
    return full;
}
#endif /* DREGG_DISTRIBUTED_EXPORTS */
