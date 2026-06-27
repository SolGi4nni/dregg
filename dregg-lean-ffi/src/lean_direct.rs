//! lean_direct.rs — THE NO-COPY (`lean_object*`) boundary.
//!
//! The JSON path (`marshal.rs` + `Dregg2.Exec.FFI.execFullForestAuthStep`) serializes the whole
//! `(host, state, turn)` to a string the Lean side immediately PARSES back into the inductives it
//! could have been handed directly, runs the executor, and re-ENCODES the post-state to a string this
//! crate re-parses. That double round-trip is the ~100µs/turn tax the bench measures, and it tracks
//! JSON BYTES. This module removes the JSON: it CONSTRUCTS the Lean `WHostCtx`/`WState`/`WTurn`
//! inductives directly via the `Dregg2.Exec.FFIDirect` BUILDER exports (bottom-up — leaves first),
//! runs the IDENTICAL proved executor via `dregg_exec_full_forest_auth_direct`, and READS the
//! post-state back out via the READER exports — no string crosses the boundary in either direction.
//!
//! # Why this is not a UB minefield
//!
//! The Rust side never touches a raw `lean_ctor_set`/offset. Every inductive is built by calling a
//! Lean `@[export]` BUILDER (`dregg_d_*`) whose body the LEAN COMPILER generated with the correct
//! constructor layout, and read by a Lean `@[export]` READER. We only ever pass/return
//! `lean_object*` (opaque) and native scalars (`u64`/`u8`/`bool`), exactly the C ABI Lean codegen
//! emits. The one discipline we own is refcounting (Lean's owned-arg convention): a builder CONSUMES
//! its `lean_object*` args, a reader CONSUMES the object it projects. So we `lean_inc` before any
//! reader call we want to read again, and never touch an object after it is consumed.
//!
//! # Availability
//!
//! Compiled in only when the linked archive exports `dregg_exec_full_forest_auth_direct`
//! (`cfg(dregg_direct_present)`, set by build.rs). When absent the public entry returns `Err` and the
//! caller falls back to the JSON path.

use crate::marshal::{WForest, WireHostCtx, WireState};
// Auth/Cap/WireAuth/WireCaveat/WireValue are referenced only by the FFI-present
// marshalling path (the `#[cfg(dregg_direct_present)]` block below) — gate the
// import to match its consumer, or it reads as unused when the FFI is absent.
#[cfg(dregg_direct_present)]
use crate::marshal::{Auth, Cap, WireAuth, WireCaveat, WireValue};
use crate::{ShadowState, ShadowVerdict, TurnStatus};

/// Whether the no-copy direct boundary is available in this build (the archive exported
/// `dregg_exec_full_forest_auth_direct` AND the Lean runtime initialised). The caller uses this to
/// decide between the direct path and the JSON oracle.
pub fn direct_available() -> bool {
    cfg!(dregg_direct_present) && crate::lean_available()
}

/// Env-gated sub-phase profile accumulator (seconds). `DREGG_FFI_PROFILE=1` makes `run_direct`
/// add each call's (in_build, exec, out_read) into these; `prof_dump` prints the per-call averages
/// and resets. Zero overhead when the env flag is off (the adds are skipped at the call site).
use std::sync::atomic::{AtomicU64, Ordering};
static PROF_IN: AtomicU64 = AtomicU64::new(0);
static PROF_EXEC: AtomicU64 = AtomicU64::new(0);
static PROF_READ: AtomicU64 = AtomicU64::new(0);
static PROF_N: AtomicU64 = AtomicU64::new(0);

fn prof_accum(in_s: f64, exec_s: f64, read_s: f64) {
    PROF_IN.fetch_add((in_s * 1e9) as u64, Ordering::Relaxed);
    PROF_EXEC.fetch_add((exec_s * 1e9) as u64, Ordering::Relaxed);
    PROF_READ.fetch_add((read_s * 1e9) as u64, Ordering::Relaxed);
    PROF_N.fetch_add(1, Ordering::Relaxed);
}

/// Print the accumulated per-call sub-phase averages (µs) and reset. Call after a profiling run.
pub fn prof_dump(label: &str) {
    let n = PROF_N.swap(0, Ordering::Relaxed).max(1);
    let in_us = PROF_IN.swap(0, Ordering::Relaxed) as f64 / 1e3 / n as f64;
    let ex_us = PROF_EXEC.swap(0, Ordering::Relaxed) as f64 / 1e3 / n as f64;
    let rd_us = PROF_READ.swap(0, Ordering::Relaxed) as f64 / 1e3 / n as f64;
    eprintln!(
        "DREGG_FFI_PROFILE[{label}] n={n} in_build={in_us:.3}us exec={ex_us:.3}us out_read={rd_us:.3}us total={:.3}us",
        in_us + ex_us + rd_us
    );
}

#[cfg(dregg_direct_present)]
mod imp {
    use super::*;

    /// An opaque Lean runtime object (`lean_object*`). We never dereference it; it is only ever
    /// passed to / returned from the Lean `@[export]` C-ABI functions below.
    #[repr(C)]
    pub(super) struct LeanObj {
        _private: [u8; 0],
    }
    type Obj = *mut LeanObj;

    // The Lean runtime refcount helpers (declared `static inline` in <lean/lean.h>; the C shim
    // re-exports linkable wrappers — but `lean_inc`/`lean_dec` here resolve from the runtime archive
    // the build already links). We use the public `dregg_rt_inc`/`dregg_rt_dec` symbols.
    extern "C" {
        // Linkable wrappers over the `static inline` runtime helpers (defined in the C shim
        // `lean_init.c` — the inline originals have no linkable symbol).
        fn dregg_rt_inc(o: Obj);
        fn dregg_rt_dec(o: Obj);
        fn dregg_rt_string_cstr(s: Obj) -> *const std::os::raw::c_char;
        /// `lean_mk_string` is a real LEAN_EXPORT; build a Lean `String` from a NUL-terminated UTF-8.
        fn lean_mk_string(s: *const std::os::raw::c_char) -> Obj;

        // ---- the FFIDirect BUILDER family (construct real Lean inductives) ----
        fn dregg_d_int_of_u64(mag: u64, neg: u8) -> Obj;
        fn dregg_d_nat_of_u64(n: u64) -> Obj;

        static dregg_d_natlist_nil: Obj;
        fn dregg_d_natlist_cons(x: Obj, xs: Obj) -> Obj;

        // `Auth` is a no-field enum: at the C ABI it is the UNBOXED ctor-index `u8`, NOT a
        // `lean_object*`. So `authListCons` takes the tag directly as `u8` (no boxing).
        static dregg_d_authlist_nil: Obj;
        fn dregg_d_authlist_cons(x: u8, xs: Obj) -> Obj;

        static dregg_d_cap_null: Obj;
        fn dregg_d_cap_node(t: u64) -> Obj;
        fn dregg_d_cap_endpoint(t: u64, r: Obj) -> Obj;
        static dregg_d_caplist_nil: Obj;
        fn dregg_d_caplist_cons(x: Obj, xs: Obj) -> Obj;

        fn dregg_d_value_int(i: Obj) -> Obj;
        fn dregg_d_value_dig(n: u64) -> Obj;
        fn dregg_d_value_sym(n: u64) -> Obj;
        fn dregg_d_value_record(fs: Obj) -> Obj;
        static dregg_d_fieldlist_nil: Obj;
        fn dregg_d_fieldlist_cons(name: Obj, v: Obj, xs: Obj) -> Obj;

        static dregg_d_cells_nil: Obj;
        fn dregg_d_cells_cons(id: u64, v: Obj, xs: Obj) -> Obj;
        static dregg_d_caps_nil: Obj;
        fn dregg_d_caps_cons(h: u64, cl: Obj, xs: Obj) -> Obj;
        static dregg_d_bal_nil: Obj;
        fn dregg_d_bal_cons(cell: u64, asset: u64, amt: Obj, xs: Obj) -> Obj;
        static dregg_d_cellnats_nil: Obj;
        fn dregg_d_cellnats_cons(cell: u64, val: u64, xs: Obj) -> Obj;

        fn dregg_d_mk_wstate(
            cells: Obj,
            caps: Obj,
            bal: Obj,
            nullifiers: Obj,
            commitments: Obj,
            revoked: Obj,
            lifecycle: Obj,
            death_cert: Obj,
            delegate: Obj,
        ) -> Obj;

        fn dregg_d_auth_signature(pk: u64, sig: u64) -> Obj;
        fn dregg_d_auth_proof(vk: u64, pf: u64, ba: u64, br: u64) -> Obj;
        fn dregg_d_auth_breadstuff(tok: u64) -> Obj;
        fn dregg_d_auth_bearer(dm: u64, ds: u64, stark: u8) -> Obj;
        static dregg_d_auth_unchecked: Obj;
        fn dregg_d_auth_captp(im: u64, sm: u64, isig: u64, ss: u64) -> Obj;
        fn dregg_d_auth_custom(st: u64, pf: u64) -> Obj;
        fn dregg_d_auth_oneof(cands: Obj, i: u64) -> Obj;
        fn dregg_d_auth_stealth(otp: u64, eph: u64, sig: u64) -> Obj;
        fn dregg_d_auth_token(key: u64, sig: u64) -> Obj;
        static dregg_d_authwlist_nil: Obj;
        fn dregg_d_authwlist_cons(x: Obj, xs: Obj) -> Obj;

        fn dregg_d_mk_caveat(tier: u64, cell: u64, asset: u64, min: Obj) -> Obj;
        static dregg_d_caveatlist_nil: Obj;
        fn dregg_d_caveatlist_cons(x: Obj, xs: Obj) -> Obj;

        fn dregg_d_act_balance(actor: u64, src: u64, dst: u64, amt: Obj, asset: u64) -> Obj;
        fn dregg_d_act_delegate(delegator: u64, recipient: u64, t: u64) -> Obj;
        fn dregg_d_act_revoke(holder: u64, t: u64) -> Obj;
        fn dregg_d_act_mint(actor: u64, cell: u64, asset: u64, amt: Obj) -> Obj;
        fn dregg_d_act_burn(actor: u64, cell: u64, asset: u64, amt: Obj) -> Obj;
        fn dregg_d_act_setfield(actor: u64, cell: u64, field: Obj, v: Obj) -> Obj;
        fn dregg_d_act_emit(actor: u64, cell: u64, topic: Obj, data: Obj) -> Obj;
        fn dregg_d_act_incnonce(actor: u64, cell: u64, new_nonce: Obj) -> Obj;
        fn dregg_d_act_setperms(actor: u64, cell: u64, perms: Obj) -> Obj;
        fn dregg_d_act_setvk(actor: u64, cell: u64, vk: Obj) -> Obj;
        fn dregg_d_act_introduce(introducer: u64, recipient: u64, target: u64) -> Obj;
        fn dregg_d_act_delatten(delegator: u64, recipient: u64, target: u64, keep: Obj) -> Obj;
        fn dregg_d_act_atten(actor: u64, idx: u64, keep: Obj) -> Obj;
        fn dregg_d_act_revdel(holder: u64, target: u64) -> Obj;
        fn dregg_d_act_exercise(actor: u64, target: u64, inner: Obj) -> Obj;
        fn dregg_d_act_createcell(actor: u64, new_cell: u64) -> Obj;
        fn dregg_d_act_createcellfactory(actor: u64, new_cell: u64, vk: Obj) -> Obj;
        fn dregg_d_act_spawn(actor: u64, child: u64, target: u64) -> Obj;
        fn dregg_d_act_bmint(actor: u64, cell: u64, asset: u64, value: Obj) -> Obj;
        fn dregg_d_act_nspend(nf: u64, actor: u64, spend_proof: u8) -> Obj;
        fn dregg_d_act_ncreate(cm: u64, actor: u64) -> Obj;
        fn dregg_d_act_sov(actor: u64, cell: u64) -> Obj;
        fn dregg_d_act_refusal(actor: u64, cell: u64) -> Obj;
        fn dregg_d_act_rarchive(actor: u64, cell: u64) -> Obj;
        fn dregg_d_act_cseal(actor: u64, cell: u64) -> Obj;
        fn dregg_d_act_cunseal(actor: u64, cell: u64) -> Obj;
        fn dregg_d_act_cdestroy(actor: u64, cell: u64, cert_hash: u64) -> Obj;
        fn dregg_d_act_rdel(actor: u64, child: u64) -> Obj;
        fn dregg_d_act_psend(actor: u64) -> Obj;
        fn dregg_d_act_hwrite(actor: u64, target: u64, addr: Obj, v: Obj, new_root: Obj) -> Obj;
        static dregg_d_actlist_nil: Obj;
        fn dregg_d_actlist_cons(x: Obj, xs: Obj) -> Obj;

        fn dregg_d_mk_wforest(auth: Obj, caveats: Obj, action: Obj, children: Obj) -> Obj;
        fn dregg_d_mk_wchild(holder: u64, keep: Obj, parent_cap: Obj, sub: Obj) -> Obj;
        static dregg_d_childlist_nil: Obj;
        fn dregg_d_childlist_cons(x: Obj, xs: Obj) -> Obj;

        fn dregg_d_mk_wturn(
            agent: u64,
            nonce: u64,
            fee: Obj,
            valid_until: u64,
            block_height: u64,
            prev_hash: u64,
            root: Obj,
        ) -> Obj;
        fn dregg_d_mk_whostctx(
            now: u64,
            block_height: u64,
            frozen: Obj,
            stored_head: u64,
            budget: u64,
        ) -> Obj;

        // ---- the executor (takes the three built values; returns a WStatusResult) ----
        fn dregg_exec_full_forest_auth_direct(host: Obj, state: Obj, turn: Obj) -> Obj;

        // ---- MEASUREMENT-ONLY exports (additive; see FFIDirect.lean §MEASUREMENT) ----
        // The bare cross-into-Lean floor: takes the same `WState` and returns it (no exec).
        fn dregg_ffi_identity(state: Obj) -> Obj;
        // `execDirect` with monotonic-clock fences between its 4 sub-phases (prints to stderr only
        // under DREGG_LEAN_PROFILE=1). Pure-typed (runs its IO internally via `unsafeIO`), so the ABI
        // is the SAME `WStatusResult` ctor as `execDirect` — no `world` token to thread.
        fn dregg_exec_full_forest_auth_direct_profiled(host: Obj, state: Obj, turn: Obj) -> Obj;

        // ---- the READER family (project the result + post-state to scalars) ----
        fn dregg_d_res_status(r: Obj) -> u64;
        fn dregg_d_res_loglen(r: Obj) -> u64;
        fn dregg_d_res_reason(r: Obj) -> u64;
        fn dregg_d_res_state(r: Obj) -> Obj;
        fn dregg_d_int_mag(i: Obj) -> u64;
        fn dregg_d_int_neg(i: Obj) -> u8;

        fn dregg_d_st_cells(w: Obj) -> Obj;
        fn dregg_d_st_caps(w: Obj) -> Obj;
        fn dregg_d_st_bal(w: Obj) -> Obj;
        fn dregg_d_st_nullifiers(w: Obj) -> Obj;
        fn dregg_d_st_commitments(w: Obj) -> Obj;
        fn dregg_d_st_revoked(w: Obj) -> Obj;
        fn dregg_d_st_lifecycle(w: Obj) -> Obj;
        fn dregg_d_st_deathcert(w: Obj) -> Obj;
        fn dregg_d_st_delegate(w: Obj) -> Obj;

        fn dregg_d_natlist_len(xs: Obj) -> u64;
        fn dregg_d_natlist_get(xs: Obj, i: u64) -> u64;

        fn dregg_d_cells_len(xs: Obj) -> u64;
        fn dregg_d_cells_id(xs: Obj, i: u64) -> u64;
        fn dregg_d_cells_val(xs: Obj, i: u64) -> Obj;

        fn dregg_d_value_tag(v: Obj) -> u64;
        fn dregg_d_value_int_get(v: Obj) -> Obj;
        fn dregg_d_value_nat_get(v: Obj) -> u64;
        fn dregg_d_value_record_get(v: Obj) -> Obj;
        fn dregg_d_fieldlist_len(xs: Obj) -> u64;
        fn dregg_d_fieldlist_name(xs: Obj, i: u64) -> Obj;
        fn dregg_d_fieldlist_val(xs: Obj, i: u64) -> Obj;

        fn dregg_d_bal_len(xs: Obj) -> u64;
        fn dregg_d_bal_cell(xs: Obj, i: u64) -> u64;
        fn dregg_d_bal_asset(xs: Obj, i: u64) -> u64;
        fn dregg_d_bal_amt(xs: Obj, i: u64) -> Obj;

        fn dregg_d_caps_len(xs: Obj) -> u64;
        fn dregg_d_caps_holder(xs: Obj, i: u64) -> u64;
        fn dregg_d_caps_clist(xs: Obj, i: u64) -> Obj;
        fn dregg_d_caplist_len(xs: Obj) -> u64;
        fn dregg_d_caplist_get(xs: Obj, i: u64) -> Obj;
        fn dregg_d_cap_tag(c: Obj) -> u64;
        fn dregg_d_cap_target(c: Obj) -> u64;
        fn dregg_d_cap_rights(c: Obj) -> Obj;
        fn dregg_d_authlist_len(xs: Obj) -> u64;
        fn dregg_d_authlist_get(xs: Obj, i: u64) -> u8;

        fn dregg_d_cellnats_len(xs: Obj) -> u64;
        fn dregg_d_cellnats_cell(xs: Obj, i: u64) -> u64;
        fn dregg_d_cellnats_val(xs: Obj, i: u64) -> u64;
    }

    /// `dregg_rt_string_cstr` reads a borrowed string; we build an owned `String` then `dec` the Lean
    /// string (the reader handed us an owned ref). Caller passes an OWNED `Obj` (consumes it).
    unsafe fn read_owned_string(s: Obj) -> String {
        let cstr = dregg_rt_string_cstr(s);
        let out = std::ffi::CStr::from_ptr(cstr)
            .to_string_lossy()
            .into_owned();
        dregg_rt_dec(s);
        out
    }

    /// Build a Lean `String` from a Rust `&str`. Returns an OWNED `Obj`. NUL is impossible in a field
    /// name (the marshaller never produces one); we still guard.
    unsafe fn mk_string(s: &str) -> Obj {
        let c = std::ffi::CString::new(s).unwrap_or_default();
        lean_mk_string(c.as_ptr())
    }

    /// Build a Lean `Int` from an `i128`. Returns an OWNED `Obj`. The kernel ints (balances, field
    /// values, fees) fit `i64` in practice; we carry the magnitude + sign through the Lean builder
    /// (which boxes a real `Int`), so no precision is lost up to `u64` magnitude.
    unsafe fn mk_int(i: i128) -> Obj {
        let neg = i < 0;
        let mag = i.unsigned_abs();
        // The wire/kernel ints are <= u64 magnitude; clamp defensively (a value beyond u64 would be a
        // marshalling bug the JSON path would also mis-handle). The builder takes a u64 magnitude.
        let mag_u64 = if mag > u64::MAX as u128 {
            u64::MAX
        } else {
            mag as u64
        };
        dregg_d_int_of_u64(mag_u64, neg as u8)
    }

    /// Read an owned Lean `Int` back to `i128` (consumes the obj via the mag/neg readers, which each
    /// consume — so we `inc` before the first and let the second consume).
    unsafe fn read_owned_int(i: Obj) -> i128 {
        dregg_rt_inc(i);
        let mag = dregg_d_int_mag(i); // consumes one ref (the inc'd one)
        let neg = dregg_d_int_neg(i) != 0; // consumes the original ref
        if neg {
            -(mag as i128)
        } else {
            mag as i128
        }
    }

    // ---- list builders (Auth / Cap / Value-fields / AuthW / caveat / action / child) ----

    unsafe fn build_auth_list(rights: &[Auth]) -> Obj {
        let mut acc = dregg_d_authlist_nil;
        for a in rights.iter().rev() {
            // The element is the UNBOXED Auth ctor index (== the `Auth as u8` discriminant, which
            // matches the Lean `Auth` ctor order Read=0..Notify=7). Pass it directly — no boxing.
            acc = dregg_d_authlist_cons(*a as u8, acc);
        }
        acc
    }

    unsafe fn build_cap(c: &Cap) -> Obj {
        match c {
            Cap::Null => dregg_d_cap_null,
            Cap::Node(t) => dregg_d_cap_node(*t),
            Cap::Endpoint(t, rights) => dregg_d_cap_endpoint(*t, build_auth_list(rights)),
        }
    }

    unsafe fn build_cap_list(cl: &[Cap]) -> Obj {
        let mut acc = dregg_d_caplist_nil;
        for c in cl.iter().rev() {
            acc = dregg_d_caplist_cons(build_cap(c), acc);
        }
        acc
    }

    unsafe fn build_value(v: &WireValue) -> Obj {
        match v {
            WireValue::Int(i) => dregg_d_value_int(mk_int(*i)),
            WireValue::Dig(n) => dregg_d_value_dig(*n),
            WireValue::Sym(n) => dregg_d_value_sym(*n),
            WireValue::Record(fs) => {
                let mut acc = dregg_d_fieldlist_nil;
                for (name, fv) in fs.iter().rev() {
                    acc = dregg_d_fieldlist_cons(mk_string(name), build_value(fv), acc);
                }
                dregg_d_value_record(acc)
            }
        }
    }

    unsafe fn build_auth_w(a: &WireAuth) -> Obj {
        match a {
            WireAuth::Signature { pubkey, sig } => dregg_d_auth_signature(digest_low(pubkey), *sig),
            WireAuth::Proof {
                vk,
                proof,
                bound_action,
                bound_resource,
            } => dregg_d_auth_proof(digest_low(vk), *proof, *bound_action, *bound_resource),
            WireAuth::Breadstuff { token } => dregg_d_auth_breadstuff(*token),
            WireAuth::Bearer {
                deleg_msg,
                deleg_sig,
                stark,
            } => dregg_d_auth_bearer(digest_low(deleg_msg), *deleg_sig, *stark as u8),
            WireAuth::Unchecked => dregg_d_auth_unchecked,
            WireAuth::CapTpDelivered {
                intro_msg,
                sender_msg,
                intro_sig,
                sender_sig,
            } => dregg_d_auth_captp(
                digest_low(intro_msg),
                digest_low(sender_msg),
                *intro_sig,
                *sender_sig,
            ),
            WireAuth::Custom { kind_stmt, proof } => {
                dregg_d_auth_custom(digest_low(kind_stmt), *proof)
            }
            WireAuth::OneOf {
                candidates,
                proof_index,
            } => {
                let mut acc = dregg_d_authwlist_nil;
                for c in candidates.iter().rev() {
                    acc = dregg_d_authwlist_cons(build_auth_w(c), acc);
                }
                dregg_d_auth_oneof(acc, *proof_index)
            }
            WireAuth::Stealth {
                one_time_pk,
                ephemeral_pk,
                sig,
            } => dregg_d_auth_stealth(digest_low(one_time_pk), digest_low(ephemeral_pk), *sig),
            WireAuth::Token { issuer_key, sig } => dregg_d_auth_token(digest_low(issuer_key), *sig),
        }
    }

    /// The verified `liftAuthW` lowers every digest field (pubkey/vk/…) via `Int.ofNat` of the wire
    /// `Nat`. The JSON path carries the FULL 256-bit digest as 64-hex, but `parseHex32` reads it into
    /// a `Nat` and `stateOfWState`/`liftAuthW` only ever fold it as that `Nat` — and the gate's WHO
    /// leg the demos exercise compares the lifted statement to the proof. The kernel's `Nat` digest is
    /// the WHOLE hex as a big Nat; a `u64` low slice is what the JSON `to_hex32(u64)` demos use. To
    /// stay byte-identical to the JSON path for the credential leg we carry the SAME `Nat` the JSON
    /// parser would produce — i.e. the full 256-bit big-endian value. Since the builder takes a `u64`,
    /// we pass the low 64 bits, matching the demo/fixture digests (`Digest::from_u64`) the producer
    /// path uses; a full-width digest credential is a JSON-path-only feature until the builder widens.
    fn digest_low(d: &crate::marshal::Digest) -> u64 {
        u64::from_be_bytes(d.0[24..32].try_into().unwrap())
    }

    unsafe fn build_caveat_list(cs: &[WireCaveat]) -> Obj {
        let mut acc = dregg_d_caveatlist_nil;
        for c in cs.iter().rev() {
            acc = dregg_d_caveatlist_cons(
                dregg_d_mk_caveat(c.tier, c.cell, c.asset, mk_int(c.min)),
                acc,
            );
        }
        acc
    }

    unsafe fn build_action(a: &crate::marshal::WireAction) -> Obj {
        use crate::marshal::WireAction as A;
        match a {
            A::Balance {
                actor,
                src,
                dst,
                amt,
                asset,
            } => dregg_d_act_balance(*actor, *src, *dst, mk_int(*amt), *asset),
            A::Delegate {
                delegator,
                recipient,
                t,
            } => dregg_d_act_delegate(*delegator, *recipient, *t),
            A::Revoke { holder, t } => dregg_d_act_revoke(*holder, *t),
            A::Mint {
                actor,
                cell,
                asset,
                amt,
            } => dregg_d_act_mint(*actor, *cell, *asset, mk_int(*amt)),
            A::Burn {
                actor,
                cell,
                asset,
                amt,
            } => dregg_d_act_burn(*actor, *cell, *asset, mk_int(*amt)),
            A::SetField {
                actor,
                cell,
                field,
                v,
            } => dregg_d_act_setfield(*actor, *cell, mk_string(field), mk_int(*v)),
            A::Emit {
                actor,
                cell,
                topic,
                data,
            } => dregg_d_act_emit(*actor, *cell, mk_int(*topic), mk_int(*data)),
            A::IncNonce {
                actor,
                cell,
                new_nonce,
            } => dregg_d_act_incnonce(*actor, *cell, mk_int(*new_nonce)),
            A::SetPerms { actor, cell, perms } => {
                dregg_d_act_setperms(*actor, *cell, mk_int(*perms))
            }
            A::SetVk { actor, cell, vk } => dregg_d_act_setvk(*actor, *cell, mk_int(*vk)),
            A::Introduce {
                introducer,
                recipient,
                target,
            } => dregg_d_act_introduce(*introducer, *recipient, *target),
            A::DelegateAtten {
                delegator,
                recipient,
                target,
                keep,
            } => dregg_d_act_delatten(*delegator, *recipient, *target, build_auth_list(keep)),
            A::Attenuate { actor, idx, keep } => {
                dregg_d_act_atten(*actor, *idx, build_auth_list(keep))
            }
            A::RevokeDelegation { holder, target } => dregg_d_act_revdel(*holder, *target),
            A::Exercise {
                actor,
                target,
                inner,
            } => {
                let mut acc = dregg_d_actlist_nil;
                for ia in inner.iter().rev() {
                    acc = dregg_d_actlist_cons(build_action(ia), acc);
                }
                dregg_d_act_exercise(*actor, *target, acc)
            }
            A::CreateCell { actor, new_cell } => dregg_d_act_createcell(*actor, *new_cell),
            A::CreateCellFromFactory {
                actor,
                new_cell,
                vk,
            } => dregg_d_act_createcellfactory(*actor, *new_cell, mk_int(*vk)),
            A::Spawn {
                actor,
                child,
                target,
            } => dregg_d_act_spawn(*actor, *child, *target),
            A::BridgeMint {
                actor,
                cell,
                asset,
                value,
            } => dregg_d_act_bmint(*actor, *cell, *asset, mk_int(*value)),
            A::NoteSpend {
                nf,
                actor,
                spend_proof,
            } => dregg_d_act_nspend(*nf, *actor, *spend_proof as u8),
            A::NoteCreate { cm, actor } => dregg_d_act_ncreate(*cm, *actor),
            A::MakeSovereign { actor, cell } => dregg_d_act_sov(*actor, *cell),
            A::Refusal { actor, cell } => dregg_d_act_refusal(*actor, *cell),
            A::ReceiptArchive { actor, cell } => dregg_d_act_rarchive(*actor, *cell),
            A::CellSeal { actor, cell } => dregg_d_act_cseal(*actor, *cell),
            A::CellUnseal { actor, cell } => dregg_d_act_cunseal(*actor, *cell),
            A::CellDestroy {
                actor,
                cell,
                cert_hash,
            } => dregg_d_act_cdestroy(*actor, *cell, *cert_hash),
            A::RefreshDelegation { actor, child } => dregg_d_act_rdel(*actor, *child),
            A::PipelinedSend { actor } => dregg_d_act_psend(*actor),
            A::HeapWrite {
                actor,
                target,
                addr,
                value,
                new_root,
            } => dregg_d_act_hwrite(
                *actor,
                *target,
                mk_int(*addr),
                mk_int(*value),
                mk_int(*new_root),
            ),
        }
    }

    unsafe fn build_forest(f: &WForest) -> Obj {
        let auth = build_auth_w(&f.auth);
        let caveats = build_caveat_list(&f.caveats);
        let action = build_action(&f.action);
        let mut kids = dregg_d_childlist_nil;
        for c in f.children.iter().rev() {
            let child = dregg_d_mk_wchild(
                c.holder,
                build_auth_list(&c.keep),
                build_cap(&c.parent_cap),
                build_forest(&c.sub),
            );
            kids = dregg_d_childlist_cons(child, kids);
        }
        dregg_d_mk_wforest(auth, caveats, action, kids)
    }

    unsafe fn build_state(s: &WireState) -> Obj {
        let mut cells = dregg_d_cells_nil;
        for (id, v) in s.cells.iter().rev() {
            cells = dregg_d_cells_cons(*id, build_value(v), cells);
        }
        let mut caps = dregg_d_caps_nil;
        for (h, cl) in s.caps.iter().rev() {
            caps = dregg_d_caps_cons(*h, build_cap_list(cl), caps);
        }
        let mut bal = dregg_d_bal_nil;
        for (cell, asset, amt) in s.bal.iter().rev() {
            bal = dregg_d_bal_cons(*cell, *asset, mk_int(*amt), bal);
        }
        let nullifiers = build_nat_list(&s.nullifiers);
        let commitments = build_nat_list(&s.commitments);
        let revoked = build_nat_list(&s.revoked);
        let lifecycle = build_cellnats(&s.lifecycle);
        let death_cert = build_cellnats(&s.death_cert);
        let delegate = build_cellnats(&s.delegate);
        dregg_d_mk_wstate(
            cells,
            caps,
            bal,
            nullifiers,
            commitments,
            revoked,
            lifecycle,
            death_cert,
            delegate,
        )
    }

    unsafe fn build_nat_list(ns: &[u64]) -> Obj {
        let mut acc = dregg_d_natlist_nil;
        for n in ns.iter().rev() {
            acc = dregg_d_natlist_cons(dregg_d_nat_of_u64(*n), acc);
        }
        acc
    }

    unsafe fn build_cellnats(es: &[(u64, u64)]) -> Obj {
        let mut acc = dregg_d_cellnats_nil;
        for (c, v) in es.iter().rev() {
            acc = dregg_d_cellnats_cons(*c, *v, acc);
        }
        acc
    }

    // ---- readers ----

    /// Read a `Value`. BORROWS `v` (net-zero on its refcount): every reader call consumes a ref, so
    /// we `inc` exactly once before each one. The caller retains ownership of `v` and frees it.
    unsafe fn read_value(v: Obj) -> WireValue {
        dregg_rt_inc(v);
        let tag = dregg_d_value_tag(v); // consumes the inc'd ref → net zero on v
        match tag {
            0 => {
                dregg_rt_inc(v);
                WireValue::Int(read_owned_int(dregg_d_value_int_get(v))) // int_get consumes inc'd
            }
            1 => {
                dregg_rt_inc(v);
                WireValue::Dig(dregg_d_value_nat_get(v))
            }
            2 => {
                dregg_rt_inc(v);
                WireValue::Sym(dregg_d_value_nat_get(v))
            }
            _ => {
                dregg_rt_inc(v);
                let fs = dregg_d_value_record_get(v); // consumes inc'd; returns OWNED field list
                let len = {
                    dregg_rt_inc(fs);
                    dregg_d_fieldlist_len(fs)
                };
                let mut out = Vec::with_capacity(len as usize);
                for i in 0..len {
                    let name = {
                        dregg_rt_inc(fs);
                        read_owned_string(dregg_d_fieldlist_name(fs, i))
                    };
                    let fv = {
                        dregg_rt_inc(fs);
                        let o = dregg_d_fieldlist_val(fs, i);
                        let r = read_value(o);
                        dregg_rt_dec(o);
                        r
                    };
                    out.push((name, fv));
                }
                dregg_rt_dec(fs);
                WireValue::Record(out)
            }
        }
    }

    unsafe fn read_auth_list(xs: Obj) -> Vec<Auth> {
        dregg_rt_inc(xs);
        let len = dregg_d_authlist_len(xs);
        let mut out = Vec::with_capacity(len as usize);
        for i in 0..len {
            dregg_rt_inc(xs);
            let tag = dregg_d_authlist_get(xs, i);
            out.push(auth_of_u8(tag));
        }
        out
    }

    fn auth_of_u8(t: u8) -> Auth {
        match t {
            0 => Auth::Read,
            1 => Auth::Write,
            2 => Auth::Grant,
            3 => Auth::Call,
            4 => Auth::Reply,
            5 => Auth::Reset,
            6 => Auth::Control,
            _ => Auth::Notify,
        }
    }

    unsafe fn read_cap(c: Obj) -> Cap {
        dregg_rt_inc(c);
        let tag = dregg_d_cap_tag(c);
        match tag {
            0 => Cap::Null,
            2 => {
                dregg_rt_inc(c);
                let t = dregg_d_cap_target(c);
                Cap::Node(t)
            }
            _ => {
                dregg_rt_inc(c);
                let t = dregg_d_cap_target(c);
                dregg_rt_inc(c);
                let rights = {
                    let o = dregg_d_cap_rights(c);
                    let r = read_auth_list(o);
                    dregg_rt_dec(o);
                    r
                };
                Cap::Endpoint(t, rights)
            }
        }
    }

    unsafe fn read_post_state(w: Obj) -> WireState {
        // cells
        let cells_o = {
            dregg_rt_inc(w);
            dregg_d_st_cells(w)
        };
        let n = {
            dregg_rt_inc(cells_o);
            dregg_d_cells_len(cells_o)
        };
        let mut cells = Vec::with_capacity(n as usize);
        for i in 0..n {
            let id = {
                dregg_rt_inc(cells_o);
                dregg_d_cells_id(cells_o, i)
            };
            let v = {
                dregg_rt_inc(cells_o);
                let o = dregg_d_cells_val(cells_o, i);
                let r = read_value(o);
                dregg_rt_dec(o);
                r
            };
            cells.push((id, v));
        }
        dregg_rt_dec(cells_o);

        // caps
        let caps_o = {
            dregg_rt_inc(w);
            dregg_d_st_caps(w)
        };
        let cn = {
            dregg_rt_inc(caps_o);
            dregg_d_caps_len(caps_o)
        };
        let mut caps = Vec::with_capacity(cn as usize);
        for i in 0..cn {
            let h = {
                dregg_rt_inc(caps_o);
                dregg_d_caps_holder(caps_o, i)
            };
            let cl_o = {
                dregg_rt_inc(caps_o);
                dregg_d_caps_clist(caps_o, i)
            };
            let cll = {
                dregg_rt_inc(cl_o);
                dregg_d_caplist_len(cl_o)
            };
            let mut cl = Vec::with_capacity(cll as usize);
            for j in 0..cll {
                dregg_rt_inc(cl_o);
                let cap_o = dregg_d_caplist_get(cl_o, j);
                cl.push(read_cap(cap_o));
                dregg_rt_dec(cap_o);
            }
            dregg_rt_dec(cl_o);
            caps.push((h, cl));
        }
        dregg_rt_dec(caps_o);

        // bal
        let bal_o = {
            dregg_rt_inc(w);
            dregg_d_st_bal(w)
        };
        let bn = {
            dregg_rt_inc(bal_o);
            dregg_d_bal_len(bal_o)
        };
        let mut bal = Vec::with_capacity(bn as usize);
        for i in 0..bn {
            let cell = {
                dregg_rt_inc(bal_o);
                dregg_d_bal_cell(bal_o, i)
            };
            let asset = {
                dregg_rt_inc(bal_o);
                dregg_d_bal_asset(bal_o, i)
            };
            let amt = {
                dregg_rt_inc(bal_o);
                read_owned_int(dregg_d_bal_amt(bal_o, i))
            };
            bal.push((cell, asset, amt));
        }
        dregg_rt_dec(bal_o);

        let nullifiers = read_nat_list_field(w, StField::Nullifiers);
        let commitments = read_nat_list_field(w, StField::Commitments);
        let revoked = read_nat_list_field(w, StField::Revoked);
        let lifecycle = read_cellnats_field(w, StField::Lifecycle);
        let death_cert = read_cellnats_field(w, StField::DeathCert);
        let delegate = read_cellnats_field(w, StField::Delegate);

        WireState {
            cells,
            caps,
            bal,
            escrows: vec![],
            nullifiers,
            commitments,
            queues: vec![],
            swiss: vec![],
            revoked,
            lifecycle,
            death_cert,
            delegate,
        }
    }

    enum StField {
        Nullifiers,
        Commitments,
        Revoked,
        Lifecycle,
        DeathCert,
        Delegate,
    }

    unsafe fn read_nat_list_field(w: Obj, f: StField) -> Vec<u64> {
        let o = {
            dregg_rt_inc(w);
            match f {
                StField::Nullifiers => dregg_d_st_nullifiers(w),
                StField::Commitments => dregg_d_st_commitments(w),
                StField::Revoked => dregg_d_st_revoked(w),
                _ => unreachable!(),
            }
        };
        let n = {
            dregg_rt_inc(o);
            dregg_d_natlist_len(o)
        };
        let mut out = Vec::with_capacity(n as usize);
        for i in 0..n {
            dregg_rt_inc(o);
            out.push(dregg_d_natlist_get(o, i));
        }
        dregg_rt_dec(o);
        out
    }

    unsafe fn read_cellnats_field(w: Obj, f: StField) -> Vec<(u64, u64)> {
        let o = {
            dregg_rt_inc(w);
            match f {
                StField::Lifecycle => dregg_d_st_lifecycle(w),
                StField::DeathCert => dregg_d_st_deathcert(w),
                StField::Delegate => dregg_d_st_delegate(w),
                _ => unreachable!(),
            }
        };
        let n = {
            dregg_rt_inc(o);
            dregg_d_cellnats_len(o)
        };
        let mut out = Vec::with_capacity(n as usize);
        for i in 0..n {
            let c = {
                dregg_rt_inc(o);
                dregg_d_cellnats_cell(o, i)
            };
            let v = {
                dregg_rt_inc(o);
                dregg_d_cellnats_val(o, i)
            };
            out.push((c, v));
        }
        dregg_rt_dec(o);
        out
    }

    /// THE no-copy round-trip: build → run `execDirect` → read. Single-threaded (the existing ST
    /// contract); no object escapes the call; the result is fully drained before its refs are
    /// dropped. Returns the decoded [`ShadowState`] (verdict + post-state), matching the JSON path.
    pub(super) fn run_direct(
        host: &WireHostCtx,
        state: &WireState,
        turn_root: &WForest,
        turn: &WireTurnHdr,
    ) -> ShadowState {
        unsafe {
            let dbg = std::env::var("DREGG_DIRECT_DEBUG").as_deref() == Ok("1");
            macro_rules! step {
                ($s:expr) => {
                    if dbg {
                        eprintln!("[direct] {}", $s);
                    }
                };
            }
            // Env-gated sub-phase profiler: times (b) IN tree construction, (c) the execDirect call,
            // (d)+(e) reading the OUT tree back into the WireState mirror. Off (zero cost) unless
            // DREGG_FFI_PROFILE=1. Phase (a) "build the Rust mirror" is measured at the call site in
            // exec-lean (`ledger_to_wire_state`), since this fn already receives the mirror.
            let prof = std::env::var("DREGG_FFI_PROFILE").as_deref() == Ok("1");
            let t_in0 = if prof {
                Some(std::time::Instant::now())
            } else {
                None
            };
            step!("build host");
            // Build the three boundary values (owned).
            let host_o = dregg_d_mk_whostctx(
                host.now,
                host.block_height,
                build_nat_list(&host.frozen),
                host.stored_head,
                host.budget,
            );
            step!("build state");
            let state_o = build_state(state);
            step!("build forest");
            let root_o = build_forest(turn_root);
            step!("build turn");
            let turn_o = dregg_d_mk_wturn(
                turn.agent,
                turn.nonce,
                mk_int(turn.fee),
                turn.valid_until,
                turn.block_height,
                turn.prev_low,
                root_o,
            );
            let t_exec0 = if prof {
                Some(std::time::Instant::now())
            } else {
                None
            };

            step!("exec");
            // Run the IDENTICAL proved executor on the built values (consumes host_o/state_o/turn_o).
            let res = dregg_exec_full_forest_auth_direct(host_o, state_o, turn_o);
            step!("read result");
            let t_read0 = if prof {
                Some(std::time::Instant::now())
            } else {
                None
            };

            // Drain the WHOLE result while it is still alive (no escaping GC object).
            let status_code = {
                dregg_rt_inc(res);
                dregg_d_res_status(res)
            };
            let loglen = {
                dregg_rt_inc(res);
                dregg_d_res_loglen(res)
            };
            let reason_code = {
                dregg_rt_inc(res);
                dregg_d_res_reason(res)
            };
            let post_o = {
                dregg_rt_inc(res);
                dregg_d_res_state(res)
            };
            let post = read_post_state(post_o);
            dregg_rt_dec(post_o);
            dregg_rt_dec(res);

            if prof {
                let (in0, ex0, rd0) = (t_in0.unwrap(), t_exec0.unwrap(), t_read0.unwrap());
                let now = std::time::Instant::now();
                super::prof_accum(
                    (ex0 - in0).as_secs_f64(),
                    (rd0 - ex0).as_secs_f64(),
                    (now - rd0).as_secs_f64(),
                );
            }

            let status = match status_code {
                2 => Some(TurnStatus::BodyCommitted),
                1 => Some(TurnStatus::PrologueCommittedBodyFailed),
                _ => Some(TurnStatus::Rejected),
            };
            let committed = status_code == 2;
            ShadowState {
                verdict: ShadowVerdict {
                    committed,
                    loglen,
                    status,
                    // The no-copy direct ABI now returns the admission-reason code (the same
                    // `AdmissionReason.reasonCode` the JSON-wire path carries — `dregg_d_res_reason`),
                    // so the legible refusal "why" is byte-identical across both FFI paths.
                    reason: crate::AdmissionReason::from_code(reason_code),
                    divergence_note: None,
                },
                state: post,
            }
        }
    }

    /// MEASUREMENT: time `iters` round trips through the BARE identity export
    /// (`dregg_ffi_identity`) — build the same `WState` once, then loop: inc the built object,
    /// call across into Lean (which hands it straight back), and dec the returned ref. Returns the
    /// median per-call seconds. This isolates the pure cross-into-Lean + region/refcount cost with
    /// NO executor work. Single-threaded (the ST contract); the built `WState` is reused across
    /// iters (its construction is NOT timed — only the boundary crossing is).
    pub(super) fn identity_floor_median(state: &WireState, iters: u32) -> f64 {
        unsafe {
            let state_o = build_state(state);
            // warm (lazy first-call init must not contaminate)
            for _ in 0..3 {
                dregg_rt_inc(state_o);
                let r = dregg_ffi_identity(state_o);
                dregg_rt_dec(r);
            }
            let mut samples = Vec::with_capacity(iters as usize);
            for _ in 0..iters {
                let t0 = std::time::Instant::now();
                dregg_rt_inc(state_o);
                let r = dregg_ffi_identity(state_o);
                core::hint::black_box(r);
                dregg_rt_dec(r);
                samples.push(t0.elapsed().as_secs_f64());
            }
            dregg_rt_dec(state_o);
            samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
            samples[samples.len() / 2]
        }
    }

    /// MEASUREMENT: run the PROFILED executor export once on freshly-built boundary values. The Lean
    /// side prints its per-phase `DREGG_LEAN_PROFILE` line (when that env var is `1`) and returns the
    /// identical `WStatusResult`, which we drain exactly like `run_direct` (so the call is faithful).
    /// Used by the bench under a profiling loop; not on the production path.
    pub(super) fn run_direct_profiled(
        host: &WireHostCtx,
        state: &WireState,
        turn_root: &WForest,
        turn: &WireTurnHdr,
    ) -> ShadowState {
        unsafe {
            let host_o = dregg_d_mk_whostctx(
                host.now,
                host.block_height,
                build_nat_list(&host.frozen),
                host.stored_head,
                host.budget,
            );
            let state_o = build_state(state);
            let root_o = build_forest(turn_root);
            let turn_o = dregg_d_mk_wturn(
                turn.agent,
                turn.nonce,
                mk_int(turn.fee),
                turn.valid_until,
                turn.block_height,
                turn.prev_low,
                root_o,
            );
            let res = dregg_exec_full_forest_auth_direct_profiled(host_o, state_o, turn_o);
            let status_code = {
                dregg_rt_inc(res);
                dregg_d_res_status(res)
            };
            let loglen = {
                dregg_rt_inc(res);
                dregg_d_res_loglen(res)
            };
            let reason_code = {
                dregg_rt_inc(res);
                dregg_d_res_reason(res)
            };
            let post_o = {
                dregg_rt_inc(res);
                dregg_d_res_state(res)
            };
            let post = read_post_state(post_o);
            dregg_rt_dec(post_o);
            dregg_rt_dec(res);
            let status = match status_code {
                2 => Some(TurnStatus::BodyCommitted),
                1 => Some(TurnStatus::PrologueCommittedBodyFailed),
                _ => Some(TurnStatus::Rejected),
            };
            let committed = status_code == 2;
            ShadowState {
                verdict: ShadowVerdict {
                    committed,
                    loglen,
                    status,
                    // The no-copy direct ABI now returns the admission-reason code (the same
                    // `AdmissionReason.reasonCode` the JSON-wire path carries — `dregg_d_res_reason`),
                    // so the legible refusal "why" is byte-identical across both FFI paths.
                    reason: crate::AdmissionReason::from_code(reason_code),
                    divergence_note: None,
                },
                state: post,
            }
        }
    }
}

/// The Turn ENVELOPE fields the direct boundary needs (the root forest is passed separately so the
/// recursive build is shared with the children). `prev_low` is the low-64 of the `prev` digest — the
/// same `Nat` the JSON `parseHex32` folds for the demo/fixture chain heads (`Digest::from_u64`).
#[derive(Debug, Clone)]
pub struct WireTurnHdr {
    pub agent: u64,
    pub nonce: u64,
    pub fee: i128,
    pub valid_until: u64,
    pub block_height: u64,
    pub prev_low: u64,
}

/// Run the verified executor over ALREADY-EXTRACTED wire values via the no-copy `lean_object*`
/// boundary (no JSON in either direction). Requires [`direct_available`]; returns `Err` otherwise so
/// the caller falls back to the JSON path.
#[cfg(dregg_direct_present)]
pub fn shadow_exec_direct(
    host: &WireHostCtx,
    state: &WireState,
    turn_root: &WForest,
    turn: &WireTurnHdr,
) -> Result<ShadowState, String> {
    crate::lean_available()
        .then_some(())
        .ok_or_else(|| "lean runtime not initialised".to_string())?;
    Ok(imp::run_direct(host, state, turn_root, turn))
}

#[cfg(not(dregg_direct_present))]
pub fn shadow_exec_direct(
    _host: &WireHostCtx,
    _state: &WireState,
    _turn_root: &WForest,
    _turn: &WireTurnHdr,
) -> Result<ShadowState, String> {
    Err(
        "dregg_exec_full_forest_auth_direct not exported by the linked archive (rebuild to enable)"
            .into(),
    )
}

/// MEASUREMENT-ONLY: median per-call seconds of the BARE FFI-into-Lean floor (`dregg_ffi_identity`)
/// over `iters` crossings on the same built `WState`. Isolates the pure cross-into-Lean +
/// region/refcount cost (no executor work). For `perf/benches/lean_ffi_turn.rs`. `Err` if the
/// archive lacks the export or the runtime is uninitialised.
#[cfg(dregg_direct_present)]
pub fn identity_floor_median(state: &WireState, iters: u32) -> Result<f64, String> {
    crate::lean_available()
        .then_some(())
        .ok_or_else(|| "lean runtime not initialised".to_string())?;
    Ok(imp::identity_floor_median(state, iters))
}

#[cfg(not(dregg_direct_present))]
pub fn identity_floor_median(_state: &WireState, _iters: u32) -> Result<f64, String> {
    Err("dregg_ffi_identity not exported by the linked archive (rebuild to enable)".into())
}

/// MEASUREMENT-ONLY: run the PROFILED executor export once (Lean prints its per-phase
/// `DREGG_LEAN_PROFILE` line when that env var is `1`); returns the same `ShadowState` the
/// production path would. For `perf/benches/lean_ffi_turn.rs`.
#[cfg(dregg_direct_present)]
pub fn shadow_exec_direct_profiled(
    host: &WireHostCtx,
    state: &WireState,
    turn_root: &WForest,
    turn: &WireTurnHdr,
) -> Result<ShadowState, String> {
    crate::lean_available()
        .then_some(())
        .ok_or_else(|| "lean runtime not initialised".to_string())?;
    Ok(imp::run_direct_profiled(host, state, turn_root, turn))
}

#[cfg(not(dregg_direct_present))]
pub fn shadow_exec_direct_profiled(
    _host: &WireHostCtx,
    _state: &WireState,
    _turn_root: &WForest,
    _turn: &WireTurnHdr,
) -> Result<ShadowState, String> {
    Err("dregg_exec_full_forest_auth_direct_profiled not exported by the linked archive".into())
}
