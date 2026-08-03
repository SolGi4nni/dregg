//! **THE PICKLES PROOF WIRE ENCODER** — one `PicklesProofProofsVerified2ReprStableV2`, two
//! grammars.
//!
//! Both halves were written and judged in `src/bin/pickles_proof_wire.rs`; they live here so a
//! SECOND consumer — `src/marshal.rs`, which turns a kimchi `ProverProof` into that record — can
//! emit through exactly the encoder that seven real block proofs round-trip byte-identically
//! through. Nothing in this module changed when it moved; the bin's gate re-runs on it.
//!
//! * **binprot** — a block's `protocolStateProof`, the p2p wire, a zkApp account update.
//! * **sexp (base64'd)** — o1js `Proof.toJSON().proof`, read by `Pickles.proofOfBase64`.
//!
//! See the bin's module header for the grammar, the sexplib separator rule, and why openmina's
//! own `SexpOf` cannot be used for the o1js half.

use std::fmt::Write as _;

use mina_p2p_messages::array::ArrayN16;
use mina_p2p_messages::bigint::BigInt;
use mina_p2p_messages::binprot::BinProtWrite;
use mina_p2p_messages::v2::*;

// ───────────────────────────── the sexp printer ─────────────────────────────
//
// Written against the grammar observed in o1js's own proof (see the module header). Every
// function appends to one `String`; there is no intermediate tree, so the output is exactly the
// concatenation below and nothing can silently reorder a record.

/// ⚑ **SEXPLIB'S SEPARATOR RULE, which is not "join with a space".**
///
/// `Sexp.to_string` is `to_string_mach`, whose `pp_mach_internal` carries a `may_need_space` flag:
/// it is set only after printing a BARE (unescaped) atom, and a space is emitted only when the
/// next thing to print is ALSO a bare atom. A list resets it to `false` on both entry and exit.
/// So `(a b)` gets a space, `(a(b))` does not, `((a)(b))` does not, and `(a"\016")` does not.
///
/// Every atom this file emits is bare except the `Domain_log2` char, which is emitted already
/// quoted. A bare atom here never contains `)` or `"`, so the flag is recoverable from the
/// boundary characters: space iff the left side did not end a list-or-quote and the right side
/// does not begin one.
///
/// This was NOT free. Joining lists with a space parsed fine — `Pickles.proofOfBase64` accepted
/// all eight objects — and diverged from Mina's own printer at sexp offset 502, first seen when
/// the gate re-printed our input with `proofToBase64` and compared. A parse-only gate would
/// never have shown it.
fn glue(out: &mut String, next: &str) {
    let lhs_bare = !out.ends_with(')') && !out.ends_with('"') && !out.is_empty();
    let rhs_bare = !next.starts_with('(') && !next.starts_with('"');
    if lhs_bare && rhs_bare {
        out.push(' ');
    }
    out.push_str(next);
}

/// Concatenate sexp fragments under [`glue`].
fn join(items: &[String]) -> String {
    let mut s = String::new();
    for it in items {
        glue(&mut s, it);
    }
    s
}

/// `(name value)` — one record field.
fn field(out: &mut String, name: &str, value: &str) {
    out.push('(');
    out.push_str(name);
    glue(out, value);
    out.push(')');
}

/// `BigInt` → `0x` + 64 UPPERCASE hex, big-endian.
fn s_bigint(v: &BigInt) -> String {
    let le = v.to_bytes();
    let mut s = String::with_capacity(66);
    s.push_str("0x");
    for b in le.iter().rev() {
        let _ = write!(s, "{b:02X}");
    }
    s
}

/// A curve point / any 2-tuple of `BigInt` → `(a b)`.
fn s_pair(p: &(BigInt, BigInt)) -> String {
    format!("({})", join(&[s_bigint(&p.0), s_bigint(&p.1)]))
}

/// `Limb_vector.Constant.Hex64` → 16 LOWERCASE hex, no prefix.
fn s_hex64(v: &LimbVectorConstantHex64StableV1) -> String {
    format!("{:016x}", v.0.as_u64())
}

/// A challenge: `Scalar_challenge.t = { inner : Hex64 * Hex64 }` → `((inner(l0 l1)))`.
fn s_challenge(
    c: &PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2AChallenge,
) -> String {
    let inner = format!(
        "({})",
        join(&[s_hex64(&c.inner.0[0]), s_hex64(&c.inner.0[1])])
    );
    let mut r = String::from("(");
    field(&mut r, "inner", &inner);
    r.push(')');
    r
}

/// A bulletproof challenge: `{ prechallenge : Scalar_challenge.t }`.
fn s_bp_challenge(
    c: &PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2A,
) -> String {
    let mut r = String::from("(");
    field(&mut r, "prechallenge", &s_challenge(&c.prechallenge));
    r.push(')');
    r
}

fn s_list(items: &[String]) -> String {
    format!("({})", join(items))
}

/// `Option` — `()` for None, `(x)` for Some. This is the shape every absent selector takes.
fn s_opt(v: Option<String>) -> String {
    match v {
        None => "()".to_string(),
        Some(s) => format!("({s})"),
    }
}

fn s_bool(b: bool) -> String {
    if b {
        "true".into()
    } else {
        "false".into()
    }
}

/// The 4-limb `Digest.Constant` → `(l0 l1 l2 l3)`.
fn s_digest(d: &CompositionTypesDigestConstantStableV1) -> String {
    s_list(&d.0 .0.iter().map(s_hex64).collect::<Vec<_>>())
}

fn s_proofs_verified(p: &PicklesBaseProofsVerifiedStableV1) -> String {
    match p {
        PicklesBaseProofsVerifiedStableV1::N0 => "N0".into(),
        PicklesBaseProofsVerifiedStableV1::N1 => "N1".into(),
        PicklesBaseProofsVerifiedStableV1::N2 => "N2".into(),
    }
}

/// `Domain_log2` is an OCaml CHAR. OCaml's sexp printer emits it as a QUOTED STRING with a
/// three-digit decimal escape — `"\016"` for 14 — which is why `field` suppresses the space.
fn s_char(c: &CompositionTypesBranchDataDomainLog2StableV1) -> String {
    let b = c.0.as_u8();
    // OCaml `Char.escaped` prints printable ASCII bare and everything else as `\DDD`.
    if b.is_ascii_graphic() && b != b'"' && b != b'\\' {
        format!("\"{}\"", b as char)
    } else {
        format!("\"\\{b:03}\"")
    }
}

fn s_plonk(
    p: &PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonk,
) -> String {
    let mut r = String::from("(");
    field(&mut r, "alpha", &s_challenge(&p.alpha));
    field(
        &mut r,
        "beta",
        &format!(
            "({})",
            join(&[s_hex64(&p.beta.0[0]), s_hex64(&p.beta.0[1])])
        ),
    );
    field(
        &mut r,
        "gamma",
        &format!(
            "({})",
            join(&[s_hex64(&p.gamma.0[0]), s_hex64(&p.gamma.0[1])])
        ),
    );
    field(&mut r, "zeta", &s_challenge(&p.zeta));
    field(
        &mut r,
        "joint_combiner",
        &s_opt(p.joint_combiner.as_ref().map(s_challenge)),
    );
    let f = &p.feature_flags;
    let mut ff = String::from("(");
    field(&mut ff, "range_check0", &s_bool(f.range_check0));
    field(&mut ff, "range_check1", &s_bool(f.range_check1));
    field(&mut ff, "foreign_field_add", &s_bool(f.foreign_field_add));
    field(&mut ff, "foreign_field_mul", &s_bool(f.foreign_field_mul));
    field(&mut ff, "xor", &s_bool(f.xor));
    field(&mut ff, "rot", &s_bool(f.rot));
    field(&mut ff, "lookup", &s_bool(f.lookup));
    field(&mut ff, "runtime_tables", &s_bool(f.runtime_tables));
    ff.push(')');
    field(&mut r, "feature_flags", &ff);
    r.push(')');
    r
}

fn s_deferred_values(
    d: &PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValues,
) -> String {
    let mut r = String::from("(");
    field(&mut r, "plonk", &s_plonk(&d.plonk));
    field(
        &mut r,
        "bulletproof_challenges",
        &s_list(
            &d.bulletproof_challenges
                .0
                .iter()
                .map(s_bp_challenge)
                .collect::<Vec<_>>(),
        ),
    );
    let mut bd = String::from("(");
    field(
        &mut bd,
        "proofs_verified",
        &s_proofs_verified(&d.branch_data.proofs_verified),
    );
    field(&mut bd, "domain_log2", &s_char(&d.branch_data.domain_log2));
    bd.push(')');
    field(&mut r, "branch_data", &bd);
    r.push(')');
    r
}

fn s_proof_state(p: &PicklesProofProofsVerified2ReprStableV2StatementProofState) -> String {
    let mut r = String::from("(");
    field(
        &mut r,
        "deferred_values",
        &s_deferred_values(&p.deferred_values),
    );
    field(
        &mut r,
        "sponge_digest_before_evaluations",
        &s_digest(&p.sponge_digest_before_evaluations),
    );
    let m = &p.messages_for_next_wrap_proof;
    let mut mw = String::from("(");
    field(
        &mut mw,
        "challenge_polynomial_commitment",
        &s_pair(&m.challenge_polynomial_commitment),
    );
    field(
        &mut mw,
        "old_bulletproof_challenges",
        &s_list(
            &m.old_bulletproof_challenges
                .0
                .iter()
                .map(|v| s_list(&v.0 .0.iter().map(s_bp_challenge).collect::<Vec<_>>()))
                .collect::<Vec<_>>(),
        ),
    );
    mw.push(')');
    field(&mut r, "messages_for_next_wrap_proof", &mw);
    r.push(')');
    r
}

fn s_messages_for_next_step_proof(
    m: &PicklesProofProofsVerified2ReprStableV2MessagesForNextStepProof,
) -> String {
    let mut r = String::from("(");
    // ⚑ `app_state : unit` on the wire. The verifier SUBSTITUTES the block's state hash; the
    // proof itself carries nothing there. Printed `()`.
    field(&mut r, "app_state", "()");
    field(
        &mut r,
        "challenge_polynomial_commitments",
        &s_list(
            &m.challenge_polynomial_commitments
                .iter()
                .map(s_pair)
                .collect::<Vec<_>>(),
        ),
    );
    field(
        &mut r,
        "old_bulletproof_challenges",
        &s_list(
            &m.old_bulletproof_challenges
                .iter()
                .map(|v| s_list(&v.0.iter().map(s_bp_challenge).collect::<Vec<_>>()))
                .collect::<Vec<_>>(),
        ),
    );
    r.push(')');
    r
}

/// One chunked evaluation point: `(ArrayN16<BigInt>, ArrayN16<BigInt>)` → `((z…)(zω…))`.
fn s_evalpair(p: &(ArrayN16<BigInt>, ArrayN16<BigInt>)) -> String {
    format!(
        "({})",
        join(&[
            s_list(&p.0.iter().map(s_bigint).collect::<Vec<_>>()),
            s_list(&p.1.iter().map(s_bigint).collect::<Vec<_>>())
        ])
    )
}

fn s_prev_evals_evals(p: &PicklesProofProofsVerified2ReprStableV2PrevEvalsEvalsEvals) -> String {
    let mut r = String::from("(");
    let arr = |xs: &[(ArrayN16<BigInt>, ArrayN16<BigInt>)]| {
        s_list(&xs.iter().map(s_evalpair).collect::<Vec<_>>())
    };
    field(&mut r, "w", &arr(&p.w.0));
    field(&mut r, "coefficients", &arr(&p.coefficients.0));
    field(&mut r, "z", &s_evalpair(&p.z));
    field(&mut r, "s", &arr(&p.s.0));
    field(&mut r, "generic_selector", &s_evalpair(&p.generic_selector));
    field(
        &mut r,
        "poseidon_selector",
        &s_evalpair(&p.poseidon_selector),
    );
    field(
        &mut r,
        "complete_add_selector",
        &s_evalpair(&p.complete_add_selector),
    );
    field(&mut r, "mul_selector", &s_evalpair(&p.mul_selector));
    field(&mut r, "emul_selector", &s_evalpair(&p.emul_selector));
    field(
        &mut r,
        "endomul_scalar_selector",
        &s_evalpair(&p.endomul_scalar_selector),
    );
    let o = |x: &Option<(ArrayN16<BigInt>, ArrayN16<BigInt>)>| s_opt(x.as_ref().map(s_evalpair));
    field(
        &mut r,
        "range_check0_selector",
        &o(&p.range_check0_selector),
    );
    field(
        &mut r,
        "range_check1_selector",
        &o(&p.range_check1_selector),
    );
    field(
        &mut r,
        "foreign_field_add_selector",
        &o(&p.foreign_field_add_selector),
    );
    field(
        &mut r,
        "foreign_field_mul_selector",
        &o(&p.foreign_field_mul_selector),
    );
    field(&mut r, "xor_selector", &o(&p.xor_selector));
    field(&mut r, "rot_selector", &o(&p.rot_selector));
    field(&mut r, "lookup_aggregation", &o(&p.lookup_aggregation));
    field(&mut r, "lookup_table", &o(&p.lookup_table));
    field(
        &mut r,
        "lookup_sorted",
        &s_list(&p.lookup_sorted.0.iter().map(o).collect::<Vec<_>>()),
    );
    field(&mut r, "runtime_lookup_table", &o(&p.runtime_lookup_table));
    field(
        &mut r,
        "runtime_lookup_table_selector",
        &o(&p.runtime_lookup_table_selector),
    );
    field(&mut r, "xor_lookup_selector", &o(&p.xor_lookup_selector));
    field(
        &mut r,
        "lookup_gate_lookup_selector",
        &o(&p.lookup_gate_lookup_selector),
    );
    field(
        &mut r,
        "range_check_lookup_selector",
        &o(&p.range_check_lookup_selector),
    );
    field(
        &mut r,
        "foreign_field_mul_lookup_selector",
        &o(&p.foreign_field_mul_lookup_selector),
    );
    r.push(')');
    r
}

fn s_wire_proof(p: &PicklesWrapWireProofStableV1) -> String {
    let mut r = String::from("(");
    let mut c = String::from("(");
    field(
        &mut c,
        "w_comm",
        &s_list(
            &p.commitments
                .w_comm
                .0
                .iter()
                .map(s_pair)
                .collect::<Vec<_>>(),
        ),
    );
    field(&mut c, "z_comm", &s_pair(&p.commitments.z_comm));
    field(
        &mut c,
        "t_comm",
        &s_list(
            &p.commitments
                .t_comm
                .0
                .iter()
                .map(s_pair)
                .collect::<Vec<_>>(),
        ),
    );
    c.push(')');
    field(&mut r, "commitments", &c);

    let e = &p.evaluations;
    let mut ev = String::from("(");
    field(
        &mut ev,
        "w",
        &s_list(&e.w.0.iter().map(s_pair).collect::<Vec<_>>()),
    );
    field(
        &mut ev,
        "coefficients",
        &s_list(&e.coefficients.0.iter().map(s_pair).collect::<Vec<_>>()),
    );
    field(&mut ev, "z", &s_pair(&e.z));
    field(
        &mut ev,
        "s",
        &s_list(&e.s.0.iter().map(s_pair).collect::<Vec<_>>()),
    );
    field(&mut ev, "generic_selector", &s_pair(&e.generic_selector));
    field(&mut ev, "poseidon_selector", &s_pair(&e.poseidon_selector));
    field(
        &mut ev,
        "complete_add_selector",
        &s_pair(&e.complete_add_selector),
    );
    field(&mut ev, "mul_selector", &s_pair(&e.mul_selector));
    field(&mut ev, "emul_selector", &s_pair(&e.emul_selector));
    field(
        &mut ev,
        "endomul_scalar_selector",
        &s_pair(&e.endomul_scalar_selector),
    );
    ev.push(')');
    field(&mut r, "evaluations", &ev);

    field(&mut r, "ft_eval1", &s_bigint(&p.ft_eval1));

    let b = &p.bulletproof;
    let mut bp = String::from("(");
    field(
        &mut bp,
        "lr",
        &s_list(
            &b.lr
                .iter()
                .map(|(l, rr)| format!("({})", join(&[s_pair(l), s_pair(rr)])))
                .collect::<Vec<_>>(),
        ),
    );
    field(&mut bp, "z_1", &s_bigint(&b.z_1));
    field(&mut bp, "z_2", &s_bigint(&b.z_2));
    field(&mut bp, "delta", &s_pair(&b.delta));
    field(
        &mut bp,
        "challenge_polynomial_commitment",
        &s_pair(&b.challenge_polynomial_commitment),
    );
    bp.push(')');
    field(&mut r, "bulletproof", &bp);
    r.push(')');
    r
}

/// **THE SEXP ENCODER** — `Pickles.Proof.Proofs_verified_2.Repr.Stable.V2` in Mina's own
/// S-expression grammar, the exact string `Pickles.proofOfBase64` reads after base64 decoding.
pub fn sexp_of_proof(p: &PicklesProofProofsVerified2ReprStableV2) -> String {
    let mut st = String::from("(");
    field(
        &mut st,
        "proof_state",
        &s_proof_state(&p.statement.proof_state),
    );
    field(
        &mut st,
        "messages_for_next_step_proof",
        &s_messages_for_next_step_proof(&p.statement.messages_for_next_step_proof),
    );
    st.push(')');

    let mut pe = String::from("(");
    let mut inner = String::from("(");
    field(
        &mut inner,
        "public_input",
        &s_pair(&p.prev_evals.evals.public_input),
    );
    field(
        &mut inner,
        "evals",
        &s_prev_evals_evals(&p.prev_evals.evals.evals),
    );
    inner.push(')');
    field(&mut pe, "evals", &inner);
    field(&mut pe, "ft_eval1", &s_bigint(&p.prev_evals.ft_eval1));
    pe.push(')');

    let mut r = String::from("(");
    field(&mut r, "statement", &st);
    field(&mut r, "prev_evals", &pe);
    field(&mut r, "proof", &s_wire_proof(&p.proof));
    r.push(')');
    r
}

// ───────────────────────────── the binprot encoder ─────────────────────────────

/// **THE BINPROT ENCODER.** `BinProtWrite` is derived on every node of the proof type
/// (`generated.rs:1005-1020` and its children); the encoder is a call, and the whole question is
/// whether it reproduces real bytes. [`roundtrip`] answers it.
pub fn binprot_of_proof(p: &PicklesProofProofsVerified2ReprStableV2) -> Vec<u8> {
    let mut v = Vec::new();
    p.binprot_write(&mut v).expect("binprot write");
    v
}
