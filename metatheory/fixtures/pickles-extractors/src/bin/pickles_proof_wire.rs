//! **PICKLES PROOF WIRE — the encoder, and the round-trip that judges it.**
//!
//! ## The gap this closes
//!
//! This tree could DECODE a Pickles proof (`bridge/src/mina_pickles.rs`, `MinaBinprot.lean`,
//! `main.rs`'s `binprot_read`) and could DERIVE a `VerificationKey` a Mina node parses
//! (`pickles-vk-derive`). It could not EMIT a proof object in either wire encoding. This binary
//! does, and it is judged the only way an encoder can honestly be judged: **on real bytes, by
//! byte identity.**
//!
//! ## ⚑ THERE ARE TWO WIRE ENCODINGS AND THEY ARE NOT THE SAME
//!
//! | encoding | what carries it | reader |
//! |---|---|---|
//! | **binprot** | a block's `protocolStateProof`, the p2p wire, a zkApp account update | openmina `binprot_read`, Mina's OCaml `bin_read_t` |
//! | **sexp** (base64'd) | o1js `Proof.toJSON().proof` / `Proof.fromJSON` | `Pickles.proofOfBase64`, i.e. Mina's OCaml sexp reader compiled into o1js |
//!
//! Measured, not assumed: `bridge/mina-zkapp/.fullchain/proof-5.json`'s `proof` field base64-decodes
//! to ASCII `((statement((proof_state((deferred_values((plonk((alpha((inner(8e9c…`. It is an
//! S-expression. It is NOT binprot. An encoder that emits only binprot cannot be handed to o1js,
//! and an encoder that emits only sexp cannot be put on the p2p wire. Both are emitted here.
//!
//! ## ⚑ openmina's own `SexpOf` CANNOT be used for the o1js half, and its round-trip is BROKEN
//!
//! `p2p-messages/src/v2/manual.rs:236-247` — `OfSexp for LimbVectorConstantHex64StableV1` REFUSES
//! any atom whose length is not exactly 16 (`if hex_str.len() != 16 { return Err(...) }`).
//! `manual.rs:262-269` — `SexpOf` for the same type EMITS `format!("0x{:016x}")`, eighteen chars.
//! So `openmina_sexp_of(x)` is not readable by `openmina_of_sexp`, and it does not match Mina,
//! whose own printer emits the bare 16 lowercase hex digits (verified against o1js's proof above:
//! `(beta(eaf9112db9f3d5b8 c65a17708076d06d))`). The sexp printer below is therefore written
//! HERE, against the observed OCaml grammar, not delegated.
//!
//! ## The grammar, pinned against o1js's own emitted proof
//!
//! * record  `((f1 v1)(f2 v2)…)`. ⚑ The separator is sexplib's `to_string_mach` rule, NOT
//!   "join with a space": a space appears only BETWEEN TWO BARE ATOMS. `(ft_eval1 0x1F18…)` has
//!   one; `(branch_data((proofs_verified N1)…`, `(domain_log2"\016")` and `((a)(b))` do not.
//!   See [`glue`] — joining lists with a space still PARSED and was caught only by re-printing.
//! * `BigInt`  `0x` + 64 UPPERCASE hex, BIG-endian  (`bigint.rs:192-205` agrees).
//! * `Hex64`   16 lowercase hex, NO prefix.
//! * `unit`  `()`;  `Option`  `()` for None, `(x)` for Some;  `bool`  `true`/`false`.
//! * `Proofs_verified`  `N0`/`N1`/`N2`;  `Domain_log2` is a CHAR, printed `"\016"` (3-digit decimal).
//! * list/array/vector  `(e1 e2 …)`;  tuple  `(a b)`.
//!
//! ## What it runs
//!
//! For every block fixture given (default: the whole `metatheory/fixtures/mina-blocks/` set plus
//! the 539508 control):
//!
//!   1. base64url → bytes → `PicklesProofProofsVerified2ReprStableV2::binprot_read`, ZERO trailing.
//!   2. `binprot_write` → **compare against the ORIGINAL bytes.** Byte-identical or the offset of
//!      the first difference. This is the encoder's verdict on real data.
//!   3. sexp-print → base64 → written out for `bridge/mina-zkapp/scripts/mina-proof-parse-gate.mjs`,
//!      which hands it to `Pickles.proofOfBase64` — Mina's own reader — and then RE-PRINTS the
//!      parsed object with Mina's own `proofToBase64` and compares. Parsing says well-formed;
//!      the re-print comparison says our printer IS Mina's printer, character for character.
//!   4. **A PROOF OBJECT WE BUILT**, not one we echoed: [`synthetic_proof`] assembles a
//!      `PicklesProofProofsVerified2ReprStableV2` from OUR OWN Pallas points (`g = k·G` for a
//!      counter `k`, so every point is on-curve and none is copied) and our own canonical field
//!      elements, then encodes it BOTH ways and reads it back. Nothing about it verifies — it is
//!      an object of the right SHAPE, which is the stated milestone.
//!
//! ## Scope
//!
//! A parseable proof is not a verifying proof. Nothing here claims the emitted object satisfies
//! any check beyond decoding; §REMAINDER in the report says what is between the two.
//!
//! RUN
//!   cargo run --release --manifest-path metatheory/fixtures/pickles-extractors/Cargo.toml \
//!       --bin pickles_proof_wire -- <out-dir> [fixture.json …]

use std::fmt::Write as _;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use base64::Engine as _;
use mina_curves::pasta::{Fp, Pallas};
use mina_p2p_messages::array::ArrayN16;
use mina_p2p_messages::bigint::BigInt;
use mina_p2p_messages::binprot::{BinProtRead, BinProtWrite};
use mina_p2p_messages::list::List;
use mina_p2p_messages::pseq::PaddedSeq;
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

// ───────────────────────────── the gate ─────────────────────────────

#[derive(serde::Deserialize)]
struct Fixture {
    #[serde(default)]
    state_hash: String,
    #[serde(default)]
    blockchain_length: String,
    protocol_state_proof_base64_urlsafe: String,
}

struct Verdict {
    path: String,
    height: String,
    state_hash: String,
    n_bytes: usize,
    trailing: usize,
    identical: bool,
    first_divergence: Option<usize>,
    sexp_len: usize,
    sexp_b64: String,
}

fn first_diff(a: &[u8], b: &[u8]) -> Option<usize> {
    for i in 0..a.len().min(b.len()) {
        if a[i] != b[i] {
            return Some(i);
        }
    }
    if a.len() == b.len() {
        None
    } else {
        Some(a.len().min(b.len()))
    }
}

fn roundtrip(path: &str) -> Verdict {
    let raw = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));
    let fx: Fixture =
        serde_json::from_str(&raw).unwrap_or_else(|e| panic!("{path} does not parse: {e}"));
    let orig = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(fx.protocol_state_proof_base64_urlsafe.trim_end_matches('='))
        .expect("base64url");

    let mut slice = orig.as_slice();
    let proof = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut slice)
        .unwrap_or_else(|e| panic!("{path}: binprot_read failed: {e}"));
    let trailing = slice.len();

    let re = binprot_of_proof(&proof);
    let identical = re == orig;
    let first_divergence = if identical {
        None
    } else {
        first_diff(&orig, &re)
    };

    // ⚑ The re-encoded bytes must ALSO decode to the same value. Byte identity already implies
    // it here, but when it fails this is what tells us whether we lost information or only
    // re-spelled it.
    let mut s2 = re.as_slice();
    let reparsed = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut s2)
        .expect("our own binprot output decodes");
    assert_eq!(
        reparsed, proof,
        "{path}: our encoding decodes to a DIFFERENT proof"
    );

    let sexp = sexp_of_proof(&proof);
    let sexp_b64 = base64::engine::general_purpose::STANDARD.encode(sexp.as_bytes());

    Verdict {
        path: path.to_string(),
        height: fx.blockchain_length,
        state_hash: fx.state_hash,
        n_bytes: orig.len(),
        trailing,
        identical,
        first_divergence,
        sexp_len: sexp.len(),
        sexp_b64,
    }
}

// ─────────────────────── a proof object WE BUILT ───────────────────────

/// `k·G` on Pallas, as the wire's `(x, y)` pair. Every point in the synthetic proof comes from
/// here, so none is copied from a real proof and all are on-curve.
fn our_point(k: u64) -> (BigInt, BigInt) {
    let g = Pallas::generator();
    let p = (g * mina_curves::pasta::Fq::from(k)).into_affine();
    let (x, y) = p.xy().expect("k*G is not the identity");
    (
        BigInt::from_bytes(x.into_bigint().to_bytes_le().try_into().unwrap()),
        BigInt::from_bytes(y.into_bigint().to_bytes_le().try_into().unwrap()),
    )
}

fn our_fp(k: u64) -> BigInt {
    let v = Fp::from(k) * Fp::from(0x9E3779B97F4A7C15u64) + Fp::from(1u64);
    BigInt::from_bytes(v.into_bigint().to_bytes_le().try_into().unwrap())
}

fn our_hex64(k: u64) -> LimbVectorConstantHex64StableV1 {
    LimbVectorConstantHex64StableV1((k.wrapping_mul(0x9E3779B97F4A7C15) | 1).into())
}

fn our_challenge(
    k: u64,
) -> PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2AChallenge {
    PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2AChallenge {
        inner: PaddedSeq([our_hex64(k), our_hex64(k + 1)]),
    }
}

fn our_bp(k: u64) -> PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2A {
    PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2A {
        prechallenge: our_challenge(k),
    }
}

fn our_evalpair(k: u64) -> (ArrayN16<BigInt>, ArrayN16<BigInt>) {
    (vec![our_fp(k)].into(), vec![our_fp(k + 1)].into())
}

/// **A `Proofs_verified_2`-shaped proof object assembled here, from our own values.** Nothing in
/// it is copied from a real proof. It does not verify and is not claimed to; it exists so the
/// parse gate is answering "can dregg EMIT one", not "can dregg re-emit one it was handed".
fn synthetic_proof() -> PicklesProofProofsVerified2ReprStableV2 {
    let mut ctr = 1u64;
    let mut next = || {
        ctr += 1;
        ctr
    };

    let plonk = PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonk {
        alpha: our_challenge(next()),
        beta: PaddedSeq([our_hex64(next()), our_hex64(next())]),
        gamma: PaddedSeq([our_hex64(next()), our_hex64(next())]),
        zeta: our_challenge(next()),
        // Real Mina block wrap proofs carry NONE here; the o1js proof read in the header carries
        // Some. Emitting None exercises the `()` arm, which is the one a block uses.
        joint_combiner: None,
        feature_flags:
            PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkFeatureFlags {
                range_check0: false,
                range_check1: false,
                foreign_field_add: false,
                foreign_field_mul: false,
                xor: false,
                rot: false,
                lookup: false,
                runtime_tables: false,
            },
    };

    let deferred_values =
        PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValues {
            plonk,
            bulletproof_challenges: PaddedSeq(std::array::from_fn(|i| our_bp(100 + i as u64))),
            branch_data: CompositionTypesBranchDataStableV1 {
                proofs_verified: PicklesBaseProofsVerifiedStableV1::N2,
                domain_log2: CompositionTypesBranchDataDomainLog2StableV1(14u8.into()),
            },
        };

    let proof_state = PicklesProofProofsVerified2ReprStableV2StatementProofState {
        deferred_values,
        sponge_digest_before_evaluations: CompositionTypesDigestConstantStableV1(PaddedSeq(
            std::array::from_fn(|i| our_hex64(200 + i as u64)),
        )),
        messages_for_next_wrap_proof:
            PicklesProofProofsVerified2ReprStableV2MessagesForNextWrapProof {
                challenge_polynomial_commitment: our_point(7),
                old_bulletproof_challenges: PaddedSeq(std::array::from_fn(|j| {
                    PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2(
                        PaddedSeq(std::array::from_fn(|i| our_bp(300 + (j * 15 + i) as u64))),
                    )
                })),
            },
    };

    let messages_for_next_step_proof =
        PicklesProofProofsVerified2ReprStableV2MessagesForNextStepProof {
            app_state: (),
            challenge_polynomial_commitments: (0..2u64)
                .map(|i| our_point(11 + i))
                .collect::<Vec<_>>()
                .into_iter()
                .collect::<List<_>>(),
            old_bulletproof_challenges: (0..2u64)
                .map(|j| PaddedSeq(std::array::from_fn(|i| our_bp(400 + j * 16 + i as u64))))
                .collect::<Vec<_>>()
                .into_iter()
                .collect::<List<_>>(),
        };

    let prev_evals = PicklesProofProofsVerified2ReprStableV2PrevEvals {
        evals: PicklesProofProofsVerified2ReprStableV2PrevEvalsEvals {
            public_input: (our_fp(500), our_fp(501)),
            evals: PicklesProofProofsVerified2ReprStableV2PrevEvalsEvalsEvals {
                w: PaddedSeq(std::array::from_fn(|i| our_evalpair(600 + i as u64 * 2))),
                coefficients: PaddedSeq(std::array::from_fn(|i| our_evalpair(700 + i as u64 * 2))),
                z: our_evalpair(800),
                s: PaddedSeq(std::array::from_fn(|i| our_evalpair(810 + i as u64 * 2))),
                generic_selector: our_evalpair(830),
                poseidon_selector: our_evalpair(832),
                complete_add_selector: our_evalpair(834),
                mul_selector: our_evalpair(836),
                emul_selector: our_evalpair(838),
                endomul_scalar_selector: our_evalpair(840),
                range_check0_selector: None,
                range_check1_selector: None,
                foreign_field_add_selector: None,
                foreign_field_mul_selector: None,
                xor_selector: None,
                rot_selector: None,
                lookup_aggregation: None,
                lookup_table: None,
                lookup_sorted: PaddedSeq([None, None, None, None, None]),
                runtime_lookup_table: None,
                runtime_lookup_table_selector: None,
                xor_lookup_selector: None,
                lookup_gate_lookup_selector: None,
                range_check_lookup_selector: None,
                foreign_field_mul_lookup_selector: None,
            },
        },
        ft_eval1: our_fp(900),
    };

    let proof = PicklesWrapWireProofStableV1 {
        commitments: PicklesWrapWireProofCommitmentsStableV1 {
            w_comm: PaddedSeq(std::array::from_fn(|i| our_point(1000 + i as u64))),
            z_comm: our_point(1100),
            t_comm: PaddedSeq(std::array::from_fn(|i| our_point(1200 + i as u64))),
        },
        evaluations: PicklesWrapWireProofEvaluationsStableV1 {
            w: PaddedSeq(std::array::from_fn(|i| {
                (our_fp(1300 + i as u64 * 2), our_fp(1301 + i as u64 * 2))
            })),
            coefficients: PaddedSeq(std::array::from_fn(|i| {
                (our_fp(1400 + i as u64 * 2), our_fp(1401 + i as u64 * 2))
            })),
            z: (our_fp(1500), our_fp(1501)),
            s: PaddedSeq(std::array::from_fn(|i| {
                (our_fp(1510 + i as u64 * 2), our_fp(1511 + i as u64 * 2))
            })),
            generic_selector: (our_fp(1530), our_fp(1531)),
            poseidon_selector: (our_fp(1532), our_fp(1533)),
            complete_add_selector: (our_fp(1534), our_fp(1535)),
            mul_selector: (our_fp(1536), our_fp(1537)),
            emul_selector: (our_fp(1538), our_fp(1539)),
            endomul_scalar_selector: (our_fp(1540), our_fp(1541)),
        },
        ft_eval1: our_fp(1600),
        bulletproof: PicklesWrapWireProofStableV1Bulletproof {
            // ⚑ 15 rounds: the wrap IPA has log2(2^15) = 15 (l, r) pairs, which is what every
            // real block proof read below carries.
            lr: (0..15u64)
                .map(|i| (our_point(1700 + i * 2), our_point(1701 + i * 2)))
                .collect::<Vec<_>>()
                .into(),
            z_1: our_fp(1800),
            z_2: our_fp(1801),
            delta: our_point(1900),
            challenge_polynomial_commitment: our_point(1901),
        },
    };

    PicklesProofProofsVerified2ReprStableV2 {
        statement: PicklesProofProofsVerified2ReprStableV2Statement {
            proof_state,
            messages_for_next_step_proof,
        },
        prev_evals,
        proof,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let out_dir = args
        .first()
        .cloned()
        .unwrap_or_else(|| "/tmp/pickles-proof-wire".to_string());
    std::fs::create_dir_all(&out_dir).expect("out dir");

    let fixtures: Vec<String> = if args.len() > 1 {
        args[1..].to_vec()
    } else {
        let mut v = vec!["mina_devnet_block.json".to_string()];
        let dir = "../mina-blocks";
        if let Ok(rd) = std::fs::read_dir(dir) {
            let mut names: Vec<_> = rd
                .filter_map(|e| e.ok())
                .map(|e| e.path().to_string_lossy().to_string())
                .filter(|p| p.ends_with(".json"))
                .collect();
            names.sort();
            v.extend(names);
        }
        v
    };

    println!("== BINPROT ROUND-TRIP ON REAL BLOCK PROOFS ==");
    let mut verdicts = Vec::new();
    let mut all_identical = true;
    for f in &fixtures {
        let v = roundtrip(f);
        all_identical &= v.identical && v.trailing == 0;
        println!(
            "[roundtrip] {:<52} h={:<8} bytes={:<6} trailing={} byte_identical={} {}",
            v.path,
            v.height,
            v.n_bytes,
            v.trailing,
            v.identical,
            match v.first_divergence {
                None => String::new(),
                Some(o) => format!("FIRST_DIVERGENCE_AT={o}"),
            }
        );
        std::fs::write(
            format!("{out_dir}/{}.o1js-proof.json", sanitize(&v.path)),
            format!(
                "{{\n  \"publicInput\": [],\n  \"publicOutput\": [],\n  \"maxProofsVerified\": 2,\n  \"proof\": \"{}\"\n}}\n",
                v.sexp_b64
            ),
        )
        .expect("write o1js proof json");
        verdicts.push(v);
    }

    println!("\n== A PROOF OBJECT WE BUILT (nothing copied from a real proof) ==");
    let synth = synthetic_proof();
    let sb = binprot_of_proof(&synth);
    let mut s = sb.as_slice();
    let back = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut s)
        .expect("our synthetic proof decodes with openmina's reader");
    assert_eq!(
        back, synth,
        "synthetic proof does not survive its own encoding"
    );
    assert_eq!(s.len(), 0, "synthetic proof left trailing bytes");
    println!("[synthetic] binprot bytes = {} ; openmina binprot_read ACCEPTS and re-decodes EQUAL ; trailing = 0", sb.len());
    let synth_sexp = sexp_of_proof(&synth);
    let synth_b64 = base64::engine::general_purpose::STANDARD.encode(synth_sexp.as_bytes());
    println!("[synthetic] sexp bytes = {}", synth_sexp.len());
    std::fs::write(format!("{out_dir}/synthetic.binprot"), &sb).expect("write");
    std::fs::write(
        format!("{out_dir}/synthetic.o1js-proof.json"),
        format!(
            "{{\n  \"publicInput\": [],\n  \"publicOutput\": [],\n  \"maxProofsVerified\": 2,\n  \"proof\": \"{synth_b64}\"\n}}\n"
        ),
    )
    .expect("write");

    // A machine-readable summary for the gate script.
    let mut j = String::from("{\n  \"roundtrip\": [\n");
    for (i, v) in verdicts.iter().enumerate() {
        let _ = write!(
            j,
            "    {{\"fixture\": {:?}, \"height\": {:?}, \"state_hash\": {:?}, \"binprot_bytes\": {}, \"trailing\": {}, \"byte_identical\": {}, \"first_divergence\": {}, \"sexp_bytes\": {}}}{}\n",
            v.path,
            v.height,
            v.state_hash,
            v.n_bytes,
            v.trailing,
            v.identical,
            match v.first_divergence {
                None => "null".to_string(),
                Some(o) => o.to_string(),
            },
            v.sexp_len,
            if i + 1 == verdicts.len() { "" } else { "," }
        );
    }
    let _ = write!(
        j,
        "  ],\n  \"all_byte_identical\": {all_identical},\n  \"synthetic_binprot_bytes\": {},\n  \"synthetic_sexp_bytes\": {}\n}}\n",
        sb.len(),
        synth_sexp.len()
    );
    std::fs::write(format!("{out_dir}/summary.json"), j).expect("write summary");

    println!("\nwrote {out_dir}/*.o1js-proof.json and summary.json");
    if !all_identical {
        eprintln!("PROOF_WIRE_RESULT=RED (a real proof did not survive decode->encode)");
        std::process::exit(1);
    }
    println!("PROOF_WIRE_RESULT=GREEN");
}

fn sanitize(p: &str) -> String {
    std::path::Path::new(p)
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "fixture".into())
}
