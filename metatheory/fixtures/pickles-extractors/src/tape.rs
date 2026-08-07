//! **THE STEP PROOF'S PHASE-1 Fq TAPE, AS A LEAN OBJECT — from the proof the forty words describe.**
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! Nothing here is an AIR. It authors no constraint, no `Builder` gadget and no `air_accepts`
//! predicate. It **reads** Fq coordinates off a kimchi proof our own prover produced, runs the
//! o1-labs Fq sponge over them, and renders decimal literals. The circuit that absorbs those
//! literals is Lean's (`Dregg2.Circuit.Emit.KimchiWrapMain`).
//!
//! ## ⚑ What this exists to kill: THREE step proofs in one pipeline
//!
//! Measured 2026-08-05. The wrap-side pipeline had three different step proofs in it, and every
//! shape agreed, so nothing was ever red:
//!
//! | consumer | proof it was about | reproducible? |
//! |---|---|---|
//! | the forty public words (`gates::prepared_statement`) | `pickles_kimchi_marshal`'s `prove_step` — Mina's SRS, seeded | yes |
//! | the wrap transcript's absorbed commitments (`KimchiWrapMain.RC_*`) | a third-party `create_circuit(0,5)` export | not ours at all |
//! | the Lean chain fixture (`KimchiStepWrapChainFixture`) | `export_step_tape`'s own proof — kimchi's TEST SRS, **`OsRng`** | **no** |
//!
//! `prevs = 2`, `wComms = 15`, `tComms = 7` on all three, so "same shape" hid "different proof" —
//! and the third was not even reproducible, because its prover took `OsRng`. On top of that,
//! `lr` and `delta` had no real source in the EMITTED circuit at all: `KimchiWrapMainField`'s
//! `lrPointQ i = xhatBase (5 + i % 50)` made thirty-two of the thirty-three IPA points fifty SRS
//! Lagrange bases, cycled.
//!
//! There is now **one** `prove_step`, and this module is a function of its return value. The tape,
//! the step key, the challenges and the forty are the same object's shadows.
//!
//! ## What is measured rather than asserted
//!
//! * the 56 `index_to_field_elements` coordinates re-absorbed through a fresh Fq sponge REPRODUCE
//!   `VerifierIndex::digest` — so the key list is the digest's preimage, not a second copy;
//! * the flat Fq tape reproduces `proof.oracles(...)`'s own β, γ, α′, ζ′ and digest, via an
//!   INDEPENDENT sponge replay (`absorb_commitment` per commitment, then flat, then compared);
//! * ⚑ the POSITIVE control: bending one Fq coordinate of `w_comm[0]` moves all five;
//! * ⚑ the NEGATIVE control: bending `z_1`, `z_2`, `ft_eval1`, `delta` and `sg` of the SAME proof
//!   and re-running `oracles(...)` on the MUTATED object leaves all five identical, and the tape
//!   is re-extracted from that object so the Lean-side comparison is of two extractions.
//!
//! Every one of those is an `assert!`, so this module REFUSES to render a tape it could not
//! reproduce.

use std::fmt::Write as _;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use ark_poly::EvaluationDomain as _;
use mina_curves::pasta::{Fp, Fq, Vesta};
use mina_poseidon::FqSponge as _;
use poly_commitment::commitment::{absorb_commitment, PolyComm};
use poly_commitment::SRS as _;

use kimchi::circuits::wires::{COLUMNS, PERMUTS};
use kimchi::proof::{PointEvaluations, RecursionChallenge};

use crate::marshal::StepKimchiProof;
use crate::transcript::{StepBase, StepScalar, StepVerifierIndex};

/// Everything the export is a function of. One proof object, one verifier index, one run.
pub struct StepTapeInputs<'a> {
    /// The Lean-emitted step circuit's name, as it appears in the JSON the prover consumed.
    pub circuit_name: &'a str,
    pub rows: usize,
    pub public_words: usize,
    pub prove_ms: u128,
    pub verify_ms: u128,
    pub proof: &'a StepKimchiProof,
    pub vk: &'a StepVerifierIndex,
    pub public_input: &'a [Fp],
    /// `transcript::public_comm`'s output — the very commitment the transcript absorbed.
    pub public_comm: &'a PolyComm<Vesta>,
    pub prev_challenges: &'a [RecursionChallenge<Vesta>],
}

/// The rendered artifacts, plus the numbers the caller prints.
pub struct StepTapeOut {
    /// `Dregg2/Circuit/Emit/KimchiStepWrapChainFixture.lean`.
    pub fixture_lean: String,
    /// `Dregg2/Circuit/Emit/KimchiStepWrapChainKey.lean`.
    pub key_lean: String,
    /// The JSON sidecar, for a gate that wants the numbers without parsing Lean.
    pub json: serde_json::Value,
    /// How many Fq words the phase-1 tape carries before β.
    pub tape_words: usize,
    /// How many Fq words the whole wrap transcript absorbs — the 116 the census counts.
    pub transcript_words: usize,
    /// How many curve POINTS those words are — the 58.
    pub transcript_points: usize,
    pub ipa_rounds: usize,
}

// ───────────────────────────── decimal rendering ─────────────────────────────

/// Decimal, via arkworks' own `Display` — the canonical residue, which is what every Lean literal
/// in this tree is.
fn dq(x: &Fq) -> String {
    x.to_string()
}
fn dp(x: &Fp) -> String {
    x.to_string()
}

/// The two Fq coordinates of a Vesta point, with kimchi's own infinity convention
/// (`sponge.rs:332-344`: "absorb a fake point (0, 0)").
fn xy(p: &Vesta) -> (Fq, Fq) {
    if p.infinity {
        (Fq::zero(), Fq::zero())
    } else {
        (p.x, p.y)
    }
}

/// Flatten a `PolyComm` to the Fq words `absorb_commitment` feeds the sponge, chunk by chunk.
fn comm_xy(c: &PolyComm<Vesta>) -> Vec<Fq> {
    let mut out = Vec::new();
    for chunk in &c.chunks {
        let (x, y) = xy(chunk);
        out.push(x);
        out.push(y);
    }
    out
}

fn lean_nat_list(name: &str, doc: &str, xs: &[Fq]) -> String {
    let parts: Vec<String> = xs.iter().map(dq).collect();
    format!(
        "/-- {doc} -/\ndef {name} : List Nat :=\n  [{}]\n\n",
        parts.join(", ")
    )
}

/// The same, for a list of **Fp** scalars — the step proof's own public input, which is the one
/// place a scalar rather than a coordinate crosses into a Lean list.
fn lean_nat_list_fp(name: &str, doc: &str, xs: &[Fp]) -> String {
    let parts: Vec<String> = xs.iter().map(dp).collect();
    format!(
        "/-- {doc} -/\ndef {name} : List Nat :=\n  [{}]\n\n",
        parts.join(", ")
    )
}

/// ⚑⚑ **`Types.Step.Statement`'s per-slot packed WIDTH** — the Rust twin of
/// `Dregg2/Circuit/Emit/PicklesStepStatement.lean`'s `slotBits`, and the reason it exists here is
/// that the WRAP circuit's x_hat ladder is sized by it (`wrap_verifier.ml:539-577`), so a correction
/// point computed at the wrong shift cancels nothing.
///
/// The layout is `Statement.spec Max_proofs_verified.n Backend.Tock.Rounds.n`
/// (`composition_types.ml:1453-1459`) with `Per_proof.In_circuit.spec` (`:1265-1274`), packed by
/// `Impls.Step.input` (`impls.ml:128-142`) where a `B Field` is `Step.Other_field.typ_unchecked`,
/// i.e. `(x >> 1, x & 1)` — **two** wires (`impls.ml:90-101`; openmina's own
/// `to_field_elements.rs:213-233` writes the same pair). Everything else is one.
///
/// ⚠ A public input that is NOT `STMT_WORDS` wide is not a statement and this says so by giving it
/// the all-255 partition it actually has — that is the shape the twelve-word Lean-emitted circuit
/// had, and it is a different object, not an older version of this one.
fn step_statement_slot_bits(n: usize) -> Vec<usize> {
    const PP_FIELDS: usize = 5;
    const PP_DIGESTS: usize = 1;
    const PP_CHALLENGES: usize = 2;
    const PP_SCALAR_CHALLENGES: usize = 3;
    const PP_BP_LOG2: usize = 15; // Backend.Tock.Rounds.n — NOT Tick's 16
    const PP_BOOLS: usize = 1;
    const PREVS: usize = 2;
    const PP_WORDS: usize =
        2 * PP_FIELDS + PP_DIGESTS + PP_CHALLENGES + PP_SCALAR_CHALLENGES + PP_BP_LOG2 + PP_BOOLS;
    const STMT_WORDS: usize = PP_WORDS * PREVS + 1 + PREVS;
    if n != STMT_WORDS {
        return vec![255; n];
    }
    (0..n)
        .map(|i| {
            if i >= PP_WORDS * PREVS {
                return 255; // messages_for_next_step_proof + messages_for_next_wrap_proof
            }
            let j = i % PP_WORDS;
            if j < 2 * PP_FIELDS {
                if j % 2 == 0 {
                    255
                } else {
                    1
                }
            } else if j < 2 * PP_FIELDS + PP_DIGESTS {
                255
            } else if j < PP_WORDS - PP_BOOLS {
                128
            } else {
                1
            }
        })
        .collect()
}

/// A fresh o1-labs Fq sponge — the same `static_params()` `kimchi::verifier` uses.
fn fresh() -> StepBase {
    StepBase::new(mina_poseidon::pasta::fq_kimchi::static_params())
}

// ───────────────────────────── the export ─────────────────────────────

/// Extract, cross-check, and render. Panics on any falsification: a tape this could not reproduce
/// must not reach Lean wearing the name of one it could.
pub fn export(inp: StepTapeInputs<'_>) -> StepTapeOut {
    let StepTapeInputs {
        circuit_name,
        rows,
        public_words,
        prove_ms,
        verify_ms,
        proof,
        vk,
        public_input,
        public_comm,
        prev_challenges,
    } = inp;

    let vk_digest: Fq = vk.digest::<StepBase>();

    // ── the 56 `index_to_field_elements` coordinates of THIS index ──
    //
    // `VerifierIndex::digest` absorbs exactly the 28 Pickles index commitments when no optional
    // gate commitment is present. If one were, the 56 words below would be a PREFIX of the digest's
    // preimage wearing the name of all of it.
    assert!(
        vk.range_check0_comm.is_none()
            && vk.range_check1_comm.is_none()
            && vk.foreign_field_add_comm.is_none()
            && vk.foreign_field_mul_comm.is_none()
            && vk.xor_comm.is_none()
            && vk.rot_comm.is_none()
            && vk.lookup_index.is_none(),
        "`VerifierIndex::digest` would absorb more than the 28 Pickles index points"
    );
    assert_eq!(vk.sigma_comm.len(), PERMUTS, "Plonk_types.Permuts.n");
    assert_eq!(vk.coefficients_comm.len(), COLUMNS, "Plonk_types.Columns.n");
    let mut index_xy: Vec<Fq> = vec![];
    let mut n_inf: usize = 0;
    let mut inf_at: Vec<String> = vec![];
    {
        let mut push = |c: &PolyComm<Vesta>, label: String| {
            assert_eq!(c.chunks.len(), 1, "{label}: a chunked index commitment");
            if c.chunks[0].infinity {
                n_inf += 1;
                inf_at.push(label);
            }
            index_xy.extend(comm_xy(c));
        };
        for (j, cm) in vk.sigma_comm.iter().enumerate() {
            push(cm, format!("sigma_comm[{j}]"));
        }
        for (j, cm) in vk.coefficients_comm.iter().enumerate() {
            push(cm, format!("coefficients_comm[{j}]"));
        }
        for (cm, name) in [
            (&vk.generic_comm, "generic_comm"),
            (&vk.psm_comm, "psm_comm"),
            (&vk.complete_add_comm, "complete_add_comm"),
            (&vk.mul_comm, "mul_comm"),
            (&vk.emul_comm, "emul_comm"),
            (&vk.endomul_scalar_comm, "endomul_scalar_comm"),
        ] {
            push(cm, name.to_string());
        }
    }
    assert_eq!(index_xy.len(), 2 * (PERMUTS + COLUMNS + 6));
    // ⚑ THE PREIMAGE IDENTITY. A fresh Fq sponge over exactly those 56 words IS the index digest.
    {
        let mut kr = fresh();
        kr.absorb_fq(&index_xy);
        assert_eq!(
            dq(&kr.digest_fq()),
            dq(&vk_digest),
            "absorbing the 56 index_to_field_elements coordinates is NOT the index digest"
        );
    }
    // ⚠ `index_to_field_elements` flattens the identity as the FAKE POINT (0,0), which is off
    // `y² = x³ + 5`; W-COMBINE folds the 28 points with the INCOMPLETE `Ops.add_fast`, so ONE
    // identity commitment leaves `bulletproof_success` with no satisfying witness. kimchi's own
    // `create_circuit(0,5)` test key had seven of 28, which is the defect this walked out of.
    assert_eq!(
        n_inf,
        0,
        "{n_inf} of this step index's 28 commitments are the point at infinity ({}) — \
         W-COMBINE's add_fast fold has no witness over a key like that",
        inf_at.join(", ")
    );
    println!(
        "[KEY  ] 56 index_to_field_elements coords; {n_inf} of 28 at infinity; \
         56-coord replay == VerifierIndex::digest == the tape's first word : true"
    );

    // ── the phase-1 blocks ──
    let prevcomm_xy: Vec<Fq> = prev_challenges
        .iter()
        .flat_map(|rc| comm_xy(&rc.comm))
        .collect();
    let pubcomm_xy: Vec<Fq> = comm_xy(public_comm);
    let wcomm_xy: Vec<Fq> = proof.commitments.w_comm.iter().flat_map(comm_xy).collect();
    let zcomm_xy: Vec<Fq> = comm_xy(&proof.commitments.z_comm);
    let tcomm_xy: Vec<Fq> = comm_xy(&proof.commitments.t_comm);

    // ── INDEPENDENT REPLAY: a fresh Fq sponge over exactly those commitments ──
    let mut replay = fresh();
    replay.absorb_fq(&[vk_digest]);
    for rc in prev_challenges {
        absorb_commitment(&mut replay, &rc.comm);
    }
    absorb_commitment(&mut replay, public_comm);
    for c in &proof.commitments.w_comm {
        absorb_commitment(&mut replay, c);
    }
    let r_beta: Fp = replay.challenge();
    let r_gamma: Fp = replay.challenge();
    absorb_commitment(&mut replay, &proof.commitments.z_comm);
    let r_alpha_chal: Fp = replay.challenge();
    absorb_commitment(&mut replay, &proof.commitments.t_comm);
    let r_zeta_chal: Fp = replay.challenge();
    let r_digest: Fp = replay.clone().digest();

    // ── and what `proof.oracles(...)` — the verifier's own path — produced ──
    let o = proof
        .oracles::<StepBase, StepScalar, _>(vk, public_comm, Some(public_input))
        .expect("oracles");
    let beta = o.oracles.beta;
    let gamma = o.oracles.gamma;
    let alpha_chal = o.oracles.alpha_chal.0;
    let zeta_chal = o.oracles.zeta_chal.0;
    let digest = o.digest;
    let cip: Fp = o.combined_inner_product;

    assert_eq!(r_beta, beta, "replay beta != oracles beta");
    assert_eq!(r_gamma, gamma, "replay gamma != oracles gamma");
    assert_eq!(r_alpha_chal, alpha_chal, "replay alpha' != oracles alpha'");
    assert_eq!(r_zeta_chal, zeta_chal, "replay zeta' != oracles zeta'");
    assert_eq!(r_digest, digest, "replay digest != oracles digest");
    println!(
        "[CROSS] independent Fq-sponge replay reproduces oracles' beta/gamma/alpha'/zeta'/digest : true"
    );

    // ⚑ The tape the Lean side absorbs, as ONE flat list, in absorb order.
    let mut tape: Vec<Fq> = vec![vk_digest];
    tape.extend_from_slice(&prevcomm_xy);
    tape.extend_from_slice(&pubcomm_xy);
    tape.extend_from_slice(&wcomm_xy);

    println!(
        "[TAPE ] 1 + {} + {} + {} = {} Fq words before beta; z_comm {} ; t_comm {}",
        prevcomm_xy.len(),
        pubcomm_xy.len(),
        wcomm_xy.len(),
        tape.len(),
        zcomm_xy.len(),
        tcomm_xy.len()
    );

    // ── what the phase-1 tape does NOT read: the IPA scalars and ft_eval1 (all Fp) ──
    let z1 = proof.proof.z1;
    let z2 = proof.proof.z2;
    let ft_eval1 = proof.ft_eval1;
    let (dx, dy) = xy(&proof.proof.delta);
    let (sx, sy) = xy(&proof.proof.sg);

    // ── the two red controls, MEASURED on this proof ──
    let phase1 = |tape: &[Fq], zc: &[Fq], tc: &[Fq]| -> (Fp, Fp, Fp, Fp, Fp) {
        let mut s = fresh();
        s.absorb_fq(tape);
        let b: Fp = s.challenge();
        let g: Fp = s.challenge();
        s.absorb_fq(zc);
        let a: Fp = s.challenge();
        s.absorb_fq(tc);
        let z: Fp = s.challenge();
        let d: Fp = s.clone().digest();
        (b, g, a, z, d)
    };
    // The flat-tape run must agree with the `absorb_commitment` run, or the tape is not the tape.
    assert_eq!(
        phase1(&tape, &zcomm_xy, &tcomm_xy),
        (beta, gamma, alpha_chal, zeta_chal, digest),
        "the flat Fq tape does not reproduce the verifier's own challenges"
    );

    // POSITIVE. Bend the first Fq coordinate of `w_comm`.
    let bent_idx = 1 + prevcomm_xy.len() + pubcomm_xy.len();
    let mut bent_tape = tape.clone();
    bent_tape[bent_idx] += Fq::from(1u64);
    let (b_beta, b_gamma, b_alpha, b_zeta, b_digest) = phase1(&bent_tape, &zcomm_xy, &tcomm_xy);
    assert_ne!(b_beta, beta, "bending w_comm[0].x left beta fixed");
    assert_ne!(b_gamma, gamma, "bending w_comm[0].x left gamma fixed");
    assert_ne!(b_alpha, alpha_chal, "bending w_comm[0].x left alpha' fixed");
    assert_ne!(b_zeta, zeta_chal, "bending w_comm[0].x left zeta' fixed");
    assert_ne!(
        b_digest, digest,
        "bending w_comm[0].x left the digest fixed"
    );
    println!(
        "[RED + ] bending tape word {bent_idx} (w_comm[0].x, an Fq coordinate of the STEP proof) \
         moves beta, gamma, alpha', zeta' AND the digest"
    );

    // NEGATIVE. Bend the parts phase 1 never absorbs and re-run the WHOLE phase-1 path on the
    // mutated object, then RE-EXTRACT its tape, so Lean compares two independent extractions.
    let mut unread_proof = proof.clone();
    unread_proof.proof.z1 += Fp::from(1u64);
    unread_proof.proof.z2 += Fp::from(1u64);
    unread_proof.ft_eval1 += Fp::from(1u64);
    unread_proof.proof.delta = -unread_proof.proof.delta;
    unread_proof.proof.sg = -unread_proof.proof.sg;
    let uo = unread_proof
        .oracles::<StepBase, StepScalar, _>(vk, public_comm, Some(public_input))
        .expect("oracles on the unread-bent proof");
    assert_eq!(uo.oracles.beta, beta, "an unread bend moved beta");
    assert_eq!(uo.oracles.gamma, gamma, "an unread bend moved gamma");
    assert_eq!(
        uo.oracles.alpha_chal.0, alpha_chal,
        "an unread bend moved alpha'"
    );
    assert_eq!(
        uo.oracles.zeta_chal.0, zeta_chal,
        "an unread bend moved zeta'"
    );
    assert_eq!(uo.digest, digest, "an unread bend moved the digest");
    let u_wcomm: Vec<Fq> = unread_proof
        .commitments
        .w_comm
        .iter()
        .flat_map(comm_xy)
        .collect();
    let u_zcomm: Vec<Fq> = comm_xy(&unread_proof.commitments.z_comm);
    let u_tcomm: Vec<Fq> = comm_xy(&unread_proof.commitments.t_comm);
    let mut unread_tape: Vec<Fq> = vec![vk.digest::<StepBase>()];
    for rc in &unread_proof.prev_challenges {
        unread_tape.extend(comm_xy(&rc.comm));
    }
    unread_tape.extend_from_slice(&pubcomm_xy);
    unread_tape.extend_from_slice(&u_wcomm);
    assert_eq!(u_wcomm, wcomm_xy, "the unread bend changed w_comm");
    assert_eq!(
        unread_tape, tape,
        "the unread bend changed the phase-1 tape"
    );
    assert_ne!(unread_proof.proof.z1, z1);
    assert_ne!(unread_proof.proof.z2, z2);
    assert_ne!(unread_proof.ft_eval1, ft_eval1);
    let (udx, udy) = xy(&unread_proof.proof.delta);
    let (usx, usy) = xy(&unread_proof.proof.sg);
    assert_ne!((udx, udy), (dx, dy));
    assert_ne!((usx, usy), (sx, sy));
    println!(
        "[RED - ] bending z_1, z_2, ft_eval1, delta and sg of the SAME proof and re-running \
         oracles(...) leaves beta/gamma/alpha'/zeta'/digest IDENTICAL"
    );

    // ── the one scalar that crosses fields ──
    let two_to_255: Fp = Fp::from(2u64).pow([255u64]);
    let type1_c: Fp = two_to_255 + Fp::from(1u64);
    let type1_scale: Fp = Fp::from(2u64).inverse().unwrap();
    let cip_shifted_fp: Fp = (cip - type1_c) * type1_scale;
    assert_eq!(
        cip_shifted_fp + cip_shifted_fp + type1_c,
        cip,
        "Type1 shift does not round-trip"
    );
    let cip_word_fq: Fq = Fq::from_le_bytes_mod_order(&cip_shifted_fp.into_bigint().to_bytes_le());
    assert_eq!(
        cip_word_fq.into_bigint().to_bytes_le(),
        cip_shifted_fp.into_bigint().to_bytes_le(),
        "the Fp->Fq reinterpretation changed the integer - p < q is violated"
    );
    println!(
        "[CROSS] combined_inner_product: Fp {} -> Type1-shifted Fp -> ONE Fq wire (p < q)",
        dp(&cip)
    );

    // ── the IPA `(L,R)` pairs and `delta` — ⚑ THE THIRTY-THREE POINTS THAT HAD NO SOURCE ──
    let mut lr_xy: Vec<Fq> = Vec::new();
    for (l, r) in &proof.proof.lr {
        let (lx, ly) = xy(l);
        let (rx, ry) = xy(r);
        lr_xy.extend_from_slice(&[lx, ly, rx, ry]);
    }
    let ipa_rounds = proof.proof.lr.len();
    println!(
        "[TAPE ] IPA rounds = {ipa_rounds} ({} Fq words of (L,R)) + delta (2) — \
         the {} points `lrPointQ`/`deltaPointQ` used to fill with SRS Lagrange bases",
        lr_xy.len(),
        2 * ipa_rounds + 1
    );

    // ───── ⚑ THE STEP PROOF'S OWN `openings.evals`, IN `to_absorption_sequence` ORDER ─────
    //
    // ⚠ ⚑ **SAY WHICH FINALIZE THESE ARE FOR, BECAUSE THE TREE GOT IT WRONG FOR A DAY.** These are
    // **Fp** — Vesta's scalar field — at the STEP proof's own domain. They are the object
    // `step_main`'s `finalize_other_proof` reads: a step circuit verifies WRAP proofs, each of which
    // carries deferred values ABOUT the step proof it wrapped, and those are Fp scalars a native-Fp
    // circuit can finalize. `KimchiStepMainCore.evVal` is the mixer standing where this belongs.
    //
    // They are **NOT** what `KimchiWrapMain` §19/§20 reads, and four docblocks used to say they
    // were. `wrap_main`'s `finalize_other_proof` finalizes deferred values about **wrap** proofs —
    // Fq, at the wrap domain, `Scalars.Tock`, `Shifted_value.Type2` — which is why §19's own
    // `FIN_OMEGA`/`FIN_SHIFTS` are Mina's devnet WRAP verifier index's and why §19c reads
    // `MinaRealBlockGate.EVZ`/`EVZW` instead. Exporting these here does not make them that object.
    //
    // `Evals.to_absorption_sequence` (`plonk_types.ml`): `z`, then the six always-on gate
    // selectors, then `w`×15, `coefficients`×15, `s`×6 — 43 columns, which is `FIN_NCOLS`.
    let ev = &proof.evals;
    let ev_cols: Vec<&PointEvaluations<Vec<Fp>>> = [
        &ev.z,
        &ev.generic_selector,
        &ev.poseidon_selector,
        &ev.complete_add_selector,
        &ev.mul_selector,
        &ev.emul_selector,
        &ev.endomul_scalar_selector,
    ]
    .into_iter()
    .chain(ev.w.iter())
    .chain(ev.coefficients.iter())
    .chain(ev.s.iter())
    .collect();
    // ⚑ THE REFUSAL, EXTENDED IN THE SAME SHAPE AS THE SLOT-WIDTH ONE ABOVE. A published word that
    // does not fit its slot is refused there; here, a column that is CHUNKED is refused, because
    // `evals_of_split_evals` is the identity only at one chunk and a 43-entry fold over the first
    // chunk of a chunked column is a prefix wearing the name of the whole.
    const EV_NCOLS: usize = 1 + 6 + COLUMNS + COLUMNS + (PERMUTS - 1);
    assert_eq!(
        EV_NCOLS, 43,
        "to_absorption_sequence is not 1 + 6 + 15 + 15 + 6"
    );
    assert_eq!(
        ev_cols.len(),
        EV_NCOLS,
        "the absorption sequence is {} columns, not {EV_NCOLS}",
        ev_cols.len()
    );
    for (i, c) in ev_cols.iter().enumerate() {
        assert_eq!(
            (c.zeta.len(), c.zeta_omega.len()),
            (1, 1),
            "evaluation column {i} is chunked ({}, {}) — `evals_of_split_evals` is not the identity \
             on it and a one-chunk read would be a prefix wearing the name of the column",
            c.zeta.len(),
            c.zeta_omega.len()
        );
    }
    let ev_zeta: Vec<Fp> = ev_cols.iter().map(|c| c.zeta[0]).collect();
    let ev_zetaw: Vec<Fp> = ev_cols.iter().map(|c| c.zeta_omega[0]).collect();
    // …and `evals.public_input`, refused rather than zero-filled when the prover left it empty.
    let pub_ev = ev.public.as_ref().expect(
        "the step proof carries no public evaluation — `prover.rs:995` fills it only for a \
                 circuit with a public input, and substituting zeros would be a fixture",
    );
    assert_eq!(
        (pub_ev.zeta.len(), pub_ev.zeta_omega.len()),
        (1, 1),
        "the public evaluation is chunked"
    );
    let (pub_eval_z, pub_eval_w) = (pub_ev.zeta[0], pub_ev.zeta_omega[0]);
    println!(
        "[EVALS] {EV_NCOLS} to_absorption_sequence columns at ζ and ζω, one chunk each; \
         ft_eval1 and (p(ζ), p(ζω)) alongside — the object step_main's finalize_other_proof reads \
         (Fp, step domain), NOT the wrap circuit's"
    );

    // ⚑ Every point on this tape must be ON VESTA. `Inner_curve.typ` is `assert_on_curve`
    // upstream, and `Scalar_challenge.endo_inv` has no witness over an off-curve `l` — which is
    // why the filler had to be on-curve in the first place. Real points are on-curve by
    // construction; checking it here is what makes that a measurement rather than a deduction.
    {
        let mut pts: Vec<Vesta> = vec![];
        for rc in prev_challenges {
            pts.extend(rc.comm.chunks.iter().copied());
        }
        pts.extend(public_comm.chunks.iter().copied());
        for c in &proof.commitments.w_comm {
            pts.extend(c.chunks.iter().copied());
        }
        pts.extend(proof.commitments.z_comm.chunks.iter().copied());
        pts.extend(proof.commitments.t_comm.chunks.iter().copied());
        for (l, r) in &proof.proof.lr {
            pts.push(*l);
            pts.push(*r);
        }
        pts.push(proof.proof.delta);
        let off: Vec<usize> = pts
            .iter()
            .enumerate()
            .filter(|(_, p)| !(p.infinity || p.is_on_curve()))
            .map(|(i, _)| i)
            .collect();
        assert!(off.is_empty(), "points off Vesta at tape indices {off:?}");
        assert!(
            pts.iter().all(|p| !p.infinity),
            "a tape point is the identity — it would flatten to the fake point (0,0), off y² = x³ + 5"
        );
        println!(
            "[CURVE] all {} tape points are on y² = x³ + 5 over Fq and none is the identity",
            pts.len()
        );
    }

    // ⚑ THE CENSUS, AND `x_hat` IS DELIBERATELY NOT IN IT. `wrap_verifier.ml:617` absorbs `x_hat`,
    // but in the EMITTED circuit that pair is §15's MSM output (`WrapShape.xhatXY`) and not a value
    // read off the proof — `w6_xhat` is the rung that made it derived. So the block this tape
    // SOURCES for `KimchiWrapMain.itemVal` is `sg_old + w_comm + z_comm + t_comm + lr + delta`:
    //
    //     sg_old 2 + w_comm 15 + z_comm 1 + t_comm 7  = 25 points / 50 words
    //     lr 2·16 + delta 1                           = 33 points / 66 words
    //                                                 = 58 points / 116 words
    //
    // `STEP_PUBCOMM_XY` is still exported, because `KimchiStepWrapChain` OVERRIDES the MSM output
    // with it — a reality gate about `proof.oracles(...)` has to absorb the commitment the verifier
    // absorbed. Counting it here would inflate the fixture census by the one pair a rung derives.
    let transcript_words =
        prevcomm_xy.len() + wcomm_xy.len() + zcomm_xy.len() + tcomm_xy.len() + lr_xy.len() + 2;
    let transcript_points = transcript_words / 2;
    assert_eq!(
        transcript_words,
        2 * (prev_challenges.len() + COLUMNS + 1 + proof.commitments.t_comm.chunks.len())
            + 2 * (2 * ipa_rounds + 1),
        "the sourced census is not sg_old + w_comm + z_comm + t_comm + lr + delta"
    );

    // ─────── ⚑ THE x_hat MSM's OWN INPUTS — this proof's public input, this proof's DOMAIN ───────
    //
    // `wrap_verifier.ml:539-616` builds `x_hat` as an MSM over the verified proof's public input
    // against `lagrange ~domain srs i`, negates it (`:610`) and adds `Generators.h` (`:612-616`).
    // kimchi's own prologue (`verifier.rs:834-857`, transcribed at `transcript::public_comm`) is
    // the same object: `mask_custom(MSM(L, −public_input), 1)` = `−Σ pᵢ·Lᵢ + h`.
    //
    // ⚠ ⚑ **THE DOMAIN IS THE TRAP, AND IT IS EXACTLY THE `lr` DEFECT'S CLASS.** A Lagrange basis
    // is a function of the DOMAIN, and `MinaStepSrsLagrange.LAGRANGE_XY` is taken at
    // `2^Common.Max_degree.step_log2 = 65536` — Mina's `step-transaction` domain. This proof's
    // domain is `2^{}`. Bases from the wrong domain are on-curve, are genuine SRS Lagrange
    // commitments, and reproduce NOTHING — `onCurveQ` is structurally incapable of noticing, which
    // is why the check below is the RE-DERIVATION and not a curve predicate.
    let domain_log2 = vk.domain.log_size_of_group as usize;
    assert_eq!(
        1usize << domain_log2,
        vk.domain.size(),
        "domain.log_size_of_group does not describe domain.size()"
    );
    assert_eq!(
        public_comm.chunks.len(),
        1,
        "x_hat is chunked ({} chunks) — the wrap circuit absorbs ONE pair",
        public_comm.chunks.len()
    );
    assert_eq!(
        public_input.len(),
        vk.public,
        "public input width {} != verifier index public {}",
        public_input.len(),
        vk.public
    );
    let lgr = vk.srs().get_lagrange_basis(vk.domain);
    let mut lagrange_pts: Vec<Vesta> = Vec::new();
    let mut lagrange_xy: Vec<Fq> = Vec::new();
    for (i, c) in lgr.iter().take(public_input.len()).enumerate() {
        assert_eq!(c.chunks.len(), 1, "lagrange basis {i} is chunked");
        let g = c.chunks[0];
        assert!(
            !g.infinity && g.is_on_curve(),
            "lagrange basis {i} is not a Vesta point"
        );
        lagrange_pts.push(g);
        lagrange_xy.extend(comm_xy(c));
    }
    assert_eq!(lagrange_pts.len(), public_input.len());
    let urs_h = vk.srs().blinding_commitment();
    assert!(
        !urs_h.infinity && urs_h.is_on_curve(),
        "the SRS blinding base is not a Vesta point"
    );
    let (hx, hy) = xy(&urs_h);

    // ⚑⚑ **THE PER-SLOT WIDTHS, AND THEY STOPPED BEING ALL-255 WHEN THE STEP CIRCUIT STARTED
    // PUBLISHING A `Types.Step.Statement`.** This block used to read *"every entry here is a full
    // `Field.size_in_bits = 255` scalar — this proof's public input is 12 unconstrained Fp
    // elements, not a packed Pickles statement"*. It is one now
    // (`Dregg2/Circuit/Emit/PicklesStepStatement.lean`, established at
    // `composition_types.ml:1265-1274,1453-1459`), so the partition is what
    // `wrap_verifier.ml:539-577` makes of a packed statement:
    //
    //   * a 255-bit slot (a `B Field`'s `hi` half, or a `B Digest`) → `Add_with_correction`,
    //     `chunks_needed 255 = 51`, `actual_shift = 255`;
    //   * a 128-bit slot (`B Challenge` / `Scalar Challenge` / `B Bulletproof_challenge`) →
    //     `Add_with_correction`, `chunks_needed 127 = 26`, `actual_shift = 130` — ⚠ **130, not
    //     128**: `scale_fast2'` applies `chunks_needed` to `num_bits − 1` and the shift is
    //     `bits_per_chunk × chunks` (`plonk_curve_ops.ml:250-256`);
    //   * a ONE-bit slot (a `B Field`'s parity half, `B Bool`) → `` `Cond_add ``
    //     (`wrap_verifier.ml:573-577`), which runs NO ladder and has NO correction.
    //
    // A correction computed at the wrong shift is an on-curve point that cancels nothing, and the
    // re-derivation below is what refuses it. `correction_xy` is therefore indexed over the
    // `Add_with_correction` partition ONLY, in slot order — the same convention
    // `MinaStepSrsLagrange.CORRECTION_XY` uses and the same one `xhatCorrIdx` reads.
    const BITS_PER_CHUNK: usize = 5;
    let chunks_needed = |n: usize| (n + BITS_PER_CHUNK - 1) / BITS_PER_CHUNK;
    let slot_bits = step_statement_slot_bits(public_input.len());
    assert_eq!(slot_bits.len(), public_input.len());
    // ⚑ the width census, against the number Mina's own compiled `wrap-transaction` reports:
    // W-XHAT's share of `VarBaseMul 2417` is `15 × 51 + 40 × 26 = 1805`.
    if public_input.len() == 67 {
        let n255 = slot_bits.iter().filter(|b| **b == 255).count();
        let n128 = slot_bits.iter().filter(|b| **b == 128).count();
        let n1 = slot_bits.iter().filter(|b| **b == 1).count();
        assert_eq!(
            (n255, n128, n1),
            (15, 40, 12),
            "the packed step statement's width census is not Mina's"
        );
        assert_eq!(
            n255 * chunks_needed(254) + n128 * chunks_needed(127),
            1805,
            "the x_hat chunk count is not the 1805 of Mina's VarBaseMul 2417"
        );
    }
    // …and every published word actually FITS the slot it claims, which is the obligation
    // `scale_fast2`'s top-bit asserts enforce in the wrap circuit.
    for (i, (p, b)) in public_input.iter().zip(slot_bits.iter()).enumerate() {
        let w = p.into_bigint().num_bits() as usize;
        assert!(
            w <= *b,
            "step public word {i} is {w} bits wide and its statement slot is {b}"
        );
    }
    let mut correction_xy: Vec<Fq> = Vec::new();
    let mut xhat_bits: Vec<Fq> = Vec::new();
    for (g, b) in lagrange_pts.iter().zip(slot_bits.iter()) {
        xhat_bits.push(Fq::from(*b as u64));
        if *b == 1 {
            continue; // `Cond_add` — no ladder, no correction
        }
        let shift = BITS_PER_CHUNK * chunks_needed(*b - 1);
        let two_to_shift: Fp = Fp::from(2u64).pow([shift as u64]);
        let c = (-(g.into_group() * two_to_shift)).into_affine();
        assert!(
            !c.infinity && c.is_on_curve(),
            "a correction point is degenerate"
        );
        let (cx, cy) = xy(&c);
        correction_xy.push(cx);
        correction_xy.push(cy);
    }

    // ⚑ THE RE-DERIVATION. Not "the bases are plausible" — the MSM the Lean circuit will emit,
    // evaluated here over the exported bases and the exported scalars, IS the pair the transcript
    // absorbed at `wrap_verifier.ml:617`. A base from the wrong domain, a scalar in the wrong
    // order, or a missing blinding add all fail HERE rather than three layers downstream.
    {
        let mut acc = <Vesta as AffineRepr>::Group::zero();
        for (p, g) in public_input.iter().zip(lagrange_pts.iter()) {
            acc += g.into_group() * *p;
        }
        let redone = (-acc + urs_h.into_group()).into_affine();
        assert_eq!(
            xy(&redone),
            xy(&public_comm.chunks[0]),
            "−Σ pᵢ·Lᵢ + h is NOT the public-input commitment the transcript absorbed"
        );
    }
    // …and the negative control for the trap: the domain-65536 basis this tree already holds does
    // NOT reproduce it. Stated as an inequality on the first base, because that is the object a
    // copy-paste would take.
    {
        let wrong = vk.srs().get_lagrange_basis_from_domain_size(1 << 16)[0].chunks[0];
        assert_ne!(
            xy(&wrong),
            xy(&lagrange_pts[0]),
            "the step domain and Mina's step-transaction domain share a Lagrange basis — the \
             domain trap this export exists to close would be undetectable"
        );
    }
    println!(
        "[XHAT ] domain 2^{domain_log2}; {} Lagrange bases + {} corrections + h; \
         −Σ pᵢ·Lᵢ + h == public_comm : true (and the 2^16-domain basis differs)",
        lagrange_pts.len(),
        correction_xy.len() / 2
    );

    // ───────────────────── the fixture module ─────────────────────
    let mut l = String::new();
    l.push_str(&format!(
        r#"/-
# KimchiStepWrapChainFixture — GENERATED. DO NOT EDIT.

Written by `metatheory/fixtures/pickles-extractors/src/tape.rs`, called from
`src/bin/pickles_kimchi_marshal.rs` — **the same binary, the same run and the same `prove_step`
return value that produces the forty public words** `PreparedStatement::to_public_input` demands of
the wrap circuit.

⚑ **THAT SENTENCE IS THE WHOLE POINT, AND IT WAS FALSE UNTIL 2026-08-05.** This module used to be
written by `pickles-chain-harness/src/bin/export_step_tape.rs`, a SECOND binary that proved a
SECOND step proof — over kimchi's TEST SRS and with **`OsRng`**, so it was not even reproducible —
while `KimchiWrapMain.RC_*` absorbed a THIRD proof's commitments (a third-party
`create_circuit(0,5)` export) and the forty came from the marshaller's. Three proofs, one pipeline,
`prevs = 2 / wComms = 15 / tComms = 7` on all three, and therefore never a red. That binary is
DELETED; this is its replacement and there is one proof.

⚑ **THIS IS DREGG'S OWN STEP PROOF.** The phase-1 Fq tape of a proof of **`{}`** — the circuit
`Dregg2.Circuit.Emit.KimchiStepMain` assembles and `EmitStepMainJson` emits — proved on Vesta with
`ProverProof::create_recursive` over **MINA'S OWN SRS** (`ledger::verifier::get_srs::<Fp>()`,
`SRS::<Vesta>::create(65536)`, which is what pins the IPA to sixteen rounds) and ACCEPTED by the
real `kimchi::verifier::batch_verify`.

⚑ **WHY THE COORDINATES ARE Fq AND NEED NO ENCODING.** A step proof commits on **Vesta**, whose
BASE field is Fq; the wrap circuit's native field is `Tock.Field = Fq`
(`wrap_main_inputs.ml:4,6`) and its inner curve IS Vesta (`wrap_main_inputs.ml:104-105`). So these
words are already elements of the field the wrap sponge computes in. The step proof's SCALAR data
is Fp and would need `Other_field` (one Fq wire, `impls.ml:167-217`, because `p < q` —
`impls.ml:51`); none of it is on this tape.

The challenges below are what **kimchi's own verifier** computed for this proof
(`proof.oracles(...)`), cross-checked against an independent Fq-sponge replay in the exporter.

  step circuit : {}
  rows         : {}
  public words : {}
  prev_challenges : {}
  IPA rounds   : {}
  transcript   : {} Fq words / {} Vesta points (sg_old, w_comm, z_comm, t_comm, lr, delta)

⚠ **NO WALL-CLOCK NUMBER APPEARS IN THIS FILE.** The exporter it replaces printed `prove … ms
verify … ms` into the header, which made a *committed generated artifact* differ on every
regeneration — so the one property a generated file has to have, that a second run moves zero
bytes, could never be checked. The timings are in the run log and in `step-tape.json`.
-/
import Dregg2.Circuit.Emit.PastaField

namespace Dregg2.Circuit.Emit.KimchiStepWrapChainFixture

/-! ## The step circuit this tape came from. -/

/-- The Lean-emitted step circuit's name, as it appears in the JSON the prover consumed. -/
def STEP_CIRCUIT : String := "{}"
/-- Its row count. -/
def STEP_ROWS : Nat := {}
/-- Its public-input width. -/
def STEP_PUBLIC : Nat := {}
/-- `Max_proofs_verified.n` worth of recursion accumulators, so the tape's `sg_old` block is real. -/
def STEP_PREV_CHALLENGES : Nat := {}

/-! ## The phase-1 Fq tape, in `kimchi/src/verifier.rs:159-273` order — which is the order
`wrap_verifier.ml:537-631` re-runs in-circuit. -/

/-- The step proof's verifier-index digest (`verifier.rs:162-163`), an Fq element. -/
def STEP_VKDIGEST : Nat := {}

"#,
        circuit_name,
        circuit_name,
        rows,
        public_words,
        prev_challenges.len(),
        ipa_rounds,
        transcript_words,
        transcript_points,
        circuit_name,
        rows,
        public_words,
        prev_challenges.len(),
        dq(&vk_digest),
    ));
    l.push_str(&lean_nat_list(
        "STEP_PREVCOMM_XY",
        "The 2 `RecursionChallenge` commitments, `(x,y)` each (`verifier.rs:165-168`; in-circuit `sg_old`, `wrap_verifier.ml:538`).",
        &prevcomm_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_PUBCOMM_XY",
        "The negated-public-input commitment, `(x,y)` (`verifier.rs:834-858,171`; in-circuit `x_hat`, `wrap_verifier.ml:617`).",
        &pubcomm_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_WCOMM_XY",
        "The 15 witness commitments, `(x,y)` each (`verifier.rs:173-177`; in-circuit `wrap_verifier.ml:619`). ⚑ THESE ARE THE STEP CIRCUIT'S OWN COLUMNS.",
        &wcomm_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_ZCOMM_XY",
        "`z_comm`, absorbed between γ and α′ (`verifier.rs:250`; in-circuit `:623`).",
        &zcomm_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_LR_XY",
        "⚑ The IPA `(L,R)` pairs, four Fq coordinates per round (`wrap_verifier.ml:159-181`, inside `bullet_reduce`). Absorbed AFTER the fork, so they touch no phase-1 challenge — and REAL since 2026-08-05, where `KimchiWrapMainField.lrPointQ` used to hand back `xhatBase (5 + i % 50)`.",
        &lr_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_TCOMM_XY",
        "The chunks of `t_comm`, absorbed between α′ and ζ′ (`verifier.rs:269`; in-circuit `:630`).",
        &tcomm_xy,
    ));

    l.push_str(&format!(
        r#"/-! ## What the o1-labs verifier itself derived from that tape.

These are `proof.oracles(...)`'s own outputs, cross-checked in the exporter against an independent
`DefaultFqSponge<VestaParameters>` replay (`assert_eq!`, not a print). Nothing in Lean may consume
them as given: `KimchiStepWrapChain` RE-DERIVES them from the tape above and pins the result. -/

/-- β — the first `challenge()` (`verifier.rs:233`), 128 bits. -/
def STEP_BETA : Nat := {}
/-- γ (`verifier.rs:236`). -/
def STEP_GAMMA : Nat := {}
/-- α′, the PRECHALLENGE before the endomorphism lift (`verifier.rs:254`). -/
def STEP_ALPHA_CHAL : Nat := {}
/-- ζ′, likewise (`verifier.rs:273`). -/
def STEP_ZETA_CHAL : Nat := {}
/-- The phase-1 digest (`verifier.rs:283`), reinterpreted in Fp. This is
`sponge_digest_before_evaluations` — `wrap_verifier.ml:646`'s FORK squeeze. -/
def STEP_DIGEST : Nat := {}

/-! ## ⚑ THE NEGATIVE CONTROL'S SUBJECT — parts of the SAME step proof that the phase-1 tape does
NOT absorb. Bending any of these leaves every value above unchanged, which is what makes the
positive control a measurement of the WIRE rather than of the proof's mere existence.

`z_1`, `z_2` and `ft_eval1` are **Fp** (Vesta's scalar field) — the data that WOULD need the
`Other_field` encoding to enter the wrap circuit. `sg` is an Fq point phase 1 never sees.

⚠ **`delta` IS NO LONGER IN THIS CATEGORY AND THE ENTRY SAYS SO.** It is absorbed at
`wrap_verifier.ml:420`, inside `check_bulletproof`, which is W-BULLET — a rung that IS assembled.
So `STEP_DELTA_XY` is on the wrap transcript; it is off *phase one*, which is a narrower claim and
the one the control actually measures. -/

/-- The IPA opening scalar `z_1` (Fp) — `openings_proof.z_1`, `wrap_main.ml:357-364`. -/
def STEP_Z1_FP : Nat := {}
/-- The IPA opening scalar `z_2` (Fp). -/
def STEP_Z2_FP : Nat := {}
/-- `ft_eval1` (Fp) — a phase-TWO word; the Fr-sponge absorbs it, the Fq-sponge never does. -/
def STEP_FT_EVAL1_FP : Nat := {}
/-- ⚑ `delta`'s Fq coordinates — absorbed at `wrap_verifier.ml:420`, inside `check_bulletproof`.
REAL since 2026-08-05: `KimchiWrapMainField.deltaPointQ` used to be `xhatBase 60`. -/
def STEP_DELTA_XY : List Nat := [{}, {}]
/-- `sg` (`challenge_polynomial_commitment`)'s Fq coordinates — the NEXT proof's `sg_old`, not this
transcript's input. ⚑ `pickles_kimchi_marshal` MEASURES that this equals
`⟨b_poly_coefficients(u⃗), srs.g⟩` over Mina's own 65,536 generators. -/
def STEP_SG_XY : List Nat := [{}, {}]

/-! ## ⚑ THE POSITIVE CONTROL, MEASURED. The exporter bent tape word `STEP_BENT_INDEX` — the first
Fq coordinate of the step proof's `w_comm` — by one and re-ran the SAME Fq sponge. These are what
it produced. `KimchiStepWrapChain` re-derives them, so "the wrap transcript moves with the step
proof" is a computation both sides perform, not a claim either makes. -/

/-- The absolute index in the tape that was bent: `1 + |sg_old| + |x_hat|`. -/
def STEP_BENT_INDEX : Nat := {}
def STEP_BENT_BETA : Nat := {}
def STEP_BENT_GAMMA : Nat := {}
def STEP_BENT_ALPHA_CHAL : Nat := {}
def STEP_BENT_ZETA_CHAL : Nat := {}
def STEP_BENT_DIGEST : Nat := {}

/-! ## ⚑ THE ONE SCALAR THAT CROSSES FIELDS.

`combined_inner_product` is an **Fp** value — the step proof's own scalar field. `wrap_main.ml:454`
shifts it with `Shifts.tick1 = Shifted_value.Type1.Shift.create (module Tick.Field)`, created over
**Fp** and not over the wrap circuit's Fq (`shifted_value.ml:124-131`: `c = 2^255 + 1`,
`scale = 1/2`, `of_field s = (s − c)·scale`, all in Fp). The shifted Fp element then occupies ONE
Fq wire — `impls.ml:167-217`, `Impls.Wrap.Other_field.t = Field.t`, transported by
`Tock.Field.of_bits ∘ Tick.Field.to_bits`, which is the identity on the integer because `p < q`
(`impls.ml:51`). `wrap_verifier.ml:395` absorbs exactly that one word.

⚑ THIS IS THE WHOLE Fp→Fq CROSSING ON THIS TRANSCRIPT. The commitments needed none: they are Vesta
points and Vesta's BASE field IS Fq. -/

/-- `combined_inner_product`, raw, in Fp. -/
def STEP_CIP_FP : Nat := {}
/-- `Shifted_value.Type1.of_field` of it, still in Fp: `(cip − (2^255+1))·2⁻¹ mod p`. -/
def STEP_CIP_SHIFTED_FP : Nat := {}
/-- The single Fq wire the wrap sponge absorbs — the same integer, since `p < q`. -/
def STEP_CIP_WORD_FQ : Nat := {}

/-- The step proof's IPA round count — how many `(L,R)` pairs `bullet_reduce` absorbs. -/
def STEP_IPA_ROUNDS : Nat := {}

/-! ## ⚑ THE NEGATIVE CONTROL, RE-EXTRACTED.

The exporter took the SAME accepted proof object, bent `z_1`, `z_2`, `ft_eval1`, `delta` and `sg`,
and then extracted the phase-1 tape from the MUTATED object from scratch. The lists below are that
second extraction. Comparing them with the honest ones is therefore a comparison of two independent
extractions from two different proof objects — not a list against itself. -/

/-- The phase-1 tape re-extracted from the unread-bent proof. -/
def STEP_UNREAD_TAPE : List Nat :=
  [{}]
/-- Its `z_comm`. -/
def STEP_UNREAD_ZCOMM_XY : List Nat :=
  [{}]
/-- Its `t_comm`. -/
def STEP_UNREAD_TCOMM_XY : List Nat :=
  [{}]
/-- ...and the five values that DID change, so the bend is not a no-op. -/
def STEP_UNREAD_Z1_FP : Nat := {}
def STEP_UNREAD_Z2_FP : Nat := {}
def STEP_UNREAD_FT_EVAL1_FP : Nat := {}
def STEP_UNREAD_DELTA_XY : List Nat := [{}, {}]
def STEP_UNREAD_SG_XY : List Nat := [{}, {}]

"#,
        dp(&beta),
        dp(&gamma),
        dp(&alpha_chal),
        dp(&zeta_chal),
        dp(&digest),
        dp(&z1),
        dp(&z2),
        dp(&ft_eval1),
        dq(&dx),
        dq(&dy),
        dq(&sx),
        dq(&sy),
        bent_idx,
        dp(&b_beta),
        dp(&b_gamma),
        dp(&b_alpha),
        dp(&b_zeta),
        dp(&b_digest),
        dp(&cip),
        dp(&cip_shifted_fp),
        dq(&cip_word_fq),
        ipa_rounds,
        unread_tape.iter().map(dq).collect::<Vec<_>>().join(", "),
        u_zcomm.iter().map(dq).collect::<Vec<_>>().join(", "),
        u_tcomm.iter().map(dq).collect::<Vec<_>>().join(", "),
        dp(&unread_proof.proof.z1),
        dp(&unread_proof.proof.z2),
        dp(&unread_proof.ft_eval1),
        dq(&udx),
        dq(&udy),
        dq(&usx),
        dq(&usy),
    ));

    // ───────── ⚑ the x_hat MSM's own inputs, as Lean lists ─────────
    l.push_str(&format!(
        r#"/-! ## ⚑ THE `x_hat` MSM'S OWN INPUTS — this proof's public input against THIS PROOF'S
DOMAIN's Lagrange basis.

`wrap_verifier.ml:539-616` computes `x_hat` as `−Σ pᵢ·Lᵢ + Generators.h`, and `:617` absorbs it.
kimchi's own verifier prologue (`verifier.rs:834-857`) computes the SAME object as
`mask_custom(MSM(L, −public_input), 1)` — which is why `STEP_PUBCOMM_XY` above and the MSM over the
three lists below are one value and not two. **The exporter asserts that equality in Rust before
writing this file**, so a base from the wrong domain cannot reach Lean.

⚠ ⚑ **THE DOMAIN IS THE TRAP.** A Lagrange basis is a function of the DOMAIN.
`MinaStepSrsLagrange.LAGRANGE_XY` is taken at `2^Common.Max_degree.step_log2 = 65536`, Mina's
`step-transaction` domain; **this** proof's domain is `2^{}`. Bases from the wrong domain are
on-curve, are genuine SRS Lagrange commitments of the same SRS, and reproduce nothing — the same
shape as `lrPointQ i = xhatBase (5 + i % 50)`, which `onCurveQ` was structurally incapable of
noticing. The exporter therefore checks the RE-DERIVATION, and additionally asserts that the
2^16-domain basis differs from this one.

⚠ ⚑ **THE WIDTHS ARE NOT UNIFORM, AND `STEP_XHAT_BITS` IS WHERE THEY ARE.** These scalars ARE the
packed `Types.Step.Statement` a Pickles step rule carries: `wrap_verifier.ml:542-548` expands its 57
words into 67 entries at **15 at 255 bits, 40 at 128, 12 at 1**. The twelve one-bit entries take
`` `Cond_add `` (`:573-577`) and run NO ladder, so `STEP_XHAT_CORRECTION_XY` below is indexed over
the **55**-entry `Add_with_correction` partition and not over all 67. The exporter refuses to write
this file if a published word does not fit its slot. -/

/-- `log2` of the step proof's own evaluation domain — the wire's `branch_data.domain_log2`, and
`(domain_log2 <<< 2) ||| proofs_verified` is Mina's public-input slot 29. -/
def STEP_DOMAIN_LOG2 : Nat := {}

"#,
        domain_log2, domain_log2
    ));
    l.push_str(&lean_nat_list_fp(
        "STEP_PUBLIC_IN",
        "⚑ The step proof's OWN public input — the `Fp` scalars the MSM scales, in index order. \
         `stepmain_step_r8_finalize.json`'s `public_input`, as the prover consumed it — the packed `Types.Step.Statement`.",
        public_input,
    ));
    l.push_str(&lean_nat_list(
        "STEP_LAGRANGE_XY",
        "⚑ `lagrange ~domain srs i` for `i < STEP_PUBLIC` at **this proof's** domain, `(x,y)` each \
         — Vesta points of Mina's own `SRS::<Vesta>::create(65536)`, taken at `2^STEP_DOMAIN_LOG2` \
         and NOT at the `2^16` `MinaStepSrsLagrange` uses.",
        &lagrange_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_XHAT_CORRECTION_XY",
        "⚑ `lagrange_with_correction`'s second component, `negate (pow2pow g actual_shift)` \
         (`wrap_verifier.ml:247-291`), indexed over the `Add_with_correction` PARTITION ONLY — a \
         one-bit slot takes `Cond_add` (`:573-577`), runs no ladder and has no correction. \
         `actual_shift` is `bits_per_chunk × chunks_needed (num_bits − 1)`, i.e. **255** for a \
         255-bit slot and **130** (not 128) for a 128-bit one.",
        &correction_xy,
    ));
    l.push_str(&lean_nat_list(
        "STEP_XHAT_BITS",
        "⚑ Slot `i`'s packed WIDTH — `Types.Step.Statement`'s own, computed by the exporter's \
         `step_statement_slot_bits` and therefore a SECOND source for \
         `PicklesStepStatement.slotBits`. 15 at 255, 40 at 128, 12 at 1; the exporter refuses to \
         write this file if a published word does not fit its slot.",
        &xhat_bits,
    ));
    l.push_str(&lean_nat_list(
        "STEP_URS_H_XY",
        "⚑ `Generators.h` — the SRS blinding base `x_hat blinding` adds (`wrap_verifier.ml:612-616`) \
         and `mask_custom` adds on the verifier side. Same SRS as `MinaStepSrsLagrange.URS_H_XY`, \
         which is a two-source pin rather than a second copy.",
        &[hx, hy],
    ));
    // ───────── ⚑ the step proof's own `openings.evals` ─────────
    l.push_str(
        r#"/-! ## ⚑ THE STEP PROOF'S OWN `openings.evals` — AND WHICH `finalize_other_proof` THEY ARE FOR.

`Evals.to_absorption_sequence` (`plonk_types.ml`) order: `z`, the six always-on gate selectors
(`generic`, `poseidon`, `complete_add`, `mul`, `emul`, `endomul_scalar`), `w`×15,
`coefficients`×15, `s`×6 — **43** columns, one chunk each. The exporter REFUSES to write this
module if any column is chunked: `evals_of_split_evals` is the identity only at one chunk, and a
43-entry fold over the first chunk of a chunked column is a prefix wearing the name of the whole.

⚠ ⚑ **THESE ARE THE *STEP* CIRCUIT'S FINALIZE INPUT, NOT THE WRAP CIRCUIT'S, AND FOUR DOCBLOCKS
SAID OTHERWISE.** A step circuit verifies WRAP proofs; each wrap proof's statement carries deferred
values ABOUT the step proof it wrapped, and those are **Fp** — Vesta's scalar field, native to a
step circuit. So `step_main`'s `finalize_other_proof` reads THESE, and
`KimchiStepMainCore.evVal`'s mixer is what stands where they belong.

`wrap_main`'s `finalize_other_proof` reads the other side of the cycle: deferred values about
**wrap** proofs, in **Fq** at the wrap domain, folded with `Scalars.Tock` and closed with
`Shifted_value.Type2`. That is why `KimchiWrapMain` §19's `FIN_OMEGA` and `FIN_SHIFTS` are Mina's
devnet WRAP verifier index's, and why §19c reads `MinaRealBlockGate.EVZ`/`EVZW` rather than
anything in this file. **Exporting these here does not make them that object**, and the sentence
"they are Fp, so they enter only through `Other_field`, and that encoding is the distance to the
top of the ladder" was wrong about which finalize it was describing. -/

"#,
    );
    l.push_str(&lean_nat_list_fp(
        "STEP_EVALS_ZETA",
        "⚑ The step proof's 43 `to_absorption_sequence` columns at ζ, one chunk each (Fp).",
        &ev_zeta,
    ));
    l.push_str(&lean_nat_list_fp(
        "STEP_EVALS_ZETAW",
        "…and at ζω.",
        &ev_zetaw,
    ));
    l.push_str(&lean_nat_list_fp(
        "STEP_PUB_EVAL",
        "⚑ `evals.public_input` — `(p(ζ), p(ζω))` of the same proof. `STEP_FT_EVAL1_FP` above is \
         its partner; together they are the five-element prefix a finalize sponge absorbs ahead of \
         the 43 columns.",
        &[pub_eval_z, pub_eval_w],
    ));
    l.push_str("end Dregg2.Circuit.Emit.KimchiStepWrapChainFixture\n");

    // ───────────────────── W-KEY's module ─────────────────────
    let mut k = String::new();
    k.push_str(&format!(
        r#"/-
# KimchiStepWrapChainKey — GENERATED. DO NOT EDIT.

Written by `metatheory/fixtures/pickles-extractors/src/tape.rs`, in the SAME RUN that wrote
`KimchiStepWrapChainFixture` — from the SAME `VerifierIndex`, of the SAME proof whose forty public
words `pickles_kimchi_marshal` prints.

⚑ **DREGG'S OWN STEP CIRCUIT'S VERIFICATION KEY**, flattened to the 56 Fq coordinates
`Pickles_base.Side_loaded_verification_key.index_to_field_elements` produces
(`side_loaded_verification_key.ml:159-183`): 7 `sigma_comm`, 15 `coefficients_comm`, then
`generic_comm`, `psm_comm`, `complete_add_comm`, `mul_comm`, `emul_comm`, `endomul_scalar_comm`.

⚑ **WHY THIS IS A MODULE OF ITS OWN.** `KimchiWrapMainCore.keyConst` — the per-branch step-key table
`choose_key` (`wrap_verifier.ml:189-204`) folds — sits BELOW `KimchiStepWrapChainFixture` in the
import graph, so it cannot see the tape module. This is a second MODULE and not a second SOURCE: one
binary, one `VerifierIndex`, one run.

⚑ **THE PREIMAGE IDENTITY, ASSERTED IN RUST BEFORE THIS FILE WAS WRITTEN.** A fresh
`DefaultFqSponge<VestaParameters>` fed exactly these 56 words reproduces
`VerifierIndex::digest::<BaseSponge>()`, which is `KimchiStepWrapChainFixture.STEP_VKDIGEST`, which
is the FIRST WORD of the phase-1 tape `kimchi::verifier` itself absorbed for the accepted proof. So
committing to these 56 numbers and absorbing that digest are the same act, and
`KimchiStepWrapChain.the_chain_climbs_past_bind_at_dreggs_own_step_key` re-derives the identity in
Lean rather than trusting this sentence.

⚑ **AND NONE OF THE 28 POINTS IS THE IDENTITY** — asserted in Rust, refusing to emit otherwise.
`index_to_field_elements` flattens infinity as the fake point `(0,0)`, which is off `y² = x³ + 5`,
and W-COMBINE folds these 28 with the INCOMPLETE `Ops.add_fast`; one identity commitment leaves
`bulletproof_success` with no satisfying witness. kimchi's own `create_circuit(0,5)` test key had
seven, which is the defect this whole line of work walked out of.

  step circuit : {}
  rows         : {}
  public words : {}
  points at infinity : 0 of 28
-/

namespace Dregg2.Circuit.Emit.KimchiStepWrapChainKey

"#,
        circuit_name, rows, public_words
    ));
    k.push_str("/-- The 56 coordinates, `index_to_field_elements` order. -/\ndef STEP_OWN_VK_XY : List Nat :=\n[\n");
    for (i, chunk) in index_xy.chunks(4).enumerate() {
        let last = (i + 1) * 4 >= index_xy.len();
        k.push_str("  ");
        k.push_str(&chunk.iter().map(dq).collect::<Vec<_>>().join(", "));
        k.push_str(if last { "\n" } else { ",\n" });
    }
    k.push_str("]\n\n");
    let _ = write!(
        k,
        "/-- The digest RUST KIMCHI computed for that index — the same number\n\
         `KimchiStepWrapChainFixture.STEP_VKDIGEST` carries, re-stated here so this module stands\n\
         alone below the fixture and `chain_key_module_agrees_with_the_tape` can tie the two. -/\n\
         def STEP_OWN_VK_DIGEST : Nat := {}\n\n",
        dq(&vk_digest)
    );
    k.push_str("end Dregg2.Circuit.Emit.KimchiStepWrapChainKey\n");

    // ───────────────────── the JSON sidecar ─────────────────────
    let json = serde_json::json!({
        "step_circuit": circuit_name,
        "step_rows": rows,
        "step_public": public_words,
        "prev_challenges": prev_challenges.len(),
        "prove_ms": prove_ms,
        "verify_ms": verify_ms,
        "vk_digest": dq(&vk_digest),
        "index_xy": index_xy.iter().map(dq).collect::<Vec<_>>(),
        "prevcomm_xy": prevcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "pubcomm_xy": pubcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "w_comm_xy": wcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "z_comm_xy": zcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "t_comm_xy": tcomm_xy.iter().map(dq).collect::<Vec<_>>(),
        "lr_xy": lr_xy.iter().map(dq).collect::<Vec<_>>(),
        "delta_xy": [dq(&dx), dq(&dy)],
        "sg_xy": [dq(&sx), dq(&sy)],
        "transcript_words": transcript_words,
        "transcript_points": transcript_points,
        "beta": dp(&beta),
        "gamma": dp(&gamma),
        "alpha_chal": dp(&alpha_chal),
        "zeta_chal": dp(&zeta_chal),
        "digest": dp(&digest),
        "z1_fp": dp(&z1),
        "z2_fp": dp(&z2),
        "ft_eval1_fp": dp(&ft_eval1),
        "ipa_rounds": ipa_rounds,
        "bent_index": bent_idx,
        "bent": { "beta": dp(&b_beta), "gamma": dp(&b_gamma), "alpha_chal": dp(&b_alpha),
                  "zeta_chal": dp(&b_zeta), "digest": dp(&b_digest) },
        "cip_fp": dp(&cip),
        "cip_shifted_fp": dp(&cip_shifted_fp),
        "cip_word_fq": dq(&cip_word_fq),
        // ⚑ the STEP circuit's finalize input — Fp, one chunk per column. NOT the wrap's.
        "evals_zeta_fp": ev_zeta.iter().map(dp).collect::<Vec<_>>(),
        "evals_zeta_omega_fp": ev_zetaw.iter().map(dp).collect::<Vec<_>>(),
        "public_eval_fp": [dp(&pub_eval_z), dp(&pub_eval_w)],
    });

    StepTapeOut {
        fixture_lean: l,
        key_lean: k,
        json,
        tape_words: tape.len(),
        transcript_words,
        transcript_points,
        ipa_rounds,
    }
}
