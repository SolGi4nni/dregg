//! **THE THREE GATES PICKLES PASSES BEFORE IT CONSULTS A KEY — DRIVEN, AND THEIR LITERAL
//! VERDICTS.**
//!
//! `verify_zkapp` (`proofs/verification.rs:829-855`) is one `bool` over
//! `accumulator_check && verify_impl`, and `verify_impl` (`:858-894`) is five steps deep. Four of
//! those five are **private** (`run_checks`, `compute_deferred_values`,
//! `get_message_for_next_step_proof`, `get_prepared_statement`), so a single `false` says nothing
//! about where it stopped. This module drives the ladder rung by rung so that a refusal has a
//! NAME.
//!
//! | rung | what it decides | how it is reached here |
//! |---|---|---|
//! | **A** `accumulator_check` | `C == ⟨b_poly_coefficients(u⃗), srs.g⟩` | **Mina's own**, `pub` |
//! | **B** `expand_deferred` | recomputes ξ, r, `combined_inner_product`, `b`, `perm`, `ζ^…` | **Mina's own**, `pub` |
//! | **checks** `run_checks` | chunk arity, feature flags, domain bounds | TRANSCRIBED, `fn` |
//! | **C** `…_for_next_{step,wrap}_proof.hash()` | binds the VK's 28 points and the app state | **Mina's own**, `pub` |
//! | **terminal** `to_public_input(40)` | the forty words the wrap circuit must have as PUBLIC INPUT | **Mina's own**, `pub` |
//!
//! ⚑ **Transcription is marked as transcription.** `run_checks` is reproduced here from
//! `verification.rs:557-675` because it cannot be called; it is NOT evidence in the way rungs A,
//! B, C and the terminal are, and it is labelled so in the output.
//!
//! ## What the terminal rung is FOR
//!
//! `to_public_input` is not a check — it is the **specification of the wrap circuit's public
//! input**. Pickles demands forty field elements in a fixed order (`prepared_statement.rs:53-183`,
//! `composition_types.ml:739`):
//!
//! ```text
//!   0 combined_inner_product   5 beta            10 sponge_digest_before_evaluations
//!   1 b                        6 gamma           11 hash(messages_for_next_wrap_proof)
//!   2 zeta_to_srs_length       7 alpha           12 hash(messages_for_next_step_proof)
//!   3 zeta_to_domain_size      8 zeta            13..28 bulletproof_challenges (16)
//!   4 perm                     9 xi              …  branch_data
//! ```
//!
//! Slots 0–4 and 9 are **`expand_deferred`'s recomputation, not the proof's claim** — the wire
//! does not carry them at all (`generated.rs:805-810`: `deferred_values` is `plonk`,
//! `bulletproof_challenges`, `branch_data`, and nothing else). So a wrap circuit that reads its
//! own fixtures for those words is reading numbers Pickles will overwrite. [`wrap_public_input`]
//! emits what Pickles will actually hand it.

use ark_ff::PrimeField;
use ledger::proofs::accumulator_check::accumulator_check;
use ledger::proofs::public_input::messages::{MessagesForNextStepProof, MessagesForNextWrapProof};
use ledger::proofs::public_input::prepared_statement::{
    DeferredValues, PreparedStatement, ProofState,
};
use ledger::proofs::step::{expand_deferred, ExpandDeferredParams, StatementProofState};
use ledger::proofs::transaction::{InnerCurve, PlonkVerificationKeyEvals};
use ledger::proofs::unfinalized::AllEvals;
use ledger::proofs::util::{extract_bulletproof, extract_polynomial_commitment, two_u64_to_field};
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
use mina_p2p_messages::v2::PicklesProofProofsVerified2ReprStableV2;
use poly_commitment::ipa::SRS;

/// The wire object every rung is asked about.
pub type Wire = PicklesProofProofsVerified2ReprStableV2;

/// `zk_rows` for a side-loaded wrap verification —
/// `side_loaded_verification_key.ml:232`, hardcoded 3 at `verifiers.rs:441` and
/// `verification.rs:704`.
pub const ZK_ROWS: u64 = 3;

/// The wrap circuit's public input count. `verifiers.rs:400` — `let public = 40; // Is that
/// constant ?`. It is not derived from the VK, so it is not negotiable per-app.
pub const WRAP_PUBLIC_INPUT: usize = 40;

// ───────────────────────────── Gate A ─────────────────────────────

/// **Mina's own `accumulator_check`, run on our object.**
///
/// `Err` means a coordinate was not a field element; `Ok(false)` means the batched MSM did not
/// vanish. Both are refusals and they are different refusals.
pub fn gate_a(srs: &SRS<Vesta>, wire: &Wire) -> Result<bool, String> {
    accumulator_check(srs, &[wire]).map_err(|e| format!("{e:?}"))
}

// ───────────────────────────── Gate B ─────────────────────────────

/// **`compute_deferred_values`, reconstructed around Mina's own `expand_deferred`.**
///
/// `compute_deferred_values` (`verification.rs:676-717`) is private; every part of it that does
/// arithmetic — `expand_deferred`, the two `TryFrom`s, `extract_bulletproof`, `two_u64_to_field`
/// — is public and is what is called here. The wrapper is fifteen lines of plumbing and is
/// reproduced exactly, INCLUDING the detail that it overwrites `expand_deferred`'s endo-lifted
/// `bulletproof_challenges` with the RAW two-limb values (`:684-690` vs `step.rs:2036-2042`):
/// the wrap circuit's public input carries prechallenges, and the lift happens in-circuit.
pub fn gate_b(wire: &Wire) -> anyhow::Result<DeferredValues<Fp>> {
    let bulletproof_challenges: Vec<Fp> = wire
        .statement
        .proof_state
        .deferred_values
        .bulletproof_challenges
        .iter()
        .map(|chal| {
            let pre: [u64; 2] = chal.prechallenge.inner.each_ref().map(|v| v.as_u64());
            two_u64_to_field(&pre)
        })
        .collect();

    let old_bulletproof_challenges: Vec<[Fp; 16]> = wire
        .statement
        .messages_for_next_step_proof
        .old_bulletproof_challenges
        .iter()
        .map(|v| {
            v.0.clone()
                .map(|v| two_u64_to_field(&v.prechallenge.inner.0.map(|v| v.as_u64())))
        })
        .collect();

    let proof_state: StatementProofState = (&wire.statement.proof_state).try_into()?;
    let evals: AllEvals<Fp> = (&wire.prev_evals).try_into()?;

    let deferred = expand_deferred(ExpandDeferredParams {
        evals: &evals,
        old_bulletproof_challenges: &old_bulletproof_challenges,
        proof_state: &proof_state,
        zk_rows: ZK_ROWS,
    })?;

    Ok(DeferredValues {
        bulletproof_challenges,
        ..deferred
    })
}

// ───────────────────────────── the `run_checks` rung ─────────────────────────────

/// ⚠ **TRANSCRIBED, not called.** `run_checks` is `fn` at `verification.rs:557`. The three
/// conditions it evaluates that do not need a verifier index are reproduced; the two that compare
/// against `verifier_index.domain.log_size_of_group` take it as an argument.
///
/// `validate_feature_flags` is also private and is reproduced by its contract rather than its
/// body: with every flag `false`, every optional evaluation must be absent.
pub fn run_checks_transcribed(wire: &Wire, wrap_domain_log2: u32) -> Vec<(&'static str, bool)> {
    let e = &wire.prev_evals.evals.evals;
    let mut single = true;
    {
        let mut check = |p: &(
            mina_p2p_messages::array::ArrayN16<mina_p2p_messages::bigint::BigInt>,
            mina_p2p_messages::array::ArrayN16<mina_p2p_messages::bigint::BigInt>,
        )| {
            single = single && p.0.len() <= 1 && p.1.len() <= 1;
        };
        for p in e.w.iter() {
            check(p);
        }
        for p in e.coefficients.iter() {
            check(p);
        }
        check(&e.z);
        for p in e.s.iter() {
            check(p);
        }
        for p in [
            &e.generic_selector,
            &e.poseidon_selector,
            &e.complete_add_selector,
            &e.mul_selector,
            &e.emul_selector,
            &e.endomul_scalar_selector,
        ] {
            check(p);
        }
    }

    let ff = &wire
        .statement
        .proof_state
        .deferred_values
        .plonk
        .feature_flags;
    let all_off = !ff.range_check0
        && !ff.range_check1
        && !ff.foreign_field_add
        && !ff.foreign_field_mul
        && !ff.xor
        && !ff.rot
        && !ff.lookup
        && !ff.runtime_tables;
    let no_optional_evals = e.range_check0_selector.is_none()
        && e.range_check1_selector.is_none()
        && e.foreign_field_add_selector.is_none()
        && e.foreign_field_mul_selector.is_none()
        && e.xor_selector.is_none()
        && e.rot_selector.is_none()
        && e.lookup_aggregation.is_none()
        && e.lookup_table.is_none();

    let step_domain = wire
        .statement
        .proof_state
        .deferred_values
        .branch_data
        .domain_log2
        .as_u8() as u32;

    vec![
        ("only uses single chunks", single),
        (
            "feature flags are consistent with evaluations",
            all_off == no_optional_evals,
        ),
        (
            "domain size is small enough (step <= 16)",
            step_domain <= 16,
        ),
        (
            "actual_wrap_domain <= least_wrap_domain (15)",
            wrap_domain_log2 <= 15,
        ),
        (
            "actual_wrap_domain >= greatest_wrap_domain (13)",
            wrap_domain_log2 >= 13,
        ),
    ]
}

// ───────────────────────────── Gate C and the terminal ─────────────────────────────

/// The 28 wrap-index points as Pickles types them, taken from a kimchi verifier index we produced.
///
/// ⚠ **This is not a minted VK.** It is the verifier index of the circuit that produced the proof,
/// re-typed. A `PlonkVerificationKeyEvals` with any other provenance would be a key chosen to fit,
/// which is the thing this pipeline refuses to do.
pub fn vk_evals_of_wrap_index(
    vk: &kimchi::verifier_index::VerifierIndex<
        { mina_poseidon::pasta::FULL_ROUNDS },
        Pallas,
        SRS<Pallas>,
    >,
) -> PlonkVerificationKeyEvals<Fp> {
    let one = |c: &poly_commitment::PolyComm<Pallas>| {
        assert_eq!(c.chunks.len(), 1, "a wrap index commitment is one chunk");
        InnerCurve::<Fp>::of_affine(c.chunks[0])
    };
    PlonkVerificationKeyEvals {
        sigma: std::array::from_fn(|i| one(&vk.sigma_comm[i])),
        coefficients: std::array::from_fn(|i| one(&vk.coefficients_comm[i])),
        generic: one(&vk.generic_comm),
        psm: one(&vk.psm_comm),
        complete_add: one(&vk.complete_add_comm),
        mul: one(&vk.mul_comm),
        emul: one(&vk.emul_comm),
        endomul_scalar: one(&vk.endomul_scalar_comm),
    }
}

/// **Gate C, both halves, with Mina's own hashers.**
///
/// `get_message_for_next_step_proof` hashes the VK's 28 points AND the app state alongside the
/// wire's recursion data (`messages.rs:138-200`), which is why a wrap proof is never portable
/// between keys: slot 12 of the public input moves when the key does.
pub fn gate_c(
    wire: &Wire,
    vk_evals: &PlonkVerificationKeyEvals<Fp>,
) -> anyhow::Result<([u64; 4], [u64; 4])> {
    let m = &wire.statement.messages_for_next_step_proof;
    let challenge_polynomial_commitments: Vec<InnerCurve<Fp>> =
        extract_polynomial_commitment(&m.challenge_polynomial_commitments)?;
    let old_bulletproof_challenges: Vec<[Fp; 16]> =
        extract_bulletproof(&m.old_bulletproof_challenges);
    let step = MessagesForNextStepProof {
        app_state: &(),
        dlog_plonk_index: vk_evals,
        challenge_polynomial_commitments,
        old_bulletproof_challenges,
    };

    let w = &wire.statement.proof_state.messages_for_next_wrap_proof;
    let cpc: Vec<InnerCurve<Fq>> =
        extract_polynomial_commitment(std::slice::from_ref(&w.challenge_polynomial_commitment))?;
    let old: Vec<[Fq; 15]> = extract_bulletproof(&[
        w.old_bulletproof_challenges[0].0.clone(),
        w.old_bulletproof_challenges[1].0.clone(),
    ]);
    let wrap = MessagesForNextWrapProof {
        challenge_polynomial_commitment: cpc[0].clone(),
        old_bulletproof_challenges: old,
    };

    Ok((step.hash(), wrap.hash()))
}

/// **The forty field elements Pickles will hand the wrap circuit as its public input.**
///
/// `get_prepared_statement` (`verification.rs:477-497`) is private; every constituent is public
/// and is assembled here in its order. `to_public_input` is Mina's own.
///
/// This is the object the wrap emit path needs and does not have. It is not a check we can pass
/// today — it is the statement of what "a real wrap proof" would have to be a proof OF.
pub fn wrap_public_input(
    wire: &Wire,
    vk_evals: &PlonkVerificationKeyEvals<Fp>,
    deferred: DeferredValues<Fp>,
) -> anyhow::Result<Vec<Fq>> {
    let (step_hash, wrap_hash) = gate_c(wire, vk_evals)?;
    let digest: [u64; 4] = wire
        .statement
        .proof_state
        .sponge_digest_before_evaluations
        .each_ref()
        .map(|v| v.as_u64());
    let prepared = PreparedStatement {
        proof_state: ProofState {
            deferred_values: deferred,
            sponge_digest_before_evaluations: digest,
            messages_for_next_wrap_proof: wrap_hash,
        },
        messages_for_next_step_proof: step_hash,
    };
    prepared.to_public_input(WRAP_PUBLIC_INPUT)
}

/// The name of every one of the forty public words, in order —
/// `prepared_statement.rs:88-181`.
///
/// ⚑ All forty are meaningful; `to_public_input` ends with
/// `assert_eq!(fields.len(), npublic_input)`, so there is no padding to ignore. `branch_data` is
/// the packed `(domain_log2 << 2) | proofs_verified` (`branch_data.ml:63`), the eight feature
/// flags are booleans in struct order (`step.rs:125-150`), `uses_lookup` is their disjunction
/// minus `foreign_field_add` and `runtime_tables` (`composition_types.ml:146`), and the last word
/// is the joint combiner or zero.
pub fn wrap_public_input_slot_names() -> Vec<String> {
    let mut v: Vec<String> = vec![
        "combined_inner_product".into(),
        "b".into(),
        "zeta_to_srs_length".into(),
        "zeta_to_domain_size".into(),
        "perm".into(),
        "beta".into(),
        "gamma".into(),
        "alpha".into(),
        "zeta".into(),
        "xi".into(),
        "sponge_digest_before_evaluations".into(),
        "messages_for_next_wrap_proof(hash)".into(),
        "messages_for_next_step_proof(hash)".into(),
    ];
    for i in 0..16 {
        v.push(format!("bulletproof_challenges[{i}]"));
    }
    v.push("branch_data((domain_log2<<2)|proofs_verified)".into());
    for f in [
        "range_check0",
        "range_check1",
        "foreign_field_add",
        "foreign_field_mul",
        "xor",
        "rot",
        "lookup",
        "runtime_tables",
    ] {
        v.push(format!("feature_flags.{f}"));
    }
    v.push("uses_lookup".into());
    v.push("joint_combiner_or_zero".into());
    debug_assert_eq!(v.len(), WRAP_PUBLIC_INPUT);
    v
}

/// A field element as decimal — the form every emitted fixture in this tree uses.
pub fn dec<F: PrimeField>(f: &F) -> String {
    f.into_bigint().to_string()
}

/// `expand_deferred` hands back `combined_inner_product` and `b` in Pickles' SHIFTED encoding
/// (`plonk_checks.rs:67-95`), which is what the public input carries. Comparing a shifted value
/// against a raw one is comparing two different numbers and would read as a disagreement that is
/// not there — so the un-shift is re-exported and used at every comparison site.
pub use ledger::proofs::public_input::plonk_checks::ShiftingValue;
