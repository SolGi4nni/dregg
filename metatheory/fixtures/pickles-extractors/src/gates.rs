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
use mina_p2p_messages::v2::{
    PicklesProofProofsVerified2ReprStableV2,
    PicklesProofProofsVerified2ReprStableV2MessagesForNextStepProof,
};
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

/// ⚑ **`N_PREVIOUS` FOR DREGG'S OWN STEP RULE — ONE, AND THE RECORD IS UNPADDED AT IT.**
///
/// `step.rs:2676-2679` names the three cases outright: *"For block and merge proofs, the number is
/// 2; for zkapp with proof authorization, it's 1; for other proofs, it's 0."* Dregg's step rule
/// (`KimchiStepMainCore`) assembles ONE `verify_one`, and its `branch_data.proofs_verified_mask` is
/// `Prefix_mask.there N1` — one previous proof of two slots.
///
/// ⚠ **AND THE RECORD IS THE ONE FIELD THAT IS NOT PADDED.** `step.rs:2848-2857` builds
/// `challenge_polynomial_commitments` as `prevs.iter().map(…).collect()` over
/// `prevs: [PerProofWitness; N_PREVIOUS]` and `old_bulletproof_challenges` as the vector
/// `verify_one` returned — while the SAME function pads `messages_for_next_wrap_proof` (`:2764-2772`)
/// and `unfinalized_proofs` (`:2861-2868`) to two, explicitly and in view. The omission is
/// deliberate, and `wrap.rs:658-666` is what consumes it: `actual_proofs_verified` is literally
/// `<the record>.old_bulletproof_challenges.len()`.
pub const STEP_RULE_N_PREVIOUS: usize = 1;

/// ⚑ **DREGG'S STEP RULE'S APP STATE — `KimchiStepMainCore.hmOVal 0` and `1`.**
///
/// `(23 + 5000011·i + 11·i²) mod p`, the two words segment D's `Not_opt` prefix absorbs after the
/// index. They are the INDUCTIVE RULE's own statement: no `verify_one` sub-circuit derives them, so
/// the step assembly names them as witnesses and this is the same pair read from the other side.
///
/// ⚠ **THIS IS A SNAPSHOT AND IT IS GUARDED AS ONE.** `segd_slot12_probe` hashes segment D's whole
/// preimage — these two words included — with openmina's own `MessagesForNextStepProof::hash()` and
/// compares the result against the step statement's published word 54 read out of the tracked
/// `KimchiStepWrapChainFixture`. If `hmOVal` moves and this does not, that probe REFUSES.
pub const STEP_RULE_APP_STATE: [&str; 2] = ["23", "5000045"];

/// …as field elements.
pub fn step_rule_app_state() -> Vec<Fp> {
    use std::str::FromStr;
    STEP_RULE_APP_STATE
        .iter()
        .map(|s| Fp::from_str(s).expect("an app-state word is a decimal numeral"))
        .collect()
}

// ───────────────────────────── Gate A ─────────────────────────────

/// **Mina's own `accumulator_check`, run on our object.**
///
/// `Err` means a coordinate was not a field element; `Ok(false)` means the batched MSM did not
/// vanish. Both are refusals and they are different refusals.
pub fn gate_a(srs: &SRS<Vesta>, wire: &Wire) -> Result<bool, String> {
    accumulator_check(srs, &[wire]).map_err(|e| format!("{e:?}"))
}

// ───────────────────────────── Gate A2 ─────────────────────────────

/// One reconstructed recursion slot: what a Mina reader will hand `kimchi::verifier::verify`.
#[derive(Debug, Clone, PartialEq)]
pub struct ReconstructedSlot {
    /// `true` when the commitment came from the wire, `false` when the reader had to invent it —
    /// `dummy_ipa_wrap_sg()`, inserted at the front.
    pub from_wire: bool,
    pub comm: Pallas,
    pub chals: [Fq; 15],
}

/// ⚑⚑⚑ **GATE A2 — THE RECURSION PAIR, AS MINA'S READER REBUILDS IT.**
///
/// `accumulator_check` (gate A) is a **different pair**: the Vesta `messages_for_next_wrap_proof
/// .challenge_polynomial_commitment` against the sixteen `deferred_values.bulletproof_challenges`.
/// It is `Ok(true)` on an object whose *other* accumulator — the Pallas one the wrap proof's own
/// kimchi `prev_challenges` carries — is completely mispaired, because nothing in gate A touches
/// it. That blind spot is what this rung exists for.
///
/// This is `prover.rs:113-158 make_padded_proof_from_p2p`'s recursion-slot assembly, reproduced
/// (the function is private, and `mod prover` is not `pub`):
///
/// ```text
/// let mut comms = statement.messages_for_next_step_proof.challenge_polynomial_commitments;
/// while comms.len() < 2 { comms.push_front(get_challenge_polynomial_commitments_padding()); }
/// zip(comms, extract_bulletproof(statement.proof_state
///                                 .messages_for_next_wrap_proof.old_bulletproof_challenges))
/// ```
///
/// The result is exactly what `verify_impl` gives o1-labs' verifier as `prev_challenges`. A caller
/// compares it against the `RecursionChallenge`s the proof was actually made with; anything that
/// does not match means Mina will verify a proof we did not produce.
///
/// ⚠ The padding constant is `prover.rs:13-28`, which is `dummy_ipa_wrap_sg()`
/// (`wrap.rs:545-568`) as a literal — the same point `MinaWrapHackDummySg.DUMMY_WRAP_SG` exports,
/// and the same point `wrap.rs:736` prepends on the PROVER side. Reader and prover pad with one
/// constant; that is why the reconstruction is meant to be exact and not approximate.
pub fn gate_a2(wire: &Wire) -> Result<Vec<ReconstructedSlot>, String> {
    // `prover.rs:13-28 get_challenge_polynomial_commitments_padding()` — `dummy_ipa_wrap_sg()`.
    let pad = ledger::proofs::wrap::dummy_ipa_wrap_sg();

    let comms: Vec<InnerCurve<Fp>> = extract_polynomial_commitment(
        &wire
            .statement
            .messages_for_next_step_proof
            .challenge_polynomial_commitments,
    )
    .map_err(|e| format!("{e:?}"))?;
    let mut comms: Vec<(bool, Pallas)> = comms
        .iter()
        .map(|c| (true, InnerCurve::to_affine(c)))
        .collect();
    while comms.len() < crate::marshal::PROOFS_VERIFIED {
        comms.insert(0, (false, pad));
    }

    let old = &wire
        .statement
        .proof_state
        .messages_for_next_wrap_proof
        .old_bulletproof_challenges;
    let chals: Vec<[Fq; 15]> = extract_bulletproof(&[old.0[0].0.clone(), old.0[1].0.clone()]);

    Ok(comms
        .into_iter()
        .zip(chals)
        .map(|((from_wire, comm), chals)| ReconstructedSlot {
            from_wire,
            comm,
            chals,
        })
        .collect())
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

/// **The 28 points of a `PlonkVerificationKeyEvals`, flattened in `to_field_elements` order** —
/// `sigma[0..7]`, `coefficients[0..15]`, `generic`, `psm`, `complete_add`, `mul`, `emul`,
/// `endomul_scalar`, each as `(x, y)`. This is the order `sponge_after_index` absorbs
/// (`step_verifier.ml:1149-1157`) and the order `segd_slot12_probe` reconstructs.
pub fn vk_evals_flat(vk: &PlonkVerificationKeyEvals<Fp>) -> Vec<Fp> {
    let mut out = Vec::with_capacity(56);
    let mut push = |c: &InnerCurve<Fp>| {
        let a = c.to_affine();
        out.push(a.x);
        out.push(a.y);
    };
    for s in vk.sigma.iter() {
        push(s);
    }
    for c in vk.coefficients.iter() {
        push(c);
    }
    for p in [
        &vk.generic,
        &vk.psm,
        &vk.complete_add,
        &vk.mul,
        &vk.emul,
        &vk.endomul_scalar,
    ] {
        push(p);
    }
    assert_eq!(out.len(), 56, "28 points, two coordinates each");
    out
}

/// ⚑⚑ **THE LEAN FIXTURE FOR THE OUTER `dlog_plonk_index` — dregg's OWN wrap verification key.**
///
/// `step.rs:2718` is `let dlog_plonk_index = w.exists(super::merge::dlog_plonk_index(wrap_prover))`
/// — the index the OUTER `hash_messages_for_next_step_proof` absorbs is **the instance's own wrap
/// key**, not the previous branch's. Only `expand_proof` gets the previous branch's (`:2725,2734`),
/// and that is what the INNER, `_opt` hash uses. Two hashes, two keys.
///
/// The step assembly's segment D absorbed `MinaStepPrevCommitments.INDEX_XY` — Mina devnet block
/// 539508's `wrap-transaction` key, which is right for segment C and wrong for segment D. This is
/// the module that gives it the right one.
///
/// ⚠ **AND IT IS A WITNESS ON THE STEP SIDE, NOT A PINNED CONSTANT.** `w.exists` is what keeps the
/// two circuits stratified: the wrap circuit pins the step keys as `Inner_curve.constant`
/// (`wrap_main.ml:98-101`), so its coefficients carry the step VK; if the step circuit pinned the
/// wrap VK back, the two key equations would close on each other and neither VK would be
/// computable. `KimchiStepWrapChain.the_wrap_gates_carry_the_step_key_and_none_of_the_step_proofs_values`
/// is the measurement.
///
/// ⚠ `rung` is the emitting binary's `WRAP_RUNG` and is INTERPOLATED into the generated docblock
/// rather than spelled there. It was spelled, and it went stale the day `WRAP_RUNG` moved from
/// `wrapmain_smoke_w1_transcript.json` to `wrapmain_smoke_w4_bind.json` (2026-08-10): the module
/// then named a 0-arity circuit as the one whose key it carried, while carrying the 40-arity one's.
/// A generated file that describes its own provenance must derive that description from the same
/// constant the value came from, or it is a second copy that can disagree.
pub fn wrap_own_vk_lean(vk: &PlonkVerificationKeyEvals<Fp>, rung: &str) -> String {
    let flat = vk_evals_flat(vk);
    let mut s = String::new();
    s.push_str(&format!(
        "/-\n\
         # MinaWrapOwnVerifierKey — dregg's OWN wrap circuit's verification key, 56 coordinates.\n\
         \n\
         ⚑ GENERATED by `pickles-extractors/src/bin/pickles_kimchi_marshal.rs`\n\
         (`gates::wrap_own_vk_lean`). Do not hand-edit: re-run the marshal and copy it over.\n\
         \n\
         These are `vk_evals_of_wrap_index(wrap_index.verifier_index)` — the kimchi verifier index\n\
         of the wrap circuit this pipeline COMPILES AND PROVES (`pickles-wrapmain-harness`'s\n\
         `{rung}`), re-typed as Pickles' `PlonkVerificationKeyEvals` and\n\
         flattened `sigma[0..7] · coefficients[0..15] · generic · psm · complete_add · mul · emul ·\n\
         endomul_scalar`, each point as `(x, y)`. They are **Pallas** points, so their coordinates\n\
         live in Fp — the STEP circuit's own field, which is why segment D can absorb them.\n\
         \n\
         ⚑ WHAT CONSUMES THIS: the OUTER `hash_messages_for_next_step_proof`'s `sponge_after_index`\n\
         (`step_main.ml:525-566`, `step.rs:2718`). The INNER `_opt` hash keeps\n\
         `MinaStepPrevCommitments.INDEX_XY` — the PREVIOUS branch's key (`step.rs:2725,2734`).\n\
         \n\
         ⚠ **A WITNESS, NOT A PIN, AND THAT IS WHAT TERMINATES THE RECURSION.** `KimchiStepMainCore`\n\
         takes these 56 words as `w.exists` (`idxOVar`, no `idxConstRows`), so they reach the step\n\
         circuit's WITNESS and never its gates. The step VK is therefore invariant under this module,\n\
         the wrap gates that pin the step VK as `Inner_curve.constant` are invariant under it, and so\n\
         is the wrap VK this module IS. Re-installing it converges in ONE pass\n\
         (`KimchiStepWrapChain.the_wrap_gates_carry_the_step_key_and_none_of_the_step_proofs_values`,\n\
         `KimchiStepMainPins13.the_cone_of_word_fifty_four_holds_no_published_statement_entry`).\n\
         -/\n\
         namespace Dregg2.Circuit.Emit.MinaWrapOwnVerifierKey\n\n\
         /-- The 28 points as 56 coordinates, `to_field_elements` order. -/\n\
         def INDEX_WORDS : List Nat :=\n[\n"
    ));
    for (i, v) in flat.iter().enumerate() {
        s.push_str("  ");
        s.push_str(&dec(v));
        if i + 1 != flat.len() {
            s.push(',');
        }
        s.push('\n');
    }
    s.push_str(
        "]\n\n\
         /-- …as points. -/\n\
         def INDEX_XY : List (Nat × Nat) :=\n  \
         (List.range 28).map (fun k => (INDEX_WORDS.getD (2 * k) 0, INDEX_WORDS.getD (2 * k + 1) 0))\n\n\
         end Dregg2.Circuit.Emit.MinaWrapOwnVerifierKey\n",
    );
    s
}

/// **Gate C, both halves, with Mina's own hashers.**
///
/// `get_message_for_next_step_proof` hashes the VK's 28 points AND the app state alongside the
/// wire's recursion data (`messages.rs:138-200`), which is why a wrap proof is never portable
/// between keys: slot 12 of the public input moves when the key does.
///
/// ⚑⚑ **THE `app_state: &()` DEFECT, CLOSED 2026-08-07.** This hashed the WIRE's `app_state`, which
/// is `()` — a `unit` on the p2p record — and therefore contributed ZERO field elements where the
/// step circuit's segment D absorbs `N_HM_APP = 2`. That was not a faithful reading of the wire: it
/// was reading the wire where openmina explicitly does not. `verification.rs:438-454` destructures
/// `app_state: _, // unused` and substitutes the CALLER's app state (`:872`), because the record's
/// `app_state` field is erased on the wire and the verifier is expected to know what it is
/// verifying. So the record Pickles hashes has the real app state in it, and this now hands it the
/// same two words segment D absorbs — [`STEP_RULE_APP_STATE`].
///
/// ⚠ **AND THE ARITY IS CHECKED RATHER THAN ACCEPTED.** [`STEP_RULE_N_PREVIOUS`] is what
/// `step.rs:2848-2857` makes the record's length; a record of any other length is a record about a
/// different rule, and the caller is told which so the disagreement is a NAMED refusal instead of a
/// silently different digest. This does NOT truncate: truncating here would make `gate_c` disagree
/// with [`gate_b`], which folds the SAME vector into `expand_deferred`'s `challenges_digest`, and
/// `wrap.rs:658-666` sets the step proof's own kimchi recursion arity from it
/// (`actual_proofs_verified = <the record>.old_bulletproof_challenges.len()`). The three have to
/// move together or ξ stops agreeing.
/// ⚑⚑⚑ **THE STEP RECORD'S `challenge_polynomial_commitment`, AS A LEAN MODULE — cells 58–59 of
/// slot 12.**
///
/// `messages_for_next_step_proof.challenge_polynomial_commitments[i]` is **the WRAP proof's**
/// `prev_challenges[i].comm` (`marshal::marshal` takes a `&WrapKimchiProof`), and kimchi FORCES that
/// to `commit(b_poly(chals))`: an unrelated point makes `batch_verify` return `OpenProof` (measured,
/// first run). **So this point is not a choice on either side** — it is a function of the fifteen
/// prechallenges of its slot alone, and those are the STEP STATEMENT's own packed words
/// (`marshal::step_statement_prechallenges`, entries `32·p + 16 + j`).
///
/// ⚠⚠ **IT IS A PALLAS POINT, AND THE FIRST ATTEMPT AT THIS MODULE PUT A VESTA ONE IN IT.**
/// `challenge_polynomial_commitments` is `Vec<InnerCurve<Fp>>` — coordinates in Fp, the STEP
/// circuit's own native field, which is the only kind of point segment D can absorb. The STEP
/// proof's `prev_challenges[0].comm` is a Vesta point in Fq; installing that emitted a witness whose
/// `assert_on_curve` could not hold and the step prover refused with `"rest of division by vanishing
/// polynomial"`. The measurement that settles which object this is, and it was worth making rather
/// than reasoning about: `accumulator_check.rs:10-64` reads `messages_for_next_WRAP_proof
/// .challenge_polynomial_commitment` (Vesta, slot 11) and is **structurally blind to this one**.
/// What re-derives THIS point is `gate_a2`.
///
/// ⚑ **WHAT CONSUMES THIS: `KimchiStepMainCore`'s segment D, and NOTHING ELSE.** `hmOutSpec` takes
/// it as the `[Gx; Gy]` pair the OUTER `hash_messages_for_next_step_proof` absorbs. §19's
/// `check_bulletproof` keeps `solveG`'s output — see `KimchiStepMainCore.vGaX` for why those are two
/// points in this assembly and one point upstream, and what that costs.
///
/// ⚠ **A WITNESS, NOT A PIN, AND THAT IS WHAT TERMINATES THE FLAG DAY.** The fifteen live at step
/// statement entries 16…30 and 48…62; segment D's squeeze is entry **64**. Re-emitting the step
/// circuit with a different `[Gx; Gy]` was MEASURED to move entry 64 and no other published entry,
/// so the fifteen — and therefore this point — are invariant under the install. One pass.
pub fn step_own_accumulator_lean(acc: &Pallas, chals: &[[u64; 2]]) -> String {
    let (x, y) = (acc.x, acc.y);
    let mut s = String::new();
    s.push_str(&format!(
        "/-\n\
         # MinaStepOwnAccumulator — the step record's own `challenge_polynomial_commitment`.\n\
         \n\
         ⚑ GENERATED by `pickles-extractors/src/bin/pickles_kimchi_marshal.rs`\n\
         (`gates::step_own_accumulator_lean`). Do not hand-edit: re-run the marshal and copy it over.\n\
         \n\
         `commit(b_poly(chals))` over the Tock SRS (`SRS::<Pallas>::create(2 ^ 15)`) at the {n}\n\
         prechallenges of the WRAP proof's PUBLISHED recursion slot — the step statement's own\n\
         packed words, entries `32·p + 16 + j` (`marshal::step_statement_prechallenges`).\n\
         \n\
         It is a **Pallas** point, so its coordinates live in Fp — the step circuit's own field,\n\
         which is why segment D can absorb them. ⚠ The STEP proof's own `prev_challenges[_].comm`\n\
         is a VESTA point in Fq and does NOT belong here; that mistake emitted a witness whose\n\
         `assert_on_curve` could not hold and the step prover refused outright.\n\
         \n\
         ⚑ WHAT BINDS IT ON MINA'S SIDE: **gate A2**, not `accumulator_check`.\n\
         `accumulator_check` reads `messages_for_next_WRAP_proof.challenge_polynomial_commitment`\n\
         (Vesta, slot 11) and is structurally blind to this one. `gates::gate_a2` front-pads the\n\
         step record's commitments with `dummy_ipa_wrap_sg()`, zips them against\n\
         `messages_for_next_wrap_proof.old_bulletproof_challenges`, and checks\n\
         `comm == ⟨b_poly_coefficients(chals), pallas_srs.g⟩` per slot.\n\
         \n\
         ⚑ WHAT CONSUMES THIS: `KimchiStepMainCore.mkStepAtAdvice`'s `specD := hmOutSpec s sp gAcc`,\n\
         i.e. cells 58–59 of the seventy-six `hash_messages_for_next_step_proof` absorbs. §19's\n\
         `check_bulletproof` does NOT: it keeps `solveG`'s output (`StepData.gXY`), and that split\n\
         is stated at `KimchiStepMainCore.vGaX` rather than here.\n\
         \n\
         ⚠ **A WITNESS, NOT A PIN.** These two words reach the step circuit's WITNESS and never its\n\
         gates, so the step VK is invariant under this module. And the fifteen it is taken over are\n\
         statement entries 16…30 / 48…62 while segment D's squeeze is entry 64 — re-emitting with a\n\
         different `[Gx; Gy]` was MEASURED to move entry 64 alone, so the install converges in ONE\n\
         pass, the same asymmetry `MinaWrapOwnVerifierKey`'s docblock states for the 56 index words.\n\
         -/\n\
         namespace Dregg2.Circuit.Emit.MinaStepOwnAccumulator\n\n\
         /-- The accumulator's `x`. -/\n\
         def ACC_X : Nat :=\n  ",
        n = chals.len()
    ));
    s.push_str(&dec(&x));
    s.push_str("\n\n/-- …and its `y`. -/\ndef ACC_Y : Nat :=\n  ");
    s.push_str(&dec(&y));
    s.push_str(
        "\n\n/-- The pair segment D absorbs. -/\n\
         def ACC_XY : Nat × Nat := (ACC_X, ACC_Y)\n\n\
         end Dregg2.Circuit.Emit.MinaStepOwnAccumulator\n",
    );
    s
}

/// ⚑ **THE RECORD'S OWN `challenge_polynomial_commitments`, as the group points the sponge absorbs.**
///
/// Cells 58.. of slot 12's 76-cell preimage. Exposed so a caller can print them beside segment D's
/// own — [`gate_c`] folds them straight into a digest, and a digest cannot say WHICH cell moved.
pub fn record_challenge_polynomial_commitments(
    m: &PicklesProofProofsVerified2ReprStableV2MessagesForNextStepProof,
) -> anyhow::Result<Vec<InnerCurve<Fp>>> {
    Ok(extract_polynomial_commitment(
        &m.challenge_polynomial_commitments,
    )?)
}

/// ⚑ **The record's own `old_bulletproof_challenges`, one `[Fp; 16]` per recursion slot.**
/// The last sixteen cells of slot 12's preimage at `STEP_RULE_N_PREVIOUS = 1`.
pub fn record_old_bulletproof_challenges(
    m: &PicklesProofProofsVerified2ReprStableV2MessagesForNextStepProof,
) -> Vec<[Fp; 16]> {
    extract_bulletproof(&m.old_bulletproof_challenges)
}

pub fn gate_c(
    wire: &Wire,
    vk_evals: &PlonkVerificationKeyEvals<Fp>,
    app_state: &[Fp],
) -> anyhow::Result<([u64; 4], [u64; 4])> {
    let m = &wire.statement.messages_for_next_step_proof;
    let challenge_polynomial_commitments: Vec<InnerCurve<Fp>> =
        extract_polynomial_commitment(&m.challenge_polynomial_commitments)?;
    let old_bulletproof_challenges: Vec<[Fp; 16]> =
        extract_bulletproof(&m.old_bulletproof_challenges);
    let step = MessagesForNextStepProof {
        app_state: &app_state.to_vec(),
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
    app_state: &[Fp],
    deferred: DeferredValues<Fp>,
) -> anyhow::Result<Vec<Fq>> {
    let (step_hash, wrap_hash) = gate_c(wire, vk_evals, app_state)?;
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
