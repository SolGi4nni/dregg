//! # `dregg-lightclient` — the whole-history light client.
//!
//! ## What this is (the magnesium → gold endpoint, Rust side)
//!
//! A light client that trusts the WHOLE finalized history of N turns by verifying ONE succinct
//! recursive aggregate — the [`WholeChainProof`] that `circuit/src/ivc_turn_chain.rs::
//! prove_turn_chain_recursive` folds — and **re-witnessing nothing**: no re-execution of any turn,
//! no re-hashing of any state, no walk of the blocklace. It calls the single succinct verifier
//! [`verify_turn_chain_recursive`] (whose cost is independent of N) and, on success, reads off the
//! public commitments the aggregate binds.
//!
//! This is the executable counterpart of the Lean theorem
//! `Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history`. Under `EngineSound` —
//! the plonky3 FRI obligation `recursive_sound`, the EffectVm circuit⟺executor obligation
//! `leaf_sound`, the `TurnChainBindingAir` obligation `binding_sound` — verifying `agg.root` yields
//! `AggregateAttests`. What the fold discharges in-circuit:
//!
//! - `binding_sound` — ordering (no reorder/drop/insert, the temporal tooth `new_root[i] ==
//!   old_root[i+1]`) and the final root as the genuine fold, via the wrapped `TurnChainBindingAir`
//!   leaf;
//! - `leaf_sound` — **the folded leaves ARE the turn circuits**: each leaf is the Lean-descriptor
//!   EffectVM AIR (`EffectVmDescriptorAir`, the graduated ONE-circuit cutover constraint set —
//!   Poseidon2 state-commit hash sites, transition continuity, `OLD/NEW_COMMIT` PI bindings, range
//!   checks) re-proven over that turn's REAL 186-column execution trace and verified IN-CIRCUIT by
//!   the recursion wrap (`circuit/src/ivc_turn_chain.rs::prove_descriptor_leaf` +
//!   `build_and_prove_next_layer`). The host-side descriptor admission
//!   (`verify_descriptor_participant`) is an admission discipline, NOT the soundness boundary: a
//!   prover that SKIPS it cannot produce a verifying root for a forged turn, because a forged
//!   `(old_root, new_root)` has no satisfying leaf (the `ungated_prover_with_forged_post_commit_
//!   cannot_produce_a_root` / `ungated_prover_with_stub_leaf_cannot_produce_a_root` tamper tests in
//!   `ivc_turn_chain`).
//!
//! The light client additionally holds a **trust anchor**: the [`RecursionVk`] verifier-key
//! fingerprint of the honest root circuit, obtained once from an honest setup fold and distributed
//! exactly like any SNARK VK (genesis/checkpoint configuration — NEVER taken from the artifact under
//! verification). [`verify_history`] refuses unless (1) the presented root's recomputed fingerprint
//! equals the anchor (a from-scratch prover aggregating a DIFFERENT circuit's proofs is refused
//! here — previously the engine reconstructed circuit data from the proof itself and accepted any
//! valid recursive proof), (2) the carried `genesis_root`/`final_root`/`num_turns`/`chain_digest`
//! verify as the public inputs of the carried chain-binding STARK (Fiat–Shamir binds all four, so a
//! relabeled public claim is refused — the publics are read against a proof, not trusted as bare
//! fields), and (3) the root batch proof verifies.
//!
//! What remains NAMED, not discharged (the honest floor): `recursive_sound` — the recursion fork's
//! FRI engine soundness — plus two precisely-scoped fork follow-ups the harness pins narrow but do
//! not close (stated in full in `circuit/src/ivc_turn_chain.rs`'s module docs): (a) the VK pin fixes
//! the ROOT circuit's structure, but the fork's aggregation circuit takes each CHILD proof's
//! preprocessed commitment as a runtime public input living in the constraint-free `PublicAir` trace
//! that host verification never checks, so leaf-circuit identity is not yet pinned in-band; (b) leaf
//! public values are not re-exposed at the root (`into_recursion_input::<BatchOnly>` passes empty
//! `table_public_inputs` and the fork ignores them when building the aggregation circuit), so the
//! carried binding proof is not in-band linked to the binding leaf folded INSIDE the root. Both
//! close with the same fork lever: thread `table_public_inputs` up the tree and host-check the
//! circuit public vector. [`AttestedHistory`] is the `AggregateAttests` verdict under that named
//! carrier, and [`verify_history`] is the light-client check.
//!
//! ## Proofs are ADDITIVE ATTESTATION — and that is the POINT.
//!
//! The light client does NOT re-derive history. The succinct proof's validity IS the trust. A node
//! that produced the history runs the (expensive) prover once; every downstream verifier — a wallet,
//! a bridge, a peer syncing from a checkpoint — runs `verify_history` and obtains the same whole-
//! history attestation in constant work. That is the whole value of the IVC fold.
//!
//! ## The honest trust boundary (mirrors the Lean named hypotheses)
//!
//! `verify_turn_chain_recursive` is the plonky3 recursive-STARK verifier; its soundness is the FRI
//! obligation the Lean model NAMES (`EngineSound.recursive_sound`) rather than re-proves — you cannot
//! prove plonky3 FRI soundness in Lean, and this crate does not pretend to. What the light client
//! DOES guarantee, gap-free, is the COMPOSITION: IF the aggregate verifies (engine sound), THEN the
//! whole history is attested — which is precisely where a real aggregation bug (verify proof-of-step-7
//! but export step-3's roots; swap a leg; drop a turn) would have to surface, and the Lean
//! `light_client_verifies_whole_history` + `tampered_aggregate_cannot_bind` + `leaf_pairing_defeats_
//! swap` show it cannot.
//!
//! Build: `cargo build -p dregg-lightclient` (carries `dregg-circuit` with its default `recursion`
//! feature). Tests fold a real K-turn chain and light-verify it, and confirm a corrupted aggregate is
//! rejected.

#![cfg(feature = "recursion")]
#![forbid(unsafe_code)]

use dregg_circuit::field::BabyBear;
use dregg_circuit::ivc_turn_chain::{
    FinalizedTurn, RecursionVk, TurnChainError, WholeChainProof, prove_turn_chain_recursive,
    verify_turn_chain_recursive,
};

/// The whole-history attestation a light client obtains from ONE verified aggregate — the Rust mirror
/// of `Dregg2.Circuit.RecursiveAggregation.AggregateAttests`. It carries ONLY public commitments; the
/// per-turn states and proofs are NOT here (the light client never saw them). Holding an
/// `AttestedHistory` means: *every one of `num_turns` finalized turns executed correctly, in order,
/// from `genesis_root` to `final_root`, and `chain_digest` commits to that exact ordered history.*
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestedHistory {
    /// The genesis state root the attested history starts from (`WholeChainProof.genesis_root`,
    /// the Lean `AggregateAttests.genesis_pinned`).
    pub genesis_root: BabyBear,
    /// The final state root the attested history reaches — the genuine fold of the whole history
    /// (`WholeChainProof.final_root`, the Lean `AggregateAttests.final_is_genuine_fold`).
    pub final_root: BabyBear,
    /// The running digest committing to the ORDERED `(old_root, new_root)` pairs — distinct histories
    /// with the same endpoints still differ here (`WholeChainProof.chain_digest`; the AIR's
    /// `acc_out = hash_4_to_1([acc_in, old, new, idx])` chain).
    pub chain_digest: BabyBear,
    /// How many finalized turns the attested history folds (`WholeChainProof.num_turns`). The light
    /// client learns ALL of them executed correctly without seeing any.
    pub num_turns: usize,
}

/// Why a light-client verification failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LightClientError {
    /// The succinct aggregate proof did not verify — the engine REJECTED it. No attestation is
    /// granted. (Carries the underlying recursion error.)
    AggregateInvalid(TurnChainError),
}

impl core::fmt::Display for LightClientError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LightClientError::AggregateInvalid(e) => {
                write!(f, "light-client: aggregate proof did not verify: {e}")
            }
        }
    }
}

impl std::error::Error for LightClientError {}

/// **THE LIGHT-CLIENT CHECK** — verify ONE succinct aggregate against the client's trust anchor and
/// obtain the whole-history attestation, re-witnessing NOTHING.
///
/// `expected_vk` is the client's trust anchor — the verifier-key fingerprint of the honest root
/// circuit, obtained once from an honest setup fold ([`WholeChainProof::root_vk_fingerprint`] on the
/// setup party's own artifact) and carried in the client's configuration like any SNARK VK. It must
/// NEVER be read off the artifact being verified.
///
/// This runs [`verify_turn_chain_recursive`]'s three teeth (cost independent of the number of folded
/// turns): the VK pin, the carried-publics attestation against the chain-binding proof, and the root
/// batch-STARK verification. It does **not** re-execute any turn, re-hash any state, or inspect any
/// per-turn leaf. On success it returns the [`AttestedHistory`] read off the aggregate's public
/// commitments — which the binding attestation just verified against a proof — the Rust embodiment of
/// `light_client_verifies_whole_history`'s conclusion: every turn executed correctly, the chain is
/// correctly ordered, and `final_root` is the genuine fold of the whole history.
///
/// This is additive attestation: the verification IS the trust.
pub fn verify_history(
    agg: &WholeChainProof,
    expected_vk: &RecursionVk,
) -> Result<AttestedHistory, LightClientError> {
    // The check: VK pin + claimed-publics attestation + the root. Re-witnessing nothing.
    // (Lean: `hroot : verify agg.root = true`.)
    verify_turn_chain_recursive(agg, expected_vk).map_err(LightClientError::AggregateInvalid)?;

    // The attestation — the public roots the verified aggregate binds. (Lean: `AggregateAttests`.)
    Ok(AttestedHistory {
        genesis_root: agg.genesis_root,
        final_root: agg.final_root,
        chain_digest: agg.chain_digest,
        num_turns: agg.num_turns,
    })
}

/// Convenience for a prover/relayer: fold a finalized-turn chain into ONE aggregate, then light-verify
/// it. The fold is the expensive step (done once, by whoever produced the history); `verify_history`
/// is the cheap step every light client repeats. Returns the aggregate + its attestation.
///
/// As the SETUP-side entry point this self-anchors: the VK fingerprint is extracted from the locally
/// produced fold (`agg.root_vk_fingerprint()`) — which is exactly how an honest setup MINTS the trust
/// anchor it then distributes to light clients. A remote verifier must instead call
/// [`verify_history`] with its configured anchor.
pub fn fold_and_attest(
    turns: &[FinalizedTurn],
) -> Result<(WholeChainProof, AttestedHistory), LightClientError> {
    let agg = prove_turn_chain_recursive(turns).map_err(LightClientError::AggregateInvalid)?;
    let vk = agg.root_vk_fingerprint();
    let attested = verify_history(&agg, &vk)?;
    Ok((agg, attested))
}

// =============================================================================
// THE THIRD LEG — the finality certificate (quorum / tau).
//
// `verify_history` above proves the aggregate-correctness LEGS (1+2): the whole history executed
// correctly and its `final_root` is the genuine fold. But a *correct-looking* history is not a
// *finalized* one — an equivocating prover can fold a perfectly valid aggregate over a FORK the
// network never finalized. A real light client (a wallet, a bridge) must additionally check that the
// root it is shown is the one a BFT quorum FINALIZED. That is this leg.
//
// This is the Rust embodiment of `Dregg2.Distributed.FinalizedLightClient.
// light_client_accepts_finalized_history`: the client takes `(aggregate, finalized_root, finality
// cert)` and accepts ONLY when (1) the aggregate verifies, (2) `agg.final_root == finalized_root ==
// cert.finalized_root` (the root seam), and (3) the finality cert exhibits a super-ratification
// quorum (a supermajority of DISTINCT participants) over the finalized root.
// =============================================================================

/// A finality certificate the light client checks WITHOUT the lace or a full node — the compressed
/// attestation that a BFT quorum finalized `finalized_root`. The node computed super-ratification
/// (`ordering::tau` / `is_super_ratified`) over the whole blocklace; the light client, which never saw
/// the lace, instead checks this certificate: the set of DISTINCT participants whose signed votes
/// ratify the finalized head, counted against the REAL supermajority threshold
/// (`dregg_blocklace::ordering::supermajority_threshold = 2n/3 + 1`).
///
/// The Rust mirror of `FinalizedLightClient.FinalityCert` + `CertValid`: `signers` are the distinct
/// participants of the ratifying quorum (the cert's evidence payload), `participant_count` is the
/// group size the supermajority is taken over, and `finalized_root` is the root the quorum certifies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalityCert {
    /// The DISTINCT participant ids whose signed votes ratify the finalized head (the quorum). A
    /// participant appearing twice is counted ONCE — the node's super-ratification counts distinct
    /// creators (`ratifyingCreators.dedup`), so the cert's quorum is over distinct signers too.
    pub signers: Vec<[u8; 32]>,
    /// The total number of participants in the finalizing group — the `n` the supermajority
    /// threshold `2n/3 + 1` is computed against.
    pub participant_count: usize,
    /// The finalized state root this certificate attests a quorum super-ratified. Must equal the
    /// aggregate's `final_root` (the root seam) for the cert to bind the proven history.
    pub finalized_root: BabyBear,
}

impl FinalityCert {
    /// The count of DISTINCT signers in the quorum (a doubly-listed participant counts once — the
    /// node's super-ratification dedups ratifying creators).
    pub fn distinct_signers(&self) -> usize {
        let mut seen: Vec<&[u8; 32]> = Vec::with_capacity(self.signers.len());
        for s in &self.signers {
            if !seen.iter().any(|t| *t == s) {
                seen.push(s);
            }
        }
        seen.len()
    }

    /// **The quorum leg.** True iff a supermajority of DISTINCT participants signed — counted against
    /// the REAL node threshold `dregg_blocklace::ordering::supermajority_threshold(participant_count)
    /// = 2*participant_count/3 + 1`. This is the Rust mirror of `FinalizedLightClient.CertQuorum`
    /// (`isSuperRatified`'s `ratifyingCreators.length ≥ superMajority`).
    pub fn has_quorum(&self) -> bool {
        self.distinct_signers()
            >= dregg_blocklace::ordering::supermajority_threshold(self.participant_count)
    }
}

/// Why a finalized-history light-client verification failed (the three-leg surface).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FinalizedError {
    /// Leg 1+2: the succinct aggregate proof did not verify. (Carries the recursion error.)
    AggregateInvalid(TurnChainError),
    /// The root seam broke: the aggregate's proven `final_root` is not the shown `finalized_root`
    /// (a valid proof of history A cannot be paired with a finality cert for a different root).
    AggregateRootMismatch {
        /// The root the aggregate proves.
        proven: u32,
        /// The root the client was shown.
        shown: u32,
    },
    /// The root seam broke on the cert side: the certificate finalized a DIFFERENT root than the one
    /// shown (the cert does not certify this history's endpoint).
    CertRootMismatch {
        /// The root the certificate finalized.
        certified: u32,
        /// The root the client was shown.
        shown: u32,
    },
    /// Leg 3: the finality certificate did NOT exhibit a super-ratification quorum — fewer than
    /// `2n/3 + 1` distinct participants signed. The shown root was not finalized; NO attestation.
    NoQuorum {
        /// Distinct signers the cert exhibited.
        distinct_signers: usize,
        /// The supermajority threshold required (`2n/3 + 1`).
        threshold: usize,
    },
}

impl core::fmt::Display for FinalizedError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FinalizedError::AggregateInvalid(e) => {
                write!(f, "finalized light-client: aggregate did not verify: {e}")
            }
            FinalizedError::AggregateRootMismatch { proven, shown } => write!(
                f,
                "finalized light-client: aggregate proves root {proven} but was shown {shown}"
            ),
            FinalizedError::CertRootMismatch { certified, shown } => write!(
                f,
                "finalized light-client: cert finalized root {certified} but was shown {shown}"
            ),
            FinalizedError::NoQuorum {
                distinct_signers,
                threshold,
            } => write!(
                f,
                "finalized light-client: finality cert sub-quorum ({distinct_signers} distinct \
                 signers < {threshold} required) — root not finalized"
            ),
        }
    }
}

impl std::error::Error for FinalizedError {}

/// The verdict a light client obtains from `(aggregate, finalized_root, finality cert)` when all
/// three legs hold — the Rust mirror of `FinalizedLightClient.FinalizedHistoryAttested`. It carries
/// the whole-history attestation PLUS the finality fact: the endpoint root is the one a BFT quorum
/// finalized. Holding it means: *the root I trust is the genuine fold of a whole history that executed
/// correctly AND was finalized by a supermajority — and I re-executed nothing and never saw the lace.*
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedAttestation {
    /// Legs 1+2: the whole-history attestation (every turn correct, correctly ordered, genuine fold).
    pub history: AttestedHistory,
    /// Leg 3: the finalized root the quorum certified (== `history.final_root`, the seam).
    pub finalized_root: BabyBear,
    /// The number of DISTINCT participants whose quorum finalized the root (≥ `2n/3 + 1`).
    pub quorum_signers: usize,
}

/// **THE FINALIZED LIGHT-CLIENT CHECK** — verify ONE aggregate + ONE finality cert and obtain a
/// FINALIZED whole-history attestation, re-witnessing nothing and never touching the lace.
///
/// Runs exactly: (1) `verify_history` on the aggregate against the client's trust anchor (VK pin +
/// binding attestation + one recursive STARK verify, cost independent of history length); (2) the
/// root seam `agg.final_root == finalized_root == cert.finalized_root`; (3) the quorum check
/// `cert.has_quorum()` (count distinct signers ≥ `2n/3 + 1`). On success returns
/// `FinalizedAttestation` — the Rust embodiment of `light_client_accepts_finalized_history`'s
/// conclusion. Additive attestation: the aggregate verify + the quorum count IS the trust in the whole
/// finalized history.
pub fn verify_finalized_history(
    agg: &WholeChainProof,
    expected_vk: &RecursionVk,
    finalized_root: BabyBear,
    cert: &FinalityCert,
) -> Result<FinalizedAttestation, FinalizedError> {
    // Leg 1+2: the succinct aggregate (re-witnessing nothing).
    let history = verify_history(agg, expected_vk).map_err(|e| match e {
        LightClientError::AggregateInvalid(te) => FinalizedError::AggregateInvalid(te),
    })?;

    // Leg 2 (seam, aggregate side): the proven endpoint must be the shown root.
    if agg.final_root != finalized_root {
        return Err(FinalizedError::AggregateRootMismatch {
            proven: agg.final_root.as_u32(),
            shown: finalized_root.as_u32(),
        });
    }
    // Leg 2 (seam, cert side): the certificate must finalize the shown root.
    if cert.finalized_root != finalized_root {
        return Err(FinalizedError::CertRootMismatch {
            certified: cert.finalized_root.as_u32(),
            shown: finalized_root.as_u32(),
        });
    }

    // Leg 3: the quorum (super-ratification) check — against the REAL node threshold.
    if !cert.has_quorum() {
        return Err(FinalizedError::NoQuorum {
            distinct_signers: cert.distinct_signers(),
            threshold: dregg_blocklace::ordering::supermajority_threshold(cert.participant_count),
        });
    }

    Ok(FinalizedAttestation {
        history,
        finalized_root,
        quorum_signers: cert.distinct_signers(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::effect_vm::pi;
    use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace, sel};
    use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::joint_turn_aggregation::DescriptorParticipant;
    use dregg_circuit::lean_descriptor_air::{parse_vm_descriptor, prove_vm_descriptor};

    /// Build a real finalized turn on the PRODUCTION descriptor path: execute a transfer debit of
    /// `amount` from `(balance, nonce)`, prove the 186-column trace through the Lean transfer
    /// descriptor (`prove_vm_descriptor`, the audited p3 batch prover — the same wire artifact the
    /// SDK cutover emits), and carry the trace as the in-circuit leaf witness. Returns the turn +
    /// its REAL `(old_root, new_root)` Poseidon2 commitments.
    fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
        let state = CellState::new(balance, nonce);
        let effects = vec![Effect::Transfer {
            amount,
            direction: 1,
        }];
        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let old_root = public_inputs[pi::OLD_COMMIT];
        let new_root = public_inputs[pi::NEW_COMMIT];
        let json = descriptor_for_selector(sel::TRANSFER).expect("transfer descriptor registered");
        let desc = parse_vm_descriptor(json).expect("transfer descriptor parses");
        let dpis = &public_inputs[..desc.public_input_count];
        let proof =
            prove_vm_descriptor(&desc, &trace, dpis).expect("descriptor proves honest transfer");
        (
            FinalizedTurn::new(
                DescriptorParticipant::v1(proof, public_inputs),
                trace,
            ),
            old_root,
            new_root,
        )
    }

    /// A continuous chain of `k` real finalized turns (each turn's post-state IS the next's pre-state).
    fn make_chain(
        start_balance: u64,
        start_nonce: u32,
        step: u64,
        k: usize,
    ) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
        let mut turns = Vec::with_capacity(k);
        let mut balance = start_balance;
        let mut nonce = start_nonce;
        let mut genesis = BabyBear::ZERO;
        let mut final_root = BabyBear::ZERO;
        for i in 0..k {
            let (turn, old_root, new_root) = make_turn(balance, nonce, step);
            if i == 0 {
                genesis = old_root;
            }
            final_root = new_root;
            turns.push(turn);
            balance -= step;
            nonce += 1;
        }
        (turns, genesis, final_root)
    }

    /// **THE LIGHT-CLIENT HEADLINE (Rust witness).** Fold a real K=3 finalized-turn chain — REAL
    /// descriptor leaves verified in-circuit — into ONE aggregate, then verify it AS A LIGHT CLIENT
    /// — re-witnessing nothing — and obtain an `AttestedHistory` whose endpoints are the genuine
    /// genesis/final roots and whose `num_turns` is the whole history. This is
    /// `light_client_verifies_whole_history` run on real proofs.
    #[test]
    fn light_client_attests_whole_history() {
        let (turns, genesis, final_root) = make_chain(1000, 0, 7, 3);

        let (agg, attested) =
            fold_and_attest(&turns).expect("a continuous 3-turn chain must fold and light-verify");

        assert_eq!(
            attested.num_turns, 3,
            "the light client learns ALL three turns are attested"
        );
        assert_eq!(
            attested.genesis_root, genesis,
            "attested genesis = real genesis root"
        );
        assert_eq!(
            attested.final_root, final_root,
            "attested final = real folded final root"
        );
        assert_eq!(
            attested.chain_digest, agg.chain_digest,
            "digest carried from the aggregate"
        );

        // The trust anchor the honest setup distributes (extracted from ITS OWN fold).
        let vk = agg.root_vk_fingerprint();

        // Re-verifying the SAME aggregate (a second light client, holding the anchor) re-obtains
        // the SAME attestation — additive attestation is idempotent + cheap.
        let attested2 = verify_history(&agg, &vk).expect("a second light client must also verify");
        assert_eq!(
            attested, attested2,
            "every light client obtains the same whole-history verdict"
        );

        // REFUSED: a light client whose anchor pins a DIFFERENT circuit refuses this aggregate —
        // the VK pin is checked before anything trusts the proof's self-described circuit data.
        let mut wrong_anchor = vk;
        wrong_anchor.0[0] ^= 0xFF;
        match verify_history(&agg, &wrong_anchor) {
            Err(LightClientError::AggregateInvalid(
                dregg_circuit::ivc_turn_chain::TurnChainError::VkFingerprintMismatch { .. },
            )) => {}
            other => panic!("a mismatched VK anchor must refuse the aggregate; got {other:?}"),
        }
    }

    /// **THE ANCHOR MODEL'S LOAD-BEARING PROPERTY.** The VK fingerprint is a function of the root
    /// CIRCUIT SHAPE, not of the folded history's content: two different histories of the same
    /// window shape fingerprint identically, so ONE anchor distributed at setup verifies every
    /// honest fold of that shape. (And therefore: a fingerprint mismatch really means a DIFFERENT
    /// CIRCUIT, not merely different data — the refusal is the from-scratch-prover tooth, never a
    /// false positive on honest history.)
    #[test]
    fn vk_anchor_is_circuit_shape_not_history_content() {
        // Two DIFFERENT 2-turn histories (different balances, nonces, step sizes, hence different
        // roots/digests) of the same window shape.
        let (turns_a, _ga, _fa) = make_chain(1000, 0, 7, 2);
        let (turns_b, _gb, _fb) = make_chain(5000, 9, 13, 2);

        let (agg_a, _) = fold_and_attest(&turns_a).expect("history A folds");
        let (agg_b, _) = fold_and_attest(&turns_b).expect("history B folds");
        assert_ne!(
            agg_a.final_root, agg_b.final_root,
            "the histories genuinely differ"
        );

        // The anchor minted from history A's fold...
        let anchor = agg_a.root_vk_fingerprint();
        assert_eq!(
            anchor,
            agg_b.root_vk_fingerprint(),
            "same window shape => same verifier-key fingerprint (shape, not content)"
        );

        // ...verifies history B's aggregate.
        verify_history(&agg_b, &anchor)
            .expect("one setup-distributed anchor must verify every honest fold of that shape");
    }

    /// Build a finality cert with `k_signers` DISTINCT participants over `participant_count` total,
    /// certifying `root`. With `k_signers >= 2*participant_count/3 + 1` this is a genuine quorum.
    fn make_cert(k_signers: usize, participant_count: usize, root: BabyBear) -> FinalityCert {
        let signers: Vec<[u8; 32]> = (0..k_signers)
            .map(|i| {
                let mut id = [0u8; 32];
                id[0] = i as u8;
                id
            })
            .collect();
        FinalityCert {
            signers,
            participant_count,
            finalized_root: root,
        }
    }

    /// **THE THREE-LEG HEADLINE (Rust witness).** Fold a real K=2 chain, then verify it AS A FINALIZED
    /// light client: the aggregate verifies (legs 1+2), the root seam holds, AND a genuine 3-of-4
    /// super-ratification quorum certifies the final root (leg 3). The client obtains a
    /// `FinalizedAttestation` whose endpoint is the genuine, QUORUM-finalized root — re-witnessing
    /// nothing and never seeing the lace. This is `light_client_accepts_finalized_history` on real
    /// proofs + a real quorum.
    #[test]
    fn finalized_light_client_accepts_finalized_history() {
        let (turns, _genesis, final_root) = make_chain(1000, 0, 7, 2);
        let (agg, _att) = fold_and_attest(&turns).expect("a continuous 2-turn chain must fold");

        // n=4 ⇒ supermajority threshold = 2*4/3 + 1 = 3. A 3-signer quorum finalizes.
        let cert = make_cert(3, 4, final_root);
        assert!(
            cert.has_quorum(),
            "3-of-4 must be a supermajority (2*4/3+1 = 3)"
        );

        let vk = agg.root_vk_fingerprint();
        let attestation = verify_finalized_history(&agg, &vk, final_root, &cert)
            .expect("aggregate + quorum cert + seam must all hold");

        assert_eq!(attestation.history.num_turns, 2, "both turns attested");
        assert_eq!(
            attestation.finalized_root, final_root,
            "the trusted root is the finalized one"
        );
        assert_eq!(
            attestation.quorum_signers, 3,
            "the quorum is 3 distinct signers"
        );
    }

    /// **REJECTION TOOTH 1 — tampered aggregate.** Splicing a foreign public final root onto the
    /// aggregate is now refused by the CLAIMED-PUBLICS ATTESTATION (the carried binding proof
    /// Fiat–Shamir-binds the genuine final root, so the relabeled field fails verification) —
    /// earlier and stronger than the old endpoint-seam comparison, which only bit when the shown
    /// root happened to differ. And the seam itself still bites for an UNtampered aggregate shown
    /// the wrong root: a valid quorum for root B cannot launder a proof of root A either way.
    #[test]
    fn finalized_light_client_rejects_tampered_aggregate() {
        let (turns, _g, final_root) = make_chain(1000, 0, 7, 2);
        let (mut agg, _att) = fold_and_attest(&turns).expect("the honest chain must fold");
        let vk = agg.root_vk_fingerprint();

        // (a) Tamper: claim a DIFFERENT public final root than the one the aggregate proves.
        let other_final = final_root + BabyBear::ONE;
        assert_ne!(other_final, final_root, "the foreign root must differ");
        agg.final_root = other_final;

        // A genuine quorum for the ORIGINAL finalized root — the relabeled aggregate must be
        // refused outright (the carried publics no longer verify against the binding proof).
        let cert = make_cert(3, 4, final_root);
        match verify_finalized_history(&agg, &vk, final_root, &cert) {
            Err(FinalizedError::AggregateInvalid(
                dregg_circuit::ivc_turn_chain::TurnChainError::ClaimedPublicsUnattested { .. },
            )) => {}
            other => panic!(
                "a relabeled aggregate final root must be refused by the binding attestation; \
                 got {other:?}"
            ),
        }
        agg.final_root = final_root;

        // (b) The seam still bites for an HONEST aggregate shown a wrong finalized root: the
        // aggregate verifies, but its proven endpoint is not the root the client was shown.
        let shown = final_root + BabyBear::ONE;
        let cert_b = make_cert(3, 4, shown);
        match verify_finalized_history(&agg, &vk, shown, &cert_b) {
            Err(FinalizedError::AggregateRootMismatch { proven, shown: s }) => {
                assert_eq!(proven, final_root.as_u32());
                assert_eq!(s, shown.as_u32());
            }
            other => panic!("a wrong shown root must be rejected at the seam; got {other:?}"),
        }
    }

    /// **REJECTION TOOTH 2 — sub-quorum finality cert (FORGED finality).** A cert with only 2 of 4
    /// distinct signers is BELOW the `2*4/3+1 = 3` supermajority threshold: the root was NOT finalized.
    /// Even though the aggregate verifies and the seam holds, the finalized client REJECTS with
    /// `NoQuorum`. You cannot obtain a finalized attestation without a genuine BFT quorum — the
    /// fork-attack defense. (Rust mirror of `not_final_leader_invalidates` / sub-quorum rejection.)
    #[test]
    fn finalized_light_client_rejects_sub_quorum_cert() {
        let (turns, _g, final_root) = make_chain(1000, 0, 7, 2);
        let (agg, _att) = fold_and_attest(&turns).expect("the honest chain must fold");

        // 2 of 4 signers — below the supermajority threshold of 3. A forged/insufficient finality cert.
        let weak_cert = make_cert(2, 4, final_root);
        assert!(
            !weak_cert.has_quorum(),
            "2-of-4 must NOT be a supermajority"
        );

        let vk = agg.root_vk_fingerprint();
        match verify_finalized_history(&agg, &vk, final_root, &weak_cert) {
            Err(FinalizedError::NoQuorum {
                distinct_signers,
                threshold,
            }) => {
                assert_eq!(distinct_signers, 2);
                assert_eq!(threshold, 3, "supermajority of 4 is 3");
            }
            other => panic!("a sub-quorum finality cert must be rejected; got {other:?}"),
        }
    }

    /// **REJECTION TOOTH 3 — cert finalizes the WRONG root.** A valid 3-of-4 quorum that certifies a
    /// DIFFERENT root than the aggregate's endpoint breaks the cert-side seam: an adversary cannot pair
    /// a real proof of history A with a real finality cert for history B. The finalized client REJECTS
    /// with `CertRootMismatch`. (Rust mirror of `root_mismatch_unbinds`.)
    #[test]
    fn finalized_light_client_rejects_cert_for_other_root() {
        let (turns, _g, final_root) = make_chain(1000, 0, 7, 2);
        let (agg, _att) = fold_and_attest(&turns).expect("the honest chain must fold");

        // A genuine quorum — but it finalized a DIFFERENT root.
        let foreign_root = final_root + BabyBear::ONE;
        assert_ne!(foreign_root, final_root);
        let cert = make_cert(3, 4, foreign_root);
        assert!(cert.has_quorum(), "the cert itself carries a real quorum");

        let vk = agg.root_vk_fingerprint();
        match verify_finalized_history(&agg, &vk, final_root, &cert) {
            Err(FinalizedError::CertRootMismatch { certified, shown }) => {
                assert_eq!(certified, foreign_root.as_u32());
                assert_eq!(shown, final_root.as_u32());
            }
            other => panic!("a cert finalizing a different root must be rejected; got {other:?}"),
        }
    }

    /// **REJECTION TOOTH 4 — duplicate signers cannot fake a quorum.** A cert that lists the SAME
    /// participant 3 times over a group of 4 has only ONE distinct signer — far below the threshold of
    /// 3. `distinct_signers` dedups (mirroring the node's `ratifyingCreators.dedup`), so a forged cert
    /// padded with repeats is rejected as sub-quorum. Sybil-by-repeat does not finalize.
    #[test]
    fn finalized_light_client_dedups_repeated_signers() {
        let (turns, _g, final_root) = make_chain(1000, 0, 7, 2);
        let (agg, _att) = fold_and_attest(&turns).expect("the honest chain must fold");

        let mut id = [0u8; 32];
        id[0] = 7;
        let padded_cert = FinalityCert {
            signers: vec![id, id, id], // one distinct signer, listed thrice
            participant_count: 4,
            finalized_root: final_root,
        };
        assert_eq!(padded_cert.distinct_signers(), 1, "repeats count once");
        assert!(
            !padded_cert.has_quorum(),
            "one distinct signer is not a quorum of 4"
        );

        let vk = agg.root_vk_fingerprint();
        match verify_finalized_history(&agg, &vk, final_root, &padded_cert) {
            Err(FinalizedError::NoQuorum {
                distinct_signers, ..
            }) => {
                assert_eq!(distinct_signers, 1, "duplicates collapsed to one");
            }
            other => panic!("a repeat-padded sub-quorum cert must be rejected; got {other:?}"),
        }
    }

    /// **THE REJECTION TOOTH (Rust witness).** A light client REFUSES a corrupted aggregate
    /// OUTRIGHT: splicing foreign public claims (final root + digest) onto the artifact fails the
    /// claimed-publics attestation — the carried binding proof Fiat–Shamir-binds the genuine values,
    /// so `verify_history` returns `AggregateInvalid(ClaimedPublicsUnattested)` and grants NO
    /// attestation. (This used to be a SOFT tooth: the public fields were not read from any proof at
    /// verify time, so a spliced aggregate "verified" and the test could only assert the attestation
    /// repeated the lie. Now the lie itself is refused.) Mirror of the Lean
    /// `tampered_aggregate_cannot_bind`: a broken aggregate cannot attest.
    #[test]
    fn light_client_rejects_corrupted_aggregate() {
        let (turns, _g, _f) = make_chain(1000, 0, 7, 2);
        let (mut agg, _attested) = fold_and_attest(&turns).expect("the honest chain must fold");
        let vk = agg.root_vk_fingerprint();

        // Corrupt the PUBLIC final root + digest the aggregate claims — splice foreign public
        // claims onto THIS aggregate's root proof.
        agg.final_root = agg.final_root + BabyBear::ONE;
        agg.chain_digest = agg.chain_digest + BabyBear::ONE;

        match verify_history(&agg, &vk) {
            Err(LightClientError::AggregateInvalid(
                dregg_circuit::ivc_turn_chain::TurnChainError::ClaimedPublicsUnattested { .. },
            )) => {
                // The verifier rejected outright — the publics are read against a proof now.
            }
            other => panic!(
                "spliced public claims must be REFUSED by the claimed-publics attestation; \
                 got {other:?}"
            ),
        }
    }
}
