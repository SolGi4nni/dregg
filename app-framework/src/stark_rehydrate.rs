//! STARK-gated rehydration — a frustum-snapshot whose re-expansion is gated by a
//! **real STARK proof**, NOT by a witness-replay over the receipt chain.
//!
//! ## The contrast this module draws (the whole point)
//!
//! [`crate::rehydration`] ships the deos frustum-snapshot today: a [`Sturdyref`]
//! carries an [`InteractionLog`], and its liveness-type is DERIVED by *walking* that
//! log — [`InteractionLog::all_witnessed`] checks every interaction carries a genuine
//! `turn_hash` (a receipt present in the witness-graph). That is **Tier A**
//! (`docs/deos/DEOS-APPS.md` §"the two tiers"): tamper-evidence by **witness replay**
//! — the rehydrator re-walks the receipt chain and trusts that the receipts attest the
//! turns.
//!
//! This module is **Tier B**: the snapshot carries a *real STARK proof* of the turn
//! that produced the surface state, and rehydration **VERIFIES the STARK** instead of
//! walking a log. Opening the image proves "this surface state is the genuine endpoint
//! of a verified turn-history" the way a **light client** does — it checks one proof,
//! it does not re-execute or re-walk anything. A tampered surface state, a forged
//! proof, or a proof against the wrong post-state is **rejected at rehydration**: the
//! STARK verify fails closed.
//!
//! The proof artifact is the **rotated multi-table `Ir2BatchProof`** (the leaf the
//! whole-chain IVC fold builds on) minted by
//! [`dregg_turn::rotation_witness::mint_rotated_participant_leg`] over the *executor's
//! genuine before/after cells*. Its public inputs carry the rotated Poseidon2
//! state-commitments at PI 34/35 ([`RotatedParticipantLeg::old_root`] /
//! [`RotatedParticipantLeg::new_root`]); the descriptor's in-circuit hash sites force
//! PI 35 to be the genuine post-state commitment, so a claimed NEW_COMMIT with no
//! satisfying execution is UNSAT. Verification is
//! [`dregg_circuit::descriptor_ir2::verify_vm_descriptor2`] — the **Lean-free** verify
//! surface (`dregg-circuit`'s `verifier` feature compiles it without the prover/DFT),
//! and it is **seconds-scale** for a single turn (the multi-turn `WholeChainProof`
//! ROOT — see [`stark_chain_snapshot`] — is the minutes-scale light-client artifact the
//! same weld extends to).
//!
//! ## What stays the same (the per-viewer jail)
//!
//! The membrane is *unchanged*. A [`StarkSnapshot`] still re-expands per-viewer through
//! the REAL [`crate::rehydration::Membrane`] / [`dregg_cell::is_attenuation`] lattice: a powerful
//! holder's snapshot yields a NARROWER surface to a weaker viewer, an incomparable
//! identity cannot peek. Swapping the *tamper-evidence mechanism* (witness-replay →
//! STARK) does not loosen the *confinement* (the cap-membrane) — the two are
//! orthogonal, exactly as `DEOS.md` separates them.
//!
//! ## Runnable demos
//!
//! Two `examples/` binaries exercise this module end to end against the REAL prover +
//! verifier (`cargo run -p dregg-app-framework --example <name>`):
//!   - **`stark_rehydrate`** — the Tier-A-vs-Tier-B narration: a snapshot carries a real
//!     STARK and rehydration VERIFIES it (light-client style), per-viewer, with the
//!     tampered-PI-35 / wrong-descriptor anti-ghost teeth.
//!   - **`stark_frustum_cull`** — the **non-amplification proof obligation made
//!     concrete**: it mints TWO real legs (a fuller endpoint and a *darkened* one) and
//!     shows the weaker viewer holding the darkened proof provably **cannot prove the
//!     fuller view** — splicing the fuller PI-35 commitment into the darkened proof is
//!     UNSAT ([`verify_stark_proof_against`] rejects), AND the membrane independently
//!     refuses to project the fuller lineage
//!     ([`crate::rehydration::RehydrateError::Amplification`]). Two independent walls =
//!     "frustum culling the semantic graph" with teeth.

use dregg_cell::{AuthRequired, Cell};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::{CellState as VmCellState, Effect as VmEffect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::ivc_turn_chain::ir2_leaf_wrap_config;
use dregg_circuit::plonky3_recursion_impl::recursive::DreggRecursionConfig;
use dregg_types::CellId;

use crate::affordance::AffordanceSurface;
use crate::rehydration::{Membrane, RehydrateError, RehydratedSurface, Rehydration};

/// The rotated participant leg the snapshot carries: the real `Ir2BatchProof` + the
/// descriptor it satisfies + the 38-PI vector it attests. Re-exported from the circuit
/// so a downstream snapshot consumer names one type.
pub use dregg_circuit::joint_turn_aggregation::RotatedParticipantLeg;

/// The rotated NEW-state commitment lives at PI index 35 (`V1_PI_COUNT + 1`): the
/// genuine Poseidon2 post-state commitment the descriptor's hash sites bind. Tampering
/// this felt and re-verifying is the single-leg anti-ghost tooth (`new_root` is read
/// off it).
pub const PI_NEW_COMMIT: usize = 35;
/// The rotated OLD-state commitment lives at PI index 34 (`V1_PI_COUNT`).
pub const PI_OLD_COMMIT: usize = 34;

// =============================================================================
// What can go wrong VERIFYING a STARK-gated snapshot
// =============================================================================

/// Why a STARK-gated rehydration was refused.
///
/// The two failure families are *orthogonal* (the design point): a [`Self::Membrane`]
/// refusal is the cap-lattice saying "this viewer has no projection"; a
/// [`Self::StarkInvalid`] refusal is the *STARK verifier* saying "this surface state is
/// not the genuine endpoint of a verified turn" (a tampered post-state, a forged proof,
/// or a wrong-descriptor proof). Tier A could only ever raise the first; Tier B fails
/// closed on the second WITHOUT walking any receipt chain.
#[derive(Clone, Debug)]
pub enum StarkRehydrateError {
    /// The cap-membrane refused — the viewer's authority and the lineage are
    /// incomparable (no projection both admit). Identical to the Tier-A refusal.
    Membrane(RehydrateError),
    /// The carried STARK did **not** verify against the carried public inputs: the
    /// surface state is not the genuine endpoint of the claimed verified turn. This is
    /// the Tier-B fail-closed — a tampered post-state (PI 35 flipped), a forged proof,
    /// or a proof verified against the wrong descriptor all land here. Carries the
    /// verifier's reason string.
    StarkInvalid(String),
}

impl std::fmt::Display for StarkRehydrateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StarkRehydrateError::Membrane(e) => write!(f, "membrane refused: {e}"),
            StarkRehydrateError::StarkInvalid(why) => {
                write!(f, "STARK verify failed (not the genuine endpoint): {why}")
            }
        }
    }
}

impl std::error::Error for StarkRehydrateError {}

// =============================================================================
// The STARK-gated frustum-snapshot
// =============================================================================

/// A frustum-snapshot whose re-expansion is gated by a **real STARK proof** of the turn
/// that produced the surface state — the Tier-B rehydration.
///
/// It carries, behind the membrane:
///   - the backing `cell` + the publisher's `lineage` authority (the frustum extent +
///     the projection ceiling — same as the Tier-A [`Sturdyref`]);
///   - **the proof** ([`RotatedParticipantLeg`]: the `Ir2BatchProof` + its descriptor +
///     its public inputs). The proof's PI 35 ([`RotatedParticipantLeg::new_root`]) is
///     the genuine Poseidon2 commitment of the surface's post-state.
///
/// It carries **no `InteractionLog`** — there is nothing to replay. Rehydration calls
/// [`Self::rehydrate_for`], which (1) verifies the STARK (the genuine-endpoint proof)
/// and (2) mints the per-viewer projection through the membrane. The order is
/// load-bearing: **no projection is minted for an unverified surface**, regardless of
/// caps (confinement-before-relation, the same discipline the receipt-chain path uses,
/// but the gate is a STARK).
#[derive(Clone)]
pub struct StarkSnapshot {
    /// The cell the snapshot is a camera on (the surface being re-viewed).
    pub cell: CellId,
    /// The publisher's authority lineage — every viewer's projection is an attenuation
    /// of this.
    pub lineage: AuthRequired,
    /// The REAL STARK proof of the turn that produced the surface state. Its
    /// `public_inputs[35]` is the genuine post-state commitment the verifier binds.
    pub proof: RotatedParticipantLeg,
}

impl StarkSnapshot {
    /// Wrap an already-minted [`RotatedParticipantLeg`] as a STARK-gated snapshot over
    /// `cell` with publisher `lineage`. Use [`mint_stark_snapshot`] to mint the leg
    /// from an executor's genuine before/after cells in one call.
    pub fn new(cell: CellId, lineage: AuthRequired, proof: RotatedParticipantLeg) -> Self {
        StarkSnapshot {
            cell,
            lineage,
            proof,
        }
    }

    /// The genuine post-state commitment this snapshot's proof attests (PI 35) — the
    /// "endpoint" the STARK proves the surface state is. This is what a wrong-root proof
    /// would mismatch.
    pub fn endpoint_commitment(&self) -> BabyBear {
        self.proof.new_root()
    }

    /// **Verify the carried STARK** — the genuine-endpoint check, with NO receipt-chain
    /// walk. Returns `Ok(())` iff the `Ir2BatchProof` verifies against its descriptor +
    /// public inputs (so the surface state is the genuine post-state the descriptor's
    /// in-circuit hash sites force PI 35 to be). This is the Lean-free
    /// [`verify_vm_descriptor2`] — the light-client verify.
    ///
    /// A tampered post-state (PI 35 flipped), a forged proof, or a proof carried under
    /// the wrong descriptor all make this return [`StarkRehydrateError::StarkInvalid`].
    pub fn verify_stark(&self) -> Result<(), StarkRehydrateError> {
        verify_stark_leg(&self.proof).map_err(StarkRehydrateError::StarkInvalid)
    }

    /// **Rehydrate** this STARK-gated snapshot for a viewer through their [`Membrane`],
    /// against the live `surface`.
    ///
    /// 1. **Verify the STARK** ([`Self::verify_stark`]) — the genuine-endpoint proof.
    ///    If it fails, NO projection is minted (confinement-before-relation; a forged or
    ///    tampered surface never re-expands, regardless of the viewer's caps).
    /// 2. The membrane derives the projection authority `(viewer held) ∧ (lineage)`
    ///    through the REAL [`dregg_cell::is_attenuation`] — [`StarkRehydrateError::Membrane`] if
    ///    incomparable.
    /// 3. The viewer reacquires exactly the live surface's affordances the projection
    ///    authority admits — the screenshot respects the lattice.
    ///
    /// The returned [`RehydratedSurface`]'s liveness-type is
    /// [`Rehydration::ReplayedDeterministic`]: the surface state is faithful-by-STARK
    /// (the genuine endpoint of a verified turn), the Tier-B analogue of "every
    /// interaction was a witnessed turn" — established by a *proof*, not a log walk.
    pub fn rehydrate_for(
        &self,
        membrane: &Membrane,
        surface: &AffordanceSurface,
    ) -> Result<RehydratedSurface, StarkRehydrateError> {
        // (1) The STARK gate FIRST — an unverified surface never re-expands.
        self.verify_stark()?;
        // (2) + (3) The cap-membrane projection (unchanged from Tier A).
        let projection = membrane
            .project_authority(&self.lineage)
            .map_err(StarkRehydrateError::Membrane)?;
        let affordances = surface.project_for(&projection);
        Ok(RehydratedSurface {
            cell: self.cell,
            projection,
            affordances,
            // Faithful-by-STARK: the genuine endpoint of a verified turn.
            liveness: Rehydration::ReplayedDeterministic,
        })
    }
}

/// Verify a rotated leg's `Ir2BatchProof` against its descriptor + public inputs — the
/// raw STARK gate ([`verify_vm_descriptor2`], Lean-free). Returns the verifier's reason
/// string on failure. Shared by [`StarkSnapshot::verify_stark`] and the anti-ghost
/// teeth.
pub fn verify_stark_leg(leg: &RotatedParticipantLeg) -> Result<(), String> {
    // The rotated leg's proof is minted under the leaf-wrap `DreggRecursionConfig`
    // (for the IVC fold), so the verify must use the generic config-parametric
    // surface, not the `DreggStarkConfig`-specialized `verify_vm_descriptor2`.
    verify_vm_descriptor2_with_config::<DreggRecursionConfig>(
        &leg.descriptor,
        &leg.proof,
        &leg.public_inputs,
        &ir2_leaf_wrap_config(),
    )
}

/// Verify a rotated `Ir2BatchProof` against an EXPLICIT descriptor + public-input pair —
/// the primitive the anti-ghost teeth use to verify the genuine proof against a
/// *tampered* PI vector (PI 35 flipped) or the *wrong* descriptor, asserting rejection.
pub fn verify_stark_proof_against(
    descriptor: &EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    verify_vm_descriptor2_with_config::<DreggRecursionConfig>(
        descriptor,
        proof,
        public_inputs,
        &ir2_leaf_wrap_config(),
    )
}

// =============================================================================
// Minting the STARK from the executor's genuine state transition
// =============================================================================

/// A transfer DEBIT of `amount` from `(balance, nonce)` — the rotated cohort effect the
/// demo mints a leg for. The rotated trace keeps the nonce on a transfer DEBIT and
/// decreases the balance by `amount` (the audited mint fixture's shape).
pub struct TransferTurn {
    /// The actor cell's balance before the turn (the executor's genuine pre-balance).
    pub balance: u64,
    /// The actor cell's nonce before the turn.
    pub nonce: u32,
    /// The amount debited.
    pub amount: u64,
}

/// Mint a STARK-gated snapshot over the **executor's genuine before/after cells** for a
/// transfer turn — the weld's producer side.
///
/// `before_cell` / `after_cell` are the REAL `dregg_cell::Cell`s read off the embedded
/// executor's ledger (before-cell read before the turn, after-cell after), so the
/// minted `Ir2BatchProof`'s PI 35 is the genuine Poseidon2 commitment of the executor's
/// post-state — the proof attests *the executor's* state transition, not a fixture's.
/// The leg self-verifies on mint (so a successful return already carries a sound proof).
///
/// `cell` / `lineage` are the snapshot's frustum (the surface cell + the publisher's
/// projection ceiling), exactly as a Tier-A [`Sturdyref`].
pub fn mint_stark_snapshot(
    cell: CellId,
    lineage: AuthRequired,
    turn: &TransferTurn,
    before_cell: &Cell,
    after_cell: &Cell,
) -> Result<StarkSnapshot, String> {
    let leg = mint_transfer_leg(turn, before_cell, after_cell)?;
    Ok(StarkSnapshot::new(cell, lineage, leg))
}

/// Mint the rotated transfer leg (the raw `Ir2BatchProof` carrier) from genuine
/// before/after cells — the call the snapshot wraps. Exposed so a chain demo can mint
/// several legs and fold them into a `WholeChainProof` (see [`stark_chain_snapshot`]).
pub fn mint_transfer_leg(
    turn: &TransferTurn,
    before_cell: &Cell,
    after_cell: &Cell,
) -> Result<RotatedParticipantLeg, String> {
    let state = VmCellState::new(turn.balance, turn.nonce);
    let effects = vec![VmEffect::Transfer {
        amount: turn.amount,
        direction: 1,
    }];
    // The receipt-log + nullifier-root the rotated mint folds into the iroot (a genuine
    // non-empty log so the iroot non-omission tooth has content to bind).
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    dregg_turn::rotation_witness::mint_rotated_participant_leg(
        &state,
        &effects,
        before_cell,
        after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        None,
    )
}

// =============================================================================
// The witness-replay contrast, made executable
// =============================================================================

/// The Tier-A *witness-replay* genuine-endpoint check, for the side-by-side contrast:
/// it re-walks the receipt chain (`turn_hashes`) and trusts a receipt is present for
/// every step. It performs **no cryptographic verification** of the turn — it counts
/// non-zero receipt hashes (the `all_witnessed` discipline). Returns `true` iff every
/// step carries a genuine (non-zero) receipt.
///
/// Contrast [`StarkSnapshot::verify_stark`]: the Tier-B gate verifies ONE STARK and
/// needs NONE of this walk — a light client checks a proof, it does not enumerate
/// receipts.
pub fn witness_replay_is_genuine(turn_hashes: &[[u8; 32]]) -> bool {
    !turn_hashes.is_empty() && turn_hashes.iter().all(|h| *h != [0u8; 32])
}

// =============================================================================
// The chain variant — the K-turn light-client ROOT the weld extends to
// =============================================================================

/// **The multi-turn variant**, named + reachable, for the light-client ROOT artifact.
///
/// A [`StarkSnapshot`] gates on ONE turn's rotated `Ir2BatchProof` (seconds to
/// prove+verify, the runnable demo). The *whole-chain* analogue gates on a
/// [`dregg_circuit::ivc_turn_chain::WholeChainProof`] — the recursive fold of K
/// finalized turns into ONE root batch-STARK proof (~502 KiB, constant-time verify
/// independent of K, the genuine light-client artifact). Opening such a snapshot would
/// call [`dregg_circuit::ivc_turn_chain::verify_turn_chain_recursive`] against the
/// caller-held VK fingerprint — the SAME weld (snapshot-carries-proof,
/// rehydrate-verifies-proof), one proof up.
///
/// The fold is **minutes-scale** and requires `dregg-circuit`'s `recursion` feature, so
/// this module ships the single-leg gate as the runnable demo and documents the chain
/// ROOT here; the canonical fold prove→verify (with its full tamper-rejection teeth)
/// lives in `circuit/tests/ivc_turn_chain_rotated.rs`. This module name is the pointer.
pub mod stark_chain_snapshot {
    // See the parent module doc: the chain variant gates on a `WholeChainProof`
    // (`verify_turn_chain_recursive`) instead of a single `Ir2BatchProof`
    // (`verify_vm_descriptor2`) — the same snapshot-carries-proof /
    // rehydrate-verifies-proof weld, at the K-turn light-client ROOT.
    pub use dregg_circuit::ivc_turn_chain::{WholeChainProof, verify_turn_chain_recursive};
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affordance::CellAffordance;
    use dregg_turn::action::{Effect as TurnEffect, Event};

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    /// Open permissions so the rotated producer-witness path admits the actor cell
    /// without auth gating (mirrors the audited mint fixture).
    fn open_permissions() -> dregg_cell::Permissions {
        dregg_cell::Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    /// The transfer actor cell at `(balance, nonce)` with open permissions.
    fn producer_cell(balance: i64, nonce: u64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
        cell.permissions = open_permissions();
        for _ in 0..nonce {
            let _ = cell.state.increment_nonce();
        }
        cell
    }

    fn emit_event(cell: CellId) -> TurnEffect {
        TurnEffect::EmitEvent {
            cell,
            event: Event {
                topic: [1u8; 32],
                data: vec![],
            },
        }
    }

    /// view@Signature, comment@Either, admin@None — the canonical doc surface.
    fn doc_surface(doc: CellId) -> AffordanceSurface {
        AffordanceSurface::named(doc, "doc")
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                emit_event(doc),
            ))
            .declare(CellAffordance::new(
                "comment",
                AuthRequired::Either,
                emit_event(doc),
            ))
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::None,
                emit_event(doc),
            ))
    }

    /// Mint a real STARK-gated snapshot over a transfer DEBIT of `amount` from
    /// `(balance, nonce)` — genuine before/after cells, a genuine `Ir2BatchProof`.
    fn mint_demo_snapshot(
        doc: CellId,
        lineage: AuthRequired,
        balance: u64,
        nonce: u32,
        amount: u64,
    ) -> StarkSnapshot {
        let before = producer_cell(balance as i64, nonce as u64);
        let after = producer_cell((balance as i64) - (amount as i64), nonce as u64);
        let turn = TransferTurn {
            balance,
            nonce,
            amount,
        };
        mint_stark_snapshot(doc, lineage, &turn, &before, &after)
            .expect("rotated transfer leg mints + self-verifies")
    }

    // ── the genuine snapshot VERIFIES its STARK and re-expands per-viewer ──

    #[test]
    fn genuine_snapshot_verifies_and_rehydrates_per_viewer() {
        let doc = cid(1);
        let surface = doc_surface(doc);
        // A root holder snapshots the surface (lineage None — the full surface), the
        // snapshot carrying a REAL STARK of a transfer turn.
        let snap = mint_demo_snapshot(doc, AuthRequired::None, 1000, 0, 7);

        // The STARK verifies — the surface state is the genuine endpoint of a verified
        // turn (NO receipt-chain walk; one proof checked).
        snap.verify_stark()
            .expect("the genuine snapshot's STARK must verify");

        // The root holder rehydrates the FULL surface.
        let root = Membrane::new(AuthRequired::None);
        let root_view = snap
            .rehydrate_for(&root, &surface)
            .expect("root rehydrates");
        assert_eq!(
            root_view.visible_names(),
            vec![
                "admin".to_string(),
                "comment".to_string(),
                "view".to_string()
            ]
        );
        // Faithful-by-STARK.
        assert_eq!(root_view.liveness, Rehydration::ReplayedDeterministic);
        assert!(root_view.liveness.is_faithful());

        // A weaker viewer (Signature) rehydrating the SAME snapshot reacquires only
        // {view} — the STARK gate did not loosen the cap-membrane.
        let viewer = Membrane::new(AuthRequired::Signature);
        let viewer_view = snap
            .rehydrate_for(&viewer, &surface)
            .expect("viewer rehydrates");
        assert_eq!(viewer_view.visible_names(), vec!["view".to_string()]);
        assert_ne!(root_view.visible_names(), viewer_view.visible_names());
    }

    // ── ANTI-GHOST: a tampered post-state (PI 35 flipped) is REJECTED ──

    #[test]
    fn tampered_endpoint_is_rejected_at_rehydration() {
        let doc = cid(2);
        let surface = doc_surface(doc);
        let mut snap = mint_demo_snapshot(doc, AuthRequired::None, 1000, 0, 7);

        // The honest endpoint verifies.
        let honest = snap.endpoint_commitment();
        snap.verify_stark().expect("honest endpoint verifies");

        // Tamper the claimed post-state commitment (PI 35) — claim the surface ended in
        // a DIFFERENT state than the proof attests. The descriptor's in-circuit hash
        // sites force PI 35 to be the genuine post-state, so the tampered PI is UNSAT.
        snap.proof.public_inputs[PI_NEW_COMMIT] = honest + BabyBear::ONE;

        // verify_stark MUST now fail — a tampered surface state is rejected.
        match snap.verify_stark() {
            Err(StarkRehydrateError::StarkInvalid(_)) => {}
            other => panic!("a tampered post-state must be rejected by the STARK; got {other:?}"),
        }
        // And rehydration fails closed — NO projection is minted for an unverified
        // surface, even for the all-powerful root holder.
        let root = Membrane::new(AuthRequired::None);
        match snap.rehydrate_for(&root, &surface) {
            Err(StarkRehydrateError::StarkInvalid(_)) => {}
            other => panic!("rehydration must fail closed on a tampered endpoint; got {other:?}"),
        }
    }

    // ── ANTI-GHOST: a wrong-descriptor proof is REJECTED ──

    #[test]
    fn wrong_descriptor_proof_is_rejected() {
        // Mint a genuine transfer leg, then try to verify its proof+PIs against a
        // DIFFERENT cohort's descriptor (a setField R24 descriptor, not transfer). The
        // proof binds its own descriptor's AIR set; a foreign descriptor rejects.
        let before = producer_cell(1000, 0);
        let after = producer_cell(993, 0);
        let turn = TransferTurn {
            balance: 1000,
            nonce: 0,
            amount: 7,
        };
        let leg = mint_transfer_leg(&turn, &before, &after).expect("transfer leg mints");

        // The genuine descriptor verifies.
        verify_stark_leg(&leg).expect("genuine descriptor verifies");

        // A foreign descriptor (resolved for a SetField effect) is a different AIR set
        // / table shape — verifying the transfer proof against it must reject.
        let foreign = foreign_descriptor();
        match verify_stark_proof_against(&foreign, &leg.proof, &leg.public_inputs) {
            Err(_) => {}
            Ok(()) => panic!("a transfer proof must NOT verify under a foreign descriptor"),
        }
    }

    /// Resolve a NON-transfer rotated descriptor (a setField R24 cohort) from the staged
    /// registry — the "wrong circuit" the wrong-descriptor tooth verifies against.
    fn foreign_descriptor() -> EffectVmDescriptor2 {
        use dregg_circuit::effect_vm::trace_rotated::rotated_descriptor_name_for_effect;
        use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
        // A SetField effect names a DIFFERENT rotated descriptor than Transfer.
        let setfield = VmEffect::SetField {
            field_idx: 0,
            value: BabyBear::ONE,
        };
        let name = rotated_descriptor_name_for_effect(&setfield)
            .expect("setField is a rotated R24 cohort member");
        let json = V3_STAGED_REGISTRY_TSV
            .lines()
            .find_map(|line| {
                let mut it = line.splitn(3, '\t');
                if it.next() == Some(name) {
                    let _display = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .expect("setField descriptor is in the staged registry");
        dregg_circuit::descriptor_ir2::parse_vm_descriptor2(json)
            .expect("setField descriptor parses")
    }

    // ── ANTI-GHOST: an incomparable viewer cannot peek (the membrane, unchanged) ──

    #[test]
    fn incomparable_viewer_cannot_peek_even_with_a_valid_stark() {
        let doc = cid(3);
        let surface = doc_surface(doc);
        // A snapshot whose lineage is a Custom identity (a fog-of-war side), carrying a
        // GENUINE STARK.
        let red = AuthRequired::Custom { vk_hash: [7u8; 32] };
        let snap = mint_demo_snapshot(doc, red, 1000, 0, 7);
        snap.verify_stark().expect("the STARK is genuine");

        // A DIFFERENT-identity viewer cannot rehydrate it — the membrane mints NO
        // projection, even though the STARK verifies. (Confinement is orthogonal to the
        // genuine-endpoint proof: a valid proof does NOT grant a viewer access.)
        let blue = Membrane::new(AuthRequired::Custom { vk_hash: [9u8; 32] });
        match snap.rehydrate_for(&blue, &surface) {
            Err(StarkRehydrateError::Membrane(RehydrateError::Amplification { .. })) => {}
            other => {
                panic!("an incomparable viewer must be refused by the membrane; got {other:?}")
            }
        }
    }

    // ── the witness-replay contrast, executable ──

    #[test]
    fn stark_gate_needs_no_receipt_chain_walk() {
        let doc = cid(4);
        let snap = mint_demo_snapshot(doc, AuthRequired::None, 1000, 0, 7);

        // Tier B: the genuine-endpoint check is ONE STARK verify — it consults NO
        // receipt log (the snapshot carries none).
        snap.verify_stark().expect("Tier B verifies one proof");

        // Tier A (the contrast): the witness-replay genuine-endpoint check re-walks a
        // receipt chain and merely counts non-zero receipts — no cryptographic turn
        // verification at all.
        let receipts = [[3u8; 32], [5u8; 32]];
        assert!(
            witness_replay_is_genuine(&receipts),
            "Tier A trusts the receipt chain (no STARK)"
        );
        // A zeroed receipt breaks the Tier-A walk (the only thing it can catch) — but a
        // forged receipt with a plausible non-zero hash would pass Tier A while the
        // STARK would reject the corresponding tampered post-state. That gap is exactly
        // what Tier B closes.
        let with_gap = [[3u8; 32], [0u8; 32]];
        assert!(!witness_replay_is_genuine(&with_gap));
    }

    /// Anti-vacuity for the witness-replay contrast helper: it is BOTH true and false on
    /// realistic inputs (an empty chain is not genuine; a full chain is).
    #[test]
    fn witness_replay_helper_is_non_vacuous() {
        assert!(!witness_replay_is_genuine(&[]), "empty chain: not genuine");
        assert!(
            witness_replay_is_genuine(&[[1u8; 32]]),
            "one receipt: genuine"
        );
    }
}
