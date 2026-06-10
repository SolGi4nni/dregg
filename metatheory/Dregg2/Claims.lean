/-
# Dregg2.Claims — RETIRED as the assurance journal; KEPT as the corpus-wide CI pin-net.

⚑ RETIREMENT NOTICE (W5). This file is no longer the assurance artifact. The current
assurance case — the FIVE top-level guarantees (Authority / Conservation / Integrity /
Freshness / Unfoolability) organized BY GUARANTEE, the right shape for *reading* the case —
is `Dregg2.AssuranceCase` (imported by the root anchor; see also DREGG3 §4). Read THAT to
answer "why should I trust a Q-chain?".

This file was the OLD chronological axiom-hygiene journal (sections by campaign date). That
narrative role is retired. It is RETAINED, unchanged in function, for the one thing
`AssuranceCase` structurally cannot be: the comprehensive, corpus-wide `#assert_axioms` net.
Because this file imports the root `Dregg2` (transitively every module), it can re-pin every
keystone the corpus advertises — including the ~190 in modules `AssuranceCase` does not (and,
to avoid a circular import with the root, cannot) import. Those ~190 pins are the UNIQUE
location of those per-keystone kernel-clean certifications; deleting them would silently drop
axiom-hygiene coverage, so the ledger stays. `AssuranceCase` is the apex; this is the net
beneath it.

The machine-checked half of `metatheory/CLAIMS.md`. Imports the root `Dregg2` (which
transitively pulls in every module) and re-pins every keystone the corpus advertises as
proved/axiom-clean via `#assert_axioms`. A pin fails unless the theorem's full axiom set
is `{propext, Classical.choice, Quot.sound}` — in particular it fails on any `sorryAx`.

This file proves nothing new — it audits:
  * Contents are ONLY `import Dregg2` + `#assert_axioms`/`#assert_namespace_axioms` lines.
  * No `axiom`/`admit`/`native_decide`/`sorry`.
  * Keystones that rest on §8 primitives or `sorry`'d operational obligations are NOT pinned
    here (they would correctly fail). Genuine OPENs are listed in `metatheory/CLAIMS.md`.
  * §8 oracles entering as typeclass parameters/hypotheses (`CryptoKernel`/`World`/`Verifiable`)
    do not appear in `collectAxioms`; theorems depending on them are kernel-clean and pinned.
  * Wrong names cause `unknownConstant` build errors — deliberately.

Two-layer zero-sorry guard:
  (a) Textual CI grep (`scripts/no-sorry-metatheory.sh`): comprehensive but textual only;
      runs the whole `lake build` and fails on any `declaration uses 'sorry'` warning.
      This is the whole-corpus net.
  (b) This ledger (`#assert_axioms` / `#assert_namespace_axioms`): stronger per-claim
      (follows the full dependency DAG, catches transitively-inherited sorry) but targeted
      to its pin list. Not redundant with (a) — each covers what the other cannot.
-/
import Dregg2

namespace Dregg2.Claims

/-! ## §0 — Conservation core (the shared library lemmas; `Dregg2.Conserve`). -/
#assert_axioms Dregg2.Conserve.sum_indicator
#assert_axioms Dregg2.Conserve.sum_pointUpdate
#assert_axioms Dregg2.Conserve.sum_conserve_of_deltas_zero
#assert_axioms Dregg2.Conserve.sum_transfer_conserve

/-! ## §0a — `Core` Law-1 + `Laws` find/verify seam (carried as typeclass fields).

`Core.conservation_step` accesses `ConservesStep.step` (discharged by the executable
kernel, §1). `Laws.search_sound` accesses `SoundSearchable.find_sound` — the non-trivial
plugin contract (`Authority.goodSoundMatcher` satisfies it; `evilMatcher_not_sound` proves
a returns-7 plugin cannot). -/
#assert_axioms Dregg2.Core.conservation_step
#assert_axioms Dregg2.Core.conservation_ordinary
#assert_axioms Dregg2.Core.mint_delta
#assert_axioms Dregg2.Core.burn_delta
#assert_axioms Dregg2.Core.noClone_of_invariant_tensor
#assert_axioms Dregg2.Core.withholding_no_free_copy
#assert_axioms Dregg2.Laws.search_sound
#assert_axioms Dregg2.Authority.goodSoundMatcher
#assert_axioms Dregg2.Authority.evilMatcher_not_sound

/-! ## §1 — The executable spine: `cexec` is step-complete, the cell lives.

`cexec_attests` realizes `Core.ConservesStep` as a theorem about the executable machine;
`conservation_step_realizes_balance` discharges the abstract Law-1 balance and provides
`instConservesStepExec`. `livingCell_sound` is the bisimulation-to-golden-oracle. -/
#assert_axioms Dregg2.Exec.cexec_attests
#assert_axioms Dregg2.Exec.conservation_step_realized
#assert_axioms Dregg2.Exec.conservation_step_realizes_balance
#assert_axioms Dregg2.Exec.livingCell_sound

/-! ## §1b — Record cell: conservation over name-keyed records. -/
#assert_axioms Dregg2.Exec.RecordCell.recCexec_attests
#assert_axioms Dregg2.Exec.RecordCell.recordCell_obs_advances
#assert_axioms Dregg2.Exec.RecordCell.recReplay_preserves_sumEquals
#assert_axioms Dregg2.Exec.RecordCell.recordCell_stepComplete
#assert_axioms Dregg2.Exec.RecordCell.recordCell_run_preserves_sumEquals

/-! ## §2 — Circuit-from-Lean: the CCS bridge + DERIVED verify-law. (`Dregg2.Circuit`) -/
#assert_axioms Dregg2.Circuit.bridge
#assert_axioms Dregg2.Circuit.verify_law_derivable

/-! ## §3 — The atomic Hyperedge (turn = wide pullback over shared TurnId). -/
#assert_axioms Dregg2.Hyperedge.Hyperedge.legs_agree
#assert_axioms Dregg2.Hyperedge.hyper_binding_is_proper
#assert_axioms Dregg2.Hyperedge.Hyperedge.toSharedTurnId
#assert_axioms Dregg2.Hyperedge.Hyperedge.toJointBinding
#assert_axioms Dregg2.Hyperedge.SharedTurnId.toHyperedge
#assert_axioms Dregg2.Hyperedge.ringHyperedge
#assert_axioms Dregg2.Hyperedge.hyper_stepComplete
#assert_axioms Dregg2.Hyperedge.hyperedge_sound
#assert_axioms Dregg2.Hyperedge.hyperedge_sound_needs_binding

/-! ## §4 — Spec.Guard: the ONE verify/find seam (meet-semilattice `attenuate_narrows`). -/
#assert_axioms Dregg2.Spec.Guard.admits_all
#assert_axioms Dregg2.Spec.Guard.admits_any
#assert_axioms Dregg2.Spec.Guard.attenuate_narrows
#assert_axioms Dregg2.Spec.Guard.admits_attenuate
#assert_axioms Dregg2.Spec.Guard.admits_witnessed_iff_discharged
#assert_axioms Dregg2.Spec.Guard.discharged_admits
#assert_axioms Dregg2.Spec.Guard.admits_monotonic
#assert_axioms Dregg2.Spec.Guard.admits_sumEquals
#assert_axioms Dregg2.Spec.Guard.admits_senderAuthorized
#assert_axioms Dregg2.Spec.Guard.admits_nonMembership
#assert_axioms Dregg2.Spec.Guard.admits_oneOf

/-! ## §5 — Spec.Conservation: multi-domain, value-monoid-parametric (committed=cleartext). -/
#assert_axioms Dregg2.Spec.LinearityClass.requires_paired_sibling_iff
#assert_axioms Dregg2.Spec.LinearityClass.is_disclosed_non_conservation_iff
#assert_axioms Dregg2.Spec.LinearityClass.paired_and_disclosed_exclusive
#assert_axioms Dregg2.Spec.linearity_examples
#assert_axioms Dregg2.Spec.conservation_over_monoid
#assert_axioms Dregg2.Spec.conservation_over_monoid_finset
#assert_axioms Dregg2.Spec.disclosed_non_conservation
#assert_axioms Dregg2.Spec.conservative_discloses_nothing
#assert_axioms Dregg2.Spec.committed_of_cleartext
#assert_axioms Dregg2.Spec.committed_iff_cleartext
#assert_axioms Dregg2.Spec.multi_domain_independent
#assert_axioms Dregg2.Spec.turnConserves_balance

/-! ## §6 — Spec.Authority: the generative capability graph (whole-history closure OPEN). -/
#assert_axioms Dregg2.Spec.confers_refl
#assert_axioms Dregg2.Spec.confers_trans
#assert_axioms Dregg2.Spec.introduce_non_amplifying
#assert_axioms Dregg2.Spec.introduce_same_target
#assert_axioms Dregg2.Spec.amplify_needs_held_amplifier
#assert_axioms Dregg2.Spec.mint_needs_held_factory
#assert_axioms Dregg2.Spec.mint_conforms_to_contract
#assert_axioms Dregg2.Spec.gen_conferral_is_attenuation
#assert_axioms Dregg2.Spec.attenuate_is_restrictive_narrowing
#assert_axioms Dregg2.Spec.gen_step_traces
#assert_axioms Dregg2.Spec.revoke_step_adds_nothing
#assert_axioms Dregg2.Spec.introduce_is_gen
#assert_axioms Dregg2.Spec.mint_is_gen
#assert_axioms Dregg2.Spec.amplify_is_gen
#assert_axioms Dregg2.Spec.attenuate_is_restrict
#assert_axioms Dregg2.Spec.revoke_is_restrict

/-! ## §7 — Spec.Lifecycle: creation/death duality (distributed-death co-witness OPEN). -/
#assert_axioms Dregg2.Spec.Lifecycle.acceptsEffects_iff
#assert_axioms Dregg2.Spec.Lifecycle.isTerminal_iff
#assert_axioms Dregg2.Spec.Lifecycle.terminal_rejects_effects
#assert_axioms Dregg2.Spec.Lifecycle.terminal_rejects_transition
#assert_axioms Dregg2.Spec.Lifecycle.migrated_terminal
#assert_axioms Dregg2.Spec.Lifecycle.destroyed_terminal
#assert_axioms Dregg2.Spec.Lifecycle.creation_and_death_are_dual
#assert_axioms Dregg2.Spec.Lifecycle.birthProvable
#assert_axioms Dregg2.Spec.Lifecycle.archival_is_fold
#assert_axioms Dregg2.Spec.Lifecycle.archived_still_live
#assert_axioms Dregg2.Spec.Lifecycle.reclaim_by_lease
#assert_axioms Dregg2.Spec.Lifecycle.creation_provable_death_temporal

/-! ## §8 — Spec.JointViaHyper: N-ary joint DERIVED from hyperedge_sound. -/
#assert_axioms Dregg2.Spec.joint_via_hyperedge
#assert_axioms Dregg2.Spec.binary_binding_from_hyperedge
#assert_axioms Dregg2.Spec.binary_joint_via_hyperedge
#assert_axioms Dregg2.Spec.singletonHyperedge
#assert_axioms Dregg2.Spec.hyperedge_is_validity_not_canonicity
#assert_axioms Dregg2.Spec.selector_needs_more_than_validity

/-! ## §9 — Spec.Choreography: blue/red split → red projects to a Hyperedge (operational OPEN). -/
#assert_axioms Dregg2.Spec.RedBinding.toHyperedge
#assert_axioms Dregg2.Spec.red_projects_to_hyperedge
#assert_axioms Dregg2.Spec.red_legs_agree
#assert_axioms Dregg2.Spec.blue_commits_independently
#assert_axioms Dregg2.Spec.blue_needs_no_hyperedge
#assert_axioms Dregg2.Spec.red_iff_coupled
#assert_axioms Dregg2.Spec.epp_membrane_is_projection

/-! ## §10 — Spec.Await: the await family = temporal Guard ⊕ dataflow DAG (topo-sort OPEN). -/
#assert_axioms Dregg2.Spec.Conditional.conditional_is_temporal_guard
#assert_axioms Dregg2.Spec.Conditional.resolved_iff_gateway_discharged
#assert_axioms Dregg2.Spec.Conditional.resolve_monotone
#assert_axioms Dregg2.Spec.Conditional.expired_stays_expired
#assert_axioms Dregg2.Spec.Conditional.gateway_admits_eq_token
#assert_axioms Dregg2.Spec.Conditional.PromiseGraph.depends_irrefl
#assert_axioms Dregg2.Spec.Conditional.PromiseGraph.depends_trans
#assert_axioms Dregg2.Spec.Conditional.PromiseGraph.broken_promise_propagates
#assert_axioms Dregg2.Spec.Conditional.PromiseGraph.broken_promise_propagates_trans
#assert_axioms Dregg2.Spec.Conditional.await_two_faces
#assert_axioms Dregg2.Spec.Conditional.temporal_face_is_await_discharge

/-! ## §11 — Spec.VatBoundary: Φ the named-lossy caps↔keys functor. `phi_functorial` is
proved under the explicit `NonDegenerate` hypothesis (the residual — not a `sorry`);
`nonDegenerate_concrete` proves the hypothesis is satisfiable. -/
#assert_axioms Dregg2.Spec.phi_admits_iff_discharged
#assert_axioms Dregg2.Spec.cross_vat_needs_witness
#assert_axioms Dregg2.Spec.phi_drops_confinement
#assert_axioms Dregg2.Spec.forwarded_cap_is_revocable
#assert_axioms Dregg2.Spec.revocable_iff_not_authority
#assert_axioms Dregg2.Spec.macaroon_does_not_cross_phi
#assert_axioms Dregg2.Spec.biscuit_crosses_phi
#assert_axioms Dregg2.Spec.phi_domain_is_exactly_biscuit
#assert_axioms Dregg2.Spec.phi_composes_with_attenuation
#assert_axioms Dregg2.Spec.phi_attenuation_factors_through_confers
#assert_axioms Dregg2.Spec.phi_functorial
#assert_axioms Dregg2.Spec.nonDegenerate_concrete
#assert_axioms Dregg2.Spec.phi_functorial_concrete

/-! ## §12 — Spec.Coherence: the cross-subsystem weave (guard = authority meet).

OPEN: pins parked pending olean rebuild. `Dregg2.Spec.Coherence` is sorry-free in source
and self-pins in its own module, but is not yet in this file's import closure. Re-enable
once `Dregg2.Spec.Coherence.olean` exists. Listed as proved in `metatheory/CLAIMS.md`. -/
-- #assert_axioms Dregg2.Spec.guard_is_authority_conferral
-- #assert_axioms Dregg2.Spec.conferralGuard_admits_self
-- #assert_axioms Dregg2.Spec.introduce_passes_conferralGuard
-- #assert_axioms Dregg2.Spec.conservation_is_hyperedge_cg5
-- #assert_axioms Dregg2.Spec.hyperedge_conserves_crossCell
-- #assert_axioms Dregg2.Spec.lifecycle_revoke_is_authority_restrictive
-- #assert_axioms Dregg2.Spec.revoke_is_terminal_restrictive
-- #assert_axioms Dregg2.Spec.migrated_and_destroyed_both_revoke
-- #assert_axioms Dregg2.Spec.choreography_red_conserves
-- #assert_axioms Dregg2.Spec.choreography_red_conserves_sum
-- #assert_axioms Dregg2.Spec.guard_attenuate_narrows_is_meet
-- #assert_axioms Dregg2.Spec.authority_confers_narrows_is_meet

/-! ## §13 — Finality: the 4-tier lattice; conservation is tier-independent. -/
#assert_axioms Dregg2.Finality.conservation_tier_independent
#assert_axioms Dregg2.Finality.conservation_tier_independent_iff

/-! ## §14 — Liveness: GC-as-cell-liveness; revocation needs consensus (unlike collection). -/
#assert_axioms Dregg2.Liveness.revocation_needs_consensus

/-! ## §15 — Exec.Consensus: quorum→finality-tier bridge (Byzantine safety stays OPEN). -/
#assert_axioms Dregg2.Exec.Consensus.quorum_reaches_bft_tier
#assert_axioms Dregg2.Exec.Consensus.committedByQuorum_reaches_bft_tier
#assert_axioms Dregg2.Exec.Consensus.below_quorum_not_bft
#assert_axioms Dregg2.Exec.Consensus.net_no_downgrade
#assert_axioms Dregg2.Exec.Consensus.net_no_downgrade_via_world
#assert_axioms Dregg2.Exec.Consensus.finality_monotone_on_net
#assert_axioms Dregg2.Exec.Consensus.quorum_grows_preserves_finality
#assert_axioms Dregg2.Exec.Consensus.committed_holds_along_rounds
#assert_axioms Dregg2.Exec.Consensus.cross_tier_join_on_net
#assert_axioms Dregg2.Exec.Consensus.NetCell.tier_eq_bft_iff

/-! ## §16 — Upgrade: anti-brick set_program (version pin + signature fallback).

The two anti-brick keystones are pinned. The eight Envelope-spine keystones are sorry-free
in source and self-pinned in `Dregg2/Upgrade.lean`, but not yet in this file's closure —
parked (same reason as §12). Re-enable after rebuild. -/
#assert_axioms Dregg2.Upgrade.upgrade_never_bricks
#assert_axioms Dregg2.Upgrade.stale_version_falls_back_to_signature
-- #assert_axioms Dregg2.Upgrade.invariant_intro
-- #assert_axioms Dregg2.Upgrade.safety_preservation
-- #assert_axioms Dregg2.Upgrade.admit_preserves_safety
-- #assert_axioms Dregg2.Upgrade.self_improvement_is_safe
-- #assert_axioms Dregg2.Upgrade.genealogy_sound
-- #assert_axioms Dregg2.Upgrade.identity_vouch_unconditional
-- #assert_axioms Dregg2.Upgrade.upgradeGenealogy_sound
-- #assert_axioms Dregg2.Upgrade.signatureVouchUnbrickable

/-! ## §17 — Proof.Refine: Exec ⊑ Abstract refinement (full simulation diagram OPEN). -/
#assert_axioms Dregg2.Proof.refine_conservation
#assert_axioms Dregg2.Proof.refine_conservation_measure
#assert_axioms Dregg2.Proof.refine_run_conservation
#assert_axioms Dregg2.Proof.refine_integrity
#assert_axioms Dregg2.Proof.refine_integrity_intra

/-! ## §18 — VCG/WP program logic, operational LTS, Pedersen §8 discharge, first-app Spec.

Pinned at the namespace level (every theorem in each namespace is asserted kernel-clean). -/
#assert_namespace_axioms Dregg2.Proof.WP
#assert_namespace_axioms Dregg2.Proof.LTS
#assert_namespace_axioms Dregg2.Crypto.Merkle
#assert_namespace_axioms Dregg2.Crypto.Pedersen
#assert_namespace_axioms Dregg2.Crypto.PredicateKernel
#assert_namespace_axioms Dregg2.Protocol.WorkflowGuard

/-! ## §19 — OPENs closed + authority-turn LTS.

Deadness-undecidability (computable form via `haltGraph` halting reduction),
quorum-intersection (honest union-cardinality bound), and GST-liveness (from a
`World.gst_liveness` class field). -/
#assert_axioms Dregg2.Liveness.dead_undecidable
#assert_axioms Dregg2.Spec.Lifecycle.distributed_death_not_co_witnessable
#assert_axioms Dregg2.Exec.CellLiveness.death_not_decidable
#assert_axioms Dregg2.World.quorum_intersection_safety
#assert_axioms Dregg2.World.liveness_after_gst
#assert_axioms Dregg2.Exec.recKDelegate_frame
#assert_axioms Dregg2.Exec.recKRevokeTarget_frame
#assert_axioms Dregg2.Exec.recKDelegate_execGraph
#assert_axioms Dregg2.Exec.recKRevokeTarget_execGraph
#assert_axioms Dregg2.Exec.recKDelegate_grounds

/-! ## §20 — LTS-gated + framing OPENs closed; third §8 discharge (`Crypto.NonMembership`).

`deadlock_freedom_by_design` proved over the choreography reachable-config LTS `GStep`/
`GReach` on the `NoRec` fragment. Both `Hyperedge` opens restated and proved.
`Crypto.NonMembership` (sorted-tree neighbor-bracketing). -/
#assert_namespace_axioms Dregg2.Crypto.NonMembership
#assert_namespace_axioms Dregg2.Coordination
#assert_namespace_axioms Dregg2.Hyperedge

/-! ## §21 — 4th/5th §8 discharges + BFT safety/liveness + cross-cell LTS + WP catalog.

`Crypto.Temporal`/`Crypto.Dfa` (both-direction bridges), `Proof.BFT` (O1 strong
`bft_safety` via `n−f` quorum intersection + O2 GST liveness; all adversary assumptions
are structure fields), `Proof.CrossCellLTS` (bilateral forward-simulation + tensor-non-finality
obstruction), `Proof.WPCatalog` (eDSL → vcg → `vcg_run_sound` closed loop). Residuals are
prose OPEN comments, not sorries. -/
#assert_namespace_axioms Dregg2.Crypto.Temporal
#assert_namespace_axioms Dregg2.Crypto.Dfa
#assert_namespace_axioms Dregg2.Proof.BFT
#assert_namespace_axioms Dregg2.Proof.CrossCellLTS
#assert_namespace_axioms Dregg2.Proof.WPCatalog

/-! ## §22 — BFT liveness + N-ary forest LTS + contention dichotomy + 6th §8 discharge.

`Proof.BFTLiveness` (pacemaker closed; `World.gst_liveness` derived from DLS88+HotStuff fields),
`Proof.ForestLTS` (N-ary cross-cell forest square), `Proof.ContendedCrossCell` (I-confluent ⇒
schedule-agnostic commit; coupled Σ=0 ⇒ ¬∃ schedule-agnostic commit), `Crypto.Bridge`
(6th §8 discharge). -/
#assert_namespace_axioms Dregg2.Proof.BFTLiveness
#assert_namespace_axioms Dregg2.Proof.ForestLTS
#assert_namespace_axioms Dregg2.Proof.ContendedCrossCell
#assert_namespace_axioms Dregg2.Crypto.Bridge

/-! ## §23 — Replacement executor reaches the wire + coinductive OPEN closes.

`Exec.TurnExecutor` (all 4 StepInv conjuncts, step-complete by construction) +
`Exec.Forest` (nested delegated call-forest, Granovetter-preserving, N-ary Σ=0
conservation) = the replacement turn-executor. `Exec.CircuitEmit` (kernel + Merkle +
algebraic ConstraintExpr circuits emit faithfully to the fingerprint-bound Rust backend).
`Proof.CoinductiveAdversary` (`obsBisim_of_uptoComm`) closes the coinductive open via
vendored Paco (gupaco up-to-context closure). -/
#assert_namespace_axioms Dregg2.Exec.TurnExecutor
#assert_namespace_axioms Dregg2.Exec.Forest
#assert_namespace_axioms Dregg2.Exec.CircuitEmit
#assert_namespace_axioms Dregg2.Proof.CoinductiveAdversary
#assert_namespace_axioms Paco

/-! ## §24 — Full op-set + cross-cell forest + runtime + eDSL + schema-migration + gadget circuits.

`TurnExecutorFull` covers every turn kind; `CrossCellForest` (Σ=0 binding-carried);
`CellRuntime` (checkpoint/replay/time-travel); `DSLEffect` (eDSL trilogy); `migrate_*`
(schema migration without bricking); `CircuitEmitGadgets` (gadget circuits to the wire). -/
#assert_namespace_axioms Dregg2.Exec.TurnExecutorFull
#assert_namespace_axioms Dregg2.Exec.CrossCellForest
#assert_namespace_axioms Dregg2.Exec.CellRuntime
#assert_namespace_axioms Dregg2.Exec.CircuitEmitGadgets
#assert_namespace_axioms Dregg2.DSLEffect
#assert_axioms Dregg2.Exec.migrate_conforms
#assert_axioms Dregg2.Exec.migrate_conserves
#assert_axioms Dregg2.Exec.migrate_anti_brick

/-! ## §25 — Gas metering + canonical interior beacon-space witness.

`Gas`: `gas_exhaustion_fails_closed` (over-budget ⇒ none, no partial mutation);
`gas_sufficient_runs` (metered = un-metered when affordable); orthogonal to conservation.
`BeaconSpaceInterior`: instantiation at strictly-interior `h=3/4` via `Measure.infinitePi
(Bernoulli 3/4)^ℕ` with genuine cross-view independence. -/
#assert_namespace_axioms Dregg2.Exec.Gas
#assert_namespace_axioms Dregg2.Proof.BeaconSpaceInterior

/-! ## §26 — Proof-carrying forest + tri-domain conservation + auth modes + Transfer vertical slice.

`ProofForest`: per-node `StepProofValid` × `Linked` ⇒ whole forest attests StepInv.
`TriDomain` (balance+authority+metadata, each independently conserving). `AuthModes` (6 modes
with witness dispatch; `captp_granted_le_held` non-amplification). `EffectTransfer` (vertical-slice
template). `TransferAir` (BabyBear constraint soundness + `transfer_underflow_attack` gap theorem). -/
#assert_namespace_axioms Dregg2.Exec.ProofForest
#assert_namespace_axioms Dregg2.Exec.TriDomain
#assert_namespace_axioms Dregg2.Exec.AuthModes
#assert_namespace_axioms Dregg2.Exec.EffectTransfer
#assert_namespace_axioms Dregg2.Spike.TransferAir

/-! ## §27 — Full effect catalog via the EffectTransfer template (E3 complete).

`EffectsPaired` (Conservative Σδ=0), `EffectsSupply` (Generative/disclosed), `EffectsAuthority`
(cap-graph edits, granted≤held non-amplification), `EffectsState` (Neutral/Monotonic/Terminal). -/
#assert_namespace_axioms Dregg2.Exec.EffectsPaired
#assert_namespace_axioms Dregg2.Exec.EffectsSupply
#assert_namespace_axioms Dregg2.Exec.EffectsAuthority
#assert_namespace_axioms Dregg2.Exec.EffectsState

/-! ## §28 — Executor axis E4–E6 complete: refinement + conditional turns + FFI.

`ExecRefinementFull` (E5): unified `AbsStep` LTS + `exec_full_refines_spec` + full operational
square; `OnlyConnectivityCloses` is a named hypothesis, not a sorry. `ConditionalTurn` (E4):
`execConditionalTurn` (finite Kahn topo-sort + EventualRef slots), EventualRef = `Await.Op.await`.
E6: `@[export] dregg_exec_full_turn` FFI in `Exec/FFI.lean`. -/
#assert_namespace_axioms Dregg2.Spec.ExecRefinementFull
#assert_namespace_axioms Dregg2.Exec.ConditionalTurn

/-! ## §29 — EffectVM constraints + Cordial-Miners DAG consensus.

`Spike.EffectVmConstraints`: 7 BabyBear AIR constraints; `underflow_now_impossible` proves
the in-circuit range proof makes the Transfer-spike wrap impossible.
`Proof.CordialMiners`: models dregg1's DAG-BFT (wave/leader/ratify/super-ratify) and proves
`cordial_agreement` via `n>3f` quorum intersection. Liveness/GST/dissemination are named OPENs. -/
#assert_namespace_axioms Dregg2.Spike.EffectVmConstraints
#assert_namespace_axioms Dregg2.Proof.CordialMiners

/-! ## §30 — De-vacuification: faithfulness-audit findings fixed.

(1) `EffectsAuthority` non-amplification: genuine over the real `List Auth` lattice
(`introduce_non_amplifying`/`exercise_non_amplifying` via `attenuate_subset`;
`amplifying_grant_rejected` as teeth). (2) `TriDomain` authority measure folds the real
cap table. (3) `ConditionalTurn.CondAbsStep` now `conservedInDomain Domain.balance [a'−a]`
(was the always-true `∃δ,a'=a+δ`). (4) `CordialMiners` SuperRatification derived from the
lace. (5) `EffectVmConstraints2` adds SetField-gating + `setfield_aux_honesty_gap` (gap as theorem). -/
#assert_namespace_axioms Dregg2.Spike.EffectVmConstraints2

/-! ## §31 — Caveat + attestation faces, faithful to the Rust ground truth.

`Authority.CaveatChain`: macaroon HMAC append-only chain (verify_iff_wellTagged, append_narrows,
forgery_requires_mac_query). `Authority.ThirdParty`: real 3P discharge (accepts_iff over
ticket/VID key-recovery ∧ bind-to-parent ∧ freshness; rejection teeth). `Authority.SelectiveDisclosure`:
hidden-attribute proofs + selective reveal + anonymous multi-show. `Authority.DV`: verifier-indexed
`DischargedFor` + transferability dial (public = ∀V non-repudiable; designated = V₀-only deniable).
Crypto stays an honest §8 Prop-portal throughout. -/
#assert_namespace_axioms Dregg2.Authority.CaveatChain
#assert_namespace_axioms Dregg2.Authority.ThirdParty
#assert_namespace_axioms Dregg2.Authority.SelectiveDisclosure
#assert_namespace_axioms Dregg2.Authority.DV

/-! ## §32 — Consistency + non-vacuity witness.

`Dregg2.Consistency`: `dregg_consistent_nonempty` exhibits a single axiom-clean `SystemModel`
instantiating all 11 system-level Prop-carriers with discriminating (non-trivial) witnesses;
cluster lemmas confirm co-instantiation does not derive False. The §8 crypto carriers are the
honest boundary (assume DLog is hard = Lean-trivial by design), not counted as non-vacuity
evidence. -/
#assert_namespace_axioms Dregg2.Consistency

/-! ## §33 — Handler-transformer: safe composition = frame-preserving update.

`Dregg2.HandlerTransformer`: `SafeStep` preorder; `instSafeStepFpu` (camera Fpu IS a
`SafeStep`); `safe_transformer_composes`; `conservation_is_safe_transformer`; `overshare_rejected`
(teeth: an over-sharing transformer is refused). Honest OPENs: the Fpu=sheaf-gluing weld and the
comodel-morphism/sheaf-of-handlers tier. -/
#assert_namespace_axioms Dregg2.HandlerTransformer

/-! ## §34 — The Hatchery (HATCHERY.md H1–H4) + the web-citizen ProofWidgets surface.

`Dregg2.Verify.*` is the Hatchery verification toolkit: `carry_forever`/`exec_frame` (Tier 1, with
an HONEST hand-back — `logMono_handback_demo` proves it never fakes a close), the `[Dregg2]`-tagged
forest-monotone frame family (Tier 2), the first-class `CellContract` with `forever` + the REAL LTL
`□` `always` (Tier 3, wired through `Proof.Temporal.always_of_step_invariant`), and the declarative
shape-catalog macros `monotone_registry%`/`conservation%`/`confinement%`/`automaton_inv%` (Tier 4).
`Verify.Regression` reproduces six shipped crowns via the catalog with both-directions defeq
witnesses. The headline keystones, pinned to the kernel triple:

The presentation layer `Dregg2.Widget.*` (the ProofWidgets vocabulary — every panel rendering REAL
executor state / `Lean.collectAxioms` verdicts, NO placeholder data) is built in-corpus via the root
import but is intentionally NOT pinned here: `Widget.Basic` declares two clearly-named DEMO axioms to
exhibit the amber "carrier-bounded" trust tier (a synthetic theorem depending on a fake §8 carrier, so
its badge is amber). That by-design dependency would correctly fail a clean-triple pin —
exactly as the §8-resting keystones are (correctly) omitted from this ledger. -/
#assert_axioms Dregg2.Verify.logMono_via_tactics
#assert_axioms Dregg2.Verify.revoked_grow_via_tactics
#assert_axioms Dregg2.Verify.identity_revoked_forever_via_tactics
#assert_axioms Dregg2.Verify.commitments_persist_via_auto
#assert_axioms Dregg2.Verify.logMono_handback_demo
#assert_axioms Dregg2.Verify.CellContract.forever
#assert_axioms Dregg2.Verify.KernelForest.always
#assert_axioms Dregg2.Verify.logAppendOnly
#assert_axioms Dregg2.Verify.conserved
#assert_axioms Dregg2.Verify.revokedPersists
#assert_axioms Dregg2.Verify.identity_revoked_forever_via_catalog

end Dregg2.Claims
