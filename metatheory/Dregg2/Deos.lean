/-
# Dregg2.Deos — the VERIFIED-DEOS crown: "a verified desktop OS" made literal.

`docs/deos/DEOS.md` §"the verified-deos program": *"every visual/interactive primitive reduces to a
kernel theorem. None are new mathematics — they are the firmament's existing proofs (attenuation,
gateOK, the receipt chain, unfoolability) restated for pixels, affordances, and rehydration."*

`deos` is the agentic desktop userlayer: cap-confined surfaces, the certified compositor, the
web-of-cells, the rehydratable frustum-snapshots — *dregg made visual, with zero new trust*. The Rust
realization already shipped (the rehydration + affordance steel in `starbridge-web-surface`); this lane
is the PROOF that it cannot amplify / the liveness-type IS the confined fragment. The four targets, each
a kernel theorem restated for the desktop:

  1. **Surface-as-capability** (`Dregg2.Deos.Surface`) — a `Target::Surface(cell)` is a kernel
     `Cap.endpoint cell rights`; a window confers no authority beyond its rights, and a view/notify-only
     surface confers NO Granovetter edge (`viewSurface_confers_no_edge`, the
     `notifyCap_confers_no_edge` shape). Projecting a surface to fewer rights cannot amplify
     (`surface_attenuate_no_amplify` = `Dregg2.Exec.attenuate_subset`).

  2. **Membrane non-amplification** (`Dregg2.Deos.Membrane`) — the rehydration membrane composes
     attenuation across hops: `reshare A→B→C ⟹ C ⊆ B ⊆ A` (`reshare_chain_attenuates`, the per-hop
     `attenuate_subset` lifted by `List.Subset.trans`), generalized to arbitrarily-long reshare chains
     (`reshareN_attenuates`). The Rust `Membrane` is the realization; this is the proof it cannot
     amplify. A widening is darkened, not granted (`reshare_refuses_amplification`).

  3. **Rehydration confinement = the liveness-type** (`Dregg2.Deos.Rehydration`) — THE CROWN.
     `ReplayedDeterministic` IS *exactly* the confined fragment: for a non-`Live` context,
     `classify = ReplayedDeterministic ↔ every interaction was a witnessed attested turn`
     (`replayedDeterministic_iff_confined`). The doc's "derived" row, as an `↔`. The replay payoff
     (`replayedDeterministic_replays`) rides the EXISTING receipt-chain tamper-evidence
     (`Dregg2.Exec.Receipts.chain_tamper_evident`) under the §8 digest oracle, carried as NAMED
     hypotheses.

  4. **Affordance soundness** (`Dregg2.Deos.Affordance`) — a cell-affordance interaction is a verified
     turn: an agent fires ONLY the affordances its caps authorize (`fire_authorized_iff`, the
     `is_attenuation` gate `required ⊆ held`), the post-state surface binds the attested root
     (`firedSurface_binds_attested_root`, the receipt's `newCommit`), and progressive enhancement is
     progressive ATTENUATION (`projectFor_monotone`).

## Honesty ledger (legs fully discharged vs carried as named hypotheses)

  * Legs 1, 2, 4 and the leg-3 CLASSIFIER CROWN (`replayedDeterministic_iff_confined` + its dual) are
    FULLY DISCHARGED — pure structural facts over the kernel cap/attenuation lattice and the receipt
    record, no oracle, every keystone `#assert_all_clean` (kernel-clean: only `propext` /
    `Classical.choice` / `Quot.sound`).
  * Leg 3's REPLAY PAYOFF (`replayedDeterministic_replays`) carries the receipt-digest
    collision-resistance as NAMED hypotheses `HInj : Function.Injective H` / `HFresh : ∀ p, H p ≠
    genesisSentinel` — the SAME `dregg2 §8` oracle `Dregg2.Exec.Receipts.chain_tamper_evident` already
    names, NEVER a Lean axiom and NEVER a `sorry`. This is the one honest seam (the digest's
    collision-resistance), in the house honesty-ledger style: a named crypto primitive, not a laundered
    vacuity. The CROWN itself (the confinement `↔`) needs no such hypothesis.

Everything builds LOCAL (`lake build Dregg2`, cwd `metatheory/`) green + axiom-clean. `metatheory/`
only; no core-`Auth`/`Cap`/`Receipt` edit — every theorem is an existing kernel proof restated for
surfaces / membranes / rehydration / affordances.
-/
import Dregg2.Deos.Surface
import Dregg2.Deos.Membrane
import Dregg2.Deos.Rehydration
import Dregg2.Deos.Affordance
-- The COMPOSITION / RERENDER / VISIBILITY widening (2026-06-14): the desktop's UI-composition
-- theorems — phrased to be MORE assured than the Cross-Domain Desktop Compositor (CDDC) ever was
-- (which trusted its compositor TCB for cross-domain isolation and shipped no machine-checked
-- non-interference). These three lanes make that proof.
import Dregg2.Deos.FogOfWar     -- per-viewer visibility NON-INTERFERENCE (the CDDC-beating headline)
import Dregg2.Deos.Compositor   -- the compositing ALGEBRA: damage is exact, paint is order-free
import Dregg2.Deos.Rerender     -- re-rendering a component is FUNCTORIAL (the rerender square)
-- The CAP ∧ STATE conjunction (2026-06-14, the language uplift): the deos affordance gate was CAP-ONLY
-- (fireGate: required⊆held) and the cell-program gate STATE-ONLY (RecordProgram.admitsCtx) — they never
-- composed. A GatedAffordance pairs the REAL cap-gate with the REAL state-gate and fireGated commits IFF
-- BOTH bite (fireGated_iff); the four cross-polarity teeth prove neither alone suffices (caps-OK-but-
-- stale and ready-but-unheld both refuse), the htmx tooth (fireGated_reactive) proves the SAME viewer's
-- button reacts to STATE, and projectGatedFor lifts the membrane-negotiated frustum to STATE-awareness.
import Dregg2.Deos.GatedAffordance
-- The TEMPORAL/REACTIVE rung (2026-06-14, the language uplift): beyond GatedAffordance's single-state
-- gate — TransitionGate (the `link` reads BOTH old+new, so a property of `new` alone can never witness
-- it), deadline/window gates (past `close` an authorized transition auto-refuses), and
-- membrane-as-predicate — two viewers at EQUAL cap-authority but different witness-graph permits project
-- DISTINCT surfaces (`membrane_two_viewers_distinct`: the per-viewer frustum divides by projection, not
-- just caps). 16 keystones #assert_all_clean.
import Dregg2.Deos.Reactive
-- The THREE OPEN CONTINENTS sharpened (2026-06-14, `desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md`):
-- advances the crown past its three named-but-waved residuals. C1 — the replay DERIVATION: replay
-- DETERMINISM (the fold is a function of the witnessed trace) is DISTINCT from the crown's tamper-
-- evidence payoff and needs NO §8 oracle — it is FORCED by `confined` (every step reads only the
-- witness; `confined_replay_deterministic` + `replay_extensional_in_witness`; `.ambient` is the typed
-- floor, `ambient_trace_unconfined`). C2 — the membrane-NEGOTIATION semantics ("the unspecified
-- continent"): the negotiated projection IS the meet `held ⊓ ask` (= `attenuate`), and the two
-- compositional FAILURE MODES are theorems — the confused-deputy (`deputy_confers_no_unheld_target`:
-- `attenuate` preserves the target, so a requester cannot retarget G's cap) and attenuation-drift
-- (`drift_cannot_recover_dropped_authority`: path-independence on top of `reshareN_attenuates`'s value
-- bound). C3 — the dregg4 forward: the single-machine n=1 atomicity collapse
-- (`single_machine_commit_needs_no_binding` = `family_atomicity` at `ι := Unit` — commit ⇔ the one
-- cell's success, NO CG-5 binding; the cross-cell cut is the price of n≥2). 8 keystones #assert_all_clean.
import Dregg2.Deos.ReplayMembrane
-- The CHOREOGRAPHY COHERENCE (2026-06-14, the "composable flows?" question answered): the deos surface
-- does NOT fork the existing Protocol/Workflow + choreography stack — it RENDERS it. A Protocol.Workflow
-- step IS a sequenced GatedAffordance/Reactive fire: workflowStep_is_gatedAffordance (a step's
-- (authorizedParty, precond) IS a cap∧state button), workflow_fires_iff_affordance_fires (exec ↔
-- gated-fire ∧ attest), phaseTransition_is_reactiveAffordance (a precond→postPhase IS the transition
-- gate); the order/skip/cap teeth carry through. 10 keystones #assert_all_clean.
import Dregg2.Deos.WorkflowBridge
-- The FLOW-COMPOSITION ALGEBRA is RIGHT-SKEWED (2026-06-14, the "does choice distribute over
-- composition?" question answered with a Lean proof): dregg's workflow/affordance-flow algebra satisfies
-- only the HALF `(P⋆R)⊔(Q⋆R) ≤ (P⊔Q)⋆R` (flow_choice_halfdistrib) — the converse FAILS
-- (flow_choice_right_skewed, the headline), so it is a right-skewed Kleene algebra with distributive
-- meets (RSKA_d⊓, à la Pradic's Weihrauch lattice). The separation is NOT in the trace language (both
-- sides denote the same set — flow_choice_languages_equal, the dregg Example 1.1); it lives in the
-- ONLINE step-by-step simulation order (≤ᶠ), the algebraic shadow of the reactive rung: in (P⊔Q)⋆R the
-- choice reads R's OUTPUT (the TransitionGate's old+new read), which the early-branch side cannot
-- anticipate with no lookahead. The distributive meet is real (flow_meet_semilattice). PAYOFF (the
-- PRECONDITION, here): right-skew ⟹ "does flow/caveat-policy A refine B" is DECIDABLE via Pradic's
-- Büchi-game characterization — built in Dregg2.Deos.FlowRefine below. 18 keystones #assert_all_clean.
import Dregg2.Deos.FlowAlgebra
-- The FLOW-REFINEMENT DECISION PROCEDURE (2026-06-14, the right-skew PAYOFF made CONSTRUCTIVE): "does flow
-- / caveat-policy A refine B?" (A ≤ᶠ B) is DECIDABLE. The dregg analogue of Pradic's Theorem 1.4 — the
-- ONLINE simulation order ≤ᶠ is characterized by a finite σ-free SIMULATION GAME (DupSim, Duplicator-win =
-- a PStep-simulation; the Büchi acceptance collapses because the iteration-free fragment makes procSize
-- strictly decrease, pstep_decreases) and decided by a kernel-reducible fuel-bounded greatest-simulation
-- check (decideRefines : Proc → Proc → Bool, decideRefines_iff: = true ↔ A ≤ᶠ B, SOUND+COMPLETE). The
-- σ-UNIFORMITY linchpin (step_to_pstep/pstep_to_step: no Step rule's letter/successor is gated by the
-- threaded state) collapses ≤ᶠ's ∀σ to ONE game, yielding the full Decidable (A ≤ᶠ B) instance
-- (instDecidableSim) — the ARGUS "refines" bar is a DECISION, not a hope. The procedure RECOMPUTES the
-- right-skew on FlowAlgebra's own counterexample, both polarities (decideRefines earlyEx lateEx = true,
-- decideRefines lateEx earlyEx = false — #guard, kernel-evaluated, agreeing with flow_choice_halfdistrib /
-- flow_choice_right_skewed). 18 keystones #assert_all_clean.
import Dregg2.Deos.FlowRefine
-- TRANSCLUSION (2026-06-14, "Xanadu that shipped"): Ted Nelson's transclusion — include-by-reference
-- with preserved provenance + unbreakable links + per-viewer confinement — made HONEST. A transclusion
-- IS a verified cross-cell observation: `Transclusion := Authority.ImportBinding.ImportedEq`, a peer
-- cell's finalized field cited at an immutable receipt. The four Xanadu properties, each a REUSE of an
-- existing kernel theorem: transclusion_is_observed_finalized_read (the bridge = ImportedEq.admits_iff),
-- transclusion_provenance_faithful (the quote equals its source, a forge cannot be cited =
-- importedEq_binds_provenanced_value + importedEq_lying_import_rejected), transclusion_no_amplify (a
-- quote is a READ, per-viewer through the membrane = Membrane.reshareN_attenuates), and the crown
-- transclusion_stable_under_source_advance (THE UNBREAKABLE LINK — the quote never rots =
-- importedEq_stable_under_source_advance, the I-confluence). 10 keystones #assert_all_clean.
import Dregg2.Deos.Transclusion

namespace Dregg2.Deos

/-! ## The verified-deos namespace assembles the four core legs + three composition lanes. Each
sub-module pins its own keystones kernel-clean (`#assert_all_clean`); this umbrella re-exports them as
the single `Dregg2.Deos` surface.

The four core targets, as one sentence: a deos surface is a kernel cap (leg 1) whose per-viewer
projection and membrane reshares cannot amplify (legs 1+2), whose affordances fire only under the
`is_attenuation` gate and bind the attested root (leg 4), and whose rehydration liveness-type IS exactly
the confined fragment (leg 3, the crown).

The three composition lanes lift the desktop from "every primitive is a kernel theorem" to "every UI
COMPOSITION is a kernel theorem" — the things a windowing system's correctness actually rests on, and
the things the CDDC *trusted its TCB to provide*:

  5. **Per-viewer visibility non-interference** (`Dregg2.Deos.FogOfWar`) — THE CDDC-BEATING HEADLINE.
     A low viewer's render is a FUNCTION of the low-authorized state ALONE: changing a hidden cell leaves
     the view bit-identical (`noninterference` + `hidden_change_invisible`), a hidden cell is structurally
     ABSENT (`hiddenCell_absent`), two viewers diverge by exactly their authority (`divergence`), and
     vision is monotone in capability (`vision_monotone`). The cross-domain non-interference the CDDC
     trusted its compositor process to provide — here a machine-checked theorem about the projection.
     This is the information-flow sibling of leg-3's confinement crown: "what you see" is determined by
     exactly the fragment inside your capability, the same shape as "what replays".

  6. **The compositing algebra** (`Dregg2.Deos.Compositor`) — built on `Apps.Compositor`'s verified
     scene-graph. Damage is EXACT (`present_damage_exact` + `unchanged_outside_target`: a present dirties
     exactly its declared regions, the dirty-region tracking is sound), paint is ORDER-FREE on a
     well-formed scene (`paint_order_independent`: T1's disjointness makes z-order irrelevant to the
     pixels, so the glass is well-defined independent of paint order), ownership is unambiguous
     (`ownerAt_unique`), the frame property holds (`render_frame_property`: editing one window cannot
     perturb another's pixels — the compositional dual of non-interference), and the scene-graph is
     closed under disjoint composition (`compose_preserves_wellFormed` + `compose_assoc`).

  7. **Rerender functoriality** (`Dregg2.Deos.Rerender`) — re-rendering is a FUNCTOR over `projectFor`.
     The rerender SQUARE commutes (`rerender_square`: re-rendering after a state update equals updating
     the rendered surface — `project ∘ step = step ∘ project`, the central web-framework guarantee),
     it is deterministic + idempotent (`rerender_idempotent`), buttons are stable across content updates
     (`rerender_after_step_authorized`), and the frustum-snapshot re-expands faithfully + per-viewer
     (`snapshot_roundtrip` + `snapshot_roundtrip_attenuated`: a snapshot is a lossless, per-viewer handle
     to the surface, not a lossy thumbnail).

"A verified desktop OS": every visual/interactive primitive AND every UI composition reduces to a kernel
theorem — and the cross-domain isolation the CDDC trusted is, here, proven. -/

end Dregg2.Deos
