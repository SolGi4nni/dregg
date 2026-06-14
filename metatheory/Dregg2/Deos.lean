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
