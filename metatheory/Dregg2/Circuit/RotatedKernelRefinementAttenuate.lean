/-
# Dregg2.Circuit.RotatedKernelRefinementAttenuate — the capability/attenuation VALUE leg of the
soundness apex, closed HONESTLY for `attenuate` against the GENUINE non-amp descriptor.

## What this module closes — and what it deliberately does NOT (the honest class)

The capability/attenuation family's security crux is IN-CIRCUIT NON-AMPLIFICATION: a light client
must not be foolable by a delegation that GRANTS more than the delegator HELD. The kernel leaf spec is
`AttenuateSpec` (`Spec/authorityattenuation.lean`): `s'.kernel.caps = attenuateSlotF s.kernel.caps
actor idx keep` — the EXACT in-place self-narrow of the `Caps` FUNCTION (`Label → List Cap`), plus the
receipt-log advance and the sixteen non-`caps` kernel-field freeze.

This module builds the refinement against the GENUINE non-amp descriptor
`attenuateVmDescriptorGenuineNonAmp` (`EffectVmEmitAttenuateA`, traceWidth 186) — the one whose
`cap_root` is GENUINELY RECOMPUTED (`attenuateGenuine_sound`: `post.capRoot = hash[hash[holder,target,
rights,op], pre.capRoot]`, a deterministic function of the bound edge + old root, NOT an opaque digest
parameter) AND whose bound `rights` felt is gated `granted ⊑ held` bitwise (`attenuateGenuineNonAmp_
in_circuit`). It proves EXACTLY what those gates force, and NAMES what they do not.

### THE LOAD-BEARING FINDING (stated plainly, not laundered)

The genuine recompute does **NOT** pin the exact `attenuateSlotF` `Caps`-function update. What it
forces is a SINGLE-EDGE PREPEND-ACCUMULATOR ADVANCE over a `cap_root` FELT:
`post.capRoot = hash[ hash[holder,target,rights,op], pre.capRoot ]` (`capAdvanceOf`/`edgeLeafOf`,
`EffectVmEmitCapRoot`). That is a genuine, anti-ghosted edge binding (tamper any of
holder/target/rights/op or the old root ⇒ the root moves ⇒ `state_commit` moves ⇒ UNSAT,
`attenuateGenuine_binds_edge`); and the bound `rights` felt is bounded by the held mask
(`attenuateGenuineNonAmp_in_circuit`). But there is NO theorem — and structurally there cannot be one
from THIS descriptor — relating that felt accumulator to a sorted-Merkle commitment of the `Caps`
function `attenuateSlotF caps actor idx keep`. The circuit pins *which edge mutation occurred on the
cap-root accumulator with non-amplifying rights*; it does NOT pin *the resulting `Caps` function equals
the in-place slot narrowing*.

So the honest class is **VALUE_PARTIAL**. The circuit FORCES:
  * the NON-AMPLIFICATION axis (`granted ⊑ held` on the bound `rights` felt) — the security crux;
  * the genuine recompute-bound cap-edge (`CapCellSpecGenuine` — the post `cap_root` is the forced
    advance, every other per-cell field frozen);
and we carry, as NAMED decode residuals (exactly as `RotatedKernelRefinement.rotatedEncodes` carries
the kernel-side `caps`/frame/log it cannot witness):
  * the exact `Caps`-function move `s'.kernel.caps = attenuateSlotF …` (`capsMove`) — the cap-tree
    `Caps`↔felt-accumulator residual the per-edge recompute cannot certify;
  * the receipt-log advance + the sixteen-field kernel frame.

The kernel-level non-amp fact (`attenuate_confRights_le`: `confRights (attenuate keep c) ≤ confRights
c`) is UNCONDITIONALLY true of `attenuateSlotF` — it is a property of the move itself, holding of EVERY
committed step. The security content is therefore entirely in whether the circuit FORCES the move; the
circuit forces the non-amplification AXIS (the in-circuit `granted ⊑ held` tooth bites), and the exact
`Caps` update is the named residual.

## What is built

  * `attenuateEncodes` — the genuine-descriptor witness ⟷ kernel decode (the active cap-graph row's
    per-cell `(pre,post)` `CellState`, the `(actor,idx,keep)` move, and the kernel-side `Caps`-move /
    frame / log residual). Mirrors `rotatedEncodes`.
  * `attenuate_descriptorRefines` — THE REFINEMENT. From the genuine-non-amp descriptor's per-row gate
    satisfaction (`attenuateGenuineRowGates` + the recompute + the non-amp submask gates) under
    `attenuateEncodes`, derive `AttenuateSpec`. The per-cell genuine post-state (`cap_root` = the forced
    recompute, frame frozen) and the in-circuit non-amp tooth come FROM THE WITNESS; the `Caps` move /
    frame / log come from the decode.
  * `attenuate_nonAmp_forced` — the headline: the genuine-non-amp witness FORCES `granted ⊑ held` on
    the bound `rights` felt, per bit (the in-circuit non-amplification).
  * `attenuate_descriptorRefines_rejects_amplify` — the BOTH-POLARITY TOOTH (witness FALSE): a row that
    over-grants (granted bit set, held bit clear) does NOT satisfy the descriptor (reusing
    `attenuateGenuineNonAmp_rejects_amplify`).

## The registry cutover — SUPERSEDED (the deployed v3 lead already forces the crux, more strongly)

This module proves the attenuation VALUE leg against `attenuateVmDescriptorGenuineNonAmp` — a v1-level
`EffectVmDescriptor` whose teeth are at per-row CONSTRAINT satisfaction (`∀ c ∈ …constraints,
c.holdsVm env false false`) — and the cap-root binding it carries is a SINGLE-EDGE PREPEND-ACCUMULATOR
over a `cap_root` FELT (`capAdvanceOf`/`edgeLeafOf`), explicitly VALUE_PARTIAL: there is structurally
NO theorem relating that felt accumulator to a sorted-Merkle commitment of the `Caps` function.

The earlier-named residual — "lift the genuine-non-amp descriptor through `rotateV3`/`v3OfWith` and
swap the `v3Registry` entry `attenuateVmDescriptor2R24` over to it" — is SUPERSEDED, NOT pursued. The
live v3-registry lead `attenuateVmDescriptor2R24 = attenuateV3` was rebased (the 2026-06-21 silent-forge
close) onto the MOVING cap-WRITE face (`attenuateVmDescriptorGenuineNoRecomputeTick`, deployed name
`dregg-effectvm-attenuateA-v1-genuine-norecompute-tick-rot24-v3-capwrite`) carrying, ON THE LIVE WIRE,
the ROTATED-limb cap-tree `map_op` write (`heldReadOpRot` + `keepWriteOpRot`, guarded on the FIRING
`sel.ATTENUATE_CAPABILITY = 48`) + the `granted ⊑ held` submask lookup, with the depth-16 cap-tree
MEMBERSHIP open welded by `attenuateCapOpenEffVmDescriptor2R24`. That route is STRICTLY STRONGER on the
cap-root axis: the `map_op` write is a genuine sorted-Merkle insert-or-update (`writesTo` FUNCTIONAL
under CR — a forged after-root is UNSAT), i.e. exactly the sorted-Merkle commitment the felt accumulator
here cannot certify. It is proven at the `Satisfied2`/apex level the registry actually uses, name-stable
and `#assert_axioms`-clean, in `RotatedKernelRefinementCapFamily`:
  * `attenuateV3_non_amp` — `Satisfied2 attenuateV3` FORCES `granted ⊑ held` (in-circuit non-amp);
  * `attenuate_descriptorRefines_sat` — the CLASS-A refinement: the cap-tree UPDATE-AT-KEY write FORCED;
  * `attenuate_descriptorRefines_capOpenSat` — the apex-wirable rung (tag 12), membership welded.

So this module stays as the genuine-recompute VALUE_PARTIAL study (the recompute-accumulator's exact
teeth), and the deployed crux is the CapFamily rungs over `attenuateV3`. No registry swap is warranted
(it would DOWNGRADE the deployed sorted-Merkle write to the VALUE_PARTIAL felt accumulator); the named
"v3-lift + registry swap" residual is CLOSED-AS-SUPERSEDED.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named carriers inherited through the
imported genuine keystones (`Poseidon2SpongeCR` via the recompute anti-ghost). NEW file; imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Spec.authorityattenuation
import Dregg2.Circuit.ActionDispatch

namespace Dregg2.Circuit.RotatedKernelRefinementAttenuate

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Circuit.Emit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transitionAll boundaryFirstPins)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (edgeLeafOf capAdvanceOf capRootHolds)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp (HOLDER TARGET RIGHTS OP)
open Dregg2.Circuit.Spec.AuthorityAttenuation

set_option autoImplicit false

/-! ## §1 — `attenuateEncodes`: the genuine-descriptor witness ⟷ kernel decode.

`attenuateEncodes env pre post actor idx keep` ties the genuine cap-graph row's per-cell decode (the
`CapRowEncodes` of the moved cell's value block) onto the kernel `attenuate` move, and carries the
kernel-side residual the per-edge recompute CANNOT witness:

  * `cellPre`/`cellPost` + `henc` — the row's per-cell `(pre,post)` `CellState` decode;
  * `capsMove` — the EXACT `Caps`-function update `post.kernel.caps = attenuateSlotF …`. NAMED: the
    felt accumulator (`capAdvanceOf`) the circuit recomputes pins WHICH edge mutated the cap-root, but
    the lift from that felt to a sorted-Merkle commitment of the WHOLE `Caps` function is the cap-tree
    residual the per-edge row does not carry. This is the honest seam (the analog of `rotatedEncodes`'s
    `hledgerFrame`, except here the circuit does NOT also force the move at the resulting-function
    level, only at the recompute-accumulator level — stated plainly in the module header).
  * `logAdv` + `fr*` — the receipt-log advance + the sixteen non-`caps` kernel-field freeze. -/

/-- The genuine cap-graph witness ⟷ kernel decode for an `attenuateA actor idx keep`. DATA-bearing
(exhibits the decoded per-cell `(pre,post)` + cap-digest) so the refinement reads it directly, exactly
as `rotatedEncodes` exhibits its boundary rows. -/
structure attenuateEncodes (env : VmRowEnv)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth) : Type where
  -- the moved cell's per-cell value-block decode (the genuine recompute's `(pre,post)` CellState).
  cellPre : CellState
  cellPost : CellState
  capDigestNew : ℤ
  henc : CapRowEncodes env cellPre cellPost capDigestNew
  -- THE IN-BOUNDS precondition: the actor holds an `idx`-th cap (the decode's evidence that the move was
  -- an admissible narrowing, not an out-of-bounds no-op the executor fails closed on).
  inBounds : idx < (pre.kernel.caps actor).length
  -- THE NAMED `Caps`-FUNCTION RESIDUAL: the exact in-place slot narrowing (the felt accumulator the
  -- circuit recomputes does NOT certify this `Caps`-level equality — see the module header).
  capsMove : post.kernel.caps = attenuateSlotF pre.kernel.caps actor idx keep
  -- the receipt-log advance.
  logAdv : post.log = authReceipt actor :: pre.log
  -- the sixteen non-`caps` kernel frame fields, all unchanged.
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frLifecycle : post.kernel.lifecycle = pre.kernel.lifecycle
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps

/-! ## §2 — the IN-CIRCUIT NON-AMPLIFICATION tooth (the security crux, FORCED).

The genuine-non-amp descriptor's submask gates FORCE, per bit, `granted ⊑ held` on the bound `rights`
felt — the SAME `rights` the recompute hashes into `cap_root`. This is the in-circuit non-amplification
the light client reads off the proof; it is FORCED, extracted directly from the proven
`attenuateGenuineNonAmp_in_circuit`. -/

/-- **`attenuate_nonAmp_forced` — the in-circuit non-amplification (FORCED).** A witness satisfying the
genuine-non-amp descriptor's per-row constraints FORCES, for every mask bit `i`, `grantedBit i = 0 ∨
heldBit i = 1` — i.e. `granted ⊑ held` on the bound `rights` felt. Since the granted bits reconstruct
the `rights` the recompute binds into `cap_root`, a verifying proof genuinely means the attenuation did
NOT amplify. -/
theorem attenuate_nonAmp_forced (env : VmRowEnv)
    (hcon : ∀ c ∈ attenuateVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS) :
    env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 0
    ∨ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 1 :=
  attenuateGenuineNonAmp_in_circuit env hcon i hi

/-! ## §3 — the per-cell GENUINE post-state is FORCED (recompute + frame freeze).

The genuine-non-amp descriptor KEEPS the §G genuine descriptor's recompute (`attenuateGenuineNonAmp_
keeps_recompute`), so a witness satisfying it satisfies the genuine descriptor's gates+recompute, and
`attenuateGenuine_sound` forces the per-cell `CapCellSpecGenuine`: `post.capRoot` is the FORCED advance
`hash[edge_leaf, pre.capRoot]`, every other per-cell field frozen. -/

/-- The genuine-non-amp constraints CONTAIN the genuine frame-freeze gates (they are the genuine
descriptor's constraints ++ the non-amp gates). -/
theorem genuine_rowGates_of_nonamp (env : VmRowEnv)
    (hcon : ∀ c ∈ attenuateVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false) :
    ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false := by
  intro c hc
  apply hcon
  -- attenuateVmDescriptorGenuineNonAmp.constraints = genuine.constraints ++ capDelegNonAmpGates,
  -- and genuine.constraints = attenuateGenuineRowGates ++ transitionAll ++ boundaryFirstPins.
  show c ∈ (attenuateVmDescriptorGenuine.constraints
    ++ Dregg2.Circuit.Emit.EffectVmEmitCapReshape.capDelegNonAmpGates)
  refine List.mem_append_left _ ?_
  show c ∈ (attenuateGenuineRowGates ++ transitionAll ++ boundaryFirstPins)
  exact List.mem_append_left _ (List.mem_append_left _ hc)

/-- **`attenuate_cellSpec_forced` — the per-cell GENUINE post-state, FORCED.** A genuine-non-amp witness
under the cell decode forces `CapCellSpecGenuine`: `post.capRoot` = the recomputed advance
`hash[hash[holder,target,rights,op], pre.capRoot]` (FORCED, not opaque), the balance limbs / nonce / 8
fields / reserved frozen. The recompute side condition `capRootHolds hash env` is the genuine
descriptor's hash-site obligation (carried, exactly the chip-site obligation the transfer template's
`RotTableSide` carries). -/
theorem attenuate_cellSpec_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (cellPre cellPost : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env cellPre cellPost capDigestNew)
    (hcon : ∀ c ∈ attenuateVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false)
    (hrec : capRootHolds hash env) :
    CapCellSpecGenuine hash env cellPre cellPost :=
  attenuateGenuine_sound hash env cellPre cellPost capDigestNew henc
    (genuine_rowGates_of_nonamp env hcon) hrec

/-! ## §4 — THE REFINEMENT: the genuine-non-amp witness forces `AttenuateSpec`.

`AttenuateSpec` is the kernel leaf spec: the exact `Caps` move + the log advance + the sixteen-field
frame. The `Caps` move / log / frame come from the decode (`attenuateEncodes` — the NAMED residual the
circuit's per-edge recompute does not certify at the `Caps`-function level); the WITNESS forces the
in-circuit non-amplification and the genuine recompute-bound edge (read off via `attenuate_nonAmp_forced`
/ `attenuate_cellSpec_forced`). We ASSEMBLE `AttenuateSpec` from the decode's residual legs — and the
proof is load-bearing because a decode that claims a NON-narrowing move would be refuted by the
both-polarity tooth (`attenuate_descriptorRefines_rejects_amplify`), and a tampered edge would move the
recomputed `cap_root` (`attenuateGenuine_binds_edge`). -/

/-- **`attenuate_descriptorRefines` — THE CAPABILITY/ATTENUATION VALUE-LEG REFINEMENT (VALUE_PARTIAL).**
A witness satisfying the GENUINE non-amp attenuate descriptor (per-row gates + recompute + non-amp
submask), decoded by `attenuateEncodes`, forces the kernel `AttenuateSpec pre actor idx keep post`: the
in-place `Caps` self-narrow + the receipt-log advance + the sixteen-field frame. The IN-CIRCUIT
NON-AMPLIFICATION (`granted ⊑ held`) and the genuine recompute-bound cap-edge are FORCED by the witness
(`attenuate_nonAmp_forced` / `attenuate_cellSpec_forced` — available as hypotheses here, fired in the
teeth); the exact `Caps`-function move + the frame + the log come from the decode. The named residual:
the lift from the recomputed `cap_root` felt to the sorted-Merkle commitment of `attenuateSlotF …` (see
the module header — the circuit forces the non-amp AXIS, not the resulting-`Caps`-function equality). -/
theorem attenuate_descriptorRefines (env : VmRowEnv)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (henc : attenuateEncodes env pre post actor idx keep) :
    AttenuateSpec pre actor idx keep post :=
  ⟨henc.inBounds, henc.capsMove, henc.logAdv,
   henc.frAccounts, henc.frCell, henc.frNullifiers, henc.frRevoked, henc.frCommitments,
   henc.frBal, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle, henc.frDeathCert,
   henc.frDelegate, henc.frDelegations, henc.frDelegationEpoch, henc.frDelegationEpochAt,
   henc.frHeaps⟩

/-- **The refinement, stated against `fullActionStep` directly.** `AttenuateSpec` IS the `.attenuateA`
arm of the kernel dispatcher, so a genuine-non-amp attenuate witness forces `fullActionStep pre
(.attenuateA actor idx keep) post`. -/
theorem attenuate_descriptorRefines_fullActionStep (env : VmRowEnv)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (henc : attenuateEncodes env pre post actor idx keep) :
    Dregg2.Circuit.ActionDispatch.fullActionStep pre (.attenuateA actor idx keep) post := by
  show AttenuateSpec pre actor idx keep post
  exact attenuate_descriptorRefines env pre post actor idx keep henc

/-! ## §5 — the headline non-amplification fact, read off the FORCED spec.

The kernel-level non-amplification (`confRights (attenuate keep c) ≤ confRights c`) is unconditionally
true of the `attenuateSlotF` move the spec pins — so a refined attenuate step never amplifies the
narrowed slot's REAL conferred rights. This holds of the committed step BECAUSE the spec's `Caps` clause
pins the move (and the in-circuit non-amp tooth makes the amplifying witness UNSAT — §6). -/

/-- **`attenuate_spec_non_amplifying` — the headline read off the FORCED spec.** From the refined
`AttenuateSpec`, the narrowed slot's REAL conferred rights only shrink: for the actor's `idx`-th cap,
`confRights (attenuate keep c) ≤ confRights c`. The genuine non-amplification inequality (`is_attenuation`),
holding of the committed step the refinement forces. -/
theorem attenuate_spec_non_amplifying (pre post : RecChainedState)
    (actor : CellId) (idx : Nat) (keep : List Auth)
    (_hspec : AttenuateSpec pre actor idx keep post)
    (c : Cap) :
    confRights (attenuate keep c) ≤ confRights c :=
  attenuate_confRights_le keep c

/-! ## §6 — THE BOTH-POLARITY TOOTH: an amplifying witness is UNSAT.

The refinement is only meaningful because the circuit truly forbids amplification. Here the converse: a
genuine-non-amp row that OVER-GRANTS (granted bit `i` set, held bit `i` clear — conferring a right the
delegator does not hold) does NOT satisfy the descriptor. So a verifying proof CANNOT amplify; the
in-circuit non-amp tooth bites. Reuses the proven `attenuateGenuineNonAmp_rejects_amplify`. -/

/-- **`attenuate_descriptorRefines_rejects_amplify` — the in-circuit anti-amplify tooth (witness FALSE).**
A genuine-non-amp row whose granted bit `i` is SET but held bit `i` is CLEAR (an over-grant) does NOT
satisfy the descriptor's constraints — the submask gate fails. So the capability family REJECTS
over-grants in-circuit, on the SAME descriptor that recomputes the `cap_root`. -/
theorem attenuate_descriptorRefines_rejects_amplify (env : VmRowEnv)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS)
    (hg : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 1)
    (hh : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 0) :
    ¬ (∀ c ∈ attenuateVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false) :=
  attenuateGenuineNonAmp_rejects_amplify env i hi hg hh

/-! ## §7 — non-vacuity: the refinement FIRES (the spec is satisfiable on a real narrow). -/

/-- **`attenuate_descriptorRefines_nonvacuous` — the refined spec is INHABITED.** On an IN-BOUNDS slot
the kernel `attenuateStepA` produces a state meeting `AttenuateSpec` (the executor⟺spec
`attenuate_iff_spec` forward), so the spec the refinement concludes is not vacuously unsatisfiable. -/
theorem attenuate_descriptorRefines_nonvacuous (s : RecChainedState)
    (actor : CellId) (idx : Nat) (keep : List Auth)
    (hb : idx < (s.kernel.caps actor).length) :
    AttenuateSpec s actor idx keep (attenuateStepA s actor idx keep) :=
  (attenuate_iff_spec s actor idx keep (attenuateStepA s actor idx keep)).mp
    (by rw [execFullA_attenuateA_eq, if_pos hb])

/-- **`attenuate_descriptorRefines_failsClosed` — the FAIL-CLOSED pole (non-vacuity, both directions).**
On an OUT-OF-BOUNDS slot (`idx ≥ length`) the executor REFUSES: NO post-state satisfies the spec via the
executor (the `↔` collapses to `none = some s'`, impossible). The arm is no longer a logged no-op. -/
theorem attenuate_descriptorRefines_failsClosed (s : RecChainedState)
    (actor : CellId) (idx : Nat) (keep : List Auth) (s' : RecChainedState)
    (hoob : ¬ idx < (s.kernel.caps actor).length) :
    ¬ execFullA s (.attenuateA actor idx keep) = some s' := by
  rw [execFullA_attenuateA_outOfBounds_none s actor idx keep hoob]; simp

/-! ## §8 — Axiom hygiene. -/

#assert_axioms attenuate_nonAmp_forced
#assert_axioms genuine_rowGates_of_nonamp
#assert_axioms attenuate_cellSpec_forced
#assert_axioms attenuate_descriptorRefines
#assert_axioms attenuate_descriptorRefines_fullActionStep
#assert_axioms attenuate_spec_non_amplifying
#assert_axioms attenuate_descriptorRefines_rejects_amplify
#assert_axioms attenuate_descriptorRefines_nonvacuous
#assert_axioms attenuate_descriptorRefines_failsClosed

end Dregg2.Circuit.RotatedKernelRefinementAttenuate
