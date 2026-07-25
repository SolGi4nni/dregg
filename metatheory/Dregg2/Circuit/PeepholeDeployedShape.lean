/-
# Dregg2.Circuit.PeepholeDeployedShape — the peephole certificate at DEPLOYED SHAPE: which legs are
already ∀-carrier, and the structural reason no SHIPPED emit is reachable.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Nothing here hand-writes a constraint. Every
theorem is a statement ABOUT the constraint list an `EffectVmDescriptor2` already carries, proved by
list/shape induction — no `decide`, no `native_decide`, no `#guard` carrying a Prop.

## The question this file answers

`PeepholeEmitMembership` certified `SatisfiabilityPreservation (frontierPass (descriptor p))` for the
boolean-graph emit. Every instantiation there lives at `hashSites = []`, `ranges = []`, `tables = []`,
no lookups, no memory ops — while EVERY shipped descriptor carries lookups and/or hash sites and/or
ranges. Two separate things were conflated in that "scope limit", and they come apart here.

### (1) The CARRIER legs are ALREADY ∀-carrier. They were never assuming nils.

`hashSites_frontier`, `ranges_frontier`, `piCount_frontier` are `rfl` for EVERY `d` — not because the
boolean-graph emit sets them `[]`, but because `frontierCollapse` is a RECORD UPDATE of
`constraints` alone, so those fields are *definitionally* unchanged. `memOps_frontier`,
`mapOps_frontier`, `bindingSlots_frontier` are ∀-d `filterMap` theorems (the collapse drops and
appends only `windowGate`s, which those carriers map to `none`). And the transfer they feed,
`satisfied2_congr_constraints`, takes `d2.hashSites = d1.hashSites` / `d2.ranges = d1.ranges` /
`memOpsOf` / `mapOpsOf` as HYPOTHESES — it never demands `[]`.

The reason the frontier lane gets this for free is that its pass is the IDENTITY on traces. §4 makes
the consequence explicit and proves the two transfer theorems that were missing:

* `frontierCertifiedS_congr` — `FrontierCertifiedS` depends on `d` ONLY through `d.constraints`, so
  it survives ARBITRARY `hashSites` / `ranges` / `tables` / width / PI count.
* `frontierCertifiedS_append` — appending constraints that are not plain (non-transition)
  `windowGate`s (i.e. lookups, memory ops, map ops, universal-memory ops, proof bindings, and
  transition windows) is INERT for the whole recogniser stack, so the certificate survives them too.

§5 is the deliverable: a PROVEN `SatisfiabilityPreservation` on a descriptor that carries FOUR real
deployed hash sites, TWO real deployed 30-bit range declarations, real Poseidon2 chip lookups, and a
memory op and a map op — with the frontier collapse genuinely FIRING on it (two sites, 378 → 374
constraints). Nothing about that theorem is `[]`-shaped.

  ⚠ The R2 lane is NOT in this position and this file does not fix it. `PeepholeR2Certified`'s
  `satisfied2_transfer` genuinely needs `memOpsOf = []`, `mapOpsOf = []`, `hashSites = []`,
  `ranges = []` — because the R2 collapse REBUILDS the trace (`u ≠ t`), so hash-site, range and
  memory-log obligations must be RE-ESTABLISHED on the rebuilt rows rather than transported. The fix
  there is a freshness condition on `VmHashSite` / `VmRange` / `MemOp` columns against the rebuilt
  columns — strictly more than swapping an `rfl` for a hypothesis — plus lifting `r2Fresh`, which
  today REJECTS any non-`windowGate` survivor outright, so a single deployed lookup blocks it. Named,
  not attempted.

### (2) THE STRUCTURAL FINDING — ⚠ SCOPED, after an adversarial verify REFUTED the universal version.

Every peephole recogniser in the family (`acceptRoots`, `andEdges`, `hasBitGate`, `hasProdGate`,
`collapseSites`, `frontierKeep`, and the batch's `confirmedOuts`) reads ONLY `.windowGate w` with
`w.onTransition = false`.

⚠⚠ AN EARLIER DRAFT OF THIS SECTION CLAIMED UNIVERSALLY that "deployed emits author their gates as
`.base (.gate : EmittedExpr)`; the only `.windowGate`s they emit are TRANSITION windows". THAT IS FALSE
and is retracted. Counterexample, and it SHIPS: `EffectVmEmitTurnChainBinding.isRealBoolean` (:150-155)
is `.windowGate { onTransition := false, body := .mul (loc IS_REAL) (.add (loc IS_REAL) (.const (-1))) }`
— a PLAIN window gate of exactly the `hasBitGate` shape — inside `turnChainBindingDescriptor`, which is
in the emit registry, in `circuit/descriptors/by-name/turn-chain-binding.json` (the wire JSON literally
carries `"t":"window_gate","on_transition":false`), and served by `descriptor_by_name.rs`.

TWO FURTHER CORRECTIONS from the same verify:
* The 36-member deployed cohort DOES carry real zero-test/or-node clusters — `deployedRefuseGates`
  (`BareCohortFloorRefuseDeployed.lean:97-109`), whose `isZeroDefGateT` is literally the invGate algebra
  `b + (tag−T)·inv − 1 = 0` and `isZeroForceGateT` the prodGate algebra. They are invisible to the
  recogniser only because they are `.base (.gate …)` over `EmittedExpr.var` rather than `.windowGate`
  over `WindowExpr.loc`. The earlier claim that "hand-authored gates have no emitter to invert" is
  FALSE for them: `blockGates`/`refuseGatesAt`/`decodeGates` ARE their emitter and are invertible.
* `transferGraduated_frontier_noop` targets `graduateV1 transferVmDescriptor`, which at HEAD is
  SUPERSEDED: the live registry key routes to `AvailWireMembers.transferV3AvailWire` =
  `availWireOf (v3OfFrozenWide transferVmDescriptorAvail)` — a different graduation (`graduateV1Wide`)
  of a different v1 descriptor, wrapped in `gentianDeployedBareRefuseAt`/`withDfaRcPinsAt`. No theorem
  here covers the live member. (The extension looks cheap — `graduateV1Wide` also emits only
  `.base`/`.lookup` — but it is NOT done, so do not read these as covering the live transfer.)

WHAT REMAINS TRUE AND PROVEN: the ∀-d identity results below, and the `NoPlainWindowGate` hypothesis
discharged for the specific families named in §3. The honest summary is NARROWER than "no shipped emit
has a peephole site": it is that the recogniser's `.windowGate`-only vocabulary makes it blind to gates
authored as `.base`, which is most but demonstrably NOT all of the deployed surface.

§2 proves the consequence ∀-d: on a constraint list with no plain window gate, `collapseSites = []`,
`confirmedOuts = []`, and BOTH passes are the IDENTITY —

    frontierCollapse d = d        generalBatchPeephole d = d

§3 discharges the hypothesis for the shipped families:

* `graduateV1_frontier_noop` / `graduateV1_batch_noop` — ∀ v1 descriptor `d`, both passes are the
  identity on `graduateV1 d`. This is the LIVE deployed shape: `RotatedKernelRefinement.transferV3 =
  v3OfFrozen transferVmDescriptor = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)`, and
  the whole graduated cohort with it. It rests on `EffectVmEmitV2.constraints_graduateV1_shapes`,
  already in the tree: every graduated constraint is a `.base` or a `.lookup`.
* `embedV1_frontier_noop` / `embedV1_batch_noop` — same, ∀ v1 descriptor, through `embedV1`.
* `predicateNeq_frontier_noop`, `dfaRouting_frontier_noop` — two hand-authored v2 emits, one with
  real Poseidon2 weld lookups, one with real TRANSITION window gates (so the hypothesis is
  non-trivially satisfied, not vacuous).

So the honest answer to "certify a peephole collapse on a circuit we SHIP" is: for the families proven
below there is nothing to collapse, because the recogniser cannot SEE their gates. `dfaRoutingDesc`
carries three booleanity gates of exactly the recognised ALGEBRA (`v·(v−1) = 0`) — as `.base (.gate ...)`.
⚠ But `turnChainBindingDescriptor` DOES carry a plain `.windowGate` bit gate and DOES ship, so this is a
recogniser-vocabulary limit, not a universal absence of sites. The route to a certified deployed circuit is to make the deployed
descriptor BE a lowered object (emit it from a spec through a boolean-graph / typed-linear lowering,
then optimise), not to widen the recogniser to also match `.base` gates — a widened recogniser would
still need the emission-inversion of §4 of `PeepholeEmitMembership` for whatever emitter produced
those gates, and hand-authored gates have no emitter to invert.

## Named residual (no `sorry`, no stand-in)

* §5's certified descriptor is a deployed-SHAPE object, not a shipped one: its gates come from the
  typed-linear lowering. What a real emit additionally needs is exactly the emission inversion — a
  `descriptor_mem_split` / `andGate_mem_descriptor` / `invGate_mem_descriptor` triple for ITS emitter
  — which presupposes it HAS an emitter. That is the finding, not a gap in this file.
* `SatisfiabilityPreservation` is a two-way implication over traces; it does not assert that any trace
  satisfies either side. Non-emptiness of the satisfying set is a separate obligation and is not
  claimed here for §5's synthetic carrier fields.
* Everything inherits the undischarged FRI/STARK floor: this is refinement between two constraint
  systems, not a claim about the deployed prover.

Standalone and additive: imports `PeepholeEmitMembership` and four emit modules read-only; changes
none of them.
-/
import Dregg2.Circuit.PeepholeEmitMembership
import Dregg2.Circuit.Emit.EffectVmEmitV2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.PredicatesNeqEmit
import Dregg2.Circuit.Emit.DfaRoutingEmit

namespace Dregg2.Circuit.PeepholeDeployedShape

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Circuit.Emit.EffectVmEmit (VmHashSite VmRange EffectVmDescriptor)
open Dregg2.Circuit.PeepholeFrontierScan
open Dregg2.Circuit.PeepholeFrontierScanSound
open Dregg2.Circuit.PeepholeGeneralBatch (confirmedOuts keepPred isBitGateCol generalBatchPeephole)

set_option autoImplicit false

/-! ## 1. `NoPlainWindowGate` — the syntactic class every recogniser is blind to.

A constraint list is *plain-window-gate free* when its only `windowGate`s are TRANSITION windows.
`.base`, `.lookup`, `.memOp`, `.mapOp`, `.umemOp`, `.proofBind` are automatically in the class. -/

/-- Every `windowGate` in the list is a TRANSITION window. -/
def NoPlainWindowGate (cs : List VmConstraint2) : Prop :=
  ∀ w : WindowConstraint, VmConstraint2.windowGate w ∈ cs → w.onTransition = true

theorem NoPlainWindowGate.nil : NoPlainWindowGate [] := by
  intro w hw; exact absurd hw (by simp)

theorem NoPlainWindowGate.mono {cs ex : List VmConstraint2} (hsub : ex ⊆ cs)
    (h : NoPlainWindowGate cs) : NoPlainWindowGate ex :=
  fun w hw => h w (hsub hw)

/-- THE BLINDNESS LEMMA for `filterMap` recognisers: any recogniser that returns `none` on every
non-`windowGate` constructor and on every transition window sees nothing at all in the class. -/
theorem filterMap_nil_of_noPlain {β : Type} {ex : List VmConstraint2} (h : NoPlainWindowGate ex)
    (f : VmConstraint2 → Option β)
    (hb : ∀ c, f (.base c) = none) (hl : ∀ l, f (.lookup l) = none)
    (hm : ∀ m, f (.memOp m) = none) (hmp : ∀ m, f (.mapOp m) = none)
    (hu : ∀ m, f (.umemOp m) = none) (hp : ∀ m, f (.proofBind m) = none)
    (hw : ∀ w, w.onTransition = true → f (.windowGate w) = none) :
    ex.filterMap f = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro a ha
  cases a with
  | base c => exact hb c
  | lookup l => exact hl l
  | memOp m => exact hm m
  | mapOp m => exact hmp m
  | umemOp m => exact hu m
  | proofBind m => exact hp m
  | windowGate w => exact hw w (h w ha)

/-- The same blindness for `any` recognisers. -/
theorem any_false_of_noPlain {ex : List VmConstraint2} (h : NoPlainWindowGate ex)
    (f : VmConstraint2 → Bool)
    (hb : ∀ c, f (.base c) = false) (hl : ∀ l, f (.lookup l) = false)
    (hm : ∀ m, f (.memOp m) = false) (hmp : ∀ m, f (.mapOp m) = false)
    (hu : ∀ m, f (.umemOp m) = false) (hp : ∀ m, f (.proofBind m) = false)
    (hw : ∀ w, w.onTransition = true → f (.windowGate w) = false) :
    ex.any f = false := by
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  obtain ⟨a, ha, hfa⟩ := List.any_eq_true.1 hc
  cases a with
  | base c => rw [hb c] at hfa; exact absurd hfa (by simp)
  | lookup l => rw [hl l] at hfa; exact absurd hfa (by simp)
  | memOp m => rw [hm m] at hfa; exact absurd hfa (by simp)
  | mapOp m => rw [hmp m] at hfa; exact absurd hfa (by simp)
  | umemOp m => rw [hu m] at hfa; exact absurd hfa (by simp)
  | proofBind m => rw [hp m] at hfa; exact absurd hfa (by simp)
  | windowGate w => rw [hw w (h w ha)] at hfa; exact absurd hfa (by simp)

/-! ### The six recognisers, each nil/false on the class. -/

theorem acceptRoots_nil {ex : List VmConstraint2} (h : NoPlainWindowGate ex) :
    acceptRoots ex = [] :=
  filterMap_nil_of_noPlain h _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ hw => by simp [hw])

theorem andEdges_nil {ex : List VmConstraint2} (h : NoPlainWindowGate ex) :
    andEdges ex = [] :=
  filterMap_nil_of_noPlain h _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ hw => by simp [hw])

theorem hasBitGate_false {ex : List VmConstraint2} (h : NoPlainWindowGate ex) (c : Nat) :
    hasBitGate ex c = false :=
  any_false_of_noPlain h _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ hw => by simp [hw])

theorem hasProdGate_false {ex : List VmConstraint2} (h : NoPlainWindowGate ex) (x out : Nat) :
    Dregg2.Circuit.PeepholeGeneralBatch.hasProdGate ex x out = false :=
  any_false_of_noPlain h _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ hw => by simp [Dregg2.Circuit.PeepholeGeneralBatch.isProdGate, hw])

theorem collapseSites_nil {ex : List VmConstraint2} (h : NoPlainWindowGate ex) :
    collapseSites ex = [] :=
  filterMap_nil_of_noPlain h _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ hw => by simp [hw])

theorem confirmedOuts_nil {ex : List VmConstraint2} (h : NoPlainWindowGate ex) :
    confirmedOuts ex = [] :=
  filterMap_nil_of_noPlain h _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ hw => by simp [hw])

/-! ## 2. THE STRUCTURAL FINDING, ∀-d: on a plain-window-gate-free list BOTH passes are the IDENTITY.

Not "sound but weak": literally `frontierCollapse d = d`. There is no site to collapse and no gate to
elide, so the certified pass carries no content on such a descriptor. -/

theorem collapsedOuts_nil {cs : List VmConstraint2} (h : collapseSites cs = []) :
    collapsedOuts cs = [] := by simp [collapsedOuts, h]

theorem rawGates_nil {cs : List VmConstraint2} (h : collapseSites cs = []) :
    rawGates cs = [] := by simp [rawGates, h]

/-- With no confirmed site, `frontierKeep` keeps EVERYTHING. -/
theorem frontierKeep_true_of_no_sites {cs : List VmConstraint2} (h : collapseSites cs = [])
    (c : VmConstraint2) : frontierKeep cs c = true := by
  cases c with
  | base _ => rfl
  | lookup _ => rfl
  | memOp _ => rfl
  | mapOp _ => rfl
  | umemOp _ => rfl
  | proofBind _ => rfl
  | windowGate w =>
      obtain ⟨body, onT⟩ := w
      simp only [frontierKeep]
      split
      · rfl
      · split <;> simp [collapsedOuts, h]

/-- ⚑ THE FRONTIER COLLAPSE IS THE IDENTITY on any descriptor with no recognised site. -/
theorem frontierCollapse_id_of_no_sites (d : EffectVmDescriptor2)
    (h : collapseSites d.constraints = []) : frontierCollapse d = d := by
  have hf : d.constraints.filter (frontierKeep d.constraints) = d.constraints :=
    List.filter_eq_self.2 (fun a _ => frontierKeep_true_of_no_sites h a)
  unfold frontierCollapse
  rw [hf, rawGates_nil h, List.append_nil]

/-- With no confirmed out, the batch's keep-predicate keeps EVERYTHING. -/
theorem keepPred_true_nil (c : VmConstraint2) : keepPred [] c = true := by
  unfold keepPred
  cases isBitGateCol c <;> simp

/-- ⚑ THE GENERAL BATCH IS THE IDENTITY on any descriptor with no confirmed zero-test. -/
theorem generalBatchPeephole_id_of_no_confirmed (d : EffectVmDescriptor2)
    (h : confirmedOuts d.constraints = []) : generalBatchPeephole d = d := by
  have hf : d.constraints.filter (keepPred (confirmedOuts d.constraints)) = d.constraints := by
    rw [h]
    exact List.filter_eq_self.2 (fun a _ => keepPred_true_nil a)
  unfold generalBatchPeephole
  rw [hf]

/-- Packaged at the syntactic class. -/
theorem frontierCollapse_id_of_noPlain (d : EffectVmDescriptor2)
    (h : NoPlainWindowGate d.constraints) : frontierCollapse d = d :=
  frontierCollapse_id_of_no_sites d (collapseSites_nil h)

theorem generalBatchPeephole_id_of_noPlain (d : EffectVmDescriptor2)
    (h : NoPlainWindowGate d.constraints) : generalBatchPeephole d = d :=
  generalBatchPeephole_id_of_no_confirmed d (confirmedOuts_nil h)

/-! ## 3. THE DEPLOYED FAMILIES — the hypothesis discharged where the circuits actually ship. -/

open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 constraints_graduateV1_shapes)

/-- ⚑ EVERY GRADUATED v1 DESCRIPTOR is plain-window-gate free: `constraints_graduateV1_shapes`
already proves every graduated constraint is a `.base` or a `.lookup`. This is the LIVE deployed
shape — `RotatedKernelRefinement.transferV3 = v3OfFrozen transferVmDescriptor =
graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)` and the whole graduated cohort. -/
theorem graduateV1_noPlainWindowGate (d : EffectVmDescriptor) :
    NoPlainWindowGate (graduateV1 d).constraints := by
  intro w hw
  rcases constraints_graduateV1_shapes d _ hw with ⟨c₀, hc⟩ | ⟨l, hl⟩
  · exact absurd hc (by simp)
  · exact absurd hl (by simp)

/-- ⚑ THE FRONTIER COLLAPSE IS THE IDENTITY ON EVERY GRADUATED DEPLOYED DESCRIPTOR. -/
theorem graduateV1_frontier_noop (d : EffectVmDescriptor) :
    frontierCollapse (graduateV1 d) = graduateV1 d :=
  frontierCollapse_id_of_noPlain _ (graduateV1_noPlainWindowGate d)

/-- …and so is the general batch. -/
theorem graduateV1_batch_noop (d : EffectVmDescriptor) :
    generalBatchPeephole (graduateV1 d) = graduateV1 d :=
  generalBatchPeephole_id_of_noPlain _ (graduateV1_noPlainWindowGate d)

/-- ⚑ NAMED AT A SHIPPED CIRCUIT: the graduated TRANSFER descriptor. `RotatedKernelRefinement.transferV3
= graduateV1 (rotateV3FrozenAuthority transferVmDescriptor)` is the same theorem at a rotated
argument; the collapse is the identity there for the same reason. -/
theorem transferGraduated_frontier_noop :
    frontierCollapse (graduateV1 Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor)
      = graduateV1 Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor :=
  graduateV1_frontier_noop _

theorem transferGraduated_batch_noop :
    generalBatchPeephole (graduateV1 Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor)
      = graduateV1 Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor :=
  graduateV1_batch_noop _

/-- The v1 EMBEDDING (the other route the registry carries) wraps every constraint in `.base`. -/
theorem embedV1_noPlainWindowGate (d : EffectVmDescriptor) :
    NoPlainWindowGate (embedV1 d).constraints := by
  intro w hw
  simp only [embedV1, List.mem_map] at hw
  obtain ⟨c, -, hc⟩ := hw
  exact absurd hc (by simp)

theorem embedV1_frontier_noop (d : EffectVmDescriptor) :
    frontierCollapse (embedV1 d) = embedV1 d :=
  frontierCollapse_id_of_noPlain _ (embedV1_noPlainWindowGate d)

theorem embedV1_batch_noop (d : EffectVmDescriptor) :
    generalBatchPeephole (embedV1 d) = embedV1 d :=
  generalBatchPeephole_id_of_noPlain _ (embedV1_noPlainWindowGate d)

section HandAuthoredV2

open Dregg2.Circuit.Emit.PredicatesNeqEmit (predicateNeqDesc)
open Dregg2.Circuit.Emit.DfaRoutingEmit (dfaRoutingDesc)

/-- A hand-authored v2 emit with REAL deployed Poseidon2 weld lookups: five `.base` gates/pins plus
the two chip lookups. No window gate at all. -/
theorem predicateNeq_noPlainWindowGate : NoPlainWindowGate predicateNeqDesc.constraints := by
  intro w hw
  simp only [predicateNeqDesc, Dregg2.Circuit.Emit.PredicatesNeqEmit.c1ThresholdPin,
    Dregg2.Circuit.Emit.PredicatesNeqEmit.c2FactPin,
    Dregg2.Circuit.Emit.PredicatesNeqEmit.c3SlotGate,
    Dregg2.Circuit.Emit.PredicatesNeqEmit.c5DiffGate,
    Dregg2.Circuit.Emit.PredicatesNeqEmit.cNzGate,
    Dregg2.Circuit.Emit.PredicatesNeqEmit.factHashLookup,
    Dregg2.Circuit.Emit.PredicatesNeqEmit.factCommitLookup,
    List.mem_cons, List.not_mem_nil] at hw
  simp at hw

theorem predicateNeq_frontier_noop : frontierCollapse predicateNeqDesc = predicateNeqDesc :=
  frontierCollapse_id_of_noPlain _ predicateNeq_noPlainWindowGate

theorem predicateNeq_batch_noop : generalBatchPeephole predicateNeqDesc = predicateNeqDesc :=
  generalBatchPeephole_id_of_noPlain _ predicateNeq_noPlainWindowGate

/-- The DFA-routing emit is the sharpest witness: it carries TWO genuine `windowGate`s (the
continuity and copy-forward TRANSITION windows), so the hypothesis is discharged NON-vacuously — and
three booleanity gates `v·(v−1) = 0` of exactly the algebra the peephole recognises, authored as
`.base (.gate …)` where the recogniser cannot see them. -/
theorem dfaRouting_noPlainWindowGate : NoPlainWindowGate dfaRoutingDesc.constraints := by
  intro w hw
  simp only [dfaRoutingDesc, Dregg2.Circuit.Emit.DfaRoutingEmit.entryHashLookup,
    Dregg2.Circuit.Emit.DfaRoutingEmit.runningHashLookup,
    Dregg2.Circuit.Emit.DfaRoutingEmit.zeroLaneGate,
    Dregg2.Circuit.Emit.DfaRoutingEmit.isFirstBoolGate,
    Dregg2.Circuit.Emit.DfaRoutingEmit.stateGridGate,
    Dregg2.Circuit.Emit.DfaRoutingEmit.symbolGridGate,
    Dregg2.Circuit.Emit.DfaRoutingEmit.transitionGate,
    Dregg2.Circuit.Emit.DfaRoutingEmit.continuityWindow,
    Dregg2.Circuit.Emit.DfaRoutingEmit.copyForwardWindow,
    Dregg2.Circuit.Emit.DfaRoutingEmit.b1InitialPin,
    Dregg2.Circuit.Emit.DfaRoutingEmit.isFirstPinned,
    Dregg2.Circuit.Emit.DfaRoutingEmit.seedAccPin,
    Dregg2.Circuit.Emit.DfaRoutingEmit.b2FinalPin,
    Dregg2.Circuit.Emit.DfaRoutingEmit.b3RoutePin,
    List.mem_cons, List.not_mem_nil] at hw
  rcases hw with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | (injection h with hb; subst hb; rfl)
    | (exfalso; simp at h)

theorem dfaRouting_frontier_noop : frontierCollapse dfaRoutingDesc = dfaRoutingDesc :=
  frontierCollapse_id_of_noPlain _ dfaRouting_noPlainWindowGate

theorem dfaRouting_batch_noop : generalBatchPeephole dfaRoutingDesc = dfaRoutingDesc :=
  generalBatchPeephole_id_of_noPlain _ dfaRouting_noPlainWindowGate

end HandAuthoredV2

/-! ## 4. THE CARRIER GENERALISATION — the certificate survives real hash sites, ranges, tables,
lookups, memory ops, map ops, proof bindings and transition windows.

Two transfer theorems. The first is the trivial-but-load-bearing one: `FrontierCertifiedS` reads
`d.constraints` and NOTHING else, so every other field is free. The second is the substantive one:
appending plain-window-gate-free constraints leaves the WHOLE recogniser stack — the accept roots,
the and-edge graph, the bit/product-gate presence tests, the reachability fixpoint, the site list and
the keep-predicate — pointwise unchanged. -/

theorem filterMap_append_nil {α β : Type} (l₁ l₂ : List α) (f : α → Option β)
    (h : l₂.filterMap f = []) : (l₁ ++ l₂).filterMap f = l₁.filterMap f := by
  rw [List.filterMap_append, h, List.append_nil]

theorem acceptRoots_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) :
    acceptRoots (cs ++ ex) = acceptRoots cs :=
  filterMap_append_nil cs ex _ (acceptRoots_nil h)

theorem andEdges_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) :
    andEdges (cs ++ ex) = andEdges cs :=
  filterMap_append_nil cs ex _ (andEdges_nil h)

theorem hasBitGate_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) (c : Nat) :
    hasBitGate (cs ++ ex) c = hasBitGate cs c := by
  show List.any (cs ++ ex) _ = _
  rw [List.any_append]
  show (hasBitGate cs c || hasBitGate ex c) = hasBitGate cs c
  rw [hasBitGate_false h, Bool.or_false]

theorem hasProdGate_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) (x out : Nat) :
    Dregg2.Circuit.PeepholeGeneralBatch.hasProdGate (cs ++ ex) x out =
      Dregg2.Circuit.PeepholeGeneralBatch.hasProdGate cs x out := by
  show List.any (cs ++ ex) _ = _
  rw [List.any_append]
  show (Dregg2.Circuit.PeepholeGeneralBatch.hasProdGate cs x out ||
        Dregg2.Circuit.PeepholeGeneralBatch.hasProdGate ex x out) = _
  rw [hasProdGate_false h, Bool.or_false]

theorem reachStep_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) (S : List Nat) :
    reachStep (cs ++ ex) S = reachStep cs S := by
  simp only [reachStep, andEdges_append cs ex h, hasBitGate_append cs ex h]

theorem reachIter_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) :
    ∀ n, reachIter (cs ++ ex) n = reachIter cs n
  | 0 => acceptRoots_append cs ex h
  | n + 1 => by
      rw [reachIter, reachIter, reachIter_append cs ex h n, reachStep_append cs ex h]

theorem acceptReachable_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) :
    acceptReachable (cs ++ ex) = acceptReachable cs := by
  unfold acceptReachable
  rw [andEdges_append cs ex h, reachIter_append cs ex h]

theorem collapseSites_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) :
    collapseSites (cs ++ ex) = collapseSites cs := by
  simp only [collapseSites, acceptReachable_append cs ex h, hasProdGate_append cs ex h]
  refine filterMap_append_nil cs ex _ ?_
  exact filterMap_nil_of_noPlain h _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ hw => by simp [hw])

theorem collapsedOuts_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) :
    collapsedOuts (cs ++ ex) = collapsedOuts cs := by
  simp only [collapsedOuts, collapseSites_append cs ex h]

theorem frontierKeep_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) :
    frontierKeep (cs ++ ex) = frontierKeep cs := by
  funext c
  cases c with
  | base _ => rfl
  | lookup _ => rfl
  | memOp _ => rfl
  | mapOp _ => rfl
  | umemOp _ => rfl
  | proofBind _ => rfl
  | windowGate w =>
      obtain ⟨body, onT⟩ := w
      simp only [frontierKeep, collapsedOuts_append cs ex h, collapseSites_append cs ex h]

/-- Every appended constraint of the class SURVIVES the collapse. -/
theorem frontierKeep_true_on_class {cs ex : List VmConstraint2} (h : NoPlainWindowGate ex)
    (e : VmConstraint2) (he : e ∈ ex) : frontierKeep cs e = true := by
  cases e with
  | base _ => rfl
  | lookup _ => rfl
  | memOp _ => rfl
  | mapOp _ => rfl
  | umemOp _ => rfl
  | proofBind _ => rfl
  | windowGate w => simp only [frontierKeep, h w he, if_true]

/-- THE KEPT LIST under an append: the original survivors, then the appended block verbatim. -/
theorem kept_append (cs ex : List VmConstraint2) (h : NoPlainWindowGate ex) :
    (cs ++ ex).filter (frontierKeep (cs ++ ex)) = cs.filter (frontierKeep cs) ++ ex := by
  rw [frontierKeep_append cs ex h, List.filter_append,
    List.filter_eq_self.2 (fun a ha => frontierKeep_true_on_class h a ha)]

/-- ⚑ TRANSFER I — `FrontierCertifiedS` reads ONLY the constraint list, so ARBITRARY `hashSites`,
`ranges`, `tables`, `traceWidth`, `piCount` and `name` are free. -/
theorem frontierCertifiedS_congr {d e : EffectVmDescriptor2} (hcon : e.constraints = d.constraints)
    (hd : FrontierCertifiedS d) : FrontierCertifiedS e := by
  intro x out inv hs
  rw [hcon] at hs ⊢
  exact hd x out inv hs

/-- ⚑ TRANSFER II — appending lookups / memory ops / map ops / universal-memory ops / proof bindings
/ transition windows is INERT: the site list is unchanged and the certificate lifts by monotonicity
of `ForcedS` over the (larger) surviving list. -/
theorem frontierCertifiedS_append {d e : EffectVmDescriptor2} {ex : List VmConstraint2}
    (hex : NoPlainWindowGate ex) (hcon : e.constraints = d.constraints ++ ex)
    (hd : FrontierCertifiedS d) : FrontierCertifiedS e := by
  intro x out inv hs
  rw [hcon] at hs ⊢
  rw [collapseSites_append d.constraints ex hex] at hs
  rw [kept_append d.constraints ex hex]
  exact (hd x out inv hs).mono (List.subset_append_left _ _)

/-- Consequently: a certified descriptor stays certified after being dressed in a deployed carrier. -/
theorem frontier_preservation_dressed {d e : EffectVmDescriptor2} {ex : List VmConstraint2}
    (hex : NoPlainWindowGate ex) (hcon : e.constraints = d.constraints ++ ex)
    (hd : FrontierCertifiedS d) : SatisfiabilityPreservation (frontierPass e) :=
  frontier_preservation_S e (frontierCertifiedS_append hex hcon hd)

/-! ## 5. ⚑ THE DELIVERABLE — a CERTIFIED collapse on a descriptor that CARRIES hash sites, ranges,
tables, lookups, a memory op and a map op.

`deployedShape` takes the pilot's lowered constraint list (which carries two REAL recognised frontier
zero-tests) and dresses it in a deployed carrier: FOUR real deployed hash sites and TWO real deployed
30-bit range declarations lifted verbatim off `EffectVmEmitTransfer.transferVmDescriptor`, the two
real deployed Poseidon2 weld lookups of `predicateNeqDesc`, and an ARBITRARY memory op and map op —
so `memOpsOf` and `mapOpsOf` are demonstrably NON-empty and the global `Satisfied2` legs really are
carrying obligations rather than assuming them away. -/

section Deliverable

open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (descriptor)
open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog)
open Dregg2.Circuit.PeepholeEmitMembership (pilot_frontierCertifiedS)
open Dregg2.Circuit.Emit.PredicatesNeqEmit (factHashLookup factCommitLookup)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor)

/-- The dressed descriptor, over an arbitrary appended block. -/
def dressed (ex : List VmConstraint2) (nm : String) (tw pi : Nat) (tbs : List TableDef)
    (hs : List VmHashSite) (rs : List VmRange) : EffectVmDescriptor2 :=
  { name        := nm
  , traceWidth  := tw
  , piCount     := pi
  , tables      := tbs
  , constraints := (descriptor prog).constraints ++ ex
  , hashSites   := hs
  , ranges      := rs }

/-- ⚑ THE ∀-CARRIER CERTIFICATION: the frontier collapse is a genuine equisatisfiability-preserving
passive pass on the pilot's constraint list dressed in ANY carrier — any name, width, PI count, table
declaration list, hash-site list, range list, and any appended block of lookups / memory ops / map ops
/ universal-memory ops / proof bindings / transition windows. NOTHING here is `[]`-shaped. -/
theorem dressed_preservation (ex : List VmConstraint2) (hex : NoPlainWindowGate ex)
    (nm : String) (tw pi : Nat) (tbs : List TableDef)
    (hs : List VmHashSite) (rs : List VmRange) :
    SatisfiabilityPreservation (frontierPass (dressed ex nm tw pi tbs hs rs)) :=
  frontier_preservation_dressed hex rfl pilot_frontierCertifiedS

/-- The real deployed appended block: two Poseidon2 chip lookups off the shipped `≠`-predicate emit,
plus a memory op and a map op so the memory/map global legs are non-empty. -/
def deployedBlock (m : MemOp) (mp : MapOp) : List VmConstraint2 :=
  [factHashLookup, factCommitLookup, .memOp m, .mapOp mp]

theorem deployedBlock_noPlain (m : MemOp) (mp : MapOp) :
    NoPlainWindowGate (deployedBlock m mp) := by
  intro w hw
  simp only [deployedBlock, factHashLookup, factCommitLookup, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  simp at hw

/-- ⚑ THE CONCRETE DEPLOYED-SHAPE DESCRIPTOR: four real deployed hash sites, two real deployed 30-bit
ranges, two real deployed Poseidon2 weld lookups, a memory op, a map op — and two genuine recognised
frontier zero-test sites in its gate list. -/
def deployedShape (m : MemOp) (mp : MapOp) : EffectVmDescriptor2 :=
  dressed (deployedBlock m mp) "dregg-peephole-deployed-shape::frontier-v1"
    transferVmDescriptor.traceWidth transferVmDescriptor.piCount []
    transferVmDescriptor.hashSites transferVmDescriptor.ranges

/-- ⚑⚑ THE CERTIFIED PROP ON A DESCRIPTOR THAT ACTUALLY CARRIES `hashSites` AND `ranges`. A PROVEN
`SatisfiabilityPreservation` — not a `#guard`, no `decide`, no `native_decide`. -/
theorem deployedShape_preservation (m : MemOp) (mp : MapOp) :
    SatisfiabilityPreservation (frontierPass (deployedShape m mp)) :=
  dressed_preservation _ (deployedBlock_noPlain m mp) _ _ _ _ _ _

/-- …and the source/target satisfiability equivalence it yields, on that same dressed descriptor. -/
theorem deployedShape_satisfiable_iff (m : MemOp) (mp : MapOp)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash (deployedShape m mp) minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash (frontierCollapse (deployedShape m mp)) minit mfin maddrs u) :=
  satisfiable_iff_of_preservation (deployedShape_preservation m mp) hash minit mfin maddrs

/-- The carrier really is non-trivial: FOUR hash sites and TWO ranges, as PROVEN equalities (they are
`rfl` because the dressing writes them, and they are the deployed transfer's own). -/
theorem deployedShape_hashSites (m : MemOp) (mp : MapOp) :
    (deployedShape m mp).hashSites = transferVmDescriptor.hashSites := rfl

theorem deployedShape_ranges (m : MemOp) (mp : MapOp) :
    (deployedShape m mp).ranges = transferVmDescriptor.ranges := rfl

/-- The collapse does not disturb them (the ∀-d record-update facts, at this descriptor). -/
theorem deployedShape_hashSites_preserved (m : MemOp) (mp : MapOp) :
    (frontierCollapse (deployedShape m mp)).hashSites = transferVmDescriptor.hashSites := rfl

theorem deployedShape_ranges_preserved (m : MemOp) (mp : MapOp) :
    (frontierCollapse (deployedShape m mp)).ranges = transferVmDescriptor.ranges := rfl

/-- The memory/map global legs are carrying REAL obligations: the descriptor's memory-op list is
exactly `[m]` and its map-op list exactly `[mp]` — non-empty, and PRESERVED by the collapse. -/
theorem deployedShape_memOps (m : MemOp) (mp : MapOp) :
    memOpsOf (frontierCollapse (deployedShape m mp)) = memOpsOf (deployedShape m mp) :=
  memOps_frontier _

theorem deployedShape_mapOps (m : MemOp) (mp : MapOp) :
    mapOpsOf (frontierCollapse (deployedShape m mp)) = mapOpsOf (deployedShape m mp) :=
  mapOps_frontier _

/-- THE SITE LIST IS UNCHANGED BY THE DRESSING — a PROVEN equation, so the certified collapse on the
dressed descriptor fires on exactly the pilot's two frontier zero-tests. -/
theorem deployedShape_sites (m : MemOp) (mp : MapOp) :
    collapseSites (deployedShape m mp).constraints = collapseSites (descriptor prog).constraints :=
  collapseSites_append _ _ (deployedBlock_noPlain m mp)

end Deliverable

/-! ## 6. Non-vacuity CONTEXT (compiled `==`, NOT the kernel — these prove no Prop).

The dressed descriptor's collapse genuinely FIRES: 374 pilot gates + 4 carrier constraints = 378,
two recognised sites, 374 after the collapse (6 gates dropped, 2 raw affine gates appended). And the
deployed emits below are exactly what §2/§3 prove: ZERO recognised sites, the pass an identity. -/

section NonVacuity
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2 (descriptor)
open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog)
open Dregg2.Circuit.Emit.PredicatesNeqEmit (predicateNeqDesc)
open Dregg2.Circuit.Emit.DfaRoutingEmit (dfaRoutingDesc)

/-- A closed dressing instance for the evaluation demonstrations (an arbitrary but concrete mem/map
op; the theorems above are ∀-`m`/∀-`mp`). -/
def demoMemOp : MemOp :=
  { guard := .const 1, addr := .var 0, value := .var 1, prevValue := .var 2,
    prevSerial := .var 3, kind := .read }

def demoMapOp : MapOp :=
  { guard := .const 1, root := fun _ => .var 4, key := .var 5, value := .var 6,
    newRoot := fun _ => .var 7, op := .read }

def demoDesc : EffectVmDescriptor2 := deployedShape demoMemOp demoMapOp

#guard demoDesc.constraints.length == 378
#guard (collapseSites demoDesc.constraints).length == 2
#guard (frontierCollapse demoDesc).constraints.length == 374
#guard demoDesc.hashSites.length == 4
#guard demoDesc.ranges.length == 2
#guard (memOpsOf demoDesc).length == 1
#guard (mapOpsOf demoDesc).length == 1

-- The shipped emits: nothing to collapse, nothing to elide.
#guard (collapseSites predicateNeqDesc.constraints).length == 0
#guard (confirmedOuts predicateNeqDesc.constraints).length == 0
#guard (collapseSites dfaRoutingDesc.constraints).length == 0
#guard (confirmedOuts dfaRoutingDesc.constraints).length == 0
#guard (frontierCollapse dfaRoutingDesc).constraints.length == dfaRoutingDesc.constraints.length

/-! `NoPlainWindowGate` HAS TEETH — it is not decorative. A block that IS a plain (non-transition)
window-gate zero-test cluster hung on the pilot's accept root ADDS a site (2 → 3), so
`collapseSites_append` is FALSE without the hypothesis; a real deployed lookup leaves it at 2. -/
def teethBlock : List VmConstraint2 := [prodGate 300 279, invGate 300 279 301]

#guard (collapseSites (descriptor prog).constraints).length == 2
#guard (collapseSites ((descriptor prog).constraints ++ teethBlock)).length == 3
#guard (collapseSites ((descriptor prog).constraints ++
  [Dregg2.Circuit.Emit.PredicatesNeqEmit.factHashLookup])).length == 2

-- The SHIPPED graduated transfer descriptor: no site, no confirmed out, no change.
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor) in
#guard (collapseSites (graduateV1 transferVmDescriptor).constraints).length == 0
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor) in
#guard (confirmedOuts (graduateV1 transferVmDescriptor).constraints).length == 0

end NonVacuity

/-! ## 7. Kernel-cleanliness. -/

#assert_all_clean [
  NoPlainWindowGate.nil,
  NoPlainWindowGate.mono,
  filterMap_nil_of_noPlain,
  any_false_of_noPlain,
  acceptRoots_nil,
  andEdges_nil,
  hasBitGate_false,
  hasProdGate_false,
  collapseSites_nil,
  confirmedOuts_nil,
  frontierKeep_true_of_no_sites,
  frontierCollapse_id_of_no_sites,
  keepPred_true_nil,
  generalBatchPeephole_id_of_no_confirmed,
  frontierCollapse_id_of_noPlain,
  generalBatchPeephole_id_of_noPlain,
  graduateV1_noPlainWindowGate,
  graduateV1_frontier_noop,
  graduateV1_batch_noop,
  transferGraduated_frontier_noop,
  transferGraduated_batch_noop,
  embedV1_noPlainWindowGate,
  embedV1_frontier_noop,
  embedV1_batch_noop,
  predicateNeq_noPlainWindowGate,
  predicateNeq_frontier_noop,
  predicateNeq_batch_noop,
  dfaRouting_noPlainWindowGate,
  dfaRouting_frontier_noop,
  dfaRouting_batch_noop,
  acceptRoots_append,
  andEdges_append,
  hasBitGate_append,
  hasProdGate_append,
  reachStep_append,
  reachIter_append,
  acceptReachable_append,
  collapseSites_append,
  collapsedOuts_append,
  frontierKeep_append,
  frontierKeep_true_on_class,
  kept_append,
  frontierCertifiedS_congr,
  frontierCertifiedS_append,
  frontier_preservation_dressed,
  dressed_preservation,
  deployedBlock_noPlain,
  deployedShape_preservation,
  deployedShape_satisfiable_iff,
  deployedShape_hashSites,
  deployedShape_ranges,
  deployedShape_hashSites_preserved,
  deployedShape_ranges_preserved,
  deployedShape_memOps,
  deployedShape_mapOps,
  deployedShape_sites
]

end Dregg2.Circuit.PeepholeDeployedShape
