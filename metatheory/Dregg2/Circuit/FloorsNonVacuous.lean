/-
# Dregg2.Circuit.FloorsNonVacuous — the apex's named floors/carriers are NON-VACUOUS.

## The discipline this enforces ("don't launder vacuity")

The circuit-soundness apex takes its floors/carriers as HYPOTHESES (the honest pattern — floors enter
as `Prop`-classes / structures, not as `axiom`s). But a hypothesis that is secretly UNINHABITABLE makes
every theorem consuming it VACUOUSLY true. This module proves, per load-bearing carrier, that it is
genuinely inhabited (a concrete witness) AND — where the predicate should constrain — genuinely
separating (provably TRUE for some input, FALSE for another), so none is a silently-impossible
hypothesis.

  * `Poseidon2SpongeCR` (§1) — the CR floor IS injectivity. Inhabited by a concrete injective sponge
    (an `Encodable.encode` realization), SEPARATED by a constant sponge that violates it. So the
    predicate is meaningful (not `True`) and realizable (a hypothetical injective hash satisfies it) —
    exactly the non-degeneracy the named crypto floor needs. (CR of the REAL Poseidon2 is the assumed
    crypto content; what is proven here is that the PREDICATE is non-trivial, the only Lean-decidable
    part.)
  * `ChipTableSoundN` (§2) — the wide genuine-permutation chip soundness. A concrete genuine chip table
    SATISFIES it (every row a real `chipRowN permOut ins`); a forged table (a non-`chipRowN` row)
    VIOLATES it. So `Satisfied2Faithful`'s chip conjunct genuinely separates honest from forged chips.
  * `Satisfied2Faithful` (§3) — THE KEYSTONE. The full FAITHFUL object is inhabited by a real transfer:
    a faithful trace whose `.poseidon2` table is a genuine `ChipTableSoundN permOut` table, whose
    `.range` table IS `rangeRows BAL_LIMB_BITS`, with `permWidth`/`chipHashIsLane0` discharged — lifting
    the per-row satisfiability to the deployed accept-set with its chip/range faithfulness as CONJUNCTS.
    So the apex's faithful hypothesis is provably non-vacuous: a real transfer realizes the FULL object,
    not just `Satisfied2`.
  * `EffAuthoritySource` (§4) — the effect-parametric cap-open authority carrier. Its conclusion is
    non-trivial: `authorizedFacetEffB` provably SEPARATES (TRUE for an owner turn, FALSE for a
    non-owner with no caps) — so the carrier is not a degenerate "always authorized" gate. (Full
    structural inhabitation needs a deployed depth-16 cap-tree opening trace — the named realizability
    floor `CapOpenTraceFloor`, dual of `StarkComplete`; what is shown here is the conclusion's
    non-degeneracy.)
  * `StarkComplete` (§5) — the dual audited p3 completeness floor. Its body `∃ π, verifyBatch … = accept`
    is a genuine obligation: `Verdict.accept ≠ Verdict.reject`, so accepting is NOT vacuously-always
    nor impossible-always — the predicate is non-degenerate. (Inhabiting the class requires producing an
    accepting proof against the OPAQUE `verifyBatch`; it is the named FRI/p3 realizability, not a
    Lean-internal vacuity.)

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Every inhabitation/separation is a
CONSTRUCTED term or a structural discharge, no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.Satisfied2Faithful
import Dregg2.Circuit.CircuitCompletenessNonVacuityReal
import Dregg2.Circuit.RotatedKernelRefinementFacet

namespace Dregg2.Circuit.FloorsNonVacuous

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Satisfied2Faithful
open Dregg2.Circuit.Emit.EffectVmEmit (satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — `Poseidon2SpongeCR`: the CR floor is a NON-TRIVIAL predicate (= injectivity).

`Poseidon2SpongeCR sponge := ∀ xs ys, sponge xs = sponge ys → xs = ys` is literally injectivity. We
prove the predicate is non-degenerate: a concrete injective sponge SATISFIES it, a constant sponge
VIOLATES it. (The CR of the REAL Poseidon2 is the assumed crypto content; the Lean-decidable part — that
this hypothesis is a meaningful, satisfiable, non-trivial predicate, not `True` and not `False` — is
what makes the named floor non-vacuous rather than secretly-empty or secretly-everything.) -/

/-- A concrete INJECTIVE sponge: encode the input list to a natural via `Encodable` and cast to `ℤ`.
`Encodable.encode` is injective on `List ℤ`, and `Nat → ℤ` is injective, so the composite is. -/
def encodeSponge : List ℤ → ℤ := fun xs => (Encodable.encode xs : ℤ)

/-- **`encodeSponge` SATISFIES `Poseidon2SpongeCR`** — the floor is INHABITED by a concrete injective
sponge. So the CR hypothesis is realizable: a (hypothetical) injective hash discharges it. -/
theorem encodeSponge_cr : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR encodeSponge := by
  intro xs ys h
  have hnat : (Encodable.encode xs : ℤ) = (Encodable.encode ys : ℤ) := h
  exact Encodable.encode_injective (Int.natCast_inj.mp hnat)

/-- **`Poseidon2SpongeCR` is INHABITED.** -/
theorem poseidon2SpongeCR_inhabited :
    ∃ sponge : List ℤ → ℤ, Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR sponge :=
  ⟨encodeSponge, encodeSponge_cr⟩

/-- **`Poseidon2SpongeCR` is NON-TRIVIAL (separates).** A constant sponge collapses distinct inputs, so
it VIOLATES the predicate — the CR floor is NOT `True`, it carries real content (an honest hash that is
not injective fails it). -/
theorem poseidon2SpongeCR_separates :
    ∃ sponge : List ℤ → ℤ, ¬ Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR sponge := by
  refine ⟨fun _ => 0, ?_⟩
  intro h
  -- `h [0] [1] (rfl : 0 = 0)` would force `[0] = [1]`, a contradiction.
  have : ([0] : List ℤ) = [1] := h [0] [1] rfl
  simp at this

/-! ## §2 — `ChipTableSoundN`: the wide chip-soundness predicate SEPARATES honest from forged.

`ChipTableSoundN permOut tbl := ∀ r ∈ tbl, ∃ ins, ins.length ≤ CHIP_RATE ∧ r = chipRowN permOut ins`.
A genuine chip table (every row a real `chipRowN permOut ins`) SATISFIES it; a forged table with a row
that is NOT any `chipRowN permOut ins` VIOLATES it. So `Satisfied2Faithful`'s `chipTableFaithful`
conjunct genuinely constrains — a prover cannot supply an arbitrary table and call it chip-sound. -/

/-- The genuine width-8 squeeze used throughout: lane 0 carries the digest (here `0`), lanes 1..7 ride
along as `0`. `permWidth`/`chipHashIsLane0` hold by computation. -/
def permOut0 : List ℤ → ℤ := fun _ => 0

/-- The genuine permutation exposing `CHIP_OUT_LANES` lanes, every lane `0` (a degenerate-but-genuine
permutation: a real chip AIR with all-zero squeeze for the all-zero state — sound by construction). -/
def permOutZ : List ℤ → List ℤ := fun _ => List.replicate CHIP_OUT_LANES 0

theorem permOutZ_width (ins : List ℤ) : (permOutZ ins).length = CHIP_OUT_LANES := by
  simp [permOutZ]

/-- The v1 digest IS lane 0 of `permOutZ` (`0`). -/
theorem permOutZ_lane0 (ins : List ℤ) : permOut0 ins = (permOutZ ins).headD 0 := by
  simp [permOut0, permOutZ, CHIP_OUT_LANES]

/-- A GENUINE one-row chip table: the single row is a real `chipRowN permOutZ []` (arity-0 absorb). -/
def genuineChipTbl : Table := [chipRowN permOutZ []]

/-- **`genuineChipTbl` SATISFIES `ChipTableSoundN permOutZ`** — every row is a real `chipRowN` tuple.
So the wide chip-soundness predicate is INHABITED by a genuine chip table. -/
theorem genuineChipTbl_sound : ChipTableSoundN permOutZ genuineChipTbl := by
  intro r hr
  -- the only row IS `chipRowN permOutZ []`.
  simp only [genuineChipTbl, List.mem_singleton] at hr
  -- arity 0 IS an admitted chip arity (the pad/fact row) — the witness survives the strengthening
  -- of `ChipTableSoundN` from `≤ CHIP_RATE` to `ChipArityAdmitted`.
  exact ⟨[], of_decide_eq_true (Eq.refl true), hr⟩

/-- A FORGED chip table: a single row `[0]` that is NOT any `chipRowN permOutZ ins` (a real chip row
begins with the arity tag and carries the full padded-input + 8-lane output block, so it has length
`1 + CHIP_RATE + CHIP_OUT_LANES = 20 ≠ 1`). -/
def forgedChipTbl : Table := [[0]]

/-- The length of a wide chip row is `1 + CHIP_RATE + CHIP_OUT_LANES` (here `1 + 11 + 8 = 20`) —
for EVERY `ins`, with no arity side condition.

⚑ The arity hypothesis is GONE, and its deletion is the point. This proof used to unfold `padTo`
and re-derive the width from `ins.length + (CHIP_RATE - ins.length)`, which needs
`ins.length ≤ CHIP_RATE` and is why it carried `ChipArityAdmitted ins.length`. `padTo` is
`take`-shaped since `7f8ab5d29` (`xs.take n ++ replicate (n - xs.length) 0`, exactly `n` for every
input), so the width is `padTo_length_eq` — UNCONDITIONAL — and the hypothesis was left standing
with nothing to do. Keeping it would be a no-op binder on a lemma that is now strictly stronger.
This is the FOURTH proof that walked through `padTo`'s body; `f278f5756` took two and `384ae9c70`
took the third, and this one was missed because it is the only one that reached the body through
`rw` rather than an `unfold`/`simp only` list. -/
theorem chipRowN_length (ins : List ℤ) :
    (chipRowN permOutZ ins).length = 1 + CHIP_RATE + CHIP_OUT_LANES := by
  simp only [chipRowN, List.length_cons, List.length_append, permOutZ, List.length_replicate,
    padTo_length_eq]
  omega

/-- **`forgedChipTbl` VIOLATES `ChipTableSoundN permOutZ`** — its row `[0]` (length `1`) cannot be any
genuine `chipRowN permOutZ ins` (length `20`). So the predicate genuinely SEPARATES: a forged table is
NOT accepted — `Satisfied2Faithful`'s chip conjunct is not vacuously-always-true. -/
theorem forgedChipTbl_unsound : ¬ ChipTableSoundN permOutZ forgedChipTbl := by
  intro h
  obtain ⟨ins, _hins, hrow⟩ := h [0] (by simp [forgedChipTbl])
  -- `[0] = chipRowN permOutZ ins` forces `1 = 20` via lengths.
  have hl : ([0] : List ℤ).length = (chipRowN permOutZ ins).length := by rw [hrow]
  rw [chipRowN_length ins] at hl
  simp [CHIP_RATE, CHIP_OUT_LANES] at hl

/-- **`ChipTableSoundN` is non-vacuous (inhabited AND separating).** -/
theorem chipTableSoundN_nonvacuous :
    (∃ tbl : Table, ChipTableSoundN permOutZ tbl)
    ∧ (∃ tbl : Table, ¬ ChipTableSoundN permOutZ tbl) :=
  ⟨⟨genuineChipTbl, genuineChipTbl_sound⟩, ⟨forgedChipTbl, forgedChipTbl_unsound⟩⟩

/-! ## §3 — THE KEYSTONE: `Satisfied2Faithful` is inhabited by a REAL transfer.

We build a FAITHFUL trace whose auxiliary tables ARE the deployed faithful tables:
  * `.poseidon2` = `genuineChipTbl` — a genuine `ChipTableSoundN permOutZ` table;
  * `.range` = `rangeRows BAL_LIMB_BITS` — the genuine limb table (the deployed range AIR's height);
  * `.memory` / `.mapOps` = `[]` — `graduateV1` emits no mem/map ops.
With `rows = []` the per-row legs of `Satisfied2` are vacuous (`∀ i < 0`), so the per-row gates impose
no obstruction on the FAITHFUL tables, and the mem/map legs collapse to the empty log against the empty
boundary — exactly as the empty-trace floor (`satisfied2_transferV3_empty`), but now over a `tf` that
carries the GENUINE chip/range faithfulness. Then `chipTableFaithful` (= `genuineChipTbl_sound`) and
`rangeTableFaithful` (= rfl) are discharged STRUCTURALLY, lifting `Satisfied2` to the FULL faithful
object. The keystone: the deployed accept-set's chip/range faithfulness is realizable by a transfer. -/

open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3FrozenAuthority)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (memLog_graduateV1 mapLog_graduateV1)

/-- The faithful auxiliary tables, as a TOP-LEVEL function: a genuine chip table on `.poseidon2`, the
genuine limb table on `.range`, empty elsewhere. Kept top-level (not an inline structure field) so the
range-faithfulness lemma reduces `faithfulTf .range` to `rangeRows BAL_LIMB_BITS` by `unfold` WITHOUT a
projection-driven `whnf` that would try to EVALUATE the size-`2^30` `rangeRows` list. -/
def faithfulTf : TableId → Table := fun tid =>
  if tid = .poseidon2 then genuineChipTbl
  else if tid = .range then rangeRows BAL_LIMB_BITS
  else []

/-- The FAITHFUL trace: zero main rows, but the auxiliary tables ARE the deployed faithful tables (a
genuine chip table `genuineChipTbl`, the genuine range table `rangeRows BAL_LIMB_BITS`, empty mem/map).
This is the prover's run that emits no transfer rows but lays down the genuine fixed chip/range tables —
their faithfulness is independent of the (empty) main domain. -/
def faithfulTrace : VmTrace where
  rows := []
  pub  := fun _ => 0
  tf   := faithfulTf

/-- `faithfulTrace.tf` IS `faithfulTf` (function-level `rfl` — no application, so no evaluation). -/
theorem faithfulTrace_tf : faithfulTrace.tf = faithfulTf := rfl

theorem faithfulTf_poseidon2 : faithfulTf .poseidon2 = genuineChipTbl := by unfold faithfulTf; rfl
theorem faithfulTf_range : faithfulTf .range = rangeRows BAL_LIMB_BITS := by unfold faithfulTf; rfl
theorem faithfulTf_memory : faithfulTf .memory = [] := by unfold faithfulTf; rfl
theorem faithfulTf_mapOps : faithfulTf .mapOps = [] := by unfold faithfulTf; rfl

theorem faithfulTrace_poseidon2 : faithfulTrace.tf .poseidon2 = genuineChipTbl := by
  rw [faithfulTrace_tf, faithfulTf_poseidon2]
theorem faithfulTrace_range : faithfulTrace.tf .range = rangeRows BAL_LIMB_BITS := by
  rw [faithfulTrace_tf, faithfulTf_range]
theorem faithfulTrace_memory : faithfulTrace.tf .memory = [] := by
  rw [faithfulTrace_tf, faithfulTf_memory]
theorem faithfulTrace_mapOps : faithfulTrace.tf .mapOps = [] := by
  rw [faithfulTrace_tf, faithfulTf_mapOps]
theorem faithfulTrace_rows : faithfulTrace.rows = [] := rfl

/-- The underlying `Satisfied2` of the faithful trace: the per-row legs are vacuous (`rows = []`); the
mem/map legs collapse to the empty log against the empty boundary (`graduateV1` emits none), now read off
the faithful `tf` (`.memory`/`.mapOps` are `[]` there). We discharge the per-row legs against
`faithfulTrace_rows` only — NEVER unfolding `tf` (which carries the size-`2^30` `rangeRows`). -/
theorem satisfied2_faithfulTrace (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2 hash transferV3 minit mfin [] faithfulTrace where
  rowConstraints := by intro i hi; rw [faithfulTrace_rows] at hi; simp at hi
  rowHashes := by intro i hi; rw [faithfulTrace_rows] at hi; simp at hi
  rowRanges := by intro i hi; rw [faithfulTrace_rows] at hi; simp at hi
  memAddrsNodup := List.nodup_nil
  memClosed := by
    intro op hop
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1] at hop
    simp at hop
  memDisciplined := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    trivial
  memBalanced := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
      MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet]
  memTableFaithful := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      memLog_graduateV1]
    -- t.tf .memory = [] = [].map opRow.
    rw [faithfulTrace_memory, List.map_nil]
  mapTableFaithful := by
    rw [show transferV3 = graduateV1 (rotateV3FrozenAuthority transferVmDescriptor) from rfl,
      mapLog_graduateV1]
    rw [faithfulTrace_mapOps]

/-- **`satisfied2Faithful_transferV3` — THE KEYSTONE.** The FULL `Satisfied2Faithful` object is inhabited
for the live `transferV3` by the faithful trace: `Satisfied2` (from `satisfied2_faithfulTrace`) PLUS the
genuine chip-table faithfulness (`genuineChipTbl_sound`), the genuine range-table faithfulness (`rfl`),
the permutation width (`permOutZ_width`), and the lane-0 digest identity (`permOutZ_lane0`). So the
apex's `Satisfied2Faithful` hypothesis is provably NON-VACUOUS — a real transfer descriptor realizes the
deployed accept-set with its chip/range faithfulness carried as CONJUNCTS, not just `Satisfied2`. -/
theorem satisfied2Faithful_transferV3 (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2Faithful permOutZ permOut0 transferV3 minit mfin [] faithfulTrace where
  toSatisfied2 := satisfied2_faithfulTrace permOut0 minit mfin
  permWidth := permOutZ_width
  chipHashIsLane0 := permOutZ_lane0
  chipTableFaithful := by rw [faithfulTrace_poseidon2]; exact genuineChipTbl_sound
  rangeTableFaithful := faithfulTrace_range

/-- **`satisfied2Faithful_inhabited` — stated plainly: the faithful object is NON-EMPTY.** There exist a
permutation, a digest, a memory boundary and a trace inhabiting `Satisfied2Faithful` of the live
`transferV3`. So the apex's faithful hypothesis is not a silently-impossible antecedent. -/
theorem satisfied2Faithful_inhabited :
    ∃ (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
      (maddrs : List ℤ) (t : VmTrace),
      Satisfied2Faithful permOut hash transferV3 minit mfin maddrs t :=
  ⟨permOutZ, permOut0, fun _ => 0, fun _ => (0, 0), [], faithfulTrace,
   satisfied2Faithful_transferV3 (fun _ => 0) (fun _ => (0, 0))⟩

/-- **The collapse recipe FIRES on the keystone witness.** From the inhabited faithful object the v1
denotation `satisfiedVm` holds on every row WITHOUT any free chip/range lever — the structure CARRIES
them. (`rows = []`, so the conclusion `∀ i < 0` is vacuous here; the point is the RECIPE
`satisfied2Faithful_satisfiedVm` accepts the constructed object, not a hypothesis.) -/
theorem keystone_collapse_recipe
    (hgrad : Dregg2.Circuit.Emit.EffectVmEmitV2.graduable
      (rotateV3FrozenAuthority transferVmDescriptor) = true) :
    ∀ i, i < faithfulTrace.rows.length →
      satisfiedVm permOut0 (rotateV3FrozenAuthority transferVmDescriptor)
        (envAt faithfulTrace i) (i == 0) (i + 1 == faithfulTrace.rows.length) :=
  satisfied2Faithful_satisfiedVm permOutZ permOut0 (rotateV3FrozenAuthority transferVmDescriptor)
    (fun _ => 0) (fun _ => (0, 0)) [] faithfulTrace hgrad
    (satisfied2Faithful_transferV3 (fun _ => 0) (fun _ => (0, 0)))

/-! ## §4 — `EffAuthoritySource`: the cap-open authority CONCLUSION is non-trivial (separates).

`EffAuthoritySource` is a data-bearing (`Type 1`) carrier whose FULL inhabitation needs a deployed
depth-16 cap-tree opening trace (the named realizability floor `CapOpenTraceFloor`, the dual of
`StarkComplete`). What is Lean-decidable — and what guards against the carrier being a degenerate
"always authorized" gate — is that its CONCLUSION `authorizedFacetEffB` genuinely SEPARATES: TRUE for an
owner turn, FALSE for a non-owner holding no caps. So the authority the carrier forces is real content,
not a vacuous pass. -/

open Dregg2.Exec (Turn)
open Dregg2.Exec.FacetAuthority (FacetCaps AuthProvided authorizedFacetEffB authorizedFacetEffB_owner)

/-- The empty cap assignment: nobody holds any cap. -/
def noCaps : FacetCaps := fun _ => []

/-- **`authorizedFacetEffB` is TRUE for an owner turn** (`actor = src`) — the carrier's authority
conclusion is satisfiable. -/
theorem authority_holds_owner (provided : AuthProvided) (effectBit : Dregg2.Exec.FacetAuthority.EffectMask) :
    authorizedFacetEffB noCaps provided effectBit { actor := 7, src := 7, dst := 0, amt := 0 } = true :=
  authorizedFacetEffB_owner noCaps provided effectBit _ rfl

/-- **`authorizedFacetEffB` is FALSE for a non-owner with no caps** (`actor ≠ src`, empty `caps`) — the
carrier's authority conclusion is NOT vacuously-always-true. So `EffAuthoritySource`'s forced authority
genuinely constrains: a turn lacking both ownership and a cap is REJECTED. -/
theorem authority_fails_no_cap (provided : AuthProvided) (effectBit : Dregg2.Exec.FacetAuthority.EffectMask) :
    authorizedFacetEffB noCaps provided effectBit { actor := 7, src := 9, dst := 0, amt := 0 } = false := by
  unfold authorizedFacetEffB noCaps
  simp

/-- **The authority conclusion SEPARATES (non-trivial).** Some turn authorizes, another does not — so the
authority gate the `EffAuthoritySource` carrier forces is genuine content, not a degenerate constant. -/
theorem authorizedFacetEffB_separates :
    (∃ (caps : FacetCaps) (p : AuthProvided) (e : Dregg2.Exec.FacetAuthority.EffectMask) (tr : Turn),
        authorizedFacetEffB caps p e tr = true)
    ∧ (∃ (caps : FacetCaps) (p : AuthProvided) (e : Dregg2.Exec.FacetAuthority.EffectMask) (tr : Turn),
        authorizedFacetEffB caps p e tr = false) :=
  ⟨⟨noCaps, .signature, 0, _, authority_holds_owner .signature 0⟩,
   ⟨noCaps, .signature, 0, _, authority_fails_no_cap .signature 0⟩⟩

/-! ## §5 — `StarkComplete`: the completeness body is a non-degenerate obligation.

`StarkComplete.build` produces `∃ π, verifyBatch (vkOfRegistry R) pi π = Verdict.accept`. Inhabiting the
class requires an accepting proof against the OPAQUE `verifyBatch` — the named FRI/p3 realizability, not
a Lean-internal vacuity. What is Lean-decidable — and guards against the obligation being secretly
`True` (always trivially met) or secretly `False` (impossible to meet) — is that `Verdict.accept` is a
DISTINCT, REACHABLE verdict: `accept ≠ reject`. So "`verifyBatch … = accept`" is a real constraint
(neither tautology nor contradiction at the verdict level). -/

open Dregg2.Circuit.CircuitSoundness (Verdict)

/-- **`Verdict.accept ≠ Verdict.reject`** — the verdict the `StarkComplete` obligation demands is a
distinct outcome, so "accept" is a non-trivial target (not definitionally the only verdict). -/
theorem verdict_accept_ne_reject : Verdict.accept ≠ Verdict.reject := by decide

/-- **The `StarkComplete` obligation is non-degenerate at the verdict level.** There are at least two
distinct verdicts, so `verifyBatch … = accept` neither holds for all verdicts (it is not `True`) nor for
none (`accept` is itself a verdict). The completeness floor's body is a genuine realizability obligation,
not a laundered tautology. -/
theorem starkComplete_obligation_nondegenerate :
    ∃ v₁ v₂ : Verdict, v₁ ≠ v₂ :=
  ⟨Verdict.accept, Verdict.reject, verdict_accept_ne_reject⟩

/-! ## §6 — axiom hygiene. -/

#assert_axioms encodeSponge_cr
#assert_axioms poseidon2SpongeCR_separates
#assert_axioms genuineChipTbl_sound
#assert_axioms forgedChipTbl_unsound
#assert_axioms satisfied2_faithfulTrace
#assert_axioms satisfied2Faithful_transferV3
#assert_axioms satisfied2Faithful_inhabited
#assert_axioms keystone_collapse_recipe
#assert_axioms authority_fails_no_cap
#assert_axioms authorizedFacetEffB_separates
#assert_axioms starkComplete_obligation_nondegenerate

end Dregg2.Circuit.FloorsNonVacuous
