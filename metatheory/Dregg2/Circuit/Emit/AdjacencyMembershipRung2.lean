/-
# Dregg2.Circuit.Emit.AdjacencyMembershipRung2 — the RUNG-2 discharge of the last-row ordering
residual for the emitted neighbor-adjacency (sorted-set non-membership) descriptor
(`adjacencyDesc`), and the LANDED emit-fix (`adjLastOrderFix`) that closes genuine no-forgery
UNCONDITIONALLY.

## What Rung 1 gave us and what the residual WAS (now closed by the emit-fix)

`AdjacencyMembershipRefine.lean` (RUNG 1) proves the whole-descriptor bridge in two pieces:
  * `adjacency_sat_refines` : `Satisfied2 adjacencyDesc` + the NAMED Poseidon2 chip carrier
    (`ChipTableSound`) FORCE an `AdjacencyAuthFragment` — both leaves fold AUTHENTICALLY (dir-ordered
    Poseidon2 combine per active level) up to their top spine node `*_CUR[last]`, both top parents
    `*_PAR[last]` are pinned to the SAME public `root`, `root` is a genuine `hash` of the last-row
    `(left,right)` pair, and the published indices are consecutive.
  * `adjacency_full_bridge` : the fragment PLUS `TopLevelOrdered` (the ONE un-forced fact) yields the
    full functional spec `AdjacentLeavesUnderRoot` — both leaves are the leaves of full authentic
    Poseidon2-Merkle paths reaching the same committed root at consecutive indices.

`TopLevelOrdered` is the residual: on the LAST trace row, each path's `par` is the authentic
dir-ordered combine of its `(cur, sib)`. Rung 1 names WHY it is un-forced: the deployed DSL lowers
the `Binary`/`Polynomial` child-ordering gates as `is_transition = false` (they fire on EVERY row,
`dsl_plonky3.rs:225/240`), but `AdjacencyMembershipEmit` maps them to IR-v2 `.base (.gate …)`, whose
`VmConstraint.holdsVm` makes a `.gate` VACUOUS on the last row. So the top-level ordering
`L_LEFT[last] = dir-order-left(L_CUR[last], L_SIB[last])` (etc.) is DROPPED, breaking exactly ONE edge
of the authentication chain:

    leaf →(fold, ENFORCED)→ L_CUR[last] →(ordering gate, DROPPED)→ {L_LEFT,L_RIGHT}[last]
                                                                  →(chip lookup, ENFORCED)→ root

## The classification (was RUNG2_PARTIAL) — and why the residual needed an EMIT fix, not a crypto one

The disclosed commitment is the SHALLOW Merkle `root = hash [L_LEFT[last], L_RIGHT[last]]` — it binds
only the top hash's TWO children. Unlike the DFA route-commitment (a DEEP fold binding every row, which
`fold_inj`/CR pins whole), the CR carrier here can bind the disclosed pair `(L_LEFT, L_RIGHT)[last]` to
the genuine one (`topPair_no_forgery`, §5, consuming `CollisionFree`), but it CANNOT bind the SPINE
CONNECTION `L_CUR[last] ∈ dir-order⁻¹(L_LEFT, L_RIGHT)[last]`: nothing commits `L_CUR[last]` at the top,
and the broken edge is an ARITHMETIC ordering gate, not a hash-preimage relation. So the residual was a
genuine EMIT/lowering-fidelity gap, and the fix is an emit change (now landed) — not a new crypto carrier.

This file DISCHARGES the residual and the emit-fix that closes it:
  * §2  `adjacency_rung2_closes` — the closure: `Satisfied2 adjacencyDesc` + `ChipTableSound` +
        `LastRowOrdered` ⟹ the genuine no-forgery spec `AdjacentLeavesUnderRoot`. Consumes the NAMED
        carrier `ChipTableSound` (the last-row `root = hash[left,right]` binding). This is the discharge.
  * §3  `adjLastOrderFix` — the exact 6 constraints the emit must add (`.base (.boundary VmRow.last …)`
        of the dir-binary / left-order / right-order bodies, per path), and `lastRowOrdered_of_fix`
        proving those constraints ENFORCE `LastRowOrdered`. This names the emit-fix constructively.
  * §4  `adjacency_rung2_fixed_closes` — the CROWN, now on the REAL descriptor: a `Satisfied2` of the
        emitted `adjacencyDesc` (which CARRIES the landed `adjLastOrderFix`) forces
        `AdjacentLeavesUnderRoot` UNCONDITIONALLY — no re-assumed `LastRowOrdered`. The fix is landed and
        SUFFICIENT.
  * §5  `topPair_no_forgery` — the partial no-forgery the CR carrier DOES buy (the top pair is bound to
        the genuine children), honestly delimited: it does NOT close the spine connection.
  * §6  the TRUE half — a genuine trace whose closure FIRES to `AdjacentLeavesUnderRoot`.
  * §7  the LOAD-BEARING witness — a concrete forged trace that `Satisfied2`s the fix-less
        `adjacencyDescCore` yet VIOLATES `TopLevelOrdered` AND is REJECTED by the fixed real
        `adjacencyDesc`. Proves `adjLastOrderFix` is load-bearing, not decorative: the fix is exactly
        what turns the accepted forgery into a rejection.

## The emit-fix (now LANDED)

`AdjacencyMembershipEmit` now emits, per path, the three child-ordering bodies ALSO as
`.base (.boundary VmRow.last …)` (`adjLastOrderFix`), so `holdsVm` fires them on the last row too — the
deployed DSL's actual every-row `assert_zero` (`is_transition = false`) semantics. `adjacencyDesc`
is now the fixed descriptor (`adjacencyConstraintsCore ++ adjLastOrderFix`), so the top-level ordering
is enforced on every row and the Rung-1 `TopLevelOrdered` residual is CLOSED.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The Poseidon2 chip carrier enters ONLY as
the NAMED hypothesis `ChipTableSound hash (t.tf .poseidon2)`; the Poseidon2 CR carrier enters ONLY as
`CollisionFree (dfaPrims hash)`. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.AdjacencyMembershipRefine
import Dregg2.Circuit.Emit.DfaRoutingRung2

namespace Dregg2.Circuit.Emit.AdjacencyMembershipRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   WindowConstraint WindowExpr ChipTableSound chip_lookup_sound chipLookupTuple CHIP_RATE
   chipRow memLog mapLog memCheck_nil)
open Dregg2.Circuit.Emit.AdjacencyMembershipEmit
open Dregg2.Circuit.Emit.AdjacencyMembershipRefine
open Dregg2.Crypto (CryptoPrimitives)
open Dregg2.Crypto.DfaAcceptanceAir (CollisionFree)
open Dregg2.Circuit.Emit.DfaRoutingRung2 (dfaPrims collisionFree_of_injective)

set_option autoImplicit false

/-- The membership tactic (local copy — the Rung-1 macro is file-local): every constraint we name is
literally in `adjacencyDesc.constraints` (= `adjacencyConstraints`). -/
local macro "adj_mem" : tactic =>
  `(tactic| (show _ ∈ adjacencyConstraints;
             simp [adjacencyConstraints, adjacencyConstraintsCore, adjLastOrderFix, adjLastIdxFix,
               pathBlock]))

/-! ## §1 — `LastRowOrdered`: the emit-fix's semantic content (the residual, phrased as a hypothesis
the fixed emit supplies). Exactly the three child-ordering bodies of each path, forced to vanish on the
LAST trace row — what the deployed DSL's every-row `Binary`/`Polynomial` gates enforce and the IR-v2
`.gate` mapping drops. -/

/-- The six ordering-gate bodies of both paths, vanishing on the last trace row. -/
def LastRowOrdered (t : VmTrace) : Prop :=
  (dirBinaryBody L_DIR).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (leftOrderBody L_CUR L_SIB L_DIR L_LEFT).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (rightOrderBody L_CUR L_SIB L_DIR L_RIGHT).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (dirBinaryBody U_DIR).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (leftOrderBody U_CUR U_SIB U_DIR U_LEFT).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (rightOrderBody U_CUR U_SIB U_DIR U_RIGHT).eval (envAt t (t.rows.length - 1)).loc = 0

/-! ## §2 — THE DISCHARGE: `LastRowOrdered` + the chip carrier close `TopLevelOrdered`, hence the full
functional no-forgery spec via the Rung-1 bridge. -/

/-- **`LastRowOrdered` closes the residual `TopLevelOrdered`.** On the last row, the three ordering
bodies (from `LastRowOrdered`) plus the last-row chip lookup `par = hash[left,right]` (from the NAMED
`ChipTableSound` carrier, escaping the transition zerofier) collapse to the authentic dir-ordered
combine — exactly `combine_of_gates` at the top level, for both paths. -/
theorem topLevelOrdered_of_lastRowOrdered {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 0 < t.rows.length)
    (hlro : LastRowOrdered t) :
    TopLevelOrdered hash t := by
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  obtain ⟨hdL, hlL, hrL, hdU, hlU, hrU⟩ := hlro
  refine ⟨?_, ?_⟩
  · exact combine_of_gates hash (envAt t (t.rows.length - 1)).loc
      L_CUR L_SIB L_DIR L_LEFT L_RIGHT L_PAR hdL hlL hrL
      (lookupChip hsat hChip _ hLlt L_LEFT L_RIGHT L_PAR L_PAR_LANES (by adj_mem))
  · exact combine_of_gates hash (envAt t (t.rows.length - 1)).loc
      U_CUR U_SIB U_DIR U_LEFT U_RIGHT U_PAR hdU hlU hrU
      (lookupChip hsat hChip _ hLlt U_LEFT U_RIGHT U_PAR U_PAR_LANES (by adj_mem))

/-- **`adjacency_rung2_closes` — THE RUNG-2 DISCHARGE (semantic form).** A trace that `Satisfied2`s the
emitted `adjacencyDesc`, rides the NAMED Poseidon2 chip carrier, and additionally has the last-row
ordering forced (`LastRowOrdered` — exactly what the emit-fix supplies) is a genuine two-path
binary-Merkle authentication transcript of two consecutive-index leaves under one shared committed
root: `AdjacentLeavesUnderRoot`. The named carrier discharged is `ChipTableSound`; the residual removed
is the emit's dropped last-row ordering. -/
theorem adjacency_rung2_closes {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlro : LastRowOrdered t) :
    AdjacentLeavesUnderRoot hash (t.pub PI_LEAF_LOWER) (t.pub PI_LEAF_UPPER)
      (t.pub PI_ROOT) (t.pub PI_IDX_LOWER) (t.pub PI_IDX_UPPER) :=
  adjacency_full_bridge hlen hsat hChip
    (topLevelOrdered_of_lastRowOrdered hsat hChip hlen hlro)

/-! ## §3 — THE EMIT-FIX (`adjLastOrderFix`, now LANDED in `AdjacencyMembershipEmit`), proven to
ENFORCE `LastRowOrdered`.

`adjLastOrderFix` is the six last-row ordering boundary constraints (three per path) the emit adds:
each is the exact child-ordering body the DSL's every-row `Binary`/`Polynomial` gate carries,
re-lowered as a `.base (.boundary VmRow.last …)` so it fires on the last row (where the IR-v2 `.gate`
mapping makes it vacuous). It now lives in the emit file and `adjacencyDesc.constraints`
(= `adjacencyConstraintsCore ++ adjLastOrderFix`) contains it. -/

/-- A declared last-row boundary body vanishes on the last row — the generic form of the Rung-1
`lastBoundaryZero`, over ANY descriptor `d` carrying the constraint. -/
theorem genLastBoundaryZero {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hlen : 0 < t.rows.length) (body : EmittedExpr)
    (hmem : VmConstraint2.base (.boundary VmRow.last body) ∈ d.constraints) :
    body.eval (envAt t (t.rows.length - 1)).loc = 0 := by
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  have hlast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    have : t.rows.length - 1 + 1 = t.rows.length := by omega
    simp [this]
  have h := hsat.rowConstraints _ hLlt _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h
  exact h (by decide)

/-- **`lastRowOrdered_of_fix` — the emit-fix ENFORCES `LastRowOrdered`.** For any descriptor `d` whose
constraints CONTAIN `adjLastOrderFix`, a `Satisfied2` of `d` forces `LastRowOrdered` (each fix
constraint is a last-row boundary read). This is the constructive content of "add these six and the
residual is enforced". -/
theorem lastRowOrdered_of_fix {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash d minit mfin maddrs t) (hlen : 0 < t.rows.length)
    (hmem : ∀ c ∈ adjLastOrderFix, c ∈ d.constraints) :
    LastRowOrdered t := by
  have g : ∀ b : EmittedExpr, VmConstraint2.base (.boundary VmRow.last b) ∈ adjLastOrderFix →
      b.eval (envAt t (t.rows.length - 1)).loc = 0 :=
    fun b hb => genLastBoundaryZero hsat hlen b (hmem _ hb)
  refine ⟨g _ ?_, g _ ?_, g _ ?_, g _ ?_, g _ ?_, g _ ?_⟩ <;>
    (show _ ∈ adjLastOrderFix) <;>
    repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-! ## §4 — THE CROWN: the REAL (fixed-emit) descriptor forces the full no-forgery spec UNCONDITIONALLY.

With `adjLastOrderFix` now landed in the emit, `adjacencyDesc.constraints`
(= `adjacencyConstraintsCore ++ adjLastOrderFix`) CONTAINS the fix, so `lastRowOrdered_of_fix` forces
`LastRowOrdered` from `Satisfied2 adjacencyDesc` directly — no re-assumed hypothesis. -/

/-- **`adjLastOrderFix ⊆ adjacencyDesc.constraints`** — the fix is genuinely part of the emitted
descriptor (it is the right append component of `adjacencyConstraints`). -/
theorem adjLastOrderFix_subset :
    ∀ c ∈ adjLastOrderFix, c ∈ adjacencyDesc.constraints := by
  intro c hc
  show c ∈ adjacencyConstraints
  rw [show adjacencyConstraints
        = (adjacencyConstraintsCore ++ adjLastOrderFix) ++ adjLastIdxFix from rfl]
  exact List.mem_append_left _ (List.mem_append_right _ hc)

/-- **`adjacency_rung2_fixed_closes` — THE UNCONDITIONAL CROWN on the REAL descriptor.** A `Satisfied2`
of the emitted `adjacencyDesc` (which now carries the emit-fix), against the NAMED Poseidon2 chip
carrier, forces the genuine functional no-forgery spec `AdjacentLeavesUnderRoot` — UNCONDITIONALLY, no
re-assumed `LastRowOrdered`. The emit-fix (`adjLastOrderFix`, now landed) closes the Rung-1
`TopLevelOrdered` gap; nothing else is missing. -/
theorem adjacency_rung2_fixed_closes {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    AdjacentLeavesUnderRoot hash (t.pub PI_LEAF_LOWER) (t.pub PI_LEAF_UPPER)
      (t.pub PI_ROOT) (t.pub PI_IDX_LOWER) (t.pub PI_IDX_UPPER) := by
  have hlro : LastRowOrdered t := lastRowOrdered_of_fix hsat hlen adjLastOrderFix_subset
  exact adjacency_rung2_closes hlen hsat hChip hlro

/-! ## §5 — What the CR carrier DOES buy (and honestly, what it does NOT). -/

/-- **`topPair_no_forgery` — the partial no-forgery the Poseidon2 CR carrier discharges.** Against the
NAMED CR carrier `CollisionFree (dfaPrims hash)` and the honest anchor `root = hash[gL, gR]` (the
disclosed root's genuine children, from a real reference tree), the last-row disclosed child columns
`(L_LEFT, L_RIGHT)[last]` are FORCED to the genuine pair `(gL, gR)`: the prover cannot forge the top
`(left,right)` away from the honest ones. This consumes `compress_pair_inj` non-vacuously.

**What CR does NOT give (the emit gap):** it does NOT force `(gL, gR) = dir-order(L_CUR[last],
L_SIB[last])` — i.e. that the trace's authentic top spine node `L_CUR[last]` is genuinely a child of the
root. That connection is the ARITHMETIC ordering gate the emit drops (§7 exhibits a `Satisfied2` trace
where it fails), and no CR carrier can close it — the Merkle root is a SHALLOW commitment (only the top
hash's two children), so `L_CUR[last]` is uncommitted at the top. Hence the emit-fix (§3/§4), not a
crypto carrier, is the closure. -/
theorem topPair_no_forgery {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (cf : @CollisionFree ℤ _ (dfaPrims hash))
    (gL gR : ℤ)
    (hanchor : t.pub PI_ROOT = hash [gL, gR]) :
    (envAt t (t.rows.length - 1)).loc L_LEFT = gL
    ∧ (envAt t (t.rows.length - 1)).loc L_RIGHT = gR := by
  letI := dfaPrims hash
  have frag := adjacency_sat_refines hlen hsat hChip
  have heq : CryptoPrimitives.compress ((envAt t (t.rows.length - 1)).loc L_LEFT)
                ((envAt t (t.rows.length - 1)).loc L_RIGHT)
           = CryptoPrimitives.compress gL gR := by
    show hash [(envAt t (t.rows.length - 1)).loc L_LEFT, (envAt t (t.rows.length - 1)).loc L_RIGHT]
       = hash [gL, gR]
    rw [← frag.rootHashedLower]; exact hanchor
  exact cf.compress_pair_inj _ _ _ _ heq

/-- The CR carrier is realizable (NOT vacuously assumed): `CollisionFree (dfaPrims hash)` is inhabited
from `Function.Injective hash` (`collisionFree_of_injective`, the reference realization). A genuine
Poseidon2 `hash` supplies CR; injectivity is the reference stand-in that makes the hypothesis set of
`topPair_no_forgery` non-empty. -/
theorem cr_carrier_realizable {hash : List ℤ → ℤ} (hinj : Function.Injective hash) :
    @CollisionFree ℤ _ (dfaPrims hash) :=
  collisionFree_of_injective hinj

/-! ## §6 — Non-vacuity, TRUE half: a GENUINE trace whose closure FIRES.

A depth-1 adjacency: the two SIBLING leaves `10` (index 0, LEFT child) and `20` (index 1, RIGHT child)
under the shared parent `root = mHash [10,20] = 1020`. The lower path folds `10` with sibling `20`,
`dir=0`; the upper path folds `20` with sibling `10`, `dir=1` — both reach `1020`. The child-ordering
holds (`L_LEFT=L_CUR=10`, `L_RIGHT=L_SIB=20`; `U_LEFT=10=U_SIB`, `U_RIGHT=20=U_CUR`), so `LastRowOrdered`
holds and the RUNG-2 closure FIRES to the genuine `AdjacentLeavesUnderRoot`. -/

/-- A concrete little-endian digit hash — distinguishes child order (`[a,b] ↦ 100a+b`). -/
private def mHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- The genuine depth-1 row: leaves `10`/`20` as SIBLINGS, ordered children `(10,20)`, both parents =
root `1020`, indices `0`/`1`, `pow=1`. `L_DIR=0` (lower is left), `U_DIR=1` (upper is right). -/
private def wRow : Assignment := fun c =>
  if c = L_CUR then 10 else if c = L_SIB then 20 else if c = L_LEFT then 10
  else if c = L_RIGHT then 20 else if c = L_PAR then 1020
  else if c = U_CUR then 20 else if c = U_SIB then 10 else if c = U_DIR then 1
  else if c = U_LEFT then 10 else if c = U_RIGHT then 20 else if c = U_PAR then 1020
  else if c = U_IDX_OUT then 1 else if c = POW then 1 else 0

private def wPub : Assignment := fun k =>
  if k = PI_ROOT then 1020 else if k = PI_LEAF_LOWER then 10
  else if k = PI_LEAF_UPPER then 20 else if k = PI_IDX_UPPER then 1 else 0

private def wTbl : List (List ℤ) :=
  [chipRow mHash [10, 20] (List.replicate 7 0)]

private def wTrace : VmTrace :=
  { rows := [wRow], pub := wPub
    tf := fun tid => match tid with | .poseidon2 => wTbl | _ => [] }

/-- The concrete chip table is genuinely SOUND (every row is a real `chipRow` of `mHash`). -/
theorem wtChipSound : ChipTableSound mHash (wTrace.tf .poseidon2) := by
  intro r hr
  simp only [wTrace, wTbl, List.mem_singleton] at hr
  exact ⟨[10, 20], List.replicate 7 0, by decide, by decide, hr⟩

/-- **The genuine trace `Satisfied2`s the deployed descriptor** — the two lookups by membership, the
per-row gates vacuous on the single (= last) row, and the boundary/PI pins met. -/
theorem wtSat :
    Satisfied2 mHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] wTrace := by
  have hmemlog : memLog adjacencyDesc wTrace = [] := rfl
  have hmaplog : mapLog adjacencyDesc wTrace = [] := rfl
  have hF : (0 == 0) = true := rfl
  have hL : (0 + 1 == wTrace.rows.length) = true := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show wTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    rw [show adjacencyDesc.constraints = adjacencyConstraints from rfl] at hc
    simp only [adjacencyConstraints, adjacencyConstraintsCore, adjLastOrderFix, adjLastIdxFix,
      pathBlock, List.cons_append, List.nil_append] at hc
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        copyWindow, Lookup.holdsAt, hF, hL] <;>
      decide
  · intro i _; trivial
  · intro i _ r hr; simp [adjacencyDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- The genuine trace's last-row ordering holds (`decide` over the concrete row) — so `LastRowOrdered`
is jointly satisfiable with `Satisfied2`, not an empty antecedent. -/
theorem wtLastRowOrdered : LastRowOrdered wTrace := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **THE RUNG-2 CLOSURE FIRES on the genuine witness (TRUE half).** Feeding the concrete satisfying
trace, its sound chip table, and its (achievable) `LastRowOrdered` to `adjacency_rung2_closes` recovers
the genuine `AdjacentLeavesUnderRoot` — two authentic Merkle paths for the sibling leaves `10, 20`
reaching the shared root `1020` at consecutive indices `0, 1`. -/
theorem wtTrace_rung2_fires :
    AdjacentLeavesUnderRoot mHash (wTrace.pub PI_LEAF_LOWER) (wTrace.pub PI_LEAF_UPPER)
      (wTrace.pub PI_ROOT) (wTrace.pub PI_IDX_LOWER) (wTrace.pub PI_IDX_UPPER) :=
  adjacency_rung2_closes (by decide) wtSat wtChipSound wtLastRowOrdered

/-- The recovered spec is over the genuine public values (leaves `10,20`; root `1020`; indices `0,1`) —
a real adjacency, not a constant. -/
theorem wtTrace_value :
    wTrace.pub PI_LEAF_LOWER = 10 ∧ wTrace.pub PI_LEAF_UPPER = 20
    ∧ wTrace.pub PI_ROOT = 1020 ∧ wTrace.pub PI_IDX_UPPER = wTrace.pub PI_IDX_LOWER + 1 := by
  refine ⟨rfl, rfl, rfl, ?_⟩; decide

/-! ## §7 — THE LOAD-BEARING witness: `adjLastOrderFix` is exactly what rejects the top-level forgery.

The same depth-1 shape, but the top children are FORGED: `L_LEFT=3, L_RIGHT=4`, `root = mHash[3,4] =
304`, while the leaf is `L_CUR=10` with `L_SIB=0, L_DIR=0`. The child-ordering gate that would force
`L_LEFT = L_CUR = 10` is VACUOUS on the last row under the TRANSITION-only `.gate` mapping — so the
forged trace `Satisfied2`s the CORE descriptor (`adjacencyDescCore`, the constraints WITHOUT the fix) —
yet the leaf `10` is NOT a child of the committed root `304` (its authentic top spine folds to
`combine mHash 0 10 0 = 1000 ≠ 304`). The landed emit-fix (`adjLastOrderFix`) is EXACTLY what catches
this: the fixed real `adjacencyDesc` REJECTS the forged trace (its last-row `leftOrderBody` boundary is
`3 - 10 = -7 ≠ 0`). So the fix is LOAD-BEARING — the core accepts the forgery, the real emit does not. -/

/-- The forged row: leaf `10` (lower) / `20` (upper), but top children `(3,4)` unrelated to the leaves,
parents = the forged root `304 = mHash[3,4]`, indices `0`/`1`. Ordering NOT enforced on the last row. -/
private def fRow : Assignment := fun c =>
  if c = L_CUR then 10 else if c = U_CUR then 20
  else if c = L_LEFT then 3 else if c = L_RIGHT then 4 else if c = L_PAR then 304
  else if c = U_LEFT then 3 else if c = U_RIGHT then 4 else if c = U_PAR then 304
  else if c = POW then 1 else if c = U_IDX_OUT then 1 else 0

private def fPub : Assignment := fun k =>
  if k = PI_ROOT then 304 else if k = PI_LEAF_LOWER then 10
  else if k = PI_LEAF_UPPER then 20 else if k = PI_IDX_UPPER then 1 else 0

private def fTbl : List (List ℤ) :=
  [chipRow mHash [3, 4] (List.replicate 7 0)]

private def fTrace : VmTrace :=
  { rows := [fRow], pub := fPub
    tf := fun tid => match tid with | .poseidon2 => fTbl | _ => [] }

theorem fChipSound : ChipTableSound mHash (fTrace.tf .poseidon2) := by
  intro r hr
  simp only [fTrace, fTbl, List.mem_singleton] at hr
  exact ⟨[3, 4], List.replicate 7 0, by decide, by decide, hr⟩

/-- **`adjacencyDescCore`** — the emitted descriptor WITHOUT the last-row ordering fix (the
transition-only `adjacencyConstraintsCore`). This is what the CURRENT emit would produce were the fix
dropped; it is the descriptor the forged trace exploits. -/
def adjacencyDescCore : EffectVmDescriptor2 :=
  { adjacencyDesc with constraints := adjacencyConstraintsCore }

/-- **The forged trace PROVABLY `Satisfied2`s the fix-less CORE descriptor** — the transition-only
ordering `.gate`s are vacuous on the last row, so the top children lie while every other constraint
holds. (This is the forgery the deployed every-row `assert_zero` lowering — now mirrored by
`adjLastOrderFix` — closes.) -/
theorem fSatCore :
    Satisfied2 mHash adjacencyDescCore (fun _ => 0) (fun _ => (0, 0)) [] fTrace := by
  have hmemlog : memLog adjacencyDescCore fTrace = [] := rfl
  have hmaplog : mapLog adjacencyDescCore fTrace = [] := rfl
  have hF : (0 == 0) = true := rfl
  have hL : (0 + 1 == fTrace.rows.length) = true := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show fTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    rw [show adjacencyDescCore.constraints = adjacencyConstraintsCore from rfl] at hc
    simp only [adjacencyConstraintsCore, pathBlock, List.cons_append, List.nil_append] at hc
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        copyWindow, Lookup.holdsAt, hF, hL] <;>
      decide
  · intro i _; trivial
  · intro i _ r hr; simp [adjacencyDescCore, adjacencyDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **The residual `TopLevelOrdered` genuinely FAILS on the forged trace.** The lower top parent `304`
is not the authentic combine `combine mHash 0 10 0 = 1000` — so `Satisfied2` of the CORE +
`ChipTableSound` do NOT force `TopLevelOrdered`. The dropped ordering is a REAL gap, not a proof
artifact. -/
theorem cheat_not_topLevelOrdered : ¬ TopLevelOrdered mHash fTrace := by
  intro h; exact absurd h.1 (by decide)

/-- **`LastRowOrdered` genuinely FAILS on the forged trace** — the lower `leftOrderBody` is
`3 - 10 = -7 ≠ 0`. So `LastRowOrdered` is NOT derivable from a fix-less `Satisfied2`: it is
load-bearing, and the same fact makes the forged trace FAIL the fixed real `adjacencyDesc`. -/
theorem cheat_not_lastRowOrdered : ¬ LastRowOrdered fTrace := by
  intro h; exact absurd h.2.1 (by decide)

/-- **The landed fix REJECTS the forged trace.** The forged trace does NOT `Satisfied2` the real
(fixed-emit) `adjacencyDesc`: its added last-row `leftOrderBody` boundary body is `3 - 10 = -7 ≠ 0`.
This is the constraint `adjLastOrderFix` supplies — the top-level forgery is now caught IN the
descriptor. -/
theorem fNotSat :
    ¬ Satisfied2 mHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace := by
  intro h
  have hmem : VmConstraint2.base (.boundary VmRow.last (leftOrderBody L_CUR L_SIB L_DIR L_LEFT))
      ∈ adjacencyDesc.constraints := by adj_mem
  have h0 := h.rowConstraints 0 (by decide) _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
    show (0 + 1 == fTrace.rows.length) = true from rfl] at h0
  revert h0
  decide

/-- The forged trace witnesses that `adjLastOrderFix` is LOAD-BEARING, not decorative: it `Satisfied2`s
the fix-less CORE descriptor (with a sound chip table) yet BREAKS the no-forgery residual
`TopLevelOrdered` AND is REJECTED by the fixed real `adjacencyDesc`. The fix is exactly what turns the
accepted forgery into a rejection. -/
theorem cheat_load_bearing :
    Satisfied2 mHash adjacencyDescCore (fun _ => 0) (fun _ => (0, 0)) [] fTrace
    ∧ ChipTableSound mHash (fTrace.tf .poseidon2)
    ∧ ¬ TopLevelOrdered mHash fTrace
    ∧ ¬ Satisfied2 mHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace :=
  ⟨fSatCore, fChipSound, cheat_not_topLevelOrdered, fNotSat⟩

/-! ## §9 — THE INDEX-RECONSTRUCTION FIX (`adjLastIdxFix`, now LANDED), proven to ENFORCE
`LastRowIdxReconstructed`, with the BETWEEN-LEAF forgery as its LOAD-BEARING witness.

Conjunct C of a sound non-membership witness — the two leaves sit at CONSECUTIVE tree positions,
i.e. the indices reconstructed from the path direction bits differ by exactly 1 — was un-bound on the
last row. `idxStepBody` (`idx_out - idx_in - dir*pow`) was emitted only as a transition `.gate`
(`pathBlock`), which `holdsVm_gate_true` makes VACUOUS on the last row, so `L_IDX_OUT[last]` /
`U_IDX_OUT[last]` were FREE — pinned only to the index PIs and the consecutiveness tooth, DECOUPLED from
the genuine reconstruction `idx_in[last] + dir[last]*pow[last]`. A prover could therefore publish index
values inconsistent with the actual leaf positions: present two NON-adjacent leaves as adjacent (fake
consecutiveness), a bogus non-membership witness. This is ISOMORPHIC to the top-level ORDERING drop the
authors already closed with `adjLastOrderFix` — the same last-row `.gate`-vacuity, one conjunct over.

`adjLastIdxFix` re-lowers the two index bodies as `.base (.boundary VmRow.last …)`, firing on the last
row too (the deployed every-row `assert_zero` semantics, `dsl_plonky3.rs`), so the published last-row
index is bound to the in-circuit reconstruction on EVERY row. -/

/-- The two index-accumulation bodies of both paths, vanishing on the last trace row: the published
last-row `idx_out` equals the genuine in-circuit reconstruction `idx_in + dir*pow`. -/
def LastRowIdxReconstructed (t : VmTrace) : Prop :=
  (idxStepBody L_DIR L_IDX_IN L_IDX_OUT).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (idxStepBody U_DIR U_IDX_IN U_IDX_OUT).eval (envAt t (t.rows.length - 1)).loc = 0

/-- **`adjLastIdxFix ⊆ adjacencyDesc.constraints`** — the index fix is genuinely part of the emitted
descriptor (the rightmost append component of `adjacencyConstraints`). -/
theorem adjLastIdxFix_subset :
    ∀ c ∈ adjLastIdxFix, c ∈ adjacencyDesc.constraints := by
  intro c hc
  show c ∈ adjacencyConstraints
  rw [show adjacencyConstraints
        = (adjacencyConstraintsCore ++ adjLastOrderFix) ++ adjLastIdxFix from rfl]
  exact List.mem_append_right _ hc

/-- **`lastRowIdxReconstructed_of_fix` — the index fix ENFORCES `LastRowIdxReconstructed`.** For any
descriptor `d` whose constraints CONTAIN `adjLastIdxFix`, a `Satisfied2` of `d` forces the last-row
index reconstruction (each fix constraint is a last-row boundary read). -/
theorem lastRowIdxReconstructed_of_fix {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash d minit mfin maddrs t) (hlen : 0 < t.rows.length)
    (hmem : ∀ c ∈ adjLastIdxFix, c ∈ d.constraints) :
    LastRowIdxReconstructed t := by
  have g : ∀ b : EmittedExpr, VmConstraint2.base (.boundary VmRow.last b) ∈ adjLastIdxFix →
      b.eval (envAt t (t.rows.length - 1)).loc = 0 :=
    fun b hb => genLastBoundaryZero hsat hlen b (hmem _ hb)
  refine ⟨g _ ?_, g _ ?_⟩ <;>
    (show _ ∈ adjLastIdxFix) <;>
    repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-- **`adjacency_rung2_idx_bound` — THE UNCONDITIONAL INDEX CROWN on the REAL descriptor.** A
`Satisfied2` of the emitted `adjacencyDesc` (which now carries the index fix) forces
`LastRowIdxReconstructed`: `idx_out[last] = idx_in[last] + dir[last]*pow[last]` for both paths — the
published index cannot be decoupled from the committed path's reconstruction. UNCONDITIONAL, no
re-assumed hypothesis. Together with `adjacency_rung2_fixed_closes` (the ordering/hash/consecutive
crown), the two exhaust conjuncts A/B/C of a sound non-membership witness. -/
theorem adjacency_rung2_idx_bound {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t) :
    LastRowIdxReconstructed t :=
  lastRowIdxReconstructed_of_fix hsat hlen adjLastIdxFix_subset

/-! ### §9b — THE LOAD-BEARING witness: `adjLastIdxFix` is exactly what rejects the between-leaf forgery.

A depth-1 shape whose child-ordering, hashing, root pins and consecutiveness ALL genuinely hold, but the
published indices are FORGED away from the reconstruction: the lower leaf `20` genuinely sits at position
`1` (`L_DIR = 1`, right child) and the upper leaf `10` at position `0` (`U_DIR = 0`, left child) — a
genuinely NON-consecutive-ascending pair (`idx_lower = 1 > idx_upper = 0`). The prover publishes the
forged `(idx_lower, idx_upper) = (0, 1)` to FAKE ascending consecutiveness. The index step that would
force `L_IDX_OUT = L_IDX_IN + L_DIR*pow = 1` is VACUOUS on the last row under the transition-only `.gate`
mapping, so the forged trace `Satisfied2`s the CORE descriptor (`adjacencyDescCore`, without the fix) —
yet the published index `0` is NOT the genuine reconstruction `1`. The landed `adjLastIdxFix` is EXACTLY
what catches this: the fixed real `adjacencyDesc` REJECTS the forged trace (its last-row `idxStepBody`
boundary is `0 - 0 - 1*1 = -1 ≠ 0`). The core accepts the forgery, the real emit does not. -/

/-- The forged row: lower leaf `20` genuinely at position 1 (`L_DIR=1`), upper leaf `10` genuinely at
position 0 (`U_DIR=0`), both genuinely dir-ordered children `(10,20)` of the shared root `1020`, but the
published indices FORGED to `L_IDX_OUT=0` / `U_IDX_OUT=1` (fake ascending consecutiveness). -/
private def gRow : Assignment := fun c =>
  if c = L_CUR then 20 else if c = L_SIB then 10 else if c = L_DIR then 1
  else if c = L_LEFT then 10 else if c = L_RIGHT then 20 else if c = L_PAR then 1020
  else if c = U_CUR then 10 else if c = U_SIB then 20
  else if c = U_LEFT then 10 else if c = U_RIGHT then 20 else if c = U_PAR then 1020
  else if c = U_IDX_OUT then 1 else if c = POW then 1 else 0

private def gPub : Assignment := fun k =>
  if k = PI_ROOT then 1020 else if k = PI_LEAF_LOWER then 20
  else if k = PI_LEAF_UPPER then 10 else if k = PI_IDX_UPPER then 1 else 0

private def gTbl : List (List ℤ) :=
  [chipRow mHash [10, 20] (List.replicate 7 0)]

private def gTrace : VmTrace :=
  { rows := [gRow], pub := gPub
    tf := fun tid => match tid with | .poseidon2 => gTbl | _ => [] }

theorem gChipSound : ChipTableSound mHash (gTrace.tf .poseidon2) := by
  intro r hr
  simp only [gTrace, gTbl, List.mem_singleton] at hr
  exact ⟨[10, 20], List.replicate 7 0, by decide, by decide, hr⟩

/-- **The forged trace PROVABLY `Satisfied2`s the fix-less CORE descriptor** — the transition-only index
`.gate` is vacuous on the last row, so the published index lies while every other constraint (ordering,
hash, root pins, consecutiveness) holds. -/
theorem gSatCore :
    Satisfied2 mHash adjacencyDescCore (fun _ => 0) (fun _ => (0, 0)) [] gTrace := by
  have hmemlog : memLog adjacencyDescCore gTrace = [] := rfl
  have hmaplog : mapLog adjacencyDescCore gTrace = [] := rfl
  have hF : (0 == 0) = true := rfl
  have hL : (0 + 1 == gTrace.rows.length) = true := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show gTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    rw [show adjacencyDescCore.constraints = adjacencyConstraintsCore from rfl] at hc
    simp only [adjacencyConstraintsCore, pathBlock, List.cons_append, List.nil_append] at hc
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        copyWindow, Lookup.holdsAt, hF, hL] <;>
      decide
  · intro i _; trivial
  · intro i _ r hr; simp [adjacencyDescCore, adjacencyDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **`LastRowIdxReconstructed` genuinely FAILS on the forged trace** — the lower `idxStepBody` is
`0 - 0 - 1*1 = -1 ≠ 0` (published position `0` ≠ genuine reconstruction `1`). So `LastRowIdxReconstructed`
is NOT derivable from a fix-less `Satisfied2`: it is load-bearing, and the same fact makes the forged
trace FAIL the fixed real `adjacencyDesc`. -/
theorem gForge_not_idxReconstructed : ¬ LastRowIdxReconstructed gTrace := by
  intro h; exact absurd h.1 (by decide)

/-- **THE GATE — the landed fix REJECTS the forged trace.** The forged trace does NOT `Satisfied2` the
real (fixed-emit) `adjacencyDesc`: its added last-row lower `idxStepBody` boundary is `0 - 0 - 1*1 =
-1 ≠ 0`. This is the constraint `adjLastIdxFix` supplies — the between-leaf index forgery is now caught
IN the descriptor. This is the REGRESSION: the trace that WAS `Satisfied2` (of the core) is now NOT. -/
theorem gNotSat :
    ¬ Satisfied2 mHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] gTrace := by
  intro h
  have hmem : VmConstraint2.base (.boundary VmRow.last (idxStepBody L_DIR L_IDX_IN L_IDX_OUT))
      ∈ adjacencyDesc.constraints := by adj_mem
  have h0 := h.rowConstraints 0 (by decide) _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
    show (0 + 1 == gTrace.rows.length) = true from rfl] at h0
  revert h0
  decide

/-- The forged trace witnesses that `adjLastIdxFix` is LOAD-BEARING, not decorative: it `Satisfied2`s
the fix-less CORE descriptor (with a sound chip table) yet BREAKS the no-forgery invariant
`LastRowIdxReconstructed` AND is REJECTED by the fixed real `adjacencyDesc`. The fix is exactly what
turns the accepted between-leaf index forgery into a rejection. -/
theorem gForge_load_bearing :
    Satisfied2 mHash adjacencyDescCore (fun _ => 0) (fun _ => (0, 0)) [] gTrace
    ∧ ChipTableSound mHash (gTrace.tf .poseidon2)
    ∧ ¬ LastRowIdxReconstructed gTrace
    ∧ ¬ Satisfied2 mHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] gTrace :=
  ⟨gSatCore, gChipSound, gForge_not_idxReconstructed, gNotSat⟩

/-! ## §8 — Axiom tripwires. -/

#assert_axioms topLevelOrdered_of_lastRowOrdered
#assert_axioms adjacency_rung2_closes
#assert_axioms lastRowOrdered_of_fix
#assert_axioms adjLastOrderFix_subset
#assert_axioms adjacency_rung2_fixed_closes
#assert_axioms topPair_no_forgery
#assert_axioms cr_carrier_realizable
#assert_axioms wtSat
#assert_axioms wtTrace_rung2_fires
#assert_axioms fSatCore
#assert_axioms fNotSat
#assert_axioms cheat_not_topLevelOrdered
#assert_axioms cheat_not_lastRowOrdered
#assert_axioms cheat_load_bearing
#assert_axioms adjLastIdxFix_subset
#assert_axioms lastRowIdxReconstructed_of_fix
#assert_axioms adjacency_rung2_idx_bound
#assert_axioms gSatCore
#assert_axioms gNotSat
#assert_axioms gForge_not_idxReconstructed
#assert_axioms gForge_load_bearing

end Dregg2.Circuit.Emit.AdjacencyMembershipRung2
