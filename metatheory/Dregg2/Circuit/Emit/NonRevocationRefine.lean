/-
# Dregg2.Circuit.Emit.NonRevocationRefine — the WHOLE-DESCRIPTOR functional-correctness bridge
for the `revocation` family (sorted-tree NON-MEMBERSHIP: prove a queried item is NOT revoked).

## What Rung 0 gave us (`NonRevocationEmit.lean`) and what this file adds

`NonRevocationEmit` byte-pins `nonRevocationDesc` and proves per-GATE lemmas (`cont_body_zero_iff`,
`diffL_body_zero_iff`, `diffR_body_zero_iff`, `rangeLBind_body_zero_iff`, `adj_body_zero_iff`). Each
says one gate polynomial is zero iff its LOCAL integer equation holds. This file proves the missing
WHOLE-DESCRIPTOR bridge: a trace SATISFYING the descriptor (`DescriptorIR2.Satisfied2`) forces the
GENUINE non-membership relation the circuit is meant to compute — welded to the proven semantic
model `Dregg2.Crypto.NonMembership` (`sorted_gap_excludes` / `NonMember`), the SAME combinatorial
keystone `SortedTreeNonMembership` and `AttestedQuery` ride.

## The semantic model this refines (spec_status = SPEC_EXISTS_NO_EMIT)

`Dregg2.Crypto.NonMembership.NonMember spine e := Sorted spine ∧ e ∉ spine` — the trace-independent
functional non-membership relation; and `sorted_gap_excludes` — the unconditional combinatorial core
(two ADJACENT sorted leaves `lo < e < hi` EXCLUDE `e`). We prove `nonRevocationDesc`'s acceptance set
refines this: `Satisfied2 ⟹ NonMember`.

## The refinement (SAT_IMPLIES_SEM) — proven, with ONE precisely-named residual (status PARTIAL)

`nonRevocation_sat_refines` : `Satisfied2 nonRevocationDesc` on an ACTIVE row-0 window
(`1 < rows.length`, so row 0 is non-last where the `.gate`s fire and first where the PI pins fire),
against the NAMED Poseidon2 chip carrier (`ChipTableSound`) and the NAMED range-table carrier
(`RangeTableSound`), FORCES `NonRevocationFragment`:
  * the queried item is pinned to `pi[QUERIED_ITEM]` and the committed root to `pi[ROOT]`;
  * the root is a GENUINE two-level Poseidon2 fold of the adjacent pair
    (`root = hash [hash [L, R], sib]` — level-0 child hash, continuity, level-1 root hash, root pin);
  * the two ordering witnesses satisfy `diff_left = x − L − 1`, `diff_right = R − x − 1`, and the
    ℤ-SOUND half of the half-field bound `diff ≤ HALF_P_MINUS_1`;
  * the neighbor positions are consecutive (`RPOS = LPOS + 1`).

### The residual (status PARTIAL — a real ℤ-vs-BabyBear drift, MODEL-FOUND)

The strict ordering `L < x < R` needs the STRICT-LOWER half `diff ≥ 0`. In the deployed BabyBear
field every wire is a canonical felt (`≥ 0`), and a violated ordering wraps the range-wire past `2^30`
→ UNSAT (`revocation.rs` half-field tooth). But `Satisfied2` evaluates over ℤ with no field
reduction, so the range lookup `RL = HALF_P_MINUS_1 − diff ∈ [0, 2^30)` only bounds `diff ∈
(HALF_P_MINUS_1 − 2^30, HALF_P_MINUS_1]` — the UPPER half is ℤ-sound (recorded in the Fragment), the
LOWER strict bound is NOT ℤ-forced. `FieldCanonicalDiffs` names exactly that gap (`0 ≤ diff_left ∧ 0 ≤
diff_right`), which the field secures; `fragment_strict` derives `L < x < R` from it, and
`nonRevocation_nonmembership` composes with `sorted_gap_excludes` for the full `NonMember` conclusion.
The gap is isolated to one named, currently-un-ℤ-forced fact — exactly `AdjacencyMembershipRefine`'s
shape. On honest witnesses `FieldCanonicalDiffs` HOLDS (the concrete witness below has `diff = 99`).

## Non-vacuity (the anti-scar, IN THIS FILE)
  * `demo_excludes` / `demo_member_not_nonmember` — the SPEC is TRUE and FALSE (`25`... no: `200 ∉
    [100,300]` yet `¬ NonMember [100,300] 100`, a present key is not a non-member).
  * `concrete_sat` — a CONCRETE 2-row trace genuinely SATISFIES the deployed `Satisfied2` (the
    hypothesis is INHABITED, not an empty antecedent) under realizable `ChipTableSound` /
    `RangeTableSound`; `concrete_nonmembership` runs the full bridge on it to prove `200 ∉ [100,300]`.
  * `concrete_fail` — a de-bracketed trace (non-consecutive positions) is genuinely REJECTED (the
    adjacency gate bites): the descriptor separates satisfying from violating witnesses.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The Poseidon2 CR carrier enters ONLY as
the NAMED hypothesis `ChipTableSound hash (tf .poseidon2)` (never as an axiom); the range argument's
faithfulness enters ONLY as the NAMED hypothesis `RangeTableSound`; the exclusion core
`sorted_gap_excludes` is unconditional combinatorics. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.NonRevocationEmit
import Dregg2.Crypto.NonMembership

namespace Dregg2.Circuit.Emit.NonRevocationRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   ChipTableSound chip_lookup_sound chipLookupTuple chipRow CHIP_RATE CHIP_OUT_LANES
   Table memLog mapLog)
open Dregg2.Circuit.Emit.NonRevocationEmit
open Dregg2.Crypto.NonMembership (Sorted Adjacent NonMember sorted_gap_excludes)

set_option autoImplicit false

/-! ## §0 — the range-table soundness carrier (authored; the LogUp range argument's faithfulness).

`Satisfied2` binds only the memory / map-ops tables to the trace (`memTableFaithful` /
`mapTableFaithful`); the range table `tf .range`, like the chip table `tf .poseidon2`, is a SEPARATE
named carrier — the running AIR's own range argument certifies every looked-up wire lies in
`[0, 2^bits)`. This is the twin of `ChipTableSound` for `TableId.range`. -/

/-- **`RangeTableSound bits tbl`** — every row of the range table is a single value in `[0, 2^bits)`.
The faithful denotation of the deployed 30-bit `TableSem::Range` lookup argument. -/
def RangeTableSound (bits : Nat) (tbl : Table) : Prop :=
  ∀ r ∈ tbl, ∃ v : ℤ, r = [v] ∧ 0 ≤ v ∧ v < 2 ^ bits

/-- **THE RANGE LEVER.** Against a sound range table, a looked-up wire lies in `[0, 2^bits)`. -/
theorem range_lookup_sound {bits : Nat} {tbl : Table} (hS : RangeTableSound bits tbl)
    (v : ℤ) (hmem : [v] ∈ tbl) : 0 ≤ v ∧ v < 2 ^ bits := by
  obtain ⟨w, hrow, h0, h1⟩ := hS [v] hmem
  have hvw : v = w := by simpa using hrow
  subst hvw; exact ⟨h0, h1⟩

/-! ## §1 — extracting the row-0 facts from `Satisfied2` (the descriptor's own constraints).

Row 0 is the ACTIVE window when `1 < t.rows.length`: it is non-last (the `.gate`s fire) AND first
(the `.piBinding VmRow.first` pins fire). The lookups fire on every row. -/

/-- Constraint-membership tactic: every constraint we name is literally in `nonRevocationDesc`. -/
local macro "nr_mem" : tactic =>
  `(tactic| (simp [nonRevocationDesc, level0Lookup, level1Lookup, rangeLLookup, rangeRLookup]))

/-- A declared `.gate` fires on the active row 0 (non-last, since `length ≥ 2`): its body vanishes. -/
theorem gateZero0 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (body : EmittedExpr)
    (hmem : VmConstraint2.base (.gate body) ∈ nonRevocationDesc.constraints) :
    body.eval (envAt t 0).loc = 0 := by
  have h0 : 0 < t.rows.length := by omega
  have hlast : (0 + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  have h := hsat.rowConstraints 0 h0 _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h
  exact h

/-- A declared first-row PI binding pins `loc[col] = pub[k]` on row 0. -/
theorem piFirst0 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hlen : 1 < t.rows.length) (col k : Nat)
    (hmem : VmConstraint2.base (.piBinding VmRow.first col k) ∈ nonRevocationDesc.constraints) :
    (envAt t 0).loc col = t.pub k := by
  have h0 : 0 < t.rows.length := by omega
  have h := hsat.rowConstraints 0 h0 _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  exact h (by decide)

/-- A declared Poseidon2 chip lookup, against the NAMED sound chip table, forces the digest column to
carry the genuine hash of the inputs (on row 0). This is where the Poseidon2 CR carrier enters. -/
theorem chip0 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 1 < t.rows.length) (ins : List EmittedExpr) (digestCol : Nat) (lanes : List Nat)
    (hins : ins.length ≤ CHIP_RATE)
    (hmem : VmConstraint2.lookup ⟨TableId.poseidon2, chipLookupTuple ins digestCol lanes⟩
              ∈ nonRevocationDesc.constraints) :
    (envAt t 0).loc digestCol = hash (ins.map (·.eval (envAt t 0).loc)) := by
  have h0 : 0 < t.rows.length := by omega
  have h := hsat.rowConstraints 0 h0 _ hmem
  simp only [VmConstraint2.holdsAt, Lookup.holdsAt] at h
  exact chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t 0).loc ins digestCol lanes hins h

/-- A declared range lookup, against the NAMED sound range table, bounds its wire to `[0, 2^30)`. -/
theorem range0 {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range))
    (hlen : 1 < t.rows.length) (col : Nat)
    (hmem : VmConstraint2.lookup ⟨TableId.range, [.var col]⟩ ∈ nonRevocationDesc.constraints) :
    0 ≤ (envAt t 0).loc col ∧ (envAt t 0).loc col < 2 ^ ORDERING_BITS := by
  have h0 : 0 < t.rows.length := by omega
  have h := hsat.rowConstraints 0 h0 _ hmem
  simp only [VmConstraint2.holdsAt, Lookup.holdsAt, List.map_cons, List.map_nil,
    EmittedExpr.eval] at h
  exact range_lookup_sound hRange _ h

/-! ## §2 — the fully-forced fragment (SAT_IMPLIES_SEM, sound part). -/

/-- **`NonRevocationFragment hash t`** — everything a `Satisfied2` active-row-0 window FORCES: the two
pins, the genuine two-level Poseidon2 root fold of the adjacent pair, the two ordering equations with
the ℤ-sound UPPER half-field bound, and position adjacency. -/
structure NonRevocationFragment (hash : List ℤ → ℤ) (t : VmTrace) : Prop where
  /-- The queried item is pinned to the public no-double-spend input. -/
  queried    : (envAt t 0).loc X = t.pub QUERIED_PI
  /-- The committed root is a GENUINE two-level Poseidon2 fold of the adjacent bracketing pair
  `L, R` under sibling `sib` (level-0 child hash ∘ continuity ∘ level-1 root hash ∘ root pin). -/
  rootHashed : t.pub ROOT_PI
                 = hash [hash [(envAt t 0).loc LEAF_L, (envAt t 0).loc LEAF_R],
                         (envAt t 0).loc SIB1]
  /-- The lower gap witness: `diff_left = x − L − 1`. -/
  diffL      : (envAt t 0).loc DIFF_L = (envAt t 0).loc X - (envAt t 0).loc LEAF_L - 1
  /-- The upper gap witness: `diff_right = R − x − 1`. -/
  diffR      : (envAt t 0).loc DIFF_R = (envAt t 0).loc LEAF_R - (envAt t 0).loc X - 1
  /-- The ℤ-SOUND upper half-field bound on the lower gap (`RL ≥ 0` ⇒ `diff_left ≤ HALF_P_MINUS_1`). -/
  boundL     : (envAt t 0).loc DIFF_L ≤ HALF_P_MINUS_1
  /-- The ℤ-SOUND upper half-field bound on the upper gap. -/
  boundR     : (envAt t 0).loc DIFF_R ≤ HALF_P_MINUS_1
  /-- The two neighbor positions are consecutive (the adjacency side condition). -/
  adjacent   : (envAt t 0).loc RPOS = (envAt t 0).loc LPOS + 1

/-- **`nonRevocation_sat_refines` — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM, sound fragment).**
A `Satisfied2` of `nonRevocationDesc` on an active row-0 window, against the NAMED Poseidon2 chip and
range carriers, forces `NonRevocationFragment`. The one un-ℤ-forced fact (the strict lower bound = the
field-canonicity of the diff wires) is the named residual — see `fragment_strict`. -/
theorem nonRevocation_sat_refines {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range)) :
    NonRevocationFragment hash t := by
  -- the two genuine chip hashes (level-0 child, level-1 root).
  have hp0 := chip0 hsat hChip hlen [.var LEAF_L, .var LEAF_R] PAR0 LEVEL0_LANES (by decide) (by nr_mem)
  have hp1 := chip0 hsat hChip hlen [.var CUR1, .var SIB1] PAR1 LEVEL1_LANES (by decide) (by nr_mem)
  simp only [List.map_cons, List.map_nil, EmittedExpr.eval] at hp0 hp1
  -- the gate equations (through the byte-pinned per-gate lemmas).
  have hcont := (cont_body_zero_iff _).mp (gateZero0 hsat hlen contBody (by nr_mem))
  have hdl := (diffL_body_zero_iff _).mp (gateZero0 hsat hlen diffLBody (by nr_mem))
  have hdr := (diffR_body_zero_iff _).mp (gateZero0 hsat hlen diffRBody (by nr_mem))
  have hrl := (rangeLBind_body_zero_iff _).mp (gateZero0 hsat hlen rangeLBindBody (by nr_mem))
  -- (NonRevocationEmit proves only the L-variant `*_zero_iff`; the R-binding is the structural twin.)
  have hrr : (envAt t 0).loc RR = HALF_P_MINUS_1 - (envAt t 0).loc DIFF_R := by
    have hg := gateZero0 hsat hlen rangeRBindBody (by nr_mem)
    simp only [rangeRBindBody, EmittedExpr.eval] at hg
    omega
  have hadj := (adj_body_zero_iff _).mp (gateZero0 hsat hlen adjBody (by nr_mem))
  -- the two 30-bit range bounds (their ≥ 0 half gives the ℤ-sound upper half-field bound).
  have hRLb := range0 hsat hRange hlen RL (by nr_mem)
  have hRRb := range0 hsat hRange hlen RR (by nr_mem)
  -- the two pins.
  have hqp := piFirst0 hsat hlen X QUERIED_PI (by nr_mem)
  have hrp := piFirst0 hsat hlen PAR1 ROOT_PI (by nr_mem)
  refine
    { queried := hqp
      rootHashed := ?_
      diffL := hdl
      diffR := hdr
      boundL := ?_
      boundR := ?_
      adjacent := hadj }
  · rw [← hrp, hp1, hcont, hp0]
  · have h := hRLb.1; rw [hrl] at h; omega
  · have h := hRRb.1; rw [hrr] at h; omega

/-! ## §3 — the named field-canonicity residual + the full non-membership refinement. -/

/-- **`FieldCanonicalDiffs t` — THE NAMED RESIDUAL.** The strict-lower half of the half-field
ordering: the two diff wires are field-canonical (`≥ 0`). The deployed BabyBear circuit secures this
(every felt is `≥ 0`, and a wrapped diff overflows the range-wire past `2^30` → UNSAT); the ℤ `eval`
of `Satisfied2` omits field reduction, so it is not ℤ-forced. Holds on every honest witness. -/
def FieldCanonicalDiffs (t : VmTrace) : Prop :=
  0 ≤ (envAt t 0).loc DIFF_L ∧ 0 ≤ (envAt t 0).loc DIFF_R

/-- **`fragment_strict`** — the fragment PLUS the named residual yields the STRICT ordering bracket
`L < x < R` (`diff ≥ 0` ⇒ `x ≥ L + 1` and `R ≥ x + 1`). Isolates the whole gap to `FieldCanonicalDiffs`. -/
theorem fragment_strict {hash : List ℤ → ℤ} {t : VmTrace} (frag : NonRevocationFragment hash t)
    (hcanon : FieldCanonicalDiffs t) :
    (envAt t 0).loc LEAF_L < (envAt t 0).loc X ∧ (envAt t 0).loc X < (envAt t 0).loc LEAF_R := by
  obtain ⟨hcl, hcr⟩ := hcanon
  refine ⟨?_, ?_⟩
  · have hd := frag.diffL; omega
  · have hd := frag.diffR; omega

/-- **`nonRevocation_nonmembership` — THE FULL FUNCTIONAL REFINEMENT (SAT_IMPLIES_SEM, welded).**
A `Satisfied2` active-row-0 window, against the two named carriers, the field-canonicity residual,
and the committed sorted spine in which the bracketing leaves `L, R` are ADJACENT (the
`SpineCommits`-style tree↔spine interface, exactly as `SortedTreeNonMembership.nonMembership_sound`
takes it), forces the queried item to be a GENUINE non-member of the committed set — `NonMember spine
x`, welded to `Crypto.NonMembership.sorted_gap_excludes`. The queried item is NOT revoked. -/
theorem nonRevocation_nonmembership {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hRange : RangeTableSound ORDERING_BITS (t.tf .range))
    (hcanon : FieldCanonicalDiffs t)
    (spine : List ℤ)
    (hsorted : Sorted spine)
    (hadj : Adjacent spine ((envAt t 0).loc LEAF_L) ((envAt t 0).loc LEAF_R)) :
    NonMember spine ((envAt t 0).loc X) := by
  have frag := nonRevocation_sat_refines hlen hsat hChip hRange
  obtain ⟨hlo, hhi⟩ := fragment_strict frag hcanon
  exact ⟨hsorted, sorted_gap_excludes spine _ _ _ hsorted hadj hlo hhi⟩

#assert_axioms range_lookup_sound
#assert_axioms nonRevocation_sat_refines
#assert_axioms fragment_strict
#assert_axioms nonRevocation_nonmembership

/-! ## §4 — non-vacuity of the SPEC (the anti-scar: the target is TRUE and FALSE, not a stub). -/

/-- **Witness TRUE — the non-membership spec is INHABITED.** With `100`/`300` adjacent in `[100,300]`
and `100 < 200 < 300`, the combinatorial keystone proves `200 ∉ [100,300]`. -/
theorem demo_excludes : (200 : ℤ) ∉ ([100, 300] : List ℤ) :=
  sorted_gap_excludes [100, 300] 100 300 200 (by simp [Sorted, List.pairwise_cons])
    ⟨[], [], rfl⟩ (by norm_num) (by norm_num)

/-- **Witness FALSE — the spec CONSTRAINS.** A PRESENT key (`100 ∈ [100,300]`) is NOT a non-member,
so `NonMember` is two-valued. A `True` / `P → P` bridge could not separate this. -/
theorem demo_member_not_nonmember : ¬ NonMember ([100, 300] : List ℤ) 100 := by
  rintro ⟨_, hni⟩
  exact hni (by simp)

/-! ## §5 — THE ANTI-SCAR: a CONCRETE trace that genuinely SATISFIES the descriptor (the `Satisfied2`
hypothesis is INHABITED — not an empty/unsatisfiable antecedent), realizable carriers, the full
bridge run end-to-end, and a concrete FAILING trace (the descriptor genuinely REJECTS).

A two-row witness (active row 0 + identical padding row 1): the adjacent leaves `L = 100`, `R = 300`
bracket the queried `x = 200` (`diff_left = diff_right = 99`), at consecutive positions `5, 6`, both
folding to the committed root `hash [hash [100,300], 7]`. -/

/-- A concrete little-endian digit hash (base `10^6`): `[100,300] ↦ 100000300`. -/
private def demoHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000000 + x) 0

/-- The single active assignment. `PAR0 = CUR1 = hash [100,300]`, `PAR1 = hash [PAR0, 7] = root`. -/
private def cRow : Assignment := fun c =>
  if c = X then 200
  else if c = LEAF_L then 100
  else if c = LEAF_R then 300
  else if c = LPOS then 5
  else if c = RPOS then 6
  else if c = DIFF_L then 99
  else if c = DIFF_R then 99
  else if c = RL then 1006632860
  else if c = RR then 1006632860
  else if c = PAR0 then 100000300
  else if c = CUR1 then 100000300
  else if c = SIB1 then 7
  else if c = PAR1 then 100000300000007
  else 0

private def cPub : Assignment := fun k =>
  if k = ROOT_PI then 100000300000007 else if k = QUERIED_PI then 200 else 0

/-- The Poseidon2 chip table: the two genuine node hashes (`[100,300] ↦ PAR0`, `[PAR0,7] ↦ root`). -/
private def cTbl : List (List ℤ) :=
  [ chipRow demoHash [100, 300] (List.replicate 7 0)
  , chipRow demoHash [100000300, 7] (List.replicate 7 0) ]

/-- The range table: the single 30-bit range-wire value `1006632860 = HALF_P_MINUS_1 − 99`. -/
private def cRange : List (List ℤ) := [[1006632860]]

private def cTrace : VmTrace :=
  { rows := [cRow, cRow], pub := cPub
    tf := fun tid => match tid with
      | .poseidon2 => cTbl
      | .range => cRange
      | _ => [] }

/-- The concrete chip table is genuinely SOUND — so `ChipTableSound` is realizable, not just assumed. -/
theorem concrete_chipSound : ChipTableSound demoHash (cTrace.tf .poseidon2) := by
  intro r hr
  simp only [cTrace, cTbl, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[100, 300], List.replicate 7 0, by decide, by decide, rfl⟩
  · exact ⟨[100000300, 7], List.replicate 7 0, by decide, by decide, rfl⟩

/-- The concrete range table is genuinely SOUND — so `RangeTableSound` is realizable, not just assumed. -/
theorem concrete_rangeSound : RangeTableSound ORDERING_BITS (cTrace.tf .range) := by
  intro r hr
  simp only [cTrace, cRange, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl
  exact ⟨1006632860, rfl, by decide, by decide⟩

/-- **The `Satisfied2` HYPOTHESIS IS INHABITED.** The concrete 2-row trace genuinely satisfies the
deployed descriptor's whole denotation — every constraint holds on both row windows (the gates on the
active row 0, vacuous on the padding row 1; the lookups on both), and the (empty) memory/table legs
close. This refutes the vacuity scar: `nonRevocation_sat_refines` is NOT over an empty antecedent. -/
theorem concrete_sat :
    Satisfied2 demoHash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] cTrace := by
  have hmemlog : memLog nonRevocationDesc cTrace = [] := rfl
  have hmaplog : mapLog nonRevocationDesc cTrace = [] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show cTrace.rows.length = 2 from rfl] at hi
    simp only [nonRevocationDesc, level0Lookup, level1Lookup, rangeLLookup, rangeRLookup] at hc
    interval_cases i
    · have hF : ((0 : Nat) == 0) = true := rfl
      have hLf : ((0 : Nat) + 1 == cTrace.rows.length) = false := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hF, hLf] <;>
        decide
    · have hFf : ((1 : Nat) == 0) = false := rfl
      have hL : ((1 : Nat) + 1 == cTrace.rows.length) = true := rfl
      fin_cases hc <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
          EmittedExpr.eval, List.map_cons, List.map_nil, hFf, hL] <;>
        decide
  · intro i _; trivial
  · intro i _ r hr; simp [nonRevocationDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- The named residual HOLDS on the honest witness (`diff_left = diff_right = 99 ≥ 0`). -/
theorem concrete_canon : FieldCanonicalDiffs cTrace := ⟨by decide, by decide⟩

/-- **THE FULL BRIDGE, RUN END-TO-END on the inhabited instance.** All hypotheses jointly hold
(inhabited `Satisfied2`, realizable `ChipTableSound` / `RangeTableSound`, the residual, a concrete
sorted spine with `100`/`300` adjacent), and the descriptor's acceptance PROVES the genuine
non-membership `200 ∉ [100,300]` (`NonMember [100,300] 200`). Not a hollow green. -/
theorem concrete_nonmembership : NonMember ([100, 300] : List ℤ) 200 := by
  have hsorted : Sorted ([100, 300] : List ℤ) := by simp [Sorted, List.pairwise_cons]
  have hadj : Adjacent ([100, 300] : List ℤ)
      ((envAt cTrace 0).loc LEAF_L) ((envAt cTrace 0).loc LEAF_R) := ⟨[], [], rfl⟩
  exact nonRevocation_nonmembership (by decide) concrete_sat concrete_chipSound
    concrete_rangeSound concrete_canon [100, 300] hsorted hadj

/-- The FAILING trace: identical, but the neighbor positions are NON-consecutive (`RPOS = 8`), so the
adjacency gate `RPOS − LPOS − 1 = 8 − 5 − 1 = 2 ≠ 0` bites on the active row 0. -/
private def cRowBad : Assignment := fun c => if c = RPOS then 8 else cRow c

private def cTraceBad : VmTrace := { cTrace with rows := [cRowBad, cRowBad] }

/-- **The descriptor genuinely REJECTS.** No `Satisfied2` exists for the de-bracketed trace: the
adjacency gate is load-bearing, not decorative. -/
theorem concrete_fail :
    ¬ Satisfied2 demoHash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] cTraceBad := by
  intro h
  have hmem : VmConstraint2.base (.gate adjBody) ∈ nonRevocationDesc.constraints := by nr_mem
  have h0 := h.rowConstraints 0 (by decide) _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm,
    show ((0 : Nat) + 1 == cTraceBad.rows.length) = false from rfl] at h0
  revert h0; decide

#assert_axioms concrete_sat
#assert_axioms concrete_nonmembership
#assert_axioms concrete_fail

end Dregg2.Circuit.Emit.NonRevocationRefine
