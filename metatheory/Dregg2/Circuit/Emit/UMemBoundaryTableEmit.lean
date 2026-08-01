/-
# `Dregg2.Circuit.Emit.UMemBoundaryTableEmit` — the GENERAL universal boundary's AIR, in Lean.

## What this replaces

`Ir2Air::UMemBoundary` (`circuit/src/descriptor_ir2.rs`) is the declared `(domain, key)` list of the
universal-memory argument: it publishes each declared cell's INIT image at serial 0, consumes its
FINAL image, serves the `ir2_umem_addrs` closure table, and — unlike the cohort specialization —
carries the machinery that establishes `Nodup` for MORE than one declared address: a DOMAIN-MAJOR
LEXICOGRAPHIC strict-increase comparator over full-felt keys. Its algebra was hand-authored Rust,
which architectural law #1 forbids: *"circuits are emitted from Lean; Rust only INTERPRETS."*

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `WindowExpr` under an explicit `RowSel`. Nothing in this cutover
hand-writes a Rust constraint, and the `law1_no_new_rust_authored_constraints` baseline for
`descriptor_ir2.rs` goes DOWN.

## The comment-only claim this port turns into theorems — and the half it REFUTES

The deleted arm asserted, in prose:

> DOMAIN-MAJOR LEXICOGRAPHIC strict increase ⇒ the declared addresses are Nodup — the hypothesis
> `memcheck_sound` stands on, enforced for full-felt keys. dgap = next.domain − domain is a nibble;
> same_dom is FORCED to the dgap-zero indicator (against next-real); equal domains compare keys.

`Nodup` of the declared list is the hypothesis the ENTIRE universal-memory soundness result stands
on (`UniversalMemory.universal_memory_sound`). §4 proves the mechanism the sentence describes, and
then shows where the argument actually lives:

  * `same_dom_is_the_dgap_zero_indicator` — the inverse-witness pattern really does FORCE
    `same_dom`, in both directions, so a prover cannot choose it. That is what makes "equal domains
    compare keys" a constraint rather than a convention.
  * ⚠ `the_gates_alone_admit_a_duplicate_declared_address` — **THE FALSE POLE, and it is the whole
    point.** The domain-major half of the order rests on `dgap ∈ [0, 16)`, which is a `ir2_byte`
    LOOKUP — a BUS, not a gate. Drop that one leg and the gates admit a THREE-ROW trace with
    domains `1 → 0 → 1`: only the FIRST step needs a wrapped `dgap` (`p − 1`), the second is an
    honest nibble, and rows 0 and 2 declare THE SAME `(domain, key)`. So `Nodup` — the property the
    memory argument needs — is FALSE while every emitted gate holds.

⚑ Read that in the direction it points: it is not a defect in the deployed AIR, which HAS the
nibble lookup. It is that `TableAir.Holds` — the thing this file can prove things about — is
SILENT on the domain-major half of the order, because that half is carried by a bus leg
(`TableAirIR` §3). A soundness story that read the gates as establishing `Nodup` would be resting
on a leg this file does not have; the leg exists, one object out, in the batch's LogUp balance.

## ⚠ A residual, the same one the other two boundaries carry

`UB_ADDR_MULT` — the count the served `ir2_umem_addrs` leg rides at — is read by NO gate, on any
row. `addr_mult_is_read_by_no_gate` states it. Contained by the `ir2_umem_check` multiset (a cell
with no real boundary row has no serial-0 init send to consume), which is a containment about a
different object; `MemBoundaryTableEmit` §4c writes that argument out in full for its twin.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Crypto enters nowhere.
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.Emit.UMemBoundaryTableEmit

open Dregg2.Circuit.DescriptorIR2 (WindowExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.TableAirIR
  (BusOp BusInteraction TableAir TableGate Coherent emitTableAirJson
   v n k eSub eOneMinus gBool gAll gTrans decompCols readsCol
   KEY_LO_BITS KEY_HI_BASE KEY_HI_MAX CANON_COLS CMP_COLS
   canonHi canonLo canonDecompGates canonDecompQueries
   lexLtRowLocalGates lexLtBranchGates lexLtQueries)

set_option autoImplicit false

/-! ## §1 — The deployed column layout.

Transcribed from `descriptor_ir2.rs`'s `UB_*` constants; the `#guard`s derive each offset from the
one before it. ⚑ The first NINE columns are exactly the cohort's layout — `build_traces` writes one
prefix for both tables and pins the agreement with `THE_COHORT_IS_THE_GENERAL_PREFIX`. -/

def UB_DOMAIN : Nat := 0
def UB_KEY : Nat := 1
def UB_INIT_PRESENT : Nat := 2
def UB_INIT_VALUE : Nat := 3
def UB_FIN_PRESENT : Nat := 4
def UB_FIN_VALUE : Nat := 5
def UB_FIN_SERIAL : Nat := 6
def UB_IS_REAL : Nat := 7
def UB_ADDR_MULT : Nat := 8
/-- The canonical key split's 13-column block: `[hi4, lo27 limbs, is15, inv15]`. -/
def UB_KEY_HI4 : Nat := 9
def UB_KEY_LIMB0 : Nat := UB_KEY_HI4 + 1
def UB_KEY_IS15 : Nat := UB_KEY_LIMB0 + decompCols KEY_LO_BITS
def UB_KEY_INV15 : Nat := UB_KEY_IS15 + 1
/-- The domain-gap nibble and the `same_dom` indicator with its inverse witness. -/
def UB_DGAP : Nat := UB_KEY_INV15 + 1
def UB_SAME_DOM : Nat := UB_DGAP + 1
def UB_SAMEDOM_INV : Nat := UB_SAME_DOM + 1
/-- The key comparator's 13-column block: `[s, dhi, dlo, dlo limbs]`. -/
def UB_KCMP_S : Nat := UB_SAMEDOM_INV + 1
def UB_KCMP_DHI : Nat := UB_KCMP_S + 1
def UB_KCMP_DLO : Nat := UB_KCMP_DHI + 1
def UB_KCMP_DLO_LIMB0 : Nat := UB_KCMP_DLO + 1
/-- `UB_WIDTH`. -/
def UB_WIDTH : Nat := UB_KCMP_DLO_LIMB0 + decompCols KEY_LO_BITS

-- The deployed numbers, pinned.
#guard UB_KEY_IS15 == 20
#guard UB_KEY_INV15 == 21
#guard UB_DGAP == 22
#guard UB_SAME_DOM == 23
#guard UB_SAMEDOM_INV == 24
#guard UB_KCMP_S == 25
#guard UB_KCMP_DHI == 26
#guard UB_KCMP_DLO == 27
#guard UB_KCMP_DLO_LIMB0 == 28
#guard UB_WIDTH == 38
-- The two 13-column blocks the shared gadgets fill, against the layout that spaces them.
#guard UB_KEY_HI4 + CANON_COLS == UB_DGAP
#guard UB_KCMP_S + CMP_COLS == UB_WIDTH

/-- `DOMAIN_BOUND`: the shared limb table serves exactly `[0, 16)`, which is what the domain and
`dgap` nibble queries buy. -/
def DOMAIN_BOUND : ℤ := 16

/-- The bus names, verbatim from the Rust `BUS_*` constants. -/
def BUS_BYTE : String := "ir2_byte"
def BUS_UMEM_CHECK : String := "ir2_umem_check"
def BUS_UMEM_ADDRS : String := "ir2_umem_addrs"

/-! ## §2 — THE TABLE. -/

/-- `is_real`, the row guard. -/
def gReal : WindowExpr := v UB_IS_REAL
/-- `same_dom`, the comparator's gate. -/
def gSameDom : WindowExpr := v UB_SAME_DOM
/-- This row's canonical `(hi4, lo27)` split of its key. -/
def aHi : WindowExpr := canonHi UB_KEY_HI4
def aLo : WindowExpr := canonLo (v UB_KEY) UB_KEY_HI4
/-- The NEXT row's split, read from the next row's own columns. ⚠ Only meaningful under
`.transition`; the three branch gates that use it are the only place it appears. -/
def bHi : WindowExpr := n UB_KEY_HI4
def bLo : WindowExpr := eSub (n UB_KEY) (.mul (n UB_KEY_HI4) (k KEY_HI_BASE))

/-- The gate list, in the deleted Rust arm's emission order.

  * (1)–(4) `.all` — the row guard, both presence bits and `same_dom` are boolean.
  * (5) `.transition` — real rows form a PREFIX.
  * (6)(7) `.all` — CANONICAL `none` on both images.
  * (8)–(16) `.all` — the canonical `(hi4, lo27)` split of the key, gated by `is_real`, including
    the `is15 · lo27 = 0` UNIQUENESS tooth that makes the comparator integer-faithful
    (`MapAbsentTableEmit.canonSplit_unique`).
  * (17)(18) `.transition` — the DGAP definition (gated by `next.is_real`, so the last real→pad
    step imposes nothing) and the inverse witness that FORCES `same_dom`.
  * (19) `.all` — `dgap · same_dom = 0`: the other half of the forcing.
  * (20)–(25) `.all` — the comparator's row-local half (branch boolean + `dlo` range).
  * (26)–(28) `.transition` — ⚑ the three BRANCH equations, comparing THIS row's key against its
    SUCCESSOR's. This is the only place `nxt` appears outside the prefix and dgap gates, and it is
    why `lexLtBranchGates` is split out of `lexLtGates` in `TableAirIR` §6b: `MapAbsent` asserts
    the same three under `.all`. -/
def umemBoundaryGates : List TableGate :=
  [ gAll (gBool UB_IS_REAL)
  , gAll (gBool UB_INIT_PRESENT)
  , gAll (gBool UB_FIN_PRESENT)
  , gAll (gBool UB_SAME_DOM)
  , gTrans (.mul (eOneMinus (v UB_IS_REAL)) (n UB_IS_REAL))
  , gAll (.mul (.mul gReal (eOneMinus (v UB_INIT_PRESENT))) (v UB_INIT_VALUE))
  , gAll (.mul (.mul gReal (eOneMinus (v UB_FIN_PRESENT))) (v UB_FIN_VALUE)) ] ++
  (canonDecompGates (v UB_KEY) UB_KEY_HI4 gReal).map gAll ++
  [ gTrans (eSub (v UB_DGAP) (.mul (n UB_IS_REAL) (eSub (n UB_DOMAIN) (v UB_DOMAIN))))
  , gTrans (eSub (.mul (v UB_DGAP) (v UB_SAMEDOM_INV))
      (eSub (n UB_IS_REAL) (v UB_SAME_DOM)))
  , gAll (.mul (v UB_DGAP) (v UB_SAME_DOM)) ] ++
  (lexLtRowLocalGates UB_KCMP_S).map gAll ++
  (lexLtBranchGates aHi aLo bHi bLo UB_KCMP_S gSameDom).map gTrans

/-- The bus interactions, in the deleted Rust arm's emission order.

  * the DOMAIN nibble, the canonical split's `hi4` + limb queries, the DGAP nibble, and the
    comparator's `dhi` + `dlo` limb queries — all at multiplicity 1, the UNCOUNTED variant, so a
    pad row still queries,
  * the two Blum legs at `is_real`,
  * and the `ir2_umem_addrs` closure table this AIR SERVES, at `UB_ADDR_MULT`.

⚑ The DGAP nibble query is the one to look at twice: it is the ONLY thing that bounds the domain
gap, and §4b shows the gates alone admit a duplicate declared address without it. -/
def umemBoundaryInteractions : List BusInteraction :=
  [⟨BUS_BYTE, .query, k 1, [v UB_DOMAIN]⟩] ++
  canonDecompQueries BUS_BYTE UB_KEY_HI4 (k 1) ++
  [⟨BUS_BYTE, .query, k 1, [v UB_DGAP]⟩] ++
  lexLtQueries BUS_BYTE UB_KCMP_S (k 1) ++
  [ ⟨BUS_UMEM_CHECK, .send, gReal,
      [v UB_DOMAIN, v UB_KEY, v UB_INIT_PRESENT, v UB_INIT_VALUE, k 0]⟩
  , ⟨BUS_UMEM_CHECK, .receive, gReal,
      [v UB_DOMAIN, v UB_KEY, v UB_FIN_PRESENT, v UB_FIN_VALUE, v UB_FIN_SERIAL]⟩
  , ⟨BUS_UMEM_ADDRS, .provide, v UB_ADDR_MULT, [v UB_DOMAIN, v UB_KEY]⟩ ]

/-- **`umemBoundaryTable`** — the general universal boundary's AIR, as a Lean object. -/
def umemBoundaryTable : TableAir :=
  { name         := "dregg-ir2-umem-boundary-v1"
  , width        := UB_WIDTH
  , gates        := umemBoundaryGates
  , interactions := umemBoundaryInteractions }

/-! ## §3 — Shape pins.

Counts derived from the layout: `4 + 1 + 2 + 9 + 3 + 6 + 3 = 28` gates and
`1 + 7 + 1 + 7 + 3 = 19` interactions. -/

#guard umemBoundaryTable.width == 38
#guard umemBoundaryTable.gates.length == 28
#guard umemBoundaryTable.busCount == 19
#guard umemBoundaryTable.busCountOn BUS_BYTE == 16
#guard umemBoundaryTable.busCountOn BUS_UMEM_CHECK == 2
#guard umemBoundaryTable.busCountOn BUS_UMEM_ADDRS == 1

-- ⚑ SELECTOR pins. SIX gates are transition-scoped — the real prefix, the dgap definition, the
-- `same_dom` inverse witness, and the comparator's THREE branch equations — and 22 are unfiltered.
-- The comparator split in `TableAirIR` §6b exists precisely so these six are countable here: a
-- re-scope of a branch equation to `.all` would bind the WRAP row (the last row's `next` is row 0)
-- and compare the greatest declared key against the least, which no sorted table means.
#guard umemBoundaryTable.gateCountSel .all == 22
#guard umemBoundaryTable.gateCountSel .transition == 6
#guard umemBoundaryTable.gateCountSel .first == 0
#guard umemBoundaryTable.gateCountSel .last == 0

-- ⚑ BUS-SIDE pins.
#guard umemBoundaryTable.busCountOp BUS_UMEM_ADDRS .provide == 1
#guard umemBoundaryTable.busCountOp BUS_UMEM_ADDRS .query == 0
#guard umemBoundaryTable.busCountOp BUS_BYTE .query == 16
#guard umemBoundaryTable.busCountOp BUS_BYTE .provide == 0
#guard umemBoundaryTable.busCountOp BUS_UMEM_CHECK .send == 1
#guard umemBoundaryTable.busCountOp BUS_UMEM_CHECK .receive == 1

#guard umemBoundaryTable.isRowLocal == false

/-! ## §4 — THE COMMENT-ONLY CLAIM: the forcing PROVED, the ordering REFUTED at the gates. -/

/-! ### §4a — `same_dom` is FORCED, in both directions. -/

/-- The gate equations the `same_dom` forcing turns on, as ℤ facts about ONE transition step.
`dgapNibble` is what the `ir2_byte` query on `UB_DGAP` buys — ⚑ a BUS leg, carried as an explicit
hypothesis rather than smuggled in, which is exactly the split §4b then exploits. -/
structure SameDomStep where
  dgap     : ℤ
  sameDom  : ℤ
  inv      : ℤ
  nextReal : ℤ
  /-- gate (4), `.all`: `same_dom` is boolean. -/
  domBool     : sameDom = 0 ∨ sameDom = 1
  /-- gate (19), `.all`. -/
  gapTimesDom : dgap * sameDom = 0
  /-- gate (18), `.transition`: the inverse witness. -/
  invWitness  : dgap * inv = nextReal - sameDom
  /-- the `ir2_byte` LOOKUP on `UB_DGAP` — a bus, not a gate. -/
  dgapNibble  : 0 ≤ dgap ∧ dgap < DOMAIN_BOUND

/-- ⚑ **THE FORCING, DIRECTION ONE.** `same_dom = 1` ⇒ the domains are equal (`dgap = 0`). Over ℤ
this is immediate from `dgap · same_dom = 0`; the point is that a prover cannot claim "same domain"
while the gap column says otherwise, so the key comparator cannot be switched ON to compare two
rows in different domains. -/
theorem same_dom_forces_zero_gap (S : SameDomStep) (h : S.sameDom = 1) : S.dgap = 0 := by
  have := S.gapTimesDom
  rw [h, mul_one] at this
  exact this

/-- ⚑ **THE FORCING, DIRECTION TWO — the one that matters.** On a step into a REAL successor with
a zero gap, `same_dom` is forced to 1. So a prover cannot switch the key comparator OFF by claiming
"different domain" when the domains are in fact equal — which is what would let two rows in the
same domain declare unordered (and hence possibly EQUAL) keys. -/
theorem zero_gap_forces_same_dom (S : SameDomStep) (h : S.dgap = 0) (hr : S.nextReal = 1) :
    S.sameDom = 1 := by
  have hw := S.invWitness
  rw [h, hr, zero_mul] at hw
  linarith

/-- …and on a step into a PAD the indicator is 0, so the comparator is off at the end of the
declared list — the reason the last real row imposes no ordering on the pads after it. -/
theorem pad_successor_clears_same_dom (S : SameDomStep) (h : S.dgap = 0) (hr : S.nextReal = 0) :
    S.sameDom = 0 := by
  have hw := S.invWitness
  rw [h, hr, zero_mul] at hw
  linarith

/-! ### §4b — ⚠ THE FALSE POLE: the gates alone do NOT give `Nodup`.

The domain-major half of the order is `dgap = next.domain − domain ∈ [0, 16)`, and the range half
of that is an `ir2_byte` LOOKUP. `TableAir.Holds` is silent about bus legs (`TableAirIR` §3), so the
gates admit a `dgap` of `p − 1` — a domain DECREASE — and three rows suffice to turn that into a
duplicated declared address. -/

/-- One row of the wrap trace: a real declared cell at `(domain, p − 1)`, canonically split at the
top nibble (`hi4 = 15`, `lo27 = 0`, `is15 = 1`, `inv15 = 0` — the one split where the `is15` tooth
costs no inverse witness), with `same_dom = 0` so the key comparator is gated off. -/
def wrapLoc (domain dgap sdinv : ℤ) : Nat → ℤ := fun c =>
  if c = UB_DOMAIN then domain
  else if c = UB_KEY then 2013265920
  else if c = UB_IS_REAL then 1
  else if c = UB_ADDR_MULT then 1
  else if c = UB_KEY_HI4 then 15
  else if c = UB_KEY_IS15 then 1
  else if c = UB_DGAP then dgap
  else if c = UB_SAMEDOM_INV then sdinv
  else 0

/-- Domains `1 → 0 → 1`, all real, all declaring key `p − 1`.

Row 0's step DOWN needs `dgap = 0 − 1 ≡ p − 1` with inverse witness `p − 1` (`(p−1)² ≡ 1`); row 1's
step back UP needs `dgap = 1`, an honest nibble, with inverse witness `1`. So **exactly one of the
two gaps is out of range** — and it is out of range only against a LOOKUP. -/
def wrapTrace : List VmRowEnv :=
  [ ⟨wrapLoc 1 2013265920 2013265920, wrapLoc 0 1 1, fun _ => 0⟩
  , ⟨wrapLoc 0 1 1, wrapLoc 1 0 0, fun _ => 0⟩
  , ⟨wrapLoc 1 0 0, fun _ => 0, fun _ => 0⟩ ]

/-- The trace is COHERENT: each window's `nxt` IS its successor's `loc`, by construction. -/
theorem wrapTrace_coherent : Coherent wrapTrace := by
  intro i h
  have hi : i < 2 := by simp only [wrapTrace, List.length_cons, List.length_nil] at h; omega
  interval_cases i <;> rfl

/-- ⚑ **THE REFUTATION.** Every emitted gate holds on all three windows, and rows 0 and 2 declare
THE SAME `(domain, key)`. So `Nodup` — the hypothesis `UniversalMemory.universal_memory_sound`
stands on, and the property this table's whole comparator apparatus exists to establish — is FALSE
of a trace this AIR's GATES accept.

⚠ The direction, said plainly. This is NOT a defect the deployed prover admits: row 0's `dgap` is
`p − 1`, and the `ir2_byte` query on `UB_DGAP` bounds it to `[0, 16)`. What the theorem shows is
that the bound is a BUS leg, so `TableAir.Holds` — the only thing a single-table theorem can talk
about — does not reach it. Reading the 28 gates and concluding "the declared addresses are Nodup"
is the mistake this exhibits; the missing step is a LogUp balance in the assembled batch.

ⓘ Note what the witness does NOT need: the key comparator is never switched off illegitimately
(`same_dom` is genuinely 0 at both steps, forced by §4a), and the canonical split is honest at
every row. The ONLY thing out of place is one nibble. -/
theorem the_gates_alone_admit_a_duplicate_declared_address :
    umemBoundaryTable.Holds wrapTrace ∧
    -- rows 0 and 2 declare THE SAME (domain, key)…
    wrapTrace[0].loc UB_DOMAIN = wrapTrace[2].loc UB_DOMAIN ∧
    wrapTrace[0].loc UB_KEY = wrapTrace[2].loc UB_KEY ∧
    wrapTrace[0].loc UB_IS_REAL = 1 ∧ wrapTrace[2].loc UB_IS_REAL = 1 ∧
    -- …and the ONLY thing out of range is row 0's domain gap, which a LOOKUP bounds.
    ¬ (wrapTrace[0].loc UB_DGAP < DOMAIN_BOUND) ∧
    wrapTrace[1].loc UB_DGAP < DOMAIN_BOUND := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- NON-VACUITY, so the refutation above is not read as "these gates decide nothing": an HONEST
two-row window — the same declared cells with an in-range gap of 1 and a genuinely different key —
is accepted, and the SAME window with `same_dom` flipped to 1 is REFUSED by the `dgap · same_dom`
gate. The forcing of §4a is a gate, and it bites. -/
theorem flipping_same_dom_against_a_nonzero_gap_is_refused :
    umemBoundaryTable.RowHolds wrapTrace[1] false false ∧
    ¬ umemBoundaryTable.RowHolds
        ⟨fun c => if c = UB_SAME_DOM then 1 else wrapLoc 0 1 1 c, wrapLoc 1 0 0, fun _ => 0⟩
        false false := by
  refine ⟨by decide, by decide⟩

/-! ### §4c — ⚠ The served multiplicity, un-gated (the residual all three boundaries share). -/

/-- ⚠ **NO GATE READS `UB_ADDR_MULT`.** Same shape as `MemBoundaryTableEmit` §4c and
`UMemBoundaryCohortTableEmit` §4b: the column appears only in the `.provide` leg's multiplicity.
Contained by the `ir2_umem_check` multiset, which is a different object. -/
theorem addr_mult_is_read_by_no_gate :
    umemBoundaryTable.gates.all (fun g => !readsCol g.body UB_ADDR_MULT) = true := by decide

/-- …and the CONTRAST, so the predicate is not vacuously true of every column. ⓘ MEASURED, and the
number is smaller than a reader would guess: the KEY column is read by exactly THREE gates — the
whole-value recomposition of its canonical split, the `is15 · lo27 = 0` uniqueness tooth, and the
comparator's low-word branch. Everything else about the key is mediated by its `(hi4, lo27)`
BLOCK, which is the point of splitting it: the ordering argument never touches the raw felt. -/
theorem key_is_read_by_three_gates :
    (umemBoundaryTable.gates.filter (fun g => readsCol g.body UB_KEY)).length = 3 := by decide

/-- ⚑ …and the DGAP column is read by exactly three gates — its own definition, the inverse
witness, and the `dgap · same_dom` leg — and by NONE of them is it bounded. The bound is the
sixteenth `ir2_byte` query. Stated as an emission fact because §4b turns on it. -/
theorem dgap_is_read_by_three_gates_and_bounded_by_none :
    (umemBoundaryTable.gates.filter (fun g => readsCol g.body UB_DGAP)).length = 3 := by decide

/-! ## §5 — The wire pin. -/

/-- The wire string the Rust interpreter ingests. -/
def UMEM_BOUNDARY_JSON : String := emitTableAirJson umemBoundaryTable

/-- The emission is not empty and not a stub. -/
theorem umemBoundaryTable_is_not_empty : umemBoundaryTable.gates ≠ [] := by
  simp [umemBoundaryTable, umemBoundaryGates]

end Dregg2.Circuit.Emit.UMemBoundaryTableEmit
