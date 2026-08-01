/-
# `Dregg2.Circuit.Emit.MemBoundaryTableEmit` — the memory boundary's AIR, AUTHORED IN LEAN.

## What this replaces

`Ir2Air::MemBoundary` (`circuit/src/descriptor_ir2.rs`) is the DECLARED ADDRESS LIST of the
IR-v2 memory argument: it publishes each declared address's initial image at serial 0, consumes
its final image, and SERVES the `ir2_mem_addrs` table that `Ir2Air::Memory` queries for address
closure. Its algebra was hand-authored Rust, which architectural law #1 forbids: *"circuits are
emitted from Lean; Rust only INTERPRETS."*

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `WindowExpr` under an explicit `RowSel`. Nothing in this cutover
hand-writes a Rust constraint, and the `law1_no_new_rust_authored_constraints` baseline for
`descriptor_ir2.rs` goes DOWN.

## The comment-only claim this port turns into theorems

The deleted arm asserted, in prose:

> Strictly increasing declared addresses (⇒ Nodup): on a real→real step the gap
> `(next.addr − addr − 1)` is bound and range-checked.
> Address magnitude bound (so the increasing chain cannot wrap the field):
> `addr_chk = is_real·addr ∈ [0, 2^30)`.

Two claims, and the SECOND is the one that carries the argument. §4 proves both from the gate
equations alone, over ℤ:

  * `addr_strictMono` — the declared real addresses strictly increase.
  * `addrs_distinct_as_felts` — ⚑ and therefore are DISTINCT MOD `p`, which is the form `Nodup`
    has to take for the multiset and lookup arguments (those compare FELTS). Integer
    distinctness alone would not do.
  * `wrap_witness_without_the_magnitude_bound` — ⚠ the FALSE pole. Drop `achk` and keep every
    other gate, and a THREE-ROW witness exists whose "strictly increasing" chain lands back on
    its own first address mod `p`: `0 → 2^30 → p ≡ 0`. Two DECLARED ADDRESSES ARE THE SAME FELT,
    with the gap gate satisfied at every step. So the magnitude gate is load-bearing, and the
    prose sentence "so the increasing chain cannot wrap the field" names a real attack rather
    than a belt-and-braces.

## ⚠ A NAMED RESIDUAL this port makes visible rather than fixes

`MB_ADDR_MULT` — the count the `ir2_mem_addrs` `.provide` leg rides at — is constrained by NO
gate, including on PAD rows, where `MB_ADDR` is also unbounded (`achk = 0·addr = 0` says nothing).
The honest prover writes `mult · (is_real as u32)`, i.e. zero on a pad; the AIR does not force it.
§4c states that as a theorem (a satisfying witness with an arbitrary pad multiplicity) rather than
leaving it implied. What contains it is the `ir2_mem_check` Blum multiset, not this table: an op at
an address with no REAL boundary row has no serial-0 init send to consume, so the multiset cannot
balance however the lookup is served. That is a containment argument about a DIFFERENT AIR, and it
is written here because a reader of this table alone would not find it.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Crypto enters nowhere: this file is the ALGEBRA of
a sorted address list and its integer-faithfulness.
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.Emit.MemBoundaryTableEmit

open Dregg2.Circuit.DescriptorIR2 (WindowExpr)
open Dregg2.Circuit.TableAirIR
  (BusOp BusInteraction TableAir TableGate emitTableAirJson
   v n k eSub eOneMinus gBool gAll gTrans decompGates decompQueries limbGeom decompCols readsCol)

set_option autoImplicit false

/-! ## §1 — The deployed column layout.

Transcribed from `descriptor_ir2.rs`'s `MB_*` constants. The `#guard`s derive each offset from
the one before it, so a layout drift on either side cannot be silent. -/

/-- `MEM_GAP_BITS`. -/
def GAP_BITS : Nat := 30
/-- `2 ^ MEM_GAP_BITS` — the magnitude ceiling both range checks impose. -/
def GAP_CEIL : ℤ := 1073741824
/-- Columns one 30-bit decomposition costs (`decomp_cols(30)`). -/
def DECOMP : Nat := decompCols GAP_BITS

def MB_ADDR : Nat := 0
def MB_INIT_VAL : Nat := 1
def MB_FIN_VAL : Nat := 2
def MB_FIN_SERIAL : Nat := 3
def MB_IS_REAL : Nat := 4
def MB_ADDR_MULT : Nat := 5
def MB_AGAP : Nat := 6
def MB_AGAP_LIMB0 : Nat := 7
def MB_ACHK : Nat := MB_AGAP_LIMB0 + DECOMP
def MB_ACHK_LIMB0 : Nat := MB_ACHK + 1
/-- `MB_WIDTH`. -/
def MB_WIDTH : Nat := MB_ACHK_LIMB0 + DECOMP

-- The deployed numbers, pinned.
#guard DECOMP == 10
#guard limbGeom GAP_BITS == (8, 2)
#guard MB_ACHK == 17
#guard MB_ACHK_LIMB0 == 18
#guard MB_WIDTH == 28
-- `2 ^ 30 < p`: the arithmetic the no-wrap argument in §4 turns on, checked rather than asserted.
#guard GAP_CEIL == 2 ^ GAP_BITS
theorem gap_ceil_lt_p : GAP_CEIL < 2013265921 := by decide

/-- The bus names, verbatim from the Rust `BUS_*` constants. -/
def BUS_BYTE : String := "ir2_byte"
def BUS_MEM_CHECK : String := "ir2_mem_check"
def BUS_MEM_ADDRS : String := "ir2_mem_addrs"

/-! ## §2 — THE TABLE. -/

/-- `is_real`, the row guard. -/
def gReal : WindowExpr := v MB_IS_REAL

/-- The gate list, in the deleted Rust arm's emission order.

Three of the twelve are the interesting ones; the other nine are the two 30-bit decompositions'
booleans and recompositions.

  * (1) `.all` — the row guard is boolean.
  * (2) `.transition` — real rows form a PREFIX: `(1 − real)·next.real = 0`, so a pad may not be
    followed by a real row. This is what makes "the real rows" a contiguous initial segment and
    therefore what makes §4's induction on the index a statement about the whole declared list.
  * (3) `.transition` — the GAP DEFINITION, gated by `next.real`, so the last real→pad step
    imposes nothing. Paired with the range check on `MB_AGAP` (gates 4–7) this is
    "strictly increasing".
  * (8) `.all` — the MAGNITUDE definition `achk = is_real·addr`, range-checked by gates 9–12.
    ⚑ This one is not redundant with (3): see §4b. -/
def memBoundaryGates : List TableGate :=
  [ gAll (gBool MB_IS_REAL)
  , gTrans (.mul (eOneMinus (v MB_IS_REAL)) (n MB_IS_REAL))
  , gTrans (eSub (v MB_AGAP)
      (.mul (n MB_IS_REAL) (eSub (eSub (n MB_ADDR) (v MB_ADDR)) (k 1)))) ] ++
  (decompGates GAP_BITS (v MB_AGAP) MB_AGAP_LIMB0).map gAll ++
  [ gAll (eSub (v MB_ACHK) (.mul gReal (v MB_ADDR))) ] ++
  (decompGates GAP_BITS (v MB_ACHK) MB_ACHK_LIMB0).map gAll

/-- The bus interactions, in the deleted Rust arm's emission order.

  * the two decompositions' limb queries (multiplicity 1, as deployed — `eval_decomp` is the
    UNCOUNTED variant, so a pad row still queries),
  * the Blum legs: the declared address's INIT image published at serial 0, its FINAL image
    consumed, both at `is_real`,
  * and the `ir2_mem_addrs` table this AIR SERVES — `.provide`, at `MB_ADDR_MULT`. -/
def memBoundaryInteractions : List BusInteraction :=
  decompQueries GAP_BITS BUS_BYTE MB_AGAP_LIMB0 (k 1) ++
  decompQueries GAP_BITS BUS_BYTE MB_ACHK_LIMB0 (k 1) ++
  [ ⟨BUS_MEM_CHECK, .send, gReal, [v MB_ADDR, v MB_INIT_VAL, k 0]⟩
  , ⟨BUS_MEM_CHECK, .receive, gReal, [v MB_ADDR, v MB_FIN_VAL, v MB_FIN_SERIAL]⟩
  , ⟨BUS_MEM_ADDRS, .provide, v MB_ADDR_MULT, [v MB_ADDR]⟩ ]

/-- **`memBoundaryTable`** — the memory boundary's AIR, as a Lean object. -/
def memBoundaryTable : TableAir :=
  { name         := "dregg-ir2-mem-boundary-v1"
  , width        := MB_WIDTH
  , gates        := memBoundaryGates
  , interactions := memBoundaryInteractions }

/-! ## §3 — Shape pins.

Counts derived from the layout, not transcribed: `1 + 2 + 4 + 1 + 4 = 12` gates and
`7 + 7 + 3 = 17` interactions. -/

#guard memBoundaryTable.width == 28
#guard memBoundaryTable.gates.length == 12
#guard memBoundaryTable.busCount == 17
#guard memBoundaryTable.busCountOn BUS_BYTE == 14
#guard memBoundaryTable.busCountOn BUS_MEM_CHECK == 2
#guard memBoundaryTable.busCountOn BUS_MEM_ADDRS == 1

-- ⚑ SELECTOR pins. Exactly two gates are transition-scoped (the prefix and the gap definition);
-- everything else is unfiltered. A re-scope in either direction moves one of these.
#guard memBoundaryTable.gateCountSel .transition == 2
#guard memBoundaryTable.gateCountSel .all == 10
#guard memBoundaryTable.gateCountSel .first == 0
#guard memBoundaryTable.gateCountSel .last == 0

-- ⚑ BUS-SIDE pins. This table SERVES `ir2_mem_addrs` and QUERIES `ir2_byte`; it does neither the
-- other way round. `Ir2Air::Memory` is the client of `ir2_mem_addrs`, and a swap here would make
-- the closure argument unsatisfiable in one direction and vacuous in the other.
#guard memBoundaryTable.busCountOp BUS_MEM_ADDRS .provide == 1
#guard memBoundaryTable.busCountOp BUS_MEM_ADDRS .query == 0
#guard memBoundaryTable.busCountOp BUS_BYTE .query == 14
#guard memBoundaryTable.busCountOp BUS_BYTE .provide == 0
#guard memBoundaryTable.busCountOp BUS_MEM_CHECK .send == 1
#guard memBoundaryTable.busCountOp BUS_MEM_CHECK .receive == 1

/-! ## §4 — THE COMMENT-ONLY CLAIM, PROVED.

The gate equations, as ℤ facts about a trace. `real`/`addr`/`agap`/`achk` are the four columns
the argument touches; the decomposition columns enter only through the two RANGE facts, which is
exactly what a byte-limb decomposition buys (and what `ByteTableEmit.value_is_the_row_index`
grounds — the limbs are rows of a table whose values ARE `[0, 16)`). -/

/-- The gate equations of an `n`-row boundary trace, as integer facts. Each field names the gate
it comes from; `gapRange`/`achkRange` are what the 30-bit decompositions deliver. -/
structure BoundaryFacts (m : Nat) where
  real  : Nat → ℤ
  addr  : Nat → ℤ
  agap  : Nat → ℤ
  achk  : Nat → ℤ
  /-- gate (1), `.all`: the row guard is boolean. -/
  realBool   : ∀ i, i < m → real i = 0 ∨ real i = 1
  /-- gate (2), `.transition`: real rows form a prefix. -/
  prefixReal : ∀ i, i + 1 < m → (1 - real i) * real (i + 1) = 0
  /-- gate (3), `.transition`: the gap definition, gated by `next.real`. -/
  gapDef     : ∀ i, i + 1 < m → agap i = real (i + 1) * (addr (i + 1) - addr i - 1)
  /-- gates (4)–(7): the gap is 30-bit. -/
  gapRange   : ∀ i, i < m → 0 ≤ agap i ∧ agap i < GAP_CEIL
  /-- gate (8), `.all`: the magnitude definition. -/
  achkDef    : ∀ i, i < m → achk i = real i * addr i
  /-- gates (9)–(12): the magnitude is 30-bit. -/
  achkRange  : ∀ i, i < m → 0 ≤ achk i ∧ achk i < GAP_CEIL

variable {m : Nat}

/-- The PREFIX property, unpacked: a real row's predecessor is real. -/
theorem real_of_succ (F : BoundaryFacts m) {i : Nat} (h : i + 1 < m)
    (hr : F.real (i + 1) = 1) : F.real i = 1 := by
  have hp := F.prefixReal i h
  rw [hr, mul_one] at hp
  linarith

/-- A real row's address is bounded — `[0, 2^30)`, from `achk = 1·addr`. -/
theorem addr_range (F : BoundaryFacts m) {i : Nat} (h : i < m) (hr : F.real i = 1) :
    0 ≤ F.addr i ∧ F.addr i < GAP_CEIL := by
  have hd := F.achkDef i h
  rw [hr, one_mul] at hd
  rw [← hd]
  exact F.achkRange i h

/-- ONE STEP of the chain: a real successor's address strictly exceeds its predecessor's. -/
theorem addr_step (F : BoundaryFacts m) {i : Nat} (h : i + 1 < m)
    (hr : F.real (i + 1) = 1) : F.addr i < F.addr (i + 1) := by
  have hd := F.gapDef i h
  rw [hr, one_mul] at hd
  have hg := (F.gapRange i (by omega)).1
  rw [hd] at hg
  linarith

/-- ⚑ **THE CLAIM, HALF ONE.** The declared addresses STRICTLY INCREASE along the real prefix.
Stated over all `i < j` rather than adjacent pairs, because that is the form `Nodup` needs. -/
theorem addr_strictMono (F : BoundaryFacts m) :
    ∀ j, ∀ i, i < j → j < m → F.real j = 1 → F.addr i < F.addr j := by
  intro j
  induction j with
  | zero => intro i hij; exact absurd hij (Nat.not_lt_zero i)
  | succ t ih =>
    intro i hij hlt hr
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt' | rfl
    · have hprev : F.real t = 1 := real_of_succ F hlt hr
      exact lt_trans (ih i hlt' (by omega) hprev) (addr_step F hlt hr)
    · exact addr_step F hlt hr

/-- ⚑ **THE CLAIM, HALF TWO — the one the prose sentence is really about.** Distinct real rows
declare addresses that are distinct AS FELTS, not merely as integers. That is the form `Nodup`
must take: the `ir2_mem_addrs` lookup and the `ir2_mem_check` multiset both compare felts, so two
declared addresses congruent mod `p` would be ONE address to every argument built on them, however
far apart they are over ℤ.

The magnitude bound is what buys it — both addresses lie in `[0, 2^30)` and `2^30 < p`, so the
canonical representatives are the integers themselves. §4b shows the bound cannot be dropped. -/
theorem addrs_distinct_as_felts (F : BoundaryFacts m) {i j : Nat}
    (hi : i < m) (hj : j < m) (hij : i ≠ j)
    (hri : F.real i = 1) (hrj : F.real j = 1) :
    ¬ (F.addr i ≡ F.addr j [ZMOD 2013265921]) := by
  -- WLOG `i < j`; the strict chain then separates them over ℤ, and both are canonical.
  have key : ∀ a b : Nat, a < b → b < m → F.real b = 1 → a < m → F.real a = 1 →
      ¬ (F.addr a ≡ F.addr b [ZMOD 2013265921]) := by
    intro a b hab hbm hrb ham hra hcong
    have hlt := addr_strictMono F b a hab hbm hrb
    obtain ⟨ha0, ha1⟩ := addr_range F ham hra
    obtain ⟨hb0, hb1⟩ := addr_range F hbm hrb
    simp only [GAP_CEIL] at ha1 hb1
    have : F.addr a = F.addr b := by
      have h := hcong
      unfold Int.ModEq at h
      rwa [Int.emod_eq_of_lt ha0 (by omega), Int.emod_eq_of_lt hb0 (by omega)] at h
    omega
  rcases Nat.lt_or_ge i j with h | h
  · exact key i j h hj hrj hi hri
  · have hji : j < i := by omega
    intro hc
    exact key j i hji hi hri hj hrj hc.symm

/-! ### §4b — ⚠ THE MAGNITUDE GATE IS LOAD-BEARING: the wrap witness. -/

/-- The three-row wrap witness: addresses `0 → 2^30 → p`, real throughout, with the two gaps
`2^30 − 1` and `p − 2^30 − 1` both inside `[0, 2^30)`. -/
def wrapAddr : Nat → ℤ
  | 0 => 0
  | 1 => 1073741824
  | _ => 2013265921

/-- The gaps that chain it. -/
def wrapGap : Nat → ℤ
  | 0 => 1073741823
  | 1 => 939524096
  | _ => 0

/-- ⚑ **THE FALSE POLE.** Every gate of this table EXCEPT the magnitude one is satisfied by
`wrapAddr`, and its first and last declared addresses are THE SAME FELT. So the strictly
increasing chain has wrapped the field: the `ir2_mem_addrs` table would serve one key twice while
`addr_strictMono` still holds over ℤ, and `Nodup` — the property the memory argument actually
needs — is FALSE.

⚠ Read the direction: this does not exhibit a defect in the deployed AIR, which HAS the magnitude
gate. It exhibits that the gate cannot be dropped, which is the claim the deleted Rust arm made in
a parenthesis ("so the increasing chain cannot wrap the field") and nothing checked. A soundness
story that stopped at `addr_strictMono` would be TRUE and would not imply `Nodup`. -/
theorem wrap_witness_without_the_magnitude_bound :
    -- the gap gate holds at both steps, with both gaps inside the 30-bit range…
    (∀ i, i + 1 < 3 → wrapGap i = 1 * (wrapAddr (i + 1) - wrapAddr i - 1)) ∧
    (∀ i, i < 3 → 0 ≤ wrapGap i ∧ wrapGap i < GAP_CEIL) ∧
    -- …the chain strictly increases over ℤ…
    wrapAddr 0 < wrapAddr 1 ∧ wrapAddr 1 < wrapAddr 2 ∧
    -- …and its endpoints are the SAME FELT.
    wrapAddr 0 ≡ wrapAddr 2 [ZMOD 2013265921] := by
  refine ⟨?_, ?_, by decide, by decide, by decide⟩
  · intro i hi
    have h2 : i < 2 := by omega
    interval_cases i <;> decide
  · intro i hi
    interval_cases i <;> decide

/-- …and the magnitude gate is exactly what refuses it: row 1's address is not `< 2^30`. -/
theorem the_magnitude_gate_refuses_the_wrap : ¬ (wrapAddr 1 < GAP_CEIL) := by decide

/-! ### §4c — ⚠ THE NAMED RESIDUAL: the served multiplicity is un-gated. -/

/-- ⚠ **NO GATE READS `MB_ADDR_MULT`.** Stated as an emission fact rather than as prose: the
column appears in exactly one place, the `.provide` leg's multiplicity, and in no gate body.
A pad row may therefore carry any multiplicity and any address (`achk = 0·addr = 0` bounds
nothing), and SERVE that address to `ir2_mem_addrs`.

What contains it is the `ir2_mem_check` Blum multiset in a DIFFERENT AIR: an op at an address with
no real boundary row has no serial-0 init send to consume, so the multiset cannot balance however
the lookup is served. This theorem is the pointer to that argument, not a substitute for it. -/
theorem addr_mult_is_read_by_no_gate :
    memBoundaryTable.gates.all (fun g => !readsCol g.body MB_ADDR_MULT) = true := by decide

/-- …and the CONTRAST, so the predicate above is not vacuously true of every column: the address
column IS read, by five of the twelve gates. -/
theorem addr_is_read_by_gates :
    (memBoundaryTable.gates.filter (fun g => readsCol g.body MB_ADDR)).length = 2 := by decide

/-! ## §5 — The wire pin. -/

/-- The wire string the Rust interpreter ingests. -/
def MEM_BOUNDARY_JSON : String := emitTableAirJson memBoundaryTable

/-- The emission is not empty and not a stub. -/
theorem memBoundaryTable_is_not_empty : memBoundaryTable.gates ≠ [] := by
  simp [memBoundaryTable, memBoundaryGates]

end Dregg2.Circuit.Emit.MemBoundaryTableEmit
