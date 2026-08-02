/-
# `Dregg2.Circuit.Emit.MemoryTableEmit` — the flat memory op table's AIR, AUTHORED IN LEAN.

## What this replaces

`Ir2Air::Memory` (`circuit/src/descriptor_ir2.rs`) is the OP LOG of the IR-v2 memory argument: one
row per memory operation, carrying the address, the value written/read, the CLAIMED prior image and
its serial. It publishes each op's own image on the `ir2_mem_check` Blum multiset, consumes the
prior one it claims, receives the gathered `ir2_mem_log`, and QUERIES `ir2_mem_addrs` — the table
`MemBoundaryTableEmit` serves — for address closure. Its algebra was hand-authored Rust, which
architectural law #1 forbids: *"circuits are emitted from Lean; Rust only INTERPRETS."*

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `TExpr` under an explicit `RowSel`. Nothing in this cutover
hand-writes a Rust constraint, and the `law1_no_new_rust_authored_constraints` baseline for
`descriptor_ir2.rs` goes DOWN.

## The comment-only claim this port turns into theorems — and its FALSE half

The deleted arm asserted, in prose:

> Positional serials: 1, 2, 3, … (Lean: op i carries serial i+1).
> Read discipline: a read returns exactly its claimed previous value.
> `prev_serial < serial` (Disciplined): gap = is_real·(serial − 1 − prev_serial)
> and gap ∈ [0, 2^30) by byte decomposition.

Those three sentences are exactly `MemoryChecking.Disciplined`'s two conjuncts plus the serial
convention they are stated against. §4 proves the first two and REFUTES the third as stated:

  * `serial_is_positional` — from the emitted `.first` anchor and `.transition` increment, under
    `Coherent`, row `i` carries serial `i + 1`. This is the half `Disciplined`'s index counts.
  * `read_returns_its_claimed_value` — the second conjunct of `Disciplined`, exactly.
  * `prev_serial_le_index` — over ℤ, `prevSerial i ≤ i`, i.e. `prevSerial i < serial i`. TRUE of
    the LIFT.
  * ⚠ `wrapped_prev_serial_satisfies_every_gate` — the FALSE pole, and the load-bearing half.
    ⚑ **THERE IS NO MAGNITUDE GATE ON `MEM_PREV_SERIAL`.** `MemBoundary` bounds its declared
    address with `achk = is_real·addr ∈ [0, 2^30)`; this table has NO counterpart for the claimed
    prior serial. The gap gate *defines* `prev_serial = serial − 1 − gap` in the FIELD, so the
    admissible set at serial `s` is `{s−1, s−2, …, s−2^30} mod p` — which for a small `s` wraps
    and contains felts arbitrarily close to `p`. A ONE-ROW window with `serial = 1`, `gap = 5` and
    `prev_serial = p − 5` satisfies EVERY emitted gate (proved at `RowHolds`, on the emitted
    object, not on a transcription) while claiming a prior serial ABOVE `2^30` — so "prev_serial <
    serial" is a property of the honest prover's chosen lift, not a fact the row algebra decides.

## ⚠ The containment, which lives in a DIFFERENT object

What refuses the wrapped witness is the `ir2_mem_check` Blum multiset, not this table: the only
tuples ever PUBLISHED at a serial are this table's own positional `serial` values and the memory
boundary's serial-0 init images, so a receive at `p − 5` has nothing to consume and the permutation
cannot balance. That is a property of the assembled instance family — precisely the half
`TableAir.Holds` does not speak about (`TableAirIR` §3) — and it is written down here because a
reader of this table alone would conclude the gap gate bounds the claimed serial. It does not; it
DEFINES it.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Crypto enters nowhere: this file is the ALGEBRA of an
op log and the integer-faithfulness of its two discipline claims.
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.Emit.MemoryTableEmit

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.TableAirIR
  (TExpr BusOp BusInteraction TableAir TableGate Coherent emitTableAirJson
   v n k eSub eOneMinus gBool gAll gFirst gTrans decompGates decompQueries limbGeom decompCols)

set_option autoImplicit false

/-! ## §1 — The deployed column layout.

Transcribed from `descriptor_ir2.rs`'s `MEM_*` constants. The `#guard`s derive each offset from
the one before it, so a layout drift on either side cannot be silent. -/

/-- `MEM_GAP_BITS`. Shared with the memory boundary, which is why the decomposition emitter is
`TableAirIR`'s rather than a per-table copy. -/
def GAP_BITS : Nat := 30
/-- `2 ^ MEM_GAP_BITS` — the ceiling the serial-gap range check imposes. -/
def GAP_CEIL : ℤ := 1073741824
/-- Columns one 30-bit decomposition costs (`decomp_cols(30)`). -/
def DECOMP : Nat := decompCols GAP_BITS

def MEM_ADDR : Nat := 0
def MEM_VALUE : Nat := 1
def MEM_PREV_VALUE : Nat := 2
def MEM_PREV_SERIAL : Nat := 3
def MEM_KIND : Nat := 4
def MEM_SERIAL : Nat := 5
def MEM_IS_REAL : Nat := 6
def MEM_GAP : Nat := 7
def MEM_GAP_LIMB0 : Nat := 8
/-- `MEM_WIDTH`. -/
def MEM_WIDTH : Nat := MEM_GAP_LIMB0 + DECOMP

-- The deployed numbers, pinned.
#guard DECOMP == 10
#guard limbGeom GAP_BITS == (8, 2)
#guard MEM_WIDTH == 18
#guard GAP_CEIL == 2 ^ GAP_BITS
theorem gap_ceil_lt_p : GAP_CEIL < 2013265921 := by decide

/-- The bus names, verbatim from the Rust `BUS_*` constants. -/
def BUS_BYTE : String := "ir2_byte"
def BUS_MEM_LOG : String := "ir2_mem_log"
def BUS_MEM_CHECK : String := "ir2_mem_check"
def BUS_MEM_ADDRS : String := "ir2_mem_addrs"

/-! ## §2 — THE TABLE. -/

/-- `is_real`, the row guard. -/
def gReal : TExpr := v MEM_IS_REAL

/-- The gate list, in the deleted Rust arm's emission order.

  * (1)(2) `.all` — the row guard and the op KIND are boolean (`kind = 1` is a write).
  * (3) `.transition` — real rows form a PREFIX, so the op log is a contiguous initial segment.
  * (4) `.first` / (5) `.transition` — the POSITIONAL serial chain: row 0 carries serial 1 and
    each successor carries one more. ⚑ `.first`+`.transition` and not `.all`: on the last row p3's
    `nxt` is the WRAP row, where the increment is false for every height above 1.
  * (6) `.all` — READ DISCIPLINE: on a real read row the returned value IS the claimed prior one.
  * (7) `.all` — the SERIAL GAP definition, range-checked by gates (8)–(11). ⚠ This DEFINES
    `prev_serial`; it does not bound it (§4c). -/
def memoryGates : List TableGate :=
  [ gAll (gBool MEM_IS_REAL)
  , gAll (gBool MEM_KIND)
  , gTrans (.mul (eOneMinus (v MEM_IS_REAL)) (n MEM_IS_REAL))
  , gFirst (eSub (v MEM_SERIAL) (k 1))
  , gTrans (eSub (eSub (n MEM_SERIAL) (v MEM_SERIAL)) (k 1))
  , gAll (.mul (.mul gReal (eOneMinus (v MEM_KIND)))
      (eSub (v MEM_VALUE) (v MEM_PREV_VALUE)))
  , gAll (eSub (v MEM_GAP)
      (.mul gReal (eSub (eSub (v MEM_SERIAL) (k 1)) (v MEM_PREV_SERIAL)))) ] ++
  (decompGates GAP_BITS (v MEM_GAP) MEM_GAP_LIMB0).map gAll

/-- The bus interactions, in the deleted Rust arm's emission order.

  * the gap decomposition's limb queries (multiplicity 1, as deployed — `eval_decomp` is the
    UNCOUNTED variant, so a pad row still queries),
  * the gathered op log (`memTableFaithful`), at `is_real`,
  * the two Blum legs: this op PUBLISHES its own image at its own serial and CONSUMES the prior
    image it claims,
  * and the ADDRESS CLOSURE query against the table `MemBoundaryTableEmit` SERVES. ⚑ `.query`,
    not `.provide`: this table is the CLIENT of `ir2_mem_addrs`. -/
def memoryInteractions : List BusInteraction :=
  decompQueries GAP_BITS BUS_BYTE MEM_GAP_LIMB0 (k 1) ++
  [ ⟨BUS_MEM_LOG, .receive, gReal,
      [v MEM_ADDR, v MEM_VALUE, v MEM_PREV_VALUE, v MEM_PREV_SERIAL, v MEM_KIND]⟩
  , ⟨BUS_MEM_CHECK, .send, gReal, [v MEM_ADDR, v MEM_VALUE, v MEM_SERIAL]⟩
  , ⟨BUS_MEM_CHECK, .receive, gReal, [v MEM_ADDR, v MEM_PREV_VALUE, v MEM_PREV_SERIAL]⟩
  , ⟨BUS_MEM_ADDRS, .query, gReal, [v MEM_ADDR]⟩ ]

/-- **`memoryTable`** — the flat memory op table's AIR, as a Lean object. -/
def memoryTable : TableAir :=
  { name         := "dregg-ir2-memory-v1"
  , width        := MEM_WIDTH
  , defs         := []
  , gates        := memoryGates
  , interactions := memoryInteractions }

/-! ## §3 — Shape pins.

Counts derived from the layout, not transcribed: `2 + 1 + 2 + 1 + 1 + 4 = 11` gates and
`7 + 4 = 11` interactions. -/

#guard memoryTable.width == 18
#guard memoryTable.gates.length == 11
#guard memoryTable.busCount == 11
#guard memoryTable.busCountOn BUS_BYTE == 7
#guard memoryTable.busCountOn BUS_MEM_LOG == 1
#guard memoryTable.busCountOn BUS_MEM_CHECK == 2
#guard memoryTable.busCountOn BUS_MEM_ADDRS == 1

-- ⚑ SELECTOR pins. Exactly two gates are transition-scoped (the real prefix and the serial
-- increment) and exactly ONE is first-scoped (the serial anchor). A re-scope in either direction
-- moves one of these, and by `TableGate.transition_weakens` a drift toward `.transition` accepts
-- STRICTLY MORE while leaving the algebra byte-identical.
#guard memoryTable.gateCountSel .all == 8
#guard memoryTable.gateCountSel .transition == 2
#guard memoryTable.gateCountSel .first == 1
#guard memoryTable.gateCountSel .last == 0

-- ⚑ BUS-SIDE pins. This table QUERIES `ir2_mem_addrs` and `ir2_byte`; it SERVES nothing. The
-- boundary is the server of `ir2_mem_addrs` (`MemBoundaryTableEmit` pins the other side), and a
-- swap here would make the address-closure argument unsatisfiable in one direction and vacuous in
-- the other — with no gate involved and therefore nothing a mutation sweep could see.
#guard memoryTable.busCountOp BUS_MEM_ADDRS .query == 1
#guard memoryTable.busCountOp BUS_MEM_ADDRS .provide == 0
#guard memoryTable.busCountOp BUS_BYTE .query == 7
#guard memoryTable.busCountOp BUS_BYTE .provide == 0
-- The Blum pair: this op PUBLISHES its own image and CONSUMES the prior one. A swap here reverses
-- the whole read-consistency argument.
#guard memoryTable.busCountOp BUS_MEM_CHECK .send == 1
#guard memoryTable.busCountOp BUS_MEM_CHECK .receive == 1
#guard memoryTable.busCountOp BUS_MEM_LOG .receive == 1
#guard memoryTable.busCountOp BUS_MEM_LOG .send == 0

-- The table is NOT row-local — the serial chain reads `nxt` — which is precisely why it could not
-- be ported against the first-pass IR. Pinned so the property is checkable rather than implied by
-- the selector counts above.
#guard memoryTable.isRowLocal == false

/-! ## §4 — THE COMMENT-ONLY CLAIMS, PROVED — and the third one REFUTED.

§4a takes the positional-serial claim straight off the EMITTED gates under `Coherent` (the same
shape `ByteTableEmit.value_is_the_row_index` proves for the limb table). §4b states the remaining
gate equations as ℤ facts and derives both conjuncts of `MemoryChecking.Disciplined`. §4c exhibits
the witness that refutes the third sentence AS STATED, on the emitted object. -/

/-! ### §4a — The serial column IS the positional index (+1). -/

/-- The first-row gate, unpacked: row 0 carries serial 1. -/
theorem first_row_serial_is_one {rows : List VmRowEnv}
    (hh : memoryTable.Holds rows) (h : 0 < rows.length) :
    rows[0].loc MEM_SERIAL ≡ 1 [ZMOD 2013265921] := by
  have hg := hh 0 h ⟨.first, eSub (v MEM_SERIAL) (k 1)⟩
    (by simp [memoryTable, memoryGates, gFirst])
  simp only [TableGate.holdsAt] at hg
  have hz := hg (by simp)
  simp only [eSub, v, k, TExpr.evalWith] at hz
  unfold Int.ModEq at hz ⊢
  omega

/-- The transition gate, unpacked: on any non-final row the NEXT window's serial is one more. -/
theorem serial_step {rows : List VmRowEnv}
    (hh : memoryTable.Holds rows) (i : Nat) (hlt : i < rows.length) (h : i + 1 < rows.length) :
    rows[i].nxt MEM_SERIAL ≡ rows[i].loc MEM_SERIAL + 1 [ZMOD 2013265921] := by
  have hg := hh i hlt ⟨.transition, eSub (eSub (n MEM_SERIAL) (v MEM_SERIAL)) (k 1)⟩
    (by simp [memoryTable, memoryGates, gTrans])
  simp only [TableGate.holdsAt] at hg
  have hz := hg (by simp; omega)
  simp only [eSub, v, n, k, TExpr.evalWith] at hz
  unfold Int.ModEq at hz ⊢
  omega

/-- ⚑ **THE SERIAL CONVENTION, PROVED.** On a COHERENT accepting trace row `i` carries serial
`i + 1` — the sentence the deleted arm parenthesised as "(Lean: op i carries serial i+1)", and the
index `MemoryChecking.DisciplinedFrom` counts against.

⚠ `Coherent` is not decoration: without it `rows[i].nxt` is an unconstrained function and the
increment chain says nothing about `rows[i+1]`, so the whole claim would be about a machine that
does not exist. -/
theorem serial_is_positional {rows : List VmRowEnv}
    (hc : Coherent rows) (hh : memoryTable.Holds rows) :
    ∀ i, ∀ h : i < rows.length,
      rows[i].loc MEM_SERIAL ≡ (i : ℤ) + 1 [ZMOD 2013265921] := by
  intro i
  induction i with
  | zero => intro h; simpa using first_row_serial_is_one hh h
  | succ m ih =>
    intro h
    have hm : m + 1 < rows.length := h
    have hlt : m < rows.length := by omega
    have hstep := serial_step hh m hlt hm
    have hcoh : rows[m].nxt = rows[m + 1].loc := hc m hm
    rw [hcoh] at hstep
    have hfin : rows[m + 1].loc MEM_SERIAL ≡ ((m : ℤ) + 1) + 1 [ZMOD 2013265921] :=
      hstep.trans (Int.ModEq.add_right 1 (ih (by omega)))
    push_cast
    simpa [add_assoc] using hfin

/-! ### §4b — The two conjuncts of `Disciplined`, over ℤ. -/

/-- The gate equations of an `m`-row op-log trace, as integer facts. Each field names the gate it
comes from; `gapRange` is what the 30-bit decomposition (gates 8–11) delivers. -/
structure MemoryFacts (m : Nat) where
  real       : Nat → ℤ
  kind       : Nat → ℤ
  value      : Nat → ℤ
  prevValue  : Nat → ℤ
  serial     : Nat → ℤ
  prevSerial : Nat → ℤ
  gap        : Nat → ℤ
  /-- gate (1), `.all`. -/
  realBool   : ∀ i, i < m → real i = 0 ∨ real i = 1
  /-- gate (2), `.all`. -/
  kindBool   : ∀ i, i < m → kind i = 0 ∨ kind i = 1
  /-- gate (3), `.transition`: real rows form a prefix. -/
  prefixReal : ∀ i, i + 1 < m → (1 - real i) * real (i + 1) = 0
  /-- gate (4), `.first`. -/
  serialOne  : 0 < m → serial 0 = 1
  /-- gate (5), `.transition`. -/
  serialStep : ∀ i, i + 1 < m → serial (i + 1) - serial i - 1 = 0
  /-- gate (6), `.all`: a real read returns its claimed prior value. -/
  readDisc   : ∀ i, i < m → real i * (1 - kind i) * (value i - prevValue i) = 0
  /-- gate (7), `.all`: the serial-gap DEFINITION. -/
  gapDef     : ∀ i, i < m → gap i = real i * (serial i - 1 - prevSerial i)
  /-- gates (8)–(11): the gap is 30-bit. -/
  gapRange   : ∀ i, i < m → 0 ≤ gap i ∧ gap i < GAP_CEIL

variable {m : Nat}

/-- The PREFIX property, unpacked: a real row's predecessor is real. -/
theorem real_of_succ (F : MemoryFacts m) {i : Nat} (h : i + 1 < m)
    (hr : F.real (i + 1) = 1) : F.real i = 1 := by
  have hp := F.prefixReal i h
  rw [hr, mul_one] at hp
  linarith

/-- The serial chain over ℤ: row `i` carries serial `i + 1`. The lift of §4a. -/
theorem serial_eq_index (F : MemoryFacts m) : ∀ i, i < m → F.serial i = (i : ℤ) + 1 := by
  intro i
  induction i with
  | zero => intro h; simpa using F.serialOne h
  | succ t ih =>
    intro h
    have hs := F.serialStep t h
    have := ih (by omega)
    push_cast
    linarith

/-- ⚑ **`Disciplined`, CONJUNCT TWO.** A real READ row (`kind = 0`) returns exactly the value it
claims was there. This is `MemoryChecking.DisciplinedFrom`'s `op.kind = .read → op.val =
op.prevVal`, from the gate equation alone. -/
theorem read_returns_its_claimed_value (F : MemoryFacts m) {i : Nat} (h : i < m)
    (hr : F.real i = 1) (hk : F.kind i = 0) : F.value i = F.prevValue i := by
  have hd := F.readDisc i h
  rw [hr, hk] at hd
  simp only [one_mul, sub_zero] at hd
  linarith

/-- ⚑ **`Disciplined`, CONJUNCT ONE — OF THE LIFT.** Over ℤ the claimed prior serial is at most
the row index, i.e. strictly below the op's own serial `i + 1`. That is exactly
`op.prevSerial < n + 1`.

⚠ Read the quantifier: this is a statement about the ℤ-valued `prevSerial` field of `MemoryFacts`,
i.e. about the lift the honest prover writes. §4c shows the FELT is not so constrained. -/
theorem prev_serial_le_index (F : MemoryFacts m) {i : Nat} (h : i < m) (hr : F.real i = 1) :
    F.prevSerial i ≤ (i : ℤ) ∧ F.prevSerial i < F.serial i := by
  have hd := F.gapDef i h
  rw [hr, one_mul] at hd
  have hg := (F.gapRange i h).1
  rw [hd] at hg
  have hs := serial_eq_index F i h
  constructor <;> linarith

/-! ### §4c — ⚠ THE FALSE POLE: the gap gate DEFINES the claimed serial, it does not BOUND it.

`MemBoundaryTableEmit` bounds its declared address with a dedicated magnitude gate
(`achk = is_real·addr ∈ [0, 2^30)`) and §4b of that file shows the bound cannot be dropped. This
table has NO counterpart for `MEM_PREV_SERIAL`. The gap gate reads

    gap = is_real · (serial − 1 − prev_serial)     in the FIELD,

so at `serial = s` the admissible prior serials are `{s−1, …, s−2^30} mod p`, which for a small `s`
WRAPS. The witness below is a one-row window at `serial = 1` claiming a prior serial of `p − 5`. -/

/-- `p − 5`: the wrapped prior serial. Above `2^30`, and therefore above every serial this table
can ever publish. -/
def WRAP_PREV : ℤ := 2013265916

/-- A ONE-ROW window (first AND last, so the two transition gates are vacuous and the wrap row
never enters) claiming a prior serial of `p − 5` at its own serial 1, with the 5-gap honestly
decomposed: limb 0 is 5, every other limb and both top bits are 0. -/
def wrapRow : VmRowEnv :=
  ⟨fun c =>
      if c = MEM_PREV_SERIAL then WRAP_PREV
      else if c = MEM_SERIAL then 1
      else if c = MEM_IS_REAL then 1
      else if c = MEM_GAP then 5
      else if c = MEM_GAP_LIMB0 then 5
      else 0
  , fun _ => 0, fun _ => 0⟩

/-- ⚑ **THE REFUTATION, ON THE EMITTED OBJECT.** Every gate of `memoryTable` — the emitted list,
not a transcription — vanishes on `wrapRow`, and the claimed prior serial it carries is ABOVE
`2^30` while the op's own serial is 1. So "prev_serial < serial" is FALSE of the felts this AIR
admits, and the deleted arm's parenthesis "(Disciplined)" names a property of the honest prover's
LIFT rather than a verdict of the row algebra.

⚠ Direction, said plainly: this is not a defect in the deployed prover. What refuses the witness is
the `ir2_mem_check` multiset in the assembled batch — nothing ever PUBLISHES a tuple at serial
`p − 5`, so the permutation cannot balance — which is a containment argument about a DIFFERENT
object and is exactly the half `TableAir.Holds` is silent on (`TableAirIR` §3). A soundness story
that read the gap gate as a bound would be resting on a leg this table does not have. -/
theorem wrapped_prev_serial_satisfies_every_gate :
    memoryTable.RowHolds wrapRow true true ∧
    wrapRow.loc MEM_SERIAL = 1 ∧
    GAP_CEIL ≤ wrapRow.loc MEM_PREV_SERIAL ∧
    ¬ (wrapRow.loc MEM_PREV_SERIAL < wrapRow.loc MEM_SERIAL) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- …and the CONTRAST, so the refutation above is not read as "no gate bites here": the honest
window with `prev_serial = 0` and `gap = 0` is also accepted, and a window whose gap column
disagrees with its limbs is REFUSED. A table AIR no assignment refutes is decoration. -/
def honestRow : VmRowEnv :=
  ⟨fun c => if c = MEM_SERIAL then 1 else if c = MEM_IS_REAL then 1 else 0
  , fun _ => 0, fun _ => 0⟩

theorem honest_row_is_accepted : memoryTable.RowHolds honestRow true true := by decide

/-- NON-VACUITY, the FALSE pole of the GATES: a gap column with no limb witness is refused by the
recomposition gate. -/
theorem an_unwitnessed_gap_is_refused :
    ¬ memoryTable.RowHolds
        (⟨fun c => if c = MEM_SERIAL then 1 else if c = MEM_IS_REAL then 1
                   else if c = MEM_GAP then 1 else 0, fun _ => 0, fun _ => 0⟩)
        true true := by decide

/-- ⚠ **NO GATE RANGE-CHECKS `MEM_PREV_SERIAL`**, stated as an emission fact rather than as prose:
the column is read by exactly TWO gate bodies — the gap definition, and nothing that bounds it —
and by NO byte-bus query. Contrast `MEM_GAP_LIMB0`, which every range check bottoms out in. -/
theorem prev_serial_is_read_by_one_gate :
    (memoryTable.gates.filter (fun g => TExpr.readsColIn memoryTable.defs g.body MEM_PREV_SERIAL)).length = 1 := by decide

/-- …and by no byte query, which is where a magnitude bound would have to live. -/
theorem no_byte_query_reads_prev_serial :
    (memoryTable.interactions.filter
      (fun i => i.bus == BUS_BYTE && i.tuple.any (fun e => TExpr.readsColIn memoryTable.defs e MEM_PREV_SERIAL))).length
      = 0 := by decide

/-- …the non-vacuity contrast: the gap's limb columns ARE byte-queried, one each. -/
theorem the_gap_limbs_are_byte_queried :
    (memoryTable.interactions.filter (fun i => i.bus == BUS_BYTE)).length = 7 := by decide

/-! ## §5 — The wire pin. -/

/-- The wire string the Rust interpreter ingests. -/
def MEMORY_JSON : String := emitTableAirJson memoryTable

-- THE WIRE PIN. Byte length plus the structural `#guard`s in §3 (11 gates, 11 interactions in a
-- fixed per-bus/per-side split, width 18): any edit to a gate body, a tuple, a multiplicity or an
-- offset moves the length, and any edit to the SHAPE moves §3. (The checked-in artifact is these
-- bytes plus ONE trailing newline, which is the `by-name/` convention and which `JsonCursor` skips
-- as whitespace.)
#guard MEMORY_JSON.length == 3843

/-- The emission is not empty and not a stub. -/
theorem memoryTable_is_not_empty : memoryTable.gates ≠ [] := by
  simp [memoryTable, memoryGates]

end Dregg2.Circuit.Emit.MemoryTableEmit
