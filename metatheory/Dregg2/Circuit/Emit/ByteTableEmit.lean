/-
# `Dregg2.Circuit.Emit.ByteTableEmit` — the shared limb table's AIR, AUTHORED IN LEAN.

## What this replaces

`Ir2Air::ByteTable` (`circuit/src/descriptor_ir2.rs`) is the `[0, 2^LIMB_BITS)` table every
range check in the system bottoms out in: `eval_decomp` splits a value into 4-bit limbs and
queries each FULL limb on `ir2_byte`, so this table is what "this felt is 30 bits wide" MEANS at
the deployed prover. Its algebra was hand-authored Rust, which architectural law #1 forbids:
*"circuits are emitted from Lean; Rust only INTERPRETS."*

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `WindowExpr` under an explicit `RowSel`. Nothing in this cutover
hand-writes a Rust constraint, and the `law1_no_new_rust_authored_constraints` baseline for
`descriptor_ir2.rs` goes DOWN.

## Why this one needed the tool EXTENDED and `MapAbsent` did not

`MapAbsent` is purely row-local. This table is not: its whole content is a CROSS-ROW increment
chain plus a lookup-SERVE leg, and the first-pass `TableAir` could express neither. `RowSel`
(`.first` / `.transition`), `WindowExpr.nxt`, and `BusOp.provide` are the three additions, and
all three appear in these four lines of deployed Rust:

```rust
Ir2Air::ByteTable => {
    builder.when_first_row().assert_zero(local[0].into());                        // .first
    builder.when_transition()                                                     // .transition
           .assert_zero(next[0].into() - local[0].into() - AB::Expr::ONE);        // nxt
    LookupBus::new(BUS_BYTE).table_entry(builder, [local[0]], local[1]);          // .provide
}
```

## The comment-only claim this port turns into a theorem

`descriptor_ir2.rs`'s `BYTE_TABLE_HEIGHT` says, in prose:

> PINNED, prove- AND verify-side: the table AIR forces `value = row index`, so its committed
> HEIGHT is its value range — a taller table would silently widen every limb's admissible range.

Both halves are proved in §3, and they point in OPPOSITE directions, which is the interesting
part. `value_is_the_row_index` proves the AIR really does force the value column to be the index
(so the served key set is exactly `[0, n)`), and `gates_admit_every_height` proves the AIR does
NOT bound `n` — the increment trace of ANY length satisfies every gate. So the height pin in
`verify_vm_descriptor2` is load-bearing rather than belt-and-braces, and
`ir2_oversized_byte_table_refuses` is testing the only thing that can refuse the attack.

⚠ **A STALE COMMENT, corrected.** The deleted arm's doc says "The `[0,256)` byte table" and the
module header says "the shared `[0,256)` byte table". `LIMB_BITS` has been **4** since the
nibble-limb change, so `BYTE_TABLE_HEIGHT = 16` and the served range is `[0,16)` — the table is a
NIBBLE table with a byte table's name. Nothing depends on the wrong number (every caller reads
the constant), but a reader auditing a range bound from the prose would be off by a factor of 16.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Crypto enters nowhere: this file is the ALGEBRA of
a counter and the range semantics it grounds.
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.Emit.ByteTableEmit

open Dregg2.Circuit.DescriptorIR2 (WindowExpr)
open Dregg2.Circuit.TableAirIR
  (BusOp BusInteraction TableAir TableGate Coherent emitTableAirJson v n k eSub gFirst gTrans)

set_option autoImplicit false

/-! ## §1 — The deployed layout.

Transcribed from `descriptor_ir2.rs`: the byte instance is width 2 (`Ir2Air::ByteTable => 2`),
column 0 the VALUE and column 1 the multiplicity the `table_entry` leg rides at. -/

/-- `LIMB_BITS`. -/
def LIMB_BITS : Nat := 4
/-- `BYTE_TABLE_HEIGHT = 1 <<< LIMB_BITS`. ⚠ 16, not 256 — see the header. -/
def HEIGHT : Nat := 2 ^ LIMB_BITS
/-- The value column. -/
def BT_VALUE : Nat := 0
/-- The multiplicity column: how many times this entry is CONSUMED. Constrained by NO gate —
its discipline is the LogUp balance, not the row algebra, and saying so is the point of the
`interactionsWitness` split in `TableAirIR` §3. -/
def BT_MULT : Nat := 1
/-- The instance width. -/
def BT_WIDTH : Nat := BT_MULT + 1

#guard HEIGHT == 16
#guard BT_WIDTH == 2

/-- The bus name, verbatim from the Rust `BUS_BYTE` constant. -/
def BUS_BYTE : String := "ir2_byte"

/-! ## §2 — THE TABLE. -/

/-- The gate list, in the deleted Rust arm's emission order.

  * `.first` — the chain STARTS at zero.
  * `.transition` — each row is its predecessor plus one. `.transition` and not `.all`: on the
    last row p3's `nxt` is the WRAP row (back to row 0), where `0 = last + 1` is false for every
    height above 1, so an `.all` scope would make the honest table UNSAT. -/
def byteGates : List TableGate :=
  [ gFirst (v BT_VALUE)
  , gTrans (eSub (n BT_VALUE) (.add (v BT_VALUE) (k 1))) ]

/-- The one bus leg: this table SERVES `ir2_byte`. `.provide`, not `.query` — it is the table,
not a client of one, and in p3 the two differ by the sign of the count AND by `count_weight`. -/
def byteInteractions : List BusInteraction :=
  [⟨BUS_BYTE, .provide, v BT_MULT, [v BT_VALUE]⟩]

/-- **`byteTable`** — the shared limb table's AIR, as a Lean object. -/
def byteTable : TableAir :=
  { name         := "dregg-ir2-byte-v1"
  , width        := BT_WIDTH
  , gates        := byteGates
  , interactions := byteInteractions }

/-! ## §3 — Shape pins. -/

#guard byteTable.width == 2
#guard byteTable.gates.length == 2
#guard byteTable.busCount == 1
#guard byteTable.gateCountSel .first == 1
#guard byteTable.gateCountSel .transition == 1
#guard byteTable.gateCountSel .all == 0
-- ⚑ THE SIDE OF THE BUS. A `.query` here instead of a `.provide` would make the byte bus
-- unsatisfiable in one direction and vacuous in the other; the count pins the side.
#guard byteTable.busCountOp BUS_BYTE .provide == 1
#guard byteTable.busCountOp BUS_BYTE .query == 0

/-! ## §4 — THE COMMENT-ONLY CLAIM, PROVED (both directions).

`BYTE_TABLE_HEIGHT`'s doc comment makes one claim with two halves, and only the first half is
about the AIR. §4a proves the AIR forces `value = row index`; §4b proves it does NOT force the
height, which is why the verifier's separate pin is the thing that actually refuses the widening
attack. -/

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.TableAirIR (TableGate)

/-! ### §4a — The AIR forces `value = row index`. -/

/-- The first-row gate, unpacked: row 0's value vanishes. -/
theorem first_row_is_zero {rows : List VmRowEnv}
    (hh : byteTable.Holds rows) (h : 0 < rows.length) :
    rows[0].loc BT_VALUE ≡ 0 [ZMOD 2013265921] := by
  have hg := hh 0 h ⟨.first, v BT_VALUE⟩ (by simp [byteTable, byteGates, gFirst])
  simp only [TableGate.holdsAt] at hg
  simpa [v, WindowExpr.eval] using hg (by simp)

/-- The transition gate, unpacked: on any non-final row the NEXT window value is one more. -/
theorem step {rows : List VmRowEnv}
    (hh : byteTable.Holds rows) (i : Nat) (hlt : i < rows.length) (h : i + 1 < rows.length) :
    rows[i].nxt BT_VALUE ≡ rows[i].loc BT_VALUE + 1 [ZMOD 2013265921] := by
  have hg := hh i hlt ⟨.transition, eSub (n BT_VALUE) (.add (v BT_VALUE) (k 1))⟩
    (by simp [byteTable, byteGates, gTrans])
  simp only [TableGate.holdsAt] at hg
  have hz := hg (by simp; omega)
  simp only [eSub, v, n, k, WindowExpr.eval] at hz
  unfold Int.ModEq at hz ⊢
  omega

/-- ⚑ **THE CLAIM, HALF ONE.** On a COHERENT accepting trace the value column IS the row index.
This is what licenses reading "a limb queried on `ir2_byte`" as "a limb in `[0, height)`" — the
served key set is the set of row indices, so the RANGE a decomposition enforces is a fact about
the table's HEIGHT and nothing else.

⚠ `Coherent` is not decoration in this statement: without it `rows[i].nxt` is an unconstrained
function and the increment chain says nothing about `rows[i+1]`. -/
theorem value_is_the_row_index {rows : List VmRowEnv}
    (hc : Coherent rows) (hh : byteTable.Holds rows) :
    ∀ i, ∀ h : i < rows.length,
      rows[i].loc BT_VALUE ≡ (i : ℤ) [ZMOD 2013265921] := by
  intro i
  induction i with
  | zero => intro h; simpa using first_row_is_zero hh h
  | succ m ih =>
    intro h
    have hm : m + 1 < rows.length := h
    have hlt : m < rows.length := by omega
    have hstep := step hh m hlt hm
    have hcoh : rows[m].nxt = rows[m + 1].loc := hc m hm
    rw [hcoh] at hstep
    have hih := ih (by omega)
    have hfin : rows[m + 1].loc BT_VALUE ≡ (m : ℤ) + 1 [ZMOD 2013265921] :=
      hstep.trans (Int.ModEq.add_right 1 hih)
    simpa using hfin

/-- **THE SERVED SET, in canonical form.** On a trace no taller than the field, row `i` serves
exactly the key `i` — as an integer in `[0, p)`, not merely up to a multiple of `p`. So a
height-`n` byte table serves `[0, n)` and NOTHING else, which is the sentence a range bound is
read off. -/
theorem served_key_is_canonical {rows : List VmRowEnv}
    (hc : Coherent rows) (hh : byteTable.Holds rows) (hn : rows.length ≤ 2013265921)
    (i : Nat) (h : i < rows.length) :
    rows[i].loc BT_VALUE % 2013265921 = (i : ℤ) := by
  have hmod := value_is_the_row_index hc hh i h
  have hi : i < 2013265921 := by omega
  have hiz : (i : ℤ) < 2013265921 := by exact_mod_cast hi
  have h0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  calc rows[i].loc BT_VALUE % 2013265921 = (i : ℤ) % 2013265921 := hmod
    _ = (i : ℤ) := Int.emod_eq_of_lt h0 hiz

/-! ### §4b — ⚠ …and the AIR does NOT bound the height. -/

/-- Row `i` of the honest increment trace: value `i`, next-value `i + 1`. -/
def mkRow (i : Nat) : VmRowEnv :=
  ⟨fun c => if c = BT_VALUE then (i : ℤ) else 0
  , fun c => if c = BT_VALUE then ((i : ℤ) + 1) else 0
  , fun _ => 0⟩

/-- The honest increment trace of length `m`. -/
def indexTrace (m : Nat) : List VmRowEnv := (List.range m).map mkRow

@[simp] theorem indexTrace_length (m : Nat) : (indexTrace m).length = m := by
  simp [indexTrace]

@[simp] theorem indexTrace_get (m i : Nat) (h : i < (indexTrace m).length) :
    (indexTrace m)[i] = mkRow i := by
  simp only [indexTrace] at h ⊢
  rw [List.getElem_map, List.getElem_range]

/-- ⚑ **THE CLAIM, HALF TWO — and the reason the verifier's height pin is load-bearing.**
The gates are satisfied at EVERY height. A 32-row byte table serving `[0, 32)` — which widens
every limb in the system from 4 bits to 5 — passes this AIR exactly as the deployed 16-row one
does. Nothing in the ALGEBRA refuses it; only `verify_vm_descriptor2`'s explicit
`BYTE_TABLE_HEIGHT` check does, which is what `ir2_oversized_byte_table_refuses` measures.

This is the FALSE pole of the pair: a soundness story that stopped at `value_is_the_row_index`
would read as "the table cannot lie", and the table can — about how BIG it is. -/
theorem gates_admit_every_height (m : Nat) :
    Coherent (indexTrace m) ∧ byteTable.Holds (indexTrace m) := by
  refine ⟨?_, ?_⟩
  · intro i h
    rw [indexTrace_get m i (by omega), indexTrace_get m (i + 1) h]
    funext c
    simp only [mkRow]
    by_cases hc : c = BT_VALUE <;> simp [hc]
  · intro i h g hg
    simp only [byteTable, byteGates, gFirst, gTrans, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    rw [indexTrace_get m i h]
    rcases hg with rfl | rfl
    · simp only [TableGate.holdsAt]
      intro hf
      have hi : i = 0 := by simpa using hf
      subst hi
      simp [mkRow, v, WindowExpr.eval, Int.ModEq]
    · simp only [TableGate.holdsAt]
      intro _
      simp [mkRow, eSub, v, n, k, WindowExpr.eval, Int.ModEq]

/-- NON-VACUITY, the FALSE pole of the GATES themselves: a trace whose first row is not zero is
REFUSED. A table AIR that no assignment refutes is decoration; this exhibits the refutation. -/
theorem a_nonzero_first_row_is_refused :
    ¬ byteTable.Holds [⟨fun _ => 1, fun _ => 2, fun _ => 0⟩] := by
  intro hh
  have hg := hh 0 (by simp) ⟨.first, v BT_VALUE⟩ (by simp [byteTable, byteGates, gFirst])
  simp only [TableGate.holdsAt] at hg
  have := hg (by simp)
  revert this
  simp only [v, WindowExpr.eval]
  decide

/-! ## §5 — The wire pin. -/

/-- The wire string the Rust interpreter ingests. -/
def BYTE_JSON : String := emitTableAirJson byteTable

-- THE WIRE GOLDEN, byte-pinned in full: this table is small enough that the whole emission is
-- the golden, so there is no gap between "the shape pins pass" and "these are the bytes".
#guard BYTE_JSON ==
  "{\"name\":\"dregg-ir2-byte-v1\",\"kind\":\"table_air\",\"ir\":2,\"width\":2,\"gates\":[{\"sel\":\"first\",\"body\":{\"t\":\"loc\",\"c\":0}},{\"sel\":\"transition\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"const\",\"v\":1}}}}}],\"interactions\":[{\"bus\":\"ir2_byte\",\"op\":\"provide\",\"mult\":{\"t\":\"loc\",\"c\":1},\"tuple\":[{\"t\":\"loc\",\"c\":0}]}]}"

/-- The emission is not empty and not a stub. -/
theorem byteTable_is_not_empty : byteTable.gates ≠ [] := by
  simp [byteTable, byteGates]

end Dregg2.Circuit.Emit.ByteTableEmit
