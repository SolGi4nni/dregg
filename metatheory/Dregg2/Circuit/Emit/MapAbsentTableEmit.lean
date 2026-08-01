/-
# `Dregg2.Circuit.Emit.MapAbsentTableEmit` — the live double-spend gate's AIR, AUTHORED IN LEAN.

## What this replaces

`Ir2Air::MapAbsent` (`circuit/src/descriptor_ir2.rs`) is the in-circuit non-membership gate a note
spend rides through `noteSpendVmDescriptor2R24`'s `nullifierFreshOp`. Its ~150 lines of
`builder.assert_zero(..)` + `bus.lookup_key(..)` are hand-authored Rust algebra, which architectural
law #1 forbids: *"circuits are emitted from Lean; Rust only INTERPRETS."* The Lean side had a
MODEL of that gate (`MapAbsentImtGate.AbsentImtGatesAt` and its wide twin) but no EMISSION — the
correspondence between the model and the deployed columns was prose, re-checked by hand.

This file emits the constraints. `mapAbsentTable : TableAir` IS the AIR: the Rust interpreter reads
it and calls `assert_zero` / `lookup_key` on what it says, so the algebra has exactly one author.

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `EmittedExpr`. Nothing in this cutover hand-writes a Rust constraint,
and the `law1_no_new_rust_authored_constraints` baseline for `descriptor_ir2.rs` goes DOWN.

## ⚠ WHAT THIS CUTOVER DOES **NOT** FIX — the key is still ONE FELT

`MA_KEY`, `MA_LO_ADDR` and `MA_LO_NEXT` are one column each here, exactly as deployed. That is the
2^15.45-collision sort key `circuit/tests/mapabsent_key_width_tooth.rs` measures, and it is
UNCHANGED by this file. Widening it is a separate, larger move and this file is its PREREQUISITE,
not its substitute — see §7 for the precise reason the order is forced, and for the measured cost.

⚑ Nor is the arity-17 "wide" schema the fix. `MapOpWideKeyPigeonhole.arity17_conflates_two_addresses`
proves — for EVERY hash, no CR hypothesis — that an 8-lane address slot conflates two 32-byte
addresses, because `P^8 < 2^256`. The whole existing wide `.absent` tower is stated at `Digest8Key`
(`Lex (Fin 8 → ℤ)`), so it lands at a schema this repo has already refuted for a 32-byte key. The
successor is NINE lanes and `Digest9Key` does not exist yet. §7 prices that.

## The transcription contract

Every gate and every bus interaction below is in the SAME ORDER the deleted Rust arm emitted them,
and each is ALGEBRAICALLY EQUAL to the polynomial that arm built. ⚠ Say the resolution exactly:
"algebraically equal in the same order" is what is claimed and what was checked (the per-table
constraint-degree ledger `ir2_degree_budget` is unchanged, the honest witness proves and verifies,
and the mutation sweep in `circuit/tests/mapabsent_lean_emission_differential.rs` finds every gated
column still gated). **BYTE-IDENTITY OF THE SYMBOLIC EXPRESSION TREES WAS NOT MEASURED** — the
limb weights here are literal `16 ^ i` constants where the Rust accumulated them by repeated
multiplication — so the flag day is declared as a VK rotation rather than as a no-op.
The deployed constants are transcribed once, in §1, and `#guard`-pinned against the arithmetic that
derives them.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Crypto enters nowhere: this file is the ALGEBRA and
its integer-faithfulness, not the tree soundness (that is `MapAbsentImtGate`'s, under its named
`Poseidon2SpongeCR` floor).
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.Emit.MapAbsentTableEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.TableAirIR (BusOp BusInteraction TableAir emitTableAirJson)

set_option autoImplicit false

/-! ## §0 — Expression sugar (the shapes the deployed builder produces). -/

/-- Column read. -/
def v (c : Nat) : EmittedExpr := .var c
/-- Field constant. -/
def k (n : ℤ) : EmittedExpr := .const n
/-- `a − b`, the standard encoding (there is no `sub` node). -/
def eSub (a b : EmittedExpr) : EmittedExpr := .add a (.mul (.const (-1)) b)
/-- `1 − e`. -/
def eOneMinus (e : EmittedExpr) : EmittedExpr := eSub (k 1) e
/-- The boolean gate body `c·(c − 1)` — the Rust `x * (x - ONE)`. -/
def gBool (c : Nat) : EmittedExpr := .mul (v c) (.add (v c) (k (-1)))

/-! ## §1 — The deployed column layout.

Transcribed from `descriptor_ir2.rs`'s `MA_*` constants and `heap_root.rs`'s `HEAP_TREE_DEPTH`.
The `#guard`s at the end of this section are the arithmetic that derives each offset from the one
before it, so a layout drift on either side cannot be silent. -/

/-- `HEAP_TREE_DEPTH`. -/
def DEPTH : Nat := 16
/-- `CHIP_OUT_LANES`. -/
def LANES : Nat := 8
/-- `CHIP_RATE`. -/
def RATE : Nat := 16
/-- `CHIP_NODE8_ARITY`. -/
def NODE8_ARITY : ℤ := 16
/-- `HEAP_LEAF_ARITY`. -/
def LEAF_ARITY : ℤ := 3
/-- `KEY_LO_BITS`. -/
def LO_BITS : Nat := 27
/-- `2 ^ KEY_LO_BITS` — the canonical split base. -/
def HI_BASE : ℤ := 134217728
/-- `KEY_HI_MAX` = 15: `p − 1 = 15 · 2^27`. -/
def HI_MAX : ℤ := 15
/-- Full 4-bit limbs of a 27-bit value (`limb_geom(27).0`). -/
def LIMBS : Nat := 7
/-- Bits in the partial top limb (`limb_geom(27).1`). -/
def TOP_BITS : Nat := 3
/-- Columns one 27-bit decomposition costs (`decomp_cols(27)` = limbs + top bits). -/
def DECOMP : Nat := LIMBS + TOP_BITS
/-- `MA_DECOMP_COLS` = `[hi4, lo27 limbs, is15, inv15]`. -/
def CANON_COLS : Nat := 1 + DECOMP + 2
/-- `MA_CMP_COLS` = `[s, dhi, dlo, dlo limbs]`. -/
def CMP_COLS : Nat := 3 + DECOMP

def MA_ROOT : Nat := 0
def MA_KEY : Nat := MA_ROOT + LANES
def MA_NEW_ROOT : Nat := MA_KEY + 1
def MA_IS_REAL : Nat := MA_NEW_ROOT + LANES
def MA_LO_ADDR : Nat := MA_IS_REAL + 1
def MA_LO_VALUE : Nat := MA_LO_ADDR + 1
def MA_LO_NEXT : Nat := MA_LO_VALUE + 1
def MA_LO_LEAF : Nat := MA_LO_NEXT + 1
def MA_LO_SIB0 : Nat := MA_LO_LEAF + LANES
def MA_LO_DIR0 : Nat := MA_LO_SIB0 + LANES * DEPTH
def MA_LO_CHAIN0 : Nat := MA_LO_DIR0 + DEPTH
def MA_A_DEC0 : Nat := MA_LO_CHAIN0 + LANES * (DEPTH - 1)
def MA_K_DEC0 : Nat := MA_A_DEC0 + CANON_COLS
def MA_B_DEC0 : Nat := MA_K_DEC0 + CANON_COLS
def MA_CMP_LO0 : Nat := MA_B_DEC0 + CANON_COLS
def MA_CMP_HI0 : Nat := MA_CMP_LO0 + CMP_COLS
/-- `MA_WIDTH`. -/
def MA_WIDTH : Nat := MA_CMP_HI0 + CMP_COLS

-- The deployed numbers, pinned. A drift on either side moves one of these.
#guard DECOMP == 10
#guard CANON_COLS == 13
#guard CMP_COLS == 13
#guard MA_KEY == 8
#guard MA_NEW_ROOT == 9
#guard MA_IS_REAL == 17
#guard MA_LO_ADDR == 18
#guard MA_LO_NEXT == 20
#guard MA_LO_LEAF == 21
#guard MA_LO_SIB0 == 29
#guard MA_LO_DIR0 == 157
#guard MA_LO_CHAIN0 == 173
#guard MA_A_DEC0 == 293
#guard MA_K_DEC0 == 306
#guard MA_B_DEC0 == 319
#guard MA_CMP_LO0 == 332
#guard MA_CMP_HI0 == 345
#guard MA_WIDTH == 358

/-- `p − 1 = HI_MAX · HI_BASE`: the arithmetic the uniqueness tooth in §3 turns on, checked
rather than asserted. -/
theorem p_sub_one_eq : HI_MAX * HI_BASE = 2013265921 - 1 := by decide

/-- The bus names, verbatim from the Rust `BUS_*` constants. -/
def BUS_P2 : String := "ir2_p2"
def BUS_BYTE : String := "ir2_byte"
def BUS_MAP_LOG : String := "ir2_map_log"

/-! ## §2 — The range/comparator gadgets, emitted.

These are the Lean authors of `eval_decomp`, `eval_canon_decomp` and `eval_lex_lt`. They are
parameterized by the column block so the same emitters serve the `MapOps` table when it follows
`MapAbsent` off the hand-written path. -/

/-- `Σ_{i < 7} limb_i · 16^i`, left-associated exactly as the Rust `recomposed +=` loop
accumulates it (starting from `0`). -/
def recompose27 (limb0 : Nat) : EmittedExpr :=
  (List.range LIMBS).foldl
    (fun acc i => .add acc (.mul (v (limb0 + i)) (k (16 ^ i))))
    (k 0)

/-- `Σ_{b < 3} bit_b · 2^b` over the partial top limb's bit columns, same accumulation. -/
def topRecomp (limb0 : Nat) : EmittedExpr :=
  (List.range TOP_BITS).foldl
    (fun acc b => .add acc (.mul (v (limb0 + LIMBS + b)) (k (2 ^ b))))
    (k 0)

/-- The GATES of one 27-bit decomposition of `ve` over the 10-column block at `limb0`:
three booleans on the top-limb bits, the top-limb recomposition, then the whole-value
recomposition. Emission order is the Rust loop's. -/
def decompGates (ve : EmittedExpr) (limb0 : Nat) : List EmittedExpr :=
  (List.range TOP_BITS).map (fun b => gBool (limb0 + LIMBS + b)) ++
  [ eSub (topRecomp limb0) (v (limb0 + LIMBS - 1))
  , eSub (recompose27 limb0) ve ]

/-- The byte-table QUERIES of one 27-bit decomposition: the six FULL limbs (the seventh is
bit-decomposed instead, which is what makes the top bound tight). -/
def decompQueries (limb0 : Nat) (mult : EmittedExpr) : List BusInteraction :=
  (List.range (LIMBS - 1)).map (fun i => ⟨BUS_BYTE, .query, mult, [v (limb0 + i)]⟩)

/-- `hi4` of a canonical-decomposition block. -/
def canonHi (b0 : Nat) : EmittedExpr := v b0
/-- `lo27 = value − hi4 · 2^27`. -/
def canonLo (ve : EmittedExpr) (b0 : Nat) : EmittedExpr :=
  eSub ve (.mul (v b0) (k HI_BASE))

/-- The gates of one CANONICAL decomposition `value = hi4·2^27 + lo27` over the 13-column block
at `b0` = `[hi4, lo27 limbs (10), is15, inv15]`, gated by `gate`.

The last gate is **the uniqueness tooth**: `is15 · lo27 = 0`. With `hi4 ∈ [0,16)` by the nibble
query and `lo27 ∈ [0, 2^27)` by the decomposition, `hi4 = 15` admits only `lo27 = 0`, so the only
representable value at the top nibble is `p − 1` — the non-canonical alias `x + p` of any small
`x` is UNSAT. That is what makes the comparators in §2c integer-faithful rather than
representative-dependent. -/
def canonDecompGates (ve : EmittedExpr) (b0 : Nat) (gate : EmittedExpr) : List EmittedExpr :=
  decompGates (canonLo ve b0) (b0 + 1) ++
  [ gBool (b0 + 1 + DECOMP)
  , .mul (eSub (v b0) (k HI_MAX)) (v (b0 + 1 + DECOMP))
  , eSub (.mul (eSub (v b0) (k HI_MAX)) (v (b0 + 2 + DECOMP)))
         (eSub gate (v (b0 + 1 + DECOMP)))
  , .mul (v (b0 + 1 + DECOMP)) (canonLo ve b0) ]

/-- The queries of one canonical decomposition: the `hi4` nibble, then the low limbs. -/
def canonDecompQueries (b0 : Nat) (mult : EmittedExpr) : List BusInteraction :=
  ⟨BUS_BYTE, .query, mult, [v b0]⟩ :: decompQueries (b0 + 1) mult

/-- The gates of one lexicographic STRICT-LT `a < b` over canonical `(hi, lo)` pairs, on the
13-column block at `b0` = `[s, dhi, dlo, dlo limbs (10)]`, gated by `gate`.

`s = 1` ⇒ `bHi ≥ aHi + 1` (witness `dhi`, a nibble); `s = 0` ⇒ `bHi = aHi` and
`bLo ≥ aLo + 1` (witness `dlo`, 27-bit). -/
def lexLtGates (aHi aLo bHi bLo : EmittedExpr) (b0 : Nat) (gate : EmittedExpr) :
    List EmittedExpr :=
  gBool b0 :: decompGates (v (b0 + 2)) (b0 + 3) ++
  [ eSub (v (b0 + 1))
         (.mul (.mul gate (v b0)) (eSub (eSub bHi aHi) (k 1)))
  , .mul (.mul gate (eOneMinus (v b0))) (eSub bHi aHi)
  , eSub (v (b0 + 2))
         (.mul (.mul gate (eOneMinus (v b0))) (eSub (eSub bLo aLo) (k 1))) ]

/-- The queries of one lex comparator: the `dhi` nibble, then the `dlo` limbs. -/
def lexLtQueries (b0 : Nat) (mult : EmittedExpr) : List BusInteraction :=
  ⟨BUS_BYTE, .query, mult, [v (b0 + 1)]⟩ :: decompQueries (b0 + 3) mult

/-! ## §3 — The chip tuples. -/

/-- The 8-felt group at `base`. -/
def group8 (base : Nat) : List EmittedExpr := (List.range LANES).map (fun i => v (base + i))

/-- The arity-3 IMT leaf absorb `[3, addr, value, next, 0×13, out0..7]` (25 wide). -/
def leafTuple (addrC valC nextC leafC : Nat) : List EmittedExpr :=
  k LEAF_ARITY :: v addrC :: v valC :: v nextC ::
  ((List.range (RATE - 3)).map (fun _ => k 0) ++ group8 leafC)

/-- The arity-16 `node8` compression tuple `[16, L8, R8, out8]` (25 wide), with
`L8 = (1−dir)·cur + dir·sib` and `R8 = (1−dir)·sib + dir·cur`. -/
def node8Tuple (curBase sibBase outBase dirC : Nat) : List EmittedExpr :=
  let d : EmittedExpr := v dirC
  k NODE8_ARITY ::
  ((List.range LANES).map (fun i =>
      .add (.mul (eOneMinus d) (v (curBase + i))) (.mul d (v (sibBase + i)))) ++
   (List.range LANES).map (fun i =>
      .add (.mul (eOneMinus d) (v (sibBase + i))) (.mul d (v (curBase + i)))) ++
   group8 outBase)

/-- The digest column group the fold reads at level `lvl`: the leaf at level 0, then the chain
columns, with the LAST level's output being the committed root. -/
def foldCur (lvl : Nat) : Nat :=
  if lvl = 0 then MA_LO_LEAF else MA_LO_CHAIN0 + LANES * (lvl - 1)

/-- The digest column group the fold WRITES at level `lvl`. -/
def foldOut (lvl : Nat) : Nat :=
  if lvl + 1 = DEPTH then MA_ROOT else MA_LO_CHAIN0 + LANES * lvl

/-- The 19-felt map-log tuple `[root8, key, value, op, new_root8]`. `.absent` carries the
canonical value `0` and op code `2`. -/
def mapLogTuple : List EmittedExpr :=
  group8 MA_ROOT ++ [v MA_KEY, k 0, k 2] ++ group8 MA_NEW_ROOT

/-! ## §4 — THE TABLE. -/

/-- `is_real`, the row guard. -/
def gReal : EmittedExpr := v MA_IS_REAL

/-- The gate list, in the deleted Rust arm's emission order. -/
def mapAbsentGates : List EmittedExpr :=
  -- (1) the row guard is boolean.
  gBool MA_IS_REAL ::
  -- (2) every direction bit is boolean.
  (List.range DEPTH).map (fun lvl => gBool (MA_LO_DIR0 + lvl)) ++
  -- (3) a non-membership read PRESERVES the root, lane by lane.
  (List.range LANES).map (fun i =>
    .mul gReal (eSub (v (MA_NEW_ROOT + i)) (v (MA_ROOT + i)))) ++
  -- (4) canonical decompositions of low_addr, key, low_next.
  canonDecompGates (v MA_LO_ADDR) MA_A_DEC0 gReal ++
  canonDecompGates (v MA_KEY) MA_K_DEC0 gReal ++
  canonDecompGates (v MA_LO_NEXT) MA_B_DEC0 gReal ++
  -- (5) the POINTER BRACKET: low_addr < key < low_next, as integers.
  lexLtGates (canonHi MA_A_DEC0) (canonLo (v MA_LO_ADDR) MA_A_DEC0)
             (canonHi MA_K_DEC0) (canonLo (v MA_KEY) MA_K_DEC0)
             MA_CMP_LO0 gReal ++
  lexLtGates (canonHi MA_K_DEC0) (canonLo (v MA_KEY) MA_K_DEC0)
             (canonHi MA_B_DEC0) (canonLo (v MA_LO_NEXT) MA_B_DEC0)
             MA_CMP_HI0 gReal

/-- The bus interactions, in the deleted Rust arm's emission order. -/
def mapAbsentInteractions : List BusInteraction :=
  -- the three canonical decompositions' nibble + limb queries (multiplicity 1, as deployed:
  -- `eval_canon_decomp` is the UNCOUNTED variant, so a pad row still queries).
  canonDecompQueries MA_A_DEC0 (k 1) ++
  canonDecompQueries MA_K_DEC0 (k 1) ++
  canonDecompQueries MA_B_DEC0 (k 1) ++
  -- the two comparators' queries.
  lexLtQueries MA_CMP_LO0 (k 1) ++
  lexLtQueries MA_CMP_HI0 (k 1) ++
  -- the low leaf's arity-3 absorb, at multiplicity `is_real`.
  [⟨BUS_P2, .query, gReal, leafTuple MA_LO_ADDR MA_LO_VALUE MA_LO_NEXT MA_LO_LEAF⟩] ++
  -- the depth-many `node8` folds up ONE path to the committed root.
  (List.range DEPTH).map (fun lvl =>
    (⟨BUS_P2, .query, gReal,
      node8Tuple (foldCur lvl) (MA_LO_SIB0 + LANES * lvl) (foldOut lvl) (MA_LO_DIR0 + lvl)⟩ :
        BusInteraction)) ++
  -- the gathered absent sub-log.
  [⟨BUS_MAP_LOG, .receive, gReal, mapLogTuple⟩]

/-- **`mapAbsentTable`** — the live double-spend gate's AIR, as a Lean object. -/
def mapAbsentTable : TableAir :=
  { name         := "dregg-ir2-map-absent-v1"
  , width        := MA_WIDTH
  , gates        := mapAbsentGates
  , interactions := mapAbsentInteractions }

/-! ## §5 — Shape pins.

Counts derived from the layout, not transcribed: `1 + DEPTH + LANES + 3·9 + 2·9 = 70` gates and
`3·7 + 2·7 + 1 + DEPTH + 1 = 53` interactions. A dropped gate or bus leg moves one of these. -/

#guard mapAbsentTable.width == 358
#guard mapAbsentTable.gates.length == 70
#guard mapAbsentTable.busCount == 53
#guard mapAbsentTable.busCountOn "ir2_byte" == 35
#guard mapAbsentTable.busCountOn "ir2_p2" == 17
#guard mapAbsentTable.busCountOn "ir2_map_log" == 1

-- Each gadget's own contribution, so a regression names the gadget rather than the total.
#guard (decompGates (v 0) 100).length == 5
#guard (decompQueries 100 (k 1)).length == 6
#guard (canonDecompGates (v 0) 100 (v 1)).length == 9
#guard (canonDecompQueries 100 (k 1)).length == 7
#guard (lexLtGates (v 0) (v 1) (v 2) (v 3) 100 (v 4)).length == 9
#guard (lexLtQueries 100 (k 1)).length == 7
#guard (leafTuple 1 2 3 4).length == 25
#guard (node8Tuple 10 20 30 40).length == 25
#guard mapLogTuple.length == 19

/-- The fold really walks ONE path: level 0 reads the leaf, level `lvl+1` reads what level `lvl`
wrote, and the last level writes the COMMITTED root. Stated as a chain equation so a
transcription that short-circuits the path (writing the root early, or re-reading the leaf) is
refuted rather than merely uncounted. -/
theorem fold_is_a_chain (lvl : Nat) (h : lvl + 1 < DEPTH) : foldOut lvl = foldCur (lvl + 1) := by
  have h0 : ¬ (lvl + 1 = DEPTH) := by omega
  simp [foldOut, foldCur, h0]

/-- …and it TERMINATES at the committed root, not at a chain column. -/
theorem fold_ends_at_root : foldOut (DEPTH - 1) = MA_ROOT := by decide

/-- …and STARTS at the low leaf. -/
theorem fold_starts_at_leaf : foldCur 0 = MA_LO_LEAF := by decide

/-- Every column the table names is inside its declared width — the emission cannot read past
the row it is given. -/
theorem chain_cols_in_width (lvl : Nat) (h : lvl < DEPTH) :
    foldCur lvl + LANES ≤ MA_WIDTH ∧ MA_LO_SIB0 + LANES * lvl + LANES ≤ MA_WIDTH := by
  have h16 : lvl < 16 := h
  interval_cases lvl <;> decide

/-! ## §6 — The gadget is INTEGER-FAITHFUL: the uniqueness tooth, proved.

The reason the deployed comparators may be read as integer `<` on felts is that the canonical
split is UNIQUE. This section proves that, over ℤ, from the gate equations alone — it is the one
mathematical claim the hand-written Rust made in a comment and nothing checked. -/

/-- The canonical-split predicate the block's gates force at `gate = 1`: `hi` is a nibble, `lo`
is 27-bit, the value splits, and the `is15` tooth has fired. -/
structure CanonSplit (value hi lo : ℤ) : Prop where
  hi_lo    : 0 ≤ hi
  hi_hi    : hi < 16
  lo_lo    : 0 ≤ lo
  lo_hi    : lo < HI_BASE
  splits   : value = hi * HI_BASE + lo
  /-- The `is15 · lo27 = 0` tooth, in its forced form. -/
  tooth    : hi = HI_MAX → lo = 0

/-- **THE TOOTH.** A canonically split value lies in `[0, p)`: the split is a lift into the
canonical range, so two felts that compare by `(hi, lo)` compare as integers. -/
theorem canonSplit_lt_p {value hi lo : ℤ} (h : CanonSplit value hi lo) :
    0 ≤ value ∧ value < 2013265921 := by
  obtain ⟨hlo, hhi, llo, lhi, hs, ht⟩ := h
  simp only [HI_BASE] at lhi ht ⊢
  simp only [HI_BASE, HI_MAX] at hs ht
  subst hs
  -- `hi * 2^27 + lo` is linear in `hi` and `lo` at a literal base, so this is pure `omega`
  -- once the `hi = 15 ⇒ lo = 0` tooth is case-split.
  rcases eq_or_lt_of_le (by omega : hi ≤ 15) with h15 | h15
  · have hz := ht h15; omega
  · omega

/-- **UNIQUENESS.** Two canonical splits of values congruent mod `p` are the SAME split. This is
what makes "compare the blocks" the same relation as "compare the felts": a prover cannot
re-split a key to move it in the order. -/
theorem canonSplit_unique {v₁ v₂ hi₁ lo₁ hi₂ lo₂ : ℤ}
    (h₁ : CanonSplit v₁ hi₁ lo₁) (h₂ : CanonSplit v₂ hi₂ lo₂)
    (hcong : v₁ ≡ v₂ [ZMOD 2013265921]) : hi₁ = hi₂ ∧ lo₁ = lo₂ := by
  obtain ⟨b₁, b₂⟩ := canonSplit_lt_p h₁
  obtain ⟨c₁, c₂⟩ := canonSplit_lt_p h₂
  have hv : v₁ = v₂ := by
    have h := hcong
    unfold Int.ModEq at h
    rwa [Int.emod_eq_of_lt b₁ b₂, Int.emod_eq_of_lt c₁ c₂] at h
  subst hv
  have e := h₁.splits.symm.trans h₂.splits
  have p1 := h₁.lo_lo; have p2 := h₁.lo_hi
  have p3 := h₂.lo_lo; have p4 := h₂.lo_hi
  simp only [HI_BASE] at e p2 p4
  omega

/-- The strict-LT witness relation the comparator block forces at `gate = 1`. -/
def LexLtWitness (aHi aLo bHi bLo s dhi dlo : ℤ) : Prop :=
  (s = 0 ∨ s = 1) ∧ 0 ≤ dhi ∧ 0 ≤ dlo ∧
  dhi = s * (bHi - aHi - 1) ∧
  s * 0 + (1 - s) * (bHi - aHi) = 0 ∧
  dlo = (1 - s) * (bLo - aLo - 1)

/-- **THE COMPARATOR IS SOUND.** An accepting comparator block, over two canonical splits,
forces the strict integer inequality on the split VALUES. Both branches: the `s = 1` branch
strictly raises the nibble, the `s = 0` branch equalizes it and strictly raises the low word. -/
theorem lexLt_forces_lt {va vb aHi aLo bHi bLo s dhi dlo : ℤ}
    (ha : CanonSplit va aHi aLo) (hb : CanonSplit vb bHi bLo)
    (hw : LexLtWitness aHi aLo bHi bLo s dhi dlo) : va < vb := by
  obtain ⟨hs, hdhi, hdlo, edhi, eeq, edlo⟩ := hw
  rw [ha.splits, hb.splits]
  rcases hs with rfl | rfl
  · -- s = 0: nibbles equal, low word strictly greater.
    simp only [zero_mul, sub_zero, one_mul, zero_add] at eeq edlo
    have hEq : bHi = aHi := by linarith
    rw [hEq]; omega
  · -- s = 1: nibble strictly greater, and both low words are in [0, 2^27).
    simp only [one_mul] at edhi
    have : aHi + 1 ≤ bHi := by omega
    have hlo := ha.lo_hi
    have hlo2 := hb.lo_lo
    simp only [HI_BASE] at hlo ⊢
    nlinarith [ha.lo_lo]

/-- ⚠ NON-VACUITY, the FALSE pole: the comparator relation is REFUTABLE. `a < b` is not
derivable for every pair — there is no witness at all when `a = b`. A soundness lemma whose
premise nothing satisfies proves nothing; this exhibits the refutation. -/
theorem lexLt_has_no_witness_at_equal (hi lo : ℤ) (hlo : 0 ≤ lo) (hhi : lo < HI_BASE)
    (hn : 0 ≤ hi) (hx : hi < 16) (ht : hi = HI_MAX → lo = 0) :
    ¬ ∃ s dhi dlo, LexLtWitness hi lo hi lo s dhi dlo := by
  rintro ⟨s, dhi, dlo, hw⟩
  have hsplit : CanonSplit (hi * HI_BASE + lo) hi lo := ⟨hn, hx, hlo, hhi, rfl, ht⟩
  exact absurd (lexLt_forces_lt hsplit hsplit hw) (lt_irrefl _)

/-- NON-VACUITY, the TRUE pole: a genuine bracket HAS a witness, on the `s = 0` branch. -/
theorem lexLt_witness_exists_interior (hi lo lo' : ℤ) (h : lo < lo') :
    LexLtWitness hi lo hi lo' 0 0 (lo' - lo - 1) := by
  refine ⟨Or.inl rfl, le_refl _, by omega, by ring, by ring, by ring⟩

/-! ## §7 — ⚠ WHAT REMAINS, PRICED.

**This file closes law #1 for `MapAbsent`. It does not widen the key**, and the two are ordered:
widening means changing these constraints, so doing it while the constraints were Rust-authored
would have written NEW Rust AIR — which law #1 forbids outright, transitionally or not. The
emission had to come first. It now has.

What the widening needs, measured rather than estimated:

  1. **`Digest9Key` does not exist.** Every wide `.absent` theorem in this tree
     (`MapAbsentImtGateWide`, `MapOpWideKey{,Gate,Weld,RowBoundary,CanonDischarge}`,
     `SortedTree{Insert,NonMembership}Wide8`, `LexCompare8Emit`, `HeapLeafWideEmit`, and 11 more)
     is stated at `Digest8Key = Lex (Fin 8 → ℤ)`. `MapOpWideKeyPigeonhole.no_injection_bytes32_to_canonKey8`
     proves `P^8 < 2^256` refutes 8 lanes for a 32-byte key, and
     `arity17_conflates_two_addresses` gives the collision for EVERY hash with no CR hypothesis.
     So the 17-felt wide leaf is not the target; a 19-felt (9+1+9) one is, and the 19-file tower
     must be ported to a `Fin 9` lex key that has no definition yet.
  2. **`MapOp.key` is one `EmittedExpr` beside `root : Fin 8 → EmittedExpr`** (`DescriptorIR2`).
     Widening it re-reds the whole `MapOp` proof tower and every emitted descriptor's JSON.
  3. **The nine-lane key encoder has no AIR face.** `KeyLanes9` is proved and has four Rust twins
     (`commit/src/typed.rs::canonical_32_to_lanes_9` and three siblings), and
     `Emit/KeyCanonicity9Emit.lean`'s `keyCanonical9At` is applied by NOTHING. Contrast the FIELDS
     nonet, which is emitted and consumed. The key nonet's canonicity block must be wired into the
     members before a nine-lane key can be range-bound in circuit.
  4. The comparator here is a `(hi4, lo27)` split of ONE felt. Nine lanes need the nine-limb lex
     comparator; `LexCompare8Emit.lexLt8Descriptor` is the eight-lane version of that gadget and
     has no emit face either.

None of that is a reason to keep a Rust-authored AIR, which is why it is not why this file stops.
-/

/-! ## §8 — The wire pin.

⚠ **A NAMED SEAM, not a closed one.** `circuit/descriptors/table-airs/` is a NEW subdirectory of
the descriptor set, and `scripts/emit_descriptors.py`'s `verify_provenance` walks `DESC.iterdir()`
(top-level files) plus an explicit `by-name/` — so a third subdirectory is **invisible to the
provenance stamp**. That is the same shape as the hole which let `by-name/predicate-arith.json`
drift into a deployed forgery, and it is named here rather than left to be discovered.

What DOES bind the artifact today, and it is not nothing: the emitted bytes are `include_bytes!`d
into `faithful_note_spend_exact_v3_identity`'s AIR-shape source closure, so an edit to the artifact
moves a COMPILED fingerprint. Plus the pins below, which fix the emission on the Lean side.

Routing `EmitTableAirs.lean` into `emit_descriptors.py` (so `check-descriptor-drift.sh` covers the
directory) is the remaining work, and it is the FIRST item of the follow-up, not a nice-to-have. -/

/-- The wire string the Rust interpreter ingests. -/
def MAP_ABSENT_JSON : String := emitTableAirJson mapAbsentTable

-- THE WIRE PIN. Byte LENGTH plus the structural `#guard`s in §5 (70 gates, 53 interactions in a
-- fixed per-bus split, width 358): any edit to a gate body, a tuple, a multiplicity or an offset
-- moves the length, and any edit to the SHAPE moves §5. A full byte golden is deliberately not
-- inlined — 79 KB of literal would dominate this file — so this is a pin, not an identity, and the
-- identity is the compiled `include_bytes!` closure named above.
-- (The checked-in artifact is these bytes plus ONE trailing newline — 79,348 on disk — which is
-- `by-name/`'s convention and which `JsonCursor` skips as whitespace.)
#guard MAP_ABSENT_JSON.length == 79347

/-- The emission is not empty and not a stub — the shape that would satisfy every count pin above
while asserting nothing. -/
theorem mapAbsentTable_is_not_empty : mapAbsentTable.gates ≠ [] := by
  simp [mapAbsentTable, mapAbsentGates]

end Dregg2.Circuit.Emit.MapAbsentTableEmit
