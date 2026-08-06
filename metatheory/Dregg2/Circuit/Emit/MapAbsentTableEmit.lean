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

open Dregg2.Circuit.TableAirIR
  (TExpr BusOp BusInteraction TableAir TableGate emitTableAirJson
   v k eSub eOneMinus gBool gAll decompGates decompQueries limbGeom decompCols
   canonHi canonLo canonDecompGates canonDecompQueries lexLtGates lexLtQueries
   group8 chipAbsorbTuple node8Tuple foldCurAt foldOutAt foldQueries)

set_option autoImplicit false

/-! ## §0 — Expression sugar.

⚠ MOVED. `v`/`k`/`eSub`/`eOneMinus`/`gBool` and the byte-limb decomposition gadget
(`decompGates`/`decompQueries`) were defined privately in this file in the first pass. They are
now `TableAirIR`'s, because the second table to need them would otherwise have re-derived them —
which is the drift the first pass named. `v c` is `TExpr.loc c` (this table is purely
row-local, so `nxt` appears nowhere below) and the decomposition gadget is parameterised by bit
width, instantiated here at `KEY_LO_BITS = 27`. -/

/-! ## §1 — The deployed column layout.

Transcribed from `descriptor_ir2.rs`'s `MA_*` constants and `heap_root.rs`'s `HEAP_TREE_DEPTH`.
The `#guard`s at the end of this section are the arithmetic that derives each offset from the one
before it, so a layout drift on either side cannot be silent. -/

/-- `HEAP_TREE_DEPTH`. -/
def DEPTH : Nat := 16
/-- `CHIP_OUT_LANES`. -/
def LANES : Nat := 8
/-- `KEY_LO_BITS`. -/
def LO_BITS : Nat := 27
/-- `2 ^ KEY_LO_BITS` — the canonical split base. -/
def HI_BASE : ℤ := 134217728
/-- `KEY_HI_MAX` = 15: `p − 1 = 15 · 2^27`. -/
def HI_MAX : ℤ := 15
/-- Full 4-bit limbs of a 27-bit value (`limb_geom(27).0`). -/
def LIMBS : Nat := (limbGeom LO_BITS).1
/-- Bits in the partial top limb (`limb_geom(27).1`). -/
def TOP_BITS : Nat := (limbGeom LO_BITS).2
/-- Columns one 27-bit decomposition costs (`decomp_cols(27)` = limbs + top bits). -/
def DECOMP : Nat := decompCols LO_BITS
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

/-! ## §2 — The canonical-split / comparator gadgets.

⚠ **HOISTED, 2026-08-01 (third pass).** `canonHi`/`canonLo`/`canonDecompGates`/
`canonDecompQueries`/`lexLtGates`/`lexLtQueries` — the Lean authors of the Rust
`eval_canon_decomp` and `eval_lex_lt` — were defined HERE in the second pass. The universal-memory
BOUNDARY is the second table to need them, so they now live in `TableAirIR` §6b: the same move §0
records for `v`/`k`/`decompGates`, and for the same reason.

⚑ `lexLtGates` also SPLIT there, into `lexLtRowLocalGates ++ lexLtBranchGates`, because the
boundary asserts the three BRANCH equations under `.transition` (the Rust `transition_only` flag)
while this table asserts them under `.all`. A per-table copy would have re-derived the algebra
beside a different filter, which `TableGate.transition_weakens` says is invisible to any check
that reads the body alone. The list THIS file builds is unchanged — `lexLtGates` is still the
concatenation — and the emitted artifact is byte-identical. -/

/-! ## §3 — The chip tuples.

⚠ **HOISTED, 2026-08-02 (eighth pass).** `group8` / `leafTuple` / `node8Tuple` / `foldCur` /
`foldOut` were defined HERE. `MapOps` is the second table to fold a Merkle path through the arity-16
`node8` compression — four paths, over two independent sibling/direction blocks — so they now live
in `TableAirIR` §6c: the same move §0 and §2 record for `v`/`k`/`decompGates` and for the comparator,
and for the same reason. `leafTuple` generalized to `chipAbsorbTuple` (arity from the declared column
LIST, as the Rust closure's own doc claims), and the per-level chain became `foldQueries`. The
emitted artifact is byte-identical; only the authorship moved. -/

/-- The digest column group the fold reads at level `lvl`. -/
abbrev foldCur (lvl : Nat) : Nat := foldCurAt MA_LO_LEAF MA_LO_CHAIN0 lvl

/-- The digest column group the fold WRITES at level `lvl`. -/
abbrev foldOut (lvl : Nat) : Nat := foldOutAt MA_LO_CHAIN0 MA_ROOT DEPTH lvl

/-- The 19-felt map-log tuple `[root8, key, value, op, new_root8]`. `.absent` carries the
canonical value `0` and op code `2`. -/
def mapLogTuple : List TExpr :=
  group8 MA_ROOT ++ [v MA_KEY, k 0, k 2] ++ group8 MA_NEW_ROOT

/-! ## §4 — THE TABLE. -/

/-- `is_real`, the row guard. -/
def gReal : TExpr := v MA_IS_REAL

/-- The gate BODIES, in the deleted Rust arm's emission order. ⚑ Every one is UNFILTERED
(`RowSel.all`) — the deployed arm called `builder.assert_zero` directly, never a row filter,
and this table reads no `nxt` column. That is what made it the one table portable against the
first-pass IR, and `mapAbsent_is_row_local` below states it as a checkable claim rather than
leaving it to this comment. -/
def mapAbsentGateBodies : List TExpr :=
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

/-- The gate list: every body unfiltered. -/
def mapAbsentGates : List TableGate := mapAbsentGateBodies.map gAll

/-- The bus interactions, in the deleted Rust arm's emission order. -/
def mapAbsentInteractions : List BusInteraction :=
  -- the three canonical decompositions' nibble + limb queries (multiplicity 1, as deployed:
  -- `eval_canon_decomp` is the UNCOUNTED variant, so a pad row still queries).
  canonDecompQueries BUS_BYTE MA_A_DEC0 (k 1) ++
  canonDecompQueries BUS_BYTE MA_K_DEC0 (k 1) ++
  canonDecompQueries BUS_BYTE MA_B_DEC0 (k 1) ++
  -- the two comparators' queries.
  lexLtQueries BUS_BYTE MA_CMP_LO0 (k 1) ++
  lexLtQueries BUS_BYTE MA_CMP_HI0 (k 1) ++
  -- the low leaf's arity-3 absorb, at multiplicity `is_real`.
  [⟨BUS_P2, .query, gReal, chipAbsorbTuple [MA_LO_ADDR, MA_LO_VALUE, MA_LO_NEXT] MA_LO_LEAF⟩] ++
  -- the depth-many `node8` folds up ONE path to the committed root.
  foldQueries BUS_P2 MA_LO_LEAF MA_LO_CHAIN0 MA_ROOT MA_LO_SIB0 MA_LO_DIR0 DEPTH gReal ++
  -- the gathered absent sub-log.
  [⟨BUS_MAP_LOG, .receive, gReal, mapLogTuple⟩]

/-- **`mapAbsentTable`** — the live double-spend gate's AIR, as a Lean object. -/
def mapAbsentTable : TableAir :=
  { name         := "dregg-ir2-map-absent-v1"
  , width        := MA_WIDTH
  , prepWidth    := 0
  , defs         := []
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

-- ⚑ SELECTOR + BUS-SIDE pins. Every gate is unfiltered and every chip/byte leg is a QUERY (this
-- table serves nothing), so a re-emission that re-scopes a gate or flips a lookup side moves one
-- of these rather than passing silently on the totals above.
#guard mapAbsentTable.gateCountSel .all == 70
#guard mapAbsentTable.gateCountSel .transition == 0
#guard mapAbsentTable.gateCountSel .first == 0
#guard mapAbsentTable.gateCountSel .last == 0
#guard mapAbsentTable.busCountOp "ir2_byte" .query == 35
#guard mapAbsentTable.busCountOp "ir2_byte" .provide == 0
#guard mapAbsentTable.busCountOp "ir2_p2" .query == 17
#guard mapAbsentTable.busCountOp "ir2_map_log" .receive == 1

-- Each gadget's own contribution, so a regression names the gadget rather than the total. ⓘ The
-- canonical-split / comparator rows moved to `TableAirIR` §6b with the gadgets themselves; what is
-- pinned HERE is the part this table authors.
#guard (chipAbsorbTuple [1, 2, 3] 4).length == 25
#guard (node8Tuple 10 20 30 40).length == 25
#guard mapLogTuple.length == 19

/-- ⚑ **THE TABLE IS ROW-LOCAL**, stated rather than commented: every gate is unfiltered. With
`TableGate.transition_weakens` (a `.transition` re-scope accepts strictly MORE) this is the
claim a selector drift would have to break, and it is now checkable by `decide` instead of by
reading 70 constructors. -/
theorem mapAbsent_is_row_local : ∀ g ∈ mapAbsentTable.gates, g.sel = .all := by
  intro g hg
  simp only [mapAbsentTable, mapAbsentGates, List.mem_map] at hg
  obtain ⟨_, _, rfl⟩ := hg
  rfl

/-- The fold really walks ONE path — level 0 reads the leaf, level `lvl+1` reads what level `lvl`
wrote, and the last level writes the COMMITTED root — instantiated at THIS table's blocks. The
general statements are `TableAirIR.fold_{is_a_chain,ends_at_root,starts_at_leaf}`; what is pinned
here is that the four column blocks handed to the emitter are the right four. -/
theorem fold_is_a_chain (lvl : Nat) (h : lvl + 1 < DEPTH) : foldOut lvl = foldCur (lvl + 1) :=
  Dregg2.Circuit.TableAirIR.fold_is_a_chain MA_LO_LEAF MA_LO_CHAIN0 MA_ROOT DEPTH lvl h

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

ⓘ **THE SEAM THE FIRST PASS NAMED IS CLOSED.** `scripts/emit_descriptors.py::verify_provenance`
now DISCOVERS subdirectories (`5dab39664`) rather than walking `DESC.iterdir()` plus a hardcoded
`by-name/`, so `circuit/descriptors/table-airs/` is stamped like everything else and
`check-descriptor-drift.sh` covers it. The first pass filed this as the first item of the
follow-up; it is done, and this paragraph is the record rather than a live warning.

What ALSO binds the artifact: the emitted bytes are `include_bytes!`d into
`faithful_note_spend_exact_v3_identity`'s AIR-shape source closure, so an edit to the artifact
moves a COMPILED fingerprint. Plus the pins below, which fix the emission on the Lean side. -/

/-- The wire string the Rust interpreter ingests. -/
def MAP_ABSENT_JSON : String := emitTableAirJson mapAbsentTable

-- THE WIRE PIN. Byte LENGTH plus the structural `#guard`s in §5 (70 gates, 53 interactions in a
-- fixed per-bus split, width 358): any edit to a gate body, a tuple, a multiplicity or an offset
-- moves the length, and any edit to the SHAPE moves §5. A full byte golden is deliberately not
-- inlined — 90 KB of literal would dominate this file — so this is a pin, not an identity, and the
-- identity is the compiled `include_bytes!` closure named above.
-- ⚠ THIS NUMBER MOVED in the second pass: the gate grammar gained a `RowSel` wrapper
-- (`{"sel":"all","body":…}`) and every leaf went `{"t":"var","v":c}` → `{"t":"loc","c":c}`, so the
-- artifact re-emits. The ALGEBRA is byte-for-byte the same object; the ENCODING is not.
-- (The checked-in artifact is these bytes plus ONE trailing newline, which is `by-name/`'s
-- convention and which `JsonCursor` skips as whitespace.)
#guard MAP_ABSENT_JSON.length == 70523

/-- The emission is not empty and not a stub — the shape that would satisfy every count pin above
while asserting nothing. -/
theorem mapAbsentTable_is_not_empty : mapAbsentTable.gates ≠ [] := by
  simp [mapAbsentTable, mapAbsentGates, mapAbsentGateBodies]

end Dregg2.Circuit.Emit.MapAbsentTableEmit
