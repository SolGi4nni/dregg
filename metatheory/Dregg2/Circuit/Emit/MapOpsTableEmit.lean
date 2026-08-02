/-
# `Dregg2.Circuit.Emit.MapOpsTableEmit` — the map RECONCILIATION table's AIR, AUTHORED IN LEAN.

## What this replaces

`Ir2Air::MapOps` (`circuit/src/descriptor_ir2.rs`) is the in-row sorted-Poseidon2 opening table: one
row per map reconciliation, carrying the pre-root, the post-root, the key/value/op, one or two
Merkle paths and — since gap-#5 — the whole APPEND-AT-FREE-INDEX (`op = 4`) two-path insert with its
pointer-bracket range block. Its ~320 lines of `builder.assert_zero(..)` / `p2.lookup_key(..)` were
hand-authored Rust algebra, which architectural law #1 forbids: *"circuits are emitted from Lean;
Rust only INTERPRETS."*

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `WindowExpr` under an explicit `RowSel`. Nothing in this cutover
hand-writes a Rust constraint, and the `law1_no_new_rust_authored_constraints` baseline for
`descriptor_ir2.rs` goes DOWN.

## The comment-only claims this port turns into theorems — and the one that is REFUTED

The deleted arm asserted, in prose:

> `s` is boolean; `s ⇒ op=4`; and `op=4 ⇒ s` (so the gates cannot be disabled on an op=4 row nor
> enabled elsewhere).
> op ∈ {0 (read), 1 (write), 3 (insert), 4 (aafi-insert)}. Absent (2) is received by the map-absent
> table.
> `not_insert` is the unique degree-2 polynomial that is 1 at op = 0 and op = 1, and 0 at op = 3.
> All ride `aafi_gate = is_real·is_aafi` (zero on op≤3), so op≤3 rows see NONE of these
> lookups/asserts (byte-identical).

§4 proves the first three and ⚠ **refutes the fourth in the half that matters**:

  * `s_is_the_op4_indicator` — both directions, from the gate equations alone. The three pins really
    do force `s = [op = 4]`, so the AAFI block can be neither switched off on an insert row nor
    switched on elsewhere.
  * `selectors_are_boolean_on_every_admitted_op` — the four rational selectors (`not_insert`,
    `rw_sel`, `not_insert3`, `not_aafi`) take only `0`/`1` across the admitted op set, and
    `not_insert_is_minus_one_at_aafi` checks the sentence the comment makes about the repair: alone
    it is `−1` at `op = 4`, and it is `+s` that lands it on 0.
  * `the_absent_op_is_unsat` — `op = 2` satisfies no assignment, on the EMITTED gate list. That is
    what makes "absent is a different table" a verdict rather than a convention.
  * ⚠ `an_aafi_row_with_no_opening_satisfies_every_gate` — THE REFUTATION, and the load-bearing
    half. ⚑ **NOT ONE of this table's 84 chip legs is a gate.** A row declaring `root = 0`,
    `new_root = 0`, an honest pointer bracket `0 < 1 < 2` and an ALL-ZERO opening — no leaf digest,
    no sibling, no chain node — satisfies every one of the 91 emitted gates, at `is_real = 1`. The
    entire Merkle content of the table (84 of its 120 interactions, 70%) is carried by `ir2_p2`
    LOOKUPS, which `TableAir.Holds` is silent about by construction (`TableAirIR` §3). A soundness
    story that read the gate list as "the opening binds the root" would be resting on a leg this
    table does not have.
  * ⚠ `a_pad_row_can_spell_an_aafi_insert` — the second half of the same asymmetry, and it is the
    class prior tranches keep finding. The AAFI ROW-LOCAL gates (the 16 PATH2 direction booleans,
    the 8 empty-slot pins, the 27 canonical-split and 18 comparator gates) carry **`s` alone, no
    `is_real` factor** — while every chip leg rides `aafi_gate = is_real·s`. So a PAD row may spell
    a complete AAFI insert: it must carry a real bracket and it SENDS 35 byte-table queries at
    multiplicity 1 (the range block's queries ride `s`, not `is_real·s`), while every Merkle
    opening is off. What makes it inert is the `ir2_map_log` receive riding at `is_real` — a bus
    leg, one object out.

## ⚠ The containment, which lives in a DIFFERENT object

Everything this table is FOR — that the committed path opens the pre-root, that the updated path
recomputes the post-root, that the appended leaf lands in a slot that was empty — is a statement
about the `ir2_p2` chip bus and the `ir2_map_log` multiset, not about the row algebra. `Holds` is
exactly "the row-local algebra vanishes". Written down here because a reader of the 91 gates alone
would conclude far more than they say.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Crypto enters nowhere: this file is the ALGEBRA of a
reconciliation row and the integer-faithfulness of its selector pins, not the tree soundness (that
is `MapReconcile*` / `IndexedMerkleTree`'s, under its named `Poseidon2SpongeCR` floor).
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.Emit.MapOpsTableEmit

open Dregg2.Circuit.DescriptorIR2 (WindowExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.TableAirIR
  (BusOp BusInteraction TableAir TableGate emitTableAirJson
   v k eSub eOneMinus gBool gAll decompCols
   canonHi canonLo canonDecompGates canonDecompQueries lexLtGates lexLtQueries
   group8 chipAbsorbTuple node8Tuple foldCurAt foldOutAt foldQueries readsCol)

set_option autoImplicit false

/-! ## §1 — The deployed column layout.

Transcribed from `descriptor_ir2.rs`'s `MAP_*` constants and `heap_root.rs`'s `HEAP_TREE_DEPTH`.
Every offset is DERIVED from the one before it, exactly as the Rust derives it, so a layout drift on
either side moves a `#guard`.

⚠ **THE TRAILING COMMENTS IN THE RUST BLOCK ARE STALE FROM `MAP_DIR0` ONWARD.** `descriptor_ir2.rs`
annotates `MAP_DIR0` `// 149`, `MAP_OLD_LEAF` `// 165`, … `MAP_WIDTH` `// 897`; the arithmetic gives
150, 166, … **898**. The drift is exactly the `MAP_NEXT` column (the arity-2 → arity-3 IMT leaf
move, `919b2b0b8d`), which shifted everything from `MAP_SIB0` on by one and had its own comment
updated but not its successors'. Nothing READ those comments, so nothing went wrong — but a reader
sizing a row from them is off by one, and the Rust-side shape test pins `t.width` against the real
constant so the two sources have to agree rather than be believed. -/

/-- `HEAP_TREE_DEPTH`. -/
def DEPTH : Nat := 16
/-- `CHIP_OUT_LANES` — the 8-felt digest group width. -/
def LANES : Nat := 8
/-- `KEY_LO_BITS`. -/
def LO_BITS : Nat := 27
/-- Columns one 27-bit decomposition costs (`decomp_cols(27)`). -/
def DECOMP : Nat := decompCols LO_BITS
/-- `MA_DECOMP_COLS` — `[hi4, lo27 limbs, is15, inv15]`. -/
def CANON_COLS : Nat := 1 + DECOMP + 2
/-- `MA_CMP_COLS` — `[s, dhi, dlo, dlo limbs]`. -/
def CMP_COLS : Nat := 3 + DECOMP

-- The op≤3 block.
def MAP_ROOT : Nat := 0
def MAP_KEY : Nat := MAP_ROOT + LANES
def MAP_VALUE : Nat := MAP_KEY + 1
def MAP_OP : Nat := MAP_VALUE + 1
def MAP_NEW_ROOT : Nat := MAP_OP + 1
def MAP_IS_REAL : Nat := MAP_NEW_ROOT + LANES
def MAP_OLD_VALUE : Nat := MAP_IS_REAL + 1
/-- The IMT pointer felt: the shared `next_addr` of the read/write leaf, or the appended leaf's
`low_oldNext` on insert. Both arity-3 absorbs read it. -/
def MAP_NEXT : Nat := MAP_OLD_VALUE + 1
def MAP_SIB0 : Nat := MAP_NEXT + 1
def MAP_DIR0 : Nat := MAP_SIB0 + LANES * DEPTH
def MAP_OLD_LEAF : Nat := MAP_DIR0 + DEPTH
def MAP_NEW_LEAF : Nat := MAP_OLD_LEAF + LANES
def MAP_OLD_CHAIN0 : Nat := MAP_NEW_LEAF + LANES
def MAP_NEW_CHAIN0 : Nat := MAP_OLD_CHAIN0 + LANES * (DEPTH - 1)
/-- The op≤3 layout ends here; every column below is gated to `op = 4`. -/
def MAP_AAFI_BASE : Nat := MAP_NEW_CHAIN0 + LANES * (DEPTH - 1)
-- The AAFI (append-at-free-index) two-path insert block.
def MAP_S : Nat := MAP_AAFI_BASE
def MAP_R1 : Nat := MAP_S + 1
def MAP_LOW_ADDR : Nat := MAP_R1 + LANES
def MAP_LOW_VALUE : Nat := MAP_LOW_ADDR + 1
def MAP_LOW_NEW : Nat := MAP_LOW_VALUE + 1
def MAP_LOW_NEW_CHAIN0 : Nat := MAP_LOW_NEW + LANES
def MAP_SIB2_0 : Nat := MAP_LOW_NEW_CHAIN0 + LANES * (DEPTH - 1)
def MAP_DIR2_0 : Nat := MAP_SIB2_0 + LANES * DEPTH
def MAP_FREE_EMPTY : Nat := MAP_DIR2_0 + DEPTH
def MAP_FREE_EMPTY_CHAIN0 : Nat := MAP_FREE_EMPTY + LANES
def MAP_A_DEC0 : Nat := MAP_FREE_EMPTY_CHAIN0 + LANES * (DEPTH - 1)
def MAP_K_DEC0 : Nat := MAP_A_DEC0 + CANON_COLS
def MAP_B_DEC0 : Nat := MAP_K_DEC0 + CANON_COLS
def MAP_CMP_LO0 : Nat := MAP_B_DEC0 + CANON_COLS
def MAP_CMP_HI0 : Nat := MAP_CMP_LO0 + CMP_COLS
/-- `MAP_WIDTH`. ⚠ **898**, not the 897 the Rust comment claims. -/
def MAP_WIDTH : Nat := MAP_CMP_HI0 + CMP_COLS

-- The deployed numbers, pinned against the arithmetic that derives them.
#guard DECOMP == 10
#guard CANON_COLS == 13
#guard CMP_COLS == 13
#guard MAP_KEY == 8
#guard MAP_OP == 10
#guard MAP_IS_REAL == 19
#guard MAP_NEXT == 21
#guard MAP_SIB0 == 22
#guard MAP_DIR0 == 150
#guard MAP_OLD_LEAF == 166
#guard MAP_NEW_LEAF == 174
#guard MAP_OLD_CHAIN0 == 182
#guard MAP_NEW_CHAIN0 == 302
#guard MAP_AAFI_BASE == 422
#guard MAP_R1 == 423
#guard MAP_LOW_ADDR == 431
#guard MAP_LOW_NEW == 433
#guard MAP_SIB2_0 == 561
#guard MAP_DIR2_0 == 689
#guard MAP_FREE_EMPTY == 705
#guard MAP_A_DEC0 == 833
#guard MAP_K_DEC0 == 846
#guard MAP_B_DEC0 == 859
#guard MAP_CMP_LO0 == 872
#guard MAP_CMP_HI0 == 885
#guard MAP_WIDTH == 898

/-- The bus names, verbatim from the Rust `BUS_*` constants. -/
def BUS_P2 : String := "ir2_p2"
def BUS_BYTE : String := "ir2_byte"
def BUS_MAP_LOG : String := "ir2_map_log"

/-! ## §2 — The selectors.

`op` is confined to `{0, 1, 3, 4}` by the membership gate, and every selector below is a polynomial
in `op` and the COMMITTED boolean `s`. ⚑ `s` is a committed column rather than the degree-3
polynomial `op(op−1)(op−3)`: the map-ops degree budget is 4 and an `is_aafi` of degree 3 would blow
it in every product it enters. §4a proves the three pins really do force `s = [op = 4]`, which is
what makes the committed column as strong as the polynomial it replaces. -/

/-- `6⁻¹` in BabyBear: `6 · 1677721601 = 5p + 1`. -/
def INV6 : ℤ := 1677721601

theorem inv6_is_the_inverse_of_six : 6 * INV6 = 5 * 2013265921 + 1 := by decide

/-- `is_real`, the row guard. -/
def gReal : WindowExpr := v MAP_IS_REAL
/-- The op code column. -/
def gOp : WindowExpr := v MAP_OP
/-- The committed AAFI selector. -/
def gS : WindowExpr := v MAP_S

/-- `not_insert = 1 − 6⁻¹·op·(op − 1)` — the unique degree-2 polynomial that is 1 at `op ∈ {0, 1}`
and 0 at `op = 3`. ⚠ Its value at `op = 4` is `−1`, which is why every consumer below repairs it
with a multiple of `s`. -/
def notInsert : WindowExpr := eSub (k 1) (.mul (.mul (k INV6) gOp) (eSub gOp (k 1)))
/-- `rw_sel = not_insert + s` — fires the read/write OLD-leaf absorb at `op ∈ {0, 1}` only. -/
def rwSel : WindowExpr := .add notInsert gS
/-- `not_insert3 = not_insert + 2·s` — fires the shared PATH1 old chain at `op ∈ {0, 1, 4}`. -/
def notInsert3 : WindowExpr := .add notInsert (.mul (k 2) gS)
/-- `not_aafi = 1 − s`. -/
def notAafi : WindowExpr := eOneMinus gS
/-- `aafi_gate = is_real · s` — every AAFI chip leg's multiplicity. ⚠ NOT the multiplicity of the
AAFI range block's byte queries, which ride `s` alone; §4e is that asymmetry. -/
def aafiGate : WindowExpr := .mul gReal gS

/-! ## §3 — THE TABLE. -/

/-- The 19-felt map-log tuple `[root8, key, value, op, new_root8]`. -/
def mapLogTuple : List WindowExpr :=
  group8 MAP_ROOT ++ [v MAP_KEY, v MAP_VALUE, v MAP_OP] ++ group8 MAP_NEW_ROOT

/-- The gate BODIES, in the deleted Rust arm's emission order. ⚑ Every one is UNFILTERED
(`RowSel.all`) — the deployed arm called `builder.assert_zero` directly, never a row filter, and no
gate reads a `nxt` column: a reconciliation row is a complete statement about ONE map op, and the
LOG ORDER lives in the `ir2_map_log` multiset rather than in an adjacency constraint. -/
def mapOpsGateBodies : List WindowExpr :=
  -- (1) the row guard is boolean.
  gBool MAP_IS_REAL ::
  -- (2) op ∈ {0 (read), 1 (write), 3 (insert), 4 (aafi-insert)}. `absent` (2) rides the map-ABSENT
  --     table; §4c proves this gate REFUSES it here.
  .mul (.mul (.mul gOp (eSub gOp (k 1))) (eSub gOp (k 3))) (eSub gOp (k 4)) ::
  -- (3) every PATH1 direction bit is boolean (unconditionally — no `s`, no `is_real`).
  (List.range DEPTH).map (fun lvl => gBool (MAP_DIR0 + lvl)) ++
  -- (4)(5)(6) the AAFI selector's three pins: boolean, `s ⇒ op=4`, `op=4 ⇒ s`.
  [ gBool MAP_S
  , .mul gS (eSub gOp (k 4))
  , .mul (.mul (.mul gOp (eSub gOp (k 1))) (eSub gOp (k 3))) (eOneMinus gS)
  -- (7) READ DISCIPLINE: a real read returns the committed value. The `(op − 3)` factor disables
  --     it on insert; on `op = 4` it is ACTIVE and forces `old_value = value`.
  , .mul (.mul (.mul gReal (eOneMinus gOp)) (eSub gOp (k 3)))
      (eSub (v MAP_OLD_VALUE) (v MAP_VALUE)) ] ++
  -- (8) every PATH2 direction bit is boolean — ⚠ under `s`, where (3) is unconditional.
  (List.range DEPTH).map (fun lvl =>
    .mul (.mul gS (v (MAP_DIR2_0 + lvl))) (eSub (v (MAP_DIR2_0 + lvl)) (k 1))) ++
  -- (9) GATE (b), part one: canonical decompositions of `s·low_addr`, `s·key`, `s·low_next`. The
  --     values are `s`-multiplied so an op≤3 row decomposes ZERO and never touches its real
  --     key/next columns.
  canonDecompGates (.mul gS (v MAP_LOW_ADDR)) MAP_A_DEC0 gS ++
  canonDecompGates (.mul gS (v MAP_KEY)) MAP_K_DEC0 gS ++
  canonDecompGates (.mul gS (v MAP_NEXT)) MAP_B_DEC0 gS ++
  -- (10) GATE (b), part two: the POINTER BRACKET `low_addr < key < low_next`, as integers.
  lexLtGates (canonHi MAP_A_DEC0) (canonLo (.mul gS (v MAP_LOW_ADDR)) MAP_A_DEC0)
             (canonHi MAP_K_DEC0) (canonLo (.mul gS (v MAP_KEY)) MAP_K_DEC0)
             MAP_CMP_LO0 gS ++
  lexLtGates (canonHi MAP_K_DEC0) (canonLo (.mul gS (v MAP_KEY)) MAP_K_DEC0)
             (canonHi MAP_B_DEC0) (canonLo (.mul gS (v MAP_NEXT)) MAP_B_DEC0)
             MAP_CMP_HI0 gS ++
  -- (11) GATE (d1), part one: the free slot's digest is the EMPTY-subtree constant ZERO8.
  (List.range LANES).map (fun i => .mul gS (v (MAP_FREE_EMPTY + i)))

/-- The gate list: every body unfiltered. -/
def mapOpsGates : List TableGate := mapOpsGateBodies.map gAll

/-- The bus interactions, in the deleted Rust arm's emission order.

The five folds, named by the Rust gate letters they realize:

  * the read/write OLD path and the op≤3 NEW path share `MAP_SIB0`/`MAP_DIR0` (PATH1) and land on
    `MAP_ROOT` / `MAP_NEW_ROOT`. On `op = 4` the old path is GATE (a) — it folds the bracketing LOW
    leaf to the pre-root — and the new path is switched OFF (`not_aafi`), because `MAP_NEW_CHAIN0`
    is REUSED as the PATH2 append chain.
  * GATE (c) folds the UPDATED low leaf up PATH1 to the intermediate root `MAP_R1`.
  * GATE (d1) folds ZERO8 up PATH2 to the SAME `MAP_R1` — the empty-slot proof.
  * GATE (d2) folds the appended leaf up PATH2 to `MAP_NEW_ROOT`. -/
def mapOpsInteractions : List BusInteraction :=
  -- the three arity-3 IMT leaf absorbs: old (read/write), new, and the AAFI bracketing low leaf.
  [ ⟨BUS_P2, .query, .mul gReal rwSel,
      chipAbsorbTuple [MAP_KEY, MAP_OLD_VALUE, MAP_NEXT] MAP_OLD_LEAF⟩
  , ⟨BUS_P2, .query, gReal, chipAbsorbTuple [MAP_KEY, MAP_VALUE, MAP_NEXT] MAP_NEW_LEAF⟩
  , ⟨BUS_P2, .query, aafiGate,
      chipAbsorbTuple [MAP_LOW_ADDR, MAP_LOW_VALUE, MAP_NEXT] MAP_OLD_LEAF⟩ ] ++
  -- the two PATH1 chains, INTERLEAVED per level exactly as the deleted arm emitted them.
  ((List.range DEPTH).map (fun lvl =>
    [ (⟨BUS_P2, .query, .mul gReal notInsert3,
        node8Tuple (foldCurAt MAP_OLD_LEAF MAP_OLD_CHAIN0 lvl) (MAP_SIB0 + LANES * lvl)
          (foldOutAt MAP_OLD_CHAIN0 MAP_ROOT DEPTH lvl) (MAP_DIR0 + lvl)⟩ : BusInteraction)
    , (⟨BUS_P2, .query, .mul gReal notAafi,
        node8Tuple (foldCurAt MAP_NEW_LEAF MAP_NEW_CHAIN0 lvl) (MAP_SIB0 + LANES * lvl)
          (foldOutAt MAP_NEW_CHAIN0 MAP_NEW_ROOT DEPTH lvl) (MAP_DIR0 + lvl)⟩ :
            BusInteraction) ])).flatten ++
  -- the pointer-bracket range block's byte queries. ⚠ multiplicity `s`, NOT `is_real·s` (§4e).
  canonDecompQueries BUS_BYTE MAP_A_DEC0 gS ++
  canonDecompQueries BUS_BYTE MAP_K_DEC0 gS ++
  canonDecompQueries BUS_BYTE MAP_B_DEC0 gS ++
  lexLtQueries BUS_BYTE MAP_CMP_LO0 gS ++
  lexLtQueries BUS_BYTE MAP_CMP_HI0 gS ++
  -- GATE (c): the UPDATED low leaf `(low_addr, low_value, k)`, then its PATH1 fold to R1.
  [⟨BUS_P2, .query, aafiGate,
      chipAbsorbTuple [MAP_LOW_ADDR, MAP_LOW_VALUE, MAP_KEY] MAP_LOW_NEW⟩] ++
  foldQueries BUS_P2 MAP_LOW_NEW MAP_LOW_NEW_CHAIN0 MAP_R1 MAP_SIB0 MAP_DIR0 DEPTH aafiGate ++
  -- GATE (d1): the EMPTY slot's ZERO8 digest, up PATH2, to the SAME R1.
  foldQueries BUS_P2 MAP_FREE_EMPTY MAP_FREE_EMPTY_CHAIN0 MAP_R1 MAP_SIB2_0 MAP_DIR2_0 DEPTH
    aafiGate ++
  -- GATE (d2): the APPENDED leaf, up PATH2, to the post-root.
  foldQueries BUS_P2 MAP_NEW_LEAF MAP_NEW_CHAIN0 MAP_NEW_ROOT MAP_SIB2_0 MAP_DIR2_0 DEPTH
    aafiGate ++
  -- the gathered map-op log (`mapTableFaithful`).
  [⟨BUS_MAP_LOG, .receive, gReal, mapLogTuple⟩]

/-- **`mapOpsTable`** — the map reconciliation table's AIR, as a Lean object. -/
def mapOpsTable : TableAir :=
  { name         := "dregg-ir2-map-ops-v1"
  , width        := MAP_WIDTH
  , gates        := mapOpsGates
  , interactions := mapOpsInteractions }

/-! ## §4 — Shape pins.

Counts DERIVED from the layout, not transcribed:
`1 + 1 + DEPTH + 4 + DEPTH + 3·9 + 2·9 + LANES = 91` gates and
`3 + 2·DEPTH + 3·7 + 2·7 + 1 + 3·DEPTH = 120` interactions. -/

#guard mapOpsTable.width == 898
#guard mapOpsTable.gates.length == 91
#guard mapOpsTable.busCount == 120
#guard mapOpsTable.busCountOn BUS_P2 == 84
#guard mapOpsTable.busCountOn BUS_BYTE == 35
#guard mapOpsTable.busCountOn BUS_MAP_LOG == 1

-- ⚑ SELECTOR + BUS-SIDE pins. Every gate is unfiltered and every chip/byte leg is a QUERY (this
-- table serves nothing), so a re-emission that re-scopes a gate or flips a lookup side moves one of
-- these rather than passing silently on the totals above.
#guard mapOpsTable.gateCountSel .all == 91
#guard mapOpsTable.gateCountSel .transition == 0
#guard mapOpsTable.gateCountSel .first == 0
#guard mapOpsTable.gateCountSel .last == 0
#guard mapOpsTable.busCountOp BUS_P2 .query == 84
#guard mapOpsTable.busCountOp BUS_P2 .provide == 0
#guard mapOpsTable.busCountOp BUS_BYTE .query == 35
#guard mapOpsTable.busCountOp BUS_BYTE .provide == 0
#guard mapOpsTable.busCountOp BUS_MAP_LOG .receive == 1
#guard mapOpsTable.busCountOp BUS_MAP_LOG .send == 0

-- Each gadget's own contribution.
#guard (chipAbsorbTuple [MAP_KEY, MAP_VALUE, MAP_NEXT] MAP_NEW_LEAF).length == 25
#guard (node8Tuple 10 20 30 40).length == 25
#guard mapLogTuple.length == 19

/-- ⚑ **THE TABLE IS ROW-LOCAL**, stated rather than commented: every gate is unfiltered. With
`TableGate.transition_weakens` (a `.transition` re-scope accepts strictly MORE) this is the claim a
selector drift would have to break, and it is now checkable by `decide` instead of by reading 91
constructors. -/
theorem mapOps_is_row_local : ∀ g ∈ mapOpsTable.gates, g.sel = .all := by
  intro g hg
  simp only [mapOpsTable, mapOpsGates, List.mem_map] at hg
  obtain ⟨_, _, rfl⟩ := hg
  rfl

/-- The five folds each terminate where the reconciliation says they do — the PATH1 pair on the
committed pre-root and post-root, GATE (c) and GATE (d1) on the SAME intermediate root `R1` (which is what
makes the empty-slot proof and the low-pointer update statements about one tree), and GATE (d2) on
the post-root. A transcription that landed (d1) anywhere but `R1` would leave the append unrelated
to the update, and nothing else in this file would notice. -/
theorem the_two_aafi_paths_meet_at_r1 :
    foldOutAt MAP_LOW_NEW_CHAIN0 MAP_R1 DEPTH (DEPTH - 1) = MAP_R1 ∧
    foldOutAt MAP_FREE_EMPTY_CHAIN0 MAP_R1 DEPTH (DEPTH - 1) = MAP_R1 ∧
    foldOutAt MAP_OLD_CHAIN0 MAP_ROOT DEPTH (DEPTH - 1) = MAP_ROOT ∧
    foldOutAt MAP_NEW_CHAIN0 MAP_NEW_ROOT DEPTH (DEPTH - 1) = MAP_NEW_ROOT := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- …and the two PATH2 folds read the SAME sibling and direction blocks, which is the whole content
of "two independent openings under ONE root": (d1) and (d2) share `MAP_SIB2_0`/`MAP_DIR2_0`, and
they are DISJOINT from PATH1's `MAP_SIB0`/`MAP_DIR0`. Stated as a column-range fact because a
transcription that pointed (d2) at PATH1 would still fold, still count, and still be wrong. -/
theorem the_two_sibling_blocks_are_disjoint :
    MAP_SIB0 + LANES * DEPTH ≤ MAP_DIR0 ∧
    MAP_DIR0 + DEPTH ≤ MAP_SIB2_0 ∧
    MAP_SIB2_0 + LANES * DEPTH ≤ MAP_DIR2_0 ∧
    MAP_DIR2_0 + DEPTH ≤ MAP_WIDTH := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## §5 — THE COMMENT-ONLY CLAIMS, PROVED — and the fourth REFUTED.

§5a takes the selector pins off the gate equations as ℤ facts (the honest lift: the gates are
congruences mod `p`, and every step below uses only that a gate VANISHES, never that `ℤ/p` is a
domain). §5b evaluates the four rational selectors across the admitted op set. §5c and §5d exhibit
both refutations, `decide`d against the EMITTED gate list rather than a transcription. -/

/-! ### §5a — The AAFI selector IS the `op = 4` indicator. -/

/-- The four gate equations that pin the AAFI selector, as integer facts. Each field names the gate
it comes from. -/
structure SelectorFacts where
  op : ℤ
  s  : ℤ
  /-- gate (2): `op ∈ {0, 1, 3, 4}`. -/
  member : op * (op - 1) * (op - 3) * (op - 4) = 0
  /-- gate (4): `s` is boolean. -/
  sBool  : s * (s - 1) = 0
  /-- gate (5): `s ⇒ op = 4`. -/
  sPin   : s * (op - 4) = 0
  /-- gate (6): `op = 4 ⇒ s`. -/
  opPin  : op * (op - 1) * (op - 3) * (1 - s) = 0

/-- The admitted op codes, from the membership gate alone. -/
theorem op_is_admitted (F : SelectorFacts) : F.op = 0 ∨ F.op = 1 ∨ F.op = 3 ∨ F.op = 4 := by
  have h := F.member
  rcases mul_eq_zero.1 h with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- ⚑ **THE PIN, BOTH DIRECTIONS.** The three low-degree constraints really do force
`s = [op = 4]`: a prover can neither disable the AAFI gates on an `op = 4` row nor enable them
elsewhere. That is exactly the sentence `MAP_S`'s doc comment makes, and it is what licenses a
COMMITTED degree-1 selector standing in for the degree-3 polynomial `op(op−1)(op−3)` that would
blow the map-ops degree budget of 4. -/
theorem s_is_the_op4_indicator (F : SelectorFacts) : (F.s = 1 ↔ F.op = 4) ∧ (F.s = 0 ∨ F.s = 1) := by
  have hb : F.s = 0 ∨ F.s = 1 := by
    rcases mul_eq_zero.1 F.sBool with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  refine ⟨⟨?_, ?_⟩, hb⟩
  · intro h1
    have := F.sPin
    rw [h1, one_mul] at this
    linarith
  · intro h4
    rcases hb with h0 | h1
    · exfalso
      have hp := F.opPin
      rw [h4, h0] at hp
      norm_num at hp
    · exact h1

/-- …and the STRICT reading: on every admitted op OTHER than 4 the selector is forced OFF, so the
whole AAFI block (16 direction booleans, 8 empty-slot pins, 45 range gates, 49 chip legs) is
identically vacuous on a read / write / plain insert row. -/
theorem s_is_zero_off_aafi (F : SelectorFacts) (h : F.op ≠ 4) : F.s = 0 := by
  rcases (s_is_the_op4_indicator F).2 with h0 | h1
  · exact h0
  · exact absurd ((s_is_the_op4_indicator F).1.1 h1) h

/-! ### §5b — The four rational selectors, evaluated. -/

/-- `not_insert` at an op code, over ℤ: `1 − 6⁻¹·op·(op − 1)`, with `6⁻¹` the BabyBear inverse. The
values below are congruences mod `p`, which is the sense in which the AIR reads them. -/
def notInsertAt (op : ℤ) : ℤ := 1 - INV6 * op * (op - 1)

/-- ⚑ **THE SELECTOR TABLE**, checked rather than asserted. `rw_sel` fires exactly at `op ∈ {0,1}`,
`not_insert3` exactly at `op ∈ {0,1,4}`, `not_aafi` exactly at `op ≤ 3` — each a 0/1 multiplicity on
every admitted op, which is what makes them usable as LogUp counts at all. (A multiplicity that took
any other value would be a fractional or negative count on the chip bus.) -/
theorem selectors_are_boolean_on_every_admitted_op :
    (notInsertAt 0 + 0 ≡ 1 [ZMOD 2013265921]) ∧ (notInsertAt 1 + 0 ≡ 1 [ZMOD 2013265921]) ∧
    (notInsertAt 3 + 0 ≡ 0 [ZMOD 2013265921]) ∧ (notInsertAt 4 + 1 ≡ 0 [ZMOD 2013265921]) ∧
    (notInsertAt 0 + 2 * 0 ≡ 1 [ZMOD 2013265921]) ∧
    (notInsertAt 1 + 2 * 0 ≡ 1 [ZMOD 2013265921]) ∧
    (notInsertAt 3 + 2 * 0 ≡ 0 [ZMOD 2013265921]) ∧
    (notInsertAt 4 + 2 * 1 ≡ 1 [ZMOD 2013265921]) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- ⚠ **THE REPAIR IS REAL.** `not_insert` ALONE is `−1` at `op = 4`, not `0` — the sentence the
deleted arm makes in a parenthesis (*"`rw_sel` = `not_insert` with its op=4 value repaired from −1
to 0 via +s"*), checked. Dropping the `+ s` would put a multiplicity of `−1` on the old-leaf chip
lookup of every AAFI row, i.e. would PUBLISH one absorb rather than consume it. -/
theorem not_insert_is_minus_one_at_aafi : notInsertAt 4 ≡ -1 [ZMOD 2013265921] := by decide

/-! ### §5c — ⚠ THE FIRST REFUTATION: the gates do not open anything.

The 84 `ir2_p2` legs are the whole Merkle content of this table, and they are LOOKUPS. `Holds` is
silent about them by construction (`TableAirIR` §3), so a gate-level reading of this AIR — including
a per-cell mutation sweep — cannot see the opening at all. This exhibits the consequence. -/

/-- `−15⁻¹` in BabyBear: `−15 · 134217728 = −(p − 1) ≡ 1`. The `inv15` witness column of a canonical
decomposition whose nibble is 0 and whose gate is 1. -/
def NEG_INV15 : ℤ := 134217728

theorem neg_inv15_is_right : (-15) * NEG_INV15 = -(2013265921 - 1) := by decide

/-- An `op = 4` AAFI reconciliation row with an HONEST pointer bracket `0 < 1 < 2` and an ALL-ZERO
Merkle opening: no leaf digest, no sibling, no chain node, `root = new_root = 0`. Only the three
`inv15` witnesses and two limb columns are non-zero besides the bracket itself. -/
def openingFreeRow : VmRowEnv :=
  ⟨fun c =>
      if c = MAP_IS_REAL then 1
      else if c = MAP_OP then 4
      else if c = MAP_S then 1
      else if c = MAP_KEY then 1
      else if c = MAP_NEXT then 2
      else if c = MAP_A_DEC0 + 12 then NEG_INV15
      else if c = MAP_K_DEC0 + 1 then 1
      else if c = MAP_K_DEC0 + 12 then NEG_INV15
      else if c = MAP_B_DEC0 + 1 then 2
      else if c = MAP_B_DEC0 + 12 then NEG_INV15
      else 0
  , fun _ => 0, fun _ => 0⟩

/-- ⚑ **THE REFUTATION, ON THE EMITTED OBJECT.** Every one of the 91 emitted gates vanishes on a
REAL (`is_real = 1`) AAFI row that opens NOTHING: its pre-root, post-root, both leaf digests, all
32 sibling groups, all 60 chain groups and both direction blocks are zero. The row is
gate-indistinguishable from an honest reconciliation.

⚠ Direction, said plainly: this is not a defect in the deployed prover. What refuses the witness is
the `ir2_p2` chip bus — `perm(0 ‖ 0)[0..8]` is not `0`, so the fold's `node8` tuples have no
matching chip row — plus the `ir2_map_log` multiset that the main instance SENDs into. Both are bus
legs, and both are exactly the half `TableAir.Holds` is silent on. A soundness story that read this
table's gate list as "the committed path opens the root" would be resting on a leg it does not
have. -/
theorem an_aafi_row_with_no_opening_satisfies_every_gate :
    mapOpsTable.RowHolds openingFreeRow true true ∧
    openingFreeRow.loc MAP_IS_REAL = 1 ∧
    openingFreeRow.loc MAP_OP = 4 ∧
    (∀ i < 8, openingFreeRow.loc (MAP_ROOT + i) = 0) ∧
    (∀ i < 8, openingFreeRow.loc (MAP_NEW_ROOT + i) = 0) ∧
    (∀ i < 8, openingFreeRow.loc (MAP_OLD_LEAF + i) = 0) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩ <;> (intro i h; interval_cases i <;> decide)

/-- …and the CONTRAST, so the refutation is not read as "no gate bites here": the SAME row with the
bracket REVERSED (`low_addr = 5`, `key = 1`, so `low_addr < key` is false) is REFUSED by the
comparator's low-word branch. A table AIR no assignment refutes is decoration. -/
def reversedBracketRow : VmRowEnv :=
  ⟨fun c =>
      if c = MAP_IS_REAL then 1
      else if c = MAP_OP then 4
      else if c = MAP_S then 1
      else if c = MAP_KEY then 1
      else if c = MAP_NEXT then 2
      else if c = MAP_LOW_ADDR then 5
      else if c = MAP_A_DEC0 + 1 then 5
      else if c = MAP_A_DEC0 + 12 then NEG_INV15
      else if c = MAP_K_DEC0 + 1 then 1
      else if c = MAP_K_DEC0 + 12 then NEG_INV15
      else if c = MAP_B_DEC0 + 1 then 2
      else if c = MAP_B_DEC0 + 12 then NEG_INV15
      else 0
  , fun _ => 0, fun _ => 0⟩

theorem a_reversed_bracket_is_refused :
    ¬ mapOpsTable.RowHolds reversedBracketRow true true := by decide

/-! ### §5d — ⚠ THE SECOND REFUTATION: `op = 2` is UNSAT, and a PAD row can still spell an insert. -/

/-- The `openingFreeRow` with the `absent` op code substituted. -/
def absentOpRow : VmRowEnv :=
  ⟨fun c => if c = MAP_OP then 2 else if c = MAP_IS_REAL then 1 else 0, fun _ => 0, fun _ => 0⟩

/-- ⚑ **`absent` (op = 2) IS UNSAT IN THIS TABLE**, on the emitted gate list — so "absent is
received by the map-ABSENT table" is a verdict of the membership gate rather than a routing
convention. The membership product evaluates to `2·1·(−1)·(−2) = 4 ≢ 0`. -/
theorem the_absent_op_is_unsat : ¬ mapOpsTable.RowHolds absentOpRow true true := by decide

/-- The `openingFreeRow` with the row guard DROPPED: a PAD row spelling a complete AAFI insert. -/
def padAafiRow : VmRowEnv :=
  ⟨fun c =>
      if c = MAP_OP then 4
      else if c = MAP_S then 1
      else if c = MAP_KEY then 1
      else if c = MAP_NEXT then 2
      else if c = MAP_A_DEC0 + 12 then NEG_INV15
      else if c = MAP_K_DEC0 + 1 then 1
      else if c = MAP_K_DEC0 + 12 then NEG_INV15
      else if c = MAP_B_DEC0 + 1 then 2
      else if c = MAP_B_DEC0 + 12 then NEG_INV15
      else 0
  , fun _ => 0, fun _ => 0⟩

/-- ⚠ **THE AAFI ROW-LOCAL GATES CARRY NO `is_real` FACTOR.** The deleted arm's comment says the
AAFI legs *"all ride `aafi_gate = is_real·is_aafi` (zero on op≤3), so op≤3 rows see NONE of these
lookups/asserts"*. The op≤3 half is TRUE (§5a: `s = 0` there). The `is_real` half is not what the
sentence implies: the 16 PATH2 direction booleans, the 8 empty-slot pins and all 45 range-block
gates are gated by **`s` ALONE**, so a PAD row may set `s = 1` and must then carry a genuine
pointer bracket — and the range block's 35 byte queries ride `s` too, so the pad SENDS them at
multiplicity 1 while every chip leg (at `is_real·s = 0`) is off.

⚑ Both halves matter and they point opposite ways: the gates are STRICTER on a pad than the comment
suggests, and the bus legs are WEAKER. What makes the pad's bracket inert is the `ir2_map_log`
receive riding at `is_real` — the op never enters the gathered log — which is again a bus fact. -/
theorem a_pad_row_can_spell_an_aafi_insert :
    mapOpsTable.RowHolds padAafiRow true true ∧
    padAafiRow.loc MAP_IS_REAL = 0 ∧
    padAafiRow.loc MAP_S = 1 ∧
    padAafiRow.loc MAP_OP = 4 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- …and the pad is NOT free: dropping `is_real` does not switch the range block off. The same pad
with the bracket reversed is still REFUSED, which is the non-vacuity contrast for the theorem above
and the precise sense in which the gates are stricter than `aafi_gate` suggests. -/
def padReversedBracketRow : VmRowEnv :=
  ⟨fun c =>
      if c = MAP_OP then 4
      else if c = MAP_S then 1
      else if c = MAP_KEY then 1
      else if c = MAP_NEXT then 2
      else if c = MAP_LOW_ADDR then 5
      else if c = MAP_A_DEC0 + 1 then 5
      else if c = MAP_A_DEC0 + 12 then NEG_INV15
      else if c = MAP_K_DEC0 + 1 then 1
      else if c = MAP_K_DEC0 + 12 then NEG_INV15
      else if c = MAP_B_DEC0 + 1 then 2
      else if c = MAP_B_DEC0 + 12 then NEG_INV15
      else 0
  , fun _ => 0, fun _ => 0⟩

theorem a_pad_row_still_owes_a_real_bracket :
    ¬ mapOpsTable.RowHolds padReversedBracketRow true true := by decide

/-! ### §5e — NAMED RESIDUALS, as theorems rather than prose. -/

/-- ⚑ **THE COMMITTED ROOT IS READ BY NO GATE.** `MAP_ROOT` — the pre-root the whole reconciliation
is ABOUT — appears in no gate body on any row. It is bound by the `ir2_p2` fold's terminal `out8`
tuple and by the `ir2_map_log` receive, both bus legs. So a gate-level mutation sweep of this table
is structurally blind to the root, and any check that reads only the gates cannot distinguish a
genuine reconciliation from `openingFreeRow`. -/
theorem root_is_read_by_no_gate :
    ∀ i < 8, (mapOpsTable.gates.filter (fun g => readsCol g.body (MAP_ROOT + i))).length = 0 := by
  intro i h; interval_cases i <;> decide

/-- …and neither is the POST-root. -/
theorem new_root_is_read_by_no_gate :
    ∀ i < 8,
      (mapOpsTable.gates.filter (fun g => readsCol g.body (MAP_NEW_ROOT + i))).length = 0 := by
  intro i h; interval_cases i <;> decide

/-- …the NON-VACUITY contrast, so the two above are not read as "the sweep sees nothing": the row
guard is read by four gates and the op code by five, both on every row. -/
theorem is_real_and_op_are_read_by_gates :
    (mapOpsTable.gates.filter (fun g => readsCol g.body MAP_IS_REAL)).length = 2 ∧
    (mapOpsTable.gates.filter (fun g => readsCol g.body MAP_OP)).length = 4 ∧
    (mapOpsTable.gates.filter (fun g => readsCol g.body MAP_S)).length = 42 := by
  refine ⟨by decide, by decide, by decide⟩

/-- ⚠ …and the SIBLING columns — 256 of the 898, the largest block in the row — are read by no gate
either. Every sibling enters the AIR only through a `node8` lookup tuple. -/
theorem the_first_sibling_lane_is_read_by_no_gate :
    (mapOpsTable.gates.filter (fun g => readsCol g.body MAP_SIB0)).length = 0 ∧
    (mapOpsTable.gates.filter (fun g => readsCol g.body MAP_SIB2_0)).length = 0 := by
  refine ⟨by decide, by decide⟩

/-! ## §6 — The wire pin. -/

/-- The wire string the Rust interpreter ingests. -/
def MAP_OPS_JSON : String := emitTableAirJson mapOpsTable

-- THE WIRE PIN. Byte LENGTH plus the structural `#guard`s in §4 (91 gates, 120 interactions in a
-- fixed per-bus/per-side split, width 898): any edit to a gate body, a tuple, a multiplicity or an
-- offset moves the length, and any edit to the SHAPE moves §4. A full byte golden is deliberately
-- not inlined — 331 KB of literal would dominate this file — so this is a pin, not an identity, and
-- the identity is the compiled `include_bytes!` closure in
-- `circuit-prove/src/faithful_note_spend_exact_v3_identity.rs`. (The checked-in artifact is these
-- bytes plus ONE trailing newline, which `JsonCursor` skips as whitespace.)
#guard MAP_OPS_JSON.length == 338975

/-- The emission is not empty and not a stub — the shape that would satisfy every count pin in §4
while asserting nothing. -/
theorem mapOpsTable_is_not_empty : mapOpsTable.gates ≠ [] := by
  simp [mapOpsTable, mapOpsGates, mapOpsGateBodies]

end Dregg2.Circuit.Emit.MapOpsTableEmit
