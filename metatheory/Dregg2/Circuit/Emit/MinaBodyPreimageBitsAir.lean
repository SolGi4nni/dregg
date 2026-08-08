/-
# `Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir` — **THE 2 381 CHUNK BITS STOP BEING FREE.**

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this is a **Lean-authored AIR**. `bodyBitsDesc` is
`EffectLower.lowerTiedAir` applied to the `EffectAir` source `bodyBitsAir` (§3). There is **no
hand-written `VmConstraint2` in this file** and Rust authors nothing; Rust proves the artifact.

## ⚑⚑ THE HOLE THIS CLOSES

`MinaStateBodyHashChain` §8 residual 2, in its own words:

> *"**`pack_to_fields` IS NOT IN CIRCUIT.** … nothing gates that they are the packing of 819
> width-declared chunks, and in particular **nothing forces each chunk `< 2^n`**, without which the
> packing is not injective. That is the next rung and it is cheap: 781 of the 819 chunks are ONE
> BIT."*

`Bridge.MinaPackInjective` proves the arithmetic half — `packing_is_injective`, and
`the_range_hypothesis_is_load_bearing` exhibits the alias that follows when the hypothesis is
dropped:

    packToFields ⟨[], [(1, 1), (0, 1)]⟩ = [2] = packToFields ⟨[], [(0, 1), (2, 1)]⟩

Same 49 absorbed elements, same `state_body_hash`, same 25-link chain, same root — **and every link
honest.** This file is the gate that discharges the hypothesis.

## ⚑ THE SHAPE, AND WHY IT IS BITS AND NOT CHUNKS

The brief for this rung read *"booleanity for the 781, declared-width for the rest"*. Re-derived on
the deployed field: **a declared width IS a bit count, and at BabyBear a 32- or 64-bit chunk has no
column to live in** (`p ≈ 2^31`). So every chunk is carried as its own bit slice and the 38 wide
chunks are gated by the SAME `x·(x−1) = 0` the 781 booleans are. `MinaPackInjective.bitsToNat_lt` is
that identification as a theorem: `n` boolean columns cannot denote a value `≥ 2^n`, whatever the
prover writes.

⚑ **AND THE PRICE MOVED THE OTHER WAY FROM THE BRIEF.** The brief warned *"your chunk gates ADD
range lookups; price them in committed width"* — because `MainLayout::build` appends a nibble aux
block per range lookup and range decomposition was 71.7% of the unnarrowed accumulator row. **This
descriptor declares NO table and emits NO lookup.** A booleanity gate is a degree-2 window gate, not
a bus query, so the committed width is the declared width: **2 683 declared, 2 683 committed, 1.00×**
(`the_committed_width_is_the_declared_width`, and `circuit/tests/mina_body_preimage_bits_proves.rs`
re-derives it from `decomp_cols_pub` on the emitted bytes). Against `dregg-pasta-fp-chainlink::v1`'s
469 → 1 037 (2.21×) and the accumulator's 3 048 → 10 756 (3.53×), the chunk gates are the first rung
in this cone whose aux block is empty.

## Layout — ONE ROW, and the row is the whole packed preimage

    col 0 .. 2380         BIT j      the j-th bit of the packed half of `Body.to_input`,
                                     chunks in append order, MSB-first WITHIN each chunk
    col 2381 .. 2682      PLIMB e k  limb k of packed field element 38+e, base 256, k = 0 lowest
                                     (e < 11, k < ⌈W_e/8⌉ — 32,29,29,29,32,29,28,32,28,25,9)

    PI 0 .. 301           PLIMB e k, published so a recursion fold can reach it from
                          `air_public_targets` — the layout `MinaStateBodyHashChain`'s absorbed
                          block already speaks (`SK = 32` eight-bit limbs an element)

⚑ **WHY THE BIT COLUMNS ARE 2 381 AND NOT 11 × 254.** A packed element is `⌈W_e/8⌉` bytes wide and
the eleven runs have DIFFERENT widths (254, 226, 229, 229, 254, 227, 224, 254, 223, 194, 67). Giving
every element a uniform 254 bit columns would leave `254 − W_e` columns that the honest witness sets
to zero and nothing refuses — a PHANTOM CHUNK, and an element that is the packing of no in-range
stream at all. The bit columns are exactly the stream's, so the phantom is unrepresentable rather
than gated.

⚑ **THE SCHEDULE IS DESCRIPTOR SHAPE, NOT WITNESS — AND THAT IS LOAD-BEARING.**
`MinaPackInjective.the_schedule_hypothesis_is_load_bearing` exhibits `[(1,1)]` and `[(1,2)]`: both in
range, both packing to `[1]`. A prover who may DECLARE the widths chooses the reading. Here the
widths are the slice lengths of a constant partition
(`the_run_schedule_is_the_real_blocks_packing`), and `MinaStateHashPackPrice.
the_packing_control_flow_reads_only_the_width` is why that is legitimate: `packStep`'s branch is a
function of `(n, accN)` and never of a value, so the chunk boundaries of a `Protocol_state.Body` are
fixed by its TYPE and are the same for every Mina block.

## ⚑ WHAT THIS BUYS, IN THE UNITS THE CAMPAIGN USES — AND WHAT IT DOES NOT

**Of the `state_body_hash` preimage — 38 whole field elements and 819 width-declared chunks — this
rung constrains the 819 chunks, all 2 381 bits of them, and none of the 38 field elements.**

  * ⚑ **CONSTRAINED: 2 381 bits.** Every chunk is a bit slice of a boolean vector, so every chunk is
    below its declared width (`MinaPackInjective.the_boolean_gates_force_the_range`), so
    `packing_is_injective` applies and the eleven packed elements determine all 819 chunk values
    exactly once (`MinaPackInjective.the_gated_bits_are_determined_by_the_packing`).
  * ⚠ **NOT CONSTRAINED: the 38 whole field elements.** They pass through `packToFields` untouched,
    have no declared width and no bits here. They are elements 0..37 of the absorbed stream and this
    descriptor has no column for them. That half of the preimage is still what
    `PICKLES_OPENING_WITNESSED` covers.
  * ⚠ **AND THE ELEVEN LIMB BLOCKS ARE PUBLISHED, NOT YET WELDED.** Publication is what makes the
    weld REACHABLE — a `proofBind`/fold reads `air_public_targets`, so an unpublished column cannot
    be `cb.connect`ed at all, which is the same gap `LightClientAnchorConnectivity.
    minaLink_body_hash_is_joined_but_not_published` names one object over. Until a fold connects
    these 302 PI slots to `MinaStateBodyHashChain`'s links 19..24 absorbed blocks, the tie between
    "these bits" and "that chain's stream" is an EXECUTOR comparison. Said plainly rather than
    implied: **a prover still chooses which 2 381 bits, and this rung says only that they ARE 2 381
    bits.**

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

**2026-08-08 — A NEW DESCRIPTOR, `dregg-mina-body-preimage-bits::v1`.** Nothing existing changes
shape. It emits `circuit/descriptors/by-name/dregg-mina-body-preimage-bits-v1.json` and MINTS a VK
for it; no VK rotates, nothing re-genesises, and `PROVENANCE.json` gains no row that this file
stamps — the stamp is the operator's ceremony and four rows already await it.

## Import line for the root: `import Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir`
-/
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.GateExpr
import Dregg2.Bridge.MinaPackInjective

namespace Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir

open Dregg2.Circuit (Assignment Expr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Bridge.MinaStateHashDerive
open Dregg2.Bridge.MinaPackInjective (bitsToNat chunksOfSlices InRange PositiveWidths
  the_boolean_gates_force_the_range the_gated_bits_are_determined_by_the_packing)

set_option autoImplicit false
set_option maxRecDepth 2000000
-- ⚑ 3 085 legs through `lowerAir`, and the `rfl` shape pins below reduce the whole emitted list.
set_option maxHeartbeats 3200000

/-! ## §1 — ⚑ THE RUN SCHEDULE, AS SHAPE — AND TIED TO THE REAL BLOCK'S PACKING. -/

/-- `packStep`'s boundary rule, read as a grouping of the WIDTH schedule alone. ⚑ Legitimate
because `MinaStateHashPackPrice.the_packing_control_flow_reads_only_the_width` proves the branch
never reads a value. -/
def runsOfWidths (ws : List Nat) : List (List Nat) :=
  let step : (List (List Nat) × List Nat × Nat) → Nat → (List (List Nat) × List Nat × Nat) :=
    fun (done, cur, accN) n =>
      if n + accN < fieldSizeInBits then (done, cur ++ [n], n + accN) else (done ++ [cur], [n], n)
  match ws.foldl step ([], [], 0) with
  | (done, cur, accN) => if accN > 0 then done ++ [cur] else done

/-- ⚑ **THE ELEVEN RUN WIDTHS.** How many bits of the chunk stream each packed field element holds.
Not uniform, and that is why the bit columns are the STREAM's rather than eleven fixed blocks. -/
def RUN_WIDTH : List Nat := [254, 226, 229, 229, 254, 227, 224, 254, 223, 194, 67]

/-- The stream-bit offset each run starts at — the running sum of `RUN_WIDTH`. -/
def RUN_START : List Nat := [0, 254, 480, 709, 938, 1192, 1419, 1643, 1897, 2120, 2314]

def NELEM : Nat := 11
def NBITS : Nat := 2381

/-- ⚑ **HOW MANY LIMBS EACH ELEMENT GETS — `⌈W_e/8⌉`, AND NOT A UNIFORM 32.**

⚠ This is not a saving, it is a REFUSAL. A uniform 32-limb block would give element 10 (67 bits)
twenty-three limbs whose gate is `PLIMB = 0` — a published column no gate joins to any other, i.e.
**twenty-three decorative anchors**, fifty across the eleven elements. `LightClientAnchorConnectivity`
measures exactly that and `scripts/check-descriptor-anchor-inertness.py` is the ratchet. Allocating
`⌈W_e/8⌉` makes the empty limb unrepresentable instead of published-and-inert.

⚠ **AND SAY WHAT THAT LEAVES OWED**, because it moves an obligation rather than removing one: the
chain's absorbed block is `SK = 32` limbs an element, so the weld must connect these `⌈W_e/8⌉` and
pin the remaining `32 − ⌈W_e/8⌉` chain-side limbs to ZERO. `the_high_limbs_of_the_real_elements_are_
zero` is that they are zero in the honest witness; forcing it is the weld's job and §7 names it. -/
def LIMB_COUNT : List Nat := [32, 29, 29, 29, 32, 29, 28, 32, 28, 25, 9]

/-- The PI offset each element's limb block starts at — the running sum of `LIMB_COUNT`. -/
def LIMB_BASE : List Nat := [0, 32, 61, 90, 119, 151, 180, 208, 240, 268, 293]

def NLIMB : Nat := 302

def limbCount (e : Nat) : Nat := LIMB_COUNT.getD e 0
def limbBase (e : Nat) : Nat := LIMB_BASE.getD e 0

def runWidth (e : Nat) : Nat := RUN_WIDTH.getD e 0
def runStart (e : Nat) : Nat := RUN_START.getD e 0

/-- ⚑ The limb allocation IS `⌈W_e/8⌉`, and the bases are its running sum — derived from
`RUN_WIDTH`, not written down beside it. -/
theorem the_limb_allocation_is_the_run_widths :
    (∀ e < NELEM, limbCount e = (runWidth e + 7) / 8)
      ∧ (∀ e < NELEM, limbBase e + limbCount e = limbBase (e + 1) ∨ e + 1 = NELEM)
      ∧ LIMB_COUNT.foldl (· + ·) 0 = NLIMB
      ∧ limbBase 10 + limbCount 10 = NLIMB := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> decide




/-- The eleven runs partition the 2 381 bits with nothing left over and nothing counted twice. -/
theorem the_runs_partition_the_stream :
    RUN_WIDTH.length = NELEM ∧ RUN_START.length = NELEM
      ∧ RUN_WIDTH.foldl (· + ·) 0 = NBITS
      ∧ ∀ e < NELEM, runStart e + runWidth e = runStart (e + 1) ∨ e + 1 = NELEM := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  decide

/-- ⚑⚑ **AND THE SCHEDULE IS THE REAL BLOCK'S**, not a transcription of a printout: grouping the
devnet block's own 819 declared widths by `packStep`'s boundary rule gives exactly these eleven
runs. ⚠ Compiled: it reduces the 1 544-byte binprot parse, a two-block SHA-256 and the 819-chunk
assembly — the same object `MinaStateHashPackPrice` measures compiled. -/
theorem the_run_schedule_is_the_real_blocks_packing :
    (runsOfWidths Dregg2.Bridge.MinaStateHashPackPrice.chunkWidths).map
        (fun r => r.foldl (· + ·) 0) = RUN_WIDTH := by native_decide

/-! ## §2 — the column layout and the PI slots. -/

/-- **`BIT j`** — bit `j` of the packed half of `Body.to_input`, chunks in append order and MSB-first
within each chunk (the order `packStep`'s `acc · 2^n + x` places them in). -/
def BIT (j : Nat) : Nat := j

/-- **`PLIMB e k`** — limb `k` of packed field element `38 + e`, base 256, `k = 0` least
significant. ⚑ The `SK = 32` eight-bit limbs `MinaStateBodyHashChain.bodyAbsorbedBlock` already
publishes for the same element, so a weld is a slice comparison and no re-encoding. -/
def PLIMB (e k : Nat) : Nat := NBITS + limbBase e + k

/-- Trace width: the stream's bits, then the eleven limb blocks. -/
def BODY_BITS_WIDTH : Nat := NBITS + NLIMB

/-- PI slot of `PLIMB e k`. -/
def PI_PLIMB (e k : Nat) : Nat := limbBase e + k

def BODY_BITS_PI_COUNT : Nat := NLIMB

theorem the_layout_is_wellformed :
    BODY_BITS_WIDTH = 2683 ∧ BODY_BITS_PI_COUNT = 302
      ∧ BIT 0 = 0 ∧ BIT (NBITS - 1) = 2380
      ∧ PLIMB 0 0 = 2381 ∧ PLIMB 10 8 = 2682
      ∧ PLIMB 10 8 < BODY_BITS_WIDTH
      ∧ PI_PLIMB 10 8 < BODY_BITS_PI_COUNT := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide

/-! ## §3 — the SOURCE legs. Every one of them is a window gate; not one is a lookup. -/

open WindowExpr (loc)

/-- ⚑ **THE BOOLEANITY LEG** — `x·(x−1) = 0`, `GateExpr.gBool`'s five-node encoding, at `.all` so a
padding row is pinned too. This is the leg that, 2 381 times, discharges
`MinaPackInjective.packing_is_injective`'s range hypothesis. -/
def bitBoolLeg (j : Nat) : AirLeg :=
  .window ⟨RowSel.all, Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gBool (.leaf (.loc (BIT j))))⟩

theorem bitBoolLeg_eq (j : Nat) :
    bitBoolLeg j
      = .window ⟨RowSel.all, .mul (loc (BIT j)) (.add (loc (BIT j)) (.const (-1)))⟩ := rfl

/-- The `(coefficient, bit column)` terms of limb `k` of element `e`: the eight bits of that byte,
skipped where the run has already ended. ⚑ `runStart e + runWidth e - 1 - m` is bit-exponent `m`'s
STREAM index — the run's bits are the element's binary expansion MSB-first. -/
def limbTerms (e k : Nat) : List (Nat × Nat) :=
  (List.range 8).filterMap fun j =>
    if 8 * k + j < runWidth e then
      some (2 ^ j, BIT (runStart e + runWidth e - 1 - (8 * k + j)))
    else none

/-- `Σ cᵢ · BIT colᵢ`, right-folded. -/
def termSum : List (Nat × Nat) → WindowExpr
  | [] => .const 0
  | (c, col) :: rest => .add (.mul (.const (c : ℤ)) (loc col)) (termSum rest)

/-- ⚑ **THE LIMB LEG** — `PLIMB e k − Σ 2^j · BIT(…) = 0`. Affine in the trace: no product of two
columns anywhere, so this descriptor inherits nothing from the Pasta cone
(`bodyBits_products_are_empty`, §3b). -/
def limbLeg (e k : Nat) : AirLeg :=
  .window ⟨RowSel.all, .add (loc (PLIMB e k)) (.mul (.const (-1)) (termSum (limbTerms e k)))⟩

/-- The 352 first-row PI pins. -/
def limbPin (e k : Nat) : AirLeg := .pin ⟨VmRow.first, PLIMB e k, PI_PLIMB e k⟩

/-- All `(e, k)` pairs, in publication order. -/
def limbIdx : List (Nat × Nat) :=
  (List.range NELEM).flatMap fun e => (List.range (limbCount e)).map fun k => (e, k)

/-- ⚑⚑ **NO PUBLISHED COLUMN IS INERT.** Every limb slot this descriptor publishes has at least one
bit under it, so its gate names TWO columns and the emitted `pi_binding`'s column is in a component
larger than itself. This is `LightClientAnchorConnectivity.decorativeAnchors = []` decided on the
SOURCE, before any byte — and it is why the limb allocation is `⌈W_e/8⌉`. -/
theorem no_published_limb_is_inert : ∀ p ∈ limbIdx, limbTerms p.1 p.2 ≠ [] := by decide

/-- ⚑ **THE SOURCE.** 352 limb legs, then 2 381 booleanity legs, then 352 pins.

⚠ The ORDER is not cosmetic: `EffectAir.pinsTied` resolves each pin by scanning the leg list from
the front, so putting the 352 limb legs first is what keeps the tie verdict a kernel `decide`
instead of a 850 000-step scan behind 2 381 booleanity legs. -/
def bodyBitsAir : EffectAir :=
  { tables := []
  , legs :=
      (limbIdx.map fun p => limbLeg p.1 p.2)
        ++ ((List.range NBITS).map bitBoolLeg)
        ++ (limbIdx.map fun p => limbPin p.1 p.2) }

theorem bodyBitsAir_leg_count : bodyBitsAir.legs.length = 2985 := by rfl

theorem bodyBitsAir_mainRailOk : bodyBitsAir.mainRailOk = true := by rfl

theorem bodyBitsAir_pinsFit : bodyBitsAir.pinsFit BODY_BITS_PI_COUNT = true := by rfl

/-- ⚑ **NO LOOKUP, NO TABLE, NO LIMBS LEG — WHICH IS THE COMMITTED-WIDTH RESULT.** Decided on the
source rather than described: this air block declares zero tables and zero range lookups, so
`MainLayout::build` appends no nibble aux block and the committed row IS the declared row. -/
theorem bodyBitsAir_has_no_lookups :
    bodyBitsAir.tables = [] ∧ bodyBitsAir.ranges = []
      ∧ bodyBitsAir.limbsCount = 0 ∧ bodyBitsAir.totalRangeLookups = 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> rfl

/-- ⚑ **THE TIED SOURCE** — every published column is derived by another leg, carried in the type. -/
def bodyBitsTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := bodyBitsAir

/-- **`bodyBitsDesc` — COMPILER OUTPUT.** -/
def bodyBitsDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-body-preimage-bits::v1" BODY_BITS_WIDTH BODY_BITS_PI_COUNT [] bodyBitsTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — stated in the SOURCE's vocabulary
and never mentioning the lowering, so it is not `P → P`. -/
theorem bodyBitsDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines bodyBitsDesc [] bodyBitsAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-body-preimage-bits::v1" BODY_BITS_WIDTH BODY_BITS_PI_COUNT [] bodyBitsTiedAir).property

theorem bodyBitsDesc_name : bodyBitsDesc.name = "dregg-mina-body-preimage-bits::v1" := rfl
theorem bodyBitsDesc_width : bodyBitsDesc.traceWidth = 2683 := rfl
theorem bodyBitsDesc_piCount : bodyBitsDesc.piCount = 302 := rfl
theorem bodyBitsDesc_tables : bodyBitsDesc.tables = [] := rfl
theorem bodyBitsDesc_ranges : bodyBitsDesc.ranges = [] := rfl
theorem bodyBitsDesc_hashSites : bodyBitsDesc.hashSites = [] := rfl
theorem bodyBitsDesc_constraint_count : bodyBitsDesc.constraints.length = 2985 := rfl

/-- ⚑⚑ **THE COMMITTED WIDTH IS THE DECLARED WIDTH.** `MainLayout::build` appends
`decomp_cols(bits)` columns per RANGE lookup and `2 · SUBMASK_BITS` per submask lookup; this
descriptor emits neither, so its aux block is empty. Decided on the compiler's output.

⚑ Against the family: `dregg-pasta-fp-chainlink::v1` is 469 → 1 037 (2.21×) and
`dregg-mina-accumulator-seg::v1` is 3 048 → 10 756 (3.53×, of which range decomposition is 71.7%).
The brief for this rung expected the chunk gates to ADD range lookups; re-derived on the deployed
field they add none, because a booleanity assertion is a degree-2 gate and not a bus query. -/
theorem the_committed_width_is_the_declared_width :
    (bodyBitsDesc.constraints.filter fun c =>
      match c with | .lookup _ => true | _ => false).length = 0
    ∧ bodyBitsDesc.tables = []
    ∧ bodyBitsDesc.traceWidth = 2683 := by
  refine ⟨?_, rfl, rfl⟩
  rfl

/-! ### §3b — decided on the emitted bytes. -/

/-- Does this body read a trace cell? -/
def readsCell : WindowExpr → Bool
  | .loc _ => true
  | .nxt _ => true
  | .const _ => false
  | .add a b => readsCell a || readsCell b
  | .mul a b => readsCell a || readsCell b

def cellCols : WindowExpr → List Nat
  | .loc c => [c]
  | .nxt c => [c]
  | .const _ => []
  | .add a b => cellCols a ++ cellCols b
  | .mul a b => cellCols a ++ cellCols b

/-- Columns under a product of two cell-reading factors — the limb-product signature. -/
def prodCols : WindowExpr → List Nat
  | .loc _ => []
  | .nxt _ => []
  | .const _ => []
  | .add a b => prodCols a ++ prodCols b
  | .mul a b =>
      (if readsCell a && readsCell b then cellCols a ++ cellCols b else []) ++
        prodCols a ++ prodCols b

def constraintProdCols : VmConstraint2 → List Nat
  | .windowGate w => prodCols w.body
  | _ => []

/-- ⚑ **EVERY TWO-SIDED PRODUCT IS A BOOLEANITY PIN ON ONE COLUMN.** The limb legs are affine, so
the only columns under a product are the bit columns squaring themselves. A non-native Pasta
multiply would put two DIFFERENT indices in one gate; none does. -/
theorem bodyBits_products_are_only_the_bits :
    (bodyBitsDesc.constraints.all fun c =>
      (constraintProdCols c).eraseDups.length ≤ 1) = true := by rfl

/-! ## §4 — ⚑ THE ROW PREDICATE, AND IT IS THE THREE LEG FAMILIES. -/

/-- The value limb `(e, k)`'s gate says the limb is, at a row. -/
def limbValueOf (row : Nat → ℤ) (e k : Nat) : ℤ :=
  (limbTerms e k).foldr (fun t acc => (t.1 : ℤ) * row t.2 + acc) 0

/-- ⚑ **`bodyBitsRowOk` — the emitted constraint set's content, as a decidable verdict.** Three
conjuncts, one per leg family: booleanity on every bit column, each limb the exact byte its bits
compose, and every limb published at its PI slot. -/
def bodyBitsRowOk (row pub : Nat → ℤ) : Prop :=
  (∀ j < NBITS, row (BIT j) * (row (BIT j) - 1) = 0)
  ∧ (∀ p ∈ limbIdx, row (PLIMB p.1 p.2) = limbValueOf row p.1 p.2)
  ∧ (∀ p ∈ limbIdx, pub (PI_PLIMB p.1 p.2) = row (PLIMB p.1 p.2))

/-- ⚑⚑⚑ **THE ROW PREDICATE FORCES THE RANGE HYPOTHESIS.** A row this descriptor accepts denotes a
BOOLEAN bit vector, so every chunk read off it as a bit slice is below its declared width, so
`MinaPackInjective.packing_is_injective` applies to the stream this row denotes. This is the
theorem that makes the gate and the arithmetic one object rather than two files that agree. -/
theorem the_row_gates_force_boolean_bits {row pub : Nat → ℤ} (h : bodyBitsRowOk row pub) :
    ∀ j < NBITS, row (BIT j) = 0 ∨ row (BIT j) = 1 := by
  intro j hj
  have := h.1 j hj
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-! ## §5 — ⚑ THE REAL BLOCK'S WITNESS, AND BOTH POLARITIES.

⚠ Every theorem below is about the REAL devnet block (540221) rather than a hand-built row: the bit
stream is `bodyInput.packeds` expanded MSB-first, and `the_real_slices_are_the_real_chunks` is the
statement that the expansion is the block's own chunk stream and not a re-transcription. -/

/-- The per-chunk bit slices of the real block, MSB-first within each chunk. -/
def realSlices : List (List Nat) :=
  Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.packeds.map fun p =>
    (List.range p.2).map fun t => (p.1 >>> (p.2 - 1 - t)) &&& 1

/-- The flattened 2 381-bit stream — column `j` of the honest row. -/
def realBits : List Nat := realSlices.flatten

/-- ⚑⚑ **THE SLICES ARE THE BLOCK'S OWN CHUNKS.** Re-reading the bit slices as
`(bitsToNat, length)` pairs reproduces `bodyInput.packeds` exactly — so the object this descriptor
gates IS the chunk stream `packToFields` consumes, not a parallel encoding of it. ⚠ Without this the
whole rung is a theorem about the wrong object. -/
theorem the_real_slices_are_the_real_chunks :
    chunksOfSlices realSlices = Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.packeds := by
  native_decide

/-- …and the stream really is 2 381 bits, all boolean. -/
theorem the_real_bits_are_boolean_and_count :
    realBits.length = NBITS ∧ realBits.all (fun b => b == 0 || b == 1) = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- ⚑ **AND THE HIGH LIMBS OF EVERY PACKED ELEMENT ARE ZERO** — element `38+e` is below `2^(W_e)`,
so its base-256 digits above `⌈W_e/8⌉` are all zero. ⚠ This is the obligation the `⌈W_e/8⌉` limb
allocation MOVES rather than removes: the chain's absorbed block is 32 limbs an element, so a weld
connects these `⌈W_e/8⌉` and must pin the remaining `32 − ⌈W_e/8⌉` chain-side limbs to ZERO. Stated
here so the weld has a target that is checkable rather than assumed. -/
theorem the_high_limbs_of_the_real_elements_are_zero :
    ∀ e < NELEM,
      (packToFields Dregg2.Bridge.MinaStateHashPackPrice.bodyInput).getD (38 + e) 0
        < 2 ^ runWidth e := by
  have h : ((List.range NELEM).all fun e => decide
      ((packToFields Dregg2.Bridge.MinaStateHashPackPrice.bodyInput).getD (38 + e) 0
        < 2 ^ runWidth e)) = true := by native_decide
  intro e he
  have := List.all_eq_true.mp h e (List.mem_range.mpr he)
  simpa using this

/-- The honest row: the stream bits, then the eleven elements' limbs as their gates compute them. -/
def realRow : Nat → ℤ := fun c =>
  if c < NBITS then (realBits.getD c 0 : ℤ)
  else
    let i := c - NBITS
    let e := (List.range NELEM).findIdx (fun e => i < limbBase e + limbCount e)
    let k := i - limbBase e
    if e < NELEM then
      ((limbTerms e k).foldr (fun t acc => (t.1 : ℤ) * (realBits.getD t.2 0 : ℤ) + acc) 0)
    else 0

def realPub : Nat → ℤ := fun s =>
  if s < BODY_BITS_PI_COUNT then realRow (NBITS + s) else 0

/-- ⚑⚑ **THE HONEST ROW IS ACCEPTED.** The real block's own packed preimage, gated. -/
theorem the_real_preimage_row_is_accepted : bodyBitsRowOk realRow realPub := by
  refine ⟨?_, ?_, ?_⟩
  · have h : ((List.range NBITS).all fun j =>
        decide (realRow (BIT j) * (realRow (BIT j) - 1) = 0)) = true := by native_decide
    intro j hj
    have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    simpa using this
  · have h : (limbIdx.all fun p =>
        decide (realRow (PLIMB p.1 p.2) = limbValueOf realRow p.1 p.2)) = true := by native_decide
    intro p hp
    have := List.all_eq_true.mp h p hp
    simpa using this
  · have h : (limbIdx.all fun p =>
        decide (realPub (PI_PLIMB p.1 p.2) = realRow (PLIMB p.1 p.2))) = true := by native_decide
    intro p hp
    have := List.all_eq_true.mp h p hp
    simpa using this

/-- ⚑ **THE FALSIFIER'S TARGET.** Bit column 23 is the FIRST `1` in the real block's chunk stream —
the first twenty-three bits are the low bits of `Non_snark.digest`'s first bytes and are zero. ⚠ A
control aimed at one of those would move a zero into something, which is how a sibling lane's first
falsifier died; this one moves a value that is there. -/
def FALSIFIER_BIT : Nat := 23

/-- The forged row: bit 23 carries `2` while declaring ONE bit — an over-wide chunk, and exactly
the left half of `MinaPackInjective.the_range_hypothesis_is_load_bearing`. -/
def forgedBitRow : Nat → ℤ := fun c => if c = BIT FALSIFIER_BIT then 2 else realRow c

/-- The forged row whose published limb is not what its bits compose. -/
def forgedLimbRow : Nat → ℤ := fun c => if c = PLIMB 0 0 then realRow c + 1 else realRow c

/-- ⚑ **THE FALSIFIERS FALSIFY.** Both targets carry a NON-ZERO honest value and both mutations
MOVE it — checked, not assumed. -/
theorem the_falsifier_targets_are_non_zero_and_move :
    realRow (BIT FALSIFIER_BIT) = 1
      ∧ forgedBitRow (BIT FALSIFIER_BIT) = 2
      ∧ realRow (PLIMB 0 0) ≠ 0
      ∧ forgedLimbRow (PLIMB 0 0) ≠ realRow (PLIMB 0 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑⚑ **THE FORGERY THE OLD SHAPE WAVED THROUGH: A CHUNK ABOVE ITS DECLARED WIDTH.** A one-bit
chunk carrying `2`. The booleanity gate refuses it, and the refusal is the AIR's: no lookup, no
table, no producer pre-flight — one degree-2 gate. -/
theorem an_over_wide_chunk_bit_is_refused : ¬ bodyBitsRowOk forgedBitRow realPub := by
  intro h
  have hbad : ¬ (forgedBitRow (BIT FALSIFIER_BIT) * (forgedBitRow (BIT FALSIFIER_BIT) - 1) = 0) := by
    native_decide
  exact hbad (h.1 FALSIFIER_BIT (by decide))

/-- ⚑ **AND A LIMB THAT IS NOT ITS BITS IS REFUSED.** Move the published limb `PLIMB 0 0` by one and
leave every bit alone: the composition gate refuses, so a prover cannot publish an element the bits
do not compose. ⚠ This is the half that keeps the booleanity from being a gate on columns nobody
reads. -/
theorem a_limb_that_is_not_its_bits_is_refused : ¬ bodyBitsRowOk forgedLimbRow realPub := by
  intro h
  have hmem : ((0 : Nat), (0 : Nat)) ∈ limbIdx := by decide
  have hbad : forgedLimbRow (PLIMB 0 0) ≠ limbValueOf forgedLimbRow 0 0 := by native_decide
  exact hbad (h.2.1 (0, 0) hmem)

/-- ⚑ **BOTH POLARITIES, AS ONE STATEMENT.** -/
theorem body_bits_discriminates :
    bodyBitsRowOk realRow realPub
      ∧ ¬ bodyBitsRowOk forgedBitRow realPub
      ∧ ¬ bodyBitsRowOk forgedLimbRow realPub :=
  ⟨the_real_preimage_row_is_accepted, an_over_wide_chunk_bit_is_refused,
   a_limb_that_is_not_its_bits_is_refused⟩

/-! ## §6 — ⚑⚑⚑ THE CONCLUSION, IN THE UNITS THE CAMPAIGN USES. -/

/-- ⚑⚑⚑ **WHAT THE GATE BUYS: THE 819 CHUNKS ARE DETERMINED BY THE ELEVEN PACKED ELEMENTS.**
`MinaPackInjective.the_gated_bits_are_determined_by_the_packing` at THIS block's slicing: two rows
this descriptor accepts, sliced by the SAME schedule, whose packings agree, denote the same 819
chunk values. So the eleven packed field elements the body-hash chain absorbs pin all 2 381 bits.

⚠ **AND THE 38 FIELD ELEMENTS ARE NOT IN THIS STATEMENT.** `fields` is a parameter that rides
through untouched on both sides. Of a `Protocol_state.Body` preimage's `38 + 819` pieces this rung
constrains 819. -/
theorem the_eleven_packed_elements_pin_the_2381_bits (fields : List Nat)
    (sa sb : List (List Nat))
    (hsched : sa.map List.length = sb.map List.length)
    (hba : ∀ s ∈ sa, ∀ b ∈ s, b ≤ 1) (hbb : ∀ s ∈ sb, ∀ b ∈ s, b ≤ 1)
    (hpa : ∀ s ∈ sa, 0 < s.length) (hpb : ∀ s ∈ sb, 0 < s.length)
    (h : packToFields ⟨fields, chunksOfSlices sa⟩ = packToFields ⟨fields, chunksOfSlices sb⟩) :
    chunksOfSlices sa = chunksOfSlices sb :=
  the_gated_bits_are_determined_by_the_packing fields sa sb hsched hba hbb hpa hpb h

/-- …and the real block's slicing satisfies every hypothesis of it, so the conclusion is about the
object the chain absorbs and not about an empty premise. -/
theorem the_real_slicing_satisfies_the_hypotheses :
    (∀ s ∈ realSlices, ∀ b ∈ s, b ≤ 1) ∧ (∀ s ∈ realSlices, 0 < s.length) := by
  constructor
  · have h : (realSlices.all fun s => s.all fun b => decide (b ≤ 1)) = true := by native_decide
    intro s hs b hb
    have hs' := List.all_eq_true.mp h s hs
    have := List.all_eq_true.mp hs' b hb
    simpa using this
  · have h : (realSlices.all fun s => decide (0 < s.length)) = true := by native_decide
    intro s hs
    have := List.all_eq_true.mp h s hs
    simpa using this

/-! ## §7 — ⚠ RESIDUALS, NAMED.

1. ⚑⚑ **THE WELD IS NOT HERE.** The 302 limbs are PUBLISHED, which is what makes a `cb.connect` to
   `MinaStateBodyHashChain`'s links 19..24 absorbed blocks REACHABLE at all. Until that fold exists
   the tie between these bits and that chain's absorbed stream is an EXECUTOR comparison, exactly
   the shape `LightClientAnchorConnectivity.minaLink_body_hash_is_joined_but_not_published` names
   one object over. **A prover still chooses which 2 381 bits; this rung says only that they are
   2 381 bits and that the eleven elements determine them.**
2. ⚠ **THE 38 WHOLE FIELD ELEMENTS.** Not chunked, no declared width, no column here.
3. ⚠ **NOTHING SAYS A BODY IS REAL.** That is `PICKLES_OPENING_WITNESSED`, unchanged.
4. ⚠ **THE RECURSION BOUNDARY.** That a verifying STARK implies its statement is the FRI obligation
   this whole stack carries. This rung stands at exactly that resolution.
-/

#assert_axioms the_runs_partition_the_stream
#assert_axioms the_limb_allocation_is_the_run_widths
#assert_axioms the_layout_is_wellformed
#assert_axioms no_published_limb_is_inert
#assert_axioms bitBoolLeg_eq
#assert_axioms bodyBitsAir_leg_count
#assert_axioms bodyBitsAir_mainRailOk
#assert_axioms bodyBitsAir_pinsFit
#assert_axioms bodyBitsAir_has_no_lookups
#assert_axioms bodyBitsDesc_name
#assert_axioms bodyBitsDesc_width
#assert_axioms bodyBitsDesc_piCount
#assert_axioms bodyBitsDesc_tables
#assert_axioms bodyBitsDesc_constraint_count
#assert_axioms the_committed_width_is_the_declared_width
#assert_axioms bodyBits_products_are_only_the_bits
#assert_axioms the_row_gates_force_boolean_bits
#assert_axioms the_eleven_packed_elements_pin_the_2381_bits

-- ⚑ COMPILER-TRUSTED, and said out loud: each reduces the 1 544-byte binprot parse, a two-block
-- SHA-256 and the 819-chunk assembly, or evaluates 3 085 gates at the real block's row.
#assert_compiled the_run_schedule_is_the_real_blocks_packing
#assert_compiled the_real_slices_are_the_real_chunks
#assert_compiled the_high_limbs_of_the_real_elements_are_zero
#assert_compiled the_real_bits_are_boolean_and_count
#assert_compiled the_real_preimage_row_is_accepted
#assert_compiled the_falsifier_targets_are_non_zero_and_move
#assert_compiled an_over_wide_chunk_bit_is_refused
#assert_compiled a_limb_that_is_not_its_bits_is_refused
#assert_compiled the_real_slicing_satisfies_the_hypotheses

end Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir
