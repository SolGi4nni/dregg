/-
# `Dregg2.Circuit.Emit.LightClientSolStakeFoldAir` — the Solana stake table, FOLDED, on the prover's
own hash. One row per stake-table entry; the published root and the published denominator both come
out of the SAME rows.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this is a Lean-authored AIR. `solStakeFoldDesc` is
`EffectLower.lowerAir` applied to the `EffectAir` source `solStakeFoldAir` (§3). There is **no
hand-written `VmConstraint2` in this file.** Rust reads the emitted bytes, fills a trace, and proves.

## §0 — the hole this closes, quoted from the descriptor that has it

`LightClientSolanaAir.totalStakePins` (2026-08-04) put the active-stake DENOMINATOR into the Solana
light client's public statement, and bounded its own claim in the same breath:

> ⚠ **Bound the claim.** This pins the DENOMINATOR, not the TABLE. … **a swap to a different
> validator set with the SAME total active stake is NOT refused by this.** What IS refused is every
> swap that moves the total — which is what `STAKE_TABLE_OK` was named for (the HOLE-2 denominator
> pin) and what the SHA-256 table fold is priced out of doing (§6c).

`circuit/tests/solana_lightclient_proves.rs::a_swapped_stake_table_is_arithmetically_perfect` exhibits
exactly that row: a forged validator set that satisfies **every** gate of the served descriptor.

This file is the fold that refuses it. Its `PI_TABLE_ROOT` is DERIVED from the exhibited rows, and its
`PI_TOTAL_STAKE` is DERIVED from the SAME rows — so a table with a different membership and an
identical tally clears the tally pins and moves the root.

## §0a — ⚑ THE MEASUREMENT THAT PICKED THE HASH, and it is not SHA-256

`LightClientSolanaAir` §6c priced the SHA-256 fold of the DEPLOYED `EpochStakeTable::root`
(measured 2026-08-04, by evaluating the emitters rather than reading their docblocks):

| object | constraints | trace columns |
|---|---|---|
| `sha256Block` | 40,928 | 29,096 |
| `sha256PairHash` | 82,648 | 59,216 |
| `EpochStakeTable::root` at 703 live vote accounts (441 blocks) | **18,049,248** | **12,831,336** |
| the widest descriptor this tree has ever EMITTED | — | 15,611 |
| the widest that parses, checks and **PROVES** | — | **2,131** |

ONE SHA-256 block is 13.6× the proved ceiling. The fold is out of reach at 703 rows, at 2 rows, and
at one block.

**This descriptor is 44 columns and 58 constraints, at ANY number of validators**, because the
validators are ROWS and not columns, and because a Poseidon2 hash on this stack is one
`VmConstraint2.lookup` on the chip bus rather than 40,928 gates. At 703 vote accounts the trace is
1,024 rows × 44 columns and the chip serves 2,048 absorbs. That is the scale of the descriptors this
tree already emits and proves.

⚑ **The two numbers, side by side, and they are not the same kind of number** — which is exactly why
both are given. The SHA-256 shape puts the whole preimage in the WIDTH of one row
(**12,831,336 columns / 18,049,248 constraints**, against a proved ceiling of 2,131 columns); the
Poseidon2 shape puts it in the HEIGHT of a 44-column trace (**58 constraints, 2,048 chip absorbs at
703 validators**). The comparison that is fair is *does it fit*: one is 6,021× over the widest object
this tree has ever emitted, the other is narrower than `dregg-mina-lightclient-verify::v1`.

⚑ **The price of that is a FLAG DAY, and it is the whole reason this was reachable:**
`EpochStakeTable::root` is **dregg-authored** (`STAKE_TABLE_ROOT_TAG = b"dregg-solana-stake-table-
root:v1"`, `bridge/src/solana_consensus.rs:118`), pinned by a **dregg-authored**
`WeakSubjectivityAnchor` (`bridge/src/solana_provenance.rs:574`). Nothing on Solana's side computes
it. The commitment was ours to pick and we had picked the one hash the prover cannot afford. See
"WHAT THIS BREAKS" below for what re-emits.

## §1 — the shape: ONE absorb kind, so there is no domain-separation question

Every chip site in this descriptor is the SAME function: an arity-16 absorb of `state8 ‖ block8`.
There is no "leaf" absorb and no "node" absorb, hence no argument about whether a leaf preimage can
be confused for a node preimage — the confusion this file is built to avoid having to price. Each
stake entry is exactly TWO message blocks, on ONE trace row:

    MID8      = chipAbsorb16( ROOT_IN8 ‖ [voter₀ … voter₇] )
    ROOT_OUT8 = chipAbsorb16( MID8     ‖ [voter₈, stake₀, stake₁, stake₂, stake₃, 0, 0, 0] )

`voter` is a 32-byte vote-account pubkey as nine radix-`2^29` lanes (`8·29 + 24 = 256`), and `stake`
is a `u64` as four 16-bit limbs LSB-first — the same `u64` spelling `LightClientSolanaAir`'s tally
already uses, so the two rungs speak one language about lamports.

The three trailing zeros of the second block are `Expr.const 0` **in the lookup tuple**, not columns:
they are structural, not witnessed, so the message frame per entry is a fixed 16 felts and the frame
sequence determines the entry list.

## §2 — what the fold binds, and at what number

The running state is EIGHT felts at every step. `log₂ p = 30.906891`, so the image is
`8 · 30.906891 = 247.255128` bits and the relevant bound — a fold over a table, where an equivocating
prover needs two tables with one root — is the **BIRTHDAY COLLISION** figure:

    2^(247.255128 / 2) = 2^123.63

⚠ The second-preimage figure for the same object is `~2^247.3` and is NOT the number that governs
here. Quoting it would be the flattering half of a pair.

⚠ And the number the SHIPPED anchor was worth: `WeakSubjectivityAnchor.stake_table_root` reaches
`solLcVerifyDesc` as nine radix-`2^31` limbs, PI-bound and **UNREAD** — no constraint of any kind
names them (`LightClientAnchorConnectivity.sol_anchors_are_unread`). The root binds nothing there at
any width, because nothing reads it. This descriptor is where it becomes evidence.

`§5`'s binding is `binding ∨ Coll8 chipAbsorb8 (the pair a TOTAL extractor returned)` — the
`ReceiptChain8` discipline, and for its reasons:

* **no `Compress8CR` hypothesis** — PROVED FALSE at deployed parameters
  (`VacuitySweepTeeth.compress8CR_false_babyBear`), so a theorem carrying one says nothing about the
  deployed system;
* **no `∃ a b, a ≠ b ∧ f a = f b` disjunct** — at BabyBear that is unconditionally TRUE by
  pigeonhole, so it would carry no more content than `True`. The disjunct names the SPECIFIC pair.

## §3 — ⚠ WHAT THIS DOES NOT DO. Read before citing it.

* **It does not verify a Solana vote signature.** `ED_OK` is untouched and stays a witnessed carrier
  in the sibling rung. This fold binds the DENOMINATOR's provenance, not the numerator's.
* **It does not fold the numerator.** `ROOTED_STK` remains a witnessed projection in
  `solLcVerifyDesc`. A prover still chooses which of the bound validators it claims voted.
* **It is EQUAL-HEIGHT binding.** `FoldScheme.tableRoot_binds_or_collides` takes
  `L₁.length = L₂.length`.
  That is exactly "the same trace height", which the committed proof fixes and the verifier reads;
  it is a hypothesis about the shape of the proof, not about the prover's honesty. A shorter table
  padded to the height with the ZERO ROW `(voter = 0, stake = 0)` is *the same table* under this
  commitment — the zero row contributes nothing to the tally and the padded frame is what the anchor
  pins.
* **It does not join the two rungs INSIDE one proof.** Today the join is at the PUBLIC STATEMENT: a
  light client verifies this proof, checks `PI_TABLE_ROOT` against its governance-pinned anchor,
  verifies `dregg-solana-lightclient-verify::v1`, and checks that its `PI_TOTAL_STK` slots 19..22 are
  the four felts THIS proof derived. Both halves are the verifier's, and it already does exactly that
  with its anchor. Making it one proof is the recursion seam (`ProofBind`), and the honest reason it
  is not used here is **width**: `ProofBind`'s `commit`/`bound` are ONE FELT each
  (`DescriptorIR2.lean:503-509`, `circuit-prove/src/custom_proof_bind.rs::PROOF_BIND_COMMIT_WIDTH = 8`
  is the real object), so a seam tie of this eight-lane root would be worth **2^31**, not 2^123.63 —
  below this repo's own ~124-bit bar. Widening `ProofBind` to the eight lanes the deployed weld
  already carries is the fix; a one-felt tie shipped now is the containment that makes the fix never
  happen. Stated as a number rather than deferred as a phase.

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

**NEW descriptor** `dregg-solana-stake-table-fold::v1`, width 44, 12 PIs, 58 constraints, three
declared range tables (`range_w29` id 98 and `range_w16` id 85 — both SHARED with descriptors that
already declare them — plus `range_w24` id 93, NEW). **Emit**
`circuit/descriptors/by-name/dregg-solana-stake-table-fold-v1.json` and **mint a VK** for it.

**RE-ANCHORING, and it is a real break of a dregg-authored format:** the commitment this descriptor
computes is NOT `EpochStakeTable::root`'s SHA-256. A consumer that wants the two to agree must move
`EpochStakeTable::root` to this Poseidon2 frame (tag → `dregg-solana-stake-table-root:v2`) and
re-derive every `WeakSubjectivityAnchor.stake_table_root`. Nothing existing CHANGES SHAPE in this
commit — `solLcVerifyDesc` is untouched, no VK rotates, nothing re-genesises — and that is a
statement about *this* commit, not a reason the re-anchor is optional. Until it lands, this rung's
`PI_TABLE_ROOT` is a Poseidon2 commitment to the same table the SHA anchor names, and the two are
compared by re-deriving, not by equating.

⚠ `circuit/descriptors/PROVENANCE.json` is already UNSTAMPED from earlier flag days and
`check-descriptor-drift.sh` is already RED; this adds a row to that ledger and the stamp remains the
operator's ceremony.
-/
import Dregg2.Circuit.Emit.LightClientSolanaAir
import Dregg2.Circuit.Emit.LightClientMinaAir
import Dregg2.Circuit.DeployedCapTree
import Dregg2.Circuit.Emit.EffectLowerCertified

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Dregg2.Circuit.Emit.LightClientSolStakeFoldAir

open Dregg2.Circuit (Assignment Expr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg PiPinLeg LimbsLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8)

/-! ## §1 — the trace column layout (ONE ROW PER STAKE-TABLE ENTRY).

⚑⚑ **THE LAYOUT AND THE LEGS NOW LIVE IN `LightClientSolanaAir`, AND THAT IS NOT A MOVE FOR TIDINESS.**
Since 2026-08-04 `dregg-solana-lightclient-verify::v1` ABSORBS this fold: its columns 0..43 are these
columns, at these indices, and its source legs BEGIN with `foldLegs` — the SAME TERM this rung is
built from (`sol_fold_block_is_the_shared_source`). Two descriptors reading one leg list cannot
disagree about what a stake-table row is, which is the failure mode `CLAUDE.md` names as *"two shapes
that agree today are two shapes that will disagree later"*, removed by construction rather than by a
differential test.

The names below are re-exports so this file's own theorems, and `circuit/tests/solana_stake_table_fold.rs`,
read unchanged. -/

/-- Lane `j` of the running eight-felt table root ENTERING this row. Columns 0..7. -/
abbrev ROOT_IN (j : Nat) : Nat := LightClientSolanaAir.ROOT_IN j
/-- Lane `j` of this entry's vote-account pubkey. Columns 8..16. -/
abbrev VOTER (j : Nat) : Nat := LightClientSolanaAir.VOTER j
/-- Limb `i` of this entry's active stake, LSB-first. Columns 17..20. -/
abbrev STAKE (i : Nat) : Nat := LightClientSolanaAir.STAKE i
/-- Lane `j` of the INTERMEDIATE state. Columns 21..28. -/
abbrev MID (j : Nat) : Nat := LightClientSolanaAir.MID j
/-- Lane `j` of the running table root LEAVING this row. Columns 29..36. -/
abbrev ROOT_OUT (j : Nat) : Nat := LightClientSolanaAir.ROOT_OUT j
/-- Limb `i` of the running TOTAL active stake, LSB-first. Columns 37..40. -/
abbrev ACC (i : Nat) : Nat := LightClientSolanaAir.ACC i
/-- Carry `i` of the accumulator's limb addition. Columns 41..43. -/
abbrev CARRY (i : Nat) : Nat := LightClientSolanaAir.CARRY i

/-- Main-trace width: `8 + 9 + 4 + 8 + 8 + 4 + 3`. -/
abbrev FOLD_WIDTH : Nat := LightClientSolanaAir.FOLD_WIDTH

/-- PI slot of table-root lane `j` (slots 0..7). -/
def PI_TABLE_ROOT (j : Nat) : Nat := j
/-- PI slot of total-stake limb `i` (slots 8..11) — the DENOMINATOR, derived from the folded rows. -/
def PI_TOTAL_STAKE (i : Nat) : Nat := 8 + i
/-- Number of public inputs. -/
def FOLD_PI_COUNT : Nat := 12

/-- Pubkey lane width. **29 is the last wrap-free width at BabyBear**. -/
abbrev LANE_BITS : Nat := LightClientSolanaAir.LANE_BITS
/-- The TOP pubkey lane's width: `8·29 + 24 = 256`. -/
abbrev TOP_LANE_BITS : Nat := LightClientSolanaAir.TOP_LANE_BITS
/-- Stake-limb width — four 16-bit limbs are exactly a `u64`. -/
abbrev STAKE_BITS : Nat := LightClientSolanaAir.SOL_LIMB_BITS

/-- Width-tagged range table id. -/
abbrev rangeTid (bits : Nat) : TableId := LightClientSolanaAir.rangeTid bits

abbrev laneTable : TableDef := LightClientSolanaAir.laneTable
abbrev topLaneTable : TableDef := LightClientSolanaAir.topLaneTable
abbrev stakeTable : TableDef := LightClientSolanaAir.stakeTable

/-- The FOLD's domain tag, lane 0 of the initial state — ASCII `SSTF`. -/
abbrev FOLD_TAG : ℤ := LightClientSolanaAir.FOLD_TAG

/-- `2^16`, the limb radix. -/
abbrev RADIX : ℤ := LightClientSolanaAir.RADIX

/-! ## §2 — the SOURCE legs, in the framework's own algebra. See `LightClientSolanaAir` §3a; every
inter-row law is a `WindowLeg` at `.transition`, the seeds are `.first`, the boolean pins are `.all`,
and nothing here is a `VmConstraint2`. -/

abbrev absorbA : AirLeg := LightClientSolanaAir.absorbA
abbrev absorbB : AirLeg := LightClientSolanaAir.absorbB
abbrev foldLegs : List AirLeg := LightClientSolanaAir.foldLegs

/-- The eight LAST-row root publications. ⚑ `.last`, so the published root is the END of the fold and
not a value some row happens to carry. -/
def rootPins : List AirLeg :=
  [ .pin ⟨VmRow.last, ROOT_OUT 0, PI_TABLE_ROOT 0⟩
  , .pin ⟨VmRow.last, ROOT_OUT 1, PI_TABLE_ROOT 1⟩
  , .pin ⟨VmRow.last, ROOT_OUT 2, PI_TABLE_ROOT 2⟩
  , .pin ⟨VmRow.last, ROOT_OUT 3, PI_TABLE_ROOT 3⟩
  , .pin ⟨VmRow.last, ROOT_OUT 4, PI_TABLE_ROOT 4⟩
  , .pin ⟨VmRow.last, ROOT_OUT 5, PI_TABLE_ROOT 5⟩
  , .pin ⟨VmRow.last, ROOT_OUT 6, PI_TABLE_ROOT 6⟩
  , .pin ⟨VmRow.last, ROOT_OUT 7, PI_TABLE_ROOT 7⟩ ]

/-- The four LAST-row denominator publications. -/
def totalPins : List AirLeg :=
  [ .pin ⟨VmRow.last, ACC 0, PI_TOTAL_STAKE 0⟩
  , .pin ⟨VmRow.last, ACC 1, PI_TOTAL_STAKE 1⟩
  , .pin ⟨VmRow.last, ACC 2, PI_TOTAL_STAKE 2⟩
  , .pin ⟨VmRow.last, ACC 3, PI_TOTAL_STAKE 3⟩ ]

/-! ## §3 — ⚑ THE SOURCE AIR, and the descriptor as the COMPILER'S OUTPUT. -/

/-- ⚑ **THE SOURCE.** Forty-five legs: four range legs (three `.limbs` + one narrow lookup), two chip
absorbs, eight `.first` seeds, eight `.transition` continuities, three `.all` carry pins, four
`.first` tally seeds, four `.transition` tally steps, and twelve PI pins. -/
def solStakeFoldAir : EffectAir :=
  { tables := LightClientSolanaAir.foldTables
  , legs   := foldLegs ++ rootPins ++ totalPins }

/-- ⚑ **THE COMPILER ACCEPTED EVERY LEG.** `mainRailOk` is the decidable verdict that each leg is
EXPRESSIBLE on the deployed main rail — unit multiplicity, `.query` side, no `nxt` under `.all` /
`.first` / `.last`, no limb width at or above the wrap-free ceiling 29. `rfl` records that the
vocabulary was adequate; a leg the rail cannot hold lowers to an UNSATISFIABLE pair rather than to
silence. -/
theorem solStakeFoldAir_mainRailOk : solStakeFoldAir.mainRailOk = true := by rfl

/-- ⚑ **EVERY PUBLISHED COLUMN IS DERIVED BY ANOTHER LEG** — `EffectAir.pinsTied`, the verdict that
makes a DECORATIVE pin unrepresentable rather than merely detectable. The eight root lanes and the
four total-stake lanes are all read by the fold legs that compute them.

⚑ It is stated HERE rather than only in `PinsTiedCensus`, which had `by decide`d the same fact one
module downstream: the `TiedAir` below carries the obligation in its type, and an `autoParam` left
blank re-derives it inside the elaborator's `whnf` a third time. -/
theorem solStakeFoldAir_pinsTied : solStakeFoldAir.pinsTied = true := by decide

/-- ⚑ **THE TIED SOURCE** — `solStakeFoldAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def solStakeFoldTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := solStakeFoldAir
  ok   := solStakeFoldAir_mainRailOk
  tied := solStakeFoldAir_pinsTied

/-- **`solStakeFoldDesc`** — the Solana stake-table fold as an emitted IR-v2 AIR, one row per entry.
PIs `[table_root[0..7], total_stake[0..3]]`: the eight-lane Poseidon2 commitment to the exhibited
table and the `u64` active-stake denominator, BOTH derived from the same rows. -/
def solStakeFoldDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-solana-stake-table-fold::v1" FOLD_WIDTH FOLD_PI_COUNT [] solStakeFoldTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem solStakeFoldDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines solStakeFoldDesc [] solStakeFoldAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-solana-stake-table-fold::v1" FOLD_WIDTH FOLD_PI_COUNT [] solStakeFoldTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem solStakeFoldDesc_eq_lowerAir :
    solStakeFoldDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-solana-stake-table-fold::v1" FOLD_WIDTH FOLD_PI_COUNT [] solStakeFoldAir := rfl

/-! ### Shape pins on the emitted object. -/

theorem solStakeFoldDesc_width : solStakeFoldDesc.traceWidth = 44 := rfl
theorem solStakeFoldDesc_piCount : solStakeFoldDesc.piCount = 12 := rfl
theorem solStakeFoldAir_leg_count : solStakeFoldAir.legs.length = 45 := by decide

/-- ⚑ **THE FOLD BLOCK OF THE LIGHT CLIENT IS THIS RUNG'S OWN LEG LIST.** Not a copy, not a
differential test: the same term. A drift in either is a drift in both. -/
theorem solStakeFold_shares_its_legs_with_the_light_client :
    solStakeFoldAir.legs.take LightClientSolanaAir.foldLegs.length
      = LightClientSolanaAir.solLcVerifyAir.legs.take LightClientSolanaAir.foldLegs.length := by
  simp [solStakeFoldAir, LightClientSolanaAir.solLcVerifyAir, List.take_left']
theorem solStakeFoldDesc_constraint_count : solStakeFoldDesc.constraints.length = 58 := by decide
theorem solStakeFoldDesc_tables :
    solStakeFoldDesc.tables = [laneTable, topLaneTable, stakeTable] := rfl

/-- The three declared range tables sit at wire ids 98 / 93 / 85 — the first and third SHARED with
descriptors that already declare them, so this rung adds ONE table id to the served surface. -/
theorem solStakeFold_table_wire_ids :
    (rangeTid LANE_BITS).wireId = 98 ∧ (rangeTid TOP_LANE_BITS).wireId = 93
      ∧ (rangeTid STAKE_BITS).wireId = 85 := by decide

/-- ⚑ **BOTH CHIP SITES ARE AT AN ADMITTED ARITY, AND IT IS 16.** Measured on the emitted
constraints: every `poseidon2` lookup this descriptor carries has a 25-wide tuple whose head is the
constant 16 — `[arity, in₀…in₁₅, out₀…out₇]`, the `node8` full-width seed. A site at 8, 9, 12 or 14
would leave the deployed degree-7 admission product non-zero and no assignment could satisfy it. -/
theorem solStakeFold_chip_sites_are_arity_16 :
    (solStakeFoldDesc.constraints.filterMap fun c =>
      match c with
      | .lookup l => if l.table = TableId.poseidon2 then some (l.tuple.length, l.tuple.head?) else none
      | _ => none)
      = [(25, some (Dregg2.Exec.CircuitEmit.EmittedExpr.const 16)),
         (25, some (Dregg2.Exec.CircuitEmit.EmittedExpr.const 16))] := by decide

/-! ### ⚑ The degree census, on the compiler's output rather than in prose.

`prodCols` lists the columns appearing under a product of two CELL-READING factors — empty for a body
affine in the trace, `[c, c]` for a body squaring one column, and two DIFFERENT indices exactly when a
body multiplies two distinct witnesses (the non-native-limb-product signature). This is
`LightClientMinaLinkAir`'s measurement, at this descriptor. -/

/-- Does this window body read a trace cell at all? -/
def readsCell : WindowExpr → Bool
  | .loc _ => true
  | .nxt _ => true
  | .const _ => false
  | .add a b => readsCell a || readsCell b
  | .mul a b => readsCell a || readsCell b

/-- The columns a window body reads. -/
def cellCols : WindowExpr → List Nat
  | .loc c => [c]
  | .nxt c => [c]
  | .const _ => []
  | .add a b => cellCols a ++ cellCols b
  | .mul a b => cellCols a ++ cellCols b

/-- The columns appearing under a product of two cell-reading factors. -/
def prodCols : WindowExpr → List Nat
  | .loc _ => []
  | .nxt _ => []
  | .const _ => []
  | .add a b => prodCols a ++ prodCols b
  | .mul a b =>
      (if readsCell a && readsCell b then cellCols a ++ cellCols b else []) ++
        prodCols a ++ prodCols b

/-- The product columns of one emitted constraint. -/
def constraintProdCols : VmConstraint2 → List Nat
  | .windowGate w => prodCols w.body
  | .base (.gate b) => []
  | _ => []

/-- ⚑⚑ **THE ONLY TWO-SIDED PRODUCTS ARE THE THREE CARRY BITS, EACH SQUARING ONE COLUMN.** Measured
on the emitted object: every column that ever appears under a product is a `CARRY`, and it appears
beside itself. Nothing here multiplies two distinct witnesses, so this descriptor is degree 2 and
touches none of the non-native-arithmetic cone. -/
theorem solStakeFold_products_are_only_the_carry_bits :
    (solStakeFoldDesc.constraints.flatMap constraintProdCols)
      = [CARRY 0, CARRY 0, CARRY 1, CARRY 1, CARRY 2, CARRY 2] := by decide

/-! ## §4 — the MODEL: what the emitted chain computes, over an abstract 8-output absorb.

⚑ Nothing here models Poseidon2. `chipAbsorb8` is the deployed 8-output arity-tagged chip absorb
(`descriptor_ir2::chip_absorb_all_lanes`) as an OPAQUE `List ℤ → Digest8`, exactly as
`ReceiptChain8` and `DeployedCapTree` carry it: the binding below is a statement about the FOLD, and
its residual names a collision of that function rather than assuming it has none. -/

/-- ONE stake-table entry: a nine-lane pubkey (`v0..v8`) and a four-limb `u64` stake (`s0..s3`).
Spelled as explicit fields rather than `Fin n → ℤ` so equality is decidable by `decide` and the
extractor below stays a total computable function. -/
structure StakeRow where
  /-- Vote-account pubkey lanes 0..8, radix `2^29` (lane 8 at 24 bits). -/
  v0 : ℤ
  v1 : ℤ
  v2 : ℤ
  v3 : ℤ
  v4 : ℤ
  v5 : ℤ
  v6 : ℤ
  v7 : ℤ
  v8 : ℤ
  /-- Active stake limbs 0..3, LSB-first, 16 bits each. -/
  s0 : ℤ
  s1 : ℤ
  s2 : ℤ
  s3 : ℤ
  deriving DecidableEq, Repr

/-- The 8-output chip absorb carrier. ONE field, and it is INHABITED — no collision-resistance field,
because a structure carrying a false field is uninhabitable and every theorem quantifying over it is
vacuous (the wound `Cap8Scheme` took and shed). -/
structure FoldScheme where
  /-- The 8-output arity-tagged chip absorb (`chip_absorb_all_lanes`). -/
  chipAbsorb8 : List ℤ → Digest8

namespace FoldScheme

/-- The row's FIRST message block — the eight LOW pubkey lanes. -/
def blkA (e : StakeRow) : List ℤ := [e.v0, e.v1, e.v2, e.v3, e.v4, e.v5, e.v6, e.v7]

/-- The row's SECOND message block — the top pubkey lane, the four stake limbs, and the three
structural zeros the lookup tuple carries as constants. -/
def blkB (e : StakeRow) : List ℤ := [e.v8, e.s0, e.s1, e.s2, e.s3, 0, 0, 0]

@[simp] theorem blkA_length (e : StakeRow) : (blkA e).length = 8 := rfl
@[simp] theorem blkB_length (e : StakeRow) : (blkB e).length = 8 := rfl

/-- The arity-16 absorb input `state8 ‖ block8` — the ONE preimage shape this descriptor uses. -/
def pack (st : Digest8) (b : List ℤ) : List ℤ := List.ofFn st ++ b

@[simp] theorem pack_length (st : Digest8) (b : List ℤ) (h : b.length = 8) :
    (pack st b).length = 16 := by simp [pack, h]


/-- `pack` splits uniquely: equal-length halves and `List.ofFn` injective. -/
theorem pack_inj {s₁ s₂ : Digest8} {b₁ b₂ : List ℤ} (h : pack s₁ b₁ = pack s₂ b₂) :
    s₁ = s₂ ∧ b₁ = b₂ := by
  unfold pack at h
  have hlen : (List.ofFn s₁).length = (List.ofFn s₂).length := by simp
  obtain ⟨hl, hr⟩ := List.append_inj h hlen
  exact ⟨List.ofFn_inj.mp hl, hr⟩

/-- Distinct entries have distinct block PAIRS — so an entry equivocation is always extractable as a
chip collision rather than silently absorbed. -/
theorem blocks_ne_of_ne {e f : StakeRow} (h : e ≠ f) : blkA e ≠ blkA f ∨ blkB e ≠ blkB f := by
  by_contra hc
  push_neg at hc
  obtain ⟨ha, hb⟩ := hc
  refine h ?_
  cases e
  cases f
  simp only [blkA, blkB, List.cons.injEq, and_true] at ha hb
  simp_all

/-- One row's state step: two absorbs of the SAME arity-16 shape. -/
def rowStep (S : FoldScheme) (st : Digest8) (e : StakeRow) : Digest8 :=
  S.chipAbsorb8 (pack (S.chipAbsorb8 (pack st (blkA e))) (blkB e))

/-- The fold over a LAST-ROW-FIRST entry list (the structural recursion the extractor walks); `init`
is the descriptor's pinned seed. -/
def foldR (S : FoldScheme) (init : Digest8) : List StakeRow → Digest8
  | [] => init
  | e :: rest => S.rowStep (foldR S init rest) e

/-- **THE TABLE ROOT** — the fold over the table in TRACE ORDER (first row first). -/
def tableRoot (S : FoldScheme) (init : Digest8) (L : List StakeRow) : Digest8 :=
  S.foldR init L.reverse

/-! ### The collision extractor: a TOTAL function, no search, no `Classical.choice`. -/

/-- The extractor. Two ways to bottom out on a step, and each one NAMES a preimage pair:

  * the two OUTER (second-block) absorb inputs differ — those inputs ARE the collision;
  * the outer inputs agree but the two INNER (first-block) absorb inputs differ — those ARE it.

Otherwise both preimages agree, so the entries and the older states agree, and the walk recurses.
The unequal-length branches return `([], [])`, which is NOT a collision — the theorem below reaches
them only under an equal-length hypothesis and returns `Or.inl` there instead of a fake pair. -/
def foldRFind (S : FoldScheme) (init : Digest8) :
    List StakeRow → List StakeRow → List ℤ × List ℤ
  | [], _ => ([], [])
  | _, [] => ([], [])
  | (e :: r₁), (f :: r₂) =>
      let s₁ := S.foldR init r₁
      let s₂ := S.foldR init r₂
      let a₁ := pack s₁ (blkA e)
      let a₂ := pack s₂ (blkA f)
      let o₁ := pack (S.chipAbsorb8 a₁) (blkB e)
      let o₂ := pack (S.chipAbsorb8 a₂) (blkB f)
      if o₁ ≠ o₂ then (o₁, o₂)
      else if a₁ ≠ a₂ then (a₁, a₂)
      else foldRFind S init r₁ r₂

/-- ⚑⚑ **THE BINDING.** Two equal-height entry lists with equal fold outputs are EITHER EQUAL — so a
prover cannot keep the published root while TAMPERING with, REORDERING or SUBSTITUTING any entry — OR
the pair `foldRFind` returns is a genuine collision of the deployed 8-output chip absorb, which costs
`2^123.63` (§2).

No collision-resistance hypothesis of any kind: the residual is a NAMED PAIR, decidable, dischargeable
by the honest prover, and refutable at a colliding chip. -/
theorem foldR_binds_or_collides (S : FoldScheme) (init : Digest8) :
    ∀ R₁ R₂ : List StakeRow, R₁.length = R₂.length → S.foldR init R₁ = S.foldR init R₂ →
      R₁ = R₂ ∨ Coll8 S.chipAbsorb8 (S.foldRFind init R₁ R₂) := by
  intro R₁
  induction R₁ with
  | nil =>
    intro R₂ _ _
    cases R₂ with
    | nil => exact Or.inl rfl
    | cons f r₂ => simp_all
  | cons e r₁ ih =>
    intro R₂ hlen h
    cases R₂ with
    | nil => simp at hlen
    | cons f r₂ =>
      have hlen' : r₁.length = r₂.length := by simpa using hlen
      simp only [foldR, rowStep] at h
      by_cases houter :
          pack (S.chipAbsorb8 (pack (S.foldR init r₁) (blkA e))) (blkB e)
            ≠ pack (S.chipAbsorb8 (pack (S.foldR init r₂) (blkA f))) (blkB f)
      · refine Or.inr ?_
        simp only [foldRFind, if_pos houter]
        exact ⟨houter, h⟩
      · have hcond := houter
        rw [not_not] at houter
        obtain ⟨hmid, hblkB⟩ := pack_inj houter
        by_cases hinner :
            pack (S.foldR init r₁) (blkA e) ≠ pack (S.foldR init r₂) (blkA f)
        · refine Or.inr ?_
          simp only [foldRFind, if_neg hcond, if_pos hinner]
          exact ⟨hinner, hmid⟩
        · have hcond2 := hinner
          rw [not_not] at hinner
          obtain ⟨hst, hblkA⟩ := pack_inj hinner
          have hef : e = f := by
            by_contra hne
            rcases blocks_ne_of_ne hne with hA | hB
            · exact hA hblkA
            · exact hB hblkB
          subst hef
          simp only [foldRFind, if_neg hcond, if_neg hcond2]
          rcases ih r₂ hlen' hst with hr | hcoll
          · exact Or.inl (by rw [hr])
          · exact Or.inr hcoll

/-- The trace-order extractor. -/
def tableRootFind (S : FoldScheme) (init : Digest8) (L₁ L₂ : List StakeRow) : List ℤ × List ℤ :=
  S.foldRFind init L₁.reverse L₂.reverse

/-- ⚑ **THE ROOT BINDS THE WHOLE STAKE TABLE**, in trace order. -/
theorem tableRoot_binds_or_collides (S : FoldScheme) (init : Digest8) {L₁ L₂ : List StakeRow}
    (hlen : L₁.length = L₂.length) (h : S.tableRoot init L₁ = S.tableRoot init L₂) :
    L₁ = L₂ ∨ Coll8 S.chipAbsorb8 (S.tableRootFind init L₁ L₂) := by
  unfold tableRoot at h
  have hrev : L₁.reverse.length = L₂.reverse.length := by simpa using hlen
  rcases S.foldR_binds_or_collides init L₁.reverse L₂.reverse hrev h with hEq | hColl
  · exact Or.inl (by simpa using congrArg List.reverse hEq)
  · exact Or.inr hColl

/-! ### §4b — the tally the SAME rows denote. -/

/-- The `u64` an entry's four 16-bit limbs denote. -/
def stakeValue (e : StakeRow) : ℤ :=
  e.s0 + 65536 * e.s1 + 65536 ^ 2 * e.s2 + 65536 ^ 3 * e.s3

/-- The table's total active stake — what the `ACC` chain accumulates and the LAST row publishes. -/
def totalStake : List StakeRow → ℤ
  | [] => 0
  | e :: rest => stakeValue e + totalStake rest

/-- ⚑⚑⚑ **THE TOOTH. A SWAPPED VALIDATOR SET WITH THE SAME TALLY MOVES THE ROOT.**

This is the forgery `LightClientSolanaAir.totalStakePins` names as OUT OF ITS SCOPE and
`solana_lightclient_proves.rs::a_swapped_stake_table_is_arithmetically_perfect` exhibits satisfying
every gate of the served descriptor: a different validator set whose lamports sum to the SAME
denominator. Every tally pin of this rung still accepts it — that is the hypothesis `htot` — and the
fold refuses it, unless the pair the extractor returns is a genuine chip collision.

⚠ Read it at its own resolution. The disjunct is not decoration: at BabyBear the absorb IS collidable
by pigeonhole. What the statement says is that the forger must EXHIBIT one, at `2^123.63`, and that
the extractor hands the auditor the exact pair to check. -/
theorem distinct_table_moves_the_root (S : FoldScheme) (init : Digest8) {L₁ L₂ : List StakeRow}
    (hlen : L₁.length = L₂.length) (hne : L₁ ≠ L₂) :
    S.tableRoot init L₁ ≠ S.tableRoot init L₂
      ∨ Coll8 S.chipAbsorb8 (S.tableRootFind init L₁ L₂) := by
  by_cases hr : S.tableRoot init L₁ = S.tableRoot init L₂
  · exact Or.inr ((S.tableRoot_binds_or_collides init hlen hr).resolve_left hne)
  · exact Or.inl hr

/-- ⚑ …and the SAME-TALLY instance, which is the one that matters, because it is the one the sibling
rung's denominator pin CANNOT refuse.

⚠ **`htot` is not used by the proof, and that is the content.** The fold does not care what the
lamports add up to — it refuses every distinct table, tally-preserving or not
(`distinct_table_moves_the_root`, the general fact this is an instance of). Stating the instance is
how the two rungs are compared: `totalStakePins` refuses exactly the swaps `htot` EXCLUDES, and this
refuses the rest. -/
theorem same_tally_moves_the_root (S : FoldScheme) (init : Digest8) {L₁ L₂ : List StakeRow}
    (hlen : L₁.length = L₂.length)
    (_htot : totalStake L₁ = totalStake L₂)
    (hne : L₁ ≠ L₂) :
    S.tableRoot init L₁ ≠ S.tableRoot init L₂
      ∨ Coll8 S.chipAbsorb8 (S.tableRootFind init L₁ L₂) :=
  S.distinct_table_moves_the_root init hlen hne

end FoldScheme

/-! ### §4c — a CONCRETE same-tally pair, so the theorem above is not about an empty set.

Two two-entry tables at the SAME total (100 lamports) that differ only in WHICH validator holds which
share. `sameTallyPair_totals_agree` is the hypothesis of `same_tally_moves_the_root`, discharged; and
the two tables are genuinely distinct, so the conclusion bites. These are the exact rows the Rust
release test fills. -/

/-- Validator A's row, holding `stake` lamports. -/
def rowA (stake : ℤ) : StakeRow := ⟨11, 22, 33, 44, 55, 66, 77, 88, 99, stake, 0, 0, 0⟩
/-- Validator B's row, holding `stake` lamports. -/
def rowB (stake : ℤ) : StakeRow := ⟨111, 222, 333, 444, 555, 666, 777, 888, 999, stake, 0, 0, 0⟩

/-- The honest table: A holds 60 lamports, B holds 40. -/
def honestTable : List StakeRow := [rowA 60, rowB 40]

/-- The forged table: the SAME two validators, the SAME 100 lamports, the shares SWAPPED. A cartel
that holds 40 now claims 60. -/
def forgedTable : List StakeRow := [rowA 40, rowB 60]

theorem sameTallyPair_lengths_agree : honestTable.length = forgedTable.length := by decide

/-- ⚑ **THE TALLIES ARE IDENTICAL** — 100 lamports either way, so every denominator pin in
`solLcVerifyDesc` and every `ACC` gate in this rung accepts BOTH. -/
theorem sameTallyPair_totals_agree :
    FoldScheme.totalStake honestTable = 100 ∧ FoldScheme.totalStake forgedTable = 100 := by
  constructor <;> decide

/-- …and the tables are DIFFERENT, so `same_tally_moves_the_root` applies to them. -/
theorem sameTallyPair_tables_differ : honestTable ≠ forgedTable := by decide

/-- ⚑⚑ **THE PAIR, AS ONE STATEMENT.** For EVERY 8-output absorb carrier and every seed: these two
tables have the same tally and different roots — or the extractor names a chip collision. The Rust
release test is this statement on the deployed prover. -/
theorem sameTallyPair_is_refused (S : FoldScheme) (init : Digest8) :
    S.tableRoot init honestTable ≠ S.tableRoot init forgedTable
      ∨ Coll8 S.chipAbsorb8 (S.tableRootFind init honestTable forgedTable) :=
  S.same_tally_moves_the_root init sameTallyPair_lengths_agree
    (by rw [(sameTallyPair_totals_agree).1, (sameTallyPair_totals_agree).2])
    sameTallyPair_tables_differ

/-! ## §5 — the mod-`p` ↔ ℤ bridge for the tally chain.

An emitted gate forces its body `≡ 0 [ZMOD P]`, not `= 0`. The accumulator is EXACT anyway, and the
reason is the range legs and not luck: every term of an `accStep` body is gated below `2^16` (or is a
boolean carry), so the body's integer value lies strictly inside `(−P, P)` and the congruence lifts. -/

/-- ⚑ **THE ACCUMULATOR STEP IS EXACT.** With `acc`, `acc'`, `stk` in `[0, 2^16)` and `cin`, `cout`
boolean, the body `acc' + 2^16·cout − acc − stk − cin` lies strictly inside `(−P, P)`, so `≡ 0`
forces `= 0` over ℤ. This is what makes the four-limb running total a `u64` addition and not a
mod-`p` one. -/
theorem solStakeFold_acc_step_is_exact
    (acc acc' stk cin cout : ℤ)
    (hacc : 0 ≤ acc ∧ acc < 65536) (hacc' : 0 ≤ acc' ∧ acc' < 65536)
    (hstk : 0 ≤ stk ∧ stk < 65536)
    (hcin : cin = 0 ∨ cin = 1) (hcout : cout = 0 ∨ cout = 1) :
    -2013265921 < acc' + 65536 * cout - acc - stk - cin
      ∧ acc' + 65536 * cout - acc - stk - cin < 2013265921 := by
  obtain ⟨h1, h2⟩ := hacc
  obtain ⟨h3, h4⟩ := hacc'
  obtain ⟨h5, h6⟩ := hstk
  rcases hcin with hc | hc <;> rcases hcout with hd | hd <;> subst hc <;> subst hd <;>
    constructor <;> omega

/-- …and the width the four limbs buy: the running total is a `u64`, which is what
`LightClientSolanaAir` needed and one BabyBear column could never hold (live mainnet-beta active
stake is `2^58.586`, 214.9 MILLION times the modulus). -/
theorem solStakeFold_total_is_a_u64 :
    (65536 : ℤ) ^ 4 = 18446744073709551616
      ∧ (432650183925625587 : ℤ) < (65536 : ℤ) ^ 4 := by
  constructor <;> norm_num

/-! ## §6 — axiom hygiene. Named theorems, `#assert_axioms`, no `#guard`. -/

#assert_axioms solStakeFoldAir_mainRailOk
#assert_axioms solStakeFoldDesc_width
#assert_axioms solStakeFoldDesc_piCount
#assert_axioms solStakeFoldDesc_constraint_count
#assert_axioms solStakeFoldDesc_tables
#assert_axioms solStakeFold_table_wire_ids
#assert_axioms solStakeFold_chip_sites_are_arity_16
#assert_axioms FoldScheme.pack_inj
#assert_axioms FoldScheme.blocks_ne_of_ne
#assert_axioms FoldScheme.foldR_binds_or_collides
#assert_axioms FoldScheme.tableRoot_binds_or_collides
#assert_axioms FoldScheme.distinct_table_moves_the_root
#assert_axioms FoldScheme.same_tally_moves_the_root
#assert_axioms sameTallyPair_totals_agree
#assert_axioms sameTallyPair_is_refused
#assert_axioms solStakeFold_acc_step_is_exact
#assert_axioms solStakeFold_total_is_a_u64

end Dregg2.Circuit.Emit.LightClientSolStakeFoldAir
