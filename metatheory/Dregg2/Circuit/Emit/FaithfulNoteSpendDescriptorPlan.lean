/-
# Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan -- exact hidden-note spend AIR plan

This module fixes the wire geometry for the faithful note-spend descriptor before the new
full-state Poseidon2 lookup bus is imported.  It deliberately does **not** lower the plan through
the existing eight-output `poseidon2` bus: the live `hash_many_8` sponge needs all sixteen lanes of
one permutation's state as the input of the next permutation.  The old bus exposes lanes `0..7`
only, so using it would leave the capacity half of every absorb transition prover-selected.

The statement is the genuinely dark one, not a membership-only placeholder:

* the note opening `(owner, value, asset, nonce, randomness)` and spending key are hidden and use
  exact little-endian `u16` limbs;
* a domain-separated shielded owner address is derived from the hidden spending key, then
  canonically packed into the hidden sixteen-limb `owner`; this proves authorization while a
  sender needs only the recipient's shielded address, never their spending key;
* a domain-separated wide-v2 note commitment binds that owner and the rest of the hidden opening
  with the live rate-four `hash_many_8` schedule, then packs canonically into the hidden
  sixteen-limb tree leaf;
* the exact faithful leaf and 4-ary node sponges from `CommitmentTreeWide` are replayed to the
  historical eight-felt root;
* a domain-separated wide-v2 nullifier is derived from that same commitment, hidden key, and
  nonce, then canonically packed into the sixteen public nullifier limbs;
* height, historical root, value, asset, and the host-planned successor nullifier root are bound
  as public inputs.  The descriptor binds the successor root to the proof transcript; the current
  cut still computes and compares that successor outside this AIR.

No leaf commitment or leaf digest is public.  Publishing either identifies the spent note in the
public append-only tree and would turn a nominally shielded spend into a linkable membership proof.

`State16Step` is the exact lookup-neutral intermediate form consumed by the additive
`poseidon2_state16_chip` bus.  Each step is `[state16] -> [state16]`; every concrete sponge plan
below ends with one unmodified-state permutation for squeeze lanes 4..7.
-/
import Dregg2.Circuit.CommitmentTreeWide
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.FullStateChip
import Dregg2.Circuit.Emit.EffectVmEmit
import Mathlib.Tactic

namespace Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
  (CHIP_OUT_LANES CHIP_RATE TableId TableDef RowSemantics VmConstraint2 EffectVmDescriptor2
   mainTableDef poseidon2state16 poseidon2State16ChipTableDef chipLookupTupleState16 emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.CommitmentTreeWide

set_option autoImplicit false

/-! ## 1. Protocol and public-input geometry -/

def FIELD_MODULUS : Nat := 2013265921
def FIELD_HI_CANON_MAX : Nat := 0x7800
def STATE_LANES : Nat := 16
def DIGEST_LANES : Nat := 8
def BYTES32_U16_LIMBS : Nat := 16
def U64_U16_LIMBS : Nat := 4
def TREE_DEPTH : Nat := 16

/-- Pinned v2 domain tags, in the same ASCII-in-u32 family as the faithful tree domains.
They are protocol ABI and are mirrored byte-for-byte by the native runtime cutover. -/
def NOTE_COMMITMENT_V2_DOMAIN : Nat := 0x464e4332 -- `FNC2`
def NOTE_NULLIFIER_V2_DOMAIN : Nat := 0x464e4632  -- `FNF2`
def NOTE_OWNER_V2_DOMAIN : Nat := 0x464e4f32      -- `FNO2`

-- Public input order.  Every multi-limb integer/byte string is little-endian.
def PI_HEIGHT_BASE : Nat := 0
def PI_HISTORICAL_ROOT_BASE : Nat := PI_HEIGHT_BASE + U64_U16_LIMBS
def PI_NULLIFIER_BASE : Nat := PI_HISTORICAL_ROOT_BASE + DIGEST_LANES
def PI_VALUE_BASE : Nat := PI_NULLIFIER_BASE + BYTES32_U16_LIMBS
def PI_ASSET_BASE : Nat := PI_VALUE_BASE + U64_U16_LIMBS
def PI_SUCCESSOR_NULLIFIER_ROOT_BASE : Nat := PI_ASSET_BASE + U64_U16_LIMBS
def PI_COUNT : Nat := PI_SUCCESSOR_NULLIFIER_ROOT_BASE + DIGEST_LANES

#guard PI_HEIGHT_BASE == 0
#guard PI_HISTORICAL_ROOT_BASE == 4
#guard PI_NULLIFIER_BASE == 12
#guard PI_VALUE_BASE == 28
#guard PI_ASSET_BASE == 32
#guard PI_SUCCESSOR_NULLIFIER_ROOT_BASE == 36
#guard PI_COUNT == 44

/-! ## 2. Fixed depth-16 main-row layout

One main row is one faithful Merkle level.  Hashing the hidden note opening, nullifier, and leaf is
needed only on row zero, but current IR2 lookups are unguarded.  Those three sponge schedules are
therefore filled with genuine (possibly dummy off row zero) permutations on every row.  This is
safe and simple; a guarded-lookup optimization can remove the 15 redundant copies later.
-/

def CUR_BASE : Nat := 0                         -- 8
def SIB0_BASE : Nat := CUR_BASE + DIGEST_LANES  -- 8
def SIB1_BASE : Nat := SIB0_BASE + DIGEST_LANES -- 8
def SIB2_BASE : Nat := SIB1_BASE + DIGEST_LANES -- 8
def POS_B0 : Nat := SIB2_BASE + DIGEST_LANES
def POS_B1 : Nat := POS_B0 + 1

def OWNER_BASE : Nat := POS_B1 + 1                              -- 16 u16
def VALUE_BASE : Nat := OWNER_BASE + BYTES32_U16_LIMBS          -- 4 u16
def ASSET_BASE : Nat := VALUE_BASE + U64_U16_LIMBS              -- 4 u16
def NONCE_BASE : Nat := ASSET_BASE + U64_U16_LIMBS              -- 16 u16
def RANDOMNESS_BASE : Nat := NONCE_BASE + BYTES32_U16_LIMBS     -- 16 u16
def SPENDING_KEY_BASE : Nat := RANDOMNESS_BASE + BYTES32_U16_LIMBS -- 16 u16

-- owner-v2: 17 inputs => 5 absorbs + squeeze, packed into the existing hidden OWNER lanes.
def OWNER_STATE_BASE : Nat := SPENDING_KEY_BASE + BYTES32_U16_LIMBS
def OWNER_STATE_STEPS : Nat := 6
def OWNER_SLACK_BASE : Nat := OWNER_STATE_BASE + STATE_LANES * OWNER_STATE_STEPS
def OWNER_ZERO_BASE : Nat := OWNER_SLACK_BASE + DIGEST_LANES
def OWNER_INV_BASE : Nat := OWNER_ZERO_BASE + DIGEST_LANES

-- commitment-v2: 57 inputs => 15 absorb permutations + one squeeze permutation.
def COMMITMENT_STATE_BASE : Nat := OWNER_INV_BASE + DIGEST_LANES
def COMMITMENT_STATE_STEPS : Nat := 16
def COMMITMENT_RAW_BASE : Nat := COMMITMENT_STATE_BASE + STATE_LANES * COMMITMENT_STATE_STEPS
def COMMITMENT_SLACK_BASE : Nat := COMMITMENT_RAW_BASE + BYTES32_U16_LIMBS
def COMMITMENT_ZERO_BASE : Nat := COMMITMENT_SLACK_BASE + DIGEST_LANES
def COMMITMENT_INV_BASE : Nat := COMMITMENT_ZERO_BASE + DIGEST_LANES

-- nullifier-v2: 41 inputs => 11 absorb permutations + one squeeze permutation.
def NULLIFIER_STATE_BASE : Nat := COMMITMENT_INV_BASE + DIGEST_LANES
def NULLIFIER_STATE_STEPS : Nat := 12
def NULLIFIER_RAW_BASE : Nat := NULLIFIER_STATE_BASE + STATE_LANES * NULLIFIER_STATE_STEPS
def NULLIFIER_SLACK_BASE : Nat := NULLIFIER_RAW_BASE + BYTES32_U16_LIMBS
def NULLIFIER_ZERO_BASE : Nat := NULLIFIER_SLACK_BASE + DIGEST_LANES
def NULLIFIER_INV_BASE : Nat := NULLIFIER_ZERO_BASE + DIGEST_LANES

-- tree leaf: 17 inputs => 5 absorbs + squeeze; node: 33 inputs => 9 absorbs + squeeze.
def LEAF_STATE_BASE : Nat := NULLIFIER_INV_BASE + DIGEST_LANES
def LEAF_STATE_STEPS : Nat := 6
def NODE_STATE_BASE : Nat := LEAF_STATE_BASE + STATE_LANES * LEAF_STATE_STEPS
def NODE_STATE_STEPS : Nat := 10

def HEIGHT_BASE : Nat := NODE_STATE_BASE + STATE_LANES * NODE_STATE_STEPS
def SUCCESSOR_NULLIFIER_ROOT_BASE : Nat := HEIGHT_BASE + U64_U16_LIMBS
def LEVEL_COL : Nat := SUCCESSOR_NULLIFIER_ROOT_BASE + DIGEST_LANES
def TRACE_WIDTH : Nat := LEVEL_COL + 1

#guard CUR_BASE == 0
#guard OWNER_BASE == 34
#guard OWNER_STATE_BASE == 106
#guard COMMITMENT_STATE_BASE == 226
#guard COMMITMENT_RAW_BASE == 482
#guard NULLIFIER_STATE_BASE == 522
#guard NULLIFIER_RAW_BASE == 714
#guard LEAF_STATE_BASE == 754
#guard NODE_STATE_BASE == 850
#guard HEIGHT_BASE == 1010
#guard SUCCESSOR_NULLIFIER_ROOT_BASE == 1014
#guard LEVEL_COL == 1022
#guard TRACE_WIDTH == 1023

def cols (base count : Nat) : List Nat := (List.range count).map (base + ·)
def vars (base count : Nat) : List EmittedExpr := (cols base count).map .var
def stateCols (base step : Nat) : List Nat := cols (base + STATE_LANES * step) STATE_LANES

def ownerDigestCols : List Nat :=
  (cols (OWNER_STATE_BASE + STATE_LANES * 4) 4) ++
  (cols (OWNER_STATE_BASE + STATE_LANES * 5) 4)

def commitmentDigestCols : List Nat :=
  (cols (COMMITMENT_STATE_BASE + STATE_LANES * 14) 4) ++
  (cols (COMMITMENT_STATE_BASE + STATE_LANES * 15) 4)

def nullifierDigestCols : List Nat :=
  (cols (NULLIFIER_STATE_BASE + STATE_LANES * 10) 4) ++
  (cols (NULLIFIER_STATE_BASE + STATE_LANES * 11) 4)

def leafDigestCols : List Nat :=
  (cols (LEAF_STATE_BASE + STATE_LANES * 4) 4) ++
  (cols (LEAF_STATE_BASE + STATE_LANES * 5) 4)

def nodeDigestCols : List Nat :=
  (cols (NODE_STATE_BASE + STATE_LANES * 8) 4) ++
  (cols (NODE_STATE_BASE + STATE_LANES * 9) 4)

#guard ownerDigestCols.length == 8
#guard commitmentDigestCols.length == 8
#guard nullifierDigestCols.length == 8
#guard leafDigestCols.length == 8
#guard nodeDigestCols.length == 8
#guard nodeDigestCols == [978, 979, 980, 981, 994, 995, 996, 997]

/-! ## 3. Exact public pin contract -/

structure PublicPin where
  row : VmRow
  col : Nat
  pi : Nat
  deriving Repr, DecidableEq

def pins (row : VmRow) (traceCols : List Nat) (piBase : Nat) : List PublicPin :=
  traceCols.mapIdx fun i col => ⟨row, col, piBase + i⟩

/-- Exact verifier ABI.  Historical root is last-row derived; everything else is a row-zero
carrier.  The leaf commitment is intentionally absent. -/
def publicPins : List PublicPin :=
  pins .first (cols HEIGHT_BASE U64_U16_LIMBS) PI_HEIGHT_BASE ++
  pins .last nodeDigestCols PI_HISTORICAL_ROOT_BASE ++
  pins .first (cols NULLIFIER_RAW_BASE BYTES32_U16_LIMBS) PI_NULLIFIER_BASE ++
  pins .first (cols VALUE_BASE U64_U16_LIMBS) PI_VALUE_BASE ++
  pins .first (cols ASSET_BASE U64_U16_LIMBS) PI_ASSET_BASE ++
  pins .first (cols SUCCESSOR_NULLIFIER_ROOT_BASE DIGEST_LANES)
    PI_SUCCESSOR_NULLIFIER_ROOT_BASE

#guard publicPins.length == PI_COUNT
#guard publicPins.map (·.pi) == List.range PI_COUNT
#guard (publicPins.any fun pin => COMMITMENT_RAW_BASE ≤ pin.col &&
  pin.col < COMMITMENT_RAW_BASE + BYTES32_U16_LIMBS) == false

/-! ## 4. Full-state sponge lookup plan -/

/-- One required row of the additive state16 bus.  The actual lowering is
`chipLookupTupleState16 input outputCols`, a 33-expression tuple
`[16, input0..15, output0..15]`. -/
structure State16Step where
  input : List EmittedExpr
  outputCols : List Nat
  deriving Repr

def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
def emul (a b : EmittedExpr) : EmittedExpr := .mul a b
def eneg (a : EmittedExpr) : EmittedExpr := emul (.const (-1)) a
def esub (a b : EmittedExpr) : EmittedExpr := eadd a (eneg b)

def chunks4 {α : Type} (xs : List α) : List (List α) := xs.toChunks 4

def initialStateExpr (inputLength : Nat) : List EmittedExpr :=
  (List.range STATE_LANES).map fun i => if i = 4 then .const inputLength else .const 0

def padChunk (chunk : List EmittedExpr) : List EmittedExpr :=
  chunk ++ List.replicate (4 - chunk.length) (.const 0)

def priorStateExpr (stateBase stage : Nat) : List EmittedExpr :=
  if stage = 0 then [] else (stateCols stateBase (stage - 1)).map .var

/-- Input state for absorb `stage`: the prior full state (or the length-tagged zero state for
stage zero) plus this rate-four chunk in lanes 0..3. -/
def absorbInputExpr (stateBase inputLength stage : Nat) (chunk : List EmittedExpr) : List EmittedExpr :=
  let prior := if stage = 0 then initialStateExpr inputLength else priorStateExpr stateBase stage
  let rate := padChunk chunk
  (List.range STATE_LANES).map fun i =>
    if i < 4 then eadd (prior.getD i (.const 0)) (rate.getD i (.const 0))
    else prior.getD i (.const 0)

/-- Exact live `hash_many_8` schedule: one state16 permutation after every rate-four absorb,
then one final unmodified-state permutation whose first four lanes supply digest lanes 4..7. -/
def spongePlan (stateBase : Nat) (preimage : List EmittedExpr) : List State16Step :=
  let chunks := chunks4 preimage
  let absorb := chunks.mapIdx fun stage chunk =>
    ⟨absorbInputExpr stateBase preimage.length stage chunk, stateCols stateBase stage⟩
  let squeeze :=
    ⟨(stateCols stateBase (chunks.length - 1)).map .var, stateCols stateBase chunks.length⟩
  absorb ++ [squeeze]

def ownerPreimage : List EmittedExpr :=
  .const NOTE_OWNER_V2_DOMAIN :: vars SPENDING_KEY_BASE BYTES32_U16_LIMBS

def commitmentPreimage : List EmittedExpr :=
  .const NOTE_COMMITMENT_V2_DOMAIN ::
    (vars OWNER_BASE BYTES32_U16_LIMBS ++ vars VALUE_BASE U64_U16_LIMBS ++
      vars ASSET_BASE U64_U16_LIMBS ++ vars NONCE_BASE BYTES32_U16_LIMBS ++
      vars RANDOMNESS_BASE BYTES32_U16_LIMBS)

def nullifierPreimage : List EmittedExpr :=
  .const NOTE_NULLIFIER_V2_DOMAIN ::
    (commitmentDigestCols.map .var ++ vars SPENDING_KEY_BASE BYTES32_U16_LIMBS ++
      vars NONCE_BASE BYTES32_U16_LIMBS)

def leafPreimage : List EmittedExpr :=
  .const NOTE_LEAF_DOMAIN :: vars COMMITMENT_RAW_BASE BYTES32_U16_LIMBS

/-! The four positional child groups are built directly as expressions, so no 32-column child
copy band and no independent copy gates exist. -/

def cur (lane : Nat) : EmittedExpr := .var (CUR_BASE + lane)
def sib0 (lane : Nat) : EmittedExpr := .var (SIB0_BASE + lane)
def sib1 (lane : Nat) : EmittedExpr := .var (SIB1_BASE + lane)
def sib2 (lane : Nat) : EmittedExpr := .var (SIB2_BASE + lane)
def b0 : EmittedExpr := .var POS_B0
def b1 : EmittedExpr := .var POS_B1
def oneMinus (x : EmittedExpr) : EmittedExpr := esub (.const 1) x

def ind0 : EmittedExpr := emul (oneMinus b0) (oneMinus b1)
def ind1 : EmittedExpr := emul b0 (oneMinus b1)
def ind2 : EmittedExpr := emul (oneMinus b0) b1
def ind3 : EmittedExpr := emul b0 b1

def childExpr (slot lane : Nat) : EmittedExpr :=
  match slot with
  | 0 => eadd (sib0 lane) (emul ind0 (esub (cur lane) (sib0 lane)))
  | 1 => eadd (eadd (emul (sib0 lane) ind0) (emul (cur lane) ind1))
      (emul (sib1 lane) (eadd ind2 ind3))
  | 2 => eadd (eadd (emul (sib1 lane) (eadd ind0 ind1)) (emul (cur lane) ind2))
      (emul (sib2 lane) ind3)
  | _ => eadd (sib2 lane) (emul ind3 (esub (cur lane) (sib2 lane)))

def nodePreimage : List EmittedExpr :=
  .const NOTE_NODE_DOMAIN ::
    ((List.range 4).flatMap fun slot => (List.range DIGEST_LANES).map (childExpr slot))

def ownerPlan : List State16Step := spongePlan OWNER_STATE_BASE ownerPreimage
def commitmentPlan : List State16Step := spongePlan COMMITMENT_STATE_BASE commitmentPreimage
def nullifierPlan : List State16Step := spongePlan NULLIFIER_STATE_BASE nullifierPreimage
def leafPlan : List State16Step := spongePlan LEAF_STATE_BASE leafPreimage
def nodePlan : List State16Step := spongePlan NODE_STATE_BASE nodePreimage
def allPermutationSteps : List State16Step :=
  ownerPlan ++ commitmentPlan ++ nullifierPlan ++ leafPlan ++ nodePlan

#guard ownerPreimage.length == 17
#guard commitmentPreimage.length == 57
#guard nullifierPreimage.length == 41
#guard leafPreimage.length == 17
#guard nodePreimage.length == 33
#guard ownerPlan.length == OWNER_STATE_STEPS
#guard commitmentPlan.length == COMMITMENT_STATE_STEPS
#guard nullifierPlan.length == NULLIFIER_STATE_STEPS
#guard leafPlan.length == LEAF_STATE_STEPS
#guard nodePlan.length == NODE_STATE_STEPS
#guard allPermutationSteps.length == 50
#guard allPermutationSteps.all fun step => step.input.length == STATE_LANES
#guard allPermutationSteps.all fun step => step.outputCols.length == STATE_LANES

/-! ## 5. Canonical field-to-two-u16 packing

An equality `digest = lo + 2^16 hi` alone is not enough over BabyBear: for small digest values,
`digest + p` also fits in 31 bits.  The `hi/slack/zero/inv` gadget below proves the reconstructed
u32 is `< p = 0x78000001`:

* `hi + slack = 0x7800`, with both `hi` and `slack` 15-bit;
* `z` is the exact zero indicator of `slack`;
* if `slack = 0` (so `hi = 0x7800`), `lo = 0`.

Thus every eight-felt digest has one canonical 32-byte / sixteen-u16 image in the AIR.
-/

structure Pack8Plan where
  digestCols : List Nat
  rawBase : Nat
  slackBase : Nat
  zeroBase : Nat
  invBase : Nat
  deriving Repr

def ownerPack : Pack8Plan :=
  ⟨ownerDigestCols, OWNER_BASE, OWNER_SLACK_BASE, OWNER_ZERO_BASE, OWNER_INV_BASE⟩

def commitmentPack : Pack8Plan :=
  ⟨commitmentDigestCols, COMMITMENT_RAW_BASE, COMMITMENT_SLACK_BASE,
    COMMITMENT_ZERO_BASE, COMMITMENT_INV_BASE⟩

def nullifierPack : Pack8Plan :=
  ⟨nullifierDigestCols, NULLIFIER_RAW_BASE, NULLIFIER_SLACK_BASE,
    NULLIFIER_ZERO_BASE, NULLIFIER_INV_BASE⟩

def packBodiesAt (plan : Pack8Plan) (lane : Nat) : List EmittedExpr :=
  let digest := .var (plan.digestCols.getD lane 0)
  let lo := .var (plan.rawBase + 2 * lane)
  let hi := .var (plan.rawBase + 2 * lane + 1)
  let slack := .var (plan.slackBase + lane)
  let z := .var (plan.zeroBase + lane)
  let inv := .var (plan.invBase + lane)
  [ esub digest (eadd lo (emul (.const 65536) hi)),
    esub (eadd hi slack) (.const FIELD_HI_CANON_MAX),
    emul z (esub z (.const 1)),
    esub (emul slack inv) (oneMinus z),
    emul z slack,
    emul z lo ]

def packBodies (plan : Pack8Plan) : List EmittedExpr :=
  (List.range DIGEST_LANES).flatMap (packBodiesAt plan)

#guard (packBodies ownerPack).length == 48
#guard (packBodies commitmentPack).length == 48
#guard (packBodies nullifierPack).length == 48

structure RangePlan where
  col : Nat
  bits : Nat
  deriving Repr, DecidableEq

def u16Ranges (base count : Nat) : List RangePlan := (cols base count).map (⟨·, 16⟩)
def packRanges (plan : Pack8Plan) : List RangePlan :=
  (List.range DIGEST_LANES).flatMap fun lane =>
    [⟨plan.rawBase + 2 * lane, 16⟩, ⟨plan.rawBase + 2 * lane + 1, 15⟩,
      ⟨plan.slackBase + lane, 15⟩]

def rangePlan : List RangePlan :=
  u16Ranges VALUE_BASE U64_U16_LIMBS ++
  u16Ranges ASSET_BASE U64_U16_LIMBS ++
  u16Ranges NONCE_BASE BYTES32_U16_LIMBS ++
  u16Ranges RANDOMNESS_BASE BYTES32_U16_LIMBS ++
  u16Ranges SPENDING_KEY_BASE BYTES32_U16_LIMBS ++
  packRanges ownerPack ++ packRanges commitmentPack ++ packRanges nullifierPack ++
  u16Ranges HEIGHT_BASE U64_U16_LIMBS

#guard rangePlan.length == 132

/-! ## 6. Capacity accounting and the current-bus refusal -/

def CURRENT_P2_TUPLE : Nat := 1 + CHIP_RATE + CHIP_OUT_LANES
def REQUIRED_STATE16_TUPLE : Nat := 1 + STATE_LANES + STATE_LANES
def LOOKUPS_PER_ROW : Nat := allPermutationSteps.length
def TOTAL_STATE16_LOOKUPS : Nat := TREE_DEPTH * LOOKUPS_PER_ROW

theorem current_p2_bus_cannot_carry_sponge_state : CHIP_OUT_LANES < STATE_LANES := by decide

#guard CURRENT_P2_TUPLE == 25
#guard REQUIRED_STATE16_TUPLE == 33
#guard LOOKUPS_PER_ROW == 50
#guard TOTAL_STATE16_LOOKUPS == 800

/-! ## 7. Concrete IR2 lowering

The additive `poseidon2_state16_chip` bus now exists, so the plan lowers without weakening any
sponge transition.  Its lookup is deliberately unguarded: the current IR2 lookup grammar fires on
every main row.  An honest witness repeats the same hidden opening and its commitment/nullifier/leaf
chains on all sixteen rows; only the node chain, sibling groups, and position bits vary by level.

`root_height` is the ledger checkpoint height used by the host to select the historical root.  It
is not the Merkle arity-depth: this descriptor's proof tree is fixed at sixteen 4-ary levels.
-/

/-- Keep the deployed width-tagged range-table convention: non-30-bit table `b` is custom slot
`64+b`, hence wire id `69+b`.  This descriptor needs exact 15- and 16-bit relations. -/
def RANGE_W_TID_BASE : Nat := 64

def rangeTid (bits : Nat) : TableId :=
  if bits = 30 then .range else .custom (RANGE_W_TID_BASE + bits)

def rangeTable (bits : Nat) : TableDef :=
  ⟨rangeTid bits, "range_w" ++ toString bits, 1, .rangeLimb bits⟩

#guard (rangeTid 15).wireId == 84
#guard (rangeTid 16).wireId == 85

def state16Lookup (step : State16Step) : VmConstraint2 :=
  .lookup ⟨poseidon2state16, chipLookupTupleState16 step.input step.outputCols⟩

def state16Lookups : List VmConstraint2 := allPermutationSteps.map state16Lookup

def rangeLookup (r : RangePlan) : VmConstraint2 :=
  .lookup ⟨rangeTid r.bits, [.var r.col]⟩

def rangeLookups : List VmConstraint2 := rangePlan.map rangeLookup

def bitBody (col : Nat) : EmittedExpr :=
  emul (.var col) (esub (.var col) (.const 1))

def positionBodies : List EmittedExpr := [bitBody POS_B0, bitBody POS_B1]

/-- Ordinary gates fire on every transition row; the matching last-row boundaries close the top
level, exactly as the established 4-ary membership descriptors do. -/
def positionConstraints : List VmConstraint2 :=
  positionBodies.map (fun body => .base (.gate body)) ++
  positionBodies.map (fun body => .base (.boundary .last body))

/-- Canonical commitment/nullifier packing is needed only at the first row, where the hidden
opening, public nullifier, and initial Merkle digest meet. -/
def firstPackConstraints : List VmConstraint2 :=
  (packBodies ownerPack ++ packBodies commitmentPack ++ packBodies nullifierPack).map fun body =>
    .base (.boundary .first body)

def leafLinkBodies : List EmittedExpr :=
  (List.range DIGEST_LANES).map fun lane =>
    esub (cur lane) (.var (leafDigestCols.getD lane 0))

def leafLinkConstraints : List VmConstraint2 :=
  leafLinkBodies.map fun body => .base (.boundary .first body)

def continuityWindow (lane : Nat) : Dregg2.Circuit.DescriptorIR2.WindowExpr :=
  .add (.nxt (CUR_BASE + lane))
    (.mul (.const (-1)) (.loc (nodeDigestCols.getD lane 0)))

/-- Every transition carries all eight parent lanes into the next level. -/
def continuityConstraints : List VmConstraint2 :=
  (List.range DIGEST_LANES).map fun lane =>
    .windowGate ⟨continuityWindow lane, true⟩

/-- In-AIR fixed-depth tooth.  The first row is level zero, every transition increments by one,
and the last row is level fifteen.  Therefore a feasible ordinary-size trace has exactly sixteen
rows; the dedicated verifier additionally pins the main-instance degree bits as defense in depth. -/
def depthConstraints : List VmConstraint2 :=
  [ .base (.boundary .first (.var LEVEL_COL))
  , .windowGate ⟨
      .add (.nxt LEVEL_COL)
        (.add (.mul (.const (-1)) (.loc LEVEL_COL)) (.const (-1))), true⟩
  , .base (.boundary .last (esub (.var LEVEL_COL) (.const (TREE_DEPTH - 1)))) ]

def publicPinConstraint (pin : PublicPin) : VmConstraint2 :=
  .base (.piBinding pin.row pin.col pin.pi)

def publicPinConstraints : List VmConstraint2 := publicPins.map publicPinConstraint

def faithfulSpendConstraints : List VmConstraint2 :=
  state16Lookups ++ rangeLookups ++ positionConstraints ++ firstPackConstraints ++
    leafLinkConstraints ++ continuityConstraints ++ depthConstraints ++ publicPinConstraints

/-- The concrete Lean-authored hidden-spend descriptor.  There are no legacy hash-site or range
carriers: every permutation uses the complete state16 relation, and every limb bound is an explicit
width-tagged range lookup. -/
def faithfulNoteSpendDescriptor : EffectVmDescriptor2 :=
  { name := "faithful-note-spend-v2::exact-note16-root8-hiding"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := [mainTableDef TRACE_WIDTH, poseidon2State16ChipTableDef,
      rangeTable 15, rangeTable 16]
  , constraints := faithfulSpendConstraints
  , hashSites := []
  , ranges := [] }

#guard state16Lookups.length == 50
#guard state16Lookups.all fun c => match c with
  | .lookup l => l.table == poseidon2state16 && l.tuple.length == REQUIRED_STATE16_TUPLE
  | _ => false
#guard rangeLookups.length == 132
#guard positionConstraints.length == 4
#guard firstPackConstraints.length == 144
#guard leafLinkConstraints.length == 8
#guard continuityConstraints.length == 8
#guard depthConstraints.length == 3
#guard publicPinConstraints.length == PI_COUNT
#guard faithfulSpendConstraints.length == 393
#guard faithfulNoteSpendDescriptor.traceWidth == 1023
#guard faithfulNoteSpendDescriptor.piCount == 44
#guard faithfulNoteSpendDescriptor.tables.length == 4
#guard faithfulNoteSpendDescriptor.hashSites.isEmpty
#guard faithfulNoteSpendDescriptor.ranges.isEmpty

/-- Canonical wire image.  `EmitByName.lean` routes these exact bytes to
`circuit/descriptors/by-name/faithful-note-spend-v2.json`; the repository descriptor-drift gate
compares that artifact byte-for-byte against a fresh evaluation of this definition. -/
def faithfulNoteSpendDescriptorJson : String := emitVmJson2 faithfulNoteSpendDescriptor

-- Compact in-module KATs; the drift gate is the full 96,534-byte equality pin.
#guard faithfulNoteSpendDescriptorJson.length == 96534
#guard faithfulNoteSpendDescriptorJson.startsWith
  "{\"name\":\"faithful-note-spend-v2::exact-note16-root8-hiding\",\"ir\":2,\"trace_width\":1023"

#assert_axioms current_p2_bus_cannot_carry_sponge_state

end Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan
