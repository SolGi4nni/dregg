/-
# ShieldedExactApexV4Descriptor — emitted one-opening shielded exact swap

This is the concrete, bounded DescriptorIR2 realization of the semantic relation in
`Dregg2.Circuit.ShieldedExactApexV4`.

The fixed market rule is an atomic whole-note swap.  There are exactly two hidden inputs and two
hidden outputs.  Output zero gives the counterparty input's complete value/asset to the selected
owner; output one gives the selected input's complete value/asset to the counterparty owner.  Thus
per-asset conservation is structural, not a host-computed scalar check.

One selected opening supplies all of:

* two domain-separated Poseidon2 sponges whose sixteen low-u16 output words are the full public
  nullifier (the discarded high words are range-constrained and recomposed in-circuit);
* the two eight-lane sponges forming the public wide value/asset binding;
* input zero of the fixed swap; and
* the new FNI4 linked leaf inserted into the exact accumulator.

The exact transition is a linked-leaf AAFI over a fixed depth-32 binary tree.  It authenticates and
rewrites the predecessor leaf, authenticates an empty leaf at the exact pre-count cursor, appends
the new leaf, and derives the public successor root and `count + 1`.  FNI4, FNE4, FNN4, and FNS4 are
separate domains.  Public historical/outer roots are absorbed into FXC4 but their membership and
whole-cell transition semantics belong to the surrounding consensus/frame relation.

Every semantic polynomial is a FIRST-row boundary, so height-one/last-row vacuity is impossible.
Hash lookups remain unguarded and therefore execute on every row, as required by DescriptorIR2.
-/

import Dregg2.Circuit.ShieldedExactApexV4
import Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan

namespace Dregg2.Circuit.Emit.ShieldedExactApexV4Descriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.FaithfulNoteSpendDescriptorPlan
open Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan

set_option autoImplicit false

/-! ## Fixed protocol geometry -/

def DEPTH : Nat := 32
def ROOT_LANES : Nat := 8
def KEY_LANES : Nat := 16
def U64_LANES : Nat := 4
def OPENING_LANES : Nat := 20
def WIDE_LANES : Nat := 16

def FNI4 : Int := 0x464e4934
def FNE4 : Int := 0x464e4534
def FNN4 : Int := 0x464e4e34
def FNS4 : Int := 0x464e5334
def FXO4 : Int := 0x46584f34
def FXC4 : Int := 0x46584334
def NULLIFIER_FORK0 : Int := 0x4e463430
def NULLIFIER_FORK1 : Int := 0x4e463431
def NOTE_FORK0 : Int := 0x4e543430
def NOTE_FORK1 : Int := 0x4e543431

def U16 : Nat := 65536

/-! ## Main-row columns -/

def SELECTED_BASE : Nat := 0
def COUNTER_BASE : Nat := SELECTED_BASE + OPENING_LANES
def OUTPUT0_BASE : Nat := COUNTER_BASE + OPENING_LANES
def OUTPUT1_BASE : Nat := OUTPUT0_BASE + OPENING_LANES
def SECRET_BASE : Nat := OUTPUT1_BASE + OPENING_LANES
def NULLIFIER_BASE : Nat := SECRET_BASE + KEY_LANES
def NULLIFIER_HIGH_BASE : Nat := NULLIFIER_BASE + KEY_LANES
def BINDING_BASE : Nat := NULLIFIER_HIGH_BASE + KEY_LANES
def PRIOR_ROOT_BASE : Nat := BINDING_BASE + WIDE_LANES
def SUCCESSOR_ROOT_BASE : Nat := PRIOR_ROOT_BASE + ROOT_LANES
def PRE_COUNT_BASE : Nat := SUCCESSOR_ROOT_BASE + ROOT_LANES
def POST_COUNT_BASE : Nat := PRE_COUNT_BASE + U64_LANES
def HISTORICAL_HEIGHT_BASE : Nat := POST_COUNT_BASE + U64_LANES
def HISTORICAL_ROOT_BASE : Nat := HISTORICAL_HEIGHT_BASE + U64_LANES
def BEFORE_OUTER_BASE : Nat := HISTORICAL_ROOT_BASE + ROOT_LANES
def AFTER_OUTER_BASE : Nat := BEFORE_OUTER_BASE + ROOT_LANES
def OUTPUT0_COMMIT_BASE : Nat := AFTER_OUTER_BASE + ROOT_LANES
def OUTPUT1_COMMIT_BASE : Nat := OUTPUT0_COMMIT_BASE + WIDE_LANES
def OUTPUT_ROOT_BASE : Nat := OUTPUT1_COMMIT_BASE + WIDE_LANES
def CONSEQUENCE_BASE : Nat := OUTPUT_ROOT_BASE + ROOT_LANES

def LOW_ADDR_TAG : Nat := CONSEQUENCE_BASE + ROOT_LANES
def LOW_ADDR_BASE : Nat := LOW_ADDR_TAG + 1
def LOW_BINDING_BASE : Nat := LOW_ADDR_BASE + KEY_LANES
def LOW_NEXT_TAG : Nat := LOW_BINDING_BASE + WIDE_LANES
def LOW_NEXT_BASE : Nat := LOW_NEXT_TAG + 1
def LOW_POS_BITS : Nat := LOW_NEXT_BASE + KEY_LANES
def APP_POS_BITS : Nat := LOW_POS_BITS + DEPTH
def LOW_SIB_BASE : Nat := APP_POS_BITS + DEPTH
def APP_SIB_BASE : Nat := LOW_SIB_BASE + DEPTH * ROOT_LANES
def LEX_LOW_AUX_BASE : Nat := APP_SIB_BASE + DEPTH * ROOT_LANES
def LEX_NEXT_AUX_BASE : Nat := LEX_LOW_AUX_BASE + 17
def COUNT_CARRY_BASE : Nat := LEX_NEXT_AUX_BASE + 17

def openingValueBase (base : Nat) : Nat := base
def openingAssetBase (base : Nat) : Nat := base + 4
def openingRandomBase (base : Nat) : Nat := base + 8
def openingOwnerBase (base : Nat) : Nat := base + 12
def openingNonceBase (base : Nat) : Nat := base + 16

/-! ## Concrete sponge schedules -/

def wideTranscript (fork : Int) : List EmittedExpr :=
  [.const fork, .const 0x4452, .const 0x4547, .const 0x4757, .const 0x5051,
    .const 1, .const 1, .const 12] ++ vars SELECTED_BASE 12

def nullifierTranscript (fork : Int) : List EmittedExpr :=
  [.const fork, .const FNI4] ++ vars SECRET_BASE KEY_LANES ++ vars SELECTED_BASE OPENING_LANES

def noteTranscript (fork : Int) (openingBase : Nat) : List EmittedExpr :=
  [.const fork, .const 1] ++ vars openingBase OPENING_LANES

def leafPreimage (addrTag addrBase bindingBase nextTag nextBase : Nat) : List EmittedExpr :=
  [.const FNI4, .var addrTag] ++ vars addrBase KEY_LANES ++ vars bindingBase WIDE_LANES ++
    [.var nextTag] ++ vars nextBase KEY_LANES

def lowOldLeafPreimage : List EmittedExpr :=
  leafPreimage LOW_ADDR_TAG LOW_ADDR_BASE LOW_BINDING_BASE LOW_NEXT_TAG LOW_NEXT_BASE

def lowNewLeafPreimage : List EmittedExpr :=
  [.const FNI4, .var LOW_ADDR_TAG] ++ vars LOW_ADDR_BASE KEY_LANES ++
    vars LOW_BINDING_BASE WIDE_LANES ++ [.const 1] ++ vars NULLIFIER_BASE KEY_LANES

def appendedLeafPreimage : List EmittedExpr :=
  [.const FNI4, .const 1] ++ vars NULLIFIER_BASE KEY_LANES ++ vars BINDING_BASE WIDE_LANES ++
    [.var LOW_NEXT_TAG] ++ vars LOW_NEXT_BASE KEY_LANES

def statePreimage (rootBase countBase : Nat) : List EmittedExpr :=
  [.const FNS4] ++ vars rootBase ROOT_LANES ++ vars countBase U64_LANES

def outputRootPreimage : List EmittedExpr :=
  [.const FXO4] ++ vars OUTPUT0_COMMIT_BASE WIDE_LANES ++ vars OUTPUT1_COMMIT_BASE WIDE_LANES

def consequencePreimage (preStateBase postStateBase : Nat) : List EmittedExpr :=
  [.const FXC4, .const 1, .const 0, .const 2] ++
    vars NULLIFIER_BASE KEY_LANES ++ vars BINDING_BASE WIDE_LANES ++
    vars preStateBase ROOT_LANES ++ vars postStateBase ROOT_LANES ++
    vars OUTPUT_ROOT_BASE ROOT_LANES ++ vars HISTORICAL_HEIGHT_BASE U64_LANES ++
    vars HISTORICAL_ROOT_BASE ROOT_LANES ++ vars BEFORE_OUTER_BASE ROOT_LANES ++
    vars AFTER_OUTER_BASE ROOT_LANES

def spongeCols (inputs : List EmittedExpr) : Nat := 16 * ((chunks4 inputs).length + 1)

def NULLIFIER0_STATE : Nat := COUNT_CARRY_BASE + 3
def NULLIFIER1_STATE : Nat := NULLIFIER0_STATE + spongeCols (nullifierTranscript NULLIFIER_FORK0)
def WIDE0_STATE : Nat := NULLIFIER1_STATE + spongeCols (nullifierTranscript NULLIFIER_FORK1)
def WIDE1_STATE : Nat := WIDE0_STATE + spongeCols (wideTranscript 0)
def LOW_OLD_LEAF_STATE : Nat := WIDE1_STATE + spongeCols (wideTranscript 1)
def LOW_NEW_LEAF_STATE : Nat := LOW_OLD_LEAF_STATE + spongeCols lowOldLeafPreimage
def APPENDED_LEAF_STATE : Nat := LOW_NEW_LEAF_STATE + spongeCols lowNewLeafPreimage
def OUTPUT0_NOTE0_STATE : Nat := APPENDED_LEAF_STATE + spongeCols appendedLeafPreimage
def OUTPUT0_NOTE1_STATE : Nat := OUTPUT0_NOTE0_STATE + spongeCols (noteTranscript NOTE_FORK0 OUTPUT0_BASE)
def OUTPUT1_NOTE0_STATE : Nat := OUTPUT0_NOTE1_STATE + spongeCols (noteTranscript NOTE_FORK1 OUTPUT0_BASE)
def OUTPUT1_NOTE1_STATE : Nat := OUTPUT1_NOTE0_STATE + spongeCols (noteTranscript NOTE_FORK0 OUTPUT1_BASE)
def OUTPUT_ROOT_STATE : Nat := OUTPUT1_NOTE1_STATE + spongeCols (noteTranscript NOTE_FORK1 OUTPUT1_BASE)
def PRE_STATE_COMMIT_STATE : Nat := OUTPUT_ROOT_STATE + spongeCols outputRootPreimage
def POST_STATE_COMMIT_STATE : Nat := PRE_STATE_COMMIT_STATE + spongeCols (statePreimage PRIOR_ROOT_BASE PRE_COUNT_BASE)
def CONSEQUENCE_STATE : Nat := POST_STATE_COMMIT_STATE + spongeCols (statePreimage SUCCESSOR_ROOT_BASE POST_COUNT_BASE)

def digestCols (stateBase : Nat) (inputs : List EmittedExpr) : List Nat :=
  digestColsAt stateBase (chunks4 inputs).length

def NULLIFIER0_DIGEST : List Nat := digestCols NULLIFIER0_STATE (nullifierTranscript NULLIFIER_FORK0)
def NULLIFIER1_DIGEST : List Nat := digestCols NULLIFIER1_STATE (nullifierTranscript NULLIFIER_FORK1)
def WIDE0_DIGEST : List Nat := digestCols WIDE0_STATE (wideTranscript 0)
def WIDE1_DIGEST : List Nat := digestCols WIDE1_STATE (wideTranscript 1)
def LOW_OLD_LEAF_DIGEST : List Nat := digestCols LOW_OLD_LEAF_STATE lowOldLeafPreimage
def LOW_NEW_LEAF_DIGEST : List Nat := digestCols LOW_NEW_LEAF_STATE lowNewLeafPreimage
def APPENDED_LEAF_DIGEST : List Nat := digestCols APPENDED_LEAF_STATE appendedLeafPreimage
def OUTPUT0_COMMIT0 : List Nat := digestCols OUTPUT0_NOTE0_STATE (noteTranscript NOTE_FORK0 OUTPUT0_BASE)
def OUTPUT0_COMMIT1 : List Nat := digestCols OUTPUT0_NOTE1_STATE (noteTranscript NOTE_FORK1 OUTPUT0_BASE)
def OUTPUT1_COMMIT0 : List Nat := digestCols OUTPUT1_NOTE0_STATE (noteTranscript NOTE_FORK0 OUTPUT1_BASE)
def OUTPUT1_COMMIT1 : List Nat := digestCols OUTPUT1_NOTE1_STATE (noteTranscript NOTE_FORK1 OUTPUT1_BASE)
def OUTPUT_ROOT_DIGEST : List Nat := digestCols OUTPUT_ROOT_STATE outputRootPreimage
def PRE_STATE_DIGEST : List Nat := digestCols PRE_STATE_COMMIT_STATE (statePreimage PRIOR_ROOT_BASE PRE_COUNT_BASE)
def POST_STATE_DIGEST : List Nat := digestCols POST_STATE_COMMIT_STATE (statePreimage SUCCESSOR_ROOT_BASE POST_COUNT_BASE)

/- The consequence sponge needs contiguous copies of the two state digests. -/
def PRE_STATE_COPY : Nat := CONSEQUENCE_STATE + spongeCols (consequencePreimage 0 0)
def POST_STATE_COPY : Nat := PRE_STATE_COPY + ROOT_LANES
def CONSEQUENCE_REAL_STATE : Nat := POST_STATE_COPY + ROOT_LANES

def consequenceRealPreimage : List EmittedExpr := consequencePreimage PRE_STATE_COPY POST_STATE_COPY
def CONSEQUENCE_REAL_DIGEST : List Nat := digestCols CONSEQUENCE_REAL_STATE consequenceRealPreimage

/-! ## Binary exact tree columns and lookups -/

def NODE_STATE_BASE : Nat := CONSEQUENCE_REAL_STATE + spongeCols consequenceRealPreimage
def NODE_STATE_STRIDE : Nat := spongeCols (List.replicate 17 (.const 0))
def nodeStateBase (chain level : Nat) : Nat :=
  NODE_STATE_BASE + (chain * DEPTH + level) * NODE_STATE_STRIDE
def nodeDigestCols (chain level : Nat) : List Nat :=
  digestColsAt (nodeStateBase chain level) 5
def TRACE_WIDTH : Nat := NODE_STATE_BASE + 4 * DEPTH * NODE_STATE_STRIDE

def pathBit (chain level : Nat) : EmittedExpr :=
  .var ((if chain < 2 then LOW_POS_BITS else APP_POS_BITS) + level)
def pathSibling (chain level lane : Nat) : EmittedExpr :=
  .var ((if chain < 2 then LOW_SIB_BASE else APP_SIB_BASE) + level * ROOT_LANES + lane)

def emptyLeafDigest : List Nat :=
  Dregg2.Circuit.CommitmentTreeWide.hashMany8Real [fieldNat FNE4]

def chainLeaf (chain lane : Nat) : EmittedExpr :=
  match chain with
  | 0 => .var (LOW_OLD_LEAF_DIGEST.getD lane 0)
  | 1 => .var (LOW_NEW_LEAF_DIGEST.getD lane 0)
  | 2 => .const (emptyLeafDigest.getD lane 0)
  | _ => .var (APPENDED_LEAF_DIGEST.getD lane 0)

def chainCur (chain level lane : Nat) : EmittedExpr :=
  if level = 0 then chainLeaf chain lane
  else .var ((nodeDigestCols chain (level - 1)).getD lane 0)

def nodeLeft (chain level lane : Nat) : EmittedExpr :=
  eadd (chainCur chain level lane)
    (emul (pathBit chain level)
      (esub (pathSibling chain level lane) (chainCur chain level lane)))

def nodeRight (chain level lane : Nat) : EmittedExpr :=
  eadd (pathSibling chain level lane)
    (emul (pathBit chain level)
      (esub (chainCur chain level lane) (pathSibling chain level lane)))

def nodeInputs (chain level : Nat) : List EmittedExpr :=
  [.const FNN4] ++ (List.range ROOT_LANES).map (nodeLeft chain level) ++
    (List.range ROOT_LANES).map (nodeRight chain level)

def nodePlans : List State16Step :=
  (List.range 4).flatMap fun chain => (List.range DEPTH).flatMap fun level =>
    spongePlan (nodeStateBase chain level) (nodeInputs chain level)

/-! ## Algebraic teeth -/

def firstEq (left right : EmittedExpr) : VmConstraint2 :=
  .base (.boundary .first (esub left right))

def firstZero (body : EmittedExpr) : VmConstraint2 := .base (.boundary .first body)

def openingU16Cols : List Nat :=
  (List.range 4).flatMap fun opening => cols (opening * OPENING_LANES) OPENING_LANES

def u16Cols : List Nat :=
  openingU16Cols ++ cols SECRET_BASE KEY_LANES ++ cols NULLIFIER_BASE KEY_LANES ++
    cols PRE_COUNT_BASE U64_LANES ++ cols POST_COUNT_BASE U64_LANES ++
    cols HISTORICAL_HEIGHT_BASE U64_LANES ++ cols LOW_ADDR_BASE KEY_LANES ++
    cols LOW_NEXT_BASE KEY_LANES ++ [LEX_LOW_AUX_BASE + 16, LEX_NEXT_AUX_BASE + 16]

def u15Cols : List Nat := cols NULLIFIER_HIGH_BASE KEY_LANES

def rangeConstraints : List VmConstraint2 :=
  (u16Cols.map fun col => rangeLookup ⟨col, 16⟩) ++
    (u15Cols.map fun col => rangeLookup ⟨col, 15⟩)

def bitBody' (col : Nat) : EmittedExpr :=
  emul (.var col) (esub (.var col) (.const 1))

def bitCols : List Nat := cols LOW_POS_BITS DEPTH ++ cols APP_POS_BITS DEPTH ++
  cols LEX_LOW_AUX_BASE 16 ++ cols LEX_NEXT_AUX_BASE 16 ++ cols COUNT_CARRY_BASE 3

def bitConstraints : List VmConstraint2 := bitCols.map fun col => firstZero (bitBody' col)

def marketSwapConstraints : List VmConstraint2 :=
  ((List.range U64_LANES).map fun lane =>
    firstEq (.var (openingValueBase OUTPUT0_BASE + lane))
      (.var (openingValueBase COUNTER_BASE + lane))) ++
  ((List.range U64_LANES).map fun lane =>
    firstEq (.var (openingAssetBase OUTPUT0_BASE + lane))
      (.var (openingAssetBase COUNTER_BASE + lane))) ++
  ((List.range U64_LANES).map fun lane =>
    firstEq (.var (openingOwnerBase OUTPUT0_BASE + lane))
      (.var (openingOwnerBase SELECTED_BASE + lane))) ++
  ((List.range U64_LANES).map fun lane =>
    firstEq (.var (openingValueBase OUTPUT1_BASE + lane))
      (.var (openingValueBase SELECTED_BASE + lane))) ++
  ((List.range U64_LANES).map fun lane =>
    firstEq (.var (openingAssetBase OUTPUT1_BASE + lane))
      (.var (openingAssetBase SELECTED_BASE + lane))) ++
  ((List.range U64_LANES).map fun lane =>
    firstEq (.var (openingOwnerBase OUTPUT1_BASE + lane))
      (.var (openingOwnerBase COUNTER_BASE + lane)))

def nullifierBindingConstraints : List VmConstraint2 :=
  (List.range KEY_LANES).map fun lane =>
    let source := if lane < ROOT_LANES then NULLIFIER0_DIGEST.getD lane 0
      else NULLIFIER1_DIGEST.getD (lane - ROOT_LANES) 0
    firstZero (esub (.var source)
      (eadd (.var (NULLIFIER_BASE + lane))
        (emul (.const U16) (.var (NULLIFIER_HIGH_BASE + lane)))))

def wideBindingConstraints : List VmConstraint2 :=
  (List.range WIDE_LANES).map fun lane =>
    let source := if lane < ROOT_LANES then WIDE0_DIGEST.getD lane 0
      else WIDE1_DIGEST.getD (lane - ROOT_LANES) 0
    firstEq (.var (BINDING_BASE + lane)) (.var source)

def outputCommitConstraints : List VmConstraint2 :=
  (List.range WIDE_LANES).flatMap fun lane =>
    let out0 := if lane < ROOT_LANES then OUTPUT0_COMMIT0.getD lane 0
      else OUTPUT0_COMMIT1.getD (lane - ROOT_LANES) 0
    let out1 := if lane < ROOT_LANES then OUTPUT1_COMMIT0.getD lane 0
      else OUTPUT1_COMMIT1.getD (lane - ROOT_LANES) 0
    [firstEq (.var (OUTPUT0_COMMIT_BASE + lane)) (.var out0),
     firstEq (.var (OUTPUT1_COMMIT_BASE + lane)) (.var out1)]

def digestCopyConstraints : List VmConstraint2 :=
  (List.range ROOT_LANES).flatMap fun lane =>
    [firstEq (.var (OUTPUT_ROOT_BASE + lane)) (.var (OUTPUT_ROOT_DIGEST.getD lane 0)),
     firstEq (.var (PRE_STATE_COPY + lane)) (.var (PRE_STATE_DIGEST.getD lane 0)),
     firstEq (.var (POST_STATE_COPY + lane)) (.var (POST_STATE_DIGEST.getD lane 0)),
     firstEq (.var (CONSEQUENCE_BASE + lane)) (.var (CONSEQUENCE_REAL_DIGEST.getD lane 0))]

def selectorSum (base : Nat) : EmittedExpr :=
  sumExpr ((List.range KEY_LANES).map fun i => .var (base + i))

def selectorPrefix (base k : Nat) : EmittedExpr :=
  sumExpr ((List.range (k + 1)).map fun i => .var (base + i))

def selectedDifference (left right : Nat → EmittedExpr) (base : Nat) : EmittedExpr :=
  sumExpr ((List.range KEY_LANES).map fun i =>
    emul (.var (base + i)) (esub (right i) (left i)))

def lexBodies (left right : Nat → EmittedExpr) (base : Nat) : List EmittedExpr :=
  [esub (selectorSum base) (.const 1)] ++
  ((List.range 15).map fun i =>
    emul (oneMinus (selectorPrefix base i)) (esub (left i) (right i))) ++
  [esub (esub (selectedDifference left right base) (.const 1)) (.var (base + 16))]

def lowReal : EmittedExpr := .var LOW_ADDR_TAG
def nextReal : EmittedExpr := esub (.const 2) (.var LOW_NEXT_TAG)
def unitKey (i : Nat) : EmittedExpr := if i = 0 then .const 1 else .const 0
def lowLeft (i : Nat) : EmittedExpr := emul lowReal (.var (LOW_ADDR_BASE + i))
def lowRight (i : Nat) : EmittedExpr :=
  eadd (emul lowReal (.var (NULLIFIER_BASE + i)))
    (emul (oneMinus lowReal) (unitKey i))
def nextLeft (i : Nat) : EmittedExpr := emul nextReal (.var (NULLIFIER_BASE + i))
def nextRight (i : Nat) : EmittedExpr :=
  eadd (emul nextReal (.var (LOW_NEXT_BASE + i)))
    (emul (oneMinus nextReal) (unitKey i))

def bracketConstraints : List VmConstraint2 :=
  (lexBodies lowLeft lowRight LEX_LOW_AUX_BASE ++
    lexBodies nextLeft nextRight LEX_NEXT_AUX_BASE).map firstZero

def tagConstraints : List VmConstraint2 :=
  [firstZero (emul (.var LOW_ADDR_TAG) (esub (.var LOW_ADDR_TAG) (.const 1))),
   firstZero (emul (esub (.var LOW_NEXT_TAG) (.const 1))
     (esub (.var LOW_NEXT_TAG) (.const 2)))] ++
  ((List.range KEY_LANES).map fun lane => firstZero
    (emul (oneMinus (.var LOW_ADDR_TAG)) (.var (LOW_ADDR_BASE + lane)))) ++
  ((List.range KEY_LANES).map fun lane => firstZero
    (emul (esub (.var LOW_NEXT_TAG) (.const 1)) (.var (LOW_NEXT_BASE + lane))))

def appendPositionConstraints : List VmConstraint2 :=
  [ firstZero (esub (.var PRE_COUNT_BASE)
      (sumExpr ((List.range 16).map fun i =>
        emul (.const (2 ^ i)) (.var (APP_POS_BITS + i)))))
  , firstZero (esub (.var (PRE_COUNT_BASE + 1))
      (sumExpr ((List.range 16).map fun i =>
        emul (.const (2 ^ i)) (.var (APP_POS_BITS + 16 + i)))))
  , firstZero (.var (PRE_COUNT_BASE + 2))
  , firstZero (.var (PRE_COUNT_BASE + 3)) ]

def countIncrementConstraints : List VmConstraint2 :=
  [ firstZero
      (eadd (esub (esub (.var POST_COUNT_BASE) (.var PRE_COUNT_BASE)) (.const 1))
        (emul (.const U16) (.var COUNT_CARRY_BASE)))
  , firstZero
      (eadd (esub (esub (.var (POST_COUNT_BASE + 1)) (.var (PRE_COUNT_BASE + 1)))
        (.var COUNT_CARRY_BASE))
        (emul (.const U16) (.var (COUNT_CARRY_BASE + 1))))
  , firstZero
      (eadd (esub (esub (.var (POST_COUNT_BASE + 2)) (.var (PRE_COUNT_BASE + 2)))
        (.var (COUNT_CARRY_BASE + 1)))
        (emul (.const U16) (.var (COUNT_CARRY_BASE + 2))))
  , firstZero
      (esub (esub (.var (POST_COUNT_BASE + 3)) (.var (PRE_COUNT_BASE + 3)))
        (.var (COUNT_CARRY_BASE + 2))) ]

def rootConstraints : List VmConstraint2 :=
  ((List.range ROOT_LANES).flatMap fun lane =>
    [ firstEq (.var ((nodeDigestCols 0 (DEPTH - 1)).getD lane 0))
        (.var (PRIOR_ROOT_BASE + lane))
    , firstEq (.var ((nodeDigestCols 1 (DEPTH - 1)).getD lane 0))
        (.var ((nodeDigestCols 2 (DEPTH - 1)).getD lane 0))
    , firstEq (.var ((nodeDigestCols 3 (DEPTH - 1)).getD lane 0))
        (.var (SUCCESSOR_ROOT_BASE + lane)) ])

/-! ## Fixed 100-lane ABI -/

def publicPins : List VmConstraint2 :=
  ((List.range 4).map fun lane => .base (.piBinding .first (HISTORICAL_HEIGHT_BASE + lane) lane)) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (HISTORICAL_ROOT_BASE + lane) (4 + lane))) ++
  ((List.range 16).map fun lane => .base (.piBinding .first (NULLIFIER_BASE + lane) (12 + lane))) ++
  ((List.range 16).map fun lane => .base (.piBinding .first (BINDING_BASE + lane) (28 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (SUCCESSOR_ROOT_BASE + lane) (44 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (PRIOR_ROOT_BASE + lane) (52 + lane))) ++
  ((List.range 4).map fun lane => .base (.piBinding .first (PRE_COUNT_BASE + lane) (60 + lane))) ++
  ((List.range 4).map fun lane => .base (.piBinding .first (POST_COUNT_BASE + lane) (64 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (CONSEQUENCE_BASE + lane) (68 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (OUTPUT_ROOT_BASE + lane) (76 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (BEFORE_OUTER_BASE + lane) (84 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (AFTER_OUTER_BASE + lane) (92 + lane)))

def spongePlans : List State16Step :=
  spongePlan NULLIFIER0_STATE (nullifierTranscript NULLIFIER_FORK0) ++
  spongePlan NULLIFIER1_STATE (nullifierTranscript NULLIFIER_FORK1) ++
  spongePlan WIDE0_STATE (wideTranscript 0) ++ spongePlan WIDE1_STATE (wideTranscript 1) ++
  spongePlan LOW_OLD_LEAF_STATE lowOldLeafPreimage ++
  spongePlan LOW_NEW_LEAF_STATE lowNewLeafPreimage ++
  spongePlan APPENDED_LEAF_STATE appendedLeafPreimage ++
  spongePlan OUTPUT0_NOTE0_STATE (noteTranscript NOTE_FORK0 OUTPUT0_BASE) ++
  spongePlan OUTPUT0_NOTE1_STATE (noteTranscript NOTE_FORK1 OUTPUT0_BASE) ++
  spongePlan OUTPUT1_NOTE0_STATE (noteTranscript NOTE_FORK0 OUTPUT1_BASE) ++
  spongePlan OUTPUT1_NOTE1_STATE (noteTranscript NOTE_FORK1 OUTPUT1_BASE) ++
  spongePlan OUTPUT_ROOT_STATE outputRootPreimage ++
  spongePlan PRE_STATE_COMMIT_STATE (statePreimage PRIOR_ROOT_BASE PRE_COUNT_BASE) ++
  spongePlan POST_STATE_COMMIT_STATE (statePreimage SUCCESSOR_ROOT_BASE POST_COUNT_BASE) ++
  spongePlan CONSEQUENCE_REAL_STATE consequenceRealPreimage ++ nodePlans

def state16Lookups : List VmConstraint2 := spongePlans.map fun step =>
  .lookup ⟨poseidon2state16, chipLookupTupleState16 step.input step.outputCols⟩

def semanticConstraints : List VmConstraint2 :=
  marketSwapConstraints ++ nullifierBindingConstraints ++ wideBindingConstraints ++
    outputCommitConstraints ++ digestCopyConstraints ++ bitConstraints ++ tagConstraints ++
    bracketConstraints ++ appendPositionConstraints ++ countIncrementConstraints ++ rootConstraints

def shieldedExactApexV4Descriptor : EffectVmDescriptor2 :=
  { name := "shielded-exact-apex-v4::one-opening-whole-note-swap-aafi32-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := 100
  , tables := [mainTableDef TRACE_WIDTH, poseidon2State16ChipTableDef,
      rangeTable 15, rangeTable 16]
  , constraints := state16Lookups ++ rangeConstraints ++ semanticConstraints ++ publicPins
  , hashSites := []
  , ranges := [] }

def descriptorJson : String := emitVmJson2 shieldedExactApexV4Descriptor

#guard publicPins.length == 100
#guard shieldedExactApexV4Descriptor.piCount == 100
#guard shieldedExactApexV4Descriptor.traceWidth == TRACE_WIDTH
#guard descriptorJson.startsWith
  "{\"name\":\"shielded-exact-apex-v4::one-opening-whole-note-swap-aafi32-v1\",\"ir\":2"
#guard !(descriptorJson.contains "legacy_value_binding")

/-! ## Structural emitted-relation facts -/

theorem public_pin_mem {pin : VmConstraint2} (h : pin ∈ publicPins) :
    pin ∈ shieldedExactApexV4Descriptor.constraints := by
  simp [shieldedExactApexV4Descriptor, h]

theorem semantic_mem {constraint : VmConstraint2} (h : constraint ∈ semanticConstraints) :
    constraint ∈ shieldedExactApexV4Descriptor.constraints := by
  simp [shieldedExactApexV4Descriptor, h]

end Dregg2.Circuit.Emit.ShieldedExactApexV4Descriptor
