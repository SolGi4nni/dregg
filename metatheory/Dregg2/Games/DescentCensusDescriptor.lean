/-
# Dregg2.Games.DescentCensusDescriptor

Lean-authored custom relation for the Descent fixed-eight relic-custody census.  It opens the
eight exact overflow-field leaves at raw keys 16..23 against the cell's native-eight V2
`fields_root`, then publishes the exact counts of custody codes
`[carried=8, banked=9, floor1=1, floor2=2, floor3=3, floor4=4]`.

This descriptor speaks the same flag-day exact schema as Rust `openable_fields_root`:

* leaf: `FLD2 || occupancy || key_u16_le[4] || value_u16_le[16]`;
* node: `FLN2 || left8 || right8`;
* both are the deployed rate-four `hash_many_8` sponge, lowered through the full state16 bus.

In particular, no key or value is reduced modulo BabyBear before it reaches the sponge.  The
previous single-felt value fold admitted concrete `+p` aliases and was not an authority boundary.
Every custody value is instead forced byte-for-byte to canonical `field_from_u64(zone)` before its
exact leaf digest is recomposed to the public root.
-/
import Dregg2.Circuit.FullStateChip

namespace Dregg2.Games.DescentCensusDescriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2

set_option autoImplicit false

def RELICS : Nat := 8
def DEPTH : Nat := 16
def ZONES : Nat := 6
def DIGEST : Nat := 8
def STATE_LANES : Nat := 16
def KEY_LIMBS : Nat := 4
def VALUE_LIMBS : Nat := 16

/-! Public ABI: `[old8 || new8 || post_fields_root8 || six_counts]`. -/
def PI_OLD : Nat := 0
def PI_NEW : Nat := 8
def PI_FIELDS_ROOT : Nat := 16
def PI_COUNTS : Nat := 24
def PI_COUNT : Nat := 30

/-! Exact V2 fields-root domains.  These are ASCII `FLD2` and `FLN2`. -/
def FLD2 : Int := 0x464c4432
def FLN2 : Int := 0x464c4e32

def relicKey : Fin RELICS → Int
  | ⟨0, _⟩ => 16
  | ⟨1, _⟩ => 17
  | ⟨2, _⟩ => 18
  | ⟨3, _⟩ => 19
  | ⟨4, _⟩ => 20
  | ⟨5, _⟩ => 21
  | ⟨6, _⟩ => 22
  | ⟨7, _⟩ => 23

def zoneCode : Fin ZONES → Int
  | ⟨0, _⟩ => 8
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 4

/-! ## Column geometry

Each row is one Merkle level.  Eight paths run in parallel.  Leaf states are constant down the
trace; node states vary with the level.  A 22-felt leaf takes six absorbs plus one squeeze, and a
17-felt node takes five absorbs plus one squeeze.
-/

def STATE_BASE : Nat := 0
def STATE_SPAN : Nat := 16
def PATH_BASE : Nat := STATE_BASE + STATE_SPAN
def LEAF_STATE_STEPS : Nat := 7
def NODE_STATE_STEPS : Nat := 6

/-- `key4, value16, leaf_state112, cur8, sibling8, left8, right8,
node_state96, dir1, eq6, inv6`. -/
def PATH_SPAN : Nat := 273
def pathBase (r : Fin RELICS) : Nat := PATH_BASE + r.val * PATH_SPAN
def keyBase (r : Fin RELICS) : Nat := pathBase r
def keyCol (r : Fin RELICS) (i : Fin KEY_LIMBS) : Nat := keyBase r + i.val
def valueBase (r : Fin RELICS) : Nat := keyBase r + KEY_LIMBS
def valueCol (r : Fin RELICS) (i : Fin VALUE_LIMBS) : Nat := valueBase r + i.val
def leafStateBase (r : Fin RELICS) : Nat := valueBase r + VALUE_LIMBS
def curBase (r : Fin RELICS) : Nat := leafStateBase r + STATE_LANES * LEAF_STATE_STEPS
def curCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := curBase r + i.val
def siblingBase (r : Fin RELICS) : Nat := curBase r + DIGEST
def siblingCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := siblingBase r + i.val
def leftBase (r : Fin RELICS) : Nat := siblingBase r + DIGEST
def leftCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := leftBase r + i.val
def rightBase (r : Fin RELICS) : Nat := leftBase r + DIGEST
def rightCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := rightBase r + i.val
def nodeStateBase (r : Fin RELICS) : Nat := rightBase r + DIGEST
def dirCol (r : Fin RELICS) : Nat := nodeStateBase r + STATE_LANES * NODE_STATE_STEPS
def eqCol (r : Fin RELICS) (z : Fin ZONES) : Nat := dirCol r + 1 + z.val
def invCol (r : Fin RELICS) (z : Fin ZONES) : Nat := dirCol r + 1 + ZONES + z.val

def COUNT_COL_BASE : Nat := PATH_BASE + RELICS * PATH_SPAN
def countCol (z : Fin ZONES) : Nat := COUNT_COL_BASE + z.val
def TRACE_WIDTH : Nat := COUNT_COL_BASE + ZONES

#guard PATH_SPAN == 273
#guard TRACE_WIDTH == 2206
#guard curBase ⟨0, by decide⟩ == 148
#guard nodeStateBase ⟨0, by decide⟩ == 180
#guard dirCol ⟨0, by decide⟩ == 276

/-! ## Expression and exact-sponge helpers -/

def ev (c : Nat) : EmittedExpr := .var c
def ek (x : Int) : EmittedExpr := .const x
def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
def emul (a b : EmittedExpr) : EmittedExpr := .mul a b
def eneg (a : EmittedExpr) : EmittedExpr := emul (ek (-1)) a
def esub (a b : EmittedExpr) : EmittedExpr := eadd a (eneg b)

def cols (base count : Nat) : List Nat := (List.range count).map (base + ·)
def vars (base count : Nat) : List EmittedExpr := (cols base count).map .var
def stateCols (base step : Nat) : List Nat := cols (base + STATE_LANES * step) STATE_LANES
def chunks4 {α : Type} (xs : List α) : List (List α) := xs.toChunks 4

def initialStateExpr (inputLength : Nat) : List EmittedExpr :=
  (List.range STATE_LANES).map fun i => if i = 4 then .const inputLength else .const 0

def padChunk (chunk : List EmittedExpr) : List EmittedExpr :=
  chunk ++ List.replicate (4 - chunk.length) (.const 0)

def priorStateExpr (stateBase stage : Nat) : List EmittedExpr :=
  if stage = 0 then [] else (stateCols stateBase (stage - 1)).map .var

def absorbInputExpr (stateBase inputLength stage : Nat) (chunk : List EmittedExpr) :
    List EmittedExpr :=
  let prior := if stage = 0 then initialStateExpr inputLength else priorStateExpr stateBase stage
  let rate := padChunk chunk
  (List.range STATE_LANES).map fun i =>
    if i < 4 then eadd (prior.getD i (.const 0)) (rate.getD i (.const 0))
    else prior.getD i (.const 0)

structure State16Step where
  input : List EmittedExpr
  outputCols : List Nat
  deriving Repr

/-- Exact live `hash_many_8`: absorb-permute each rate-four chunk, then one final permutation. -/
def spongePlan (stateBase : Nat) (preimage : List EmittedExpr) : List State16Step :=
  let chunks := chunks4 preimage
  let absorb := chunks.mapIdx fun stage chunk =>
    ⟨absorbInputExpr stateBase preimage.length stage chunk, stateCols stateBase stage⟩
  let squeeze :=
    ⟨(stateCols stateBase (chunks.length - 1)).map .var, stateCols stateBase chunks.length⟩
  absorb ++ [squeeze]

def spongeSteps (inputLength : Nat) : Nat := (inputLength + 3) / 4 + 1

/-- Digest lanes are absorb-state lanes 0..3 followed by final-squeeze lanes 0..3. -/
def spongeDigestCols (stateBase inputLength : Nat) : List Nat :=
  let absorbs := (inputLength + 3) / 4
  cols (stateBase + STATE_LANES * (absorbs - 1)) 4 ++
    cols (stateBase + STATE_LANES * absorbs) 4

def leafPreimage (r : Fin RELICS) : List EmittedExpr :=
  [ek FLD2, ek 1] ++ vars (keyBase r) KEY_LIMBS ++ vars (valueBase r) VALUE_LIMBS

def leafDigestCols (r : Fin RELICS) : List Nat :=
  spongeDigestCols (leafStateBase r) (leafPreimage r).length

def nodePreimage (r : Fin RELICS) : List EmittedExpr :=
  ek FLN2 :: (vars (leftBase r) DIGEST ++ vars (rightBase r) DIGEST)

def nodeDigestCols (r : Fin RELICS) : List Nat :=
  spongeDigestCols (nodeStateBase r) (nodePreimage r).length

#guard (leafPreimage ⟨0, by decide⟩).length == 22
#guard (nodePreimage ⟨0, by decide⟩).length == 17
#guard spongeSteps 22 == LEAF_STATE_STEPS
#guard spongeSteps 17 == NODE_STATE_STEPS
#guard (leafDigestCols ⟨0, by decide⟩).length == DIGEST
#guard (nodeDigestCols ⟨0, by decide⟩).length == DIGEST

/-! ## Exact custody, path, and census constraints -/

def keyLimbExpected (r : Fin RELICS) (i : Fin KEY_LIMBS) : Int :=
  if i.val = 0 then relicKey r else 0

/-- `field_from_u64(zone)` is a 32-byte big-endian integer, then the exact leaf converts adjacent
bytes to little-endian u16 limbs.  For the six byte-sized codes this is therefore zero in limbs
0..14 and `256 * zone` in limb 15. -/
def valueLimbExpected (z : Fin ZONES) (i : Fin VALUE_LIMBS) : Int :=
  if i.val = 15 then 256 * zoneCode z else 0

def eqDiff (r : Fin RELICS) (z : Fin ZONES) : EmittedExpr :=
  esub (ev (valueCol r ⟨15, by decide⟩)) (ek (valueLimbExpected z ⟨15, by decide⟩))

def eqZero (r : Fin RELICS) (z : Fin ZONES) : EmittedExpr :=
  emul (eqDiff r z) (ev (eqCol r z))

def eqInverse (r : Fin RELICS) (z : Fin ZONES) : EmittedExpr :=
  esub (emul (eqDiff r z) (ev (invCol r z)))
    (esub (ek 1) (ev (eqCol r z)))

def eqBinary (r : Fin RELICS) (z : Fin ZONES) : EmittedExpr :=
  emul (ev (eqCol r z)) (esub (ev (eqCol r z)) (ek 1))

def zoneOneHot (r : Fin RELICS) : EmittedExpr :=
  esub ((List.finRange ZONES).foldr (fun z acc => eadd (ev (eqCol r z)) acc) (ek 0)) (ek 1)

def selectedValueLimb (r : Fin RELICS) (i : Fin VALUE_LIMBS) : EmittedExpr :=
  (List.finRange ZONES).foldr
    (fun z acc => eadd (emul (ev (eqCol r z)) (ek (valueLimbExpected z i))) acc) (ek 0)

def valueLimbGate (r : Fin RELICS) (i : Fin VALUE_LIMBS) : EmittedExpr :=
  esub (ev (valueCol r i)) (selectedValueLimb r i)

def dirBinary (r : Fin RELICS) : EmittedExpr :=
  emul (ev (dirCol r)) (esub (ev (dirCol r)) (ek 1))

def leftSelect (r : Fin RELICS) (i : Fin DIGEST) : EmittedExpr :=
  esub (ev (leftCol r i))
    (eadd (ev (curCol r i))
      (emul (ev (dirCol r)) (esub (ev (siblingCol r i)) (ev (curCol r i)))))

def rightSelect (r : Fin RELICS) (i : Fin DIGEST) : EmittedExpr :=
  esub (ev (rightCol r i))
    (eadd (ev (siblingCol r i))
      (emul (ev (dirCol r)) (esub (ev (curCol r i)) (ev (siblingCol r i)))))

def state16Lookups (r : Fin RELICS) : List VmConstraint2 :=
  (spongePlan (leafStateBase r) (leafPreimage r) ++
    spongePlan (nodeStateBase r) (nodePreimage r)).map fun step =>
      .lookup ⟨poseidon2state16, chipLookupTupleState16 step.input step.outputCols⟩

def perPathConstraints (r : Fin RELICS) : List VmConstraint2 :=
  state16Lookups r ++
  (List.finRange KEY_LIMBS).map (fun i =>
    .base (.gate (esub (ev (keyCol r i)) (ek (keyLimbExpected r i))))) ++
  [ .base (.gate (dirBinary r))
  , .base (.gate (zoneOneHot r)) ] ++
  (List.finRange VALUE_LIMBS).map (fun i => .base (.gate (valueLimbGate r i))) ++
  (List.finRange DIGEST).flatMap (fun i =>
    [.base (.gate (leftSelect r i)), .base (.gate (rightSelect r i))]) ++
  (List.finRange ZONES).flatMap (fun z =>
    [.base (.gate (eqZero r z)), .base (.gate (eqInverse r z)),
      .base (.gate (eqBinary r z))]) ++
  (List.finRange DIGEST).map (fun i =>
    .windowGate ⟨.add (.nxt (curCol r i))
      (.mul (.const (-1)) (.loc ((nodeDigestCols r).getD i.val 0))), true⟩) ++
  (List.finRange DIGEST).map (fun i =>
    .base (.boundary .first
      (esub (ev (curCol r i)) (ev ((leafDigestCols r).getD i.val 0))))) ++
  (List.finRange DIGEST).map (fun i =>
    .base (.piBinding .last ((nodeDigestCols r).getD i.val 0) (PI_FIELDS_ROOT + i.val)))

def censusSum (z : Fin ZONES) : EmittedExpr :=
  (List.finRange RELICS).foldr (fun r acc => eadd (ev (eqCol r z)) acc) (ek 0)

def countConstraints : List VmConstraint2 :=
  (List.finRange ZONES).flatMap (fun z =>
    [ .base (.boundary .first (esub (ev (countCol z)) (censusSum z)))
    , .base (.piBinding .first (countCol z) (PI_COUNTS + z.val)) ])

def statePins : List VmConstraint2 :=
  (List.range STATE_SPAN).map (fun i => .base (.piBinding .first i i))

def descentCensusDescriptor : EffectVmDescriptor2 :=
  { name := "dregg-descent-custody-census-fixed8-v2"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := [mainTableDef TRACE_WIDTH, poseidon2State16ChipTableDef]
  , constraints := statePins ++
      (List.finRange RELICS).flatMap perPathConstraints ++ countConstraints
  , hashSites := []
  , ranges := [] }

def descriptorJson : String := emitVmJson2 descentCensusDescriptor

/-! Structural regression teeth: eight exact openings, thirteen full-state permutations per path,
six public counts, and no host-only `mapOp` masquerading as authenticated membership. -/
#guard descentCensusDescriptor.traceWidth == 2206
#guard descentCensusDescriptor.piCount == 30
#guard ((descentCensusDescriptor.constraints.filter fun c =>
  match c with | .lookup l => l.table == poseidon2state16 | _ => false).length) == RELICS * 13
#guard ((descentCensusDescriptor.constraints.filter fun c =>
  match c with | .windowGate _ => true | _ => false).length) == RELICS * DIGEST
#guard ((descentCensusDescriptor.constraints.filter fun c =>
  match c with | .mapOp _ => true | _ => false).length) == 0

/-- The inverse-witness equality gadget has no false-positive indicator over the integers. -/
theorem eq_indicator_sound (x target eq inv : Int)
    (hzero : (x - target) * eq = 0)
    (hinv : (x - target) * inv = 1 - eq) :
    (eq = 1 ↔ x = target) := by
  constructor
  · intro heq
    rw [heq] at hzero
    omega
  · intro hxt
    subst x
    simp at hinv
    omega

#assert_axioms eq_indicator_sound

end Dregg2.Games.DescentCensusDescriptor
