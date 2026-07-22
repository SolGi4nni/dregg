/-
# Dregg2.Games.DescentCensusDescriptor

Lean-authored custom relation for the Descent relic-custody census.  It opens the eight fixed
custody leaves (external keys 16..23) against the cell's native-eight `fields_root`, then publishes
the exact counts of custody codes `[carried=8, banked=9, floor1=1, floor2=2, floor3=3, floor4=4]`.

The path is deliberately a dedicated custom VK, not a SlotCaveat claim: SlotCaveat only sees the
fixed `fields[0..8]` projection and cannot authenticate overflow-map values.  Here every leaf uses
the deployed arity-3 IMT digest `(field_key_hash(key), fold_bytes32(value), next_addr)` and every
level uses the deployed native-eight Poseidon2 node digest.  Eight paths run in parallel over the
16-row main trace, staying below the 1024-column compiler limit.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Games.DescentCensusDescriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2

set_option autoImplicit false

def RELICS : Nat := 8
def DEPTH : Nat := 16
def ZONES : Nat := 6
def DIGEST : Nat := 8

/-! Public ABI: `[old8 || new8 || post_fields_root8 || six_counts]`. -/
def PI_OLD : Nat := 0
def PI_NEW : Nat := 8
def PI_FIELDS_ROOT : Nat := 16
def PI_COUNTS : Nat := 24
def PI_COUNT : Nat := 30

/-! The exact field-address image and sorted-IMT successor for keys 16..23 in a Descent cell.
The successor constants include the reserved refusal-audit leaf.  They pin these openings to the
real schema leaves, rather than allowing the prover to choose eight convenient map positions. -/
def relicAddr : Fin RELICS → Int
  | ⟨0, _⟩ => 1903373793
  | ⟨1, _⟩ => 206503848
  | ⟨2, _⟩ => 186807208
  | ⟨3, _⟩ => 1229116775
  | ⟨4, _⟩ => 1194514939
  | ⟨5, _⟩ => 1456787871
  | ⟨6, _⟩ => 1049436545
  | ⟨7, _⟩ => 14058645

def relicNextAddr : Fin RELICS → Int
  | ⟨0, _⟩ => 2013265920
  | ⟨1, _⟩ => 529176517
  | ⟨2, _⟩ => 206503848
  | ⟨3, _⟩ => 1456787871
  | ⟨4, _⟩ => 1229116775
  | ⟨5, _⟩ => 1903373793
  | ⟨6, _⟩ => 1194514939
  | ⟨7, _⟩ => 186807208

def zoneCode : Fin ZONES → Int
  | ⟨0, _⟩ => 8
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 4

/-! ## Column geometry -/

def STATE_BASE : Nat := 0
def STATE_SPAN : Nat := 16
def PATH_BASE : Nat := STATE_BASE + STATE_SPAN

/-- Per-relic column span:
`raw(1), value_hash8, leaf8, cur8, sibling8, left8, right8, parent8, dir(1), eq6, inv6`. -/
def PATH_SPAN : Nat := 70
def pathBase (r : Fin RELICS) : Nat := PATH_BASE + r.val * PATH_SPAN
def rawCol (r : Fin RELICS) : Nat := pathBase r
def valueHashCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := pathBase r + 1 + i.val
def valueHashHead (r : Fin RELICS) : Nat := pathBase r + 1
def leafCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := pathBase r + 9 + i.val
def curCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := pathBase r + 17 + i.val
def siblingCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := pathBase r + 25 + i.val
def leftCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := pathBase r + 33 + i.val
def rightCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := pathBase r + 41 + i.val
def parentCol (r : Fin RELICS) (i : Fin DIGEST) : Nat := pathBase r + 49 + i.val
def dirCol (r : Fin RELICS) : Nat := pathBase r + 57
def eqCol (r : Fin RELICS) (z : Fin ZONES) : Nat := pathBase r + 58 + z.val
def invCol (r : Fin RELICS) (z : Fin ZONES) : Nat := pathBase r + 64 + z.val

def COUNT_COL_BASE : Nat := PATH_BASE + RELICS * PATH_SPAN
def countCol (z : Fin ZONES) : Nat := COUNT_COL_BASE + z.val
def TRACE_WIDTH : Nat := COUNT_COL_BASE + ZONES

#guard PATH_SPAN == 70
#guard TRACE_WIDTH == 582
#guard TRACE_WIDTH < 1024

/-! ## Expression helpers and row-local constraints -/

def ev (c : Nat) : EmittedExpr := .var c
def ek (x : Int) : EmittedExpr := .const x
def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
def emul (a b : EmittedExpr) : EmittedExpr := .mul a b
def eneg (a : EmittedExpr) : EmittedExpr := emul (ek (-1)) a
def esub (a b : EmittedExpr) : EmittedExpr := eadd a (eneg b)

def digestCols (f : Fin DIGEST → Nat) : List Nat := List.ofFn f
def digestExprs (f : Fin DIGEST → Nat) : List EmittedExpr := (digestCols f).map ev

/-- `field_from_u64(code)` puts a one-byte custody code at byte 31; the deployed byte-fold
encodes 4-byte chunks little-endian, hence the eighth chip input is `code * 2^24`. -/
def encodedCustodyInputs (r : Fin RELICS) : List EmittedExpr :=
  [ek 0, ek 0, ek 0, ek 0, ek 0, ek 0, ek 0, emul (ek 16777216) (ev (rawCol r))]

def valueHashLookup (r : Fin RELICS) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTupleN (encodedCustodyInputs r) (digestCols (valueHashCol r)) }

def leafLookup (r : Fin RELICS) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTupleN
      [ek (relicAddr r), ev (valueHashHead r), ek (relicNextAddr r)]
      (digestCols (leafCol r)) }

def nodeLookup (r : Fin RELICS) : Lookup :=
  { table := .poseidon2
  , tuple := chipLookupTupleN
      (digestExprs (leftCol r) ++ digestExprs (rightCol r))
      (digestCols (parentCol r)) }

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

def eqDiff (r : Fin RELICS) (z : Fin ZONES) : EmittedExpr :=
  esub (ev (rawCol r)) (ek (zoneCode z))

def eqZero (r : Fin RELICS) (z : Fin ZONES) : EmittedExpr :=
  emul (eqDiff r z) (ev (eqCol r z))

def eqInverse (r : Fin RELICS) (z : Fin ZONES) : EmittedExpr :=
  esub (emul (eqDiff r z) (ev (invCol r z)))
    (esub (ek 1) (ev (eqCol r z)))

def eqBinary (r : Fin RELICS) (z : Fin ZONES) : EmittedExpr :=
  emul (ev (eqCol r z)) (esub (ev (eqCol r z)) (ek 1))

/-- Every authenticated relic has exactly one legal custody zone.  Without this gate a canonical
but out-of-vocabulary code (0/5/6/7/...) makes all six equality indicators zero and disappears
from the published census. -/
def zoneOneHot (r : Fin RELICS) : EmittedExpr :=
  esub ((List.finRange ZONES).foldr (fun z acc => eadd (ev (eqCol r z)) acc) (ek 0)) (ek 1)

def perPathConstraints (r : Fin RELICS) : List VmConstraint2 :=
  [ .lookup (valueHashLookup r)
  , .lookup (leafLookup r)
  , .lookup (nodeLookup r)
  , .base (.gate (dirBinary r))
  , .base (.gate (zoneOneHot r)) ] ++
  (List.finRange DIGEST).flatMap (fun i =>
    [.base (.gate (leftSelect r i)), .base (.gate (rightSelect r i))]) ++
  (List.finRange ZONES).flatMap (fun z =>
    [.base (.gate (eqZero r z)), .base (.gate (eqInverse r z)),
      .base (.gate (eqBinary r z))]) ++
  (List.finRange DIGEST).map (fun i =>
    .windowGate ⟨.add (.nxt (curCol r i)) (.mul (.const (-1)) (.loc (parentCol r i))), true⟩) ++
  (List.finRange DIGEST).map (fun i =>
    .base (.boundary .first (esub (ev (curCol r i)) (ev (leafCol r i))))) ++
  (List.finRange DIGEST).map (fun i =>
    .base (.piBinding .last (parentCol r i) (PI_FIELDS_ROOT + i.val)))

def censusSum (z : Fin ZONES) : EmittedExpr :=
  (List.finRange RELICS).foldr (fun r acc => eadd (ev (eqCol r z)) acc) (ek 0)

def countConstraints : List VmConstraint2 :=
  (List.finRange ZONES).flatMap (fun z =>
    [ .base (.boundary .first (esub (ev (countCol z)) (censusSum z)))
    , .base (.piBinding .first (countCol z) (PI_COUNTS + z.val)) ])

def statePins : List VmConstraint2 :=
  (List.range STATE_SPAN).map (fun i => .base (.piBinding .first i i))

def descentCensusDescriptor : EffectVmDescriptor2 :=
  { name := "dregg-descent-custody-census-fixed8-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := [poseidon2ChipTableDef]
  , constraints := statePins ++
      (List.finRange RELICS).flatMap perPathConstraints ++ countConstraints
  , hashSites := []
  , ranges := [] }

def descriptorJson : String := emitVmJson2 descentCensusDescriptor

/-! Structural regression teeth: eight real openings, three wide lookups per path, six public
counts, and no host-only `mapOp` masquerading as authenticated membership. -/
#guard descentCensusDescriptor.traceWidth == 582
#guard descentCensusDescriptor.piCount == 30
#guard ((descentCensusDescriptor.constraints.filter fun c =>
  match c with | .lookup _ => true | _ => false).length) == RELICS * 3
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
