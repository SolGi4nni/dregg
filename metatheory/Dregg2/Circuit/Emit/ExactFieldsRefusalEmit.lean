/-
# ExactFieldsRefusalEmit — exact FLD2/FLN2 refusal audit update

The deployed refusal changes the protocol-reserved overflow-field at raw key `2^32`.  This emitter
replaces the legacy scalar `mapOp` leaf with the exact fields-root V2 schema:

* leaf `FLD2 || occupancy || key_u16_le[4] || value_u16_le[16]`;
* node `FLN2 || left8 || right8`;
* the live rate-four `hash_many_8` schedule through the full state16 permutation bus;
* one shared sibling/direction path for the before leaf and its in-place after update;
* sixteen verifier-known audit limbs, bound as public inputs to the after leaf byte-for-byte.

The EffectVM trace is taller than the 16-level fields tree.  `active,count` define a forced monotone
prefix: first `(1,0)`, last `(0,16)`, `nextCount = count + active`, and active may never rise.  Thus
exactly rows 0..15 recompose the path; the falling edge pins both node digests to the committed
before/after fields-root groups.  State16 lookups remain unconditional, so inactive rows carry a
genuine repeated tuple rather than relying on a dummy table row.
-/
import Dregg2.Circuit.FullStateChip
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide

namespace Dregg2.Circuit.Emit.ExactFieldsRefusalEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3

set_option autoImplicit false

def DIGEST : Nat := 8
def STATE_LANES : Nat := 16
def VALUE_LIMBS : Nat := 16
def DEPTH : Nat := 16
def LEAF_STATE_STEPS : Nat := 7
def NODE_STATE_STEPS : Nat := 6

def FLD2 : Int := 0x464c4432
def FLN2 : Int := 0x464c4e32

/-! Column geometry; kept definitionally aligned with Rust `trace_rotated::REFUSAL_EXACT_*`. -/

/-- The exact-refusal appendix starts EXACTLY where the graduated rotated refusal host ends —
`refusalV3.traceWidth = (188 + APPENDIX_SPAN) + 7·(4 + |rotV3Appendix|)`. The literal is kept so the
whole column ladder below stays `rfl`-shaped, but the `#guard` under the ladder now WELDS it to that
host width: at the 178 → 184 ninth-lane flag day this moved 1647 → 1691 (`APPENDIX_SPAN` 521 → 537
and four more appendix sites, `+16 + 28 = +44`), and at the rc-FOLD flag day 1691 → 1707
(`APPENDIX_SPAN` 537 → 539 and two more appendix sites, `+2 + 14 = +16`), and at the FIELDS-CANONICITY
flag day 1707 → 1819 (`APPENDIX_SPAN` 539 → 651 — the 112 aux columns of
`Emit.FieldsCanonicity9Emit`; no new appendix site, so the graduation multiplier is unchanged). The
guard went RED rather than silent all three times — which is the whole reason the literal is allowed
to exist. -/
def BEFORE_BASE : Nat := 1819
def OCC_COL : Nat := BEFORE_BASE
def OLD_VALUE_BASE : Nat := OCC_COL + 1
def OLD_LEAF_STATE_BASE : Nat := OLD_VALUE_BASE + VALUE_LIMBS
def OLD_CUR_BASE : Nat := OLD_LEAF_STATE_BASE + LEAF_STATE_STEPS * STATE_LANES
def SIBLING_BASE : Nat := OLD_CUR_BASE + DIGEST
def OLD_LEFT_BASE : Nat := SIBLING_BASE + DIGEST
def OLD_RIGHT_BASE : Nat := OLD_LEFT_BASE + DIGEST
def OLD_NODE_STATE_BASE : Nat := OLD_RIGHT_BASE + DIGEST
def DIR_COL : Nat := OLD_NODE_STATE_BASE + NODE_STATE_STEPS * STATE_LANES
def AFTER_BASE : Nat := DIR_COL + 1
def NEW_VALUE_BASE : Nat := AFTER_BASE
def NEW_LEAF_STATE_BASE : Nat := NEW_VALUE_BASE + VALUE_LIMBS
def NEW_CUR_BASE : Nat := NEW_LEAF_STATE_BASE + LEAF_STATE_STEPS * STATE_LANES
def NEW_LEFT_BASE : Nat := NEW_CUR_BASE + DIGEST
def NEW_RIGHT_BASE : Nat := NEW_LEFT_BASE + DIGEST
def NEW_NODE_STATE_BASE : Nat := NEW_RIGHT_BASE + DIGEST
def ACTIVE_COL : Nat := NEW_NODE_STATE_BASE + NODE_STATE_STEPS * STATE_LANES
def COUNT_COL : Nat := ACTIVE_COL + 1
def TRACE_WIDTH : Nat := COUNT_COL + 1

def AUDIT_PI_BASE : Nat := 54
def AUDIT_PI_COUNT : Nat := 16

#guard BEFORE_BASE == 1819    -- ⚑ +112 at the FIELDS-CANONICITY flag day (APPENDIX_SPAN 539 → 651)
#guard BEFORE_BASE == refusalV3.traceWidth   -- ⚑ the reality gate: no independent literal
#guard AFTER_BASE == 2077
#guard ACTIVE_COL == 2325
#guard TRACE_WIDTH == 2327
#guard AUDIT_PI_BASE == 46 + 8

def ev (c : Nat) : EmittedExpr := .var c
def ek (x : Int) : EmittedExpr := .const x
def eadd (a b : EmittedExpr) : EmittedExpr := .add a b
def emul (a b : EmittedExpr) : EmittedExpr := .mul a b
def eneg (a : EmittedExpr) : EmittedExpr := emul (ek (-1)) a
def esub (a b : EmittedExpr) : EmittedExpr := eadd a (eneg b)
def activeGate (body : EmittedExpr) : EmittedExpr := emul (ev ACTIVE_COL) body

def cols (base count : Nat) : List Nat := (List.range count).map (base + ·)
def vars (base count : Nat) : List EmittedExpr := (cols base count).map .var
def stateCols (base step : Nat) : List Nat := cols (base + STATE_LANES * step) STATE_LANES
def chunks4 {alpha : Type} (xs : List alpha) : List (List alpha) := xs.toChunks 4

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

def spongePlan (stateBase : Nat) (preimage : List EmittedExpr) : List State16Step :=
  let chunks := chunks4 preimage
  let absorb := chunks.mapIdx fun stage chunk =>
    ⟨absorbInputExpr stateBase preimage.length stage chunk, stateCols stateBase stage⟩
  let squeeze :=
    ⟨(stateCols stateBase (chunks.length - 1)).map .var, stateCols stateBase chunks.length⟩
  absorb ++ [squeeze]

def spongeDigestCols (stateBase inputLength : Nat) : List Nat :=
  let absorbs := (inputLength + 3) / 4
  cols (stateBase + STATE_LANES * (absorbs - 1)) 4 ++
    cols (stateBase + STATE_LANES * absorbs) 4

def auditKeyLimbs : List EmittedExpr := [ek 0, ek 0, ek 1, ek 0]

def oldLeafPreimage : List EmittedExpr :=
  [ek FLD2, ev OCC_COL] ++ auditKeyLimbs ++ vars OLD_VALUE_BASE VALUE_LIMBS

def newLeafPreimage : List EmittedExpr :=
  [ek FLD2, ek 1] ++ auditKeyLimbs ++ vars NEW_VALUE_BASE VALUE_LIMBS

def oldLeafDigestCols : List Nat := spongeDigestCols OLD_LEAF_STATE_BASE oldLeafPreimage.length
def newLeafDigestCols : List Nat := spongeDigestCols NEW_LEAF_STATE_BASE newLeafPreimage.length

def oldNodePreimage : List EmittedExpr :=
  ek FLN2 :: (vars OLD_LEFT_BASE DIGEST ++ vars OLD_RIGHT_BASE DIGEST)

def newNodePreimage : List EmittedExpr :=
  ek FLN2 :: (vars NEW_LEFT_BASE DIGEST ++ vars NEW_RIGHT_BASE DIGEST)

def oldNodeDigestCols : List Nat := spongeDigestCols OLD_NODE_STATE_BASE oldNodePreimage.length
def newNodeDigestCols : List Nat := spongeDigestCols NEW_NODE_STATE_BASE newNodePreimage.length

#guard oldLeafPreimage.length == 22
#guard newLeafPreimage.length == 22
#guard oldNodePreimage.length == 17
#guard newNodePreimage.length == 17
#guard (spongePlan OLD_LEAF_STATE_BASE oldLeafPreimage).length == LEAF_STATE_STEPS
#guard (spongePlan OLD_NODE_STATE_BASE oldNodePreimage).length == NODE_STATE_STEPS

def state16Lookups : List VmConstraint2 :=
  (spongePlan OLD_LEAF_STATE_BASE oldLeafPreimage ++
    spongePlan NEW_LEAF_STATE_BASE newLeafPreimage ++
    spongePlan OLD_NODE_STATE_BASE oldNodePreimage ++
    spongePlan NEW_NODE_STATE_BASE newNodePreimage).map fun step =>
      .lookup ⟨poseidon2state16, chipLookupTupleState16 step.input step.outputCols⟩

def dirBinary : EmittedExpr := activeGate (emul (ev DIR_COL) (esub (ev DIR_COL) (ek 1)))
def occBinary : EmittedExpr := activeGate (emul (ev OCC_COL) (esub (ev OCC_COL) (ek 1)))
def activeBinary : EmittedExpr := emul (ev ACTIVE_COL) (esub (ev ACTIVE_COL) (ek 1))

def oldReservedCanonical (i : Fin VALUE_LIMBS) : EmittedExpr :=
  activeGate (emul (esub (ek 1) (ev OCC_COL)) (ev (OLD_VALUE_BASE + i.val)))

def leftSelect (cur sibling left : Nat) : EmittedExpr :=
  activeGate (esub (ev left)
    (eadd (ev cur) (emul (ev DIR_COL) (esub (ev sibling) (ev cur)))))

def rightSelect (cur sibling right : Nat) : EmittedExpr :=
  activeGate (esub (ev right)
    (eadd (ev sibling) (emul (ev DIR_COL) (esub (ev cur) (ev sibling)))))

def wl (c : Nat) : WindowExpr := .loc c
def wn (c : Nat) : WindowExpr := .nxt c
def wk (x : Int) : WindowExpr := .const x
def wa (a b : WindowExpr) : WindowExpr := .add a b
def wm (a b : WindowExpr) : WindowExpr := .mul a b
def wneg (a : WindowExpr) : WindowExpr := wm (wk (-1)) a
def ws (a b : WindowExpr) : WindowExpr := wa a (wneg b)

def progressConstraints : List VmConstraint2 :=
  [ .base (.gate activeBinary)
  , .base (.boundary .first (esub (ev ACTIVE_COL) (ek 1)))
  , .base (.boundary .first (ev COUNT_COL))
  , .base (.boundary .last (ev ACTIVE_COL))
  , .base (.boundary .last (esub (ev COUNT_COL) (ek DEPTH)))
  , .windowGate ⟨ws (wn COUNT_COL) (wa (wl COUNT_COL) (wl ACTIVE_COL)), true⟩
  , .windowGate ⟨wm (wn ACTIVE_COL) (ws (wk 1) (wl ACTIVE_COL)), true⟩ ]

def pathConstraints : List VmConstraint2 :=
  [ .base (.gate occBinary), .base (.gate dirBinary) ] ++
  (List.finRange VALUE_LIMBS).map (fun i => .base (.gate (oldReservedCanonical i))) ++
  (List.finRange DIGEST).flatMap (fun i =>
    [ .base (.gate (leftSelect (OLD_CUR_BASE + i.val) (SIBLING_BASE + i.val)
        (OLD_LEFT_BASE + i.val)))
    , .base (.gate (rightSelect (OLD_CUR_BASE + i.val) (SIBLING_BASE + i.val)
        (OLD_RIGHT_BASE + i.val)))
    , .base (.gate (leftSelect (NEW_CUR_BASE + i.val) (SIBLING_BASE + i.val)
        (NEW_LEFT_BASE + i.val)))
    , .base (.gate (rightSelect (NEW_CUR_BASE + i.val) (SIBLING_BASE + i.val)
        (NEW_RIGHT_BASE + i.val))) ]) ++
  (List.finRange DIGEST).flatMap (fun i =>
    [ .base (.boundary .first
        (esub (ev (OLD_CUR_BASE + i.val)) (ev (oldLeafDigestCols.getD i.val 0))))
    , .base (.boundary .first
        (esub (ev (NEW_CUR_BASE + i.val)) (ev (newLeafDigestCols.getD i.val 0))))
    , .windowGate ⟨wm (wn ACTIVE_COL)
        (ws (wn (OLD_CUR_BASE + i.val)) (wl (oldNodeDigestCols.getD i.val 0))), true⟩
    , .windowGate ⟨wm (wn ACTIVE_COL)
        (ws (wn (NEW_CUR_BASE + i.val)) (wl (newNodeDigestCols.getD i.val 0))), true⟩
    , .windowGate ⟨wm (wm (wl ACTIVE_COL) (ws (wk 1) (wn ACTIVE_COL)))
        (ws (wl (oldNodeDigestCols.getD i.val 0))
          (wl (fieldsRootGroupCol EFFECT_VM_WIDTH i))), true⟩
    , .windowGate ⟨wm (wm (wl ACTIVE_COL) (ws (wk 1) (wn ACTIVE_COL)))
        (ws (wl (newNodeDigestCols.getD i.val 0))
          (wl (fieldsRootGroupCol (EFFECT_VM_WIDTH + B_SPAN) i))), true⟩ ])

def auditPins (piBase : Nat) : List VmConstraint2 :=
  (List.range VALUE_LIMBS).map fun i =>
    .base (.piBinding .first (NEW_VALUE_BASE + i) (piBase + i))

/-- Exact refusal host before the uniform DFA tail and faithful-wide append.  It deliberately starts
from `refusalV3` rather than `refusalFieldsWriteV3`: the legacy scalar map-op is absent. -/
def refusalExactFieldsV4 : EffectVmDescriptor2 :=
  let base := withRecordPin8Headroom2 refusalV3
  { base with
    name := "dregg-effectvm-refusal-v2-rot24-v4-write-exact-fields"
    traceWidth := TRACE_WIDTH
    piCount := base.piCount + AUDIT_PI_COUNT
    tables := v2Tables TRACE_WIDTH ++ [poseidon2State16ChipTableDef]
    constraints := base.constraints ++ state16Lookups ++ progressConstraints ++ pathConstraints ++
      auditPins base.piCount }

def withState16Table (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with tables := d.tables ++ [poseidon2State16ChipTableDef] }

/-- The exact bare-wide host used by both registry probes.  `wideAppend` rebuilds the common table
list, so the state16 declaration is restored after it. -/
def refusalExactFieldsWide : EffectVmDescriptor2 :=
  withState16Table
    (Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend
      (withDfaRcPins refusalExactFieldsV4)
      EffectVmEmitRefusal.refusalVmDescriptor.traceWidth
      (EffectVmEmitRefusal.refusalVmDescriptor.traceWidth + B_SPAN))

#guard refusalExactFieldsV4.traceWidth == TRACE_WIDTH
#guard refusalExactFieldsV4.piCount == 70
#guard (withRecordPin8Headroom2 refusalV3).piCount == AUDIT_PI_BASE
#guard refusalExactFieldsWide.traceWidth == TRACE_WIDTH + 992
#guard refusalExactFieldsWide.piCount == 90
#guard ((refusalExactFieldsV4.constraints.filter fun c =>
  match c with | .lookup l => l.table == poseidon2state16 | _ => false).length) == 26
#guard ((refusalExactFieldsV4.constraints.filter fun c =>
  match c with | .mapOp _ => true | _ => false).length) == 0

/-- The raw audit limbs are genuine public inputs, not witness-only spare params. -/
theorem auditPin_mem (i : Nat) (hi : i < VALUE_LIMBS) :
    VmConstraint2.base (.piBinding .first (NEW_VALUE_BASE + i) (AUDIT_PI_BASE + i))
      ∈ refusalExactFieldsV4.constraints := by
  have hpi : (withRecordPin8Headroom2 refusalV3).piCount = AUDIT_PI_BASE := by rfl
  simp [refusalExactFieldsV4, auditPins, hpi, hi]

#assert_axioms auditPin_mem

end Dregg2.Circuit.Emit.ExactFieldsRefusalEmit
