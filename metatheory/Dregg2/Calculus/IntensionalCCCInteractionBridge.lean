/-
# Dregg2.Calculus.IntensionalCCCInteractionBridge

This module connects `IntensionalCCCTrace` to DREGG's existing executable
`InteractionNetTrace` checker.  The connection is deliberately a connection of
*proof evidence*, not an encoding of higher-order values as Booleans:

* the typed source step retains authority for beta/eta/share denotation;
* its root rule and complete local address are encoded as a Boolean interaction
  receipt;
* `InteractionNetTrace.LocalCert.check` validates that receipt fail-closed; and
* the bridge theorem returns checker acceptance together with preservation of
  the original typed denotation.

Each source address edge becomes one `andLeft` frame whose untouched right
subnet is a unary marker for the exact edge tag.  Thus share-value and
share-body paths are distinct in the checked before/after graphs.  Root beta,
eta, first-projection, and second-projection rules likewise use four distinct
Boolean active rules.  The executable target does not pretend that these
Boolean receipt graphs are the lambda terms themselves.

`ConstraintLayout` is a small exact row budget for a later DescriptorIR2
emitter.  It fixes one active-rule row, one row per address edge, one selector
per row, two parent-link equalities per address edge, and explicit binder
checks.  It is an ABI/cost layout, not yet a DescriptorIR2 implementation or a
cryptographic IOP/IOPP.
-/
import Dregg2.Calculus.IntensionalCCCTrace
import Dregg2.Calculus.InteractionNetTrace

namespace Dregg2.Calculus.IntensionalCCCInteractionBridge

namespace Source
abbrev Ty := IntensionalCCCTrace.Ty
abbrev Net := IntensionalCCCTrace.Net
abbrev Env := IntensionalCCCTrace.Env
end Source

namespace Receipt
open InteractionNetTrace

/-! ## Lossless rule/address layout -/

/-- The four active rules of the intensional target. -/
inductive RootTag where
  | beta
  | eta
  | fstPair
  | sndPair
  deriving DecidableEq, Repr

/-- Every congruence constructor is retained as a distinct address edge. -/
inductive PathTag where
  | underSucc
  | pairLeft
  | pairRight
  | underFst
  | underSnd
  | underLam
  | appFn
  | appArg
  | underLift
  | shareValue
  | shareBody
  deriving DecidableEq, Repr

/-- Stable small integer codes for untouched Boolean marker subnets. -/
def PathTag.code : PathTag -> Nat
  | .underSucc => 0
  | .pairLeft => 1
  | .pairRight => 2
  | .underFst => 3
  | .underSnd => 4
  | .underLam => 5
  | .appFn => 6
  | .appArg => 7
  | .underLift => 8
  | .shareValue => 9
  | .shareBody => 10

theorem pathTag_code_injective : Function.Injective PathTag.code := by
  intro a b h
  cases a <;> cases b <;> simp [PathTag.code] at h ⊢

/-- Root tag plus outer-to-inner local address. -/
structure Layout where
  root : RootTag
  path : List PathTag
  deriving DecidableEq, Repr

/-- Extract the exact local rule/address layout from typed source evidence. -/
def layout : {before after : IntensionalCCCTrace.Net Γ A} ->
    IntensionalCCCTrace.LocalStep before after -> Layout
  | _, _, .beta _ _ => ⟨.beta, []⟩
  | _, _, .eta _ => ⟨.eta, []⟩
  | _, _, .fstPair _ _ => ⟨.fstPair, []⟩
  | _, _, .sndPair _ _ => ⟨.sndPair, []⟩
  | _, _, .underSucc step =>
      let inner := layout step
      ⟨inner.root, .underSucc :: inner.path⟩
  | _, _, .pairLeft step _ =>
      let inner := layout step
      ⟨inner.root, .pairLeft :: inner.path⟩
  | _, _, .pairRight _ step =>
      let inner := layout step
      ⟨inner.root, .pairRight :: inner.path⟩
  | _, _, .underFst step =>
      let inner := layout step
      ⟨inner.root, .underFst :: inner.path⟩
  | _, _, .underSnd step =>
      let inner := layout step
      ⟨inner.root, .underSnd :: inner.path⟩
  | _, _, .underLam step =>
      let inner := layout step
      ⟨inner.root, .underLam :: inner.path⟩
  | _, _, .appFn step _ =>
      let inner := layout step
      ⟨inner.root, .appFn :: inner.path⟩
  | _, _, .appArg _ step =>
      let inner := layout step
      ⟨inner.root, .appArg :: inner.path⟩
  | _, _, .underLift step =>
      let inner := layout step
      ⟨inner.root, .underLift :: inner.path⟩
  | _, _, .shareValue step _ =>
      let inner := layout step
      ⟨inner.root, .shareValue :: inner.path⟩
  | _, _, .shareBody _ step =>
      let inner := layout step
      ⟨inner.root, .shareBody :: inner.path⟩

/-- Layout depth agrees exactly with the source evidence's address depth. -/
theorem layout_path_length {before after : IntensionalCCCTrace.Net Γ A}
    (step : IntensionalCCCTrace.LocalStep before after) :
    (layout step).path.length = step.addressDepth := by
  induction step <;> simp [layout, IntensionalCCCTrace.LocalStep.addressDepth, *]

/-! ## Executable InteractionNet receipts -/

/-- Four distinct, denotation-preserving Boolean rules serve as root tags. -/
def RootTag.rule : RootTag -> InteractionNetTrace.ActiveRule
  | .beta => .andLit true true
  | .eta => .orLit false true
  | .fstPair => .andLit true false
  | .sndPair => .orLit false false

theorem rootTag_rule_injective : Function.Injective RootTag.rule := by
  intro a b h
  cases a <;> cases b <;> simp [RootTag.rule] at h ⊢

/-- Unary Boolean marker.  Different codes have different finite syntax even
when their denotations happen to coincide. -/
def marker : Nat -> InteractionNetTrace.Net
  | 0 => .lit false
  | n + 1 => .neg (marker n)

theorem marker_injective : Function.Injective marker := by
  intro n
  induction n with
  | zero =>
      intro m h
      cases m with
      | zero => rfl
      | succ m => cases h
  | succ n ih =>
      intro m h
      cases m with
      | zero => cases h
      | succ m =>
          congr 1
          exact ih (InteractionNetTrace.Net.neg.inj h)

/-- Encode an outer-to-inner address as nested left frames.  The untouched
right neighbour pins the exact source congruence tag. -/
def encodeContext : List PathTag -> InteractionNetTrace.Context
  | [] => .hole
  | tag :: rest => .andLeft (encodeContext rest) (marker tag.code)

/-- The Boolean context retains the complete address, not merely its depth. -/
theorem encodeContext_injective : Function.Injective encodeContext := by
  intro path
  induction path with
  | nil =>
      intro other h
      cases other with
      | nil => rfl
      | cons tag rest => cases h
  | cons tag rest ih =>
      intro other h
      cases other with
      | nil => cases h
      | cons tag' rest' =>
          have hcontext : encodeContext rest = encodeContext rest' :=
            InteractionNetTrace.Context.andLeft.inj h |>.1
          have hmarker : marker tag.code = marker tag'.code :=
            InteractionNetTrace.Context.andLeft.inj h |>.2
          have htag : tag = tag' := pathTag_code_injective (marker_injective hmarker)
          subst tag'
          have hrest : rest = rest' := ih hcontext
          subst rest'
          rfl

/-- Translate one typed local step to an existing executable local
certificate. -/
def translateStep {before after : IntensionalCCCTrace.Net Γ A}
    (step : IntensionalCCCTrace.LocalStep before after) :
    InteractionNetTrace.LocalCert where
  context := encodeContext (layout step).path
  rule := (layout step).root.rule

/-- A fully exposed checker invocation. -/
structure CheckedReceipt where
  before : InteractionNetTrace.Net
  cert : InteractionNetTrace.LocalCert
  after : InteractionNetTrace.Net
  deriving DecidableEq, Repr

def CheckedReceipt.check (receipt : CheckedReceipt) : Bool :=
  receipt.cert.check receipt.before receipt.after

/-- Expose exactly the endpoints committed by the translated certificate. -/
def stepReceipt {before after : IntensionalCCCTrace.Net Γ A}
    (step : IntensionalCCCTrace.LocalStep before after) : CheckedReceipt :=
  let cert := translateStep step
  ⟨cert.before, cert, cert.after⟩

/-- Every honest translation is accepted by the existing fail-closed checker. -/
@[simp] theorem stepReceipt_checks {before after : IntensionalCCCTrace.Net Γ A}
    (step : IntensionalCCCTrace.LocalStep before after) :
    (stepReceipt step).check = true := by
  simp [stepReceipt, CheckedReceipt.check, InteractionNetTrace.LocalCert.check]

/-- The accepted Boolean receipt preserves its own observation. -/
theorem stepReceipt_boolean_sound {before after : IntensionalCCCTrace.Net Γ A}
    (step : IntensionalCCCTrace.LocalStep before after) :
    (stepReceipt step).after.denote = (stepReceipt step).before.denote :=
  InteractionNetTrace.localCheck_sound (stepReceipt_checks step)

/-- End-to-end one-step theorem: the existing checker accepts the translated
receipt, and the original typed beta/eta/share step preserves its full source
denotation.  The two claims are kept separate rather than pretending that the
Boolean receipt denotes a higher-order value. -/
theorem translatedStep_checked_and_source_sound
    {before after : IntensionalCCCTrace.Net Γ A}
    (step : IntensionalCCCTrace.LocalStep before after) (env : IntensionalCCCTrace.Env Γ) :
    (stepReceipt step).check = true ∧ after.denote env = before.denote env :=
  ⟨stepReceipt_checks step, IntensionalCCCTrace.localStep_denote step env⟩

/-! ## Trace batches -/

/-- Translate a typed trace into the batch of independently exposed existing
checker receipts.  Each element retains its own exact before/after graph. -/
def translateTrace : {start finish : IntensionalCCCTrace.Net Γ A} ->
    IntensionalCCCTrace.Trace start finish -> List CheckedReceipt
  | _, _, .refl _ => []
  | _, _, .cons step tail => stepReceipt step :: translateTrace tail

/-- Executable batch check. -/
def checkReceiptBatch : List CheckedReceipt -> Bool
  | [] => true
  | receipt :: rest => receipt.check && checkReceiptBatch rest

/-- Every receipt produced from an honest typed trace is accepted. -/
@[simp] theorem translateTrace_checks {start finish : IntensionalCCCTrace.Net Γ A}
    (trace : IntensionalCCCTrace.Trace start finish) :
    checkReceiptBatch (translateTrace trace) = true := by
  induction trace <;> simp [translateTrace, checkReceiptBatch, *]

/-- End-to-end trace theorem: all existing checker invocations accept, and the
original typed endpoints have equal denotation. -/
theorem translatedTrace_checked_and_source_sound
    {start finish : IntensionalCCCTrace.Net Γ A}
    (trace : IntensionalCCCTrace.Trace start finish) (env : IntensionalCCCTrace.Env Γ) :
    checkReceiptBatch (translateTrace trace) = true ∧
      finish.denote env = start.denote env :=
  ⟨translateTrace_checks trace, IntensionalCCCTrace.trace_denote trace env⟩

/-! ## Exact row/constraint layout for later DescriptorIR2 emission -/

/-- Does this root interaction introduce/eliminate an STLC binder? -/
def RootTag.binderChecks : RootTag -> Nat
  | .beta => 1
  | .eta => 1
  | .fstPair => 0
  | .sndPair => 0

/-- Does this path edge cross a binder boundary? -/
def PathTag.binderChecks : PathTag -> Nat
  | .underLam => 1
  | .shareBody => 1
  | _ => 0

/-- Exact proposed row layout.  Four row cells are reserved as
`(opcode, beforeRef, afterRef, parentRef)`; constraints are counted separately. -/
structure ConstraintLayout where
  activeRows : Nat
  addressRows : Nat
  rowCells : Nat
  selectorConstraints : Nat
  parentLinkEqualities : Nat
  binderConstraints : Nat
  deriving DecidableEq, Repr

def constraintLayout (source : Layout) : ConstraintLayout :=
  let totalRows := source.path.length + 1
  { activeRows := 1
    addressRows := source.path.length
    rowCells := 4 * totalRows
    selectorConstraints := totalRows
    parentLinkEqualities := 2 * source.path.length
    binderConstraints := source.root.binderChecks +
      (source.path.map PathTag.binderChecks).sum }

def stepConstraintLayout {before after : IntensionalCCCTrace.Net Γ A}
    (step : IntensionalCCCTrace.LocalStep before after) : ConstraintLayout :=
  constraintLayout (layout step)

/-- A translated step always occupies exactly `addressDepth + 1` rows. -/
theorem constraint_rows_exact {before after : IntensionalCCCTrace.Net Γ A}
    (step : IntensionalCCCTrace.LocalStep before after) :
    (stepConstraintLayout step).activeRows + (stepConstraintLayout step).addressRows =
      step.addressDepth + 1 := by
  simp [stepConstraintLayout, constraintLayout, layout_path_length, Nat.add_comm]

/-- Exact cell count for the four-column proposed row ABI. -/
theorem constraint_cells_exact {before after : IntensionalCCCTrace.Net Γ A}
    (step : IntensionalCCCTrace.LocalStep before after) :
    (stepConstraintLayout step).rowCells = 4 * (step.addressDepth + 1) := by
  simp [stepConstraintLayout, constraintLayout, layout_path_length]

/-! ## Non-vacuity and hostile refusals -/

namespace Reference

open IntensionalCCCTrace

def innerBeta : LocalStep
    (Net.app (Net.lam (Net.var (.zero : Var (.nat :: .nat :: []) .nat)))
      (Net.var (.zero : Var (.nat :: []) .nat)))
    (Net.share (Net.var (.zero : Var (.nat :: []) .nat))
      (Net.var (.zero : Var (.nat :: .nat :: []) .nat))) :=
  .beta (Net.var .zero) (Net.var .zero)

def innerBefore : Net [.nat] .nat :=
  Net.app (Net.lam (Net.var (.zero : Var (.nat :: .nat :: []) .nat)))
    (Net.var (.zero : Var (.nat :: []) .nat))

def innerAfter : Net [.nat] .nat :=
  Net.share (Net.var (.zero : Var (.nat :: []) .nat))
    (Net.var (.zero : Var (.nat :: .nat :: []) .nat))

def outerBefore : Net [] .nat := Net.share (Net.lit 42) innerBefore
def outerAfter : Net [] .nat := Net.share (Net.lit 42) innerAfter

/-- A beta redex under the body side of a sharing binder. -/
def underShareBody : LocalStep outerBefore outerAfter :=
  .shareBody (Net.lit 42) innerBeta

theorem underShareBody_layout :
    layout underShareBody = ⟨.beta, [.shareBody]⟩ := by decide

theorem root_beta_constraint_layout :
    stepConstraintLayout IntensionalCCCTrace.Reference.betaEvidence =
      { activeRows := 1, addressRows := 0, rowCells := 4,
        selectorConstraints := 1, parentLinkEqualities := 0,
        binderConstraints := 1 } := by decide

theorem under_share_body_constraint_layout :
    stepConstraintLayout underShareBody =
      { activeRows := 1, addressRows := 1, rowCells := 8,
        selectorConstraints := 2, parentLinkEqualities := 2,
        binderConstraints := 2 } := by decide

def honestNested : CheckedReceipt := stepReceipt underShareBody

/-- Same root rule, wrong empty location: the existing checker rejects it
against the honest nested endpoints. -/
def wrongLocation : InteractionNetTrace.LocalCert where
  context := .hole
  rule := (layout underShareBody).root.rule

theorem wrong_location_refused :
    wrongLocation.check honestNested.before honestNested.after = false := by decide

/-- The hostile certificate changes `shareBody` to `shareValue` while retaining
the honest committed endpoints.  Their distinct marker subnets make it fail. -/
def wrongBinderSide : InteractionNetTrace.LocalCert where
  context := encodeContext [.shareValue]
  rule := (layout underShareBody).root.rule

theorem wrong_binder_side_refused :
    wrongBinderSide.check honestNested.before honestNested.after = false := by decide

/-- The actual typed trace from the intensional module translates and checks. -/
theorem reference_trace_checks :
    checkReceiptBatch
      (translateTrace IntensionalCCCTrace.Reference.betaTrace) = true := by decide

/-- The same translated trace preserves the source pair `(8,8)`. -/
theorem reference_end_to_end :
    checkReceiptBatch
        (translateTrace IntensionalCCCTrace.Reference.betaTrace) = true ∧
      IntensionalCCCTrace.Reference.shared.denote PUnit.unit =
        IntensionalCCCTrace.Reference.start.denote PUnit.unit :=
  translatedTrace_checked_and_source_sound
    IntensionalCCCTrace.Reference.betaTrace PUnit.unit

end Reference

#assert_all_clean [
  pathTag_code_injective,
  marker_injective,
  encodeContext_injective,
  layout_path_length,
  rootTag_rule_injective,
  stepReceipt_checks,
  stepReceipt_boolean_sound,
  translatedStep_checked_and_source_sound,
  translateTrace_checks,
  translatedTrace_checked_and_source_sound,
  constraint_rows_exact,
  constraint_cells_exact,
  Reference.underShareBody_layout,
  Reference.root_beta_constraint_layout,
  Reference.under_share_body_constraint_layout,
  Reference.wrong_location_refused,
  Reference.wrong_binder_side_refused,
  Reference.reference_trace_checks,
  Reference.reference_end_to_end
]

end Receipt

end Dregg2.Calculus.IntensionalCCCInteractionBridge
