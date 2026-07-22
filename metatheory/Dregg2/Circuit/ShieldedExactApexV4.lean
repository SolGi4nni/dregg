/-
# Shielded exact apex v4 — one hidden opening, one exact consequence

This module fixes the *semantic relation* that a future shielded-exact prover and verifier must
implement.  It intentionally does not emit an AIR, construct a proof, or claim a runnable verifier.

The central law is that there is one selected hidden note opening.  That same opening is used by:

* a full sixteen-u16-limb (256-bit) nullifier derivation;
* the sixteen-BabyBear-lane native-PQ value/asset binding;
* the closed, per-asset conservation equation; and
* the exact list of newly committed output notes.

The selected nullifier is appended to the exact accumulator with count `n + 1`.  The consequence
hash binds that exact transition, the wide opening commitment, the market/ring public surface, the
output-note count, and the output-note root.  There are no clear value or asset fields in the public
statement.

## Honest cryptographic boundary

All serialization, shared-witness, conservation, exact-count, and mutation-refusal laws below are
proved structurally.  Hash collision resistance, nullifier pseudorandomness, note-commitment
binding/hiding, and HidingFRI knowledge soundness are not Lean theorems here.  They are represented by
explicit surfaces and collision events.  `PinnedVerifierContract.knowledgeSound` is the future
proof-system seam: callers must supply it for a fixed relation/VK pair; this file does not inhabit it.

This is a v4 relation.  Reusing FNSP-v3 would publish the clear value and would put the clear four-limb
value in the linked leaf, so doing so cannot implement this statement.
-/

import Dregg2.Circuit.ExactNullifierAafiPlan
import Dregg2.Shielded.WideNativePqCommitment
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Dregg2.Circuit.ShieldedExactApexV4

open Dregg2.Circuit.ExactNullifierAafiPlan
open Dregg2.Shielded.WideNativePqCommitment

set_option autoImplicit false

/-! ## 1. Typed hidden notes and full-width nullifier derivation -/

/-- The complete private opening of a note at the semantic boundary.  `valueAsset` is the faithful
wide opening already proved to serialize injectively.  Owner and nonce are separate canonical words
needed by a real note/nullifier transcript; they are never public clear value fields. -/
structure NoteOpening where
  valueAsset : Opening
  owner : CanonicalU64
  nonce : CanonicalU64
  deriving DecidableEq, Repr

/-- A full 256-bit secret represented as sixteen canonical little-endian u16 words. -/
abbrev SpendSecret := Fin KEY_LIMBS -> Limb16

/-- The selected spent note.  Exactly this `note.valueAsset` participates in the wide commitment and
the conservation input list; there is no independently caller-supplied value/asset witness. -/
structure SelectedSpend where
  note : NoteOpening
  secret : SpendSecret

/-- A nullifier implementation surface.  Its output type is the existing exact 16-limb nullifier
key, and `canonical` prevents field representatives from masquerading as u16 words.  PRF security and
secret hiding remain cryptographic obligations of the eventual implementation. -/
structure NullifierSurface where
  derive : SpendSecret -> NoteOpening -> RawNullifierKey
  canonical : forall secret note, CanonicalKey (derive secret note)

/-- The exact full-width collision event a nullifier-PRF theorem must bound. -/
def NullifierCollision (surface : NullifierSurface)
    (left right : SelectedSpend) : Prop :=
  (left.secret ≠ right.secret ∨ left.note ≠ right.note) /\
    surface.derive left.secret left.note = surface.derive right.secret right.note

/-- The exact sixteen-word public encoding of a derived nullifier. -/
def derivedNullifierWords (surface : NullifierSurface) (spend : SelectedSpend) : List Int :=
  rawKeyBlock (surface.derive spend.secret spend.note)

@[simp] theorem derivedNullifierWords_length (surface : NullifierSurface)
    (spend : SelectedSpend) :
    (derivedNullifierWords surface spend).length = KEY_LIMBS := by
  simp [derivedNullifierWords]

/-- No two distinct exact nullifier keys share the same full sixteen-word encoding. -/
theorem derivedNullifierWords_eq_iff (surface : NullifierSurface) (left right : SelectedSpend) :
    derivedNullifierWords surface left = derivedNullifierWords surface right <->
      surface.derive left.secret left.note = surface.derive right.secret right.note := by
  constructor
  · intro h
    apply rawKeyBlock_injective
    simpa [derivedNullifierWords] using h
  · intro h
    simp [derivedNullifierWords, h]

/-- Distinct nullifier preimages with one derived full key are precisely a nullifier collision. -/
theorem distinct_nullifier_preimages_same_key_reduce_to_collision
    (surface : NullifierSurface) (left right : SelectedSpend)
    (different : left.secret ≠ right.secret ∨ left.note ≠ right.note)
    (sameKey : surface.derive left.secret left.note =
      surface.derive right.secret right.note) :
    NullifierCollision surface left right :=
  ⟨different, sameKey⟩

/-! ## 2. Closed hidden value flow and exact output commitments -/

/-- A note-commitment surface.  The function is explicit: this model never assumes that a
compressing hash is injective. -/
structure NoteCommitmentSurface where
  commit : NoteOpening -> WideDigest

/-- The exact note-commitment collision event that a computational binding theorem must bound. -/
def NoteCommitmentCollision (surface : NoteCommitmentSurface)
    (left right : NoteOpening) : Prop :=
  left ≠ right /\ surface.commit left = surface.commit right

/-- Distinct note openings with one commitment are precisely the note-binding collision event. -/
theorem distinct_note_openings_same_commitment_reduce_to_collision
    (surface : NoteCommitmentSurface) (left right : NoteOpening)
    (different : left ≠ right) (sameCommitment : surface.commit left = surface.commit right) :
    NoteCommitmentCollision surface left right :=
  ⟨different, sameCommitment⟩

/-- The hidden integer value of a note.  `CanonicalU64.toInt` proves it lies in `[0, 2^64)`. -/
def NoteOpening.value (note : NoteOpening) : Int := note.valueAsset.value.toInt

/-- The hidden canonical asset identifier of a note. -/
def NoteOpening.asset (note : NoteOpening) : CanonicalU64 := note.valueAsset.asset

/-- Contribution of one note to one asset's conservation equation. -/
def amountFor (asset : CanonicalU64) (note : NoteOpening) : Int :=
  if note.asset = asset then note.value else 0

/-- Per-asset total of a hidden note list. -/
def totalFor (asset : CanonicalU64) (notes : List NoteOpening) : Int :=
  (notes.map (amountFor asset)).sum

/-- Conservation is per asset, never one aggregate scalar across unrelated asset classes. -/
def Conserves (inputs outputs : List NoteOpening) : Prop :=
  forall asset, totalFor asset inputs = totalFor asset outputs

/-- Fixed current Dark-AMM public surface width. -/
def DARK_AMM_PUBLIC_LANES : Nat := 19

/-- Fixed current two-leg shielded-ring public surface width. -/
def RING_PUBLIC_LANES : Nat := 27

/-- Canonical public field lane. -/
abbrev FieldLane := Dregg2.Circuit.BabyBearFriField.BabyBear

/-- The complete fixed market/ring surface absorbed by FXC4.  Fixed function types prevent omitted
or trailing lanes, while `selectedLeg : Fin 2` pins which ring leg owns the exact full nullifier. -/
structure MarketPublicSurface where
  darkAmm : Fin DARK_AMM_PUBLIC_LANES -> FieldLane
  ring : Fin RING_PUBLIC_LANES -> FieldLane
  selectedLeg : Fin 2

theorem darkAmm_public_lane_count : Fintype.card (Fin DARK_AMM_PUBLIC_LANES) = 19 := by
  decide

theorem ring_public_lane_count : Fintype.card (Fin RING_PUBLIC_LANES) = 27 := by
  decide

/-- The witness contains one selected exact spend plus any other private inputs required by the
fixed consequence (for example the other side of a ring or reserve update), and the complete output
note list.  The selected spend is structurally the head of `consumedNotes`. -/
structure Witness where
  selected : SelectedSpend
  additionalInputs : List NoteOpening
  outputs : List NoteOpening
  marketPublic : MarketPublicSurface

/-- Every private input consumed by the consequence. -/
def Witness.consumedNotes (witness : Witness) : List NoteOpening :=
  witness.selected.note :: witness.additionalInputs

@[simp] theorem Witness.selected_mem_consumedNotes (witness : Witness) :
    witness.selected.note ∈ witness.consumedNotes := by
  simp [Witness.consumedNotes]

/-- Exact output commitments: one commitment for each witness output, in order, with neither ghost
nor omitted output. -/
def outputCommitments (surface : NoteCommitmentSurface) (witness : Witness) : List WideDigest :=
  witness.outputs.map surface.commit

@[simp] theorem outputCommitments_length (surface : NoteCommitmentSurface) (witness : Witness) :
    (outputCommitments surface witness).length = witness.outputs.length := by
  simp [outputCommitments]

/-- Eight-lane root type used by the exact accumulator, output-note tree, and consequence digest. -/
abbrev Root8 := Dregg2.Circuit.ExactNullifierAafiPlan.Root8

/-- Output-note root surface.  Collision resistance is deliberately not a structure field. -/
structure OutputRootSurface where
  hash : List WideDigest -> Root8

def OutputRootCollision (surface : OutputRootSurface)
    (left right : List WideDigest) : Prop :=
  left ≠ right /\ surface.hash left = surface.hash right

/-! ## 3. Exact v4 accumulator step and the public statement -/

/-- The shielded exact accumulator point.  Its v4 root commits FNI4 leaves carrying the wide binding;
it is not an FNS3 checkpoint over clear FNI2 values. -/
structure ExactState where
  root : Root8
  count : Nat

/-- Root-rewrite relation implemented by the future FNI4 AAFI descriptor.  It receives the complete
nullifier and all sixteen value/asset-binding lanes. -/
abbrev RootAppendRelation :=
  Root8 -> Root8 -> RawNullifierKey -> WideDigest -> Prop

/-- An exact append is a root rewrite plus the non-negotiable `count + 1` law. -/
structure ExactAppend (rootStep : RootAppendRelation) (before after : ExactState)
    (nullifier : RawNullifierKey) (binding : WideDigest) : Prop where
  rootRewrite : rootStep before.root after.root nullifier binding
  countStep : after.count = before.count + 1

/-- Public semantic statement for the shielded exact subrelation.  Value and asset occur only through
the wide commitment.  Full-turn/consensus envelope fields intentionally live in the separate v4
consensus-core model. -/
structure PublicStatement where
  nullifier : RawNullifierKey
  valueAssetBinding : WideDigest
  exactBefore : ExactState
  exactAfter : ExactState
  outputNotesRoot : Root8
  consequence : Root8

/-! ## 4. One fixed consequence transcript -/

/-- The semantic preimage of FXC4.  It binds the complete public exact transition and the complete
market/ring public surface, plus exact output count/root.  The output openings remain hidden. -/
structure ConsequencePreimage where
  nullifier : RawNullifierKey
  valueAssetBinding : WideDigest
  exactBefore : ExactState
  exactAfter : ExactState
  marketPublic : MarketPublicSurface
  outputNoteCount : Nat
  outputNotesRoot : Root8

def consequencePreimage (statement : PublicStatement) (witness : Witness) : ConsequencePreimage :=
  { nullifier := statement.nullifier
    valueAssetBinding := statement.valueAssetBinding
    exactBefore := statement.exactBefore
    exactAfter := statement.exactAfter
    marketPublic := witness.marketPublic
    outputNoteCount := witness.outputs.length
    outputNotesRoot := statement.outputNotesRoot }

/-- Consequence hash surface.  Its deployed implementation must use the fixed FXC4 domain and
canonical encodings; collision resistance is an external computational theorem. -/
structure ConsequenceSurface where
  hash : ConsequencePreimage -> Root8

def ConsequenceCollision (surface : ConsequenceSurface)
    (left right : ConsequencePreimage) : Prop :=
  left ≠ right /\ surface.hash left = surface.hash right

/-! ## 5. The shared-witness apex relation -/

/-- The actual fixed market/game rule relates the complete typed public surface to the same hidden
input and output note lists used by conservation. -/
abbrev FixedConsequenceRule :=
  MarketPublicSurface -> List NoteOpening -> List NoteOpening -> Prop

/-- All code-owned surfaces needed to state the relation.  No surface contains a proof that its
cryptographic primitive is secure. -/
structure Environment where
  nullifier : NullifierSurface
  wide : NativePqWideHashSurface
  noteCommitment : NoteCommitmentSurface
  outputRoot : OutputRootSurface
  consequence : ConsequenceSurface
  rootStep : RootAppendRelation
  /-- The actual Dark-AMM/ring/game consequence, not a caller-selected label.  A deployed environment
  must install one fixed relation here and pin the emitted descriptor/VK to it. -/
  rule : FixedConsequenceRule

/-- **The shielded exact apex relation.**  Every equality below is over a shared typed field, not a
legacy scalar compatibility join. -/
structure Relation (env : Environment) (witness : Witness) (statement : PublicStatement) : Prop where
  outputsNonempty : witness.outputs ≠ []
  nullifierFromSelected :
    statement.nullifier = env.nullifier.derive witness.selected.secret witness.selected.note
  bindingFromSelected :
    statement.valueAssetBinding =
      Dregg2.Shielded.WideNativePqCommitment.commit
        env.wide .valueBinding witness.selected.note.valueAsset
  fixedRule : env.rule witness.marketPublic witness.consumedNotes witness.outputs
  conservation : Conserves witness.consumedNotes witness.outputs
  exactAppend :
    ExactAppend env.rootStep statement.exactBefore statement.exactAfter
      statement.nullifier statement.valueAssetBinding
  outputRootExact :
    statement.outputNotesRoot = env.outputRoot.hash (outputCommitments env.noteCommitment witness)
  consequenceExact :
    statement.consequence = env.consequence.hash (consequencePreimage statement witness)

/-! ## 6. Structural refinement laws -/

/-- Both public carriers come from the selected note's one shared opening. -/
theorem Relation.shared_selected_opening {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement) :
    statement.nullifier = env.nullifier.derive witness.selected.secret witness.selected.note /\
    statement.valueAssetBinding =
      Dregg2.Shielded.WideNativePqCommitment.commit
        env.wide .valueBinding witness.selected.note.valueAsset :=
  ⟨accepted.nullifierFromSelected, accepted.bindingFromSelected⟩

/-- The accepted nullifier is the complete sixteen-u16-limb derived key. -/
theorem Relation.full_nullifier_words {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement) :
    rawKeyBlock statement.nullifier = derivedNullifierWords env.nullifier witness.selected := by
  rw [accepted.nullifierFromSelected]
  rfl

/-- The accepted full nullifier is canonical in every one of its sixteen limbs. -/
theorem Relation.full_nullifier_canonical {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement) :
    CanonicalKey statement.nullifier := by
  rw [accepted.nullifierFromSelected]
  exact env.nullifier.canonical witness.selected.secret witness.selected.note

/-- Exact count advancement is a theorem of acceptance, not a caller-authored output hint. -/
theorem Relation.exact_count_advances {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement) :
    statement.exactAfter.count = statement.exactBefore.count + 1 :=
  accepted.exactAppend.countStep

/-- The root rewrite consumes the full nullifier and all sixteen wide-binding lanes. -/
theorem Relation.root_rewrite_is_full_width {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement) :
    env.rootStep statement.exactBefore.root statement.exactAfter.root
      statement.nullifier statement.valueAssetBinding :=
  accepted.exactAppend.rootRewrite

/-- Per-asset conservation inherited by every accepted consequence. -/
theorem Relation.conserves_asset {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement)
    (asset : CanonicalU64) :
    totalFor asset witness.consumedNotes = totalFor asset witness.outputs :=
  accepted.conservation asset

/-- Acceptance proves the fixed market/game rule over the same consumed and created note lists used
by conservation; hashing a rule label is not sufficient. -/
theorem Relation.refines_fixed_consequence_rule {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement) :
    env.rule witness.marketPublic witness.consumedNotes witness.outputs :=
  accepted.fixedRule

/-- Exact output creation: the committed list has precisely one entry per hidden output. -/
theorem Relation.output_commitment_count_exact {env : Environment} {witness : Witness}
    {statement : PublicStatement} (_accepted : Relation env witness statement) :
    (outputCommitments env.noteCommitment witness).length = witness.outputs.length := by
  simp

/-- Accepted output creation cannot be empty. -/
theorem Relation.output_exists {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement) :
    0 < witness.outputs.length := by
  cases houtputs : witness.outputs with
  | nil => exact False.elim (accepted.outputsNonempty houtputs)
  | cons output rest => simp

/-- The public output root is computed from exactly the witness-created commitments. -/
theorem Relation.output_root_refines_exact_creation {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement) :
    statement.outputNotesRoot =
      env.outputRoot.hash (witness.outputs.map env.noteCommitment.commit) := by
  simpa [outputCommitments] using accepted.outputRootExact

/-! ## 7. Mutation teeth and honest collision reductions -/

/-- With a fixed witness, changing any full-nullifier limb is refused structurally. -/
theorem Relation.refuses_changed_nullifier {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement)
    {changed : RawNullifierKey} (different : changed ≠ statement.nullifier) :
    ¬ Relation env witness { statement with nullifier := changed } := by
  intro forged
  apply different
  exact forged.nullifierFromSelected.trans accepted.nullifierFromSelected.symm

/-- With a fixed witness, changing any of the sixteen wide binding lanes is refused structurally. -/
theorem Relation.refuses_changed_binding {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement)
    {changed : WideDigest} (different : changed ≠ statement.valueAssetBinding) :
    ¬ Relation env witness { statement with valueAssetBinding := changed } := by
  intro forged
  apply different
  exact forged.bindingFromSelected.trans accepted.bindingFromSelected.symm

/-- A forged non-`+1` post-count cannot satisfy the exact append relation. -/
theorem Relation.refuses_wrong_post_count {env : Environment} {witness : Witness}
    {statement : PublicStatement} (_accepted : Relation env witness statement)
    {changed : ExactState}
    (wrong : changed.count ≠ statement.exactBefore.count + 1) :
    ¬ Relation env witness { statement with exactAfter := changed } := by
  intro forged
  exact wrong forged.exactAppend.countStep

/-- With fixed outputs, changing the output-note root is refused before any hash assumption. -/
theorem Relation.refuses_changed_output_root {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement)
    {changed : Root8} (different : changed ≠ statement.outputNotesRoot) :
    ¬ Relation env witness { statement with outputNotesRoot := changed } := by
  intro forged
  apply different
  exact forged.outputRootExact.trans accepted.outputRootExact.symm

/-- With the complete preimage fixed, changing the consequence digest is refused structurally. -/
theorem Relation.refuses_changed_consequence {env : Environment} {witness : Witness}
    {statement : PublicStatement} (accepted : Relation env witness statement)
    {changed : Root8} (different : changed ≠ statement.consequence) :
    ¬ Relation env witness { statement with consequence := changed } := by
  intro forged
  apply different
  exact forged.consequenceExact.trans accepted.consequenceExact.symm

/-- If two distinct selected value/asset openings are accepted under the same wide digest, the
result is exactly a collision in the canonical field transcript hash. -/
theorem distinct_selected_openings_same_binding_reduce_to_collision
    {env : Environment} {leftWitness rightWitness : Witness}
    {leftPublic rightPublic : PublicStatement}
    (leftAccepted : Relation env leftWitness leftPublic)
    (rightAccepted : Relation env rightWitness rightPublic)
    (different : leftWitness.selected.note.valueAsset ≠ rightWitness.selected.note.valueAsset)
    (sameBinding : leftPublic.valueAssetBinding = rightPublic.valueAssetBinding) :
    HashCollision env.wide
      (fieldTranscript .valueBinding leftWitness.selected.note.valueAsset)
      (fieldTranscript .valueBinding rightWitness.selected.note.valueAsset) := by
  apply equivocation_reduces_to_hash_collision env.wide (Or.inr different)
  rw [← leftAccepted.bindingFromSelected, ← rightAccepted.bindingFromSelected]
  exact sameBinding

/-- Two different exact output-commitment lists with the same accepted output root exhibit the
precise output-root collision event. -/
theorem different_output_commitments_same_root_reduce_to_collision
    {env : Environment} {leftWitness rightWitness : Witness}
    {leftPublic rightPublic : PublicStatement}
    (leftAccepted : Relation env leftWitness leftPublic)
    (rightAccepted : Relation env rightWitness rightPublic)
    (different : outputCommitments env.noteCommitment leftWitness ≠
      outputCommitments env.noteCommitment rightWitness)
    (sameRoot : leftPublic.outputNotesRoot = rightPublic.outputNotesRoot) :
    OutputRootCollision env.outputRoot
      (outputCommitments env.noteCommitment leftWitness)
      (outputCommitments env.noteCommitment rightWitness) := by
  refine ⟨different, ?_⟩
  rw [← leftAccepted.outputRootExact, ← rightAccepted.outputRootExact]
  exact sameRoot

/-- Distinct FXC4 semantic preimages with the same accepted consequence exhibit the exact
consequence-hash collision event. -/
theorem different_consequence_preimages_same_digest_reduce_to_collision
    {env : Environment} {leftWitness rightWitness : Witness}
    {leftPublic rightPublic : PublicStatement}
    (leftAccepted : Relation env leftWitness leftPublic)
    (rightAccepted : Relation env rightWitness rightPublic)
    (different : consequencePreimage leftPublic leftWitness ≠
      consequencePreimage rightPublic rightWitness)
    (sameDigest : leftPublic.consequence = rightPublic.consequence) :
    ConsequenceCollision env.consequence
      (consequencePreimage leftPublic leftWitness)
      (consequencePreimage rightPublic rightWitness) := by
  refine ⟨different, ?_⟩
  rw [← leftAccepted.consequenceExact, ← rightAccepted.consequenceExact]
  exact sameDigest

/-! ## 8. Fixed relation / verifier-key refinement seam -/

/-- A future deployed verifier contract for one fixed relation ID and one fixed verifier-key digest.
`knowledgeSound` is an explicit cryptographic/proof-engineering obligation: this module neither
constructs it nor derives it from FRI parameters. -/
structure PinnedVerifierContract (env : Environment)
    (expectedRelationId expectedVerifierKey : List UInt8) where
  relationId : List UInt8
  verifierKey : List UInt8
  relationPinned : relationId = expectedRelationId
  verifierKeyPinned : verifierKey = expectedVerifierKey
  accepts : PublicStatement -> Prop
  knowledgeSound : forall statement, accepts statement -> exists witness, Relation env witness statement

/-- Every statement accepted by a sound pinned verifier has a semantic apex witness. -/
theorem PinnedVerifierContract.accepted_refines_relation
    {env : Environment} {relationId verifierKey : List UInt8}
    (contract : PinnedVerifierContract env relationId verifierKey)
    {statement : PublicStatement} (accepted : contract.accepts statement) :
    exists witness, Relation env witness statement :=
  contract.knowledgeSound statement accepted

/-- Consequently, every pinned-verifier acceptance advances the exact accumulator count by one. -/
theorem PinnedVerifierContract.accepted_count_advances
    {env : Environment} {relationId verifierKey : List UInt8}
    (contract : PinnedVerifierContract env relationId verifierKey)
    {statement : PublicStatement} (accepted : contract.accepts statement) :
    statement.exactAfter.count = statement.exactBefore.count + 1 := by
  obtain ⟨witness, sound⟩ := contract.knowledgeSound statement accepted
  exact sound.exact_count_advances

/-- Every pinned-verifier acceptance has a nonempty, exactly rooted output-note creation list. -/
theorem PinnedVerifierContract.accepted_has_exact_outputs
    {env : Environment} {relationId verifierKey : List UInt8}
    (contract : PinnedVerifierContract env relationId verifierKey)
    {statement : PublicStatement} (accepted : contract.accepts statement) :
    exists witness, Relation env witness statement /\
      0 < witness.outputs.length /\
      statement.outputNotesRoot =
        env.outputRoot.hash (witness.outputs.map env.noteCommitment.commit) := by
  obtain ⟨witness, sound⟩ := contract.knowledgeSound statement accepted
  exact ⟨witness, sound, sound.output_exists, sound.output_root_refines_exact_creation⟩

/-! ## Axiom audit -/

#assert_axioms derivedNullifierWords_eq_iff
#assert_axioms distinct_nullifier_preimages_same_key_reduce_to_collision
#assert_axioms distinct_note_openings_same_commitment_reduce_to_collision
#assert_axioms Relation.full_nullifier_words
#assert_axioms Relation.full_nullifier_canonical
#assert_axioms Relation.exact_count_advances
#assert_axioms Relation.conserves_asset
#assert_axioms Relation.refines_fixed_consequence_rule
#assert_axioms Relation.refuses_changed_nullifier
#assert_axioms Relation.refuses_changed_binding
#assert_axioms Relation.refuses_wrong_post_count
#assert_axioms Relation.refuses_changed_output_root
#assert_axioms Relation.refuses_changed_consequence
#assert_axioms distinct_selected_openings_same_binding_reduce_to_collision
#assert_axioms different_output_commitments_same_root_reduce_to_collision
#assert_axioms different_consequence_preimages_same_digest_reduce_to_collision
#assert_axioms PinnedVerifierContract.accepted_count_advances
#assert_axioms PinnedVerifierContract.accepted_has_exact_outputs

end Dregg2.Circuit.ShieldedExactApexV4
