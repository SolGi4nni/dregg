/-
# FHTRI005 party-local formation composition laws

This module is the narrow Lean image of the first two-party FHTRI005 runtime
cut.  It composes three already-separated facts:

1. an ordered, complete roster accepts only exact context-bound openings of
   every party-local candidate vector;
2. exact commitment injectivity makes the accepted local vectors unique for a
   fixed public commitment list; and
3. componentwise XOR reconstruction of locally consistent binary triple
   shares produces `BinaryTripleSacrifice.Valid` candidates.

The verifier is deliberately a list verifier rather than a total-function
idealization, so omission and reordering have executable refusal teeth.  Exact
commitment injectivity remains an explicit mathematical hypothesis: this file
does not turn a compressing runtime hash into an injective function or claim a
computational binding proof.
-/

import Mathlib
import Dregg2.Tactics
import Dregg2.Crypto.DealerlessPreprocessing

namespace Dregg2.Crypto.DealerlessPartyLocalComposition

open Dregg2.Crypto.BinaryTripleSacrifice
open Dregg2.Crypto.DealerlessPreprocessing

/-! ## Party-local candidates and exact ordered formation -/

/-- One party's private XOR share of a binary triple candidate. -/
structure LocalTripleShare where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq, Repr

/-- The exact FHTRI005 public context fixed before local vectors are accepted. -/
structure FormationContext (Party Session Manifest : Type*) where
  session : Session
  manifest : Manifest
  roster : List Party
  candidateCount : Nat
  deriving DecidableEq, Repr

/-- One raw party contribution.  It repeats the whole claimed context so a
cross-session, cross-manifest, or cross-roster substitution is representable
and can be rejected rather than ruled out by its type. -/
structure LocalContribution (Party Session Manifest Commitment : Type*) where
  claimedContext : FormationContext Party Session Manifest
  party : Party
  candidates : List LocalTripleShare
  commitment : Commitment
  deriving DecidableEq, Repr

/-- One local row opens exactly when its context, ordered party position,
vector shape, and commitment all match. -/
def LocalAccepted
    {Party Session Manifest Commitment : Type*}
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) (expected : Party)
    (c : LocalContribution Party Session Manifest Commitment) : Prop :=
  c.claimedContext = ctx ∧
  c.party = expected ∧
  c.candidates.length = ctx.candidateCount ∧
  commit ctx expected c.candidates = c.commitment

/-- Recursive exact-roster verifier.  Only `[]/[]` terminates successfully;
omissions and extras fall into the false cases, and each head must match the
next roster position. -/
def OrderedAccepted
    {Party Session Manifest Commitment : Type*}
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) :
    List Party → List (LocalContribution Party Session Manifest Commitment) → Prop
  | [], [] => True
  | p :: ps, c :: cs => LocalAccepted commit ctx p c ∧ OrderedAccepted commit ctx ps cs
  | _, _ => False

/-- Full formation acceptance additionally requires an unambiguous roster. -/
def FormationAccepted
    {Party Session Manifest Commitment : Type*} [DecidableEq Party]
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest)
    (cs : List (LocalContribution Party Session Manifest Commitment)) : Prop :=
  ctx.roster.Nodup ∧ OrderedAccepted commit ctx ctx.roster cs

/-- Public party/commitment sequence fixed by the formation transcript. -/
def publicCommitments
    {Party Session Manifest Commitment : Type*}
    (cs : List (LocalContribution Party Session Manifest Commitment)) :
    List (Party × Commitment) :=
  cs.map fun c => (c.party, c.commitment)

/-- Private vectors selected by a raw formation transcript. -/
def localCandidateVectors
    {Party Session Manifest Commitment : Type*}
    (cs : List (LocalContribution Party Session Manifest Commitment)) :
    List (List LocalTripleShare) :=
  cs.map (·.candidates)

theorem orderedAccepted_length
    {Party Session Manifest Commitment : Type*}
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) {roster cs}
    (h : OrderedAccepted commit ctx roster cs) : cs.length = roster.length := by
  induction roster generalizing cs with
  | nil => cases cs <;> simp_all [OrderedAccepted]
  | cons p ps ih =>
      cases cs with
      | nil => simp_all [OrderedAccepted]
      | cons c cs =>
          simp only [OrderedAccepted] at h
          simp [ih h.2]

/-- Acceptance has exactly one contribution per roster position. -/
theorem accepted_complete_roster
    {Party Session Manifest Commitment : Type*} [DecidableEq Party]
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) {cs}
    (h : FormationAccepted commit ctx cs) : cs.length = ctx.roster.length :=
  orderedAccepted_length commit ctx h.2

theorem orderedAccepted_parties
    {Party Session Manifest Commitment : Type*}
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) {roster cs}
    (h : OrderedAccepted commit ctx roster cs) : cs.map (·.party) = roster := by
  induction roster generalizing cs with
  | nil => cases cs <;> simp_all [OrderedAccepted]
  | cons p ps ih =>
      cases cs with
      | nil => simp_all [OrderedAccepted]
      | cons c cs =>
          simp only [OrderedAccepted] at h
          simp [h.1.2.1, ih h.2]

/-- Acceptance preserves the caller-specified order exactly; the verifier does
not sort contributions. -/
theorem accepted_parties_eq_ordered_roster
    {Party Session Manifest Commitment : Type*} [DecidableEq Party]
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) {cs}
    (h : FormationAccepted commit ctx cs) : cs.map (·.party) = ctx.roster :=
  orderedAccepted_parties commit ctx h.2

theorem orderedAccepted_contexts
    {Party Session Manifest Commitment : Type*}
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) {roster cs}
    (h : OrderedAccepted commit ctx roster cs) :
    ∀ c ∈ cs, c.claimedContext = ctx := by
  induction roster generalizing cs with
  | nil => cases cs <;> simp_all [OrderedAccepted]
  | cons p ps ih =>
      cases cs with
      | nil => simp_all [OrderedAccepted]
      | cons c cs =>
          simp only [OrderedAccepted] at h
          intro c' hc'
          simp only [List.mem_cons] at hc'
          rcases hc' with hcc | hc'
          · rw [hcc]
            exact h.1.1
          · exact ih h.2 c' hc'

/-- One mismatched claimed context anywhere in the list refutes acceptance. -/
theorem context_mismatch_refused
    {Party Session Manifest Commitment : Type*} [DecidableEq Party]
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) (cs)
    (hbad : ∃ c ∈ cs, c.claimedContext ≠ ctx) :
    ¬ FormationAccepted commit ctx cs := by
  intro hacc
  obtain ⟨c, hc, hne⟩ := hbad
  exact hne (orderedAccepted_contexts commit ctx hacc.2 c hc)

/-- Any omission or extra contribution changes the length and is refused. -/
theorem incomplete_roster_refused
    {Party Session Manifest Commitment : Type*} [DecidableEq Party]
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) (cs)
    (hne : cs.length ≠ ctx.roster.length) :
    ¬ FormationAccepted commit ctx cs :=
  fun h => hne (accepted_complete_roster commit ctx h)

/-- Any reordered party sequence is refused; there is no verifier-side sort. -/
theorem reordered_roster_refused
    {Party Session Manifest Commitment : Type*} [DecidableEq Party]
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (ctx : FormationContext Party Session Manifest) (cs)
    (hne : cs.map (·.party) ≠ ctx.roster) :
    ¬ FormationAccepted commit ctx cs :=
  fun h => hne (accepted_parties_eq_ordered_roster commit ctx h)

/-! ## Unique binding of party-local candidate vectors -/

theorem orderedAccepted_public_binds_local_vectors
    {Party Session Manifest Commitment : Type*}
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (hinjective : ∀ ctx p, Function.Injective (commit ctx p))
    (ctx : FormationContext Party Session Manifest)
    {roster xs ys}
    (hx : OrderedAccepted commit ctx roster xs)
    (hy : OrderedAccepted commit ctx roster ys)
    (hpublic : publicCommitments xs = publicCommitments ys) :
    localCandidateVectors xs = localCandidateVectors ys := by
  induction roster generalizing xs ys with
  | nil =>
      cases xs <;> cases ys <;> simp_all [OrderedAccepted, publicCommitments,
        localCandidateVectors]
  | cons p ps ih =>
      cases xs with
      | nil => simp_all [OrderedAccepted]
      | cons x xs =>
          cases ys with
          | nil => simp_all [OrderedAccepted]
          | cons y ys =>
              simp only [OrderedAccepted] at hx hy
              simp only [publicCommitments, List.map_cons, List.cons.injEq,
                Prod.mk.injEq] at hpublic
              have hcommit : x.commitment = y.commitment := hpublic.1.2
              have hvec : x.candidates = y.candidates := by
                apply hinjective ctx p
                rw [hx.1.2.2.2, hy.1.2.2.2, hcommit]
              have htail : localCandidateVectors xs = localCandidateVectors ys :=
                ih hx.2 hy.2 hpublic.2
              change x.candidates :: localCandidateVectors xs =
                y.candidates :: localCandidateVectors ys
              rw [hvec, htail]

/-- With exact per-context commitment injectivity, an accepted public ordered
commitment list binds one unique vector for every roster party. -/
theorem accepted_public_binds_unique_candidate_vectors
    {Party Session Manifest Commitment : Type*} [DecidableEq Party]
    (commit : FormationContext Party Session Manifest → Party →
      List LocalTripleShare → Commitment)
    (hinjective : ∀ ctx p, Function.Injective (commit ctx p))
    (ctx : FormationContext Party Session Manifest) {xs ys}
    (hx : FormationAccepted commit ctx xs)
    (hy : FormationAccepted commit ctx ys)
    (hpublic : publicCommitments xs = publicCommitments ys) :
    localCandidateVectors xs = localCandidateVectors ys :=
  orderedAccepted_public_binds_local_vectors commit hinjective ctx hx.2 hy.2 hpublic

/-! ## Party-local reconstruction composes with sacrifice validity -/

/-- Componentwise XOR reconstruction into the already-authoritative sacrifice
candidate type. -/
def reconstructTriple (x y : LocalTripleShare) : Triple where
  a := x.a.xor y.a
  b := x.b.xor y.b
  c := x.c.xor y.c

/-- Exact local premise for one reconstructed binary product share. -/
def LocallyConsistent (x y : LocalTripleShare) : Prop :=
  x.c.xor y.c = ((x.a.xor y.a) && (x.b.xor y.b))

/-- Local share consistency is exactly sufficient for the reconstructed triple
to inhabit `BinaryTripleSacrifice.Valid`. -/
theorem reconstructTriple_valid {x y : LocalTripleShare}
    (h : LocallyConsistent x y) : Valid (reconstructTriple x y) := by
  unfold LocallyConsistent at h
  unfold Valid error reconstructTriple
  change (x.c.xor y.c).xor ((x.a.xor y.a) && (x.b.xor y.b)) = false
  rw [h]
  cases x.a <;> cases y.a <;> cases x.b <;> cases y.b <;> decide

/-- Exact two-list reconstruction; malformed unequal tails are discarded, but
the accepted formation shape theorem prevents that case at the protocol seam. -/
def reconstructVector2 : List LocalTripleShare → List LocalTripleShare → List Triple
  | x :: xs, y :: ys => reconstructTriple x y :: reconstructVector2 xs ys
  | _, _ => []

/-- A pointwise-consistent pair of party-local vectors reconstructs only valid
sacrifice candidates. -/
theorem reconstructVector2_forall_valid {xs ys : List LocalTripleShare}
    (h : List.Forall₂ LocallyConsistent xs ys) :
    (reconstructVector2 xs ys).Forall Valid := by
  induction h with
  | nil => simp [reconstructVector2]
  | cons hxy _ ih =>
      simp [reconstructVector2, reconstructTriple_valid hxy, ih]

/-- Party-local view of the exact masked BFV construction from the predecessor
module. -/
def maskedLocalShareZero2 (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) : LocalTripleShare where
  a := a₀
  b := b₀
  c := outputShareZero2 a₀ a₁ b₀ b₁ r₀ r₁

def maskedLocalShareOne2 (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) : LocalTripleShare where
  a := a₁
  b := b₁
  c := outputShareOne2 a₀ a₁ b₀ b₁ r₀ r₁

/-- The party-local reconstruction is definitionally the exact candidate
already bridged into `BinaryTripleSacrifice` by `DealerlessPreprocessing`. -/
theorem reconstruct_masked_eq_constructedTriple2 (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) :
    reconstructTriple
        (maskedLocalShareZero2 a₀ a₁ b₀ b₁ r₀ r₁)
        (maskedLocalShareOne2 a₀ a₁ b₀ b₁ r₀ r₁) =
      SacrificeBridge.constructedTriple2 a₀ a₁ b₀ b₁ r₀ r₁ := rfl

theorem reconstruct_masked_valid (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) :
    Valid (reconstructTriple
      (maskedLocalShareZero2 a₀ a₁ b₀ b₁ r₀ r₁)
      (maskedLocalShareOne2 a₀ a₁ b₀ b₁ r₀ r₁)) := by
  rw [reconstruct_masked_eq_constructedTriple2]
  exact SacrificeBridge.constructedTriple2_valid a₀ a₁ b₀ b₁ r₀ r₁

/-! ## Executable refusal and algebra teeth -/

namespace Demo

def ctx : FormationContext Bool Bool Bool where
  session := false
  manifest := true
  roster := [false, true]
  candidateCount := 1

def commit (_ : FormationContext Bool Bool Bool) (_ : Bool)
    (xs : List LocalTripleShare) : List LocalTripleShare := xs

def share0 : LocalTripleShare := ⟨true, false, false⟩
def share1 : LocalTripleShare := ⟨false, true, false⟩

def contribution (p : Bool) (s : LocalTripleShare) :
    LocalContribution Bool Bool Bool (List LocalTripleShare) where
  claimedContext := ctx
  party := p
  candidates := [s]
  commitment := commit ctx p [s]

def good := [contribution false share0, contribution true share1]

def wrongContextContribution :
    LocalContribution Bool Bool Bool (List LocalTripleShare) :=
  { contribution false share0 with
    claimedContext := { ctx with session := true } }

def localAcceptsB (expected : Bool)
    (c : LocalContribution Bool Bool Bool (List LocalTripleShare)) : Bool :=
  decide (c.claimedContext = ctx) && decide (c.party = expected) &&
    decide (c.candidates.length = ctx.candidateCount) &&
    decide (commit ctx expected c.candidates = c.commitment)

def orderedAcceptsB : List Bool →
    List (LocalContribution Bool Bool Bool (List LocalTripleShare)) → Bool
  | [], [] => true
  | p :: ps, c :: cs => localAcceptsB p c && orderedAcceptsB ps cs
  | _, _ => false

def acceptsB (cs : List (LocalContribution Bool Bool Bool (List LocalTripleShare))) : Bool :=
  decide ctx.roster.Nodup && orderedAcceptsB ctx.roster cs

/-- The executable row check is exactly the proposition used by the proofs. -/
theorem localAcceptsB_iff (expected : Bool)
    (c : LocalContribution Bool Bool Bool (List LocalTripleShare)) :
    localAcceptsB expected c = true ↔ LocalAccepted commit ctx expected c := by
  simp [localAcceptsB, LocalAccepted, and_assoc]

/-- The executable recursive list check is not a parallel specification: it
decides `OrderedAccepted` exactly. -/
theorem orderedAcceptsB_iff (roster : List Bool)
    (cs : List (LocalContribution Bool Bool Bool (List LocalTripleShare))) :
    orderedAcceptsB roster cs = true ↔ OrderedAccepted commit ctx roster cs := by
  induction roster generalizing cs with
  | nil => cases cs <;> simp [orderedAcceptsB, OrderedAccepted]
  | cons p ps ih =>
      cases cs with
      | nil => simp [orderedAcceptsB, OrderedAccepted]
      | cons c cs =>
          simp [orderedAcceptsB, OrderedAccepted, localAcceptsB_iff, ih]

/-- Consequently every executable KAT below runs the same complete-roster
formation verifier whose refusal laws are theorem-pinned above. -/
theorem acceptsB_iff (cs : List (LocalContribution Bool Bool Bool (List LocalTripleShare))) :
    acceptsB cs = true ↔ FormationAccepted commit ctx cs := by
  simp [acceptsB, FormationAccepted, orderedAcceptsB_iff]

#guard acceptsB good
#guard !(acceptsB [contribution false share0])
#guard !(acceptsB good.reverse)
#guard !(acceptsB [wrongContextContribution, contribution true share1])

/-- Cross terms are load-bearing: both parties can set their local `cᵢ` to the
local product `aᵢ∧bᵢ` and still reconstruct an invalid global triple. -/
theorem diagonal_products_only_can_be_invalid :
    ¬ Valid (reconstructTriple share0 share1) := by
  simp [Valid, error, reconstructTriple, share0, share1]

#guard error (reconstructTriple share0 share1)

end Demo

#assert_axioms accepted_complete_roster
#assert_axioms accepted_parties_eq_ordered_roster
#assert_axioms context_mismatch_refused
#assert_axioms incomplete_roster_refused
#assert_axioms reordered_roster_refused
#assert_axioms accepted_public_binds_unique_candidate_vectors
#assert_axioms reconstructTriple_valid
#assert_axioms reconstructVector2_forall_valid
#assert_axioms reconstruct_masked_eq_constructedTriple2
#assert_axioms reconstruct_masked_valid
#assert_axioms Demo.diagonal_products_only_can_be_invalid

end Dregg2.Crypto.DealerlessPartyLocalComposition
