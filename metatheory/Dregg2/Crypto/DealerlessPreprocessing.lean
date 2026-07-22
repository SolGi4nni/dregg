/-
# Dealerless preprocessing: exact algebraic and state-machine laws

This file isolates the information-theoretic core needed to replace the
`fhegg-fhe` preprocessing dealer.  It deliberately proves only facts Lean can
state without a network or computational-adversary model:

* a roster-indexed family of GF(2) word shares reconstructs one global MAC key;
* after every share but one is fixed, choosing the missing share is a bijection
  onto global keys (equivalently, every target key has exactly one completion);
* an accepted commit/reveal receipt is bound to one session, manifest, and
  complete roster, and injective openings make its roster reveals unique;
* consuming an accepted correlation preserves its immutable context registry
  and marks its identifier used, so replay cannot relabel the correlation.

These are not claims about DKG, transport, equivocation resistance, liveness,
uniform random sampling, or computational commitment hiding/binding.  A live
protocol must discharge those boundaries separately.  In particular, the
commitment theorem below takes exact per-context injectivity as a hypothesis;
it does not disguise hash collision resistance as mathematical injectivity.
-/

import Mathlib
import Dregg2.Tactics
import Dregg2.Crypto.BinaryTripleSacrifice

namespace Dregg2.Crypto.DealerlessPreprocessing

open scoped BigOperators

/-! ## 1. Roster-indexed GF(2) MAC-key shares -/

/-- A width-`w` MAC-key word over GF(2).  Addition is componentwise XOR. -/
abbrev KeyWord (w : Nat) := Fin w → ZMod 2

/-- The global key reconstructed by folding every roster-indexed share. -/
def globalAlpha {parties width : Nat} (shares : Fin parties → KeyWord width) : KeyWord width :=
  ∑ i, shares i

/-- The fold visible to an observer missing party `hidden`'s share. -/
def visibleAlpha {parties width : Nat} (shares : Fin parties → KeyWord width)
    (hidden : Fin parties) : KeyWord width :=
  ∑ i ∈ Finset.univ.erase hidden, shares i

/-- Reconstruction really is the hidden share plus the complete visible fold. -/
theorem globalAlpha_eq_hidden_add_visible {parties width : Nat}
    (shares : Fin parties → KeyWord width) (hidden : Fin parties) :
    globalAlpha shares = shares hidden + visibleAlpha shares hidden := by
  have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin parties)))
    (f := shares) (Finset.mem_univ hidden)
  unfold globalAlpha visibleAlpha
  rw [← h]
  exact add_comm _ _

/-- With the visible fold fixed, the missing share translates bijectively onto
all possible global keys.  This is the exact one-time-pad algebra: it is a
bijection statement, not a computational hiding assumption. -/
def missingShareEquiv {width : Nat} (visible : KeyWord width) :
    KeyWord width ≃ KeyWord width where
  toFun missing := missing + visible
  invFun alpha := alpha - visible
  left_inv missing := by simp
  right_inv alpha := by simp

/-- Every target global key has exactly one missing-share completion once all
other roster shares are fixed. -/
theorem existsUnique_missing_share_for_global {parties width : Nat}
    (shares : Fin parties → KeyWord width) (hidden : Fin parties) (alpha : KeyWord width) :
    ∃! missing : KeyWord width, missing + visibleAlpha shares hidden = alpha := by
  refine ⟨alpha - visibleAlpha shares hidden, ?_, ?_⟩
  · simp
  · intro missing hmissing
    exact (eq_sub_iff_add_eq.mpr hmissing)

/-- Pointwise form of missing-share non-reconstruction: for any candidate
global key there is a unique hidden share realizing it while the entire visible
roster fold remains unchanged. -/
theorem missing_share_relabels_global_uniquely {parties width : Nat}
    (shares : Fin parties → KeyWord width) (hidden : Fin parties)
    (alpha' : KeyWord width) :
    ∃! missing' : KeyWord width,
      missing' + visibleAlpha shares hidden = alpha' :=
  existsUnique_missing_share_for_global shares hidden alpha'

/-- Updating the hidden roster entry realizes exactly the bijection above: the
fold of the completed roster is `missing + visibleAlpha`. -/
theorem globalAlpha_update_hidden {parties width : Nat}
    (shares : Fin parties → KeyWord width) (hidden : Fin parties) (missing : KeyWord width) :
    globalAlpha (Function.update shares hidden missing) =
      missing + visibleAlpha shares hidden := by
  rw [globalAlpha_eq_hidden_add_visible]
  have hvis :
      visibleAlpha (Function.update shares hidden missing) hidden = visibleAlpha shares hidden := by
    unfold visibleAlpha
    apply Finset.sum_congr rfl
    intro i hi
    have hine : i ≠ hidden := Finset.ne_of_mem_erase hi
    exact Function.update_of_ne hine missing shares
  rw [Function.update_self, hvis]

/-! ## 2. Exact binary algebra for threshold-BFV triple output shares -/

/-- The integer polynomial implementing XOR on canonical binary plaintexts.
Unlike ordinary ring addition, this remains XOR in odd characteristic. -/
def xorZ {R : Type*} [CommRing R] (x y : R) : R :=
  x + y - 2 * x * y

/-- Canonical embedding of a Boolean as the ring elements zero and one. -/
def bitIn {R : Type*} [CommRing R] : Bool → R
  | false => 0
  | true => 1

/-- `xorZ` agrees exactly with Boolean XOR on canonical 0/1 inputs over every
commutative ring.  This is the direct theorem-friendly correspondence for a
BFV plaintext implementation of the runtime Boolean operation. -/
theorem xorZ_bitIn_eq_bitIn_xor {R : Type*} [CommRing R] (x y : Bool) :
    xorZ (bitIn x : R) (bitIn y) = bitIn (x.xor y) := by
  cases x <;> cases y <;> simp [xorZ, bitIn, one_add_one_eq_two]

/-- Ring multiplication agrees with Boolean AND on canonical bits. -/
theorem mul_bitIn_eq_bitIn_and {R : Type*} [CommRing R] (x y : Bool) :
    (bitIn x : R) * bitIn y = bitIn (x && y) := by
  cases x <;> cases y <;> simp [bitIn]

/-- Global binary inputs and product for a two-party XOR sharing. -/
def tripleProduct2 (a₀ a₁ b₀ b₁ : Bool) : Bool :=
  (a₀.xor a₁) && (b₀.xor b₁)

/-- Public masked product opening: `z = c XOR r`, where the global mask is the
XOR of the two private mask shares. -/
def maskedProductOpening2 (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) : Bool :=
  (tripleProduct2 a₀ a₁ b₀ b₁).xor (r₀.xor r₁)

/-- Party zero absorbs the public masked opening into its private mask share. -/
def outputShareZero2 (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) : Bool :=
  r₀.xor (maskedProductOpening2 a₀ a₁ b₀ b₁ r₀ r₁)

/-- The other party keeps its mask share. -/
def outputShareOne2 (_a₀ _a₁ _b₀ _b₁ _r₀ r₁ : Bool) : Bool := r₁

/-- Exact dealerless triple reconstruction.  If `a` and `b` are XOR-shared,
the masked opening `z = c XOR r` followed by `c₀ = r₀ XOR z`, `c₁ = r₁`
produces shares whose XOR is `(a₀ XOR a₁) AND (b₀ XOR b₁)`. -/
theorem masked_two_party_product_shares_reconstruct
    (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) :
    (outputShareZero2 a₀ a₁ b₀ b₁ r₀ r₁).xor
        (outputShareOne2 a₀ a₁ b₀ b₁ r₀ r₁) =
      tripleProduct2 a₀ a₁ b₀ b₁ := by
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> cases r₀ <;> cases r₁ <;> decide

/-- The same reconstruction transported to the BFV plaintext polynomial: the
polynomial XOR of the two canonical output shares equals the canonical product
bit.  No characteristic-two shortcut is used. -/
theorem masked_two_party_product_shares_reconstruct_xorZ
    {R : Type*} [CommRing R] (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) :
    xorZ
        (bitIn (outputShareZero2 a₀ a₁ b₀ b₁ r₀ r₁) : R)
        (bitIn (outputShareOne2 a₀ a₁ b₀ b₁ r₀ r₁) : R) =
      bitIn (tripleProduct2 a₀ a₁ b₀ b₁) := by
  rw [xorZ_bitIn_eq_bitIn_xor, masked_two_party_product_shares_reconstruct]

/-- Odd-modulus refusal tooth: adding two local `1` shares gives `2`, while
their XOR is `0`.  Therefore a threshold-BFV implementation cannot replace
`xorZ` with ordinary plaintext addition. -/
theorem ordinary_addition_is_not_xor_mod_five :
    ((bitIn true : ZMod 5) + bitIn true) ≠ bitIn (true.xor true) := by
  decide

/-- The polynomial has the correct result on the same odd-modulus tooth. -/
theorem xorZ_handles_double_one_mod_five :
    xorZ (bitIn true : ZMod 5) (bitIn true) = bitIn (true.xor true) :=
  xorZ_bitIn_eq_bitIn_xor true true

/-! ### Composition with the existing sacrifice theorem -/

namespace SacrificeBridge

open Dregg2.Crypto.BinaryTripleSacrifice

/-- The masked construction packaged as the exact `Triple` consumed by the
existing sacrifice layer. -/
def constructedTriple2 (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) : Triple where
  a := a₀.xor a₁
  b := b₀.xor b₁
  c := (outputShareZero2 a₀ a₁ b₀ b₁ r₀ r₁).xor
    (outputShareOne2 a₀ a₁ b₀ b₁ r₀ r₁)

/-- The dealerless masked construction inhabits the exact validity relation
checked by `BinaryTripleSacrifice`; it is not a parallel triple notion. -/
theorem constructedTriple2_valid (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) :
    Valid (constructedTriple2 a₀ a₁ b₀ b₁ r₀ r₁) := by
  unfold Valid error constructedTriple2
  rw [masked_two_party_product_shares_reconstruct]
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> decide

/-- A constructed candidate paired with any other valid candidate passes the
already-proved sacrifice checker for either challenge bit. -/
theorem constructedTriple2_passes_sacrifice
    (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) (sacrificed : Triple)
    (hsacrificed : Valid sacrificed) (challenge : Bool) :
    check challenge (constructedTriple2 a₀ a₁ b₀ b₁ r₀ r₁) sacrificed = false :=
  valid_pair_accepts (constructedTriple2_valid a₀ a₁ b₀ b₁ r₀ r₁) hsacrificed challenge

end SacrificeBridge

/-! ### Executable byte KAT boundary

These literal byte arrays give Rust a small independent drift boundary.  The
first pins the complete Boolean truth table for the integer XOR polynomial;
the second pins masked-opening/output-share bytes for four representative
share layouts.  They are compile-time evaluations, not security theorems. -/

def boolByte (b : Bool) : UInt8 := if b then 1 else 0

def xorZByte (x y : Bool) : UInt8 :=
  UInt8.ofNat (Int.toNat (xorZ (bitIn x : Int) (bitIn y)))

/-- Row order: `(0,0), (0,1), (1,0), (1,1)`. -/
def xorZTruthTableBytes : Array UInt8 :=
  #[xorZByte false false, xorZByte false true, xorZByte true false, xorZByte true true]

#guard xorZTruthTableBytes == #[0, 1, 1, 0]

/-- One KAT row encoded as `[z,c0,c1,c0 XOR c1,c]`. -/
def maskedTripleKatRow (a₀ a₁ b₀ b₁ r₀ r₁ : Bool) : Array UInt8 :=
  let z := maskedProductOpening2 a₀ a₁ b₀ b₁ r₀ r₁
  let c₀ := outputShareZero2 a₀ a₁ b₀ b₁ r₀ r₁
  let c₁ := outputShareOne2 a₀ a₁ b₀ b₁ r₀ r₁
  #[boolByte z, boolByte c₀, boolByte c₁, boolByte (c₀.xor c₁),
    boolByte (tripleProduct2 a₀ a₁ b₀ b₁)]

def maskedTripleKatBytes : Array (Array UInt8) :=
  #[maskedTripleKatRow false false false false false false,
    maskedTripleKatRow true false true false false false,
    maskedTripleKatRow true true true false true false,
    maskedTripleKatRow true false true false true true]

#guard maskedTripleKatBytes ==
  #[#[0, 0, 0, 0, 0], #[1, 1, 0, 1, 1],
    #[1, 0, 0, 0, 0], #[1, 0, 1, 1, 1]]

/-! ## 3. Manifest-bound, complete-roster commit/reveal -/

/-- Everything that must be fixed before the beacon reveals are accepted. -/
structure CeremonyContext (Party Session Manifest : Type*) where
  session : Session
  manifest : Manifest
  roster : Finset Party

/-- A transcript is total over the context roster by construction.  Values for
non-roster parties cannot be supplied because every field requires membership
evidence. -/
structure RosterTranscript {Party Session Manifest : Type*}
    (ctx : CeremonyContext Party Session Manifest)
    (Commitment Reveal : Type*) where
  commitments : ∀ p : Party, p ∈ ctx.roster → Commitment
  reveals : ∀ p : Party, p ∈ ctx.roster → Reveal

/-- A wire receipt repeats the context binding and carries a declared presence
set.  Acceptance below requires that set to equal the complete roster. -/
structure BeaconReceipt {Party Session Manifest : Type*}
    (ctx : CeremonyContext Party Session Manifest)
    (Commitment Reveal : Type*) where
  claimedSession : Session
  claimedManifest : Manifest
  claimedRoster : Finset Party
  present : Finset Party
  transcript : RosterTranscript ctx Commitment Reveal

/-- Exact opening relation for every roster member.  `commit` receives the
whole context, so session and manifest are domain-separated at the interface. -/
def Opens {Party Session Manifest Commitment Reveal : Type*}
    (commit : CeremonyContext Party Session Manifest → Party → Reveal → Commitment)
    (ctx : CeremonyContext Party Session Manifest)
    (t : RosterTranscript ctx Commitment Reveal) : Prop :=
  ∀ p hp, commit ctx p (t.reveals p hp) = t.commitments p hp

/-- Fail-closed acceptance: exact context fields, exact complete roster, then
all openings. -/
def BeaconAccepted {Party Session Manifest Commitment Reveal : Type*}
    (commit : CeremonyContext Party Session Manifest → Party → Reveal → Commitment)
    (ctx : CeremonyContext Party Session Manifest)
    (r : BeaconReceipt ctx Commitment Reveal) : Prop :=
  r.claimedSession = ctx.session ∧
  r.claimedManifest = ctx.manifest ∧
  r.claimedRoster = ctx.roster ∧
  r.present = ctx.roster ∧
  Opens commit ctx r.transcript

/-- Acceptance binds the session exactly. -/
theorem accepted_binds_session {Party Session Manifest Commitment Reveal : Type*}
    {commit : CeremonyContext Party Session Manifest → Party → Reveal → Commitment}
    {ctx : CeremonyContext Party Session Manifest}
    {r : BeaconReceipt ctx Commitment Reveal}
    (h : BeaconAccepted commit ctx r) : r.claimedSession = ctx.session := h.1

/-- Acceptance binds the candidate/MAC manifest exactly. -/
theorem accepted_binds_manifest {Party Session Manifest Commitment Reveal : Type*}
    {commit : CeremonyContext Party Session Manifest → Party → Reveal → Commitment}
    {ctx : CeremonyContext Party Session Manifest}
    {r : BeaconReceipt ctx Commitment Reveal}
    (h : BeaconAccepted commit ctx r) : r.claimedManifest = ctx.manifest := h.2.1

/-- Acceptance admits neither a subset nor a superset: the declared presence
set is exactly the context roster. -/
theorem accepted_has_complete_roster {Party Session Manifest Commitment Reveal : Type*}
    {commit : CeremonyContext Party Session Manifest → Party → Reveal → Commitment}
    {ctx : CeremonyContext Party Session Manifest}
    {r : BeaconReceipt ctx Commitment Reveal}
    (h : BeaconAccepted commit ctx r) : r.present = ctx.roster := h.2.2.2.1

/-- A receipt carrying a different session is refused. -/
theorem wrong_session_refused {Party Session Manifest Commitment Reveal : Type*}
    {commit : CeremonyContext Party Session Manifest → Party → Reveal → Commitment}
    {ctx : CeremonyContext Party Session Manifest}
    {r : BeaconReceipt ctx Commitment Reveal}
    (hne : r.claimedSession ≠ ctx.session) : ¬ BeaconAccepted commit ctx r :=
  fun h => hne (accepted_binds_session h)

/-- A receipt carrying a different manifest is refused. -/
theorem wrong_manifest_refused {Party Session Manifest Commitment Reveal : Type*}
    {commit : CeremonyContext Party Session Manifest → Party → Reveal → Commitment}
    {ctx : CeremonyContext Party Session Manifest}
    {r : BeaconReceipt ctx Commitment Reveal}
    (hne : r.claimedManifest ≠ ctx.manifest) : ¬ BeaconAccepted commit ctx r :=
  fun h => hne (accepted_binds_manifest h)

/-- Two accepted complete-roster transcripts carrying identical commitments
have identical roster reveals, provided each context/party commitment map is
mathematically injective.  The hypothesis is intentionally exact and visible;
a deployed hash commitment supplies only a computational analogue. -/
theorem accepted_complete_roster_reveals_unique
    {Party Session Manifest Commitment Reveal : Type*}
    (commit : CeremonyContext Party Session Manifest → Party → Reveal → Commitment)
    (hinjective : ∀ ctx p, Function.Injective (commit ctx p))
    (ctx : CeremonyContext Party Session Manifest)
    (r₁ r₂ : BeaconReceipt ctx Commitment Reveal)
    (ha₁ : BeaconAccepted commit ctx r₁)
    (ha₂ : BeaconAccepted commit ctx r₂)
    (hcommit : ∀ p hp₁ hp₂,
      r₁.transcript.commitments p hp₁ = r₂.transcript.commitments p hp₂) :
    ∀ p hp₁ hp₂, r₁.transcript.reveals p hp₁ = r₂.transcript.reveals p hp₂ := by
  intro p hp₁ hp₂
  apply hinjective ctx p
  rw [ha₁.2.2.2.2 p hp₁, ha₂.2.2.2.2 p hp₂]
  exact hcommit p hp₁ hp₂

/-- Deterministic beacon output over the total roster reveal function. -/
def beaconOutput {Party Session Manifest Commitment Reveal Output : Type*}
    {ctx : CeremonyContext Party Session Manifest}
    (combine : (∀ p : Party, p ∈ ctx.roster → Reveal) → Output)
    (r : BeaconReceipt ctx Commitment Reveal) : Output :=
  combine r.transcript.reveals

/-- Complete-roster uniqueness lifts through any deterministic combiner: same
bound commitments imply the same accepted beacon output. -/
theorem accepted_same_commitments_same_output
    {Party Session Manifest Commitment Reveal Output : Type*}
    (commit : CeremonyContext Party Session Manifest → Party → Reveal → Commitment)
    (hinjective : ∀ ctx p, Function.Injective (commit ctx p))
    (ctx : CeremonyContext Party Session Manifest)
    (combine : (∀ p : Party, p ∈ ctx.roster → Reveal) → Output)
    (r₁ r₂ : BeaconReceipt ctx Commitment Reveal)
    (ha₁ : BeaconAccepted commit ctx r₁)
    (ha₂ : BeaconAccepted commit ctx r₂)
    (hcommit : ∀ p hp₁ hp₂,
      r₁.transcript.commitments p hp₁ = r₂.transcript.commitments p hp₂) :
    beaconOutput combine r₁ = beaconOutput combine r₂ := by
  apply congrArg combine
  funext p hp
  exact accepted_complete_roster_reveals_unique commit hinjective ctx r₁ r₂
    ha₁ ha₂ hcommit p hp hp

/-! ## 4. Context-preserving one-time correlation custody -/

/-- An accepted preprocessing correlation carries an immutable identifier and
context (session, manifest, roster digest, roots, etc. can inhabit `Context`). -/
structure Correlation (Id Context Payload : Type*) where
  id : Id
  context : Context
  payload : Payload

/-- Durable custody state: the accepted identifier-to-context registry and the
set of already consumed identifiers. -/
structure CustodyState (Id Context : Type*) where
  acceptedContext : Id → Option Context
  used : Finset Id

/-- Consume exactly once and only under the artifact's registered immutable
context.  Success changes only the use set. -/
def consume {Id Context Payload : Type*} [DecidableEq Id] [DecidableEq Context]
    (s : CustodyState Id Context) (c : Correlation Id Context Payload)
    (presentedContext : Context) : Option (CustodyState Id Context) :=
  if s.acceptedContext c.id = some c.context ∧
      presentedContext = c.context ∧ c.id ∉ s.used then
    some { acceptedContext := s.acceptedContext, used := insert c.id s.used }
  else
    none

/-- Any successful consumption used exactly the correlation's bound context. -/
theorem consume_success_context_pinned
    {Id Context Payload : Type*} [DecidableEq Id] [DecidableEq Context]
    {s s' : CustodyState Id Context} {c : Correlation Id Context Payload}
    {presentedContext : Context}
    (h : consume s c presentedContext = some s') :
    presentedContext = c.context := by
  unfold consume at h
  split at h
  · rename_i hgate
    exact hgate.2.1
  · contradiction

/-- The accepted identifier-to-context registry is byte-for-byte unchanged by
successful consumption.  In particular, consumption cannot relabel this or
any other correlation. -/
theorem consume_success_preserves_context_registry
    {Id Context Payload : Type*} [DecidableEq Id] [DecidableEq Context]
    {s s' : CustodyState Id Context} {c : Correlation Id Context Payload}
    {presentedContext : Context}
    (h : consume s c presentedContext = some s') :
    s'.acceptedContext = s.acceptedContext := by
  unfold consume at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    rfl
  · contradiction

/-- Successful consumption durably marks the accepted identifier used. -/
theorem consume_success_marks_used
    {Id Context Payload : Type*} [DecidableEq Id] [DecidableEq Context]
    {s s' : CustodyState Id Context} {c : Correlation Id Context Payload}
    {presentedContext : Context}
    (h : consume s c presentedContext = some s') : c.id ∈ s'.used := by
  unfold consume at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    simp
  · contradiction

/-- Once a successful transition has consumed an identifier, the exact same
correlation cannot be consumed again under any presented context. -/
theorem consume_success_refuses_replay
    {Id Context Payload : Type*} [DecidableEq Id] [DecidableEq Context]
    {s s' : CustodyState Id Context} {c : Correlation Id Context Payload}
    {presentedContext : Context}
    (h : consume s c presentedContext = some s')
    (nextContext : Context) : consume s' c nextContext = none := by
  unfold consume
  simp [consume_success_marks_used h]

#assert_axioms globalAlpha_eq_hidden_add_visible
#assert_axioms missingShareEquiv
#assert_axioms existsUnique_missing_share_for_global
#assert_axioms missing_share_relabels_global_uniquely
#assert_axioms globalAlpha_update_hidden
#assert_axioms xorZ_bitIn_eq_bitIn_xor
#assert_axioms mul_bitIn_eq_bitIn_and
#assert_axioms masked_two_party_product_shares_reconstruct
#assert_axioms masked_two_party_product_shares_reconstruct_xorZ
#assert_axioms ordinary_addition_is_not_xor_mod_five
#assert_axioms xorZ_handles_double_one_mod_five
#assert_axioms SacrificeBridge.constructedTriple2_valid
#assert_axioms SacrificeBridge.constructedTriple2_passes_sacrifice
#assert_axioms accepted_binds_session
#assert_axioms accepted_binds_manifest
#assert_axioms accepted_has_complete_roster
#assert_axioms wrong_session_refused
#assert_axioms wrong_manifest_refused
#assert_axioms accepted_complete_roster_reveals_unique
#assert_axioms accepted_same_commitments_same_output
#assert_axioms consume_success_context_pinned
#assert_axioms consume_success_preserves_context_registry
#assert_axioms consume_success_marks_used
#assert_axioms consume_success_refuses_replay

end Dregg2.Crypto.DealerlessPreprocessing
