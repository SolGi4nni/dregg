/-
# Market.PrivateBookBfvBindingAir — curve-free BFV/private-root AIR relation

This module is the first Lean-first replacement rung for the Ristretto
Bulletproof which currently joins the Dark Bazaar private root to four BFV
ciphertexts.  It fixes the deployed `N=4096`, three-RNS-prime, four-order,
two-polynomial public-key encryption shape and states the relation over every
coefficient -- no randomized compression and no sampled coefficients.

The public key and ciphertext are transported as canonical little-endian
two-`u32` limbs.  An accepting trace must:

* bind the complete BFV identity (degree, plaintext modulus, all three RNS
  moduli, key digest, and codec digest) to the full public-key coefficients;
* bind one hidden book witness to the public private-root/clearing statement;
* range every encryption coefficient in the exact `[-32,31]` envelope;
* expose the complete NTT-product stage and refine it to the schoolbook
  negacyclic product from `WgpuBfvNttSpec`; and
* satisfy both a quotient/carry equation over the integers and the resulting
  exact RNS encryption equation for every order, polynomial, modulus, and
  coefficient.

The main theorem transports `Satisfied` to `ExactPrivateBookBfvOpening`.
The only backend premise is `NttRefines`: it is exactly the portable wgpu NTT
contract, rather than a proof-system soundness assumption disguised as an AIR
gate.  A future descriptor/emitter lowers these already-fixed gates to the
BabyBear trace; HidingFRI soundness then supplies `Satisfied`.

Honest scope: this file specifies and proves the arithmetic/refinement rung. It
does not claim that a Rust emitter implements these gates, that HidingFRI is
sound, that the public-key digest is collision resistant, or that the deployed
BFV parameters meet a lattice estimator target.
-/
import Market.PrivateBookEncryptionBinding
import Dregg2.Crypto.WgpuBfvNttSpec
import Dregg2.Tactics

namespace Market.PrivateBookBfvBindingAir

open Market.MpcClearingSecurity (CrossingLeakage)
open Market.PrivateBookEncryptionBinding
open Dregg2.Crypto.WgpuBfvNttSpec

set_option autoImplicit false

/-! ## 1. Fixed deployed shape and canonical RNS transport. -/

abbrev OrderIx := Fin 4
abbrev CipherPolyIx := Fin 2
abbrev CoeffIx := Fin deployedDegree
abbrev ModulusIx := Fin 3
abbrev RootLaneIx := Fin 8
abbrev EquationIx := OrderIx × CipherPolyIx × ModulusIx × CoeffIx

/-- The live relation checks 98,304 coefficient equations, not 128 random
projections of them. -/
theorem deployed_equation_count : Fintype.card EquationIx = 98304 := by
  norm_num [deployedDegree]

/-- One RNS polynomial in the deployed degree/modulus family. -/
abbrev DeployedRns := RnsPoly (n := deployedDegree) deployedModulus

/-- Every pinned RNS modulus is nonzero; expose this to `ZMod`'s value API. -/
instance deployedModulusNeZero (row : ModulusIx) : NeZero (deployedModulus row) :=
  ⟨by fin_cases row <;> norm_num [deployedModulus]⟩

/-- Public transport form: every RNS coefficient is two little-endian `u32`
limbs.  The raw type admits malformed words; `WireRns.Canonical` refuses them. -/
abbrev WireRns := (row : ModulusIx) → CoeffIx → Word64

/-- Every limb is a `u32` and every joined word is the canonical representative
strictly below its row modulus. -/
def WireRns.Canonical (wire : WireRns) : Prop :=
  ∀ row coefficient,
    (wire row coefficient).lo < limbBase ∧
    (wire row coefficient).hi < limbBase ∧
    (wire row coefficient).join < deployedModulus row

/-- Decode canonical (or raw) wire coefficients into the exact RNS family. -/
def WireRns.decode (wire : WireRns) : DeployedRns := fun row coefficient =>
  ((wire row coefficient).join : ZMod (deployedModulus row))

/-- Canonical transport encoder for an RNS polynomial. -/
def WireRns.encode (poly : DeployedRns) : WireRns := fun row coefficient =>
  split64 (poly row coefficient).val

/-- Encoding then decoding preserves every RNS coefficient. -/
theorem WireRns.decode_encode (poly : DeployedRns) :
    (WireRns.encode poly).decode = poly := by
  funext row coefficient
  unfold WireRns.encode WireRns.decode
  rw [join_split64]
  have hval : (poly row coefficient).val < wordModulus :=
    lt_trans (ZMod.val_lt _) (lt_trans (deployed_modulus_lt row) (by
      norm_num [wordModulus, limbBase]))
  rw [Nat.mod_eq_of_lt hval]
  exact ZMod.natCast_zmod_val _

/-- The encoder always emits canonical limbs and canonical RNS residues. -/
theorem WireRns.canonical_encode (poly : DeployedRns) :
    (WireRns.encode poly).Canonical := by
  intro row coefficient
  refine ⟨split64_lo_lt _, split64_hi_lt _, ?_⟩
  unfold WireRns.encode
  rw [join_split64]
  have hval : (poly row coefficient).val < wordModulus :=
    lt_trans (ZMod.val_lt _) (lt_trans (deployed_modulus_lt row) (by
      norm_num [wordModulus, limbBase]))
  rw [Nat.mod_eq_of_lt hval]
  exact ZMod.val_lt _

/-- The exact list embedded in the relying-party BFV identity. -/
def deployedCoefficientModuli : List Nat :=
  [0xffffee001, 0xffffc4001, 0x1ffffe0001]

/-- Public field/rule pins of the live `N=4,K=4` private-book descriptor. -/
def babyBearModulus : Nat := 2013265921
def privateBookRuleId : Nat := 1430520836

theorem deployed_moduli_list :
    (List.ofFn deployedModulus) = deployedCoefficientModuli := by
  decide

/-! ## 2. Private-book semantics and the complete public statement. -/

/-- Host-independent private-book semantics used by the AIR.  `message`
contains the *exact* fhe.rs SIMD-encoded plaintext polynomial for each hidden
order, already lifted into all three RNS rows.  Thus a hand-written slot basis
cannot silently replace the deployed encoder.

`publicKeyDigest` and `codecDigest` bind the complete key and encoding domain to
the existing `BfvIdentity`.  No injectivity is assumed: the full key remains a
public input and is constrained coefficient-by-coefficient. -/
structure Semantics where
  BookWitness : Type
  validBook : BookWitness → Prop
  orderRoot : Nat → Nat → BookWitness → RootLaneIx → Nat
  clearingOutput : Nat → Nat → BookWitness → CrossingLeakage
  message : BookWitness → OrderIx → DeployedRns
  rootDigest : (RootLaneIx → Nat) → Nat
  publicKeyDigest : (CipherPolyIx → DeployedRns) → Nat
  codecDigest : Nat

/-- Full public input.  Unlike the detached statement digest, this contains
every public-key and ciphertext coefficient which the AIR constrains. -/
structure PublicInput where
  identity : BfvIdentity
  publicKey : CipherPolyIx → WireRns
  ciphertext : OrderIx → CipherPolyIx → WireRns
  /-- All eight faithful private-book root lanes consumed by HidingFRI. -/
  orderRoot : RootLaneIx → Nat
  privateStatement : PrivateStatement

/-- Project the coefficient-rich AIR statement to the pre-existing
transferable-receipt statement through a caller-selected canonical row digest.
The AIR never verifies only this projection; it is provided so the existing
apex receipt can carry the same identity/root/output while the proof verifier
consumes the full coefficient input. -/
def PublicInput.toTransferable (pub : PublicInput)
    (rowDigest : (CipherPolyIx → WireRns) → Nat) :
    Market.PrivateBookEncryptionBinding.PublicInput :=
  { identity := pub.identity
    ciphertextRows := List.ofFn (fun order : OrderIx => rowDigest (pub.ciphertext order))
    privateStatement := pub.privateStatement }

theorem PublicInput.toTransferable_fourRows (pub : PublicInput)
    (rowDigest : (CipherPolyIx → WireRns) → Nat) :
    (pub.toTransferable rowDigest).ciphertextRows.length = 4 := by
  simp [PublicInput.toTransferable]

/-- Complete public-input preflight.  This pins the exact deployed parameter
family and proves every transported coefficient is canonical. -/
structure PublicInput.Canonical (S : Semantics) (pub : PublicInput) : Prop where
  degree : pub.identity.degree = deployedDegree
  plaintextModulus : pub.identity.plaintextModulus = 1032193
  coefficientModuli : pub.identity.coefficientModuli = deployedCoefficientModuli
  publicKeyDigest :
    pub.identity.publicKeyDigest = S.publicKeyDigest (fun poly => (pub.publicKey poly).decode)
  codecDigest : pub.identity.codecDigest = S.codecDigest
  session : pub.privateStatement.session < babyBearModulus
  rule : pub.privateStatement.rule = privateBookRuleId
  rootLanes : ∀ lane, pub.orderRoot lane < babyBearModulus
  price : pub.privateStatement.output.pStar < 4
  volumeNonnegative : 0 ≤ pub.privateStatement.output.vStar
  volumeBounded : pub.privateStatement.output.vStar ≤ 60
  privateRootDigest : pub.privateStatement.orderRoot = S.rootDigest pub.orderRoot
  publicKey : ∀ poly, (pub.publicKey poly).Canonical
  ciphertext : ∀ order poly, (pub.ciphertext order poly).Canonical

/-! ## 3. Hidden encryption witness and exact coefficient relation. -/

/-- The secret opening carried by the AIR witness.  `u` is shared across both
ciphertext polynomials for one order; `error order 0` and `error order 1` are
the two fresh error polynomials. -/
structure EncryptionWitness (S : Semantics) where
  book : S.BookWitness
  u : OrderIx → CoeffIx → Int
  error : OrderIx → CipherPolyIx → CoeffIx → Int

/-- The exact six-bit signed range used by the present seeded BFV sampler
extraction: `-32 <= x < 32`. -/
def Short (x : Int) : Prop := -32 ≤ x ∧ x < 32

/-- An exact integer quotient equation implies the corresponding modular
equation.  This is the carry/quotient bridge used by the AIR refinement: the
`q * quotient` term vanishes only after the integer gate has been checked. -/
theorem quotient_equation_implies_zmod
    {q lhs product message : Nat} {error quotient : Int}
    (h : (lhs : Int) = (product : Int) + error + (message : Int) -
      (q : Int) * quotient) :
    (lhs : ZMod q) = (product : ZMod q) + (error : ZMod q) +
      (message : ZMod q) := by
  have hcast := congrArg (fun value : Int => (value : ZMod q)) h
  simpa using hcast

/-- Lift one shared signed coefficient vector into every RNS row. -/
def liftSigned (coefficients : CoeffIx → Int) : DeployedRns := fun row coefficient =>
  (coefficients coefficient : ZMod (deployedModulus row))

/-- Lift one signed error coefficient into its RNS row. -/
def errorAt {S : Semantics} (witness : EncryptionWitness S) (order : OrderIx)
    (poly : CipherPolyIx) (row : ModulusIx) (coefficient : CoeffIx) :
    ZMod (deployedModulus row) :=
  (witness.error order poly coefficient : ZMod (deployedModulus row))

/-- Only `c0` carries the encoded plaintext; `c1` carries zero. -/
def messageAt (S : Semantics) (witness : EncryptionWitness S)
    (order : OrderIx) (poly : CipherPolyIx) : DeployedRns :=
  if poly = 0 then S.message witness.book order else 0

/-- The curve-free target relation.  It binds the same hidden book witness to
the public root/output and to every exact public-key BFV coefficient equation.
The ciphertext relation is the schoolbook negacyclic reference, not an opaque
digest and not a randomized linear combination. -/
structure ExactPrivateBookBfvOpeningFor (S : Semantics) (pub : PublicInput)
    (witness : EncryptionWitness S) : Prop where
  publicCanonical : pub.Canonical S
  bookValid : S.validBook witness.book
  rootExact : S.orderRoot pub.privateStatement.session pub.privateStatement.rule witness.book =
    pub.orderRoot
  outputExact :
    S.clearingOutput pub.privateStatement.session pub.privateStatement.rule witness.book =
      pub.privateStatement.output
  uShort : ∀ order coefficient, Short (witness.u order coefficient)
  errorShort : ∀ order poly coefficient, Short (witness.error order poly coefficient)
  coefficientExact : ∀ order poly row coefficient,
    (pub.ciphertext order poly).decode row coefficient =
      rnsNegacyclicMul (liftSigned (witness.u order))
          (pub.publicKey poly).decode row coefficient +
        errorAt witness order poly row coefficient +
        messageAt S witness order poly row coefficient

/-- Existential same-opening relation consumed by the proof-system boundary. -/
def ExactPrivateBookBfvOpening (S : Semantics) (pub : PublicInput) : Prop :=
  ∃ witness : EncryptionWitness S, ExactPrivateBookBfvOpeningFor S pub witness

/-! ## 4. AIR trace and gates. -/

/-- The complete multiplication stage plus integer quotient/carry witness.  A
real AIR lowering represents these values in BabyBear limbs; this semantic
trace keeps the intended integers and RNS values explicit. -/
structure Trace where
  nttProduct : OrderIx → CipherPolyIx → DeployedRns
  quotient : OrderIx → CipherPolyIx → ModulusIx → CoeffIx → Int

/-- Tight carry range for adding one canonical product, one canonical message,
and one `[-32,31]` error before reducing to one canonical ciphertext residue. -/
def CarryRange (quotient : Int) : Prop := -1 ≤ quotient ∧ quotient ≤ 2

/-- Semantic satisfaction of the BFV binding AIR.  `mulImpl` is the NTT backend
whose portable refinement contract is separately proved/tested.  The integer
gate is the single source of the RNS equation: it names the quotient and
prevents a future BabyBear lowering from replacing exact modular equality with
unchecked field wrap. -/
structure Satisfied (S : Semantics)
    (mulImpl : DeployedRns → DeployedRns → DeployedRns)
    (pub : PublicInput) (witness : EncryptionWitness S) (trace : Trace) : Prop where
  publicCanonical : pub.Canonical S
  bookValid : S.validBook witness.book
  rootGate : S.orderRoot pub.privateStatement.session pub.privateStatement.rule witness.book =
    pub.orderRoot
  outputGate :
    S.clearingOutput pub.privateStatement.session pub.privateStatement.rule witness.book =
      pub.privateStatement.output
  uRange : ∀ order coefficient, Short (witness.u order coefficient)
  errorRange : ∀ order poly coefficient, Short (witness.error order poly coefficient)
  nttGate : ∀ order poly,
    trace.nttProduct order poly =
      mulImpl (liftSigned (witness.u order)) (pub.publicKey poly).decode
  quotientGate : ∀ order poly row coefficient,
    ((pub.ciphertext order poly row coefficient).join : Int) =
      ((trace.nttProduct order poly row coefficient).val : Int) +
        witness.error order poly coefficient +
        ((messageAt S witness order poly row coefficient).val : Int) -
        (deployedModulus row : Int) * trace.quotient order poly row coefficient
  quotientRange : ∀ order poly row coefficient,
    CarryRange (trace.quotient order poly row coefficient)

/-- The integer quotient gate is sufficient to recover the exact RNS equation;
there is no duplicate modular gate for a malicious emitter to satisfy instead. -/
theorem Satisfied.rnsEquation
    {S : Semantics} {mulImpl : DeployedRns → DeployedRns → DeployedRns}
    {pub : PublicInput} {witness : EncryptionWitness S} {trace : Trace}
    (hsat : Satisfied S mulImpl pub witness trace)
    (order : OrderIx) (poly : CipherPolyIx) (row : ModulusIx)
    (coefficient : CoeffIx) :
    (pub.ciphertext order poly).decode row coefficient =
      trace.nttProduct order poly row coefficient +
        errorAt witness order poly row coefficient +
        messageAt S witness order poly row coefficient := by
  have hmod := quotient_equation_implies_zmod
    (hsat.quotientGate order poly row coefficient)
  simpa [WireRns.decode, errorAt] using hmod

/-! ## 5. Refinement: AIR satisfaction yields the exact opening. -/

/-- **The BFV-binding keystone.** If the NTT stage refines the portable
schoolbook specification, every satisfying trace yields one hidden witness
which simultaneously opens the public private-book root/output and every
canonical BFV ciphertext coefficient under the complete pinned public key. -/
theorem satisfied_yields_exact_private_book_bfv_opening
    {S : Semantics}
    {mulImpl : DeployedRns → DeployedRns → DeployedRns}
    {pub : PublicInput} {witness : EncryptionWitness S} {trace : Trace}
    (hntt : NttRefines mulImpl)
    (hsat : Satisfied S mulImpl pub witness trace) :
    ExactPrivateBookBfvOpening S pub := by
  refine ⟨witness,
    { publicCanonical := hsat.publicCanonical
      bookValid := hsat.bookValid
      rootExact := hsat.rootGate
      outputExact := hsat.outputGate
      uShort := hsat.uRange
      errorShort := hsat.errorRange
      coefficientExact := ?_ }⟩
  intro order poly row coefficient
  calc
    (pub.ciphertext order poly).decode row coefficient =
        trace.nttProduct order poly row coefficient +
          errorAt witness order poly row coefficient +
          messageAt S witness order poly row coefficient :=
      hsat.rnsEquation order poly row coefficient
    _ = mulImpl (liftSigned (witness.u order)) (pub.publicKey poly).decode row coefficient +
          errorAt witness order poly row coefficient +
          messageAt S witness order poly row coefficient := by
      rw [hsat.nttGate order poly]
    _ = rnsNegacyclicMul (liftSigned (witness.u order))
            (pub.publicKey poly).decode row coefficient +
          errorAt witness order poly row coefficient +
          messageAt S witness order poly row coefficient := by
      rw [hntt _ _ row coefficient]

/-- The reference NTT stage needs no cryptographic or device assumption: AIR
satisfaction against it directly yields the exact opening relation. -/
theorem reference_satisfied_yields_exact_private_book_bfv_opening
    {S : Semantics} {pub : PublicInput} {witness : EncryptionWitness S} {trace : Trace}
    (hsat : Satisfied S (@rnsNegacyclicMul 3 deployedDegree deployedModulus)
      pub witness trace) :
    ExactPrivateBookBfvOpening S pub :=
  satisfied_yields_exact_private_book_bfv_opening reference_nttRefines hsat

/-! ## 6. Mutation teeth: substituted public coefficients cannot share one
satisfying trace when the exact RHS is fixed. -/

/-- The AIR relation makes each ciphertext coefficient functional for a fixed
trace/witness.  This is the coefficient-level substitution tooth absent from a
detached statement digest. -/
theorem ciphertext_coefficient_functional
    {S : Semantics} {mulImpl : DeployedRns → DeployedRns → DeployedRns}
    {pubA pubB : PublicInput} {witness : EncryptionWitness S} {trace : Trace}
    (hsatA : Satisfied S mulImpl pubA witness trace)
    (hsatB : Satisfied S mulImpl pubB witness trace)
    (order : OrderIx) (poly : CipherPolyIx) (row : ModulusIx)
    (coefficient : CoeffIx) :
    (pubA.ciphertext order poly).decode row coefficient =
      (pubB.ciphertext order poly).decode row coefficient := by
  rw [hsatA.rnsEquation, hsatB.rnsEquation]

/-- Changing any decoded ciphertext coefficient while retaining the same
witness/trace is therefore refused. -/
theorem substituted_ciphertext_coefficient_refused
    {S : Semantics} {mulImpl : DeployedRns → DeployedRns → DeployedRns}
    {pubA pubB : PublicInput} {witness : EncryptionWitness S} {trace : Trace}
    (hsatA : Satisfied S mulImpl pubA witness trace)
    {order : OrderIx} {poly : CipherPolyIx} {row : ModulusIx}
    {coefficient : CoeffIx}
    (hchanged : (pubA.ciphertext order poly).decode row coefficient ≠
      (pubB.ciphertext order poly).decode row coefficient) :
    ¬ Satisfied S mulImpl pubB witness trace := by
  intro hsatB
  exact hchanged (ciphertext_coefficient_functional hsatA hsatB _ _ _ _)

#assert_all_clean [
  Market.PrivateBookBfvBindingAir.WireRns.decode_encode,
  Market.PrivateBookBfvBindingAir.WireRns.canonical_encode,
  Market.PrivateBookBfvBindingAir.deployed_moduli_list,
  Market.PrivateBookBfvBindingAir.deployed_equation_count,
  Market.PrivateBookBfvBindingAir.PublicInput.toTransferable_fourRows,
  Market.PrivateBookBfvBindingAir.quotient_equation_implies_zmod,
  Market.PrivateBookBfvBindingAir.Satisfied.rnsEquation,
  Market.PrivateBookBfvBindingAir.satisfied_yields_exact_private_book_bfv_opening,
  Market.PrivateBookBfvBindingAir.reference_satisfied_yields_exact_private_book_bfv_opening,
  Market.PrivateBookBfvBindingAir.ciphertext_coefficient_functional,
  Market.PrivateBookBfvBindingAir.substituted_ciphertext_coefficient_refused]

end Market.PrivateBookBfvBindingAir
