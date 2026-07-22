/-
# Market.PrivateBookBfvTerminalBinding -- the terminal product is not a free witness

The q0 threshold-terminal AIR proves the exact limb equation

  lambda * product + smudge = h (mod q)

but that statement is useful only when `product` is the coefficient produced by the
same private-book NTT family proof.  A context hash beside an independently supplied
product does not establish that fact.  This module fixes the semantic relation the
fused HidingFRI lowering must implement: the terminal coordinate is typed, and the
terminal product is equality-bound to `SpectralTrace.product` at that coordinate.

There is deliberately no hash-injectivity hypothesis here.  Session/DKG/key identity
is an ordinary typed domain field of the relation; the executable proof must carry the
same fields through its public statement or recursively bound envelope.  The remaining
cryptographic obligation is then the usual knowledge-soundness of that fixed relation,
not an uninhabited claim that a compressing context hash is injective.
-/

import Market.PrivateBookBfvNttFamily

namespace Market.PrivateBookBfvTerminalBinding

open Dregg2.Crypto.WgpuBfvNttSpec
open Market.PrivateBookBfvBindingAir
open Market.PrivateBookBfvNttFamily

set_option autoImplicit false

/-! ## 1. One complete, typed terminal coordinate and its deployment domain -/

/-- One of the 98,304 production terminal equations.  There is no untyped
`coefficient_index` or caller-selected ciphertext role to reinterpret. -/
structure TerminalCoordinate where
  order : OrderIx
  ciphertext : CipherPolyIx
  modulus : ModulusIx
  coefficient : CoeffIx
  deriving DecidableEq

/-- The non-arithmetic identity that scopes a terminal equation to one deployed
clearing/key ceremony.  These are exact values, not a claim that their eventual
wire hash is injective. -/
structure TerminalDomain where
  session : Nat
  party : Nat
  dkgCommitment : Fin 8 → Nat
  collectiveKeyCommitment : Fin 8 → Nat
  deriving DecidableEq

/-- The coefficient selected from the exact spectral trace. -/
def selectedProduct (trace : SpectralTrace) (coordinate : TerminalCoordinate) :
    ZMod (deployedModulus coordinate.modulus) :=
  trace.product coordinate.order coordinate.ciphertext coordinate.modulus
    coordinate.coefficient

/-! ## 2. The terminal row and the missing same-opening weld -/

/-- Semantic contents of one threshold-share terminal row.  `product` remains
explicit because the emitted limb row carries it, but it acquires authority only
through `BoundToTrace` below. -/
structure TerminalRow (coordinate : TerminalCoordinate) where
  domain : TerminalDomain
  lambda : ZMod (deployedModulus coordinate.modulus)
  product : ZMod (deployedModulus coordinate.modulus)
  smudge : Int
  h : ZMod (deployedModulus coordinate.modulus)

/-- The terminal product is exactly the chosen coefficient of the same family trace.
This is the semantic form of the future in-proof permutation/UMEM/recursive join. -/
def BoundToTrace (trace : SpectralTrace) (coordinate : TerminalCoordinate)
    (terminal : TerminalRow coordinate) : Prop :=
  terminal.product = selectedProduct trace coordinate

/-- Exact q-row arithmetic, stated after coercing the signed smudge into `ZMod q`.
The limb/carry descriptor is the executable lowering of this equality plus bounds. -/
def Arithmetic (coordinate : TerminalCoordinate) (terminal : TerminalRow coordinate) : Prop :=
  terminal.lambda * terminal.product + terminal.smudge = terminal.h

/-- Inclusive production smudge interval. -/
def SmudgeInRange (coordinate : TerminalCoordinate) (terminal : TerminalRow coordinate) : Prop :=
  -(2 ^ 80 : Int) ≤ terminal.smudge ∧ terminal.smudge ≤ (2 ^ 80 : Int)

/-- The fused relation.  The exact spectral trace, terminal same-opening weld,
arithmetic equation, smudge interval, and deployment domain are one conjunction. -/
structure Fused
    (psi : (row : ModulusIx) → ZMod (deployedModulus row))
    (publicKey : CipherPolyIx → WireRns)
    (u : OrderIx → CoeffIx → Int)
    (key : PublicKeyCertificate)
    (trace : SpectralTrace)
    (expectedDomain : TerminalDomain)
    (coordinate : TerminalCoordinate)
    (terminal : TerminalRow coordinate) : Prop where
  spectral : trace.Exact psi publicKey u key
  domainBound : terminal.domain = expectedDomain
  productBound : BoundToTrace trace coordinate terminal
  arithmetic : Arithmetic coordinate terminal
  smudgeInRange : SmudgeInRange coordinate terminal

/-! ## 3. Consequences the previous free-product relation could not prove -/

variable
  (psi : (row : ModulusIx) → ZMod (deployedModulus row))
  (publicKey : CipherPolyIx → WireRns)
  (u : OrderIx → CoeffIx → Int)
  (key : PublicKeyCertificate)
  (trace : SpectralTrace)
  (expectedDomain : TerminalDomain)

variable (coordinate : TerminalCoordinate)
variable (terminal left right : TerminalRow coordinate)

/-- The bound product is the exact odd-NTT multiplication output at the typed
coordinate.  No independent terminal product survives the rewrite. -/
theorem Fused.product_eq_oddNttMul
    (h : Fused psi publicKey u key trace expectedDomain coordinate terminal) :
    terminal.product =
      oddNttMul (psi coordinate.modulus)
        (liftSigned (u coordinate.order) coordinate.modulus)
        ((publicKey coordinate.ciphertext).decode coordinate.modulus)
        coordinate.coefficient := by
  rw [h.productBound]
  exact h.spectral.product_eq_oddNttMul coordinate.order coordinate.ciphertext
    coordinate.modulus coordinate.coefficient

/-- Once the odd-NTT lowering discharges its already named refinement contract,
the terminal product is the intended negacyclic product coefficient. -/
theorem Fused.product_eq_negacyclicMul
    (h : Fused psi publicKey u key trace expectedDomain coordinate terminal)
    (hrefines : OddNttRefines (n := deployedDegree) psi) :
    terminal.product =
      rnsNegacyclicMul (liftSigned (u coordinate.order))
        (publicKey coordinate.ciphertext).decode coordinate.modulus
        coordinate.coefficient := by
  exact h.product_eq_oddNttMul.trans
    (hrefines (liftSigned (u coordinate.order))
      (publicKey coordinate.ciphertext).decode coordinate.modulus
      coordinate.coefficient)

/-- Two accepted terminal rows at one exact trace coordinate cannot choose
different products. -/
theorem bound_product_unique
    (hl : BoundToTrace trace coordinate left)
    (hr : BoundToTrace trace coordinate right) :
    left.product = right.product := by
  exact hl.trans hr.symm

/-- The direct hostile tooth: changing the terminal product away from the exact
carrier coefficient makes the fused relation uninhabited. -/
theorem changed_product_refused
    (changed : TerminalRow coordinate)
    (hchanged : changed.product ≠ selectedProduct trace coordinate) :
    ¬ Fused psi publicKey u key trace expectedDomain coordinate changed := by
  intro h
  exact hchanged h.productBound

/-- A context/domain substitution is refused structurally; no appeal to hash
injectivity launders the deployment identity. -/
theorem changed_domain_refused
    (changed : TerminalRow coordinate)
    (hchanged : changed.domain ≠ expectedDomain) :
    ¬ Fused psi publicKey u key trace expectedDomain coordinate changed := by
  intro h
  exact hchanged h.domainBound

/-- Rewriting the terminal equation through the weld proves that its arithmetic
actually consumes the carrier coefficient. -/
theorem Fused.carrier_equation
    (h : Fused psi publicKey u key trace expectedDomain coordinate terminal) :
    terminal.lambda * selectedProduct trace coordinate + terminal.smudge = terminal.h := by
  rw [← h.productBound]
  exact h.arithmetic

/-! ## 4. Non-vacuity -/

/-- Any exact spectral trace admits a concrete nonzero-lambda terminal row at a
chosen coordinate: lambda=1, smudge=0, and h is the selected carrier product.
This witnesses that adding the same-opening weld does not make the relation empty. -/
theorem honest_terminal_exists
    (hexact : trace.Exact psi publicKey u key)
    (expectedDomain : TerminalDomain) (coordinate : TerminalCoordinate) :
    ∃ terminal : TerminalRow coordinate,
      Fused psi publicKey u key trace expectedDomain coordinate terminal := by
  let terminal : TerminalRow coordinate :=
    { domain := expectedDomain
      lambda := 1
      product := selectedProduct trace coordinate
      smudge := 0
      h := selectedProduct trace coordinate }
  refine ⟨terminal, ?_⟩
  constructor
  · exact hexact
  · rfl
  · rfl
  · simp [Arithmetic, terminal]
  · change -(2 ^ 80 : Int) ≤ 0 ∧ 0 ≤ (2 ^ 80 : Int)
    norm_num

#assert_axioms Fused.product_eq_oddNttMul
#assert_axioms Fused.product_eq_negacyclicMul
#assert_axioms bound_product_unique
#assert_axioms changed_product_refused
#assert_axioms changed_domain_refused
#assert_axioms Fused.carrier_equation
#assert_axioms honest_terminal_exists

end Market.PrivateBookBfvTerminalBinding
