/-
# Binary Beaver-triple sacrifice: the exact GF(2) algebra

This file is the semantics pin for the additive preprocessing-sacrifice rung.
For a kept candidate `p = (a,b,c)`, a sacrificial candidate `s = (f,g,h)`,
and a post-commit challenge bit `r`, the parties open

* `rho = r*a ⊕ f`, and
* `sigma = b ⊕ g`,

then open the distributed check

`r*c ⊕ h ⊕ sigma*f ⊕ rho*g ⊕ rho*sigma`.

The central theorem below identifies that value exactly with
`r * error(p) ⊕ error(s)`, where `error(a,b,c) = c ⊕ a*b`.  Thus two valid
triples always pass.  Over GF(2), however, one challenge has only one bit of
soundness: for a malformed kept triple and any fixed sacrificial error there is
exactly one accepting challenge.  Runtime amplification must therefore use
many independently derived challenge bits after the candidate rows are
committed.

This is algebra, not a malicious-MPC theorem.  Commitment binding,
unpredictability of the post-commit beacon, authenticated response shares, and
one-time custody are named environmental/protocol premises.  In particular, a
party that can lie about its response share can defeat the algebraic verifier;
the Rust module retains an executable tooth for that residual.
-/

import Dregg2.Tactics

namespace Dregg2.Crypto.BinaryTripleSacrifice

/-- One global binary Beaver-triple candidate.  Party-local values reconstruct
to this object by component-wise XOR. -/
@[ext] structure Triple where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq, Repr

/-- Relation error: false exactly when `c = a*b` in GF(2). -/
def error (t : Triple) : Bool := t.c.xor (t.a && t.b)

/-- The Beaver relation for a global binary candidate. -/
def Valid (t : Triple) : Prop := error t = false

/-- First public masked opening. -/
def rho (challenge : Bool) (kept sacrificed : Triple) : Bool :=
  (challenge && kept.a).xor sacrificed.a

/-- Second public masked opening. -/
def sigma (kept sacrificed : Triple) : Bool :=
  kept.b.xor sacrificed.b

/-- Public sacrifice check reconstructed from the parties' check shares. -/
def check (challenge : Bool) (kept sacrificed : Triple) : Bool :=
  let r := rho challenge kept sacrificed
  let s := sigma kept sacrificed
  (challenge && kept.c).xor sacrificed.c |>.xor (s && sacrificed.a)
    |>.xor (r && sacrificed.b) |>.xor (r && s)

/-- The implementation formula is exactly the correlation of the two relation
errors.  This is the load-bearing algebraic identity used by the Rust checker. -/
theorem check_eq_error_relation (challenge : Bool) (kept sacrificed : Triple) :
    check challenge kept sacrificed =
      ((challenge && error kept).xor (error sacrificed)) := by
  rcases kept with ⟨a, b, c⟩
  rcases sacrificed with ⟨f, g, h⟩
  cases a <;> cases b <;> cases c <;>
    cases f <;> cases g <;> cases h <;> cases challenge <;> decide

/-- Completeness: two valid triples pass for either challenge bit. -/
theorem valid_pair_accepts {kept sacrificed : Triple}
    (hkept : Valid kept) (hsacrificed : Valid sacrificed) (challenge : Bool) :
    check challenge kept sacrificed = false := by
  rw [check_eq_error_relation, hkept, hsacrificed]
  cases challenge <;> decide

/-- Both possible challenges accepting the same committed pair forces both
relations to be valid.  It is the deterministic core beneath the probabilistic
post-commit challenge argument. -/
theorem both_challenges_accept_iff_valid (kept sacrificed : Triple) :
    (check false kept sacrificed = false ∧ check true kept sacrificed = false) ↔
      (Valid kept ∧ Valid sacrificed) := by
  rcases kept with ⟨a, b, c⟩
  rcases sacrificed with ⟨f, g, h⟩
  cases a <;> cases b <;> cases c <;>
    cases f <;> cases g <;> cases h <;> simp [Valid, error, check, rho, sigma]

/-- If the kept candidate is malformed, a fixed sacrificial candidate admits
exactly one challenge bit.  Hence one GF(2) sacrifice round contributes one bit
of soundness—never more. -/
theorem malformed_kept_has_unique_accepting_challenge
    {kept sacrificed : Triple} (hbad : ¬ Valid kept) :
    ∃! challenge : Bool, check challenge kept sacrificed = false := by
  rcases kept with ⟨a, b, c⟩
  rcases sacrificed with ⟨f, g, h⟩
  cases a <;> cases b <;> cases c <;>
    cases f <;> cases g <;> cases h <;> simp_all [Valid, error, check, rho, sigma]

/-- Concrete refusal tooth: the identically malformed `(0,0,1)` pair passes
challenge one but is exposed by challenge zero. -/
theorem identical_malformed_rejected_by_false :
    check false ⟨false, false, true⟩ ⟨false, false, true⟩ = true := by decide

/-- Non-vacuity companion: the same malformed commitment really does pass for
the other bit, exhibiting why amplification and beacon unpredictability are
load-bearing. -/
theorem identical_malformed_accepts_true :
    check true ⟨false, false, true⟩ ⟨false, false, true⟩ = false := by decide

#assert_axioms check_eq_error_relation
#assert_axioms valid_pair_accepts
#assert_axioms both_challenges_accept_iff_valid
#assert_axioms malformed_kept_has_unique_accepting_challenge
#assert_axioms identical_malformed_rejected_by_false
#assert_axioms identical_malformed_accepts_true

end Dregg2.Crypto.BinaryTripleSacrifice
