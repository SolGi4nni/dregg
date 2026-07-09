/-
# `Dregg2.Crypto.VRF` — the abstract VRF security framework (Micali–Rabin–Vadhan).

Reusable scaffolding for a post-quantum VRF (lattice **LB-VRF** or hash-based **XM-VRF**) that we
instantiate later. This is the metatheory for the consensus's **leader sortition**: a VRF is what lets a
validator prove "I was chosen" without letting anyone else predict or forge the choice.

**Undischarged-scaffolding boundary (read first).** There is NO concrete VRF construction in this file; the
security definitions below are the abstract GAMES. `UniqueOutputs` and `Pseudorandom` are ASSUMED
predicates — a concrete instantiation MUST discharge them, and until one is supplied they are definitions,
not proved properties. The one genuine reduction here is the `§ Lattice` skeleton, where LB-VRF's
uniqueness is REDUCED to Module-SIS (`lattice_vrf_unique_under_msis`) — that leg IS proved, down to the
`MSISHard` floor. Everything else about `Pseudorandom` is well-formedness/non-vacuity of the game, not a
discharge of it.

A **VRF** (Micali–Rabin–Vadhan) is a triple `(keygen, eval, verify)` where `eval sk x = (y, π)` produces an
output `y` and a proof `π`, and `verify pk x y π : Bool` checks the pair. We model it abstractly over
carrier types `SK PK Input Output Proof` (a `structure` with the `pkOf`/`eval`/`verify` maps), then
formalize the three standard properties:

1. **PROVABILITY (correctness)** — an honestly-evaluated `(y, π) = eval sk x` verifies. Stated over the
   abstract model given a `Correct` hypothesis relating `eval` and `verify` (`provability`).
2. **UNIQUENESS** — the critical one. For a fixed `pk` and input `x`, at MOST ONE output `y` has a
   verifying proof (`uniqueness_at_most_one`). Modeled as `UniqueOutputs`, a property of the `verify`
   *relation* (`VerifyRel`). The **"Breaking X-VRF" attack** in WOTS+/XMSS is EXACTLY a `verify` relation
   that admits two outputs — a uniqueness failure — so `two_outputs_break_uniqueness` shows two distinct
   verifying outputs REFUTE `UniqueOutputs`. The teeth are exhibited concretely: a uniqueness-RESPECTING
   toy VRF (one output verifies) and a uniqueness-VIOLATING one (two outputs verify), `#guard`-separated.
3. **PSEUDORANDOMNESS** — the output is indistinguishable from uniform without the secret. This is the
   abstract security GAME `Pseudorandom`, an ASSUMED definition (the `MSISHard`-analogue for this leg), NOT
   a proved property of any construction: a concrete instantiation MUST discharge it (LB-VRF from MLWE,
   XM-VRF from hash-CR/PRG), and until such a construction is supplied it stands undischarged as
   scaffolding — this file proves NO reduction of it to a hardness floor. What IS proved here are only the
   game's well-formedness facts: an output-blind distinguisher gains nothing unconditionally, and a
   subsingleton output space is unconditionally pseudorandom (non-vacuity of the carrier — it is
   satisfiable). Neither discharges `Pseudorandom` for a real VRF.

Finally, a **lattice instantiation skeleton** (`§ Lattice`): LB-VRF's public key is `t = A·s`, the exact
shape of `Dregg2.Crypto.HermineMSIS`, so the lattice VRF's uniqueness REDUCES to Module-SIS — two verifying
outputs on the same commitment subtract to a short nonzero kernel vector of the augmented map `[A | t]`. We
reuse `Lattice.IsMSISSolution`, `HermineSelfTargetMSIS.augmented`, and the Hermine extractor: the reduction
SHAPE is real (`lattice_vrf_uniqueness_reduces_to_msis`, `lattice_vrf_unique_under_msis`) and
`#assert_axioms`-clean, with MSIS hardness the only irreducible floor — mirroring how
`HermineSelfTargetMSIS` derives non-triviality from the challenge coordinate (here: the OUTPUT coordinate).
-/
import Dregg2.Crypto.HermineSelfTargetMSIS

namespace Dregg2.Crypto.VRF

open Dregg2.Crypto.Lattice

/-! ## The abstract VRF (Micali–Rabin–Vadhan). -/

set_option linter.dupNamespace false in
/-- **A verifiable random function.** Abstract over carrier types: secret keys `SK`, public keys `PK`,
inputs `Input`, outputs `Output`, and proofs `Proof`. `pkOf` derives the public key from a secret key (the
public half of `keygen`); `eval sk x = (y, π)` is the keyed evaluation producing output and proof;
`verify pk x y π` decides whether the pair is a genuine evaluation of `x` under `pk`. -/
structure VRF (SK PK Input Output Proof : Type*) where
  /-- The public key of a secret key (the public output of `keygen`). -/
  pkOf : SK → PK
  /-- Keyed evaluation: `eval sk x = (output, proof)`. -/
  eval : SK → Input → Output × Proof
  /-- Verification of an `(output, proof)` pair against the public key and input. -/
  verify : PK → Input → Output → Proof → Bool

variable {SK PK Input Output Proof : Type*}

/-! ## 1. Provability (correctness). -/

/-- **Correctness hypothesis.** Every honestly-evaluated pair verifies against the derived public key. The
abstract relation between `eval` and `verify` that a concrete VRF must establish. -/
def Correct (V : VRF SK PK Input Output Proof) : Prop :=
  ∀ (sk : SK) (x : Input),
    V.verify (V.pkOf sk) x (V.eval sk x).1 (V.eval sk x).2 = true

/-- **PROVABILITY.** Given correctness, an honestly-evaluated `(y, π) = eval sk x` verifies:
`verify (pkOf sk) x y π = true`. The MRV "provability" property, at the level of the abstract model. -/
theorem provability (V : VRF SK PK Input Output Proof) (hc : Correct V)
    (sk : SK) (x : Input) (y : Output) (π : Proof) (h : V.eval sk x = (y, π)) :
    V.verify (V.pkOf sk) x y π = true := by
  have hcx := hc sk x
  rw [h] at hcx
  exact hcx

#assert_axioms provability

/-! ## 2. Uniqueness (the critical property — the "Breaking X-VRF" target). -/

/-- The **verify relation**: `pk, x` admit output `y` when SOME proof makes `y` verify. Uniqueness is a
property of THIS relation — the object the "Breaking X-VRF" attack targets. -/
def VerifyRel (V : VRF SK PK Input Output Proof) (pk : PK) (x : Input) (y : Output) : Prop :=
  ∃ π : Proof, V.verify pk x y π = true

/-- **UNIQUENESS (as a property of the verify relation).** For every fixed `pk` and input `x`, at most one
output has a verifying proof. A VRF whose `verify` violates this — admitting two outputs for one `(pk, x)`
— is exactly the "Breaking X-VRF" failure (WOTS+/XMSS): the property is LOAD-BEARING, not decorative. -/
def UniqueOutputs (V : VRF SK PK Input Output Proof) : Prop :=
  ∀ (pk : PK) (x : Input) (y₁ y₂ : Output),
    VerifyRel V pk x y₁ → VerifyRel V pk x y₂ → y₁ = y₂

/-- **The "at most one output" consequence.** Under `UniqueOutputs`, two proofs `π₁, π₂` that verify
outputs `y₁, y₂` for the same `(pk, x)` force `y₁ = y₂` — the MRV uniqueness guarantee sortition needs. -/
theorem uniqueness_at_most_one (V : VRF SK PK Input Output Proof) (hu : UniqueOutputs V)
    (pk : PK) (x : Input) (y₁ y₂ : Output) (π₁ π₂ : Proof)
    (h1 : V.verify pk x y₁ π₁ = true) (h2 : V.verify pk x y₂ π₂ = true) :
    y₁ = y₂ :=
  hu pk x y₁ y₂ ⟨π₁, h1⟩ ⟨π₂, h2⟩

#assert_axioms uniqueness_at_most_one

/-- **THE TEETH.** Two DISTINCT outputs that both verify for one `(pk, x)` REFUTE `UniqueOutputs`. This is
the "Breaking X-VRF" attack stated as a theorem: a `verify` relation admitting two outputs makes the
uniqueness hypothesis FALSE — so anything downstream that assumed `UniqueOutputs` loses its premise. It is
the contrapositive of `uniqueness_at_most_one`, and it is what the violating `#guard` instance exhibits. -/
theorem two_outputs_break_uniqueness (V : VRF SK PK Input Output Proof)
    (pk : PK) (x : Input) (y₁ y₂ : Output) (π₁ π₂ : Proof)
    (hne : y₁ ≠ y₂)
    (h1 : V.verify pk x y₁ π₁ = true) (h2 : V.verify pk x y₂ π₂ = true) :
    ¬ UniqueOutputs V :=
  fun hu => hne (hu pk x y₁ y₂ ⟨π₁, h1⟩ ⟨π₂, h2⟩)

#assert_axioms two_outputs_break_uniqueness

/-! ## 3. Pseudorandomness (named carrier + trivial reductions). -/

/-- A **distinguisher** against the VRF: sees the public key, the `verify` oracle (as a function — NOT the
secret key), a challenge input `x`, and a candidate output, and returns a guess bit (`true` = "real VRF
output", `false` = "uniform"). The adversary of the pseudorandomness game. -/
abbrev Distinguisher (PK Input Output Proof : Type*) :=
  PK → (Input → Output → Proof → Bool) → Input → Output → Bool

/-- **THE PSEUDORANDOMNESS ASSUMPTION (carrier).** No distinguisher, given only the public key and the
`verify` oracle, tells a real VRF output `y = (eval sk x).1` from a uniformly sampled `u`. The
`MSISHard`-analogue for this leg: a named predicate assumed for a concrete instantiation, never proved here
(its floor is the underlying hardness — MLWE for LB-VRF, the hash for XM-VRF). Stated as perfect
indistinguishability at the level the framework supports: the distinguisher's verdict is INVARIANT to
whether it is fed the real output or a random one. -/
def Pseudorandom (V : VRF SK PK Input Output Proof) : Prop :=
  ∀ (D : Distinguisher PK Input Output Proof) (sk : SK) (x : Input) (u : Output),
    D (V.pkOf sk) (V.verify (V.pkOf sk)) x (V.eval sk x).1 =
    D (V.pkOf sk) (V.verify (V.pkOf sk)) x u

/-- **Trivial reduction: an output-blind distinguisher gains nothing — unconditionally.** A distinguisher
whose verdict does not depend on the challenge output cannot separate real from random. No assumption
needed: this is the well-formedness floor of the game (the trivial adversary always loses). -/
theorem blind_distinguisher_no_advantage (V : VRF SK PK Input Output Proof)
    (D : Distinguisher PK Input Output Proof)
    (hblind : ∀ pk o x y₁ y₂, D pk o x y₁ = D pk o x y₂)
    (sk : SK) (x : Input) (u : Output) :
    D (V.pkOf sk) (V.verify (V.pkOf sk)) x (V.eval sk x).1 =
    D (V.pkOf sk) (V.verify (V.pkOf sk)) x u :=
  hblind _ _ _ _ _

#assert_axioms blind_distinguisher_no_advantage

/-- **Trivial reduction / non-vacuity: a subsingleton output space is unconditionally pseudorandom.** When
`Output` has at most one element, the real output and any "random" `u` are literally equal, so every
distinguisher is invariant — `Pseudorandom` holds with no hardness assumption. A concrete inhabitant of the
carrier, so `Pseudorandom` is not vacuous (it is satisfiable, and here provably so). -/
theorem subsingleton_output_pseudorandom [Subsingleton Output]
    (V : VRF SK PK Input Output Proof) : Pseudorandom V := by
  intro D sk x u
  rw [Subsingleton.elim (V.eval sk x).1 u]

#assert_axioms subsingleton_output_pseudorandom

/-! ## Teeth — concrete uniqueness-respecting vs. uniqueness-violating instances.

A `Bool`-output toy VRF over `Unit` keys/inputs/proofs isolates the uniqueness property. `goodVRF` accepts
`y` iff `y = true`, so exactly ONE output verifies — `UniqueOutputs` holds. `badVRF` accepts EVERY output,
so both `true` and `false` verify — the "Breaking X-VRF" shape, and `UniqueOutputs` is FALSE. The `#guard`s
separate the two, proving uniqueness is non-vacuous AND load-bearing. -/

section Teeth

/-- A uniqueness-RESPECTING toy VRF: `verify _ _ y _ = y`, so only `y = true` verifies. -/
def goodVRF : VRF Unit Unit Unit Bool Unit where
  pkOf _ := ()
  eval _ _ := (true, ())
  verify _ _ y _ := y

/-- A uniqueness-VIOLATING toy VRF: `verify _ _ _ _ = true` accepts ANY output (the "Breaking X-VRF"
shape). Both `true` and `false` verify for the same `(pk, x)`. -/
def badVRF : VRF Unit Unit Unit Bool Unit where
  pkOf _ := ()
  eval _ _ := (true, ())
  verify _ _ _ _ := true

/-- `goodVRF` is correct: the honest output `true` verifies. -/
theorem goodVRF_correct : Correct goodVRF := fun _ _ => rfl

#assert_axioms goodVRF_correct

/-- **UNIQUENESS HOLDS** for the respecting instance: only `y = true` verifies, so any two verifying
outputs coincide. The load-bearing property, PROVED for a concrete `verify`. -/
theorem goodVRF_unique : UniqueOutputs goodVRF := by
  rintro pk x y₁ y₂ ⟨_, h1⟩ ⟨_, h2⟩
  simp only [goodVRF] at h1 h2
  rw [h1, h2]

#assert_axioms goodVRF_unique

/-- **UNIQUENESS FAILS** for the violating instance — the "Breaking X-VRF" attack, via
`two_outputs_break_uniqueness`: two distinct outputs verify under `badVRF`, refuting `UniqueOutputs`. -/
theorem badVRF_not_unique : ¬ UniqueOutputs badVRF :=
  two_outputs_break_uniqueness badVRF () () true false () () (by decide) rfl rfl

#assert_axioms badVRF_not_unique

/-- Provability round-trip on `goodVRF`, THROUGH the abstract `provability` theorem. -/
example : goodVRF.verify (goodVRF.pkOf ()) () true () = true :=
  provability goodVRF goodVRF_correct () () true () rfl

-- PROVABILITY round-trip: the honestly-evaluated pair verifies (Bool-level, executable).
#guard goodVRF.verify (goodVRF.pkOf ()) () (goodVRF.eval () ()).1 (goodVRF.eval () ()).2
-- UNIQUENESS RESPECTING: `goodVRF` accepts `true` but REJECTS `false` — exactly one output verifies.
#guard goodVRF.verify () () true () && !goodVRF.verify () () false ()
-- UNIQUENESS VIOLATING (the load-bearing tooth): `badVRF` accepts BOTH `true` AND `false` — two outputs
-- verify, so `UniqueOutputs badVRF` is false (`badVRF_not_unique`). The concrete "Breaking X-VRF" witness.
#guard badVRF.verify () () true () && badVRF.verify () () false ()

end Teeth

/-- Non-vacuity of the pseudorandomness carrier: a `Unit`-output VRF is unconditionally `Pseudorandom`. -/
def trivialVRF : VRF Unit Unit Unit Unit Unit where
  pkOf _ := ()
  eval _ _ := ((), ())
  verify _ _ _ _ := true

example : Pseudorandom trivialVRF := subsingleton_output_pseudorandom trivialVRF

/-! ## 4. Lattice instantiation skeleton — LB-VRF uniqueness reduces to Module-SIS.

LB-VRF's public key is `t = A·s` (the shape of `Dregg2.Crypto.HermineMSIS`), and a verifying proof is a
SHORT `z` binding the output `y` into the linear relation `A·z = w + y·t` — this is precisely
`HermineThreshold.verify A t w y z`, with the VRF OUTPUT `y` occupying the coordinate the signature scheme
gave the challenge. Uniqueness then reduces to Module-SIS exactly as in `HermineSelfTargetMSIS`: two
verifying outputs on the SAME commitment `w`, `y₁ ≠ y₂`, subtract to `A·(z₁ − z₂) = (y₁ − y₂)·t`, i.e. a
short NONZERO kernel vector `(z₁ − z₂, −(y₁ − y₂))` of the augmented map `[A | t]` — an `IsMSISSolution`.
The non-triviality is FREE from the output coordinate (`y₁ ≠ y₂` ⇒ second coordinate `≠ 0`), no
invertibility, no MLWE. So MSIS hardness ⇒ the lattice VRF has UNIQUE outputs. We reuse `augmented`, the
`ShortNorm (· × ·)` product instance, `IsMSISSolution`, and the Hermine extractor. -/

section Lattice

open Dregg2.Crypto.HermineSelfTargetMSIS

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-- **The lattice VRF verify relation.** Output `y : Rq` and short proof `z : M` verify against public key
`t = A·s` and per-input commitment `w` iff `A·z = w + y·t` — the SAME object as `HermineThreshold.verify`,
now read with the VRF OUTPUT in the challenge coordinate. The Prop-level image of the concrete `Bool`
`verify` a full LB-VRF instantiation supplies. -/
def latticeVerify (A : M →ₗ[Rq] N) (t w : N) (y : Rq) (z : M) : Prop :=
  HermineThreshold.verify A t w y z

/-- **LB-VRF UNIQUENESS REDUCES TO MODULE-SIS.** Two verifying outputs `(y₁, z₁)`, `(y₂, z₂)` on the SAME
commitment `w` against public key `t`, both proofs short (`βz`) and both outputs short (`βy`), with `y₁ ≠
y₂`: their difference `(z₁ − z₂, −(y₁ − y₂))` is a genuine `IsMSISSolution` for the augmented map `[A | t]`
at bound `(βz + βz) + (βy + βy)`. All three obligations are DERIVED — nonzero from the OUTPUT coordinate
(`y₁ ≠ y₂`, no invertibility/MLWE), short by the triangle inequality, kernel by the Hermine extractor
subtracting the shared commitment. This is the uniqueness reduction target, its SHAPE real. -/
theorem lattice_vrf_uniqueness_reduces_to_msis
    (A : M →ₗ[Rq] N) (t w : N) (y₁ y₂ : Rq) (z₁ z₂ : M) (βz βy : ℕ)
    (hz₁ : nrm z₁ ≤ βz) (hz₂ : nrm z₂ ≤ βz) (hy₁ : nrm y₁ ≤ βy) (hy₂ : nrm y₂ ≤ βy)
    (hne : y₁ ≠ y₂)
    (h1 : latticeVerify A t w y₁ z₁) (h2 : latticeVerify A t w y₂ z₂) :
    IsMSISSolution (augmented A t) ((βz + βz) + (βy + βy)) (z₁ - z₂, -(y₁ - y₂)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- NONZERO: the output sits in the second coordinate, so `y₁ ≠ y₂` forces the vector nonzero.
    intro h
    rw [Prod.mk_eq_zero] at h
    exact hne (sub_eq_zero.mp (neg_eq_zero.mp h.2))
  · -- SHORT: coordinate-sum norm, both coordinates bounded by the triangle inequality.
    show nrm (z₁ - z₂) + nrm (-(y₁ - y₂)) ≤ (βz + βz) + (βy + βy)
    rw [nrm_neg]
    exact Nat.add_le_add
      (le_trans (nrm_sub_le z₁ z₂) (Nat.add_le_add hz₁ hz₂))
      (le_trans (nrm_sub_le y₁ y₂) (Nat.add_le_add hy₁ hy₂))
  · -- KERNEL: the extractor cancels the shared commitment `w`, then `[A | t]` sends the difference to 0.
    have hrel : A (z₁ - z₂) = (y₁ - y₂) • t :=
      Dregg2.Crypto.Hermine.hermine_special_soundness_extracts_relation A t w y₁ y₂ z₁ z₂ h1 h2
    rw [augmented_apply, hrel, neg_smul, add_neg_cancel]

#assert_axioms lattice_vrf_uniqueness_reduces_to_msis

/-- **MSIS HARDNESS ⇒ LB-VRF HAS UNIQUE OUTPUTS.** If Module-SIS is hard for the augmented map `[A | t]` at
the extracted bound, then no two distinct short outputs verify on the same commitment: `y₁ = y₂`. The MRV
uniqueness property for the lattice instantiation, reduced down to the ONLY irreducible floor — MSIS
hardness — exactly as `HermineSelfTargetMSIS.no_forgery_under_msis_selftarget` reduces unforgeability. -/
theorem lattice_vrf_unique_under_msis
    (A : M →ₗ[Rq] N) (t w : N) (y₁ y₂ : Rq) (z₁ z₂ : M) (βz βy : ℕ)
    (hz₁ : nrm z₁ ≤ βz) (hz₂ : nrm z₂ ≤ βz) (hy₁ : nrm y₁ ≤ βy) (hy₂ : nrm y₂ ≤ βy)
    (h1 : latticeVerify A t w y₁ z₁) (h2 : latticeVerify A t w y₂ z₂)
    (hard : MSISHard (augmented A t) ((βz + βz) + (βy + βy))) :
    y₁ = y₂ := by
  by_contra hne
  exact hard ⟨_, lattice_vrf_uniqueness_reduces_to_msis A t w y₁ y₂ z₁ z₂ βz βy
    hz₁ hz₂ hy₁ hy₂ hne h1 h2⟩

#assert_axioms lattice_vrf_unique_under_msis

end Lattice

end Dregg2.Crypto.VRF
