/-
# Dregg2.Authority.DesignatedVerifier — the transferability axis (public vs designated-verifier).

dregg's authorization proof verifies as a pure function of the proof and public inputs, with no
verifier-secret parameter anywhere:

* `circuit/src/presentation.rs:224` — `pub fn verify(&self) -> PresentationVerification` takes only
  `&self` and checks it against the public `federation_root` / `request_predicate` / `timestamp`
  (no `verifier_secret` argument exists in the whole crate). Any third party holding the proof + root
  recomputes the identical `Valid` verdict.
* The Lean side: `Laws.Discharged p w := Verifiable.Verify p w = true` (`Dregg2/Laws.lean:38`) is a
  single universal verify relation, not indexed by who is checking. The model cannot even express
  "convincing only to verifier V" — every discharged transcript convinces everyone: non-repudiation.

This is a genuine missing axis, orthogonal to the disclosure dials of `Privacy.lean` and to the
attenuation dial of `Caveat.lean`. Disclosure controls what the proof reveals; transferability
controls to whom it is convincing. A proof can be fully zero-knowledge yet still non-repudiable.

This module adds the verifier-indexed discharge `DischargedFor : Verifier → Statement → Proof → Prop`
and the two endpoints of a transferability dial:

* **PUBLIC / transferable** = `∀ V, DischargedFor V s p` — convinces everyone, hence non-repudiable
  (the current dregg behaviour, recovered as the `∀ V` collapse: `publicMode_collapses_to_universal`).
* **DESIGNATED-VERIFIER** = `DischargedFor V₀ s p` for a specific `V₀` holding a verifier-secret,
  together with `¬ Transferable` — convinces `V₀` and NOT everyone. Non-transferable / deniable:
  `V₀` could have produced the same transcript using its verifier-secret, so the transcript proves
  nothing to a third party, and the authorizer can repudiate.

§8 portal: the DV-ZK / deniable-authentication crypto is an honest Prop-portal, carried as a class
(`DVKernel`) of opaque oracles + named laws — never faked as proved in Lean. `verifyFor`, `simulate`,
and the law `simulate_indistinguishable` are §8 obligations the deniable-auth scheme discharges.

Proved here (no `sorry`/`axiom`/`native_decide`):
* `public_is_transferable` / `public_convinces_any_third_party` — public mode is non-repudiable;
* `designated_not_transferable` — designated mode has a verifier it does NOT convince;
* `designated_is_deniable` — the simulator repudiation;
* `dial_endpoints_distinct` — the two modes are genuinely distinct (a witnessed separation, not vacuous).

Pure, computable, `#eval`-able over a reference DV-kernel that witnesses the interface is inhabitable.
-/
import Dregg2.CryptoKernel

namespace Dregg2.Authority.DV

open Dregg2.Crypto (CryptoKernel)

/-! ## The §8 portal: a verifier-indexed deniable-authentication kernel.

The deniable-auth analogue of `CryptoKernel` (`Dregg2/CryptoKernel.lean:40`): operation types are
uninterpreted, operations are opaque oracles, law fields are §8 obligations assumed never proved.
The single new element over `CryptoKernel`: the verify oracle is indexed by the verifier — the axis
the running `presentation.rs::verify` (`:224`) lacks. -/

/-- **`DVKernel Verifier Statement Proof VSecret`** — the §8 deniable-authentication portal.
`Verifier` identifies a checking party; `VSecret` is a verifier's verification secret (the trapdoor
powering the simulator — a chameleon trapdoor / designated verifier's secret key). All operations
are opaque; the law fields are §8 obligations the crypto scheme discharges. -/
class DVKernel (Verifier : Type) (Statement : Type) (Proof : Type) (VSecret : Type) where
  /-- **The verifier-INDEXED verify oracle (§8).** Does `proof` discharge `stmt` *for verifier* `V`?
  The verifier index is the whole point: unlike `CryptoKernel.verify` (`CryptoKernel.lean:46`) and
  `presentation.rs::verify` (`:224`), the verdict may depend on *who* is checking. Soundness /
  extractability is the circuit's obligation, NEVER a Lean law. -/
  verifyFor : Verifier → Statement → Proof → Bool
  /-- The verifier's verification-secret (its DV trapdoor). The designated verifier `V₀` is the one
  that *holds* `vsecret V₀`; a third party does not. -/
  vsecret : Verifier → VSecret
  /-- **The SIMULATOR (§8).** Given a verifier's secret and a statement, *forge a transcript* that the
  verifier itself would accept — the defining capability of a designated-verifier / deniable scheme.
  This is what makes the authorization **repudiable**: the verifier could have produced it. -/
  simulate : VSecret → Statement → Proof
  /-- **LAW — simulator indistinguishability (§8 OBLIGATION, a class field, NEVER a Lean theorem).**
  A transcript the verifier `V` simulated *with its own secret* verifies **under `V`** — i.e. `V`
  cannot tell its own forgery from a real authorization, so neither can it convince anyone else that a
  real authorization occurred. This is the crypto core of deniability; the DV-NIZK / chameleon impl
  discharges it (the circuit's zero-knowledge/simulation soundness), NOT this file. -/
  simulate_verifies : ∀ (V : Verifier) (stmt : Statement),
    verifyFor V stmt (simulate (vsecret V) stmt) = true

variable {Verifier Statement Proof VSecret : Type}

/-! ## The new axis: verifier-INDEXED discharge `DischargedFor`. -/

/-- **`DischargedFor V stmt proof`** — verifier `V` is convinced that `proof` discharges `stmt`.
The verifier-indexed generalization of `Laws.Discharged` (`Dregg2/Laws.lean:38`), which had no
verifier index — collapsing to a single universal relation hardwires dregg to non-repudiation. -/
def DischargedFor [DVKernel Verifier Statement Proof VSecret]
    (V : Verifier) (stmt : Statement) (proof : Proof) : Prop :=
  DVKernel.verifyFor (VSecret := VSecret) V stmt proof = true

instance [DVKernel Verifier Statement Proof VSecret]
    (V : Verifier) (stmt : Statement) (proof : Proof) :
    Decidable (DischargedFor (VSecret := VSecret) V stmt proof) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## The transferability DIAL and its two endpoints. -/

/-- **`Transferable Verifier stmt proof`** (= the public endpoint) — the transcript convinces every
verifier. The `∀ V` collapse that recovers dregg's current behaviour: `presentation.rs::verify` (`:224`)
gives the same verdict to all checkers = non-repudiable. `Verifier` is explicit so the quantified
universe is always pinned. -/
def Transferable (Verifier : Type) {Statement Proof VSecret : Type}
    [DVKernel Verifier Statement Proof VSecret]
    (stmt : Statement) (proof : Proof) : Prop :=
  ∀ V : Verifier, DischargedFor (VSecret := VSecret) V stmt proof

/-- **`DesignatedFor V₀ stmt proof`** (= the designated-verifier endpoint) — the transcript convinces
the specific `V₀` and is NOT transferable. The mode dregg cannot currently express; the two conjuncts
set the dial to its non-transferable extreme. -/
def DesignatedFor [DVKernel Verifier Statement Proof VSecret]
    (V₀ : Verifier) (stmt : Statement) (proof : Proof) : Prop :=
  DischargedFor (VSecret := VSecret) V₀ stmt proof
    ∧ ¬ Transferable Verifier (VSecret := VSecret) stmt proof

/-- **`TransferDial`** — the transferability dial, a two-valued setting alongside the disclosure dials
of `Privacy.lean` and the attenuation dial of `Caveat.lean`. `transferable` is "convince everyone"
(non-repudiable); `designated V₀` is "convince only `V₀`" (deniable). -/
inductive TransferDial (Verifier : Type) where
  /-- The PUBLIC setting: maximal transferability — the current, only mode dregg ships. -/
  | transferable
  /-- The DESIGNATED-VERIFIER setting for a specific verifier `V₀`: non-transferable / deniable. -/
  | designated (V₀ : Verifier)
  deriving Repr

/-- **`DialHolds dial stmt proof`** — the proposition a transcript must satisfy at each dial setting.
`public` ↦ `Transferable`; `designated V₀` ↦ `DesignatedFor V₀`. So the dial's two constructors are
*literally* the two modes — the modes ARE the dial's endpoints. -/
def DialHolds [DVKernel Verifier Statement Proof VSecret]
    (dial : TransferDial Verifier) (stmt : Statement) (proof : Proof) : Prop :=
  match dial with
  | .transferable        => Transferable Verifier (VSecret := VSecret) stmt proof
  | .designated V₀ => DesignatedFor (VSecret := VSecret) V₀ stmt proof

/-! ## (a) PUBLIC mode is transferable / non-repudiable. -/

/-- **`public_is_transferable`** — the transferable-endpoint dial setting is exactly `Transferable`:
definitional, pinning that the `transferable` constructor denotes universal convincing. -/
theorem public_is_transferable [DVKernel Verifier Statement Proof VSecret]
    (stmt : Statement) (proof : Proof)
    (h : DialHolds (VSecret := VSecret) (Verifier := Verifier) .transferable stmt proof) :
    Transferable Verifier (VSecret := VSecret) stmt proof := h

/-- **`public_convinces_any_third_party`** — NON-REPUDIATION. If a transcript is transferable, any
third party `W` is convinced (`DischargedFor W`). The authorizer cannot deny it to anyone: the
non-repudiation that dregg's verifier-index-free `presentation.rs::verify` (`:224`) forces on every
authorization. -/
theorem public_convinces_any_third_party [DVKernel Verifier Statement Proof VSecret]
    (stmt : Statement) (proof : Proof)
    (h : Transferable Verifier (VSecret := VSecret) stmt proof) (W : Verifier) :
    DischargedFor (VSecret := VSecret) W stmt proof :=
  h W

/-- **`publicMode_collapses_to_universal`** — the current dregg behaviour (`Laws.Discharged` with no
verifier index, `presentation.rs:224`) is exactly the `transferable` endpoint of the dial: the `∀ V`
collapse that the pre-existing model used all along. -/
theorem publicMode_collapses_to_universal [DVKernel Verifier Statement Proof VSecret]
    (stmt : Statement) (proof : Proof) :
    DialHolds (VSecret := VSecret) (Verifier := Verifier) .transferable stmt proof
      ↔ ∀ V : Verifier, DischargedFor (VSecret := VSecret) V stmt proof :=
  Iff.rfl

/-! ## (b) DESIGNATED mode is NON-transferable — a party other than `V₀` is not convinced. -/

/-- **`designated_convinces_V0`** — the designated verifier `V₀` is convinced: the first conjunct of
the designated endpoint. The mode is not vacuous on the side that matters to `V₀`. -/
theorem designated_convinces_V0 [DVKernel Verifier Statement Proof VSecret]
    {V₀ : Verifier} {stmt : Statement} {proof : Proof}
    (h : DesignatedFor (VSecret := VSecret) V₀ stmt proof) :
    DischargedFor (VSecret := VSecret) V₀ stmt proof := h.1

/-- **`designated_not_transferable`** — a designated-verifier transcript is NOT transferable. From
`¬ Transferable` (= `¬ ∀ V, …`) we extract a concrete verifier `W` the transcript does not convince
(`¬ DischargedFor W`). A third party other than `V₀` can genuinely fail to be persuaded — the
opposite of non-repudiation, a behaviour dregg's universal verify cannot produce. -/
theorem designated_not_transferable [DVKernel Verifier Statement Proof VSecret]
    {V₀ : Verifier} {stmt : Statement} {proof : Proof}
    (h : DesignatedFor (VSecret := VSecret) V₀ stmt proof) :
    ∃ W : Verifier, ¬ DischargedFor (VSecret := VSecret) W stmt proof := by
  -- `h.2 : ¬ ∀ V, DischargedFor V stmt proof`; classically this yields an unconvinced witness.
  have hne : ¬ ∀ V : Verifier, DischargedFor (VSecret := VSecret) V stmt proof := h.2
  by_contra hall
  exact hne (fun V => not_not.mp (fun hV => hall ⟨V, hV⟩))

/-! ## (c) DESIGNATED mode is DENIABLE — the simulator repudiation. -/

/-- **`designated_is_deniable`** — the simulator / repudiation argument. For any statement and any
designated verifier `V₀`, there exists a transcript that `V₀` accepts yet that `V₀` produced itself
from its own verification-secret (`proof = simulate (vsecret V₀) stmt`). Because `V₀` could have
manufactured the very transcript that convinces it, the transcript is zero evidence to any third party
that the authorizer ever authorized `stmt`: the authorizer can repudiate. Rests on the §8 simulator
law `DVKernel.simulate_verifies` (the crypto obligation) — used here but not proved here. -/
theorem designated_is_deniable [DVKernel Verifier Statement Proof VSecret]
    (V₀ : Verifier) (stmt : Statement) :
    ∃ proof : Proof,
      DischargedFor (VSecret := VSecret) V₀ stmt proof
        ∧ proof = DVKernel.simulate (Verifier := Verifier) (Statement := Statement)
            (Proof := Proof) (VSecret := VSecret)
            (DVKernel.vsecret (Statement := Statement) (Proof := Proof) (VSecret := VSecret) V₀)
            stmt := by
  refine ⟨DVKernel.simulate (Verifier := Verifier) (Statement := Statement)
            (Proof := Proof) (VSecret := VSecret)
            (DVKernel.vsecret (Statement := Statement) (Proof := Proof) (VSecret := VSecret) V₀)
            stmt, ?_, rfl⟩
  -- the simulated transcript verifies under V₀ — the §8 simulator law, not a Lean derivation
  exact DVKernel.simulate_verifies V₀ stmt

/-- **`repudiation_no_third_party_evidence`** — deniability contrapositive. A transcript `V₀` could
have simulated tells a third party `W` nothing about whether the authorizer authorized `stmt`: it does
not entail `DischargedFor W`. Deniability ⇒ the authorization is NOT forced onto `W`. -/
theorem repudiation_no_third_party_evidence [DVKernel Verifier Statement Proof VSecret]
    {V₀ : Verifier} {stmt : Statement} {proof : Proof}
    (h : DesignatedFor (VSecret := VSecret) V₀ stmt proof) :
    ¬ Transferable Verifier (VSecret := VSecret) stmt proof := h.2

/-! ## (d) The two modes are the dial's two ENDPOINTS — a witnessed separation (not vacuous). -/

/-- **`designated_excludes_public`** — the designated endpoint is disjoint from the transferable
endpoint: a transcript in the designated mode is NOT transferable. The dial's two settings denote
genuinely different propositions on the same transcript. -/
theorem designated_excludes_public [DVKernel Verifier Statement Proof VSecret]
    {V₀ : Verifier} {stmt : Statement} {proof : Proof}
    (h : DialHolds (VSecret := VSecret) (Verifier := Verifier) (.designated V₀) stmt proof) :
    ¬ DialHolds (VSecret := VSecret) (Verifier := Verifier) .transferable stmt proof := h.2

/-! ## A reference DV-kernel — the interface is inhabitable (theorems are not vacuous).

A toy model with two verifiers (`v0` the designated one, `vOther` an outsider). `v0` accepts any
proof echoing its secret-derived simulation tag; `vOther` accepts only a genuine public tag.
`simulate v0secret stmt` produces exactly the tag `v0` echoes — the §8 law holds by construction,
and there exist statements/proofs witnessing both endpoints. -/
namespace Reference

/-- Two verifiers: the designated `v0` and an outsider `vOther`. -/
inductive V where
  | v0
  | vOther
  deriving DecidableEq, Repr

/-- Statements and proofs are `Nat` tags; verifier secrets are `Nat` (the designated trapdoor). -/
abbrev Stmt := Nat
abbrev Prf := Nat
abbrev VSec := Nat

/-- `v0`'s secret trapdoor (a fixed nonzero tag); the outsider has a distinct secret it cannot use to
forge against `v0`'s acceptance rule. -/
def secretOf : V → VSec
  | .v0     => 1
  | .vOther => 0

/-- The designated verifier `v0`'s *simulated* transcript for a statement: a trapdoor-tagged value
`stmt + secret + 1` that ONLY `v0`'s rule accepts. (The `+1` keeps it off the public-acceptance value,
so a simulated transcript is genuinely non-transferable.) -/
def sim : VSec → Stmt → Prf := fun s stmt => stmt + s + 1

/-- Each verifier accepts its own trapdoor-simulated tag (the §8 simulator law holds for every
verifier). Additionally `vOther` accepts the genuine public tag `proof = stmt`. Crucially `v0` does
NOT accept the public tag `stmt` (only its own `sim`), so the two verifiers genuinely disagree —
what makes the designated mode non-transferable in this toy. -/
def vrfy : V → Stmt → Prf → Bool
  | .v0,     stmt, proof => decide (proof = sim (secretOf .v0) stmt)
  | .vOther, stmt, proof => decide (proof = stmt) || decide (proof = sim (secretOf .vOther) stmt)

instance : DVKernel V Stmt Prf VSec where
  verifyFor := vrfy
  vsecret := secretOf
  simulate := sim
  simulate_verifies := by
    intro Vv stmt
    cases Vv with
    | v0     => simp [vrfy, sim, secretOf]
    | vOther => simp [vrfy, sim, secretOf]

/-- A transcript `v0` simulated for statement `7`: convinces `v0` (deniability witness) but NOT
`vOther` — a concrete non-transferable transcript. -/
def designatedProof : Prf := sim (secretOf .v0) 7

/-- `v0` IS convinced by its own simulated transcript (the deniability witness verifies). -/
example : DischargedFor (VSecret := VSec) V.v0 7 designatedProof := by
  unfold DischargedFor designatedProof
  simp [DVKernel.verifyFor, vrfy, sim, secretOf]

/-- `vOther` is NOT convinced by `v0`'s simulated transcript — the teeth: a third party fails to be
persuaded, so the transcript is non-transferable (`v0`'s sim tag `7+1+1=9 ≠ 7` and `≠ vOther`'s own
sim `7+0+1=8`). -/
example : ¬ DischargedFor (VSecret := VSec) V.vOther 7 designatedProof := by
  unfold DischargedFor designatedProof
  simp [DVKernel.verifyFor, vrfy, sim, secretOf]

/-- A type-pinned wrapper so the `#eval`s below can infer the reference `DVKernel V Stmt Prf VSec`
instance (the bare `DVKernel.verifyFor` leaves the four type args ambiguous). -/
def check (Vv : V) (stmt : Stmt) (proof : Prf) : Bool :=
  DVKernel.verifyFor (Statement := Stmt) (Proof := Prf) (VSecret := VSec) Vv stmt proof

/-- A type-pinned simulator wrapper. -/
def simFor (Vv : V) (stmt : Stmt) : Prf :=
  DVKernel.simulate (Verifier := V) (Statement := Stmt) (Proof := Prf) (VSecret := VSec)
    (DVKernel.vsecret (Statement := Stmt) (Proof := Prf) (VSecret := VSec) Vv) stmt

/-- **`dial_endpoints_distinct`** — on the reference kernel there is a transcript that genuinely sits
at the designated endpoint: `designatedProof` for statement `7` satisfies `DesignatedFor v0` (`v0`
convinced AND not transferable) yet fails `Transferable V` (`vOther` is not convinced). The two dial
settings denote genuinely different propositions — the endpoints are inhabited and separated. -/
theorem dial_endpoints_distinct :
    DesignatedFor (Statement := Stmt) (Proof := Prf) (VSecret := VSec) V.v0 7 designatedProof
      ∧ ¬ Transferable V (Statement := Stmt) (Proof := Prf) (VSecret := VSec) 7 designatedProof := by
  have hv0 : DischargedFor (VSecret := VSec) V.v0 7 designatedProof := by
    unfold DischargedFor designatedProof; simp [DVKernel.verifyFor, vrfy, sim, secretOf]
  have hnt : ¬ Transferable V (Statement := Stmt) (Proof := Prf) (VSecret := VSec) 7 designatedProof := by
    intro hall
    have : DischargedFor (VSecret := VSec) V.vOther 7 designatedProof := hall V.vOther
    unfold DischargedFor designatedProof at this
    simp [DVKernel.verifyFor, vrfy, sim, secretOf] at this
  exact ⟨⟨hv0, hnt⟩, hnt⟩

-- It runs: v0 accepts its simulated transcript; vOther rejects it.
#guard check V.v0 7 designatedProof              -- the designated verifier is convinced
#guard check V.vOther 7 designatedProof == false -- a third party is NOT convinced
-- the simulator law concretely: each verifier accepts its own simulation
#guard check V.v0 7 (simFor V.v0 7)
#guard check V.vOther 7 (simFor V.vOther 7)

end Reference

/-! ## Axiom audit (`propext`, `Classical.choice`, `Quot.sound` only). -/

#print axioms public_convinces_any_third_party
#print axioms designated_not_transferable
#print axioms designated_is_deniable
#print axioms Reference.dial_endpoints_distinct

end Dregg2.Authority.DV
