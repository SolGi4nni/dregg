/-
# `Dregg2.Circuit.PremiseInhabitabilitySweepSettled` — the UNKNOWN rows of
`PremiseInhabitabilitySweep` §7, SETTLED where they can be settled, at the resolution each admits.

`PremiseInhabitabilitySweep` §7 left roughly twenty-eight declarations UNKNOWN, concentrated in
rows R3, R4, R5, R9, R10, R11, R14, R15, R16. The reason it gave, uniformly, was that "the tree
never instantiates those families at a deployed verifier, so there is nothing concrete to refute
against". That reason is CORRECT for some of them and WRONG for others, and this module separates
the two by checking, per row, whether the tree already carries an instantiation.

For R11 the reason is correct at deployment and beside the point: §9 finds a vacuity mode that
needs NO instantiation to fire, because it lives on the CONCLUSION rather than the antecedent, and
at one member of the family no deployment could repair it.

## §A what the check found (the headline, before any detail)

Four of the UNKNOWN rows were never abstract in the first place, and one was wrong in the same way
the sweep's own R18 correction was wrong:

  * **R3** (`AggAirSound.FriExtract`) — "never instantiated at the deployed verifier" is true of the
    DEPLOYED STARK verifier and false of the tree: `FriExtractNonCircular.friExtract_nonCircular`
    instantiates it at `FriExtractReal`'s carriers, whose `verify` runs a real FRI fold/codeword
    check and PROVABLY REJECTS (`verify_rejects_far`). §1 re-reads that instantiation through the
    instrument: the acceptance predicate is `Discriminating`, the floor FIRES, and the floor's own
    ANTECEDENT is discriminating too. The sweep's upper bracket
    (`aggFriExtract_inhabited_nondegenerately`) used `verify := fun _ => true`; this one does not.
  * **R9** (`FriExtractNonCircular.TranscriptOfPolynomial`) — not abstract: `friAccepts`, `vkOf`,
    `piOf` are concrete definitions, and the module DISCHARGES the residual at an honest instance
    (`honest_transcript_of_polynomial`). §1 records the verdict INHABITABLE with the antecedent
    SATISFIED, and adds the lower bracket the row was missing.
  * **R10** (`Emit/AccumulatorNonRevocationComplete.Accepts` / `NonMemberWitness`) — contains no
    abstract verifier at all. §3 SETTLES it: the accept-set is INHABITED and DISCRIMINATING, by
    exhibited witness and by refutation at `acc = 0, alpha = h`.
  * **R15** (`AssuranceCaseGrounded.BroaderCryptoReductionSuite.bls_quorum`) — its three-conjunct
    antecedent is jointly SATISFIED at `BlsThreshold.passingCert` and jointly REFUTED at
    `subQuorumCert`. §4 assembles that as the row's verdict.
  * **R16** (`Spec/VatBoundary.PhiFunctorial.preserves_id`) — settled in BOTH directions in §5:
    PROVED UNINHABITABLE at a verifier that accepts nothing (the module states this in prose at
    `VatBoundary.lean:447`; here it is a theorem), and INHABITABLE at `phi_functorial_concrete`.

## §B what was genuinely abstract, and what was done with it

  * **R5** — the nine `*LeafFriFloor` classes. The sweep machine-checked ONE (`Custom`) and reported
    the other eight as READ. §2 machine-checks all NINE against one shape (`LeafFloorShape`), each
    identity by `Iff.rfl` — which is the actual check that the body is the same — and fires both
    brackets at all nine. The eight are no longer "reasoned".
  * **R14** (`Circuit/AirSoundness.airChecks`) — genuinely parametric, and therefore BRACKETABLE
    rather than unknown. §6 proves the row's own flagged shape is a real hole: at ANY `openTr`
    whose opened tail is never `[]`, `airChecks` REJECTS EVERY proof, and `circuit_sound_via_fri`'s
    conclusion `CircuitSound applyEff (airChecks …)` then holds for EVERY `applyEff` — including
    effect semantics unrelated to the circuit. The upper bracket is a concrete instantiation at
    which `airChecks` accepts AND `FriProximity` holds.
  * **R4** (`GroundedApex.BindingExtract`) — the sweep proved it FREE on non-verifying aggregates
    (the vacuity direction). §7 adds the other direction, and it is sharper than "not free": at the
    EMPTY CHAIN the floor is outright FALSE wherever the binding verifier accepts, because its
    conclusion demands a trace that both satisfies the binding AIR (`rows ≠ []`) and `Represents []`
    (`rows = []`). §7 also records that the OBVIOUS mirror bracket — "no satisfying binding-AIR
    trace forces rejection" — is NOT available, because `BindingAirSound.satisfies_two` refutes its
    hypothesis for every `hash`.

## §C what is NOT settled here, stated so this module is not over-read

  * **R11** (thirteen carrier-gated kernels) — its DEPLOYMENT verdict is unchanged and UNKNOWN, and
    §9.6 says exactly what would settle it and why that is not engineering. But `CarrierLive` is NOT
    the right instrument: §9 proves it INSUFFICIENT. Both modes the sweep found are about the
    ANTECEDENT; a THIRD mode lives on the CONCLUSION, where a total conclusion makes the gated
    theorem free with the carrier and acceptance deleted, and `CarrierLive` still reports green.
    It is FIRED at two of the thirteen and shown ABSENT at a third. The sibling lane's MODE-1
    carrier repair is orthogonal and neither supersedes the other.
  * **NOTHING here proves anything about the DEPLOYED STARK/FRI verifier.** R3's and R9's
    instantiation is `FriExtractReal`: a 4-point BabyBear evaluation domain folding to 2 points.
    That is a REAL verifier in the sense that matters for vacuity — it rejects — and it is NOT the
    deployed one. The deployed-configuration verdict for R3/R5/R9 remains UNKNOWN, and §1 says so
    in the theorem names rather than only in prose.
  * **R9's `∀ w` form is still open.** `friExtract_nonCircular` consumes
    `∀ w, TranscriptOfPolynomial k pts w Q`; the tree discharges ONE `w`. §1.4 states exactly what
    the gap is and what would close it.
  * The `#assert_axioms` lines at the bottom check what these proofs REST ON. As
    `PremiseInhabitability` §B says, they are structurally blind to the wound being measured.
-/
import Dregg2.Circuit.PremiseInhabitabilitySweep
import Dregg2.Circuit.FriExtractNonCircular
import Dregg2.Circuit.FactoryBindingFromFold
import Dregg2.Circuit.HatcheryBindingFromFold
import Dregg2.Circuit.MembershipBindingFromFold
import Dregg2.Circuit.SovereignBindingFromFold
import Dregg2.Circuit.DslBindingFromFold
import Dregg2.Circuit.DecoBindingFromFold
import Dregg2.Circuit.BridgeBindingFromFold
import Dregg2.Circuit.BlindedMembershipBindingFromFold
import Dregg2.Circuit.AirSoundness
import Dregg2.Circuit.Emit.AccumulatorNonRevocationComplete
import Dregg2.Crypto.BlsThreshold
import Dregg2.Crypto.NonMembership
import Dregg2.Crypto.PortalFloor
import Dregg2.Crypto.Temporal
import Dregg2.Spec.VatBoundary

namespace Dregg2.Circuit.PremiseInhabitabilitySweepSettled

universe u v

open Dregg2.Circuit.PremiseInhabitability
  (Acc Empties Extracts RejectsAll AcceptsSome ofBool not_rejectsAll_of_acceptsSome
   empties_proves_anything not_of_empties_of_acceptsSome)
open Dregg2.Circuit.PremiseInhabitabilitySweep (Discriminating CarrierLive)

set_option autoImplicit false

/-! ## §1 — R3 and R9: the `FriExtract` family IS instantiated in-tree, at a REJECTING verifier.

`PremiseInhabitabilitySweep` R3/S5 reads: "quantified over an ABSTRACT `ChildVerifierSat`/`verify`;
never instantiated at the deployed verifier in-tree, so there is no acceptance predicate to test
against." The second half is right about the DEPLOYED verifier and wrong about the tree.
`Dregg2/Circuit/FriExtractReal.lean` builds `ChildProof`, a `friAccepts` that runs the actual FRI
fold relation and final-codeword check, and a `verify` that is `friAccepts` as a classical `Bool`;
`Dregg2/Circuit/FriExtractNonCircular.lean:271` then proves `AggAirSound.FriExtract` at exactly
those carriers. So the acceptance predicate the sweep says does not exist DOES exist, and every
question the instrument asks can be asked of it. -/

section R3R9

open Dregg2.Circuit.FriExtractReal
open Dregg2.Circuit.FriExtractNonCircular
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.BabyBearFriSetup (pVal fHonest)
open Dregg2.Circuit.FriQuerySoundness (Accepts)
open Dregg2.Circuit.RsUniqueDecoding (evalVec)
open Polynomial

/-- The in-tree child-proof acceptance predicate, in the instrument's vocabulary. This is the
`acc` the R3 row says does not exist. -/
def realChildAcc : Acc ChildProof := ofBool verify

/-- **R3, FIRST HALF — the acceptance predicate is `Discriminating`.** It accepts `honestProof`
(a genuine low-degree codeword folded at `α = 0`) and rejects `farProof` (whose fold leaves the
folded code). This is precisely the positive control `PremiseInhabitabilitySweep` R17 names as the
thing the STARK/FRI bundle family never had, discharged here for the recursion-child verifier. -/
theorem realChildAcc_discriminating : Discriminating realChildAcc := by
  refine ⟨⟨honestProof, ?_⟩, ⟨farProof, ?_⟩⟩
  · exact verify_accepts_honest
  · intro h
    have h' : verify farProof = true := h
    rw [verify_rejects_far] at h'
    exact Bool.noConfusion h'

/-- Neither degenerate bracket of `PremiseInhabitabilitySweep` §4 applies to the real carriers:
the verifier is not the dead one, and it is not the total one either. -/
theorem realCarriers_are_neither_degenerate_bracket :
    (¬ ∀ q : ChildProof, verify q = false) ∧ ¬ (∀ q : ChildProof, realChildAcc q) := by
  refine ⟨?_, Dregg2.Circuit.PremiseInhabitabilitySweep.discriminating_not_total
    realChildAcc_discriminating⟩
  intro hdead
  have h := verify_accepts_honest
  rw [hdead honestProof] at h
  exact Bool.noConfusion h

/-- **R3, SECOND HALF — the floor's own ANTECEDENT is discriminating too.** `ColumnsCVS` is
satisfied at the honest column word and REFUTED at the commitment `-1` (no column word pins a
negative VK core, since `vkOf` reads a `.val`). So the R3 instantiation is not the cheap model
obtained by emptying the antecedent, and it is not the cheap model obtained by making the
antecedent trivially true either. -/
theorem columnsCVS_discriminating :
    ColumnsCVS 2 pVal QH (vkOf fHonest) (piOf fHonest)
      ∧ ¬ ColumnsCVS 2 pVal QH (-1) (piOf fHonest) :=
  ⟨honest_columnsCVS, columnsCVS_falsifiable 2 pVal QH _⟩

/-- **R3 — THE VERDICT, ASSEMBLED.** At the in-tree real carriers, under the residual the module
names, `AggAirSound.FriExtract` HOLDS; its acceptance predicate is discriminating; and the
extraction FIRES on an actual run. Retaining the class's full applied shape as the subject means a
regression in `friExtract_nonCircular`'s statement breaks this theorem rather than passing silently.

⚑ Read exactly what this is: `FriExtractReal`'s domain is `Fin 4` folding to `Fin 2` over BabyBear.
It settles that R3 is not an empty notion and not satisfiable only at an accept-everything verifier.
It does NOT settle R3 at the deployed configuration — `AggAirSound.FriExtract` is still never
instantiated at `CircuitSoundness.verifyBatch`, and that verdict remains UNKNOWN. -/
theorem aggFriExtract_settled_at_a_real_rejecting_verifier {m : ℕ} (k : ℕ)
    (pts : Fin 4 → BabyBear) (Q : Fin m → Fin 4)
    (hTP : ∀ w : Fin 4 → BabyBear, TranscriptOfPolynomial k pts w Q) :
    FriExtract ChildProof verify vkCommit exposedPI (ColumnsCVS k pts Q)
      ∧ Discriminating realChildAcc
      ∧ (∃ π : ChildProof, realChildAcc π
          ∧ vkCommit π = vkOf fHonest ∧ exposedPI π = piOf fHonest) := by
  refine ⟨friExtract_nonCircular k pts Q hTP, realChildAcc_discriminating, ?_⟩
  obtain ⟨π, hv, hvk, hpi⟩ := nonCircular_extract_fires
  exact ⟨π, hv, hvk, hpi⟩

/-! ### §1.4 — R9: `TranscriptOfPolynomial` is INHABITABLE, and it is not free. -/

/-- **R9 — INHABITABLE, NON-DEGENERATELY.** The residual HOLDS at the honest instance AND its
antecedent is SATISFIED there: `pHon` is in-degree, at Hamming distance `0` from the honest column
word, and agrees with every opened value. So the R9 verdict is not UNKNOWN at the class level; the
class has a model with a live antecedent, exhibited over concrete carriers.

This is the sweep's own non-degeneracy standard (`leafFloor_inhabited_nondegenerately`) applied to
a row it left unexamined, and it uses the module's OWN discharge rather than a fresh toy. -/
theorem transcriptOfPolynomial_inhabited_nondegenerately :
    TranscriptOfPolynomial 2 pVal fHonest QH
      ∧ (∃ p : Polynomial BabyBear, p.natDegree < 2
          ∧ 2 * hammingDist fHonest (evalVec pVal p) + 2 ≤ 4
          ∧ Accepts fHonest (evalVec pVal p) QH) :=
  ⟨honest_transcript_of_polynomial, honest_childSat.proximity⟩

/-- **R9 — THE LOWER BRACKET: the residual is NOT free.** Wherever its antecedent is satisfiable at
all, `TranscriptOfPolynomial` FORCES the real FRI acceptance predicate to accept something. So
carrying it is carrying the claim that the child verifier accepts — the same reading
`deadVerifier_empties_leafFloor` gives the leaf floors, at the row the sweep could not reach.

Contrapositive, which is the vacuity statement: at carriers where FRI accepts NOTHING, this
residual empties its own antecedent — no column word is both in-radius and opening-consistent. -/
theorem transcriptOfPolynomial_forces_fri_acceptance {m : ℕ} (k : ℕ) (pts w : Fin 4 → BabyBear)
    (Q : Fin m → Fin 4) (hTP : TranscriptOfPolynomial k pts w Q)
    (p : Polynomial BabyBear) (hdeg : p.natDegree < k)
    (hball : 2 * hammingDist w (evalVec pts p) + k ≤ 4)
    (hacc : Accepts w (evalVec pts p) Q) :
    AcceptsSome realChildAcc := by
  obtain ⟨π, hfri, -, -⟩ := hTP (vkOf w) (piOf w) p hdeg hball hacc ⟨rfl, rfl⟩
  exact ⟨π, (verify_iff π).mpr hfri⟩

/-- **R9 — WHAT REMAINS OPEN, STATED AS A GAP RATHER THAN A SHRUG.** `friExtract_nonCircular`
consumes the `∀ w` form; the tree discharges the residual at ONE `w`. The two are not the same
proposition, and this theorem is the honest bridge: the `∀ w` form is exactly what is needed, and
the single-`w` discharge does not supply it.

What would settle the `∀ w` form: a FRI-completeness / prover-simulation argument over
`babyBearFriSetup` — given a `natDegree < k` polynomial within the unique-decoding radius of `w`,
build a fold challenge `α` and a folded oracle in `C'` reading back `(vkOf w, piOf w)`. That is
engineering plus a real (small) argument, not a missing primitive: the domain is `Fin 4 → Fin 2`,
the codes are concrete `Submodule`s, and `fHonest_fold_mem` already does the honest case. It is not
`decide`-able because `BabyBear` arithmetic here is noncomputable. -/
theorem friExtract_at_real_carriers_needs_the_forall_form {m : ℕ} (k : ℕ)
    (pts : Fin 4 → BabyBear) (Q : Fin m → Fin 4) :
    (∀ w : Fin 4 → BabyBear, TranscriptOfPolynomial k pts w Q) →
      FriExtract ChildProof verify vkCommit exposedPI (ColumnsCVS k pts Q) :=
  friExtract_nonCircular k pts Q

/-- **⚑ THE DEGENERATE DISCHARGE, recorded so §1 cannot be misread as "R3 is discharged".** The
`∀ w` residual DOES have a free proof — at `k > 4` the proximity antecedent `2·d + k ≤ 4` is
unsatisfiable, so `TranscriptOfPolynomial` holds at every column word for nothing. This is the cheap
model, and the next theorem shows what it buys: nothing, because the floor's own antecedent is empty
there too. Any unconditional instantiation of R3 at the real carriers must therefore be checked
against the width, exactly as `leafFloor_is_free_when_unsatisfiable` warns for R5. -/
theorem transcriptOfPolynomial_is_free_above_the_decoding_radius {m : ℕ} (k : ℕ)
    (pts : Fin 4 → BabyBear) (Q : Fin m → Fin 4) (hk : 4 < k) :
    ∀ w : Fin 4 → BabyBear, TranscriptOfPolynomial k pts w Q := by
  intro _ _ _ _ _ hball _ _
  omega

/-- …and the cheap discharge buys nothing: above the decoding radius `ColumnsCVS` is EMPTY, so the
`FriExtract` it yields quantifies over no pinned pair at all. The pairing of these two theorems is
what makes `aggFriExtract_settled_at_a_real_rejecting_verifier`'s residual hypothesis load-bearing
rather than dischargeable for free. -/
theorem columnsCVS_is_empty_above_the_decoding_radius {m : ℕ} (k : ℕ)
    (pts : Fin 4 → BabyBear) (Q : Fin m → Fin 4) (hk : 4 < k) (c : ℤ) (s : Seg) :
    ¬ ColumnsCVS k pts Q c s := by
  rintro ⟨w, hsat, -⟩
  obtain ⟨p, -, hball, -⟩ := hsat.proximity
  omega

end R3R9

/-! ## §2 — R5: ALL NINE `*LeafFriFloor` classes, machine-checked (not eight READ).

`PremiseInhabitabilitySweep` R5 instantiated its brackets at the `Custom` member and reported the
other eight as "the SAME body with the projection renamed (verified by reading each `def`)". That
is a reading, and a reading is exactly what this campaign is supposed to distrust: a renamed
projection could have a different type, a flipped conjunct, or an extra binder, and nothing would
notice. Here the nine bodies are checked against ONE shape by `Iff.rfl` — which typechecks only if
the body really is the same up to the engine projection — and both brackets fire at all nine. -/

section R5

open Dregg2.Circuit.DescriptorIR2 (ProofEngine demoEngine)
open Dregg2.Circuit.DecoBackingAttack (DecoEngine demoDeco)
open Dregg2.Circuit.BridgeBackingAttack (NoteSpendEngine demoSpend)

/-- **The `*LeafFriFloor` SHAPE, once.** `P` is the sub-proof type, `verify` its accepting bit, and
`digest` the lane the leaf exposes (`piCommit` for seven of the nine, `paymentDigest` for DECO,
`spendDigest` for the bridge note-spend). -/
def LeafFloorShape (P : Type) (verify : P → Bool) (digest : P → ℤ) (Sat : ℤ → ℤ → Prop) : Prop :=
  ∀ leafVk leafCommit : ℤ, Sat leafVk leafCommit →
    ∃ q : P, verify q = true ∧ digest q = leafCommit

/-- The shape IS the instrument's `Extracts`, so everything in `PremiseInhabitability` applies. -/
theorem leafFloorShape_iff_extracts (P : Type) (verify : P → Bool) (digest : P → ℤ)
    (Sat : ℤ → ℤ → Prop) :
    LeafFloorShape P verify digest Sat
      ↔ Extracts (fun p : ℤ × ℤ => Sat p.1 p.2)
          (fun p (q : P) => verify q = true ∧ digest q = p.2) := by
  constructor
  · intro h p hp; exact h p.1 p.2 hp
  · intro h a b hab; exact h (a, b) hab

/-- **THE LOWER BRACKET, generically.** A leaf verifier that rejects everything makes the floor
EMPTY the in-circuit satisfaction predicate. So each of the nine is exactly as strong as the claim
that its leaf verifier accepts something. -/
theorem deadVerifier_empties_leafFloorShape (P : Type) (verify : P → Bool) (digest : P → ℤ)
    (Sat : ℤ → ℤ → Prop) (hdead : ∀ q : P, verify q = false) :
    Empties (LeafFloorShape P verify digest Sat) (fun p : ℤ × ℤ => Sat p.1 p.2) := by
  intro h p hp
  obtain ⟨q, hq, -⟩ := h p.1 p.2 hp
  rw [hdead q] at hq
  exact Bool.noConfusion hq

/-- **THE UPPER BRACKET, generically.** At any engine with ONE accepting proof the floor holds with
its antecedent SATISFIED — a non-degenerate model, not the free one obtained by emptying the
antecedent. -/
theorem leafFloorShape_inhabited_nondegenerately (P : Type) (verify : P → Bool) (digest : P → ℤ)
    (q₀ : P) (hq₀ : verify q₀ = true) :
    LeafFloorShape P verify digest (fun _ c => c = digest q₀)
      ∧ (∃ a b : ℤ, (fun (_ : ℤ) (c : ℤ) => c = digest q₀) a b) :=
  ⟨fun _ _ hab => ⟨q₀, hq₀, hab.symm⟩, ⟨0, digest q₀, rfl⟩⟩

/-- The degenerate model, recorded so the previous theorem cannot be mistaken for it. -/
theorem leafFloorShape_is_free_when_unsatisfiable (P : Type) (verify : P → Bool) (digest : P → ℤ)
    (Sat : ℤ → ℤ → Prop) (hno : ∀ a b, ¬ Sat a b) :
    LeafFloorShape P verify digest Sat :=
  fun a b hab => absurd hab (hno a b)

/-! ### §2.1 — the nine identities, each by `Iff.rfl`.

`Iff.rfl` is the machine-check: it typechecks only if the class body is DEFINITIONALLY the shape at
the stated projection. A renamed field, a flipped conjunct, or an extra binder in any of the nine
makes the corresponding line fail to elaborate. -/

theorem customLeafFriFloor_is_the_shape (E : ProofEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.CustomBindingFromFold.CustomLeafFriFloor E Sat
      ↔ LeafFloorShape E.Proof E.verify E.piCommit Sat := Iff.rfl

theorem factoryLeafFriFloor_is_the_shape (E : ProofEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.FactoryBindingFromFold.FactoryLeafFriFloor E Sat
      ↔ LeafFloorShape E.Proof E.verify E.piCommit Sat := Iff.rfl

theorem contractLeafFriFloor_is_the_shape (E : ProofEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.HatcheryBindingFromFold.ContractLeafFriFloor E Sat
      ↔ LeafFloorShape E.Proof E.verify E.piCommit Sat := Iff.rfl

theorem membershipLeafFriFloor_is_the_shape (E : ProofEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.MembershipBindingFromFold.MembershipLeafFriFloor E Sat
      ↔ LeafFloorShape E.Proof E.verify E.piCommit Sat := Iff.rfl

theorem sovereignLeafFriFloor_is_the_shape (E : ProofEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.SovereignBindingFromFold.SovereignLeafFriFloor E Sat
      ↔ LeafFloorShape E.Proof E.verify E.piCommit Sat := Iff.rfl

theorem dslLeafFriFloor_is_the_shape (E : ProofEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.DslBindingFromFold.DslLeafFriFloor E Sat
      ↔ LeafFloorShape E.Proof E.verify E.piCommit Sat := Iff.rfl

theorem blindedLeafFriFloor_is_the_shape (E : ProofEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.BlindedMembershipBindingFromFold.BlindedLeafFriFloor E Sat
      ↔ LeafFloorShape E.Proof E.verify E.piCommit Sat := Iff.rfl

/-- The DECO leaf exposes `paymentDigest`, not `piCommit` — the one place the "same body with the
projection renamed" reading had to be checked rather than assumed. It IS the same shape. -/
theorem decoLeafFriFloor_is_the_shape (E : DecoEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.DecoBindingFromFold.DecoLeafFriFloor E Sat
      ↔ LeafFloorShape E.Proof E.verify E.paymentDigest Sat := Iff.rfl

/-- The bridge note-spend leaf exposes `spendDigest`. Same shape. -/
theorem noteSpendLeafFriFloor_is_the_shape (E : NoteSpendEngine) (Sat : ℤ → ℤ → Prop) :
    Dregg2.Circuit.BridgeBindingFromFold.NoteSpendLeafFriFloor E Sat
      ↔ LeafFloorShape E.Proof E.verify E.spendDigest Sat := Iff.rfl

/-! ### §2.2 — both brackets, fired at all nine. -/

/-- **R5 LOWER BRACKET AT ALL NINE.** At any engine whose leaf verifier rejects everything, EVERY
one of the nine floors empties its in-circuit satisfaction predicate. None of the nine is free. -/
theorem deadVerifier_empties_all_nine_leafFloors
    (E : ProofEngine) (D : DecoEngine) (N : NoteSpendEngine) (Sat : ℤ → ℤ → Prop)
    (hE : ∀ q : E.Proof, E.verify q = false)
    (hD : ∀ q : D.Proof, D.verify q = false)
    (hN : ∀ q : N.Proof, N.verify q = false) :
    Empties (Dregg2.Circuit.CustomBindingFromFold.CustomLeafFriFloor E Sat)
        (fun p : ℤ × ℤ => Sat p.1 p.2)
      ∧ Empties (Dregg2.Circuit.FactoryBindingFromFold.FactoryLeafFriFloor E Sat)
        (fun p : ℤ × ℤ => Sat p.1 p.2)
      ∧ Empties (Dregg2.Circuit.HatcheryBindingFromFold.ContractLeafFriFloor E Sat)
        (fun p : ℤ × ℤ => Sat p.1 p.2)
      ∧ Empties (Dregg2.Circuit.MembershipBindingFromFold.MembershipLeafFriFloor E Sat)
        (fun p : ℤ × ℤ => Sat p.1 p.2)
      ∧ Empties (Dregg2.Circuit.SovereignBindingFromFold.SovereignLeafFriFloor E Sat)
        (fun p : ℤ × ℤ => Sat p.1 p.2)
      ∧ Empties (Dregg2.Circuit.DslBindingFromFold.DslLeafFriFloor E Sat)
        (fun p : ℤ × ℤ => Sat p.1 p.2)
      ∧ Empties (Dregg2.Circuit.BlindedMembershipBindingFromFold.BlindedLeafFriFloor E Sat)
        (fun p : ℤ × ℤ => Sat p.1 p.2)
      ∧ Empties (Dregg2.Circuit.DecoBindingFromFold.DecoLeafFriFloor D Sat)
        (fun p : ℤ × ℤ => Sat p.1 p.2)
      ∧ Empties (Dregg2.Circuit.BridgeBindingFromFold.NoteSpendLeafFriFloor N Sat)
        (fun p : ℤ × ℤ => Sat p.1 p.2) :=
  ⟨deadVerifier_empties_leafFloorShape _ _ _ Sat hE,
   deadVerifier_empties_leafFloorShape _ _ _ Sat hE,
   deadVerifier_empties_leafFloorShape _ _ _ Sat hE,
   deadVerifier_empties_leafFloorShape _ _ _ Sat hE,
   deadVerifier_empties_leafFloorShape _ _ _ Sat hE,
   deadVerifier_empties_leafFloorShape _ _ _ Sat hE,
   deadVerifier_empties_leafFloorShape _ _ _ Sat hE,
   deadVerifier_empties_leafFloorShape _ _ _ Sat hD,
   deadVerifier_empties_leafFloorShape _ _ _ Sat hN⟩

/-- **R5 UPPER BRACKET AT ALL NINE.** Each of the nine HOLDS with its antecedent SATISFIED at the
tree's own demo engines (`demoEngine`, `demoDeco`, `demoSpend`), all of which have an accepting
proof. So none of the nine is an empty notion, and R5's UNKNOWN is about the deployed
instantiation only. -/
theorem all_nine_leafFloors_inhabited_nondegenerately :
    (Dregg2.Circuit.CustomBindingFromFold.CustomLeafFriFloor demoEngine (fun _ c => c = 123)
      ∧ Dregg2.Circuit.FactoryBindingFromFold.FactoryLeafFriFloor demoEngine (fun _ c => c = 123)
      ∧ Dregg2.Circuit.HatcheryBindingFromFold.ContractLeafFriFloor demoEngine (fun _ c => c = 123)
      ∧ Dregg2.Circuit.MembershipBindingFromFold.MembershipLeafFriFloor demoEngine
          (fun _ c => c = 123)
      ∧ Dregg2.Circuit.SovereignBindingFromFold.SovereignLeafFriFloor demoEngine
          (fun _ c => c = 123)
      ∧ Dregg2.Circuit.DslBindingFromFold.DslLeafFriFloor demoEngine (fun _ c => c = 123)
      ∧ Dregg2.Circuit.BlindedMembershipBindingFromFold.BlindedLeafFriFloor demoEngine
          (fun _ c => c = 123)
      ∧ Dregg2.Circuit.DecoBindingFromFold.DecoLeafFriFloor demoDeco (fun _ c => c = 123)
      ∧ Dregg2.Circuit.BridgeBindingFromFold.NoteSpendLeafFriFloor demoSpend (fun _ c => c = 123))
    ∧ (∃ a b : ℤ, (fun (_ : ℤ) (c : ℤ) => c = (123 : ℤ)) a b) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨0, 123, rfl⟩⟩ <;>
    exact fun _ _ hab => ⟨true, rfl, hab.symm⟩

end R5

/-! ## §3 — R10: `AccumulatorNonRevocationComplete` — SETTLED, no abstract verifier involved.

R10 read "not examined at the resolution the other entries were". Examined, it is not an
abstract-verifier row at all: `Accepts` is defined by an existential over a CONCRETE `Satisfied2`
against the CONCRETE `accumulatorNonRevDesc`, and the module already proves it equivalent to
`NonMemberWitness` in both directions. So the instrument's two questions — is the accept-set
inhabited, and is it discriminating — are both decidable here, and both are answered. -/

section R10

open Dregg2.Circuit.Emit.AccumulatorNonRevocationRefine
  (Ext ezero eone eadd esub emul ExtModEq unit_not_modEq_ezero emul_ezero_right)
open Dregg2.Circuit.Emit.AccumulatorNonRevocationComplete
  (Accepts NonMemberWitness witness_implies_accepts accepts_implies_witness)

/-- The non-revocation accept-set, in the instrument's vocabulary. -/
def accumAcc : Acc (Ext × Ext × Ext) := fun r => Accepts r.1 r.2.1 r.2.2

/-- **R10, FIRST HALF — the accept-set is INHABITED.** The trivial non-membership certificate
(`w = 0`, remainder `v = 1`, inverse `1`) is a genuine `NonMemberWitness`, which BUILDS an accepting
`Satisfied2` trace through the module's own completeness bridge. So this premise quantifies over a
non-empty set — the check `PremiseInhabitability` §C could never run on the FRI bundles. -/
theorem accumAcc_acceptsSome : AcceptsSome accumAcc := by
  have h1 : eadd (emul ezero (esub ezero ezero)) eone = eone := by decide
  have h2 : emul eone eone = eone := by decide
  refine ⟨(ezero, eone, ezero), witness_implies_accepts ⟨ezero, eone, eone, ?_, ?_⟩⟩
  · rw [h1]
    exact Dregg2.Circuit.Emit.AccumulatorNonRevocationRefine.ExtModEq.refl _
  · rw [h2]
    exact Dregg2.Circuit.Emit.AccumulatorNonRevocationRefine.ExtModEq.refl _

/-- **R10, SECOND HALF — the accept-set is DISCRIMINATING.** With `alpha = h` the certificate
equation collapses to `acc ≡ v`, and the `check` gate forces the remainder `v` to be a field UNIT;
a unit is never `≡ 0` (`unit_not_modEq_ezero`, no primality). So `(alpha, 0, alpha)` is REJECTED —
the accumulator zero at a challenge equal to the hashed leaf is not accepted for ANY witness.

This is the tooth the sweep's R17 positive controls have and the FRI bundle family lacks: the
predicate is neither empty nor total, proved rather than assumed. -/
theorem accumAcc_rejects_zero_at_matching_leaf (alpha : Ext) :
    ¬ accumAcc (alpha, ezero, alpha) := by
  intro hacc
  have hacc' : Accepts alpha ezero alpha := hacc
  obtain ⟨w, v, vinv, heq, hchk⟩ := accepts_implies_witness hacc'
  refine unit_not_modEq_ezero v vinv hchk ?_
  have hsub : esub alpha alpha = ezero := by
    cases alpha with
    | mk a b c d => simp [esub, ezero]
  have hadd : eadd ezero v = v := by
    cases v with
    | mk a b c d => simp [eadd, ezero]
  rw [hsub, emul_ezero_right, hadd] at heq
  exact heq.symm

/-- **R10 — THE VERDICT.** `Accepts` is inhabited and discriminating. R10 is SETTLED, and settled
positively: the row is not an emptied-premise site. -/
theorem accumAcc_discriminating : Discriminating accumAcc :=
  ⟨accumAcc_acceptsSome, ⟨(ezero, ezero, ezero), accumAcc_rejects_zero_at_matching_leaf ezero⟩⟩

end R10

/-! ## §4 — R15: the assurance case's `bls_quorum` premise — SETTLED.

R15 read "inhabitability of `accepts ∧ SnarkContract ∧ BlsContract` was not examined. Recorded as
unexamined." Examined, `Dregg2/Crypto/BlsThreshold.lean` already carries a reference committee with
BOTH polarities, and this section assembles them into the verdict the row wanted. -/

section R15

open Dregg2.Crypto.BlsThreshold
open Dregg2.Crypto.BlsThreshold.Reference

/-- Certificate acceptance, in the instrument's vocabulary, at the reference 3-of-4 committee. -/
def blsAcc : Acc (ThresholdCert fed4 99) := fun cert => cert.accepts

/-- **R15 — THE THREE-CONJUNCT PREMISE IS JOINTLY INHABITED.** `passingCert` satisfies acceptance,
the SNARK contract, AND the BLS contract simultaneously — so `bls_quorum`'s antecedent is not empty
and the field is not vacuously discharged. -/
theorem blsQuorum_premise_inhabited :
    passingCert.accepts ∧ passingCert.SnarkContract ∧ passingCert.BlsContract :=
  ⟨passingCert_accepts, passingCert_snark, passingCert_bls⟩

/-- **R15 — AND THE PREMISE BITES.** `subQuorumCert` carries a genuine SNARK contract and is
REJECTED (its selected weight is below threshold), so acceptance is DISCRIMINATING; and
`nonsigner_breaks_bls` shows the `BlsContract` conjunct is not `True`-fillable. Both degenerate
modes are excluded. -/
theorem blsAcc_discriminating : Discriminating blsAcc :=
  ⟨⟨passingCert, passingCert_accepts⟩, ⟨subQuorumCert, subQuorum_rejected⟩⟩

/-- **R15 — THE CONCLUSION FIRES.** Under the inhabited premise the suite field's own conclusion is
delivered at the reference committee: a sub-committee `S` of members, reaching the threshold,
within the total weight, every member of which signed. Not vacuous, and not a re-labelling. -/
theorem blsQuorum_conclusion_fires :
    ∃ S : Finset ℕ, S ⊆ fed4.members ∧ fed4.selectedWeight S ≥ passingCert.threshold
      ∧ fed4.selectedWeight S ≤ fed4.totalWeight ∧ (∀ i ∈ S, fed4.SignedBy i 99) :=
  accepting_cert_has_quorum passingCert passingCert_accepts passingCert_snark passingCert_bls

end R15

/-! ## §5 — R16: `VatBoundary.PhiFunctorial.preserves_id` — SETTLED IN BOTH DIRECTIONS.

R16 read "the shape with a CONFERRAL antecedent rather than verifier acceptance. Not examined."
Examined, the row is a `preserves_id` field demanding an ACCEPTING WITNESS to exist, and
`VatBoundary.lean:447` says in prose that it is FALSE over an abstract `Verifiable` whose `Verify`
accepts nothing. Prose is not a verdict. Here it is a theorem, and its counterpart — the concrete
non-degenerate model — is the module's own `phi_functorial_concrete`. -/

section R16

open Dregg2.Spec (PhiFunctorial Phi Cap confers confers_refl Guard)
open Dregg2.Laws (Verifiable Discharged)

/-- The applied shape R16 names, with the `Verifiable` instance left as an explicit argument so the
SAME shape can be refuted at one instance and proved at another. `Φ` here is the maximally-lossy
`stmtOf ≡ ()` on caps over `CellId := Bool`, `Rights := Unit` — exactly the carriers
`Dregg2.Spec.phi_functorial_concrete` uses. -/
abbrev PhiFunctorialAt (V : Verifiable Unit Bool) : Prop :=
  @PhiFunctorial Unit Unit Bool Bool Unit _ _ V (@Phi Bool Unit Unit Unit (fun _ => ()))

/-- A verifier that accepts NOTHING — the degenerate `Verifiable` `VatBoundary.lean:447` names in
prose ("an abstract `Verify` may accept none — e.g. `Verify ≡ false`"). It is a perfectly legal
instance of the class. -/
@[reducible] def deadVerifiable : Verifiable Unit Bool := ⟨fun _ _ => false⟩

/-- **R16, FIRST HALF — `preserves_id` IS UNINHABITABLE at any verifier that accepts nothing.**
`Φ`'s image is always a `witnessed` guard, whose `admits` is literally the `Verify` bit; if `Verify`
is constantly `false` then NO witness supply discharges it, while `confers c c` holds for EVERY cap
(`confers_refl`). So the whole `PhiFunctorial` structure is FALSE there — not merely unwitnessed.

The broken shape is retained as the subject (`PhiFunctorialAt` is `PhiFunctorial` applied to `Phi`
at the concrete model's own carriers), so a change to the structure's fields breaks this theorem
rather than letting the refutation lapse silently. -/
theorem phiFunctorial_uninhabitable_at_a_dead_verifier
    (V : Verifiable Unit Bool) (hdead : ∀ (s : Unit) (b : Bool), V.Verify s b = false) :
    ¬ PhiFunctorialAt V := by
  intro h
  obtain ⟨w, hw⟩ := h.preserves_id ⟨true, ()⟩ () (confers_refl _)
  have hd : @Discharged Unit Bool V () (w ()) :=
    (Guard.admits_witnessed_iff_discharged (Witness := Bool) () () w).mp hw
  have hv : V.Verify () (w ()) = true := hd
  rw [hdead] at hv
  exact Bool.noConfusion hv

/-- Fired at the concrete dead instance. -/
theorem phiFunctorial_false_at_deadVerifiable : ¬ PhiFunctorialAt deadVerifiable :=
  phiFunctorial_uninhabitable_at_a_dead_verifier deadVerifiable (fun _ _ => rfl)

/-- **R16, SECOND HALF — and it IS inhabited at a discriminating verifier.** The module's own
concrete model (`Verify s b := b`, which accepts `true` and rejects `false`) satisfies all three
fields simultaneously, so `PhiFunctorial` is not an empty notion. -/
theorem phiFunctorial_inhabited_at_a_discriminating_verifier :
    PhiFunctorialAt Dregg2.Spec.concreteVerifiable :=
  Dregg2.Spec.phi_functorial_concrete

/-- **R16 — THE VERDICT, IN ONE STATEMENT.** The SAME applied shape is REFUTED at one legal
`Verifiable` instance and PROVED at another. So `PhiFunctorial.preserves_id` is exactly as strong as
the claim that the far side's verify seam accepts something — the `CarrierLive`-style criterion, at
a row the sweep did not reach. What is UNKNOWN, precisely, is which `Verifiable` instance a deployed
vat boundary installs; the tree installs none, and the row's UNKNOWN is about that and nothing
else. -/
theorem phiFunctorial_settled_both_ways :
    (∃ V : Verifiable Unit Bool, ¬ PhiFunctorialAt V)
      ∧ (∃ V : Verifiable Unit Bool, PhiFunctorialAt V) :=
  ⟨⟨deadVerifiable, phiFunctorial_false_at_deadVerifiable⟩,
   ⟨Dregg2.Spec.concreteVerifiable, phiFunctorial_inhabited_at_a_discriminating_verifier⟩⟩

end R16

/-! ## §6 — R14: `AirSoundness.airChecks` — the flagged shape IS a hole, bracketed.

R14 flagged that acceptance "is DEFINED by an existential requiring the opened trace tail to be `[]`
— the known 'one side requires the list empty' shape — but `openTr`/`verifyLD` are abstract
parameters with no deployed instantiation, so there is nothing to refute against." There is: the
parameters are UNIVERSALLY quantified in `circuit_sound_via_fri`, so the theorem's guarantee is only
as good as its WORST instantiation, and the worst one is exhibited below. -/

section R14

open Dregg2.Circuit.AirSoundness
open Dregg2.Crypto.TurnSoundness (CircuitSound)

/-- **R14 LOWER BRACKET — `airChecks` REJECTS EVERYTHING whenever the commitment opens to a
multi-row trace.** The boundary conjunct pins the opened tail to `[]`; an `openTr` that always
returns a nonempty tail therefore has no accepting `(π, old, eff, new)` at all. Since a deployed
AIR commits to a MULTI-ROW execution trace, this is not an exotic instantiation — it is the shape
of the realistic one, and the single-row pin is what excludes it. -/
theorem airChecks_rejectsAll_of_multirow_opening
    {State Effect Proof Commitment : Type}
    (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect))
    (hmulti : ∀ com, (openTr com).2 ≠ []) :
    RejectsAll (fun q : Proof × State × Effect × State =>
      airChecks verifyLD openTr q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  rintro q ⟨com, -, hopen⟩
  exact hmulti com (congrArg Prod.snd hopen)

/-- **R14 — THE CONSEQUENCE, which is the actual finding.** At such an instantiation
`circuit_sound_via_fri`'s conclusion `CircuitSound applyEff (airChecks …)` holds for EVERY
`applyEff` — including effect semantics that have nothing to do with the circuit — and holds with NO
`FriProximity` hypothesis at all. So on those instantiations the theorem transmits zero information
about the AIR, exactly as `empties_proves_anything` describes.

This does NOT say `circuit_sound_via_fri` is wrong. It says its universally-quantified `openTr`
parameter admits instantiations at which its conclusion is free, so a consumer must exhibit that its
`openTr` really opens to a single row — which nothing in the tree does. -/
theorem circuitSound_is_free_at_multirow_opening
    {State Effect Proof Commitment : Type}
    (verifyLD : Proof → Commitment → Prop)
    (openTr : Commitment → Step State Effect × List (Step State Effect))
    (hmulti : ∀ com, (openTr com).2 ≠ [])
    (applyEff : Effect → State → State) :
    CircuitSound applyEff (airChecks verifyLD openTr) := by
  intro π old eff new h
  exact absurd h (airChecks_rejectsAll_of_multirow_opening verifyLD openTr hmulti (π, old, eff, new))

/-- **THE LOWER BRACKET'S HYPOTHESIS IS SATISFIABLE** — an opener that returns a two-row trace.
Recorded so `circuitSound_is_free_at_multirow_opening` is not itself a statement with an empty
hypothesis: multi-row is what a deployed AIR commits to. -/
theorem multirowOpener_exists :
    ∀ com : Step ℕ ℕ, ((fun c => (c, [c])) com : Step ℕ ℕ × List (Step ℕ ℕ)).2 ≠ [] :=
  fun com => List.cons_ne_nil com []

/-- **FIRED — the "proves anything" reading, concretely.** At a two-row opener the SAME `airChecks`
predicate is certified sound for `fun _ s => s + 1` AND for `fun _ s => s` — two effect semantics
that cannot both be the circuit's. A theorem certifying both certifies neither. -/
theorem circuitSound_free_for_contradictory_semantics (verifyLD : Unit → Step ℕ ℕ → Prop) :
    CircuitSound (fun _ s => s + 1) (airChecks verifyLD (fun c => (c, [c])))
      ∧ CircuitSound (fun _ (s : ℕ) => s) (airChecks verifyLD (fun c => (c, [c]))) :=
  ⟨circuitSound_is_free_at_multirow_opening verifyLD _ multirowOpener_exists _,
   circuitSound_is_free_at_multirow_opening verifyLD _ multirowOpener_exists _⟩

/-- The single-row opener the upper bracket uses: the commitment IS the row, opened with no tail. -/
def unitOpen : Step ℕ ℕ → Step ℕ ℕ × List (Step ℕ ℕ) := fun com => (com, [])

/-- The low-degree verifier accepts exactly the honest row `0 --(+1)--> 1`. Discriminating, not
`fun _ _ => True`. -/
def honestLD : Unit → Step ℕ ℕ → Prop := fun _ com => com = honestHead

/-- **R14 UPPER BRACKET — a NON-DEGENERATE instantiation.** At `honestLD`/`unitOpen` the checker
ACCEPTS a run, REJECTS another, and the `FriProximity` interface `circuit_sound_via_fri` consumes
genuinely HOLDS. So R14's shape is not an empty notion, and the lower bracket above is not the only
model — which is what makes the pair a bracket rather than a refutation. -/
theorem airChecks_inhabited_nondegenerately :
    airChecks honestLD unitOpen () 0 1 1
      ∧ (¬ airChecks honestLD unitOpen () 0 1 5)
      ∧ FriProximity toyApply honestLD unitOpen := by
  refine ⟨⟨honestHead, rfl, rfl⟩, ?_, ?_⟩
  · rintro ⟨com, hv, hopen⟩
    have h1 : com = honestHead := hv
    subst h1
    have h2 : (unitOpen honestHead).1 = (⟨0, 1, 5⟩ : Step ℕ ℕ) := congrArg Prod.fst hopen
    have h3 : honestHead.post = (5 : ℕ) := congrArg Step.post h2
    simp [honestHead] at h3
  · intro _ com hv
    have h1 : com = honestHead := hv
    subst h1
    exact ⟨rfl, trivial⟩

/-- **R14 — THE VERDICT.** The row's flagged "requires the list empty" shape is a REAL hole: it
admits a whole family of instantiations on which the soundness conclusion is free, and it admits
non-degenerate ones. The deployed verdict stays UNKNOWN for the reason the row gave — nothing in the
tree instantiates `openTr` — but the row is no longer merely flagged: the falsifier a deployed
instantiation must survive is now written down. -/
theorem airChecks_bracketed
    (verifyLD : Unit → Step ℕ ℕ → Prop)
    (openTr : Step ℕ ℕ → Step ℕ ℕ × List (Step ℕ ℕ))
    (hmulti : ∀ com, (openTr com).2 ≠ []) :
    (∀ applyEff : ℕ → ℕ → ℕ, CircuitSound applyEff (airChecks verifyLD openTr))
      ∧ airChecks honestLD unitOpen () 0 1 1 :=
  ⟨fun applyEff => circuitSound_is_free_at_multirow_opening verifyLD openTr hmulti applyEff,
   airChecks_inhabited_nondegenerately.1⟩

end R14

/-! ## §7 — R4: `GroundedApex.BindingExtract` — the missing direction.

The sweep proved `BindingExtract` FREE on aggregates whose binding proof does not verify
(`bindingExtract_is_free_when_the_binding_proof_fails`). That is the vacuity direction. The other
direction — that it is not free in general — was left open, and is the one a consumer needs. -/

section R4

open Dregg2.Circuit.GroundedApex (BindingExtract)
open Dregg2.Circuit.BindingAirSound (Satisfies)
open Dregg2.Circuit.RecursiveAggregation (Aggregate)
open Dregg2.Exec (CellId Value RecordKernelState)
open Dregg2.Distributed.HistoryAggregation (ChainStep)

/-! ⚑ THE OBVIOUS LOWER BRACKET IS NOT AVAILABLE, AND THAT IS WORTH RECORDING. The natural mirror of
`deadVerifier_empties_leafFloor` would be "at any instantiation with NO satisfying binding-AIR
trace, the floor forces rejection". That theorem would be VACUOUS: `BindingAirSound.satisfies_two`
inhabits `Satisfies hash …` for EVERY `hash`, so its hypothesis is refutable and the theorem would
carry no content. The real bracket is elsewhere, and it is sharper. -/

/-- **R4 — `BindingExtract` IS AN EMPTYING PREMISE AT THE EMPTY CHAIN.** Its conclusion demands a
trace that BOTH satisfies the binding AIR — which requires `rows ≠ []` (`Satisfies.nonempty`, the
Rust C7/nonempty constraint) — AND `Represents` the given `steps`, which at `steps = []` forces
`rows = []`. The two are jointly impossible, so at `steps = []` the floor forces the binding
verifier to REJECT EVERY aggregate's binding proof.

This is not a hypothetical instantiation: `steps` is the caller's chain, and `GroundedApex`'s
grounded binding leg consumes `BindingExtract … steps` at whatever chain it is handed. On the empty
one, the premise is the wound class exactly — and unconditionally, with no side hypothesis. -/
theorem bindingExtract_at_the_empty_chain_empties_binding_acceptance
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) :
    Empties (∀ agg : Aggregate Proof,
        BindingExtract Proof verify hash CH RH cmb compress compressN agg [])
      (fun agg : Aggregate Proof => verify agg.bindingProof = true) := by
  intro h agg hacc
  obtain ⟨rows, pub, hsat, hrep, -, -, -⟩ := h agg hacc
  cases rows with
  | nil => exact hsat.nonempty rfl
  | cons r rest => simp [Dregg2.Circuit.BindingAirSound.Represents] at hrep

/-- **AND THEREFORE THE PREMISE IS FALSE, not merely uninformative**, at any instantiation whose
binding verifier accepts the aggregate's binding proof. This is the sharpest verdict the instrument
has (`not_of_empties_of_acceptsSome`), fired at R4. -/
theorem bindingExtract_at_the_empty_chain_is_false
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (hacc : verify agg.bindingProof = true) :
    ¬ BindingExtract Proof verify hash CH RH cmb compress compressN agg [] := by
  intro h
  obtain ⟨rows, pub, hsat, hrep, -, -, -⟩ := h hacc
  cases rows with
  | nil => exact hsat.nonempty rfl
  | cons r rest => simp [Dregg2.Circuit.BindingAirSound.Represents] at hrep

/-- The per-aggregate reading: at the empty chain the floor forces this aggregate's binding proof to
fail verification. -/
theorem bindingExtract_at_the_empty_chain_forces_rejection
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof)
    (h : BindingExtract Proof verify hash CH RH cmb compress compressN agg []) :
    verify agg.bindingProof = false := by
  rcases Bool.eq_false_or_eq_true (verify agg.bindingProof) with hb | hb
  · exact absurd h (bindingExtract_at_the_empty_chain_is_false Proof verify hash CH RH cmb compress
      compressN agg hb)
  · exact hb

/-- The refutation's hypotheses are SATISFIABLE — a concrete aggregate over an accepting verifier —
so `bindingExtract_at_the_empty_chain_is_false` is not itself an empty statement. -/
theorem bindingExtract_refutation_hypotheses_are_satisfiable :
    ¬ Dregg2.Circuit.GroundedApex.BindingExtract Unit (fun _ => true) (fun _ => 0)
        (fun _ _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
        { root := (), leafProofs := [], bindingProof := (), genesisRoot := 0, finalRoot := 0,
          numTurns := 0, chainDigest := 0 } [] :=
  bindingExtract_at_the_empty_chain_is_false Unit (fun _ => true) (fun _ => 0) (fun _ _ => 0)
    (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) _ rfl

/-- **R4 — THE TWO DIRECTIONS TOGETHER.** The floor is FREE where the binding proof fails (the
sweep's result) and FALSE at the empty chain where it verifies (this module's). So `BindingExtract`
is not a conservative thing to carry: on the same abstract parameters it is alternately vacuous and
refuted, and the only region where it says something is one nobody in the tree has exhibited. The
deployment verdict is unchanged — no deployed binding verifier is instantiated — but the row is no
longer bracketed on one side only. -/
theorem bindingExtract_bracketed
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (aggRej aggAcc : Aggregate Proof) (steps : List ChainStep)
    (hrej : verify aggRej.bindingProof = false)
    (hacc : verify aggAcc.bindingProof = true) :
    BindingExtract Proof verify hash CH RH cmb compress compressN aggRej steps
      ∧ ¬ BindingExtract Proof verify hash CH RH cmb compress compressN aggAcc [] :=
  ⟨Dregg2.Circuit.PremiseInhabitabilitySweep.bindingExtract_is_free_when_the_binding_proof_fails
      Proof verify hash CH RH cmb compress compressN aggRej steps hrej,
   bindingExtract_at_the_empty_chain_is_false Proof verify hash CH RH cmb compress compressN
     aggAcc hacc⟩

end R4

/-! ## §9 — R11: A THIRD VACUITY MODE, ON THE CONCLUSION SIDE, THAT `CarrierLive` CANNOT SEE.

`PremiseInhabitabilitySweep` §5 proved the carrier-gated kernel family admits TWO independent
vacuity modes — MODE 1, a FALSE carrier (the gated theorem stays true and becomes unappliable), and
MODE 2, an EMPTY accept-set (it quantifies over nothing) — and built `CarrierLive` as the criterion
excluding both. R11 was then left UNKNOWN at deployment, and a sibling lane owns the MODE-1 carrier
repair.

`CarrierLive` is not sufficient, and the gap is not hypothetical. Both known modes are about the
ANTECEDENT — the carrier and the accept-set. NEITHER LOOKS AT THE CONCLUSION. If the conclusion is
TOTAL — true on every run — the gated theorem is free: it holds with the carrier, the verifier and
the acceptance hypothesis ALL DELETED, while `CarrierLive` reports green, `#assert_axioms` reports
clean, and no `sorry` exists. Call it MODE 3.

It is the `∃-image vacuity` shape at this family. Every one of the thirteen conclusions is an
existential (`∃ circuit …`, `∃ leaves …`, `∃ wit …`, `∃ rows …`), and an existential whose witness
is not pinned by the statement is satisfiable for free.

⚑ THIS IS NOT A SPECULATIVE MODE. Below it is FIRED at two members of the family, at two DIFFERENT
strengths, and shown ABSENT at a third — so the criterion discriminates rather than accusing
everything:

  * **`NonMembershipVerifierKernel` — MODE 3 AT EVERY INSTANTIATION, deployed or not.**
    `nonmembership_verify_sound`'s conclusion is `∃ leaves, NonMember leaves stmt.elem`, and
    `leaves := []` discharges it for every `Digest` and every statement. The theorem never mentions
    `stmt.root`. This is not an UNKNOWN awaiting a deployed verifier: no deployment can repair it,
    because the conclusion is a tautology of the `List` type. §9.2.
  * **`MerkleVerifierKernel` — MODE 3 AT THE REFERENCE KERNEL's node hash.** `MerkleMembers` DOES
    mention the root, so it is not a tautology — but at `compress := (· + ·)` over `ℤ` it is TOTAL,
    since `[⟨root - leaf, 0⟩]` recomposes any root from any leaf. And the polarity INVERTS against
    the carrier axis: at the FORGE kernel's collapsing hash the conclusion is refutable, while at
    the reference kernel it is not. The instance the sweep cited as the family's reassurance
    (`referenceMerkleKernel_carrierLive`) is the one whose conclusion says nothing. §9.3.
  * **`TemporalVerifierKernel` — MODE 3 ABSENT.** `temporal_verify_sound`'s conclusion is
    `InWindow lo hi t`, not an existential, and it is refutable at `lo = 1, hi = 0`. So MODE 3 is a
    property of particular members, not of carrier-gating as such. §9.4.

§9.5 then corrects the row's COUNT in the other direction: not every `extractable := True` is the
R11 wound, and one live instance (`PrivateLeg.lean:275`) is retired as a false positive by a
checkable property of its proof type rather than by a reading of intent.

What this does and does not settle for R11 is stated exactly in §9.6. -/

section R11

open Dregg2.Crypto.Merkle (MerkleMembers Step recompose)
open Dregg2.Crypto.NonMembership (NonMember Sorted)
open Dregg2.Crypto.Temporal (InWindow)

/-! ### §9.1 — the mode, and the criterion, generically. -/

/-- **`ConclusionTotal C`** — the gated theorem's conclusion holds on EVERY index, accepted or not. -/
def ConclusionTotal {ι : Type u} (C : ι → Prop) : Prop := ∀ i, C i

/-- **`ConclusionBites C`** — the conclusion FAILS somewhere, so asserting it excludes something.
This is the conclusion-side analogue of `AcceptsSome`, and it is what MODE 3 destroys. -/
def ConclusionBites {ι : Type u} (C : ι → Prop) : Prop := ∃ i, ¬ C i

/-- **MODE 3, GENERICALLY.** A total conclusion makes the carrier-gated shape FREE — provable with
the carrier and the acceptance hypothesis discarded, exactly as `falseCarrier_proves_anything` and
`rejectsAll_proves_anything` are free for the other two modes. Note what is NOT needed: no
assumption whatsoever about `carrier` or `acc`. -/
theorem totalConclusion_makes_the_gated_theorem_free {ι : Type u} (carrier : Prop) (acc : Acc ι)
    {C : ι → Prop} (htot : ConclusionTotal C) : carrier → ∀ i, acc i → C i :=
  fun _ i _ => htot i

/-- The two are exclusive: a conclusion cannot both bite and be total. -/
theorem not_conclusionTotal_of_conclusionBites {ι : Type u} {C : ι → Prop}
    (h : ConclusionBites C) : ¬ ConclusionTotal C := by
  obtain ⟨i, hi⟩ := h
  exact fun htot => hi (htot i)

/-- **`CarrierBites`** — the criterion that excludes ALL THREE modes: the carrier holds, acceptance
is inhabited, AND the conclusion is refutable somewhere. `CarrierLive` is the first two. -/
def CarrierBites {ι : Type u} (carrier : Prop) (acc : Acc ι) (C : ι → Prop) : Prop :=
  CarrierLive carrier acc ∧ ConclusionBites C

theorem carrierBites_excludes_falseCarrier {ι : Type u} {carrier : Prop} {acc : Acc ι}
    {C : ι → Prop} (h : CarrierBites carrier acc C) : carrier := h.1.1

theorem carrierBites_excludes_rejectsAll {ι : Type u} {carrier : Prop} {acc : Acc ι}
    {C : ι → Prop} (h : CarrierBites carrier acc C) : ¬ RejectsAll acc :=
  not_rejectsAll_of_acceptsSome h.1.2

theorem carrierBites_excludes_totalConclusion {ι : Type u} {carrier : Prop} {acc : Acc ι}
    {C : ι → Prop} (h : CarrierBites carrier acc C) : ¬ ConclusionTotal C :=
  not_conclusionTotal_of_conclusionBites h.2

/-- **THE INSTRUMENT'S BLIND SPOT, AS A THEOREM.** `CarrierLive` can hold — carrier proved,
acceptance inhabited, both vacuity modes the sweep knows about excluded — while the gated theorem
is still free. So `CarrierLive` is NECESSARY and NOT SUFFICIENT, and every green `CarrierLive`
report in `PremiseInhabitabilitySweep` §5 must be re-read as a partial check.

The witness is deliberately non-degenerate: the accept-set is a genuine two-valued predicate on `ℕ`
(accepting `0`, rejecting everything else), so the failure is not an artifact of a silly index
type. -/
theorem carrierLive_does_not_exclude_mode3 :
    ∃ (carrier : Prop) (acc : Acc ℕ) (C : ℕ → Prop),
      CarrierLive carrier acc ∧ Discriminating acc ∧ ConclusionTotal C
        ∧ (carrier → ∀ i, acc i → C i) := by
  refine ⟨True, ofBool (fun n => decide (n = 0)), fun _ => True,
    ⟨trivial, ⟨0, rfl⟩⟩, ⟨⟨0, rfl⟩, ⟨1, by simp [ofBool]⟩⟩, fun _ => trivial, ?_⟩
  exact totalConclusion_makes_the_gated_theorem_free _ _ (fun _ => trivial)

/-- **THE THREE MODES ARE PAIRWISE INDEPENDENT.** `PremiseInhabitabilitySweep`'s
`the_two_vacuity_modes_are_independent` showed modes 1 and 2 do not imply each other. MODE 3 is
independent of BOTH: the witness above has a TRUE carrier and an INHABITED, DISCRIMINATING
accept-set, so neither of the first two checks can see it. Checking any two of the three is
therefore not a check. -/
theorem mode3_is_independent_of_the_first_two :
    ∃ (carrier : Prop) (acc : Acc ℕ) (C : ℕ → Prop),
      carrier ∧ AcceptsSome acc ∧ ConclusionTotal C ∧ ¬ CarrierBites carrier acc C := by
  refine ⟨True, ofBool (fun n => decide (n = 0)), fun _ => True, trivial, ⟨0, rfl⟩,
    fun _ => trivial, ?_⟩
  rintro ⟨-, i, hi⟩
  exact hi trivial

/-! ### §9.2 — FIRED: `NonMembershipVerifierKernel` is MODE 3 at EVERY instantiation.

`nonmembership_verify_sound` (`NonMembership.lean:262`) concludes
`∃ leaves : List Digest, NonMember leaves stmt.elem`. `NonMember leaves e` is
`Sorted leaves ∧ e ∉ leaves` (`:116`), and `Sorted` is `List.Pairwise (· < ·)` (`:42`). The empty
list is sorted and contains nothing. So the conclusion is discharged by `[]`, for every ordered
`Digest` and every statement — and note what is absent from the conclusion: `stmt.root`. The
committed list the root was supposed to bind (the module's own doc comment: "the committed leaf
list is HIDDEN; `compress` CR is what binds the prover's claimed list to `root` — the `extractable`
carrier") is existentially quantified, and the existential lets it be replaced by `[]`. -/

/-- **THE TAUTOLOGY.** `nonmembership_verify_sound`'s conclusion, with every hypothesis removed. -/
theorem nonMember_conclusion_is_total {Digest : Type u} [LinearOrder Digest] (e : Digest) :
    ∃ leaves : List Digest, NonMember leaves e :=
  ⟨[], List.Pairwise.nil, fun h => List.not_mem_nil h⟩

/-- Stated as MODE 3 in the instrument's vocabulary, over statements as the index type. -/
theorem nonmembership_conclusion_is_mode3 (Digest : Type u) [LinearOrder Digest] :
    ConclusionTotal
      (fun s : Dregg2.Crypto.NonMembership.Statement Digest =>
        ∃ leaves : List Digest, NonMember leaves s.elem) :=
  fun s => nonMember_conclusion_is_total s.elem

/-- **AND THEREFORE `nonmembership_verify_sound` IS FREE — at every kernel, deployed or not.** The
gated shape it instantiates holds with the carrier and the acceptance hypothesis DELETED. Whatever
verifier a deployment installs, whatever carrier it discharges, the theorem's conclusion was
already true. The `extractable` carrier is doing no work here at all.

RETAINED SUBJECT: the statement is over `K.verify` and `K.extractable` of an arbitrary in-tree
`NonMembershipVerifierKernel`, so a repair to the class that actually pins the leaf list to
`stmt.root` breaks this theorem rather than letting the finding lapse silently. -/
theorem nonmembership_verify_sound_is_free {Digest Proof : Type u} [LinearOrder Digest]
    (K : Dregg2.Crypto.NonMembership.NonMembershipVerifierKernel Digest Proof) :
    K.extractable → ∀ s : Dregg2.Crypto.NonMembership.Statement Digest × Proof,
      (ofBool (fun p : Dregg2.Crypto.NonMembership.Statement Digest × Proof =>
        K.verify p.1 p.2)) s → ∃ leaves : List Digest, NonMember leaves s.1.elem :=
  totalConclusion_makes_the_gated_theorem_free _ _ (fun p => nonMember_conclusion_is_total p.1.elem)

/-- **THE SHARPEST READING: the conclusion does not separate accepted from REJECTED statements.**
It holds at a statement the verifier demonstrably rejects. A soundness theorem that cannot tell its
accepted runs from its rejected ones is not conditioning on acceptance in any operative sense.

The rejection hypothesis is named `_hrej` because the proof DOES NOT USE IT — that unusedness is
the entire content of the theorem, not an oversight. -/
theorem nonmembership_conclusion_holds_at_rejected_statements {Digest Proof : Type u}
    [LinearOrder Digest] (K : Dregg2.Crypto.NonMembership.NonMembershipVerifierKernel Digest Proof)
    (stmt : Dregg2.Crypto.NonMembership.Statement Digest) (proof : Proof)
    (_hrej : K.verify stmt proof = false) :
    ∃ leaves : List Digest, NonMember leaves stmt.elem :=
  nonMember_conclusion_is_total stmt.elem

/-- The verdict in the criterion's vocabulary: `CarrierBites` is UNREACHABLE for this class, at any
instantiation whatsoever. No deployment can supply the third conjunct. -/
theorem nonmembership_carrierBites_is_unreachable {Digest Proof : Type u} [LinearOrder Digest]
    (K : Dregg2.Crypto.NonMembership.NonMembershipVerifierKernel Digest Proof)
    (acc : Acc (Dregg2.Crypto.NonMembership.Statement Digest)) :
    ¬ CarrierBites K.extractable acc
        (fun s => ∃ leaves : List Digest, NonMember leaves s.elem) :=
  fun h => carrierBites_excludes_totalConclusion h (nonmembership_conclusion_is_mode3 Digest)

/-! ### §9.3 — FIRED: `MerkleVerifierKernel` is MODE 3 at the REFERENCE kernel's node hash.

`MerkleMembers compress root leaf` is `∃ path ≠ [], recompose compress leaf path = root` — it DOES
mention the root, so unlike §9.2 it is not a tautology of the type. Whether it bites depends
entirely on `compress`, and at the reference kernel's `compress := (· + ·)` over `ℤ` it does not:
one step with sibling `root - leaf` reaches any root from any leaf. -/

/-- **MODE 3 AT THE REFERENCE NODE HASH.** For every root and leaf, the single-step path
`[⟨root - leaf, 0⟩]` recomposes the root. So `MerkleMembers (· + ·)` is TOTAL over `ℤ`. -/
theorem merkleMembers_total_at_additive_compress (root leaf : Int) :
    MerkleMembers (Digest := Int) (· + ·) root leaf := by
  refine ⟨[{ sib := root - leaf, position := 0 }], List.cons_ne_nil _ _, ?_⟩
  show leaf + (root - leaf) = root
  omega

theorem merkleMembers_is_mode3_at_additive_compress :
    ConclusionTotal (fun p : Int × Int => MerkleMembers (Digest := Int) (· + ·) p.1 p.2) :=
  fun p => merkleMembers_total_at_additive_compress p.1 p.2

/-- **AND THEREFORE `merkle_verify_sound` IS FREE AT THE REFERENCE KERNEL.** The gated shape holds
with the carrier and the acceptance hypothesis DELETED — at exactly the instance
`PremiseInhabitabilitySweep.referenceMerkleKernel_carrierLive` offered as the family's reassurance,
and exactly the instance whose carrier a sibling lane has just repaired to be separately proved and
separately refuted. Both repairs are on the ANTECEDENT axis; neither touches this. -/
theorem merkle_verify_sound_is_free_at_the_reference_kernel (carrier : Prop) (acc : Acc (Int × Int)) :
    carrier → ∀ p, acc p → MerkleMembers (Digest := Int) (· + ·) p.1 p.2 :=
  totalConclusion_makes_the_gated_theorem_free carrier acc merkleMembers_is_mode3_at_additive_compress

/-- A collapsing node hash sends every non-empty path to `0`. Proved locally rather than imported so
this section does not ride on a file another lane is editing. -/
theorem recompose_collapses (path : List (Step Int)) :
    ∀ leaf : Int, path ≠ [] → recompose (fun _ _ => (0 : Int)) leaf path = 0 := by
  induction path with
  | nil => intro _ h; exact absurd rfl h
  | cons _ rest ih =>
    intro leaf _
    cases rest with
    | nil => rfl
    | cons t ts => exact ih 0 (by simp)

/-- **THE POLARITY INVERSION — the finding that makes §9.3 more than an isolated toy.** At the
FORGE kernel's collapsing node hash the conclusion BITES (`MerkleMembers` is refutable at
`root = 1`); at the REFERENCE kernel's additive node hash it does NOT. So on the conclusion axis the
family's "broken" instance is the informative one and its "good" instance is the vacuous one — the
exact opposite of the carrier axis, where the reference kernel's carrier is proved and the forge's
is refuted.

The two axes are orthogonal, and a kernel is only worth anything when it passes BOTH. Neither
`Empties`, nor `CarrierLive`, nor an axiom audit, nor a `sorry` scan sees this axis. -/
theorem merkle_conclusion_axis_inverts_against_the_carrier_axis :
    ConclusionTotal (fun p : Int × Int => MerkleMembers (Digest := Int) (· + ·) p.1 p.2)
      ∧ ConclusionBites (fun p : Int × Int => MerkleMembers (fun _ _ => (0 : Int)) p.1 p.2) := by
  refine ⟨merkleMembers_is_mode3_at_additive_compress, ⟨(1, 0), ?_⟩⟩
  rintro ⟨path, hne, hrec⟩
  rw [recompose_collapses path 0 hne] at hrec
  exact absurd hrec (by decide)

/-! ### §9.4 — THE CONTROL: `TemporalVerifierKernel` is NOT MODE 3.

`temporal_verify_sound` concludes `InWindow stmt.lo stmt.hi stmt.t`, which is `lo ≤ t ∧ t ≤ hi` —
not an existential, and false at an empty window. So MODE 3 is a property of PARTICULAR members of
the family (those whose conclusion existentially quantifies away the very object the statement was
supposed to pin), not a property of carrier-gating. Without this control §9 would be an accusation
rather than a measurement. -/

theorem temporal_conclusion_bites :
    ConclusionBites (fun s : Dregg2.Crypto.Temporal.Statement => InWindow s.lo s.hi s.t) := by
  refine ⟨{ lo := 1, hi := 0, t := 0 }, ?_⟩
  rintro ⟨hlo, -⟩
  exact absurd hlo (by decide)

theorem temporal_is_not_mode3 :
    ¬ ConclusionTotal (fun s : Dregg2.Crypto.Temporal.Statement => InWindow s.lo s.hi s.t) :=
  not_conclusionTotal_of_conclusionBites temporal_conclusion_bites

/-- **THE FAMILY IS SPLIT, AND THE SPLIT IS MACHINE-CHECKED.** Two members are MODE 3 (one at every
instantiation, one at the reference node hash) and one is not. The criterion separates them. -/
theorem the_family_splits_on_the_conclusion_axis (Digest : Type u) [LinearOrder Digest] :
    ConclusionTotal
        (fun s : Dregg2.Crypto.NonMembership.Statement Digest =>
          ∃ leaves : List Digest, NonMember leaves s.elem)
      ∧ ConclusionTotal (fun p : Int × Int => MerkleMembers (Digest := Int) (· + ·) p.1 p.2)
      ∧ ¬ ConclusionTotal (fun s : Dregg2.Crypto.Temporal.Statement => InWindow s.lo s.hi s.t) :=
  ⟨nonmembership_conclusion_is_mode3 Digest, merkleMembers_is_mode3_at_additive_compress,
   temporal_is_not_mode3⟩

/-! ### §9.5 — RETIRING A FALSE POSITIVE: `extractable := True` IS NOT ALWAYS THE R11 WOUND.

R11 counts `extractable := True` as the family's defect, and a grep for that text is how the
instances were found. The grep over-collects, and the sweep's own R18 lesson applies to its own
method: a verdict about a TEXT is not a verdict about an INSTANTIATION.

`Dregg2/Distributed/PrivateLeg.lean:275` (`honestPrivVerifier`) is a live `extractable := True` at
the real `Dregg2.Crypto.PortalFloor.VerifierKernel` class, and it is NOT the wound. Its proof type
is `Σ pl : PrivLeg, PLift (PrivLegHolds scommit pl)` — an accepting proof STRUCTURALLY CARRIES a
genuine `PrivLegHolds` proof — so extraction is free BY CONSTRUCTION and the content sits in
`verify_sound`, which is PROVED. The carrier is `True` because there is genuinely nothing left to
assume, not to avoid assuming it.

So there are two shapes behind one string:

  * **EVASIVE `True`** — the carrier names a cryptographic trust boundary (STARK extractability)
    that a DOWNSTREAM CONSUMER must discharge to use the gated theorem. Writing `True` deletes that
    obligation from every consumer at once. This is live and it BIT: `Dregg2/Verify/StripeAttest.lean`
    was discharging `DecoVerifierKernel.extractable` with `trivial : True`, which typechecked ONLY
    because the carrier was `True`; the sibling lane's repair broke it and it now supplies a real
    proof. That is the wound biting on a real consumer, which is the evidence R11 was missing.
  * **HONEST `True`** — the carrier is contentless because the WITNESS IS ALREADY IN THE DATA. No
    consumer is being let off anything, because there was nothing to let off.

⚑ THE REFINEMENT IS NECESSARY, NOT A NICETY — the existing criterion MISCLASSIFIES the honest case.
The sibling repair's test (`CarrierAudit`: a carrier is honest iff the SAME shape is REFUTABLE at a
broken sibling oracle) can never be met by `True`, so it flags `honestPrivVerifier` as wounded.
`WitnessBearing` is the side condition that retires that false positive without weakening the test
where it bites — and it is a PROPERTY OF THE INSTANTIATION, decidable by looking at the proof type,
not a reading of intent. Both sides are EXHIBITED below; nothing here is excluded middle. -/

/-- **`WitnessBearing Proof Holds`** — the proof type STRUCTURALLY carries its own conclusion: every
proof names a statement it already proves. Where this holds, extraction needs no cryptographic
assumption and the only residue is the SYNTACTIC question of whether the oracle accepts a proof at
the statement that proof carries. -/
def WitnessBearing {Stmt : Type u} (Proof : Type u) (Holds : Stmt → Prop) : Prop :=
  ∃ w : Proof → Stmt, ∀ p : Proof, Holds (w p)

/-- The canonical witness-bearing proof type — `honestPrivVerifier`'s, with `PrivLeg` abstracted. -/
theorem sigma_proof_type_is_witnessBearing {Stmt : Type} (Holds : Stmt → Prop) :
    WitnessBearing (Σ s : Stmt, PLift (Holds s)) Holds :=
  ⟨Sigma.fst, fun p => p.2.down⟩

/-- **HONEST `True`, AS A THEOREM.** At a witness-bearing proof type whose oracle accepts a proof
only at the statement that proof carries, the extraction obligation is DISCHARGED — using nothing
about the oracle beyond that syntactic acceptance equation, and no cryptographic property at all.
This is exactly why `honestPrivVerifier` may write `True` and the eight reference kernels may not. -/
theorem extraction_is_discharged_at_a_witnessBearing_proof_type
    {Stmt Proof : Type u} (Holds : Stmt → Prop) (verify : Stmt → Proof → Bool)
    (w : Proof → Stmt) (hw : ∀ p, Holds (w p))
    (hsyn : ∀ stmt proof, verify stmt proof = true → w proof = stmt) :
    True → ∀ (stmt : Stmt) (proof : Proof), verify stmt proof = true → Holds stmt := by
  intro _ stmt proof hacc
  exact hsyn stmt proof hacc ▸ hw proof

/-- `honestPrivVerifier`'s shape as a LAWFUL instance of the real in-tree class, with `PrivLeg`
abstracted to any `DecidableEq` statement type. Built here rather than imported so this section does
not ride on the `Distributed` closure; the in-tree occurrence is `PrivateLeg.lean:275`. -/
@[reducible] def witnessBearingKernel {Stmt : Type} [DecidableEq Stmt] (Holds : Stmt → Prop) :
    Dregg2.Crypto.PortalFloor.VerifierKernel Stmt (Σ s : Stmt, PLift (Holds s)) where
  Holds := Holds
  verify := fun s p => decide (p.1 = s)
  extractable := True
  verify_sound := by
    intro _ stmt proof hacc
    have heq : proof.1 = stmt := of_decide_eq_true hacc
    exact heq ▸ proof.2.down

/-- **AND WITNESS-BEARING GENUINELY FAILS AT THE FAMILY'S SHAPE.** The thirteen carrier-gated
classes quantify over an ABSTRACT `Proof` type, and no abstract proof type is witness-bearing: as
soon as the conclusion is nowhere satisfied and any proof exists, the property is FALSE. So
witness-bearing is a fact about the INSTANTIATION that the class cannot supply for its members —
which is the precise sense in which the eight reference kernels' `True` was doing work the data was
not doing. -/
theorem witnessBearing_fails_when_the_conclusion_is_unsatisfiable
    {Stmt Proof : Type u} (Holds : Stmt → Prop) (hno : ∀ s, ¬ Holds s) (p₀ : Proof) :
    ¬ WitnessBearing Proof Holds := by
  rintro ⟨w, hw⟩
  exact hno (w p₀) (hw p₀)

/-- **THE SPLIT, BOTH SIDES EXHIBITED.** One `True`-carrier instantiation is witness-bearing and its
extraction obligation HOLDS; another is not witness-bearing and its extraction obligation is FALSE
even though the identical `extractable := True` text would appear in both. So the grep that found
R11's instances cannot by itself distinguish them, and `WitnessBearing` can. -/
theorem trueCarrier_splits_on_witness_bearing :
    (∃ (Stmt Proof : Type) (Holds : Stmt → Prop) (verify : Stmt → Proof → Bool),
        WitnessBearing Proof Holds
          ∧ (True → ∀ s p, verify s p = true → Holds s))
      ∧ (∃ (Stmt Proof : Type) (Holds : Stmt → Prop) (verify : Stmt → Proof → Bool),
        ¬ WitnessBearing Proof Holds
          ∧ ¬ (True → ∀ s p, verify s p = true → Holds s)) := by
  constructor
  · refine ⟨Unit, Σ _ : Unit, PLift True, fun _ => True, fun s p => decide (p.1 = s), ?_, ?_⟩
    · exact ⟨Sigma.fst, fun p => p.2.down⟩
    · exact fun _ _ _ _ => trivial
  · refine ⟨Unit, Unit, fun _ => False, fun _ _ => true, ?_, ?_⟩
    · exact witnessBearing_fails_when_the_conclusion_is_unsatisfiable _ (fun _ h => h) ()
    · intro h
      exact h trivial () () rfl

/-- **THE FALSE POSITIVE, EXHIBITED.** The witness-bearing kernel's carrier is TRUE and
UNREFUTABLE — so the `CarrierAudit` test, which demands a refutation at a broken sibling, reports it
as wounded — while the instance is sound for a real reason the test cannot express. This is the
theorem that retires `PrivateLeg.lean:275` from R11's count. -/
theorem the_refutation_test_cannot_see_witness_bearing {Stmt : Type} [DecidableEq Stmt]
    (Holds : Stmt → Prop) :
    (witnessBearingKernel Holds).extractable
      ∧ ¬ ¬ (witnessBearingKernel Holds).extractable
      ∧ WitnessBearing (Σ s : Stmt, PLift (Holds s)) Holds :=
  ⟨trivial, fun h => h trivial, sigma_proof_type_is_witnessBearing Holds⟩

/-! ### §9.6 — WHAT §9 SETTLES FOR R11, AND WHAT IT DOES NOT.

SETTLED, and settled NEGATIVELY at a resolution no deployment can change:
`NonMembershipVerifierKernel`'s derived soundness theorem is FREE. Its conclusion is a tautology of
`List`, so this is not the usual "UNKNOWN until someone instantiates the deployed verifier" — there
is no verifier, no carrier, and no `compress` for which it says anything. The row is settled for
that one member of the thirteen, and the answer is that the member is broken.

SETTLED at the reference instantiation: `MerkleVerifierKernel`'s conclusion is TOTAL at
`compress := (· + ·)`, so the sweep's `referenceMerkleKernel_carrierLive` reassurance does not
survive the conclusion axis. It says nothing about a DEPLOYED `compress` — a real Poseidon2 node
hash is not additive, and whether `MerkleMembers` bites there is UNKNOWN and turns on preimage
resistance, which is a crypto assumption and not a Lean fact.

NOT SETTLED, and named precisely as the prompt for this sweep requires:

  * The remaining ELEVEN carrier-gated classes are NOT checked on the conclusion axis here.
    `Custom` and `Cfg` are parametric in their own relation, so their answer is "whatever the
    registration says" and there is no single verdict to give. The other nine each need the same
    two-line question asked of their conclusion, which is ENGINEERING — the instrument is now
    written down (`ConclusionBites`, `CarrierBites`) and each check is one exhibited counterexample
    or one totality proof. Nothing in the tree is missing for it.
  * The DEPLOYMENT verdict for all thirteen is UNCHANGED and UNKNOWN, for the reason R11 gave: the
    tree instantiates none of them at a deployed verifier. The instantiation that would settle it is
    a `MerkleVerifierKernel Digest Proof` whose `compress` is the real Poseidon2 node hash and whose
    `verify` is the deployed `stark::verify` — which the tree cannot build, because that `verify` is
    an `opaque`/`@[extern]` symbol with no Lean semantics. That is NOT engineering: it needs a Lean
    model of the deployed verifier, which is the same missing object the whole FRI campaign is
    about. Saying so is the honest verdict; relabelling R11 would not be.
  * MODE 3 does not subsume modes 1 and 2, and they do not subsume it
    (`mode3_is_independent_of_the_first_two`). `CarrierBites` is the conjunction. -/

end R11

/-! ## §8 — THE UPDATED TABLE (only the rows this module touched).

| # | row | verdict BEFORE | verdict AFTER | evidence here |
|---|---|---|---|---|
| R3 | `AggAirSound.FriExtract` | UNKNOWN at deployment, bracketed at `verify := fun _ => true` | **INSTANTIATED IN-TREE at a REJECTING verifier; acceptance DISCRIMINATING; antecedent DISCRIMINATING; floor FIRES.** Deployed-configuration verdict UNCHANGED (UNKNOWN). | `realChildAcc_discriminating`, `columnsCVS_discriminating`, `aggFriExtract_settled_at_a_real_rejecting_verifier`, `realCarriers_are_neither_degenerate_bracket` |
| R4 | `GroundedApex.BindingExtract` | UNKNOWN; proved FREE on non-verifying aggregates | UNKNOWN at deployment, now **BRACKETED BOTH SIDES** — FREE where the binding proof fails, and outright FALSE at the EMPTY CHAIN wherever it verifies | `bindingExtract_at_the_empty_chain_empties_binding_acceptance`, `bindingExtract_at_the_empty_chain_is_false`, `bindingExtract_refutation_hypotheses_are_satisfiable`, `bindingExtract_bracketed` |
| R5 | the nine `*LeafFriFloor` | UNKNOWN; ONE member machine-checked, eight READ | UNKNOWN at deployment, **ALL NINE machine-checked** — shape identity by `Iff.rfl`, both brackets fired | the nine `*_is_the_shape`, `deadVerifier_empties_all_nine_leafFloors`, `all_nine_leafFloors_inhabited_nondegenerately` |
| R9 | `FriExtractNonCircular.TranscriptOfPolynomial` | UNKNOWN ("no deployed instantiation") | **INHABITABLE, non-degenerately** (antecedent satisfied), and **NOT FREE** (forces FRI acceptance). The `∀ w` form `friExtract_nonCircular` consumes is still OPEN and characterized. | `transcriptOfPolynomial_inhabited_nondegenerately`, `transcriptOfPolynomial_forces_fri_acceptance`, `friExtract_at_real_carriers_needs_the_forall_form` |
| R10 | `AccumulatorNonRevocationComplete.Accepts` / `NonMemberWitness` | UNKNOWN ("not examined") | **SETTLED POSITIVELY — INHABITED and DISCRIMINATING.** No abstract verifier is involved; this row was never an emptied-premise site. | `accumAcc_acceptsSome`, `accumAcc_rejects_zero_at_matching_leaf`, `accumAcc_discriminating` |
| R14 | `Circuit/AirSoundness.airChecks` | UNKNOWN, flagged | UNKNOWN at deployment, **BRACKETED with the falsifier written down**: a multi-row `openTr` makes `airChecks` reject everything and `CircuitSound` free for EVERY `applyEff`; a single-row opener gives a non-degenerate model with `FriProximity` holding | `airChecks_rejectsAll_of_multirow_opening`, `circuitSound_is_free_at_multirow_opening`, `airChecks_inhabited_nondegenerately`, `airChecks_bracketed` |
| R15 | `AssuranceCaseGrounded…bls_quorum` | UNKNOWN ("recorded as unexamined") | **SETTLED — the three-conjunct premise is JOINTLY INHABITED and acceptance is DISCRIMINATING**, at the reference 3-of-4 committee, with the conclusion firing | `blsQuorum_premise_inhabited`, `blsAcc_discriminating`, `blsQuorum_conclusion_fires` |
| R16 | `Spec/VatBoundary.PhiFunctorial.preserves_id` | UNKNOWN ("not examined") | **SETTLED BOTH WAYS — PROVED UNINHABITABLE at a verifier that accepts nothing, PROVED INHABITED at a discriminating one.** The module's prose claim is now a theorem. | `phiFunctorial_uninhabitable_at_a_dead_verifier`, `phiFunctorial_inhabited_at_a_discriminating_verifier`, `phiFunctorial_settled_both_ways` |

| R11 | the thirteen carrier-gated kernels | UNKNOWN at deployment; TWO vacuity modes proved, `CarrierLive` offered as the criterion | UNKNOWN at deployment (unchanged), but **`CarrierLive` IS PROVED INSUFFICIENT — a THIRD, conclusion-side vacuity mode**. FIRED at two members: `NonMembershipVerifierKernel`'s soundness conclusion is a TAUTOLOGY at EVERY instantiation (settled negatively, permanently); `MerkleVerifierKernel`'s is TOTAL at the reference node hash, inverting the polarity of the carrier axis. ABSENT at `TemporalVerifierKernel`, so the criterion discriminates. AND the row's own COUNT is corrected: `PrivateLeg.lean:275`'s `extractable := True` is a FALSE POSITIVE, retired by §9.5 — its proof type carries the witness, so the carrier is honestly contentless. The wound is live and BIT elsewhere: `Verify/StripeAttest.lean` was discharging `DecoVerifierKernel.extractable` with `trivial : True`. | §9 — `carrierLive_does_not_exclude_mode3`, `mode3_is_independent_of_the_first_two`, `nonMember_conclusion_is_total`, `nonmembership_verify_sound_is_free`, `nonmembership_carrierBites_is_unreachable`, `merkleMembers_total_at_additive_compress`, `merkle_conclusion_axis_inverts_against_the_carrier_axis`, `temporal_conclusion_bites`, `the_family_splits_on_the_conclusion_axis`; §9.5 — `sigma_proof_type_is_witnessBearing`, `extraction_is_discharged_at_a_witnessBearing_proof_type`, `witnessBearing_fails_when_the_conclusion_is_unsatisfiable`, `trueCarrier_splits_on_witness_bearing`, `the_refutation_test_cannot_see_witness_bearing` |

**Still UNKNOWN after this module.** R11's DEPLOYMENT verdict for all thirteen (§9.6 names the
instantiation that would settle it and why it is not engineering), and the conclusion-axis question
for ELEVEN of the thirteen — that part IS engineering, one exhibited counterexample or one totality
proof each, with the instrument (`ConclusionBites` / `CarrierBites`) now written down. The MODE-1
carrier repair remains a sibling lane's; §9 is orthogonal to it and neither supersedes the other.

**Not claimed.** No theorem here asserts anything about the DEPLOYED STARK/FRI verifier. R3's and
R9's instantiation is a 4-point BabyBear domain folding to 2 points; that is enough to settle
"is this an empty notion" and "is this satisfiable only at an accept-everything verifier", and it is
not enough to settle anything about `CircuitSoundness.verifyBatch`, whose `cfg*` arguments are
`opaque`. R5's, R4's and R14's brackets are over the classes' own abstract parameters and say
nothing about a deployed instantiation, because there is none to say anything about. -/

#assert_axioms realChildAcc_discriminating
#assert_axioms realCarriers_are_neither_degenerate_bracket
#assert_axioms columnsCVS_discriminating
#assert_axioms aggFriExtract_settled_at_a_real_rejecting_verifier
#assert_axioms transcriptOfPolynomial_inhabited_nondegenerately
#assert_axioms transcriptOfPolynomial_forces_fri_acceptance
#assert_axioms friExtract_at_real_carriers_needs_the_forall_form
#assert_axioms transcriptOfPolynomial_is_free_above_the_decoding_radius
#assert_axioms columnsCVS_is_empty_above_the_decoding_radius
#assert_axioms leafFloorShape_iff_extracts
#assert_axioms deadVerifier_empties_leafFloorShape
#assert_axioms leafFloorShape_inhabited_nondegenerately
#assert_axioms leafFloorShape_is_free_when_unsatisfiable
#assert_axioms customLeafFriFloor_is_the_shape
#assert_axioms factoryLeafFriFloor_is_the_shape
#assert_axioms contractLeafFriFloor_is_the_shape
#assert_axioms membershipLeafFriFloor_is_the_shape
#assert_axioms sovereignLeafFriFloor_is_the_shape
#assert_axioms dslLeafFriFloor_is_the_shape
#assert_axioms blindedLeafFriFloor_is_the_shape
#assert_axioms decoLeafFriFloor_is_the_shape
#assert_axioms noteSpendLeafFriFloor_is_the_shape
#assert_axioms deadVerifier_empties_all_nine_leafFloors
#assert_axioms all_nine_leafFloors_inhabited_nondegenerately
#assert_axioms accumAcc_acceptsSome
#assert_axioms accumAcc_rejects_zero_at_matching_leaf
#assert_axioms accumAcc_discriminating
#assert_axioms blsQuorum_premise_inhabited
#assert_axioms blsAcc_discriminating
#assert_axioms blsQuorum_conclusion_fires
#assert_axioms phiFunctorial_uninhabitable_at_a_dead_verifier
#assert_axioms phiFunctorial_false_at_deadVerifiable
#assert_axioms phiFunctorial_inhabited_at_a_discriminating_verifier
#assert_axioms phiFunctorial_settled_both_ways
#assert_axioms airChecks_rejectsAll_of_multirow_opening
#assert_axioms circuitSound_is_free_at_multirow_opening
#assert_axioms multirowOpener_exists
#assert_axioms circuitSound_free_for_contradictory_semantics
#assert_axioms airChecks_inhabited_nondegenerately
#assert_axioms airChecks_bracketed
#assert_axioms bindingExtract_at_the_empty_chain_empties_binding_acceptance
#assert_axioms bindingExtract_at_the_empty_chain_forces_rejection
#assert_axioms bindingExtract_at_the_empty_chain_is_false
#assert_axioms bindingExtract_refutation_hypotheses_are_satisfiable
#assert_axioms bindingExtract_bracketed
#assert_axioms totalConclusion_makes_the_gated_theorem_free
#assert_axioms not_conclusionTotal_of_conclusionBites
#assert_axioms carrierBites_excludes_falseCarrier
#assert_axioms carrierBites_excludes_rejectsAll
#assert_axioms carrierBites_excludes_totalConclusion
#assert_axioms carrierLive_does_not_exclude_mode3
#assert_axioms mode3_is_independent_of_the_first_two
#assert_axioms nonMember_conclusion_is_total
#assert_axioms nonmembership_conclusion_is_mode3
#assert_axioms nonmembership_verify_sound_is_free
#assert_axioms nonmembership_conclusion_holds_at_rejected_statements
#assert_axioms nonmembership_carrierBites_is_unreachable
#assert_axioms merkleMembers_total_at_additive_compress
#assert_axioms merkleMembers_is_mode3_at_additive_compress
#assert_axioms merkle_verify_sound_is_free_at_the_reference_kernel
#assert_axioms recompose_collapses
#assert_axioms merkle_conclusion_axis_inverts_against_the_carrier_axis
#assert_axioms temporal_conclusion_bites
#assert_axioms temporal_is_not_mode3
#assert_axioms the_family_splits_on_the_conclusion_axis
#assert_axioms sigma_proof_type_is_witnessBearing
#assert_axioms extraction_is_discharged_at_a_witnessBearing_proof_type
#assert_axioms witnessBearing_fails_when_the_conclusion_is_unsatisfiable
#assert_axioms trueCarrier_splits_on_witness_bearing
#assert_axioms the_refutation_test_cannot_see_witness_bearing

end Dregg2.Circuit.PremiseInhabitabilitySweepSettled
