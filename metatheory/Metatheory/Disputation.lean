/-
# Metatheory.Disputation — CONSTRUCTIVE ADJUDICATION (the witness-fiber reflector).

THE CORRECTED STRUCTURE. An earlier exploration posed the thesis *"distributed agreement and
dispute-adjudication are the two adjoints of ONE `Predicate ⊣ Witness` adjunction."* A four-lens
adversarial review (epistemic-logic / category-topos / distributed-systems / judgment-aggregation;
workflow run `wiv1o0kyj`) **refuted the headline 4/4** and is recorded in memory
(`project-adjunction-thesis-verdict`). We do NOT formalize that thesis; it is false. The verified
structure is a **Lawvere hyperdoctrine / realizability tripos**:

  * `Predicate ⊣ Witness` (`Dregg2.Laws`, `Metatheory.Categorical.Seam`) is the **BASE** — the
    realizability tripos — NOT the agreement/adjudication pairing (it is single-agent; `ι` does not
    occur in `Seam`).
  * Knowledge is a **GRADED** family of per-agent Lawvere adjunctions `∃_a ⊣ q_a* ⊣ ∀_a` along the
    indistinguishability quotient; `Kₐ = ∀_a`, whose de Morgan mate is **possibility `◇ₐ`, not
    adjudication**.
  * **Agreement is a LIMIT** — the meet `DistKnows = ⋂ ∼_a` (`EpistemicConsensus`); **binding common
    knowledge is a FIXPOINT** (still limit-side), and *that* is the FLP-shadowed object.
  * **Adjudication is a SEPARATELY-built graded REFLECTOR** `R_r : Profiles → Verdicts` indexed by the
    evidence regime `r`. It does NOT come for free from the meet; its good-behaviour existence is
    exactly what FAILS in the political (ballot) regime — that non-existence *is* Arrow / List–Pettit.

This module formalizes the **gem** the verdict isolated as the defensible novelty: the witness-regime
reflector **`R_witness`**. Its content — *the verdict is read off the discharging WITNESS, never a
vote, and is therefore Byzantine-majority-proof on the certifiable domain* — is the **constructive**
(vs political) endpoint, and it **escapes the judgment-aggregation impossibility by RESTRICTING THE
DOMAIN to certifiable claims** (a Universal-Domain violation: you only adjudicate what admits a
certificate). It rests entirely on the existing kernel-clean witness-fiber theorems
(`honest_dist_knowledge_iff_holds`, `no_dist_knowledge_of_unrealizable`), now read as an ADJUDICATION
law rather than a knowledge law. Faithful Props.
-/
import Metatheory.EpistemicConsensus

namespace Metatheory.Disputation

open Dregg2.Laws Metatheory Metatheory.EpistemicConsensus

universe u v
variable {Ω : Type u} {ι : Type v} (F : Frame Ω ι)
variable {P W : Type u} [Verifiable P W]

/-- A **dispute**: two parties press competing claims; the adjudicator must return a verdict. (The
binary shape is the smallest non-trivial profile; the reflector generalizes to a profile of claims.) -/
structure Dispute (P : Type u) where
  /-- the claim pressed by the proponent. -/
  pro : Claim P
  /-- the claim pressed by the opponent. -/
  con : Claim P

/-- **CONSTRUCTIVE ADJUDICATION — the witness-fiber reflector `R_witness`.** A claim is **upheld** iff
it constructively `Holds`: a discharging witness exists. The verdict is read off the **witness**, never
off a vote. `R_witness` is defined only where a certificate can exist (the *certifiable domain*) —
exactly how it sidesteps the aggregation impossibility. -/
def upheld (X : Claim P) : Prop := Holds (W := W) X

/-- **`upheld_iff_witness` — the verdict IS the witness.** Upholding a claim is exactly the
existence of a discharging witness; no assertion or majority can manufacture it. -/
theorem upheld_iff_witness (X : Claim P) :
    upheld (W := W) X ↔ ∃ w : W, Discharged (P := P) (W := W) X.stmt w :=
  holds_iff_discharged_witness X

/-- **`verdict_is_honest_distributed_knowledge` — witness-determined, not vote-determined.**
The verdict equals exactly what the honest group can DISTRIBUTEDLY KNOW: `upheld X` iff, for some
offered witness, the honest agents have distributed knowledge of its discharge. The adjudicated outcome
is the realizability fact (`R_witness`), not an aggregation of opinions. -/
theorem verdict_is_honest_distributed_knowledge (X : Claim P) :
    upheld (W := W) X ↔ ∃ w₀ : W, F.DistKnows F.Honest (Frame.verified (Ω := Ω) X w₀) F.actual := by
  constructor
  · rintro ⟨w₀, hd⟩
    exact ⟨w₀, F.honest_distributed_knows_discharged X w₀ hd⟩
  · rintro ⟨w₀, hk⟩
    exact F.honest_dist_knowledge_iff_holds X w₀ ⟨hk, fun i _ => F.indist_refl i F.actual⟩

/-- **`byzantine_majority_cannot_uphold` — the aggregation-impossibility ESCAPE.** If a claim
does NOT hold (no witness exists), then NO offered witness lets the honest group distributedly know it —
a Byzantine majority cannot vote it into the verdict. `R_witness` is dictatorship-proof on the
certifiable domain *precisely because it is not an aggregation*: it reads a certificate, it does not
count ballots. This is the constructive endpoint of the constructive-vs-political dial. -/
theorem byzantine_majority_cannot_uphold (X : Claim P) (hno : ¬ upheld (W := W) X) (w₀ : W) :
    ¬ F.DistKnows F.Honest (Frame.verified (Ω := Ω) X w₀) F.actual :=
  F.no_dist_knowledge_of_unrealizable X w₀ hno (fun i _ => F.indist_refl i F.actual)

end Metatheory.Disputation

#assert_axioms Metatheory.Disputation.verdict_is_honest_distributed_knowledge
#assert_axioms Metatheory.Disputation.byzantine_majority_cannot_uphold
