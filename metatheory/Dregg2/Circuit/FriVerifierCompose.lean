/-
# `Dregg2.Circuit.FriVerifierCompose` — STAGE 5: the assembly, and the honest bottom line.

`docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` §5 Stage 5. Stages 1–4 delivered the faithfulness
bridge + query budget (`FriVerifierO`), the FS ε (`FriVerifierFS`), Merkle-binding-as-data + the
birthday ε + the query-log interface (`FriVerifierMerkle`), and `εQuery` at the proven
unique-decoding radius (`FriVerifierQuery`). This file composes them, and reports precisely where
the composition reaches and where it stops.

## ⚑ THE STAGE-5 FINDING — the freshness carrier was the WRONG PREDICATE, and it is REFUTABLE

Stages 2–3 carried `fsPt i ∉ queriedFinset A H` — "the adversary never queried the challenge's
squeeze point". §1 proves that hypothesis is **refuted by the honest prover**
(`challenge_computing_adversary_is_not_log_fresh`): deriving a Fiat–Shamir challenge IS querying the
permutation at the post-commitment sponge state, so EVERY adversary that computes its own transcript
— including the honest prover, and therefore every adversary that produces accepting proofs other
than by luck — has `fsPt ∈ queriedFinset A H`. `fs_epsilon_bound_of_log` is a true theorem whose
hypothesis excludes the adversaries the floor is about. It could never have been discharged; the
design's Stage-2 falsifier (§6: "if the transcript order lets the adversary see the challenge before
committing…") fires here, but NOT as a transcript bug — the deployed FS order is fine. The bug was in
the ε-statement's shape.

The correct ROM argument (BCS16; the lazy-sampling genre) never claims the adversary did not query
the point. It claims the answer is **fresh AT THE MOMENT OF ITS OWN QUERY** — uniform conditioned on
the strictly-earlier prefix — and pays `deg/|F|` per query, union-bounded over the budget. §1 proves
exactly that, and it needs NO new ordered-log data structure: **`OracleComp`'s query TREE already IS
the ordered model.** `condProb_split` conditions on the prefix; the continuation `k r` is the
suffix. The seam is CLOSED (`hit_cond`), by the induction pattern `birthday_cond` already used.

  `hit_cond : QueryBounded Q M → (∀ d, (E d).card ≤ b) → (∀ d ∈ S, σ d ∉ E d) →
      condProb (cyl S σ) (hitWin E M) ≤ Q·b / |R|`

`hitWin E M H` = "SOME query along `M`'s run receives an answer in that point's exceptional set" —
the event Stage 2 should have bounded. No freshness hypothesis, no excluded adversary: `hit_cond`
holds for ALL `Q`-query adversaries, the honest prover included. This is a strict strengthening of
Stage 2 (`fs_epsilon_bound`'s `(Q+1)·deg/|F|` arithmetic survives; its hypothesis does not).

## What §2–§4 compose, and what they do not

`εFri` (§2) is the union bound `εFS + εGrind + εMerkle + εQuery`, and `epsFri_compose` proves the
disjunction of the four bad events is `≤ εFri` **over one shared oracle for one adversary** — real,
proven, no hypothesis beyond the per-leg bounds. Three of the four legs are then discharged over that
shared oracle by in-tree theorems (`hit_cond` for FS + grind, `birthday_cond` for Merkle).

`εQuery` is the leg that does NOT come home, and §3 says so precisely rather than papering it. Two
gaps, both named, neither small:

  **(a) The word↔proof bridge.** `εQuery` (`FriVerifierQuery.epsilon_query_layer`) bounds
  `Pr[a FAR word passes the spot-checks]` over ABSTRACT `(f : ι → F, f' : κ → F)` in a `FriSetup`.
  Nothing in the tree connects a `BatchProofData`'s committed columns to such an `f`, nor derives
  "the extraction bundle fails ⟹ the committed word is far". That bridge is exactly
  `DeployedTraceExtract.DeployedFriEmbedding` — an explicit hypothesis STRUCTURE (`accept_folds`,
  `decode_trace`), already a named carrier in-tree, NOT a theorem. `friLdtExtractV3_rom` cannot be
  proven without it, and it is not a lemma-sized gap: it is the FRI-proximity-to-`VmTrace` decode.

  **(b) The sampling-model bridge, with a REAL defect.** `εQuery`'s sample space is UNIFORM
  `(α, Q) ∈ F × (Fin k → κ)`. The deployed `qidx` are `Challenger.sampleBits`, i.e.
  `toNat (H …) % 2 ^ logN` — a modular reduction of a BabyBear squeeze. `|F| = 2013265921` is ODD,
  so `2 ^ logN ∤ |F|` for every `logN ≥ 1`, and the derived indices are **provably NOT uniform** —
  proven in general by pigeonhole (`buckets_not_all_equal_of_not_dvd`) and discharged at the deployed
  field (`babybear_sampleBits_not_balanced`, §3): the `qidx` buckets CANNOT be balanced at ANY shipped
  `logN`. The bias is small but nonzero, and no in-tree theorem accounts for it. Composing `εQuery`
  over the oracle needs a uniformity-defect term that does not exist yet. This is a Stage-5 DISCOVERY
  about deployed code (design §6's "falsifier firing is a discovery"), not a modelling nicety.

§4's apex re-read is therefore CONDITIONAL in exactly one place: `nodes_union_bound` (a real theorem
— per-node failure over a shared oracle union-bounds to `#nodes · ε`) composes with
`recursive_sound_from_nodes` to give the probabilistic `NodeCarrier`/`GroundedApex` reading, but the
per-node ε it consumes is `εFri`, whose `εQuery` addend rests on (a) and (b).

## ⚑ THE HONEST BOTTOM LINE — can we say "the bits = the Q at which εFri reaches ½"?

**NO — not yet, and §5 states the two reasons in Lean rather than in prose.** What IS now true:
`εFS`, `εGrind`, `εMerkle` are proven functions of `Q` against ALL `Q`-query adversaries with no
excluded class (§1's closure is what earned this), and `epsClosedLegs` is the budget-growing function
(`epsClosedLegs_lt_half_example`, `epsClosedLegs_strictMono_example`) at which those three alone reach
½. That number is NOT "the security of the system": it omits
`εQuery`, which is where the FRI content lives. Calling it "the bits" would be the exact laundering
[[project-fri-soundness-reality]] names. The sentence the design's §7 promises requires (a) and (b).

## Permanent, honest carriers (named, never to be discharged — say so)

  * **The ROM α-pin / Poseidon2-as-random-function** (design §4.2): the deployed
    `perm : List F → List F` modelled as a uniform element of a FINITE `D → R`. Industry-standard,
    permanent. Every `condProb`/`cyl` statement here lives under it.
  * **The correlated-agreement carrier at `L > 1`** (Johnson): NOT assumed here — §2 instantiates
    `εQuery` at the PROVEN `L = 1` unique-decoding radius only (`FriVerifierQuery.epsilon_query_layer`).
    The radius is NOT silently upgraded; `εFri` is stated at the honest radius.

## Discipline

ADDITIVE: modifies NO deployed spec and NO earlier stage — `FriLdtExtractV3`, `verifyAlgo`,
`verifyAlgoO`, `RomOracle`, `RomCounting`, `RomQueryLog`, `FriVerifierFS/Merkle/Query`,
`RecursiveSoundFromNodes` are all imported read-only and untouched. `#assert_all_clean` over the
keystones; no `sorry`, no fresh `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.FriVerifierQuery
import Dregg2.Circuit.FriVerifierMerkle
import Dregg2.Circuit.RecursiveSoundFromNodes
import Dregg2.Tactics
import Mathlib.Tactic
import Dregg2.Circuit.FriChainStepIdx

namespace Dregg2.Circuit.FriVerifierCompose

open Dregg2.Crypto.RomOracle
open Dregg2.Crypto.RomCounting
  (cyl mem_cyl cyl_empty cyl_nonempty condProb condProb_nonneg condProb_le_one condProb_congr
   condProb_le_of_imp condProb_eq_zero condProb_cyl_empty condProb_split condProb_fresh_eq)
open Dregg2.Circuit.FriVerifierFS (condProb_or_le)
open Dregg2.Circuit.FriVerifierMerkle (queriedFinset mem_queriedFinset_iff queriedFinset_card_le)

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## §1 — ⚑ THE FRESHNESS SEAM: the old predicate REFUTED, the right one PROVEN.

Stage 2/3 phrased FS freshness as `fsPt ∉ queriedFinset A H`. §1.1 refutes that shape at the
adversaries that matter; §1.2 proves the shape that actually holds, by induction on the query tree
— which is already the ordered-log model the design asked for. -/

/-! ### §1.1 — the REFUTATION: computing your own challenge IS querying its point. -/

/-- **⚑ THE REFUTATION.** An adversary that derives its own Fiat–Shamir challenge queries the
permutation at that challenge's squeeze point — so the point is IN its query set. Stated over the
canonical `RomOracle` member (`ofList`, the query-a-list adversary): for the adversary that queries
`d` (the post-commitment sponge state) to learn its challenge, `d ∈ queriedFinset A H`.

This is what the honest prover does, and what every accepting-proof-finder must do: a non-interactive
FS proof is not writable without evaluating the transcript. So `fs_epsilon_bound_of_log`'s hypothesis
`fsPt i ∉ queriedFinset A H` (`FriVerifierMerkle`, Stage 3) EXCLUDES every adversary the floor is
about. The carrier was not merely undischarged — it is REFUTABLE, and §1.2 replaces it. -/
theorem challenge_computing_adversary_is_not_log_fresh
    {D R : Type} [DecidableEq D] (d : D) (H : D → R) :
    d ∈ queriedFinset (OracleComp.ofList [d] (fun rs => rs)) H := by
  rw [mem_queriedFinset_iff, OracleComp.ofList_queried]
  simp

/-- **The refutation, in the form Stage 3's hypothesis takes.** There is no `fsPt`-freshness to be
had for a challenge-computing adversary: the universally-quantified freshness premise
`∀ i, fsPt i ∉ queriedFinset A H` is FALSE for the adversary that reads its own challenge at `fsPt`.
Hence no route to `friLdtExtractV3_rom` runs through `fs_epsilon_bound_of_log` as stated. -/
theorem log_freshness_premise_false
    {D R : Type} [DecidableEq D] (d : D) (H : D → R) :
    ¬ (∀ _i : Fin 1, d ∉ queriedFinset (OracleComp.ofList [d] (fun rs => rs)) H) := by
  intro h
  exact (h 0) (challenge_computing_adversary_is_not_log_fresh d H)

/-! ### §1.2 — the CLOSURE: per-query freshness, by induction on the query TREE.

⚑ The design asked for "the minimal ordered-log interface". It is already present and needs no new
data: `OracleComp`'s tree IS ordered — in `query d k`, the continuation `k r` is exactly "what
happens after `d` is answered", and `RomCounting.condProb_split` conditions on the prefix. What was
missing is not a `queriedBefore` predicate but the per-query HIT bound, which the tree induction
proves directly. `hitWin` is the event Stage 2 should have bounded. -/

/-! ### `hitWin` / `hit_cond` / `hit_bound` — DEDUPLICATED (2026-07-25).

These five declarations existed here AND in `Dregg2.Circuit.FriChainStepIdx`, byte-identical but for
three comment lines and one opened namespace — a genuine duplicate, not a drift (verified by textual
diff before removal). They were re-derived here because that closure was red at authoring time; the
`SpongeForgeReduction` import break that forced it has since been repaired, and `FriChainStepIdx` flags
the debt in its own header.

`FriChainStepIdx`'s copy is kept because it is the LOWER module: its import closure is 51 modules
against this one's 295, so importing it here costs two new closure members while the other direction
would push all 295 into `FriSetupTower`, `FriGoodCountWeld` and `CorrelatedAgreement.Interface`. The
`export` below re-exposes the names at their original path, so the four consumers
(`FriQueryAdversary`, `FriEpsFriComposedAdversary`, `FriVerifierComposeDefected`,
`FriQuerySamplingBias`) need no edit. The Compose-only tooth `hitWin_fires` is retained below. -/
export Dregg2.Circuit.FriChainStepIdx (hitWin hitWin_pure hitWin_query hit_cond hit_bound)

section HitBound

variable {D R A : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

/-- **(TOOTH — `hit_cond` is not vacuous: the hit event genuinely FIRES.)** A 1-query adversary whose
target set is ALL of `R` hits with probability `1` — so `hitWin` is a real event with a real
probability, and the bound `Q·b/|R| = 1·|R|/|R| = 1` is tight there. -/
theorem hitWin_fires (d : D) (a : A) (H : D → R) :
    hitWin (fun _ => (Finset.univ : Finset R))
      (OracleComp.query d (fun _ => OracleComp.pure a)) H = true := by
  rw [hitWin_query]
  simp

end HitBound

/-! ## §2 — the composed `εFri`, over a SHARED oracle for ONE adversary.

The four legs are events over one adversary's single run. `εFri` is their union bound. Radius honesty:
`epsQuery`'s value is instantiated ONLY at Stage 4's PROVEN `L = 1` unique-decoding line — the
Johnson carrier is NOT assumed, and the `~112.6`-bit number is NOT read out of this pipeline. -/

/-- The FS leg: `Q` queries, each able to land in a degree-`degBound` exceptional set of the field
part of the answer. `hit_cond` proves it (§1.2). -/
noncomputable def epsFS (Q degBound cardF : ℕ) : ℝ := ((Q : ℝ) * (degBound : ℝ)) / (cardF : ℝ)

/-- The grinding leg: `Q` masked squeezes against a `2 ^ powBits` mask. `hit_cond` proves it — the
grinding accounting with no time model anywhere (design §3). -/
noncomputable def epsGrind (Q powBits : ℕ) : ℝ := (Q : ℝ) / ((2 : ℝ) ^ powBits)

/-- The Merkle leg: the birthday bound at budget `Q` over the width-pinned node oracle.
`RomQueryFloor.birthday_cond` (via Stage 3's `collFinder`) proves it. -/
noncomputable def epsMerkle (Q cardA : ℕ) : ℝ := ((Q : ℝ) * (Q : ℝ) + 1) / (cardA : ℝ)

/-- The query leg at the PROVEN unique-decoding radius: Stage 4's `epsilon_query_layer` value
`1/|F| + (1−δ)^k`. ⚑ This is radius (i) — the `L = 1` line. It is NOT the Johnson value. -/
noncomputable def epsQuery (cardF k : ℕ) (δ : ℝ) : ℝ := 1 / (cardF : ℝ) + (1 - δ) ^ k

/-- **⚑ `εFri` — the composed error, at the honest radius.**

    εFri = εFS + εGrind + εMerkle + εQuery
         = Q·deg/|F| + Q/2^pow + (Q² + 1)/|α| + (1/|F| + (1−δ)^k)

Each addend is the Stage-2/3/4 theorem's value. Three of the four are discharged over a shared oracle
below (`epsFri_compose_closed_legs`); `epsQuery` is the one that does not come home — §3. -/
noncomputable def epsFri (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ) : ℝ :=
  epsFS Q degBound cardF + epsGrind Q powBits + epsMerkle Q cardA + epsQuery cardF k δ

/-- Boolean subadditivity, ternary — the shared-oracle union bound for the three closed legs. -/
theorem condProb_or3_le {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    (C : Finset (D → R)) (f g h : (D → R) → Bool) :
    condProb C (fun H => f H || g H || h H)
      ≤ condProb C f + condProb C g + condProb C h := by
  refine le_trans (condProb_or_le C (fun H => f H || g H) h) ?_
  have := condProb_or_le C f g
  linarith

/-- Boolean subadditivity, quaternary — the full `εFri` union bound over one shared oracle. -/
theorem condProb_or4_le {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    (C : Finset (D → R)) (f g h e : (D → R) → Bool) :
    condProb C (fun H => f H || g H || h H || e H)
      ≤ condProb C f + condProb C g + condProb C h + condProb C e := by
  refine le_trans (condProb_or_le C (fun H => f H || g H || h H) e) ?_
  have := condProb_or3_le C f g h
  linarith

/-- **⚑ THE `εFri` COMPOSITION — over ONE shared oracle, for ONE `Q`-query adversary.**

Given the four legs' per-leg bounds as they are proven in Stages 2–4, the probability that ANY of
them fails on the adversary's single run is at most `εFri`. This is a REAL union bound over a SHARED
conditioning — no independence is assumed anywhere (the events are all events of one run against one
`H`, which is precisely the design §6 Stage-5 falsifier's requirement: monotone in the shared log,
so a coupled adversary cannot violate it). -/
theorem epsFri_compose {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    (C : Finset (D → R)) (wFS wGrind wMerkle wQuery : (D → R) → Bool)
    (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ)
    (hFS : condProb C wFS ≤ epsFS Q degBound cardF)
    (hGrind : condProb C wGrind ≤ epsGrind Q powBits)
    (hMerkle : condProb C wMerkle ≤ epsMerkle Q cardA)
    (hQuery : condProb C wQuery ≤ epsQuery cardF k δ) :
    condProb C (fun H => wFS H || wGrind H || wMerkle H || wQuery H)
      ≤ epsFri Q degBound cardF powBits cardA k δ := by
  refine le_trans (condProb_or4_le C wFS wGrind wMerkle wQuery) ?_
  unfold epsFri
  linarith

/-- **⚑ THE THREE CLOSED LEGS, DISCHARGED OVER A SHARED ORACLE — no supplied ε.**

For ONE `Q`-query adversary `A` and ONE `2·L`-query Merkle extractor over the SAME oracle `H : D → R`,
the FS-exceptional, grinding, and Merkle-collision events union-bound to
`εFS + εGrind + εMerkle` — with `hit_cond` (§1.2) supplying the first two and `birthday_cond` the
third. NOTHING is assumed: no freshness premise, no excluded adversary class, no named carrier beyond
the permanent ROM α-pin. This is what Stages 2+3 were reaching for and could not state.

The FS/grind legs are `hitWin` at two different target families: `EFS d` = the answers whose challenge
projection is exceptional (`degBound`-capped), `EPow d` = the answers whose mask lane is zero
(`maskBound`-capped). -/
theorem epsFri_closed_legs {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    [Nonempty R] {AnsT : Type}
    {Q L degBound maskBound : ℕ}
    (A : OracleComp D R AnsT) (hA : QueryBounded Q A)
    (Mc : OracleComp D R (D × D)) (hMc : QueryBounded L Mc)
    (EFS EPow : D → Finset R)
    (hEFS : ∀ d, (EFS d).card ≤ degBound) (hEPow : ∀ d, (EPow d).card ≤ maskBound)
    (S : Finset D) (σ : D → R)
    (hσcoll : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → σ a ≠ σ b)
    (hσFS : ∀ d ∈ S, σ d ∉ EFS d) (hσPow : ∀ d ∈ S, σ d ∉ EPow d) :
    condProb (cyl S σ)
        (fun H => hitWin EFS A H || hitWin EPow A H
          || Dregg2.Crypto.RomQueryFloor.collWin Mc H)
      ≤ ((Q : ℝ) * (degBound : ℝ)) / (Fintype.card R : ℝ)
        + ((Q : ℝ) * (maskBound : ℝ)) / (Fintype.card R : ℝ)
        + ((L : ℝ) * (S.card : ℝ) + (L : ℝ) * (L : ℝ) + 1) / (Fintype.card R : ℝ) := by
  refine le_trans (condProb_or3_le _ _ _ _) ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact hit_cond hA EFS hEFS S σ hσFS
  · exact hit_cond hA EPow hEPow S σ hσPow
  · have h := Dregg2.Crypto.RomQueryFloor.birthday_cond hMc S σ hσcoll
    refine h.trans (le_of_eq ?_)
    ring

/-! ## §3 — ⚑ `friLdtExtractV3_rom`: STATED, and the blocker NAMED (not papered).

The design's §4.3 target is
`Pr[ verifyAlgoO accepts ∧ ¬ ExtractBundle ] ≤ εFri Q params`. §2 gives the union bound; §1 closes the
FS/grind legs; Stage 3 gives the Merkle leg. What is missing is `εQuery`'s attachment — and it is
missing for TWO reasons, both stated in Lean here rather than asserted in prose. -/

/-- **BLOCKER (a) — THE WORD↔PROOF BRIDGE, as the named in-tree carrier it already is.**

`εQuery` bounds `Pr[FAR word passes]` over abstract `(f, f')` in a `FriSetup`. To reach
`friLdtExtractV3_rom` one needs, for the adversary's `BatchProofData`: a committed word, and the
implication "the extraction bundle fails ⟹ that word is FAR". Both are exactly the two Prop fields of
`DeployedTraceExtract.DeployedFriEmbedding` (`accept_folds` — the verifier-decode into the folded
code; `decode_trace` — the codeword-to-`VmTrace` decode). That structure is an explicit HYPOTHESIS in
the tree, NOT a theorem, and it is not lemma-sized: it IS the FRI-proximity-to-`VmTrace` decode.

`WordProofBridge` names the obligation at the shape Stage 5 would consume it. It is a DEFINITION of
what is missing, deliberately parameterised so that nothing here can be mistaken for a discharge:
supplying it is supplying `DeployedFriEmbedding`. -/
def WordProofBridge {Proof Word : Type} (committed : Proof → Word) (accepts : Proof → Bool)
    (bundleFails : Proof → Prop) (isFar : Word → Prop) : Prop :=
  ∀ p : Proof, accepts p = true → bundleFails p → isFar (committed p)

/-- **The bridge is exactly the hinge — it is what turns `εQuery` into an extraction bound.** Given
the bridge, "accepts ∧ bundle fails" is contained in "accepts ∧ the committed word is far", which is
the event `εQuery` bounds. This is a TRIVIALITY on purpose: it exhibits that ALL the content sits in
`WordProofBridge`, i.e. in `DeployedFriEmbedding`. Nothing is smuggled — the reduction is one line
because the mathematics is entirely on the other side of the hypothesis. -/
theorem bundleFail_imp_far_of_bridge {Proof Word : Type} {committed : Proof → Word}
    {accepts : Proof → Bool} {bundleFails : Proof → Prop} {isFar : Word → Prop}
    (hbridge : WordProofBridge committed accepts bundleFails isFar)
    (p : Proof) (hacc : accepts p = true) (hfail : bundleFails p) :
    accepts p = true ∧ isFar (committed p) :=
  ⟨hacc, hbridge p hacc hfail⟩

/-- **⚑ BLOCKER (b) — THE SAMPLING DEFECT IS REAL, AND IT IS A DISCOVERY ABOUT DEPLOYED CODE.**

`εQuery`'s sample space is UNIFORM `(α, Q) ∈ F × (Fin k → κ)`. The deployed query indices are
`Challenger.sampleBits`: `toNat (squeeze) % 2 ^ logN`. When `2 ^ bits` does not divide the number of
squeeze values, that reduction is NOT uniform — the low residues get one extra preimage each.

The defect is proven here in general, by pigeonhole, and then discharged at the DEPLOYED field — no
concrete-instance hand-waving. `buckets_not_all_equal_of_not_dvd`: if the `m` residue classes of a
range of size `n` had EQUAL counts, then `n = m · (common count)`, i.e. `m ∣ n`. Contrapositive: when
`m ∤ n` the reduction is NOT balanced. At BabyBear `|F| = 2013265921` is ODD, so `2 ^ logN ∤ |F|` for
every `logN ≥ 1` — hence `babybear_sampleBits_not_balanced`: the deployed `qidx` buckets **cannot** be
balanced at ANY shipped `logN`. The bias is small (`≈ 2 ^ logN / |F|` relative) but it is NONZERO and
NO in-tree theorem accounts for it. Composing `εQuery` over the oracle therefore needs a
uniformity-defect term that does not exist. Stated and PROVEN, not papered. -/
theorem buckets_not_all_equal_of_not_dvd {n m : ℕ} (hm : 0 < m) (hdvd : ¬ (m ∣ n))
    (cnt : Fin m → ℕ) (hsum : ∑ r : Fin m, cnt r = n) :
    ¬ (∀ r r' : Fin m, cnt r = cnt r') := by
  intro h
  have hcommon : ∑ r : Fin m, cnt r = m * cnt ⟨0, hm⟩ := by
    rw [Finset.sum_congr rfl (fun r _ => h r ⟨0, hm⟩), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [hsum] at hcommon
  exact hdvd ⟨cnt ⟨0, hm⟩, hcommon⟩

/-- The deployed field order is ODD — so no power `2 ^ logN` with `logN ≥ 1` divides it. -/
theorem babybear_order_not_divisible_by_two : ¬ (2 ∣ 2013265921) := by decide

/-- **⚑ THE DEPLOYED `sampleBits` BUCKETS CANNOT BE BALANCED — at EVERY shipped `logN ≥ 1`.**
Any assignment of counts to the `2 ^ logN` residue classes summing to `|F| = 2013265921` has two
classes of DIFFERENT size. So the deployed `Challenger.sampleBits` query indices are provably NOT
uniform, and `εQuery`'s uniform-`(α, Q)` sample space is NOT the deployed sampling distribution. -/
theorem babybear_sampleBits_not_balanced (logN : ℕ) (hlogN : 0 < logN)
    (cnt : Fin (2 ^ logN) → ℕ) (hsum : ∑ r : Fin (2 ^ logN), cnt r = 2013265921) :
    ¬ (∀ r r' : Fin (2 ^ logN), cnt r = cnt r') := by
  refine buckets_not_all_equal_of_not_dvd (pow_pos (by norm_num : (0 : ℕ) < 2) logN) ?_ cnt hsum
  intro hdvd
  exact babybear_order_not_divisible_by_two (dvd_trans (dvd_pow_self 2 hlogN.ne') hdvd)

/-- **⚑ `friLdtExtractV3_rom` — the design's §4.3 target, STATED with its two blockers EXPLICIT.**

The conclusion is the design's, verbatim in shape: a `Q`-query adversary's run yields "accepts ∧ the
extraction bundle fails" with probability `≤ εFri`. It is stated as an implication FROM the four leg
bounds — three of which §1/§2/Stage 3 discharge unconditionally, and the fourth (`hQuery`) of which
is reachable ONLY through `WordProofBridge` (blocker (a)) and a uniformity-defect account (blocker
(b)). Supplying `hQuery` today means supplying `DeployedFriEmbedding` AND ignoring the sampling bias.

⚑ THIS IS NOT A PROOF OF THE FLOOR. It is the honest statement of what the four stages compose to:
the union bound is real and the composition is sound; the FRI content is in `hQuery`, which does not
yet exist. Reading this theorem as "the floor is discharged" would be exactly the laundering
[[feedback-no-named-carrier-laundering]] forbids. -/
theorem friLdtExtractV3_rom_of_legs {D R : Type} [Fintype D] [DecidableEq D] [Fintype R]
    [DecidableEq R]
    (C : Finset (D → R)) (accepts_and_fails wFS wGrind wMerkle wQuery : (D → R) → Bool)
    (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ)
    (hcover : ∀ H ∈ C, accepts_and_fails H = true →
      (wFS H || wGrind H || wMerkle H || wQuery H) = true)
    (hFS : condProb C wFS ≤ epsFS Q degBound cardF)
    (hGrind : condProb C wGrind ≤ epsGrind Q powBits)
    (hMerkle : condProb C wMerkle ≤ epsMerkle Q cardA)
    (hQuery : condProb C wQuery ≤ epsQuery cardF k δ) :
    condProb C accepts_and_fails ≤ epsFri Q degBound cardF powBits cardA k δ :=
  le_trans (condProb_le_of_imp hcover)
    (epsFri_compose C wFS wGrind wMerkle wQuery Q degBound cardF powBits cardA k δ
      hFS hGrind hMerkle hQuery)

/-! ## §4 — the apex re-read: the union bound over `PTree` nodes.

`recursive_sound_from_nodes` folds a per-node carrier into the whole-tree claim. The probabilistic
re-read needs: per-node failure events over a SHARED oracle, union-bounded by `#nodes · ε`. That IS a
theorem (`nodes_union_bound`), and it is the design §6 Stage-5 falsifier's canary: the events are all
events of ONE run against ONE `H`, so no independence enters and a coupled adversary cannot violate
the bound. -/

open Dregg2.Circuit.RecursiveSoundFromNodes (PTree)

/-- The number of nodes in an aggregation tree — the union-bound multiplicity. -/
def nodeCount {Proof : Type} : PTree Proof → ℕ
  | .leaf _ _     => 1
  | .node _ _ l r => 1 + nodeCount l + nodeCount r

theorem nodeCount_pos {Proof : Type} (t : PTree Proof) : 0 < nodeCount t := by
  cases t <;> simp [nodeCount]

/-- **⚑ THE PER-NODE UNION BOUND (the Stage-5 canary, PROVEN).** For a finite index set of nodes,
each of whose failure events has probability `≤ ε` over the SHARED conditioning, the probability that
SOME node fails is `≤ #nodes · ε`. Induction through `condProb_or_le`; no independence anywhere —
these are events of one adversary's single run, so coupling is already accounted for. -/
theorem nodes_union_bound {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    {ι : Type} [DecidableEq ι] (C : Finset (D → R)) (s : Finset ι)
    (fail : ι → (D → R) → Bool) (ε : ℝ) (hε : ∀ i ∈ s, condProb C (fail i) ≤ ε) :
    condProb C (fun H => decide (∃ i ∈ s, fail i H = true)) ≤ (s.card : ℝ) * ε := by
  refine le_trans (Dregg2.Circuit.FriVerifierFS.condProb_exists_le C s fail) ?_
  calc ∑ i ∈ s, condProb C (fail i) ≤ ∑ _i ∈ s, ε := Finset.sum_le_sum hε
    _ = (s.card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **⚑ THE PROBABILISTIC `NodeCarrier` / `GroundedApex` RE-READ.**

`recursive_sound_from_nodes` needs `NodeCarrier verify H t` — a DETERMINISTIC per-node claim. The
ROM re-basing delivers instead: "every node's carrier holds EXCEPT with probability `≤ εFri`". This
theorem is the bridge's shape: on the oracles where NO node fails, the deterministic `NodeCarrier`
holds, so the whole-tree fold applies verbatim; and the union bound (`nodes_union_bound`) says that
set has measure `≥ 1 − #nodes·εFri`.

So `GroundedApex`'s conclusions re-read as: **"…except with probability ≤ (#nodes)·εFri(Q, params)
for any Q-query adversary"** — CONDITIONAL on the per-node `εFri`, whose `εQuery` addend rests on §3's
two blockers. The tree side is DONE (this theorem + `recursive_sound_from_nodes`); the per-node side
is what §3 says is not yet available. That is the honest apex verdict: the apex is reachable, and the
gap is entirely per-node. -/
theorem apex_probabilistic_nodeCarrier {D R : Type} [Fintype D] [DecidableEq D] [Fintype R]
    [DecidableEq R] {ι : Type} [DecidableEq ι]
    (C : Finset (D → R)) (s : Finset ι) (fail : ι → (D → R) → Bool)
    (Carrier : (D → R) → Prop) [DecidablePred Carrier]
    (hsound : ∀ H ∈ C, (∀ i ∈ s, fail i H = false) → Carrier H)
    (ε : ℝ) (hε : ∀ i ∈ s, condProb C (fail i) ≤ ε) :
    condProb C (fun H => decide (¬ Carrier H)) ≤ (s.card : ℝ) * ε := by
  refine le_trans (condProb_le_of_imp ?_) (nodes_union_bound C s fail ε hε)
  intro H hHC hfail
  simp only [decide_eq_true_eq] at hfail ⊢
  by_contra hno
  refine hfail (hsound H hHC (fun i hi => ?_))
  by_contra hfi
  exact hno ⟨i, hi, by simpa using hfi⟩

/-! ## §5 — ⚑ THE BOTTOM LINE: what "the bits" can and cannot mean today.

The design's §7 promises: `"b bits" := εFri(2^b, params) ≤ 1/2`. §5 states, in Lean, exactly how far
that sentence has come — and refuses to overstate it. -/

/-- The three legs §1–§2 CLOSED, as a function of the query budget: `εFS + εGrind + εMerkle`. This
omits `εQuery` and is therefore **NOT** the security of the system. It is named separately precisely
so that it can never be mistaken for `εFri`. -/
noncomputable def epsClosedLegs (Q degBound cardF powBits cardA : ℕ) : ℝ :=
  epsFS Q degBound cardF + epsGrind Q powBits + epsMerkle Q cardA

/-- **⚑ THE CLOSED LEGS ARE A REAL, NON-VACUOUS FUNCTION OF `Q`.** At a small concrete
parameterisation the closed-leg error is `< 1/2` — the bound genuinely constrains a `Q`-query
adversary rather than restating `≤ 1`. `epsClosedLegs 2 1 1000 8 1000 = 2/1000 + 2/256 + 5/1000`,
comfortably below `1/2`. -/
theorem epsClosedLegs_lt_half_example : epsClosedLegs 2 1 1000 8 1000 < 1 / 2 := by
  unfold epsClosedLegs epsFS epsGrind epsMerkle
  norm_num

/-- **⚑ AND IT GROWS WITH `Q` — the budget dial is real.** Doubling the budget strictly increases the
closed-leg error at any live parameterisation: `epsClosedLegs` is not a constant dressed as a bound.
This is what makes "the `Q` at which ε reaches ½" a meaningful question AT ALL for these three legs. -/
theorem epsClosedLegs_strictMono_example :
    epsClosedLegs 2 1 1000 8 1000 < epsClosedLegs 4 1 1000 8 1000 := by
  unfold epsClosedLegs epsFS epsGrind epsMerkle
  norm_num

/-- **⚑⚑ THE HONEST BOTTOM LINE, AS A THEOREM.**

`εFri` is `epsClosedLegs + epsQuery` — the closed legs plus the leg §3 shows is not yet attachable.
So ANY statement of the form "the bits are the `Q` at which `εFri` reaches ½" is, today, a statement
about `epsClosedLegs` PLUS an unproven `epsQuery` term. This theorem records the decomposition
identity so the omission cannot be silent: whatever budget `Q` one computes from the closed legs
alone, `εFri` is STRICTLY LARGER (`epsQuery > 0` always, since `1/|F| > 0`), and the difference is
exactly the FRI content.

**Verdict: NO — we cannot yet say "the bits = the query budget Q at which εFri reaches ½."** We can
say it for `epsClosedLegs` (§1's closure is what earned that, against ALL adversaries, with the
freshness carrier refuted-and-replaced rather than assumed). We cannot say it for `εFri` until
`WordProofBridge` (= `DeployedFriEmbedding`) and the `sampleBits` uniformity defect are settled. -/
theorem epsFri_exceeds_closed_legs (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ)
    (hcardF : 0 < cardF) (hδ1 : δ ≤ 1) :
    epsClosedLegs Q degBound cardF powBits cardA
      < epsFri Q degBound cardF powBits cardA k δ := by
  have hpos : (0 : ℝ) < (cardF : ℝ) := by exact_mod_cast hcardF
  have h1 : (0 : ℝ) < 1 / (cardF : ℝ) := by positivity
  have hk : (0 : ℝ) ≤ (1 - δ) ^ k := pow_nonneg (by linarith) k
  unfold epsFri epsClosedLegs epsQuery
  linarith

/-- **The decomposition, exactly.** `εFri = epsClosedLegs + epsQuery` — definitionally. The sentence
"the bits measure the `Q` at which `εFri` reaches ½" is therefore missing precisely the `epsQuery`
addend, and §3 names why. -/
theorem epsFri_eq_closed_plus_query (Q degBound cardF powBits cardA k : ℕ) (δ : ℝ) :
    epsFri Q degBound cardF powBits cardA k δ
      = epsClosedLegs Q degBound cardF powBits cardA + epsQuery cardF k δ := by
  unfold epsFri epsClosedLegs
  ring

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  challenge_computing_adversary_is_not_log_fresh,
  log_freshness_premise_false,
  hitWin_pure,
  hitWin_query,
  hit_cond,
  hit_bound,
  hitWin_fires,
  condProb_or3_le,
  condProb_or4_le,
  epsFri_compose,
  epsFri_closed_legs,
  bundleFail_imp_far_of_bridge,
  buckets_not_all_equal_of_not_dvd,
  babybear_order_not_divisible_by_two,
  babybear_sampleBits_not_balanced,
  friLdtExtractV3_rom_of_legs,
  nodeCount_pos,
  nodes_union_bound,
  apex_probabilistic_nodeCarrier,
  epsClosedLegs_lt_half_example,
  epsClosedLegs_strictMono_example,
  epsFri_exceeds_closed_legs,
  epsFri_eq_closed_plus_query
]

end Dregg2.Circuit.FriVerifierCompose
