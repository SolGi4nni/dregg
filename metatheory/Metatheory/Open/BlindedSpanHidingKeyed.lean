/-
# `Metatheory.Open.BlindedSpanHidingKeyed` — Lane B's span-recovery reduction REWIRED onto the
PROVED keyed query-counted floor; the refuted `IsPolyTime` preimage floor RETIRED.

## The situation this file closes

Lane B (`Metatheory.Open.BlindedSpanHiding`) reduced a span-recovery hiding break of the deployed
wide blinded commitment to `WidePreimageFloor`, and instantiated the floor at
`CostAdversary.IsPolyTime` (`span_recovery_hard_from_polyTime`) — then PROVED, in the same file,
that this floor is FALSE at deployed parameters (`widePreimageFloor_polyTime_false`): the
commitment is FIXED, so the constant finder that hardcodes the honest opening is `IsPolyTime` and
wins with probability `1`. Every hiding statement conditioned on that floor is VACUOUS.

The PROVED successor floor now exists: `Dregg2.Crypto.KeyedRomHidingFloor.keyedRomHiding_hard` —
the two-world hiding advantage of the blinded commitment is `≤ (2Q+1)/2^λ` against every
`Q`-query KEYED adversary (oracle and blinding sampled AFTER the adversary is fixed), an
information-theoretic counting bound with NO cryptographic assumption. This file rewires Lane B's
reduction shape onto that class.

## What the rewiring IS (and honestly is not)

Lane B's extractor `recoverToPreimage` turned a span-recoverer into a wide-hash preimage-finder
inside the FIXED-ORACLE game pair. That game pair is UNSALVAGEABLE at any cost class admitting the
hardcoder: with the commitment fixed, "recover the opening" is won by writing the opening down, so
no faithful embedding of Lane B's `Adversary (spanRecoverGame)` into the keyed class exists — the
rewiring is at the GAME level, not an adversary-by-adversary bridge. The span-recovery break is
restated over the keyed random oracle (`SpanRecoverer`, §2): the adversary fixes two candidate
spans and a `Q`-query tree BEFORE the oracle and the blinding are sampled, receives the challenge
commitment, and outputs the span it believes was committed. The successor extractor
`recoverToDistinguisher` (§3) — Lane B's `recoverToPreimage` role, on the keyed side — turns a
recoverer into a `HidingDistinguisher` by a pure output reshaping (claim-check the recovered
span), PRESERVING the query budget (`mapTree`); the recoverer's two-world recovery gap IS the
extracted distinguisher's hiding advantage (`spanRecoverGap_eq_hidingAdv`), so the PROVED floor
applies. Nothing here is conditional on a refutable cost-model floor: `span_hiding_from_keyed_floor`
is an UNCONDITIONAL theorem of the keyed-ROM query-bounded model.

  * **The headline (§5):** `span_hiding_from_keyed_floor` — at any `λ`-bit-blinding family, EVERY
    polynomial-query keyed span-recoverer's recovery gap is NEGLIGIBLE, by `keyedRomHiding_hard`
    through the extractor. Deployed-shape corollary `blindedSpan_recovery_negl`; the recovery
    interpretation `recoverProb_sum_le`: a `Q`-query recoverer identifies the committed span no
    better than the blind guesser, up to `2Q/|B|` — `recoverProb₀ + recoverProb₁ ≤ 1 + 2Q/|B|`.
  * **The retirement (§6):** `span_recovery_rewired` pins BOTH halves — the successor floor holds
    at the deployed shape AND the floor Lane B rested on is refuted (Lane B's own theorem, cited
    READ-ONLY as a refutation; it appears NOWHERE as a hypothesis).
  * **Teeth (§4, §6):** the HARDCODER (the exact adversary that refuted Lane B's floor) is
    ADMITTED by the keyed class at `Q = 0` and its recovery gap is EXACTLY `0`
    (`hardcodeRecoverer_gap_zero`) — defanged, not excluded. A REAL one-query recoverer has
    strictly POSITIVE gap (`oneQueryRecoverer_gap_pos`) — the class contains genuine attacks. The
    FULL-TAPE recoverer prices the `⊤` pole at `1 − 1/|R|` (`topRecoverer_gap`), breaks the bound
    at a concrete instance (`canary_top_breaks_recover_bound`), is PROVABLY outside the one-query
    class (`canary_topRecoverer_not_oneQuery`), and refutes the unrestricted recovery floor at the
    deployed family (`blindedSpan_recoveryTop_false`). The CANARY `example` pins that the floor at
    an UNRELATED distinguisher does not discharge the recoverer's bound — the extractor is
    load-bearing, not a `P → P` unfold.

## Named residuals — at CURRENT resolution

  1. **ROM-modeling of the wide Poseidon2** — the same standard, named, undischarged residual the
     collision floor (`RomQueryFloor`) and the hiding floor (`KeyedRomHidingFloor`) carry.
  2. **Query budget ≠ running time.** The class bounds ORACLE QUERIES; work between queries is
     unbounded (`RomQueryFloor`'s named residual). NO `PolyTimeRomBridge` (a poly-time ⇒
     query-bounded keystone) exists in this tree as of 2026-07-23 — if one lands, THIS file's
     `span_hiding_from_keyed_floor` is the exact site where it would lift the conclusion to the
     poly-time class; until then no poly-time claim is made.
  3. **Lane B's fixed-oracle games are RETIRED, not bridged** (see above): the successor game
     re-keys the experiment; Lane B's §(a) statistical half and its in-file refutation remain
     standing and are untouched.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. NEW ADDITIVE file; imports read-only; the refuted floor is cited only under `¬`.
-/
import Dregg2.Crypto.KeyedRomHidingFloor
import Dregg2.Tactics

namespace Metatheory.Open.BlindedSpanHidingKeyed

open Dregg2.Crypto.KeyedRomHidingFloor
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded Ensemble)
open Dregg2.Crypto.ProbCrypto (winProb winProb_nonneg winProb_le_one)

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## §1 — budget-preserving output reshaping of a query tree, and a disjointness fact.

The keyed extractor is a PURE OUTPUT RESHAPING of the recoverer's tree — the same "assemble the
answer, no new queries" discipline Lane B's `recoverToPreimage` had, now with the resource that
matters (the QUERY budget) preserved by construction. -/

section MapTree

variable {D R A A' : Type}

/-- Post-compose a query tree's output — NO change to its query structure. This is what "the
extractor is a pure reshaping" MEANS at the query-counted class: the budget is preserved on the
nose (`mapTree_queryBounded`), where Lane B could only assert an `IsPolyTime` overhead bound. -/
def mapTree (f : A → A') : OracleComp D R A → OracleComp D R A'
  | .pure a => .pure (f a)
  | .query d k => .query d (fun r => mapTree f (k r))

@[simp] theorem mapTree_pure (f : A → A') (a : A) :
    mapTree (D := D) (R := R) f (.pure a) = .pure (f a) := rfl

@[simp] theorem mapTree_query (f : A → A') (d : D) (k : R → OracleComp D R A) :
    mapTree f (.query d k) = .query d (fun r => mapTree f (k r)) := rfl

/-- The reshaped tree computes `f` of the original's output — same path, same queries. -/
theorem mapTree_eval (f : A → A') (M : OracleComp D R A) (H : D → R) :
    (mapTree f M).eval H = f (M.eval H) := by
  induction M with
  | pure a => rfl
  | query d k ih =>
      rw [mapTree_query, OracleComp.eval_query, OracleComp.eval_query]
      exact ih (H d)

/-- **THE BUDGET IS PRESERVED EXACTLY.** A `Q`-query tree reshaped is a `Q`-query tree — the
extractor spends ZERO additional queries. -/
theorem mapTree_queryBounded (f : A → A') {Q : ℕ} {M : OracleComp D R A}
    (h : QueryBounded Q M) : QueryBounded Q (mapTree f M) := by
  induction h with
  | pure n a =>
      rw [mapTree_pure]
      exact .pure n (f a)
  | query n d k hk ih =>
      rw [mapTree_query]
      exact .query n d _ (fun r => ih r)

end MapTree

/-- **Disjoint win events share one unit of probability.** If no outcome wins both games, the win
probabilities sum to at most `1` — the counting fact behind "you cannot name the committed span
AND misname it". -/
theorem winProb_add_le_one {Ω : Type} [Fintype Ω] (p q : Ω → Bool)
    (hdisj : ∀ ω, p ω = true → q ω = true → False) :
    winProb p + winProb q ≤ 1 := by
  classical
  unfold Dregg2.Crypto.ProbCrypto.winProb
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
  · simp [h0]
  · have hpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast h0
    rw [← add_div, div_le_one hpos]
    have hdis : Disjoint (Finset.univ.filter (fun o => p o = true))
        (Finset.univ.filter (fun o => q o = true)) :=
      Finset.disjoint_left.mpr (fun {o} hp hq =>
        hdisj o (Finset.mem_filter.1 hp).2 (Finset.mem_filter.1 hq).2)
    have hcard : (Finset.univ.filter (fun o => p o = true)).card
        + (Finset.univ.filter (fun o => q o = true)).card ≤ Fintype.card Ω := by
      rw [← Finset.card_union_of_disjoint hdis]
      exact Finset.card_le_univ _
    exact_mod_cast hcard

/-! ## §2 — the KEYED span-recovery break.

The successor of Lane B's `spanRecoverGame`, with the disease removed at the STATEMENT: nothing
is fixed for the adversary to hardcode. The recoverer commits to two candidate spans and (in the
class, §3) a query tree; only THEN are the oracle `H` and the hidden blinding `r` sampled, and the
challenge commitment `H (m_b, r)` — the deployed `hash(span_digest ‖ BLINDING)` shape — is handed
over. The recoverer outputs the span it believes was committed. -/

section Recovery

variable {Msg B R : Type}
variable [Fintype Msg] [DecidableEq Msg] [Fintype B] [DecidableEq B]
variable [Fintype R] [DecidableEq R] [Nonempty B] [Nonempty R]

/-- **A RAW SPAN-RECOVERER.** Two candidate spans fixed up front, and a `recover` verdict that at
the RAW type may read the whole experiment tape `(H, r, c)` — deliberately maximal, exactly as
`HidingDistinguisher.accept`; `QueryRecovery` below is the restriction with content, and §4's
`topRecoverer` shows what the raw type can do that the class cannot. The output is the span the
adversary CLAIMS was committed — recovery, the hiding break Lane B's consumer game named. -/
structure SpanRecoverer (Msg B R : Type) where
  /-- The first candidate span (a fixed-width span digest; width fixed by the TYPE). -/
  msg0 : Msg
  /-- The second candidate span. -/
  msg1 : Msg
  /-- The recovery verdict: full oracle, blinding, challenge commitment ↦ claimed span. Raw. -/
  recover : ((Msg × B) → R) → B → R → Msg

/-- The committed span in world `b`. -/
def SpanRecoverer.msgAt (A : SpanRecoverer Msg B R) : Bool → Msg
  | false => A.msg0
  | true => A.msg1

/-- **THE PROBABILITY THE RECOVERER CLAIMS `msg0`, in world `b`.** The challenger samples `H`
uniform over `Msg × B → R` and the blinding `r` uniform over `B` — both AFTER `A` is fixed — and
hands `A` the challenge `H (msgAt b, r)`; this is the mass on which `A` names `msg0`. The exact
shape of `KeyedRomHidingFloor.acceptProb`, with the accept verdict "claimed span = `msg0`". -/
noncomputable def claimProb (A : SpanRecoverer Msg B R) (b : Bool) : ℝ :=
  (∑ r : B, winProb (fun H : (Msg × B) → R =>
      decide (A.recover H r (H (A.msgAt b, r)) = A.msg0)))
    / (Fintype.card B : ℝ)

/-- **THE PROBABILITY THE RECOVERER RECOVERS the committed span, in world `b`** — it outputs
`msgAt b` when `msgAt b` was committed. The genuine recovery-success measure. -/
noncomputable def recoverProb (A : SpanRecoverer Msg B R) (b : Bool) : ℝ :=
  (∑ r : B, winProb (fun H : (Msg × B) → R =>
      decide (A.recover H r (H (A.msgAt b, r)) = A.msgAt b)))
    / (Fintype.card B : ℝ)

/-- **THE SPAN-RECOVERY GAP** — how much more often the recoverer names `msg0` when `msg0` IS
committed than when `msg1` is. The two-world form of "the output carries information about the
committed span"; `0` for every oracle-blind strategy (hardcoders included, §4). -/
noncomputable def spanRecoverGap (A : SpanRecoverer Msg B R) : ℝ :=
  |claimProb A false - claimProb A true|

/-- **THE QUERY-BOUNDED KEYED CLASS — the `Eff` with content.** The recoverer FACTORS THROUGH a
challenge-indexed `Q`-query tree: its claimed span is a function of the challenge commitment and
the oracle answers it asked for — NOT of the raw oracle and NOT of the hidden blinding. Fixed
before the oracle and blinding are sampled: the `KeyedRomFloor` discipline that defeats
hardcoding. -/
def QueryRecovery (Q : ℕ) (A : SpanRecoverer Msg B R) : Prop :=
  ∃ N : R → OracleComp (Msg × B) R Msg,
    (∀ c, QueryBounded Q (N c)) ∧
    ∀ (H : (Msg × B) → R) (r : B) (c : R), A.recover H r c = (N c).eval H

/-! ## §3 — THE REWIRED REDUCTION: a span-recoverer becomes a hiding distinguisher.

Lane B's `recoverToPreimage` assembled the recovered opening into a wide-hash preimage; its
efficiency was an `IsPolyTime` discharge over a floor that turned out FALSE. The keyed extractor
claim-checks the recovered span; its efficiency is the EXACT budget preservation of `mapTree`,
and the floor it feeds is PROVED. -/

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES** — the keyed successor of Lane B's
`recoverToPreimage`. A span-recoverer becomes a hiding distinguisher by accepting exactly when
the recovered span is `msg0`: a pure output reshaping with everything else passed through. -/
def recoverToDistinguisher (A : SpanRecoverer Msg B R) : HidingDistinguisher Msg B R where
  msg0 := A.msg0
  msg1 := A.msg1
  accept := fun H r c => decide (A.recover H r c = A.msg0)

/-- **⚑ CLASS-PRESERVATION — the reduction, at the resource level.** A `Q`-query keyed recoverer
extracts to a `Q`-query keyed distinguisher: the claim-check rides the SAME tree (`mapTree`), so
not one query is added. The keyed analogue of Lane B's `hEff` discharge — proved structurally,
not assumed. -/
theorem recoverToDistinguisher_queryHiding (A : SpanRecoverer Msg B R) (Q : ℕ)
    (hA : QueryRecovery Q A) : QueryHiding Q (recoverToDistinguisher A) := by
  obtain ⟨N, hQb, hrun⟩ := hA
  refine ⟨fun c => mapTree (fun m => decide (m = A.msg0)) (N c),
    fun c => mapTree_queryBounded _ (hQb c), fun H r c => ?_⟩
  show decide (A.recover H r c = A.msg0)
    = (mapTree (fun m => decide (m = A.msg0)) (N c)).eval H
  rw [mapTree_eval, hrun H r c]

/-- The recoverer's claim probability IS the extracted distinguisher's accept probability — the
extractor changes the TYPE of the break, not the experiment. -/
theorem claimProb_eq_acceptProb (A : SpanRecoverer Msg B R) (b : Bool) :
    claimProb A b = acceptProb (recoverToDistinguisher A) b := by
  cases b <;> rfl

/-- **⚑ GAP-PRESERVATION — the reduction, at the advantage level.** The span-recovery gap IS the
extracted distinguisher's hiding advantage — an EQUALITY, not an inequality: the keyed floor's
bound transfers to the recoverer with no loss. Lane B's `recover_adv_le`, sharpened. -/
theorem spanRecoverGap_eq_hidingAdv (A : SpanRecoverer Msg B R) :
    spanRecoverGap A = hidingAdv (recoverToDistinguisher A) := by
  unfold spanRecoverGap hidingAdv
  rw [claimProb_eq_acceptProb A false, claimProb_eq_acceptProb A true]

/-- **⚑ THE PER-BUDGET BOUND, on the PROVED floor.** Every `Q`-query keyed span-recoverer's
recovery gap is at most `2Q/|B|` — `KeyedRomHidingFloor.hidingAdv_le` (proved, counting, no
assumption) through the extractor. This is the statement `span_recovery_hard_from_polyTime`
wanted to be: same consumer, real floor. -/
theorem spanRecoverGap_le (A : SpanRecoverer Msg B R) (Q : ℕ) (hA : QueryRecovery Q A) :
    spanRecoverGap A ≤ 2 * (Q : ℝ) / (Fintype.card B : ℝ) := by
  rw [spanRecoverGap_eq_hidingAdv]
  exact hidingAdv_le _ Q (recoverToDistinguisher_queryHiding A Q hA)

/-- In world `false` the recovery target IS `msg0`: recovering and claiming coincide. -/
theorem recoverProb_false_eq_claimProb (A : SpanRecoverer Msg B R) :
    recoverProb A false = claimProb A false := rfl

/-- **⚑ RECOVERY IS NO BETTER THAN BLIND GUESSING, up to `2Q/|B|`.** For distinct candidate spans,
the two worlds' recovery successes sum to at most `1 + 2Q/|B|`. The blind guesser that always
claims `msg0` achieves the sum `1` exactly (`recoverProb₀ = 1`, `recoverProb₁ = 0`); a `Q`-query
tree can beat it by at most the floor's `2Q/|B|`. This is the recovery-flavoured reading of the
gap bound — the quantitative content of "the commitment hides its span". -/
theorem recoverProb_sum_le (A : SpanRecoverer Msg B R) (Q : ℕ) (hA : QueryRecovery Q A)
    (hne : A.msg0 ≠ A.msg1) :
    recoverProb A false + recoverProb A true
      ≤ 1 + 2 * (Q : ℝ) / (Fintype.card B : ℝ) := by
  have hBpos : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  -- World `true`: recovering `msg1` and claiming `msg0` are DISJOINT events.
  have htrue : recoverProb A true + claimProb A true ≤ 1 := by
    unfold recoverProb claimProb
    rw [← add_div, div_le_one hBpos]
    calc (∑ r : B, winProb (fun H : (Msg × B) → R =>
            decide (A.recover H r (H (A.msgAt true, r)) = A.msgAt true)))
          + (∑ r : B, winProb (fun H : (Msg × B) → R =>
            decide (A.recover H r (H (A.msgAt true, r)) = A.msg0)))
        = ∑ r : B, (winProb (fun H : (Msg × B) → R =>
            decide (A.recover H r (H (A.msgAt true, r)) = A.msgAt true))
          + winProb (fun H : (Msg × B) → R =>
            decide (A.recover H r (H (A.msgAt true, r)) = A.msg0))) := by
          rw [Finset.sum_add_distrib]
      _ ≤ ∑ _r : B, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun r _ => ?_)
          refine winProb_add_le_one _ _ (fun H h1 h0 => ?_)
          have e1 : A.recover H r (H (A.msgAt true, r)) = A.msgAt true :=
            of_decide_eq_true h1
          have e0 : A.recover H r (H (A.msgAt true, r)) = A.msg0 :=
            of_decide_eq_true h0
          exact hne (e0.symm.trans e1)
      _ = (Fintype.card B : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  -- The gap bound turns the world-`false` surplus into `2Q/|B|`.
  have hgapdef : spanRecoverGap A = |claimProb A false - claimProb A true| := rfl
  have hgap : claimProb A false - claimProb A true
      ≤ 2 * (Q : ℝ) / (Fintype.card B : ℝ) := by
    have h1 := spanRecoverGap_le A Q hA
    have h2 : claimProb A false - claimProb A true ≤ spanRecoverGap A := by
      rw [hgapdef]
      exact le_abs_self _
    linarith
  have hfalse : recoverProb A false = claimProb A false :=
    recoverProb_false_eq_claimProb A
  linarith

/-! ## §4 — TEETH: the hardcoder DEFANGED, a real winner INSIDE, the full tape PRICED OUT. -/

/-- **THE HARDCODER** — the EXACT adversary shape that refuted Lane B's `IsPolyTime` floor
(`widePreimageFloor_polyTime_false`'s constant finder): it ignores everything and claims `msg0`. -/
def hardcodeRecoverer (m0 m1 : Msg) : SpanRecoverer Msg B R where
  msg0 := m0
  msg1 := m1
  recover := fun _ _ _ => m0

/-- The hardcoder is ADMITTED by the keyed class, at budget `0` — it is not excluded by fiat. -/
theorem hardcodeRecoverer_queryRecovery (m0 m1 : Msg) :
    QueryRecovery 0 (hardcodeRecoverer (B := B) (R := R) m0 m1) :=
  ⟨fun _ => .pure m0, fun _ => .pure 0 m0, fun _ _ _ => rfl⟩

/-- Any `0`-query recoverer's gap is EXACTLY `0` — sampling the blinding after the adversary is
fixed makes hardcoding worthless. -/
theorem zeroQuery_spanRecoverGap_eq_zero (A : SpanRecoverer Msg B R)
    (hA : QueryRecovery 0 A) : spanRecoverGap A = 0 := by
  rw [spanRecoverGap_eq_hidingAdv]
  exact zeroQuery_hidingAdv_eq_zero _ (recoverToDistinguisher_queryHiding A 0 hA)

/-- **(TOOTH — the hardcoder, DEFANGED.)** Where Lane B's floor let this adversary win with
probability `1`, the keyed game gives it recovery gap EXACTLY `0`: it learns NOTHING about the
committed span. The disease is cured at the statement, not bandaged at the class. -/
theorem hardcodeRecoverer_gap_zero (m0 m1 : Msg) :
    spanRecoverGap (hardcodeRecoverer (B := B) (R := R) m0 m1) = 0 :=
  zeroQuery_spanRecoverGap_eq_zero _ (hardcodeRecoverer_queryRecovery m0 m1)

/-- **A REAL ONE-QUERY RECOVERER.** Guesses a blinding `r0`, probes `(m0, r0)`, and claims `m0`
exactly when the probe matches the challenge — `KeyedRomHidingFloor.oneQueryAdv`, recovery-typed. -/
def oneQueryRecoverer (m0 m1 : Msg) (r0 : B) : SpanRecoverer Msg B R where
  msg0 := m0
  msg1 := m1
  recover := fun H _r c => if H (m0, r0) = c then m0 else m1

/-- The one-query recoverer is in the class at every budget `≥ 1` — it factors through a genuine
one-query tree. -/
theorem oneQueryRecoverer_queryRecovery (m0 m1 : Msg) (r0 : B) (Q : ℕ) (hQ : 1 ≤ Q) :
    QueryRecovery Q (oneQueryRecoverer (B := B) (R := R) m0 m1 r0) := by
  refine ⟨fun c => .query (m0, r0) (fun a => .pure (if a = c then m0 else m1)),
    fun c => ?_, fun H r c => rfl⟩
  exact (QueryBounded.query 0 (m0, r0) _ (fun a => QueryBounded.pure 0 _)).mono hQ

/-- The one-query recoverer EXTRACTS TO `oneQueryAdv` exactly — the reduction sends the real
recovery attack to the real distinguishing attack. -/
theorem oneQueryRecoverer_extract_eq (m0 m1 : Msg) (r0 : B) (hne : m0 ≠ m1) :
    recoverToDistinguisher (oneQueryRecoverer (B := B) (R := R) m0 m1 r0)
      = oneQueryAdv m0 m1 r0 := by
  have hacc : (fun (H : (Msg × B) → R) (_r : B) (c : R) =>
        decide ((if H (m0, r0) = c then m0 else m1) = m0))
      = fun (H : (Msg × B) → R) (_r : B) (c : R) => decide (H (m0, r0) = c) := by
    funext H r c
    by_cases h : H (m0, r0) = c
    · simp [h]
    · simp [h, Ne.symm hne]
  show HidingDistinguisher.mk m0 m1
      (fun H _r c => decide ((if H (m0, r0) = c then m0 else m1) = m0))
    = HidingDistinguisher.mk m0 m1 (fun H _r c => decide (H (m0, r0) = c))
  rw [hacc]

/-- **(TOOTH — the class contains a recoverer that REALLY WINS SOMETIMES.)** With a genuine digest
space the one-query recoverer's gap is strictly positive: the bound `2Q/|B|` is a statement about
something. -/
theorem oneQueryRecoverer_gap_pos (m0 m1 : Msg) (r0 : B) (hne : m0 ≠ m1)
    (hR : 1 < Fintype.card R) :
    0 < spanRecoverGap (oneQueryRecoverer (B := B) (R := R) m0 m1 r0) := by
  rw [spanRecoverGap_eq_hidingAdv, oneQueryRecoverer_extract_eq m0 m1 r0 hne]
  exact oneQueryAdv_hidingAdv_pos m0 m1 r0 hne hR

/-- **THE FULL-TAPE RECOVERER** — reads all of `H` and the actual hidden blinding `r` (legal at
the raw type, impossible for a query tree), recomputes the world-`false` commitment, and names
the span accordingly. -/
def topRecoverer (m0 m1 : Msg) : SpanRecoverer Msg B R where
  msg0 := m0
  msg1 := m1
  recover := fun H r c => if c = H (m0, r) then m0 else m1

/-- The full-tape recoverer extracts to `topAdv` exactly. -/
theorem topRecoverer_extract_eq (m0 m1 : Msg) (hne : m0 ≠ m1) :
    recoverToDistinguisher (topRecoverer (B := B) (R := R) m0 m1) = topAdv m0 m1 := by
  have hacc : (fun (H : (Msg × B) → R) (r : B) (c : R) =>
        decide ((if c = H (m0, r) then m0 else m1) = m0))
      = fun (H : (Msg × B) → R) (r : B) (c : R) => decide (c = H (m0, r)) := by
    funext H r c
    by_cases h : c = H (m0, r)
    · simp [h]
    · simp [h, Ne.symm hne]
  show HidingDistinguisher.mk m0 m1
      (fun H r c => decide ((if c = H (m0, r) then m0 else m1) = m0))
    = HidingDistinguisher.mk m0 m1 (fun H r c => decide (c = H (m0, r)))
  rw [hacc]

/-- **(⊤-POLE, EXACTLY PRICED.)** Unrestricted, span recovery succeeds with gap `1 − 1/|R|`:
remove the query bound and the span is recovered almost surely. The class restriction is
load-bearing. -/
theorem topRecoverer_gap (m0 m1 : Msg) (hne : m0 ≠ m1) :
    spanRecoverGap (topRecoverer (B := B) (R := R) m0 m1)
      = 1 - 1 / (Fintype.card R : ℝ) := by
  rw [spanRecoverGap_eq_hidingAdv, topRecoverer_extract_eq m0 m1 hne]
  exact topAdv_hidingAdv m0 m1 hne

end Recovery

/-! ### Concrete canaries — `Msg = Fin 2`, `B = Fin 8`, `R = Fin 4`, budget `Q = 1`
(the `KeyedRomHidingFloor` §7 instantiation, on the recovery side). -/

/-- **(CANARY — the full-tape recoverer BREAKS the one-query bound.)** Gap `3/4 > 1/4`. If this
ever stops holding, the bound has degenerated. -/
theorem canary_top_breaks_recover_bound :
    ¬ (spanRecoverGap (topRecoverer (Msg := Fin 2) (B := Fin 8) (R := Fin 4) 0 1)
        ≤ 2 * ((1 : ℕ) : ℝ) / (Fintype.card (Fin 8) : ℝ)) := by
  rw [spanRecoverGap_eq_hidingAdv,
    topRecoverer_extract_eq (Msg := Fin 2) (B := Fin 8) (R := Fin 4) 0 1 (by decide)]
  exact canary_top_breaks_bound

/-- **(CANARY — hence the full-tape recoverer is PROVABLY not a one-query tree.)** -/
theorem canary_topRecoverer_not_oneQuery :
    ¬ QueryRecovery 1 (topRecoverer (Msg := Fin 2) (B := Fin 8) (R := Fin 4) 0 1) := by
  intro h
  have hext := recoverToDistinguisher_queryHiding _ 1 h
  rw [topRecoverer_extract_eq (Msg := Fin 2) (B := Fin 8) (R := Fin 4) 0 1 (by decide)] at hext
  exact canary_topAdv_not_oneQuery hext

/-! ## §5 — the λ-indexed family layer and ⚑ THE HEADLINE. -/

/-- A family of raw span-recoverers, one per security parameter. -/
structure FamilySpanRecoverer (F : HidingRomFamily) where
  /-- The recoverer at parameter `l`. -/
  adv : ∀ l, SpanRecoverer (F.Msg l) (F.B l) (F.R l)

/-- **THE QUERY-BOUNDED KEYED CLASS, λ-indexed** — the `Eff` of the recovery floor. -/
def KeyedRomRecoveryEff (F : HidingRomFamily) (Q : ℕ → ℕ)
    (A : FamilySpanRecoverer F) : Prop :=
  ∀ l, QueryRecovery (Q l) (A.adv l)

/-- The family recoverer's recovery-gap ensemble. -/
noncomputable def famRecoverGap (F : HidingRomFamily) (A : FamilySpanRecoverer F) :
    Ensemble := fun l =>
  letI := F.msgFin l; letI := F.msgDec l; letI := F.bFin l; letI := F.bDec l
  letI := F.rFin l; letI := F.rDec l; letI := F.bNe l; letI := F.rNe l
  spanRecoverGap (A.adv l)

/-- **THE RECOVERY FLOOR SCHEMA** — `HidingHard`'s shape, at the recovery break. -/
def RecoveryHard (F : HidingRomFamily) (Eff : FamilySpanRecoverer F → Prop) : Prop :=
  ∀ A : FamilySpanRecoverer F, Eff A → Negl (famRecoverGap F A)

/-- **(⊥-pole — vacuous, recorded so satisfiability is not mistaken for evidence.)** -/
theorem recoveryHard_bot_vacuous (F : HidingRomFamily) :
    RecoveryHard F (fun _ => False) := fun _ h => h.elim

/-- The extractor, λ-indexed. -/
def extractFamily (F : HidingRomFamily) (A : FamilySpanRecoverer F) :
    FamilyHidingDistinguisher F :=
  ⟨fun l =>
    letI := F.msgDec l
    recoverToDistinguisher (A.adv l)⟩

/-- Class-preservation, λ-indexed: a keyed `Q`-query recoverer family extracts to a keyed
`Q`-query distinguisher family. -/
theorem extractFamily_eff (F : HidingRomFamily) (Q : ℕ → ℕ) (A : FamilySpanRecoverer F)
    (hA : KeyedRomRecoveryEff F Q A) : KeyedRomHidingEff F Q (extractFamily F A) := by
  intro l
  letI := F.msgFin l; letI := F.msgDec l; letI := F.bFin l; letI := F.bDec l
  letI := F.rFin l; letI := F.rDec l; letI := F.bNe l; letI := F.rNe l
  show QueryHiding (Q l) (recoverToDistinguisher (A.adv l))
  exact recoverToDistinguisher_queryHiding (A.adv l) (Q l) (hA l)

/-- Gap-preservation, λ-indexed: the recovery-gap ensemble IS the extracted family's hiding
ensemble. -/
theorem famRecoverGap_eq (F : HidingRomFamily) (A : FamilySpanRecoverer F) :
    famRecoverGap F A = famHidingAdv F (extractFamily F A) := by
  funext l
  letI := F.msgFin l; letI := F.msgDec l; letI := F.bFin l; letI := F.bDec l
  letI := F.rFin l; letI := F.rDec l; letI := F.bNe l; letI := F.rNe l
  show spanRecoverGap (A.adv l) = hidingAdv (recoverToDistinguisher (A.adv l))
  exact spanRecoverGap_eq_hidingAdv (A.adv l)

/-- **⚑⚑⚑ SPAN HIDING FROM THE KEYED FLOOR — THE HEADLINE, the rewired Lane B.** At any family
with a `λ`-bit blinding space and any polynomially bounded query budget, EVERY keyed
query-bounded span-recoverer's recovery gap is NEGLIGIBLE: the blinded commitment hides its span.

Resting on `keyedRomHiding_hard` — PROVED, information-theoretic, no cryptographic assumption —
through the budget-exact extractor `recoverToDistinguisher`; NOT on `WidePreimageFloor` at
`IsPolyTime`, which is REFUTED (`widePreimageFloor_polyTime_false`) and appears nowhere here as a
hypothesis. Unlike Lane B's `span_recovery_hard_from_polyTime` this theorem is UNCONDITIONAL (in
the keyed-ROM query-bounded model): its named residuals are the ROM-modeling of the wide Poseidon2
and the query-budget (not running-time) resource — see the header. NO `PolyTimeRomBridge` exists
in this tree today; if that keystone lands, applying it HERE lifts this conclusion to the
poly-time class. -/
theorem span_hiding_from_keyed_floor (F : HidingRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => 2 * (Q l : ℝ) + 1))
    (hw : ∀ l, letI := F.bFin l; Fintype.card (F.B l) = 2 ^ l) :
    RecoveryHard F (KeyedRomRecoveryEff F Q) := by
  intro A hA
  rw [famRecoverGap_eq F A]
  exact keyedRomHiding_hard F Q hQ hw (extractFamily F A) (extractFamily_eff F Q A hA)

/-- **(CANARY — the floor at an UNRELATED distinguisher does NOT discharge the recoverer's
bound.)** Only the extractor connects the two games; if this stops failing, the reduction has
degenerated into a `P → P` the floor would satisfy directly. -/
example (F : HidingRomFamily) (Q : ℕ → ℕ)
    (_hQ : PolyBounded (fun l => 2 * (Q l : ℝ) + 1))
    (_hw : ∀ l, letI := F.bFin l; Fintype.card (F.B l) = 2 ^ l)
    (_A : FamilySpanRecoverer F) (B' : FamilyHidingDistinguisher F)
    (_hB : KeyedRomHidingEff F Q B') : True := by
  fail_if_success
    (have : Negl (famRecoverGap F _A) := keyedRomHiding_hard F Q _hQ _hw B' _hB)
  trivial

/-! ## §6 — the deployed shape, the poles there, and ⚑ THE RETIREMENT. -/

/-- **SPAN RECOVERY AT THE DEPLOYED SHAPE, NEGLIGIBLE** — `blindedSpanRomFamily` is
`KeyedRomHidingFloor`'s deployed-shape family (`λ`-bit blinding felt, wide 8-felt digest). -/
theorem blindedSpan_recovery_negl (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => 2 * (Q l : ℝ) + 1)) :
    RecoveryHard blindedSpanRomFamily (KeyedRomRecoveryEff blindedSpanRomFamily Q) :=
  span_hiding_from_keyed_floor blindedSpanRomFamily Q hQ blindedSpanRom_card_B

/-- **(TOOTH — the class at the deployed family is INHABITED by a real winner.)** The one-query
recoverer family has strictly positive gap at every parameter — the floor is not `⊥` in
disguise. -/
theorem blindedSpan_recovery_inhabited (Q : ℕ → ℕ) (hQ : ∀ l, 1 ≤ Q l) :
    ∃ A : FamilySpanRecoverer blindedSpanRomFamily,
      KeyedRomRecoveryEff blindedSpanRomFamily Q A
        ∧ ∀ l, 0 < famRecoverGap blindedSpanRomFamily A l := by
  have hlt : ∀ l : ℕ, 1 < 2 * 2 ^ l := by
    intro l
    have : 0 < 2 ^ l := by positivity
    omega
  refine ⟨⟨fun l => oneQueryRecoverer (B := Fin (2 ^ l)) (R := Fin (2 ^ (8 * l + 8)))
      (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l)) (⟨1, hlt l⟩ : Fin (2 * 2 ^ l))
      (⟨0, by positivity⟩ : Fin (2 ^ l))⟩, fun l => ?_, fun l => ?_⟩
  · letI := blindedSpanRomFamily.msgFin l; letI := blindedSpanRomFamily.msgDec l
    letI := blindedSpanRomFamily.bFin l; letI := blindedSpanRomFamily.bDec l
    letI := blindedSpanRomFamily.rFin l; letI := blindedSpanRomFamily.rDec l
    letI := blindedSpanRomFamily.bNe l; letI := blindedSpanRomFamily.rNe l
    exact oneQueryRecoverer_queryRecovery _ _ _ (Q l) (hQ l)
  · letI := blindedSpanRomFamily.msgFin l; letI := blindedSpanRomFamily.msgDec l
    letI := blindedSpanRomFamily.bFin l; letI := blindedSpanRomFamily.bDec l
    letI := blindedSpanRomFamily.rFin l; letI := blindedSpanRomFamily.rDec l
    letI := blindedSpanRomFamily.bNe l; letI := blindedSpanRomFamily.rNe l
    show 0 < spanRecoverGap (oneQueryRecoverer (B := Fin (2 ^ l)) (R := Fin (2 ^ (8 * l + 8)))
      (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l)) (⟨1, hlt l⟩ : Fin (2 * 2 ^ l))
      (⟨0, by positivity⟩ : Fin (2 ^ l)))
    refine oneQueryRecoverer_gap_pos _ _ _ ?_ ?_
    · intro h
      have := congrArg Fin.val h
      simp at this
    · show 1 < Fintype.card (Fin (2 ^ (8 * l + 8)))
      rw [Fintype.card_fin]
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (8 * l + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **(⊤-POLE at the deployed family — the UNRESTRICTED recovery floor is FALSE.)** The full-tape
recoverer family's gap is `1 − 1/|R l| ≥ 1/2` at every parameter — not negligible. Same game, two
classes, opposite verdicts: the query bound does the work. -/
theorem blindedSpan_recoveryTop_false :
    ¬ RecoveryHard blindedSpanRomFamily (fun _ => True) := by
  have hlt : ∀ l : ℕ, 1 < 2 * 2 ^ l := by
    intro l
    have : 0 < 2 ^ l := by positivity
    omega
  intro h
  let Atop : FamilySpanRecoverer blindedSpanRomFamily :=
    ⟨fun l => topRecoverer (B := Fin (2 ^ l)) (R := Fin (2 ^ (8 * l + 8)))
      (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l)) (⟨1, hlt l⟩ : Fin (2 * 2 ^ l))⟩
  have hnegl := h Atop trivial
  have hge : ∀ l, (1 : ℝ) / 2 ≤ famRecoverGap blindedSpanRomFamily Atop l := by
    intro l
    letI := blindedSpanRomFamily.msgFin l; letI := blindedSpanRomFamily.msgDec l
    letI := blindedSpanRomFamily.bFin l; letI := blindedSpanRomFamily.bDec l
    letI := blindedSpanRomFamily.rFin l; letI := blindedSpanRomFamily.rDec l
    letI := blindedSpanRomFamily.bNe l; letI := blindedSpanRomFamily.rNe l
    have hne : (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l)) ≠ ⟨1, hlt l⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    show (1 : ℝ) / 2 ≤ spanRecoverGap
      (topRecoverer (B := Fin (2 ^ l)) (R := Fin (2 ^ (8 * l + 8)))
        (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l)) (⟨1, hlt l⟩ : Fin (2 * 2 ^ l)))
    rw [topRecoverer_gap _ _ hne, Fintype.card_fin]
    have h2 : (2 : ℝ) ≤ ((2 ^ (8 * l + 8) : ℕ) : ℝ) := by
      have h2n : (2 : ℕ) ≤ 2 ^ (8 * l + 8) := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (8 * l + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast h2n
    have hinv : 1 / ((2 ^ (8 * l + 8) : ℕ) : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) h2
    linarith
  obtain ⟨l, hlt2, hl2⟩ := ((hnegl 1).and (Filter.eventually_ge_atTop 2)).exists
  have hl2' : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
  have hnn : (0 : ℝ) ≤ famRecoverGap blindedSpanRomFamily Atop l :=
    le_trans (by norm_num) (hge l)
  rw [abs_of_nonneg hnn, pow_one] at hlt2
  have hinv : 1 / (l : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hl2'
  linarith [hge l]

/-- **⚑⚑⚑ THE REWIRING, IN ONE STATEMENT — the retirement pin.** Both halves at once:

  1. span recovery of the deployed-shape wide blinded commitment is NEGLIGIBLE against EVERY
     polynomial-query keyed adversary — PROVED, resting on `keyedRomHiding_hard` (counting, no
     assumption) through the budget-exact extractor;
  2. the floor the OLD conditional statement (`span_recovery_hard_from_polyTime`) rested on —
     Lane B's `WidePreimageFloor` at `IsPolyTime` — is REFUTED at every deployed commitment
     (Lane B's own theorem, cited read-only; it is a CONCLUSION here, never a hypothesis).

The old reduction was real but fed a false floor; the rewired reduction feeds a proved one. The
named residuals are the ROM-modeling of the wide Poseidon2 and the query-budget resource — not a
refutable cost-model floor. -/
theorem span_recovery_rewired (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => 2 * (Q l : ℝ) + 1)) :
    RecoveryHard blindedSpanRomFamily (KeyedRomRecoveryEff blindedSpanRomFamily Q)
      ∧ ∀ D : Metatheory.Open.BlindedSpanHiding.BlindedSpanCommitment,
          ¬ D.WidePreimageFloor (Dregg2.Crypto.CostAdversary.IsPolyTime D.preAnsSize) :=
  ⟨blindedSpan_recovery_negl Q hQ, fun D => D.widePreimageFloor_polyTime_false⟩

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  mapTree_eval,
  mapTree_queryBounded,
  winProb_add_le_one,
  recoverToDistinguisher_queryHiding,
  claimProb_eq_acceptProb,
  spanRecoverGap_eq_hidingAdv,
  spanRecoverGap_le,
  recoverProb_sum_le,
  hardcodeRecoverer_queryRecovery,
  zeroQuery_spanRecoverGap_eq_zero,
  hardcodeRecoverer_gap_zero,
  oneQueryRecoverer_queryRecovery,
  oneQueryRecoverer_extract_eq,
  oneQueryRecoverer_gap_pos,
  topRecoverer_extract_eq,
  topRecoverer_gap,
  canary_top_breaks_recover_bound,
  canary_topRecoverer_not_oneQuery,
  recoveryHard_bot_vacuous,
  extractFamily_eff,
  famRecoverGap_eq,
  span_hiding_from_keyed_floor,
  blindedSpan_recovery_negl,
  blindedSpan_recovery_inhabited,
  blindedSpan_recoveryTop_false,
  span_recovery_rewired
]

end Metatheory.Open.BlindedSpanHidingKeyed
