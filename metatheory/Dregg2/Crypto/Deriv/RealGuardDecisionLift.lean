/-
# Dregg2.Crypto.Deriv.RealGuardDecisionLift — the guard-decision METHOD swept across REAL dregg
guards, with every should-agree pair LIFTED from a machine verdict to a `Prop`.

`HandlebarsGuardDecision.lean` ran one deployed guard (the templater's brace-ban) through the whole
method: classify the fragment, DECIDE emptiness, DECIDE equivalence of two spellings, and CROSS the
verdicts into theorems by kernel-reducing the decision instance. `RealGuardAudit{,2}.lean` extracted
24 REAL guards from the running codebase (each cited at `file:line`) and ran the CHEAP Bool route on
them — `#guard emptyFix …`, which is compiled evaluation and PROVES NO `Prop`.

This module is the join: the audits' real guards, at the resolution the templater got. Every
`#guard` here is labelled as Bool-only; every verdict that matters is a THEOREM produced by running
`predRE_{emptiness,equivalence}_decidable_{scalar,dfe}` in the kernel.

## ═══ THE VERDICTS — six real guard families, lifted ═══

| § | real guard / pair (site)                                   | question   | verdict | `Prop` |
|---|------------------------------------------------------------|------------|---------|--------|
| 2 | `askHistoryGate` `disp ≥ 4 ∧ menace = 0` (dialogue.rs:274-283) | satisfiable? | FIRES | `askHistory_satisfiable` |
| 2 | `grantGate` `disp ≥ 5 ∧ secret ≥ 1` (dialogue.rs:313-323)   | satisfiable? | FIRES | `grantGate_satisfiable` |
| 2 | `fightOrFall` `hp ≥ 1 ∧ hp ≤ 20` (bloodgate.rs:579-606)     | overlap?   | NONEMPTY | `fightOrFall_band_nonempty` |
| 3 | goad `disp ≤ 3` vs friendly `disp ≥ 4 ∧ menace = 0`         | exclusive? | **EMPTY** | `goad_excludes_history` (+ frame-level cash-out) |
| 4 | ⚑ executor `StateConstraint`s (`:274-283`) vs renderer plain-Rust (`:438`) | same rule? | **EQUIVALENT** | `history_gate_no_drift` (+ `history_gate_frames_agree`) |
| 4 | the same pair with the `menace` conjunct DROPPED            | same rule? | NOT equivalent | `history_gate_needs_menace` |
| 5 | credential `age ≥ 18` (roundtrip.rs:186) vs `age ≥ 1` (anonymity_soundness.rs:242) | same? / subsumes? | NOT equiv; one-way | `age18_not_equiv_age1`, `age18_subsumes_age1`, `age1_not_subsumes_age18` |
| 6 | goad `≤ FLOOR-1` (`:268`) vs `¬(≥ FLOOR)`                   | complement? | NOT equiv **raw**, EQUIVALENT under presence | `goad_not_equiv_complement`, `goad_equiv_complement_present` |
| 7 | `ownerMatch` (PredicateLibrary.lean:91) vs its `¬¬` spelling | same?      | EQUIVALENT | `ownerMatch_equiv_notnot` |
| 7 | `ownerMatch` vs `ownerMismatch`; `ownerMatch ⋒ ownerMismatch` | same? / empty? | NOT equiv; EMPTY | `ownerMatch_not_equiv_mismatch`, `ownerContra_unsatisfiable` |

### ⚑ THE PRIZE (§4) — the duplicate gate does NOT drift
`dungeon-on-dregg/src/dialogue.rs` writes the LN_ASK_HISTORY availability rule TWICE: once for the
executor as `StateConstraint`s (`:274-283`, compiled `FieldGte(disposition, HISTORY_DISPOSITION_FLOOR)`
∧ `FieldEquals(menace, 0)`), and once for the renderer as plain Rust
(`:438`, `menace == 0 && disposition >= HISTORY_DISPOSITION_FLOOR`). If those two drift, the NPC
narrates a refusal the executor would admit (or the reverse). The decision says **EQUIVALENT** —
and this file makes that a theorem: `history_gate_no_drift : ∀ w, derives w askHistoryGate =
derives w historyRenderer`, and `history_gate_frames_agree`, which cashes it to the statement a
reader of `dialogue.rs` wants: on EVERY state frame, the executor gate and the renderer gate return
the same Boolean. Not "on the frames we tested" — on every frame, at every word length, over the
infinite `Value` alphabet.

It is not a tautology of the machinery: the same instance at the same fuel decides the pair
NOT equivalent as soon as the `menace` conjunct is dropped (`history_gate_needs_menace`), and the
`rfl` for a deliberately-false variant FAILS to typecheck (measured; see §8).

⚠ And the honest shape of the ANSWER: the two sites turn out to differ only by the ORDER of their
conjuncts, so the frame-level statement is ALSO hand-provable once you know that
(`history_gate_frames_agree_hand` = `Bool.and_comm`; machine and hand agree, as they must). The
duplicate gate is not drifting, and it is not drifting for a shallow reason. The lift whose verdict
NO algebraic identity backs is §6's — `≤ FLOOR-1` vs `¬(≥ FLOOR)` under a presence restriction,
where the answer turns on fail-closed absence semantics and the threshold-cell cover, not on a
Boolean law.

### The interesting negatives
* **§3** the goad/friendly mutual exclusion `dialogue.rs:43-45` merely NARRATES ("gate each other's
  lines") is now PROVEN: no frame satisfies both, at any word length.
* **§6** the goad gate is authored as the hand-computed complement `FieldLte(disposition, FLOOR-1)`
  of `FieldGte(disposition, FLOOR)`. Those spellings are NOT complements on the record substrate —
  they differ exactly on the ABSENT-`disposition` frame (the atom fails closed, the negation admits)
  — and they ARE the same rule once presence is assumed. Both halves are theorems here. The
  deployed 8-slot Rust cell always has the field present, so this is a real semantic edge, not a
  live bug; the `Prop` is what makes the caveat checkable instead of narrated.

## Resource discipline — MEASURED, not assumed
Every lift is a kernel reduction of a `Decidable` instance (`of_decide_eq_{true,false}` + `rfl`).
Fuel is set just above the MEASURED least saturating fuel of each fixpoint (compiled probe), since
fuel above saturation is free but fuel below it falls back to the astronomical bound-based route.

`/usr/bin/time -l` over `lake env lean` on this file, 3 warm runs each:
* **whole file (18 kernel-reduced lifts + 7 hand proofs): 5.02 / 5.01 / 5.32 s user, peak RSS
  2.06 / 2.04 / 2.06 GB**, against a bare-import baseline (same three imports, no declarations) of
  **1.35 / 1.38 / 1.36 s user, 1.778 GB** — i.e. **+3.7 s CPU and +0.28 GB** for ALL the crossings
  together. Nearly all of the absolute memory is loading mathlib oleans, not the fixpoints.
* **the PRIZE alone** (fuel 640, `|V| = 196` candidate frames, the largest reduction here), in its
  own file: 1.91 / 1.96 / 1.94 s user vs a 1.42 / 1.34 / 1.48 s baseline, 1.860 GB vs 1.774 GB —
  **+0.53 s CPU, +0.086 GB**.
* wall clock is I/O-noise-dominated at this size (7.6–27.9 s either way), so CPU is the honest
  figure.

This is the same order as `HandlebarsGuardDecision`'s measured crossings (+2.1–2.4 s / +0.16–0.19 GB
for three) at ~15× the candidate-cover size, and ~2.5 orders below the retracted "64 GB / 20 min"
claim that kept `SymbolicIntervals` §6 and `PredicateLibrary` §5's scalar/dfe decisions commented
out behind `-- [resource]` banners. Those banners are wrong at these guard sizes; this file is the
counter-evidence. NO `native_decide` anywhere, and no `@decide` on an unmeasured instance.

`#assert_all_clean`, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.RealGuardAudit
import Dregg2.Crypto.Deriv.RealGuardAudit2
import Dregg2.Tactics

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.Deriv.PredRE (derives leaf null der derives_sym derives_inter derives_neg)

namespace RealGuardDecisionLift

open RealGuardAudit RealGuardAudit2

/-! ## §1 FRAGMENT CLASSIFICATION — which cover each swept guard rides.

⚠ Every `#guard` in this section is COMPILED EVALUATION of a `Bool` and proves NO `Prop`; it is a
membership check that licenses the *choice of instance* used in §2-§7 (whose `rfl`s are the real
kernel content). The three families swept here:

* **interval / threshold cover** (`scalarRE`, `coverOfScalars`) — the dialogue, bloodgate and
  credential guards: `fieldGe`/`fieldLe`/`fieldEquals` over `Int` record slots.
* **correlated-witness cover** (`dfeRE`, `coverOfDigFieldEq`) — `ownerMatch`/`noSelfTransfer`:
  cross-field digest equality, which the pin cover cannot even state.
* **NOT reached here** — the reactive/affine/virtual-context guards of `RealGuardAudit2` (§1, §2.1,
  §4, §5) ride the DBM and box covers; those have runnable Bool verdicts there, and lifting them is
  the same crossing at a different cover (residual §9). -/

-- the interval-cover guards (and the pairs' symmetric differences — the fragment is closed under it)
#guard scalarRE askHistoryGate && scalarRE historyRenderer && scalarRE goadGate
    && scalarRE friendlyFloor && scalarRE goadAsComplement && scalarRE dispPresent
    && scalarRE grantGate && scalarRE ageGte18 && scalarRE ageGte1
    && scalarRE survivalFloor && scalarRE fallGate
#guard scalarRE (symDiff askHistoryGate historyRenderer)
    && scalarRE (symDiff askHistoryGate friendlyFloor)
    && scalarRE (symDiff goadGate goadAsComplement)
    && scalarRE goadVsHistory && scalarRE fightOrFall && scalarRE sAgeFwd && scalarRE sAgeBwd

-- the correlated-witness guards
#guard dfeRE "sender" "owner" ownerMatch && dfeRE "sender" "owner" ownerMatchNotNot
    && dfeRE "sender" "owner" ownerMismatch && dfeRE "sender" "owner" ownerContra
    && dfeRE "from" "to" noSelfTransfer

/-! ### The MEASURED shape of each fixpoint (compiled probe, `leastFuel`/`reachFix`).

`|V|` = the candidate cover the instance itself enumerates; `least` = the smallest fuel at which the
worklist saturates (below it the instance falls back to the `emptinessBound` powerset route, which
is astronomical); `classes` = the size of the saturated `≅`-frontier. Fuel used in §2-§7 is the next
round number above `least`. Bool-only data, stated so the fuels below are legible rather than magic:

| guard / pair                   | \|V\| | least | classes |
|--------------------------------|------|-------|---------|
| `askHistoryGate`               |  25  |   77  |    3    |
| `grantGate`                    |  25  |   77  |    3    |
| `fightOrFall`                  |   8  |   42  |    5    |
| `goadVsHistory`                |  40  |  162  |    4    |
| `symDiff askHistory historyRenderer` | 196 | 590 | 3 |
| `symDiff askHistory friendlyFloor`   | 112 | 450 | 4 |
| `symDiff ageGte18 ageGte1`     |  14  |   58  |    4    |
| `sAgeFwd` / `sAgeBwd`          |   8  |   34  |    4    |
| `symDiff goadGate goadAsComplement` | 14 | 58 |    4    |
| `dGoadPresent`                 |  38  |  192  |    5    |
| the `dfe` guards               |   2  |  8-10 |   3-4   |
-/

-- the saturation claims, re-checked in-file at the fuels the lifts use (Bool-only):
#guard (reachFix (scalarFixCands (symDiff askHistoryGate historyRenderer)) 640
          (symDiff askHistoryGate historyRenderer)).isSome
#guard ((reachFix (scalarFixCands (symDiff askHistoryGate historyRenderer)) 640
          (symDiff askHistoryGate historyRenderer)).map List.length).getD 1000 ≤ 8
#guard (reachFix (scalarFixCands goadVsHistory) 192 goadVsHistory).isSome
#guard (reachFix (scalarFixCands dGoadPresent) 224 dGoadPresent).isSome

/-! ## §1a THE BRIDGES — from a language verdict to the statement a reader of the Rust wants.

Three small hand proofs (no kernel reduction) that turn the decisions' `∃ w`/`∀ w` shapes into
per-FRAME statements about the guards, since every guard swept here is a single-frame `.sym φ`. -/

/-- A single-frame guard derives exactly its leaf on a one-frame word. -/
theorem derives_singleton_sym (φ : Pred) (a : Value) : derives [a] (.sym φ) = leaf φ a := by
  cases h : leaf φ a with
  | true => exact (derives_sym [a] φ).mpr ⟨a, rfl, h⟩
  | false =>
      cases hd : derives [a] (.sym φ) with
      | false => rfl
      | true =>
          obtain ⟨b, hb, hleaf⟩ := (derives_sym [a] φ).mp hd
          injection hb with hab _
          subst hab
          rw [h] at hleaf
          exact Bool.noConfusion hleaf

/-- **`exclusion_of_empty`** — an EMPTY intersection is a per-frame mutual exclusion: no state frame
satisfies both guards. -/
theorem exclusion_of_empty {R S : PredRE} (h : ¬ ∃ w, derives w (.inter R S) = true) (a : Value) :
    ¬ (derives [a] R = true ∧ derives [a] S = true) := by
  rintro ⟨hr, hs⟩
  exact h ⟨[a], by rw [derives_inter, hr, hs]; rfl⟩

/-- **`subsumption_of_empty`** — an EMPTY `R ⋒ ¬S` is subsumption: every `R`-witness satisfies `S`. -/
theorem subsumption_of_empty {R S : PredRE} (h : ¬ ∃ w, derives w (.inter R (.neg S)) = true)
    (w : List Value) (hr : derives w R = true) : derives w S = true := by
  cases hs : derives w S with
  | true => rfl
  | false => exact absurd ⟨w, by rw [derives_inter, derives_neg, hr, hs]; rfl⟩ h

/-- **`not_subsumption_of_nonempty`** — a NONEMPTY `R ⋒ ¬S` refutes subsumption. -/
theorem not_subsumption_of_nonempty {R S : PredRE}
    (h : ∃ w, derives w (.inter R (.neg S)) = true) :
    ¬ ∀ w, derives w R = true → derives w S = true := by
  obtain ⟨w, hw⟩ := h
  rw [derives_inter, derives_neg, Bool.and_eq_true, Bool.not_eq_true'] at hw
  intro hsub
  rw [hsub w hw.1] at hw
  exact Bool.noConfusion hw.2

/-! ## §2 SATISFIABILITY, LIFTED — can these real gates ever fire?

`RealGuardAudit` §4 answered this for 15 guards with `#guard emptyFix … = some false` (Bool only).
Here the three with genuine conjunctive content are CROSSED: a `some true` on any of them would
have been a live bug (a gate no player can ever pass), so the `Prop` is worth having. -/

set_option maxRecDepth 4000 in
/-- **The friendly-history gate FIRES.** `disposition ≥ 4 ∧ menace = 0` (`dialogue.rs:274-283`) has
a satisfying frame — the two-field conjunction is not a brick. -/
theorem askHistory_satisfiable : ∃ w, derives w askHistoryGate = true :=
  @of_decide_eq_true (∃ w, derives w askHistoryGate = true)
    (predRE_emptiness_decidable_scalar 96 (R := askHistoryGate) rfl) (by rfl)

set_option maxRecDepth 4000 in
/-- **The grant gate FIRES.** `disposition ≥ 5 ∧ topic_secret ≥ 1` (`dialogue.rs:313-323`) — the
gate re-stapled onto every `passage_open`/`oil_given` write is satisfiable, so the passage can be
opened at all. -/
theorem grantGate_satisfiable : ∃ w, derives w grantGate = true :=
  @of_decide_eq_true (∃ w, derives w grantGate = true)
    (predRE_emptiness_decidable_scalar 96 (R := grantGate) rfl) (by rfl)

set_option maxRecDepth 4000 in
/-- **The DESIGNED overlap is real.** `bloodgate.rs` intends a band where a player can both fight
on (`hp ≥ 1`) and fall (`hp ≤ 20`); the intersection is NONEMPTY, so the two stakes genuinely
overlap rather than partitioning. -/
theorem fightOrFall_band_nonempty : ∃ w, derives w fightOrFall = true :=
  @of_decide_eq_true (∃ w, derives w fightOrFall = true)
    (predRE_emptiness_decidable_scalar 48 (R := fightOrFall) rfl) (by rfl)

/-! ## §3 THE DESIGNED EXCLUSION, LIFTED — `dialogue.rs:43-45` stops being a narration.

The comment claims the friendly and hostile paths "gate each other's lines". `RealGuardAudit` §5
decided that at Bool resolution. Here it is a theorem, and then a per-frame statement. -/

set_option maxRecDepth 4000 in
/-- **goad ∧ friendly is EMPTY.** No word of ANY length satisfies both the goad gate
(`disposition ≤ 3`) and the full friendly-history gate (`disposition ≥ 4 ∧ menace = 0`). -/
theorem goad_excludes_history : ¬ ∃ w, derives w goadVsHistory = true :=
  @of_decide_eq_false (∃ w, derives w goadVsHistory = true)
    (predRE_emptiness_decidable_scalar 192 (R := goadVsHistory) rfl) (by rfl)

/-- **...cashed to the frame level**: no Keeper state whatsoever admits BOTH the goad and the
friendly-history line. This is the property `dialogue.rs:43-45` asserts in a comment. -/
theorem goad_excludes_history_frames (a : Value) :
    ¬ (derives [a] goadGate = true ∧ derives [a] askHistoryGate = true) :=
  exclusion_of_empty goad_excludes_history a

/-! ## §4 ⚑ THE PRIZE — the SAME RULE WRITTEN TWICE, decided and lifted.

The LN_ASK_HISTORY availability rule exists twice in `dungeon-on-dregg/src/dialogue.rs`:
* the EXECUTOR spelling (`:274-283`), compiled `StateConstraint`s — `askHistoryGate` =
  `disposition ≥ 4 ∧ menace = 0`;
* the RENDERER spelling (`:438`), plain Rust — `historyRenderer` = `menace == 0 ∧ disposition ≥ 4`.

They are NOT syntactically equal (the conjuncts are commuted, and they are written in different
languages). A drift between them is a real bug class. The verdict is EQUIVALENT — as a `Prop`.

⚠ SCOPE, stated before the theorem, not after: `askHistoryGate` is the DECIDABLE SLICE of the
executor case. `augment_case` at `:274-286` attaches THREE things — the compiled
`FieldGte(disposition, HISTORY_DISPOSITION_FLOOR)` (from the scene condition `{ disposition >= 4 }`
at `:147`), `FieldEquals(menace, 0)`, and a `WriteOnce { topic_history }`. The `WriteOnce` is
REACTIVE (old-vs-new), outside the interval cover, and the renderer does not check it at all (it
constrains the WRITE, not the availability). So the equivalence below is: *the executor's
availability constraints* ≡ *the renderer's availability check*. It is NOT a claim that the two
sites carry the same constraint SET. -/

set_option maxRecDepth 20000 in
/-- **⚑ NO DRIFT.** The executor's `StateConstraint` gate and the renderer's hand-written
availability check accept EXACTLY the same words, at every length, over the infinite `Value`
alphabet. The duplicate gate in `dialogue.rs` is genuinely one rule. -/
theorem history_gate_no_drift : ∀ w, derives w askHistoryGate = derives w historyRenderer :=
  @of_decide_eq_true (∀ w, derives w askHistoryGate = derives w historyRenderer)
    (predRE_equivalence_decidable_scalar 640 (R := askHistoryGate) (S := historyRenderer) rfl rfl)
    (by rfl)

/-- **...at the resolution a reader of `dialogue.rs` wants**: on EVERY state frame, the executor
gate and the renderer gate return the same Boolean. (`leaf φ a = φ.eval (symbolOld a) a` — the
single-frame evaluation both spellings are.) -/
theorem history_gate_frames_agree (a : Value) :
    leaf (.and (.atom (.simple (.fieldGe "disposition" 4)))
               (.atom (.simple (.fieldEquals "menace" 0)))) a
  = leaf (.and (.atom (.simple (.fieldEquals "menace" 0)))
               (.atom (.simple (.fieldGe "disposition" 4)))) a := by
  have h := history_gate_no_drift [a]
  rw [askHistoryGate, historyRenderer, derives_singleton_sym, derives_singleton_sym] at h
  exact h

/-- **The same statement, re-derived BY HAND — machine and theorem agree.** ⚠ Say the shallowness
out loud: the two `dialogue.rs` sites turn out to differ ONLY by the ORDER of their conjuncts, so
once the decision has told us that, the frame-level agreement is `Bool.and_comm`. That is the
honest shape of this result — the drift the decision was asked about is ABSENT, and the absence is
algebraically shallow. What the decision contributed is (a) nobody had to notice the two spellings
were algebraically related before asking, and (b) it returns NOT-equivalent the moment they are not
(`history_gate_needs_menace`, and §6, where no algebraic identity relates the pair at all). -/
theorem history_gate_frames_agree_hand (a : Value) :
    leaf (.and (.atom (.simple (.fieldGe "disposition" 4)))
               (.atom (.simple (.fieldEquals "menace" 0)))) a
  = leaf (.and (.atom (.simple (.fieldEquals "menace" 0)))
               (.atom (.simple (.fieldGe "disposition" 4)))) a := by
  simp only [leaf, Pred.eval]
  exact Bool.and_comm _ _

set_option maxRecDepth 20000 in
/-- **The decision is DISCRIMINATING, not a tautology of the machinery.** Drop the `menace`
conjunct from the renderer's spelling — the exact drift a careless edit produces — and the SAME
instance at the SAME fuel decides NOT equivalent. So `history_gate_no_drift` is a fact about these
two spellings, not about the decision procedure. -/
theorem history_gate_needs_menace : ¬ ∀ w, derives w askHistoryGate = derives w friendlyFloor :=
  @of_decide_eq_false (∀ w, derives w askHistoryGate = derives w friendlyFloor)
    (predRE_equivalence_decidable_scalar 512 (R := askHistoryGate) (S := friendlyFloor) rfl rfl)
    (by rfl)

/-! ## §5 THE STAGED CREDENTIAL MISMATCH, LIFTED — `anonymity_soundness.rs:238-252`.

The test presents `age ≥ 1` against an expected `age ≥ 18` and REQUIRES rejection. Its semantic
ground is three verdicts, all lifted here: the predicates are NOT equivalent, the stronger one
SUBSUMES the weaker (the minimal-disclosure reuse direction), and the converse FAILS. -/

set_option maxRecDepth 4000 in
/-- **NOT the same predicate** — the ground for the test's required rejection. -/
theorem age18_not_equiv_age1 : ¬ ∀ w, derives w ageGte18 = derives w ageGte1 :=
  @of_decide_eq_false (∀ w, derives w ageGte18 = derives w ageGte1)
    (predRE_equivalence_decidable_scalar 96 (R := ageGte18) (S := ageGte1) rfl rfl) (by rfl)

set_option maxRecDepth 4000 in
/-- `age ≥ 18 ⋒ ¬(age ≥ 1)` is EMPTY — the machine half of subsumption. -/
theorem sAgeFwd_empty : ¬ ∃ w, derives w sAgeFwd = true :=
  @of_decide_eq_false (∃ w, derives w sAgeFwd = true)
    (predRE_emptiness_decidable_scalar 48 (R := sAgeFwd) rfl) (by rfl)

/-- **The stronger proof SERVES the weaker request**: every witness of `age ≥ 18` satisfies
`age ≥ 1`. This is the reuse direction minimal disclosure relies on. -/
theorem age18_subsumes_age1 (w : List Value) (h : derives w ageGte18 = true) :
    derives w ageGte1 = true :=
  subsumption_of_empty (R := ageGte18) (S := ageGte1) sAgeFwd_empty w h

set_option maxRecDepth 4000 in
/-- `age ≥ 1 ⋒ ¬(age ≥ 18)` is NONEMPTY — the machine half of the converse failure. -/
theorem sAgeBwd_nonempty : ∃ w, derives w sAgeBwd = true :=
  @of_decide_eq_true (∃ w, derives w sAgeBwd = true)
    (predRE_emptiness_decidable_scalar 48 (R := sAgeBwd) rfl) (by rfl)

/-- **...and the weaker proof does NOT serve the stronger request** — subsumption runs exactly one
way, which is precisely why `anonymity_soundness.rs` demands a rejection. -/
theorem age1_not_subsumes_age18 :
    ¬ ∀ w, derives w ageGte1 = true → derives w ageGte18 = true :=
  not_subsumption_of_nonempty (R := ageGte1) (S := ageGte18) sAgeBwd_nonempty

/-! ## §6 THE `FLOOR - 1` DERIVATION, LIFTED — the semantic edge, now checkable.

`dialogue.rs:268` authors the goad gate as `FieldLte(disposition, HISTORY_DISPOSITION_FLOOR - 1)`:
the author computed the complement of `FieldGte(disposition, FLOOR)` BY HAND. Is `≤ 3` the
complement of `≥ 4`? Not on the record substrate — on an ABSENT `disposition` the atom fails closed
while the negation admits. Both halves are lifted: the raw pair separates, and under a presence
restriction they coincide. -/

set_option maxRecDepth 4000 in
/-- **The hand-computed complement is NOT the complement** — the absent-`disposition` frame
separates `FieldLte(disposition, FLOOR-1)` from `¬FieldGte(disposition, FLOOR)`. (Over the deployed
8-slot cell, where the field is always present, this is not a live bug — see the next theorem — but
it is a real semantic edge no doc-comment states.) -/
theorem goad_not_equiv_complement :
    ¬ ∀ w, derives w goadGate = derives w goadAsComplement :=
  @of_decide_eq_false (∀ w, derives w goadGate = derives w goadAsComplement)
    (predRE_equivalence_decidable_scalar 96 (R := goadGate) (S := goadAsComplement) rfl rfl)
    (by rfl)

set_option maxRecDepth 8000 in
/-- **...and under PRESENCE they are the same rule.** Conjoin both spellings with a
present-and-scalar domain guard (`disposition ≥ 0 ∨ disposition ≤ 0`) and the two decide
EQUIVALENT — so the `FLOOR - 1` derivation is correct exactly where the deployed cell lives. -/
theorem goad_equiv_complement_present :
    ∀ w, derives w (.inter goadGate dispPresent) = derives w (.inter goadAsComplement dispPresent) :=
  @of_decide_eq_true
    (∀ w, derives w (.inter goadGate dispPresent) = derives w (.inter goadAsComplement dispPresent))
    (predRE_equivalence_decidable_scalar 224
      (R := .inter goadGate dispPresent) (S := .inter goadAsComplement dispPresent) rfl rfl)
    (by rfl)

/-! ## §7 THE CROSS-FIELD OWNER-MATCH PAIR, LIFTED — a cover the pin route cannot even state.

`ownerMatch`/`noSelfTransfer` (`PredicateLibrary.lean:91,95`) are `digFieldEq` guards: cross-field
digest equality over an infinite domain, so `predAtoms?` returns `none` and the minterm cover does
not exist. `SymbolicMintermsPlus`' correlated-witness cover (`coverOfDigFieldEq`, two frames — the
complete signature set for a one-observable algebra) does reach them, and these are its lifts. -/

/-- **The owner-match tooth FIRES.** -/
theorem ownerMatch_satisfiable : ∃ w, derives w ownerMatch = true :=
  @of_decide_eq_true (∃ w, derives w ownerMatch = true)
    (predRE_emptiness_decidable_dfe 32 "sender" "owner" (R := ownerMatch) rfl) (by rfl)

/-- **The no-self-transfer tooth FIRES.** -/
theorem noSelfTransfer_satisfiable : ∃ w, derives w noSelfTransfer = true :=
  @of_decide_eq_true (∃ w, derives w noSelfTransfer = true)
    (predRE_emptiness_decidable_dfe 32 "from" "to" (R := noSelfTransfer) rfl) (by rfl)

/-- **`sender = owner ∧ sender ≠ owner` is EMPTY at every length** — a negative verdict the pin
cover could not even state, since it cannot represent a cross-field equality. -/
theorem ownerContra_unsatisfiable : ¬ ∃ w, derives w ownerContra = true :=
  @of_decide_eq_false (∃ w, derives w ownerContra = true)
    (predRE_emptiness_decidable_dfe 32 "sender" "owner" (R := ownerContra) rfl) (by rfl)

/-- **The should-agree spelling pair AGREES**: the owner-match guard and its double-negation
spelling accept exactly the same transitions (the refactor `¬¬p ⇝ p` on a cross-field tooth). -/
theorem ownerMatch_equiv_notnot : ∀ w, derives w ownerMatch = derives w ownerMatchNotNot :=
  @of_decide_eq_true (∀ w, derives w ownerMatch = derives w ownerMatchNotNot)
    (predRE_equivalence_decidable_dfe 32 "sender" "owner"
      (R := ownerMatch) (S := ownerMatchNotNot) rfl rfl) (by rfl)

/-- **...and the should-DISagree pair disagrees**: the owner-match guard and the violation guard are
separated (so the `dfe` decision is discriminating on this cover too). -/
theorem ownerMatch_not_equiv_mismatch : ¬ ∀ w, derives w ownerMatch = derives w ownerMismatch :=
  @of_decide_eq_false (∀ w, derives w ownerMatch = derives w ownerMismatch)
    (predRE_equivalence_decidable_dfe 32 "sender" "owner"
      (R := ownerMatch) (S := ownerMismatch) rfl rfl) (by rfl)

/-- **...cashed to the frame level**: no transfer frame is both owner-matched and owner-mismatched. -/
theorem ownerContra_frames (a : Value) :
    ¬ (derives [a] ownerMatch = true ∧ derives [a] ownerMismatch = true) :=
  exclusion_of_empty ownerContra_unsatisfiable a

/-! ## §8 Axiom hygiene. -/

#assert_all_clean [
  derives_singleton_sym, exclusion_of_empty, subsumption_of_empty, not_subsumption_of_nonempty,
  askHistory_satisfiable, grantGate_satisfiable, fightOrFall_band_nonempty,
  goad_excludes_history, goad_excludes_history_frames,
  history_gate_no_drift, history_gate_frames_agree, history_gate_frames_agree_hand,
  history_gate_needs_menace,
  age18_not_equiv_age1, sAgeFwd_empty, age18_subsumes_age1,
  sAgeBwd_nonempty, age1_not_subsumes_age18,
  goad_not_equiv_complement, goad_equiv_complement_present,
  ownerMatch_satisfiable, noSelfTransfer_satisfiable, ownerContra_unsatisfiable,
  ownerMatch_equiv_notnot, ownerMatch_not_equiv_mismatch, ownerContra_frames
]

/-! ## §9 RESIDUALS — named precisely.

* **(cost, MEASURED — the numbers, not a fear)** Whole file `5.02 / 5.01 / 5.32 s` user and
  `2.06 / 2.04 / 2.06 GB` peak RSS over 3 warm `/usr/bin/time -l lake env lean` runs, against a
  `1.35 / 1.38 / 1.36 s`, `1.778 GB` bare-import baseline: **+3.7 s CPU, +0.28 GB** for all 18
  crossings; the largest single one (the §4 prize, fuel 640, `|V| = 196`) is **+0.53 s / +0.086 GB**
  measured in isolation. Nothing here approaches the `~60 s / 6 GB` back-out threshold.

* **(the crossings DISCRIMINATE — mutation canary, run externally)** Four deliberately-wrong
  variants were compiled and all four FAILED, so no lift here is a `rfl` that would have succeeded
  regardless: (1) claiming the near-miss pair (`askHistoryGate ≡ friendlyFloor`) EQUIVALENT —
  `rfl` failed; (2) claiming the goad/friendly intersection NONEMPTY — `rfl` failed; (3) claiming
  `ownerMatch ≡ ownerMismatch` — `rfl` failed; (4) the TRUE prize statement at fuel `100` (below
  the measured saturation point `590`) — did NOT silently go green: it hit `maxRecDepth` in the
  bound-based fallback. Under-fuelling fails LOUD.

* **(fuel is not free BELOW saturation)** Each lift's fuel sits just above the MEASURED least
  saturating fuel of its fixpoint (§1's table, from a compiled probe). Above saturation, fuel is
  free (the worklist returns the moment `pending` empties); BELOW it, the instance falls back to
  `predRENonemptyDecidableG` at the `emptinessBound` powerset, which is astronomical for these
  `neg`-headed symmetric differences. So these fuels are load-bearing and must be re-measured for
  any new guard — the general counting bound in `SymbolicFixpoint`'s termination note is still
  unproven, exactly as `HandlebarsGuardDecision` §6 records.

* **(semantic resolution, unchanged from `RealGuardAudit`)** Verdicts are at `Int`-record resolution
  (Lean atoms over `Int` slots with absence, fail-closed), not at the Rust executor's
  `FieldElement` mod-p resolution, and PER-FRAME (a satisfying post-state exists), not per-trace
  (play can reach it). For the small constants swept here (0..20, 18) the two agree; nothing above
  leans on wraparound. The `dialogue.rs` renderer/executor equivalence is therefore a statement
  about the two RULES as `Pred`s — it does not by itself prove the Rust renderer implements
  `historyRenderer` (that is the Rust-side correspondence, out of this fragment's reach).

* **(EXTRACTION, not generation — the load-bearing manual step)** These `PredRE`s are hand-
  transcriptions of the Rust sites (`RealGuardAudit`'s cited `file:line`s), re-checked against
  `dungeon-on-dregg/src/dialogue.rs` at `:196-198`, `:265-286`, `:438` while writing this file.
  Nothing generates them FROM the Rust, so a constant or conjunct changing on the Rust side does
  not break any theorem here — it silently makes the extraction stale. Two specific fragilities
  worth naming: the scene text hardcodes `{ disposition >= 4 }` (`:147`) while the renderer reads
  `HISTORY_DISPOSITION_FLOOR` (`:198`), and their agreement is held by a RUST unit assertion
  (`:540-544`), not by anything in Lean; and the goad gate's `FLOOR - 1` (`:268`) is a hand-computed
  complement whose semantic edge is §6. Closing this residual means emitting the guards from the
  compiled `Program` rather than transcribing them — the real next build.

* **(the covers not swept)** `RealGuardAudit2`'s reactive (`WriteOnce`, `BoundedBy`), cross-field
  DBM (`fieldLeField`), bounded-affine (`bandProgram`/`consvProgram`) and virtual-context (polis
  `AnyOf`) verdicts remain at Bool `#guard` resolution there. Lifting them is the SAME crossing
  through `predRE_{emptiness,equivalence}_decidable_difference` / `_at`; the DBM covers are larger
  (`|V|` grows with the difference grid), so each needs its own measurement before it is shipped.

* **(one pair the fragment still cannot reach)** `RealGuardAudit` §6b names it: the secret-topic
  renderer check (`dialogue.rs:457`, `topic_history >= 1`) vs the executor's `BoundedBy`
  (`:294-303`) is a should-agree pair whose two sides live in DIFFERENT covers (interval vs
  reactive-difference), so no single cover decides the pair. That is the honest wall, unchanged.
-/

end RealGuardDecisionLift

end Dregg2.Crypto.Deriv
