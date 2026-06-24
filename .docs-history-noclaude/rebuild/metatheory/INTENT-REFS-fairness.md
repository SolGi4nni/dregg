# INTENT-REFS — Liveness, Justness & Fairness (van Glabbeek)

**Pillar:** the right **completeness criterion** for liveness in dregg2's reactive turn-system — the answer to
Track-D's gated question *"what liveness assumption, and how to ground `Enabled`/`Effective`?"*
**Companion to:** `PHASE-2-INTENT-SPEC.md` — the Track-D (liveness/fairness) scope-spec.
**Status:** the **decision record** + reference map for Track D (liveness/fairness) and the deferred liveness
reading of Track B (CTL `AF`/`EG`). Produced by the `study-vanglabbeek-fairness` workflow (2026-06-04):
hunt (9 papers pulled) → deep-read → dregg mapping (grounded in the real executor code).

**The decision (ember's colleague Rob van Glabbeek's theory):** adopt **JUSTNESS**, not weak/strong fairness,
as Track-D's base completeness criterion. The rest of this doc is why, the precise machinery, and the
buildable theorem.

**Anchor papers (all in `pdfs/`):**
- van Glabbeek & Höfner, *Progress, Justness and Fairness* (ACM Comput. Surv. 2019), arXiv [1810.07414](https://arxiv.org/abs/1810.07414) `[vanGlabbeek-Hoefner-progress-justness-fairness-survey-1810.07414.pdf]` — **the taxonomy**.
- van Glabbeek, *Justness: A Completeness Criterion for Capturing Liveness Properties of Reactive Systems* (FoSSaCS'19), arXiv [1909.00286](https://arxiv.org/abs/1909.00286) `[…justness-completeness-criterion-1909.00286.pdf]` — **Def 1–7, the directly-portable LTSC + B-just predicate**.
- van Glabbeek & Höfner, *CCS: It's not Fair!* (Acta Inf.), arXiv [1505.05964](https://arxiv.org/abs/1505.05964) `[…CCS-its-not-fair-1505.05964.pdf]` — **fairness is unimplementable in CCS-like languages**.
- van Glabbeek, *Reactive Temporal Logic* (EPTCS 2020) `[vanGlabbeek-reactive-temporal-logic.pdf]` — the reactive modal operators.
- + *Ensuring Liveness of Distributed Systems* (research agenda), *Progress/Fairness/Justness in Process Algebra* (2015), *Just Enough Fairness for Session Types / Lock-freedom* (2021), *Mutual Exclusion with Time-outs* (2021), *Coarsest Precongruences Respecting Safety & Liveness* (2010). Cite-only: *Just Verification of Mutual Exclusion* (2025), *Just Testing* (FoSSaCS'23).

---

## 0. The frame: a completeness criterion, not an "assumption"

van Glabbeek's reframing ([Just] §1, Def 1): a transition system alone does not say which maximal paths are
*actual* runs. A **completeness criterion** is a *predicate on paths* selecting the runs that can really occur.
Progress, justness, weak/strong/full fairness are completeness criteria ordered by **strength** (F stronger
than H iff F rules out at least all paths H does). A liveness property `𝒢` *holds under C* iff every
C-complete path satisfies `𝒢`. **The danger:** an over-strong criterion (fairness) disqualifies paths that
*can* actually occur, so it certifies liveness properties that are operationally **false** ([Survey] §13;
[Just] §4 — "Bart never gets his beer", "Alice never picks up the phone").

---

## 1. The hierarchy (exact, with the implication chain)

The model: an LTS `(S, Tr, source, target, I, ℓ)`; a path is `s₀ t₁ s₁ …`. **Order:** `P ≤ J ≤ Wy ≤ Sy ≤ Fu`.

- **Progress (P)** — the floor ([Survey] §3, Def 3.1): a path is progressing iff infinite or stuck (last
  state has no outgoing transition). "Never idle while a transition is enabled." Built into LTL/CTL by
  quantifying over infinite paths. **Cannot** rule out forever running one component while another,
  perpetually-enabled, never moves. Per-system, not per-component.
- **Justness (J)** — *the recommendation* ([Survey] §13 / Def 16.2; [Just] Def 6): equip the system with a
  **concurrency relation** `↝ ⊆ Tr × Tr`; write `t ⌣̸ u` ("u interferes with t") for `¬(t ↝ u)`. A path is
  **just** iff every enabled non-blocking transition `t` is eventually followed by some `u` with `t ⌣̸ u`
  — *a ready component cannot be starved forever while only non-interfering activity proceeds*. **J implies
  P.** Crucially **justness is a strong form of PROGRESS, not a fairness property** ([Just] §4: "we cannot
  cast justness as a fairness property" — it asserts a condition holds *once*, not perpetually/infinitely-often).
- **Weak fairness (Wy / justice)** ([Survey] Def 4.1): with a set `𝒯` of *tasks*, every **continuously-enabled**
  task occurs infinitely often. Strictly stronger than justness (`J ≤ Wy`); over-commits.
- **Strong fairness (Sy / compassion)**: every **relentlessly-enabled** (infinitely-often) task occurs
  infinitely often. `Wy ≤ Sy`.
- **Full fairness (Fu)** = the AGEF property (a goal state reachable from every reachable state); = KFAR in
  process algebra. Too strong; only definable as AGEF. Not relevant to Track D.

Two orthogonal axes: **conditional vs unconditional** (verification uses conditional — "holds *as long as*
fair"; unconditional/impartiality is rejected as infeasible, [Survey] §18); **local vs global** task-extraction
(actions/transitions/components/groups…, [Survey] §5). Justness coincides with *fairness of events* (`J ≡ JZ
= JE`, [Survey] Thm 15.1).

---

## 2. Why justness, not fairness (four decisive arguments)

1. **Fairness yields FALSE liveness guarantees; justness is warranted by default** ([Survey] §13; [Just] §4).
   A peer that may legitimately never act (a non-responsive counterparty) makes any fairness-derived liveness
   operationally false. "Fairness assumptions are by default unwarranted… justness by default *is* warranted."
2. **Fair schedulers CANNOT be implemented in CCS-like reactive languages** (*CCS: It's not Fair!*). dregg2's
   executor IS such a language (interleaved reactive cell-turns synchronising on effects). You cannot assume a
   property your runtime provably cannot realise. Justness *is* feasible ([Just] Thm 1: every finite run
   extends to a just run, given countable per-state branching — trivially met, the forest is finitely
   branching).
3. **Justness is the unique non-trivial "typically warranted" criterion** ([Survey] §17 evaluation table):
   only P, J (and JT / strong-weak) score "+"; all of WA…SG score "−". Justness is feasible + liveness-enhancing
   + warranted simultaneously.
4. **Justness is refinement- and equivalence-stable; weak fairness is not** ([Survey] §14, §6.2). dregg2 is
   verified at the Lean-spec level and *refined/compiled to Rust* (THE SWAP). A criterion that breaks under
   action refinement silently invalidates the proof after the swap. Justness rides the concurrency relation,
   inherited by refinement.

---

## 3. The portable machinery ([Just] Def 5–6)

**LTSC** (LTS-with-concurrency) = `(S, Tr, source, target, ℓ, ↝)` with `↝ ⊆ Tr• × Tr` satisfying:
- **(1) irreflexivity on non-blocking:** `t ⌣̸ t` (firing `t` consumes that occurrence);
- **(2) closure:** if nothing on a path from `source(t)` interfered with `t`, then `t` (a same-label variant)
  is still enabled at the end — *enabledness is lost only through genuine interference*.

**`t ↝ u`** reads "u does not interfere with t" (u touches no resource t needs). **Components presentation**
([Survey] §13): derive `↝` from `npc : Tr → 𝒫(𝒞)` (necessary participant components) and `afc : Tr → 𝒫(𝒞)`
(affected components): **`t ↝ u ⟺ npc(t) ∩ afc(u) = ∅`**. Symmetric when `npc = afc` (the common case);
**asymmetric** for broadcast/signal (`npc ⊋ afc` — the traffic-light/attestation case).

**Reactive B-justness ([Just] Def 6 — the predicate):** for `Rec ⊆ B ⊆ Act` (blocking actions), a path is
**B-just** iff for every suffix and every **non-blocking** transition `t ∈ Tr•₋B` enabled at its start, some `u`
with `t ⌣̸ u` occurs in the suffix. Stated **only over non-blocking transitions** — a transition the
*environment* can refuse is NOT a justness obligation. **Feasibility** ([Just] Thm 1): finitely-branching ⇒
justness is never vacuously unsatisfiable.

---

## 4. The dregg2 mapping — the answer to the gated question

**The load-bearing code fact** (`Exec/CellReal.lean`): `cellNextA s cf = (execFullForestA s cf.1).getD s` —
on a rejected turn it **fail-closes to a STUTTER self-loop** (`Step s s` always available). That is exactly why
`Temporal.Eventually` is only trivially provable and why `Proof/CTL.lean` ships only the safety fragment
(`AF committed` would demand the goal on the eternal stutter branch). **The stutter is van Glabbeek's
non-progressing / blocking transition; justness excludes it.**

**The decision + grounding (answers Q-D1):**
- **Base criterion = reactive B-justness** ([Just] Def 6 over `trajA`). Weak/strong fairness only as opt-in,
  per-cell, *local* strengthenings ([Survey] §5 TLA⁺-style) for specific cells that need them — never the floor.
- **`Enabled` / `Effective` grounded on the commit/stutter discriminant** — NOT "some `cf` exists" (trivial):
  ```
  Commits s cf  := (execFullForestA s cf.1).isSome            -- "effective": the executor ACCEPTS it (not getD-stutter)
  EnabledAt s c := ∃ cf, NonBlocking cf ∧ Commits s cf ∧ c ∈ npcA cf
  ```
  `isSome` is the right grounding *because it is exactly what separates a commit from the fail-closed
  self-loop*. (ember's Q-D1 answer: **yes, `Enabled` = commit-success `isSome`** — refined to non-blocking +
  the npc-membership the concurrency relation needs.)
- **Concurrency relation from `npcA`/`afcA` over CELLS as components.** `npcA cf` = root actor ∪
  `targetOf` over the lowered forest (`targetOf : FullActionA → CellId` is **already in `Exec/FullForest.lean`**);
  `afcA cf` = cells `cf` mutates. `concurrent cf u := Disjoint (npcA cf) (afcA u)`. Symmetric for ordinary
  effects; **asymmetric for the caveat/attestation/disclosure faces** (`afcA ⊊ npcA` — the signal/synchron case,
  matching the dregg4 disclosure dial-cube).
- **blocked-by-environment vs unjustly-starved:** a non-committing turn with a **blocking** label (cross-vat
  send / `RefreshDelegation` / await) is *blocked by the environment* — no justness obligation, bounded
  operationally by `Liveness.Lease` (already in place). A turn that stays enabled (uninterfered) yet never fires
  is *unjustly starved* — the schedule justness forbids.

**The payoff theorem (new `Proof/Fairness.lean`):**
```
def Just (s) (sched) : Prop :=                    -- port of [Just] Def 6
  ∀ k, ∀ cf, NonBlocking cf → Commits (trajA s sched k) cf → ∃ n, k ≤ n ∧ interferes cf (sched n)

theorem just_progress (P) (s) (sched) (hjust : Just s sched)
    (μ : RecChainedState → Nat)                   -- well-founded measure toward P
    (henab : ∀ k, ¬ P (trajA s sched k) → ∃ cf, NonBlocking cf ∧ Commits (trajA s sched k) cf ∧
               ∀ u, interferes cf u → μ (cellNextA (trajA s sched k) u) < μ (trajA s sched k))
    (hzero : ∀ x, μ x = 0 → P x) :
    Eventually P s sched
```
The genuine `◇`, dual to the existing `□`-rule (`always_of_step_invariant`). Carry premises as **fields**
(BFTLiveness-`Pacemaker`-style), never `axiom`. The supporting lemma `commits_stable_off_npc` (port of [Just]
closure (3): enabledness lost only via interference, from per-effect locality) is the technical crux.

**Teeth (non-vacuity):** (1) `badSched := fun _ => cf5` firing only an independent cell forever **starves**
an enabled `cf0` (`concurrent cf0 cf5`) → `¬ Just fma0 badSched`, a machine-checked refutation (dregg2's
[Survey] Example 21). (2) the **loser-refund** liveness demonstrator: `μ := pendingRefunds.card`, every
interfering continuation a refund step → `just_progress` discharges `Eventually (refunded loser)`.

**This settles Track-B's `AF`/`EG` via the SAME gate:** restrict the CTL path quantifiers to **just paths**
(`AF_just P`); `livingAF_just_progress` follows from `just_progress` + the existing `livingAG_iff_temporalAlways`
/ `EF_iff_reachable` bridges. One decision, both tracks unblocked.

---

## 5. Honest flags (where the model needs care — not stubs)

- **`afcA` (affected-cell set) needs a per-effect audit** of all 46 `FullActionA` kinds (balances/caps/
  `kernel.revoked`/log/escrow side-tables). MEMORY warns side-tables are easy to undercount. Build it
  **conservatively over-approximated first** (superset ⇒ `interferes` over-fires ⇒ justness sound-but-strong),
  then tighten. Do NOT stub it.
- **`NonBlocking` (the `B` label partition)** is a modelling choice (which effects are environment-dependent).
  Principled (the `Lease`/`Live` machinery already encodes "blocking ⇒ bounded by lease, not by liveness") but
  new surface.
- **`commits_stable_off_npc`** is provable but non-trivial — a *uniform* per-effect locality lemma over
  `execFullForestA` (frame lemmas exist piecemeal: `applyHalfOut_caps`, `recKExec_frame`). Budget it as a real
  proof (the ◇-analogue of what `CellCarry.lean` did for `□`), not a `#guard`.
- **Cross-cell interference is bilateral only** so far (`SharedBinding`/`jointApply`); the N-ary `Hyperedge`
  interference awaits the executable N-ary `jointApply` (same residue as conservation, `CrossCellLTS §10`).

---

## 6. PDFs pulled this session (validated, in `pdfs/`)
`vanGlabbeek-Hoefner-progress-justness-fairness-survey-1810.07414.pdf` · `vanGlabbeek-justness-completeness-criterion-1909.00286.pdf`
· `vanGlabbeek-ensuring-liveness-distributed-systems-research-agenda.pdf` · `vanGlabbeek-reactive-temporal-logic.pdf`
· `vanGlabbeek-Hoefner-CCS-its-not-fair-1505.05964.pdf` · `vanGlabbeek-Hoefner-progress-fairness-justness-process-algebra-2015.pdf`
· `vanGlabbeek-Hoefner-Horne-just-enough-fairness-session-types-lockfreedom-2021.pdf` · `vanGlabbeek-modelling-mutual-exclusion-timeouts-2021.pdf`
· `vanGlabbeek-coarsest-precongruences-safety-liveness-2010.pdf`
