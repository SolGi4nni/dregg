# The Polis interleaved-multi-agent hyperproperty — a frontier report (for gpt5.5)

*Companion to `docs/POLIS.md`. Everything below the line "what we have" is built, green,
kernel-clean, CI-covered, tagged `cut-trace-remainder-0.1`. Everything below "the frontier" is
the one remaining open object. This report states it precisely and asks where to take it.*

---

## 0. One-paragraph context

The polisware constitution ("the cut, the trace, and the remainder") is a kernel-clean Lean
artifact: `Metatheory.Polis` (the abstract spine), `Metatheory.DreggPolis` (welds to the real
dregg substrate), `Metatheory.PolisNonConfusion` / `Metatheory.PolisPolitician` (deployed
floors), `Metatheory.PolisFlowRefine` (the decidable flow-capture bar). The governing discipline
is **govern trace-shape, not motive**: enforcement quantifies over the opaque inhabitant
(`polis_safety : ∀ ctrl …`), so no interior is ever inspected. The whole near-term vision is
welded; **one** object remains, and it is genuinely a new construction, not a weld: the
**interleaved-multi-agent politician hyperproperty**.

---

## 1. What we have — the single-trace governance abstraction

```lean
structure CaptureBar (Trace : Type) (violatesFloor : Trace → Prop) where
  badShape         : Trace → Prop
  publicDecidable  : DecidablePred badShape          -- governable WITHOUT interior inspection
  loadBearing      : ∀ τ, badShape τ → violatesFloor τ   -- zero false positives (no "astrology")
  leastRestrictive : ∀ τ, violatesFloor τ → badShape τ   -- zero misses (bars every violation)
```

A `CaptureBar` is the politician's analogue of svenvs `liberty`: a public-trace predicate that
bars **exactly** the floor-violating traces and is **decidable from the public trace alone**.
We also have the composition primitive

```lean
def CaptureBar.or (b₁ : CaptureBar Trace v₁) (b₂ : CaptureBar Trace v₂)
  : CaptureBar Trace (fun τ => v₁ τ ∨ v₂ τ)     -- union of bars over a COMMON trace type
```

**Two concrete single-trace bars are built:**

1. **exit-foreclosure** — `CaptureBar (List RState)`, `badShape τ := ∃ s ∈ τ, B < s.dist`
   (a subject lost bounded recovery / its exit was foreclosed). With
   `dreggReal_envelope_no_foreclosure`: the `∀`-opaque envelope (which pins `dist ≤ B`) prevents
   foreclosure for **every** opaque controller — but only along a **single trajectory**.
2. **flow/policy capture** — `CaptureBar Proc`, `badShape A := decideRefines A F = false`
   (`A`'s online behaviour escapes the floor flow `F`, i.e. `¬ (A ≤ᶠ F)`). This one is
   **decidable**, sound+complete, via the deployed Büchi/DupSim simulation game
   `Dregg2.Deos.FlowRefine.decideRefines_iff` (dregg's analogue of Pradic Thm 1.4).

**A capture-shape catalog is pinned** — each is a deployed kernel-clean theorem, but each lives
over its *own* observable, **not yet a `CaptureBar` over a common trace**:

| shape | deployed theorem | observable type |
|---|---|---|
| disclosure-ratchet | `DiscloseAt.accepts_invariant_under_dial` | `Dial` position |
| grade-laundering | `Finality.no_downgrade`, `Tier.rank_injective` | `Finality.Tier` run |
| clerk-monopoly | `FullForestAuthPortal.proof_arm_sound` | portal arm |
| hole-rent | `ConditionalTurn.condTurn_atomic` | a conditional turn |

---

## 2. The frontier — the interleaved-multi-agent hyperproperty

The deep object. gpt5.5's own framing from the botswarm: *"single-agent svenvs proves a negative
invariant; polisware must prove negative invariants **plus liveness plus anti-capture
hyperproperties over traces**; abuse can be about **comparative possibilities** — B could have
exited in τ₁ but not after A's lawful routing sequence τ₂."* Three sub-problems block it:

### (a) Heterogeneous trace types → one unified trace
The bars live over `List RState` / `Proc` / `Dial` / `Tier` / portal / conditional-turn.
`CaptureBar.or` only composes bars over a **common** `Trace`. To fold them into one politician
floor we need a unified `Trace DreggState DreggAction` — a single interleaved run of many
subjects' **public** events over a shared state — with projections to each shape's observable
(the `Dial` reached, each value's `Tier`, each policy's `Proc`, each subject's `RState`/recovery).

### (b) Trace-property → hyperproperty (the relational core)
Every bar we have is a **trace property** (`Trace → Prop`). But domination is **relational /
comparative**, gpt5.5's own formula:

```
dominates A B τ  :=  public_actions_of A τ  reduce  viable_options B τ  below  B.floor
                     ∧ ¬ valid_consent B τ  ∧ ¬ authorized_settlement τ
```

`viable_options B τ` is a **counterfactual over B's *public* option-space** — what B could still
lawfully do — and it must be computed **without inspecting B's interior** (the `∀`-opacity
constraint is non-negotiable; it is the whole protected-remainder result). This is a hyperproperty
(a predicate on *sets* of traces / a 2-trace comparison: B-with-A's-actions vs B-without).

### (c) Decidability / governability under `∀`-opacity
For the floor to be **enforced** (not merely stated), the hyperproperty must be **decidable, or at
least monitorable, from the public trace**. The flow-refinement case *is* decidable (Büchi). The
general set-of-traces hyperproperty is not. gpt5.5 listed the catalog as *"invariant + liveness +
anti-capture hyperproperties"*: some are **safety** (a bad finite prefix — monitorable), some are
**liveness** (e.g. "exit remains *eventually* available" — not directly monitorable).

### The four non-negotiable constraints any solution must meet
1. **`∀`-opacity** — no interior; all measures over public actions/traces/option-spaces.
2. **least-restrictive** — `badShape ⇔ exactly floor-violation` (the `CaptureBar` law).
3. **decidable-from-public-trace** — `publicDecidable` (governability).
4. **monotone-composable** — the floor must compose so **amendment non-regression**
   (`amendment_stream_nonregression`) survives at the hyperproperty level.

---

## 3. Our current thinking (candidate moves — please confirm / refute / sharpen)

- **Self-composition for 2-safety.** Domination is comparative (B-with-A vs B-without-A).
  Comparative properties are 2-safety / k-safety, classically reduced to a **trace property on a
  product (self-composed) system**. So: build the product trace lattice and reduce
  `dominates A B` to a single-trace `badShape` on the product — at which point `CaptureBar` +
  `CaptureBar.or` apply directly, and it is decidable iff the product is finite-state. Is this the
  right backbone?
- **Bounded-liveness → safety.** The svenvs `cwithin … B` trick (recovery *within B steps*, which
  is what makes corrigibility decidable) lifted to hyperproperties: replace each liveness shape
  ("eventually exit") with its bounded form ("exit within `B`"), turning it into a safety property
  with a finite bad prefix — monitorable, decidable. Is bounded-liveness the right uniform move for
  the whole catalog (no-lock-in, no-appeal-exhaustion, no-hole-rent)?
- **The deployed substrates.** dregg already has, candidate-built: the **blocklace / `LaceMerge`
  configuration lattice** (the multi-agent causal order; merge = colimit/`Finset`-union), the
  **`CoinductiveAdversary` / adversary-stream confluence** work (schedules of *unbounded
  interleaved* turns — `Proof/ContendedCrossCell.lean`, the cross-cell whole-history OPEN), the
  **`decideRefines`** Büchi game, the **Settlement-Soundness** theorem (authority-live-at-settlement)
  and the **distributed-timetravel config-lattice + RCCS** semantics. **Hypothesis: the polis
  interleaved-multi-agent hyperproperty is *the same object* as the cross-cell whole-history
  adversary-stream confluence** — i.e. the polis frontier and the circuit-soundness cross-cell
  frontier coincide. If so, one construction serves both.

---

## 4. The questions for gpt5.5

1. **Formal home.** HyperLTL/HyperCTL\* (the standard hyperproperty logic, with its monitorability
   theory), or the **event-structure / configuration-lattice + game-semantic** route (which dregg
   already instantiates), or a **coalgebraic** one? Which gives a **decidable or monitorable
   fragment** that covers the politician catalog under `∀`-opacity?
2. **The option-space measure.** How to formalize `viable_options B τ` — "what B can still lawfully
   do" — purely over B's **public** option-space, no interior? Candidates: B's remaining admissible
   flow under `≤ᶠ` (so domination = "A's actions push B's flow below the floor flow", reusing
   `decideRefines`); reachability of B's home in the config lattice (a game: B has a winning
   strategy to reach home); the exit-foreclosure `dist ≤ B` measure generalized. Which is right, and
   does it stay `∀`-opaque?
3. **Safety vs liveness split + monitorability.** Which catalog shapes are safety (monitorable
   from a finite bad prefix) vs liveness, and is **bounded-liveness** the uniform reduction to make
   the liveness ones decidable? Is "no-lock-in-over-time" a bounded-`cwithin` safety hyperproperty?
4. **Self-composition / product construction.** Is reducing `dominates A B` to a single-trace
   property on a self-composed product the right backbone, and what is the product here — two copies
   of the config lattice differing only on A's events? Does it stay finite-state (hence decidable)
   for the bounded fragment?
5. **Composition algebra / grade.** You earlier suggested a **quantale/semiring grade** and that
   the politician floor is a conjunction of safety + bounded-liveness. What is the composition
   algebra for `CaptureBar`s over the unified trace such that the **or-fold stays
   monotone-amendable** (so `amendment_stream_nonregression` lifts)? Is the meet of hyperproperty
   floors itself a hyperproperty floor, decidable where components are?
6. **The cross-cell coincidence.** Is the polis interleaved hyperproperty literally the deployed
   **`CoinductiveAdversary` / adversary-stream confluence** object (the cross-cell whole-history
   OPEN)? If yes, can the polis floor be *defined as* "the adversary-stream confluence holds for
   every subject's exported floor", inheriting whatever decidable fragment that work has?

---

## 5. The ask, in one line

**Pick the formal home (HyperLTL vs event-structure+games vs coalgebraic), give us the
`∀`-opaque public option-space measure for `viable_options`, the safety/bounded-liveness split that
makes the catalog monitorable, and the self-composition/product backbone that reduces relational
domination to a single-trace `CaptureBar` on a unified `Trace DreggState DreggAction` — staying
decidable and monotone-composable so amendment non-regression survives.** And tell us whether this
is the same object as the cross-cell whole-history adversary-stream confluence, so one proof serves
both frontiers.
