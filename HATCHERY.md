# 🥚 The Hatchery

*A verification toolkit and smart-contract-verification surface for dregg2 — where a verified cell gets its "forever" guarantees with the shell already cracked.*

---

## 0. Thesis

dregg2 has, sitting underneath it, one extraordinarily reusable theorem:

```lean
theorem livingCellA_carries
    (Good  : RecChainedState → Prop)
    (hpres : ∀ s cf, Good s → Good (cellNextA s cf))   -- prove it for ONE step
    (s : RecChainedState) (hinit : Good s) (sched : SchedA) :
    ∀ n, Good (trajA s sched n)                         -- get it for ALL time, ANY adversary
```

Every "crown" and every app we've shipped is an instance of it. The author's *entire* obligation is `hpres` — a single-step preservation — and the coalgebra hands back unbounded-time, all-schedules safety for free.

The Hatchery is the observation that **`hpres` itself is almost always mechanical**, plus the tooling to make it so. The same tooling that compresses *our* proofs is, verbatim, the **smart-contract verification product** we offer userspace: an app author declares an invariant in a structured shape, and gets a machine-checked "holds forever, against any adversary" theorem in our axiom-clean TCB — no hand proof.

> One artifact, two payoffs. It accelerates the verification work immediately in front of us, and it *is* the userspace offering.

---

## 1. The observation: our proofs are one skeleton, retyped

Look at three independently-authored results — `CellNullifier.livingCellA_no_double_spend`, `CellCommit.livingCellA_commitments_persist`, `Identity.livingCellA_revoked_grow`. Strip the names and they are **the same proof**:

```
1.  reduce  ∀ s cf, Good s → Good (cellNextA s cf)
              via cellNextA = (execFullForestA s cf.1).getD s   (commit | stay-put)
2.  reduce  the forest step to a per-action step
              via execFullForestA_eq_execFullTurnA  (the proved bridge)
3.  case-split execFullA over all ~46 FullActionA constructors
4.    45 arms: the registry field is UNTOUCHED        → `rfl` / a frame lemma
5.     1 arm: it GROWS (cons / insert / monotone)     → `List.subset_cons` etc.
6.  feed the one-step result to livingCellA_carries   → "forever"
```

Steps 1, 2, 6 are *identical every time*. Step 3 is a fixed 46-way split. Step 4 is "this effect doesn't touch my field" repeated ~45×. Only step 5 — the one growing arm — carries real content, and it's usually one lemma.

We have paid for this skeleton by hand, in full, **at least five times**. That is the tax the Hatchery abolishes — and it's exactly the tax a userspace author would otherwise pay to verify *their* contract.

---

## 2. Architecture — four tiers

Naming the Isabelle analog in brackets, because this is consciously *that* genre of tool (Eisbach `method`, Nagashima's PSL `try_hard`, Certora CVL, the Move Prover), built on Lean's own substrate.

### Tier 1 — Domain tactics  *[Eisbach / `method`]*

The boilerplate-killers. Pure metaprogramming over our executor; **zero new dependencies** (we already ship `aesop` v4.30).

```lean
-- The front-end: discharge the livingCellA_carries plumbing, leave only the genuine one-step goal.
macro "carry_forever" Good:term : tactic =>
  `(tactic| refine livingCellA_carries $Good ?step ?_ ?_ ?_ <;> intro s cf hgood)

-- The headliner: given a state projection, auto-split the executor and kill every untouched arm.
-- Leaves ONLY the arms that actually move the projection — the real proof obligations.
syntax "exec_frame" (term)? : tactic
-- elaborates to: unfold cellNextA; split (commit/stay); rw [execFullForestA_eq_execFullTurnA];
--   induction the turn list; cases (fa : FullActionA) <;>
--   first | (rfl) | (simp only [<dregg_frame simp set>]) | (skip   -- hand back the grower)

-- The §8 boundary, codified: declare an @[extern] primitive + its soundness CARRIER,
-- auto-emit the derived `_floor_sound` that takes the carrier as an EXPLICIT hypothesis
-- (never baking accept ⇒ sound into a def — the PortalFloor.lean discipline, as a command).
syntax "crypto_portal" ident "carrier" term : command
```

`exec_frame` is the keystone. It is also what makes the **sequential effect-widening safe**: when you add a new `FullActionA` arm, you supply its one kernel-op frame lemma and re-run — the tactic *reports which carried safeties the new effect preserves or breaks*. Adding an effect becomes local, mechanical, and auto-checked instead of "manually re-verify every invariant against the new arm."

### Tier 2 — A proof-strategy search  *[PSL `try_hard` — and `aesop` is already the engine]*

We do **not** reinvent search. Lean ships `aesop`, the extensible rule-set-driven engine PSL wanted. We ship a **`dregg` rule-set**:

```lean
declare_aesop_rule_sets [dregg]

@[aesop safe apply (rule_sets := [dregg])] -- the lifts
theorem execFullForestA_eq_execFullTurnA   : …
@[aesop unsafe 50% apply (rule_sets := [dregg])]
theorem List.subset_cons                   : …   -- the canonical "grower"

@[aesop simp (rule_sets := [dregg])]       -- the frame family: "effect X leaves field Y alone"
theorem recKExecAsset_revoked_eq  : …
theorem recKDelegateAtten_caps    : …
-- … every @[dregg_frame] lemma is tagged once, discovered forever
```

Then a carried-safety goal is dispatched by *trying the safety shapes in order*:

```lean
macro "dregg_auto" : tactic => `(tactic| aesop (rule_sets := [dregg, default]))
```

`@[dregg_frame]` / `@[dregg_bridge]` / `@[dregg_grow]` attributes are thin wrappers that register into the rule-set. New frame lemmas join the search automatically — the effect-widening and every later workflow inherit them.

### Tier 3 — The contract bundle  *[the userspace surface]*

What an app author actually fills in. The three apps become the regression tests proving this reproduces the hand-written crowns.

```lean
/-- A verified dregg cell-program: an invariant + the shape it inhabits.
    The one-step obligation is discharged by the Tier-1/2 tactics; everything
    temporal is derived. -/
structure CellContract where
  Inv     : RecChainedState → Prop
  shape   : SafetyShape
  step_ob : ∀ s cf, Inv s → Inv (cellNextA s cf)   -- usually `by exec_frame` / a shape tactic

namespace CellContract
/-- The payoff, free for every contract: holds at every index of the unbounded
    adversarial trajectory, under every schedule. -/
theorem forever (C : CellContract) {s} (h : C.Inv s) (sched) :
    ∀ n, C.Inv (trajA s sched n) :=
  livingCellA_carries C.Inv C.step_ob s h sched

/-- Once Proof/Temporal (and the CTL/μ layer) land, the same bundle yields modal specs. -/
theorem always (C : CellContract) {s} (h : C.Inv s) (sched) : Always C.Inv s sched :=
  C.forever h sched
end CellContract
```

### Tier 4 — The shape catalog  *[Certora CVL / Move Prover specs]*

The five safety shapes we keep re-deriving become *declarative templates*. The author names a field and a shape; a macro expands it to the right `CellContract` + invokes the right tactic. **This is the smart-contract spec language.**

```lean
monotone_registry%  revoked        -- "once revoked, forever"            (Identity)
monotone_registry%  nullifiers     -- "no double-spend, forever"         (CellNullifier)
monotone_registry%  commitments    -- "published commitment persists"    (CellCommit, NameService)
conservation%       (asset 0)      -- "supply conserved, no drift"       (CellReal)
confinement%        ceiling U      -- "authority never exceeds U"        (CellConfine)
automaton_inv%      (tail ≤ head)  -- "consumer never passes producer"   (Subscription)
eventually%         Goal           -- liveness: "Goal is reached"         (needs CTL/μ + fairness)
```

Each template knows its one-step discharge:

| Shape | Property class | One-step obligation | Discharge |
|---|---|---|---|
| `conservation%` | equality of a measure | `π(next) = π(s)` | `exec_frame` + the per-asset delta lemma |
| `monotone_registry%` | grow-only set | `reg(s) ⊆ reg(next)` | `exec_frame` (45 frame arms + 1 `subset_cons`) |
| `confinement%` | authority ⊆ ceiling | `Confined U next` | `exec_frame` + `attenuate_subset` |
| `automaton_inv%` | relation among fields | `Inv s → Inv next` | `exec_frame` + `omega`/field algebra |
| `eventually%` | reachability | a ranking / fairness witness | CTL/μ `lfp` + Lentil fairness *(future)* |

---

## 3. The userspace story — "smart-contract verification" for dregg

Today, verifying a new app costs ~500–700 lines of the skeleton above. With the Hatchery, the author writes their cell-program and a few spec lines:

```lean
-- A userspace registry contract, fully verified, no hand proof.
def MyRegistry : CellContract :=
  monotone_registry% commitments        -- the one declaration

example {s} (h : MyRegistry.Inv s) (sched) :
    ∀ n, MyRegistry.Inv (trajA s sched n) :=
  MyRegistry.forever h sched              -- "registered ⇒ registered forever", machine-checked
```

Properties expressible out of the box: *no double-spend*, *append-only audit log*, *authority confinement* (capability safety — the seL4 shape), *supply conservation / no inflation*, *monotone state* (once-true-stays-true: revocations, registrations, finalizations), and *field-relational invariants* (caps, ordering, balances-in-range). With the temporal layer: *□ safety* and *◇ liveness/progress* specs.

The guarantee is strictly stronger than typical smart-contract tools: not "holds in the tested traces" or "holds modulo an SMT oracle," but **holds at every step of the unbounded trajectory, against every adversarial schedule, with no `sorry` and no external solver in the trust base.**

---

## 4. Why it goes *first* (force-multiplier on the immediate work)

The Hatchery is feature-workflow **#0** because the queued verification program is mostly more instances of the same skeleton:

- **Effects / caveats / predicates widening** — sequential because it touches the shared `FullActionA` dispatch. `exec_frame` turns "re-verify every invariant by hand after each new effect" into "add one frame lemma, re-run, get a report." This is the single biggest de-risk of the hardest queued task.
- **CTL / μ-calculus** — the modal operators are named `lfp`/`gfp` instances; the Hatchery's `CellContract` is exactly the object they quantify over, and `dregg_auto` extends to discharge `EX/AF/EG`-shaped goals.
- **Confidentiality / noninterference** — low-equivalence preservation is *another carried invariant* (`Inv := low-equiv to a reference run`); `exec_frame` discharges most arms.
- **Privacy-crypto + ZK** — `crypto_portal` is the codified §8 discipline these modules need for every primitive.

Build the multiplier, then everything downstream is cheaper and more uniform.

---

## 5. Engineering & TCB hygiene

- **Substrate:** Lean 4.30 metaprogramming (`elab` / `macro` / `Lean.Elab.Tactic`), simp-attribute sets, and **`aesop` (already a v4.30 dependency)** as the search engine. **No new lake dependencies.**
- **Axiom-clean by construction:** the tactics produce ordinary proof terms checked by the kernel. Every Hatchery-generated theorem is pinned with `#assert_axioms` like everything else. No `native_decide`, no SMT oracle, no `sorry` — the tactics either close the goal honestly or hand it back.
- **Honest by construction:** `exec_frame` *hands back* the arms it can't frame rather than fudging them; `crypto_portal` *forces* the soundness carrier to remain an explicit hypothesis. The tooling cannot launder a gap into a false "PROVED."
- **External work = blueprints, not deps:** the adoptable Lean libs (CSLib, VCVio, LeanLTL, Lentil) all target older toolchains than our 4.30; we port-thin their relevant cores (all sorry-free) rather than add version-skewed dependencies — the same discipline that refused the Z3-laden CRDT lib. `Veil` (z3/cvc5 oracle) is blacklisted from the TCB.

---

## 6. Build plan

| Phase | Deliverable | Gate |
|---|---|---|
| H1 | Tier 1 tactics (`carry_forever`, `exec_frame`, `crypto_portal`) in `Dregg2/Verify/Tactics.lean` | reproduce one crown's `hpres` with `by exec_frame` |
| H2 | Tier 2 `dregg` aesop rule-set + `@[dregg_frame/_bridge/_grow]` attributes; tag the existing frame family | `dregg_auto` closes `livingCellA_no_double_spend`'s step |
| H3 | Tier 3 `CellContract` + `forever`/`always` derivations | the 3 apps re-expressed as `CellContract`s, same theorems |
| H4 | Tier 4 shape catalog macros (`monotone_registry%`, `conservation%`, `confinement%`, `automaton_inv%`) | each existing crown reduced to a one-line declaration; regression-equal to the hand proof |
| H5 | `eventually%` + temporal specs | *deferred to the CTL/μ + liveness workflow* |

Each phase: Sonnet drafts, Opus gates (build green + `#assert_axioms`-clean + reads the generated term for non-vacuity), I commit. The three apps are the standing regression suite — the catalog is correct exactly when it reproduces their proved theorems verbatim.

---

## 7. Non-goals & honest boundaries

- The Hatchery does **not** prove the crypto primitives sound — `crypto_portal` *organizes* the §8 assumptions, it doesn't discharge them.
- It does **not** close the down-connection to the running binary (that's THE SWAP) — it verifies the Lean model; faithfulness of the model to Rust is a separate axis.
- `eventually%` / liveness needs the CTL/μ + fairness layer; until then the catalog is safety-only (□), which is most of what contracts want.
- It automates the *regular* obligations. A genuinely novel one-step argument still gets written by hand — but `exec_frame` will have cleared the 45 boring arms around it.

---

*we built the same proof five times by hand —*
*now we teach the egg to hatch itself,*
*and hand the next dreamer a clean shell.*

🥚🐉
