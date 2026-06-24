# INTENT-REFS — Linear Logic, Session Types & Resource Semantics (conservation + exchange)

**Pillar:** the *proof-theoretic backbone* for the spine's two load-bearing slogans —
- **conservation = linearity**: a resource is consumed *exactly once* (no weakening = no
  silent discard; no contraction = no double-spend);
- **fulfillment = a well-typed session**: a fill is a *typed protocol* between demand and
  supply whose linear typing **is** the no-double-spend, and whose channel carries the
  escrowed resource.

**Companion to:** [`INTENT-AS-CO-RECEIPT.md`](./INTENT-AS-CO-RECEIPT.md) (the design spine —
esp. §2 face 3 "resource = escrow", §3 the adjunction/solver, §5 conservation).
**Siblings (do not overlap; cross-reference):**
[`INTENT-REFS-resources.md`](./INTENT-REFS-resources.md) (the *categorical / SMC / resource-theory*
layer — convertibility preorder, decorated cospans, Petri nets) and
[`INTENT-REFS-optics.md`](./INTENT-REFS-optics.md) (the *optic / coend / solver* layer).
This doc is the **substructural logic** layer *underneath* both: where the resources/optics docs
say "a non-cartesian SMC", this doc says *why* (the structural rules linear logic deletes) and
gives the **session-type** reading of a fill that the SMC layer treats as a bare morphism.
**Sibling LEARNINGS (the prior deep read, six papers):**
[`/Users/ember/dev/breadstuffs/pdfs/LEARNINGS-laws-linear-monoidal.md`](../../../pdfs/LEARNINGS-laws-linear-monoidal.md)
— the *two-laws* memo (Law 1 conservation / Law 2 ordering) with corrections C1–C5 and a Lean
build order. This doc is the *reference map* that memo's takeaways rest on; I do not re-derive its
T1–T9 table, I cite it.

**Research date:** 2026-06-03. Status: reference map, not a spec. Citations verified against the
actual PDFs in `/Users/ember/dev/breadstuffs/pdfs/` where marked `[in library]`; the two central
new pulls (Caires–Pfenning, Wadler) verified by reading their first page.

---

## 0. What dregg2 already has on this axis (so we don't duplicate)

Two modules already *implement* the easy/buildable half of this pillar. A third
(`Resource.lean`) implements the separation-logic resource-algebra tier. The references below
are scoped to *deepen these*, not restart them.

### `Dregg2/Coordination.lean` — multiparty session types (Law 2, the ordering/session backbone)
A faithful MPST layer, Honda–Yoshida–Carbone-shaped:
- **`GlobalType`** (`comm` / `choice` / `mu`+`var` / `done`) = the choreography `G`; **`LocalType`**
  (directed `send`/`recv`/`select`/`offer`) = the endpoint type; **`project G p`** = `G ↾ p`.
- **Projection is honestly partial**: `mergeLocal` is the *identity merge* (the conservative sound
  core of the classical MPST merge), and `projectBranches` can return `none` — `projectBranches_can_fail`
  is a kernel-checked witness that incompleteness is real, not vacuous.
- **`Dual`** (per-step `send`/`recv` & `select`/`offer` compatibility) + an operational
  small-step LTS (`GStep` / `GReach`) with the side-conditions `NoRec` / `NoSelfComm` / `Guarded`.
- **Theorems proved (axiom-clean, `#assert_axioms`):** `projection_sound` (head-duality / EPP
  soundness), `deadlock_freedom_by_design` (Carbone–Montesi progress over *reachable* configs —
  with `deadlock_initial_counterexample` proving the naive "over initial projections" form is
  FALSE), `deadlock_freedom_progress_step`, `privacy_by_projection` (uninvolved role ⇒ `done`,
  scoped to `NoRec` with `privacy_var_counterexample` for why the scope is needed).
- **Explicitly flagged OPEN:** the linearity⇒I-confluence conflation is *refuted* — session typing
  (Law 2) and `Confluence.IConfluent` (the cross-group-runnability third judgement) are independent;
  `iconfluent_fragment_crossgroup_free` carries that. Recursion is parked behind `NoRec`.

> **Gap this doc targets for Coordination.** It is *multiparty (MPST)* but **not** *propositions-as-
> sessions* — the types are an inductive grammar, not linear-logic propositions, and there is **no
> linearity/cut-elimination story tying the session to conservation.** The Caires–Pfenning / Wadler
> references (#2/#3) are exactly the missing bridge: they make a session type a *linear proposition*
> so that "the protocol completed" and "the resource was consumed once" are *one* proof. A fill in
> `INTENT-AS-CO-RECEIPT` §1 is binary (demand⊣supply), i.e. the **binary** Caires–Pfenning fragment,
> which is *simpler* and *more directly resource-typed* than the multiparty `Coordination` already has.

### `Dregg2/Await.lean` — algebraic effects + one-shot (linear) continuations
The continuation half of linearity:
- **`OneShot R S`** — a resumption wrapped as a *use-exactly-once* affine resource: **no duplicator,
  one eliminator `resume`** — one-shotness is a *type-level* invariant, not a runtime flag.
- **`Linear k`** (`uses ≤ 1`, the affine law) + `one_shot_is_static`.
- The decisive design theorem **`runtime_guard_is_double_spend`**: a *runtime* one-shot guard
  (`Guarded.tryResume`, Dolan's "raise on second resume") *admits* the first re-entry and only
  *then* denies — i.e. the runtime guard **is** the double-spend window it purports to close;
  the static `OneShot` removes the second call as a *constructible term*. This is **the
  conservation-as-linearity thesis in miniature**: "consume exactly once" must be a typing
  invariant, not a guard.
- Plotkin–Pretnar `Handler`; **the turn as the rollback handler** (`turnAsRollbackHandler`):
  `commit` = `resume` exactly once, `abort` = drop (0 uses) — `commit_resumes_once` /
  `rollback_discards_continuation`. The two legal affine uses of a captured continuation.
- The four await faces (`zkpromise`/`discharge`/`intent`/`promiseGraph`) unify to one `AwaitCore`
  (`four_faces_unify`); **face 3 `intent`** with `intent.Fires := ∃ w, Discharged want w` is the
  existential-resolver intent the spine's §3 talks about.

> **Gap this doc targets for Await.** One-shotness is enforced on the *continuation*, but the
> *resource* the continuation carries (the escrowed `A`) is not yet itself linearly typed — the
> "exactly once" lives on control flow, not on the funded bundle. The linear-logic references make
> the *escrowed resource* a linear hypothesis `A` in a sequent `A ⊢ C`, so consume-exactly-once
> covers the value, not just the resume.

### `Dregg2/Resource.lean` (+ `Exec/MultiAsset.lean`) — the separation-logic / camera tier (Law 1)
The resource-algebra implementation that the separation-logic references (#4) sit over:
- **`ResourceAlgebra` (Iris camera, discrete):** partial commutative monoid `op` + `valid`
  (the partiality) + `core` (the duplicable/persistent part) with the three core laws; the
  **frame-preserving update** `Fpu a b := ∀ f, valid (a · f) → valid (b · f)` is the general
  conservation law, with `conservation_is_fpu`. `ℕ`/`Excl`/`Auth` cameras (`Auth` = the
  sovereign `● a` / fragment `◦ b` authoritative split = exactly Iris `auth`).
- **`Exec/MultiAsset.lean`:** *per-asset* conservation (`maTotal k a` indexed by `AssetId`, never
  one collapsed scalar — a turn moving asset 0 leaves asset 1 *literally* untouched), keystone
  `maExec_conserves_per_asset`, and the **camera bridge** `maMovedAsset_debit_is_fpu`: the per-cell
  debit/credit is the `(ℤ,+)` shadow of a frame-preserving update under a fixed asset supply `T`.
- **`Conserve.lean`:** the reusable `sum_transfer_conserve` lemma + the `conserve` / `commit_cases`
  tactics (debit/credit cancellation, fail-loud).

> **Gap this doc targets for Resource.** The camera/FPU machinery is the *separation-logic
> resource model*; what is missing is the **frame rule as the formal statement of per-cell local
> reasoning + JointTurn disjointness** (O'Hearn/Reynolds, #4) — i.e. that conservation proved
> "locally" on one cell's footprint lifts to the whole multi-cell config because the frame
> (everyone else's resources) is untouched. `maTransfer_untouched` is the *seed* of the frame rule
> already; the references give it its name and its compositional form.

**One-line situation:** dregg2 already has (a) MPST sessions with deadlock-freedom, (b) one-shot
linear continuations + the turn-as-rollback-handler, and (c) Iris-camera resources with
per-asset FPU conservation. **What it lacks is the *unifying bridge*: propositions-as-sessions,
where a fill is a cut between dual linear proofs and "session done" ⟺ "resource consumed once",
plus the frame rule named as the local-reasoning law over disjoint cells.** That bridge is the
point of references #1–#4 below.

---

## TL;DR ranking

| # | Reference | Authors / venue | Gives us | Spine hook |
|---|-----------|-----------------|----------|------------|
| **1** | **Linear Logic** | Girard, *TCS* 1987 `[in library]` | the origin: no weakening/contraction = consume-exactly-once = conservation; `⊗`/`&`/`⊸`/`!`; turn = `pre ⊸ post` | §2 face 3, §5 (conservation), Law 1 |
| **2** | **Session Types as Intuitionistic Linear Propositions** | Caires–Pfenning, *CONCUR* 2010 `[PULLED]` | **propositions-as-sessions**: ILL prop = session type, proof = process, **cut = communication**, cut-reduction = the protocol running; session fidelity + deadlock-freedom *as theorems of the logic* | §1 (fill = cut), §3 (demand⊣supply), §7 (formalize the session-typed fulfillment) |
| **3** | **Propositions as Sessions** | Wadler, *ICFP* 2012 `[PULLED]` | the *classical* CP + functional GV; **deadlock-freedom from cut-elimination**; a clean small calculus to mirror | §1, the auction settle as a deadlock-free session |
| **4** | **Separation logic / the frame rule** | O'Hearn–Reynolds–Yang; Brookes–O'Hearn (CSL) `[in library]` | `{P} C {Q}` with the **frame rule** `{P∗F}C{Q∗F}` = local reasoning over **disjoint** resources; `∗` = our per-cell disjointness | §5 (per-cell conservation), §7 (JointTurn disjointness), `Resource.lean` frame |
| **5** | **Multiparty Asynchronous Session Types** | Honda–Yoshida–Carbone, *POPL* 2008 / *JACM* 2016 `[in library JACM]` | global type → projections → local types; deadlock-freedom by projection | **already in `Coordination.lean`** — *compare, don't rebuild* |
| **6** | **Computational interpretations of linear logic** | Abramsky, *TCS* 1993 | proofs-as-processes (the ancestor of #2/#3); `⊗`/`⅋` = parallel composition; cut = interaction | context for #2/#3; the lineage Wadler continues |
| **7** | **Ledger = commutative monoid; transfer = monoid action** | (synthesised; grounded in Coecke–Fritz #res-1 + Girard) | conservation = a **monoid homomorphism invariant** `Σ : State → (M,+)`; we *already nearly have this* | §5 (conservation), restate `maExec_conserves` as a monoid-hom |
| **8** | **ILL `!` / Bunched Implications (BI)** | Girard `!`; O'Hearn–Pym BI 1999 | `!A` = replicable/read-only resource = **escrow-held / catalyst caps**; BI's `∗` vs `∧` = the separation `Resource.lean` wants | §2 face 3 (catalyst/escrow caps), `Resource.lean` `core` |

The library also holds a *cluster* of session-types-from-linear-logic papers already read in the
LEARNINGS memo (Lindley–Morris *Sessions as Propositions*; van den Heuvel–Pérez *Comparing…*;
Fu–Xi–Das *Dependent Session Types*) — re-listed under §"adjacent" below, not re-pulled.

---

## 1. Girard — *Linear Logic* — **the origin of "consume exactly once = conservation"**

- **Author / year / venue:** Jean-Yves Girard, *Theoretical Computer Science* 50 (1987) 1–101.
- **In library:** `girard-linear-logic-syntax-semantics.pdf` (the *Syntax & Semantics* survey form).
- **What it gives us + how it maps onto the spine.** Linear logic is the logic of *resources that
  cannot be freely copied or thrown away*. The decisive structural fact for us:
  - **No weakening** (`Γ ⊢ Δ` does NOT give `Γ, A ⊢ Δ`): you cannot *discard* a hypothesis — a
    resource brought to a fill **must be used**, not silently dropped. = "no value vanishes."
  - **No contraction** (`Γ, A, A ⊢ Δ` does NOT collapse to `Γ, A ⊢ Δ`): you cannot *duplicate* a
    hypothesis — a single escrowed `A` cannot fund two fills. = **the no-double-spend, as a
    structural rule**. This is *exactly* `Await.runtime_guard_is_double_spend`'s thesis stated in
    the proof theory: the double-spend is precisely contraction, and the only safe defence is to
    delete contraction from the logic (= static linearity), not to guard it at runtime.
  - **The connectives we need:** `A ⊗ B` (multiplicative conjunction — *both*, resources combine
    side-by-side: our multi-cell JointTurn `⊗`); `A ⊸ B` (linear implication — **a turn is `pre ⊸
    post`**: it *consumes* the pre-state's resources to *produce* the post-state's, Girard's
    chemical reading `2H₂ ⊗ O₂ ⊸ 2H₂O`); `A & B` (additive conjunction — *external choice*, the
    `offer`/branch in `Coordination`); `A ⊕ B` (additive disjunction — *internal choice*, `select`).
  - **The exponential `!A`** re-introduces *copyable* situations: `!A` may be weakened and
    contracted, i.e. it is the **read-only / replicable** resource. → see #8: this is the formal
    model of an **escrow-held or catalyst capability** (present, may be read by many fills, not
    consumed) — `INTENT-AS-CO-RECEIPT` §2 face 3.
  - **The multiplicative fragment (MLL)** — `⊗`, `⅋`, `⊸`, units `1`/`⊥` — is the **fragment for
    resource exchange**: an exchange routes a multiplicative bundle, no choice/replication needed
    for the bilateral core. `INTENT-AS-CO-RECEIPT` §1's `fulfill : Intent(A ⊢ C) ⊗ Morphism(A→C) ⟶
    Receipt` lives entirely in MLL.
- **Map to existing Lean.** This *is* Law 1 in `LEARNINGS-laws-linear-monoidal.md` (T3/T4): the
  turn-category must be **non-cartesian** (withhold copy `Δ` / erase `◇`), which is the
  category-theoretic shadow of "no contraction / no weakening". `Conserve.sum_transfer_conserve`
  and `MultiAsset.maExec_conserves_per_asset` are *the model-side consequence*: because the kernel
  state has no copy/discard, the per-asset sum is an invariant.
- **Lean/mathlib status.** No linear-logic proof system in mathlib (it is a *classical/intuitionistic*
  type theory). The honest encoding is **not** "build a linear sequent calculus in Lean" but **carry
  linearity in the model**: a non-cartesian `MonoidalCategory` (mathlib `CategoryTheory.Monoidal`,
  *withholding* `Monoidal.Cartesian`) + the conservation functor `Σ`. Substructurality is encoded
  as *the absence of `Δ`/`◇`*, exactly as Selinger §6 licenses (see resources-doc #4).
- **Why ranked #1.** It is the single source that names *why* conservation = "consume exactly once":
  it is the deletion of weakening + contraction. Everything else here is an interpretation of it.

## 2. Caires & Pfenning — *Session Types as Intuitionistic Linear Propositions* — **fill = cut**

- **Authors / year / venue:** Luís Caires & Frank Pfenning, *CONCUR* 2010 (LNCS 6269, pp. 222–236).
- **PDF:** CMU tech-report form, `[PULLED → caires-pfenning-session-types-ill-concur2010.pdf]`
  (verified first page: "a type system for the π-calculus that **exactly corresponds** to the
  standard sequent calculus for **dual intuitionistic linear logic** … the first purely logical
  account … ensures **session fidelity, absence of deadlocks**, and a **tight operational
  correspondence between π-calculus reductions and cut elimination steps**").
- **What it gives us + how it maps onto the spine — THE bridge.** This is the propositions-as-
  sessions theorem dregg2's `Coordination.lean` *lacks*. The dictionary:
  - **a session type IS a linear proposition** (`A ⊗ B` = "send a channel of type `A`, continue as
    `B`"; `A ⊸ B` = "receive `A`, continue as `B`"; `A ⊕ B` / `A & B` = internal/external choice;
    `!A` = a *shared/replicable* service; `1` = `end`). So `Coordination.LocalType`'s `send`/`recv`/
    `select`/`offer`/`done` are *exactly* the ⊗/⊸/⊕/&/1 connectives — already, but un-named as logic.
  - **a well-typed process IS a proof**; the typing judgement `Δ ⊢ P :: x:A` reads "process `P`
    *offers* a channel `x` of session type `A`, *using* the linear channel context `Δ`" — the
    **rely/guarantee** reading (this is the *intuitionistic* two-sidedness the LEARNINGS memo C4
    picks for *locality*).
  - **cut IS communication; cut-elimination IS the protocol running.** Composing the *demand* proof
    (a process that uses a channel `A ⊸ C`) with the *supply* proof (a process that offers it) along
    the channel is the **cut rule**, and reducing that cut step-by-step *is* the session executing.
    → **This is `INTENT-AS-CO-RECEIPT` §1 `fulfill` made proof-theoretic:** the intent `A ⊢ C` is an
    open proof with a typed hole; the offer `A → C` is the dual proof; **plugging = cut**, and the
    *receipt that discharges the intent is the cut-eliminated (closed) proof*. "Receipt and intent
    annihilate into one completed turn" is **literally cut-elimination**.
  - **session fidelity + deadlock-freedom are theorems of the logic**, not side-conditions: a
    well-typed (cut-eliminable) configuration never gets stuck and always follows its protocol. Where
    `Coordination.deadlock_freedom_by_design` proves this *operationally* over an MPST LTS with
    `NoRec`/`NoSelfComm`/`Guarded` side-conditions, the logical account gets it *for free* from
    cut-elimination — and **handles recursion** (via `!`/co-recursion) that `Coordination` parks
    behind `NoRec`.
  - **the escrowed resource is the linear hypothesis.** The funded `A` of `INTENT-AS-CO-RECEIPT` §2
    face 3 is a *linear antecedent* `A` in `A ⊢ C`: it is in the context exactly once, so it is
    *consumed* exactly once by the fill — the escrow's "released to the filler exactly on the
    discharging receipt" is the linearity of `A` in the sequent. **This is the cleanest formal home
    for escrow we have found.**
- **Why ranked #2 (above MPST #5).** The spine's fill (§1) is **binary** (demand⊣supply along one
  channel), and Caires–Pfenning is *the* binary, resource-typed, conservation-aware account. It is
  *simpler* and *more directly about resources* than the multiparty machinery already in
  `Coordination.lean` — and it is the bridge that turns that machinery from "an inductive grammar
  with a hand-proved deadlock theorem" into "a fragment of linear logic where conservation and
  session-completion are the same proof."
- **Lean/mathlib status.** No propositions-as-sessions formalisation in mathlib. There *are* external
  Coq/Agda mechanisations of this exact correspondence (e.g. the Actris program logic
  `[in library: actris2-session-types-separation-logic.pdf]` realises Caires–Pfenning-style session
  types *inside Iris separation logic* — which is **directly relevant** since `Resource.lean` is
  already an Iris camera: Actris is the proof that session channels can be **resources in the same
  camera as the balances**, unifying Law 1 and Law 2 in one separation logic). For Lean, the honest
  first step is to *re-read* `Coordination.LocalType` as the ⊗/⊸/⊕/&/1 connectives and add a `Dual`-
  is-`(·)^⊥` lemma + a *cut* combinator whose reduction is the session step — small, and it upgrades
  the existing module rather than restarting it.

## 3. Wadler — *Propositions as Sessions* — **deadlock-freedom from cut-elimination; the clean calculus**

- **Author / year / venue:** Philip Wadler, *ICFP* 2012 (and *J. Funct. Programming* 24 (2014)).
- **PDF:** `[PULLED → wadler-propositions-as-sessions-icfp2012.pdf]` (verified first page:
  "a calculus **CP** in which propositions of **classical linear logic** correspond to session
  types … a linear functional language **GV** … **deadlock freedom follows from the correspondence
  to linear logic**").
- **What it gives us + how it maps onto the spine.** Wadler's CP is the *classical* (one-sided)
  cousin of Caires–Pfenning, and his GV is a *functional* surface language with session types
  translated into CP. Two things we take:
  - **the cleanest small calculus to mirror.** CP has exactly the connectives we need and a *very*
    compact proof of deadlock-freedom (cut can always be eliminated because the proof net is acyclic
    — there is no "waiting cycle"). This is the *target shape* for a future `Dregg2/Session.lean`:
    far smaller than the full MPST LTS in `Coordination.lean`, and it is the *binary* fill the spine
    actually uses.
  - **GV = the functional/intent surface.** GV is "a linear λ-calculus with session-typed channels";
    `INTENT-AS-CO-RECEIPT`'s *intent objects* (a typed hole + funded resources) are GV values, and
    the *solver* assembling `A → B₁ → … → C` is a GV program composing channels — which connects to
    the §3 coend/optic solver in the **optics** sibling doc (the optic is the *categorical* picture;
    GV is the *term-language* picture of the same composition).
  - **classical vs intuitionistic is a real fork** (LEARNINGS C4): Wadler's CP is *classical*
    (more typable processes, but **loses locality**); Caires–Pfenning is *intuitionistic* (rely-
    guarantee + **locality** — "a capability received across a membrane cannot be re-served"). For
    the **membrane law** dregg wants *intuitionistic* (#2); for the *acyclic-net deadlock-freedom
    proof technique* Wadler's classical presentation is the cleaner to borrow. Carry both: intuit.
    for the *typing discipline*, classical proof-nets for the *deadlock argument*.
- **Lean/mathlib status.** None in mathlib. CP/GV have Agda mechanisations in the literature (e.g.
  by the Wen/Kokke/Lindley school) to read for the encoding, not to depend on.

## 4. Separation logic & the frame rule — O'Hearn / Reynolds / Brookes–O'Hearn — **local reasoning over disjoint resources**

- **Authors / venues:** John Reynolds, *Separation Logic* (LICS 2002); Peter O'Hearn, John Reynolds,
  Hongseok Yang, *Local Reasoning about Programs that Alter Data Structures* (CSL 2001);
  Brookes–O'Hearn, *Concurrent Separation Logic* (CSL/CONCUR lineage).
- **In library:** `concurrent-separation-logic-brookes-ohearn.pdf`,
  `actris2-session-types-separation-logic.pdf`, `disel-distributed-separation-logic.pdf`,
  `beginners-guide-iris-coq-separation-logic-2105.12077.pdf`, the handler-separation-logic pair.
- **What it gives us + how it maps onto the spine.** Separation logic adds to Hoare logic the
  **separating conjunction `P ∗ Q`** ("`P` and `Q` hold on *disjoint* pieces of resource") and the
  **frame rule**:
  ```
        {P} C {Q}
    ───────────────────  (C does not touch F's footprint)
    {P ∗ F} C {Q ∗ F}
  ```
  i.e. *if `C` is correct on its own footprint, it stays correct in any larger world, because the
  frame `F` is untouched.* This is **exactly the missing-name for what `MultiAsset.lean` already
  half-proves**: `maTransfer_untouched` ("every asset `b ≠ a` is literally unchanged") and the fact
  that a transfer only touches `{src, dst}` *is the frame rule* — conservation proved *locally* on
  the two-cell footprint lifts to the whole `accounts` set because everyone else's balance is the
  frame. Mapped onto the spine:
  - **per-cell conservation = a local Hoare triple**; the JointTurn over disjoint cells = the
    **frame rule applied to `∗`-separated cell footprints** (`INTENT-AS-CO-RECEIPT` §5; §7
    JointTurn disjointness). The CG-2 equalizer / cross-cell gluing in the *resources* sibling doc
    (decorated cospans) is the *categorical* face of the same disjointness.
  - **`∗` is the separation `Resource.lean` is built for.** The Iris camera's `op` (`·`) with its
    `valid` predicate **is** the resource model of `∗`: `a ∗ b` is well-formed iff `valid (a · b)`,
    and the **frame-preserving update** `Fpu a b := ∀ f, valid (a·f) → valid (b·f)` is *literally
    the frame rule at the resource-algebra level* ("the update is sound against any frame `f`").
    So `Resource.conservation_is_fpu` and `MultiAsset.maMovedAsset_debit_is_fpu` are **already the
    semantic frame rule** — what is missing is the *syntactic* `{P∗F}C{P'∗F}` triple layer naming it.
  - **Concurrent SL (Brookes–O'Hearn): disjoint concurrency composes.** Two threads (cells) on
    disjoint resource run in parallel and their proofs combine — the **soundness of running
    cross-group turns without an atomic commit** when footprints are disjoint, which is *exactly*
    `Coordination.iconfluent_fragment_crossgroup_free`'s content from the separation side
    (disjointness ⇒ no coordination needed; overlap ⇒ must escalate). The two judgements meet here.
  - **Actris (`[in library]`): session types ∗ separation logic.** Actris embeds *binary session
    types* (à la Caires–Pfenning) as Iris separation-logic resources, with a `chan ↦ proto`
    assertion that is itself a separating-conjunction resource. → the **unification target**: in
    `Resource.lean`'s camera, a **session channel and a balance are resources of the same algebra**,
    so Law 1 (conservation) and Law 2 (ordering/session) are theorems in *one* logic — the deepest
    payoff of this whole pillar.
- **Lean/mathlib status.** No separation logic in mathlib; the canonical mechanisations are in **Coq
  (Iris)** — `Resource.lean` is a deliberate *discrete* port of the Iris camera. The frame rule
  itself does not need full Iris: with the camera already in hand, a **`Frame`/`Footprint`** layer
  (a triple `{pre} exec {post}` over a footprint `Finset CellId`, plus a `frame` lemma that an
  untouched cell's balance is preserved) is a *small, honest* Lean build directly on
  `MultiAsset.maTransfer_untouched`. That is the recommended new artifact for this pillar (see below).

## 5. Honda–Yoshida–Carbone — *Multiparty Asynchronous Session Types* — **already in `Coordination.lean`; compare**

- **Authors / year / venue:** Kohei Honda, Nobuko Yoshida, Marco Carbone, *POPL* 2008; journal
  version *JACM* 63(1) 2016. **In library:** `mpst-honda-yoshida-carbone-jacm.pdf`.
- **What it gives us / status.** This is the source `Coordination.lean` already implements: global
  type → projection `G ↾ p` → local types → deadlock-freedom-by-projection. **Do not rebuild.** The
  value of *re-citing* it here is the comparison axis: MPST gives the *N-ary choreography* but is
  **not** propositions-as-sessions — it has no linear-logic / cut-elimination backbone, which is why
  `Coordination` must *hand-prove* deadlock-freedom over an LTS with `NoRec`. The recommended move
  (#2/#3) is to *add* the binary linear-logic reading underneath the existing MPST grammar, not
  replace it. Related library MPST papers (dynamic multirole, parameterised, async subtyping,
  hybrid) are extensions to defer.

## 6. Abramsky — *Computational interpretations of linear logic* — **proofs-as-processes (the ancestor)**

- **Author / year / venue:** Samson Abramsky, *Theoretical Computer Science* 111 (1993) 3–57 (the
  "proofs as processes" programme; with Bellin–Scott 1994).
- **What it gives us.** The *original* reading that #2 and #3 continue (Wadler's first sentence cites
  it): linear-logic proofs interpreted as **concurrent processes**, `⊗`/`⅋` as forms of parallel
  composition, **cut as interaction/communication**, normalisation as computation. We cite it for
  lineage and for the `⅋` (multiplicative disjunction = "par", the *output* dual of `⊗` input) which
  the *classical* CP (#3) uses and which names the symmetry between a demand-side and a supply-side
  channel. Not pulled (older, not open-access in a clean PDF); the content we need is fully covered
  by the #2/#3 PDFs which restate it.

## 7. Ledger = commutative monoid; transfer = monoid action — **conservation as a monoid-hom invariant (we nearly have it)**

- **Status:** synthesised target, grounded in Coecke–Fritz (resources sibling #1) + Girard (#1 here)
  + the existing Lean. No single canonical paper "owns" this folklore; the rigorous backing is the
  resource-theory **core layer** (a resource theory's invariant content = a *commutative preordered
  monoid* `(R,+,⪰,0)`, Coecke–Fritz Def 4.1) specialised to *conservation* (the preorder is equality
  on the conserved quantity).
- **What it gives us + how it maps onto the spine.** State the conservation law as **algebra, not
  combinatorics**:
  - **a ledger is a commutative monoid.** The balances of one asset form `(CellId → ℤ, +)`; the
    **total supply** is the monoid homomorphism `Σ : (CellId → ℤ) → (ℤ, +)`, `Σ bal = ∑_c bal c`.
  - **a transfer is a monoid action / a `Σ`-preserving endomorphism.** `maTransferBal src dst a amt`
    is the map "subtract `amt` at `src`, add at `dst`"; it is in the **kernel of the boundary** —
    `Σ ∘ transfer = Σ` — i.e. transfer is the *zero-sum* (conservative) part of the monoid of state
    updates. Minting/burning are the *non-kernel* generators (declared `Σ`-shifts), exactly
    LEARNINGS C3.
  - **conservation = a monoid-homomorphism invariant.** `maExec_conserves_per_asset : maTotal k' a =
    maTotal k a` **already says** "`Σ` is invariant under the transfer action." The *upgrade* is to
    state it once, abstractly: `Σ` is a monoid hom and `transfer ∈ ker(Σ-boundary)`, so the per-asset
    keystone becomes a one-liner corollary of an algebraic fact rather than a re-run debit/credit sum.
  - **per-asset = a product of monoids.** The honest conserved object is the **vector** `ℤ^AssetId`
    (LEARNINGS Q1): `Σ : (CellId → AssetId → ℤ) → (AssetId → ℤ)`, a hom into the product monoid,
    conserved *componentwise* — which is precisely `MultiAsset`'s "never collapse to one scalar."
- **Lean/mathlib status.** **Pure reuse, no new mathlib.** mathlib has `AddCommMonoid`, `AddMonoidHom`
  (`→+`), `Finset.sum` as a hom (`map_sum`), and product monoids. Restating `maTotal` as an
  `AddMonoidHom` and `maExec_conserves_per_asset` as "the transfer endo is in its kernel-boundary" is
  a **light refactor that buys generality**: the same statement then covers any commutative-monoid-
  valued resource (`ℕ`, `ℚ≥0`, `K → ℕ`) — which `Resource.lean`'s opening comment already anticipates.

## 8. ILL `!` / Bunched Implications (BI) — **read-only / replicable resources = escrow-held / catalyst caps**

- **Sources:** Girard's exponential `!A` (#1); O'Hearn & Pym, *The Logic of Bunched Implications*,
  *Bull. Symbolic Logic* 5(2) 1999 (BI = the logic where `∗`/separation and `∧`/sharing **coexist**
  — the proof theory *underneath* separation logic #4).
- **What it gives us + how it maps onto the spine.** Two complementary "duplicable resource" stories:
  - **`!A` (the exponential):** the *one* type that **may** be weakened and contracted — a resource
    you can *read many times without consuming*. This is the precise model of `INTENT-AS-CO-RECEIPT`
    §2 face 3's **catalyst / escrow-held capability** (present-and-required for the fill, but
    *returned*, not spent — Coecke–Fritz catalysis in the resources doc, *here given its logical
    constructor*) and of a **read-only / attenuating capability** (held, not consumed). In
    `Resource.lean` the camera **`core`** (`|a|`, the duplicable/persistent part) is *exactly* `!` at
    the resource-algebra level: `core a = some ca` with `ca · a = a` is "the part of `a` you may copy
    freely" = the persistent/`!`-able fragment. So `Resource.core` **is** the camera's `!`.
  - **BI's two conjunctions (`∗` vs `∧`):** BI is the logic where *separating* `∗` (disjoint
    resources) and *additive* `∧` (shared context) live together — which is *precisely* the modelling
    tension `Resource.lean`'s header calls out (NFT disjointness vs authoritative-fragment sharing).
    BI is the proof-theoretic justification that a cell's state can carry **both** linear balances
    (`∗`-separated) **and** shared/`!`-able read-only caps in one assertion. For dregg this names the
    *caps↔keys* split logically: linear `∗` for value, `!`/`∧` for replicable attestations.
- **Lean/mathlib status.** No BI/linear-logic object in mathlib; the relevant Lean already exists as
  **`Resource.core`** (the `!`/persistent fragment) — what is missing is only the *lemma* that
  `core`-fragments are exactly the freely-duplicable (weakenable+contractable) resources, i.e. an
  Iris-style `Persistent`/`□` characterisation. Small, and it gives escrow-held caps a one-line type.

---

## Adjacent sources already in the library / cited in the spine (not re-pulled)

- **Lindley & Morris, *Sessions as Propositions*** `[in library: sessions-as-propositions-1406.3479.pdf]`
  — propositions-as-sessions in a *functional* setting (GV-style); the *ordering* (Law 2) layer of the
  LEARNINGS memo. Cut-elimination = communication, stated for a λ-calculus.
- **van den Heuvel & Pérez, *Comparing Session Type Systems derived from Linear Logic***
  `[in library: comparing-session-type-systems-linear-logic-2401.14763.pdf]` — the classical-vs-
  intuitionistic fork (LEARNINGS C4): intuitionistic gives **locality** (received authority can't be
  re-served = the membrane law), classical gives more typable processes. **Read this before choosing
  the membrane's logic.**
- **Fu, Xi, Das, *Dependent Session Types for Verified Concurrent Programming***
  `[in library: dependent-session-types-verified-concurrency-2510.19129.pdf]` — `ch⟨P⟩`/`hc⟨P⟩`
  provider/client duality; **a sequential program as the spec of a concurrent one** = the
  differential-testing oracle architecture (Lean = sequential golden oracle, Rust = concurrent impl).
- **Actris (session types ∗ Iris separation logic)** `[in library:
  actris2-session-types-separation-logic.pdf]` — the concrete proof that session channels are
  resources in the *same* separation logic as the heap/balances; the unification template for
  `Resource.lean` + a session layer.
- **Coecke–Fritz–Spekkens, *A mathematical theory of resources*** — the *categorical* resource-theory
  layer; fully covered in the **resources** sibling doc (#1 there). Conservation's "core layer =
  commutative preordered monoid" is the backing for §7 above.
- **Selinger, *Graphical languages for monoidal categories*** `[in library]` — the *diagrammatic*
  face of linearity (cartesian iff has copy `Δ`/erase `◇`; withhold them = linear). Covered in the
  **resources** sibling doc (#4 there).
- The MPST extension cluster (`dynamic-multirole`, `parameterised`, `precise-subtyping-async`,
  `hybrid-multiparty`, `monitorability`, `role-parametric-go`, `bft-web-services-session-types`)
  — extensions of #5 to defer until the binary linear core lands.

---

## What to formalize first

Three concrete recommendations, ranked. The theme: **the easy/buildable wins are model-side
algebra and a frame layer; the deep win is propositions-as-sessions — defer it but aim for it.**

**Recommendation 1 (do first — pure reuse, highest certainty): restate conservation as a
monoid-homomorphism invariant (§7).** We *already nearly have this*. `MultiAsset.maTotal` is a
`Finset.sum`; make it an `AddMonoidHom (CellId → AssetId → ℤ) (AssetId → ℤ)` (mathlib `map_sum`),
and restate `maExec_conserves_per_asset` as "the transfer endomorphism lies in the boundary-kernel
of `Σ`" (componentwise on the product monoid `ℤ^AssetId`). **Cost: a light refactor, no new
mathlib.** **Payoff:** the per-asset keystone becomes a corollary of an algebraic fact (transfer is
zero-sum), generalises for free to any commutative-monoid resource (`ℕ`/`ℚ≥0`/`K→ℕ` — which
`Resource.lean` already wants), and gives the spine a *one-sentence* conservation law: "total
supply is a monoid hom; every non-mint/burn turn is in its kernel." This directly serves
`INTENT-AS-CO-RECEIPT` §5 / §7 "conservation-across-a-fill as a corollary of the kernel per-asset
invariant."

**Recommendation 2 (do second — small, names what's half-built): a frame layer over
`MultiAsset` (§4).** Add a `Footprint := Finset CellId` and a Hoare-ish triple
`{pre on footprint} maExec {post on footprint}`, then prove the **frame lemma** directly from the
existing `maTransfer_untouched`: a cell *outside* `{src, dst}` has its balance preserved, so any
property of the frame survives the turn. This is the *syntactic* `{P∗F}C{P∗F}` naming of what
`maTransfer_untouched` + `conservation_is_fpu` already establish semantically. **Cost: small (the
hard lemma exists).** **Payoff:** it is the formal statement of **per-cell local reasoning +
JointTurn disjointness** (`INTENT-AS-CO-RECEIPT` §5/§7), it connects `Resource.lean`'s FPU (the
semantic frame rule) to a usable triple layer, and it is the separation-logic twin of the
I-confluence "disjoint ⇒ no coordination" judgement (`Coordination.iconfluent_fragment_crossgroup_free`).

**Recommendation 3 (the deep target — defer, but design toward it): the binary session-typed
fulfillment (§2/§3), and yes it is worth it for the auction.** Re-read `Coordination.LocalType` as
the linear-logic connectives (`send`=⊗-output, `recv`=⊸/⊗-input, `select`=⊕, `offer`=&, `done`=1),
add `Dual` = linear negation `(·)^⊥`, and a **`cut`** combinator whose one reduction step is the
session advancing — then **a fill is a cut between the demand proof (`A ⊸ C`) and the supply proof,
and the discharging receipt is the cut-eliminated proof** (`INTENT-AS-CO-RECEIPT` §1 made
proof-theoretic; the escrowed `A` is the linear antecedent consumed exactly once). **Is it worth it
for the gallery auction?** *Yes, with scope discipline:* the auction settle (escrow → reveal →
winner-pays → conservation) is a **binary, deadlock-sensitive resource exchange** — exactly what the
Caires–Pfenning binary fragment certifies *for free* (session fidelity + deadlock-freedom +
consume-once), where `Coordination`'s multiparty machinery would over-engineer it and still hand-
prove deadlock. The honest sequencing: ship Recs 1–2 (which the auction needs *anyway* for
conservation), build the auction against them, and bring the session-typed `cut` in as the layer
that proves *no-frontrunning-by-protocol-structure* and *atomic settle* — at which point Actris
(`[in library]`) shows how to fold the session channel into the *same* `Resource.lean` camera as the
balances, unifying Law 1 and Law 2. That unification is the prize; Recs 1–2 are the rent.

**Net mathlib gap.** Rec 1 = pure reuse (`AddMonoidHom`, `map_sum`, product monoids). Rec 2 = small
build on an existing lemma (no new mathlib). Rec 3 = a genuine BUILD (no propositions-as-sessions or
linear sequent calculus in mathlib) but **scoped to the binary fragment and built *on top of* the
existing `Coordination.LocalType`** rather than from scratch — and *not* a linear logic *in* Lean,
but a model carrying linearity (non-cartesian category + linear-antecedent-as-camera-element), which
is exactly the encoding Girard's structural reading and Iris cameras already license.

---

## PDFs pulled this session (validated `%PDF`, in `/Users/ember/dev/breadstuffs/pdfs/`)

- `caires-pfenning-session-types-ill-concur2010.pdf` — Caires & Pfenning, *Session Types as
  Intuitionistic Linear Propositions*, CONCUR 2010 (ref #2). [229 KB, first page verified]
- `wadler-propositions-as-sessions-icfp2012.pdf` — Wadler, *Propositions as Sessions*, ICFP 2012
  (ref #3). [207 KB, first page verified]

**Already present (cited, not re-pulled):** `girard-linear-logic-syntax-semantics.pdf` (#1),
`mpst-honda-yoshida-carbone-jacm.pdf` (#5), `concurrent-separation-logic-brookes-ohearn.pdf` /
`actris2-session-types-separation-logic.pdf` / `disel-distributed-separation-logic.pdf` /
`beginners-guide-iris-coq-separation-logic-2105.12077.pdf` (#4), `sessions-as-propositions-1406.3479.pdf`,
`comparing-session-type-systems-linear-logic-2401.14763.pdf`,
`dependent-session-types-verified-concurrency-2510.19129.pdf` (adjacent), plus the LEARNINGS memo
`LEARNINGS-laws-linear-monoidal.md`.
**Not pulled:** Abramsky 1993 (#6, older, no clean OA PDF — content fully covered by #2/#3);
O'Hearn–Pym BI 1999 (#8, content carried by the in-library Iris/CSL PDFs).
