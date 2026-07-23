# DESIGN — A Proof-Producing Arithmetizer

> **Verify corrections (GROUNDED verdict):** (1) §1.4's two "named residuals" at the concrete-AIR
> level are already CLOSED in the committed tree — the foundation is more complete than the doc states
> (conservative slip, doesn't touch the thesis). (2) MVP-0's mutation canary must bite on something the
> proof term DEPENDS on: `dfaAccepts_reduces` is parametric in `accept`, so mutating `accept` alone won't
> break typecheck — the load-bearing canary mutates the DELTA / the statement↔spec linkage. (3) MVP-1's
> `guard` leaf needs a `guardAccepts_as_cert` lemma that does not yet exist; use `vpa` (which ships
> `vpaAccepts_as_cert`) as the MVP-1 second leaf, and add the guard lemma as its own step.


**Status:** design scout. NO implementation, NO Lean written. Grounded in the files that exist.
**Date:** 2026-07-22.

## 0. The one-sentence claim, and the honest version of it

**Aspiration.** A Lean-4 elaborator `#arithmetize spec` (or `arithmetize% spec`) that, from a SPEC,
emits BOTH (1) an arithmetization and (2) a machine-checked refinement theorem
`∀ trace, satisfies air trace → specHolds (decode trace)` — *generated*, not hand-written. The
proof-carrying answer to Gabbay's "correct to a high degree of certainty": here the per-instance
refinement proof is *generated* and Lean *checks* it, so certainty is a checked theorem, not a
degree.

**Honest version, after reading the tree.** There are TWO things this codebase calls
"arithmetization", separated by a large gap in proof weight, and the design MUST NOT paper over it:

- an **ABSTRACT constraint system** — the relation-parametric certificate `Hypergraph.Cert R`
  (`metatheory/Dregg2/Crypto/Chain.lean`). Its soundness is already GENERIC over the relation `R`
  (`bridge`, `Cert.map`, `Cert.foldSound`). Turning a spec into this object and assembling its
  soundness proof is **tractable to auto-generate**, because the compiler's whole instruction set is
  a small fixed library of already-proven, generic lemmas that you *apply*, never re-prove.

- a **CONCRETE felt/row AIR** — an `EffectVmDescriptor2` (`metatheory/Dregg2/Circuit/DescriptorIR2.lean`)
  emitted to a byte-pinned JSON wire object and loaded by Rust, whose refinement is a bespoke
  field-by-field proof over ℤ mod `p` (`dyck_sat_imp_row_valid` in
  `metatheory/Dregg2/Circuit/Emit/DyckStackRefine.lean`, ~170 lines of primality splits and field
  lifts, and the *decode glue* is still an OPEN residual there). Auto-generating THIS is **much
  harder** and is not close to solved even by hand.

The MVP targets the abstract level. The abstract↔concrete-AIR bridge is the named, unfunded hard
part. This document says which is which at every step.

---

## 1. What actually exists (the ground truth this design stands on)

### 1.1 The abstract substrate — `Hypergraph.Cert` and its three generic lemmas
`metatheory/Dregg2/Crypto/Chain.lean` (a leaf: Mathlib + `Dregg2.Tactics` only):

- `chain R : List α → Prop` — consecutive elements one `R`-step apart.
- `Cert R start goal c := c.head? = some start ∧ c.getLast? = some goal ∧ chain R c`.
- `bridge R start goal : (∃ c, Cert R start goal c) ↔ ReflTransGen R start goal` — **the** soundness
  keystone, one proof for ALL `R`.
- `Cert.map f hf : Cert R x y c → Cert S (f x) (f y) (c.map f)` — functorial transport along a
  relation-preserving map (`∀ x y, R x y → S (f x) (f y)`).
- `Cert.foldSound out Sem hstep : Cert R x y c → Sem (out y) y → Sem (c.flatMap out) x` — the generic
  "walk the chain, accumulate output, carry an invariant" induction. This is the ENTIRE multi-row
  assembly machinery, exposed as one lemma.

These are `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}) and non-vacuously
witnessed (`cert_map_nonvacuous`).

### 1.2 The "swap the relation R" dispatch is ALREADY the codebase's pattern — done by hand
Four sibling files each show that a machine's acceptance IS a `Cert` over one relation, differing
ONLY in `R`. They are near-identical in shape:

| file | relation `R` | `..._as_cert` (accept ⟺ Cert + boundaries) | `..._reduces` (⇒ ReflTransGen, via `bridge`) |
|---|---|---|---|
| `Crypto/DfaAsCert.lean` | `delta a b := b.state = a.next` | `dfaAccepts_as_cert` | `dfaAccepts_reduces` |
| `Crypto/VpaAsCert.lean` | `R_vpa a b := b.pre = a.post` | `vpaAccepts_as_cert` | `vpaAccepts_reduces` |
| `Crypto/ReplayAsCert.lean` | `ReplayStep g` (pushdown move) | `replay_as_cert` | (`replay_iff_reflTransGen`) |
| `Crypto/Hypergraph.lean` | `g.Produces` | `cfg_parse_via_reduction` | = `bridge g.Produces` |

Every one of these is: (a) define `R`; (b) a mostly-`Iff.rfl` bridge that `chain R` = the machine's
own `chained` predicate; (c) reassociate the acceptance conjuncts and swap `chain` for `Cert`; (d)
feed the `Cert` half through `bridge`. **This is exactly the boilerplate a metaprogram should
generate.** `DfaAsCert`'s `chained_iff_chain` is literally `fun _ => Iff.rfl`.

`ReplayAsCert` further shows the multi-row story: the heavy `mrun_imp_replay` induction is re-derived
as a single `Cert.foldSound` instance (`mrun_imp_replay_via_fold`) at `out := rowRules`,
`Sem rs row := Replay dyck rs row.inp row.stk`, with the content split into `mrun_cert` (run-shape)
and `mstep_step` (one local step). The generic fold does the induction; the per-machine content is a
one-step lemma. **This is the compositional shape the proof-generator would target.**

### 1.3 The prototype — HandlebarsWitness (the pattern already hand-built)
`metatheory/Dregg2/Crypto/HandlebarsWitness.lean` is a hand-built proof-producing emit for one
grammar:

- `renderRules T d` — a `def` that GENERATES the concrete leftmost rule sequence by structural
  recursion on the template `T` and data `d` (`renderRules := startRule T :: T.segments.flatMap
  (segRules d)`; `stateRules` recurses on the word).
- `renderRules_accepts : safe T d → ReplayAccepts (handlebarsToGrammar T) (renderRules T d) (render
  T d)` — a THEOREM whose proof is by structural recursion **mirroring the def** (`segs_replay` /
  `safe_state_replays` recurse the same shape `renderRules` does, threading a continuation stack).
- `materialized_agrees : compact_sound … (renderRules_accepts …) = render_mem_language …` — a
  consistency tooth proven by `rfl`: the materialized certificate and the pre-existing existence
  proof are the SAME fact (proof irrelevance).

**Read as a template for the general mechanism:** `renderRules` is "generate the witness/AIR-fragment
by recursion on the spec AST", `renderRules_accepts` is "generate the proof by the same recursion",
`materialized_agrees` is "the generated artifact agrees with the abstract truth". The arithmetizer
generalizes this triple from one hard-coded grammar to any spec built from the DSL constructors.

### 1.4 The concrete-AIR target — what "the real AIR" is, and how heavy its refinement is
`EffectVmDescriptor2` = `{ name, traceWidth, piCount, constraints : List VmConstraint2, hashSites,
ranges }`. `VmConstraint2 = .base (.gate/.piBinding/.boundary) | .windowGate | .lookup`.
`emitVmJson2 d : String` serializes it; a `#guard emitVmJson2 dyckParseDesc == "…"` byte-pins the
wire object (`DyckStackEmit.lean` §6), and `descriptor_by_name` serves it to Rust. The Dyck
descriptor is **79 constraints wide, 38 columns**.

Its refinement `dyck_sat_imp_row_valid` (DyckStackRefine.lean, lines 638–810) is the proof a
metaprogram would have to GENERATE at this level. Its actual shape:
- build local combinators `G`/`W` (a gate/window body vanishes mod `p` on a transition row),
  `CL`/`CN` (canonicality), `lift_loc`/`lift_nl` (mod-`p` congruence → ℤ equality under
  canonicality), `gc` (gated equal-to-constant), `wt` (gated cross-row thread), `dd` (gated depth
  delta), and lane pins `hop/hlS/hcl/hz`;
- then discharge each of ~18 fields of the `DyckRowValid` structure by applying those combinators,
  several via **primality splits** (`pPrimeInt.dvd_mul`, `range_of_gate`, `bin_of_gate`) and `omega`.

This is not application of a fixed generic library — it is a bespoke tactic proof keyed to THIS
constraint set, THIS column layout, THIS field prime. Two further facts sharpen the honesty:
1. `dyckDesc` is a HAND TRANSCRIPTION, not emit-gated to the deployed descriptor (the file's own
   header, §"second named gap"). So even the hand refinement is not yet machine-tied to the wire
   object it claims to be about.
2. The whole-parse theorem `parse_sat_imp_replay` is NOT proven — the DECODE glue (reading `D`-wide
   symbol cells + `STACK_DEPTH` back into `List (Symbol …)` and truncating `done` padding) is a
   named §7 residual. Row-level SAT⇒SEM + multi-row assembly are the two proven halves; the decode
   is open.

**Conclusion for the design:** at the concrete-AIR level the human hasn't finished ONE instance by
hand. An auto-generator there is a research program, not an MVP.

---

## 2. Architecture — the arithmetizer as a certified compiler

The arithmetizer is a **certified compiler** `compile : SpecAST → (Air × Proof)` by structural
recursion on the spec, where each constructor's case emits an AIR fragment and a proof fragment, and
the fragments compose through the `Cert` lemmas. "Swap the relation `R`" is the compiler's leaf
dispatch; `Cert.map` / `Cert.foldSound` are its combinators.

```
                SpecAST  ──compile──▶  (Air fragment, Refinement proof term)
   leaf   dfa δ q₀ acc   ─▶  Cert delta            + dfaAccepts_as_cert / _reduces
   leaf   guard φ        ─▶  Cert (predStep φ)     + (predicate-rung as_cert)
   leaf   rel R          ─▶  Cert R                + bridge R
   node   seq s₁ s₂      ─▶  Cert.map / concat     + compose children via Cert.map
   node   run  s (rows)  ─▶  Cert.foldSound out Sem+ children's step-soundness
```

Two properties make this a *certified* compiler rather than a code generator that hopes:

- **The instruction set is a fixed, already-proven, generic lemma library** (§1.1, §1.2). The
  generated proof is a TERM built by chaining `mkApp`/`Cert.map`/`bridge` — it either typechecks in
  the kernel or the elaborator errors. There is no per-example tactic search at this level, hence no
  "proves the cases I tested, `sorry`s the rest" failure mode *for the abstract layer*.
- **The output object is the same `Cert R` the substrate already reasons about**, so the generated
  theorem's *statement* is expressed in the vocabulary the soundness lemmas already close. The
  compiler never invents a new soundness obligation; it instantiates existing ones.

The elaborator's three mechanical jobs (per requirement D):
1. **emit the def** `def <name>_air : <AirType> := <term built from the spec AST>` — via `Qq` typed
   term construction, or a `macro` that expands to the definition. The Handlebars `renderRules` is
   the hand-rolled precedent: a recursion producing the object.
2. **emit the theorem** `theorem <name>_sound : <refinement statement>` whose PROOF TERM is built by
   the same recursion, composing per-constructor soundness lemmas. This is the interesting part
   (§3).
3. **add both to the environment** — `Lean.Elab.Command.elabCommand` + `addDecl` / `addAndCompile`
   for the def, then a second `addDecl` for the theorem, type-checked by the kernel on insertion.

---

## 3. The DSL — what specs are the input

Start with what dregg HAS decision procedures and `Cert`/acceptance-as-cert instances for. Concrete
initial `SpecAST`:

```
inductive SpecAST
  | dfa    (δ) (q₀) (accept)              -- Crypto/Dfa + DfaAsCert.delta
  | vpa    (M) (q₀) (accept)              -- Crypto/Vpa + VpaAsCert.R_vpa
  | guard  (φ : Pred)                     -- Crypto/PredicateKernel; the Pred-alphabet guard
  | rel    (R) (start) (goal)             -- any inductive relation with `bridge R` (Hypergraph/CFG)
  | seq    (SpecAST) (SpecAST)            -- composition via Cert.map
```

Rationale for these leaves — each already has the machinery the compiler needs to *cite*:
- `dfa` / `vpa` — `DfaAsCert` / `VpaAsCert` give `..._as_cert` and `..._reduces` verbatim; the
  compiler's DFA case is essentially "name and apply `dfaAccepts_reduces`".
- `guard φ` — the `Pred` alphabet and its decision procedures already drive the
  `Predicates*Emit`/`Predicates*Refine` family and the guarded-grammar work
  (`HandlebarsGuarded*`). The guard rung's acceptance-as-cert is the predicate analogue of
  `DfaAsCert`.
- `rel R start goal` — the escape hatch to the FULL generality of `Hypergraph.bridge`: any inductive
  reduction relation the user supplies with a relation-preserving structure. `cfg_parse_via_reduction`
  is the worked instance.
- `seq` — the first genuine COMPOSITION node, discharged by `Cert.map` (transport one config space
  into a simulating one) or list concatenation of chains. This is the constructor that proves the
  compiler *composes* rather than just dispatching a single leaf.

The DSL is deliberately the intersection of "has a `Cert` story" and "is small"; it grows by ADDING
a leaf + its one `..._as_cert` lemma, which is exactly the per-file cost `DfaAsCert`/`VpaAsCert`
already pay by hand.

---

## 4. The proof-gen strategy (the interesting core)

The refinement proof is generated compositionally, assembled from per-constructor lemmas. Grounded in
the ACTUAL lemmas:

**Leaf.** For `dfa δ q₀ accept`, the generated fragment is a proof of
`DfaAccepts δ q₀ accept trace → ∃ first last, … ∧ ReflTransGen delta first last`, and the proof term
IS `dfaAccepts_reduces δ q₀ accept trace` (or `dfaAccepts_as_cert` if the target keeps the `Cert`
form). No search: the metaprogram emits `Expr.app`s of an existing theorem to the spec's components.
`guard`, `rel` are the same shape at their own `..._as_cert` / `bridge`.

**Sequential node.** For `seq s₁ s₂`, the compiler has child proofs `p₁ : Cert R₁ x₁ y₁ c₁`,
`p₂ : Cert R₂ x₂ y₂ c₂`. It emits a relation-preserving map `f` (into a common config space) and
applies `Cert.map f hf` to transport, then composes the chains. The `hf : ∀ x y, R x y → S (f x) (f
y)` obligation is itself a small generated term (or, at first, a required user-supplied instance —
see risks). `Cert.map`'s existence and non-vacuity (`cert_map_nonvacuous`) are the ground truth this
rests on.

**Multi-row / run node.** For a spec whose semantics is a per-row invariant folded along a trace,
the compiler emits a `Cert.foldSound out Sem hstep` application. It must generate three inputs:
- `out : Config → List β` (what each row contributes — e.g. `rowRules`),
- `Sem : List β → Config → Prop` (the carried invariant — e.g. `Replay dyck rs row.inp row.stk`),
- `hstep : ∀ x y, R x y → ∀ rs, Sem rs y → Sem (out x ++ rs) x` (one-step soundness).

`ReplayAsCert.mrun_imp_replay_via_fold` is the EXACT worked precedent: `out := rowRules`, `Sem` the
replay predicate, `hstep := mstep_step`, and the multi-row induction is the ONE `Cert.foldSound`
call. The compiler's job for a run node is to synthesize `out`/`Sem` from the spec and hand
`Cert.foldSound` the per-step lemma; the induction it does NOT have to generate — the library owns
it. **That is the leverage:** the hardest part of the Dyck proof (the multi-row induction) is already
a reusable lemma; the generator supplies only the parts that vary.

**Consistency tooth (optional, high-value).** Mirror `materialized_agrees`: emit a `rfl`-checked
equation that the generated certificate, fed through the abstract soundness, equals the spec's own
existence proof. Where it holds by proof-irrelevance it is free and it is the strongest possible
statement that the generated object is not a decorative mirror.

**Why this resists the brittle-proofgen failure at the abstract level.** The generated proof is a
composition of applications of a closed set of generic, kernel-checked lemmas. It contains no `simp`
call whose success depends on the example, and no metavariable left for a tactic to discharge by
search. If the composition typechecks, it is a real proof of the stated theorem; if it doesn't, the
elaborator throws — it cannot silently `sorry`. (The generator's OWN correctness is a separate
matter — see §6 — but a generated *green* is a genuine green.)

---

## 5. The layers — abstract vs concrete-AIR (be honest)

This is the load-bearing distinction.

### Layer A — ABSTRACT (tractable to auto-generate; the MVP lives here)
- Output: a `Cert R`-shaped constraint object (or a thin record around it).
- Soundness: `bridge` / `Cert.map` / `Cert.foldSound` + the per-leaf `..._as_cert` lemmas.
- Proof-gen: compositional application of a FIXED generic library. No field prime, no row layout, no
  mod-`p` reasoning, no decode.
- Evidence it is tractable: `DfaAsCert`/`VpaAsCert`/`ReplayAsCert` are that proof, written by hand,
  short, and structurally identical — i.e. mechanical. The generator automates the writing of these
  siblings.

### Layer B — CONCRETE felt/row AIR (much harder; NOT the MVP)
- Output: a real `EffectVmDescriptor2` (columns, gates, window constraints, chip lookups),
  `emitVmJson2`-serialized and byte-pinned, loaded by Rust.
- Soundness: a `dyck_sat_imp_row_valid`-shaped `Satisfied2 desc trace → RowValid`, over ℤ mod `p`,
  with primality splits, canonicality lifts, and gated field extraction — THEN the abstract assembly
  of §5A on top, THEN the decode glue.
- Why auto-gen is hard here, concretely:
  1. The row proof is bespoke per constraint set; it is NOT the application of a closed generic
     library. The Dyck proof builds ad-hoc combinators (`gc`, `wt`, `dd`) inline. A generator needs
     these EXTERNALIZED into a reusable, spec-indexed lemma set — which does not yet exist.
  2. `decode` is open even by hand (§7 residual). You cannot auto-generate a proof of a theorem no
     one has stated a stable form of.
  3. The emit gate + byte-pin + `descriptor_by_name` wiring is its own discipline; a concrete
     arithmetizer must generate the descriptor AND its `#guard` AND keep it faithful to Rust — and
     for Dyck that faithfulness is currently a hand transcription, not a machine equality.

**The MVP targets Layer A first, unambiguously.** Layer B is the roadmap's second act, gated on a
de-risking experiment (§7).

### The A↔B bridge (the interesting seam, stated not solved)
The dream is: generate the Layer-A abstract cert AND a Layer-B descriptor from ONE spec, plus a proof
that the descriptor REFINES the abstract cert (`Satisfied2 desc trace → ∃ c, Cert R (decode trace)
… c`). Then abstract soundness composes on top for free. Today that bridge is exactly the
hand-written `dyck_sat_imp_row_valid` + the missing decode. Auto-generating the bridge is the crux of
Layer B and the honest frontier of the whole idea.

---

## 6. The MVP slice — the smallest thing that proves the elaborator does BOTH

**MVP-0 (validates the mechanism itself).** `#arithmetize` given a concrete DFA (δ, q₀, accept as
Lean values) adds to the environment:
- `def <name>_air := …` a `Cert delta`-shaped object over the DFA's step relation, AND
- `theorem <name>_sound : DfaAccepts δ q₀ accept trace → ∃ first last, first.state = q₀ ∧ accept
  last.next ∧ ReflTransGen delta first last`, with proof term `dfaAccepts_reduces …`.

This is deliberately the *smallest* thing: the soundness lemma already exists, so MVP-0 proves the
one novel mechanical capability — **an elaborator that emits BOTH a checked `def` AND a
kernel-checked `theorem` in one command** — without any new mathematics. Acceptance gate: the added
theorem's *statement* is the real refinement (not `P → P`), it is `#assert_axioms`-clean, and a
mutated spec (wrong `accept`) makes the generated theorem FAIL to typecheck (the canary that the
proof is load-bearing, per the project's proof-integrity discipline).

**MVP-1 (validates composition).** Extend `SpecAST` to `{ dfa | guard | seq }` with `seq` discharged
by `Cert.map`. Now the generator recurses on a 2-level AST and ASSEMBLES a proof from two child
proofs + one composition lemma. Acceptance gate: a `seq` of two distinct leaves produces a theorem
whose proof genuinely uses both children (mutating either child's spec breaks the green).

**MVP-2 (validates the fold).** One `run`-shaped spec whose refinement the generator discharges via a
single `Cert.foldSound` call, re-deriving (by generation) the statement `mrun_imp_replay_via_fold`
proves by hand. This closes the loop to the heaviest abstract machinery and shows the generator can
drive the multi-row induction lemma.

All three are Layer A. None touches felts, rows, `emitVmJson2`, or decode.

---

## 7. Hard parts, honest risks, and the first thing to de-risk

**Robust proof-gen (the "green on tested cases, `sorry` elsewhere" trap).** Mitigated at Layer A by
construction: the generator emits compositions of a closed generic lemma set, so a generated proof is
a real proof or a hard elaboration error — never a silent hole. The residual risk is the GENERATOR's
own coverage: a spec shape it doesn't handle should ERROR, not emit a vacuous theorem. Guard: forbid
the generator from ever emitting `sorry`/`admit`/`trivial`-into-a-metavariable; require every leaf to
resolve to a named library lemma or fail; ship an adversarial test that a malformed/mutated spec
yields a red, not a vacuous green (the project's standing lesson: a `P → P` builds green and reports
success).

**The abstract↔concrete-AIR bridge (§5).** The real wall. Two sub-risks: (a) the row-level refinement
is bespoke, not library application; (b) decode is unsolved by hand. Do NOT let the MVP's Layer-A
success be described as if it were Layer B — that is the project's recurring "describe at current
resolution, not intended" sin. A generated Layer-A theorem says "the abstract cert refines the spec",
NOT "the deployed felt AIR the prover runs refines the spec".

**Metaprogramming friction.** `Qq` typed-term construction, universe/implicit handling in
`Lean.Elab.Command`, and `addDecl` type-checking are all standard but fiddly; expect friction in
generating well-typed `Expr`s for the composition nodes (the `hf` relation-preserving map in
`Cert.map` is the first place the generator must SYNTHESIZE a term, not just apply one). This is
schedule risk, not feasibility risk.

**Novelty calibration (say it plainly).** Proof-producing / certifying compilation is a KNOWN
paradigm — CompCert-style translation validation, certifying algorithms, proof-carrying code. A
per-instance generated-and-checked refinement is not a new proof theory. The genuinely fresh parts
are narrow and worth stating precisely: (1) the ZK-**arithmetization** application — generating an
AIR/constraint object together with its refinement in the same assistant that authors the AIR; (2)
the proof-carrying-vs-"high-certainty" positioning — replacing a degree-of-belief with a checked
per-instance theorem. Do not oversell it as a general breakthrough; it is an integration of a known
paradigm into dregg's Lean-authored-AIR discipline, and its value is that the discipline already has
the generic soundness library (§1.1) that makes the generation compositional rather than bespoke.

**Critical-path unknown to de-risk FIRST (before any Layer-B work).** *Is there a finite, composable,
spec-indexed library of row-level refinement lemmas such that a NEW descriptor's SAT⇒SEM proof is
ASSEMBLY, not bespoke tactic work?* The Dyck proof's inline combinators (`G`/`W`/`gc`/`wt`/`dd`/
`bin_of_gate`/`range_of_gate`) are a hint that such a library is latent. The experiment: refactor
`dyck_sat_imp_row_valid`'s per-field extraction into an externalized, reusable lemma set, then attempt
to assemble a SECOND descriptor's row refinement from that same set BY HAND. If a human can assemble
the second one from a fixed library, a metaprogram can generate it; if the second one still needs new
bespoke tactics, Layer B auto-gen is not yet feasible and the honest deliverable stays at Layer A.

---

## 8. Scope

- **MVP (Layer A, MVP-0 → MVP-2): weeks.** MVP-0 is small (name-and-apply an existing lemma inside an
  elaborator that adds a def + a theorem). MVP-1/MVP-2 add one composition lemma and one fold each.
  The dominant cost is metaprogramming friction (`Qq`, `Command` elab), not mathematics — the
  soundness library exists.
- **Full (Layer B, concrete felt AIR + refinement + emit gate + decode): months, and gated.** Blocked
  on (a) the §7 de-risking experiment succeeding, (b) a stated, stable `decode`/whole-parse theorem
  form (open by hand today), and (c) generating the `emitVmJson2` + `#guard` + `descriptor_by_name`
  wiring faithfully. If the §7 experiment FAILS, the honest scope caps at Layer A plus a hand-written
  A↔B bridge per descriptor — still valuable, but not an auto-generated concrete arithmetizer.

**One-line recommendation.** Build the Layer-A proof-producing arithmetizer (weeks, low risk, real
result: generated + checked refinement theorems for DFA/guard/seq specs), and in parallel run the §7
row-lemma-library experiment as the single gate that decides whether the concrete-AIR act is a
project or a research bet. Describe the Layer-A result at Layer-A resolution.
