# DESIGN — Bridge Synthesis (Arithmetizer MVP-2)

**Status:** design scout, READ-ONLY. NO Lean written. Grounded in the committed tree.
**Date:** 2026-07-23.
**Substrate:** this is Lean-authored AIR. Everything below emits/composes proofs about the
`EffectVmDescriptor2` produced by `TypedLinearPredicateDescriptorIR2.descriptor`, a Lean function.
Rust hand-writes none of it.

**Files read in full:**
- `metatheory/Dregg2/Crypto/Arith/ArithmetizeTypedPredicate.lean` (the MVP-1 command)
- `metatheory/Dregg2/Metatheory/TypedLinearPredicateDescriptorIR2.lean` (the Layer-B compiler +
  `Program.Holds` semantics + the hand-written `InterchainRung` witness)
- `metatheory/Dregg2/Metatheory/DirectLogicOptimizerCertificate.lean` (`Formula` + `Formula.Holds`)

---

## 0. The one-sentence claim, and the honest version

**Aspiration.** `#arithmetizeTypedRefinement foo := prog refines Spec via bridge` today requires the
caller to hand-write `bridge : ∀ input, prog.Holds input ↔ Spec input`. Synthesize the bridge and the
arithmetizer takes a program and emits the live descriptor **plus** its spec-level soundness with no
hand proof.

**Honest version, after reading the tree.** "The bridge" is not one obligation, it is a *composition
of three*, and only the first two are synthesizable. Reading `InterchainRung.program_holds_iff`
(the one fully-worked hand bridge in the tree, IR2 lines 1094-1099) makes the seam visible:

```
program.Holds (inputOf tag payload)   ↔   Reaches tag payload
└─────────── (A) Formula fold ──────────┘   └── caller prose ──┘
             (B) per-atom canonicalization
```

`program.Holds input` unfolds to `Formula.Holds (p.AtomTruth input) p.source`, i.e. the Boolean
combination `source` folded over atom-truth leaves `(atomTerms a).evalField input = 0`. Turning that
into `Reaches tag payload := tag = 0 ∨ (payload ≠ 0 ∧ (tag = 1 ∨ tag = 2))` is **two mechanical
steps**: (A) fold the AST `source`, (B) solve each affine atom (`input0 + (-1) = 0 ↔ input0 = 1`).
Both are what the hand `simp` at lines 1096-1099 does. The **third** step — linking that canonical
form to *arbitrary user prose* — is `encoded_program_exact` (lines 1109-1125), a bespoke 14-line
case analysis onto the external verified decision `reachedConsensusCore`, and it is **not**
synthesizable because the target is unstructured prose the elaborator cannot read.

MVP-2 synthesizes (A)+(B). It does **not** synthesize (C). When the caller lets their spec *be* the
canonical form, (C) collapses to `Iff.rfl` and the bridge is fully automatic.

---

## 1. Ground truth — the semantics the synthesis reflects over

From IR2 and `DirectLogicOptimizerCertificate`:

```lean
inductive AffineTerm (m : Nat) | const (v : Int) | input (i : Fin m) | neg | add   -- affine, no ×
inductive Formula   (n : Nat)  | atom (a : Fin n) | top | bot | not | and | or     -- Boolean AST

structure Program (pub sec atoms) where
  atomTerms : Fin atoms → AffineTerm (pub + sec)
  source    : Formula atoms

Program.AtomTruth p input a : Prop := (p.atomTerms a).evalField input = 0        -- leaf = affine = 0
Program.Holds    p input    : Prop := Formula.Holds (p.AtomTruth input) p.source -- fold of ∧/∨/¬

Formula.Holds truth : Formula n → Prop        -- atom↦truth a, top↦True, bot↦False, not↦¬, and↦∧, or↦∨
AffineTerm.evalField input : AffineTerm m → BabyBear    -- BabyBear := ZMod 2013265921, symbolic input
```

Two structural facts make this reflectable **at elaboration** and dodge the kernel:
- `source : Formula atoms` and each `atomTerms a : AffineTerm m` are **concrete syntax trees** known
  as `Expr` values when the command runs. Walking them is a meta-computation over constructors, never
  a kernel reduction over `ZMod`.
- `input : Fin (pub+sec) → BabyBear` is a **bound variable** in the bridge statement. Nothing about
  the field value is ever reduced; `evalField input _` stays a symbolic polynomial.

---

## 2. Why the obvious `decide` route is the 64GB trap — and what reflection means here

The forbidden route, spelled out. To auto-prove `Holds ↔ Spec` by `decide` you would put a
`Decidable` instance on a `ZMod 2013265921` predicate and let the kernel reduce it. That fails two
ways, both bad:

1. **It cannot even run on the bridge.** The bridge quantifies `∀ input`. `decide` needs a *closed*
   proposition; a symbolic `input` has nothing to reduce. So `decide` is inapplicable to the actual
   obligation — it only "works" if you first monomorphize to a concrete input.
2. **Monomorphized, it detonates.** `Decidable ((x : BabyBear) = 0)` is `ZMod.decEq`, which is
   `Fin 2013265921` equality. Forcing it drives the kernel to WHNF-reduce `ZMod 2013265921` arithmetic
   — `Fin.add`/`Fin.mul` carry a `Nat.mod _ 2013265921` on ~31-bit numerals, and the instance +
   `Nat.rec` unfolding blows the term up. This is the measured 64GB / 20-min OOM the resource
   discipline forbids. **Do not build a `Decidable` instance on any `ZMod p` predicate and `decide`
   it. Do not `@decide`/`of_decide_eq`. Do not `#eval`/kernel-reduce `evalField` at a concrete input.**

**The reflection route is the opposite of value-reduction: it reflects the SYNTAX, not the field
value.** The codebase already contains the exact discipline, twice:
- `evalBit` + `evalBit_one_iff` (IR2 lines 380-423): a structural evaluator over the `Formula` AST
  with an inductive soundness lemma — reflection on syntax, field stays symbolic. (This one lives on
  the field-witness side, not the bridge, but it is the *pattern* MVP-2 copies.)
- `two_ne_zero`/`three_ne_zero` (IR2 lines 1082-1092) prove modular facts about the 2-billion modulus
  via `ZMod.intCast_eq_intCast_iff` + `norm_num [Int.ModEq]` — **the symbolic route that never
  reduces a `Fin 2013265921`.** This is the proof the tree already prefers over `decide`, and the
  synthesizer emits proofs of exactly this weight.

### The critical honest correction to the task's framing

The task proposes `holdsBool : Program → (Fin n → ZMod p) → Bool` with `holdsBool = true → Holds`.
**A `Bool`-valued evaluator over `ZMod p` inputs does not help the bridge, and if forced it *is* the
trap.** To emit a `Bool` from `evalField input = 0` you must decide field-zero, which for symbolic
`input` is stuck (no `Bool` to compute) and for concrete `input` is the `ZMod.decEq` detonation. Value
reflection buys nothing here because the bridge is `∀`-quantified over a symbolic field.

The correct reflective object is **an `Iff`-proof synthesized by structural recursion on the syntax**
(`Formula`, `AffineTerm`), producing a *symbolic* canonical `Prop`, with the field variable never
reduced. Reflection is over the AST at elaboration; the "cheap Bool computation" the task wants
exists only in the shape-classifier that *picks which canonicalization lemma to apply per atom*
(over `AffineTerm`/`Nat`/`Fin` constructors — no `ZMod`), not in a field-value evaluator.

*(A genuine computable `Bool` evaluator does exist and is worth building as a **separate** capability
— see §5 — but over `Int` via the already-present `evalInt`, for cheap concrete-witness `#guard`
checks, and only one-way up to the modulus-alias frontier. It is not a bridge synthesizer.)*

---

## 3. The synthesis design

Two synthesized objects, composed. Both emitted by an elaborator that walks the `Program`'s concrete
syntax and adds kernel-checked theorems via `addDecl`, exactly as MVP-1 already does.

### (A) `foo_fold` — the Formula fold, synthesized by structural recursion on `source`

Emit `foo_fold : p.Holds input ↔ ⟨Boolean combination of (atomTerms a).evalField input = 0⟩`, where
the RHS is generated by recursing on the concrete `source : Formula atoms`:
`atom a ↦ (atomTerms a).evalField input = 0`, `top ↦ True`, `bot ↦ False`, `not ↦ ¬`, `and ↦ ∧`,
`or ↦ ∨`. The proof is definitional: `Program.Holds`, `Program.AtomTruth`, `Formula.Holds` unfold by
`rfl`/congruence over the AST. **Cost:** linear in AST size, no `ZMod` touched. This step is *total
and exact* — it never approximates.

### (B) `foo_atoms` — per-atom canonicalization, fixed `linear_combination` schema

For each atom `a`, emit `(atomTerms a).evalField input = 0 ↔ ⟨solved form⟩` by a shape-directed
tactic:
- `eqConst i k` (= `.add (.input i) (.const (-k))`) → `input i = k`, proof
  `constructor <;> intro h <;> linear_combination h` — **verbatim the existing `add_neg_one_zero_iff`
  / `add_neg_two_zero_iff`** (IR2 lines 1076-1080), which are `linear_combination`, symbolic, cheap.
- `eqInput i j` → `input i = input j`, same schema.
- general affine `Σ cᵢ·inputᵢ + d`: no field-safe pivot in general (dividing by `cᵢ` needs `cᵢ`
  coprime to `p`), so canonicalize to `ring_nf` normal form or, in the worst case, to itself
  (`Iff.rfl`). Still Holds-side, felt-free, symbolic. **The canonicalizer is total; it is
  *simplifying* only on the recognized shapes** (which is every atom in every witness in the tree —
  `eqConst`, `input`).

A tiny `Bool`/meta classifier over the `AffineTerm` constructors selects the branch. No `ZMod`
reduction anywhere; every emitted proof is a `linear_combination`/`ring` term of the same weight as
the hand lemmas already in the file.

### Compose → `foo_holds_canon` and the new default-spec command

`foo_holds_canon : p.Holds input ↔ CanonicalForm p input` = `(A).trans (congr of B over the fold)`.
Then a new command needing **zero caller bridge**:

```
#arithmetizeTypedCanonical foo := prog
  -- emits everything #arithmetizeTypedPredicate does, PLUS
  foo_holds_canon  : ∀ input, foo_program.Holds input ↔ CanonicalForm foo_program input
  foo_spec_sound   : LiveRefinesSpec foo_program (CanonicalForm foo_program)  -- via liveRefinesSpecOf ∘ foo_holds_canon
  foo_spec_exact   : LiveExact       foo_program (CanonicalForm foo_program)  -- via liveExactOf       ∘ foo_holds_canon
```

`CanonicalForm foo_program` is the synthesized spec — a legible field-equation predicate, not
`P → P`, not a felt/trace statement. The existing `liveRefinesSpecOf`/`liveExactOf` combinators
(IR2-consumer lines 181-198 of the MVP-1 file) are reused unchanged; only their `bridge` argument is
now `foo_holds_canon` instead of a hand term.

### (C) stays manual — and stays honest

`#arithmetizeTypedRefinement foo := prog refines Spec via bridge` remains for callers who want their
**own prose** spec (`reachedConsensusCore`, a game rule, …). Their obligation shrinks from
`Holds ↔ Spec` to `CanonicalForm ↔ Spec` (rewrite by `foo_holds_canon`), i.e. the fold and the affine
solving are already discharged. When the prose *is* the canonical form, it is `Iff.rfl`.

---

## 4. Measurement — generated-vs-hand, from the two worked bridges in the tree

| Bridge (hand, today) | hand lines | simp-set / lemmas | under MVP-2 synthesis |
|---|---|---|---|
| `alphaBridge` (ArithmetizeTypedPredicate 296-299) | 4 (one `simp`) | ~15 names + shared `add_neg_one_zero_iff` | **0** — `CanonicalForm = AlphaSpec` emitted; `alpha_spec_sound` free |
| `betaBridge` (315-323) | 4 (one `simp`) | ~15 names | **0** |
| `program_holds_iff` (IR2 1094-1099) | 6 (one `simp`) | 16 names + `add_neg_one/two_zero_iff` | **0** — RHS `Reaches` is exactly `CanonicalForm program` |
| `encoded_program_exact` (IR2 1109-1125) — the **prose Spec link** | 14 (case split) | `two_ne_zero`,`three_ne_zero`,`intCast_eq_intCast_iff`,… | **stays manual** (arbitrary external prose) — but now atop `foo_holds_canon`, so its `Reaches`-fold is free |
| `modulus_{tag,payload}_alias_frontier` (IR2 1131-1154) | ~10 each | the range/alias wall | **stays a labeled residual** — never auto-closed |

So for the three `Holds ↔ canonical` bridges the tree hand-writes today, synthesis takes **~14 hand
lines → 0**. The prose link and the modulus frontier are correctly *not* eliminated. The pilot
number to report on landing: **3 of 3 in-tree `Holds`-side bridges auto-discharged; `alpha`/`beta`/
`gamma` witnesses lose their hand `simp` and shared `add_neg_*` lemmas; `encoded_program_exact`'s
`Reaches`-fold portion is replaced by a `rw [foo_holds_canon]`.**

No build was run for this design (read-only lane; running `decide`/reductions is the very trap under
study). All costs above are read off the existing kernel-checked hand proofs, whose weight the
synthesized terms match exactly (`linear_combination` / `Formula.Holds` unfolding / `norm_num
[Int.ModEq]`).

---

## 5. Bonus capability (separate, not the bridge): concrete-witness `Bool` checker over `Int`

`AffineTerm.evalInt` (IR2 line 57) is already computable over `Int`. A `holdsBoolInt : Program →
(Fin n → Int) → Bool` folding `evalInt input a == 0` through the AST, with
`holdsBoolInt p input = true → (|values| < p) → p.Holds (Int.cast ∘ input)`, gives cheap `#guard`
witness-checking for *concrete* candidate inputs — useful for canaries. It is **one-way** and gated by
the modulus-alias frontier (`modulus_*_alias_frontier` is exactly why: integer-zero ≠ field-zero past
`p`). It is NOT a bridge synthesizer and must never be sold as one. Keep it over `Int` (never `ZMod`)
so the `Bool` actually reduces without the modulus trap.

---

## 6. Synthesizable vs manual — the honest ledger

| Obligation | Status | Why |
|---|---|---|
| `Holds ↔ CanonicalForm` — Formula fold (A) | **SYNTHESIZABLE, exact** | definitional unfolding over concrete `source` |
| `Holds ↔ CanonicalForm` — affine atom solving (B) | **SYNTHESIZABLE** on recognized shapes; total elsewhere | fixed `linear_combination` schema, symbolic |
| `CanonicalForm ↔ arbitrary prose Spec` (C) | **MANUAL** (often `Iff.rfl`) | equivalence of two arbitrary `Prop`s is undecidable; prose carries no readable structure |
| integer/field range & alias canonicalization | **RESIDUAL, labeled** | `modulus_*_alias_frontier`; needs a range gadget, out of bridge scope |
| descriptor/FRI/witness-gen floor | **inherited, unchanged** | every descriptor-level theorem already carries it |

**Is `Holds ↔ Spec` even the right thing to auto-derive?** No — not in that form. The right
synthesized object is `Holds ↔ CanonicalForm` (the program's own canonical field-equation reading),
with the Spec link left as a *small, felt-free, fold-free* manual `Iff` — or eliminated entirely by
letting `CanonicalForm` **be** the spec. That is the honest MVP-2.

---

## 7. Effort — days, not weeks

- (A) Formula-fold `Iff` synthesizer (meta-recursion on `Formula`, `evalBit` is the template): **1-2 days.**
- (B) per-atom canonicalizer + `AffineTerm` shape classifier + fixed `linear_combination` schema: **1-2 days.**
- `#arithmetizeTypedCanonical` command + `foo_holds_canon`/spec wiring + positive/negative canaries
  (reuse the MVP-1 `#guard_msgs` armed canary): **1 day.**

**MVP-2 total: ~3-5 days, under a week.** What is *weeks/months* is explicitly out of scope: the
concrete-AIR decode glue and the range/alias canonicalization gadget behind
`modulus_*_alias_frontier`. Those are named residuals, not part of bridge synthesis.

---

## 8. Recommendation — the concrete next move

Build **(A) the Formula-fold `Iff` synthesizer** first, as a standalone `elab`/meta term-builder that,
given a `Program` value, produces `p.Holds input ↔ CanonicalForm p input` and kernel-checks it. Pilot
it by **regenerating `InterchainRung.program_holds_iff`**: the synthesized RHS must be
definitionally/`simp`-equal to the hand `Reaches`, and the synthesized proof must be `#assert_axioms`-
clean and pass the same negative canary (ALPHA-statement-from-BETA-compilation rejected). That single
pilot proves (A)+(B) end-to-end against a real hand bridge, quantifies "14 → 0", and de-risks the
command wiring — without ever constructing a `Decidable` instance on `ZMod 2013265921`.
