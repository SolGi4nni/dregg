# OpenTheory → Lean 4 importer: research + design

Status: scoping doc + working first-slice spike (2026-07-26).
Motivation: import a verified EVM (**Verifereum**, HOL4) into Lean as the trusted
core of a verified zkEVM. The importer is built to be **reusable for the whole
HOL family** (HOL4 / HOL Light / ProofPower), not a one-off Verifereum shim.

Guiding constraints (house law):
- **Kernel-anchored.** The importer is *untrusted*. Every imported theorem is a
  native Lean `Expr` handed to the Lean kernel; a mistranslation fails to
  type-check. The TCB stays Lean-only.
- **House-law-clean.** No axioms beyond dregg's existing classical set
  (`propext`, `Classical.choice`, `Quot.sound`); enforced with `#print axioms`
  the same way `metatheory/AxiomProbe.lean` does.

---

## STEP 1 — Does it already exist? Verdict: **GAP.**

There is **no OpenTheory→Lean, HOL4→Lean, or HOL-Light→Lean importer**, mature or
otherwise. Every proof-*import* sink for the HOL ecosystem targets Isabelle,
Coq/Rocq, or Metamath. Lean is present only as a *source* (Lean→Dedukti) or as a
*verifier of a different format* (Metamath), never as an import *sink* for HOL.

What exists, and which direction it runs:

| Prior art | Direction | Lean sink? | Notes |
|---|---|---|---|
| **OpenTheory** article format + `opentheory` tool ([gilith](https://www.gilith.com/opentheory/), [article spec](https://www.gilith.com/opentheory/article.html)) | HOL ⇄ article | — | The interchange format itself. HOL4/HOL-Light/ProofPower all read & write it. This is the on-ramp we target. |
| **xrchz/isabelle-opentheory** ([repo](https://github.com/xrchz/isabelle-opentheory)) | OpenTheory → Isabelle/HOL | no | Closest cribbable design: a stack-machine replay of articles into a host kernel. Single-threaded, slow, but the reference for *replay-into-a-host*. |
| **HOL-Light → Isabelle/HOL "rebooted"** ([Tourret et al.](https://members.loria.fr/STourret/papers/isabelle24translation.pdf)); **Obua/Skalberg "Importing HOL into Isabelle/HOL"** | HOL Light → Isabelle | no | Patches the HOL Light kernel to log its inference trace, then replays. Same shape as what we want, wrong sink. |
| **hol2dk** ([Deducteam](https://github.com/Deducteam/hol2dk)) + **coq-hol-light** ([repo](https://github.com/Deducteam/coq-hol-light)) | HOL Light → Dedukti/Lambdapi → **Coq/Rocq** | no | Dumps HOL-Light proofs, translates via the λΠ-calculus-modulo. Ported the 20k-theorem Multivariate library to Rocq. Lambdapi's `export` targets are **Dedukti, Coq, HRS, CPF — not Lean** ([Lambdapi CLI](https://lambdapi.readthedocs.io/en/latest/options.html)). |
| **lean2dk / Lean4Less** ([lean2dk](https://github.com/Deducteam/lean2dk), [Lean4Less](https://github.com/Deducteam/Lean4Less)) | **Lean → Dedukti** | — | Opposite direction. No Dedukti→Lean back-translation exists, so hol2dk cannot be "finished" into Lean via Dedukti today. |
| **mm-lean4** ([digama0](https://github.com/digama0/mm-lean4)) | Metamath *checked in Lean* | (verifier) | Mario Carneiro's Metamath **verifier** in Lean 4 — checks `set.mm`, does **not** import Metamath theorems as Lean `theorem`s. Precedent for "kernel-adjacent tooling in Lean", not an importer. |
| **Candle** ([verified HOL checker](https://www.sciencedirect.com/science/article/pii/S2352220820300158)) | verified OpenTheory article checker (CakeML) | no | Precedent for a *verified* article replayer — relevant to the optional STEP-3 meta-theorem, not to Lean import. |

Adjacent facts worth stating plainly:
- **A Lean sink is absent across the entire chain.** Isabelle, Coq/Rocq, and
  Metamath each have HOL-ecosystem bridges; Lean has none. This is the gap.
- **The Dedukti hub does not reach Lean.** Lambdapi exports to Coq but not Lean,
  and the only Lean/Dedukti tool runs Lean→Dedukti. So we cannot piggyback on
  hol2dk; we build a **direct** OpenTheory→Lean replayer.
- OpenTheory is the right interchange layer precisely because HOL4 already
  *emits* it (Holmake `--ot`, see STEP 3), so we do not have to patch the HOL4
  kernel ourselves — Obua/Tourret had to patch HOL-Light; we inherit HOL4's
  logging kernel for free.

**Verdict: build it.** OpenTheory→Lean 4 is a genuine, unclaimed gap, and it is
the *reusable* choice: one importer covers HOL4, HOL-Light, and ProofPower,
because all three speak the article format.

---

## STEP 2 — The replay design

### 2.1 The article format (the thing we parse)

An OpenTheory article is a UTF-8 text file, **one command per line**, driving a
**stack machine** over a dictionary. There are **37 commands** in the current
format (v6) ([article spec](https://www.gilith.com/opentheory/article.html),
[command overview](https://page.mi.fu-berlin.de/rote/Software/OpenTheory/opentheory-commands.html)).
A line is: a **number** (pushes `Num`), a **"quoted string"** (pushes `Name`), or
a **command word**. The stack objects are:

```
Num | Name | List of objects | TypeOp | Type | Const | Var | Term | Thm
```

Command groups:
- **Literals / structure:** number, name, `nil`, `cons`, `hdTl`, `pop`.
- **Dictionary:** `def` (store top under a numeric key), `ref` (recall), `remove`.
- **Types:** `typeOp` (name→TypeOp), `opType` (TypeOp + list of Types → Type),
  `varType` (name→type variable).
- **Terms:** `const` (name→Const), `constTerm` (Const + Type → Term),
  `var` (Name+Type → Var), `varTerm` (Var → Term), `absTerm` (Var + Term → λ),
  `appTerm` (Term + Term → application).
- **Directives:** `version`, `pragma`.

### 2.2 The primitive inference commands (the theorems we replay)

These are the commands that produce/consume `Thm` objects. Semantics from the
[article spec](https://www.gilith.com/opentheory/article.html) (Γ, Δ = hypothesis
sets; ⊦ = HOL sequent). The **minimal HOL kernel** underneath is the 10-rule
HOL-Light core plus the two definition principles plus `axiom`; OT v6 also ships
`sym`/`trans`/`proveHyp`/`defineConstList` as first-class commands (derivable,
but logged directly for compactness).

| Command | Pops → Pushes | HOL inference | Lean realization |
|---|---|---|---|
| `refl` | Term *t* → Thm `⊦ t = t` | reflexivity | `mkEqRefl t` (`Eq.refl`) |
| `assume` | Term *φ* → Thm `{φ} ⊦ φ` | assumption | hypothesis fvar of type `φ` in the local ctx |
| `absThm` | Var *v*, Thm `Γ ⊦ t = u` → `Γ ⊦ (λv.t) = (λv.u)` | abstract congruence | `funext`-style: `mkLambdaFVars #[v] · ` over the eq, i.e. `funext (fun v => h)` |
| `appThm` | Thm `Δ ⊦ x=y`, Thm `Γ ⊦ f=g` → `Γ∪Δ ⊦ f x = g y` | application congruence | `Meta.mkCongr h_fg h_xy` (core `congr`) |
| `betaConv` | Term `(λv.t) u` → `⊦ (λv.t) u = t[u/v]` | β | `mkEqRefl` after whnf: `Eq.refl` typed at the β-redex (defeq) |
| `deductAntisym` | Thm `Δ ⊦ ψ`, Thm `Γ ⊦ φ` → `(Γ∖{ψ})∪(Δ∖{φ}) ⊦ φ = ψ` | mutual implication → eq | `propext ⟨fun hφ => …, fun hψ => …⟩` discharging the swapped hyps |
| `eqMp` | Thm `Δ ⊦ φ=ψ`, Thm `Γ ⊦ φ` → `Γ∪Δ ⊦ ψ` | eq modus ponens | `Eq.mp h_eq h_φ` (φ,ψ : Prop) |
| `subst` | Thm *θ*, subst `[[(tv,ty)…],[(v,tm)…]]` → instantiated Thm | type + term instantiation | substitute into the proof term: `Expr.instantiate`/`replaceFVar`, or `θ` applied to instantiated fvars |
| `sym` | Thm `Γ ⊦ t=u` → `Γ ⊦ u=t` | symmetry | `Eq.symm h` |
| `trans` | Thm `Δ ⊦ u=w`, Thm `Γ ⊦ t=u` → `Γ∪Δ ⊦ t=w` | transitivity | `Eq.trans h1 h2` |
| `proveHyp` | Thm `Δ ⊦ ψ`, Thm `Γ ⊦ φ` → `(Δ∖{φ})∪Γ ⊦ ψ` | cut / hyp discharge | substitute proof `Γ⊦φ` for the `φ` hypothesis fvar in `Δ⊦ψ` |
| `axiom` | List Γ, Term *φ* → Thm `Γ ⊦ φ`; record as assumption | external axiom | see §2.4 — must resolve to a *known* Lean theorem/axiom, never a fresh `axiom` |
| `defineConst` | Name *n*, Term *t* → Const *c*, Thm `⊦ c = t` | constant definition | Lean `def c := t` + its `rfl` defining equation `⊦ c = t` |
| `defineConstList` | Name list, Thm → Consts + defining Thm | mutual/tuple const def | a batch of Lean `def`s + their defining eqs |
| `defineTypeOp` | Name *n*, Name *abs*, Name *rep*, Name-list *A*, Thm `⊦ φ t` → TypeOp, Const *abs*, Const *rep*, Thm `⊦ (λa. abs(rep a)) = λa. a`, Thm `⊦ (λr. rep(abs r) = r) = λr. φ r` | type definition (carve a non-empty subset) | `Subtype φ` (+ its `Nonempty` from the witness Thm); `abs`,`rep` as the constructor/`.val`; the two round-trip theorems by `rfl`/`Subtype.ext` |
| `thm` | Term *φ*, List Γ, Thm → export `Γ ⊦ φ` | export | close over free vars, `addDecl` a Lean `theorem` — the **kernel checks here** |

### 2.3 The encoding (the trusted core, kept tiny)

HOL is classical **simple type theory** (Church). The map to native Lean 4:

- **`bool` ↦ `Prop`.** HOL propositions are Lean `Prop`s. HOL `⇔`/`=` at type
  `bool` becomes Lean `Eq` on `Prop` (with `propext` bridging to `Iff` where an
  `Iff` shape is wanted). *Subtlety:* HOL `=` is one polymorphic constant; at
  `bool` it must remain provably interchangeable with `Iff`. `deductAntisym`
  (which manufactures a `bool` equality from mutual entailment) is realized with
  `propext`; this is the single place the `bool↦Prop` choice is load-bearing.
- **`α → β` (HOL `fun`) ↦ Lean `α → β`.** Direct. `appTerm`↦application,
  `absTerm`↦`fun`. HOL is total, so no partiality mismatch.
- **`ind` (infinity) ↦ an infinite Lean type.** HOL's `ind` is an infinite type
  (axiom of infinity). Map it to a fixed carrier with a proof of infinitude —
  `Nat`, or a fresh opaque type carrying `Infinite`. The HOL infinity axiom is
  then discharged by Lean's `Nat`-based witness (no new axiom).
- **The choice operator `ε` / `@` ↦ `Classical.choice` / `Classical.epsilon`.**
  HOL's Hilbert choice becomes Lean's classical choice. `SELECT_AX`
  (`P x ⇒ P (ε P)`) is a Lean theorem over `Classical.epsilon_spec`.
- **Type definitions (`defineTypeOp`) ↦ `Subtype` (+ `Quotient` when needed).**
  HOL's `new_basic_type_definition` carves a non-empty subset `{x // φ x}` of an
  existing type with an `abs`/`rep` bijection onto it. Lean `Subtype φ` with
  `rep := Subtype.val` and `abs := fun r => ⟨r, proof⟩` gives exactly the two
  round-trip theorems; the non-emptiness witness Thm supplies the `Nonempty`
  needed to define `abs` on the whole representing type (HOL `abs` is total —
  off-predicate it is `Classical.choice`-junk, matching HOL's underspecification).
  Quotient constructions that HOL builds *on top of* `defineTypeOp` map to
  `Quotient`/`Quot` where an author used a quotient; the primitive itself is
  subtype-carving.
- **Constant definitions (`defineConst`) ↦ `def` + defining equation.** A Lean
  `def c := t` whose `⊦ c = t` is `rfl`.
- **Hypotheses (Γ).** An OT sequent `Γ ⊦ φ` becomes a Lean term with the members
  of Γ as **local `fvar` hypotheses**; `assume` introduces one, `deductAntisym`/
  `proveHyp`/`eqMp` discharge them by substituting a proof `Expr` for the fvar.
  At `thm`, remaining frees are closed with `mkForallFVars`/`mkLambdaFVars`.

How the Isabelle importer handles the same subtleties (cribbed): it replays into
the host kernel one primitive at a time, represents HOL `bool` as the host's
Prop-analogue, and realizes `new_basic_type_definition` with the host's typedef
package — confirming the `Subtype`/round-trip shape is the standard move.

### 2.4 The precise TCB

An imported theorem is trustworthy iff you trust:

1. **The Lean kernel.** It type-checks every `addDecl`. This is dregg's existing
   TCB — importing HOL adds nothing here.
2. **The encoding (§2.3).** The ~6 mapping decisions (`bool↦Prop`, `→↦→`,
   `ind↦`infinite carrier, `ε↦Classical`, `defineTypeOp↦Subtype`,
   `defineConst↦def`). These are *stated in Lean* and, in the strong version
   (STEP 3 follow-on), *proved sound*.
3. **The realizations of the ~16 commands (§2.2).** Each is a Lean term
   constructor. **A wrong realization cannot produce an unsound theorem — it
   produces an `Expr` the kernel rejects.** Demonstrated: claiming `1 = 2` while
   supplying a proof of `1 = 1` yields `(kernel) declaration type mismatch` — the
   import fails, it does not lie.
4. **The `axiom` command's resolution table.** This is the *one* place import
   can smuggle unsoundness, because `axiom` asserts `Γ ⊦ φ` with no proof. It
   MUST resolve each article axiom to an already-present Lean theorem (the three
   HOL axioms → their Lean discharges in §2.3), and **refuse** (hard error) any
   `axiom` command whose statement is not on a whitelist of discharged HOL
   axioms. An `axiom` that fell through to a fresh Lean `axiom` would be a
   silent-unsoundness / fail-open gate — forbidden, and caught by `#print axioms`
   showing an unexpected constant.

**TCB = Lean kernel + the encoding + the axiom whitelist.** The parser and the
16 rule realizations are *outside* the TCB: the kernel is their check.

### 2.5 Axiom cleanliness

HOL's three axioms map into Lean's classical set with **no additions**:

| HOL axiom | Lean discharge | Lean axiom used |
|---|---|---|
| extensionality (`ETA_AX`/funext) | `funext` | `propext`-free; `funext` is a theorem (from `Quot.sound`) |
| choice (`SELECT_AX`) | `Classical.epsilon_spec` | `Classical.choice` (+ `propext`) |
| infinity (`INFINITY_AX`) | `Nat` is `Infinite` | none (constructive witness) |
| `bool` two-valued / `propext`-shaped steps (`deductAntisym`) | `propext` | `propext` |

So every imported theorem depends on a **subset of `{propext, Classical.choice,
Quot.sound}`** — dregg's existing set. Enforced exactly as
`metatheory/AxiomProbe.lean` already does: a `#print axioms` line per imported
theorem, red if anything else (especially a stray `sorryAx` or an un-whitelisted
`axiom`) appears.

---

## STEP 3 — Scope, language, first slice

### 3.1 Language recommendation: **a Lean 4 metaprogram** (not an OCaml/Rust emitter)

Build the replayer as a Lean 4 metaprogram (`import Lean`, a small Lake project),
replaying articles into `Expr`s and committing via `addDecl`.

Why, over the alternative of an OCaml/Rust frontend that *emits Lean source*:
- **TCB.** The metaprogram hands terms straight to the kernel (`addDecl`). A
  source-emitter adds Lean's *parser + elaborator* to the trusted path and a
  serialization round-trip; the metaprogram's checked object is the raw kernel
  term. Smaller, sharper TCB — the house requirement.
- **Fidelity.** Article terms are already explicitly typed; elaboration would
  re-infer and can drift. Direct `Expr` construction is 1:1 with the article.
- **No source-gen ceremony.** No name-mangling, no import graph, no pretty-print
  ambiguity.
- Optional perf escape hatch: a *thin* OCaml/Rust **pre-parser/pre-tokenizer** for
  multi-hundred-MB articles is fine — but the replay and the kernel check stay in
  Lean. (The real HOL stdlib articles are large; parsing is the only place raw
  speed matters, and even that is likely fine in Lean.)

### 3.2 Effort estimate

- **First end-to-end (parse + core inference rules + `bool`/`→` encoding +
  `defineConst`):** ~1–2 weeks. The OT kernel is small and fully specified.
- **Full primitive coverage + `defineTypeOp`/`defineConstList` + `subst`/hyp
  bookkeeping + the axiom whitelist + `#print axioms` gate:** ~3–5 weeks.
- **Scaling to a real corpus (OpenTheory `base` stdlib, then Verifereum):**
  dominated by (a) article *volume* and replay performance, (b) the Verifereum
  compute blocker in §3.5 — not by kernel complexity.

### 3.3 First slice — **DONE, and now a real-article importer.**

`docs/opentheory-importer-poc/OTPoC.lean` — a self-contained Lean 4 metaprogram
(`import Lean`, **no Mathlib**; namespace `OTImport`) — has grown from the day-one
spike into an importer that replays a **real HOL4-emitted OpenTheory v6 article**
end-to-end, kernel-checked and axiom-clean. Command semantics follow the reference
reader (`HOL4 src/opentheory/reader/OpenTheoryReader.sml`), including exact pop
orders. Run it (Lean 4.30.0):
```
OT_ARTICLE=docs/opentheory-importer-poc/prodWitness.art \
  lean docs/opentheory-importer-poc/OTPoC.lean
```

**What now works:**
1. A **real v6 tokenizer + stack machine + dictionary** (`def`/`ref`/`remove`),
   objects `Num/Name/List/TypeOp/Type/Const/Var/Term/Thm`.
2. The **encoding**: `bool↦Prop`, `→↦→`, `ind↦Nat` (fixed infinite carrier),
   HOL type vars ↦ Lean `Type` fvars, HOL term vars ↦ interned fvars (HOL
   name+type identity), `=↦@Eq`, and the `Data.Bool` constants
   `T/F/∧/∨/¬/⇒/∀/∃` ↦ Lean `True/False/And/Or/Not/(imp)/(forall)/Exists`
   (Hilbert `select ↦ Classical.epsilon`).
3. **Primitive rules with full Γ (hypothesis) bookkeeping:** `refl`, `assume`,
   `appThm` (`AP_THM`∘`AP_TERM`∘`TRANS`), `absThm` (`funext`), `betaConv`
   (a *single* beta step), `eqMp` (`Eq.mp`), `sym` (`Eq.symm`), `trans`
   (`Eq.trans`), `deductAntisym` (`propext`, oriented exactly as the reader's
   `IMP_ANTISYM_RULE (DISCH c2 th1)(DISCH c1 th2) ⟹ c2=c1`), `proveHyp` (cut:
   substitute the minor proof for the discharged hypothesis fvar), `subst`
   (`INST_TYPE` **then** `INST`, run as **two sequential phases** — see the
   nominal-variable note below), `defineConst` (closed/monomorphic defs, inlined),
   `defineTypeOp` (**the type-definition primitive** — `Subtype φ` carving with a
   total `abs`/`rep` and the two round-trip theorems proved generically), and
   `thm` (closes free type/term vars **and each type var's `[Nonempty A]`
   witness**, `addDecl` — **the kernel checks here**).

   Two semantic subtleties were found and fixed the same way the earlier
   `betaConv`/`deductAntisym`/`subst` bugs were (reading the reader + article
   spec, then the kernel as the backstop):
   - **HOL every-type-is-nonempty is load-bearing.** A `bool`-requiring article
     asserts `!t.(!x:A.t)=t` and `? = \p. p(εp)`, and uses `select`; all three
     are FALSE / ill-typed in Lean over an *empty* `A`. So every HOL type
     variable is now introduced as `A : Type` **together with** an instance
     `[Nonempty A]`; `select`↦`Classical.epsilon` draws its instance from a
     structural `Nonempty` builder, and `subst`'s `INST_TYPE` **travels the
     witness** (`A := τ` also rewrites `hA : Nonempty A` to a `Nonempty τ` proof)
     or the kernel rejects a stray `Nonempty A` argument at `τ`.
   - **HOL variables are NOMINAL; Lean fvars are not.** `INST` must match a
     substitution redex `v` by **(name, type)**, not Lean `FVarId` — the
     `INST_TYPE` re-intern can leave two distinct fvars for one HOL variable.
     Running `INST_TYPE` and `INST` as one `replaceFVars` also let the type
     re-intern **clobber** a term substitution of the same variable; the two are
     now separate phases.
4. The **axiom soundness gate (§2.4)**: `axiom` resolves *only* to a pre-proved
   Lean theorem whose statement is **defeq** to the asserted formula (a discharge
   table of the Andrews/HOL `bool` definitions), via metavar unification for
   polymorphism. Anything else **hard-errors** — no fall-through to a fresh Lean
   `axiom`. Every exported theorem is additionally checked axiom-clean with
   `collectAxioms ⊆ {propext, Classical.choice, Quot.sound}`.

**Results (verbatim).** Two real articles import end-to-end, kernel-checked and
axiom-clean:
- **`prodWitness.art`** (1712 lines, ~1170 commands): the product-type existence
  witness. Discharges the `bool`-theory definitions of `∃`, `⇒`, `∀`, `∧`, `⊦ T`.
  ```
  OTImport.imported0_2 : ∀ (A B : Type) (x : A) (y : B),
    (fun p => ∃ x y, p = fun a b => a = x ∧ b = y) fun a b => a = x ∧ b = y
  ```
- **`unit-def.art`** — the **OpenTheory standard-library `unit` type definition**
  (package `unit-def-1.13`, HOL Light provenance; 2428 lines, ~1700 command
  words). It exercises the whole new surface: `defineTypeOp`,
  `defineConst`, `sym`, `trans`, `proveHyp`, `pop`, and **8** `axiom` assumptions
  (the 5 above plus `? = \p.p(εp)`, `!t.(t<=>T)<=>t`, `!t.(!x:A.t)=t`, the last
  two of which are the type-nonemptiness clauses). It carves the unit type as
  `{b : Prop // b}` and proves its characteristic theorem:
  ```
  OTImport.imported0_1 : ∀ (x : {b // b}), x = Classical.epsilon (fun x => True)
  ```
Two inline gate tests ship alongside: an **ACCEPT** article (`⊦ T`) and two
**REJECT** articles (a rogue `axiom ⊦ p`, one of them with the `Nonempty`-threaded
type-var path active) that the gate refuses fail-closed. Every export additionally
passes the `collectAxioms ⊆ {propext, Classical.choice, Quot.sound}` gate — which
also **caught a real `sorryAx`** mid-development when a proof term was
kernel-rejected, confirming the new rules cannot smuggle an axiom.

**Remaining (labeled residuals, not blockers).** `defineConstList` and
*polymorphic* `defineConst` (a constant with free type variables) are not yet
supported — both hard-error. `defineTypeOp` handles arity-0 type operators (`unit`);
a **parameterized** type definition (`pair`, `sum`, `option`) needs the type-arg
abstraction + a metavar-unification instantiation path, and hard-errors today.
`thm`/`axiom` support only an **empty external Γ** (what self-contained standard-
library articles export). These are the next increments; the spine (parse → replay
with Γ + type-nonemptiness + nominal `subst` → `Expr` → kernel → axiom-clean, on
two real articles including a type definition) is proven.

### 3.4 The optional stronger guarantee (distinct from replay soundness)

Replay soundness is **free**: the kernel rejects any mistranslation, so an
imported `theorem` is as trustworthy as any hand-written Lean theorem *given the
encoding and the axiom whitelist*. That is the guarantee the spike already has.

The **stronger, optional** guarantee is a **meta-theorem**: formalize HOL's
syntax + `air_accepts`-style provability in Lean, formalize the §2.3 encoding as
a function `⟦·⟧ : HOLTerm → Expr`, and prove *"if the article's HOL derivation is
valid then the emitted Lean term inhabits `⟦stmt⟧`"* — i.e. the encoding and the
16 realizations are sound *for all inputs*, not just checked per-run. This is the
Candle-style ([verified HOL checker](https://www.sciencedirect.com/science/article/pii/S2352220820300158))
result, ported to Lean. It removes the encoding from the trusted list (leaving
only the Lean kernel + the axiom whitelist). **This is a separate research
deliverable and is not required for the zkEVM to stand** — it is the difference
between "the kernel checked this import" and "the *importer* is proved correct."

### 3.5 Is Verifereum importable via this path?

**Mechanically yes, but gated by one concrete blocker.** Details:

- **Substrate.** Verifereum ([repo](https://github.com/verifereum/verifereum)) is
  a production-quality EVM Execution-Layer semantics in **HOL4**, targeting the
  live Osaka fork, validated against the Ethereum Execution Spec Tests. HOL4 is
  a full member of the OpenTheory family.
- **Export mechanism (free, no kernel patch needed).** HOL4 emits OpenTheory
  articles natively: build HOL4 with the logging kernel (`bin/build --otknl`),
  then `Holmake --ot` replaces `new_theory`/`export_theory` with versions that
  **log an article per theory** containing every saved theorem
  ([opentheory FAQ](https://www.gilith.com/opentheory/faq.html)). Verifereum
  itself advertises **no** OT export today, so this is added on the HOL4 side, not
  in Verifereum.
- **THE BLOCKER — `compute`/`EVAL`.** Verifereum's whole selling point is that its
  EVM semantics is *"executable by evaluation inside the logic"*, i.e. it leans
  heavily on HOL4's `compute`/`cv_compute`/`EVAL` kernel-computation primitive.
  **The OpenTheory exporter cannot record computation as primitive inferences**
  — this is a known, open conflict ([HOL issue #1118](https://github.com/HOL-Theorem-Prover/HOL/issues/1118)).
  Any theorem whose proof used `EVAL`/`cv_compute` cannot currently be logged to
  an article. So Verifereum is **not importable as-is** until one of:
    - (a) the compute steps are re-derived through *logged* primitive inferences
      (correct, but potentially enormous/slow — compute exists precisely to avoid
      that), or
    - (b) OT logging learns to expand `cv_compute` into primitive inferences
      (upstream HOL4 work), or
    - (c) we import only the *statement-level* results (specs, functional-
      correctness lemmas) whose proofs are not compute-bound, and re-prove the
      compute-heavy executable lemmas natively in Lean.
- **Honest resolution.** The reusable importer is the right foundation and the
  HOL4→article path is real, but "import Verifereum into Lean" is **blocked on
  the compute-logging gap**, not on the importer. That gap is upstream-HOL4
  shaped and must be surfaced as the gating risk for the verified-zkEVM plan —
  not discovered after the importer is built.
- **De-risked in depth: see `docs/CV-COMPUTE-FEASIBILITY.md`.** `cv_compute` is a
  *trusted ML kernel primitive* (`Thm.compute`/`Count.Compute`) that stamps
  `⊦ f x = v` without a certificate and without a trace; the OT logger
  hard-`raise`s on it (`Logging.sml:715`). There is **no compact certificate** to
  log — the only sound logging path re-derives by rewriting from the retained
  inputs, which **EXPLODES** (article ∝ reduction length). So: logging **one small
  lemma** (`⊦ fib 20 = 6765`) is a bounded ~week patch to `Logging.sml`; logging
  Verifereum's compute-heavy EVM execution is a size quagmire. Recommendation:
  import Verifereum's *statement-level* results via this importer and **re-prove
  the executable/compute-bound lemmas natively in Lean** as *bounded* obligations,
  where the kernel's GMP `Nat`/`BitVec` + `brecOn` reduction re-checks them
  tractably (~tens of µs/step; comfortable to ~1e4 steps) **without
  `native_decide`** — measured; see the doc's Part 2, which also flags that a long
  unbounded execution trace is expensive on either side.

---

## Sources

- OpenTheory article format spec — https://www.gilith.com/opentheory/article.html
- OpenTheory command overview — https://page.mi.fu-berlin.de/rote/Software/OpenTheory/opentheory-commands.html
- OpenTheory project / `opentheory` tool / FAQ — https://www.gilith.com/opentheory/ , https://www.gilith.com/opentheory/faq.html
- Hurd, *The OpenTheory Standard Theory Library* — https://www.gilith.com/papers/stdlib.pdf
- Kumar & Hurd, *Standalone Tactics using OpenTheory*
- xrchz/isabelle-opentheory — https://github.com/xrchz/isabelle-opentheory
- Tourret et al., *HOL Light to Isabelle/HOL translation rebooted* — https://members.loria.fr/STourret/papers/isabelle24translation.pdf
- Obua & Skalberg, *Importing HOL into Isabelle/HOL*
- hol2dk — https://github.com/Deducteam/hol2dk ; coq-hol-light — https://github.com/Deducteam/coq-hol-light ; *Translating HOL-Light proofs to Coq* — https://easychair.org/publications/open/mtFT
- Assaf & Burel, *Translating HOL to Dedukti* — https://arxiv.org/pdf/1507.08720
- Lambdapi export targets (Coq/Dedukti/HRS/CPF; no Lean) — https://lambdapi.readthedocs.io/en/latest/options.html
- lean2dk — https://github.com/Deducteam/lean2dk ; Lean4Less — https://github.com/Deducteam/Lean4Less
- Carneiro, mm-lean4 (Metamath verifier in Lean 4) — https://github.com/digama0/mm-lean4
- *A verified proof checker for higher-order logic* (Candle) — https://www.sciencedirect.com/science/article/pii/S2352220820300158
- *Sharing a Library between Proof Assistants: Reaching out to the HOL family* — https://arxiv.org/pdf/1807.01873
- Verifereum — https://github.com/verifereum/verifereum
- HOL4 `compute` vs OpenTheory logging conflict — https://github.com/HOL-Theorem-Prover/HOL/issues/1118
