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
orders. Run it (Lean 4.30.0) — as the gate, which is also how CI runs it:
```
bash scripts/check-opentheory-importer.sh              # ~8s: the real articles, with floors
bash scripts/check-opentheory-importer.sh --self-test  # ~42s: + proves each guard goes red
lean docs/opentheory-importer-poc/OTPoC.lean           # the raw elaboration, from the repo root
```
The bundled articles (`unit-def.art`, `prodWitness.art`) are **required**: a missing
one is a hard error, not a skip. `OT_ARTICLE=<path>` adds one more article;
`OT_ARTICLE_DIR=<dir>` overrides where the bundled ones are looked for. Until
2026-07-27 the imports sat behind `pathExists` fallbacks and nothing in the tree
ran this file at all, so with the articles absent it elaborated **`EXIT=0`, green,
having imported exactly one theorem (`True`)** — the gate script and the hard
error exist because of that measurement.

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

   ⚠ It was fail-**deferred**, not fail-closed, until 2026-07-27. A discharge
   candidate whose `[Nonempty _]` instance the synthesizer could not solve left an
   **unassigned metavar** in the returned proof term, so the gate said *discharged*
   and the refusal came from the kernel at `addDecl`, one layer downstream of the
   guarantee this doc states. Measured on `⊦ ∀ (t : Prop), (∀ _ : Empty, t) = t` —
   false at `t := False`. The gate now requires every peeled binder to be really
   instantiated (the returned term is metavariable-free and its type is re-checked
   against the article's formula with the instantiation fixed), and refuses there.
   No article surface was found that reaches it — every HOL type variable carries a
   `Nonempty` witness — so this was a defect in the gate's *contract*, not a
   demonstrated exploit; the contract is what the doc sells.

5. The **Γ-content check in `thm`**, which is a soundness check and not a hygiene
   one. `thm` compared only the SIZE of the article's declared Γ against the
   proof's open hypotheses, so an article declaring the false sequent `q ⊢ p` over
   a proof of `p ⊢ p` imported successfully and exported `∀ p, p → p`. The kernel
   cannot see this: it checks that the exported term proves *its own* statement, so
   it guarantees the export is TRUE, never that it is the ARTICLE'S theorem. Each
   declared hypothesis must now match a distinct actually-assumed one up to defeq.
   That distinction is load-bearing for the whole "import Verifereum" thesis.

> ## ⚑ CORRECTED 2026-07-27 — the audit ledger for §3.3, and what has since been repaired
>
> The load-bearing technical work here is **real** and survived adversarial probing: `prodWitness.art`
> and `unit-def.art` genuinely import end-to-end, kernel-checked and axiom-clean (5 and 8 axiom
> assumptions discharged respectively — both counts confirmed by re-running the **committed** bytes),
> the axiom gate genuinely refuses both rogue articles with the real `AXIOM GATE (fail-closed)` error,
> all 12 discharge-table entries are ordinary Lean theorems with real proofs, and there is no `sorry`,
> `axiom` or `native_decide` in `OTPoC.lean`. **What was overstated was the packaging around it.**
>
> Six findings were measured against the committed artifact on 2026-07-27
> (`docs/AUDIT-IMPORTER-AND-DOCS.md` §1, F-A1…F-A7, F-C3, F-C4). **Five have since been repaired by a
> concurrent lane; I re-checked each against HEAD rather than restating the audit.** They are recorded
> here because a reader who saw the earlier version of this document needs to know what moved.
>
> | # | What was wrong (measured) | Status at HEAD |
> |---|---|---|
> | **F-A1a** | All three real-article imports were guarded by `if ← p.pathExists then … else logInfo`. With **no article files and `OT_ARTICLE` unset** the file elaborated **`EXIT=0`, green**, having imported exactly one theorem — `True`. `logInfo`, not `logWarning`, not `throwError`: a missing article was indistinguishable from a passing one at the exit code. | **REPAIRED.** One `pathExists` remains (`:1180`) and `:1166` documents in place why it is not a fallback. |
> | **F-A1b** | `grep -rn "opentheory\|OTPoC\|OPENTHEORY" .github/ scripts/ metatheory/lakefile*` → **zero hits**. Wired into no workflow, no lake target, not `scripts/local-gates.sh`. It ran only when a human typed the command below. | **REPAIRED.** Now two gates in `scripts/local-gates.sh:229-230` (`opentheory-importer` and a `--self-test` red-check) plus `.github/workflows/ci.yml:1206`. |
> | **F-A2** | `OTPoC.lean:27` and this document said the gate **"HARD-ERRORS"** on anything else. It was fail-***deferred***: `tryDischarge` returned `some` on a proof term carrying an **unassigned instance metavariable** (`synthInstance?` cannot solve e.g. `Nonempty Empty`), so the gate **discharged the false statement** `∀ (t : Prop), (∀ x : Empty, t) = t` with `proof.hasMVar = true`. The kernel refused it one layer later, at `addDecl`. | **REPAIRED.** The discharge path now rejects any surviving hole (`if pf.hasExprMVar \|\| pf.hasLevelMVar then return none`) **and** re-checks that the instantiated statement is still the article's formula, both metavariable-free (`:498-508`). **[UNVERIFIED]** and worth stating: the audit could not construct an article that ever reached the old hole, and did not *prove* the article surface admits no empty type — so the defect was in the gate's **contract**, not demonstrably in its **behaviour**. |
> | **F-A3** | `thm` checked only `th.hyps.size == ls.size` — the **size** of the declared Γ, never its contents. An article declaring the false HOL sequent `q ⊢ p` over a proof of `p ⊢ p` passed, exported `∀ (p : Prop), p → p`, logged success, and named it `imported0_1` — a name recording nothing about which article theorem it is meant to be. | **REPAIRED**, and §3.3 above now states the distinction: the kernel guarantees the export is **TRUE**, never that it is the **ARTICLE'S** theorem. `:1077` now requires each declared hypothesis to match a distinct actually-assumed one up to defeq, with `:1060-1061`'s size check retained as an independent bite (`:1254`). |
> | **F-A4** | `importArticleExpectFail` caught **any** exception and reported `reject-test OK` — a malformed 3-token article "passed" it on `stack underflow`, asserting nothing about *why* the rejection happened. | **REPAIRED.** Each reject-test now asserts the reason its rejection carries. |
> | **F-A5** | `OTPoC.lean:1111-1115` asserted, unhedged and in the present tense, that `pair-closed.art` *"Exercises … 30 `thm` exports end-to-end, kernel-checked + axiom-clean."* It has **never once been observed to complete.** The honest hedge existed only in the commit body — and a reader six weeks out opens the file, not `git log`. This document did not mention `pair-closed.art` **at all**, in either direction. | **REPAIRED** in the residuals below, which now state plainly that it has never been observed to import end-to-end. |
>
> **Two further corrections that are not about code.**
>
> - **"the axiom-clean gate caught a real `sorryAx` … confirming the new rules cannot smuggle an
>   axiom"** was a **non-sequitur**. One catch shows the gate fired once; it does not establish
>   "cannot". The word is withdrawn (and the Results block below now says so).
> - **`defineConstList` has zero occurrences across all three committed articles**, and the commit
>   *subject* that shipped it reads as delivered. It is implemented and **wholly unexercised** —
>   **[UNVERIFIED]**, not wrong: untested.
>
> **Two reported results were stated over runs that never reached a terminal state** (audit F-C3,
> F-C4). *"Builds green (hbox, lean 4.30.0); regression clean"* was written while the last run of the
> **committed** bytes had not terminated; the last run that *did* reach a terminal state was an
> **error** (`defineConst Data.Pair.,: defining term has free term variable(s)`) from a file version
> two edits earlier. The accept/reject and `unit-def` claims **are** true of the committed bytes —
> the audit independently re-established that by running them — but they were not verified at the time
> they were made. Separately, the reported *"HOL4 `--otknl` built 62 core dirs in 35 min … the
> HOL4→article pipeline is **de-risked end-to-end**"* cites as its evidence a build that **FATAL'd**
> (`opentheory failed: *** FATAL: Build failed in directory .../src/boss`). The third blocker was
> correctly diagnosed and its fix applied (`opentheory install base` → `base-1.221`) — and then
> **never rebuilt**: no `bin/build` or `Holmake` invocation exists after that point. **Two of the three
> blockers were verified by a build; the third's fix was never exercised, so "de-risked end-to-end" is
> withdrawn.**
>
> **Also [UNVERIFIED]** (audit §6, stated rather than passed): whether `pair-closed.art` ever
> completes, and whether its 30 exports are kernel-checked and axiom-clean — **unverified in both
> directions**, no failure was observed either; and `prodWitness.art`'s *"real HOL4-emitted"*
> provenance — its structure is strongly consistent with tool emission and `OpenTheoryReader.sml`
> exists at the cited path, but it was not re-emitted from HOL4 and the emitter is unconfirmed.

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
  OTImport.imported0_1 : (fun P => ∀ (x : { b // b }), P x) fun v =>
    v = Classical.epsilon fun x => True
  ```
  (That is the importer's actual output, re-measured 2026-07-27. This block
  previously showed the beta-reduced `∀ (x : {b // b}), x = Classical.epsilon
  (fun x => True)` under a "verbatim" heading; the two are beta-equivalent, so the
  mathematics is unaffected, but the printed form was hand-prettified and the
  authoring commit's own code never emitted it.)

Gate tests ship alongside and RUN on every invocation: an **ACCEPT** article
(`⊦ T`), two **REJECT** articles (a rogue `axiom ⊦ p`, one with the
`Nonempty`-threaded type-var path active), a **Γ-SWAP** article (declares `q ⊢ p`
over a proof of `p ⊢ p`) and a **Γ-DROP** article, plus three direct probes at the
discharge gate (the `Empty` instance must be refused; the `Nat` instance must
still discharge, metavariable-free; a statement outside the table must be
refused). Each reject-test asserts the REASON the rejection carries, because an
error-agnostic one passes just as happily after the gate it tests stops firing —
the malformed-article probe run during the audit "passed" on `stack underflow`.
Every export additionally passes the `collectAxioms ⊆ {propext, Classical.choice,
Quot.sound}` gate, which **caught a real `sorryAx`** mid-development. (One catch
shows the gate fires; it is not evidence that an axiom *cannot* be smuggled.)

**Remaining (labeled residuals, not blockers).** `defineConstList`, *polymorphic*
`defineConst` (a constant with free type variables) and **parameterized**
`defineTypeOp` (`pair`, `sum`, `option`) are all **implemented** as of `9bb3bb75a`
— this list said they hard-error, which has been false since that commit.
What is *not* established is that they work on a real article: the article that
exercises them, `pair-closed.art` (the composed OpenTheory `pair` theory: 64205
lines, 30 `thm` commands, **2243** `subst` commands), **has never been observed to
import end-to-end.** The originating run reached 2 h 20 m of CPU with zero bytes of
output against a "~16 min" estimate, and a re-run for the 2026-07-27 repair passed
the same mark. The bottleneck is `subst`, which is quadratic in the article. It is
therefore opt-in (`OT_PAIR_CLOSED=1`) and no claim of completion is made anywhere.
`defineConstList` additionally has **zero** occurrences in any committed article.
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
