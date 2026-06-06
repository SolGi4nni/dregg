/-
# Dregg2.Catalog — the catalog code-gen (`catalog … where`) + the `discharge` guard-seam tactic.

Two deliverables:

1. **`catalog NS where | name (binders) := <Guard body> ⊨ <rhs> (by <proof>)?`** — a
   `command` elaborator emitting the `Spec/Guard.lean §7` triple per entry:

       def name (binders) : Guard _ _ := <body>
       @[simp] theorem admits_name (binders) (req w) :
           admits (name <args>) req w = true ↔ <rhs> := by <proof | simp [name]>
       #assert_axioms admits_name        -- honesty pin on 100% of output

   The auto-`#assert_axioms` is the tripwire: a default proof that secretly needs a `sorry`
   fails at generation time. The anti-goal is a flat coproduct inductive; the goal is
   derived smart-constructors over the small primitives (`firstParty`/`witnessed`/`all`/`any`/`gnot`).

2. **`discharge`** — the guard-seam opener. Rewrites goals mentioning `Guard.admits` via the
   structural `admits_*` simp set + `Bool.and/or_eq_true`, leaving one goal per leaf. The
   `Dregg2` aesop rule-set closes leaves automatically — behind the fail-loud rail.

Discipline: no `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.Spec.Guard
import Dregg2.Tactics
import Aesop

namespace Dregg2.Catalog

open Dregg2.Spec Dregg2.Spec.Guard Dregg2.Laws

/-! ## §1 — The catalog code-gen elaborator.

The catalog source-of-truth is Rust (`cell/src/program.rs` / `turn/src/action.rs`). A
declarative block elaborates each entry to the Guard §7 triple. Per-entry binders are
restricted to the explicit `(id : type)` form so the characterization lemma can reconstruct
`name <args>`. -/

/-- One catalog entry: `| name (binders)* := <Guard body> admits <rhs> (by <proof>)?`.
Binders are explicit `(id : type)` groups (the §7 shape) — `bracketedBinder`s spliced
verbatim into both the generated `def` and `theorem`. -/
syntax catalogEntry :=
  "| " ident (ppSpace bracketedBinder)* " := " term
    " ⊨ " term (" by " tacticSeq)?

/-- `catalog NS where <entries>` — emit the smart-constructor + `admits`-characterization +
auto-`#assert_axioms` triple for each entry. The `⊨ <rhs>` reads "the guard's `admits`
characterization is `<rhs>`" (we use `⊨`, not the keyword `admits`, to avoid reserving the
`admits` token that the generated lemmas themselves apply). -/
syntax (name := catalogBlock) "catalog " ident " where" (ppLine catalogEntry)+ : command

open Lean Elab Command in
/-- Pull the leading binder identifiers out of an array of explicit `bracketedBinder`s (the
`(id₁ id₂ … : type)` form), so we can build the application head `name id₁ id₂ …`. -/
private def explicitBinderIds (bs : Array Syntax) : Array Ident := Id.run do
  let mut ids : Array Ident := #[]
  for b in bs do
    -- an explicit binder is `(` binderIdent+ : type `)`; the binderIdents live at index 1.
    for idStx in b.getArg 1 |>.getArgs do
      if idStx.isIdent then
        ids := ids.push ⟨idStx⟩
  pure ids

open Lean Elab Command in
elab_rules : command
  | `(command| catalog $ns:ident where
        $[| $names:ident $[$bss]* := $bodies:term
              ⊨ $rhss:term $[ by $prfs:tacticSeq]? ]*) => do
    let n := names.size
    -- the catalog label becomes the namespace of the generated decls:
    -- `catalog StateConstraintGuard where | monotonic …` ↦ `StateConstraintGuard.monotonic`.
    let nsName := ns.getId
    for i in [0:n] do
      let entryId := names[i]!
      let bss_i := bss[i]!                        -- TSyntaxArray of binders for THIS entry
      let body := bodies[i]!
      let rhs  := rhss[i]!
      let prf? := prfs[i]!
      -- the smart-constructor's fully-qualified name + its `admits_` characterization name
      let name := mkIdentFrom entryId (nsName ++ entryId.getId)
      -- the applied head `name id₁ id₂ …`, built from the explicit binder ids
      let argIds := explicitBinderIds (bss_i.map (·.raw))
      let appHead ← `($name:ident $argIds*)
      -- `admits_name` as a SINGLE final component (not `admits.name`), under the catalog NS
      let thmName := mkIdentFrom entryId (nsName ++ Name.mkSimple ("admits_" ++ entryId.getId.toString))
      -- Use RAW (unhygienic) identifiers for the ambient section variables so the generated
      -- decls bind to `Request`/`Statement`/`Witness` in the enclosing `section`, and a raw
      -- `req`/`w` so the theorem's extra binders are referable from the (user-written) RHS.
      let reqT := mkIdent `Request; let stmtT := mkIdent `Statement; let witT := mkIdent `Witness
      let reqV := mkIdent `req; let wV := mkIdent `w
      -- 1. the smart-constructor `def` (binders spliced verbatim)
      elabCommand <| ← `(command|
        def $name:ident $bss_i* : Guard $reqT $stmtT := $body)
      -- 2. the `admits`-characterization, default proof `simp [name]` (closes the mechanical
      --    majority); an explicit `by …` overrides it for the proof-manual variants.
      let proofTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ←
        match prf? with
        | some p => pure p
        | none   => `(tacticSeq| simp [$name:ident])
      elabCommand <| ← `(command|
        @[simp] theorem $thmName:ident $bss_i*
            ($reqV : $reqT) ($wV : $stmtT → $witT) :
            admits ($appHead) $reqV $wV = true ↔ $rhs := by $proofTac)
      -- 3. THE HONESTY PIN — wired into 100% of generated output. A default-proof variant
      --    that secretly needed a `sorry` trips this `#assert_axioms` AT GENERATION TIME.
      elabCommand <| ← `(command| #assert_axioms $thmName:ident)

/-! ## §2 — Worked slice: regenerate `Spec/Guard.lean §7` via the codegen.

Demonstrates the codegen on the `monotonic`/`sumEquals`/`senderAuthorized`/`nonMembership`
slice. The generated `admits_*` lemmas self-pin via the auto `#assert_axioms`. -/

section CatalogDemo
variable {Request : Type} {Statement : Type} {Witness : Type} [Verifiable Statement Witness]

catalog StateConstraintGuard where
  | monotonic (f : Request → Nat) (t : Nat) :=
      firstParty (fun req => decide (t ≤ f req))
      ⊨ (t ≤ f req)
  | sumEquals (fs : List (Request → Nat)) (v : Nat) :=
      firstParty (fun req => decide ((fs.map (fun f => f req)).sum = v))
      ⊨ ((fs.map (fun f => f req)).sum = v)
  | senderAuthorized (s : Statement) :=
      witnessed s
      ⊨ (Discharged s (w s))
      by simp [StateConstraintGuard.senderAuthorized, admits_witnessed, Discharged]
  | nonMembership (s : Statement) :=
      gnot (witnessed s)
      ⊨ (¬ Discharged s (w s))
      by simp [StateConstraintGuard.nonMembership, admits_gnot, admits_witnessed, Discharged]

end CatalogDemo

/-! ## §3 — The `Dregg2` aesop rule-set (the leaf closer behind the fail-loud rail).

A named aesop rule-set `Dregg2` for downstream modules to register guard-seam simp
lemmas and close leaves with `aesop (rule_sets := [Dregg2])` — only behind the
`first | … | fail` honesty wrapper. Per aesop's scoping rules, registration and use
live in importing modules; `discharge` is self-contained `simp only` and does not
depend on the rule-set. -/

declare_aesop_rule_sets [Dregg2]

/-- Hatchery forest-grow frame lemmas tagged for `exec_frame` / `exec_frame_production`. -/
register_simp_attr dregg_frame

/-! ## §4 — `discharge`: the guard-seam opener.

Unfolds `admits` through the `all`/`any`/`gnot` structure via the `@[simp]` lemmas, splits
the boolean conjunction/disjunction, and leaves one goal per leaf. Honesty rail: the rewrite
is wrapped in `first | (…; done) | fail "…"`. The `done` is load-bearing — it fails loudly
if any leaf is left open, preventing half-unfolded progress. -/

/-- `discharge` — reduce a goal mentioning `Guard.admits` to its leaf obligations and close
them from context: rewrite via the structural `admits_*` simp set (`all`/`any`/`gnot`/
`firstParty`/`witnessed`) + the GENERATED `@[simp]` characterizations + `Bool.and/or_eq_true`,
then close the decidable / hypothesis leaves with `simp_all` / `omega`.

HONESTY RAIL: the structural rewrite is a `simp only [admits_*]` that FAILS ON NO PROGRESS —
so on a non-guard goal `discharge` falls straight through to the `fail` branch (it cannot fake
progress). The trailing `done` is load-bearing: if a leaf is left OPEN (e.g. a genuinely false
guard, or one missing its context fact) the first arm errors and `discharge` FAILS LOUDLY
rather than report a half-unfolded `admits` as progress. -/
macro "discharge" : tactic =>
  `(tactic| first
    | (-- 1. structural unfold — `simp only` over the admits lemmas; errors (→ fail) on a
       --    goal that mentions no `Guard.admits` (no rewrite ⇒ no progress).
       simp only [Guard.admits_all_eq, Guard.admits_any_eq, Guard.admits_gnot,
                  Guard.admits_firstParty, Guard.admits_witnessed,
                  Guard.admitsAll_cons, Guard.admitsAll_nil,
                  Guard.admitsAny_cons, Guard.admitsAny_nil,
                  Guard.admits_attenuate,
                  Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
                  Dregg2.Laws.Discharged] at *
       -- 2. close the leaves from context (decidable props / supplied hyps). Each leaf is a
       --    `firstParty` decidable prop or a `witnessed` `Discharged` — `simp_all`/`omega`
       --    discharge the ones context justifies. A FALSE leaf is left open → `done` fails.
       first | done | (try simp_all) <;> (try omega)
       -- 3. the load-bearing `done`: no residual leaf may survive masquerading as progress.
       done)
    | fail "discharge: no `Guard.admits` to unfold (or a leaf was left open) — \
        is this a guard goal, and are its context facts present?")

/-! ## §5 — Demonstrations / regression tests.

`example`s demonstrating `discharge` on real goals and `fail_if_success` negative tests
confirming it cannot close non-guard goals or false leaves. -/

section DischargeDemo
variable {Request : Type} {Statement : Type} {Witness : Type} [Verifiable Statement Witness]

/-- `discharge` closes a real conjunctive guard goal: `all [firstParty p, firstParty q]`
admits iff both leaves do. It unfolds through `all`, splits the `&&`, and the decidable
leaves close. -/
example (p q : Request → Bool) (req : Request) (w : Statement → Witness)
    (hp : p req = true) (hq : q req = true) :
    admits (all [firstParty p, firstParty q] : Guard Request Statement) req w = true := by
  discharge

/-- `discharge` closes a nested guard with a `firstParty` decidable leaf — a `balance ≥
amount`-style precondition (`decide (t ≤ f req)`) inside a conjunction unfolds to the
arithmetic leaf, which `omega` closes from the context fact `h`. -/
example (f : Request → Nat) (t : Nat) (q : Request → Bool) (req : Request) (w : Statement → Witness)
    (h : t ≤ f req) (hq : q req = true) :
    admits (all [firstParty (fun r => decide (t ≤ f r)), firstParty q] : Guard Request Statement)
      req w = true := by
  discharge

/-- The GENERATED `StateConstraintGuard.monotonic` smart-constructor's `@[simp]`
characterization (emitted by the codegen, auto-`#assert_axioms`-pinned) reduces its `admits`
to the arithmetic predicate — usable by plain `simp` exactly like the hand-written §7 version. -/
example (f : Request → Nat) (t : Nat) (req : Request) (w : Statement → Witness)
    (h : t ≤ f req) :
    admits (StateConstraintGuard.monotonic f t : Guard Request Statement) req w = true := by
  simp [StateConstraintGuard.admits_monotonic, h]

/-- HONESTY-RAIL negative test. On a goal with NO `Guard.admits`, `discharge` must FAIL
LOUDLY (it must not fall through to a weaker closer that fakes progress). We assert that
failure with `fail_if_success`: if `discharge` ever silently "succeeded" here, this `example`
would fail to compile — the rail becomes a build-checked regression test. -/
example (n : Nat) (h : n = 1) : True := by
  fail_if_success
    (have : n + 1 = 2 := by discharge)
  trivial

/-- HONESTY-RAIL negative test (variant): a guard goal that is genuinely FALSE
(`firstParty p` admits but `p req = false`) cannot be closed by `discharge` — it reduces to
the false leaf `p req = true` and stops, never fabricating it. -/
example (p : Request → Bool) (req : Request) (w : Statement → Witness) (hp : p req = false) :
    True := by
  fail_if_success
    (have : admits (firstParty p : Guard Request Statement) req w = true := by discharge)
  trivial

end DischargeDemo

end Dregg2.Catalog
