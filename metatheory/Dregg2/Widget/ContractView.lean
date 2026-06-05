/-
# Dregg2.Widget.ContractView — a single verified GUARANTEE, rendered as a contract card.

`Widget/Basic.lean` built the proof-fact trust badge: a metaprogram that reads a declaration's **REAL**
axiom set (`Lean.collectAxioms`) and classifies a trust `Tier` straight off the proof term — a colour that
*cannot be hand-faked*. `Widget/ProofBadgeGallery.lean` tabulated that verdict over many theorems.

This module is the **single-guarantee card**: it renders ONE verified safety as a `panel` carrying

1. the **human invariant statement** (the contract author's prose — what the cell guarantees), and, beside it,
2. the **machine type signature of the `forever` theorem, pretty-printed LIVE** from the environment
   (`Meta.ppExpr` on the constant's real `.type`) — so the card shows not a claim *about* a theorem but the
   theorem's actual statement, read off the term, and
3. the **`forever` theorem name** with its **computed trust tier pill** (the same `collectAxioms`-derived
   verdict `#dregg_badge` shows), the **axiom count**, and the **named extra (non-kernel) axioms**.

It is STARBRIDGE-LEAN-REIMAGINING.md §3 Pillar 3's `ContractView`: *"a verified guarantee rendered: the
invariant, the `forever` theorem."* Driven from the shipped app crown
`Dregg2.Apps.Identity.livingCellA_identity_revoked_forever` — *"a revoked identity can never be re-validated,
at every index of every adversarial schedule."*

> **No placeholders.** Every field is computed from a REAL Lean value at elaboration time: the rendered type
> is `Meta.ppExpr` of the live constant's type, the tier pill is `Basic.tierOfName` off the genuine axiom set,
> the axiom count is `collectAxioms.size`. There is no hardcoded statement string, no mock tier. If the
> theorem's type changed, the card's type line would change; if it picked up a stray axiom, the pill would go
> amber/red AND the build-time tripwire (§4) would refuse to elaborate.

> **Independence.** This renders from a theorem `Name` + a human gloss + the `Basic` badge — deliberately NOT
> from the `CellContract` structure of `Dregg2.Verify.Contract` (built concurrently in another chain). The
> two meet only at the surface; the rendering path has no `Verify.Contract` dependency.

Discipline: NO `sorry`/`admit`/`native_decide`/SMT, NO new `axiom`s. Every helper is term-level and
kernel-clean (`#assert_axioms`-pinned, §5); the only effectful content is the `MetaM` reads of the
environment (`ppExpr`/`collectAxioms`), forced by `#html` (§3) and checked by the tripwire (§4).
-/
import Dregg2.Widget.Basic
import Dregg2.Apps.Identity

open Lean Elab Command Meta
open ProofWidgets
open scoped ProofWidgets.Jsx

namespace Dregg2.Widget

/-! ## §1 — A `Guarantee`: the contract author's two inputs.

A guarantee names a `forever` theorem (the REAL declaration whose `collectAxioms`/type drive the card) and a
human invariant gloss (the prose the author asserts the cell upholds). Everything else on the card — the type
signature, the tier, the axiom set — is computed from `name`. This is intentionally NOT
`Dregg2.Verify.Contract.CellContract`: the card renders from a `Name`, so it stays decoupled from the Hatchery
contract bundle (see the module docstring on independence). -/

/-- One verified guarantee to render: the `forever` theorem to read, plus a human gloss of the invariant it
upholds. `name` must be a REAL in-tree declaration — `tierOfName`/`ppExpr` resolve it against the live
environment, and the §4 tripwire fails the build on a typo. -/
structure Guarantee where
  /-- The `forever` theorem — the REAL declaration whose axiom set + type drive the card. -/
  name      : Name
  /-- Human gloss: what safety this cell upholds (the contract author's prose). -/
  invariant : String
  deriving Inhabited

/-- **THE shipped guarantee this card renders.** The Identity app's permanent-revocation crown: once a
credential id is in the revocation registry, it stays there at every index of every adversarial trajectory —
so a revoked identity can never be re-validated. A genuine NON-conservation safety (it reads the kernel
registry, not the per-asset measure), carried forever by `livingCellA_carries`. The prose is the author's
spec; the machine statement is read live off the term (§2). -/
def identityRevokedForever : Guarantee where
  name      := ``Dregg2.Apps.Identity.livingCellA_identity_revoked_forever
  invariant := "Once a credential id is revoked, it stays revoked at EVERY index of EVERY adversarial \
    schedule — a revoked identity can never be re-validated."

/-! ## §2 — Reading the REAL statement: the `forever` theorem's type, pretty-printed live.

`statementOf` is the heart of "the card shows the theorem, not a claim about it". It resolves the constant and
runs `Meta.ppExpr` on its actual `.type` — the same elaborated `Expr` the kernel checked. The result is the
genuine `∀ … → ∀ n, credNul ∈ (trajA s sched n).kernel.revoked` statement, not a hand-typed string. -/

/-- **`statementOf` — the `forever` theorem's TYPE, pretty-printed from the live environment.** Reads the
constant's real `.type` (`getConstInfo`) and renders it with `Meta.ppExpr`. Runs in `MetaM` (it needs the
local pretty-printing context). This is what makes the card non-vacuous: a *different* theorem yields a
*different* statement string, with no hand-set text anywhere. -/
def statementOf (name : Name) : MetaM String := do
  let ci ← getConstInfo name
  return toString (← Meta.ppExpr ci.type)

/-! ## §3 — The card. A titled `panel` whose every field is computed from the REAL term.

`contractCard` assembles the panel: the human invariant gloss, the LIVE machine statement, the theorem name,
its computed tier pill, the axiom count, and the named extra axioms. The tier pill reuses `Basic.badge` with
`Basic`'s `collectAxioms`-derived `Tier.color`/`Tier.bg`, so the colour is exactly the fact `#dregg_badge`
shows — just framed as a single guarantee rather than a gallery row. -/

/-- A statement block: the machine type rendered in a monospace, wrapping, faintly-bordered code box. The
`forever` theorem's real type goes here — the load-bearing "this is what was proved" line. -/
private def stmtBox (stmt : String) : Html :=
  <div style={json% {
      fontFamily: "ui-monospace, SFMono-Regular, Menlo, monospace",
      fontSize: "12px",
      color: $valColor,
      background: "#161b22",
      border: $("1px solid " ++ panelBorder),
      borderRadius: "6px",
      padding: "8px 10px",
      whiteSpace: "pre-wrap",
      lineHeight: "1.5",
      overflowWrap: "anywhere"
    }}>{.text stmt}</div>

/-- The "extra (non-kernel) axioms" value: `kernel-clean` in green when there are none, else the named axioms
(so an amber/red guarantee *names* what it rests on). Pure — fed the real `extraAxiomsOf` list. -/
private def extraValue (extra : Array Name) : Html :=
  if extra.isEmpty then
    badge "kernel-clean" "#0d1117" "#3fb950"
  else
    .text (String.intercalate ", " (extra.toList.map (·.toString)))

/-- **`contractCard` — one verified guarantee, fully computed.** Resolves nothing by hand: reads the
declaration's REAL transitive axiom set (`Lean.collectAxioms`) and `.type`, classifies the tier via
`Basic.classifyAxioms`, pretty-prints the statement via `statementOf`, and emits a `panel` of
[invariant gloss · live machine statement · theorem name · tier pill · axiom count · extra axioms]. The pill
colour/label come from the computed `Tier`; the statement line comes from `ppExpr`; nothing is hand-set.
`MetaM` because it reads the environment — `#html` (below) forces that read. -/
def contractCard (g : Guarantee) : MetaM Html := do
  let stmt ← statementOf g.name
  let axs ← Lean.collectAxioms g.name
  let env ← getEnv
  let isAxiom := match env.find? g.name with
    | some (.axiomInfo _) => true
    | _ => false
  let tier := classifyAxioms isAxiom axs
  let extra := extraAxiomsOf axs
  return panel s!"verified guarantee · {g.name}" #[
    kvRow "invariant" (.text g.invariant),
    -- The LIVE machine statement — the theorem's real type, pretty-printed from the term.
    kvRowText "forever theorem (statement read live from the kernel-checked type)" "",
    stmtBox stmt,
    -- The trust verdict, computed off the genuine axiom set (the colour cannot be faked).
    kvRow "trust tier" (badge tier.label tier.color tier.bg),
    kvRowText "" tier.blurb,
    kvRowText "axioms (total)" (toString axs.size),
    kvRow "extra (non-kernel)" (extraValue extra)
  ]

/-! ## §3b — Force the render. `#html (contractCard … : MetaM Html)` elaborates the card over the REAL value:
`HtmlEval (MetaM Html)` runs the `ppExpr`/`collectAxioms` reads and builds the `Html`, so the verify step
genuinely exercises the render path over the live theorem. Put your cursor on it to see the card. -/

#html (contractCard identityRevokedForever : MetaM Html)

/-! ## §4 — Build-time TRIPWIRE: the card's green pill is CHECKED, not asserted.

This is the card's credibility. We re-run the classifier in `CommandElabM` and demand the EXACT tier the card
shows — `kernelChecked` (green) for the shipped revocation crown. If that theorem ever picked up a stray axiom
(a hidden `sorry`, an accidental dependency), this `run_cmd` would `throwError` and the FILE WOULD NOT BUILD —
exactly like `#assert_axioms`. So a green card is not a claim; it is a checked fact.

It ALSO checks the live statement is the genuine revocation invariant, not a placeholder: the pretty-printed
type must mention `revoked` (the moving registry) — the property the gloss promises. A vacuous renderer (empty
or constant statement) would fail this. -/
run_cmd do
  let g := identityRevokedForever
  -- (1) The trust tier the card shows is the tier the kernel actually computes.
  let t ← Command.liftCoreM <| tierOfName g.name
  unless t = .kernelChecked do
    throwError "CONTRACTVIEW TRIPWIRE: {g.name} expected KernelChecked (green), computed {t.label} \
      — its REAL axiom set disagrees with the card's colour"
  -- (2) The statement the card renders is read live AND is the genuine revocation invariant (mentions the
  -- moving registry `revoked`). This refutes a vacuous/placeholder renderer.
  let stmt ← Command.liftTermElabM <| statementOf g.name
  unless (stmt.splitOn "revoked").length > 1 do
    throwError "CONTRACTVIEW TRIPWIRE: rendered statement does not mention `revoked` — \
      the card is not reading the real invariant. Got: {stmt}"
  logInfo m!"contractview tripwire OK: {g.name} is KernelChecked (green); \
    live statement reads the real `revoked` invariant ({stmt.length} chars)"

/-! ## §5 — Axiom hygiene. The card's own pure assembly is pinned kernel-clean.

The `Html`-building leaves (`stmtBox`/`extraValue`) and the guarantee datum must rest on nothing but the
kernel triple — the card cannot certify a guarantee's trust while carrying trust-debt of its own.
(`contractCard`/`statementOf` are `MetaM` programs — effectful reads of the environment — so we pin the pure
leaves; their kernel-cleanliness plus the §4 tripwire is the card's credibility.) -/

#assert_axioms stmtBox
#assert_axioms extraValue
#assert_axioms identityRevokedForever
#assert_axioms Guarantee.invariant

/-! ## §6 — Non-vacuity by `#eval` (no render elaboration needed).

The renderer MOVES — it reads genuinely different statements for different theorems, and the tier classifier
genuinely partitions. These run the PURE / `CoreM` cores directly, so the contrast needs no infoview:

* the live statement of the revocation crown is non-trivial AND contains its moving quantity `revoked`
  (a placeholder renderer would fail both), and it is LONGER than a trivial `rfl` theorem's statement —
  proving `statementOf` reads real, decl-specific content rather than emitting a constant; and
* the classifier returns the green tier for the crown's kernel-clean shape but a different tier for a
  carrier-bearing shape — so the pill is not a constant. -/

-- The live statement is the real revocation invariant: non-empty and mentions `revoked`.
-- (MetaM check: `throwError` on failure FAILS THE BUILD — a build-enforced assertion, not a glance.)
#eval show MetaM Unit from do
  let s ← statementOf ``Dregg2.Apps.Identity.livingCellA_identity_revoked_forever
  unless (!s.isEmpty) && decide ((s.splitOn "revoked").length > 1) do
    throwError "statementOf revocation crown should be non-empty and mention `revoked`"  -- true

-- The renderer is decl-specific, not a constant: the crown's statement is strictly longer than a trivial
-- `rfl` theorem's (`demo_clean : 3 = 3` is a much smaller type than the revocation ∀-statement).
#eval show MetaM Unit from do
  let big ← statementOf ``Dregg2.Apps.Identity.livingCellA_identity_revoked_forever
  let small ← statementOf ``Dregg2.Widget.demo_clean
  unless decide (small.length < big.length) do
    throwError "crown statement should be strictly longer than the trivial rfl theorem's"  -- true

-- The tier pill moves: kernel-clean ⇒ green; a §8-carrier-bearing shape ⇒ amber. Not a constant.
#guard decide (classifyAxioms false #[``propext] ≠ classifyAxioms false #[``propext, `fooExtern])  -- true

end Dregg2.Widget
