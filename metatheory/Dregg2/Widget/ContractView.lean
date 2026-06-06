/-
# Dregg2.Widget.ContractView — a verified guarantee rendered as a contract card.

Renders ONE verified safety from a real `forever` theorem + human gloss. The production Hatchery path
uses `Verify.Contract` (`revokedPersists` on `trajG`); the card reads the theorem type live from the
environment and classifies trust via `collectAxioms`.
-/
import Dregg2.Widget.Basic
import Dregg2.Verify.Contract

open Dregg2.Exec
open Lean Elab Command Meta
open ProofWidgets
open scoped ProofWidgets.Jsx

namespace Dregg2.Widget

structure Guarantee where
  name      : Name
  invariant : String
  deriving Inhabited

/-- Production identity revocation — `revokedPersists` on the gated executor. -/
def identityRevokedForeverG : Guarantee where
  name      := ``Dregg2.Verify.identity_revoked_forever_production
  invariant := "Once a credential id is revoked, it stays revoked at EVERY index of EVERY adversarial \
    schedule on the production executor — a revoked identity can never be re-validated."

def statementOf (name : Name) : MetaM String := do
  let ci ← getConstInfo name
  return toString (← Meta.ppExpr ci.type)

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

private def extraValue (extra : Array Name) : Html :=
  if extra.isEmpty then
    badge "kernel-clean" "#0d1117" "#3fb950"
  else
    .text (String.intercalate ", " (extra.toList.map (·.toString)))

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
    kvRowText "forever theorem (statement read live from the kernel-checked type)" "",
    stmtBox stmt,
    kvRow "trust tier" (badge tier.label tier.color tier.bg),
    kvRowText "" tier.blurb,
    kvRowText "axioms (total)" (toString axs.size),
    kvRow "extra (non-kernel)" (extraValue extra)
  ]

#html (contractCard identityRevokedForeverG : MetaM Html)

/-- The card renders the production `CellContract.forever` payoff type (mentions `trajG` + `revoked`). -/
example (x : Nat) (s : RecChainedState) (h : x ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, x ∈ (trajG s sched n).kernel.revoked :=
  Dregg2.Verify.identity_revoked_forever_production x s h sched

run_cmd do
  let g := identityRevokedForeverG
  let t ← Command.liftCoreM <| tierOfName g.name
  unless t = .kernelChecked do
    throwError "CONTRACTVIEW TRIPWIRE: {g.name} expected KernelChecked (green), computed {t.label}"
  let stmt ← Command.liftTermElabM <| statementOf g.name
  unless (stmt.splitOn "revoked").length > 1 do
    throwError "CONTRACTVIEW TRIPWIRE: rendered statement does not mention `revoked`. Got: {stmt}"
  unless (stmt.splitOn "trajG").length > 1 do
    throwError "CONTRACTVIEW TRIPWIRE: production card should mention `trajG`. Got: {stmt}"
  logInfo m!"contractview tripwire OK: {g.name} is KernelChecked; mentions `revoked` + `trajG`"

#assert_axioms stmtBox
#assert_axioms extraValue
#assert_axioms identityRevokedForeverG
#assert_axioms Guarantee.invariant

#guard (classifyAxioms false #[``propext] ≠ classifyAxioms false #[``propext, `fooExtern])

end Dregg2.Widget