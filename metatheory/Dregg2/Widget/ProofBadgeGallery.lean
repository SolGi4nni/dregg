/-
# Dregg2.Widget.ProofBadgeGallery — the trust-tier-is-a-fact-about-the-proof-term SURFACE.

`Widget/Basic.lean` built the single-decl proof-fact badge: a metaprogram that reads a declaration's
**REAL** axiom set with `Lean.collectAxioms` and classifies a trust `Tier` (green `kernelChecked` / amber
`carrierBounded` / red `extraAxioms` / grey `axiomItself`) straight off the proof term — a colour that
*cannot be hand-faked*, because it is a function of what `collectAxioms` actually returns.

This module is the **gallery**: it runs that same classifier over a *curated set of REAL dregg theorems*
and lays the verdicts out as an `Html` **table** of `(theorem · trust tier · axioms)`. It is the literal
realisation of STARBRIDGE-LEAN-REIMAGINING.md §5 — *"the reborn tier is a fact about the proof term,
computed live"* — at gallery scale: one glance, every headline theorem, each pill the truth about its term.

> **No placeholders.** Every row is driven by a `Lean.collectAxioms` read of a theorem that is *actually in
> the environment and actually proved*. There is no hardcoded `tier`, no mock axiom list, no "Silver/Golden"
> cosmetic. The pill colour, the axiom count, and the named extra-axioms are all `MetaM`-computed off the
> live proof term at elaboration time. If any curated theorem silently picked up a stray axiom, its pill
> would change colour — and the build-time tripwire (`run_cmd`, below) would FAIL to elaborate.

## The curated set (every entry a REAL, in-tree, proved theorem)

* **`Dregg2.Exec.livingCellA_carries`** — THE CROWN. The parametric "prove one step, hold forever, against
  any adversary" coalgebra (`CellCarry.lean:57`). Every app safety is an instance of it.
* **`Dregg2.Exec.livingCellA_logMono`** — the NON-conservation app-verification payoff: the audit/receipt
  log is append-only forever (`CellCarry.lean:135`). Carried by the crown off the executor's ChainLink shape.
* **`Dregg2.Exec.livingCellA_obs_invariant'`** — the CONSERVATION theorem: the per-asset badge never drifts
  along the unbounded trajectory, re-derived *through* the crown (`CellCarry.lean:75`). The conservation
  warmup, subsumed.
* **`Dregg2.Apps.Identity.livingCellA_identity_revoked_forever`** — a shipped APP crown instance: a revoked
  identity can never be re-validated, at every index of every adversarial schedule (`Apps/Identity.lean:593`).
* **`Dregg2.Apps.ConservationBridge.committed_is_leakfree`** — a second conservation-side headline: a
  committed maneuver leaks nothing across the boundary (`Apps/ConservationBridge.lean:127`).

All five are kernel-clean (`#assert_axioms`-pinned at their definition sites), so the gallery's five real
rows come back GREEN — that is the honest outcome, and the gallery proves it from the proof terms, live.

## On the amber (`carrierBounded`) tier — the faithful story

The spec asks for a carrier-bounded theorem *"if you can find one."* The finding, verified against
the whole `Dregg2/**` tree this session: **there is no real dregg theorem at `carrierBounded`**, by design.
dregg's §8 crypto/authority carriers are entered as **`opaque` definitions / typeclass hypotheses** (the
`*Extern` opaques in `Crypto/PortalFloor.lean`, the `AuthPortal.soundness` class fields), *never* as
`axiom`-keyword constants — so `collectAxioms` never books them, and a faithful dregg proof lands GREEN, not
amber. (Grep confirms: zero `axiom`-keyword carriers in the tree; every `*Extern` is `opaque`.) The amber
tier exists precisely so that *if* such an obligation were ever booked as an honest `axiom`, the badge would
route it amber rather than silently green. To exhibit that the classifier produces amber, the
gallery's final row is the **clearly-labelled synthetic demonstrator** `Dregg2.Widget.demo_via_carrier`
(from `Basic.lean`: a theorem resting on the named demo axiom `demoEd25519VerifyExtern`, which carries the
`Extern` §8 fragment). It is marked SYNTHETIC in the table — it is *not* a real dregg theorem dressed up; it
is the discriminator that proves the gallery's colours partition. Its presence keeps the surface honest: the
real theorems are all green, and the one amber cell openly says why it is amber.

No new `axiom`s here (the demo axioms live in `Basic`).
Every helper is term-level; the only non-`MetaM` content is pure `Html`/`String` assembly.
-/
import Dregg2.Widget.Basic
import Dregg2.Apps.Identity
import Dregg2.Apps.ConservationBridge

open Lean Elab Command Meta
open ProofWidgets
open scoped ProofWidgets.Jsx

namespace Dregg2.Widget

/-! ## §1 — A curated entry: a real theorem `Name` + a short human role + an honest synthetic flag.

The gallery is driven by this list of REAL declaration names. Nothing here is the verdict — the verdict is
computed per row in §2 off `collectAxioms`. The `role` is human-facing prose (what the theorem *says*); the
`synthetic` flag is `true` ONLY for the labelled `carrierBounded` demonstrator (see the module docstring),
so the surface never passes off a demo decl as a real dregg theorem. -/

/-- One curated gallery row: a declaration name to classify, a human role gloss, and whether it is the
labelled synthetic discriminator (not a real dregg theorem). -/
structure GalleryEntry where
  /-- The declaration to read with `collectAxioms` — a REAL in-tree name (or the labelled demo). -/
  name      : Name
  /-- Human-facing prose: what this theorem actually guarantees. -/
  role      : String
  /-- `true` iff this is the synthetic `carrierBounded` demonstrator, not a real dregg theorem. -/
  synthetic : Bool := false
  deriving Inhabited

/-- **The curated set.** Five REAL, proved, kernel-clean dregg theorems (the crown, the two non-conservation
& conservation carries, a shipped app instance, a boundary-leak headline) plus ONE clearly-labelled
synthetic row that exhibits the amber `carrierBounded` tier (see the module docstring for why no *real*
dregg theorem is amber). The names are resolved against the live environment in §3 — a typo would fail
`run_cmd`, not silently vanish. -/
def galleryEntries : List GalleryEntry :=
  [ { name := ``Dregg2.Exec.livingCellA_carries,
      role := "THE CROWN — prove one step, hold forever, against any adversary" },
    { name := ``Dregg2.Exec.livingCellA_logMono,
      role := "audit log is append-only forever (non-conservation safety)" },
    { name := ``Dregg2.Exec.livingCellA_obs_invariant',
      role := "per-asset conservation never drifts (conservation, via the crown)" },
    { name := ``Dregg2.Apps.Identity.livingCellA_identity_revoked_forever,
      role := "shipped app: a revoked identity can never be re-validated" },
    { name := ``Dregg2.Apps.ConservationBridge.committed_is_leakfree,
      role := "a committed maneuver leaks nothing across the boundary" },
    { name := ``Dregg2.Widget.demo_via_carrier,
      role := "SYNTHETIC demonstrator — exhibits the amber carrier tier (not a real dregg theorem)",
      synthetic := true } ]

/-! ## §2 — Per-row rendering: a `<tr>` whose every cell is computed from the REAL proof term.

`entryRow` reads the genuine axiom set and constructs the row. The tier pill reuses `Basic.badge` with
`Basic`'s computed `Tier.color`/`Tier.bg`, so the colour is the same `collectAxioms`-derived fact the
single-decl `#dregg_badge` shows — just tabulated. -/

/-- A header cell `<th>`: left-aligned, muted, monospace, with a faint bottom rule. -/
private def thCell (label : String) : Html :=
  <th style={json% {
      textAlign: "left",
      padding: "6px 12px 6px 0",
      color: $keyColor,
      fontWeight: "600",
      fontSize: "12px",
      borderBottom: $("1px solid " ++ panelBorder),
      whiteSpace: "nowrap"
    }}>{.text label}</th>

/-- A body cell `<td>`: top-aligned, monospace, faint row rule, bright value. `value` is arbitrary `Html`
so a cell can hold the tier pill or a stacked axiom list, not just text. -/
private def tdCell (value : Html) : Html :=
  <td style={json% {
      textAlign: "left",
      verticalAlign: "top",
      padding: "7px 12px 7px 0",
      color: $valColor,
      fontFamily: "ui-monospace, SFMono-Regular, Menlo, monospace",
      fontSize: "12px",
      borderBottom: $("1px solid " ++ panelBorder)
    }}>{value}</td>

/-- The "extra (non-kernel) axioms" cell content: `kernel-clean` in green when there are none, else the
named axioms (so an amber/red verdict *names* what it rests on). Pure — fed the real `extraAxiomsOf` list. -/
private def extraAxiomsCell (extra : Array Name) : Html :=
  if extra.isEmpty then
    badge "kernel-clean" "#0d1117" "#3fb950"
  else
    .element "div" #[] (extra.map (fun a => Html.text (a.toString ++ " ")))

/-- **`entryRow` — one fully-computed gallery row.** Resolves nothing by hand: reads the declaration's REAL
transitive axiom set (`Lean.collectAxioms`), asks `getConstInfo`-style whether it is itself an `axiom`,
classifies via `Basic.classifyAxioms`, and emits a `<tr>` of `[theorem name+role · tier pill · axiom count ·
extra axioms]`. The pill colour/label come from the computed `Tier`; nothing is hand-set. Runs in any
`MonadEnv` so it can be driven from `MetaM`/`CommandElabM`/RPC. -/
def entryRow [Monad m] [MonadEnv m] (e : GalleryEntry) : m Html := do
  let axs ← Lean.collectAxioms e.name
  let env ← getEnv
  let isAxiom := match env.find? e.name with
    | some (.axiomInfo _) => true
    | _ => false
  let tier := classifyAxioms isAxiom axs
  let extra := extraAxiomsOf axs
  -- The theorem name: short name in bright mono, the human role beneath it (muted), and a SYNTHETIC tag
  -- when this is the labelled demonstrator rather than a real dregg theorem.
  let nameStr := e.name.toString
  let roleColor := if e.synthetic then "#d29922" else keyColor
  let nameCell : Html :=
    <div>
      <div style={json% {color: $valColor, fontWeight: "600"}}>{.text nameStr}</div>
      <div style={json% {color: $roleColor, fontSize: "11px", marginTop: "2px",
          fontFamily: "ui-sans-serif, system-ui, sans-serif"}}>{.text e.role}</div>
    </div>
  return .element "tr" #[] #[
    tdCell nameCell,
    tdCell (badge tier.label tier.color tier.bg),
    tdCell (.text (toString axs.size)),
    tdCell (extraAxiomsCell extra)
  ]

/-! ## §3 — The gallery: a titled `panel` wrapping a `<table>` of all the computed rows.

`galleryHtml` maps `entryRow` over `galleryEntries` (the REAL theorems) and assembles the table inside the
shared `Basic.panel`. The whole thing is `MetaM Html` because each row reads the environment; feeding it to
`#html` (§4) forces that read — the render path is exercised over genuine `collectAxioms` output. -/

/-- **`galleryHtml` (the surface).** A dark `panel` titled with the gallery's purpose, containing a `<table>`
whose header is `[theorem · trust tier · axioms · extra (non-kernel)]` and whose body is one `entryRow` per
curated entry — every cell computed from the REAL proof term. This is the literal "trust tier is a fact
about the proof term" gallery: a single Lean value rendering the live verdicts on the headline theorems. -/
def galleryHtml [Monad m] [MonadEnv m] : m Html := do
  let rows ← galleryEntries.toArray.mapM entryRow
  let header : Html :=
    <thead><tr>
      {thCell "theorem"}{thCell "trust tier"}{thCell "axioms"}{thCell "extra (non-kernel)"}
    </tr></thead>
  let table : Html :=
    <table style={json% {
        borderCollapse: "collapse",
        width: "100%",
        fontFamily: "ui-sans-serif, system-ui, sans-serif"
      }}>
      {header}
      {.element "tbody" #[] rows}
    </table>
  return panel "dregg proof-fact gallery · trust tier = a fact about the proof term"
    #[ table,
       -- A footer legend: the colour key, so the table reads standalone. Plain text, no verdict here.
       <div style={json% {marginTop: "10px", fontSize: "11px", color: $keyColor,
           fontFamily: "ui-sans-serif, system-ui, sans-serif"}}>
         {.text "green = axioms ⊆ {propext, Classical.choice, Quot.sound} · amber = named §8 carrier · red = un-vetted axiom · grey = the decl IS an axiom"}
       </div> ]

/-! ## §4 — Force the render. `#html (galleryHtml : MetaM Html)` elaborates the gallery over the REAL
values: `HtmlEval (MetaM Html)` runs the `collectAxioms` reads and builds the `Html`, so the verify step
exercises the render path. Put your cursor on it to see the gallery in the infoview. -/

#html (galleryHtml : MetaM Html)

/-! ## §5 — Build-time TRIPWIRE: the gallery's colours are checked, not asserted.

This is the gallery's credibility. We re-run the classifier in `CommandElabM` and demand the EXACT tier we
claim for each entry: the five real theorems MUST be `kernelChecked` (green) and the synthetic
demonstrator MUST be `carrierBounded` (amber). If any real crown ever picked up a stray axiom — a hidden
`sorry`, an accidental `axiom` dependency — this `run_cmd` would `throwError` and the FILE WOULD NOT BUILD.
So a green row in the rendered gallery is not a claim; it is a checked fact, exactly like `#assert_axioms`.

It also proves the gallery is NON-VACUOUS: the verdicts are not all the same. The real rows are green AND
the synthetic row is amber — two different `collectAxioms` outcomes, partitioned by the classifier
(`kernelChecked ≠ carrierBounded`), confirmed by the kernel here. -/
run_cmd do
  for e in galleryEntries do
    let t ← Command.liftCoreM <| tierOfName e.name
    let expected := if e.synthetic then Tier.carrierBounded else Tier.kernelChecked
    unless t = expected do
      throwError "GALLERY TRIPWIRE: {e.name} expected tier {expected.label}, computed {t.label} \
        (its REAL axiom set disagrees with the row's colour)"
  -- Non-vacuity, machine-checked: the gallery shows ≥ 2 distinct tiers (green real + amber demo),
  -- so the surface is not a constant. (`decide` over `DecidableEq Tier`; no `native_decide`.)
  unless decide (Tier.kernelChecked ≠ Tier.carrierBounded) do
    throwError "GALLERY: the tier partition collapsed — kernelChecked = carrierBounded"
  logInfo m!"gallery tripwire OK: {galleryEntries.length} rows classified; \
    real theorems kernel-clean (green), synthetic demonstrator carrier-bounded (amber) — colours checked"

/-! ## §6 — Axiom hygiene. The gallery's own pure assembly is pinned kernel-clean.

The `Html`-building helpers (`thCell`/`tdCell`/`extraAxiomsCell`) and the entry list must themselves rest on
nothing but the kernel triple — the gallery cannot lecture about trust tiers while carrying trust-debt of
its own. (The amber comes ONLY from the labelled demo decl's axiom set, read live, never from any new axiom
introduced here.) `entryRow`/`galleryHtml` are `MetaM` programs (effectful reads of the environment), so we
pin the pure leaves; their kernel-cleanliness plus the §5 tripwire is the gallery's credibility. -/

#assert_axioms thCell
#assert_axioms tdCell
#assert_axioms extraAxiomsCell
#assert_axioms galleryEntries

/-! ## §7 — A `#eval` glance at the non-vacuity (no elaboration of the render needed).

The classifier moves: feeding `classifyAxioms` the shapes the gallery actually encounters — a kernel-clean
set vs. a §8-carrier-bearing set — yields the two distinct tiers the table shows. If the gallery were a
constant, these would print the same label; they do not. (This mirrors `Basic.lean`'s contrast, re-stated
here so the gallery file is self-evidently non-vacuous.) -/

-- A real-row shape (kernel triple only) ⇒ green.
#guard (classifyAxioms false #[``propext, ``Classical.choice, ``Quot.sound]).label == "KernelChecked"  -- "KernelChecked"
-- The synthetic-row shape (a §8 carrier-named extra axiom) ⇒ amber.
#guard (classifyAxioms false #[``propext, `demoEd25519VerifyExtern]).label == "CarrierBounded"  -- "CarrierBounded"
-- The two are distinct — the gallery partitions its rows.
#guard decide (classifyAxioms false #[``propext] ≠ classifyAxioms false #[``propext, `fooExtern])  -- true

end Dregg2.Widget
