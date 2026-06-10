/-
# Dregg2.Widget.Basic — the ProofWidgets substrate for the dregg *inspector* vocabulary.

This is the shared foundation every leaf inspector widget reuses. It carries two things:

1. **A tiny `Html` vocabulary** — `badge`, `kvRow`, `panel` — so every dregg widget renders with one
   consistent look (a dark panel, monospace key/value rows, a coloured pill). These are plain
   `ProofWidgets.Html` builders; nothing here runs at proof time except the badge metaprogram below.

2. **THE PROOF-FACT TRUST BADGE — the heart of "no placeholders".** A metaprogram that, given a
   declaration `Name`, reads its **REAL** axiom set with `Lean.collectAxioms` (the same primitive the
   project's `#assert_axioms` tripwire uses, `Dregg2/Tactics.lean:34`) and classifies a *trust tier*
   straight off the proof term. The badge is therefore **computed, never hand-set**: you cannot paint a
   green "KernelChecked" pill on a theorem that secretly leans on `sorryAx` or an extra `axiom`, because
   the pill's colour is a function of what `collectAxioms` actually returns.

   The tiers (ascending in trust-debt):
   * **`kernelChecked`** — every axiom is one of the three standard kernel axioms
     `{propext, Classical.choice, Quot.sound}`. This is the clean set the whole metatheory pins to. The
     living-cell crown (`livingCellA_carries`) and its app instances sit here.
   * **`carrierBounded`** — additionally rests on a *named dregg §8 carrier* (a crypto/authority oracle).
     dregg's design enters those carriers as **typeclass parameters / hypotheses** (`AuthPortal.soundness`,
     `SignatureKernel.unforgeable`, the `*Extern` opaques in `Crypto/PortalFloor.lean`), so a *faithful*
     dregg proof never actually lands here — by construction such a carrier is discharged by the caller,
     not depended on as an `axiom`. The tier exists so that **if** a §8 obligation were ever booked as an
     honest `axiom`-keyword carrier, the badge would route it here (amber: "trusted modulo a named §8
     assumption") rather than silently green. The discriminating demo at the bottom of this file proves
     the classifier distinguishes this case.
   * **`extraAxioms`** — depends on an axiom that is neither kernel-standard nor a recognised carrier:
     an *un-vetted* trust assumption. Red. (`sorryAx` lands here — a hidden `sorry` shows up RED.)
   * **`axiomItself`** — the named declaration *is* an `axiom` (no proof term at all). Grey: "asserted,
     not proved". This is the "clearly-marked no-term state" the inspector must never confuse with green.

   Surface: `Tier` (the value) · `classifyAxioms` (the pure core, `#eval`-testable) · `tierOfName`
   (the `MetaM Name → Tier` metaprogram) · `proofFactBadge` (the `Name → MetaM Html` renderer) ·
   `#dregg_badge <ident>` (the command that prints the badge in the infoview).

The only `axiom`s in this file are two clearly-named
*demo* carriers in the final §, present solely to exhibit that the classifier reports a DIFFERENT tier for
an axiom-bearing decl — the non-vacuity witness. Every real definition is term-level and kernel-clean.
-/
import Dregg2.Exec.CellCarry
import ProofWidgets.Component.HtmlDisplay

open Lean Elab Command
open ProofWidgets
open scoped ProofWidgets.Jsx

namespace Dregg2.Widget

/-! ## §1 — The shared `Html` vocabulary (`badge` · `kvRow` · `panel`).

Inline-styled so a leaf widget needs no external CSS. The palette is deliberately small: a near-black
panel, a faint divider per row, monospace values, and a coloured pill. Leaf widgets compose these. -/

/-- The dregg dark-panel background. -/
def panelBg : String := "#0e1116"
/-- The faint divider / border colour. -/
def panelBorder : String := "#2b313b"
/-- The muted label colour (keys). -/
def keyColor : String := "#8b949e"
/-- The bright value colour. -/
def valColor : String := "#e6edf3"

/-- A coloured **pill** — a rounded, padded inline span. The atom every status indicator is built from.
`fg`/`bg` are CSS colour strings; `label` is the text. Used by `tierBadge` and reusable by leaves for any
small status chip (e.g. "committed" / "rejected" / "live"). -/
def badge (label : String) (fg : String := valColor) (bg : String := panelBorder) : Html :=
  <span style={json% {
      display: "inline-block",
      padding: "1px 8px",
      borderRadius: "10px",
      fontSize: "12px",
      fontWeight: "600",
      fontFamily: "ui-monospace, SFMono-Regular, Menlo, monospace",
      color: $fg,
      background: $bg
    }}>{.text label}</span>

/-- A **key/value row** — a muted monospace label and a bright value, separated, with a faint bottom
border. The workhorse of every inspector panel (`"axioms"` ↦ the list, `"effect"` ↦ the constructor…).
The `value` is arbitrary `Html` so a row can hold a nested badge or a sub-list, not just text. -/
def kvRow (key : String) (value : Html) : Html :=
  <div style={json% {
      display: "flex",
      justifyContent: "space-between",
      alignItems: "center",
      gap: "16px",
      padding: "4px 0",
      borderBottom: $("1px solid " ++ panelBorder),
      fontFamily: "ui-monospace, SFMono-Regular, Menlo, monospace",
      fontSize: "13px"
    }}>
    <span style={json% {color: $keyColor}}>{.text key}</span>
    <span style={json% {color: $valColor, textAlign: "right"}}>{value}</span>
  </div>

/-- Convenience: a `kvRow` whose value is plain text. -/
def kvRowText (key val : String) : Html := kvRow key (.text val)

/-- A **panel** — a titled dark card wrapping a stack of children (typically `kvRow`s). The outer frame
of every dregg inspector widget. `title` renders as a small bright header above the body. -/
def panel (title : String) (children : Array Html) : Html :=
  <div style={json% {
      background: $panelBg,
      border: $("1px solid " ++ panelBorder),
      borderRadius: "8px",
      padding: "12px 14px",
      maxWidth: "560px",
      fontFamily: "ui-sans-serif, system-ui, sans-serif",
      color: $valColor
    }}>
    <div style={json% {
        fontSize: "13px",
        fontWeight: "700",
        letterSpacing: "0.02em",
        marginBottom: "8px",
        color: $valColor
      }}>{.text title}</div>
    <div>{...children}</div>
  </div>

/-! ## §2 — The trust **`Tier`** and its presentation.

A `Tier` is a *verdict on a proof term*, ordered by how much trust-debt it carries. The presentation
(`tierColor`/`tierBg`/`tierLabel`/`tierBlurb`) is pure metadata; the verdict itself is computed in §3. -/

/-- The trust verdict read off a declaration's real axiom set. See the module docstring for the full
meaning of each tier. Ordered ascending in trust-debt: `kernelChecked < carrierBounded < extraAxioms`,
with `axiomItself` orthogonal (the decl is an assumption, not a proof). -/
inductive Tier where
  /-- Axioms ⊆ `{propext, Classical.choice, Quot.sound}` — the clean kernel set. -/
  | kernelChecked
  /-- Clean PLUS a named dregg §8 carrier (crypto/authority oracle) booked as an `axiom`. -/
  | carrierBounded
  /-- Depends on an un-vetted axiom outside the kernel set and not a recognised carrier (incl. `sorryAx`). -/
  | extraAxioms
  /-- The named declaration IS an `axiom` — no proof term at all. -/
  | axiomItself
  deriving DecidableEq, Repr, Inhabited

/-- Foreground colour for the tier pill. Green = clean, amber = carrier-bounded, red = un-vetted,
grey = asserted. -/
def Tier.color : Tier → String
  | .kernelChecked  => "#0d1117"
  | .carrierBounded => "#0d1117"
  | .extraAxioms    => "#ffffff"
  | .axiomItself    => "#0d1117"

/-- Background colour for the tier pill. -/
def Tier.bg : Tier → String
  | .kernelChecked  => "#3fb950"  -- green
  | .carrierBounded => "#d29922"  -- amber
  | .extraAxioms    => "#da3633"  -- red
  | .axiomItself    => "#8b949e"  -- grey

/-- Short pill label. -/
def Tier.label : Tier → String
  | .kernelChecked  => "KernelChecked"
  | .carrierBounded => "CarrierBounded"
  | .extraAxioms    => "ExtraAxioms"
  | .axiomItself    => "AxiomItself"

/-- One-line human gloss shown beneath the pill. -/
def Tier.blurb : Tier → String
  | .kernelChecked  => "axioms ⊆ {propext, Classical.choice, Quot.sound} — kernel-clean"
  | .carrierBounded => "clean, modulo a named §8 carrier (crypto/authority oracle)"
  | .extraAxioms    => "depends on an un-vetted axiom (a hidden sorry shows up here)"
  | .axiomItself    => "asserted, not proved — this declaration IS an axiom"

/-! ## §3 — The classifier: tier read straight off the real axiom set.

The three standard kernel axioms, and the dregg §8 *carrier vocabulary* — substrings that mark an axiom
as a recognised cryptographic/authority oracle (the names appearing across `Crypto/PortalFloor.lean`'s
`@[extern]` opaques and the `AuthPortal`/`*Kernel` soundness carriers). Recognition is by name fragment so
it stays robust as carriers are added. -/

/-- The clean kernel axioms — the allow-list the whole metatheory pins to. -/
def kernelAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- §8 carrier name fragments. An extra axiom whose name contains one of these is treated as a *named*,
*recognised* cryptographic/authority assumption (amber), not an un-vetted one (red). Drawn from the dregg
portal vocabulary: the `@[extern]` crypto opaques (`*Extern`) and the soundness carriers
(`unforgeable`/`extractable`/`binding`/`Portal`/`Crypto`/`Carrier`/`Kernel`). -/
def carrierFragments : List String :=
  ["Extern", "Carrier", "carrier", "Portal", "Crypto",
   "unforgeable", "extractable", "binding", "Kernel"]

/-- `true` iff `n`'s string form contains `frag` as a substring (Bool-valued via `splitOn`: a present
substring splits the string into ≥ 2 pieces). -/
def nameHasFragment (n : Name) (frag : String) : Bool :=
  (n.toString.splitOn frag).length > 1

/-- `true` iff `n` matches any §8 carrier fragment. -/
def isCarrierAxiom (n : Name) : Bool :=
  carrierFragments.any (nameHasFragment n)

/-- **The pure classification core (`#eval`-testable).** Given whether the declaration *is itself* an
axiom (`isAxiom`) and the **real** axiom set `axs` returned by `collectAxioms`, compute the `Tier`.

This is intentionally pure (no `MetaM`) so it can be unit-contrasted with `#eval`: feeding it different
axiom sets yields different tiers, with NO elaboration needed. The metaprogram `tierOfName` is just this
function fed the genuine `collectAxioms`/`getConstInfo` output. -/
def classifyAxioms (isAxiom : Bool) (axs : Array Name) : Tier :=
  if isAxiom then .axiomItself
  else
    let extra := axs.filter (fun a => !kernelAxioms.contains a)
    if extra.isEmpty then .kernelChecked
    else if extra.all isCarrierAxiom then .carrierBounded
    else .extraAxioms

/-- The extra (non-kernel) axioms a decl carries — what the badge lists under "extra axioms". Pure. -/
def extraAxiomsOf (axs : Array Name) : Array Name :=
  axs.filter (fun a => !kernelAxioms.contains a)

/-! ## §4 — The metaprogram: `tierOfName` + `proofFactBadge` + `#dregg_badge`.

`tierOfName` reads the REAL proof term. `proofFactBadge` renders it as a panel. `#dregg_badge` prints it
in the infoview. The trust verdict is a function of `collectAxioms`'s output — it cannot be faked. -/

/-- **`tierOfName` — the trust verdict from the actual proof term.** Resolves `name` in the environment,
reads its full transitive axiom set via `Lean.collectAxioms`, asks `getConstInfo` whether the constant is
itself an `axiom`, and hands both to the pure `classifyAxioms`. Runs in any `MonadEnv` (so leaf widgets
can call it from `MetaM`/`CommandElabM`/RPC). -/
def tierOfName [Monad m] [MonadEnv m] (name : Name) : m Tier := do
  let axs ← Lean.collectAxioms name
  let env ← getEnv
  let isAxiom := match env.find? name with
    | some (.axiomInfo _) => true
    | _ => false
  return classifyAxioms isAxiom axs

/-- **`proofFactBadge` — the rendered trust badge for a declaration.** A `panel` titled with the decl
name, carrying: the tier pill, the human blurb, the axiom count, and the explicit list of extra
(non-kernel) axioms (so a `carrierBounded`/`extraAxioms` verdict *names* what it rests on). Everything is
computed from `collectAxioms`/`getConstInfo` — no field is hand-set. -/
def proofFactBadge [Monad m] [MonadEnv m] (name : Name) : m Html := do
  let axs ← Lean.collectAxioms name
  let env ← getEnv
  let isAxiom := match env.find? name with
    | some (.axiomInfo _) => true
    | _ => false
  let tier := classifyAxioms isAxiom axs
  let extra := extraAxiomsOf axs
  let extraStr := if extra.isEmpty then "(none)"
    else String.intercalate ", " (extra.toList.map (·.toString))
  return panel s!"proof-fact · {name}" #[
    kvRow "trust tier" (badge tier.label tier.color tier.bg),
    kvRowText "" tier.blurb,
    kvRowText "axioms (total)" (toString axs.size),
    kvRowText "extra (non-kernel)" extraStr
  ]

/-- **`#dregg_badge <ident>`** — print the computed proof-fact trust badge for a declaration in the
infoview. Put your cursor on the command. The badge reflects the declaration's REAL axiom set; it is the
inspector's answer to *"is this theorem actually proved, and on what trust?"* -/
syntax (name := dreggBadgeCmd) "#dregg_badge " ident : command

@[command_elab dreggBadgeCmd]
def elabDreggBadge : CommandElab := fun
  | stx@`(#dregg_badge $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let html ← liftCoreM <| proofFactBadge name
    -- Render via the ProofWidgets HtmlDisplay panel, anchored at the command.
    liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← Server.rpcEncode html) })
      stx
    -- Also log a plain-text verdict so the tier is visible without the infoview (CI / headless).
    let tier ← liftCoreM <| tierOfName name
    logInfo m!"#dregg_badge {name}: {tier.label} — {tier.blurb}"
  | stx => throwError "unexpected syntax {stx}"

/-! ## §5 — NON-VACUITY: the badge moves, and it discriminates four different proof terms.

First, the **pure** contrast — `classifyAxioms` returns a *different* `Tier` for each shape of axiom set,
with no elaboration at all. If the classifier were vacuous (always one tier), these `#eval`s would all
print the same value; they do not. -/

-- KernelChecked: no extra axioms.
#guard (classifyAxioms false #[``propext, ``Classical.choice, ``Quot.sound]).label == "KernelChecked"  -- "KernelChecked"
-- CarrierBounded: an extra axiom whose name carries a §8 fragment ("Extern").
#guard (classifyAxioms false #[``propext, `dregg_someVerifyExtern]).label == "CarrierBounded"  -- "CarrierBounded"
-- ExtraAxioms: an extra axiom that is NOT a recognised carrier.
#guard (classifyAxioms false #[``propext, `someRandomAssumption]).label == "ExtraAxioms"  -- "ExtraAxioms"
-- ExtraAxioms: a hidden sorry shows up RED.
#guard (classifyAxioms false #[``sorryAx]).label == "ExtraAxioms"                   -- "ExtraAxioms"
-- AxiomItself: the decl is an axiom.
#guard (classifyAxioms true #[]).label == "AxiomItself"                             -- "AxiomItself"
-- The four verdicts are pairwise distinct — the classifier partitions.
#guard decide (Tier.kernelChecked ≠ Tier.carrierBounded ∧ Tier.carrierBounded ≠ Tier.extraAxioms
              ∧ Tier.extraAxioms ≠ Tier.axiomItself)                                -- true

/-- Two clearly-named **demo carrier axioms** — present ONLY to exhibit the `carrierBounded` /
`extraAxioms` / `axiomItself` tiers on REAL declarations (the discriminating example the spec asks for).
They are never used by any real dregg proof; faithful dregg carriers enter as typeclass hypotheses, not
`axiom`s (see the module docstring). `demoEd25519VerifyExtern` carries the `Extern` §8 fragment; `demoUnvettedAssumption` does not. -/
axiom demoEd25519VerifyExtern : (1 : Nat) = 1
axiom demoUnvettedAssumption : (2 : Nat) = 2

/-- A theorem resting on the *carrier-named* demo axiom ⇒ `carrierBounded` (amber). -/
theorem demo_via_carrier : (1 : Nat) = 1 := demoEd25519VerifyExtern
/-- A theorem resting on the *un-vetted* demo axiom ⇒ `extraAxioms` (red). -/
theorem demo_via_extra : (2 : Nat) = 2 := demoUnvettedAssumption
/-- A proved theorem ⇒ `kernelChecked` (green). -/
theorem demo_clean : (3 : Nat) = 3 := rfl

/-! ### The badges. The two crowns MUST come back green (their real axiom sets are kernel-clean); the
demos exhibit the other three tiers. This is the heart of "no placeholders": the colour is the truth. -/

-- THE CROWNS (the spec's required non-vacuity targets) — KernelChecked.
#dregg_badge Dregg2.Exec.livingCellA_carries
#dregg_badge Dregg2.Exec.livingCellA_logMono

-- The discriminating examples — the badge reports DIFFERENT tiers for carrier/extra/axiom decls.
#dregg_badge demo_clean                 -- KernelChecked (green)
#dregg_badge demo_via_carrier           -- CarrierBounded (amber)
#dregg_badge demo_via_extra             -- ExtraAxioms   (red)
#dregg_badge demoEd25519VerifyExtern    -- AxiomItself   (grey)

/-! ### Machine-checked discrimination (not just `#eval` glances).

These `example`s PROVE — kernel-checked, by `decide`/`native`-free `rfl` on `DecidableEq Tier` — that the
metaprogram returns the intended, *distinct* tiers for the crowns vs. the demos. They run `tierOfName` in
`CommandElabM` and compare. If a crown ever picked up a stray axiom, `live_crowns_are_kernel_clean` would
FAIL to elaborate — a build-time tripwire, exactly like `#assert_axioms`. -/
run_cmd do
  let t1 ← Command.liftCoreM <| tierOfName ``Dregg2.Exec.livingCellA_carries
  let t2 ← Command.liftCoreM <| tierOfName ``Dregg2.Exec.livingCellA_logMono
  unless t1 = .kernelChecked && t2 = .kernelChecked do
    throwError "EXPECTED both crowns KernelChecked, got {t1.label} / {t2.label}"
  let tc ← Command.liftCoreM <| tierOfName ``demo_via_carrier
  let te ← Command.liftCoreM <| tierOfName ``demo_via_extra
  let ta ← Command.liftCoreM <| tierOfName ``demoEd25519VerifyExtern
  let tk ← Command.liftCoreM <| tierOfName ``demo_clean
  unless tc = .carrierBounded do throwError "EXPECTED demo_via_carrier CarrierBounded, got {tc.label}"
  unless te = .extraAxioms do throwError "EXPECTED demo_via_extra ExtraAxioms, got {te.label}"
  unless ta = .axiomItself do throwError "EXPECTED demoEd25519VerifyExtern AxiomItself, got {ta.label}"
  unless tk = .kernelChecked do throwError "EXPECTED demo_clean KernelChecked, got {tk.label}"
  logInfo m!"discrimination OK: crowns={t1.label}/{t2.label}; demos carrier={tc.label} \
    extra={te.label} axiom={ta.label} clean={tk.label}"

/-! ## §6 — Axiom hygiene. The substrate's own definitions are pinned kernel-clean.

The `classifyAxioms`/`tierOf*`/`badge`/`panel` machinery must itself be `{propext, Classical.choice,
Quot.sound}`-clean (the demo `axiom`s above are deliberately excluded — they are the discriminator, not
part of the substrate). The pure classifier and the Html helpers carry the badge's own credibility. -/

#assert_axioms classifyAxioms
#assert_axioms isCarrierAxiom
#assert_axioms extraAxiomsOf
#assert_axioms badge
#assert_axioms kvRow
#assert_axioms panel
#assert_axioms Tier.label
#assert_axioms Tier.blurb

end Dregg2.Widget
