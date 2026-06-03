/-
# Dregg2.Widget.ConservationLedger — the per-asset balance ledger of a REAL committed transfer,
charted, with the conservation law badged.

This leaf widget renders the per-asset conserved quantity of the dregg record kernel — the very
`cellObsA s b = recTotalAssetWithEscrow s.kernel b` the living-cell bisimulation observes
(`Dregg2/Exec/CellReal.lean:30`, `RecordKernel.lean:1136`) — *before* and *after* running the genuine
46-effect, auth-gated executor `execFullForestA` over a genuine conserving forest. It is the
quantitative companion to `Widget/DreggForest.lean`'s structural call-tree: that widget answers "what
does this turn DO?"; this one answers "what does it do to the BOOKS, and does anything leak?".

THE "NO PLACEHOLDERS" DISCIPLINE — every number on the chart is computed from the executor, never typed:

  * The driving value is `Dregg2.Exec.transferCF` (`CellReal.lean:140`): actor 0 transfers 30 of asset 0
    from cell 0 to cell 1, a `ConservingForest` (its `∀ b, Δ = 0` obligation is discharged in-tree). The
    initial state is `Dregg2.Exec.TurnExecutorFull.fma0` (`TurnExecutorFull.lean:4193`): a real 2-asset
    ledger — cell 0 holds 100 of asset 0 + 7 of asset 1, cell 1 holds 5 of asset 0 (asset-0 supply 105,
    asset-1 supply 7).
  * The "after" column is `(execFullForestA fma0 transferCF.1).getD fma0` — the ACTUAL committed kernel
    state the executor produces (the forest commits: `execFullForestA fma0 transferCF.1` is `some`). The
    per-asset totals (`recTotalAssetWithEscrow`) and the per-cell `bal` entries are then read straight off
    that state. There is no hand-entered "after" — swap the forest or the start state and every bar moves.
  * The chart series are the per-asset conserved totals (asset 0 and asset 1) BEFORE vs AFTER. Because the
    transfer is internal to asset 0 and touches neither asset's supply, both series land on the same value
    before and after — that visual flatness IS the conservation law, drawn from real numbers. The
    accompanying per-cell rows show the MOVEMENT underneath the conserved total (cell 0's asset-0 balance
    falls by 30, cell 1's rises by 30), so the chart is demonstrably non-trivial: the books move, the
    totals do not.

THE GUARANTEE, BADGED. The `#dregg_badge` at the bottom is anchored over the REAL keystone
`Dregg2.Exec.recKExecAsset_conserves_per_asset` (`RecordKernel.lean:544`) — the proof that
every committed per-asset transfer preserves `recTotalAsset k' b = recTotalAsset k b` for EVERY asset `b`.
The badge colour is a function of that theorem's real `collectAxioms` set (it comes back green —
kernel-clean), so the "conserved" claim under the chart is not decoration: it is the proof term's verdict.

Discipline: NO `sorry`/`admit`/`native_decide`/SMT, NO new `axiom`s. Every charting helper is a total,
term-level read of the real executor state; the pure derivations are `#assert_axioms`-pinned to the
standard kernel triple. The `#html`/`#eval`s at the bottom force the render path AND exhibit the
non-vacuity (the conserved totals are flat while the per-cell balances genuinely move).
-/
import Dregg2.Widget.Basic
import Dregg2.Exec.CellReal
import ProofWidgets.Component.Recharts

open Lean
open ProofWidgets
open ProofWidgets.Recharts
open scoped ProofWidgets.Jsx
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest

namespace Dregg2.Widget

/-! ## §1 — The REAL before/after states, straight from the executor.

`ledgerBefore` is the genuine start state `fma0`; `ledgerAfter` is what `execFullForestA` actually
commits when fed the conserving `transferCF` forest (`getD` self-loops on the inadmissible case, but this
forest commits — see the `#eval` non-vacuity below). Nothing here is hand-built: the "after" state is the
executor's own output over the real forest. -/

/-- The kernel state BEFORE the turn — the real `fma0` 2-asset ledger. -/
def ledgerBefore : RecordKernelState := fma0.kernel

/-- The kernel state AFTER the turn — the ACTUAL state `execFullForestA` commits for `transferCF`
(stay-put `getD` only on an inadmissible turn; this conserving transfer commits). Read off the executor,
never typed in. -/
def ledgerAfter : RecordKernelState := ((execFullForestA fma0 transferCF.1).getD fma0).kernel

/-- The assets the chart covers — exactly the asset classes `fma0` actually carries balances in (asset 0
and asset 1). A small fixed index set, but the VALUES at each index are read from the executor. -/
def chartedAssets : List AssetId := [0, 1]

/-- The cells the per-cell breakdown covers — the live `accounts` of `fma0` (cells 0 and 1). -/
def chartedCells : List CellId := [0, 1]

/-! ## §2 — The charted quantity: the per-asset CONSERVED total (`recTotalAssetWithEscrow`).

This is precisely `cellObsA`'s observation — the per-asset vector the living-cell bisimulation tracks and
that `recKExecAsset_conserves_per_asset` proves invariant on committed transfers. A scalar aggregate would
hide a cross-asset launder; the per-asset vector does not. We read it off both states; the conservation
law predicts (and the kernel proves) that each entry is unchanged across a committed transfer. -/

/-- The per-asset conserved total of asset `b` in kernel state `k`: `recTotalAsset k b` plus off-ledger
escrow held at `b` (here escrow is empty, so it is the ledger supply). The exact `cellObsA` observation. -/
def conservedTotal (k : RecordKernelState) (b : AssetId) : ℤ := recTotalAssetWithEscrow k b

/-- One chart datum per asset: `{ asset, before, after }`, each value the REAL conserved total read off
the corresponding kernel state. Fed directly to Recharts `LineChart.data`. -/
def assetRow (b : AssetId) : Json :=
  json% {
    asset:  $(toJson s!"asset {b}"),
    before: $(toJson (conservedTotal ledgerBefore b)),
    after:  $(toJson (conservedTotal ledgerAfter b))
  }

/-- The Recharts `data` array — one datum per charted asset, every number from the executor. -/
def ledgerData : Array Json := (chartedAssets.map assetRow).toArray

/-! ## §3 — The per-cell movement underneath the conserved total (the `bal` ledger itself).

The conserved totals are flat (that is the law); the MOVEMENT lives in the per-cell `bal : CellId →
AssetId → ℤ` entries. These rows surface that movement — cell 0's asset-0 balance falls, cell 1's rises,
their sum (the conserved total) unchanged — so the widget visibly shows BOTH the invariant and the
non-trivial transfer beneath it. The delta is read off the two real states. -/

/-- The change in cell `c`'s asset-`a` balance across the committed turn: `after − before`, both read off
the real `bal` ledger. -/
def balDelta (c : CellId) (a : AssetId) : ℤ := ledgerAfter.bal c a - ledgerBefore.bal c a

/-- A signed integer as a short string with an explicit sign (`+30` / `-30` / `0`). -/
def signedStr (z : ℤ) : String := if z > 0 then s!"+{z}" else toString z

/-- One per-cell row for asset `a`: `cell c · before → after (Δ)`, all from the real `bal` ledger. -/
def cellBalRow (a : AssetId) (c : CellId) : Html :=
  let before := ledgerBefore.bal c a
  let after  := ledgerAfter.bal c a
  let d      := balDelta c a
  kvRow s!"cell {c} · asset {a}"
    (badge s!"{before} → {after}  ({signedStr d})"
      valColor
      (if d = 0 then panelBorder else "#1f6feb33"))

/-! ## §4 — The chart + the ledger panel.

`ledgerChart` is the Recharts `LineChart` of the per-asset conserved totals (two series: before/after).
`conservationPanel` wraps it with the per-cell movement rows and a per-asset conserved/violated verdict
(read off the data: `before = after` ⇒ conserved). Reuses the `Basic.lean` palette so it matches the
inspector look. -/

/-- The Recharts line chart of per-asset conserved totals — X axis = asset class, two lines
(before vs after). The `data` is `ledgerData` (real executor numbers); a flat pair of lines per asset is
the conservation law made visible. -/
def ledgerChart : Html :=
  <LineChart width={460} height={260} data={ledgerData}>
    <XAxis dataKey?={toJson "asset"} type={.category} />
    <YAxis allowDataOverflow={Bool.false} />
    <Line type={.monotone} dataKey={toJson "before"} stroke="#8b949e" dot?={Bool.true} />
    <Line type={.monotone} dataKey={toJson "after"}  stroke="#3fb950" dot?={Bool.true} />
  </LineChart>

/-- A per-asset conserved/violated verdict row, READ off the chart data: the conserved total before vs
after, with a green "conserved" pill iff they are equal (they are — that is the proved law). -/
def assetVerdictRow (b : AssetId) : Html :=
  let before := conservedTotal ledgerBefore b
  let after  := conservedTotal ledgerAfter b
  let ok     := before = after
  kvRow s!"asset {b} total"
    (badge (if ok then s!"{before} → {after}  conserved" else s!"{before} → {after}  VIOLATED")
      (if ok then "#0d1117" else "#ffffff")
      (if ok then "#3fb950" else "#da3633"))

/-- **The conservation ledger panel.** A titled dark card: the per-asset chart on top, then the per-asset
conserved-total verdicts, then the per-cell `bal` movement rows that show the transfer beneath the
invariant. Every number is computed from `execFullForestA fma0 transferCF.1` — the REAL committed turn. -/
def conservationLedgerPanel : Html :=
  <div style={json% {
      background: $panelBg,
      border: $("1px solid " ++ panelBorder),
      borderRadius: "8px",
      padding: "12px 14px",
      maxWidth: "560px",
      fontFamily: "ui-sans-serif, system-ui, sans-serif",
      color: $valColor
    }}>
    <div style={json% {fontSize: "13px", fontWeight: "700", marginBottom: "2px"}}>
      {.text "dregg conservation ledger · transferCF over fma0 (committed)"}
    </div>
    <div style={json% {fontSize: "11px", color: $keyColor, marginBottom: "10px"}}>
      {.text "per-asset conserved total (recTotalAssetWithEscrow = cellObsA) before vs after a REAL execFullForestA commit · grey = before, green = after"}
    </div>
    {ledgerChart}
    <div style={json% {marginTop: "10px"}}>
      {.element "div" #[] ((chartedAssets.map assetVerdictRow).toArray)}
    </div>
    <div style={json% {marginTop: "8px", fontSize: "11px", color: $keyColor,
        fontFamily: "ui-sans-serif, system-ui, sans-serif", marginBottom: "4px"}}>
      {.text "movement underneath the conserved total — the per-cell bal ledger (the books move, the totals do not):"}
    </div>
    {.element "div" #[]
      ((chartedAssets.flatMap (fun a => chartedCells.map (cellBalRow a))).toArray)}
  </div>

/-! ## §5 — Force the render over the REAL value (`#html`), then BADGE the conservation guarantee.

`#html conservationLedgerPanel` elaborates the whole derivation — `execFullForestA fma0 transferCF.1`,
`recTotalAssetWithEscrow` on both states, the per-cell `bal` reads — and saves the widget, so the verify
step genuinely exercises the chart's render path over the executor's real output. The `#dregg_badge`
anchors the conservation keystone: its colour is the proof term's verdict (green = kernel-clean). -/

-- THE RENDER DRIVER — elaborates the chart over the real committed transfer.
#html conservationLedgerPanel

-- THE GUARANTEE — the per-asset conservation keystone, badged from its REAL axiom set (kernel-clean).
#dregg_badge Dregg2.Exec.recKExecAsset_conserves_per_asset

/-! ## §6 — NON-VACUITY (`#eval`): the transfer COMMITS, the totals are FLAT, the per-cell books MOVE.

If the widget were placeholder, these would not track the executor. They do: the forest commits, each
per-asset conserved total is literally equal before and after (the law), AND the per-cell balances change
by ±30 (a real transfer beneath the invariant). The conserved-vs-moved contrast is the non-vacuity. -/

-- The forest genuinely commits (so `ledgerAfter` is the executor's output, not the `getD` fallback).
#eval (execFullForestA fma0 transferCF.1).isSome                              -- true
-- The per-asset conserved totals BEFORE — the real `fma0` supplies (asset 0 = 105, asset 1 = 7).
#eval chartedAssets.map (conservedTotal ledgerBefore)                          -- [105, 7]
-- The per-asset conserved totals AFTER — IDENTICAL (the proved conservation law, from real numbers).
#eval chartedAssets.map (conservedTotal ledgerAfter)                           -- [105, 7]
-- Machine-checked flatness: every charted asset's conserved total is unchanged across the commit.
#eval chartedAssets.all (fun b => decide (conservedTotal ledgerAfter b = conservedTotal ledgerBefore b))  -- true
-- …yet the per-cell `bal` ledger genuinely MOVES — cell 0's asset 0 falls 30, cell 1's rises 30 (NOT flat).
#eval balDelta 0 0                                                             -- -30
#eval balDelta 1 0                                                             -- +30
-- The contrast that proves non-vacuity: totals flat (Δ=0) WHILE the books move (Δ≠0) — a real transfer,
-- conserved. (`true` = "some per-cell delta is nonzero" — the chart is not a constant.)
#eval (chartedCells.any (fun c => decide (balDelta c 0 ≠ 0)))                   -- true
-- The chart `data` itself, as fed to Recharts — real numbers, one datum per asset (no placeholder).
#eval ledgerData.size                                                          -- 2

/-! ## §7 — Axiom hygiene. The pure ledger derivations are pinned kernel-clean.

The functions that PRODUCE the chart numbers — the conserved-total read, the per-cell delta, the datum
builder — must themselves rest on nothing but `{propext, Classical.choice, Quot.sound}`; they carry the
widget's "computed, not faked" credibility. (The `Html` builders inherit ProofWidgets' own clean axioms;
we pin the dregg-specific derivations. The badged guarantee `recKExecAsset_conserves_per_asset` is pinned
at its own definition site, `RecordKernel.lean:2540`.) -/

#assert_axioms conservedTotal
#assert_axioms balDelta
#assert_axioms assetRow
#assert_axioms ledgerData
#assert_axioms signedStr

end Dregg2.Widget
