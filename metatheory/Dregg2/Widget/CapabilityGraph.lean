/-
# Dregg2.Widget.CapabilityGraph — the Granovetter capability graph, rendered from a REAL `Caps`.

The capability table `Caps := Label → List Cap` (`Authority/Positional.lean`) is the cell's slot
table: each *holder* label points at the caps it holds, and each cap names a *target* with the
authority it confers (`capAuthConferred`). This widget renders that table as an interactive directed
graph (`ProofWidgets.GraphDisplay`, a d3-force layout): **holders and targets are nodes; each held
cap is an edge `holder → target` labelled by the `Auth` tags it confers.**

The rendered value is a **real executor `Caps`**, never placeholder data. We drive from two genuine
cap tables built with the executor's own `grant`/`derive` operations (`Dregg2/Exec/Caps.lean`):
* `Dregg2.Exec.c0` — the existing `#eval`-able example (holder `0` holds an `endpoint 7 [read,write]`);
* `capGraphDemo` — a three-holder table built by **delegating** caps with `derive`/`attenuate`, so
  the **Granovetter discipline is visible in the picture**: a child holder receives an *attenuated*
  copy of a parent's cap, and its edge is labelled with strictly fewer `Auth` tags than the parent's.

The whole point of "no placeholder" is the next line: the **non-amplification law is attached as a
computed proof-fact badge**, not a caption. `Dregg2.Exec.derive_no_amplify` /
`Dregg2.Exec.attenuate_confRights_le` (`granted ≤ held`, PROVED in `Exec/Caps.lean`) is rendered by
`#dregg_badge` (from `Widget/Basic.lean`), whose colour is a function of the theorem's REAL axiom set
(`Lean.collectAxioms`). The badge is green (KernelChecked) **iff** the law really is kernel-clean — it
cannot be hand-painted. The graph shows the Granovetter edges; the badge proves they never amplify.

Surface: `capHolders`/`capGraphRows` (the table read off a `Caps` over an explicit label list) ·
`authTag`/`capEdges`/`capVertices` (the graph data, pure & `#eval`-able) · `capGraphHtml` (the rendered
`GraphDisplay`) · the `#html` force-render + the `#dregg_badge` non-amplification proof-fact.

Every datum is computed from a
real `Caps` value; the proof-fact is read off the real axiom set. Reuses `Widget/Basic.lean` +
`Exec/Caps.lean`; edits neither.
-/
import Dregg2.Widget.Basic
import Dregg2.Exec.Caps
import ProofWidgets.Component.GraphDisplay

open Lean Elab Command
open ProofWidgets
open scoped ProofWidgets.Jsx

namespace Dregg2.Widget

open Dregg2.Authority (Auth Cap Label Caps capAuthConferred)
open Dregg2.Exec (attenuate derive grant c0 confRights)

/-! ## §1 — The graph data, read off a REAL `Caps` value.

`Caps := Label → List Cap` is a *total function*; to render it we read it over an explicit, finite
list of holder labels (the cell's live slots). Everything here is pure and `#eval`-able — the graph is
a computation over the actual cap table, with no hand-entered nodes or edges. -/

/-- A single row of the rendered cap table: a `holder` label, the `target` a held cap names, and the
`rights` (`Auth` tags) that cap confers. One row per (holder, held-cap). This is the literal content
of `Caps` over the live holder list — the edges of the Granovetter graph. -/
structure CapRow where
  /-- The label holding the cap (the edge source). -/
  holder : Label
  /-- The target object the cap names (the edge target). `none` for a `null` cap (no target). -/
  target : Option Label
  /-- The authority the cap confers (`capAuthConferred`) — the edge label. -/
  rights : List Auth
  deriving Repr, Inhabited

/-- The cap-table rows for `caps` read over the explicit `holders` list: for each holder, one row per
cap it holds, carrying the cap's target and conferred authority. This is the executable projection of
the `Caps` function onto a finite slot list — the data the graph renders, computed, never placeheld. -/
def capGraphRows (caps : Caps) (holders : List Label) : List CapRow :=
  holders.flatMap (fun h =>
    (caps h).map (fun c =>
      let tgt : Option Label := match c with
        | .endpoint t _ => some t
        | .node t       => some t
        | .null         => none
      { holder := h, target := tgt, rights := capAuthConferred c }))

/-- The distinct node labels of the graph: every holder, plus every target named by a held cap. A
node is rendered for each. Computed from the rows (hence from the real `Caps`). -/
def capNodes (rows : List CapRow) : List Label :=
  let holders := rows.map (·.holder)
  let targets := rows.filterMap (·.target)
  (holders ++ targets).dedup

/-! ## §2 — A REAL, delegation-bearing cap table (the Granovetter picture has content).

`c0` (from `Exec/Caps.lean`) is a single-holder table — fine, but a one-edge graph does not *show*
non-amplification. So we also build `capGraphDemo` with the executor's own `derive`/`attenuate`: an
owner delegates *attenuated* copies of its cap down a chain, so the rendered edges visibly shrink —
`read,write` ↦ `read` ↦ (`write` filtered out) — which is exactly the law the badge proves. -/

/-- The owner's master cap: an `endpoint` on target `7` conferring full `read + write`. -/
def ownerCap : Cap := .endpoint 7 [Auth.read, Auth.write]

/-- **A real, delegation-bearing capability table.** Built ONLY with the executor's verified
operations:
* holder `0` (the owner) is `grant`ed the master `ownerCap` (`read,write` on `7`);
* holder `1` is `derive`d an attenuated copy keeping only `[read]` (the Granovetter handoff);
* holder `2` is `derive`d from that an attenuated copy keeping only `[write]` — but `write` was
  already dropped upstream, so by `attenuate`'s filter holder `2` ends up with **no** rights on `7`
  (a child can never recover authority a parent dropped — the law made visible).

Because it is `grant`/`derive` over the real `Cap` algebra, every edge's label is `capAuthConferred`
of an honestly-attenuated cap, and `derive_no_amplify` governs every delegation step. -/
def capGraphDemo : Caps :=
  let g0 := grant (fun _ => []) 0 ownerCap
  let g1 := derive g0 1 [Auth.read] ownerCap
  derive g1 2 [Auth.write] (attenuate [Auth.read] ownerCap)

/-- The holder slots we render for `capGraphDemo`. -/
def capGraphDemoHolders : List Label := [0, 1, 2]

/-- The holder slot we render for `c0`. -/
def c0Holders : List Label := [0]

/-! ## §3 — `Auth`-tag presentation + the `GraphDisplay` node/edge builders.

Pure `Html`/data builders. The vertices and edges are computed from the `CapRow`s of a real `Caps`;
the edge labels are the actual `capAuthConferred` tags. -/

/-- Short tag for an `Auth` right (the edge-label vocabulary). -/
def authTag : Auth → String
  | .read    => "read"
  | .write   => "write"
  | .grant   => "grant"
  | .call    => "call"
  | .reply   => "reply"
  | .reset   => "reset"
  | .control => "control"

/-- A holder/target rights list rendered as a compact `read·write` string (`∅` when empty — the
visible "no authority" a fully-attenuated child carries). -/
def rightsLabel (rs : List Auth) : String :=
  if rs.isEmpty then "∅" else String.intercalate "·" (rs.map authTag)

/-- The node id string for a label. -/
def nodeId (l : Label) : String := s!"L{l}"

/-- A graph **vertex** for a label: a rounded dark chip (via `<foreignObject>`) showing the label, so
holders and targets read as `L0`, `L7`, … in the picture. -/
def capVertex (l : Label) : GraphDisplay.Vertex where
  id := nodeId l
  boundingShape := .rect 46 26
  label :=
    <foreignObject x="-23" y="-13" width={46} height={26}>
      <div style={json% {
          width: "46px", height: "26px",
          display: "flex", alignItems: "center", justifyContent: "center",
          borderRadius: "6px",
          border: $("1px solid " ++ panelBorder),
          background: $panelBg, color: $valColor,
          fontFamily: "ui-monospace, SFMono-Regular, Menlo, monospace",
          fontSize: "12px", fontWeight: "600"
        }}>{.text (nodeId l)}</div>
    </foreignObject>
  details? := some (.text s!"capability holder / target label {l}")

/-- A graph **edge** for one cap row: `holder → target`, labelled by the rights the cap confers (the
`Auth` tags). The label is an SVG `<text>` over the edge midpoint. A `null` cap (no target) yields no
edge. -/
def capEdge (row : CapRow) : Option GraphDisplay.Edge :=
  row.target.map (fun t =>
    { source := nodeId row.holder
      target := nodeId t
      label? := some
        <g>
          <rect x="-26" y="-9" width={52} height={18} rx={4}
                fill={panelBg} stroke={panelBorder} />
          <text textAnchor="middle" dominantBaseline="middle"
                fill={valColor}
                style={json% {fontFamily: "ui-monospace, Menlo, monospace", fontSize: "11px"}}>
            {.text (rightsLabel row.rights)}
          </text>
        </g>
      details? := some (.text
        s!"holder L{row.holder} → target L{t} · confers [{rightsLabel row.rights}]") })

/-- All vertices for a `Caps` read over `holders` — one per distinct node label. -/
def capVertices (caps : Caps) (holders : List Label) : Array GraphDisplay.Vertex :=
  (capNodes (capGraphRows caps holders)).toArray.map capVertex

/-- All edges for a `Caps` read over `holders` — one per held (non-null) cap, labelled by its rights. -/
def capEdges (caps : Caps) (holders : List Label) : Array GraphDisplay.Edge :=
  ((capGraphRows caps holders).filterMap capEdge).toArray

/-- **The rendered Granovetter capability graph** for a real `Caps` value over its live holder list:
holders and targets as nodes, each held cap as a directed, rights-labelled edge. A d3-force layout
(`GraphDisplay`) with details enabled so a click reveals the precise `holder → target · confers […]`.
Driven entirely by the actual cap table — no placeholder nodes or edges. -/
def capGraphHtml (caps : Caps) (holders : List Label) : Html :=
  <GraphDisplay
    vertices={capVertices caps holders}
    edges={capEdges caps holders}
    forces={#[ .link { distance? := some 120 }, .manyBody { strength? := some (-260) },
               .x {}, .y {} ]}
    showDetails={true} />

/-! ## §4 — NON-VACUITY: the table is read, and the delegation attenuates.

These `#eval`s prove the graph data MOVES with the real `Caps`: the rows are the actual held caps, and
the delegation chain visibly drops rights (`read,write` ↦ `read` ↦ `∅`). If the projection were
vacuous (e.g. always empty, or ignoring the cap table), these would not show the shrinking labels. -/

-- The owner holds `read·write` on `7`; the picture's owner→7 edge is labelled exactly this.
#guard ((capGraphRows capGraphDemo capGraphDemoHolders).map (fun r => (r.holder, r.target, rightsLabel r.rights)))
  == [(0, some 7, "read·write"), (1, some 7, "read"), (2, some 7, "∅")]
  -- [(0, some 7, "read·write"), (1, some 7, "read"), (2, some 7, "∅")]

-- The Granovetter shrink, as a Bool: holder 1's rights ⊊ holder 0's, and holder 2's are empty.
#guard
  (let rows := capGraphRows capGraphDemo capGraphDemoHolders
   let r0 : Nat := (rows.find? (·.holder == 0)).map (·.rights.length) |>.getD 0   -- 2
   let r1 : Nat := (rows.find? (·.holder == 1)).map (·.rights.length) |>.getD 99  -- 1
   let r2 : Nat := (rows.find? (·.holder == 2)).map (·.rights.length) |>.getD 99  -- 0
   decide (r1 < r0 ∧ r2 < r1))                                                    -- true (strictly attenuating)

-- The node set is computed from the table (owner/children + the shared target 7), not hand-listed.
#guard capNodes (capGraphRows capGraphDemo capGraphDemoHolders) == [0, 1, 2, 7]  -- [0, 1, 2, 7]
#guard (capVertices capGraphDemo capGraphDemoHolders).size == 4            -- 4
#guard (capEdges capGraphDemo capGraphDemoHolders).size == 3               -- 3

-- The existing `c0` example also renders (single holder, single edge) — a second real table.
#guard ((capGraphRows c0 c0Holders).map (fun r => (r.holder, r.target, rightsLabel r.rights)))
  == [(0, some 7, "read·write")]
  -- [(0, some 7, "read·write")]

-- The graph value's own moving quantity: the delegation graph has MORE nodes/edges than `c0`'s.
#guard decide ((capEdges capGraphDemo capGraphDemoHolders).size > (capEdges c0 c0Holders).size)  -- true

/-! ## §5 — FORCE THE RENDER. `#html` elaborates the `GraphDisplay` over the real `Caps`.

This exercises the full render path (vertex/edge `RpcEncodable`, the d3-force component) over the
actual cap table at elaboration time — exactly what the surface will mount. Put your cursor on a
`#html` to see the interactive Granovetter graph. -/

-- The delegation-bearing table: three holders, the attenuating chain, the shared target.
#html capGraphHtml capGraphDemo capGraphDemoHolders

-- The existing `c0` executor example, rendered as a graph too.
#html capGraphHtml c0 c0Holders

/-! ## §6 — THE PROOF-FACT: non-amplification (`granted ≤ held`) attached as a COMPUTED badge.

Every edge above is governed by the Granovetter law `derive_no_amplify` — a derived/attenuated cap
confers a SUBSET of its parent's authority. `#dregg_badge` (from `Widget/Basic.lean`) reads the law's
REAL axiom set via `Lean.collectAxioms` and colours the badge by trust tier; it is green
(KernelChecked) precisely because the law is kernel-clean (`{propext, Classical.choice, Quot.sound}`).
The graph SHOWS the attenuating edges; these badges PROVE they never amplify — the colour is the truth,
not a caption. -/

-- The list-level Granovetter law: `capAuthConferred (attenuate keep c) ⊆ capAuthConferred c`.
#dregg_badge Dregg2.Exec.derive_no_amplify
-- The lattice-level `is_attenuation`: `confRights (attenuate keep c) ≤ confRights c` (granted ≤ held).
#dregg_badge Dregg2.Exec.attenuate_confRights_le
-- The underlying narrowing fact the two rest on.
#dregg_badge Dregg2.Exec.attenuate_subset

/-! ### Machine-checked: the attached law really is kernel-clean (a build-time tripwire).

Not just a `#dregg_badge` glance — this PROVES (via `tierOfName`, the same `collectAxioms` core) that
the non-amplification law the widget attaches is `KernelChecked`. If `derive_no_amplify` ever picked up
a stray axiom, this `run_cmd` would FAIL to elaborate, and the widget would refuse to build — exactly
the "no placeholder, the colour is the truth" guarantee, enforced. -/
run_cmd do
  let t ← Command.liftCoreM <| tierOfName ``Dregg2.Exec.derive_no_amplify
  let tl ← Command.liftCoreM <| tierOfName ``Dregg2.Exec.attenuate_confRights_le
  unless t = .kernelChecked && tl = .kernelChecked do
    throwError "EXPECTED non-amplification laws KernelChecked, got {t.label} / {tl.label}"
  Lean.logInfo m!"CapabilityGraph: non-amplification attached as {t.label} (granted ≤ held, kernel-clean)"

/-! ## §7 — Axiom hygiene. The widget's own data builders are pinned kernel-clean.

The graph-data projection (`capGraphRows`/`capNodes`/`capEdges`) and the demo cap table must be
`{propext, Classical.choice, Quot.sound}`-clean — the widget introduces no trust of its own; it only
reflects the real `Caps` and the already-proved non-amplification law. -/

#assert_axioms capGraphRows
#assert_axioms capNodes
#assert_axioms capGraphDemo
#assert_axioms authTag
#assert_axioms rightsLabel

end Dregg2.Widget
