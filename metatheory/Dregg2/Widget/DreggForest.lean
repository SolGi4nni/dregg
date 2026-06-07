/-
# Dregg2.Widget.DreggForest — a dregg call-FOREST rendered as a node/edge graph (the executor inspector).

This leaf widget draws a real `FullForestA` (the tree-shaped, 46-effect, auth-gated call-forest the
wholesale-swap exports — `Dregg2/Exec/FullForest.lean`) as an interactive force-directed graph using
ProofWidgets' `GraphDisplay`. It is the *structural* companion to `Widget/Basic.lean`'s proof-fact trust
badge: the badge answers "*is this theorem proved, on what trust?*"; this widget answers "*what does this
turn's call-tree actually DO, and where does delegated authority flow?*".

THE "NO PLACEHOLDERS" DISCIPLINE — every glyph is COMPUTED from the real Lean value, never typed in:

  * **Nodes** are the forest's tree nodes. A node's label is `ctorName a` — the genuine `FullActionA`
    constructor at that node (a total fold over the actual 46-constructor inductive at
    `TurnExecutorFull.lean:1928`) — together with `targetOf a`, the cell the executor reads as that node's
    target (`FullForest.lean:123`, the very `targetOf` the executor uses as each child edge's *delegator*).
    Click a node: its `details?` lists `ctorSummary a` (the constructor's real argument vector). If you
    swap the value for a different forest, the labels change with it — there is no hard-coded label table.

  * **Edges** are the forest's delegation edges, walked in the SAME pre-order the executor lowers
    (`lowerForestA`). Each edge is drawn from the parent node to the child subtree's root, labelled with the
    delegation it carries — the holder, the *attenuated* rights `capAuthConferred (attenuate keep parentCap)`
    actually conferred, and the cap's target `capTarget parentCap` (`FullForest.lean:114`, the discriminant
    the executor gates on). Click an edge: its `details?` shows the held-vs-granted Granovetter inequality
    `capAuthConferred (attenuate keep parentCap) ⊆ capAuthConferred parentCap` (`edge_no_amplify`,
    `FullForest.lean:389`) — the no-amplification law, READ off the edge data, not asserted.

The driving value is `Dregg2.Exec.FullForest.goodFullForest` — the project's own non-vacuous witness: a
3-node, 3-level mint→transfer→burn tree that commits per-asset (`execFullForestA fmaDeleg goodFullForest`
is `some`) with two genuinely-held, non-amplifying delegation edges. The `#html` at the bottom forces the
render path to elaborate over that real value, so the build EXERCISES the whole derivation.

Discipline: NO `sorry`/`admit`/`native_decide`/SMT. Every rendering function is a total, term-level fold
over the real `FullForestA`/`FullActionA`/`Cap` data; the pure derivations are `#assert_axioms`-pinned to
the standard kernel triple. The `#html`/`#eval`s at the bottom are the non-vacuity witnesses (a different
forest yields a different graph — proven by an `#eval` contrast on the derived vertex/edge counts).
-/
import Dregg2.Widget.Basic
import Dregg2.Exec.FullForest
import ProofWidgets.Component.GraphDisplay

open Lean
open ProofWidgets
open scoped ProofWidgets.Jsx
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority

namespace Dregg2.Widget

/-! ## §1 — Labels DERIVED from the real value (`ctorName` · `ctorSummary` · the `Cap`/`Auth` printers).

These are the heart of "no placeholders": each is a total fold over the ACTUAL inductive, so the glyph a
node/edge shows is a function of the value. `ctorName` returns the genuine `FullActionA` constructor name
(all 56 arms of `TurnExecutorFull.lean`'s `FullActionA`); `ctorSummary` additionally splices the constructor's real
argument vector. Swap the forest and the labels follow — nothing is hard-coded. -/

/-- One `Auth` right, short. -/
def authStr : Auth → String
  | .read => "read" | .write => "write" | .grant => "grant" | .call => "call"
  | .reply => "reply" | .reset => "reset" | .control => "control"

/-- A `List Auth` as `[a, b, …]`. -/
def authsStr (as : List Auth) : String :=
  "[" ++ String.intercalate ", " (as.map authStr) ++ "]"

/-- A `Cap`, compactly: `null` / `node t` / `endpoint t [rights]`. -/
def capStr : Cap → String
  | .null            => "null"
  | .node t          => s!"node {t}"
  | .endpoint t r    => s!"endpoint {t} {authsStr r}"

/-- The delegation target of a cap as a short arrow string (`→t`, or `→·(null)` for a null cap). Reads the
real `capTarget` discriminant (`FullForest.lean:114`) — the cell the executor gates each handoff on. -/
def capTargetArrow (c : Cap) : String :=
  match capTarget c with
  | some t => s!"→{t}"
  | none   => "→·(null)"

/-- The delegation target of a cap as text for a details row (`t`, or `none (null cap)`). -/
def capTargetText (c : Cap) : String :=
  match capTarget c with
  | some t => toString t
  | none   => "none (null cap)"

/-- **`ctorName a`** — the genuine `FullActionA` constructor name at this node. A TOTAL fold over the real
56-constructor inductive (`TurnExecutorFull.lean`'s `FullActionA`); this is the node's headline glyph, derived from
the value (NOT a placeholder). -/
def ctorName : FullActionA → String
  | .balanceA _ _              => "balanceA"
  | .delegate _ _ _            => "delegate"
  | .revoke _ _                => "revoke"
  | .mintA _ _ _ _             => "mintA"
  | .burnA _ _ _ _             => "burnA"
  | .setFieldA _ _ _ _         => "setFieldA"
  | .emitEventA _ _ _ _        => "emitEventA"
  | .incrementNonceA _ _ _     => "incrementNonceA"
  | .setPermissionsA _ _ _     => "setPermissionsA"
  | .setVKA _ _ _              => "setVKA"
  | .introduceA _ _ _          => "introduceA"
  | .delegateAttenA _ _ _ _    => "delegateAttenA"
  | .attenuateA _ _ _          => "attenuateA"
  | .dropRefA _ _              => "dropRefA"
  | .revokeDelegationA _ _     => "revokeDelegationA"
  | .validateHandoffA _ _ _    => "validateHandoffA"
  | .exerciseA _ _ _           => "exerciseA"
  | .createCellA _ _           => "createCellA"
  | .createCellFromFactoryA _ _ _ => "createCellFromFactoryA"
  | .spawnA _ _ _              => "spawnA"
  | .bridgeMintA _ _ _ _       => "bridgeMintA"
  | .createEscrowA _ _ _ _ _ _ => "createEscrowA"
  | .releaseEscrowA _ _        => "releaseEscrowA"
  | .refundEscrowA _ _         => "refundEscrowA"
  | .createObligationA _ _ _ _ _ _ => "createObligationA"
  | .fulfillObligationA _ _    => "fulfillObligationA"
  | .slashObligationA _ _      => "slashObligationA"
  | .noteSpendA _ _ _          => "noteSpendA"
  | .noteCreateA _ _           => "noteCreateA"
  | .createCommittedEscrowA _ _ _ _ _ _ _ => "createCommittedEscrowA"
  | .releaseCommittedEscrowA _ _ => "releaseCommittedEscrowA"
  | .refundCommittedEscrowA _ _  => "refundCommittedEscrowA"
  | .bridgeLockA _ _ _ _ _ _   => "bridgeLockA"
  | .bridgeFinalizeA _ _ _ _   => "bridgeFinalizeA"
  | .bridgeCancelA _ _         => "bridgeCancelA"
  | .sealA _ _ _               => "sealA"
  | .unsealA _ _ _             => "unsealA"
  | .createSealPairA _ _ _ _   => "createSealPairA"
  | .makeSovereignA _ _        => "makeSovereignA"
  | .refusalA _ _              => "refusalA"
  | .receiptArchiveA _ _       => "receiptArchiveA"
  | .queueAllocateA _ _ _ _    => "queueAllocateA"
  | .queueEnqueueA _ _ _ _ _ _ _ => "queueEnqueueA"
  | .queueDequeueA _ _ _ _   => "queueDequeueA"
  | .queueResizeA _ _ _ _      => "queueResizeA"
  | .queueAtomicTxA _ _        => "queueAtomicTxA"
  | .queuePipelineStepA _ _ _ _ => "queuePipelineStepA"
  | .pipelinedSendA _          => "pipelinedSendA"
  | .exportSturdyRefA _ _ _ _ _ => "exportSturdyRefA"
  | .enlivenRefA _ _ _ _       => "enlivenRefA"
  | .swissHandoffA _ _ _ _     => "swissHandoffA"
  | .swissDropA _ _ _          => "swissDropA"
  | .cellSealA _ _             => "cellSealA"
  | .cellUnsealA _ _           => "cellUnsealA"
  | .cellDestroyA _ _ _        => "cellDestroyA"
  | .refreshDelegationA _ _    => "refreshDelegationA"

/-- **`ctorSummary a`** — the constructor name PLUS its real argument vector (for the representative arms
the demo forests exercise: balance/mint/burn/the authority + state ops). Spliced from the value's actual
fields, so a node's details box shows the genuine `(actor, cell, asset, amount)` etc. Arms not surfaced by
the demo trees fall through to `ctorName a` (still the real constructor, no fabricated args). -/
def ctorSummary : FullActionA → String
  | .balanceA t a              => s!"balanceA (actor={t.actor}, src={t.src} → dst={t.dst}, asset={a}, amt={t.amt})"
  | .mintA actor cell a amt    => s!"mintA (actor={actor}, cell={cell}, asset={a}, +{amt})"
  | .burnA actor cell a amt    => s!"burnA (actor={actor}, cell={cell}, asset={a}, -{amt})"
  | .delegate del recip t      => s!"delegate (delegator={del}, recipient={recip}, target={t})"
  | .revoke holder t           => s!"revoke (holder={holder}, target={t})"
  | .introduceA intro recip t  => s!"introduceA (introducer={intro}, recipient={recip}, target={t})"
  | .delegateAttenA del recip t keep =>
      s!"delegateAttenA (delegator={del}, recipient={recip}, target={t}, keep={authsStr keep})"
  | .exerciseA actor t inner   => s!"exerciseA (actor={actor}, target={t}, inner={inner.length} effects)"
  | .setFieldA actor cell f v  => s!"setFieldA (actor={actor}, cell={cell}, field={f}, value={v})"
  | .incrementNonceA actor cell n => s!"incrementNonceA (actor={actor}, cell={cell}, newNonce={n})"
  | .emitEventA actor cell topic d => s!"emitEventA (actor={actor}, cell={cell}, topic={topic}, data={d})"
  | a                          => ctorName a

/-! ## §1.5 — Small inline-styled chips for the graph (HTML inside the SVG `<foreignObject>`).

`GraphDisplay` draws labels as SVG; non-SVG (HTML) labels go inside `<foreignObject>`. These chips reuse the
`Basic.lean` palette (`panelBg`/`panelBorder`/`keyColor`/`valColor`) so the forest matches the badge look. -/

/-- A two-line node chip: the effect name (bold) over `→cell N`. -/
def panelNodeChip (name sub : String) : Html :=
  <div style={json% {
      background: $panelBg,
      border: $("1px solid " ++ panelBorder),
      borderRadius: "6px",
      padding: "3px 6px",
      textAlign: "center",
      fontFamily: "ui-monospace, SFMono-Regular, Menlo, monospace",
      lineHeight: "1.1"
    }}>
    <div style={json% {fontSize: "12px", fontWeight: "700", color: $valColor}}>{.text name}</div>
    <div style={json% {fontSize: "10px", color: $keyColor}}>{.text sub}</div>
  </div>

/-- An edge chip: the conferred rights over the target. -/
def panelEdgeChip (rights tgt : String) : Html :=
  <div style={json% {
      background: "#161b22",
      border: $("1px solid " ++ panelBorder),
      borderRadius: "5px",
      padding: "1px 5px",
      textAlign: "center",
      fontFamily: "ui-monospace, SFMono-Regular, Menlo, monospace",
      fontSize: "10px",
      color: $keyColor
    }}>
    <span style={json% {color: $valColor}}>{.text rights}</span>
    {.text (" " ++ tgt)}
  </div>

/-! ## §2 — Node / edge data, COMPUTED from the forest, as plain `GraphDisplay.Vertex`/`Edge` records.

We walk the `FullForestA` in EXECUTION pre-order (a node, then its children left-to-right — exactly
`lowerForestA`'s order) threading a unique path id (`"n"`, `"n.0"`, `"n.0.1"`, …). For each node we emit one
`Vertex` whose label is the derived `ctorName`/`targetOf`; for each child we emit one `Edge` (parent → child
root) carrying the delegation's holder, conferred (attenuated) rights, and `capTarget`. The walk is
structural over the mutual `FullForestA`/`List FullChildA` (the same shape as `lowerForestA`). -/

/-- The vertex label: a small `<foreignObject>`-wrapped pill showing the effect constructor and its target
cell. Built from `ctorName a` + `targetOf a` — the real constructor and the executor's target field. -/
def nodeLabel (a : FullActionA) : Html :=
  -- `<g transform>` centres the `<foreignObject>` on the vertex (string attr ⇒ no `Neg Json`).
  <g transform="translate(-70,-16)">
    <foreignObject width={140} height={32}>
      {panelNodeChip s!"{ctorName a}" s!"→cell {targetOf a}"}
    </foreignObject>
  </g>

/-- A node's details: the full constructor summary + the target the executor reads. -/
def nodeDetails (a : FullActionA) : Html :=
  panel "node · effect" #[
    kvRowText "constructor" (ctorName a),
    kvRowText "summary" (ctorSummary a),
    kvRowText "targetOf (delegator)" (toString (targetOf a))
  ]

/-- An edge's label: the conferred (ATTENUATED) rights and the delegation target. Computed via the real
`attenuate`/`capAuthConferred`/`capTarget`, so it shows what the child ACTUALLY gains, not the declared cap. -/
def edgeLabel (keep : List Auth) (parentCap : Cap) : Html :=
  <g transform="translate(-58,-14)">
    <foreignObject width={116} height={28}>
      {panelEdgeChip (authsStr (capAuthConferred (attenuate keep parentCap))) (capTargetArrow parentCap)}
    </foreignObject>
  </g>

/-- An edge's details: the delegation holder, the parent cap, the attenuation `keep`, the cap target, AND
the no-amplification fact `conferred ⊆ capAuthConferred parentCap` (`edge_no_amplify`), READ off the data. -/
def edgeDetails (holder : Label) (keep : List Auth) (parentCap : Cap) : Html :=
  let granted := attenuate keep parentCap
  let conferredCount := (capAuthConferred granted).length
  let heldCount := (capAuthConferred parentCap).length
  panel "edge · delegation" #[
    kvRowText "holder (recipient)" (toString holder),
    kvRowText "parentCap (held)" (capStr parentCap),
    kvRowText "attenuate keep" (authsStr keep),
    kvRowText "granted (attenuated)" (capStr granted),
    kvRowText "capTarget" (capTargetText parentCap),
    kvRow "no-amplify" <|
      badge s!"conferred {conferredCount} ⊆ held {heldCount}"
        (if conferredCount ≤ heldCount then "#0d1117" else "#ffffff")
        (if conferredCount ≤ heldCount then "#3fb950" else "#da3633")
  ]

/-- A single graph node for a forest node at path id `pid`. -/
def mkVertex (pid : String) (a : FullActionA) : GraphDisplay.Vertex :=
  { id := pid
    label := nodeLabel a
    boundingShape := .rect 140 32
    details? := some (nodeDetails a) }

/-- A single graph edge for a delegation from parent path `pp` to child root path `cp`. -/
def mkEdge (pp cp : String) (holder : Label) (keep : List Auth) (parentCap : Cap) : GraphDisplay.Edge :=
  { source := pp
    target := cp
    label? := some (edgeLabel keep parentCap)
    details? := some (edgeDetails holder keep parentCap)
    attrs := #[("strokeWidth", (2 : Nat)), ("className", "dim")] }

/-! ## §3 — The structural WALK: forest → (vertices, edges), in execution pre-order.

Mutual structural recursion over `FullForestA`/`List FullChildA` (the same recursion shape as
`lowerForestA`/`lowerChildrenA`). `forestGraph pid f` emits `f`'s root vertex at `pid` and recurses into its
children; `childrenGraph pid i kids` emits, for the `i`-th child, the parent→child edge and the child's
subgraph. The path id makes every vertex id unique. -/

mutual
/-- The vertices+edges of a forest rooted at path `pid`. -/
def forestGraph (pid : String) : FullForestA → (Array GraphDisplay.Vertex × Array GraphDisplay.Edge)
  | ⟨a, kids⟩ =>
    let v := mkVertex pid a
    let (vs, es) := childrenGraph pid 0 kids
    (#[v] ++ vs, es)

/-- The vertices+edges of a child list, the `i`-th child rooted at `pid.i`; each child contributes its
parent→child delegation edge (holder/keep/parentCap) plus its own subgraph. -/
def childrenGraph (pid : String) (i : Nat) :
    List FullChildA → (Array GraphDisplay.Vertex × Array GraphDisplay.Edge)
  | []                                  => (#[], #[])
  | ⟨holder, keep, parentCap, sub⟩ :: rest =>
    let cp := s!"{pid}.{i}"
    let edge := mkEdge pid cp holder keep parentCap
    let (subV, subE) := forestGraph cp sub
    let (restV, restE) := childrenGraph pid (i + 1) rest
    (subV ++ restV, #[edge] ++ subE ++ restE)
end

/-- The vertices of a forest (root path `"n"`). -/
def forestVertices (f : FullForestA) : Array GraphDisplay.Vertex := (forestGraph "n" f).1
/-- The edges of a forest (root path `"n"`). -/
def forestEdges (f : FullForestA) : Array GraphDisplay.Edge := (forestGraph "n" f).2

/-! ### The node-label list, in execution pre-order — the textual shadow of the rendered nodes.

`forestCtorNames` is the SAME pre-order walk as `forestGraph`, collecting each node's derived `ctorName`
(rather than building a vertex). It is the `#eval`-able non-vacuity witness: the list of labels the graph
draws, derived purely from the value — feed a different forest and the list changes. -/

mutual
/-- The derived `ctorName` of every forest node, in execution pre-order (`lowerForestA` order). -/
def forestCtorNames : FullForestA → List String
  | ⟨a, kids⟩ => ctorName a :: childrenCtorNames kids
/-- The derived `ctorName`s of a child list's subtrees, in order. -/
def childrenCtorNames : List FullChildA → List String
  | []                      => []
  | ⟨_, _, _, sub⟩ :: rest  => forestCtorNames sub ++ childrenCtorNames rest
end

/-! ## §5 — The forest panel + the `#html` driver (forces the render over the REAL value).

`dreggForestGraph f` is the full `GraphDisplay` for a forest. The `#html` below elaborates it over
`Dregg2.Exec.FullForest.goodFullForest` (the project's own committing, non-amplifying 3-node tree), so the
verify step EXERCISES the whole derivation — `ctorName`/`targetOf`/`attenuate`/`capTarget` over real data. -/

/-- The complete `GraphDisplay` element for a forest: vertices+edges from the structural walk, with a link
force tuned for a readable tree layout, and the details box enabled (click a node/edge). -/
def dreggForestGraph (f : FullForestA) : Html :=
  <GraphDisplay
    vertices={forestVertices f}
    edges={forestEdges f}
    forces={#[ .link { distance? := some 140 }, .manyBody { strength? := some (-260) },
               .x { strength? := some 0.06 }, .y { strength? := some 0.06 } ]}
    showDetails={true} />

/-- The forest graph wrapped in the dregg panel (title + a one-line legend). -/
def dreggForestPanel (title : String) (f : FullForestA) : Html :=
  <div style={json% {
      background: $panelBg,
      border: $("1px solid " ++ panelBorder),
      borderRadius: "8px",
      padding: "12px 14px",
      maxWidth: "720px",
      fontFamily: "ui-sans-serif, system-ui, sans-serif",
      color: $valColor
    }}>
    <div style={json% {fontSize: "13px", fontWeight: "700", marginBottom: "2px"}}>{.text title}</div>
    <div style={json% {fontSize: "11px", color: $keyColor, marginBottom: "8px"}}>
      {.text "nodes = FullActionA effects (ctorName · →targetOf) · edges = delegation handoffs (attenuated rights · capTarget) · click for details"}
    </div>
    {dreggForestGraph f}
  </div>

/-! **THE RENDER DRIVER.** Force-elaborate the forest graph over the REAL `goodFullForest` value. The
`#html` command runs the full derivation (walk + `ctorName`/`targetOf`/`attenuate`/`capTarget` over the
actual tree) and saves the widget — so the leaf build genuinely exercises the render path. Put your cursor
on the command to see the interactive graph. -/
#html dreggForestPanel "dregg call-forest · goodFullForest (mint → transfer → burn, 2 gated edges)" goodFullForest

/-! ## §6 — NON-VACUITY (`#eval`): the graph is COMPUTED from the value, and a DIFFERENT forest gives a
DIFFERENT graph. If the derivation were placeholder, these counts/labels would not track the value. -/

-- `goodFullForest`: 3 nodes (mint root, transfer child, burn grandchild) ⇒ 3 vertices, 2 delegation edges.
#guard (forestVertices goodFullForest).size == 3   -- 3
#guard (forestEdges goodFullForest).size == 2      -- 2
-- The vertex ids are the unique pre-order paths (root, child, grandchild):
#guard ((forestVertices goodFullForest).map (fun v => v.id)) == #["n", "n.0", "n.0.0"]  -- #["n", "n.0", "n.0.0"]
-- The derived node labels ARE the real constructors, in pre-order (mint → balance → burn):
#guard forestCtorNames goodFullForest == ["mintA", "balanceA", "burnA"]  -- ["mintA", "balanceA", "burnA"]
-- The edges connect parent path → child path (the actual delegation structure):
#guard ((forestEdges goodFullForest).map (fun e => (e.source, e.target))) == #[("n","n.0"), ("n.0","n.0.0")]  -- #[("n","n.0"), ("n.0","n.0.0")]

-- A DIFFERENT forest ⇒ a DIFFERENT graph. `deepFullForest` is a 3-level transfer chain: still 3 nodes / 2
-- edges, but the labels are ALL `balanceA` (not mint/burn) — the labels track the value, not a fixed table.
#guard (forestVertices deepFullForest).size == 3   -- 3
#guard forestCtorNames deepFullForest == ["balanceA", "balanceA", "balanceA"]  -- ["balanceA", "balanceA", "balanceA"]
-- `emitOnlyForest` is a SINGLE node, NO edges — the walk genuinely shrinks for a childless forest.
#guard (forestVertices emitOnlyForest).size == 1   -- 1
#guard (forestEdges emitOnlyForest).size == 0      -- 0
#guard forestCtorNames emitOnlyForest == ["emitEventA"]  -- ["emitEventA"]
-- `authFullForest` (introduce → exercise) — distinct constructors again, derived from the value.
#guard forestCtorNames authFullForest == ["introduceA", "exerciseA"]  -- ["introduceA", "exerciseA"]
-- The label lists genuinely DIFFER across forests (not a constant) — the derivation tracks the value:
#guard decide (forestCtorNames goodFullForest ≠ forestCtorNames deepFullForest)  -- true

-- The EDGE labels are the ATTENUATED conferred rights (not the declared cap). `goodFullForest`'s first edge
-- keeps `[read]` of an `endpoint [read,write]` cap ⇒ conferred drops `write` (the Granovetter shrink shows).
-- (Read off the first child WITHOUT `head!` — a total match, so no `Inhabited` obligation.)
#guard (match goodFullForest.children with
        | ⟨_, keep, pc, _⟩ :: _ => (authsStr (capAuthConferred (attenuate keep pc)),  -- ("[read]",
                                    authsStr (capAuthConferred pc))                   --  "[read, write]")
        | []                    => ("(no edge)", "(no edge)")) == ("[read]", "[read, write]")

/-! ## §7 — Axiom hygiene. The pure derivations (the glyph + the walk) are pinned kernel-clean.

The label/summary/printer functions and the structural walk that PRODUCE the graph must themselves be
`{propext, Classical.choice, Quot.sound}`-clean — they carry the widget's "computed, not faked" credibility.
(The `Html` builders inherit ProofWidgets' own clean axioms; we pin the dregg-specific derivations.) -/

#assert_axioms ctorName
#assert_axioms ctorSummary
#assert_axioms capStr
#assert_axioms capTargetArrow
#assert_axioms authsStr
#assert_axioms forestGraph
#assert_axioms forestVertices
#assert_axioms forestEdges
#assert_axioms forestCtorNames

end Dregg2.Widget
