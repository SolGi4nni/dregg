# Rehydratable Surfaces — the certified-compositor / sturdyref-membrane model

*(2026-06-14. The canonical articulation of ember's "rehydratable screenshot"
idea, grounded in the dregg substrate. A living draft — the vision is ember's;
this doc names it back against what is actually in the tree. Sibling:
`../reference/firmament.md` (the compositor-PD), `BUILD-STATUS.md`
(`starbridge-web-surface`).)*

## Thesis (one sentence)

A dregg "screenshot" is the present render-output of a **certified compositor**
over a **witness-graph**; what it actually embeds is a **sturdyref behind a
membrane**; "opening" it is the **membrane-negotiated, per-viewer reacquisition**
of the live (or replayable) witnessed state it was always a certified projection
of — so *open the image* can mean *instantiate the slice* without *trust the author*.

## Why this is not a party trick (the inversion that makes it sound)

The naive version — "embed a faithfulness zkproof in a PNG" — retrofits the proof
onto a dead artifact, and asks a viewer to instantiate arbitrary author-state
(an attack surface, not a feature). The dregg version moves the proof **upstream
and structural**: the frame came out of a compositor whose rendering is *itself a
verified turn over the witness-graph*, so the compositor can only draw what the
graph authorizes. "Faithful" stops being a property you prove *about* an image and
becomes a property guaranteed by *where the image came from*. Frustum-culling is
the right mental model and it **relocates**: the culling happens in the compositor's
render pass over the witness-graph; rehydration is not reconstruct-from-thumbnail,
it is *re-attach a live view to a graph the frame was already a certified
projection of*. The screenshot rehydrates because it was never a dead artifact — it
is a paused camera on a running, witnessed scene.

## Crystal vs. cursor was a false binary — the sturdyref dissolves it

The artifact is neither a self-contained offline crystal (the full state) nor a
mere live cursor (a handle that dies with the contexts). It is a **sturdyref** — a
persistable capability, serializable into the frame, handed to someone cold, that
on activation *re-establishes* a live connection: reconnect-to-extant OR
restore/replay-from-witness, as the membrane decides at activation time. The unit
of portability was never the data or the connection — it is **the revocable right
to renegotiate the connection**.

## The membrane makes rehydration relational, not absolute

A plain sturdyref reconnects you to *the thing*. A membrane-mediated one reconnects
you to *a view of the thing shaped by who you are and what you hold*. Two agents
(human or AI) opening "the same" screenshot do not rehydrate identical
instantiations — each negotiates, across the membrane, the slice their capabilities
authorize and their context wants. The frustum is **re-derived per-viewer at the
membrane** from (their authority) ∧ (the graph's permitted projections). The
membrane is where "I shared a screenshot" stops being "I leaked my session" and
becomes "I extended a revocable, attenuated, per-viewer right to re-view": it
(a) re-checks authority at reacquisition, (b) is revocable between projections,
(c) attenuates what is exposed, (d) is *negotiated* (neither side unilaterally
dictates the surface).

## The membrane negotiation IS a GitHub-org settings page (ember, the adoptability unlock)

The membrane's negotiation semantics are not an exotic new protocol — a GitHub org
settings page already *is* a membrane UI: teams = capability groups · repo roles
(read/triage/write/maintain/admin) = the attenuation lattice · visibility =
projection scope · fork policy = re-share/delegation rules · member mgmt =
grant/revoke · branch protection = the constraint set on permitted actions. Every
membrane primitive has a boring, familiar home there. Self-similar kicker: a
settings page is *itself* a rendered view over the org's permission graph — so the
negotiation surface is the same *kind* of object as the thing it governs. Familiar
UX is what makes it adoptable; the cap+proof substrate is what makes it sound.

## The liveness cost is a TYPE (honest by construction)

"Both live and replay" has a liveness cost you cannot negotiate away: if the
membrane chooses witness-replay because the contexts are gone, replay-fidelity is
bounded by how deterministically the witness-graph captured the servo
non-determinism (timing, external fetches, agent choices) — so "replay" can be
*reconstruction*, not resurrection. The membrane must **type** its rehydrations,
carried in the decentralized type system on every reacquisition:

```
enum Rehydration { Live, ReplayedDeterministic, ReconstructedApproximate }
```

so *open the image* tells you *which kind of true* you are getting, by construction
— the system cannot lie about whether you are touching the live scene or a faithful
replay, because the reacquisition is typed. (The same "mark what you are actually
handing someone" discipline this whole stack keeps rediscovering, enforced at the
type level instead of by good manners.)

## Substrate mapping — what is real vs. the new build

| the vision | dregg component | state |
|---|---|---|
| certified compositor | the **compositor-PD** (sole framebuffer+input cap holder; `../reference/firmament.md` compositor-PD section) | designed (still wood — the framebuffer/input-cap PD + the libservo link) |
| witness-graph | the **receipt/ledger graph** — `AttestedRoot` + receipt-stream + verified turns (*the graph the rotation flip is hardening the proofs of*) | live |
| live servo contexts | **`starbridge-web-surface`** — the cap-gated `WebSurfaceDelegate` | built |
| frame embeds a handle | a **sturdyref** (captp `SwissTable::enliven` + `Netlayer::dial`) | **built** (`starbridge-web-surface::Sturdyref` — a `dregg://` cap-handle + authority lineage + witness-log; over the existing `DreggUri`/`AttestedRoot`) |
| rehydration = attested fetch | the **`dregg://` verified cross-cell turn** returning attested content | built (`rehydrate()` wires the existing web-of-cells attested fetch) |
| the membrane | an **ocap membrane** (attenuating proxy) + the org-settings negotiation UX + the `Rehydration` type | **enforcer built on `is_attenuation`** (`starbridge-web-surface::Membrane` — per-viewer projection + chained-hop composition); org-settings negotiation UX still wood |
| the `Rehydration` liveness-type | **derived (built)** — `Rehydration::classify` computes it from a context's witnessed-vs-ambient interaction log (a confinement readout, not a hand-set field) | **built** |

~70% of the primitives are in the repo. Rehydratable surfaces are a *thin* layer
(sturdyref-in-a-frame encoding + membrane-as-settings negotiation + the liveness
type) over substrate already being hardened — not a research moonshot. **As of
2026-06-14 the sturdyref encoding, the membrane enforcer (the per-viewer projection
+ the chained-attenuation algebra over the real `is_attenuation`), and the derived
liveness-type are STEEL** — running, tested code in `starbridge-web-surface`
(`src/rehydrate.rs`, `examples/rehydrate_demo.rs`, 19 module tests). What is still
wood: the certified compositor-PD (the framebuffer/input cap holder) + the libservo
link (a `dregg://` attested fetch stands in for the compositor's render-pass, as
`MockSurface` stands in for the libservo `WebView`), and the membrane's
*org-settings negotiation UX* (the cap algebra under it is built; the
who-proposes/who-refuses surface is the next continent — residual #1).

**The frustum-snapshot over an *interactive* surface is also STEEL now**
(`starbridge-web-surface::affordance`, `examples/affordance_demo.rs`). A
`AffordanceSnapshot` is the rehydratable artifact applied to a cell's interactive
affordances (its `CellAffordance`s — named `dregg_turn::Effect` templates, the deos
"htmx on crack" element): the snapshot is tiny (a `Sturdyref` + the culling
boundary = the cell + the affordance *names*, NOT the effect-templates and NOT any
projection), and `rehydrate_affordances` re-expands the frustum PER-VIEWER by
composing the EXISTING `rehydrate()` (so an unattested scene yields NO surface —
confinement before relation) with the per-viewer affordance projection through the
SAME `Membrane` / `is_attenuation` gate, carrying the derived `Rehydration`
liveness-type through to the re-expanded interactive surface. So the "paused camera
on a witnessed scene" is now a paused camera on a witnessed *interactive* scene:
two viewers re-expand one snapshot into two different live affordance sets, each
liveness-typed, each confined by construction. This is the membrane model's
rehydration lifted from a *view* to an *interactive surface*, on the same proven
primitives.

## Honest residuals (decisions, not flaws)

1. **The membrane's negotiation semantics are the next real continent — the
   *algebra* is now pinned; the *negotiation UX* is what remains.** Who proposes
   the projection, who refuses, what happens on disagreement is a protocol, and it
   is the easy-to-wave-at / hard-to-make-sound part; the org-settings framing gives
   it a familiar shape. **The chained-attenuation algebra is now BUILT** (the part
   the residual flagged as "still needs pinning"): `Membrane::reshare` composes
   attenuation across chained reacquisitions (A→B→C) by re-applying the REAL
   `is_attenuation` per hop on every axis (window rights / fetch / navigate /
   permissions), refusing any hop where C would receive more than B held — the same
   `is_attenuation` lattice the cap crown proves, lifted to projection composition,
   with anti-ghost tests (`a_reshare_chain_attenuates_and_an_amplifying_reshare_is_refused`).
   What is still wood: the *negotiation surface* itself (the GitHub-org-settings UI —
   who-proposes/who-refuses/disagreement), not the lattice it would manipulate.
2. **Replay-fidelity is bounded by witness determinism.** The sturdyref guarantees
   you reacquire something *faithful-by-construction*; it cannot guarantee it is the
   *same* something. The `Rehydration` type is how the membrane stays honest about
   that gap rather than papering it.

3. **The liveness-type is a confinement readout, not just an honesty label — and
   that assignment is now `derived` (BUILT).** The appealing form: a servo context
   whose external interactions are themselves `dregg://` attested fetches (cap-gated,
   receipt-logged) has its non-determinism *captured in the witness-graph as attested
   turns* → `ReplayedDeterministic` **by construction**; a context that reached outside
   the membrane (a raw fetch, an un-witnessed timing/agent choice) is intrinsically
   `ReconstructedApproximate`, because the thing that made it non-deterministic was
   never witnessed. So `ReplayedDeterministic` = *exactly the confined fragment*
   ("everything this context did went through the membrane"), which makes the enum do
   **double duty**: honesty label AND a readout of how much behavior stayed inside the
   capability discipline — the same shape as the coordination-price classifier doing
   security work by pricing absence-guards.

   **Ledger row — liveness-type assignment: `derived-from-attested-non-determinism`
   (BUILT), no longer `heuristic`.** `Rehydration::classify(log, sources_reachable)`
   COMPUTES the variant from a context's `InteractionLog` (a list of interactions each
   tagged witnessed — carries an `AttestedRoot` — vs. ambient): `Live` iff the sources
   are reachable; else `ReplayedDeterministic` iff *every* interaction `is_witnessed`
   (and "witnessed" is itself derived — an `AttestedFetch`'s `AttestedRoot` must
   structurally hold: `is_v4_receipt_complete() && has_quorum()`, so a purported
   attestation that does not even hold is *not* a witness); else
   `ReconstructedApproximate`. It is not a hand-set field — the enum is now a *proven*
   confinement metric, with both-polarity tests
   (`liveness_is_derived_replayed_when_every_interaction_is_witnessed`,
   `liveness_is_derived_reconstructed_when_any_interaction_is_ambient`,
   `a_structurally_invalid_attestation_is_not_witnessed`). The "type it" move the doc
   named is settled.

## The endgame in one line

The unit was never the pixels or the data — it was *the revocable right to
renegotiate the connection*, which is exactly a sturdyref behind a membrane;
the screenshot is UX, the substance is the attested, per-viewer, liveness-typed
re-expansion of a certified projection of a witnessed scene.
