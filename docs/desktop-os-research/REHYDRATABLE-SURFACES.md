# Rehydratable Surfaces — the certified-compositor / sturdyref-membrane model

*(2026-06-14. The canonical articulation of ember's "rehydratable screenshot"
idea, grounded in the dregg substrate. A living draft — the vision is ember's;
this doc names it back against what is actually in the tree. Sibling:
`ARCHITECTURES.md` (the compositor-PD), `DISTRIBUTED-SERVO-FACETS.md` (the
web-of-cells fetch), `BUILD-STATUS.md` (`starbridge-web-surface`).)*

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
| certified compositor | the **compositor-PD** (sole framebuffer+input cap holder; `ARCHITECTURES.md` Nitpicker lens) | designed |
| witness-graph | the **receipt/ledger graph** — `AttestedRoot` + receipt-stream + verified turns (*the graph the rotation flip is hardening the proofs of*) | live |
| live servo contexts | **`starbridge-web-surface`** — the cap-gated `WebSurfaceDelegate` | built |
| frame embeds a handle | a **sturdyref** (captp `SwissTable::enliven` + `Netlayer::dial`) | exists |
| rehydration = attested fetch | the **`dregg://` verified cross-cell turn** returning attested content | built (web-of-cells demo) |
| the membrane | an **ocap membrane** (attenuating proxy) + the org-settings negotiation UX + the `Rehydration` type | **the new build** |

~70% of the primitives are in the repo. Rehydratable surfaces are a *thin* layer
(sturdyref-in-a-frame encoding + membrane-as-settings negotiation + the liveness
type) over substrate already being hardened — not a research moonshot.

## Honest residuals (decisions, not flaws)

1. **The membrane's negotiation semantics are the next real continent.** Who
   proposes the projection, who refuses, what happens on disagreement, and how
   attenuation *composes across chained reacquisitions* (A membranes to B, B
   reshares to C) — that is a protocol, and it is the easy-to-wave-at / hard-to-make-
   sound part. The org-settings framing gives it a familiar shape; the chained-
   attenuation algebra still needs pinning (it is the same `is_attenuation` lattice
   the cap crown already proves, lifted to projection composition).
2. **Replay-fidelity is bounded by witness determinism.** The sturdyref guarantees
   you reacquire something *faithful-by-construction*; it cannot guarantee it is the
   *same* something. The `Rehydration` type is how the membrane stays honest about
   that gap rather than papering it.

## The endgame in one line

The unit was never the pixels or the data — it was *the revocable right to
renegotiate the connection*, which is exactly a sturdyref behind a membrane;
the screenshot is UX, the substance is the attested, per-viewer, liveness-typed
re-expansion of a certified projection of a witnessed scene.
