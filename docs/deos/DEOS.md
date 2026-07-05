# deos — the agentic desktop userlayer (the outer brand)

*(2026-06-14. The naming + the program. `deos` is ember's chosen outer brand for the
agentic desktop. This doc is the home of the brand, the "verified desktop OS"
verification program, and the "usefully webby / htmx-on-crack" interaction model.)*

## The naming (ember-set, canonical)

- **robigalia** — THE PROJECT (the whole stack, the org).
- **dregg** — THE KERNEL (the formally-verified distributed object-capability kernel;
  the Lean executor + the emitted circuits + the witness-graph).
- **deos** — THE AGENTIC DESKTOP USERLAYER, the outer brand. Everything a human or
  AI agent *touches*: the cap-confined surfaces, the certified compositor, the
  web-of-cells, the rehydratable frustum-snapshots. deos is dregg made visual,
  interactive, and webby — with zero new trust.

So: **deos runs on dregg runs in robigalia.** The desktop is the firmament made
visual; a window IS a `Capability{ Target::Surface(cell), rights }`; nothing in deos
adds authority the kernel does not already prove.

## What deos IS (and is not)

deos is **not web-for-web's-sake**. It is the realization that the web's *interaction
model* — declarative, hypertext-driven, server-rendered, progressively enhanced
(htmx's thesis) — is the right UX, and that dregg can make every piece of it
**capability-gated, verified, and attenuable** instead of ambient-authority soup.

- **htmx on crack.** In htmx, an element declares `hx-post="/x"` and the server
  returns a fragment. In deos, a **cell declares affordances** — named, typed
  effect-templates — and an interaction is a **verified turn**: the "button" is a
  cap-gated effect, the "fragment" is the attested post-state surface, and *who may
  press it* is decided by held capabilities, not a session cookie. Every interactive
  element is a turn the witness-graph records. Progressive enhancement becomes
  progressive *attenuation*: an agent sees exactly the affordances its caps authorize.
  This is steel in `starbridge-web-surface::affordance`: a `CellAffordance` is a named
  `dregg_turn::Effect` template, the render/fire gate is the GENUINE `is_attenuation`
  (`required ⊆ held`, the proven lattice — not a new gate), and `project_for` returns
  the per-viewer affordance set. The one seam is the *dispatch* of a fired
  `AffordanceIntent` to a live `TurnExecutor` (the same serve-turn seam the
  web-of-cells fetch names); the effect carried IS the real one, and whether it may
  fire at all is decided in-band by the proven gate.

- **The frustum-culled snapshot — THE dregg-only novelty.** A deos "screenshot" is a
  frame of the certified compositor over the witness-graph; it embeds a **sturdyref
  behind a membrane** (see `desktop-os-research/REHYDRATABLE-SURFACES.md`), so
  *opening the image* re-attaches a live, **per-viewer, attenuated, liveness-typed**
  interactive surface. Nothing else can offer this: it requires the verified
  witness-graph (so the frame is faithful by construction) + the ocap substrate (so
  the rehydration is confined by construction) + the sturdyref/membrane (so the right
  is revocable + per-viewer). A normal screenshot is a dead pixel grid; a deos snapshot
  is *a paused camera on a witnessed scene that re-expands inside its own jail*. This
  is the truest thing deos offers that is a genuine novelty of dregg — not a feature
  port, a category only this substrate can have.

## The verified-deos program (a verified *desktop* OS — the Lean targets)

The desktop adds ZERO new trust, so its safety is provable from the kernel's own
metatheory. The four modeling targets (Lean, `metatheory/Dregg2/Deos/…`) are ALL
DISCHARGED at HEAD; the sibling `desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md`
advances PAST them (the C1 replay derivation + C2 negotiation algebra, `ReplayMembrane.lean`):

1. **Surface-as-capability.** `Target::Surface(cell)` is a point on the existing
   `(target, rights)` gradation; a window confers no authority beyond its
   rights (the same shape as `notifyCap_confers_no_edge`). **DISCHARGED:**
   `Surface.lean::surfaceConfersExactly` + `viewSurface_confers_no_edge`.
2. **Membrane non-amplification.** The rehydration membrane composes `is_attenuation`
   across hops; `reshare A→B→C ⟹ C's authority ⊆ B's held ⊆ A's` (the chained
   lattice law — the proven `is_attenuation` lifted to projection composition). The Rust
   `Membrane` in `starbridge-web-surface` is the realization; the Lean is the proof it
   cannot amplify. **DISCHARGED:** `Membrane.lean::reshare_chain_attenuates`.
3. **Rehydration confinement = the liveness-type.** `ReplayedDeterministic`
   *is exactly* the confined fragment: a context whose every external interaction was
   an attested turn replays deterministically; otherwise `ReconstructedApproximate`.
   This makes the liveness-type a *proven* confinement readout (the doc's "derived"
   row, lifted to a theorem) — the verified-desktop crown. **DISCHARGED:**
   `Rehydration.lean::replayedDeterministic_iff_confined`.
4. **Affordance soundness.** A cell-affordance interaction is a verified turn; an
   agent can only fire affordances its caps authorize (gateOK on the affordance
   effect-template), and the post-state surface binds the attested root. **DISCHARGED:**
   `Affordance.lean::fire_authorized_iff` + `firedSurface_binds_attested_root`.

These four are "a verified desktop OS": every visual/interactive primitive reduces to
a kernel theorem. None are new mathematics — they are the firmament's existing
proofs (attenuation, gateOK, the receipt chain, unfoolability) restated for pixels,
affordances, and rehydration.

## Build status + queue

- **STEEL (built, tested, in `starbridge-web-surface`):** the cap-confined
  `WebSurfaceDelegate`, the `dregg://` web-of-cells attested fetch, and the rehydration
  stack — `Sturdyref`, the `Membrane` enforcer (per-viewer projection + chained
  `is_attenuation`), the derived `Rehydration` liveness-type, the `rehydrate_demo`.
  **PLUS the cell-affordances + frustum-snapshot layer** (`src/affordance.rs`,
  `examples/affordance_demo.rs`, 15 module tests): `CellAffordance` (a named
  effect-TEMPLATE carrying a REAL `dregg_turn::Effect`) cap-gated by the GENUINE
  `is_attenuation` (`required ⊆ held`, never a new gate); the per-viewer
  `AffordanceSurface::project_for` (progressive enhancement → progressive
  *attenuation* — two viewers diverge over one surface); the anti-ghost
  `AffordanceSurface::fire` (an unauthorized fire is REFUSED in-band, an authorized
  one yields a verified-turn `AffordanceIntent`); and the frustum-snapshot
  `AffordanceSnapshot` (tiny — a `Sturdyref` + the culling boundary, NOT the
  affordance data) with `rehydrate_affordances` re-expanding it PER-VIEWER through
  the existing `Membrane`, carrying the derived `Rehydration` liveness-type — the
  dregg-only novelty made real.
  **PLUS the fog-of-war WORLD** (`src/game.rs`, `src/world.rs`,
  `examples/{fog_of_war_demo,deos_world_demo}.rs`) — the forcing-function exemplar
  where the security property IS the game mechanic: fog = the per-viewer membrane
  projection (the no-peek keystone, proof-backed by a real `FogVisionVerifier`);
  terrain-occluded line-of-sight; mixed unit archetypes + objectives + win
  conditions; moves + objective-captures as cap-gated real `Effect`s; a federated
  `Lobby` of `GameWorld`s published as attested cells; `AgentPlayer`s (policy-driven,
  cap-confined) playing a full `play_match` to a decision; and the membrane as a
  `MembraneNegotiation` surface (the org-settings page — attenuated, re-shareable,
  liveness-typed, fog-respecting spectator grants). See `DEOS-APPS.md` §"the forcing
  function". (Tier A; the ZK Tier-B vision AIR is the named cross-crate follow-up.)
- **STEEL (built, tested, in `app-framework` — the composed deos-app framework):** the
  `DeosApp`/`DeosCell` composition (`src/deos_app.rs`) — affordance surfaces over the
  `EmbeddedExecutor`, the web-of-cells publish, the rehydration seam, the generated web
  component — **PLUS the cap∧state `GatedAffordance` rung** (`src/affordance.rs`, the
  Rust twin of the Lean `Dregg2.Deos.GatedAffordance`): a `GatedAffordance` pairs the
  GENUINE `is_attenuation` cap-gate with a REAL `CellProgram` live-state gate (the SAME
  `CellProgram::evaluate` the executor runs), and a button lights IFF caps AND state both
  pass. `DeosCell::{project_gated_for, fire_gated_through_executor}` read the cell's LIVE
  state from `EmbeddedExecutor::cell_state` (the author threads no `(old, new)`); the
  state-tooth refusal is `FireError::StateConditionUnmet`, in-band, before any dispatch.
  The exemplar is `examples/deos_council_board.rs` (+ `tests/deos_council_board.rs`): a
  council approval board where the `approve` button lights only for an approver AND only
  while PENDING, goes DARK the instant the proposal RESOLVES (the htmx tooth — same
  viewer, the surface reacts to the cell), an unauthorized fire is refused by the cap
  tooth and a stale-state fire by the state tooth (both anti-ghost, nothing submitted),
  a both-pass fire runs a real verified turn through the executor, and a frustum-snapshot
  rehydrates per-viewer (an incomparable identity gets no projection).
- **DISCHARGED (Lean, `metatheory/Dregg2/Deos/`):** the verified-deos modeling — the
  four theorems above (`Surface.lean` · `Membrane.lean` · `Rehydration.lean` ·
  `Affordance.lean`), extended PAST them by `ReplayMembrane.lean` (C1/C2). See
  `desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md`.
- **OPEN (forward):** the membrane wired into the live captp sturdyref path (not just
  the web crate) · starbridge-v2 native cockpit embedding the affordance surfaces.
- **WOOD (frontier):** the certified compositor-PD (sole framebuffer+input cap holder,
  seL4). The cap-gated render path to pixels has since LANDED (`servo-render::fetch_render_present`,
  the Stage-A pipeline; the gpui-offscreen→seL4 framebuffer path is closed per
  `docs/reference/{firmament,cockpit}.md`); the remaining seam is the libservo DOM
  rasterization (`MockSurface` + a `dregg://` attested fetch stand in for the real
  `WebView` today).

*Cross-refs: `desktop-os-research/REHYDRATABLE-SURFACES.md` (the membrane model) ·
`desktop-os-research/ARCHITECTURES.md` (the compositor-PD) · `STARBRIDGE-V2.md` (the
native cockpit).*
