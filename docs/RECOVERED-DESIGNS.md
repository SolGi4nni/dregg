# Recovered designs — specced-but-unbuilt ideas worth building

A sweep of the ~100 most-recently-edited `.md` files surfaced designs that are
fully thought through and code-grounded but never built — "held," not lost. This
file makes them durable so they stop getting re-forgotten across compactions. Each
is a real lane: the design exists, often most of the machinery exists, and the
remaining work is named. Promote the best into `HORIZONLOG.md`/`docs/NEXT-WAVE.md`
as they're scheduled; close a line by building it (git history is the record).

Source docs are cited; verify against `HEAD` before starting (these are
point-in-time reads).

## Cheap, high-leverage (the proof/machinery is already done)

- **Clearance-lattice in cell-program predicates.** `ClearanceGraph.dominatesD` is
  *proved* (`metatheory/Dregg2/.../ClearanceGraph.lean:53,92`) but no
  `StateConstraint` constructor invokes it — the predicate language cannot yet say
  "this transition requires clearance ≥ ℓ." Wiring one constructor makes the
  storage-gateway-mandate / compartment-workflow-mandate clearance checks *real*
  (they're flat set-contains scaffolds today). The hard part is done. Source:
  `metatheory/docs/rebuild/_POLICY-LANGUAGES-REFRESH.md:48`. Effort S–M.
- **`fields_root` committed map (the record-layer upgrade).** Replace the fixed
  `[FieldElement; 8]` slot array with a Poseidon2 keyed accumulator committing a
  `key → value` map — apps get unlimited fields, the circuit width stays fixed. The
  Lean record is *already* unbounded (`Value.lean`); the constraint is only the Rust
  `[FieldElement;8]` + circuit. Additive (hybrid, zero deletion); wire one app
  end-to-end. The polis/council apps already MAX OUT 8 slots. Source:
  `metatheory/docs/rebuild/_RECORD-LAYER-UPGRADE.md`. Effort M.
- **Macaroon/biscuit ↔ cap-crown bridge (the "deepest open thread").** Make the
  caveat that narrows a capability-bearing verb emit the *same* `(granted, held)`
  pair the kernel cap leg already consumes, and prove the one-line bridge
  `chainGateG na = true → granted(na) ⊆ held(na)` on delegation. Converts the
  four-aspect `&&` from defense-in-depth into a *proven identity*. One Lean lemma +
  one SDK field. Source: `docs/AUTHORIZATION-MODEL.md:53`,
  `docs/OPEN-LOOPS-PRECOMPACTION.md:52`. Effort M.
- **WholeChainProof serde (one fork-side fix, two unblocks).** Add derives + a
  versioned envelope to the recursion fork's whole-chain proof. Releases BOTH the
  web over-wire byte-verify AND pg-dregg's proof-gate (tier-c) at once. Source:
  `docs/NEXT-WAVE.md:183`. Effort S.
- **`notify` as authority (`Auth.notify`).** Five subsystems re-implement
  async-signal without a verified `notify` authority primitive — a ~9-site
  mechanical edit. "A brick, not because it's hard, but because the hole is
  load-bearing." ADOS swarm-coordination needs a verified async edge. Source:
  `docs/NOTIFY-PRIMITIVE.md:13`. Effort S–M.
- **Cap-root hash site for all delegation/cap effects (IR gap).** ~15 effects
  (delegate, delegateAtten, attenuate, introduce, dropRef, revoke,
  refreshDelegation) carry an `IR GAP` for the cap-root hash site; the design is
  done (additive, width-neutral) and the emitter skeleton exists from transfer.
  Feeds in-circuit non-amplification everywhere (the ARGUS linchpin). Source:
  `metatheory/docs/rebuild/_IR-EXTENSION-DESIGN.md`. Effort M.

## ADOS / live-cockpit (unblocked NOW that n>1 commits + the precious landed)

- **ADOS narration→effect compiler (R1).** Map each narrated agent tool-call to the
  specific protocol effect(s) it claims to have caused, so a narration line binds to
  a receipt hash. The sharpest product tooth for the pug-handoff bar. The feed-level
  divergence panel already ships; this is the per-turn join. Source:
  `docs/NEXT-WAVE.md:209`. The `~/pug/builders-dev` (Cloudflare DO multi-agent
  council) + `~/pug/buildr-private-beta` (the herdr-lineage agent workspace manager)
  integrators wire in at the `Swarm::run` seam (`docs/ADOS-DEEPENING.md`).
- **Live-node cockpit connection.** Move starbridge-v2 reads to gpui's async
  executor; wire `/api/events/stream` SSE into the ReceiptInspector with
  `cx.notify()`. The channel/mailbox/court organs become LIVE reflections the moment
  this runs — it was held on S5, which is done. Source: `docs/NEXT-WAVE.md:122`.
  Effort M.

## deos surface frontiers

- **deos app-framework rebuild + `dregg new deos-app` scaffold.** The framework's
  job is to compose the six layers (verified state · SDK surface · distribution ·
  rehydration · affordances · surface) and scaffold an app in an afternoon. Seven
  gaps named; this is the pug-handoff bar (strangers can't build a deos app yet).
  Source: `docs/deos/DEOS-APPS.md:39`. Effort L.
- **Embedded servo (the browser as a cap-confined guest).** Implement the libservo
  `WebViewDelegate` cap-gate build — the embedder's delegate impl *is* the cap gate.
  Design fully settled (`docs/EMBEDDED-WEB-SURFACE.md`); the lever is the libservo
  embed (the mozjs long pole). Turns the cockpit into a cap-gating browser and lets
  the legacy web-starbridge embed as a tab. Source: `docs/NEXT-WAVE.md:138`. Effort L.
- **Web cells (live DOM bundles as dregg cells).** Publish an app's live state as a
  `LiveDomSnapshot` cell — transcludable, rehydratable, cap-confined. The
  `deos-web-cells` crate exists. Source: `docs/deos/WEB-CELLS.md`. Effort M–L.
- **Tussle — the Toribash-style verified game.** Full design + code groundings
  (`docs/deos/TUSSLE.md`, `starbridge-apps/tussle/`). The forcing function for joint
  turns + pg-dregg + rehydratable surfaces. (The app crate is now real deos-native;
  the *game* is the unbuilt part.)
- **Browser-extension → Studio sign-turn weld.** `runtime-extension.js` +
  `appApiRows` already anticipate `signTurn`/`signTurnV3`; the extension holds keys
  and does the disclosure-picker — the missing wire makes the full-effect submit
  path real from the browser. Source:
  `metatheory/docs/rebuild/_FRONTEND-OVERHAUL-PLAN.md:176`. Effort S–M.
- **Frustum-snapshot deepening.** The witness-graph REPLAY protocol; the
  membrane-negotiation semantics ("the unspecified continent"); liveness-type as a
  confinement READOUT not just an honesty label. Source:
  `docs/OPEN-LOOPS-PRECOMPACTION.md:80`, `docs/desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md`.

## OS-scale

- **Live cell migration.** ~80% derives from existing theorems; the two-phase-commit
  migration FSM is already in Rust (`turn/src/executor/migration.rs:25`). Ship the
  triple + receipts over the shared DAG. Falls out: a distributed debugger + a
  capability market. Source: `docs/rebuild/DREGG4-OS-ENDGAME.md:59`.
- **Playground → example gallery (the three-door UX collapse).** The Playground's
  31 bespoke sections become example seeds ("open in Studio"); Learn / Studio /
  Explorer each get one job. Deletes the third door without deleting content; no
  code changes to start. Source: `metatheory/docs/rebuild/_FRONTEND-OVERHAUL-PLAN.md:127`.

## Doc-tidy (separate from building — see the audit)

The same sweep flagged dated-snapshot docs for deletion (the `HANDOFF-2026-06-0{3,6}.md`,
`EFFECT-FIDELITY-LEDGER.md`, `DREGG2-GAP-MAP.md`, `_RECOVERED-DESIGNS-2026-06-02.json`),
`OPEN-LOOPS-PRECOMPACTION.md` live-tails to migrate into HORIZONLOG, and trajectory
banners to trim from `_DREGG1-DREGG2-UNIFICATION-LEDGER.md` + `DREGG4-UNIFICATION.md`.
That tidy is a present-tense/teach-what-is pass, not a build lane.
