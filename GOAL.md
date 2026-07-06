# GOAL — deos as the substrate for confined, verifiable, forkable hosted agents

**Standing goal (set 2026-07-05, ember asleep → Fable works the night):**
Unify the grain and the confined-hermes hosting stacks so a hosted agent (a
jailed coding agent, or any BYO brain) IS a first-class grain: OS-jailed +
leased/metered + persisted-as-forkable-mind-cell + R2-verifiable by the renter.

North star: *rent a coding agent you can jail, budget, fork, rewind, and
cryptographically audit against the chain.*

## Current thrust
UNITS 1 + 3 LANDED (seam proven end-to-end vs a real grain). UNIT 2 (real
firmament OS-jail, `real-jail` feature) building — the load-bearing "body is
OS-jailed" move. macOS Seatbelt is real+enforced so it validates locally.
Design: `docs/deos/GRAIN-CONFINED-BODY.md`.

## Key grounding facts (verified at HEAD)
- The unification seam is `AgentBrain` (`dregg-agent/src/agent.rs:482`):
  `next_action(step)->Option<AgentAction>` + `observe(&ActionObservation)`.
  A jailed body plugs in as a brain — the grain drive path is unchanged.
- `deos-hermes` is a STANDALONE heavy workspace (pulls `dregg-sdk` default =
  verified Lean executor) → a main-workspace crate can't depend on it. Reuse the
  jail primitive directly: `dregg-firmament` `process-pd` = `libc`-only (cheap),
  `process-pd-sandbox` adds seccomp+landlock. That's the light path.
- `agent-host/src/isolation.rs` `JailSpec` (bwrap, Linux-only) is a 2nd backend.

## Next 3 moves
1. `grain-jail` crate: the line protocol + `ConfinedBrain` (AgentBrain impl),
   validated against a stand-in body over a pipe. No jail yet. [UNIT 1 — code
   written, building (blocked on the shared cargo lock)]
2. Spawn the body under firmament `process-pd[-sandbox]`; assert confinement
   teeth. [UNIT 2]
3. Drive a real `agent-platform` grain with a `ConfinedBrain` end-to-end;
   renter verifies (R2) the jailed session. [UNIT 3]

## Unit-2 grounding (verified at HEAD)
- `dregg-firmament` is workspace-EXCLUDED (its own `[workspace]`, edition 2021),
  BUT members `servo-render`/`starbridge-v2`/`android-cell`/`starbridge-web-surface`
  already path-dep it — so `grain-jail` CAN path-dep it under a `real-jail`
  feature (cargo ignores a path-dep's own `[workspace]`). No manifest fight.
- `process-pd` = `libc`-only (fork/fd-close/socketpair); `process-pd-sandbox`
  adds seccomp+landlock (Linux). macOS sandbox: firmament HAS a Seatbelt backend
  (`process_kernel.rs:1247`), so the real OS-jailed body can be validated LOCALLY
  on this macOS box, not only on a Linux builder. `spawn_pd_confined` lives in
  `sel4/dregg-firmament/src/process_kernel.rs`.

## Reorder note
UNIT 3 (real-grain end-to-end) pulled AHEAD of UNIT 2 (firmament jail): proving
the unification against the real grain machinery is higher value-per-risk than
hand-rolling firmament fork/fd at this hour. Key facts that made it clean:
`drive`/`drive_serving` take `&mut dyn AgentBrain` (ConfinedBrain slots in);
`AgentAction::CellWrite` is INTRINSIC (`agent.rs:1775` `state.cells.insert` — no
external tool); `cell:<path>` caps grant the write. So a ConfinedBrain over an
in-process channel drives a real grain with zero drive-path change. Unit 2 (swap
the in-process channel for a firmament endpoint fd via `spawn_pd_confined_with_
surface` → clean parent `UnixStream`) is next; it needs `process-pd-sandbox`
(macOS Seatbelt works locally).

## Done-log
- Grounded the grain↔confined-body seam; wrote `docs/deos/GRAIN-CONFINED-BODY.md`.
- UNIT 1 LANDED (`8de7447da`): `grain-jail` (protocol + `ConfinedBrain` + map +
  5 tests green), added to workspace.
- UNIT 3 code written: `grain-jail/tests/grain_end_to_end.rs` — a ConfinedBrain
  drives a REAL agent-platform grain (rent → drive_serving → meter → R2 verify →
  forgery refused; + a cap-refusal test). dev-deps agent-platform/hosted-lease/
  types. BUILDING (heavy tree).

## Open decisions for morning-ember
- (none yet)

## Honest caveats carried
- Live external Nous hermes broken in-env (`ModuleNotFoundError: acp`) → validate
  live via the Rust stand-in ACP peer / `--brain hermes` model-over-portal.
- Grain R3 whole-history STARK is a known gap (`WHOLE_HISTORY_GAP`); R2 is the
  verifiability ceiling today.
- `agent-host/src/isolation.rs` bwrap jail is built-but-unwired.
- Public substrate repo: never write the operated-product name or the wrong
  stack name (the HTTP stack is `httpe`); a commit hook enforces this.
