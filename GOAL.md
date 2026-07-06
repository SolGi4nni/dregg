# GOAL — deos as the substrate for confined, verifiable, forkable hosted agents

**Standing goal (set 2026-07-05, ember asleep → Fable works the night):**
Unify the grain and the confined-hermes hosting stacks so a hosted agent (a
jailed coding agent, or any BYO brain) IS a first-class grain: OS-jailed +
leased/metered + persisted-as-forkable-mind-cell + R2-verifiable by the renter.

North star: *rent a coding agent you can jail, budget, fork, rewind, and
cryptographically audit against the chain.*

## STATE FOR MORNING-EMBER (2026-07-06 ~01:05, overnight session)
The confined-body grain is DONE and green — 13 commits (`8de7447da`..`ea92ed7d3`),
incl. the full hostile-body robustness set (crash/hang+SIGKILL/garbage/cap/flood).
A hosted body plugs into the grain's `AgentBrain` seam as a `ConfinedBrain`
(crate `grain-jail`), so with ZERO grain-drive-path change a body is OS-jailed
(firmament, macOS Seatbelt — validated locally, denies /etc/passwd), yet every
action is cap-gated + metered + minted + R2-verified, does real file work through
the seam, and a crashing body leaves the grain clean. Play with it:
`cargo run -p grain-jail --example rent_a_confined_agent [--features real-jail]`.

WHY I STOPPED HERE (not blocked, a quality call): the one remaining north-star
piece — the real coding-agent body (an in-jail LLM harness over ONE granted
egress door) — is first-of-its-kind, security-sensitive network-confinement work
(no existing firmament test drives the real net door from a jailed child; a
correct deny-test must distinguish sandbox-EPERM from ECONNREFUSED on macOS SBPL).
Rushing it at 00:25 risked a vacuous/wrong test. It is CRISPLY SCOPED with exact
APIs in `docs/deos/GRAIN-CONFINED-BODY.md` (Frontier) — a clean fresh-head start.

## Verified GAPS (from a resume-tick verify-before-building pass)
- FORK/REWIND a CONFINED session is BLOCKED: fork/rewind/stitch live on
  `grain-fork::Grain` (mind = raw `learn`/`recall` cell memory, NO agent-brain
  drive); the confined session lives on `agent-platform::Tenant` (brain-driven,
  only R1 checkpoint-countersign, NO fork/rewind). Composing them = the spine-#4
  grain-struct UNIFICATION (give the Tenant's Session-mind fork/rewind, OR give
  grain-fork::Grain an AgentBrain drive) + an agent-platform edit (another
  terminal's file). A real unit, not a demo.
- EGRESS DOOR needs a firmament API note: `spawn_pd_confined_with_surface` gives a
  clean byte-pipe but the DEFAULT (endpoint-only) confinement; `spawn_pd_confined_
  with(granted, Confinement, body)` takes a custom `Confinement` (add the net door
  via `with_net_out("host:port")`) but gives NO surface socket. Combining a net
  door WITH a clean line-protocol pipe needs either a firmament surface+confinement
  variant (edit the excluded firmament crate) or the fd-recovery dance
  (deos-hermes's `recover_endpoint_fd`). LEAD: `spawn_pd_confined_with` hands the
  body a `KernelClient` (the CONTROL socket) — if KernelClient exposes its fd /
  UnixStream, use THAT as the line-protocol byte-pipe (as deos-hermes uses the
  endpoint), so the net-door Confinement + the pipe coexist with no firmament edit.
  Verify KernelClient's API first. Decide before building the LLM body.

## Next moves (fresh head)
1. The egress door — resolve the surface+netdoor variant question above first,
   then `spawn_confined_body_with_egress` (`Confinement::with_net_out`, ONE
   host:port) + a CORRECT deny test (distinguish sandbox-EPERM from ECONNREFUSED).
2. The in-jail model harness: `OpenAICompatBrain` inside the jail over a MOCK
   model server on 127.0.0.1 → the full "rent a coding agent" mechanic.
3. Spine-#4 grain-struct unification (fork/rewind a confined session).
4. PRODUCTIZE in agent-platform (first-class confined/jailed drive) — other
   terminal's file; helper or quiet window. + run `--features real-jail` in CI.

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
- UNIT 3 LANDED (`ee47494c4`): `grain-jail/tests/grain_end_to_end.rs` — a
  ConfinedBrain drives a REAL grain (rent → drive_serving → meter → R2 verify →
  forgery refused; + a cap-refusal test). 2 tests green.
- UNIT 2 LANDED (`f855fec2a`): `grain-jail/src/jail.rs` (`real-jail` feature) —
  a REAL firmament-jailed body (macOS Seatbelt) drives the ConfinedBrain over a
  socketpair and is DENIED /etc/passwd (confinement tooth bites). Validated
  locally. Run with `--features real-jail`.
- UNIT 4 LANDED (`d994fdee9`): a REAL jailed body drives a REAL grain, R2-verified
  — the complete mechanic bar the LLM.
- DEMO + DOCS LANDED (`49d1ee5b2`, `bb9666e69`): runnable `cargo run` example
  (both in-process + `--features real-jail`), `docs/guide/CONFINED-AGENTS.md`.
- CRASH-ROBUSTNESS LANDED (`23df1d51e`): a jailed body that crashes mid-session
  leaves the grain clean + R2-verifiable (host absorbs a hostile/faulty body).
- OP EXTENSION LANDED (`4fff5263a`): protocol `args` → generic `Op(ToolCall)` so a
  confined body does REAL file work (fs_write host-side, cap-gated).
- HOSTILE-BODY ROBUSTNESS COMPLETE: crash (`23df1d51e`) + hang/timeout+SIGKILL-reap
  (`4973c6a59`) + flood/OOM cap (this commit) + garbage + cap-exceed. A confined
  or jailed body cannot wedge, fool, or OOM the host by any of these.

## What "awesome" is next (post-spine)
- A runnable EXAMPLE (`cargo run`) — the "rent a verifiable confined agent" demo.
- docs/guide onramp.
- PRODUCTIZE: agent-platform gains a first-class jailed-grain drive (⚠ agent-
  platform is another terminal's active file — do via a grain-jail helper or a
  quiet-window edit, not a clobber).
- The real coding-agent body: a confined Rust harness + a GRANTED EGRESS DOOR to
  an LLM (firmament `with_read_path`/egress) — the jail denies execve, so the
  body is in-jail Rust reaching the model over one revocable door. [bigger]
- SSE transcript: replay → incremental live push (spine #5).

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
