# APPS AS CELLS — the deos applications become full members of the cell graph

## The one-sentence thesis

> A deos app is not a gpui silo that happens to render inside deos; it is a **view
> over the one cap-secure, conserved, provenance-carrying, time-travelable,
> mergeable cell graph** — its core object is a cell (or cell-subgraph), its
> mutations are turns, its history is a receipt chain, its documents speak the
> patch-theoretic document language, and its multiplayer/merge is the
> branch-and-stitch membrane — so the editor, the terminal, the chat room, and the
> Hermes session all share *one* substrate and the moldable inspector can open any
> of them as cells.

The apps stand at different depths. The terminal's alacritty grid
(`deos-terminal/src/model.rs:204` — `Terminal` owns an `Arc<FairMutex<Term>>`) and
the chat timeline (`deos-matrix`) live in app memory; the editor's durable core is
a `dregg_doc::RopeDoc` patch history (`deos-zed/src/editor.rs:80`), and the Hermes
tool-call stream is receipted turns. The unlock, uniform across all four, is to
make each app's *durable core* a cell and each
*mutation* a turn, leaving the *ephemeral view-state* (scroll offset, cursor blink,
selection, syntax-highlight cache) where it belongs — in app memory. The seams that
point here already exist; this doc designs the mappings against the real machinery
and stages them honestly into now / soon / research.

The discipline (per the project memories): a labeled seam is *work to drive*, not a
wall to live behind (`feedback-seams-are-work-not-walls`); the capability usually
already EXISTS, disconnected — **weld, do not rebuild** (the WELD METHOD). This doc
is a census-then-weld plan, not a from-scratch design.

---

## 0. The substrate, in the terms the apps need

The four properties an app inherits *for free* by becoming a cell, each grounded:

| property | machinery | file:line |
|---|---|---|
| **a stateful object** | `Cell { state, capabilities, program, lifecycle, permissions, … }`; `CellState` is 16 user fields + an ext-field map (`fields_root`) + 8 kernel side-table roots (`system_roots`) + a signed balance | `cell/src/cell.rs:1-9`, `cell/src/state.rs:100-120`, `state.rs:31-67` (`N_SYSTEM_ROOTS` / `system_root::*`) |
| **cap-gated mutation** | a mutation is a `Turn` the executor admits only if `required ⊆ held`; the c-list is `CapabilitySet`, each `CapabilityRef` carries `permissions: AuthRequired`, facet mask, expiry, R7 freshness epoch | `cell/src/capability.rs:43-90`, `turn/src/executor/execute.rs:210` (`execute(turn, ledger) -> TurnResult`) |
| **conservation (Σδ=0)** | the signed-`i64` balance well + the issuer-cell-carries-−supply discipline; every turn conserves value | `cell/src/state.rs:111-120` |
| **provenance / time-travel** | every committed turn leaves a `TurnReceipt`; `History::replay_to` / `fork_at` folds the chain; the witness cursor is a consistent cut | `turn/src/collapse.rs:14-21`, `deos-matrix/src/membrane.rs:126` (`WitnessCursor`) |
| **per-viewer projection + merge** | `Membrane::project`/`reshare` (the anti-amplification meet), `World::fork`, snapshot/restore, the stitch | `deos-matrix/src/membrane.rs:20-42`, `BRANCH-AND-STITCH-PROTOCOL.md` |

Two substrate facts are *load-bearing* for the apps specifically, because apps are
interactive and turns are not free:

- **`WitnessMode::Symbolic`** (`turn/src/collapse.rs:99-137`). A turn's *state
  transition* (balances/caps/nonces — the abstract progress proved in
  `ExecRefinement.lean`) is separable from the *witness layer* (the Merkle
  `pre/post_state_hash` a light client needs). Symbolic mode applies the full
  transition and runs **every admission gate identically**, but DEFERS witness
  materialization (it never calls `Ledger::root()`), stamping `DEFERRED_STATE_HASH`
  (`collapse.rs:81`). `collapse` (`collapse.rs:171`) re-runs the recorded symbolic
  turns under `Full` to reproduce byte-identical publishable witnesses. **This is
  the answer to "an app can't pay a witness per keystroke."** A symbolic receipt is
  local/unpublishable until collapsed — exactly right for a fast interactive loop
  that collapses on a checkpoint/publish boundary.
- **`CommitmentMode::Partial`** (`turn/src/action.rs:31-38`) + the partial-turn /
  promise machinery (`turn/src/{pending,eventual,conditional}.rs`, referenced from
  `membrane.rs:33`). A signer need not see the whole turn forest to sign one action,
  and a turn can carry holes resolved later — the basis for collaborative/joint
  edits where the consent point is a hole.

---

## 1. EDITOR (deos-zed) — buffer = a document-language DOCUMENT, file = a cell

### Where it stands

deos-zed is built around the ONE seam this needs: **`Fs`**
(`deos-zed/src/fs.rs:68-86`). The editor, file-tree, and demo never call `std::fs`;
all I/O goes through `trait Fs { load, save, read_dir, metadata, backend_label }`.
`RealFs` (std::fs) ships; `FirmamentFs` (`deos-zed/src/fs/firmament.rs`) is the
**live cell-backed impl** behind the `firmament` feature (the stub build without
the feature errors clearly rather than faking it). The mapping it realizes:

| `Fs` method | firmament realization (`firmament.rs:10-21`) |
|---|---|
| `load(path)` | resolve `path` → the file-cell via the path namespace; read the committed content substance (a read is authority-checked, no turn) |
| `save(path, c)` | a **dregg TURN**: a cap-gated `SetField` write over the file-cell's content, driven through the real `TurnExecutor`; the **receipt is the "saved" ack**, independently verifiable |
| `read_dir(p)` | list the namespace's entries under `p` (the directory cell) |
| `metadata(p)` | resolve the path → file-cell or directory; report kind + length |

The save path routes through the seam: `Editor::save` (`editor.rs:380`) calls
`self.fs.save(&path, &content)` (`editor.rs:396`). `FirmamentFs` runs over the
`LedgerSpine` seam (`deos_zed::fs::LedgerSpine`), with two impls: `OwnedSpine`,
a self-contained in-process `Ledger` + `TurnExecutor` (the same verified spine
starbridge-v2's `World` wraps), seeding an author cell + a root directory cell;
and `WorldSpine` (`starbridge-v2/src/dock/editor_surface.rs:80`), which mounts
the *host deos image's* live `World` — saves go through `World::commit_turn` and
land in the same `World::ledger()` the cockpit cell inspector reads, so the
editor edits the image's cells, not a private ledger.
`EditorPane::firmament_over(world, ...)` wires the `WorldSpine` mount into the
unified boot (`starbridge-v2/src/unified_boot.rs:195`) and self-hosting
(`self_hosting.rs`) paths.

### The two-level mapping (file=cell; buffer=document — both built)

**Level 1 — file = cell, save = receipted turn (BUILT, `firmament` feature).**
`save` is a content-replacing turn; the content substance is the editable text.
This is the *content-flat* mapping: the cell's commitment binds the whole-file
bytes; save is atomic for free (the turn commits or it doesn't). This is the
editor's membership in the cell graph, confined to one impl file — the editor and
file-tree code never changed, which is the whole point of the `Fs` seam.

**Level 2 — buffer = a document-language DOCUMENT (BUILT — the `dregg-doc`
crate).** The content-flat file is the floor; the *document language*
(`DOCUMENT-LANGUAGE.md`) is the ceiling. There, a document is a **Pijul-shaped
patch graph**: vertices are content-addressed atoms (spans), edges encode order,
status is alive/dead (monotone tombstone). The patch core is the workspace crate
`dregg-doc` (`DocGraph`, the `Add`/`Delete`/`Connect` patch grammar, `History`,
merge, blame — `dregg-doc/src/{graph,patch,history,merge,blame}.rs`), and the
editor folds it:

- The **rope buffer ↔ patch graph impedance** is bridged by the **diff-to-patch**
  layer: `Editor` holds a `dregg_doc::RopeDoc` (`editor.rs:80-98`) — a patch
  `History` whose fold materializes the buffer; on save, `RopeDoc::edit_rope`
  (`dregg-doc/src/rope.rs:53`) diffs the new rope against the current content and
  accrues the minimal `Add`/`Delete`/`Connect` patch. The visible buffer stays a
  rope (fast interactive editing, ephemeral view-state); the *durable* document is
  the patch fold. Atom granularity is a **design choice to revisit empirically** —
  the editor runs line-granular (`Granularity::Line`, `editor.rs:327`;
  `DOCUMENT-LANGUAGE.md` §4.4); the merge-correctness theorem is proven in
  `metatheory/Dregg2/Deos/DocMerge.lean`, and `RopeDoc::merge_branch`
  (`dregg-doc/src/rope.rs:156`) is the pushout the editor calls. The
  blame/timeline + conflict-object faces render in `deos-zed/src/doc_viewer.rs`
  (both alternatives side by side, never a `<<<<<<<` text wound).

- **Multi-author = branch-and-stitch.** Each author edits a **branch** of the
  document cell (a divergent configuration off a past witness cursor, holding NO
  cap to the shared doc — firmament confinement, `BRANCH-AND-STITCH-PROTOCOL.md`
  §2). Publishing is a **`Stitch` = pushout** (§3): I-confluent spans merge clean;
  a contested paragraph yields a **first-class conflict state** (an antichain in the
  order — `DocMerge.lean::ConflictAt`), NOT a rejected merge; a genuinely
  conserved/authority-pinned clash forces a linear-logic *explicit drop*. The
  conflict renders as "both versions, choose or rewrite," the rest of the doc
  usable while the conflict stands.

- **Per-region edit caps.** Read-projection is the membrane (a darkened span keeps
  its provenance, withholds bytes); write-authority is the affordance gate
  (`{view, comment, edit, admin}` lifted to per-region, `DOCUMENT-LANGUAGE.md`
  §3.2-3.3). "Who may edit which region" = "who holds the `edit` cap reaching those
  cells."

### What's a cell vs ephemeral

| durable (cell / turn / receipt) | ephemeral (app view-state) |
|---|---|
| file content (substance / patch-fold) | rope buffer (a fast cache of the fold) |
| save / each patch (a turn + receipt) | cursor position, selection, scroll |
| document conflict states (antichain) | syntax-highlight cache, language choice |
| the directory tree (`DirectoryCell`s) | tree expand/collapse UI state |

---

## 2. TERMINAL (deos-terminal) — session = a cell, command = a cap-gated turn

### Where it stands

The terminal model (`deos-terminal/src/model.rs`) is a real PTY over `$SHELL` with
the alacritty event loop parsing bytes into a `Term` grid. `TerminalSurface`
(`cockpit_surface.rs`) mounts it as a cockpit dock surface. Today the *entire*
session — scrollback, grid, cwd, env — lives in `Terminal`'s `Arc<FairMutex<Term>>`
(`model.rs:204`). `spawn_shell` (`cockpit_surface.rs:38`) inherits the host's
`current_dir` + `env::vars`. There is **no cell, no cap, no receipt** — a terminal
is the most ambient-authority surface in deos (it runs `$SHELL` with the host's full
authority).

### The mapping

**Session = a cell.** A terminal session is a cell whose state is:
- `cwd` and `env` → cell state fields (`CellState::fields` / the ext-field map).
- the **command history = a provenance chain** — each command is a turn, so the
  history *is* the receipt chain (`History`), time-travelable and replayable.
- scrollback / the live grid → **ephemeral view-state** (the `TerminalContent`
  snapshot, `model.rs:61-72`), NOT cell state. The grid is a *projection* of the
  byte stream, regenerable; it is not the durable object.

**Each command = a cap-gated turn (the exec-cap).** This is the deos novelty for a
terminal: running a command is **exercising an exec capability** over the session
cell. Instead of the shell having ambient authority, the session cell holds an
**exec-cap** (a `CapabilityRef` with a facet mask and possibly a `CapabilityCaveat`
— `capability.rs:31-40` — e.g. "only commands matching this allowlist," "rate ≤ N,"
"deadline D"). A command-run turn:
1. spends the exec-cap (authority-checked, `required ⊆ held`),
2. records the command + its effect on `cwd`/`env`/exit-status as the turn's effect,
3. leaves a receipt — so "what ran in this terminal, under what authority" is a
   verifiable chain, not an opaque syscall trail.

This is the **same shape Hermes already realizes** (§4): the Hermes `ToolGateway`
turns a tool-call into a cap-gated metered receipted turn (`deos-hermes/src/bridge.rs`,
`grant_registry.rs`'s scope + rate ceiling + deadline). A terminal command is a
tool-call by another name; the exec-cap is the terminal's `ToolGrant`.

### The hard part: interactivity vs per-turn cost → `WitnessMode::Symbolic`

A terminal **cannot pay a witness per keystroke** — even per-command, a full Merkle
witness on every `ls` is too heavy for an interactive shell. This is precisely what
`WitnessMode::Symbolic` (`turn/src/collapse.rs`) exists for:

- The session runs **Symbolic**: each command-turn applies its full state
  transition and runs **every admission gate** (the exec-cap check is NOT deferred —
  `collapse.rs:30-34`), but defers the Merkle root, stamping `DEFERRED_STATE_HASH`.
  The interactive loop stays fast; the *decisions* (was this command authorized?)
  are made eagerly and identically to Full.
- On a **publish/checkpoint boundary** (closing the session, sharing it via a
  membrane, settling it to mainline), `collapse` (`collapse.rs:171`) re-runs the
  recorded command-turns under `Full` to materialize the publishable receipt chain
  — byte-identical to what a Full run would have produced.

So a PTY session becomes a cell **without losing interactivity**: keystrokes stay
PTY-fast (raw bytes to the shell, `model.rs:293`); the *command* is the turn
granularity; the witness is deferred and collapsed on demand. The symbolic-local /
collapse-to-publish split is the load-bearing design choice, and the machinery is
already built.

### What's a cell vs ephemeral

| durable | ephemeral |
|---|---|
| session cell: `cwd`, `env`, exec-cap | the live grid / `TerminalContent` snapshot |
| each command (a symbolic turn → collapsed receipt) | scrollback rendering, cursor blink, colors |
| the exec-cap caveats (allowlist/rate/deadline) | display offset, selection, window size |

(Honest residual: a long-running *interactive* program inside the PTY — `vim`, a
REPL — is one PTY session = one cell with a stream of keystrokes the cell does not
turn-ify individually; the *command invocation* is the turn, the program's internal
I/O is ephemeral PTY traffic. The exec-cap gates *launching* the program; gating its
internal syscalls is the seL4-PD confinement story, not the turn layer.)

---

## 3. CHAT (deos-matrix) — room = a cell, messages = its history

### Where it stands — largely designed already

`deos-matrix/src/membrane.rs` is the richest of the seams and already does most of
this design's work. It defines the **rehydratable membrane**: a chat message carries
a `MembraneEnvelope` (`membrane.rs:58-100`) — a cap-bounded, frustum-culled snapshot
of a deos world-fork at a witness cursor, with an anti-substitution `frustum_root`
tooth, a `dregg://` sturdyref, an attenuated `lineage` (`SurfaceCapability` bytes),
and the `FrustumCut`. A recipient **rehydrates** it into a live fork, **drives**
real verified turns on it, and **stitches** divergent forks back (`MembraneHost`
trait, `membrane.rs:206-238`).

The "real now" ledger (`membrane.rs:20-34`) names exactly the in-tree machinery:
`World::fork`, `persist::Snapshot` + `apply_snapshot_verified` (fail-closed),
`Ledger::iter()` over `Cell::capabilities` (the frustum), `Membrane::project`/
`reshare` (anti-amplification meet), `rehydrate`. The stitch's conflict algebra is
typed (`StitchOutcome` / `ConflictObject` / `ConflictReason` — Conservation /
Nullifier / AuthorityRevoked / CapAmplification, `membrane.rs:160-195`) — conflicts
as first-class objects, exactly the document-language shape (§1 Level 2) at the
world-fork granularity.

### The mapping (the one piece to name explicitly)

What `membrane.rs` carries *across* a room; what this doc adds is naming the **room
itself as a cell**:

- **room = a cell**; its **messages = its history** (the receipt/turn chain). A
  message-send is a turn appending to the room cell; the membrane envelope rides as
  a message *payload* (the `software.ember.deos.membrane` event key,
  `membrane.rs:49`). The room's membership/permissions are the room cell's
  `Permissions` + c-list; "who may post" is a cap.
- **Liveness is DERIVED, never asserted** (`membrane.rs:137-148`, mirroring
  `Rehydration`): a rehydrated membrane is `Live` / `ReplayedDeterministic` /
  `ReconstructedApproximate` by computation, so the chat UI cannot lie about whether
  you're reading a live fork or a frozen snapshot.
- The **stitch IS the cross-app merge** (see §5): because the membrane snapshots a
  *world-fork* (not a chat-specific object), a membrane minted from the editor or a
  game and *sent through chat* rehydrates the same way. Chat is the **transport that
  makes the membrane multiplayer**; the merge spans apps because the object on the
  wire is a generic frustum, not a chat type.

What stays ephemeral: the rendered timeline, typing indicators, read receipts (the
Matrix kind, not the dregg receipt), draft input — all view-state. The durable
object is the room cell + its turn history + the membrane payloads.

---

## 4. HERMES (deos-hermes) — session = a cell, tool-calls = turns (DONE)

### Where it stands — the reference realization

deos-hermes is the **already-closed** instance of this whole thesis, and the other
apps should be read against it. Hermes (an agent) exposes itself over ACP; a deos
ACP client intercepts **every tool-call before it runs** and routes it through the
proven `ToolGateway` (`deos-hermes/src/lib.rs:1-37`). The tool-call becomes a
**cap-gated, metered, RECEIPTED dregg turn** on the verified executor — or an in-band
refusal. This is the ADOS thesis ("a turn = the exercise of an attenuable
proof-carrying token over owned state, leaving a verifiable receipt") realized with
a real agent.

The grounding (`lib.rs:25-27`): the enforcement is *entirely* the proven
`ToolGateway`'s (`delegAdmit` mirror + executor-side `mandate_program` backstop).
`bridge.rs`'s `HermesGateway` (`bridge.rs:108`) holds one `ToolGateway` per
`ToolKind`, lazily admitted via `ToolGateway::admit` against a root token + a
`ToolGrant` (`grant_registry.rs` — scope + rate ceiling + deadline), and routes each
call through `ToolGateway::invoke` (`HermesGateway::admit_call`, `bridge.rs:245`),
mapping the verdict back to an ACP `PermissionOutcome`. The REAL path yields a
genuine `dregg_turn::TurnReceipt`, and the ACP *transport* is real too:
`acp_client` is the ndjson JSON-RPC ACP client (`initialize` → `session/new` →
`session/prompt`, answering each `session/request_permission` through the
gateway), transport-agnostic over `AcpPeer` — it spawns a live `hermes-acp`
subprocess (`acp_client::AcpTransport`) or drives an in-process peer.
`HermesAgentPeer` (`deos-hermes/src/agent_peer.rs`) is the brain-driven ACP peer
that replaced the scripted `MockHermesPeer`: an `LlmBrain`'s closed loop whose
every `CallTool` step becomes a streamed `tool_call` + permission request answered
by the gateway. `deos-hermes/tests/acp_loop.rs` exercises the loop over the faithful mock;
`deos-hermes/tests/live_acp.rs` drives the real `hermes-acp` subprocess end to end (it skips,
stating why, when the environment lacks the install or a model provider).

### The mapping (already true)

- **session = a cell**: the Hermes session is the agent's cell; its authority is
  the root token + the per-kind `ToolGrant` caps.
- **tool-call = turn**: each invocation is a cap-gated metered turn → receipt.
- **the affordance set IS the agent's attenuated action space** (the `DEOS-APPS.md`
  agent-as-first-class-user shape): Hermes cannot exceed its grants; a smarter brain
  does not get a bigger cage.

Hermes is the **template** the terminal exec-cap (§2) directly copies: the
`ToolGateway` + `ToolGrant` (scope/rate/deadline) is exactly the terminal's
exec-cap + caveat. "A terminal command is a tool-call by another name" is not a
metaphor — it is the same gateway.

---

## 5. THE UNIFICATION — apps as views over the one graph

### 5.1 One graph, many lenses

Once each app's core is a cell, the four apps are **views over one cell graph**, and
the moldable inspector (`INSPECTOR-FRAMEWORK.md`) is the framework that makes this
literal. A cell offers multiple **presentations** (`PresentationKind` —
`RawFields` / `Graph` / `DomainVisual` / `Provenance` / `Affordances` / `Invariant`
/ `Source`, `INSPECTOR-FRAMEWORK.md` §1.1). An *app* is a **`DomainVisual`
presentation** of its core cell:

- the editor is the `DomainVisual` of a document cell (the rendered/source/
  conflict-view, `DOCUMENT-LANGUAGE.md` §5);
- the terminal is the `DomainVisual` of a session cell (the grid);
- the chat room is the `DomainVisual` of a room cell (the timeline);
- the Hermes session is the `DomainVisual` of an agent cell (the tool-call stream).

The same cell *also* offers `RawFields` (the cockpit inspector's field-tree),
`Provenance` (the receipt-chain scrubber — undo/redo/time-travel for *any* app),
`Graph` (the ocap web), `Affordances` (its verb buttons). **So the cockpit's
moldable inspector and the apps share the same cells**: opening a terminal session
in the inspector shows its exec-cap, its cwd field, its command receipt chain;
opening a document shows its patch graph and conflict states. The app is the
domain-pretty face; the inspector is the moldable many-faced face; they are
*presentations of one `Presentable`*, not parallel state.

Every app mutation, uniformly, is a **`Gadget` on the predict-then-commit spine**
(`INSPECTOR-FRAMEWORK.md` §1.2): `IntentDraft → simulate() → commit()`
(`starbridge-v2/src/simulate.rs`). A save, a command-run, a message-send, a
tool-call — each is a `CommittingGadget` whose `commit()` runs the identical turn
the app fires. The apps stop being special; they are gadget-armed presentations.

### 5.2 The membrane / merge spans apps

Because the on-the-wire object is a **generic frustum of the cell graph** (a
`MembraneEnvelope` of a `World::fork`, `membrane.rs`), not an app-specific type,
**the membrane and the merge span apps**:

- A document branch (§1), a terminal session (§2), a game world (`DEOS-APPS.md`),
  or a mixed subgraph can all be frustum-culled, sent through chat (§3 is the
  transport), rehydrated by a peer, driven, and stitched back — *with one
  mechanism*. The stitch's conflict algebra (Σδ=0 / nullifier / authority /
  cap-amp, `membrane.rs:182-195`) is value-layer-universal; the document-language
  conflict (an antichain, `DocMerge.lean::ConflictAt`) is the data-layer sibling
  (`DOCUMENT-LANGUAGE.md` §2.4). Both surface as first-class conflict-objects.
- This is the payoff the silo model *cannot* reach: in the silo world, sharing an
  editor buffer and sharing a terminal session and sharing a chat are three
  bespoke features. Here they are one frustum-snapshot + rehydrate + stitch,
  because the apps are views over one graph.

### 5.3 Why this is the deos UX vision realized

The moldable-inspector vision (1999-AOL wonder fused with Pharo liveness) *requires*
this: an adept can open any app's cell in the inspector and mold it live (the Pharo
image-is-its-own-IDE bar); a 5-year-old can click an app surface and absorb it (the
AOL bar). Both work *because the app is a presentation of a cell* — there is one
object, seen two ways, not an app-silo and a separate inspector that can never reach
into it.

---

## 6. THE PHASED PLAN — landed vs remaining

### LANDED (in-tree, feature-gated where noted)

1. **Editor file=cell** — `FirmamentFs` is the live cell-backed `Fs` impl
   (`deos-zed/src/fs/firmament.rs`, `firmament` feature): `save` = a cap-gated
   receipted `SetField` turn through the real `TurnExecutor`; `load`/`read_dir`/
   `metadata` = authority-checked reads. The editor/file-tree code never changed —
   the whole point of the `Fs` seam. The host-image mount is in-tree too:
   `WorldSpine` implements `LedgerSpine` over the live cockpit `World`, wired in
   via `EditorPane::firmament_over` in the unified-boot and self-hosting paths
   (§1); `OwnedSpine` is the self-contained in-process impl of the same seam.
2. **Hermes** — the cap-gated tool-call→turn→receipt path AND the ACP transport
   are real: `acp_client` drives a live `hermes-acp` subprocess or the
   brain-driven `HermesAgentPeer` (`agent_peer.rs`); `deos-hermes/tests/live_acp.rs` covers
   the live loop (§4).
3. **Buffer = document** — the `dregg-doc` patch core (`DocGraph`, the
   `Add`/`Delete`/`Connect` grammar, `History`, merge, blame) + the rope↔patch
   bridge (`RopeDoc::edit_rope`) + the editor fold + the blame/conflict viewer
   (`doc_viewer.rs`), with the merge join proven in
   `metatheory/Dregg2/Deos/DocMerge.lean` (§1 Level 2).
4. **The executor-backed `MembraneHost`** — `ForkMembraneHost`
   (`starbridge-v2/src/shared_fork.rs:1017`, `dev-surfaces` feature) mints real
   frustum envelopes, rehydrates into real `World` forks, drives real turns, and
   stitches the diff back; the `deos-matrix` chat lane holds it as its
   `dyn MembraneHost`.
5. **The inspector L1 spine** — `Presentable`/`PresentationKind`
   (`starbridge-v2/src/presentable.rs:345`) with cell/document/cap inspections
   implemented (`cell_inspector.rs`, `doc_lens.rs`, `cap_inspector.rs`).

### NOW (weld; the substrate carries it)

6. **Terminal session=cell, command=turn** — give the session a cell (cwd/env
   fields + an exec-cap modeled on Hermes' `ToolGrant`); run the session in
   `WitnessMode::Symbolic` (`collapse.rs`); make each command a cap-gated symbolic
   turn; `collapse` on session-close/share. Reuses the Hermes gateway shape and the
   already-built symbolic machinery — a weld, not a build.
7. **Chat room=cell** — name the room a cell with messages as its turn history; the
   `MembraneEnvelope` rides as a message payload (`membrane.rs:49`), and the
   executor-backed host exists (item 4).
8. **Per-region edit caps** — lift `{view,comment,edit,admin}` to per-region edit
   caps over the document patch graph (`DOCUMENT-LANGUAGE.md` §3.2-3.3).

### SOON (the conflict semantics end to end)

9. **First-class conflict states end to end** — the editor's conflict-object
   viewer (`doc_viewer.rs`) and the stitch's typed conflicts (`StitchOutcome`)
   exist; remaining: the `ConflictView` presentation + resolution gadget in the
   inspector (`DOCUMENT-LANGUAGE.md` §3.5) so a conflict is *resolved* through the
   same gadget spine it is rendered by.
10. **Terminal collapse-to-membrane** — sharing a session through chat = collapse +
    frustum-cull + send; a peer rehydrates a read-only or drivable session fork.

### RESEARCH (the load-bearing proofs / open questions)

11. **Atom granularity** for the document patch graph (char/line/span/semantic) —
    an *empirical* design choice, not a theorem (`DOCUMENT-LANGUAGE.md` §4.4). The
    editor runs line-granular; refine if it hurts.
12. **Conflict-as-state soundness** — a stored conflict binds *both* alternatives +
    provenance in the cell commitment, so a light client can't be shown a conflict
    hiding a forged alternative (the `holeFill_binds_in_circuit` discipline applied
    to the antichain).
13. **Settlement Soundness carried across the cross-app stitch** — the core
    authority-live-at-settlement theorem is proven
    (`metatheory/Metatheory/SettlementSoundness.lean`: `settlement_soundness`,
    `revoke_before_tip_unsettleable`); remaining: carrying it across the apps —
    light-client-unfoolability for a frustum-of-mixed-apps rehydrate + stitch.
14. **The interactive tempo dial (#169)** for the symbolic-local / verified-at-
    boundary loop tuned per app (terminal vs editor vs game have different collapse
    cadences) — `DEOS-APPS.md` §"interactive/real-time tempo gap".

---

## 7. HONESTY LEDGER

**Solid from code read at HEAD:** the `Fs` seam + the live cell-backed
`FirmamentFs` save=turn impl (`deos-zed/src/fs.rs`, `fs/firmament.rs`, `firmament`
feature; the save path routes through it, `editor.rs:380-396`), mounted over the
live cockpit `World` via `WorldSpine`
(`starbridge-v2/src/dock/editor_surface.rs:80`, wired at `unified_boot.rs:195`
and in `self_hosting.rs`); the terminal PTY
model (`deos-terminal/src/model.rs`) with state in app memory and ambient host
authority (`cockpit_surface.rs:38`); `WitnessMode::Symbolic` + `collapse` + the
symbolic-defers-witness-not-decision soundness (`turn/src/collapse.rs`);
`CommitmentMode::Partial` (`turn/src/action.rs:32`); the Hermes ToolGateway path —
tool-call → cap-gated metered receipted turn — REAL end to end, including the ACP
transport (`deos-hermes/src/{lib,bridge,grant_registry,acp_client,agent_peer}.rs`);
the rehydratable membrane — envelope, frustum cut, witness cursor, derived
liveness, mint/rehydrate/drive/stitch trait, typed conflict-objects — with the
executor-backed `ForkMembraneHost` (`deos-matrix/src/membrane.rs`,
`starbridge-v2/src/shared_fork.rs:1017`); the cell/cap/state/executor substrate
(`cell/src/{cell,state,capability}.rs`, `turn/src/executor/execute.rs:210`); the
document language patch core — the `dregg-doc` workspace crate + the rope↔patch
bridge folded into the editor — with the merge-correctness theorem proven in
`metatheory/Dregg2/Deos/DocMerge.lean` (`DOCUMENT-LANGUAGE.md` §4.4); the moldable
inspector `Presentable` spine (`starbridge-v2/src/presentable.rs:345`).

**The honest gap (what is NOT built):** (a) the terminal session cell + exec-cap
(designed here, not yet coded — but every
primitive it needs exists); (b) per-region edit caps + the conflict-resolution
gadget; (c) the cross-app *carry* of the proven Settlement Soundness theorem
(`SettlementSoundness.lean` proves the core; the frustum-of-mixed-apps stitch is
the remaining extension). None of these is a foundational hole — each is a **weld
or a small new core**, which is exactly the thesis: the apps become cells by
connecting machinery that already exists, not by inventing a new substrate.

---

*( ˘▾˘ ) a closing couplet, since four windows turned out to be one graph seen four ways:*

*the buffer, the shell, the room, the tool — no longer four apart;*
*one cell graph wears four faces now, one merge across one heart.*
