## debugger
The **debugger** is a faithful step-through for a single dregg turn. It never mutates the live world: it clones the ledger, stands up a fresh executor, and for each effect *prefix* (effects `0..k`) it builds a real prefix-turn, runs it through the real `TurnExecutor`, and snapshots the post-state — balance, nonce, and capabilities on every touched cell, plus the running conservation delta `Σδ`. The entry point is `debug_turn(world, turn)` (`debug.rs:456`), returning a `TurnTrace` of `Step`s.

What it shows is one row per effect in depth-first order: the effect label (e.g. `transfer 100 · a→b`), the `Σδ` at that step, and whether the executor accepted that prefix. When the turn refuses, the prize is the `RefusalExplanation` (`debug.rs:174`): the guard family (`GuardKind` — Conservation, Capability, Authorization, Precondition, History, Structural, Proof, Other), the offending effect index, the cells involved, and a plain headline + detail.

A user reads the panel top-to-bottom as a verdict trail: pre-state, then each effect's effect on touched cells, then either the commit line or "you over-spent on cell X (conservation guard, effect 2)." It maps to the protocol exactly because the turn is a `CallForest` the executor applies depth-first and commits or rolls back atomically; the debugger mirrors that by re-running real prefixes. The cockpit render is `debugger_panel()` (`cockpit.rs:5560`).

## replay
**Replay** is verified time-travel over committed history. The `History` recorder (`replay.rs:120`) holds the ordered `RecordedStep`s (either a genesis install or a committed turn) plus the canonical ledger root *tooth* after each step. Every scrub re-derives state by replaying the recorded turns from genesis through a fresh executor, and verifies the reconstructed root matches the recorded tooth — fail-closed on mismatch. The core method is `History::replay_to(k)` (`replay.rs:247`).

The panel shows a timeline scrubber (step 0 = empty pre-genesis root through step N = head), each entry clickable and labeled with its root tooth; at the cursor it shows the verified reconstruction and a verification badge; below that, `History::diff(i,j)` shows what the cursor's turn did. An optional what-if fork via `History::fork_at(k, alt)` branches at step `k` with a different turn and shows the divergence.

It maps to the protocol because `History` records the same input `Turn` objects the executor processes (not the pre/post commitments) — replay means feeding them through the real executor again, so a replayed turn commits identically. The root tooth is the deterministic, order-independent `Ledger::root` a verifier checks as the true state commitment (the anti-substitution tooth). The cockpit render is `replay_panel()` (`cockpit.rs:5623`).

## workspace
The **workspace** is a fork-the-world evaluator — Smalltalk's `doIt`/`printIt`/`inspectIt`/commit loop, dregg-native. You compose a turn as an `IntentDraft`, evaluate it to predict consequences without mutating the live world, print and inspect the predicted post-state as live objects, then commit it for real or discard it. The `Workspace` struct is at `workspace.rs:149`.

`doIt` is `Workspace::evaluate(&world)` (`workspace.rs:199`): it runs `simulate::simulate` on a fork so the live world is read-only, then re-forks to read the predicted post-state. `printIt` is a one-line summary — predicted receipt hash, action count, computrons, image root, cell-count delta, or a truncated refusal. `inspectIt` returns the predicted post-state as the same uniform `Inspectable` rows the OBJECTS tab renders.

A user composes the draft, presses **doIt**, reads the verdict and inspected objects, then **commit** (runs only when the prediction committed, and runs the *identical* turn) or **discard**. It maps to the protocol via the faithfulness guarantee: prediction and commit run the same verified executor over the same `IntentDraft`, so the real receipt matches the predicted one exactly. The cockpit render is `workspace_panel()` (`cockpit.rs:3705`).

## wonder
**Wonder** is the warm front door — the live ledger projected as glowing, pokeable cells a newcomer clicks around with no manual (the 1999-AOL-as-a-four-year-old half of the deos UX, where wonder precedes comprehension). The `WonderRoom` (`wonder.rs:265`) holds every live cell as a `GlowingCell` carrying its real balance, capability count, and a `liveliness ∈ [0,1]` glow, rebuilt fresh every frame via `WonderRoom::build(&world)`.

The glow is real: `liveliness` is derived from the live dynamics stream, counting how many recent events touched the cell, decaying toward zero for older activity. Each cell carries a `Halo` with three real actions — Inspect (project through `reflect::reflect_cell`), Grab (arm a drag), and Explain (a warm plain sentence from the cell's real fields + recent dynamics).

A user clicks a glowing cell to inspect it in the moldable INSPECTOR; the brightest cell explains itself in prose. A drag is a real conserving turn: arm → drop_on → predict (fork-the-world; an over-drag surfaces as `Refused`) → resolve (predicted-first — never commits something the prediction refused), producing a real `TurnReceipt`. The cockpit render is `wonder_panel()` (`cockpit.rs:3797`).

## cipherclerk
**Cipherclerk** is the agent's real cryptographic credential holder — a thin reflective projection of the genuine `dregg_sdk::AgentCipherclerk` wallet, not a mock. It surfaces **identities** (HD-derived signing keys), **held tokens** (real minted macaroons + attenuated narrowings), and **delegations** (signed envelopes addressed to recipients' public keys). The `Identity` struct is at `cipherclerk.rs:56`.

Per identity it shows the 32-byte public key, the world `cell_id` (`blake3(domain) ⊕ pubkey`, the same derivation `Cell::with_balance` uses), the HD derivation path, and the held tokens with their authority flags and decoded caveat chains.

A user drives four verbs over the real clerk: **mint root** (forges a real macaroon), **attenuate** (narrows the latest root, appending real caveats to the HMAC chain), **delegate** (a signed envelope to the recipient's real pubkey), and **discharge/verify** (runs the *real* `AgentCipherclerk::verify_token`: HMAC chain validation + caveat/Datalog evaluation). It maps to the protocol at three welds: the identity's derived `cell_id` is exactly the cell it owns; the attenuated macaroon's appended caveats are evaluated by the real verifier; a delegation is a signed envelope discharged against the deterministically-derived root key. The cockpit render is `cipherclerk_panel()` (`cockpit.rs:5637`).

## editor
The **editor** is the authoring surface where an operator *writes* dregg artifacts (cell programs from guard-algebra atoms, factory descriptors, multi-effect call forests) as typed builders, gets a **static assurance verdict** before paying to submit, and on pass **deploys them through the embedded verified executor**. Three movements — author, validate, deploy — live in `edit.rs`.

Authoring uses typed builders that write protocol types directly: `ProgramBuilder` assembles `CellProgram` constraint atoms; `FactoryBuilder` writes `FactoryDescriptor`s; `ForestBuilder` + `ActionBuilder` write `CallForest`s. Validation (`validate`, `edit.rs:124`) calls the real canonical `dregg_userspace_verify::analyze` and projects its `Assurance` onto the editor's `Verdict` — conservation / no_amplification / wellformed findings. This is the safety rail: a pass is **necessary, not sufficient** — it checks the userspace-decidable shape, not dynamic facts.

A user authors, presses validate to see PASS/FAIL with located findings, then deploys. `deploy_program` genesis-installs a cell carrying the authored program; `deploy_forest` validates first — on static failure it refuses without spending gas, on pass it commits the forest's effects through the embedded executor, which may *still* reject on dynamic grounds. The cockpit render is `editor_panel()` (`cockpit.rs:7382`).

## composer
The **composer** is L2 of the moldable inspector: an interactive gadget for the protocol's `StateConstraint` slot-caveat algebra. It builds a *real* constraint out of genuine atoms, validates it fail-closed (anti-strip / cost / coordination), installs it onto a cell, and fires a turn the verified executor enforces — it never reimplements evaluation, it calls the genuine `CellProgram::evaluate`. Backing: `predicate_composer.rs`.

The palette is `Atom` — ten leaf predicates (`SenderIs`, `SenderMemberOf`, `BalanceGte`/`Lte`, `BalanceDeltaLte`/`Gte`, `FieldEquals`/`Gte`/`Lte`). The author composes a recursive `Composite`: `Leaf`, `AnyOf` (disjunction), or `AnyOfBound` (anti-strip disjunction whose branches name their own proof carriers).

`validate` (`predicate_composer.rs:417`) is fail-closed: it refuses an `AnyOfBound` whose witnessed branch can be stripped to a cheap leg (the anti-strip forge), refuses vacuous empty disjunctions, and flags FREE/BOUNDED coordination mismatches. `install` routes through `World::set_cell_program`; `install_and_fire` emits a real `SetField` turn whose program-check loop refuses a violating value. The Trace face *is* the executor's verdict one turn ahead. Exercised via the SIMULATE surface (`cockpit.rs:2806`).

## simulate
**Simulate** is fork-and-predict: compose any intent (effects over any cells), run it through a deep-copied world carrying the *same* verified executor, and see the predicted post-state, receipt, deltas, or refusal — all without touching the live world. Only on commit does the identical turn run for real. The core type is `IntentDraft` (`simulate.rs:216`); the result is `SimOutcome` (`simulate.rs:324`).

The panel shows the composed turn, and after a simulation: the predicted receipt hash, action count, metered computrons; per-cell before/after balance deltas plus births and retirements; the dynamics events; the predicted image root; or the exact refusal reason and whether it fired statically or dynamically.

A user cycles the agent cell, the target cell, and an effect kind, then **SIMULATE (predict)** runs `simulate()` through the fork; **COMMIT for real** (enabled only after a successful prediction) runs the identical turn on the live world. It maps to the protocol because the fork is `World::fork()` (deep clone of ledger + factory registry + chain heads), both prediction and commit run the same `DreggEngine`, and faithfulness is by identity: the simulated and committed receipt hashes match given the same pre-state and timestamp. The cockpit render is `simulate_panel()` (`cockpit.rs:2830`).

## agent
The **agent** surface is a cap-confined view of a single agent cell's *provable* activity. An agent is an intricate perceive/decide/act loop; dregg grounds the one seam that matters — its actions at the tool-call/turn boundary — by making every action a cap-gated, receipted, conservation-checked turn. The model is `AgentActivity` (`agent.rs:115`).

It shows a header (cell id, backed/unbacked, live balance, committed-turn count, reach, nonce); **the held mandate** as rows of `MandateEdge` (target cell, slot, rights label, faceted?, expiry); **recent cap-gated actions** as `AgentAction` rows (✓ committed or ✗ refused, height, human summary, action count, computrons, receipt hash); and the **authorization boundary** as `Authorization` CAN/CANNOT verbs.

A user reads the mandate to see exactly which cells the agent reaches and at what rights, watches the activity feed, sees refusals shown openly (an attempted over-grant is REFUSED — the executor's guarantee firing, never hidden), and knows the edge of the loop's reach. It maps to the protocol because the mandate is the cell's real c-list, the actions are committed `Turn`s read from `World::receipts()` filtered by agent, and no-ambient-authority/conservation/ocap/lifecycle are all executor-enforced — so the activity is on-ledger truth, never a self-report. The cockpit render is `agent_panel()` (`cockpit.rs:5143`).

## swarm
The **swarm** surface extends single-agent activity to N agents coordinating as confined Surface cells. Members coordinate via an async notify-edge model — one member emits an event (a receipted turn) depositing a pending "wake" in another's inbox; the recipient drains it in its own separate future turn (two independent receipts, two heights — async, not a joint turn). The render model is `SwarmView` (`swarm.rs:1351`).

It shows a swarm-wide header (members, total actions, pending wakes); per-member rows (name, id, balance, inbox with ⚡ pending / ✓ drained entries); an activity feed; and a budget strip (per-member spent/ceiling meter, aggregate headroom, optional shared-pool meter with a verified conservation bound).

A user drives member actions: a coordinator emits a task to a worker (an `EmitEvent` turn; a wake lands if the recipient admits the topic via its `NotifyCap` badge mask), a worker drains its inbox, or a coordinator bundles transfer + wake in one seam. It maps to the protocol because each member is an agent cell with a held mandate, each action is a real turn, the notify edge is a real async chain gated by a real `dregg_firmament::NotifyCap` badge mask, and budgets are floor meters enforced fail-closed. The async model is *visible*: two receipts, two heights, two agents. The cockpit render is `swarm_panel()` (`cockpit.rs:5319`).

## shell
The **shell** is the cap-first window manager over real cells. It owns the `Surface`s, the z-order stack, the focus, and the firmament surface-fabric the window caps are checked against. There is no ambient authority over a window: every op — focus, raise, move, resize, minimize, close, share — is gated by the surface's capability, a real `dregg_firmament::Capability{ Surface(cell) }`. The `Shell` struct is at `shell.rs:190`.

It shows the **verified scene**: an ordered list of windows, each with anti-spoof chrome — an `IdentityLabel` carrying the owning cell's real id + lifecycle badge read fresh from the ledger (never the surface's self-report).

A user drives windows only by presenting the cap the shell minted: focus/raise/move/resize/close (cap-gated), and `share(cap, recipient, narrower_rights)` — a real `Effect::GrantCapability` turn where a *widening* share is rejected by the executor (no-amplification firing at the desktop). Frames go on-screen through `present`, which fires cap-auth then scene-authority gates (region non-overlap, label binding = owner ⊕ state-root, focus-exclusivity). The cockpit render is `shell_panel()` (`cockpit.rs:4912`).

## terminal
The **terminal** is a command surface as a cap-confined Surface cell — and the place the ADOS tool-call seam lives: an agent's `Bash`/command routed through a terminal-cell's capability. There is no bearer secret; the command is gated by real capability membership. The `TerminalCell` struct is at `terminal.rs:212`.

It shows the terminal name, the backing cell id (the command-authority anchor), the **mandate** (the target cells this terminal may reach — itself plus every cap in its c-list), and the append-only output history (the command line, committed/REFUSED, the receipt hash, the computrons, the reason).

A user runs a command via `run(world, cmd)`, where two gates fire in order: first the **command cap-gate** (is the target within the mandate? out-of-mandate returns `OutOfMandate` and appends a REFUSED line before any turn), then the **executor gate** (the authorized command runs as a real verified turn). It maps to the protocol because each typed command lowers to a real `Effect`, the two-gate composition mirrors `shell::present`, and the receipt *is* the output line — it never lies. The cockpit render is `terminal_panel()` (`cockpit.rs:7287`).

## buffer
The **buffer** is a text editor backed by a real cell, with cap-gated writes — a buffer is a cap-confined view of a cell whose state *is* the buffer, so *who may edit it* is an ocap question the verified executor answers. The `BufferCell` struct is at `buffer.rs:225`.

It shows the buffer name, the backing cell id, whether the buffer is READ-ONLY under the held cap (an attenuated surface cap cannot promote itself to write), whether it is CLEAN or DIRTY, the revision (the cell's nonce), and the two digests (visible-doc BLAKE3 vs stored).

A user types freely into the view (in-memory, no ledger touch), then lands it with `commit(world, cap)`, where two gates fire: the **buffer-cap gate** (the cap must name this surface and carry full write authority `AuthRequired::None`; a read-only mirror is refused before any turn), then the **executor gate** (the `SetField` turn runs; the cell's nonce advances). It maps to the protocol because the content digest lives in the cell's state at a fixed slot, so a commit advances the source-state-root like a balance move, and a read-only mirror (obtained by a real `share()` narrowing) cannot write — no-amplification firing at the editor. The cockpit render is `buffer_panel()` (`cockpit.rs:7200`).

## trust
The **trust** panel is the human's view of their own authority — the identity cell as a living card. It projects three faces: **WHO-I-AM** (lifecycle state, current devices/speakers, guardian council + recovery threshold), **KEY-EVENT LOG** (the KERI-shaped rotation history), and **RECOVERY** (the "ask your guardians" quorum gauge plus the cooling-window safety pause). The `TrustPanel` struct is at `trust_panel.rs:196`.

The identity card shows the `IdentityState`, the `Device` speakers, the guardians (name, cell id, weight), the "any K of N guardians" recovery shape, and raw key commitments. The KEL timeline shows each `KeyEvent`. The recovery gauge tracks `RecoveryProgress` with a plain-language headline.

A user inspects the WHO-I-AM card, audits the KEL, and watches the recovery quorum climb, reading the cooling-window countdown. It maps to the protocol because the cell's 16-slot state holds the live key commitment, guardian council commitment, and pre-committed next keys, decoded by the genuine `dregg_sdk::identity::inspect_identity`; `RecoveryProgress::quorum_met()` mirrors exactly the executor's weighted K-of-N `ThresholdSigVerifier` floor (fail-closed below threshold). The cockpit render is `trust_tab()` (`cockpit.rs:3547`).

## docs
The **docs** surface is a cap-gated, patch-theoretic document editor (Pijul-shaped, conflicts-as-states). A document is a real cell; each edit is a genuine turn through the executor leaving a verified receipt; conflicts are first-class states, not errors. Modules: `doc_editor.rs` (the authoring model) and `doc_lens.rs` (the moldable inspection faces).

It shows the substrate identity (doc cell id, editor cell, state commitment, and the seam check `commitment == projection`), a moldable inspection with five faces (RawFields, Rendered prose with inline conflict markers, Patch History, the Conflicts antichain, the Commitment two-regime explanation), the rendered document, and inline conflicts-as-states — each clashing region showing its regime, attributed alternatives (author + receipt hash), and one-click resolution buttons.

A user appends text or commits a draft delta; demonstrates the cap gate with `attempt_unauthorized` (returning `CapabilityNotHeld` in-band); sows honest conflicts (both alternatives commit as real turns into an unordered antichain); and resolves them with a later real cap-gated turn. It maps to the protocol because a document *is* a cell, an edit *is* a cap-gated turn through the real executor, the content *is* the fold of the patch history, and the seam is closed — the folded content's commitment equals the cell-state commitment a light client would verify. The cockpit render is `docs_panel()` (`cockpit.rs:8643`).

## time
The **time** surface is the headline livability panel of deos — time-travel + suspend + fractal meta-debug, as one control panel. It reuses the real models with no parallel cache. The model is `TimeCockpitModel` (`time_travel.rs:74`), built purely (never mutating the world).

It shows three stacked powers: a **liveness badge** (an honest trichotomy — LIVE at head, REPLAYED-DETERMINISTIC in the past, APPROXIMATE if the log doesn't reach) plus the **rewind scrubber** of `ScrubTick`s (each flagged with its per-step reversibility verdict: ⊘ a committed boundary a spend/burn/revoke can't un-turn, • a reversible step, · genesis); a **suspend gate** (the M5 freeze banner + the staged continuation of queued turns); and a **metastack navigator** (the fractal debug-the-debugger tower).

A user clicks a tick to scrub there (root-verified replay), clicks SUSPEND/RESUME, and climbs/descends the metastack to debug the debugger. The reversibility badges teach where the un-turn frontier is — you can rewind to a committed spend, not past it. It maps to the protocol because the scrubber uses `History::replay_to`, the reversibility classification calls `Turn::is_reversible(&pre_state)`, the suspend gate reads `World::is_suspended()`, and the metastack is the lazily-materialized `meta_debug::MetaStack`. The cockpit render is `time_panel()` (`cockpit.rs:8180`).

## share
The **share** surface is a revocable-right-to-review membrane — not a session leak but a sound capability system for sharing attenuated views. "Sharing a screenshot" becomes "extending a revocable, attenuated, audited right to re-view a witnessed slice." The backing model is `SnapshotEditor` (`snapshot_editor.rs:180`).

It shows four sculpting sections plus an audit trail: the captured snapshot header; **Cull the frustum** (lens/sub-object/affordance toggles — both start FULL, toggling only narrows); **Pare the authority** (rights tiers from the real `is_attenuation` lattice, a widening colored as a warning); **Verify** (is the pared role ⊆ held? plus the genuine membrane-projected preview of what each recipient rehydrates); and **Share** (mint the artifact, greyed if not sound).

A user captures the focused view, culls lenses and affordances (narrowing only), pares the dial to a rights tier (an amplification refused in-band), verifies, and shares (the no-amplification gate is in-band; an over-wide pare returns `WouldAmplify`). It maps to the protocol because the snapshot is the live inspector's own paused witness-cursor camera, the dial rides the proven `Capability::attenuate` + `is_attenuation`, and the recipient preview is *not* narrated — it is the real per-viewer projection, so two recipients with different caps rehydrate different affordances from the same artifact. The cockpit render is `share_panel()` (`cockpit.rs:4102`).
