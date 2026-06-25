# The firmament & seL4

The firmament is the **cap-gradation bridge**: an seL4 capability and a dregg
capability are treated as one abstraction at different points on a distance
parameter `n`. The whole subsystem lives in the standalone Cargo crate
`sel4/dregg-firmament/` (its own workspace root, path-depending on the real
`dregg-cell`, `dregg-turn`, `dregg-types` so it never reinvents `granted ⊆ held`
— `sel4/dregg-firmament/Cargo.toml:30`, `:92-96`).

This doc describes what is at HEAD. Each load-bearing claim cites a real
`file:line` or `Module.decl`.

## The unified handle

An app holds ONE `Capability { target, rights }` and invokes / attenuates /
delegates it with the same verbs regardless of where the target lives
(`sel4/dregg-firmament/src/lib.rs:341`). `rights` is the REAL dregg rights
lattice — `Rights = AuthRequired` (`lib.rs:232`), re-exported alongside the
genuine `is_attenuation` (`lib.rs:223`).

`Target` names what the cap points at, which fixes the distance and therefore
the backing the router dispatches to (`lib.rs:251`):

- `Target::Local { slot }` — a slot in a CNode (`n = 1`); invocation is a
  syscall (`lib.rs:254`).
- `Target::Distributed { cell }` — a dregg cell on a federation; invocation is a
  turn (`lib.rs:263`).
- `Target::Surface { cell }` — a dregg cell rendered as a window; a window IS a
  capability over a cell, resolved through the same gate and executor as a
  distributed cell (`lib.rs:275`).
- `Target::HostPd { pd }` — a confined forked-child PD reached only over its
  firmament Endpoint (`lib.rs:288`).

`Capability::attenuate` is backing-agnostic and gates on the real
`is_attenuation` (`granted ⊆ held`); a widening returns `None`
(`lib.rs:398-409`). The unit test exercises that local and distributed handles
attenuate through the SAME check and a widening is rejected at both
(`lib.rs:509`).

### Bounds and the `n = 1` collapse

`Bounds` carries the honest distance bounds that held for an op:
`revocation_immediate`, `commit_synchronous`, `n` (`lib.rs:416`). `Bounds::LOCAL`
is the strong `n = 1` set (immediate revoke, synchronous commit, `n = 1` —
`lib.rs:432`). `Bounds::distributed(n)` relaxes both when `n > 1` but collapses
to `LOCAL` at `n ≤ 1` (`lib.rs:440-452`); the test
`n_equals_one_collapse` asserts `Bounds::distributed(1) == Bounds::LOCAL`
(`lib.rs:532`). A `Resolution` returns the `Backing` that resolved an
invocation plus the `Bounds` that held, so a test can prove one handle resolved
local AND distributed differing only in bounds (`lib.rs:461`).

### The Lean ground

The handle, bounds, and collapse are mirrored in `Dregg2.Firmament.CapGradation`:
`Capability` (`CapGradation.Capability`), `attenuate`
(`CapGradation.Capability.attenuate`), and theorems `attenuate_decision_backing_agnostic`,
`attenuate_preserves_target`, `attenuate_iff_grantOk`, `no_amplification`,
`no_amplification_surface`, `distributed_collapses_at_one`,
`bounds_relax_above_one`, `verbs_independent_of_n`,
`surface_same_verb_different_bounds`, `surface_backing_eq_distributed`
(`metatheory/Dregg2/Firmament/CapGradation.lean:289-484`).

## The router

`FirmamentRouter` owns all four backings (`local`, `distributed`, `surface`,
`host`) plus an optional `holder_cell`, and dispatches on `Target` alone
(`src/router.rs:65`, `:124`). `resolve` routes Local→kernel, Distributed→executor
turn, Surface→same surface fabric as distributed, HostPd→firmament Endpoint
(`router.rs:124-149`). `attenuate_and_grant` first runs the backing-agnostic
`Capability::attenuate` pre-check, then ENFORCES the narrowing again at the
backing — `seL4_CNode_Mint` reduced-rights locally, the real `recKDelegateAtten`
turn distributedly (defense in depth) (`router.rs:151-237`). `backing_of` reports
which backing would resolve a handle for assertions only — the app cannot branch
on it (`router.rs:245`).

### The local backing

`LocalBacking` is a CNode slot table standing in for the seL4 cap space:
`install` an original cap (`src/local.rs:70`), `invoke` models `seL4_Call` and
checks the requested rights against held via `is_attenuation` (`local.rs:92`),
`mint` is `seL4_CNode_Mint` with reduced rights gated on `is_attenuation`
(`local.rs:119`), revoke is synchronous and transitive. On a real PD these become
the actual syscalls; the rights lattice is the genuine `AuthRequired`
(`local.rs:1-25`).

### The distributed backing

`DistributedBacking` holds a REAL `dregg_cell::Ledger` and
`dregg_turn::TurnExecutor` — not a mock (`src/distributed.rs:40`, `:49`).
`delegate` runs a genuine `Effect::GrantCapability` turn through
`TurnExecutor::execute`, so `granted ⊆ held` is enforced by the real executor's
attenuation gate and a widening grant is rejected with `DelegationDenied`
(`distributed.rs:14-25`). `n` is the federation's distance, default `1`
(`distributed.rs:44`, `:49`).

## The semihost: `EmulatedKernel`

`EmulatedKernel` is the semihost firmament's `n = 1` microkernel
(`src/emulated_kernel.rs:290`). It PROMOTES `LocalBacking`'s CNode slot table
(reused as `KernelState::cnode`, `emulated_kernel.rs:264`) and ADDS the three
seL4 IPC primitives, all under one `Mutex` + `Condvar` so the `n = 1` bounds are
genuinely real (`emulated_kernel.rs:256-295`):

- **Synchronous Endpoint** — a rendezvous: `call` parks a message and blocks
  until the receiver parks a generation-matched reply; `recv`/`reply` are the
  server half; there is no buffering (`emulated_kernel.rs:116-136`, `:589`,
  `:634`, `:657`). The cross-thread rendezvous round-trips in
  `endpoint_call_recv_reply_rendezvous_cross_thread` (`emulated_kernel.rs:962`).
  `call_served_by` collapses the rendezvous to an inline same-thread call for
  simple boot tests (`emulated_kernel.rs:680`).
- **Notification** — a badge-OR accumulator: `signal` ORs a badge and wakes
  waiters; `wait` blocks until non-zero then read-and-clears (seL4_Wait reset
  semantics) (`emulated_kernel.rs:146-150`, `:486`, `:534`). `poll_notification`
  is the non-blocking read-and-clear for single-threaded dispatch
  (`emulated_kernel.rs:556`).
- **Untyped + Retype** — a byte budget that mints EXACTLY the declared
  `ObjectType` (`emulated_kernel.rs:393`, `:419`). The kernel enforces both type
  (`RetypeError::WrongType`) and budget (`RetypeError::Exhausted`); the
  slot-caveat as a kernel invariant — a CNode factory cannot mint a Frame
  (`emulated_kernel.rs:419-463`, tests `retype_mints_only_the_declared_type`
  `:984` and `retype_exhausts_the_untyped_budget` `:996`).

`bounds()` returns `Bounds::LOCAL` and these are genuine: a revoke under the held
lock has no in-flight window, a present is one map (`emulated_kernel.rs:382`,
test `bounds_local_is_genuinely_real_synchronous_revoke` `:800`).

### NotifyCap — the held, attenuable signal authority

`NotifyCap { target, rights, badge_mask }` makes async-signal a thing you hold
(`emulated_kernel.rs:166`). `signal_admissible` permits a signal iff the cap
targets THIS notification AND `badge & !badge_mask == 0` (`emulated_kernel.rs:187`).
`attenuate` narrows both rights (via `is_narrower_or_equal`) and mask (via
bit-subset), refusing a widening on either axis (`emulated_kernel.rs:200`).
`signal_gated` is the cap-gated wake: admissible ⇒ OR the masked badge, else
`IpcError::NotPermitted` fail-closed (`emulated_kernel.rs:514-527`). The
both-polarity teeth and non-amplification are tested in
`signal_gated_commits_within_mask_refuses_outside_mask` (`:879`) and
`attenuated_notify_cap_admits_only_a_subset` (`:912`).

This Rust mirrors the verified `Dregg2.Firmament.NotifyAuthority`:
`NotifyCap.signalAdmissible`, `NotifyCap.attenuateNotify`,
`NotifyCap.signalGated`, with theorems `attenuateNotify_narrows`,
`attenuateNotify_refuses_mask_widening`, `attenuateNotify_refuses_rights_widening`,
`signalAdmissible_attenuate_no_amplify`, `signalGated_commits_of_admissible`,
`signalGated_refuses_of_inadmissible` (`metatheory/Dregg2/Firmament/NotifyAuthority.lean:182-299`),
and the authority-confinement theorems `notificationCap_confers_at_most_notify_read`,
`notificationCap_never_grant`, `notificationCap_never_call`,
`notificationCap_never_reply` (`NotifyAuthority.lean:331-372`).

### The honest v0 non-fidelity

`EmulatedKernel::ISOLATION_FIDELITY` states the one deliberate gap plainly: at v0
host threads share one address space, so "no ambient authority" is
by-construction-in-the-API, NOT MMU-enforced — a malicious thread could read
another PD's memory or forge a cap by writing raw bytes
(`emulated_kernel.rs:308-317`). It is labeled, not laundered, and CLOSED by the
v1 process backing.

## The microkit facade

`microkit_facade` is the std-backed half of the `sel4-microkit`-shaped API the
dregg PDs code against, so one PD source runs on the semihost and on real seL4
(`src/microkit_facade.rs:1-39`). It mirrors the real crate name-for-name:
`MessageInfo` (`microkit_facade.rs:56`), `ChannelSet` (badge→channels,
`:89`), `Channel` with `notify`/`pp_call`/`irq_ack` (`:159`, `:187`, `:199`,
`:219`), `Handler` with `notified`/`protected`/`fault` (`:227`), `EventLoop`
(`:266`), `ProtectionDomain::spawn` (a PD as a host thread, `:313`), and `Region`
+ the `memory_region_symbol!` macro for shared memory (`:363`, `:408`). A
`Channel` carries the kernel handle + a `ChannelTable` so an index resolves to a
kernel object; on real seL4 the index alone suffices and the kernel handle is the
facade's only shape difference, hidden from PD code (`:158-163`).

## The PDs

### executor-PD — the heart

`ExecutorPd<R: TurnRunner>` is the Endpoint server for staged turns: it SOLELY
holds `turn_in` (R) and `commit_out` (RW), holds NO device cap, and runs every
turn through its `TurnRunner` (`src/executor_pd.rs:153-173`). The contract: an
app stages length-prefixed turn bytes into `turn_in`
(`stage_turn_into`, `executor_pd.rs:436`), signals the executor, which reads,
runs `run_turn_bytes`, writes the receipt (commit) or reason (reject) into
`commit_out`, and replies a verdict tag (`step_staged_turn` `:332`,
`serve_turn` `:371`). A rejected/malformed/over-large/unknown-verb turn advances
no state — fail-closed (`executor_pd.rs:332-360`, `:411`, `read_len_prefixed`
`:455`). Labels: `LABEL_RUN_TURN=1`, `LABEL_TURN_COMMITTED=2`,
`LABEL_TURN_REJECTED=3` (`executor_pd.rs:68-79`).

`TurnRunner` is the verified semantics behind the Endpoint; the wire carries only
bytes and the runner gives them meaning (`executor_pd.rs:91-101`). On the
semihost the runner is the cockpit's real `dregg_sdk::embed::DreggEngine` (a
`TurnExecutor` over a `Ledger`); the real seL4 runner is `execFullForestG` via
`dregg-lean-ffi`, same bytes-in/receipt-out contract (`executor_pd.rs:82-90`).
`FIDELITY` records what runs now vs. WALL step 4 (the Lean ELF runtime port,
blocked on real seL4, not here) (`executor_pd.rs:184-194`). The boot test
`app_pd_stages_turn_executor_pd_commits_receipt_round_trips`
(`tests/executor_pd_boot.rs:105`) drives the full path.

### compositor-PD — the framebuffer/input multiplexer

`CompositorPd` SOLELY holds the framebuffer region, models its scene as a dregg
cell (an ordered list of `Surface`s), and enforces the verified scene as the gate
on every `present()` (`src/compositor_pd.rs:469-486`). It is the ONLY new TCB —
no app logic, no widget toolkit, no placement policy (`compositor_pd.rs:1-11`,
`:534`). A `Surface` is `(owner, regions, content_digest, source_state_root,
z_layer, focus_flag)` (`compositor_pd.rs:110`).

The three scene-authority teeth (`Scene::scene_admit` folds them,
`compositor_pd.rs:313`):

- **T1 non-overlap** — a present targets only the presenter's owned regions
  (`granted ⊆ held`) and disjoint from every foreign surface; else
  `Refusal::Overpaint` (`t1_non_overlap` `:227`).
- **T2 label-binding** — the declared label must equal
  `label_of(presenter, source_state_root)`, a function the compositor computes
  from the authority lineage, never the app; else `Refusal::LabelSpoof`
  (`label_of` `:85`, `t2_label_bound` `:270`).
- **T3 focus-exclusivity** — at most one focused surface; input routes only to
  the focus holder; else `Refusal::DoubleFocus` / `Refusal::InputMisroute`
  (`t3_focus_exclusive` `:282`, `t3_input_routed` `:303`, `route_input` `:679`).

`present` runs the gate first, then composites only the authorized regions into
the framebuffer and logs a `FrameCommit` — a refusal writes no pixel and logs
nothing (`compositor_pd.rs:568-610`). `serve_present` is the Endpoint server form
(`:621`). The teeth mirror the Lean `Dregg2.Apps.Compositor` AppSpec and the
`*_rejected` theorems (`compositor_pd.rs:50-59`, `:174-176`). `FIDELITY` states
the framebuffer is a host buffer and the compositor enforces scene AUTHORITY, not
scanned-out pixels; F1/F2/F3 (frame attestation, IOMMU/DMA confinement, verified
GPU) are the named hardware-trust frontier, not solved here
(`compositor_pd.rs:494-505`).

### Live repaint on turn

The `repaint` module wires the executor-PD → compositor-PD loop: a committed turn
PROJECTS a `DirtyRegion` (owner cell, new source-state-root, new content-digest)
into a shared `repaint_out` region and notifies the compositor, which reads it,
builds a scene-gated `Present`, and advances the framebuffer; a rejected turn
projects and notifies NOTHING (`src/repaint.rs:103-130`, `:153-179`).
`project_dirty_from_turn` returns `None` for a rejected turn (`repaint.rs:167`).
The projected `Present` declares the genuine owner label and does NOT claim focus
— a content advance, not an input assertion — and the compositor still gates it
(`DirtyRegion::to_present` `:141`). `encode_dirty`/`decode_dirty` are the
hand-rolled wire (`repaint.rs:226`, `:238`). `REPAINT_FIDELITY` records that the
authority path is real on the semihost (the framebuffer differs at exactly the
dirty region; a rejected turn leaves it byte-identical) while the pixels' last hop
to a panel is the same graphics frontier the compositor names
(`repaint.rs:89-101`). The end-to-end proof is
`tests/live_repaint_on_turn.rs` — two framebuffer snapshots straddling the turn
(`live_repaint_on_turn.rs:19-31`).

## The v1 process-backed substrate (`process-pd`)

`ProcessKernel` (Unix, `--features process-pd`) closes the v0 isolation gap by
making PDs forked PROCESSES so the host MMU enforces address-space separation
(`src/process_kernel.rs:1-46`, gated `lib.rs:160`). Three load-bearing pieces:
process-backed PDs (`spawn_pd` — own page tables), `shm_open`/`mmap` shared
regions granted by randomized name, and an epoch-tagged cap-handle
`ValidityTable` that refuses a cap forged from raw bytes with `CapError::Forged`
(the cross-process CNode-unforgeability analogue) (`process_kernel.rs:18-46`). The
PD source is unchanged across v0/v1; only the backing moves thread→process
(`lib.rs:81-85`). `ProcessKernel::ISOLATION_FIDELITY` states what is now
MMU-enforced (`process_kernel.rs:50-55`).

`HostPdBacking` is the registry resolving a `Target::HostPd` cap by a validated
round-trip over a confined child's existing control socket; without `process-pd`
it is an empty registry so the router still compiles in every feature combination
(`src/host_pd.rs:1-29`). A migrated surface re-homes its present/input round-trips
onto the child's firmament Endpoint via `SurfaceEvent`/`SurfaceFrame`
(`host_pd.rs:37-70`).

### Sandbox confinement (`process-pd-sandbox`)

`process-pd-sandbox` (implies `process-pd`) adds OS-sandboxed confinement: a
forked child, right after `fork()` and before its body runs, closes every
non-granted fd and drops ambient OS authority — macOS Seatbelt `(deny default)`,
Linux `unshare` namespaces + `NO_NEW_PRIVS` + default-deny seccomp-bpf +
Landlock — so its only channel is the firmament Endpoint (`Cargo.toml:80-90`,
module gated `lib.rs:170`, `confine_child`/`Confinement` exported `lib.rs:217`).

## The recovery monitor

`RecoveryMonitor` is an external watcher that reads the LIVE ARTIFACT
(`Subsystem::probe`), never a self-reported "OK" (`src/recovery_monitor.rs:1-39`).
When a subsystem (or recovery action) CLAIMS healthy but the probe witnesses
wedged, it emits `Divergence::RecoveryNotHolding` and escalates rather than
looping forever (`recovery_monitor.rs:42-60`). A restart is `Verdict::Recovered`
only if a FRESH post-restart probe witnesses health — fail-closed
(`recovery_monitor.rs:56-60`). It is recursive (a `MonitorSubsystem` is itself a
`Subsystem`) and the real live-Endpoint adapter `HostPdSubsystem` is gated on
`process-pd` (`lib.rs:193-198`).
