# The semihost cockpit — starbridge-v2 on the sel4 PD world

> starbridge-v2 is the native dregg master interface. Its backend is **the
> semihosted seL4 protection-domain world**: the verified executor runs as the
> **executor-PD** over the firmament's `EmulatedKernel` (the n=1 microkernel),
> the compositor-PD owns the framebuffer, the persist-PD holds the durable store
> — the SAME protection-domain sources a real seL4 boot would run, launched as
> in-process servers under `cargo test` / the native binary. The gpui frontend is
> an app-PD's client. The n=1 collapse makes this the same code path as a real
> seL4 boot, only the launch mechanism (an in-process server vs. a kernel-scheduled
> PD) differing.

This document teaches the architecture as it stands: what runs, how a turn
reaches the heart through the cap partition, and — held to the same honesty the
firmament's fidelity labels carry — exactly where the line between *runnable now*
and *designed* falls.

---

## 1. The shape: three PDs and a frontend, on one n=1 microkernel

The desktop-OS layering (`docs/DREGG-DESKTOP-OS.md §2`) names the organs. On the
semihost they are concrete Rust over one shared `EmulatedKernel`
(`sel4/dregg-firmament/src/emulated_kernel.rs`):

```
┌───────────────────────────────────────────────────────────────────────┐
│  gpui frontend (native window)          — an APP-PD's client            │
│    renders the shell's composed scene; issues turns                     │
├───────────────────────────────────────────────────────────────────────┤
│  L6  SHELL + WINDOW-MANAGER (starbridge-v2: shell.rs, surface.rs)        │
│       a window IS a firmament Surface cap (granted ⊆ held)               │
├───────────────────────────────────────────────────────────────────────┤
│  L5  COMPOSITOR-PD (compositor_pd.rs)   — SOLE framebuffer holder        │
│       enforces the verified scene (T1 non-overlap / T2 label / T3 focus) │
├───────────────────────────────────────────────────────────────────────┤
│  L3  EXECUTOR-PD (executor_pd.rs)       — THE HEART                      │
│       runs every turn through the verified World; turn_in→step→commit_out│
│  L4  PERSIST-PD (persist-stub)          — the durable store (seat)       │
├───────────────────────────────────────────────────────────────────────┤
│  EmulatedKernel — the n=1 microkernel                                    │
│    Endpoint (sync Call/Recv/Reply) · Notification (badge-OR) ·           │
│    Untyped+Retype · shared regions · CNode mint/revoke (is_attenuation)  │
└───────────────────────────────────────────────────────────────────────┘
```

Every organ shares ONE `EmulatedKernel`: a `notify`/`pp_call` in one PD reaches
the SAME endpoint/notification object in another — the faithful seL4 property
that two PDs invoke the same kernel object. The kernel advertises
`Bounds::LOCAL`, and these are *genuinely real* on the host: a host thread's
revoke is synchronous (one `Mutex`-guarded removal under the held lock — no
in-flight window), a host present is one map. The cap checks are the genuine
dregg `is_attenuation` (`granted ⊆ held`). It is a faithful `n = 1` firmament,
not a lossy mock (`docs/DREGG-DESKTOP-OS.md §3`, the fidelity discipline).

---

## 2. The executor-PD: the heart, over the n=1 microkernel

`docs/FIRMAMENT.md §2` fixes the executor-PD as **L3, the heart** — "*every*
authority decision, *every* cap mint/revoke, *every* state transition flows
through it." Its cap partition is exact: `turn_in` (R, the de-enveloped
signature-checked turn), `commit_out` (RW, the commit-log/receipt entry persist
durably stores), and a notification edge to/from each app-PD. It holds **no
device cap, no NIC cap** — it is pure compute over bytes, and the verified
semantics is the only authority over state transitions.

`sel4/dregg-firmament/src/executor_pd.rs` is that seat, running on the semihost.
`ExecutorPd<R>` is the Endpoint SERVER for staged turns; `R: TurnRunner` is the
verified semantics behind the Endpoint. The wire is the executor-PD's exact
`turn_in → step → commit_out` contract:

1. **stage** — an app-PD writes the length-prefixed turn bytes (postcard `Turn`,
   as the wire carries a turn; `turn/src/turn.rs` "transmitted via postcard")
   into the `turn_in` region (`ExecutorPd::stage_turn`);
2. **signal** — the app-PD `pp_call`s the executor's PP channel
   (`Channel::pp_call` → kernel `Call`), the `ingress→executor` edge the real
   `executor-stub` PD awaits on channel 1;
3. **step** — the executor `recv`s, reads `turn_in`, runs the bytes through `R`
   (`ExecutorPd::step_staged_turn`), writes the `TurnReceipt` (on commit) or the
   rejection reason (on reject) into `commit_out`, and `reply`s a verdict tag;
4. **read back** — the app-PD reads the receipt out of `commit_out`
   (`ExecutorPd::commit_out_read`).

The app-PD never touches the ledger — it hands BYTES to the heart and reads BYTES
back. A turn the runner rejects writes only the reason to `commit_out` and
advances no state (fail-closed — the Rust analogue of the Lean executor returning
`Rejected`).

`TurnRunner` decouples the PD seat from the `dregg-turn`/`dregg-sdk` turn types:
the wire is bytes, and only the runner gives them meaning. The real seL4
executor-PD's runner is `execFullForestG` via `dregg-lean-ffi`; the contract —
"turn bytes in, receipt-or-reason bytes out, fail-closed" — is identical.

### The cockpit's runner is the real verified World

On the semihost, `R` is `starbridge_v2::world::WorldRunner` — it OWNS the
cockpit's real `World` (the embedded `dregg_sdk::embed::DreggEngine`: the verified
`TurnExecutor` over a `dregg_cell::Ledger`, plus the provenance log, the dynamics
stream, the replayable history). On a staged turn it decodes the postcard `Turn`
and runs it through the FULL real `World::commit_turn` path — chain-head
threading, history recording, dynamics emission, receipt append. **Not a bypass:
the semihost path runs the IDENTICAL `World` logic, just reached through the PD
wire.** `SemihostCockpit::commit_turn_via_semihost` is the cockpit's app-PD side:
encode → stage → drive the executor-PD body → read the receipt back out of
`commit_out` → decode. The receipt genuinely round-trips through the RW region.

This is the keystone payoff `docs/DREGG-DESKTOP-OS.md §3` states plainly: **"the
verified executor-PD hosts on the host's ordinary macOS/Linux Lean runtime ... so
the semihost has a REAL verified heart NOW"** — the executor-PD blocker that gates
real-seL4 (the Lean ELF runtime port, WALL step 4) does **not** gate the emulator.

---

## 3. The n=1 collapse: the same code path as a real seL4 boot

The firmament's central claim (`docs/FIRMAMENT.md §3`) is that an seL4 capability
and a dregg capability are the same abstraction at different points on a *distance
parameter* `n` (the number of machines a resource is spread across). On the
firmament `n = 1` (everything on one box), so the distributed bounds collapse to
strong-local: revocation is immediate, commit is synchronous, checkpoint is
consistent.

The semihost realizes `n = 1` faithfully. The executor-PD over the
`EmulatedKernel` is the SAME `turn_in → step → commit_out` partition the real
seL4 executor-PD (`sel4/dregg-pd/executor-stub`, `sel4/dregg-pd/executor-pd`)
maps and awaits — that PD reads `turn_in`, writes `commit_out`, and waits on the
`ingress→executor` channel, and it idles its verified-turn path ONLY because the
Lean ELF runtime is not yet linked on bare-metal aarch64. The semihost executor-PD
**runs** that path, because off-seL4 the verified semantics is an ordinary host
runtime. The cap partition, the wire framing, the fail-closed rejection, the
`Bounds::LOCAL` collapse — all identical. Only the launch mechanism differs: an
in-process server / host thread here, a kernel-scheduled PD there.

This is why the cockpit is "always on the verified sel4 substrate even on a Mac":
the turn does not take a different path because it is on a Mac; it takes the
firmament's `turn_in → step → commit_out` path through the n=1 microkernel, which
is the path a real seL4 boot takes with the bounds unchanged.

---

## 4. The compositor-PD: the framebuffer, behind the gate

`sel4/dregg-firmament/src/compositor_pd.rs` is the L5 multiplexer — the SOLE
holder of the framebuffer region (an `EmulatedKernel` shm region no app-PD is
granted), modelling its scene as a dregg cell, enforcing the verified scene
(T1 non-overlap / T2 label-binding / T3 focus-exclusivity — the anti-ghost teeth
proven in the Lean `Dregg2.Apps.Compositor` AppSpec) as the gate on every
`present()` an app-PD submits over an Endpoint. An app composites ONLY its
cap-authorized region; an overpaint of another surface's region is REFUSED at the
framebuffer (no-amplification at the glass). This runs end-to-end today
(`tests/compositor_pd_boot.rs`: two app-PDs composite, the overpaint is refused,
input routes to the focused one).

The shell (starbridge-v2 `shell.rs`, `surface.rs`) treats a window as a firmament
Surface cap: holding/attenuating/delegating/revoking a window is exactly
holding/attenuating/delegating/revoking that cap, through the SAME `granted ⊆ held`
gate and the SAME real `TurnExecutor` as every other dregg cap. The window
authority rides the firmament fabric the local and distributed backings already
proved — no parallel bearer-secret model (`docs/DREGG-DESKTOP-OS.md §7`).

### The wgpu software-render path (the eventual in-sel4 render)

The compositor-PD enforces scene AUTHORITY, not scanned-out pixels. On the
semihost the framebuffer is a host in-memory buffer; the pixels an app produces
are the renderer's. The eventual in-sel4 render path is a **software wgpu adapter
(lavapipe / the software rasterizer) targeting the compositor-PD's framebuffer
region**: an app-PD renders its surface with wgpu against a software adapter
(no GPU device cap needed), and the resulting pixels become the `contentDigest`
the app `present()`s to the compositor-PD, which composites the authorized region
into the framebuffer it solely holds. Binding the scanned-out framebuffer to the
cell's `contentDigest` (F1 last-hop frame attestation), IOMMU/DMA confinement of a
malicious display PD (F2), and a verified GPU/servo compositor (F3) are the named
hardware-trust frontier (`docs/DREGG-DESKTOP-OS.md §5`, R3 Stage C) — severe
problems with closure lanes, never walls, not solved here. The compositor mediates
AUTHORITY over the scene (verified); the pixels it produces are the renderer's.

---

## 5. Honest design-vs-built ledger

The discipline (`docs/DREGG-DESKTOP-OS.md`, the fidelity labels): every claim
arrives with its boundary. Here is the line.

| Piece | State |
|---|---|
| `EmulatedKernel` — Endpoint / Notification / Untyped+Retype / regions / CNode mint+revoke, genuinely-`n=1` | **RUNS** (`emulated_kernel.rs`, green) |
| 2-PD notify slice + m0-hello boot (`init()`+`notified()` over the kernel) | **RUNS** (`tests/boot_pds.rs`, green) |
| Compositor-PD: two app-PDs composite, overpaint refused, input routed | **RUNS** (`tests/compositor_pd_boot.rs`, green) |
| **Executor-PD: `turn_in → step → commit_out` over the Endpoint** (`executor_pd.rs`) | **RUNS** (`tests/executor_pd_boot.rs`, green) |
| **Cockpit turn through the semihost executor-PD** (`SemihostCockpit::commit_turn_via_semihost`) hosting the real `World` | **RUNS** (`world.rs` tests: commits, rejects fail-closed, byte-for-byte equal to the direct path) |
| Surface caps / window authority on the firmament fabric (shell, surface.rs) | **RUNS** (gpui-free, `cargo test`-able) |
| v1 process-backed PDs (MMU-enforced isolation, `shm_open`/`mmap`, cap validity table) | **RUNS, opt-in** (`--features process-pd`, `process_kernel.rs`, `tests/process_isolation.rs`) |
| The gpui frontend dispatching its turns through `SemihostCockpit` instead of `World` directly | **DESIGNED** — the cockpit's many panels still call `World::commit_turn` in-process; the semihost path is wired + proven equivalent, but the frontend has not been cut over to route through it. The cutover is mechanical (swap the commit call) once the multi-PD frontend wiring is laid. |
| The wgpu software-render path → compositor-PD framebuffer (in-sel4 render) | **DESIGNED** (§4) — the authority gate runs; the pixel pipeline is the named graphics frontier |
| Real seL4 executor-PD (the Lean ELF runtime on bare-metal aarch64) | **DESIGNED / blocked at WALL step 4** — the verified semantics is an ordinary host runtime off-seL4 (so the semihost runs it); the bare-metal port is the queued milestone (`docs/FIRMAMENT.md §6`, `sel4/dregg-pd/executor-pd/WALL.md`). The MMU-block premise was refuted and the embeddable runtime measured (`docs/EMBEDDABLE-LEAN-RUNTIME.md`). |
| persist-PD durable store (redb-over-block-cap) | **SEAT** — `persist-stub` holds the L4 seat + maps `commit_in`; the snapshot model lands in `persist/src/snapshot.rs`; the PD is a quarter milestone |

The one-line verdict: **the executor-PD world runs underneath a cockpit turn
today** — staged, signalled, stepped, and read back through the n=1 microkernel's
cap partition, yielding the byte-identical verified receipt the direct path does.
What remains is the *frontend cutover* (route the cockpit's panels' commits
through `SemihostCockpit` rather than `World` directly) and the *real-seL4 boot*
(the bare-metal Lean runtime), neither of which changes the path a turn takes —
they change only what launches the PD.

---

## 6. The path to a fully-semihosted cockpit

1. **Frontend cutover (mechanical).** The cockpit (`src/cockpit.rs`, `main.rs`)
   constructs a `World` and calls `commit_turn` directly across its panels. Hold
   a `SemihostCockpit` instead and route the panels' commits through
   `commit_turn_via_semihost`. The equivalence test
   (`semihost_path_matches_the_direct_path_byte_for_byte`) is the safety net: the
   receipt and the image root are identical, so the cutover is behaviour-preserving.
2. **Multi-PD frontend (the app-PD boundary).** Run the gpui frontend as an
   app-PD client of the executor-PD + compositor-PD over the `EmulatedKernel`
   Endpoints (the cross-PD `serve_turn` / `serve_present` path on their own
   threads), rather than the inline single-thread drive — the faithful PD
   scheduling shape `tests/executor_pd_boot.rs` and `tests/compositor_pd_boot.rs`
   already exercise.
3. **The wgpu software-render path (§4).** Render surfaces with a software wgpu
   adapter and `present()` the pixels to the compositor-PD's framebuffer.
4. **v1 process backing across the board** (`--features process-pd`) — MMU-enforced
   isolation for every PD, closing the v0 single-address-space label.
5. **Real seL4 boot** — the bare-metal Lean runtime (WALL step 4) makes the SAME
   PD sources run as kernel-scheduled PDs, with the bounds unchanged at `n = 1`.

*The cockpit is the firmament made interactive. We do not run a different backend
on a Mac; we run the n=1 seL4 PD world — the executor-PD heart, the compositor-PD
glass — as in-process servers over the EmulatedKernel, the same `turn_in → step →
commit_out` and `present → gate → composite` paths a real seL4 boot takes, with
only the launch mechanism differing and the frontier (the Lean ELF runtime, the
graphics crypto-floor) labelled as severe-problems-with-closure-lanes, never
walls.*
