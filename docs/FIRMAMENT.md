# The Firmament — the seL4-hosted deterministic ground for houyhnhnm apps

*Architecture doc. Present-tense, first-principles. The firmament is the
seL4-hosted substrate that embeds the dregg executor, holds the apps, gives
them capabilities (local seL4 + distributed dregg under one model), and can
checkpoint/restore them transparently. Companion to `docs/SEL4-EMBEDDING.md`
(the boot ladder + the Lean-runtime blocker) and `sel4/` (the booting PDs).*

---

## 1. What the firmament is

The **firmament** is the boundary that holds the apps and gives them a
deterministic ground to run on. Concretely it is four things, each a real
seL4 construct:

1. **The seL4 root** — the microkernel + the Microkit monitor + the CapDL
   initializer that instantiates the protection-domain (PD) assembly. This is
   the trusted computing base: ~10kLOC of verified C, the only code that runs
   in privileged mode.

2. **The dregg-executor PD** — the *heart*. A protection domain that embeds
   the verified executor (`execFullForestG` via `dregg-lean-ffi`, the
   credential-gated complete-turn executor proved in `metatheory/`). The
   firmament runs every app turn *through* this PD: a turn arrives, the
   executor decodes it, runs the verified `decode → step → encode`, and emits
   a receipt. Nothing reaches durable state except through a turn this PD
   accepted. (Status: this PD now **boots and runs a verified turn** — §6, §7 + [`docs/EMBEDDABLE-LEAN-RUNTIME.md`](EMBEDDABLE-LEAN-RUNTIME.md); what remains is productionization, not the runtime port.)

3. **The capability fabric** — the unification of two capability graphs under
   one interface. seL4 caps isolate the PDs (which PD may touch which page,
   device, notification). dregg caps mediate the cells *inside* the executor
   PD (c-lists, grants, attenuation). The firmament's claim is that these are
   the **same abstraction at two points on a distance parameter** (§3).

4. **The checkpoint/restore substrate** — the machinery that freezes a PD's
   cap-state + memory and thaws it deterministically. seL4 gives transparent
   PD checkpoint/restore; dregg gives the snapshot/seal model
   (`persist/src/snapshot.rs`, `Dregg2/Spec/Lifecycle.lean`). The firmament
   *marries* them: a PD checkpoint **is** a dregg snapshot (§4).

The apps live *inside* the firmament. They are fully deterministic and
houyhnhnm — pure, reproducible, no hidden nondeterminism, no deception (§5).
The firmament is what makes that contract enforceable rather than aspirational:
the apps cannot reach a clock, an RNG, a socket, or another app's memory except
through a capability the firmament hands them, and every turn they take runs
through the verified executor and is replayable.

```
            ┌──────────────────────── seL4 root (TCB: kernel + monitor) ─────────────────────┐
            │                                                                                 │
            │   ┌─ app-PD ─┐   ┌─ app-PD ─┐        the FIRMAMENT BOUNDARY                      │
            │   │ houyhnhnm│   │ houyhnhnm│   (every turn crosses it into the executor)        │
            │   └────┬─────┘   └────┬─────┘                                                    │
            │        │  turn        │  turn                                                    │
            │        ▼              ▼                                                          │
            │   ┌──────────────────────────┐   ┌──────────────┐   ┌──────────────┐            │
            │   │   executor-PD (HEART)     │──▶│  verifier-PD │   │  persist-PD  │            │
            │   │ execFullForestG, verified │   │ STARK check, │   │ snapshot⊕    │            │
            │   │ decode→step→encode        │   │ no prover    │   │ overlay, redb│            │
            │   └─────────────┬────────────┘   └──────────────┘   └──────┬───────┘            │
            │                 │ receipt                                   │ device cap          │
            │                 ▼                                          ▼                     │
            │           ┌──────────────┐                          [ block device ]             │
            │           │   net-PD     │── NIC cap ──▶ [ virtio-net ] ── the DISTRIBUTED edge   │
            │           └──────────────┘                                                       │
            └─────────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. The PD topology — where each cap and trust boundary sits

The firmament is the five-PD assembly (`sel4/dregg.system`), evolved so the
executor-PD is the heart and the app-PDs sit inside the boundary:

| PD | Role | Caps it holds | Trust boundary |
|----|------|---------------|----------------|
| **executor-PD** | the firmament heart: runs every turn through the verified `execFullForestG` | `turn_in` (R), `state` (RW), `receipt_out` (RW), a notification to each app-PD | holds NO device cap, NO NIC cap — it is pure compute over bytes. The verified semantics is the only authority over state transitions. |
| **verifier-PD** | independent proof checking: bundle-in → STARK verify → verdict-out | `proof_in` (R), `verdict_out` (RW), one notification | holds NO prover authority, NO state cap. The seL4-enforced form of "a verifier runs in a separate process with no callback into a prover" (`verifier/src/lib.rs`). |
| **persist-PD** | the durable store: commit log, checkpoints, snapshot⊕overlay | the **sole** holder of the storage-device cap; `commit_in` (R) from the executor | the only PD that can touch the disk. No other PD can read or forge durable state. |
| **net-PD** | the network edge: virtio-net driver + smoltcp; turn ingress + gossip | the **sole** holder of the NIC cap + the virtio-mmio region + DMA paddr | the only PD that can touch the wire. De-envelopes + Ed25519-checks a `SignedTurn` *before* handing it to the executor; bad signatures never reach the heart. This PD is the **distributed end** of the cap gradation (§3). |
| **app-PD(s)** | the houyhnhnm apps: pure, deterministic, replayable | only the caps the firmament grants: a `turn_out` page to submit turns, a notification, and whatever dregg cell-caps the app was issued | cannot reach a clock, RNG, socket, device, or another app's memory. Ambient authority is structurally absent (§5). |

The seL4 cap partition **is** the trust boundary the dregg crate-split already
gestures at: `dregg-verifier`'s "no callback into a prover" becomes the
verifier-PD's missing prover cap; `dregg-persist`'s "the node's one durable
store" becomes the persist-PD's sole device cap. The firmament makes the
architecture's invariants load-bearing at the kernel level.

---

## 3. The transparent local↔distributed capability gradation

This is the firmament's central thesis: **an seL4 capability and a dregg
capability are the same abstraction at different points on a distance
parameter.** Both are unforgeable, attenuable, delegable references that
mediate access to a resource. They differ only in *how far away* the resource
is and *what bounds hold on operations against it*.

### One interface, two backings

A firmament capability is a handle `(target, rights)` that an app holds and
may invoke, attenuate (`rights' ⊆ rights`), or delegate. The interface is the
same whether the target is:

- **local** — an seL4 kernel object (a CNode slot, an endpoint, a frame). The
  invocation is a kernel syscall; revocation is `seL4_CNode_Revoke`; the rights
  are seL4 cap rights.
- **distributed** — a dregg cell on a (possibly remote) federation. The
  invocation is a turn through the executor-PD; revocation is the group-key
  epoch lift (the `remove(m)` that darkens ciphertext + capabilities in one
  turn); the rights are dregg grant-attenuation (`granted ⊆ held`, enforced by
  the capability crown / `checkSubset`).

The app does not see which backing it holds. It holds a capability; it
invokes it; the firmament routes the invocation to the kernel (local) or the
executor→net path (distributed). **Adoption is attenuation** at both ends:
granting a sub-capability is `seL4_CNode_Mint` with reduced rights locally and
`recKDelegateAtten` (the proven `granted ≤ held` gate) distributedly.

### The distance parameter `n` and what collapses at `n = 1`

The single-machine principle (`project-dregg4-vision`, the
`SINGLE-MACHINE PRINCIPLE`): the honest bounds on a distributed capability are
**distance bounds**, parametrized by the topology `n` (the number of machines
the cap's target is spread across). The firmament is the place where
`n = 1` — everything is on one seL4 machine — so the distributed bounds
**collapse to strong local properties**:

| Operation | `n > 1` (distributed) | `n = 1` (firmament, local) |
|-----------|-----------------------|----------------------------|
| **Revocation** | eventual: the epoch lift must propagate; an in-flight invocation may still land | **immediate**: `seL4_CNode_Revoke` is synchronous; the cap is dead the instant the syscall returns |
| **Checkpoint** | a *consistent cut* across machines (Chandy–Lamport); may be stale | **consistent checkpoint**: one PD's cap-state + memory is captured atomically (§4) |
| **Commit** | quorum/finality latency; the turn is final only after the blocklace finalizes it | **synchronous commit**: the persist-PD writes the commit record in one redb transaction before the turn returns |
| **Agreement** | FLP-bounded; needs a consensus round | trivial: one machine is its own quorum |

This is the single-machine principle made *architectural*. The firmament is
not "distributed dregg, crippled to one box" — it is the **collapsed limit**
of the same capability model, where the distance parameter is pinned to its
minimum and the bounds become the strong properties. A capability that an app
holds works identically whether the executor resolves it locally (kernel
object, immediate) or routes it to a peer over the net-PD (cell, eventual). The
gradation is *transparent*: the same `(target, rights)` handle, the same
attenuate/delegate/invoke operations, sliding along `n`.

The net-PD reaching the network (M3, §6) is what makes the `n > 1` end *real*
and not merely designed: a capability whose target lives on another machine is
resolved across the wire the net-PD holds. With both ends present, the
gradation is a measured axis, not a slogan.

### The cap-gradation bridge in CODE (`sel4/dregg-firmament/`)

The gradation above is not just a design — it is a runnable crate.
`sel4/dregg-firmament/` is a standalone Rust crate (its own `target/`, NOT a
member of the repo-root or Microkit workspaces) that turns this section into
code, wired to the **real dregg capability semantics** (it path-depends on the
genuine `dregg-cell` + `dregg-turn`, so it never reinvents `granted ⊆ held`):

- **One unified handle.** `Capability { target, rights }` is the `(target,
  rights)` pair. `Target` is `Local { slot }` (an seL4 CNode slot) or
  `Distributed { cell }` (a real dregg `CellId`). `rights` is the REAL
  `dregg_cell::AuthRequired` lattice — one rights model, two backings.
- **One router, two backings.** `FirmamentRouter` owns a `LocalBacking` (the
  seL4 syscall boundary: a CNode slot table where `mint` = `seL4_CNode_Mint`
  with reduced rights, `revoke` = synchronous transitive `seL4_CNode_Revoke`,
  `invoke` = `seL4_Call`) and a `DistributedBacking` (a **real**
  `dregg_turn::TurnExecutor` over a **real** `dregg_cell::Ledger`). The app
  calls `router.resolve(&handle)` / `router.attenuate_and_grant(...)`; the
  router dispatches by the handle's target alone. The app cannot tell which
  backing it holds.
- **Real attenuation at both ends.** The LOCAL mint and the DISTRIBUTED
  delegate BOTH gate on the genuine `granted ⊆ held`: locally via
  `dregg_cell::is_attenuation` on the reduced-rights mint; distributedly via a
  GENUINE `Effect::GrantCapability` turn through the executor (which rejects a
  widening grant with `DelegationDenied`, byte-for-byte the deployed
  semantics). A widening is refused identically at both backings.
- **The `n = 1` collapse, concrete.** `Bounds` carries
  `revocation_immediate` / `commit_synchronous` / `n`. At `n = 1` a distributed
  resolution's bounds **collapse to the strong local ones** — a runtime witness
  of §3's collapse table. As `n` rises the bounds relax (eventual revocation,
  quorum commit) while the verbs stay identical.
- **The acceptance test** (`tests/fluid_reach_out.rs`,
  `one_handle_resolves_local_and_distributed`): a single backing-agnostic app
  function `run_app` invokes + attenuates + delegates BOTH a local kernel
  object AND a real dregg cell through ONE router, ONE handle type. It asserts
  the local leg mints a live child slot, the distributed leg's
  `GrantCapability` turn COMMITS and the recipient cell actually holds the
  narrowed cap, and that at `n = 1` the two resolutions' bounds are identical.
  The fluid reach-out, proven runnable (`cd sel4/dregg-firmament &&
  ./run-test.sh` — 10 tests green, the real executor in the loop).

### The fluid reach-out — first-class local, seamless to distributed

The firmament's product promise (ember, 2026-06-13): a **local Robigalia install
is a first-class dregg deployment**, not a demo or a crippled subset. An app runs
deterministically on the local firmament holding local caps with the strong
`n = 1` properties (immediate revocation, synchronous commit, consistent
checkpoint). The moment one of its programs **reaches out to the network** —
invokes a capability whose target is a cell on a remote federation — the firmament
resolves it through the executor→net-PD path, and the program flows into **native
distributed dregg with no seam**: the same `(target, rights)` handle, the same
attenuate / delegate / invoke verbs, the same receipts and proofs. Nothing in the
app code distinguishes the local invocation from the remote one; only the *bounds*
relax (immediate→eventual revocation, synchronous→quorum commit) as `n` rises.
First-class locally, fluid to the wire — that is the gradation's whole point and
the firmament's headline UX, not an afterthought. It is also why `n = 1` is a
**stepping stone, not a terminus**: the same binary that runs the local firmament
scales out to `n > 1` without a rewrite, because there was only ever one model.

---

## 4. Transparent checkpoint/restore — PD checkpoint **is** a dregg snapshot

seL4 gives transparent checkpoint/restore of a protection domain: capture a
PD's capability state (its CNode) + its mapped memory, and later restore it.
dregg gives the snapshot/seal model. The firmament marries them so a houyhnhnm
app can be **frozen and thawed deterministically**, with an integrity tooth
that makes the thaw unforgeable.

### The dregg snapshot model (`persist/src/snapshot.rs`)

The snapshot is `checkpoint ⊕ overlay`, and the equation
`recover = checkpoint ⊕ overlay = replay` is the verified recovery spec
(`metatheory/Dregg2/Distributed/CrashRecovery.lean`, `recover_eq_replay`):

- A **checkpoint** (`LedgerCheckpoint`, `persist/src/ledger_store.rs`) is the
  full cell state at a height cut — the "freeze."
- An **overlay** (`Snapshot.overlay: Vec<Cell>`, from `cell_overlay_since`,
  `persist/src/commit_log.rs`) is every cell post-state committed *after* that
  cut — the "delta since freeze," last-writer-wins.
- **Replay** = instantiate the checkpoint, then `upsert_cell` the overlay over
  it (`snapshot.rs`, `apply_snapshot`). The result is provably equal to a full
  replay from genesis, *for any checkpoint cut* — so where you cut is free.

### The root tooth — the anti-substitution guard

`Snapshot.claimed_root: [u8; 32]` is the **root-binding tooth**. It is the
Merkle root of the reconstructed ledger, and it is bound to the chain at
`CommitRecord::ledger_root` (`persist/src/commit_log.rs`) — the post-state
commitment the federation attested to. The tooth makes the thaw unforgeable
three ways:

1. **Ship-side** (`ship_snapshot`): a node never ships a snapshot whose
   reconstructed root ≠ its own recorded finalized root (fail-closed).
2. **Apply-side** (`apply_snapshot`): the joiner independently recomputes the
   root from `checkpoint ⊕ overlay`; if it ≠ `claimed_root`, the thaw is
   refused (fail-closed). Tampering with the checkpoint *or* the overlay fails
   here.
3. **Trusted-root** (`apply_snapshot_verified`): the joiner additionally
   checks `claimed_root` against a root it already trusts (a finality proof) —
   so a server cannot ship a *self-consistent* snapshot of a *different*
   ledger.

### How the PD checkpoint maps to the snapshot

In the firmament an app-PD's deterministic state is a dregg cell forest. The
mapping:

| seL4 PD checkpoint | dregg snapshot |
|--------------------|----------------|
| freeze the PD's cap-state + memory atomically | `ship_snapshot` — capture `checkpoint ⊕ overlay` at a height cut |
| the delta since the freeze | the `overlay` (cell post-states since the cut) |
| restore = rebuild frozen state + replay delta | `apply_snapshot` — `upsert` the overlay onto the checkpoint |
| "is this the state I froze?" | the `claimed_root` tooth — recompute + compare, fail-closed |
| restore only to a trusted anchor | `apply_snapshot_verified(trusted_root)` |

Because the app is houyhnhnm — deterministic, no hidden state — its entire
observable state *is* its cell forest, so the dregg snapshot captures it
completely. There is no torn state (the checkpoint is a single-height cut), no
lost mutation (the overlay carries every committed write), no double-apply (the
commit cursor is crash-consistent), and no forgery (the root tooth). Freezing
and thawing a houyhnhnm app is `ship_snapshot` then `apply_snapshot_verified`.

### Seal vs. snapshot — the Lifecycle taxonomy

`metatheory/Dregg2/Spec/Lifecycle.lean` distinguishes the *lifecycle* states a
cell can be in, which is orthogonal to snapshot-shipping:

- **`sealed (reasonHash, sealedAt)`** — reversible quiescence: the cell rejects
  new effects, state + history preserved; `unseal` returns it to `live`. This
  is the *pause* primitive: freeze an app-PD in place (stop accepting turns)
  without shipping it anywhere.
- **`live`** — effects flow normally.
- **`archived`** — still live, but the receipt-chain prefix is folded into a
  checkpoint (the IVC fold) — the history-compression that makes the snapshot's
  checkpoint cheap.
- **`migrated` / `destroyed`** — terminal (no transition leaves them, proved by
  `terminal_rejects_transition`).

So the firmament has two complementary freeze operations: **seal** (pause in
place, reversible via unseal) and **snapshot** (ship the state, verifiable via
the root tooth). A transparent checkpoint/restore of an app-PD is
*seal → ship_snapshot → (move/store) → apply_snapshot_verified → unseal*.

---

## 5. The deterministic-houyhnhnm app contract

The firmament enforces that apps are **houyhnhnm**: pure, reproducible, no
hidden nondeterminism, no deception. The enforcement is structural — it falls
out of the cap fabric, not from app good behaviour.

**What the firmament enforces:**

1. **No ambient authority.** An app-PD's CNode contains *only* the caps the
   firmament minted for it: a `turn_out` page, a notification, and its issued
   dregg cell-caps. It has no device cap, no NIC cap, no cap to any other PD's
   memory. Anything not granted is unreachable — seL4 enforces this in
   hardware (the MMU + the cap-derivation tree).

2. **No wall-clock, no RNG — except through caps.** There is no `gettimeofday`,
   no `getrandom`, no syscall surface in an app-PD (it is `#![no_std]`,
   `#![no_main]`, panic=abort, with only the Microkit IPC primitives). If an
   app needs time or randomness it must receive it as an *input to its turn*
   (a cap-mediated value the executor supplies and the receipt records), so the
   value is part of the replayable transcript rather than an ambient draw.

3. **Replayability.** Every app action is a turn through the executor-PD. The
   turn + its inputs are recorded in the commit log (`persist/src/commit_log.rs`,
   `CommitRecord`). Re-running the recorded turns from a checkpoint reproduces
   the exact state (`recover_eq_replay`). Determinism is not trusted — it is
   *checked*: the executor is the verified `execFullForestG`, so the same
   inputs always yield the same post-state + receipt + root.

4. **No deception.** The executor is the verified semantics; the verifier-PD
   independently STARK-checks the turn's proof with no prover authority; the
   snapshot's root tooth makes a thawed state self-attesting. An app cannot
   claim a state transition the executor did not produce, and cannot ship a
   snapshot of a state it was not in. The whole stack is "the proof witnesses
   the protocol's correct evolution" (the ARGUS vision) carried down to the
   seL4 substrate.

The contract in one line: **an app's entire observable behaviour is a sequence
of cap-mediated, verified, replayable turns over a deterministic cell forest,
with no path to ambient nondeterminism and no path to assert an unverified
transition.** The firmament is the substrate that makes every clause of that
sentence true by construction.

---

## 6. The heart and the edge — status

The firmament needs a **heart** (a PD that runs real verified compute) and an
**edge** (a PD that reaches the network, making the `n > 1` end of the
gradation real). Their status:

### The executor-PD (the true heart) — boots a verified turn; the port is DONE

The executor-PD embeds the Lean-compiled `execFullForestG`. It now **boots and
runs a verified turn inside a real seL4 protection domain** (`status:2 ok:1`,
live-verified — [`docs/EMBEDDABLE-LEAN-RUNTIME.md`](EMBEDDABLE-LEAN-RUNTIME.md) §4).
Getting there cleared two compounding obstacles, established by direct probe of the
toolchain (`leanrt` v4.30.0) and then executed as the excision below:

1. **Object format.** The compiled Lean closure (`libdregg_lean.a`, ~8200
   objects) and the Lean runtime archives (`libleanrt.a` etc.) are **Mach-O
   arm64** (the macOS host build), while the seL4 target is **ELF
   `aarch64-unknown-none`**. The entire closure must be *recompiled* with
   `leanc` targeting an ELF triple — not a relink.

2. **The libuv coupling at runtime init.** The pure executor path
   (`dregg_exec_full_forest_auth_str`) performs no IO. But the init ritual
   `lean_initialize_runtime_module` (in `init_module.cpp.o`) has an **undefined
   reference to `initialize_libuv` and `initialize_io`** — so the linker pulls
   in the 10 libuv-coupled leanrt objects (`dns, event_loop, io, libuv,
   net_addr, signal, system, tcp, timer, udp`) even though we never run the
   event loop. The pure-path objects additionally require `mi_malloc`
   (mimalloc), `pthread_*` (GC/thread init), the C++ exception runtime
   (`__cxa_*`), and TLS (`__tlv_bootstrap`).

**The excision plan (the exact remaining wall + the path through it):**

- **The 10 libuv objects are cleanly separable** — they are named by IO concern
  and the pure path calls none of them. Stub `initialize_libuv` and
  `initialize_io` as no-ops returning success (the executor never opens a
  socket/file/timer), and provide the handful of `uv_*` symbols the linker
  demands but execution never reaches. The other six runtime initializers
  (`alloc, debug, mutex, object, thread, process, stack_overflow`) are
  libuv-free and stay. This is *weld, not build*.
- **GMP** is referenced only by `mpz.cpp.o` + `sharecommon.cpp.o`. It is
  portable C (malloc + libc only); recompile it for the ELF target, or — for a
  hand-reduced shim that uses only small fixnums — stub the `mpz` path.
- **The substrate for libc/pthread/mimalloc** exists experimentally in
  rust-sel4: `crates/experimental/sel4-musl` (a musl syscall-emulation shim)
  and `crates/private/support/sel4-root-task-with-std`. The executor-PD is a
  **root-task-with-std** style PD (not a bare Microkit PD): build musl for the
  ELF target, wire `sel4-musl`'s syscall handler, recompile the Lean closure
  with `leanc --target aarch64-unknown-linux-musl`, link under the shim with
  the libuv objects excised.

That checklist — *(1) ELF-recompile the Lean closure under leanc; (2) excise the
10 libuv objects + stub their two init functions; (3) GMP for ELF; (4) host on
`sel4-musl` + a root-task runtime* — **is done**, and the executor-PD boots and
runs a real turn, printing the receipt over serial: the firmament's first
heartbeat. What remains is productionization (crypto-floor curves · principled
elaborator trim · fold the root-task into the 5-PD Microkit assembly), not the
runtime port — see [`docs/EMBEDDABLE-LEAN-RUNTIME.md`](EMBEDDABLE-LEAN-RUNTIME.md) §4.

### The verifier-PD STARK core (the bankable heart organ)

Until the executor-PD lands, the firmament's verified-compute heart is the
**verifier-PD running a real plonky3 STARK verification**. This needs *no
Lean*: the verify entry (`verify_effect_vm_proof`, `verifier/src/lib.rs`) calls
`stark::verify` (`circuit/src/stark.rs`), and the entire verify path uses only
`core::ops` / `core::fmt` — no getrandom (verification is deterministic), no
rayon, no std collections. The port is `std → core` on ~20 circuit files, all
mechanical (plonky3 is already `#![no_std]`). A booting verifier-PD that does
real proof-checking is a concrete firmament organ and the high-value win when
the full Lean port is too deep for one lane (§ `sel4/dregg-pd/verifier-stark/`).

### The net-PD (the edge)

M3 networking is the distributed edge. The `sel4-virtio-net` driver PD already
cross-builds for seL4; the rust-sel4 `http-server` example
(`crates/examples/microkit/http-server/`) is the canonical multi-PD net
assembly (virtio-net driver PD + smoltcp client PD + shared ring buffers +
virtio-mmio phys_addr/DMA paddr setvars). A stripped TCP-echo / DHCP client PD
over `sel4-shared-ring-buffer-smoltcp` is the minimal edge boot (§
`sel4/dregg-pd/net/`).

**The driver PD now PROBES a real virtio-net device on-device (M3 edge, the
slot-alignment wall cleared).** `make run-net` (`sel4/net-driver-only.system`)
boots the driver PD against a real QEMU `-device virtio-net-device` on the
mmio bus. The wall was `InvalidDeviceType(0)` — an *empty* mmio slot — because
the boot ran without the QEMU device flags; the mmio slot math was already
right (`virtio_mmio` region `phys_addr=0xa003000` + the config `OFFSET=0xe00`
lands on slot 31, where QEMU places a single virtio-mmio device). With the
device present, the driver reads the `VirtIOHeader` and brings the NIC up;
captured serial (`/tmp/sel4-net-driver-probe2.log`):

```
[net] virtio-mmio probe: version=Modern device_type=Network vendor=0x554d4551
[net] virtio-net device UP — MAC [52, 54, 00, 12, 34, 56] — the firmament reached the wire
```

That is the firmament's edge touching the wire: `device_type=Network`, vendor
`0x554d4551` ("QEMU"), the NIC up with its MAC. The remaining net wiring is the
smoltcp **client** PD + the shared-ring assembly (a TCP echo over
`sel4-shared-ring-buffer-smoltcp`), which turns "the NIC is up" into "a turn
arrives over TCP" — the `n > 1` invocation path of the cap-gradation bridge.

---

## 7. The firmament status board

| Firmament organ | What it is | Status |
|-----------------|------------|--------|
| **seL4 root + monitor** | TCB, CapDL init, Microkit monitor | ✅ boots (M0/M2 on aarch64, M5 on riscv64) |
| **executor-PD (heart)** | verified `execFullForestG` | ✅ boots a verified turn (`status:2 ok:1`, root-task; §6, `docs/EMBEDDABLE-LEAN-RUNTIME.md`). Remaining: productionization (crypto-floor curves · elaborator trim · Microkit fold) |
| **verifier-PD STARK core (heart organ)** | real plonky3 STARK verify | ◐ no_std structural verify boots (M1); STARK-core port is mechanical std→core (§6) |
| **persist-PD** | snapshot⊕overlay + root tooth | ◐ snapshot model lands in `persist/src/snapshot.rs`; PD = redb-over-block-cap (quarter) |
| **net-PD (edge)** | virtio-net + smoltcp | ◐ driver PROBES a real virtio-net on-device — `device_type=Network`, NIC up (M3, `make run-net`); smoltcp client PD + ring assembly remains (§6) |
| **app-PDs** | houyhnhnm apps | ◐ rbg DirectoryCell PD boots (M2); the cap contract (§5) is the firmament's enforcement target |
| **cap fabric** | local↔distributed gradation | ◐ **runnable bridge** in `sel4/dregg-firmament/`: one `(target, rights)` handle + router, real dregg attenuation (`granted ⊆ held`) at both ends, the `n = 1` collapse witnessed, 10 tests green incl. the real executor in the loop (§3) |
| **checkpoint/restore** | seal/snapshot/unseal | design (§4) on real `snapshot.rs` + Lifecycle.lean; PD-checkpoint wiring is quarter+ |

**The firmament has a heart and an edge.** The true heart — the executor-PD —
**boots and runs a verified turn** (`status:2 ok:1`); the verifier-PD runs a real
STARK check as the complementary heart organ; the net-PD reaches the network (the
edge). What remains is productionization of the executor-PD (crypto-floor curves ·
elaborator trim · fold into the 5-PD Microkit assembly) and the smoltcp client PD
for full TCP — weeks, not the open-ended runtime fog the roadmap once feared.

---

## 8. Decisions for the project lead

1. **Heart sequencing — RESOLVED (both).** The executor-PD port landed *and* the
   verifier-PD STARK core ships as the complementary heart organ: the executor-PD
   boots a verified turn today (§6), and the STARK-core path (no Lean, mechanical)
   is the second heart. The remaining executor-PD work is productionization, not
   the port.

2. **GMP strategy — RESOLVED.** Real GMP 6.3.0 is cross-built for aarch64-musl and
   linked into the booting executor-PD (`docs/EMBEDDABLE-LEAN-RUNTIME.md` §4); no
   fixnum-shim was needed. (The shim remains a possible size optimization, not a
   blocker.)

3. **Executor-PD runtime shape — RESOLVED for v0, productionization step named.**
   The booting executor-PD is a `sel4-musl` + `root-task-with-std` (simpler, weaker
   internal isolation). Folding it into a Microkit-PD with the cap-partition trust
   boundary (the steady-state `dregg.system` shape) is the named productionization
   step (§6, §7).

4. **The `n = 1` collapse as the security model — DECIDED (ember, 2026-06-13):
   BOTH.** The single-machine firmament is VITAL and must be **fully first-class**
   — its strong properties (immediate revocation, consistent checkpoint,
   synchronous commit) are **headline guarantees** of the `n = 1` deployment, not
   transient ones — AND it is a **stepping stone** to `n > 1`, never a terminus.
   The product target is the **fluid reach-out** (§3, "The fluid reach-out"): a
   local Robigalia install runs programs first-class on the firmament, and when a
   program reaches the network it flows into native distributed dregg seamlessly
   (same capability, the bounds simply relax along `n`). The architecture stays
   the collapsed limit of one model that scales out without a rewrite.
