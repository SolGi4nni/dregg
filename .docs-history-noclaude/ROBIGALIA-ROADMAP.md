# ROBIGALIA-ROADMAP — dregg as a native seL4 OS

*Vision + scoping doc. Present-tense where the seL4 side is real (the boot ladder
boots, the verified executor has run one turn inside a PD); clearly-scoped work
where it isn't (the service-loop executor PD, the block-cap persist backend, the
2-PD net assembly). First-principles, no trajectory narrative. Names every seam
as work with a closure lever, never a wall; never overclaims. Cites the tree as
of 2026-06-13. Companion to `docs/SEL4-EMBEDDING.md` (the boot ladder + the
toolchain), `docs/FIRMAMENT.md` (the PD architecture + the cap gradation),
`docs/CAPDL-POLYGLOT-DX.md` (the DreggDL cell-cap spec), and `sel4/` (the booting
PDs + the WALL journals).*

---

## 0. The one-paragraph thesis

dregg's claim is capability-security by construction: every action is a held
capability presented to a gate, the Lean kernel *is* the executor, and every turn
leaves a receipt. A native seL4 OS lets the **deployment substrate share that
thesis**. seL4 is a microkernel whose ~10kLOC of C is machine-checked and whose
only authority primitive is the unforgeable, attenuable, delegable **capability**
— the exact same primitive dregg builds the protocol on. So "capabilities all the
way down" stops being a slogan: the seL4 cap graph isolates the OS components
(executor, verifier, persist, net, apps), and the dregg cap graph (cells, c-lists,
grants) mediates inside the executor component. This roadmap is how dregg becomes a
bootable seL4 image: the **protection-domain model**, the **first real port**
(`DirectoryFactory → seL4_Untyped_Retype`, already done — M2 boots), the **Lean
runtime bottom-half port** (the historical blocker — *now brought up to a one-turn
demo, with honest residue before it is a service*), the **capDL/DreggDL** dual
cap-graph instantiation, and the **staged path** (verifier-PD unblocked now →
executor-PD carried from its one-turn demo to a Microkit-PD service → bootable node
image). The discipline of the doc is to say exactly where each piece *is*, not
where it is aimed.

---

## 1. The protection-domain model — the OS *is* a cap-partitioned PD assembly

A native seL4 dregg OS is a **Microkit assembly of protection domains** whose seL4
capability partition *is* the trust boundary. This is not aspiration: it boots.
`sel4/dregg.system` is the five-PD assembly, every PD a real cross-compiled ELF
that reaches userspace and prints over serial, on a native-macOS toolchain
(Microkit SDK 2.2.0 + rust-sel4, no Docker — `sel4/README.md`, `sel4/setup.sh`).
The seats:

| PD | Role | Caps it holds (the partition) | Trust boundary it earns | Status |
|----|------|-------------------------------|-------------------------|--------|
| **executor** | the heart: runs every turn through the verified `execFullForestG` | `turn_in` (R), `commit_out` (RW), a notification to each app-PD — **NO device cap, NO NIC cap** | the verified semantics is the *only* authority over state transitions; it is pure compute over bytes | seat held by `executor-stub`; the **real** verified executor has run one turn in a root-task PD (§3) — carrying it into this seat is the headline lever |
| **verifier** | independent proof checking: a real STARK proved + verified on-device | self-contained (no shared region) — **NO prover authority, NO state cap** | "a verifier runs in a separate process with no callback into a prover" (`verifier/src/lib.rs`) becomes the verifier-PD's *missing* prover cap + the one-way executor→verifier channel | **boots** — `verifier-stark` runs a real BabyBear+BLAKE3+FRI STARK with the anti-ghost tooth (§2, `sel4/dregg-pd/verifier-stark/`) |
| **persist** | the durable store: commit log, checkpoints, snapshot⊕overlay | the **sole** holder of the storage-device cap; `commit_out` (R) | the only PD that can touch the disk; no other PD can read or forge durable state | seat held by `persist-stub` (maps `commit_out` R, no block cap yet); the redb-over-block-cap backend is §4 |
| **net** | the edge: virtio-net driver; turn ingress + gossip | the **sole** holder of the NIC cap + the virtio-mmio region + DMA paddr + IRQ 79 | the only PD that can touch the wire; de-envelopes + Ed25519-checks a `SignedTurn` *before* the executor sees it; bad signatures never reach the heart | **probes a real virtio-net device on-device** (`device_type=Network`, NIC up, MAC); the smoltcp client PD + ring assembly remains (§5) |
| **app(s)** | the houyhnhnm apps: pure, deterministic, replayable | only the caps the firmament grants: a `turn_out` page, a notification, its issued dregg cell-caps | cannot reach a clock, RNG, socket, device, or another app's memory — ambient authority is *structurally absent* (the MMU + the cap-derivation tree enforce it) | **boots** — the rbg `DirectoryCell` PD (CAS + ACL + factory slot-caveat, §6) is the first app-PD |

The cross-PD byte channels are the **only** shared state, and each is an seL4 cap
held by exactly the PDs that need it: `turn_in` (net writes a checked turn →
executor reads R), `commit_out` (executor writes RW → persist reads R). The
control-flow edges are three Microkit channels — `net→executor`,
`executor→persist`, and a deliberately **one-way** `executor→verifier` (the
verifier signals "verdict ready" and *never* calls out to a prover; the missing
reverse edge *is* the no-prover-callback property). There is no other path; the cap
layout forbids it.

This is the seL4-native realization of the dregg crate-split: `dregg-verifier`'s
"no callback into a prover" is the verifier-PD's missing prover cap;
`dregg-persist`'s "the node's one durable store" is the persist-PD's sole device
cap. The architecture's invariants become load-bearing at the kernel level — the
component boundaries *are* the trust boundaries.

### The web surface as a sixth PD (research, gated)

`docs/EMBEDDED-WEB-SURFACE.md` §5 adds a `renderer` PD running Servo whose entire
authority is the seL4 caps its parent hands it (a framebuffer region cap + an IPC
endpoint to a `web-broker` PD that solely holds the NIC/storage caps), so the
renderer *physically cannot* fetch except by asking the broker, which discharges
the surface's macaroon first. This is the kernel-enforced form of the embedded-web
authority model — and it is honestly gated: a Servo-on-seL4 port is its own large
effort (a multi-MB `std`/POSIX-assuming codebase + a GPU/framebuffer-cap story),
sequenced behind the executor-PD. Named as the architectural end-state, not claimed
near.

---

## 2. The verifier PD — unblocked now (the bankable verified heart organ)

The verifier path is the part of the OS that needs **no Lean** and runs real
verified compute today. Two reasons it is the unblocked beachhead:

1. **It is Lean-free by feature.** A *default* verifier build is not Lean-free —
   through `{dregg-captp, dregg-federation, dregg-turn}` it transitively links
   `dregg-lean-ffi` (libuv/GMP/C++). The fix is one feature line:
   `verifier/Cargo.toml` carries a `no-lean-link` feature fanning out to those
   three. `cargo build -p dregg-verifier --features no-lean-link` finishes clean;
   the binary links **only `libSystem`+`libiconv`**, has **zero** Lean/libuv/GMP
   symbols, and the closure has no tokio/mio/async/redb/net. `make verify-isolation`
   asserts this on the host — the precondition that the verify path can be a clean
   seL4 PD. **And there is no downgrade temptation here**: the verifier carries no
   executor authority, so `no-lean-link` on it is pure link-suppression, not a
   guarantee change (contrast the executor, §3, where shipping the unverified Rust
   executor as authoritative *would* be a downgrade).

2. **The STARK core is `#![no_std]`-portable.** The verify entry uses only
   `core::ops`/`core::fmt` — no getrandom (verification is deterministic), no rayon,
   no std collections. plonky3 is already `#![no_std]`.

This is not a plan — it boots. `sel4/dregg-pd/verifier-stark/` runs a **real
cryptographic STARK** on seL4: it PROVES a 4-row AIR (a 78 KiB proof), VERIFIES it
(ACCEPT), roundtrips the wire form, and shows the **anti-ghost teeth** — a tampered
proof REJECTS ("Trace Merkle proof failed"), a wrong public-input REJECTS ("Public
inputs mismatch"). The STARK core is the *verbatim* `dregg-circuit` custom STARK
(BabyBear + BLAKE3 Merkle + FRI + Fiat-Shamir) carried `std → core`/`alloc` —
byte-identical prove/verify. `prove()` is deterministic (Fiat-Shamir, no RNG/clock),
so the PD needs no entropy source. No Lean, no libuv, no GMP.

The verifier PD is the firmament's **bankable verified-compute heart organ**: the OS
does real, independent, on-device proof-checking *now*, with the no-prover-callback
property kernel-enforced, while the executor PD is carried from its one-turn demo to
a service (§3).

---

## 3. THE historical blocker — the Lean runtime bottom-half — brought up to one turn

This section is the load-bearing honesty of the roadmap, and it has *moved* since
the companion docs were last revised. `SEL4-EMBEDDING.md` §2/§7 and `FIRMAMENT.md`
§6/§7 call the executor-PD "the one true blocker… weeks-to-a-quarter of specialist
work," and *for a service-grade executor PD that remains the honest framing*. But
the wall has been driven through to a **demonstrated one-turn boot**, and the doc
discipline is to say exactly that — neither hiding the progress nor inflating it
into a finished service.

### Why it was the blocker

The verified executor is not portable Rust — it is **compiled Lean linked into the
node**. `dregg_exec_full_forest_auth` (= `execFullForestG` + admission, proved in
`metatheory/`) takes bytes, returns bytes, performs no IO — but linking it drags the
whole Lean runtime: the closure `libdregg_lean.a` (~8200 objects), `leanrt`, the
Lean stdlib, the Lean kernel C++, **GMP**, **libuv** (Lean's IO/event loop), the
C++ runtime, and a malloc/thread substrate. Two compounding facts made it a wall:
the host build is **Mach-O arm64** while the seL4 target is **ELF** (a recompile,
not a relink), and the runtime init pulls libuv even though the pure executor path
opens no socket/file/timer.

### The excision plan, and where each step now stands

The plan was four steps. **All four are green at the one-turn-demo level**
(`sel4/dregg-pd/executor-pd/WALL.md`, `sel4/dregg-pd/executor-rootserver/WALL-roottask.md`):

| Step | What | Status (one-turn demo) |
|------|------|------------------------|
| (1) | ELF-recompile the Lean closure under `leanc` | **green** — all 757 Dregg2 `:c` facets ELF-recompile for aarch64 with **zero source changes**; the entry `dregg_exec_full_forest_auth` survives as a global text symbol |
| (2) | an ELF Lean runtime bottom-half (leanrt + Init/Std/Lean/mathlib/deps + the kernel C++) | **green — built** from `lean4@d024af099` sources for hosted `aarch64-linux-musl`; the 10 libuv-coupled `leanrt` objects excised + their two init functions stubbed (the IO monad kept, the event loop dropped) |
| (3) | GMP for ELF | **green** — real GMP 6.3.0 cross-built static for aarch64-musl |
| (4) | host on seL4 | **done (one turn)** — the verified turn runs **inside a real seL4 protection domain** under `qemu-system-aarch64` |

**The turn runs, on the microkernel.** The seL4 kernel boots, drops to user space,
the executor root-task PD installs its `sel4-musl` syscall handler, the Lean runtime
initializes, and `dregg_exec_full_forest_auth` produces **`status:2, ok:1`
(bodyCommitted — accepted)** over serial: nonce 7→8, a 30-unit transfer (cell-0
100→90, balances `[0,0,70]`/`[1,0,35]`), nullifier 111 + commitment 222 registered.
It is **byte-for-byte the receipt** the host-musl validation banked — the same
verified computation, now beating on seL4. The boot evidence is
`executor-rootserver/out/sel4-boot-evidence.log`; the reproducer is
`executor-rootserver/scripts/build-image.sh` (provision → relink → cargo → loader →
add-payload, end to end). Getting there cleared eleven precise walls, each fixed at
root cause, not worked around: building the seL4/musllibc fork (`muslForSeL4`, every
syscall routed through `__sysinfo`, zero `svc`); a standalone root-task seL4 kernel
+ the rust-sel4 loader; the merged libsel4 headers; the static C++ runtime link; the
macOS-host cross-asm fix that turned a 7 KB data-only loader stub into a real 62 KB
loader; a 2.5 GiB RAM window + a 2^19-slot root CNode for the large image; a
`.preinit_array` syscall-handler install (before the C++ ctors malloc); a
`dl_iterate_phdr` override; the by-number startup syscall surface; and a sentinel
`/dev/urandom` (the runtime seeds its hash from it at init).

### The honest residue — what "one turn boots" is NOT yet

This is a demonstrated heartbeat, not a service. Five residues stand between it and
the steady-state executor PD, each a lever, none a wall:

1. **Crypto floor stubbed.** The 8 `dregg_*` crypto-floor symbols are a
   Rust-PD-supplied stub (`crypto-stub.c`, panic-if-reached). The demo wire is a
   *non-crypto* turn, so it never reaches them. **Lever:** wire the real
   Poseidon2/BLAKE3/Ed25519 (the Rust crypto the production node already supplies)
   into the PD for crypto-bearing turns.
2. **Determinism shims.** `/dev/urandom`, `clock_gettime`, `getrandom` are
   deterministic zero-fill — faithful for the deterministic verified turn (its real
   crypto is the floor above), but a PD needing genuine entropy/time would wire a
   hardware/seL4 source.
3. **Root-task, not Microkit PD.** The demo is a `root-task-with-std`-style PD
   (`sel4-musl` is experimental and root-task-only in rust-sel4). The steady-state
   `dregg.system` seat is a **Microkit PD**. **Lever:** carry the executor onto a
   Microkit-PD musl substrate, or decide (a project-lead call, §8) to ship the
   executor as a root-task component beside the Microkit assembly.
4. **One turn, not a loop.** The PD runs *one* turn from a baked-in demo wire and
   exits. The seat in §1 reads a turn stream from `turn_in` and writes commits to
   `commit_out`. **Lever:** the service loop — block on the `net→executor`
   notification, decode the staged turn, run the verified step, stage the commit,
   signal persist.
5. **One re-emission fidelity gap, recovered exactly.** The released `lean -c` is
   internally inconsistent for `l_String_instDecidableLtRaw___aux__1` (called by
   `Init.Data.String.Basic`, not re-emitted by its canonical owner); reached at
   executor *init*. Recovered **not hand-rolled**: a `String.Pos.Raw` is a `Nat`, its
   `<` is `Nat.decLt`, and the self-contained sibling that *is* emitted is verbatim
   `lean_nat_dec_lt(p1,p2)` — so the faithful body is `lean_nat_dec_lt` (`aux-defs.c`).
   Three sibling auxiliaries share the gap but are verified-unreachable on the turn
   and stay abort-guarded.

There is also a **285 MB image** (the whole Lean `mathlib`/`Lean` archives link in;
`--gc-sections` keeps the reachable closure, but the olean-derived *data* is heavy).
Shrinking it (dead-data GC) is a follow-up, not a blocker.

### The escape hatch (and why it is scaffold, not destination)

`dregg-lean-ffi` has a `no-lean-link` feature (used for wasm32/zkvm) that builds the
node marshal-only with runtime stubs (`lean_available()` = false). An seL4 node
*could* ship "shadow-off," running only the Rust executor (`dregg-turn`). But per
the standing steer ("the Rust executor is the subject-under-test, the Lean is the
source of truth"), shipping the unverified executor as the *authoritative* one would
be a guarantee downgrade. `no-lean-link` is the bring-up scaffold; with the Lean
turn now booting inside a PD, the destination is in reach without it.

---

## 4. The persist PD — a capability-secure durable store

`persist/` is the node's one durable store (commit log, checkpoints, blocklace,
forever digests), backed by `redb` — an mmap-based embedded KV store. mmap + a real
block device + a filesystem is exactly what an seL4 userland does not give for free.
The path:

1. **The PD owns the device cap, solely.** In `dregg.system` the persist PD is the
   *only* holder of the storage-device cap; no other component can touch the disk.
   This is the seL4-native form of the crate-level invariant ("the node's one durable
   store"). Today the seat (`persist-stub`) maps `commit_out` (R) and nothing else —
   the device cap will land *here* and only here.
2. **Back redb with a raw block cap, not a filesystem.** seL4 ships no filesystem.
   The near-term backend is a `redb` `StorageBackend` over a raw block cap (no POSIX
   file) — more realistic than wiring a verified FS. The verified-FS options
   (BilbyFs/Cogent line) are external efforts to *adopt*, not build, and are beyond a
   quarter.
3. **rbg's VFS heritage is the design sketch.** `rbg/src/vfs.rs` models storage as
   Volume (budget) / Blob (content-addressed note) / Directory (c-list + provenance),
   and notes the key property: **notes ARE nameless writes — the address IS the
   content.** Content-addressed storage needs *no* inode/naming layer, which is
   exactly what makes a minimal block-cap backend sufficient. In the cap mapping
   (`sel4/RBG-TO-SEL4.md`) a Blob is a **frame cap**, a Volume is a **quota of frames**
   the persist PD owns.

The snapshot model that backs checkpoint/restore already exists and is verified:
`persist/src/snapshot.rs` is `checkpoint ⊕ overlay`, with `recover = checkpoint ⊕
overlay = replay` proved (`metatheory/Dregg2/Distributed/CrashRecovery.lean`,
`recover_eq_replay`) and a `claimed_root` anti-substitution tooth (recompute the
Merkle root from `checkpoint ⊕ overlay`, fail-closed on mismatch). On seL4 this
marries to seL4's transparent PD checkpoint/restore (`FIRMAMENT.md` §4): a PD
checkpoint *is* a dregg snapshot. That wiring is quarter+; the model is the part that
is done.

---

## 5. The net PD — the edge that makes the distributed end real

`net/` + the node's gossip/blocklace sync + HTTP ingress assume tokio + POSIX
sockets. On seL4 the network story is a userspace stack behind a driver PD that
solely holds the NIC cap. Status — the edge **touches the wire**:
`sel4/dregg-pd/net/` (the rust-sel4 virtio-net driver vendored with git-pinned deps)
cross-builds and BOOTS; `make run-net` boots it against a real QEMU `-device
virtio-net-device`, and captured serial shows the probe succeed:

```
[net] virtio-mmio probe: version=Modern device_type=Network vendor=0x554d4551
[net] virtio-net device UP — MAC [52, 54, 00, 12, 34, 56] — the firmament reached the wire
```

`device_type=Network`, vendor `0x554d4551` ("QEMU"), the NIC up with its MAC. The
slot-alignment wall is cleared: the virtio-mmio region (`phys_addr=0xa003000` + the
config `OFFSET=0xe00`) lands on the slot QEMU places a single virtio-mmio device
(31); the earlier `InvalidDeviceType(0)` was an *empty* slot from booting without the
device flag, not bad mmio math. The cap layout (the mmio region + DMA paddr + IRQ 79)
lives *only* in the net PD — the trust-boundary point of the whole assembly.

The remaining net wiring, named as the three precise pieces it is:

1. a **smoltcp client PD** (DHCP/echo, then turn ingress) over
   `sel4-shared-ring-buffer-smoltcp` + `sel4-async-network` — turns "the NIC is up"
   into "a turn arrives over TCP";
2. the **2-PD `.system` assembly** (`sel4/net.system`, scaffolded) + the shared-ring
   channel wiring between driver and client;
3. the **de-envelope boundary** — the net PD parses the postcard `SignedTurn` and
   verifies the Ed25519 signature *before* staging it in `turn_in` for the executor
   (the one wire format all three SDKs already share, `CAPDL-POLYGLOT-DX.md`).

The rust-sel4 `http-server` example (virtio-net driver PD + smoltcp client PD +
shared ring buffers) is the canonical multi-PD net assembly to follow. The edge is
what makes the `n > 1` end of the cap gradation (§7) *real*: a capability whose target
lives on another machine is resolved across the wire this PD holds.

---

## 6. The first real port — `DirectoryFactory → seL4_Untyped_Retype` (done: M2 boots)

The smallest thing that turns an rbg *idea* into a real seL4 *mechanism* is the
factory → Untyped retype edge — the one place where dregg's "capability-secure
creation" claim becomes a *kernel-enforced fact*. It is **additive** (it does not
need the Lean runtime port, so it proceeded in parallel), and it is **done at the
app-PD level**: M2 boots.

`sel4/dregg-pd/rbg-dir/` is the rbg `DirectoryCell` brought up as a real seL4
component: a versioned capability-list with CAS `swap`, a membership ACL, and
provenance, plus the `DirectoryFactory` slot-caveat — ported faithfully from the
`std`-bound heritage (`rbg/src/{directory,factory}.rs`) onto `#![no_std]` + `alloc`
so it actually boots. The cap mapping (`sel4/RBG-TO-SEL4.md`) is the reviewable
artifact behind it:

| rbg concept (heritage, `std`) | seL4 primitive | what the port does |
|---|---|---|
| `DirectoryCell` — a named, versioned c-list with provenance | **CNode** + a userspace name→slot index | the c-list becomes a real seL4 CNode; entries are caps in slots; the name→slot map stays in userspace (seL4 caps are slot-indexed, not named) |
| `DirectoryFactory` — constrained cell creation | **Untyped cap + `seL4_Untyped_Retype`** | the factory PD holds an Untyped cap + a retype template; it can mint *only* the declared object type — the slot-caveat is a kernel invariant, not a Rust check |
| `SturdyRef` — a persistable, revivable reference | **badged endpoint cap** + a DreggDL entry that re-mints it at load | reviving a SturdyRef = the loader re-installing the badged cap from the deployment spec |
| `ScopedIntentPool` — membership-bounded intents | **endpoint cap whose badge encodes the scope** | seL4 enforces that only badge-holders invoke it — membership-bounding by construction |
| `vfs::Blob` / `Volume` | **frame cap** / a **quota of frames** the persist PD owns | content-addressed notes need no inode layer (§4) |

The concrete invocation the port realizes:
`seL4_Untyped_Retype(untyped, CNode_object, …)` mints a fresh CNode for the new
directory's c-list — the factory *physically cannot* mint anything but the declared
type. M2 demonstrates the discipline running as a userspace component
(`rbg-dir/src/main.rs:224`: "→ maps to `seL4_Untyped_Retype(untyped, CNode, ..)`").
This earns the "capabilities all the way down" claim for the factory/creation path
*before* the full executor PD is a service.

---

## 7. capDL / DreggDL — the dual cap-graph instantiation

seL4's **CapDL** is a single declarative description of a whole system's capability
layout — every component, kernel object, and capability one component holds to
another — that a **loader** reads and instantiates at boot. The description is the
source of truth; the running system is its image; the authority structure is
auditable and reproducible off one file. A native dregg OS instantiates **two**
checkable cap-graph specs, one per layer:

- **CapDL** (or the Microkit `.system` assembly, which `dregg.system` already is) —
  the **component** caps: which PD holds which CNode/endpoint/frame/device cap. The
  five-PD partition of §1 *is* this spec; the loader instantiates exactly that object-
  and-capability graph at boot.
- **DreggDL** (`CAPDL-POLYGLOT-DX.md`) — the **cell** caps inside the executor PD: a
  single declarative description of a dregg deployment's federation / factories /
  cells / grants, where each `[[grant]]` row is one `Effect::GrantCapability` edge in
  the authority graph. Reading all `[[grant]]` rows off the file *is* reading the whole
  dregg cap graph — the CapDL property, at the protocol layer. It reuses the existing
  serializable types verbatim (`FactoryDescriptor`, `FactoryCreationParams`, `Effect`,
  `FederationId`); a malformed DreggDL produces turns the executor *rejects*, never an
  unsafe deployment it accepts — DreggDL is a convenience + audit artifact, never a
  trust boundary.

The synthesis: a bootable dregg image carries *both* — a CapDL/`dregg.system` spec for
the component caps, a DreggDL spec for the cell caps — so the deployment is
reproducible and auditable at **both** the kernel and the protocol layer. And DreggDL
pairs with `dregg-userspace-verify` (`check_conservation`, `check_no_amplification`,
`check_wellformed`) to *statically check* the lowered `CallForest` before any turn is
submitted, with the honest static/dynamic boundary (`boundary.rs`) keeping the static
check from masquerading as the executor or the proof. The SturdyRef→badged-endpoint
mapping (§6) is where the two specs *touch*: a DreggDL SturdyRef is revived by the
loader re-installing a badged seL4 cap — one spec naming a cap the other instantiates.
Capabilities, and the descriptions of them, all the way down.

---

## 8. The local↔distributed cap gradation — why `n = 1` is first-class, not a toy

The reason the single-machine seL4 image is *the* product target and not a demo:
`FIRMAMENT.md` §3's central thesis is that **an seL4 capability and a dregg capability
are the same abstraction at two points on a distance parameter `n`** (the number of
machines the cap's target is spread across). Both are unforgeable, attenuable,
delegable references; they differ only in how far the resource is and what bounds hold.
At `n = 1` — everything on one seL4 machine — the distributed bounds **collapse to
strong local properties**: revocation is *immediate* (`seL4_CNode_Revoke` is
synchronous) instead of eventual; checkpoint is a *consistent cut* of one PD instead
of a Chandy–Lamport cut across machines; commit is *synchronous* (one redb transaction)
instead of quorum-latency; agreement is *trivial* (one machine is its own quorum)
instead of FLP-bounded.

This is not just design — it is a runnable crate. `sel4/dregg-firmament/` turns §3 into
code wired to the *real* dregg capability semantics (it path-depends on genuine
`dregg-cell` + `dregg-turn`, so it never reinvents `granted ⊆ held`): one unified
`Capability { target, rights }` handle where `target` is `Local { slot }` (an seL4
CNode slot) or `Distributed { cell }` (a real dregg `CellId`) and `rights` is the real
`AuthRequired` lattice; one `FirmamentRouter` with a `LocalBacking` (mint =
`seL4_CNode_Mint`, revoke = synchronous transitive `seL4_CNode_Revoke`, invoke =
`seL4_Call`) and a `DistributedBacking` (a real `TurnExecutor` over a real `Ledger`);
real attenuation at **both** ends (a widening grant is refused identically — locally via
`is_attenuation`, distributedly via a genuine `Effect::GrantCapability` turn that
returns `DelegationDenied`); and the `n = 1` collapse witnessed at runtime (`Bounds`
carries `revocation_immediate`/`commit_synchronous`/`n`). The acceptance test
(`tests/fluid_reach_out.rs`) drives one backing-agnostic app function through *both* a
local kernel object and a real dregg cell via one router — 10 tests green, the real
executor in the loop.

The product promise (decided, ember 2026-06-13: **both**): a local Robigalia install is
a **first-class** dregg deployment with the strong `n = 1` guarantees as *headline*
properties — AND a **stepping stone** to `n > 1`, never a terminus. The same binary that
runs the local firmament scales out without a rewrite, because there was only ever one
model: the moment a program **reaches out to the network** (invokes a capability whose
target is a cell on a remote federation), the router resolves it through the
executor→net-PD path and the program flows into native distributed dregg **with no seam**
— the same handle, the same attenuate/delegate/invoke verbs, the same receipts; only the
*bounds* relax along `n`. The net PD reaching the wire (§5) is what makes the `n > 1` end
real and not merely designed.

---

## 9. The staged path

The sequencing follows the blockers: the verifier PD is unblocked now; the executor PD
is carried from its one-turn demo to a service; the bootable node image follows.

### Now (boots today)
- **The five-PD assembly boots** (`make run-assembly`): verifier-stark (real STARK
  heart organ) + executor-stub (heart seat) + persist-stub + net (real virtio probe) +
  rbg-dir (the first app-PD). The cap partition is the trust boundary, instantiated.
- **The verified executor has run one turn inside a seL4 PD** (§3) — the heartbeat,
  banked with its residue named.
- **The first real cap port is done** — M2's `DirectoryFactory → seL4_Untyped_Retype`.
- **The cap-gradation bridge is runnable** — `sel4/dregg-firmament/`, 10 tests green.
- **M5** — the whole path boots on riscv64 too (M0 on `qemu_virt_riscv64`: OpenSBI →
  seL4 → userspace → dregg PD).

### Next (the executor PD from demo to service — the headline lever)
- **Wire the crypto floor** — the real Poseidon2/BLAKE3/Ed25519 into the executor PD,
  so crypto-bearing turns run, not only the non-crypto demo wire (§3 residue 1).
- **The service loop** — block on the `net→executor` notification, read the staged turn
  from `turn_in`, run the verified step, stage the commit in `commit_out`, signal persist
  (§3 residue 4). This is the difference between "one turn ran" and "the node runs turns."
- **The runtime-shape decision** (§3 residue 3, a project-lead call): carry the executor
  onto a **Microkit-PD** musl substrate to drop into the `dregg.system` executor seat, or
  ship it as a **root-task** component beside the Microkit assembly (simpler, the demo's
  shape, weaker isolation against the other PDs).
- **The GMP decision** (a project-lead call): full GMP recompiled for ELF (done, portable,
  heavy) vs. a **fixnum-only shim** that stubs the `mpz` path *iff* no turn exceeds 63-bit
  fixnums (needs a kernel numeric-range check) — the shim deletes a whole C dependency.
- **Image shrink** — dead-data GC on the 285 MB image (the heavy olean-derived data), a
  follow-up not a blocker.

### Next (the node's other organs)
- **persist over a raw block cap** (§4) — the device cap lands in the persist PD; redb's
  `StorageBackend` over a block cap; then the PD-checkpoint ↔ dregg-snapshot wiring on the
  already-verified `snapshot.rs` model.
- **The 2-PD net assembly** (§5) — the smoltcp client PD + shared-ring channel + the
  Ed25519 de-envelope boundary, turning "the NIC is up" into "a turn arrives over TCP."
- **A single-node devnet image** — `net → executor → persist` wired, verifier isolated,
  caps partitioned. This is a legitimate milestone on its own: the single-machine principle
  says `n = 1` is the target that collapses the distributed bounds (§8), not a defer-excuse.

### Beyond
- **Multi-node gossip** over the net PD (the `n > 1` end of the gradation, real).
- **A verified FS under persist** (§4.2) and a verified network-driver story — *external*
  verification efforts to adopt, not build.
- **The confined-Servo `renderer` PD** (§1, `EMBEDDED-WEB-SURFACE.md` §5) — research,
  gated on a Servo-on-seL4 port + a GPU/framebuffer-cap story, sequenced behind the
  executor PD.

---

## 10. Honest blocker summary

1. **The executor PD is no longer a wall, but it is not yet a service.** The historical
   "one true blocker" — a libuv-free, IO-free `leanrt` + GMP on musl/seL4 — is **built**,
   and the verified `dregg_exec_full_forest_auth` has **run one real turn inside a seL4
   PD** (`status:2 ok:1`, byte-identical receipt). What remains to make it the
   `dregg.system` heart seat is named, scoped work, not mystery: wire the real crypto
   floor (the demo stubs it), add the turn-stream service loop (the demo runs one turn and
   exits), and decide the runtime shape (root-task today vs. a Microkit-PD musl substrate).
   It does **not** block the verifier PD, which runs real STARK verification today.
2. **No verified FS** — near-term persist is a raw-block redb backend, not a verified
   filesystem; the verified-FS line is external work to adopt.
3. **The net edge probes but does not yet carry turns** — the driver brings the NIC up;
   the smoltcp client PD + 2-PD ring assembly + Ed25519 de-envelope boundary remain (§5).
4. **rbg is heritage, the cap ports are greenfield** — there is no pre-existing seL4
   integration; this is built against the seL4 Rust SDK. The first port
   (`DirectoryFactory → seL4_Untyped_Retype`) is *done* (M2); the rest of the
   `RBG-TO-SEL4.md` mapping (SturdyRef→badged-endpoint, ScopedIntentPool→badged-endpoint)
   is the next additive slice.
5. **The downgrade temptation persists for the executor** — `no-lean-link` makes the node
   build without Lean, but shipping the unverified Rust executor as authoritative is a
   guarantee downgrade; it is bring-up scaffold only. With the Lean turn now booting in a
   PD, the destination is reachable without taking the scaffold as the answer. (For the
   verifier there is no such temptation — it carries no executor authority.)

---

*dregg's thesis is capabilities all the way down, and seL4 is the substrate that makes
the deployment share it: the kernel cap graph isolates the OS components, the dregg cap
graph mediates the cells inside the executor. The assembly boots — five PDs whose cap
partition is the trust boundary, a real STARK verified on-device, a real virtio NIC
brought up, the first factory-creation port made a kernel invariant, and the verified
executor's first turn run inside a protection domain. The historical wall — the Lean
runtime — is through, to a heartbeat; carrying that heartbeat to a service (the crypto
floor, the turn loop, the Microkit-PD shape) is the headline near-term work, named as
work, not claimed as done. A native seL4 dregg OS is the collapsed `n = 1` limit of the
same one model that scales out without a rewrite — first-class locally, fluid to the
wire.*
