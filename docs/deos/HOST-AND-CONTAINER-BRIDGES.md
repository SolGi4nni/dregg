# HOST & CONTAINER BRIDGES — the advanced non-seL4 firmament

*Design/research doc. Present-tense where the substrate it extends is real (the
firmament router, the `(target, rights)` handle, the `HostPd` sandboxed-firmament
backing, the `Confinement` cap→OS-rule mapping); clearly-scoped frontier where it
isn't (the new `Target` kinds, the container cell, the bridge backings). First
principles, no trajectory narrative.*

> Companion docs: `docs/FIRMAMENT.md` (the cap-gradation bridge — the abstraction
> these bridges extend), `docs/DREGG-DESKTOP-OS.md §3` (the sandboxed-firmament
> KEYSTONE this is the *inverse* of), `docs/deos/CROSS-DEVICE-FIRMAMENT.md` (the
> device-distance instance of the same router), `docs/deos/SEL4-PARITY-PLAN.md`
> (the systems gap toward native seL4).
> Companion code: `sel4/dregg-firmament/src/{lib,router,host_pd,sandbox,surface,process_kernel}.rs`,
> `cell/src/capability.rs`.

---

## 0. The one-paragraph thesis

The firmament already says: **an seL4 kernel capability, a dregg federation
capability, and a window are the same abstraction at different points on a
distance parameter `n`** — one `(target, rights)` handle, dispatched by a router
to a backing the app cannot see (`sel4/dregg-firmament/src/lib.rs`). The Phase-0
*sandbox* (`sandbox.rs`) took a forked host PD and **DENIED** it all ambient host
authority: a confined child can `open()` nothing, `socket()` nothing, `execve()`
nothing — its only channel is the firmament Endpoint. The bridges in this doc are
the **GRANT direction of the exact same cap→OS-resource mapping**. A *host bridge*
exposes a specific host-OS resource (a directory, a port, a device, a process) as
a single dregg cap; exercising that cap is a turn that leaves a receipt. A
*container bridge* runs a real OS container (Docker/OCI/podman, or a lighter jail)
as a **cap-confined sub-world** attached to the cap-graph: the container is a
dregg *cell*, its lifecycle (start/stop/exec) is a *turn*, and its resources
(its filesystem, its ports, its stdio) become caps in the graph. Both reuse the
unified `is_attenuation` (`granted ⊆ held`) gate and add **no new authority
model** — only new `Target` kinds backed by new bridge backings. And because the
app holds a backing-agnostic handle, every one of these bridges is a **drop-in**
for the eventual native-seL4 version: same cap, swap the backing from a host-OS
gateway to an seL4 PD/driver.

---

## 1. The substrate we extend (cited, real today)

### 1.1 One handle, one router, swappable backings

`Capability = { target: Target, rights: AuthRequired }` (`lib.rs:300-306`). The
router (`router.rs`) dispatches purely on `target`:

| `Target` variant   | backing                | what an invocation IS                          |
|--------------------|------------------------|------------------------------------------------|
| `Local{slot}`      | `LocalBacking`         | an seL4 CNode/endpoint syscall (or host stub)  |
| `Distributed{cell}`| `DistributedBacking`   | a real `TurnExecutor::execute` turn            |
| `Surface{cell}`    | `SurfaceBacking`       | a present/draw turn (a window IS a cell)        |
| `HostPd{pd}`       | `HostPdBacking`        | a validated round-trip to a confined forked PD |

The app **never branches on the backing** (`lib.rs:27-33`). The only thing that
differs across backings is the returned `Bounds { revocation_immediate,
commit_synchronous, n }` (`lib.rs:375-413`): at `n = 1` everything is
strong-local — immediate revoke, synchronous commit. Adding a bridge means adding
a `Target` arm + a backing; **no app code, no rights model, no router contract
changes.** This is the whole reason the bridges are cheap.

### 1.2 The cap → OS-resource mapping ALREADY EXISTS — as a DENY list

`Confinement` (`sandbox.rs:63-97`) is the seed of the cap→OS map, but pointed at
*subtraction*:

- `endpoint_fds: Vec<RawFd>` — the only fds the child keeps; **every other fd is
  closed** (`close_all_but`, `sandbox.rs:164-178`).
- `read_paths: Vec<String>` — a file-cap → **an SBPL `(allow file-read* (subpath
  "<p>"))` on macOS** (`build_profile`, `sandbox.rs:238-255`) / **a Landlock read
  rule on Linux** (`apply_landlock`, `sandbox.rs:420-452`).
- Network: an *empty net namespace* + seccomp denial of `socket` on Linux; no
  `network*` in the macOS SBPL (`sandbox.rs:308-336, 369-396, 226-234`).

Read that table the other way and it IS the host-bridge spec: **a granted
read-path is a host-file read-cap; a passed socket fd is a host-net cap; a kept
fd is a host-device/handle cap.** The Phase-0 sandbox starts from `(deny default)`
and *grants back exactly the listed resources*. A host bridge is precisely "start
from deny-default, then grant back the resources this specific cap names" — the
confinement and the bridge are **two readings of one mapping**. This is why the
bridge is not a new mechanism: it is `Confinement` used as an allow-list issued
*per cap* instead of *per PD-spawn*.

### 1.3 `HostPd` is the prototype of a "host resource as a cap"

`HostPdBacking` (`host_pd.rs`) already registers a confined child's control
Endpoint under a `HostPdId`, gates invocation on `is_attenuation(held, requested)`
(`host_pd.rs:99-131`), and treats *holding the socket* as *holding the cap* (drop
the Endpoint → the cap is dead, `host_pd.rs:117-122`). A host bridge generalizes
this from "a confined PD over a control socket" to "any host resource over a
mediating gateway."

---

## 2. The HOST BRIDGE — host resources as caps (the GRANT direction)

### 2.1 The principle

A deos app reaches a host file/socket/device/process **only via a host-bridge
cap**. There is no ambient host access (that is exactly what the sandbox removed);
the bridge **re-grants** specific resources, one cap at a time, each exercise a
cap-checked, receipted turn. A cap reads "read this host dir" / "connect to this
host port" / "read this device" / "signal this process group"; it carries
`AuthRequired` rights and attenuates/delegates/revokes through the same gate as
every other dregg cap.

The host bridge is itself a **cap-confined gateway PD** — a small, trusted
firmament component that *is* allowed the host syscalls (it runs un-sandboxed, or
with a broad-but-bounded host profile), and that mediates every app request
against the cap the app presents. The app PD stays confined; only the gateway
touches the host. This is the powerbox pattern: authority enters the cap-world
**only** through the gateway, and only as the caps it mints.

### 2.2 New `Target` kinds

Add to `Target` (`lib.rs:210-252`), each addressed by an opaque
bridge-assigned id (exactly like `HostPdId`, `lib.rs:202-203`):

```rust
pub enum Target {
    Local { slot: u32 },
    Distributed { cell: CellId },
    Surface { cell: CellId },
    HostPd { pd: HostPdId },

    // ── NEW: host-bridge targets ──
    /// A host filesystem subtree the bridge mediates (read and/or write per
    /// rights). Backed by a Landlock rule / SBPL subpath / a passed dir-fd.
    HostFile { node: HostFileId },
    /// A host network endpoint (a bound listener, or permission to connect to a
    /// host:port). Backed by a passed/created socket fd held by the gateway.
    HostSocket { sock: HostSockId },
    /// A host device (a char/block device, a serial port, a camera). Backed by a
    /// passed device fd; rights gate read vs write vs ioctl.
    HostDevice { dev: HostDevId },
    /// A host process (or process group) the bridge supervises. Rights gate
    /// signal / read-stdout / write-stdin / wait. Backed by a pid + pipe fds.
    HostProcess { proc: HostProcId },
}
```

`HostFileId`, `HostSockId`, `HostDevId`, `HostProcId` are opaque newtypes around a
`u64`, monotonic from the gateway — the app names the id, never the host path or
port (the path/port lives in the gateway's registry, the same way `HostPdEntry`
holds the `UnixStream`, `host_pd.rs:37-45`).

### 2.3 The bridge backing

A single `HostBridgeBacking` (sibling of `HostPdBacking` in `FirmamentRouter`,
`router.rs:65-82`) owns a registry per kind:

```rust
pub struct HostBridgeBacking {
    files:   BTreeMap<HostFileId, HostFileEntry>,   // { rights, root: PathBuf, dir_fd }
    sockets: BTreeMap<HostSockId, HostSockEntry>,   // { rights, kind, fd | (host,port) }
    devices: BTreeMap<HostDevId,  HostDevEntry>,    // { rights, dev_fd, allowed_ioctls }
    procs:   BTreeMap<HostProcId, HostProcEntry>,   // { rights, pid, stdin, stdout, stderr }
    next_id: u64,
}
```

`invoke(target, op, rights)` does the same two-step `HostPdBacking::invoke` does
(`host_pd.rs:99-131`):

1. **Cap-check** `is_attenuation(entry.rights, rights)` — refuse if the op's
   required authority exceeds the held cap (`granted ⊆ held`, never reinvented).
2. **Mediate** the op against the host through the gateway's held fd/path:
   - `HostFile` read: `openat(dir_fd, relpath, O_RDONLY)` *scoped under the
     registered root* (path-traversal rejected: a `..` that escapes the root is
     refused before the syscall — the gateway enforces the subtree the cap names,
     exactly as Landlock would).
   - `HostFile` write: gated by the cap carrying a write right; the write is the
     mutating op, so it is the one that **becomes a dregg turn** (see §2.4).
   - `HostSocket` connect/accept/read/write on the held socket fd.
   - `HostDevice` read/write/ioctl, with `ioctl` restricted to the registered
     allow-list (the device-cap's facet).
   - `HostProcess` signal/read-stdout/write-stdin/wait on the held pid + pipes.

Every mediated op returns a `Resolution { backing: Backing::HostBridge, bounds:
Bounds::LOCAL, note }` — strong-local, `n = 1`: a host file lives on this box, so
a revoke (drop the entry / close the fd) is immediate and a write is synchronous,
exactly like `Bounds::LOCAL` (`lib.rs:392-396`).

### 2.4 Reads need no turn; writes ARE turns (the FirmamentFs law)

This is the rule `FirmamentFs` already states for the editor seam
(`deos-zed/src/fs/firmament.rs:11-48`): **a read is authority-checked but does not
mutate state, so it needs no turn; a write/mutation becomes a dregg turn that
leaves a receipt.** The host bridge inherits this exactly:

- `HostFile` read / `HostSocket` recv / `HostDevice` read / `HostProcess`
  read-stdout → a cap-checked mediated syscall; **no turn, no receipt** (it
  changes no sovereign state).
- `HostFile` write / `HostDevice` write / `HostProcess` write-stdin/signal /
  spawning a `HostProcess` → a **turn**: the gateway runs an `Effect` through the
  real `TurnExecutor` (the `SurfaceBacking::delegate` pattern, `surface.rs:24-30`)
  binding *what changed on the host* into the receipt. "deos wrote to the host
  serial port under cap X at time T" becomes an attestable event, not an opaque
  syscall — the same upgrade `FirmamentFs` makes for `save`.

This keeps the receipted-turn cost where it belongs (mutations of authority over
host state) and keeps high-frequency reads cheap.

### 2.5 Minting host caps: the powerbox

A host cap is born only by a deliberate grant — the **powerbox**, the same role
the compositor plays minting a surface (`surface.rs:104-116`). When the user
picks "give this app read access to ~/Documents" (a file-picker, a settings
toggle, an MCP `act`), the gateway:

1. registers a `HostFileEntry { rights: read, root: ~/Documents, dir_fd }`,
2. returns a `HostFileId`,
3. installs `Capability::host_file(id, AuthRequired::None)` into the app cell's
   c-list (`CapabilitySet::grant`, `cell/src/capability.rs:173`).

From there the app attenuates it (read-only → a single subdir), delegates it to a
sub-app (a worker that only needs that one file), and the user revokes it (drop
the entry + close the fd → the cap is dead the instant it returns, `n = 1`). All
through the **existing** `Capability::attenuate` (`lib.rs:358-369`) and
`CapabilitySet::revoke` tombstone path (`capability.rs:335-345`) — nothing
host-specific.

### 2.6 Faceting host caps

The existing `allowed_effects: EffectMask` facet on `CapabilityRef`
(`capability.rs:71`) is the natural carrier for the *operation* facet of a host
cap: a `HostFile` cap faceted to read-only; a `HostDevice` cap faceted to a
specific ioctl set; a `HostProcess` cap faceted to "read stdout but never signal."
`attenuate_faceted` (`capability.rs:414-437`) already enforces facets only ever
*narrow* (bitwise subset) — so a delegated host cap can be cut down to a thinner
slice but never widened. No new faceting machinery.

---

## 3. The CONTAINER BRIDGE — a container as a cap-confined attached world

### 3.1 The principle

Run an OS container as a **cap-confined sub-world attached to the cap-graph**.
This is the membrane-fork idea (`docs/deos/SHARED-FORK-CONSENT.md`,
`MEMBRANE-FORWARDER.md`) realized as a **real OS container** instead of an
in-image fork: a confined sub-world whose boundary is the host's container
isolation (namespaces/cgroups, or a VM on macOS) rather than an seL4 PD boundary.

The cap-graph holds **a cell that represents the container** (the same way a
surface IS a cell, `surface.rs:1-12`). Its *lifecycle is turns*: create / start /
stop / exec / destroy are cap-gated turns that mutate the container cell's state
and leave receipts. Its *resources are caps*: the container's filesystem, its
ports, its stdio, its exec sessions become host-bridge caps (§2) **scoped to that
container's world**. "Attach to the cap-world" means precisely: the container's
resources become caps in the graph, and deos apps interact with the container
**only** through those caps.

### 3.2 The container cell + lifecycle-as-turns

A container is a dregg cell (`Cell`, the same kind `SurfaceBacking::seed_surface`
seeds, `surface.rs:84-102`). Its content substance holds the container's
**declarative spec + observed state**: image ref, the OCI config (mounts, env,
caps, resource limits), the runtime kind, and a status (`Created | Running |
Stopped | Exited(code) | Destroyed`). Lifecycle ops are turns through the real
executor:

| op        | turn (Effect on the container cell)                     | bounds        |
|-----------|--------------------------------------------------------|---------------|
| `create`  | mint the container cell from a spec; status `Created`   | `n=1` sync    |
| `start`   | runtime `start`; status → `Running`; receipt binds pid  | `n=1` sync    |
| `stop`    | runtime `stop/kill`; status → `Stopped`                 | `n=1` sync    |
| `exec`    | runtime `exec`; mints a `HostProcess` cap (§2.2) inside | `n=1` sync    |
| `destroy` | runtime `rm`; status → `Destroyed`; **revokes all** child caps | `n=1` sync |

Each op is cap-gated on the **container-control cap** (a cap over the container
cell, faceted to start/stop/exec/destroy via `EffectMask`). So "who may stop this
container" / "who may exec into it" / "who may only read its logs" is the ordinary
cap question, answered by the ordinary gate. Because the runtime lives on this box,
the bounds are `Bounds::LOCAL` — a `destroy` revoke darkens every child cap the
instant it returns, exactly like a surface revoke darkens the glass
(`surface.rs:50-58`). `n > 1` (a container on another node, reached over the wire)
relaxes the bounds without changing the verbs — the same reach-out as a remote
surface.

### 3.3 The container's resources as caps

When a container is created, the bridge mints (does **not** auto-grant ambient)
caps **scoped to that container's world**, installable into apps via the powerbox:

- **Filesystem**: a `HostFile` cap whose `root` is a bind-mount / volume of the
  container (or the container's rootfs subtree), read or read-write per rights. An
  app editing files "in" the container is editing through this cap — the same
  `FirmamentFs` seam (§2.4), the same receipted writes.
- **Network**: a `HostSocket` cap to a published container port (the bridge holds
  the host-side socket / port-forward; the app connects through the cap). The
  container's own network namespace stays its boundary; the cap is the single
  pinhole.
- **Stdio / exec**: each `exec` mints a `HostProcess` cap (pid + stdin/stdout/
  stderr pipes) — a terminal into the container is a `HostProcess` cap rendered on
  a `Surface` (the deos-terminal surface, recent commit `1d76efd0`, over a
  container-exec cap instead of a host PTY).
- **Logs / events**: a read-only `HostProcess`-stdout-shaped cap over the
  container's log stream.

Every one of these is a §2 host-bridge cap with its `root`/`fd`/`pid` pointing
*into the container's confined world*. The container boundary (namespaces / VM)
is the **outer** confinement; the cap is the **inner** grant. Two readings of one
mapping again, nested one level deeper.

### 3.4 The OS runtimes + Rust crates (the backing's host side)

The container bridge backing speaks to whatever container runtime the host
provides. Per-platform, all behind a `container-bridge` feature (mirroring the
`process-pd-sandbox` cfg-gating, `Cargo.toml`):

- **Linux (native, lightest):** the most "trailblazing-for-seL4" option is a
  direct **OCI runtime** with no daemon — **`youki`** (CNCF-sandbox, Rust,
  OCI-runtime-spec, rootless, cgroups v2, seccomp, the same Landlock/seccomp
  primitives `sandbox.rs` already uses). The bridge writes an OCI `config.json`
  from the container cell's spec and drives `youki create/start/kill/delete`
  directly. This is the cleanest mental model for the seL4 trailblaze: an OCI
  bundle ≈ a confined sub-world spec, the runtime ≈ the thing that instantiates it
  — which is exactly what an seL4 PD-assembly initializer does.
- **Docker / podman (daemon/API, broadest reach):** **`bollard`** (Rust, the
  Docker daemon API; as of the 1.52 moby schema it supports **both Docker and
  podman** as first-class runtimes with rootless-podman socket auto-discovery, and
  API-version negotiation). The bridge talks the engine API: create/start/stop/
  exec/attach/logs/port-bindings all map directly onto the §3.2 turns and §3.3
  caps. `bollard`'s `exec` + `attach` give the stdin/stdout/stderr streams the
  `HostProcess` cap wraps; its port-binding info gives the `HostSocket` cap; its
  bind-mount/volume config gives the `HostFile` cap root.
- **macOS:** Docker/podman are VM-backed (a Linux VM); `bollard` talks to the VM's
  engine socket identically. The native Apple **Containerization** framework
  (per-container lightweight VMs) is the forward path; until a Rust binding exists,
  the bridge uses the engine socket (`bollard`) or shells the `container`/`docker`
  CLI behind the same backing trait. The VM IS the confinement boundary — the cap
  model above is unchanged.
- **Windows:** the Docker engine API (`bollard` over the named-pipe/TCP endpoint);
  HCS/host-compute is the native forward path. Same backing trait.

The key design move: the backing is a **trait** (`ContainerRuntime`) with
`create/start/stop/exec/destroy/mount_cap/port_cap/stdio_cap`. `youki`, `bollard`,
and a CLI-shim are three impls. The router and the cap model never see which —
exactly the `LocalBacking`/`DistributedBacking` split (`lib.rs:88-95`).

### 3.5 Container as the realization of a membrane fork

`SHARED-FORK-CONSENT.md` / the membrane-fork machinery describes a confined
sub-world forked from a parent with a consented boundary. A container bridge is
**that pattern with an OS container as the boundary primitive**: the parent
(the deos image) forks a sub-world (the container), the boundary is enforced by
the host (namespaces/VM) instead of an in-image membrane, and the "stitch back"
is the receipted caps that cross the boundary (a `HostFile` write turn, a
`HostSocket` byte stream). The same consent/attenuation discipline governs what
crosses. This is why the container bridge is not a foreign bolt-on: it is a known
dregg shape (the confined sub-world) given a heavier, real-OS boundary.

---

## 4. How both attach to the cap-graph

```
                       ┌───────────────────────────────────────┐
   deos app PD         │           FirmamentRouter             │
   (confined)          │  resolve(cap) → backing by Target      │
      │ holds          │                                        │
      │ Capability ───►│  Local        → LocalBacking (seL4)    │
      │ {target,rights}│  Distributed  → DistributedBacking     │
      │                │  Surface      → SurfaceBacking         │
      │                │  HostPd       → HostPdBacking          │
      │                │  HostFile/    ┐                        │
      │                │  HostSocket/  ├─► HostBridgeBacking ───┼──► host OS
      │                │  HostDevice/  │   (the gateway PD)     │   (gated syscalls)
      │                │  HostProcess  ┘                        │
      │                │  Container*   ─► ContainerBridge ──────┼──► youki/bollard
      └────────────────┤   (the container cell + child caps)   │    (a confined world)
                       └───────────────────────────────────────┘
```

- A **host cap** is `Capability{ target: HostFile{...}, rights }` in an app's
  c-list; the router sends it to `HostBridgeBacking`; the gateway mediates the
  host syscall against the cap. Attenuate/delegate/revoke = the ordinary cap verbs.
- A **container** is a `Cell` in the graph (a container cell); its control cap is a
  `Distributed{cell}`/`Surface{cell}` cap faceted to lifecycle effects; its
  resource caps are host-bridge caps scoped to the container. A container can be
  delegated (hand a teammate exec-only access), attenuated (read-only logs), and
  revoked (destroy → all child caps die at `n=1`).
- Both ride the **same** `is_attenuation` gate (`capability.rs:603-605`), the same
  tombstone-revoke (`capability.rs:335-345`), the same `Bounds` (`lib.rs:375-413`).

---

## 5. The security model — a bridge is a cap-confined gateway

The non-negotiable invariant: **no ambient host access except what a cap grants.**
This is the *dual* of the sandbox invariant, and it must be enforced with the same
seriousness (`sandbox.rs:37-46`, the trust statement).

1. **App PDs stay confined.** The app process is still the Phase-0
   confined child (`spawn_pd_confined`, `process_kernel.rs:1253`): it cannot
   `open`/`socket`/`execve` directly. The only host authority it has is the caps
   it holds, exercised *through the gateway*. The bridge does not loosen the
   sandbox; it adds a mediated channel.
2. **The gateway is the only host-privileged component** and is small + trusted —
   the TCB grows by exactly the gateway, the way the compositor is "the ONLY new
   TCB" (`lib.rs:97-106`). It mediates **every** request against the presented
   cap; it never exposes a host fd/path/pid the cap does not name. Path-traversal
   out of a `HostFile` root, an ioctl outside a `HostDevice` allow-list, a connect
   to a port the `HostSocket` cap does not cover — all refused **before** the host
   syscall.
3. **Holding the resource IS holding the cap.** As in `HostPdBacking`
   (`host_pd.rs:117-122`), the gateway's held fd/pid/path is load-bearing: revoke
   the cap → the gateway drops the entry and closes the fd → the resource is
   unreachable the instant the revoke returns (`n=1`).
4. **Mutations are receipted.** Every host *write* and every container *lifecycle*
   op is a turn (§2.4, §3.2). The receipt binds what changed on the host/container
   into the verifiable record — so "this app touched this host resource under this
   authority" is attestable, not ambient. (Reads are cap-checked but unreceipted —
   they change no sovereign state.)
5. **Fail-closed.** If the gateway cannot enforce a cap's scope (e.g. it cannot
   resolve the registered root, or a runtime call fails ambiguously), it refuses —
   the `spawn_pd_confined` discipline (`process_kernel.rs:1304-1311`): never run
   the op with broader authority than the cap names.
6. **Honest TCB statement (don't-launder-vacuity).** What this ENFORCES: a confined
   app reaches a host file/port/device/container **only** through a cap the gateway
   mediates; no cap → no access. What remains TRUSTED: the host OS's own isolation
   (Seatbelt/namespaces/the container runtime/the VM) — the *same* trust the MMU
   isolation and the Phase-0 sandbox already place in the host kernel. The bridge
   adds no new cryptographic assumption; it adds a mediating gateway whose
   correctness is the new trusted surface, stated plainly.

---

## 6. How this trailblazes native-seL4-deos

The native seL4 deos is the world where **every resource is natively a cap/PD** —
a file is a cap to a storage-PD, a network endpoint is a cap to the net-PD, a
device is a cap to a driver-PD, a "container" is a cap to a confined PD-assembly.
The host/container bridges are the **drop-in rehearsal** of exactly that, with a
host-OS backing instead of an seL4 backing:

| host/container bridge (now)              | native seL4 deos (later)                  |
|------------------------------------------|-------------------------------------------|
| `Target::HostFile` → gateway mediates a host path | `Target::HostFile` → cap to the storage/VFS-PD |
| `Target::HostSocket` → gateway holds a host socket| `Target::HostSocket` → cap to the net-PD |
| `Target::HostDevice` → gateway holds a device fd  | `Target::HostDevice` → cap to a driver-PD |
| `Target::HostProcess` → gateway supervises a pid  | `Target::HostProcess` → cap to a child PD |
| container = `youki`/`bollard` confined world      | container = an seL4 PD-assembly (a sub-firmament) |
| confinement = Seatbelt/namespaces/VM              | confinement = the seL4 MMU + cap space    |

**The `Target` enum, the `Capability` handle, the `is_attenuation` gate, the
`Bounds`, the powerbox grant, the receipted-write rule, and every line of app code
are UNCHANGED across the two columns.** Only the backing moves — from a host-OS
gateway to an seL4 PD/driver — exactly as the v0→v1 backing swap kept "the PD
source UNCHANGED across both" (`lib.rs:80-85`). An OCI bundle driven by `youki`
*is the same shape* as an seL4 PD-assembly: a declarative spec of a confined world,
instantiated by a runtime. Building the bridges now means the seL4-native version
is a backing swap, not a redesign — and it means deos is **useful on mac/lin/win
today** (it can reach your real files, your real ports, your real containers,
under sovereign caps) while pre-figuring the substrate that makes those caps
native.

---

## 7. Phased plan — smallest first slice → the full fabric

The discipline: each phase ships a real, tested slice that reuses a proven
primitive; no phase is a wall needing a new authority model.

### Phase H0 — the single host-dir read-cap (the smallest real bridge)
The inverse of the Phase-0 sandbox, one resource:
- Add `Target::HostFile{node}` + `HostFileId` to `lib.rs` (unconditional variant,
  like `HostPd`, so the router compiles in every feature combo).
- Add `HostBridgeBacking` with only the `files` registry + a `read` op:
  `openat(dir_fd, relpath, O_RDONLY)` scoped under a registered root, gated by
  `is_attenuation`. Mirror `HostPdBacking::invoke` exactly.
- Router arm + `backing_of`. `Resolution { backing: HostBridge, bounds: LOCAL }`.
- Test (the `host_pd` test shape): register `~/somedir` as a read cap, read a file
  through it, prove a `..` traversal and an unregistered path are **refused**, and
  prove attenuating the cap to a subdir then reading outside it fails.
- **Payoff:** a confined deos app reads one real host directory through one
  sovereign, attenuable, revocable cap. The whole host-bridge thesis, minimal.

### Phase H1 — host writes as turns + the powerbox
- Add the `write` op → routed through the executor as a turn with a receipt (the
  `FirmamentFs.save` shape, `deos-zed/src/fs/firmament.rs:36-48`).
- Wire the powerbox grant path (a file-picker / MCP `act` that mints a `HostFile`
  cap into an app cell). Prove the receipted-write round-trip and revoke-darkens.

### Phase H2 — host sockets + devices + processes
- `Target::HostSocket` (connect to a host:port / accept on a bound listener),
  `Target::HostDevice` (read/write/ioctl with an allow-list), `Target::HostProcess`
  (spawn/signal/stdio). Each a registry + an op set + the cap-check; reads
  unreceipted, mutations as turns. The deos-terminal surface (`1d76efd0`) over a
  `HostProcess` PTY cap is the visible payoff.

### Phase C0 — the container start/stop cell (the smallest real container)
- Add the container `Cell` shape (status + spec in content substance) + a
  `ContainerRuntime` trait with a first impl (`bollard` on the dev mac, talking the
  VM engine socket; `youki` on Linux behind `container-bridge`).
- Lifecycle turns: `create` / `start` / `stop` / `destroy` as cap-gated effects on
  the container cell. Test: create a `hello-world` container cell, start it, read
  its status, stop+destroy it, prove the control cap gates each op and `destroy`
  revokes child caps.
- **Payoff:** a real OS container is a cell in the cap-graph whose lifecycle is
  receipted turns.

### Phase C1 — the container's resources as caps
- On `create`, mint `HostFile` (a volume), `HostSocket` (a published port), and per-
  `exec` `HostProcess` caps scoped to the container's world (§3.3), via the §2
  backing. A deos terminal surface over a container-`exec` cap; the editor's
  `FirmamentFs` mounted on a container volume cap.

### Phase C2 — the full bridge fabric
- The `ContainerRuntime` trait gains the `youki` (Linux native, no daemon) impl and
  the macOS Apple-Containerization path as bindings mature; the gateway PD becomes
  the single host-privileged firmament component, the app PDs all confined.
- Container caps delegate/attenuate across the cap-graph (hand a teammate exec-only
  access; a CI cell with a destroy-on-timeout standing obligation,
  `STANDING-OBLIGATION.md`).
- The seL4-native backing swap (§6): the same `Target` kinds re-backed by
  storage/net/driver/sub-firmament PDs, app code unchanged.

---

## 8. Open questions / honest frontier

- **Gateway TCB minimization.** The gateway is the new trusted host-privileged
  component. Keep it as small as the compositor (`lib.rs:97-106`): pure mediation,
  no policy, no app logic. The smaller it is, the closer the trust statement (§5.6)
  is to the sandbox's.
- **Receipt fidelity for host effects.** A host write's receipt binds *what we
  intended to write*; the host could in principle diverge (a hostile host OS). The
  honest claim is "deos issued this write under this cap at this time," not "the
  host durably stored exactly these bytes" — the latter needs the host to be in the
  trust base (it already is, like the MMU). Document the seam; do not overclaim.
- **macOS native containers.** Apple's Containerization framework (per-container
  light VMs) is the right forward backing; until a Rust binding exists the bridge
  uses the engine socket (`bollard`) or a CLI shim behind the `ContainerRuntime`
  trait — a backing detail, invisible to the cap model.
- **Cross-device container caps (`n > 1`).** A container on another node reached
  over the wire is the `Distributed` reach-out applied to a container cell — the
  `CROSS-DEVICE-FIRMAMENT.md` machinery, bounds relaxed, verbs unchanged. Designed
  for, not built in the first slices.

---

*Sources for the container ecosystem survey: [bollard (docs.rs)](https://docs.rs/bollard),
[fussybeaver/bollard (GitHub)](https://github.com/fussybeaver/bollard),
[youki (crates.io)](https://crates.io/crates/youki),
[youki-dev/youki (GitHub)](https://github.com/youki-dev/youki).*
