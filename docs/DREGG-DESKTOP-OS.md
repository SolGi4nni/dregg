# DREGG-DESKTOP-OS — the dregg-native, distributed, web-forward desktop

*Status: vision + layered architecture + staged roadmap. Honest about
research-vs-near-term. The first build slice is precisely specified at the end.*

> Companion docs: `docs/FIRMAMENT.md` (the cap-gradation bridge this whole OS is
> the visual/interactive extension of), `docs/SEL4-EMBEDDING.md` (the seL4
> substrate), `sel4/dregg-firmament/` (the bridge in code), `starbridge-v2/`
> (the gpui master interface that already embeds the verified executor).

---

## 1. The vision in one breath

**A window is a dregg cell's surface capability.** The whole desktop is the
firmament's one `(target, rights)` handle carried all the way out to pixels,
input, and storage: every desktop resource — a turn, a framebuffer, an input
focus, a window — is an object-capability at some point on a distance parameter
`n`, reached through ONE router, with the *bounds* the only thing that slides.
`n = 1` (one machine) is first-class **and** a stepping stone to distributed:
the collapsed limit (immediate revoke, synchronous present, consistent capture),
never a terminus. We add exactly **one** `Target` variant (`Surface{cell}`),
**one** device-holding protection domain per device seat (the compositor joins
the net-PD and persist-PD as a sibling), and **one** deliberately-tiny
compositor multiplexer — and inherit *everything else* (attenuation, delegation,
revocation, provenance, the n-parametrized bounds, unfoolability) from dregg's
existing, proven capability metatheory. The same cap-first code runs **best on
mac/linux today** through a host-native rust-sel4 facade, and on **real
seL4 later**, byte-for-byte unchanged.

---

## 2. The layered architecture

Eight layers, one model. Each is built by *specializing* a primitive that
already exists (the WELD method — the census says the capability usually already
exists, disconnected; welding beats building). The through-line: *nothing is
invented that the firmament does not already prove.*

```
┌─────────────────────────────────────────────────────────────────────────┐
│ L8  starbridge-v2 — the MASTER INTERFACE (gpui)                            │
│     embeds the verified executor + World + dynamics stream; cipherclerk +  │
│     Cmd-K palette = the secure-attention / trusted-path anchor.            │
│     IS the n=1 robigalia root-OS desktop on mac TODAY (Metal path).        │
├─────────────────────────────────────────────────────────────────────────┤
│ L7  APP CELLS + WEB SURFACES (houyhnhnm, untrusted)                        │
│     every app is a dregg cell; a window is a child surface-cell it birthed │
│     via a surface-factory cap. A servo WebView is one such app confined    │
│     behind ONE surface-cap (the DarpaBrowser story).                      │
├─────────────────────────────────────────────────────────────────────────┤
│ L6  SHELL + WINDOW-MANAGER CELLS (untrusted, client-side handling)         │
│     a window-manager is a compositor-client-cell that is ALSO a compositor │
│     to the apps it frames (Genode recursive stacking, free from            │
│     cells-holding-caps-to-cells). The powerbox lives here.                 │
├─────────────────────────────────────────────────────────────────────────┤
│ L5  THE COMPOSITOR-PD (the new minimal multiplexer — the ONLY new TCB)     │
│     the third device-holding organ: SOLE holder of framebuffer/GPU + HID   │
│     device caps. Models its scene as a verified dregg cell. NO app logic,  │
│     NO widget toolkit, NO placement policy. CPU-composited first.          │
├─────────────────────────────────────────────────────────────────────────┤
│ L4  DEVICE-HOLDING ORGAN PDs (sole-device-cap holders)                     │
│     persist-PD (disk), net-PD (NIC, the n>1 edge), gpu-driver-PD,          │
│     input-driver-PD — each the SOLE holder of one device cap + its         │
│     virtio-mmio region + DMA paddr, cloned from the proven net driver.     │
├─────────────────────────────────────────────────────────────────────────┤
│ L3  THE VERIFIED EXECUTOR-PD (the HEART)                                   │
│     embeds the Lean execFullForestG closure. On the host it links the      │
│     ORDINARY mac/linux Lean runtime (no libuv excision) — a REAL verified  │
│     heart on day one. On seL4 it is the sel4-musl + root-task-with-std     │
│     host of the ELF closure (WALL step 4, the one remaining substrate      │
│     wall).                                                                 │
├─────────────────────────────────────────────────────────────────────────┤
│ L2  THE FIRMAMENT CAP FABRIC  (sel4/dregg-firmament — EXISTS)             │
│     FirmamentRouter over ONE Capability{target,rights}. Target gains its   │
│     THIRD backing: Local{slot} | Distributed{cell} | NEW Surface{cell}.    │
│     All three attenuate/delegate/revoke through the SAME is_attenuation     │
│     (granted⊆held) gate; Bounds carry the n-parametrized collapse.        │
├─────────────────────────────────────────────────────────────────────────┤
│ L1  THE MICROKERNEL SEAM  (the same-code contract)                         │
│     a sel4-microkit API facade (protection_domain!/Handler/Channel/        │
│     MessageInfo/memory_region_symbol!) cfg-selected: std-backed (semihost) │
│     vs no_std-asm-svc (real seL4). A PD's init()+notified/protected bodies │
│     are LITERALLY the same text on both. UML's `um` arch / gVisor platform. │
├─────────────────────────────────────────────────────────────────────────┤
│ L0  TCB FLOOR / HARDWARE                                                   │
│     seL4: microkernel + Microkit monitor + CapDL init (~10kLOC verified C).│
│     host: the semihost EmulatedKernel (std-only, in-process). One          │
│     DreggDL/capDL boot spec instantiates the cap layout for BOTH.         │
└─────────────────────────────────────────────────────────────────────────┘
```

The same binary that runs the local firmament scales to `n > 1` without a
rewrite, because **there was only ever one model — the bounds simply relax along
`n`.** "Web-forward desktop OS" and "distributed object-capability OS" become the
*same statement about pixels.*

---

## 3. The semihosted-seL4 KEYSTONE (the portability fulcrum)

This is the load-bearing decision of the whole plan, and the reason
*best-on-mac/linux-now* is not a compromise but a fulcrum.

**THE ROBIGALIA EMULATOR = a host-native backend for the rust-sel4 API surface,
so ONE PD source tree runs (a) on the host emulator today and (b) on real seL4
unchanged.** The contract (the "port", UML-style) is the `sel4-microkit` API the
dregg PDs *already* code against: the `#[protection_domain]` entry, the `Handler`
trait (`notified`/`protected`/`fault`), `Channel` (`notify`/`pp_call`/`irq_ack`),
`MessageInfo` + the IPC buffer, and `memory_region_symbol!`. Below it sits the
lower seam, `sel4::sys` (the asm `svc` syscall helpers + CNode/Untyped
invocations). The cut is drawn at **both** layers (microkit-facade for app PDs;
a `sel4::sys` backend for the executor/root-task PD) and the backend is selected
by `cfg`, both over ONE `EmulatedKernel`.

**The EmulatedKernel is NOT a from-scratch mock.** It is
`sel4/dregg-firmament/src/local.rs`'s `LocalBacking` — which *already* has a real
CNode slot-table (`BTreeMap<u32, Slot>`) with a mint/revoke derivation tree
(`minted_from`), mint-with-`is_attenuation`, and synchronous-transitive revoke,
all green (`mint_attenuates_and_refuses_amplification`,
`revoke_is_synchronous_and_transitive`) — **PROMOTED** with three additions:

- a synchronous **Endpoint** (rendezvous: a `Call` parks on a condvar until a
  `Recv` arrives — faithful seL4 synchrony), backing `Channel::pp_call`;
- a **Notification** (badge-OR accumulator + condvar wake; `Signal` = badge-OR +
  wake, `Wait` = block-until-nonzero), backing `Channel::notify` and the
  `Notified` event;
- **Untyped + Retype** (a byte/object budget that mints exactly the declared
  object type — the kernel-enforced form of the factory slot-caveat,
  `DirectoryFactory → Untyped_Retype`).

`Channel`s map to emulated Notification/Endpoint caps; `memory_region_symbol!`
maps to host shared buffers (thread: `&mut [u8]`; process: `mmap`/`shm_open`), so
the net-client's smoltcp-over-shared-ring-buffer code runs against host shared
rings **unchanged**. Badges carry the scope/membership/fault discriminator
(matching Microkit's `IS_ENDPOINT`/`IS_FAULT` bits), so the membership-bounded
discovery and factory slot-caveat semantics hold identically.

**THE PAYOFF that makes this the fulcrum:** the verified executor-PD hosts on
the host's *ordinary* macOS/Linux Lean runtime (no libuv excision, no musl port
needed off-seL4), so **the semihost has a REAL verified heart NOW** — the
executor-PD blocker that gates real-seL4 (WALL step 4) does **not** gate the
emulator.

**THE FIDELITY DISCIPLINE (don't-launder-vacuity).** The emulator advertises
`Bounds::LOCAL` and these are *genuinely real* on the host (a host thread's
revoke IS synchronous; a host present IS one map) — it is a **faithful `n = 1`
firmament, NOT a lossy mock.** The cap checks are the *genuine* dregg
attenuation (`is_attenuation`). The ONE deliberate non-fidelity is **honestly
labeled**: host threads (v0) share an address space, so "no ambient authority"
is by-construction-in-the-API, not MMU-enforced. This is *exactly* the gap UML's
traced-thread → SKAS evolution faced, and it is closed by the same fix: the v1
**process-backed-PD upgrade** (`shm_open`/`mmap` regions; an opaque
generation/epoch-tagged cap handle + a kernel-side validity table so a PD can't
forge a cap by writing raw bytes — host RAM has no CHERI tag bits) and ultimately
the real-seL4 target. The acceptance gate for calling the EmulatedKernel
"faithful" is a **differential-against-real-seL4-under-QEMU loop** (the
model-finds-the-bug pattern), not assertion.

**Precedent.** gVisor's Sentry (a faithful re-impl of a privileged ABI in host
userspace with a pluggable *platform*); UML's `um` arch (same-code-targets-both
at one well-defined seam); rust-sel4's own `sel4-musl` (the inverse — it
emulates *Linux* syscalls inside a real seL4 PD via a single
`set_syscall_handler` indirection, which is precisely the seam the semihost
installs at the `sel4::sys` layer). seL4's own CAmkES SIMULATION flag is the
*negative* result that proves the niche is unfilled: it still runs the REAL
verified kernel under full-system QEMU — there is **no** host-native shim of the
cap/IPC surface. The robigalia emulator is genuinely new. dregg's win over
gVisor: dregg already *has* the formal semantics (the executor IS the verified
Lean), so the emulator is a faithful *model* rather than a from-scratch
reimplementation.

**Honest determinism win:** the emulator is the natural place to make the
houyhnhnm clock/RNG a *recorded, replayable* cap-input for free (real
determinism, not the host wall-clock).

---

## 4. The migration path (best-on-mac/linux-now → seL4-native-future)

Five overlapping tracks, each **staged-additive-then-cutover** (the MINTED
pattern — the native thing lands *beside* the old thing, the router cuts traffic
over, the old thing is disabled) — **never a flag-day**.

**TRACK 0 — the SEMIHOST (the fulcrum that unblocks everything).** Ship the
`semihost-kernel` + facade so the SAME PD code (m0-hello, the rbg DirectoryCell,
the net-client smoltcp PD, the compositor-PD) runs under `cargo test` on
mac/linux AND on real seL4, gated by a shared integration test that boots the
same PD set both ways — so the same-code claim is *continuously checked*, not
asserted once. The semihost links the ordinary Lean runtime, so it has the
verified executor on day one (no Lean-port blocker).

**TRACK 1 — the Surface backing (code-first, BEFORE pixels).** The FIRST
milestone (see §8): add `Target::Surface{cell}` to the firmament handle and prove
it composes with the existing capability discipline. Zero pixels, zero drivers,
zero new trust surface.

**TRACK 2 — the native-now compositor.** Generalize starbridge-v2's single gpui
window into a cap-first multi-surface compositor on the host GPU (`gpui_wgpu` is
*already in the lockfile* — backend selection, not a port; the mac Metal path
works today). Render TWO surfaces where the compositor **refuses** to
composite/route-input to a surface whose owner lacks the cap — the
no-amplification guarantee firing at the *pixel* layer, exactly the
teaching-moment pattern the cockpit's "⚠ over-grant" already uses for transfers.
Then add one servo `OffscreenRenderingContext` WebView as a surface-cell.

**TRACK 3 — the Linux compat fulcrum (real-seL4 side; the service-migration
lever).** A libvmm VMM-PD boots an *unmodified* aarch64 Linux/buildroot guest as
a Microkit `<virtual_machine>` beside the executor-PD heart; **day one the VM
owns the devices via emulated virtio backends, so a full Linux userspace (dbus,
drivers, apps) runs immediately** — no Lean-port blocker on the critical path.
Then each device/service is **lifted one-by-one** from in-VM to a native dregg
sDDF driver-PD. The net-PD is *already* an sDDF driver/client pair, so generalize
it: per device class add the canonical trio **driver-PD → virtualiser-PD →
{native dregg client-PD | the VM's virtio backend}**. Extraction order,
easiest/highest-leverage first:

1. **NETWORK** (done-shaped) — the existing net driver-PD becomes the backend for
   BOTH the VM's virtio-net AND native dregg ingress, via a net virtualiser; the
   Linux guest's packets and dregg turns share one NIC.
2. **TIMER** — trivial sDDF class, needed by smoltcp/the executor.
3. **SERIAL/console** — sDDF serial + libvmm virtio-console.
4. **BLOCK/STORAGE** — the persist-PD becomes an sDDF block driver
   (redb-over-raw-block-cap); the VM mounts a virtio-blk backed by it, so guest
   files land in dregg's verified snapshot/overlay store with the root tooth.
5. **INPUT**, then **DISPLAY/framebuffer last** (hardest; the GPU stays in the VM
   longest — webgpu/servo compositing is the eventual native target).

A **dbus → turn bus-broker PD** presents a dbus system-bus endpoint to the VM
(over virtio-serial/vsock); each `(service, client)` pair is a **badged seL4
endpoint** (Genode's pattern) whose badge carries a dregg capability, so a dbus
method-call on a migrated service becomes a `seL4_Call` the broker resolves
`badge → cap → dregg turn` through the executor-PD, returning the receipt as the
dbus reply. So a Linux app calling `org.dregg.Storage.Put` runs a *real
mandate-gated dregg turn*. dbus well-known names map to dregg cells via the rbg
DirectoryCell — the bus's name table IS a dregg c-list. **The non-deterministic
Linux VM is an explicit legacy quarantine OUTSIDE the houyhnhnm boundary;
migrated services LEAVE it as they go native.** Architectural existence proof:
LionsOS/Kitty (au-ts) — *the firmament's target shape with the executor/cell
layer swapped in*.

> **The semihost shortcut.** On the mac/linux host the compat VM may be **skipped
> entirely** — the host OS *is* the compat layer, so the semihost simply runs the
> dregg PDs natively. The libvmm VM is meaningful mainly on *real* seL4.

**TRACK 4 — the seL4 substrate ladder (the verified destination).** A five-stage
ladder, each a real QEMU boot extending the prior (see §6 R3). The honest
framing: **display + HID are inherently-LOCAL (`n = 1`) seats — the desktop is
the `n = 1` collapse made visible** — while net is the only seat that slides
along `n`. The same binaries scale from the semihost to the seL4 image.

---

## 5. The verified-graphics / trusted-path NORTH STAR (the most research-y facet)

**THE CORE REFRAME: output-integrity IS unfoolability applied to the display
path.** dregg already proves (`AssuranceCase.lean` `unfoolability_guarantee`)
that a light client checking only `verify root = true` learns the whole history
evolved correctly — it cannot be fooled by *the pale ghost* (a server lying about
protocol state). The verified-graphics facet asks the SAME question one hop
further out: **can the HUMAN at the glass be fooled?** The pale ghost on the
display is a UI that paints pixels claiming "cell C holds balance B / you are
signing transfer T" when C does not, OR steals the keystroke meant for C and
routes it to attacker A. So the property is two anti-ghost teeth on the I/O
boundary: *(output)* every surface region is the genuine projection of its owning
cell's verified post-state; *(input)* every input event is delivered only to the
cell the user demonstrably chose.

**The compositor is a verified dregg cell.** Its state IS the scene graph — an
ordered list of surfaces, each `(owningCellId, regionRect, contentDigest,
sourceStateRoot, zLayer, focusFlag)`. Compositing is a TURN: a cell submits
`present(region, contentDigest @ myStateRoot)` against the compositor cell, and
the executor's caveat gate enforces the security invariants AS anti-ghost teeth
via the EXISTING `EffectCommit`/`VerificationToolkit` machinery (the SAME way 45+
effects were welded — `app_commit_iff_admit` + `app_violation_rejected` come for
free):

- **T1 NON-OVERLAP** — a cell writes only regions its capability authorizes;
  `granted ⊆ held` with `Rights = region-set` on the SAME `is_attenuation`
  lattice the firmament uses; overpainting another cell's region is **UNSAT**.
- **T2 LABEL-BINDING** — every surface's rendered label is a *function* of its
  `owningCellId` + `sourceStateRoot` (read by the compositor from cell state,
  NOT the app — the executor knows the authority lineage: which factory minted
  it, sovereign-vs-hosted, attenuation depth, all unforgeable by the client); a
  label ≠ owner is **UNSAT**. This is Nitpicker's floating label **upgraded** from
  a server courtesy to a verified *state-root binding a light client can
  independently check* — richer than Qubes' flat color border because dregg
  authority is a structured provenance lattice.
- **T3 FOCUS-EXCLUSIVITY** — at-most-one `focusFlag`; input routes only to it;
  delivering input to a non-focused cell, or two focus flags, is **UNSAT** (EROS
  *traceability of volition* as a state invariant — only the USER selects focus,
  the input analogue of "only connectivity begets connectivity").
- **T4 NO-INFERENCE** — `present()` reads only its own region's prior contents (a
  cap-scoped read; double-buffered shared surfaces kill the display covert
  channel, per EWS — feeds info-flow pillar #31).

The compositor cell's state-root then commits the WHOLE scene; the existing
`state_root()` / `Ledger::root` tooth applies unchanged, so *the scene the user
sees* inherits the same root-binding + conservation story as the ledger.

**THE TRUSTED PATH = SAK + the verified label overlay.** The one thing that
cannot be a normal cell is the secure-attention gesture: a tiny trusted-path PD
(or the root task) holds the SOLE input cap and the SOLE top-`zLayer` surface
cap. A reserved gesture (seL4: a kernel-routed key combo via the trusted PD's
exclusive keyboard-IRQ cap; semihost: a reserved host chord) suspends normal
input and draws an unspoofable overlay — at a `zLayer` no cell holds a cap to
(T1) — showing, for the focused surface, the genuine `(owningCellId,
sourceStateRoot)` read straight from compositor-cell state, NOT from the app.
**This is the cipherclerk / Cmd-K palette in starbridge-v2 promoted to a trust
anchor:** "who am I really talking to, and is its state-root the one my light
client verified?"

**ATTESTED USER-VOLITION.** When a gesture in a trusted surface authorizes a
value-moving turn ("sign this" in the cipherclerk), the compositor-PD emits a
*signed input-receipt* the executor-PD can require as a turn premise (EWS
volition via dregg's existing attestation/receipt machinery, mirroring the
net-PD's Ed25519 pre-check). The receipt commits to `(surface CellId + gesture +
nonce + which turn-field it authorizes)` to defeat replay/confusion; the
compositor holds only an *attestation key* and the executor checks a signature —
the compositor **never** becomes a second authority over state. **A value-moving
turn can require proof a real user clicked.**

**What's verifiable NOW vs the FRONTIER.** NOW (pure Lean + the existing toolkit,
zero new axioms, runnable in starbridge-v2's embedded executor and the semihost):
the scene-graph invariants T1–T4 as anti-ghost teeth via a `VerificationToolkit`
`AppSpec` whose admit-predicate is the conjunction. This is a real
verified-by-construction result. FRONTIER (named hardware-trust assumptions — the
honest seams, *severe-problems-with-closure-lanes, never walls*):

- **F1 — the LAST HOP.** Binding the *scanned-out framebuffer* to the cell's
  `contentDigest` requires either a verified display driver that *hashes what it
  scans out* (a frame attestation: "panel showed digest D for region R") or trust
  in the GPU. With an untrusted DMA-capable GPU this is a named assumption
  exactly as sDDF flags IOMMU as unverified.
- **F2 — IOMMU/DMA confinement.** A display/GPU PD doing DMA can scribble
  arbitrary framebuffer regions unless an IOMMU cap confines it to its granted
  regions; seL4 does not yet verify SystemMMU translation, so "T1 holds against a
  malicious driver" is currently an **assumption, not a theorem** — *this is THE
  crypto-floor-equivalent named primitive for graphics.*
- **F3 — verified GPU/servo/webgpu compositing.** Out of reach; the honest
  near-term stance is a **software compositor cell** (CPU blit, à la
  EROS/Nitpicker) where T1–T4 are *real*, with GPU acceleration as an explicitly
  *trusted* fast path: a SEPARATE untrusted render-PD whose output is itself a
  frame-cap the compositor composites (preserves the trust model, bounds
  performance). NEVER launder F1/F2 as solved.

Direct lineage: EROS Trusted Window System (EWS, Shapiro et al. 2004 — "user
volition is traceable," the input-side dual of output-integrity) and Nitpicker
(Feske & Helmuth 2005 — the ~1,500-LOC existence proof that a trusted-path
compositor TCB can be small enough to verify). The boundary is honest: the
compositor mediates *authority* (verified); the *pixels* it produces are not
covered by the executor's proof — a thin untrusted renderer (CapDesk-style) that
can be malicious without harming confined apps because it holds only the granted
facets.

---

## 6. The staged roadmap (R0..Rn)

Each stage names its **first concrete milestone** and is honest about
research-vs-near-term.

### R0 — THE KEYSTONE: `Target::Surface{cell}` (days; near-term) ← START HERE

Add the Surface backing to `sel4/dregg-firmament` and prove it composes with the
existing capability discipline, BEFORE any pixels. **This is the
transfer-triangle-equivalent for the desktop** (see §8 for the precise spec). It
validates the design's central claim — *a surface is just another point on the
distance parameter* — the SAME way the executor-state bridge (#180) and the
channels weld (#181) validated theirs: one green test against the REAL executor
in the loop. **Companion (same breath, Lean):** a `Compositor` `AppSpec` via the
existing `VerificationToolkit` (admit-predicate = T1 ∧ T3 ∧ label==owner) so
`app_commit_iff_admit` + `app_violation_rejected` come for free, with `#guard`
teeth that BITE (overpaint REJECTS, label-spoof REJECTS, double-focus REJECTS) —
making "output-integrity = unfoolability on the scene" a theorem the same day,
axiom-clean.

### R1 — THE n=1 DESKTOP ON THE HARDWARE YOU HAVE (weeks; near-term)

- Promote `LocalBacking → EmulatedKernel` (+ Endpoint/Notification/Untyped) and
  ship the `sel4-microkit` facade; boot **m0-hello + a 2-PD notify slice + the
  rbg DirectoryCell** on the host emulator via `cargo test` — no QEMU, no
  nightly, no build-std.
- In parallel, in **starbridge-v2** build the verified surface loop: a "surface"
  `FactoryDescriptor`, a surface `EffectMask` facet, `present()` as a real turn
  with the anti-ghost tooth (a non-attenuating grant REJECTS; an
  overpaint/label-spoof/double-focus REJECTS), a `SurfaceDamaged` `WorldEvent` on
  the dynamics stream, and a gpui panel rendering it — *the transfer-triangle for
  the desktop, on mac Metal TODAY.* The verified executor hosts on the ordinary
  host Lean runtime here, so the heart is REAL immediately. (starbridge-v2's
  `surface.rs`/`dynamics.rs`/`world.rs` already exist in-tree.)

### R2 — THE NATIVE-NOW COMPOSITOR + ONE WEB SURFACE (weeks; near-term)

- Generalize the single gpui window into a cap-first multi-surface compositor
  (`gpui_wgpu` already in the lock — backend selection, mac Metal works today).
- Add one servo `OffscreenRenderingContext` WebView bound 1:1 to a surface-cell
  (the DarpaBrowser confinement story). *(Servo's heft is a deferrable backend
  choice — see §7 risks; the SurfaceCell seam is renderer-agnostic.)*

### R3 — THE SERVICE FULCRUM + REAL seL4 SUBSTRATE (weeks-months; mixed)

The five-stage seL4 ladder (TRACK 4), interleaved with the Linux compat fulcrum
(TRACK 3):

- **Stage A** — host the verified executor on `sel4-musl` + `root-task-with-std`
  (**WALL step 4, the single highest-value seL4 build outstanding**; steps 1–3
  GREEN: ELF closure, ELF leanrt+lib+kernel, real GMP 6.3.0; a real turn already
  runs on aarch64-linux-musl, status:2). Swap `dregg-executor-stub-pd` in
  `dregg.system`. This is a *characterized* port (a syscall-trace enumerates the
  exact `brk`/`mmap`/`futex`/`writev`/`clock` set), NOT open-ended research.
- **Stage B** — close the net edge to a full TCP→turn round-trip
  (net-PD → executor-PD → persist-PD); the `n > 1` end real end-to-end.
- **Stage C** — gpu-driver-PD + input-driver-PD cloned from the net driver
  (`virtio-drivers 0.13.0` already pins VirtIOGpu/VirtIOInput with the sel4
  hal-impl — a WELD not a build; 2D framebuffer scanout first; **ramfb** the
  de-risked fallback display). De-risk: bring each up STANDALONE (its own one-PD
  `.system`, like `run-net`) before assembly.
- **Stage D** — the compositor-PD owns the framebuffer + the gpu/input PP
  channels; window lifecycle IS cap mint/attenuate/revoke via the firmament's
  `LocalBacking` (`seL4_CNode_Mint`/`Revoke`, n=1 immediate). Two app-PDs
  composite to screen, input routes to the focused one (banscii artist's
  `region_in → composite → region_out → flush`, generalized).
- **Stage E** — the bootable `dregg.system` desktop: `make run-desktop` opens a
  QEMU window where a verified turn's result appears on-screen, driven by real
  keyboard/mouse. The cap partition is the whole trust boundary: only gpu-driver
  holds the GPU cap, only input-driver the HID cap, only persist storage, only
  net the NIC, only the executor authority over state.

Concurrently the **service migration** (TRACK 3): boot the libvmm `simple` Linux
guest as `sel4/dregg-pd/vmm/`; wire its virtio-net backend to the already-booting
net-driver-PD via a net-virtualiser (a `curl` from inside the VM egresses through
the dregg-owned NIC); then the dbus→turn bus-broker; then extract services LEFT
one at a time.

### R4 — THE APEX: VERIFIED GRAPHICS / GPU / SERVO (beyond-a-quarter; research)

- Adopt `gpui_wgpu` as the canonical renderer spanning Metal / Vulkan / WebGPU /
  Vulkan-on-virtio-gpu; servo WebViews as confined surface-cells; the GPU stays
  in an **untrusted render-PD** whose output is a frame-cap (T1–T4 stay real on
  the CPU compositor).
- The remote (`n > 1`) surface: a remote app's window composited locally over the
  net-PD. DETERMINISTIC content ships STATE not pixels (the Croquet lesson —
  dregg *proves* the determinism Croquet trusts; the state-root tooth makes the
  embedded remote surface SELF-ATTESTING, dregg's novel answer to Arcan's "no
  visual identity to safely forward"); OPAQUE content ships a content-commitment
  + bytes over the net-PD ring (Arcan A12 / waypipe).
- The eventual "native verified graphics driver" is a verified
  virtio-gpu/DRM-KMS driver-PD — the GPU analogue of the verified-FS line, an
  external adoption at the apex of the ladder. Real silicon is gated on this.

**Platform ladder.** aarch64 QEMU virt is the primary rung (R0–R3 land here);
riscv64 already boots M0/M5 (the arch-agnostic PDs port by retarget).

---

## 7. Where it all fits — and what's already DONE

### Already DONE (the foundation this builds on)

- **THE FIRMAMENT** (`sel4/dregg-firmament/`) — the cap-gradation bridge in
  CODE: ONE `Capability{target,rights}` handle, `Target = Local{slot} |
  Distributed{cell}`, a `FirmamentRouter` that dispatches by target alone, the
  `LocalBacking` (real CNode slot-table + mint/revoke derivation tree) and the
  `DistributedBacking` (a GENUINE `dregg_turn::TurnExecutor` over a real
  `dregg_cell::Ledger` — a widening grant is rejected with `DelegationDenied`,
  byte-for-byte the deployed semantics), the `Bounds` n-parametrized collapse,
  and the green tests (`attenuate_is_backing_agnostic_and_uses_real_check`,
  `n_equals_one_collapse`, `real_executor_enforces_attenuation_on_delegate`,
  `real_executor_rejects_amplifying_delegate`). **This is the proven bridge the
  Surface backing rides — Surface is the third point on the distance parameter.**
- **THE VERIFIED EXECUTOR RUNS NATIVELY** — the Lean `execFullForestG` closure
  recompiled to ELF + linked against an ELF Lean runtime built from lean4 source;
  it runs a real turn on aarch64-linux-musl (status:2 accepted, nonce 7→8, a
  transfer applied, anti-ghost holds; WALL steps 1–3 green). Remaining: host it
  on the seL4 root-task-with-std substrate (WALL step 4).
- **NET** — a virtio-net driver PD + a smoltcp net-client PD boot on seL4/QEMU
  (real bidirectional wire, pcap-proven; DHCP + TCP:5555 + an Ed25519 SignedTurn
  gate). **The net-PD is the template every new device PD clones, and the
  already-sDDF-shaped driver/client pair the migration spine generalizes.**
- **starbridge-v2** — a gpui-based master interface that EMBEDS the real verified
  executor (cipherclerk + a Cmd-K palette + debugger/replay/objects). Its
  `surface.rs`/`shell.rs` cap-first window manager runs on the REAL
  `dregg_firmament` surface cap (`SurfaceCapability` IS a
  `Capability{ Surface(cell), rights }` over a real `SurfaceBacking`; every
  window op resolves through `granted ⊆ held`, and a widening window-share is
  rejected by the real executor — the divergence below is CLOSED); its
  `dynamics.rs` already emits a `WorldEvent` stream with `since(cursor)`; its
  `world.rs` embeds a real `World` over a real `TurnExecutor`. **It IS the n=1
  robigalia root-OS desktop on mac today.**

### How the pieces fit

- The **executor-PD** is L3, the heart — *every* authority decision, *every* cap
  mint/attenuate/revoke, IS a turn here. On the host it links the ordinary Lean
  runtime (R1); on seL4 it is WALL step 4 (R3 Stage A).
- The **firmament** is L2 — the one router; the desktop adds exactly one `Target`
  variant to it (R0).
- The **net-client PD** is the `n > 1` edge (L4) — the only seat that slides
  along `n`; it closes to a full turn round-trip at R3 Stage B and carries the
  remote surface at R4.
- **starbridge-v2** is L8 — the master interface that is *both* the native-now
  compositor (R1/R2) and the eventual seL4-native compositor target's gpui face;
  its cipherclerk/palette is the SAK trust anchor (§5).

### The latent divergence is CLOSED — one surface-cap model

starbridge-v2's `SurfaceCapability` IS the real `dregg_firmament`
`Capability{ target: Surface(cell), rights }` (`starbridge-v2/src/surface.rs`).
There is no parallel bearer-secret model: the shell
(`starbridge-v2/src/shell.rs`) owns a real `dregg_firmament::SurfaceBacking` (a
genuine `dregg_cell::Ledger` + `dregg_turn::TurnExecutor`), and **every window
op — focus / raise / move / resize / minimize / close / share — authenticates
by resolving the presented cap through the firmament's `granted ⊆ held`
(`is_attenuation`) gate** (`Shell::authorize` → `SurfaceBacking::invoke`), not a
secret match. Window authority is exactly holding the real `Capability` over the
surface's backing cell; attenuating/delegating/revoking the window is
attenuating/delegating/revoking that cap.

A window-**share** (`Shell::share`) is a GENUINE `Effect::GrantCapability` turn
through the real executor, so a **WIDENING share is REJECTED** with
`DelegationDenied` at the window-manager layer — the no-amplification guarantee
firing at the desktop (test:
`shell::tests::a_narrowing_window_share_commits_and_a_widening_share_rejects`,
mirroring the firmament's own `real_executor_rejects_widening_surface_share`).
The cockpit surfaces this as a teaching moment (the `⚠ over-share` verb / the
`Shell: over-share` palette command), exactly as the composer's `⚠ over-grant`
does for transfers. The surface module's discipline is preserved: NO mock
surfaces, and the trusted-path identity label is the shell's, drawn from the
live world ledger (the §5 T2 property), never the surface's self-description —
authority is the firmament cap-graph, identity is the live world; two ledgers,
two distinct roles. This was the natural R1 starbridge-v2 weld, landed on R0.

---

## 8. THE FIRST BUILD SLICE (precise)

> **Synthesis verdict.** All three architecture lenses (Genode/Nitpicker,
> Fuchsia/Zircon, dregg-first-principles) independently converge on the *same*
> first slice with self-scores 9/9/9. That convergence is itself the signal:
> this is the load-bearing keystone, and it is *code-first, before pixels, before
> drivers, with zero new trust surface.*

**Crate:** `sel4/dregg-firmament` (the existing standalone workspace —
path-depends on the real `dregg-cell`/`dregg-turn`/`dregg-types`, builds into its
own target dir; it never reinvents `granted ⊆ held`).

**Goal:** make "a window = a dregg cell's surface capability" REAL and
load-bearing — a surface cap that attenuates/delegates/revokes through the SAME
`is_attenuation` gate and the SAME `TurnExecutor` as every other dregg cap, with
the `n = 1` bounds collapse proven for PRESENT/REVOKE. This is the smallest
change that validates the whole design's central claim, reusing the firmament's
proven bridge, **before a single pixel or device driver.**

**Files:**

1. **`src/lib.rs`** — extend the handle (the file is ~280 lines; the two-variant
   `Target` is at `lib.rs:77`):
   - Add a third variant to `Target`:
     `Surface { cell: CellId }`, mirroring `Distributed { cell }` exactly.
   - Add `Capability::surface(cell, rights)` (mirroring `Capability::local` /
     `Capability::distributed`) and `Target::surface(cell)` / `Target::is_surface()`
     (mirroring `Target::local` / `Target::is_local`).
   - `Capability::attenuate` already works for any target (it gates on
     `is_attenuation` and clones `self.target`), so a surface cap narrows by the
     real lattice *with no change* — verify this in a test, do not special-case
     it.

2. **`src/surface.rs`** (NEW) — a `SurfaceBacking` module mirroring
   `DistributedBacking` (it path-depends on the genuine `dregg-cell`/`dregg-turn`,
   like `distributed.rs` does — NOT a parallel model):
   - Holds a real `dregg_cell::Ledger` + a real `dregg_turn::TurnExecutor` (reuse
     `DistributedBacking`'s `seed_cell`/`install` shape).
   - `invoke(holder, surface_cell, rights)` — resolves the surface cap against
     real cell-state via the REAL `is_attenuation` (`requested ⊆ held`), returning
     a `Resolution { backing: …, bounds: Bounds::distributed(n) /* = LOCAL at
     n=1 */, note }`. (For the surface op-set, `invoke` stands in for
     PRESENT/EMBED/GRANT-INPUT/REVOKE as the resolution against authority; the
     full op verbs land at R3 Stage D.)
   - `delegate(granter, recipient, surface_cell, narrower)` — runs a GENUINE
     `Effect::GrantCapability` turn through `TurnExecutor::execute`, so a surface
     cap delegates through the real executor's attenuation gate and a **widening
     grant is rejected with `DelegationDenied`** — identical to
     `DistributedBacking::delegate`.
   - Add a third `Backing` discriminant is **not** required (Surface resolves via
     the same real-turn path as Distributed); reuse `Backing::DistributedTurn`, or
     add `Backing::SurfaceTurn` if a test wants to distinguish — keep it minimal.

3. **`src/router.rs`** — wire the third arm:
   - `FirmamentRouter::resolve`: add a `Target::Surface { cell } =>` arm
     dispatching to the `SurfaceBacking` (exactly as the `Distributed` arm
     dispatches to `DistributedBacking`).
   - `FirmamentRouter::attenuate_and_grant`: add the matching `Surface` arm (the
     backing-agnostic `cap.attenuate(...)` pre-check already runs first; the arm
     calls `surface.delegate(...)`).
   - Add the `SurfaceBacking` field to `FirmamentRouter` (or compose it; mirror
     the `distributed` field).

4. **`tests/fluid_reach_out.rs`** (EXTEND the existing integration test) — add two
   tests, mirroring the in-tree `handle_tests`:
   - **`surface_attenuate_is_backing_agnostic`** — a `Surface` handle narrows by
     the REAL `AuthRequired` lattice: `Either → Signature` succeeds; `Signature →
     Either` is **REJECTED** by the real executor identically to the
     local/distributed cases (`real_executor_rejects_amplifying_delegate` is the
     template). Assert the narrowed handle keeps the SAME `Surface` target — only
     rights moved.
   - **`surface_n_equals_one_collapse`** — PRESENT/REVOKE collapse to
     immediate/synchronous at `n = 1`: assert the surface `Resolution.bounds ==
     Bounds::LOCAL` (`revocation_immediate && commit_synchronous`), and that at
     `n > 1` the bounds relax (`revocation_immediate == false`) while the VERBS are
     unchanged — REVOKE is `seL4_CNode_Revoke`-synchronous at n=1 (the window goes
     dark instantly).

**What it must demonstrate (the acceptance bar):**

1. A `Capability { target: Surface(cell), rights }` is constructed, invoked,
   attenuated, and delegated through the SAME `is_attenuation` (granted ⊆ held)
   gate and the SAME real `TurnExecutor` as every other dregg cap — *not a
   parallel model.*
2. A **widening** surface grant is **rejected** by the real executor
   (`DelegationDenied`), byte-for-byte the deployed attenuation semantics.
3. The `n = 1` bounds collapse holds for the surface op-set: PRESENT/REVOKE are
   immediate/synchronous (`Bounds::LOCAL`); at `n > 1` the bounds relax and the
   verbs are unchanged.
4. `cargo test` green in the standalone workspace (via `./run-test.sh`) — **no
   QEMU, no nightly, no seL4, no pixels, no device drivers.**

**Why this is first:** it is the *smallest* change that makes the design's
central claim — *a surface is just another point on the distance parameter* —
real and load-bearing in code, reusing the firmament's proven bridge with **zero
new trust surface and zero device drivers**, validated by one green test against
the REAL executor exactly the way the executor-state bridge (#180) and the
channels weld (#181) validated theirs. Only *after* R0 is green do you build the
compositor-PD multiplexer + frame-cap mapping + trusted-chrome renderer on top
(R3 Stage D), and the starbridge-v2 surface-loop demo + the `SurfaceCapability`
rebase (R1) on the side.

---

*The desktop is the firmament made visual and interactive. We do not invent a
windowing model; we carry the one capability handle out to the glass, hold every
seam to one worthwhile semantics, and label the frontier (F1/F2/F3 — the graphics
crypto-floor) as severe-problems-with-closure-lanes, never walls. n=1 is
first-class today; the same binary reaches the wire tomorrow with only the bounds
relaxed.*
