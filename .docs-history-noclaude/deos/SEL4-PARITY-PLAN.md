# seL4 ↔ native PARITY — the systems plan toward "the deos image does what native does"

The native deos image (`starbridge-v2`) is a live, inspectable, mutable Pharo-style
desktop over real dregg cells. The seL4 deos image (`make run-image`) is a live,
navigable, on-glass object browser of the SAME real cells. This doc maps, against
the real code at HEAD, the gap between them as a **systems** question — pixels,
input, in-VM turns, durability, networking — and gives the ordered plan to close it.

It is INDEPENDENT of the stratified-fixpoint / incremental-projection question
(`docs/deos/REFLEXIVE-MIGRATION.md` §2, `STRATIFIED-FIXPOINT.md`): that is the
native efficiency/reflexivity track. This is the device track. They meet only at
the very end (the gpui↔framebuffer Mode, §3), kept-in-mind-but-later.

The discipline throughout: every gap is named WITH what it reuses (a proven
rbg/Microkit/virtio primitive or the proven two-PD `net.system` topology) versus the
genuinely-new device plumbing. No gap is a wall that needs a new kernel primitive.

---

## 1. CURRENT STATE (cited)

### 1.1 What BOOTS and RENDERS on device today

The deos-image PD boots, configures ramfb, and paints REAL cells on glass:

- **The display PD.** `deos-image.system:72-94` assembles ONE protection domain,
  `deos_image`, the sole holder of three caps and nothing else: the fw_cfg engine
  MMIO window (`fwcfg_mmio`, phys `0x9020000`), a 4 MiB DMA framebuffer
  (`fb_dma`, huge-page-backed so `region_paddr` is one contiguous 4 MiB run,
  `:50`/`:77-78`), and the virtio-keyboard's mmio/DMA/IRQ (slot 30, IRQ 78,
  `:60-93`). seL4 faults any stray access — the cap partition IS the trust boundary.
- **Bytes → glass.** `fb.rs` drives QEMU's `ramfb` standalone display over the
  fw_cfg DMA protocol; `Canvas` is a `&'static mut [u32]` over the mapped
  framebuffer at `800×600` XRGB8888. Re-mapping is cheap and idempotent — every
  repaint calls `unsafe { Canvas::map() }` afresh (`main.rs:93-99`). This is the
  same fw_cfg/ramfb path the `compositor-fb` PD first proved.
- **The live object browser (`Mode::Image`).** `view::draw` paints the cell rail +
  focused-cell inspector from `image_data::IMAGE` — real baked `dregg_cell`
  snapshots (real `CellId::derive_raw` ids, signed balances, c-lists, fields,
  `state_commitment()`), `@generated` by the host `gen_image_snapshot` example.
  The PD is `#![no_std]` and cannot link std `dregg-cell`, so the cells are
  computed at build time and embedded (`main.rs:27-33`).
- **The baked cockpit frame (`Mode::Cockpit`).** `cockpit_frame::blit`
  (`main.rs:97`) copies the **baked** `COCKPIT_RGBA` (`include_bytes!`, exactly
  `800*600*4 = 1_920_000` bytes) into the framebuffer, RGBA8→XRGB8888 per pixel.
  That RGBA is the REAL gpui `cockpit::Cockpit` element tree, rendered HEADLESS
  off-VM (`starbridge-v2 --render-cockpit` over `gpui::HeadlessAppContext` +
  offscreen wgpu on lavapipe) and embedded — landed in `d92d0526c` ("the LIVE
  cockpit element tree renders on the seL4 framebuffer"). A `#![no_std]` PD cannot
  link wgpu, so the heavy render runs at build time, exactly as `image_data`
  bakes cells.
- **The artifacts are fresh.** `build/deos-image.img` (5.0 MB) and
  `dregg-deos-image-pd.elf` (2.06 MB) are built; Microkit SDK 2.2.0 and
  `qemu-system-aarch64` present. `make run-image` boots the interactive
  keyboard-driven viewer.

### 1.2 Input: ALREADY wired (for image mode), DISCARDED in cockpit mode

This is the key not-greenfield finding (`SEL4-INTERACTIVE-COCKPIT.md` §1.3):

- **The virtio-keyboard path is complete and booting.** `keyboard.rs` is a real
  `virtio_drivers::device::input::VirtIOInput` driver using the SAME `HalImpl` +
  device-cap discipline as the net-driver PD. `init()` probes slot 30; `drain()`
  reads Linux evdev `{event_type, code, value}` events and folds them to a `Nav`
  (`keyboard.rs:114-131`). `make run-image` supplies
  `-device virtio-keyboard-device,bus=virtio-mmio-bus.30` (`Makefile:355`).
- **The loop closes.** `Handler::notified` (`main.rs:200-207`): keyboard IRQ →
  `keyboard::drain` → `Viewer::apply(nav)` → repaint-on-change → `KBD.irq_ack()`
  to re-arm. `apply` (`main.rs:103-192`) is the navigation state machine; it
  repaints only on a real transition (`:173-190`).
- **The discard.** In cockpit mode all navigation is INERT — `main.rs:123`
  (`if self.mode == Mode::Cockpit { return false; }`); only TAB
  (`Nav::Toggle`, handled by the early return at `:106`) leaves it. The cockpit
  is a single static baked frame with no input forwarding and no pointer device.

### 1.3 The executor PD: runs a REAL turn, but disconnected

- `executor-pd/src/main.rs` boots and runs ONE real verified turn through
  `dregg_exec_full_forest_auth` → `status:2 ok:1` (nonce 7→8, a 30-unit transfer,
  nullifier + commitment, `main.rs:46-52`). The Lean-runtime wall is PASSED — it
  is a static aarch64-musl image, 0 undefined; what remains is productionization,
  not a runtime port.
- **It has NO channels.** `main.rs:57-65`: "No channels to service yet … the
  handler will accept a `turn_in` page, run it … and write the receipt to
  `receipt_out`." `HandlerImpl` is an empty `impl Handler`. That documented-but-
  unimplemented handler is the live-repaint seam.

### 1.4 The persist-PD: host-green, not on device — the `BlockCapBackend` wall

The durable spine is **real redb-over-block-cap durability + the hosting economy,
host-green but not on-device** (`sel4/persist-hosttest/`, `REFLEXIVE-MIGRATION.md`
§5.2):

- `commit_store.rs` — the chain gate (`verify_chain_step`: `prev_root == head` ∧
  `ordinal == cursor`, fail-closed `ChainRefusal`) + the `CommitRecord` +
  idempotent-replay/torn-state guard, `no_std`+`alloc`, lifted VERBATIM from
  `pg-dregg/mirror.rs` + `persist/commit_log.rs` so the SAME code rides inside the
  PD.
- `redb_store.rs` — REAL redb ACID over a `StorageBackend` whose **5 ops** (`len` ·
  `read` · `set_len` · `sync_data` · `write`) ARE a raw block device. `RegionBackend`
  realizes it host-side over a `File` (positional `read_exact_at`/`write_all_at` +
  `fsync`). The tooth `commits_survive_drop_and_reopen_over_the_same_bytes`
  (`:741-778`) PROVES durability: commit, drop store + backend, reopen over the same
  bytes, recover head + cursor + log + indices, chain self-checks.
- `hosting.rs` — pay-coin-to-be-hosted as a conserving `Transfer` turn + lapsed-fee
  eviction, every charge/eviction a durable row; modeled by `HostingLease.lean`.
- **~21 tests green** across `redb_store` (8), `hosting` (6), `main`/`durable_main`
  (the host witness) — durability, anti-substitution, conservation, restart-recovery.
- **The one named wall: `BlockCapBackend`** (`redb_store.rs:38-40`, 119-127). A
  single `redb::StorageBackend` impl routing the 5 ops through the seL4 virtio-blk
  block cap the persist PD solely holds — `read`/`write`/`sync_data` swap the `File`
  for the block cap; the durable-store logic ABOVE it is byte-for-byte unchanged.
  Plus the `commit_out` shared-region framing (`persist-stub/src/main.rs` already
  maps `commit_out` R and reads the executor's sentinel) and the persist-PD ELF
  link. This is M6 of the migration (`REFLEXIVE-MIGRATION.md` §6).

### 1.5 The proven cross-PD topology already in the tree

The two-PD live loop is fully proven in `net.system`: two PDs share huge-page DMA
regions, the driver `notify()`s the client over a `<channel>` (`net.system:64-72`;
`net/src/main.rs:79` `notify_client = || channels::CLIENT.notify()`), and the client
reacts in its IRQ handler. The 5-PD `dregg.system` assembly ALREADY declares
`turn_in` (1 MiB) + `commit_out` (4 MiB) DMA regions and the executor↔persist
channel (`dregg.system:62-65`, `:188-190`) — so the DMA+channel shape the live-turn
and persist loops need is already a booting pattern in this tree, not a new invention.

### 1.6 The n = 1 framing

Native and seL4 are two points on the firmament distance parameter `n`
(`FIRMAMENT.md:122-140`, §3). The same `(target, rights)` capability is local-seL4-cap
at `n = 1` and distributed-dregg-cap at `n > 1`; at `n = 1` the distributed bounds
collapse to strong-local ones (immediate revocation, synchronous commit, consistent
checkpoint — `FIRMAMENT.md:178-189`, decided ember 2026-06-13 as the security model,
`:486-489`). Parity is therefore not "port native to a weaker platform"; it is
**realize the same image at `n = 1`**, where the persist-PD gives the desktop the
exact image-durability the host World also wants.

---

## 2. THE PARITY GAP + THE ORDERED PLAN

The gap, stated plainly: on device the cells are FROZEN (a build-time bake), the
cockpit is FROZEN (a build-time RGBA), input drives only image-mode navigation, and
nothing the user does persists. Native is live, mutable, persistent. The plan closes
that in four rungs, each building on a green half.

### (i) CONSUME input in cockpit mode + add a pointer

**Goal:** stop discarding navigation in cockpit mode; add a virtio-tablet pointer so
clicks hit-test cells.

- **Reused:** the entire keyboard path (`keyboard.rs`, IRQ 78, the `notified`→
  `drain`→`apply` loop) builds and boots TODAY. The pointer is a byte-for-byte copy
  of the keyboard's PD block — same `VirtIOInput`, same `HalImpl`, same device-cap
  discipline. `EV_ABS` (absolute X/Y) + `EV_KEY` BTN_LEFT are already surfaced by
  `VirtIOInput::pop_pending_event`; no new crate, no driver change.
- **Genuinely-new plumbing:**
  - Forward `Nav` into cockpit mode instead of the `main.rs:123` early return —
    pure additive (the cockpit baked frame can stay; nav can move a focus overlay /
    select a cockpit pane). Trivial.
  - A `pointer.rs` sibling of `keyboard.rs` holding a second `VirtIOInput` on
    **slot 31** (IRQ 79, channel id 1; slots 30/31 share the `0xa003000` page at
    OFFSETs `0xc00`/`0xe00`, so ONE mmio region backs both — two IRQs + two DMA
    regions still required). One `.system` block, one `Makefile` flag
    (`-device virtio-tablet-device,bus=virtio-mmio-bus.31`), one `notified` arm.
  - **Pick the tablet, not the relative mouse:** ramfb has no hardware cursor;
    `EV_ABS` absolute coords map directly to framebuffer pixels — exactly what a
    click-target hit-test wants (`apply_pointer` reuses `view.rs`'s known rail
    geometry `RAIL_W=232`/`TOP_H=40` to map a click → `state.focus`).

**Builds today vs the wall:** entirely additive to a known-green build. No wall.

### (ii) LIVE-REPAINT-ON-TURN — the executor-PD's missing channel handler

**Goal:** an in-VM turn mutates a cell and the focused cell re-paints, live.

- **Reused:** the executor PD already runs a real verified turn; the viewer already
  repaints on every state change (`paint()` re-maps + redraws); `view.rs` already
  renders VALUE/STATE/EVIDENCE from cell data, so a changed balance/nonce shows with
  ZERO new draw code. The cross-PD loop is the proven `net.system` shared-DMA +
  `<channel>` topology, and `dregg.system` already declares `turn_in`/`commit_out`
  + the executor↔persist channel — the device swapped for a turn queue.
- **Genuinely-new plumbing:**
  - **A `deos-live.system`** = `deos-image.system` ⊕ the executor PD ⊕ three
    huge-page DMA regions (`turn_in` the encoded turn, `receipt_out` the receipt,
    `cells_out` the post-turn `image_data::ImageCell` snapshot) ⊕ two `<channel>`s
    (`CH_EXEC` viewer→executor "turn queued", `CH_VIEWER` executor→viewer "receipt
    ready, cells updated"), copied from `net.system:64-72`.
  - **The executor channel handler** (the documented-but-empty `notified`,
    `executor-pd/src/main.rs:57-65`): read `turn_in` → run
    `dregg_exec_full_forest_auth` → write `cells_out` (the post-turn `ImageCell`
    array) + `receipt_out` → `CH_VIEWER.notify()`. THE load-bearing missing piece.
  - **The viewer's data source moves** from `static IMAGE` (`image_data.rs` bake)
    to a mapped `cells_out` region — the `ImageCell` layout stays identical, so
    `view.rs` is UNTOUCHED; only the `IMAGE` accessor changes. Plus a trigger
    (a key, e.g. `t`, or BTN_LEFT) that encodes a turn into `turn_in` +
    `CH_EXEC.notify()`, and a `CH_VIEWER` arm that re-reads `cells_out` + `paint()`s.
  - **First scaffold:** a single canned turn (the executor's own proven 30-unit
    transfer) demonstrates the loop end-to-end before arbitrary turn encoding.
  - The executor is a root-task-with-std PD today (`SEL4-EMBEDDING.md`); folding it
    into the Microkit `<channel>` assembly alongside the viewer is the named
    productionization step.

**Builds today vs the wall:** both halves are green in isolation; the wall is the
WIRING (the channel handler + `deos-live.system`). No new kernel/Microkit/virtio
primitive — "implement the handler the code documents" + "copy the net.system loop."

### (iii) The persist-PD `BlockCapBackend` — the in-VM image PERSISTS (M6)

**Goal:** an in-VM turn that lands is DURABLE; the image survives a PD restart,
exactly as the host World persists to local redb. The `n = 1` synchronous commit.

- **Reused:** the ENTIRE durable store above the backend is host-green and
  byte-identical — `DurableCommitStore`, the chain gate, the one-redb-txn commit
  discipline, the hosting economy, ~21 tests. `RegionBackend` already isolates the
  exactly-5 ops that differ; the `commit_out` region is already mapped by the persist
  seat (`persist-stub/src/main.rs`) and `dregg.system` already declares the
  executor→persist channel + `commit_out` (4 MiB).
- **Genuinely-new plumbing:**
  - **`BlockCapBackend`** — the single `redb::StorageBackend` impl whose
    `len`/`read`/`set_len`/`sync_data`/`write` route through the seL4 virtio-blk
    block cap (an LBA read/write + a device flush, mirroring `RegionBackend`'s
    positional file I/O). A bounded device-driver trait impl over a virtio-blk slot
    (the same device-cap discipline as `keyboard.rs`/`net/`).
  - **The `commit_out` framing** — the executor writes the finalized `CommitRecord`
    bytes into `commit_out`; the persist PD's `notified` (channel id 1, already
    stubbed) reads them and calls `DurableCommitStore::commit_verified_turn` in ONE
    redb txn before the turn returns.
  - **The persist-PD ELF link** — promote `persist-stub` to the real persist PD
    linking `commit_store`+`redb_store`+`hosting` (host-green) over `BlockCapBackend`.
  - Once closed, the in-VM starbridge image persists to the persist-PD with the SAME
    `CommitRecord` bytes the host World persists to local redb — the n = 1 collapse.

**Builds today vs the wall:** the store + tests are green; the wall is REAL
seL4/virtio-blk plumbing on the macOS user-mode-qemu-aarch64 checkpoint + the ELF
link. The single device-driver trait impl is the whole new surface; the durable logic
above it does not change.

### (iv) Toward the FULL NODE in seL4 — networking + producer in-VM

**Goal (the bigger systems wave ember flagged):** the producer runs IN the VM, so the
deos image is not just a viewer of local cells but a full node — talks the wire,
sequences turns, hosts apps.

- **Reused:** `net.system` ALREADY boots the two-PD virtio-net topology — a driver PD
  (sole NIC-cap holder) + a smoltcp client PD over shared rings + a channel
  (`net.system`, `net/src/main.rs`). The 5-PD `dregg.system` already places net +
  executor + persist + verifier + app PDs with their channels. The producer logic is
  the existing pg-dregg/node spine (chain gate, blocklace, drainer) the persist tests
  already reuse host-side.
- **Genuinely-new plumbing:**
  - The smoltcp/lwIP client→executor path (the client PD forwarding inbound turns to
    the executor over a channel — the net.system client end, currently echo, grown to
    a turn ingress).
  - The producer/sequencer running in-VM (the blocklace + drainer over `no_std`+
    `alloc`, or a root-task-with-std PD like the executor) — the bigger lift, sized
    in `SEL4-EMBEDDING.md` / `PG-DREGG-ON-SEL4.md`.
  - Full-node assembly: net ⇄ producer ⇄ executor ⇄ persist ⇄ deos-image as one
    Microkit image (the `dregg.system` 5-PD assembly grown with the display PD).

**Builds today vs the wall:** net.system boots; the wall is the producer-in-VM port
(the heaviest, genuinely-new systems work — sequence it last, after (i)-(iii) prove
the display↔executor↔persist spine).

---

## 3. HOW THIS MEETS THE FIRMAMENT THESIS

The firmament thesis: ONE capability across DISTANCE — local seL4-cap ↔ distributed
dregg-cap ↔ surface=window — the same abstraction at points on `n`
(`FIRMAMENT.md:34`, `:96`, §3). Parity is the realization of that thesis on the
desktop:

- **Native and seL4 are points on `n`, not two systems.** The native World and the
  in-VM image run the SAME executor (`dregg_exec_full_forest_auth`), the SAME
  `CommitRecord`/chain gate, the SAME cells. seL4 is `n = 1`; native is a degenerate
  `n = 1` without the cap partition. Closing (ii)+(iii) makes the in-VM image
  behaviorally the native image AT `n = 1` — with the cap partition as a strict
  security gain (seL4 faults any PD that touches a cap it does not solely hold).
- **The persist-PD is the n = 1 image-durability the host World ALSO wants.**
  `REFLEXIVE-MIGRATION.md` §5.1 names the native gap: `starbridge-v2` is purely
  in-memory (no `dregg-persist`/redb dep), every launch boots a fresh demo world.
  Both Worlds want the same durable spine; the persist-PD store (`redb_store.rs`,
  host-green) is LITERALLY the same code the native World should adopt (§5.1 move A).
  Rung (iii) and the native persistence weld are ONE durable store at two points on
  `n` — the same `CommitRecord` bytes either way.
- **The gpui↔framebuffer Mode is the bridge to the real cockpit-in-VM.** Today the
  cockpit is a build-time-baked gpui RGBA. The proven offscreen render (`d92d0526c`)
  is the seed; the honest live-on-VM path is the DATA-driven `view.rs` repaint
  (rung ii), because a `#![no_std]` PD cannot link wgpu — the heavy gpui render stays
  off-VM, the live rung is the cell-data repaint. Promoting cockpit surface
  geometry/z/focus into `SetField` effects on a compositor cell (so the cockpit
  re-bakes on new state) is the firmament reflexive-substrate bridge
  (`REFLEXIVE-MIGRATION.md` §6, the gpui↔firmament mapping; surface IS a real
  `dregg_firmament::Capability` over `Target::Surface`). **Honest: that mapping is
  keep-in-mind-but-later** — it sequences after the (i)-(iii) display↔executor↔persist
  spine proves out, and it is entangled with the native incremental-projector work,
  which this systems track is independent of.

---

## 4. THE SEAMS + THE ORDERED TASK LIST

### The seams (named, each with its closure lane)

1. **Cockpit input is discarded** (`main.rs:123`). Closure: rung (i) — forward
   `Nav` into a cockpit focus/selection state instead of the early return. Additive.
2. **No pointer device.** Closure: rung (i) — `pointer.rs` + slot-31 virtio-tablet,
   a copy of the keyboard block; `EV_ABS` decode is a new arm, not a new primitive.
3. **The executor PD has no channel handler** (`executor-pd/src/main.rs:57-65`).
   Closure: rung (ii) — implement the documented `turn_in → exec → cells_out/
   receipt_out → notify` handler. The load-bearing live-turn seam.
4. **No `deos-live.system`** wiring viewer + executor + 3 DMA + 2 channels. Closure:
   rung (ii) — copy `net.system`'s proven two-PD shared-DMA+channel topology.
5. **The viewer reads a frozen `static IMAGE`.** Closure: rung (ii) — move the
   `IMAGE` accessor from a `static` to a mapped `cells_out` region; `view.rs`
   unchanged (`ImageCell` layout identical).
6. **`BlockCapBackend` is unimplemented** (`redb_store.rs:38-40`). Closure: rung
   (iii) — the 5-op `StorageBackend` over the virtio-blk cap + `commit_out` framing
   + persist-PD ELF link. The durable store above it does not change.
7. **The producer runs off-VM.** Closure: rung (iv) — the net-client→executor turn
   ingress + the producer/sequencer in-VM. The heaviest, last.
8. **The gpui live cockpit is a build-time bake** (compositor geometry is
   engine-local, not cells). Closure: the firmament reflexive-substrate bridge
   (`REFLEXIVE-MIGRATION.md` §6) — keep-in-mind-but-later, after the spine + entangled
   with the native projector track.

### The ordered task list (what builds vs the wall at each step)

| # | Task | Reuses | Builds today? | The wall |
|---|------|--------|---------------|----------|
| 1 | Forward `Nav` into cockpit mode | the whole keyboard loop | ✅ green build | none (additive) |
| 2 | `pointer.rs` + slot-31 virtio-tablet + `apply_pointer` hit-test | `keyboard.rs` byte-for-byte; `view.rs` geometry | ✅ green build | new `.system` block + `Makefile` flag (additive) |
| 3 | `cells_out`-backed `IMAGE` accessor (data source move) | `view.rs` unchanged (`ImageCell` layout) | ✅ green build | viewer reads a mapped region, not a static |
| 4 | `deos-live.system` (viewer ⊕ executor ⊕ 3 DMA ⊕ 2 channels) | `net.system` topology; `dregg.system` `turn_in`/`commit_out` | the PDs build green | new assembly wiring (proven pattern) |
| 5 | Executor channel handler (`turn_in → exec → cells_out/receipt_out → notify`) | the verified turn already runs | the turn runs green | implement the documented `notified` (load-bearing) |
| 6 | Viewer trigger + `CH_VIEWER` repaint arm | `paint()` repaint-on-change | ✅ green build | close the loop on the new channel |
| 7 | `BlockCapBackend` (5-op `StorageBackend` over virtio-blk cap) | `redb_store.rs` store + ~21 tests; `keyboard.rs` device-cap discipline | the store is green host-side | REAL virtio-blk plumbing on qemu-aarch64 |
| 8 | `commit_out` framing + real persist-PD ELF link | `persist-stub` seat; `commit_store`/`hosting` host-green | host-green | wire executor→persist commit + ELF link |
| 9 | net-client → executor turn ingress | `net.system` two-PD net topology | net.system boots | grow the echo client into a turn ingress |
| 10 | producer/sequencer in-VM (full node) | pg-dregg/node spine; `dregg.system` 5-PD | — | the producer port (heaviest, genuinely-new) |

Tasks 1-3 are independently shippable additive slices against a known-green build.
4-6 are the live-turn rung (the make-or-break systems milestone — the in-VM image
becomes alive). 7-8 are the durability rung (the image persists at `n = 1`). 9-10 are
the full-node wave. Every rung reuses a proven primitive or the proven `net.system`
topology; the only genuinely-new device surface is the virtio-tablet decode arm (2),
the executor channel handler (5), and `BlockCapBackend` (7). No step needs a new
kernel, Microkit, or virtio primitive.
