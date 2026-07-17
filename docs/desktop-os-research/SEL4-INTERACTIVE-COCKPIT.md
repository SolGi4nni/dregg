# The interactive, live deos cockpit on seL4

This doc designs and scaffolds making the **hosted cockpit image interactive and
live** on the seL4 framebuffer: (1) keyboard/mouse INPUT from QEMU reaching the
cockpit's event handling, and (2) LIVE-REPAINT-ON-TURN — when the in-VM executor
runs a real turn, the focused cell re-paints.

It builds directly on what already boots after `d92d0526c` ("the LIVE cockpit
element tree renders on the seL4 framebuffer") and `bbccc03ca` (the live image
viewer). It REUSES the real Microkit/virtio primitives already in `sel4/`; it
never reinvents them. Where a piece is genuinely missing it is named, not faked.

Everything below cites the real code as of HEAD.

---

## 1. The current render path (from the real code)

The render path today lives entirely inside ONE protection domain, the
**deos-image PD** (`sel4/dregg-pd/deos-image/`), assembled by
`sel4/deos-image.system` and booted by `make run-image`.

### 1.1 Bytes → glass (the framebuffer)

- The PD is the **sole holder** of three caps and nothing else
  (`deos-image.system:43-94`): the fw_cfg engine MMIO window (`fwcfg_mmio`, phys
  `0x9020000`), a 4 MiB DMA framebuffer region (`fb_dma`, `0x400_000`,
  huge-page-backed so `region_paddr` is one contiguous run), and the virtio
  keyboard's mmio/DMA/IRQ (slot 30).
- `fb.rs` drives QEMU's `ramfb` standalone display over the fw_cfg DMA protocol:
  `configure_ramfb()` (`fb.rs:143`) finds the `etc/ramfb` selector
  (`find_ramfb_select`, `fb.rs:105`) and DMA-writes a `RamFbCfg`
  (`addr=fb_paddr`, `XRGB8888`, `800x600`, `fb.rs:162-185`). Geometry is
  `WIDTH=800 HEIGHT=600 BPP=4` (`fb.rs:13-16`).
- The drawing surface is `Canvas` (`fb.rs:214`), a `&'static mut [u32]` over the
  mapped framebuffer (`Canvas::map`, `fb.rs:221`) with `put`/`rect`/`text`/…
  primitives. **Re-mapping is cheap and idempotent**: every repaint calls
  `unsafe { Canvas::map() }` afresh (`main.rs:94`). This is the same fw_cfg/ramfb
  protocol the `compositor-fb` PD first proved (`compositor-fb/src/main.rs`,
  `GRAPHICAL-SEL4-BOOT.md §3`); `fb.rs` is the factored-for-live-repaint copy.

### 1.2 The two modes, and how the gpui RGBA reaches the framebuffer

The viewer (`main.rs:78-99`) has two modes:

- **`Mode::Image`** — the live object browser: `view::draw(&mut canvas, &state)`
  (`main.rs:96`, `view.rs`) paints the cell rail + the focused-cell inspector
  from `image_data::IMAGE` (real baked `dregg_cell` snapshots).
- **`Mode::Cockpit`** — `cockpit_frame::blit(&mut canvas)` (`main.rs:97`).
  `cockpit_frame.rs:52` copies the **baked** `COCKPIT_RGBA`
  (`include_bytes!("cockpit_frame.rgba")`, `cockpit_frame.rs:40`; exactly
  `800*600*4 = 1_920_000` bytes) into the framebuffer, converting RGBA8 →
  XRGB8888 per pixel (`cockpit_frame.rs:71-81`).

The `cockpit_frame.rgba` is the **real gpui `cockpit::Cockpit` element tree**,
rendered HEADLESS off-VM and baked in at build time: `starbridge-v2
--render-cockpit` (`starbridge-v2/src/main.rs::render_cockpit_headless`,
`GPUI-OFFSCREEN-FORK.md:43`) drives a `gpui::HeadlessAppContext` over
`TestPlatform`, resolves the frame's `gpui::Scene`, and
`Window::render_to_image` runs it through the offscreen wgpu renderer on lavapipe
(no GPU, no window) on the render host — 1600x1200@2x Lanczos-downscaled to 800x600. A
`#![no_std]` PD cannot link wgpu, so the heavy render happens at build time and
the RGBA is embedded, EXACTLY as `image_data.rs` bakes real cells.

**The seam this doc addresses:** the cockpit mode is today a *single static baked
frame*. It does not respond to input (`main.rs:123`: in cockpit mode all
navigation keys are inert; only TAB leaves it) and it does not change when a turn
runs (there is no turn loop touching it). The image mode IS interactive but is
likewise a frozen snapshot (`main.rs:44-48`: "the cells do NOT yet CHANGE while
you watch").

### 1.3 Input is ALREADY wired (for image mode)

This is the most important current-state finding. The **virtio-keyboard input
path is already complete and booting** for the image viewer:

- `deos-image.system:60-93` grants slot-30 virtio-mmio (`0xa003000`), a 1 MiB DMA
  region for the event rings, and **IRQ 78** (`48 + 30`) wired to PD channel
  `id=0`.
- `make run-image` adds `-device virtio-keyboard-device,bus=virtio-mmio-bus.30`
  (`Makefile:354`).
- `keyboard.rs` is a real `virtio_drivers::device::input::VirtIOInput` driver
  (`keyboard.rs:68`) using the SAME `HalImpl` + device-cap discipline as the
  net-driver PD. `init()` (`keyboard.rs:73`) probes the slot; `drain()`
  (`keyboard.rs:114`) reads Linux evdev events `{event_type, code, value}` and
  folds them to a `Nav` (`keyboard.rs:121-128`).
- The loop closes in `Handler::notified` (`main.rs:200`): keyboard IRQ →
  `keyboard::drain` → `Viewer::apply(nav)` → repaint on change → `KBD.irq_ack()`
  to re-arm. `apply` (`main.rs:103`) is the navigation state machine; it only
  repaints on a real transition (`main.rs:173-190`).

So **keyboard → cockpit event handling is half-built**: the transport, IRQ,
driver, decode, and repaint-on-change loop all exist; the gap is that cockpit
mode discards the navigation (`main.rs:123`) instead of forwarding it to the
cockpit, and there is no pointer (mouse) device.

---

## 2. INPUT plan: keyboard (extend) + mouse (add), virtio all the way

### 2.1 Mechanism: virtio-input, NOT PS/2

Use **virtio-input** for both keyboard and mouse. Reasons grounded in the tree:

- The keyboard already IS virtio-input (`keyboard.rs`), proven booting. PS/2
  would be a second, foreign driver (i8042) for no benefit.
- `sel4/dregg-pd/net/` establishes the exact reusable pattern: one PD is the SOLE
  holder of a virtio-mmio slot + DMA region + IRQ, probes with `MmioTransport`
  (`sel4/dregg-pd/net/src/main.rs:44-71`), and drives a `virtio_drivers` device. The keyboard
  follows it verbatim (`keyboard.rs:1-12` says so explicitly).
- QEMU ships `virtio-tablet-device` and `virtio-mouse-device` for `virtio-mmio`,
  and `virtio_drivers`' `VirtIOInput` already decodes their evdev streams
  (`EV_ABS` for the tablet's absolute X/Y, `EV_KEY` for buttons). No new crate.

**Pick the tablet, not the relative mouse**, for the pointer: a ramfb scanout has
no hardware cursor and the guest gets no host pointer-acceleration context. The
tablet's `EV_ABS` absolute coordinates map *directly* to framebuffer pixels — no
accumulator, no warp — which is exactly what a click-target hit-test wants. This
mirrors how every QEMU GUI defaults to `-device usb-tablet` for absolute pointing.

**Missing piece (named):** the current `keyboard.rs` `drain()` only handles
`EV_KEY` (`keyboard.rs:118`). The tablet emits `EV_ABS` (type 3) X/Y plus
`EV_KEY` BTN_LEFT (`0x110`). `VirtIOInput::pop_pending_event` surfaces these, so
no driver change is needed — only a new decode arm. That is implementation, not a
missing primitive.

### 2.2 The wiring sketch — one new device, in the SAME PD

The cleanest scaffold keeps everything in the deos-image PD (no new PD needed for
input — the PD already owns the framebuffer it must repaint, so co-locating the
input avoids a cross-PD hop on the hot path). Add a second virtio-input device on
**slot 31** (the keyboard is slot 30; the net PD already demonstrates slot 31 as
a free choice — `Makefile:139`). Concretely:

`deos-image.system` (add alongside the keyboard block, mirroring it exactly):

```xml
<!-- the virtio-tablet pointer: slot 31, phys 0xa003e00 base lands in this page;
     mirrors the keyboard's slot-30 grant exactly. IRQ = 48 + 31 = 79. -->
<memory_region name="virtio_ptr_mmio" size="0x1000" phys_addr="0xa003000" />  <!-- shares the slot-30/31 page; OFFSET 0xe00 -->
<memory_region name="virtio_ptr_dma"  size="0x200_000" page_size="0x200_000" />
...
<map mr="virtio_ptr_mmio" vaddr="0x6_000_002_000" perms="rw" cached="false" setvar_vaddr="virtio_ptr_mmio_vaddr" />
<map mr="virtio_ptr_dma"  vaddr="0x7_000_001_000" perms="rw" cached="true"  setvar_vaddr="virtio_ptr_dma_vaddr" />
<setvar symbol="virtio_ptr_dma_paddr" region_paddr="virtio_ptr_dma" />
<irq irq="79" id="1" />   <!-- a SECOND channel; the keyboard already uses id 0 -->
```

> Note: slots 30 and 31 (`0xa003c00`, `0xa003e00`) both fall inside the single
> 4 KiB page at `0xa003000`, so ONE `virtio_kbd_mmio`/`virtio_ptr_mmio` page can
> back both with different `MmioTransport` OFFSETs (`0xc00` kbd / `0xe00` ptr,
> matching `keyboard.rs:34`'s `KBD_MMIO_OFFSET`). Two IRQs (78, 79) and two DMA
> regions are still required.

`Makefile` `run-image`/`run-image-headless`/`capture-image-modes` add one flag:

```
-device virtio-tablet-device,bus=virtio-mmio-bus.31
```

PD code: a new `pointer.rs` (sibling of `keyboard.rs`) holding a second
`VirtIOInput`, a `PTR: Channel = Channel::new(1)` constant in `main.rs` (the
keyboard owns `Channel::new(0)`, `main.rs:69`), and a new IRQ arm in
`Handler::notified`:

```rust
fn notified(&mut self, channels: ChannelSet) -> Result<(), Infallible> {
    if channels.contains(KBD) { /* existing keyboard drain+apply */ }
    if channels.contains(PTR) {
        if let Some(p) = self.ptr.as_mut() {
            for ev in pointer::drain(p) {        // PointerEv { x, y, button_down }
                let _ = self.apply_pointer(ev);  // hit-test + focus/click + repaint
            }
        }
        let _ = PTR.irq_ack();
    }
    Ok(())
}
```

`apply_pointer` is the hit-test: the image mode already lays out the cell rail at
known geometry (`view.rs`: `RAIL_W=232`, `TOP_H=40`, per-cell row height), so a
click in the rail maps to a `state.focus` and a click in the main pane maps to a
substance tile — i.e. mouse synthesizes the SAME `Nav` transitions the keyboard
produces, then `paint()`. For the cockpit mode, the pointer feeds §3.3 below.

**What builds today:** the keyboard path builds and boots now. Adding the tablet
is purely additive — one `.system` block, one `Makefile` flag, one `pointer.rs`
modeled byte-for-byte on `keyboard.rs`, one `notified` arm. No new primitive.

---

## 3. LIVE-REPAINT-ON-TURN: executor-PD → focused-cell repaint

This is the deeper rung. Today the cells are a frozen `image_data::IMAGE` baked
at build time (`main.rs:44-48` names this exactly as the frontier). The goal: the
in-VM executor runs a real turn, mutates a cell, and the focused cell re-paints.

### 3.1 What exists to build on

- **The executor PD boots and runs a real verified turn** inside seL4
  (`executor-pd/src/main.rs:46-52`: `dregg_exec_full_forest_auth → status:2 ok:1`,
  nonce 7→8, a 30-unit transfer, nullifier+commitment). Per
  `SEL4-EMBEDDING.md:6-11` the Lean-runtime port is DONE; what remains is
  productionization, not a runtime port. **Crucially the executor PD has no
  channels yet** (`executor-pd/src/main.rs:57-65`: "No channels to service yet …
  the handler will accept a `turn_in` page, run it, and write the receipt to
  `receipt_out`"). That handler is the seam.
- **The cross-PD live loop pattern already exists**, fully, in `sel4/net.system`: two
  PDs share DMA regions (`virtio_net_*`), the driver `notify()`s the client over
  a `<channel>` (`sel4/net.system:64-72`, `sel4/dregg-pd/net/src/main.rs:79` `notify_client`), and
  the client's IRQ handler reacts. This IS the executor→viewer loop topology,
  one device swapped for a turn queue.

### 3.2 The topology — a two-PD `deos-live.system`

Grow `deos-image.system` into a two-PD assembly (call it `deos-live.system`),
modeled on `net.system`:

```
  ┌────────────────┐  turn_in (DMA)   ┌──────────────────┐
  │  deos-image PD │ ───────────────▶ │   executor PD    │
  │  (display +    │                  │ (verified turn:  │
  │   kbd + tablet)│ ◀─────────────── │  exec_full_forest│
  │                │  receipt_out +   │  → receipt)      │
  └────────────────┘  cells_out (DMA) └──────────────────┘
         ▲  CH_VIEWER (notify)  CH_EXEC (notify)
         └── repaint focused cell on receipt notify
```

- Three shared DMA regions (huge-page-backed, the `net.system` discipline):
  `turn_in` (the encoded turn the viewer submits), `receipt_out` (the receipt the
  executor writes), and `cells_out` (the post-turn cell snapshot, in the SAME
  `image_data::ImageCell` layout the viewer already renders — so the viewer's
  draw code is UNCHANGED, only its data source moves from `static IMAGE` to a
  mapped region).
- Two channels, exactly as `net.system:65-72`: `deos-image id=N ⇄ executor id=M`.
  Viewer notifies executor "a turn is queued"; executor notifies viewer "receipt
  ready, cells updated".

### 3.3 The loop, step by step

1. **Trigger.** A keypress/click in the viewer is mapped (in `apply` /
   `apply_pointer`) to an intent that means "run this turn" — e.g. ENTER on a
   "transfer" affordance, or a dedicated key. The viewer encodes the turn into
   `turn_in` and `CH_EXEC.notify()`s the executor. (For the first scaffold a
   single canned turn — the executor's own proven 30-unit transfer — is enough to
   demonstrate the loop end to end.)
2. **Execute.** The executor PD's `notified` (the handler `main.rs:57-65`
   reserves) reads `turn_in`, runs `dregg_exec_full_forest_auth`, writes the
   receipt to `receipt_out` and the mutated cell snapshot to `cells_out`, then
   `CH_VIEWER.notify()`s the viewer.
3. **Repaint.** The viewer's `notified` gains a `CH_VIEWER` arm: on notify it
   re-reads `cells_out` into its view state and calls `paint()`. Because the
   draw path already keys off `state.focus`, the **focused cell re-paints with
   the new balance/nonce/state_root the instant the turn lands** — the named
   "cells re-paint as the executor runs" rung from the live-image-viewer
   (`main.rs:44-48`).

The repaint is already correct and cheap: `paint()` re-maps the framebuffer and
redraws (`main.rs:93-99`); `view.rs` already renders VALUE/STATE/EVIDENCE from
cell data, so a changed balance or nonce shows with zero new draw code.

### 3.4 What builds today vs the seam

- **Builds + boots today:** the display, the keyboard loop, the repaint-on-change
  machinery (`paint()` on every transition), AND the executor PD running a real
  verified turn — *but in isolation*. Both halves are green; they are not yet
  connected.
- **The seam (named, with its closure lane):**
  1. The executor PD has **no channel handler** — it idles after init
     (`executor-pd/src/main.rs:57-65`). The closure is to implement the
     `turn_in → exec → receipt_out/cells_out → notify` handler it already
     describes in its own doc comment. This is the load-bearing missing piece.
  2. There is **no `deos-live.system`** wiring the two PDs + three DMA regions +
     two channels. The closure is to write it, copying `net.system`'s shared-DMA
     + `<channel>` topology (the pattern is proven; only the region names and PD
     set change).
  3. The viewer's cell data must move from `static IMAGE` (`image_data.rs`,
     build-time bake) to a **mapped `cells_out` region** so a turn can mutate it.
     The `ImageCell` layout stays identical, so `view.rs` is untouched; only the
     `IMAGE` accessor changes from a `static` to a region read.
  4. The executor PD is a **root-task-with-std** PD today
     (`SEL4-EMBEDDING.md:318`); folding it into the Microkit `<channel>` assembly
     alongside the viewer is the productionization step `SEL4-EMBEDDING.md:247`
     already names ("Microkit assembly wiring ingress → executor → persist").

None of these need a new kernel/Microkit/virtio primitive. Every one is either
"implement the handler the code already documents" or "copy `net.system`'s proven
two-PD shared-DMA+channel topology with the device swapped for a turn queue."

### 3.5 The repaint loop is WIRED + PROVEN on the semihost (the same-code path)

The §3.3 loop is now **implemented and proven** on the semihost firmament — the
host-runnable (`cargo test`, no Microkit SDK) realization of the SAME PD source
that runs on real seL4. `sel4/dregg-firmament/` is the
`EmulatedKernel`/`microkit_facade` model where the executor-PD
(`src/executor_pd.rs`) and the compositor-PD (`src/compositor_pd.rs`) already run
on ONE kernel; before this they were both green but DISCONNECTED, exactly the §3
seam.

What is wired (`sel4/dregg-firmament/src/repaint.rs`, ~9 unit + 2 boot tests):

- **The projection** `project_dirty_from_turn(owner, ServedTurn) → Option<DirtyRegion>`
  — a committed turn projects a `DirtyRegion { owner, new_source_state_root,
  new_content_digest }` (the new state-root/digest folded from the committed
  receipt — faithful to the binding discipline: a distinct committed state ⟹ a
  distinct frame). A **REJECTED** turn projects `None` (fail-closed — no repaint).
  This is the PD-boundary form of the deos `deos-js/src/signals.rs` dirty-set: a
  touched cell ⟼ the surface that must re-present.
- **The wire** `encode_dirty`/`decode_dirty` over a shared `repaint_out` region
  (the third region of the §3 topology, beside `turn_in`/`commit_out`), hand-
  rolled + dependency-free exactly like `compositor_pd::encode_present` and the
  net-client's `[len][msg]` framing. A malformed frame decodes to `None` (no
  repaint).
- **The repaint** `DirtyRegion::to_present(target) → Present` — turns the dirty
  signal into the compositor's scene-gated `present()`, declaring the GENUINE
  owner-label (T2) and NOT claiming focus (a content advance, not an input
  assertion). It rides the SAME compositor gate as any present.

What is PROVEN (`sel4/dregg-firmament/tests/live_repaint_on_turn.rs`):

- **A COMMITTED turn re-paints the focused cell** — the executor runs the genuine
  `granted ⊆ held` gate, projects a `DirtyRegion`, writes `repaint_out`, the
  compositor reads it and presents → **two framebuffer snapshots DIFFER at exactly
  the focused cell's region** (tile 10 advances from blank to the turn's frame).
- **A REJECTED turn re-paints NOTHING** — the widening turn is refused at the
  heart, projects `None`, the compositor is never woken → **the framebuffer is
  BYTE-IDENTICAL** (fail-closed).
- **The scene gate still fires on a repaint** — a turn cannot re-paint a region
  its cell does not own; a repaint targeting a foreign surface's region is REFUSED
  (T1 — no amplification at the pixel layer), the victim's tile untouched.

This adds ONLY the projection + the wire — NO new primitive. It rides the proven
executor-PD turn path, the proven compositor-PD present gate, and the cross-PD
`notify`/shared-region `Channel` the 2-PD notify slice (`sel4/dregg-firmament/tests/boot_pds.rs`)
proves. The honest fidelity label travels with the code
(`dregg_firmament::REPAINT_FIDELITY`): the loop is REAL on the semihost (a genuine
turn drives a genuine scene-gated present advancing the framebuffer); the
framebuffer's last hop to a scanned-out panel is the F1/F2/F3 graphics frontier
the compositor already names, NOT solved here.

### 3.6 What the real-seL4 Microkit runner needed — NOW LANDED (see §3.6.1)

**All four steps below are CLOSED on real seL4** — `sel4/deos-live.system` boots
live-repaint-on-turn under QEMU (`make run-deos-live`). This subsection is kept as
the design record of what the transcription required; §3.6.1 is the landing.

The semihost proves the LOOP (same PD source). To see it on the seL4 framebuffer
originally needed the Microkit SDK (`microkit` was not on PATH when this was first
written; `qemu-system-aarch64` IS present). The real-seL4 work that was required,
none of it a new primitive:

1. **`deos-live.system`** — the §3.2 two-PD assembly (`deos-image` PD ⊕
   `executor` PD ⊕ `turn_in`/`commit_out`/`repaint_out` DMA regions ⊕ the two
   `<channel>`s), copied from `net.system`'s proven shared-DMA + `<channel>`
   topology. (The net-client weld `80c9468f` already demonstrates the exact
   `turn_in` RW-staging + `EXECUTOR.notify()` shape this needs.)
2. **The bare-metal executor-PD handler** (`sel4/dregg-pd/executor-pd`) gains the
   `repaint_out` write + `CH_REPAINT.notify()` after a commit — the exact code
   `repaint.rs` proves on the semihost, transcribed to the real `memory_region_
   symbol!` + `Channel` (the same text, per §3's same-code contract).
3. **The deos-image PD's `notified(CH_REPAINT)` arm** — read `repaint_out`,
   present the dirty region (the viewer's `view.rs`/`fb.rs` `paint()` is already
   the repaint-on-change machinery; only its trigger moves to the notify).
4. The executor-PD Lean-ELF runtime link remains the real-seL4 WALL step (it
   idles its verified-turn path on bare metal until the runtime links — NOT a
   blocker on the semihost, where the genuine runner runs NOW).

**Run command for ember (once the Microkit SDK is on PATH):** the semihost proof
runs anywhere with `cd sel4/dregg-firmament && cargo test --test
live_repaint_on_turn` (2/2 green, no SDK needed). The real-seL4 framebuffer
demonstration is `make run-image` after `deos-live.system` lands (step 1–3 above).

### 3.6.1 LANDED — `deos-live.system` drives live-repaint-on-turn on real seL4

Steps 1–4 above are now CLOSED on real seL4. Step 4's "WALL" (the executor-PD
Lean-ELF runtime link) was already cleared by the `executor-microkit-pd` keystone
(`sel4/dregg-pd/executor-microkit-pd/WALL.md`: the verified executor links into a
Microkit PD, 0 undefined symbols, and runs `status:2 ok:1`) plus the 2 MiB-page
microkit patch (`microkit-patch/0001-2mib-elf-image-pages.patch`) that fits the
~285-MiB executor image under the loader. So `deos-live.system` is the FULL loop,
booting:

- **`sel4/deos-live.system`** — the two-PD assembly: the `executor` PD (the banked
  verified-executor ELF) ⊕ the `deos_image` PD (ramfb + virtio-keyboard), three
  shared regions (`turn_in` R, `commit_out` RW→R), and two channels (executor
  `commit ready` id 2 ⇄ viewer REPAINT id 1; the one-way verifier edge id 3 ⇄ id 2,
  ignored). NO executor relink — it reuses the keystone ELF verbatim.
- **The bare-metal repaint arm** (`deos-image/src/main.rs`): a `REPAINT` channel
  arm in `notified()` reads the verified turn's JSON receipt from the shared
  `commit_out` region, parses `status`/`ok`/`nonce`, and repaints. The genuine
  receipt drives the frame — a REJECTED turn (status≠2) shows the fail-closed
  banner, mirroring the semihost `repaint.rs` `DirtyRegion`/`None` discipline.
- **On glass** (`deos-image/src/view.rs`): the `live_turn_banner` overlay — the
  "VERIFIED TURN on seL4" banner with the real receipt facts.

Booted under `qemu-system-aarch64` (`make run-deos-live` / `run-deos-live-headless`,
the relinked `0x90000000` loader + the 2 MiB-page patched microkit, ZERO faults
across both PDs). The serial transcript (`sel4/deos-live-boot-evidence.log`):

```
[executor]   ==> bodyCommitted — the executor PD ran a REAL accepted turn ( ◕‿◕ )
[executor]   signalling persist (ch 2) + verifier (ch 3)
...
[deos-image]   ramfb CONFIGURED: addr=0x65e00000 XRGB8888 800x600 stride=3200
[deos-image]   <== LIVE TURN #1: the executor PD committed a VERIFIED turn
               (status:2 ok:1, nonce->8, receipt 313B) — repainting on glass ( ◕‿◕ )
```

A genuine `dregg_exec_full_forest_auth` turn, in its own cap-bounded protection
domain, drives a framebuffer repaint in the display PD over a real cross-PD seL4
notification — on real seL4, not the stub. Run `make run-deos-live`.

---

## 4. Concrete next-step PD/IPC sketch (the smallest end-to-end slice)

> The **repaint-on-turn** half of this sketch has since LANDED (§3.6.1,
> `deos-live.system`, `make run-deos-live`). What remains genuinely open is the
> **input-drives-turn** half: the virtio-tablet pointer (§2, still no `pointer.rs` /
> no tablet flag in the Makefile) and wiring a keypress/click to trigger the turn.
> The sketch below is retained as the original end-to-end shape.

The smallest slice that demonstrates BOTH input-drives-turn AND repaint-on-turn,
reusing only proven primitives:

1. **Input (additive, in deos-image PD).** Add `pointer.rs` + the slot-31
   virtio-tablet grant (§2.2). Map ONE evdev source — BTN_LEFT — to "run the
   canned turn." (Keyboard already works; a dedicated key, e.g. `t`, can be the
   keyboard trigger with zero new device.)
2. **`deos-live.system`** = `deos-image.system` ⊕ the executor PD ⊕ three DMA
   regions (`turn_in`, `receipt_out`, `cells_out`) ⊕ two `<channel>`s, copied
   from `net.system:64-72`.
3. **Executor handler** (`executor-pd/src/main.rs`): implement the documented
   `notified` — `turn_in` → `dregg_exec_full_forest_auth` → write `cells_out`
   (the post-turn `ImageCell` array) + `receipt_out`, then `CH_VIEWER.notify()`.
4. **Viewer**: (a) `IMAGE` reads from `cells_out` not the static bake; (b) on a
   trigger, encode a turn into `turn_in` + `CH_EXEC.notify()`; (c) a `CH_VIEWER`
   arm in `notified` that re-reads `cells_out` and `paint()`s.

Result: press a key (or click) → the executor runs a REAL verified turn in its
own PD → the focused cell's balance/nonce/state_root re-paint on glass, live. The
cockpit mode then gets the same treatment by having `--render-cockpit` re-bake on
the new state (the heavy gpui render stays off-VM; the live-on-VM rung is the
data-driven `view.rs` repaint, which is the honest, no-GPU-in-PD path).

### Build confidence

The semihost firmament (`sel4/dregg-firmament/`) builds + tests with plain
`cargo` (no SDK): `cargo test` is green (56 lib + all integration tests,
including `live_repaint_on_turn`), and that is where the §3 loop is now proven
(§3.5). The bare-metal `make build-image`/`make run-image` path needs the Microkit
SDK on PATH (`MICROKIT_SDK`); `qemu-system-aarch64` is present. When the SDK is
available, `make run-image` boots the interactive keyboard-driven viewer; the
input extension (§2) is additive to that build, and the live-turn loop (§3) is the
transcription of the now-proven semihost wiring (§3.6).

---

## 5. Summary of findings

- **Input is not greenfield** — virtio-keyboard input is already wired end to end
  and booting (`keyboard.rs` + `deos-image.system:60-93` + `Makefile:354`). The
  missing pieces are (a) forwarding navigation INTO cockpit mode instead of
  discarding it (`main.rs:123`), and (b) a virtio-tablet pointer (an additive
  copy of the keyboard block; `EV_ABS` decode is a new arm, not a new primitive).
- **The render path is one PD, ramfb + Canvas** (`fb.rs`), with the gpui cockpit
  as a build-time-baked RGBA blit (`cockpit_frame.rs`). Repaint is already cheap
  and idempotent (`paint()` re-maps the framebuffer every transition).
- **Live-repaint-on-turn is WIRED + PROVEN on the semihost** (§3.5,
  `sel4/dregg-firmament/src/repaint.rs` + `sel4/dregg-firmament/tests/live_repaint_on_turn.rs`, 8 unit
  + 2 boot tests green). A committed turn through the executor-PD projects a
  `DirtyRegion`, writes a shared `repaint_out` region, and the compositor-PD reads
  it and runs a scene-gated `present()` — **two framebuffer snapshots differ at
  exactly the dirty region** (the focused cell re-paints); a REJECTED turn
  projects nothing → the framebuffer is **byte-identical** (fail-closed); and the
  T1 gate still refuses a repaint of a region the cell does not own. This is the
  SAME PD source that runs on real seL4; it adds ONLY the projection + the wire,
  no new primitive — the deos `signals.rs` dirty-set → repaint-hook model lifted
  across the PD boundary.
- **The bare-metal seL4 demonstration has LANDED** (§3.6.1). `sel4/deos-live.system`
  is the two-PD assembly (the `executor` PD ⊕ the `deos_image` PD, `turn_in`/
  `commit_out` shared regions + the two `<channel>`s); the bare-metal executor-PD
  commits a verified turn and signals, and the deos-image PD's `REPAINT` channel arm
  (`deos-image/src/main.rs:78`) reads `commit_out` and repaints. It boots under
  `qemu-system-aarch64` with ZERO faults across both PDs — **run `make
  run-deos-live`** (`sel4/Makefile:412`). The executor-PD Lean-ELF runtime link that
  §3.6 named as the WALL was cleared by the `executor-microkit-pd` keystone
  (`sel4/dregg-pd/executor-microkit-pd/WALL.md`). The semihost proof still runs with
  `cd sel4/dregg-firmament && cargo test --test live_repaint_on_turn`.
- **No missing kernel/Microkit/virtio primitive.** Every seam is "implement the
  handler the code already documents" or "copy the proven net.system topology."
