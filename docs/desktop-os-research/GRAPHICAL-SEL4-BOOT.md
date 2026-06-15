# GRAPHICAL-SEL4-BOOT — a real framebuffer driven by a seL4 PD, visible in a QEMU window

*The first graphical milestone of deos-on-seL4: the **bytes->glass path on seL4,
end to end**, at the simplest honest scope. A single protection domain (the
`compositor-fb` PD) configures QEMU's `ramfb` display device over `fw_cfg` and
writes a deos splash directly into a framebuffer it solely holds — pixels the
QEMU window scans out. This is what closes the **output side** that THEME 3 of
`docs/MATURATION-LEDGER.md` names ("authority is real, pixels & durability are
not"): until now the firmament booted HEADLESS (`-nographic`), and the
compositor "framebuffer" was a 256-byte host-test authority witness
(`sel4/dregg-firmament/src/compositor_pd.rs`, `FRAMEBUFFER_TILES = 256`), not
pixels. Now a real seL4 PD drives real (emulated) display hardware.*

*Companion to [SERVO-ON-SEL4.md](SERVO-ON-SEL4.md) (the software-rendered Servo
PD this scanout is the destination for), [ARCHITECTURES.md](ARCHITECTURES.md)
(the compositor-PD as the third device-holding sibling), and
[../FIRMAMENT.md](../FIRMAMENT.md) §2/§6 (the one-device-cap-per-PD discipline
the net-driver PD established and this PD reuses for the display).*

---

## 0. The verdict in one paragraph

**Built and proven, end to end.** A real seL4 Microkit image
(`build/dregg-graphical.img`) boots a single PD that (1) solely holds QEMU's
`fw_cfg` engine MMIO cap (a device region pinned to phys `0x9020000` on the
`virt` machine), (2) holds a 2 MiB DMA framebuffer region whose **guest-physical**
base it learns via Microkit's `region_paddr` setvar, (3) walks the `fw_cfg` file
directory over DMA to find `etc/ramfb`, (4) configures `ramfb` (geometry +
`XRGB8888` + the framebuffer phys addr) over the `fw_cfg` DMA-write interface,
and (5) renders a deos splash (a teal gradient, a bordered card, a legible
hand-rolled-font banner, and an 8-bar colour test pattern) into the framebuffer.
**QEMU scans it out**: a `screendump` of the running guest produces a `640x480`
frame whose pixels are exactly the bytes the PD wrote (verified pixel-by-pixel —
the top-of-gradient teal, the `(16,22,30)` card interior, and the RED/GREEN/WHITE
test bars all match). The pixel SOURCE is still a static in-PD splash, not
`servo-render`'s SWGL `RgbaFrame`, and the scene-authority teeth
(`compositor_pd.rs` T1/T2/T3) are not yet wired onto this scanout — those are the
named staging rungs in §4. **The bytes->glass mechanism is solved; what remains
is feeding it the right bytes and gating them.**

## 1. How to run it

```sh
cd sel4

# Build the PD ELF + link the graphical image (needs the Microkit SDK at
# $HOME/sel4-sdk/microkit-sdk-2.2.0 — run ./setup.sh once if absent).
make build-graphical

# THE VISIBLE WINDOW (macOS) — a real QEMU window scanning out the PD's pixels;
# serial stays on stdio so the boot diagnostics print alongside the window.
make run-graphical

# On Linux: the only change is the display backend.
make run-graphical QEMU_DISPLAY=gtk          # or sdl

# Window-less proof (CI / background / over SSH): the SAME image with
# -display none. The PD still configures ramfb + draws; its serial output proves
# resolution, framebuffer phys addr, the etc/ramfb selector, and bytes written.
make run-graphical-headless
```

The exact `run-graphical` QEMU invocation:

```sh
qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 2G \
  -device ramfb \
  -display cocoa,show-cursor=on \
  -device loader,file=build/dregg-graphical.img,addr=0x70000000,cpu-num=0 \
  -serial mon:stdio
```

`-device ramfb` is the display; the EL2 `virt` machine + `-cpu cortex-a53` are
unchanged from the headless firmament (the Microkit kernel is a hypervisor, so
`virtualization=on` is required). The image carries the `compositor-fb` PD; QEMU
provides the `ramfb` device the PD drives.

## 2. The serial proof (what the PD reports — verifiable with no window)

```
Booting all finished, dropped to user space
INFO  [sel4_capdl_initializer::initialize] Starting CapDL initializer
MON|INFO: Microkit Monitor started!

    ┌─────────────────────────────────────────┐
    │   deos · robigalia v0  —  GRAPHICAL      │
    │   compositor-fb PD : ramfb scanout       │
    └─────────────────────────────────────────┘
[compositor-fb] booted — the SOLE holder of the fw_cfg device cap + the
[compositor-fb] framebuffer DMA region (the graphical edge)
[compositor-fb]   fb vaddr=0x2000000 fb paddr=0x60400000 (region 2048 KiB; fb 1200 KiB)
[compositor-fb]   fw_cfg MMIO vaddr=0x6000000000 (phys 0x9020000, the virt fw_cfg engine)
[compositor-fb]   drew deos splash: 640x480 XRGB8888, 1228800 bytes written into the fb region
[compositor-fb]   fw_cfg file 'etc/ramfb' found: selector key = 0x0025
[compositor-fb]   ramfb CONFIGURED via fw_cfg: addr=0x60400000 fourcc=XRGB8888 640x480 stride=2560
[compositor-fb]   the QEMU display now scans out this PD's pixels. deos is on glass. ( ◕‿◕ )
```

Each line is load-bearing: `fb paddr=0x60400000` is the real guest-physical base
the `region_paddr` setvar reported (handed to `ramfb`, since the scanout engine
dereferences guest-physical, not the PD's vaddr); `etc/ramfb found: selector key
= 0x0025` proves the `fw_cfg` DMA **read** path (the directory walk) works; and
`ramfb CONFIGURED` (with no `ERROR` warning) proves the `fw_cfg` DMA **write** of
the `RAMFBCfg` landed. A `screendump` of the running guest confirms QEMU's side:
the scanned-out `640x480` frame is byte-for-byte the splash the PD drew.

## 3. The mechanism (how the bytes reach glass)

The whole device handshake is QEMU's `fw_cfg` + `ramfb` protocol, driven from a
confined PD exactly as the net-driver PD drives `virtio-net` (`sel4/dregg-pd/net`):

- **`fw_cfg` MMIO** on the `virt` machine lives at phys `0x9020000` (qemu
  `hw/arm/virt.c`): a data register at `+0x00`, a 16-bit **big-endian** selector
  at `+0x08`, and a 64-bit **big-endian** DMA-address register at `+0x10`. The PD
  maps a 4 KiB device page covering it (uncached), via a `<memory_region
  phys_addr="0x9020000">` it is the sole holder of.
- **The framebuffer** is a 2 MiB **huge-page-backed** DMA region (so
  `region_paddr` is a single 2 MiB-aligned physically-contiguous run — a
  scanned-out framebuffer must be contiguous in guest-physical space). The PD
  draws into its mapped vaddr; the region's guest-phys base (via `<setvar
  region_paddr>`) is what it hands to `ramfb`. The last 4 KiB of the region is
  the PD's `fw_cfg` DMA scratch (the DMA descriptor + the `RAMFBCfg` + the
  directory read buffer all need known guest-phys addresses too).
- **The `fw_cfg` DMA descriptor** is `{ control:u32, length:u32, address:u64 }`,
  all big-endian; the PD writes the descriptor's guest-phys addr to the DMA
  register to kick a transfer and spins until the engine clears the in-flight
  bits. It (a) DMA-reads the file directory (selector `0x19`) to find
  `etc/ramfb`'s selector key, then (b) DMA-writes the 28-byte `RAMFBCfg`
  (`{ addr:u64, fourcc:u32, flags:u32, width:u32, height:u32, stride:u32 }`, all
  big-endian; `fourcc = DRM_FORMAT_XRGB8888 = 0x34325258`) to that file. QEMU
  then scans `width x height` from `addr`.

Everything is hand-rolled in `sel4/dregg-pd/compositor-fb/src/main.rs` — no
external image/font/fw_cfg crate — keeping the firmament's minimal dep graph (the
runtime is only `sel4-microkit`). The RGBA splash and the 5x7 bitmap-font banner
are drawn straight into the framebuffer slice.

## 4. Staging — from a static splash to the full cockpit

This rung is **"a PD writes a static RGBA frame, and it scans out."** The path to
the desktop endgame, in honest rungs:

1. **`servo-render`'s SWGL renders INTO the compositor-fb framebuffer (HOST-side
   first).** `servo-render` already produces a real `RgbaFrame` (RGBA8) on the
   host via WebRender's SWGL (`servo-render/src/swgl_context.rs:100`,
   green today — see SERVO-ON-SEL4.md §0). The next step is a `present`-shaped
   seam that blits an `RgbaFrame` into this PD's framebuffer region instead of the
   static splash: swap `draw_splash` for "copy the latest frame from a shared
   region the renderer fills." On the host this is a `Vec<u8>` copy; on seL4 it is
   a shared-memory region between a render PD and this display PD. **Cost: small —
   the frame is already the right pixel format (RGBA8/XRGB8888) and size.**

2. **Wire the scene-authority teeth (`compositor_pd.rs` T1/T2/T3) onto the
   scanout.** Today this PD is a single full-screen surface with no gate. The
   `compositor_pd.rs` model already proves T1 non-overlap / T2 label-binding / T3
   focus-exclusivity (mirroring the Lean `Dregg2.Apps.Compositor` AppSpec) over a
   `present(region, contentDigest)` wire. Lifting that gate onto THIS framebuffer
   means: partition the framebuffer into the scene's regions, and let each app-PD
   `present` only its cap-authorized tiles — a refused present writes no pixel.
   The model is built (host-tested); this is the **welding** of the proven
   authority model onto the real scanout. **Cost: medium — the gate exists; the
   work is the per-region blit + the cross-PD `present` Endpoint.**

3. **The full starbridge-v2 cockpit on seL4 (the days-to-weeks frontier).** Two
   genuinely hard poles, both already named in SERVO-ON-SEL4.md and
   MATURATION-LEDGER.md THEME 3, NEITHER solved here:
   - **Servo-in-a-PD.** Servo is irreducibly multi-threaded (~8-14 `std::thread`s
     even single-process); the current `sel4-musl` substrate has no
     thread-creation backing. That is the central Stage-B blocker (SERVO-ON-SEL4.md
     §0) — ahead of graphics, ahead of `mozjs`. Until it lands, the render PD runs
     on the host and ships frames to this display PD over a region (rung 1).
   - **The executor-PD Lean runtime.** The cockpit's *authority* (the verified
     turn behind each surface's `sourceStateRoot`) still wants the Lean
     `execFullForestG` cross-compiled to `aarch64-sel4-microkit` (the
     executor-stub seat, `sel4/dregg-pd/executor-stub`). The embeddable-runtime
     spike already refuted the "blocker" framing (the runtime is measurable;
     `docs/EMBEDDABLE-LEAN-RUNTIME.md`), so this is a grind, not a research wall.

**What is built here (rung 0) vs the frontier (rung 3):** the **bytes->glass
mechanism** — a confined seL4 PD configuring real display hardware over `fw_cfg`
and scanning out a real framebuffer — is **solved and proven**. The remaining
work is feeding that framebuffer the right bytes (rung 1: SWGL frames) and gating
them with the proven scene authority (rung 2), with the two days-to-weeks poles
(Servo-in-a-PD, the Lean executor) the genuine frontier (rung 3). The glass is
real; the pixels on it are, for now, a splash.

## 5. The file set

- `sel4/dregg-pd/compositor-fb/` — the new PD crate (`Cargo.toml` + `src/main.rs`):
  the `fw_cfg`/`ramfb` driver + the RGBA splash renderer.
- `sel4/dregg-graphical.system` — the single-PD graphical assembly (the
  framebuffer DMA region + the `fw_cfg` device region + the PD).
- `sel4/Makefile` — `build-graphical` / `run-graphical` / `run-graphical-headless`
  targets + the `QEMU_AARCH64_GRAPHICAL` / `QEMU_DISPLAY` vars.
- `sel4/dregg-pd/Cargo.toml` — the new crate registered as a workspace member.
