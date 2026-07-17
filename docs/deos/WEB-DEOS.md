# WEB DEOS — the full gpui cockpit, in the browser

Web deos is the same cockpit as native, **bundled for and booted in a browser
tab**: the real `gpui` element-tree renderer on the `gpui_web` platform backend
(wasm32 + WebGPU canvas), driving the **same in-browser verified executor** the
native desktop drives. It is *not* a lesser "web skin" reimplementation of the
UI — it is one renderer, one model, two platforms (native windowing vs. a
browser canvas).

**State today:** the gpui-web cockpit is bundled (`web/pkg-gpui/`) and **paints a
real cockpit frame in headless Chrome** — the dock, the cell-list panel, the
multi-pane surfaces, text and color, the same `Scene` native draws — over a live
WebGPU canvas at full device-pixel resolution (e.g. 2560×1640 backing on a 2×
display). The captured proof frame is `web/cockpit-gpui-web-painted.png`. The
bundle, the build script, and the verification are in "[The full
cockpit](#the-full-cockpit-this-change)" and "[Honest verification
(browser-run)](#honest-verification-browser-run)" below.

This document states the architecture, the per-app backend map, the build
story, and — honestly — what the first slice proves versus the distance to full
parity.

## The two planes

A deos surface is two planes that meet at the cockpit:

- **Presentation plane** — `gpui`. The element tree, layout, the resolved
  `Scene`, paint. Native paints it through `gpui_macos`/`gpui_linux`/
  `gpui_windows` (Metal/Vulkan/D3D). The web paints the *same* `Scene` through
  `gpui_web` → `gpui_wgpu`'s `WgpuRenderer` → WebGPU on an `HtmlCanvasElement`.
- **Data plane** — the embedded verified executor (`starbridge_v2::world::World`
  over `dregg_turn::TurnExecutor`). It already compiles to wasm and runs
  in-tab today (see `starbridge-v2/web/src/lib.rs`, the `WebImage` atlas skin):
  every `act` is a real cap-gated turn through the verified executor, no server.

The whole point of web deos is to put the **native presentation plane on the
web platform over the already-wasm data plane** — so the browser tab is the full
cockpit, not a JSON viewer of it.

### Why gpui-in-browser is real (not aspirational)

The gpui fork (`emberian/zed@407a6ff`) ships a complete web backend,
`gpui_web` (`crates/gpui_web`): a full `Platform` implementation —
`WebPlatform` / `WebDispatcher` / `WebDisplay` / `WebWindow` plus events,
keyboard, and an HTTP client over `fetch`. `WebWindow::new` creates a
`<canvas>`, appends it to the document body, and binds a
`gpui_wgpu::WgpuRenderer` to it (`WgpuRenderer::new_from_canvas`); `WebPlatform::run`
asynchronously initializes the WebGPU context (`WgpuContext::new_web()`), then
runs the gpui app loop via `wasm_bindgen_futures::spawn_local`.

The boot path is *identical in shape* to native — only the platform constructor
differs:

```rust
// native (starbridge-v2/src/main.rs::run_window):
gpui_platform::application().run(|cx| {
    gpui_component::init(cx);
    cx.open_window(opts, |window, cx| cx.new(|cx| Cockpit::with_node(world, anchors, focus, None, seed)))
});

// web (starbridge-v2/web/src/cockpit_web.rs::boot_cockpit):
gpui_platform::web_init();
gpui_platform::single_threaded_web().run(|cx| {
    gpui_component::init(cx);
    cx.open_window(opts, |window, cx| cx.new(|cx| Cockpit::with_node(world, anchors, focus, None, seed)))
});
```

The two booters now construct the **same** `starbridge_v2::cockpit::Cockpit` over the **same** `World` — the only difference is the platform constructor and that the web boot opens the cockpit directly (the native boot front-doors through the login surface first).

`gpui_platform` is the abstraction seam: `current_platform()` selects
`MacPlatform`/`WindowsPlatform`/`gpui_linux` on native and
`gpui_web::WebPlatform` under `cfg(target_family = "wasm")`. So the cockpit's
`Render` impls — pure `div().child(...)` element trees — are platform-agnostic
and run unchanged on either.

## The full cockpit (this change)

`starbridge-v2/web/src/cockpit_web.rs` (gated `cfg(all(wasm32, feature =
"gpui-web"))`) boots the **REAL** `starbridge_v2::cockpit::Cockpit` — the same
comprehensive master interface the native desktop opens — on `gpui_web`, driving
the live in-browser `World`:

- The full cockpit element tree: the dock + the surface set + the
  **gpui-component widget library** (the text `Input`/`Button`/list set), not a
  reduced web-only view and not the JSON/atlas skin. It is the exact same
  `Cockpit::with_node(world, anchors, focus, None, seed)` the native `run_window`
  constructs (`node_url = None`, the data plane is the in-tab executor; the demo
  `seed` fills the image in live off the first-paint path).
- It drives the live image through the embedded executor: every affordance click
  is a **real cap-gated turn through the verified executor in-tab** (the
  `World::commit_turn` seam), with the post-state re-reflected on the next frame —
  the same mechanism as native.
- The wasm entrypoint `boot_cockpit()` (wasm-bindgen) seeds `world::demo_genesis`
  (the at-rest genesis image + the deferred demo seed, the same the native cockpit
  boots), boots a single-threaded web gpui app, registers the cockpit fonts
  (Lilex + IBM Plex) and calls `gpui_component::init(cx)` (the widget globals —
  exactly as native boot does), opens a window (creating the WebGPU canvas), and
  mounts the cockpit.

**What it proves (the BUNDLED + BROWSER-RUN state, honestly):** the gpui-web
cockpit is **bundled** (`web/pkg-gpui/`, via `build-gpui.sh` → `wasm-bindgen
--target web`, exporting `boot_cockpit`) and **runs in a real (headless-Chrome)
browser**: `init()` resolves, `boot_cockpit()` is invoked, the `gpui_web`
platform **initializes WebGPU successfully** (`gpui_wgpu::wgpu_context: Selected
GPU adapter … WebGPU context initialized successfully`) and creates the cockpit
`<canvas>`.

It then **paints a real cockpit frame in headless Chrome.** After WebGPU init the
`gpui_web` run-loop runs the requestAnimationFrame + ResizeObserver loop, the
canvas backing store resizes to the full device-pixel viewport (e.g. 2560×1640
on a 2× display), and the cockpit element tree draws — the verification reports
`canvas backing max : 2560x1640 (PAINTED a real frame)` and `run-loop reentrancy
: false`. The captured frame is `web/cockpit-gpui-web-painted.png`.

**The fix.** Earlier this stopped before first paint: the run-loop threw `closure
invoked recursively or after being dropped` and the canvas stayed 1×1. The cause
was a lifetime bug in the `gpui_web` fork's app boot, **not** a scheduler
re-entrancy. On the web, `Platform::run` is fire-and-forget — WebGPU init and
`on_finish_launching` run inside a `spawn_local` future and `run()` returns to JS
immediately, with the browser owning the event loop. But `Application::run` then
dropped the owning `Application(Rc<AppCell>)` when it returned (and the spawned
future's clone dropped when `on_finish_launching` finished), destroying the
`AppCell` → `cx.windows` → the `WebWindow` → its `_raf_closure` /
`_resize_observer_closure`. The browser's already-scheduled rAF and registered
ResizeObserver then fired on *freed* closures — wasm-bindgen's "invoked … after
being dropped" — before any frame painted. The fix (`crates/gpui/src/app.rs`,
`emberian/zed` fork) leaks the owning `Rc` on wasm (`std::mem::forget(self)`) so
the app lives for the page's lifetime, mirroring native platforms where `run()`
blocks forever in the OS event loop.

(The gpui-free `WebImage` JSON skin — `web/pkg`, `web/pkg-release`, exports
`webimage_*` — also paints+drives in headless Chrome, verified separately.)

### The module lift (what made it reachable)

`cockpit`, `views` (and the `dock` engine they reach) were binary-private `mod`s
in `starbridge-v2/src/main.rs` — a separate cdylib (the `web/` crate) could not
name `cockpit::Cockpit`. They now live in the **library** behind a gpui-gated
`pub mod` (`#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))] pub mod
cockpit;` in `src/lib.rs`). This is a pure module-placement change — no cockpit
internal logic moved. Three supporting moves:

- `extern crate self as starbridge_v2;` in `lib.rs` (gpui-gated) so the cockpit's
  many `starbridge_v2::dock` / `starbridge_v2::world` / … self-references resolve
  unchanged now that they live *inside* the crate that used to be their dependency.
- `main.rs` reaches the lifted modules through `use starbridge_v2::{cockpit,
  login};`, leaving every `cockpit::Cockpit` / `login::LoginSurface` path in the
  bin untouched.
- `replay::replay_panel` (a gpui element the cockpit places) was gated on
  `gpui-ui` ALONE; widened to the union gate so the web build sees it too.

`login` is the one lifted module gated `gpui-ui`-ONLY (native), not the union: it
drives the DURABLE-session-image path (`session::{open_session_world,
session_base_dir}` + `LoginManager::logout_durable`, all `cfg(not(wasm32))`
filesystem code). The web boot mounts `Cockpit` directly — the in-tab image is
ephemeral — so it never needs the login front door. (If a web login front door is
wanted later, its ceremony minus the durable-image persistence wasm-compiles; the
gate would widen then.)

The native build is unaffected (`cargo check --features native-full` green; the
cockpit/views/dock gate is the union `any(gpui-ui, gpui-web)`, native-full enables
`gpui-ui`).

## The build story

One script bundles it — `starbridge-v2/web/build-gpui.sh`:

```
cd starbridge-v2/web
./build-gpui.sh                 # release (default)
# = cargo build --release --target wasm32-unknown-unknown -p starbridge-web --features gpui-web
#   then: wasm-bindgen --target web --out-dir pkg-gpui <…>/release/starbridge_web.wasm
#   then: wasm-opt -Oz (if installed)
```

This produces `web/pkg-gpui/{starbridge_web.js, starbridge_web_bg.wasm, …}`,
**exporting `boot_cockpit`** — which is exactly what `web/cockpit_gpui.html`
imports (`import init, { boot_cockpit } from './pkg-gpui/starbridge_web.js'`).
The default `web/pkg` and `web/pkg-release` bundles export only the gpui-free
`webimage_*` skin; `pkg-gpui` is the bundle the gpui cockpit needs and is now
produced.

> wasm-bindgen-cli version must MATCH the resolved `wasm-bindgen` crate
> (`starbridge-v2/Cargo.lock` → 0.2.125); a mismatched CLI fails with a schema-
> version error. `cargo install -f wasm-bindgen-cli --version <that>`.

The default build (`cargo build … -p starbridge-web`, no features) is unchanged —
it produces the gpui-free `WebImage` atlas skin. `gpui-web` is **purely
additive**: it turns on a new `starbridge-v2/gpui-web` feature (gpui +
gpui_platform + gpui-component, NO native sub-features) plus the gpui crates in
the web crate, and compiles in `cockpit_web`.

**Compile + bundle: green.** The `gpui-web` release build is green (`Finished
release profile in ~2m`): the full `starbridge-v2` lib (the lifted cockpit +
gpui-component widget tree) AND the `starbridge-web` cdylib (the `boot_cockpit`
mount of the real `Cockpit`) both compile to `wasm32-unknown-unknown`, and the
`pkg-gpui` wasm-bindgen bundle is produced (release wasm ~28M unoptimized; far
smaller through `wasm-opt -Oz`, not installed in this environment).
gpui-component compiles with `default-features = false` (its tree-sitter syntax
grammars are all opt-in features, none enabled) — no native font/clipboard/
tree-sitter leaf force-pulls onto the wasm path.

## Honest verification (browser-run)

The bundle was loaded and run in **headless Chrome** (Chrome 151 dev, WebGPU via
`--enable-unsafe-webgpu --use-angle=metal`), the same browser-run bar the
gpui-free `WebImage` skin already passes. What was observed, in order:

1. `./pkg-gpui/starbridge_web.js` + `_bg.wasm` fetch (200), `init()` resolves.
2. `boot_cockpit()` is invoked (no synchronous throw).
3. `[INFO] gpui_web::dispatcher` falls back to single-threaded (no
   SharedArrayBuffer — expected without COOP/COEP headers).
4. `[INFO] gpui_wgpu::wgpu_context: Selected GPU adapter … (BrowserWebGpu)`
   then `[INFO] gpui_web::platform: WebGPU context initialized successfully`.
   **WebGPU is up; the cockpit `<canvas>` is created.**
5. The `gpui_web` run-loop runs: rAF + ResizeObserver fire, the canvas backing
   store resizes to the full device-pixel viewport, and the cockpit element tree
   draws. The harness reports `canvas backing max : 2560x1640 (PAINTED a real
   frame)` and `run-loop reentrancy : false`; the captured frame is
   `web/cockpit-gpui-web-painted.png`.

So the verified result is: **bundled + browser-loaded + `boot_cockpit` invoked +
WebGPU context initialized + the cockpit paints a real frame on a live WebGPU
canvas.** The earlier `closure invoked recursively or after being dropped` ceiling
was a lifetime bug in the fork's app boot (the `Application` was dropped while the
browser still held its scheduled rAF/ResizeObserver closures); it is fixed by
leaking the owning `Rc` on wasm in `Application::run` (see "The fix" above).

### The minimal feature set (what's ON / what's deliberately OFF)

The cockpit's `native-full` feature drags three native-only resource holdouts.
The new `gpui-web` feature path turns them **off**:

| Feature | native-full | gpui-web (wasm) | why |
| --- | --- | --- | --- |
| `embedded-executor` | on | **on** | the data plane — already wasm-clean (proven by the atlas skin) |
| `gpui` + `gpui_platform` | on (native platform) | **on (gpui_web)** | the presentation plane; `gpui_platform` forwards to `gpui_web` on wasm32 |
| `gpui_platform/{runtime_shaders,x11,wayland}` | on | **off** | macOS Metal / Linux X11+Wayland windowing — inert on wasm, kept out for clarity |
| `web-shell` (servo/libservo) | on | **off** | servo is native-only (C++ swgl / mozjs) — the one app with no in-browser-gpui path |
| `dev-surfaces` (deos-zed editor + deos-terminal) | on | **off** | alacritty PTY + `RealFs` are native resources (the *gpui UI* of these CAN run on web; the *backend* needs a wire — see app map) |
| `render-capture` (gpui `test-support` offscreen wgpu) | on | **off** | the native headless bake; the browser paints to a live canvas, no offscreen capture |
| `live-node` (reqwest blocking) | on | **off** | reqwest's blocking client is native; a web live-node uses `fetch`/WebSocket (future) |

So the wasm cockpit feature set is exactly: **cockpit gpui UI + embedded
executor + gpui_web**, with web-shell / dev-surfaces / render-capture / live-node
off. The data plane was already fine on wasm; `gpui_web` swaps in for the native
gpui platform; the holdouts are the native-resource backends, each addressed in
the app map below.

## Per-app backend map (the node as the web backend)

Each deos app is **gpui UI (renders in-browser today)** + a **backend wire**.
The UI half is platform-agnostic gpui and runs on `gpui_web`; the backend half
is where a native resource lives, and the web build wires it to `node/` (over
HTTP/WebSocket) or to the in-browser executor.

| App | gpui UI in-browser | Backend wire needed for web |
| --- | --- | --- |
| **Cockpit / inspectors** | ✅ today (this slice: home/inspector/affordances; the full surface set is element-tree work) | none — drives the in-browser `World` directly |
| **Terminal** (`deos_terminal::TerminalView`) | gpui grid renders on web; alacritty's PTY does not exist in a browser | **WIRED** — PTY over a WebSocket. `starbridge_web::pty_ws` owns both ends: a native WS↔PTY server (`pty_ws::serve`, the `starbridge-web-pty-ws` bin) that gives each connection a real `$SHELL` on a `portable-pty` PTY and bridges bytes, and the wasm `WsTransport` (a `web_sys::WebSocket`) the browser grid drives. Proven end-to-end by `starbridge-v2/web/tests/pty_ws_e2e.rs` (real shell, real socket, `echo`/`pwd` bytes return). The net-cap gate (origin/shell/cwd) is the named next wire at the per-connection accept. |
| **Editor** (`deos_zed::Editor`) | gpui editor renders on web | swap `RealFs::arc()` for a **firmament-backed `Arc<dyn Fs>`** over the in-browser executor (the editor already takes `Arc<dyn Fs>` — see `editor_surface.rs`), or an `Fs` over `node/`'s file API |
| **Chat** (`deos_matrix::chat::ChatView`) | gpui chat renders on web | `matrix-rust-sdk` (`matrix-sdk 0.18`) **wasm-compiles** (it targets wasm32 with a `fetch`/IndexedDB stack); the headless `deos-matrix` core compiles to wasm and the gpui `ChatView` paints it — the cleanest fully-in-tab app after the cockpit |
| **Web-shell** (servo / libservo) | ❌ native-only | servo is a native C++/mozjs engine; there is no in-browser servo. The browser tab already *is* a web engine, so a web-deos "web-shell" surface would be a sandboxed `<iframe>`/native browsing context behind the net-cap gate, not gpui-rendered servo. This is the one app with no gpui-on-web path. |

So three of the four self-hosting apps (terminal, editor, chat) keep their gpui
UI on `gpui_web` and differ only in **where the backend resource lives** — a
node websocket (terminal), an `Fs` impl (editor), or a wasm-native SDK (chat).
Servo is the lone native-only holdout.

## Distance to full parity (honest)

The full `cockpit::Cockpit` is now **bundled, booted, and PAINTING in-browser**
(WebGPU initializes and the cockpit element tree draws a real frame in headless
Chrome — `web/cockpit-gpui-web-painted.png`; see "Honest verification" above).
All three former blockers are CLOSED — including the run-loop reentrancy, fixed
by leaking the owning `Rc` on wasm (see "The fix"). The only remaining gaps are
the native-resource backends:

1. **`cockpit::Cockpit` is binary-private.** ✅ CLOSED. `cockpit`/`login`/`views`
   were lifted from `main.rs` into the library behind a gpui-gated `pub mod`
   (the union gate `any(gpui-ui, gpui-web)`), with `extern crate self as
   starbridge_v2` so their self-references resolve unchanged. No cockpit
   internals moved. The `web/` cdylib now names `Cockpit` directly.
2. **gpui-component on wasm.** ✅ COMPILES. The vendored `gpui-component` (text
   `Input`, `Button`, the shadcn-style set) builds to `wasm32-unknown-unknown`
   with `default-features = false` (its tree-sitter syntax grammars are all
   opt-in features, none enabled). `gpui_component::init(cx)` is called at web
   boot exactly as native does.
3. **The `gpui_web` run-loop reentrancy.** ✅ CLOSED. Earlier the single-threaded
   run-loop threw `closure invoked recursively or after being dropped` before
   first paint. This was a lifetime bug in the `gpui_web` fork's app boot (the
   `Application`'s owning `Rc` was dropped while the browser still held its
   scheduled rAF/ResizeObserver closures), NOT a scheduler re-entrancy. The fix
   leaks the owning `Rc` on wasm in `Application::run` (`crates/gpui/src/app.rs`,
   `emberian/zed` fork; see "The fix"). The cockpit now paints a real frame.
4. **The native-resource backends** (terminal PTY, editor Fs, web-shell servo) —
   each needs its wire per the app map.
   - **Terminal PTY** — ✅ **WIRED + PROVEN.** `starbridge_web::pty_ws` is the
     WS↔PTY bridge (native server + wasm `WsTransport`), proven end-to-end by
     `starbridge-v2/web/tests/pty_ws_e2e.rs` (`2 passed`: a real `$SHELL` on a real PTY echoes
     `echo`'s marker and returns `pwd`'s cwd over a real WebSocket — the exact
     byte path the browser `WsTransport` speaks). The remaining seam is purely the
     gpui-web *view* wiring: the cockpit's terminal pane is `dev-surfaces`
     (alacritty, native-only) today, so the gpui-web cockpit must mount a
     `WsTransport`-backed grid view instead of the alacritty one to surface this
     backend in-tab. The backend it would dial exists and runs.
   - **Editor Fs** — architecturally wasm-reachable: `deos_zed`'s `FirmamentFs`
     core is deliberately gpui-free and built on the SAME `dregg-turn`/`dregg-cell`
     executor spine that already runs in the tab (see deos-zed's wasm32 target
     block), so a save is an **in-tab receipted turn** — no transport needed,
     unlike the terminal. The seam is the build/mount wiring: `dev-surfaces`
     (which pulls `deos-zed`) is off the `gpui-web` feature, so the web cockpit
     does not mount the editor pane yet; enabling deos-zed's wasm Fs core on the
     gpui-web build + opening a `FirmamentFs`-over-`World` editor pane on wasm is
     the wire. No new server.
   - **Chat** — `matrix-sdk 0.18` wasm-compiles (IndexedDB store + `js` plumbing +
     `spawn_local`, per deos-matrix's `cfg(target_family = "wasm")` block), so the
     backend is in-tab against a live homeserver. And chat now has a
     **renderer-independent card**: `deos_matrix::chat_view::chat_view` projects the
     real `ChatCard` (timeline, live turn-count bind, composer input firing the real
     `send_turn`) to the serializable view-tree, mounted through the same
     CardPane/dock bridge as the composer (`build_chat_card_surface`,
     `dock/card_surface.rs`) — so chat reaches every `deos-view` backend, not just
     gpui. Remaining: `dev-surfaces` (which pulls `deos-matrix`) is off the gpui-web
     build — the wire is enabling deos-matrix's wasm graph on gpui-web + an opener
     that mounts the chat card surface.
   These surfaces are feature-gated OFF the web build (`dev-surfaces`/`web-shell`
   are not in the `gpui-web` feature). The UI for terminal/editor/chat is already
   gpui and web-ready; the terminal *backend* now runs, and the editor/chat
   backends are wasm-reachable in-tab — the residual work is the per-surface
   gpui-web view mount.

"Can gpui *boot* in the browser" is settled — `gpui_web` is a complete platform,
the full cockpit bundle loads, and WebGPU initializes. "Does gpui *paint* the
cockpit in the browser" is **now settled too**: after the `Rc`-leak fix (#3) the
run-loop drives rAF + ResizeObserver and the cockpit element tree draws a real
frame in headless Chrome (`web/cockpit-gpui-web-painted.png`). The remaining work
is the three native-resource backends (websocket / Fs / wasm-SDK) — of which the
terminal PTY wire is already built + proven — with servo the single native-only
surface.

## Files

- `starbridge-v2/web/src/cockpit_web.rs` — the `boot_cockpit` wasm entrypoint
  that mounts the REAL `starbridge_v2::cockpit::Cockpit` on `gpui_web`.
- `starbridge-v2/web/src/lib.rs` — declares `cockpit_web` (gated) + `pty_ws` (the
  terminal backend) alongside the existing `WebImage` atlas skin.
- `starbridge-v2/web/src/pty_ws.rs` — **the terminal backend wire.** Native:
  `serve`/`bind_serve` (the WS↔PTY bridge over `portable-pty` + `tokio-tungstenite`).
  Wasm: `WsTransport` (a `web_sys::WebSocket` feeding PTY bytes through `vte` into
  a render grid). Shared: the `WireMsg` wire codec (binary frames = PTY data, JSON
  text frames = resize/exit control). One wire, two ends, one crate.
- `starbridge-v2/web/src/bin/pty-ws.rs` — the `starbridge-web-pty-ws` server bin
  (`required-features = ["pty-ws-server"]`); `serve`s `$SHELL` on a PTY per WS conn.
- `starbridge-v2/web/tests/pty_ws_e2e.rs` — the end-to-end proof: stand up the
  in-process server on an ephemeral port, drive a real shell over a real WebSocket,
  assert `echo <marker>` and `pwd` bytes return over the socket. `2 passed`.
- `starbridge-v2/web/Cargo.toml` — the `gpui-web` feature (additive; pulls gpui +
  gpui_platform + gpui-component + web-sys + `starbridge-v2/gpui-web`).
- `starbridge-v2/Cargo.toml` — the `gpui-web` feature on the main crate (gpui +
  gpui_platform + gpui-component without native sub-features; web-shell/
  dev-surfaces/render-capture/live-node off).
- `starbridge-v2/src/lib.rs` — the lifted `pub mod cockpit; pub mod login; pub
  mod views;` (+ `dock`), gpui-gated `any(gpui-ui, gpui-web)`, and `extern crate
  self as starbridge_v2`.
- `starbridge-v2/src/main.rs` — `use starbridge_v2::{cockpit, login};` (the bin
  reaches the now-lib modules).
- `starbridge-v2/web/cockpit_gpui.html` — boots the `pkg-gpui` bundle and calls
  `boot_cockpit()`.
- `starbridge-v2/web/build-gpui.sh` — the one-command bundle: cargo build
  (`--features gpui-web`, wasm32) → `wasm-bindgen --target web --out-dir
  pkg-gpui` (exports `boot_cockpit`) → optional `wasm-opt -Oz`.
- `starbridge-v2/web/pkg-gpui/` — the produced bundle (`starbridge_web.js` +
  `_bg.wasm`, exporting `boot_cockpit`) that `cockpit_gpui.html` imports.
