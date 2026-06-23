# The FirmamentFs seam

deos-zed is a real code editor that edits real files inside deos. Its single
load-bearing design decision is that **the editor never touches a filesystem
directly** — every file operation goes through one trait, `Fs`
(`src/fs.rs`). Today that trait is backed by `RealFs` (`std::fs`). Tomorrow it is
backed by `FirmamentFs`, where a file is a sovereign cell and a save is a
receipted dregg turn. That transition is a **one-impl change**: no editor, no
file-tree, no UI code moves.

This document specifies that seam.

## The trait

```rust
pub trait Fs: Send + Sync + 'static {
    fn load(&self, path: &Path) -> Result<String>;
    fn save(&self, path: &Path, content: &str) -> Result<()>;
    fn read_dir(&self, path: &Path) -> Result<Vec<DirEntry>>;
    fn metadata(&self, path: &Path) -> Result<Metadata>;
    fn backend_label(&self) -> &'static str;
}
```

It mirrors the subset of Zed's `fs::Fs` that an editor actually exercises:
`load` on open, `save` on save, `read_dir` + `metadata` for the file tree. It is
kept small and synchronous on purpose — the editor already runs file I/O off a
background spawn, and a synchronous trait is far simpler to satisfy with a
`FirmamentFs` whose `save` is a turn.

The editor holds an `Arc<dyn Fs>` and depends on nothing else. `backend_label()`
is surfaced in the editor's status line, so which backing store is in use is
**visible to the user** — the firmament swap is observable, not silent.

## RealFs (today)

`std::fs`, with a write-to-temp-then-rename `save` so a crash mid-write can never
truncate the user's file. This is the default and it works now: the demo seeds a
real file, the editor opens + edits + saves it, and the bytes on disk change
(verified independently of the seam — see `cargo run --bin demo -- --verify`).

## FirmamentFs (the next step)

A file becomes a **cell**; a save becomes a **receipted turn**. The mapping:

| `Fs` method     | firmament realization |
|-----------------|-----------------------|
| `load(path)`    | resolve `path` → a read cap through the directory namespace; read the cell's content substance. A read is authority-checked but does not mutate state, so it needs no turn. |
| `save(path, c)` | a dregg **turn**: exercise a write cap over the file-cell, replacing its content; the turn leaves a verifiable **receipt**. "Save" becomes an attestable event, not an opaque syscall. |
| `read_dir(p)`   | `DirectoryCell::list()` — the capability-scoped listing (`rbg/src/directory.rs`). Holding the directory cap *is* the authority to enumerate it. |
| `metadata(p)`   | `DirectoryCell::get(name)` → resolve to a sturdy ref + cell kind. |

### The path → cap namespace

A path like `/proj/src/main.rs` resolves component-by-component through
`DirectoryCell`s (`rbg/src/directory.rs`):

- Each `DirectoryCell` maps names → `(cap, version)` via `get(name)`, mutates via
  an atomic CAS `swap(name, version, cap)`, and lists via `list()`.
- Directories contain directories (recursive scoping), so a path walk is a chain
  of `get` calls ending at a leaf **file-cell**, whose content substance is the
  editable text.
- The **root `DirectoryCell` cap is the editor's mount point**. The editor can
  only see and edit what that cap reaches — which is exactly the firmament
  confinement story: one cap across distance
  (`sel4/dregg-firmament/`), the n=1 collapse of local-seL4-cap ↔ distributed
  dregg-cap ↔ surface.

### What `save` actually is

`save` is the one mutating operation, so it is the one that becomes a turn:

1. Build a turn that spends a write cap on the file-cell and binds the new
   content as the cell's next content substance (Σδ=0 over the content-cell: the
   old content note is nullified, the new one created).
2. Submit through the executor; obtain the **receipt** — the proof-carrying
   token that this exact edit happened under this exact authority.
3. The receipt is the editor's "saved" acknowledgement, and it is independently
   verifiable: a light client can confirm the file now holds this content
   **without trusting the editor**.

This is the whole point of the seam. It upgrades "the editor wrote a file" from
an unwitnessed side effect into a **witnessed, attenuable, receipted turn**.

## FirmamentFs is real — behind the `firmament` feature

`src/fs/firmament.rs` now ships a LIVE impl: build with `--features firmament`
and `FirmamentFs` owns an in-process `dregg_cell::Ledger` + `dregg_turn::TurnExecutor`
(the SAME verified spine starbridge-v2's `World` wraps). A file is a cell; a
`save` is a real cap-gated `SetField` turn driven through the executor, leaving a
genuine `TurnReceipt`. The feature is OFF by default so the `RealFs` build stays
light and the lean / standalone builds never link the Lean archive — with the
feature off, the same file compiles a stub whose methods return a clear "rebuild
with `--features firmament`" error (so the trait is satisfied either way).

What is real vs. sketched in the first slice:

- **Real:** `load`/`save`/`read_dir`/`metadata` over cells; `save` is a genuine
  executor turn (cap-gated, journaled, finalized — `pre_state_hash != post_state_hash`,
  a chained `TurnReceipt` per save, in-band refusal when the editor lacks the
  file's edit cap); content round-trips through the ledger's committed `fields_map`
  (the same overflow map dregg-doc's `ExecutorDrivenDoc` uses), so the file cell's
  `fields_root` — which the canonical state commitment absorbs — commits to the
  content a light client can trust.
- **Sketched (first slice):** the path → cell namespace is an in-memory flat
  `BTreeMap<PathBuf, CellId>` (the simpler alternative this doc named), not yet
  `rbg`'s richer `DirectoryCell` name→cap map; and the host-handoff (a deos image
  handing `FirmamentFs` its own mounted root + shared executor) is the next wire.

Proof: `cargo test --features firmament` (unit + `tests/firmament_fs.rs`) and
`cargo run --features firmament --bin demo -- --firmament`.

## FirmamentFs IN THE BROWSER — the in-tab executor (wasm32)

The editor renders in the browser on `gpui_web` (the host's WebGPU canvas), but a
browser tab has no `std::fs` — `RealFs` cannot back it. `FirmamentFs` can: it
needs no disk, only an in-process `Ledger` + `TurnExecutor`, and that executor is
**wasm-clean** (it is the same no-Lean-link verifier-shape executor
starbridge-web drives in the tab). So the in-browser editor's `Fs` binds to a
`FirmamentFs` running the IN-TAB executor — a file is a cell, a save is a turn, in
the browser's own kernel.

The crate is split so this compiles:

- The `Fs` seam (`src/fs.rs` + `src/fs/firmament.rs`) is **gpui-free**. It is the
  only surface gated OUT of the `gui` feature.
- `gui` (on by default) carries the gpui editor / file-tree / doc-viewer. gpui's
  *native* windowing (font-kit/x11/wayland) cannot link to wasm32, so the wasm
  build is `--no-default-features --features firmament`: the executor-backed `Fs`
  core, no gpui. The browser *renderer* is the host's `gpui_web` (starbridge-web),
  not deos-zed's own gpui linkage — the same renderer/executor split starbridge-web
  already rides.
- The dregg executor crates are **target-split** (mirroring `starbridge-v2/Cargo.toml`):
  on native they resolve with default features (the Lean-linked producer); on
  `wasm32-unknown-unknown` they resolve `default-features = false` + `prover`
  (no Lean archive, the verifier shape) plus the transitive wasm forcings
  (getrandom backends, `clear_on_drop/no_cc`, `lockstitch/portable`,
  `biscuit-auth/wasm`). The SAME `FirmamentFs` source compiles for both.

Build + prove:

```
# native default (gpui editor + RealFs default) — unchanged
cargo build
# the in-browser Fs core, native (the executable save-is-a-turn proof)
cargo test  --no-default-features --features firmament --test firmament_fs
# the in-browser Fs core, FOR THE TAB
cargo build --no-default-features --features firmament --target wasm32-unknown-unknown
```

The wasm-runtime distance: the crate **compiles to wasm32** and the
save-is-a-turn path runs in the gpui-free core (the SAME code the wasm target
compiles) under a native `cargo test`. The remaining step to run it literally in a
tab is a `wasm-bindgen` shim + a JS harness that holds the `Arc<dyn Fs>` and
drives `gpui_web` — wiring, not a substrate question (the executor is already
proven to compile and run for the target).

## How the host wires it

In starbridge-v2, the cockpit holds a live `World` with the embedded executor
and a mounted root directory. To make the editor firmament-backed:

1. Construct a `FirmamentFs::new(root_cap, executor)` (signature lands when the
   host types are threaded in) and box it as `Arc<dyn Fs>`.
2. Hand that `Arc<dyn Fs>` to `EditorPane::new(...)`
   (`starbridge-v2/src/dock/editor_surface.rs`) instead of `RealFs::arc()`.

Nothing in the editor or the file tree changes. The editor that was editing disk
files is now editing cells, with receipted saves, because the only thing that
ever spoke to a filesystem was the `Fs` trait.
