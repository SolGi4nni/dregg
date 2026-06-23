# Embedding the REAL Zed in deos — recon + design

**Goal.** The full Zed `Workspace` running as a deos surface: the real `editor`
+ `project_panel` + integrated terminal + agent/assistant panel + search + git
UI + outline panel + command palette + the dock/pane chrome — all of Zed —
with its filesystem backed by `FirmamentZedFs` (files = cells, save = a verified
turn).

This doc is grounded in a **build-proven** foundation slice (below) and maps the
staging to the full embed. Everything labeled BUILT/PROVEN is verified by
`cargo build`/`cargo test` in this crate; everything labeled DESIGNED is mapped
but not yet wired.

---

## 0. What is BUILT + PROVEN (the foundation)

The mechanics that the entire full-Zed embed depends on are proven here:

1. **The Zed crates pull + compile at our gpui rev.** `editor` + `workspace` +
   `project` + `language` pulled as git deps at the SAME zed fork rev our `gpui`
   comes from (`emberian/zed@407a6ff`) **compile and link** —
   `cargo build --features full-zed` is GREEN (the editor crate + its ~96
   zed-fork transitive crates / ~983 total packages, including `wasmtime`,
   `cranelift`, `lsp`, `dap`, `terminal`, `tree-sitter`, built in ~2 minutes).
   The `[patch.crates-io]` table (replicating the zed fork's own patches +
   deos-zed's proof-dep overrides) makes resolution work first try; **nothing
   fought.**

2. **`FirmamentZedFs` implements Zed's async `fs::Fs` trait over the cell-ledger**
   (`src/firmament_zed_fs.rs`). It wraps deos-zed's gpui-free `FirmamentFs` (a
   file IS a cell; a save IS a cap-gated `SetField` turn through a real in-process
   `TurnExecutor`, leaving a `TurnReceipt`) and adapts the synchronous cell ops
   to Zed's `async fn load/save/create_file/rename/read_dir/metadata/...`.
   `tests/firmament_zed_fs.rs` drives it **through `Arc<dyn fs::Fs>`** — exactly
   the surface a Zed `Project` holds — and asserts: a save is a receipted turn,
   conservation holds (Σδ=0), `read_dir`/`metadata` expose the namespace.

3. **A real Zed `Project` mounts over `FirmamentZedFs` and saves a turn**
   (`tests/project_over_cells.rs`, `--features full-zed`). It builds an actual
   `Project::test` whose `Fs` is the cell-ledger, the worktree scan SEES the cell
   namespace, `project.open_buffer` loads a seeded file-CELL into a real Zed
   `language::Buffer`, a real Zed rope `edit` mutates it, and
   `project.save_buffer` fires `Fs::save(path, &Rope, _)` → **a verified turn on
   the ledger.** This is the load-bearing proof: Zed's project/worktree/buffer
   layer drives the cell-Fs end to end.

What this means: the seam is real and the crate-pull mechanics are real. The
full embed is **wiring + boot scaffolding on top of a proven foundation**, not a
research risk.

### What's stubbed in the `Fs` adapter (honest)

`FirmamentZedFs` fully implements the content + structure methods
(`load`/`load_bytes`/`save`/`atomic_write`/`write`/`create_file`/`create_dir`/
`rename`/`copy_file`/`metadata`/`is_file`/`is_dir`/`read_dir`/`canonicalize`/
`open_sync`). It STUBS (explicit `bail!`/empty, never a silent wrong answer):
`watch` (empty event stream + no-op watcher — the worktree's initial scan still
populates), `open_repo`/`git_*` (no git over cells yet), `trash`/`restore`,
`open_handle`, `extract_tar_file`, `create_symlink`, `read_link`. None of these
are exercised by the editor/project slice; each is a named follow-on below.

---

## 1. The full-Zed dependency weight (measured)

Pulling `editor`→`workspace`→`project`→`language` already drags in essentially
the whole Zed app graph:

- **96 zed-fork crates**, **983 total packages**.
- Heavy transitive crates present: `wasmtime` + `cranelift-codegen` (the
  WASM **extension host**), `lsp`, `dap`, `terminal`, `tree-sitter`, `resvg`,
  `prettier`, `node_runtime`, `client`/`rpc`/`collab`-adjacent crates.

Adding the remaining **panels** (`project_panel`, `terminal_view`/`terminal`,
`agent`/`agent_ui`, `git_ui`, `search`, `outline_panel`, `command_palette`,
`title_bar`, `collab_ui`, `onboarding`) adds **UI crates** but little NEW
transitive weight — they sit on the `workspace`/`project`/`editor` base already
in the graph. The `zed` binary crate itself (the app shell) is the one crate we
do NOT pull (we replace its `main()` with deos boot scaffolding — §3).

All these panel crates are PRESENT at our rev (verified): `zed`, `workspace`,
`project`, `project_panel`, `terminal`, `terminal_view`, `agent`, `agent_ui`,
`git_ui`, `search`, `outline_panel`, `outline`, `command_palette`, `title_bar`,
`collab_ui`, `onboarding`, `theme`, `settings`, `client`, `lsp`, `dap`,
`extension`, `extension_host`, `language_extension`. (Absent: `assistant_context`,
`welcome` — folded into `agent`/`onboarding` upstream at this rev.)

### Things that will fight (the honest risk list for the full embed)

- **`node_runtime`** — LSP servers + many extensions shell out to a Node binary.
  The foundation uses `NodeRuntime::unavailable()` (no LSP servers spawn). Real
  LSP needs a Node binary in the deos image OR `NodeRuntime` pointed at a
  confined Hermes-style process. **Designed, not built.**
- **`extension_host`** (wasmtime) — loads `.wasm` extensions; needs a writable
  extensions dir + network to fetch them. Over cells this becomes an
  extension-cell store. Can be left disabled for the first full-Workspace embed.
- **`dap`** (debugger) — spawns debug adapters; same shell-out concern as Node.
- **`client`/`collab`** — Zed's auth/collab backend. The foundation uses
  `FakeHttpClient::with_404_response()` (offline). The deos embed runs offline /
  points collab at a dregg-Matrix bridge (the MEMBRANE star) — a deos-native
  substitution, designed separately.
- **`terminal`** — needs a real PTY. On the native deos desktop this is fine
  (the same PTY the deos cockpit dock already drives). On seL4/in-browser it
  needs the confined-PTY path.
- **The windowed render** is not runnable headlessly in CI; the proof is the
  **build + the project-over-cells turn test**. A live windowed `Workspace`
  render is the on-desktop demo, not a CI gate (same posture as deos-zed's
  `--screenshot` offscreen path).

---

## 2. The panel map (what each surface needs)

Zed registers panels via `workspace.add_panel(panel, window, cx)` after each
`Panel::load(workspace_handle, cx)` resolves (see
`crates/zed/src/zed.rs::initialize_panels`). The deos embed replicates exactly
this, panel-by-panel:

| Panel / surface        | crate              | needs over FirmamentZedFs                                  | stage |
|------------------------|--------------------|------------------------------------------------------------|-------|
| **Editor** (center)    | `editor`           | the buffer load/save seam — **PROVEN**                     | 1 |
| **Project panel**      | `project_panel`    | `read_dir`/`metadata`/`watch` over the cell namespace      | 2 |
| **Outline panel**      | `outline_panel`    | tree-sitter outline of open buffers (no Fs)                | 2 |
| **Integrated terminal**| `terminal_view`/`terminal` | a PTY (native: the deos dock PTY; confined elsewhere) | 3 |
| **Search**             | `search` (in `workspace`) | project-wide `read_dir`+`load` (already provided)   | 2 |
| **Command palette**    | `command_palette`  | action registry only (no Fs)                               | 2 |
| **Git panel / Git UI** | `git_ui`           | `open_repo`/`git_*` — needs git-over-cells (STUBBED now)   | 4 |
| **Agent / assistant**  | `agent`/`agent_ui` | language-model client → route to the confined Hermes/ACP gate | 4 |
| **Title bar / dock**   | `title_bar`/`workspace` | pure chrome (no Fs)                                    | 2 |
| **Collab panel**       | `collab_ui`        | collab client → dregg-Matrix bridge OR disabled            | 5 |
| **Debug panel**        | `dap`/`debugger_ui`| debug adapters (shell-out) — likely disabled in deos       | 5 |

`watch` (live cross-pane refresh) is the one Fs method the project panel + search
want beyond what's built. The design: drive `PathEvent`s off the
`FirmamentFs` **receipt log** — each save-turn emits a `Created/Changed` event
for its cell's path, so an edit in the editor refreshes the project panel. This
is a natural extension of the receipt provenance log already in `FirmamentFs`.

---

## 3. Booting a real Zed `Workspace` inside deos (the scaffolding)

`crates/zed/src/main.rs` runs **97 `::init` calls** before opening a workspace.
The deos embed needs the SUBSET that the chosen panels require — minus the
standalone-binary shell (crash handler, auto-update, CLI/IPC, the OS app menu,
the login/collab flow). The core sequence (from `main.rs`), grouped:

**Always (any Workspace):**
`settings::init(cx)` · `theme_settings::init(LoadThemes, cx)` ·
`release_channel::init(version, cx)` · `client::init` (or a deos-offline stub) ·
`project::Project::init(&client, cx)` · `language` registry +
`languages::init(registry, fs, node_runtime, cx)` · `command_palette::init(cx)` ·
`zed::init(cx)` (action handlers) · then build an `AppState` and call
`zed::initialize_workspace(app_state, cx)`.

**Per panel** (only what we enable): `project_panel`/`outline_panel`/
`terminal_view`/`git_ui`/`agent_ui`/`debugger_ui` each have an `init(cx)` +
a `Panel::load(workspace_handle, cx)` that `initialize_panels` awaits and
`add_panel`s.

The deos-side boot is therefore: **a `deos_workspace::boot(fs: Arc<FirmamentZedFs>,
cx)`** that (a) installs the settings/theme/language globals, (b) builds a
`Project::local` over the `FirmamentZedFs` (the real `node_runtime`/`client`
replaced by deos-offline equivalents), (c) opens a `Workspace` window (gpui view —
the same gpui instance the deos cockpit dock uses, so it drops into the dock like
deos-zed's `CockpitSurface`), (d) registers the enabled panels. This is a
direct adaptation of `initialize_workspace` + the subset of `main.rs`'s init —
**designed; the foundation proves the Project + Fs half of it.**

The `FirmamentZedFs` is the SAME `gpui` instance as the cockpit (it depends on
the zed-fork gpui at our rev, like `starbridge-v2` + `gpui-component`), so the
`Workspace` `Entity`/`Window` types are byte-identical to the cockpit's — it
mounts in the deos dock the same way deos-zed's thin editor does today.

---

## 4. Staging — the honest ladder

1. **Editor over FirmamentZedFs** — *BUILT + PROVEN here.* Real Zed `editor`
   crate compiles; a real Zed `Project`+`Buffer` loads a cell + saves a turn.
2. **Editor + project panel + outline + search + command palette + title bar/dock**
   — the "browse + edit the cell namespace" Workspace. Needs the `boot`
   scaffolding (§3) + `watch`-off-the-receipt-log. No new shell-out deps.
   *Designed; lowest-risk next slice.*
3. **+ integrated terminal** — `terminal_view` over the native deos PTY (the
   cockpit dock already drives one); confined PTY for seL4/browser.
4. **+ git UI + agent panel** — git-over-cells (`open_repo`/`git_*` impl, the
   biggest new Fs work) and the agent panel routed to the confined Hermes/ACP
   tool gate (the deos MEMBRANE). LSP comes online here (a Node binary or a
   confined language-server process in the image).
5. **+ collab / debug** — the dregg-Matrix collab bridge; debug adapters. Most
   likely disabled or deos-substituted rather than ported verbatim.

The through-line: **every file the whole IDE touches is a cell, and every save —
from any panel — is a verified turn leaving a receipt.** The foundation proves
that load-bearing claim today; the ladder is the surface area.
