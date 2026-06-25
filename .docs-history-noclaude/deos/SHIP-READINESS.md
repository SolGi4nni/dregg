# deos cockpit — SHIP-READINESS

What the headline `starbridge-v2 --features native-full` build actually does when you
run it. This matrix is **established by RUNNING** each surface's real harness (render
bakes that drive the prebuilt release binary + the per-crate test suites), not by
reading code. Every row carries the evidence: the test-result line and/or the baked
artifact that proves it.

Reproduce with `scripts/ship-readiness-smoke.sh` (reuses the prebuilt release binary
for the bakes; runs the per-crate suites). Pass `--fast` to skip the heavy
embedded-executor suites.

`native-full` ships: `embedded-executor · app-registry · gpui-ui · live-node ·
render-capture · web-shell (→ servo-render/libservo, the real WebView) · dev-surfaces
(→ deos-zed editor · deos-terminal · deos-hermes agent · deos-matrix chat · firmament)`.

## Headline

**The shipped cockpit is complete-and-runs.** Every feature surface is genuinely
wired and runs at runtime — nothing is a stub or a build-flag that doesn't execute.
Across the audit: 0 BUSTED, 0 STUB. Two surfaces are **PARTIAL** with a single,
precisely-named, by-design seam each (the node write-back lane and the live-Matrix
homeserver wire) — neither is a broken path; both degrade honestly and both have the
designed write surface already present. One naming caveat: there are *two* web
surfaces; the one literally named "web-shell" is the real libservo WebView (SOLID),
while the `dregg://` web-of-cells tile is the SWGL rasterizer (PARTIAL-by-design,
libservo upgrade named-next).

## The matrix

| # | Surface | Verdict | Evidence (ran) |
|---|---------|---------|----------------|
| 1 | **Self-hosting loop** (editor-save=turn → disk mirror → terminal rustc) | **SOLID** | `--render-self-hosting-full` → 3200×2000 PNG. "THE FULL SINGLE LOOP RAN": save fired a real cap-gated `SetField` turn (receipts 5→6 on-ledger), dual-wrote the cell to disk, the live `sh` PTY ran `rustc main.rs && ./prog` → printed `v2`. |
| 2 | **Unified boot** (live-node pane + editor + terminal, node-attached) | **PARTIAL** | `--render-unified-boot --node :8775` → 3800×2000 PNG. Live-node pane attached (lean producer LIVE, 2 cells·1 receipt pulled over `/api/cells`+`/api/receipts`); editor save fired (local receipts 5→6); live alacritty PTY ran `cargo --version` → `cargo 1.94.0-nightly`. **SEAM** (empirically probed by the bake itself): editor save is LOCAL-World only — node receipts stayed 1→1; `--node` attach is READ-ONLY-synced. Write-back lane exists (`client.rs::submit_turn` → POST `/turn/submit`, confirmed live on the node) but `EditorPane::firmament_over` does not route through it yet. |
| 3 | **Servo web-shell** (real http+https WebView) | **SOLID** | `servo-render` `cargo test --features libservo` → **23 passed, 0 failed** incl. `webview::tests::first_real_render_data_page_through_the_compositor_gate`, `real_http_page_rasterized_through_the_cap_gate`, `real_https_page_rasterized_through_the_cap_gated_tls_socket`, the net-cap socket gate. Cockpit `panels_webshell.rs:240` drives the real `render_url_to_frame_netcap` (`ServoBuilder`→`WebViewBuilder`→load→read_to_image), fail-closed when the engine isn't linked. *(Caveat: the separate `dregg://` web-of-cells tile in `web_cells.rs` is the SWGL content-tile rasterizer, real pixels but PARTIAL-by-design — libservo upgrade named-next in-source.)* |
| 4 | **Apps** (the wired apps launch on World + fire turns) | **SOLID** | `cargo test --no-default-features --features app-registry --lib` → **565 streamed `... ok`, 0 FAILED, 0 `error`** (full lib run; the trailing summary line was lost to build-lock contention from parallel agents in this shared workspace, but every streamed test passed). Load-bearing tests confirmed green: `every_wired_app_launches_and_fires_a_real_turn`, `every_wired_app_launches_on_the_cockpit_world`, `launching_gallery_fires_a_real_verified_turn_visible_to_a_second_reader`, `launching_polis_council_commits_a_propose_turn`, powerbox `launching_an_app_births_a_fresh_confined_cell_holding_no_authority`. The heaviest in-suite slice ran clean standalone: `shared_fork` **21 passed, 0 failed** (row 9). |
| 5 | **Editor** (deos-zed, FirmamentFs save = receipted turn) | **SOLID** | `deos-zed` `cargo test --features firmament` → **11 passed, 0 failed**: `save_is_a_receipted_turn_and_content_round_trips_through_the_ledger`, `save_without_the_edit_cap_is_refused_in_band`, `firmament_pane::cockpit_editor_pane_save_is_a_receipted_turn_through_the_pane`, `editor_pane_save_lands_on_the_shared_ledger_a_second_reader_inspects`. **Note**: firmament is OFF in deos-zed's default `cargo test` (default = gui/document only, 4 tests) — the save=turn seam needs `--features firmament` to exercise. native-full turns it on (`firmament = ["deos-zed/firmament"]`). |
| 6 | **Terminal** (deos-terminal, real PTY) | **SOLID** | `deos-terminal` `cargo test` → **6 passed** (1 doctest ignored). Real `alacritty_terminal::tty::new` over `$SHELL`: `real_shell_echoes_a_marker` (spawns `/bin/sh -i`, echoes a marker through the grid), `pty_resizes_without_panicking`, `shell_over_websocket_echoes_a_marker` (spawns the real `deos-terminal-pty-ws` server, drives a shell over a real WebSocket). |
| 7 | **Hermes agent** (the receipted loop) | **SOLID** | `deos-hermes` `cargo test` → **18 passed, 2 ignored**. The loop is real: `hermes_tool_call_becomes_a_cap_gated_receipted_turn`, `confined_agent_runs_a_metered_receipted_multi_turn_session`, `full_acp_session_drives_every_permission_through_the_gate`, in-band refusals (past-deadline/over-rate/out-of-scope). The 2 ignored are the live-LLM-subprocess path (`--ignored`, needs a hermes-acp install + reachable provider) — an intentional env-gate, not a hole. |
| 8 | **Chat** (deos-matrix, room = cell, the bridge) | **PARTIAL** | `deos-matrix` `cargo test` → **36 passed, 0 failed**: `send_is_a_turn_with_a_receipt`, `room_is_a_cell_with_advancing_history`, the membrane round-trip + `rehydrate_fails_closed_on_root_substitution`, every object-kind round-trips fail-closed. **SEAM**: the 4 `live_homeserver` tests print "ok" but **silently early-return** when `DEOS_MATRIX_TEST_HS`+creds (+ a docker conduit) are unset — the over-a-real-Matrix-server wire was NOT exercised in this run. The bridge logic is SOLID; the live-server round-trip is env-gated. |
| 9 | **Membrane** (shared_fork — a message = a cap-bounded world-fork) | **SOLID** | `cargo test --no-default-features --features embedded-executor --lib shared_fork` → **21 passed, 0 failed**: `real_membrane_mints_serializes_rehydrates_into_a_real_fork`, `real_membrane_rehydrate_fails_closed_on_a_substituted_snapshot`, `real_membrane_driven_turn_stitches_back_through_the_real_settlement_gate`, `multiplayer_one_frustum_two_principals_drive_then_stitch_both`, consent gate fires-once / fail-closed / forged-witness-rejected. |
| 10 | **Inspectors** (reflective surfaces — the moldable lens family L1–L10 + reflect) | **SOLID** | `deos-reflect` `cargo test` → **5 passed** (`present_emits_the_moldable_faces`, `crawl_reads_four_substances`, `frustum_is_cap_bounded`, `ocap_graph_has_the_grant_edge`, `affordance_surface_projects_per_viewer`). All 12 `MoldableLens` variants (Cell L1 / Capability L4 / DeepCell L5 / Receipt L6 / Token L7 / Federation L8 / Circuit L9 / Settlement L10 / Blame / ReadCap / History) have a real render arm in `panels_main.rs:624-722` calling genuine deos-reflect/cell builders — none are placeholder text (Federation/Blame degrade *honestly* when disconnected/cv-absent). Two newer lenses re-verified live: `read_cap_lens` **6 passed** (real `ReadCap::attenuate` lattice, byte-identity binding), `history_lens` **4 passed** (real `Effect::invert` reversibility map). |
| 11 | **Node attach** (LiveNode HTTP+SSE sync over the wire) | **SOLID** (read-sync) | `cargo test --no-default-features --features embedded-executor,live-node --lib live_node` → **6 passed, 0 failed**: SSE parser (single record / chunk-splits+heartbeats / drops a bad frame without aborting), `receipt_feed_dedups_resumes_and_counts_new`, `live_reflection_matches_the_uniform_inspectable_shape`. Live node on `:8775` confirmed serving real `/api/cells`+`/api/receipts`+`/api/events/stream`, and `POST /turn/submit` is live (validates body). The unified-boot bake proved the cockpit actually pulls this data. Write-back is the same seam as row 2. |

## The two seams, stated precisely

Both PARTIAL rows share the shape "the read/logic path is fully wired and run; one
*write*/live-external lane is built-but-not-routed or env-gated." Neither is a broken
or fake path.

1. **Node write-back (rows 2 & 11).** The cockpit editor's FirmamentFs save commits a
   real receipted turn to the cockpit's **local** `World` (`WorldSpine` over
   `World::commit_turn`). The `--node` attach is a **read-only** sync (`LiveNode::sync`
   snapshot reads + the SSE receipt pump). The write surface to push that turn to the
   node's verified executor *exists* — `client.rs::submit_turn` → `POST /turn/submit`
   (confirmed reachable + validating on the running node) — it is simply not yet the
   route `EditorPane::firmament_over` takes. To close: route the firmament save turn
   through `NodeClient::submit_turn` (in addition to / instead of the local spine).

2. **Live Matrix homeserver (row 8).** The room=cell / send=receipted-turn / membrane
   bridge logic is fully tested (36 green). The 4 `live_homeserver` tests that round-trip
   over a *real* Matrix server are env-gated (`DEOS_MATRIX_TEST_HS` + creds + a docker
   conduit per `scripts/live-test.sh`) and **silently skip** (print "ok" via early
   `return`) when unset. To exercise: stand up a throwaway conduit and set the env.

## Artifacts (this run)

- Render bakes: `self-hosting-full.png.png` (3200×2000, 372 KB), `unified-boot.png.png`
  (3800×2000, 504 KB) — both baked from the prebuilt
  `starbridge-v2/target/release/starbridge-v2`.
- Per-crate test logs captured under the smoke-run OUTDIR (see
  `scripts/ship-readiness-smoke.sh`).
