# DEOS Improvement Backlog — 2026-07-24 (level-up from opus-4.6-era)

VERDICT: DEOS is genuinely good code held to a real bar — the load-bearing designs (ViewNode IR + mount
fail-safes, hermes fail-closed tool routing, matrix forward-compat parsing, deos-zed receipt/patch weld) are
disciplined; the scary raw unwrap counts largely dissolve into #[cfg(test)] + infallible calls. The level-up is
a consistent set of EDGE failures across three themes:
- **T1 — panic-on-adversarial-input** (a recurring class): byte-slice-after-BYTE-length-check on author/guest
  strings (a 64-byte multibyte string slices mid-codepoint → panic; in mozjs unwinds through extern "C" = abort/UB);
  unbounded/overflowing allocation from untrusted committed content. A shared char-safe hex/id codec + a capped
  read_blob helper retire BOTH sub-classes across deos-view, both JS engines, deos-zed, servo at once.
- **T2 — hand-synced twins drift**: the two JS engines (deos-js SM vs deos-js-runtime boa) diverge on fire
  contract/value-width/error-surfacing/isolation, and ApplyOp already drifted (4 vs 5 variants); 2×
  messages_to_anthropic, 2× web walkers, triplicated slot/gate model, hex8 copy-pasted ~6×. Each is a standing
  drift source. Extract shared substance crates.
- **T3 — dead/superseded code with a LYING doc**: deos-leptos gate.rs ("THE load-bearing module" — dead, live
  path uses ReactiveAffordance); deos-view Tabs comment (a JS visibility layer that doesn't exist); matrix
  person_trust/fetch_media (zero call sites). In a checkable-claims codebase, a green test on dead code misleads.

## TOP 10 (value × reach × ROI)
1. [T1, S, HIGH] byte-slice-after-byte-len-check panic — deos-view render.rs:1118, deos-js js.rs:2361/2365 +
   reflect_binding.rs:30, deos-js-runtime world.rs:490. Shared char-safe hex/id codec.
2. [T1, S, HIGH] unchecked size/len alloc → OOM/OOB — deos-view mount.rs:63,68; deos-zed firmament.rs:148
   (Vec::with_capacity(untrusted len)); servo swgl_context.rs:218/310 (width*height*4 in u32 overflows). Drop
   pre-alloc / clamp / checked_mul+usize.
3. [correctness, M, HIGH] web Tabs node non-functional — deos-view web.rs:220,1285,1876 (buttons class
   deos-tab but handler matches deos-button → clicks fire no turn; CSS hardcodes panel 0). Add tab handler +
   drive visibility from the live slot.
4. [robustness, S, HIGH] no iteration cap on the live HttpLlm agent loop — deos-hermes agent_peer/acp_client +
   brain.rs:499; a looping model drives unbounded PAID provider round-trips (LocalBrain self-terminates, HttpLlm
   doesn't). max_steps guard forcing Finish after N tool-calls/turn.
5. [T2, L, HIGH] the two JS engines diverge (fire -1/fatal vs throw; i32+-1-sentinel vs i64; swallow vs surface;
   ApplyOp 4-vs-5). Pick one fire contract; extract a shared substance crate; DECIDE boa's fate (no crate
   consumes deos-js-runtime though it's the only wasm/native engine).
6. [correctness, S, HIGH] deos-zed save-patch accrued BEFORE save, never rolled back on failure — editor.rs:393
   (Err arm :446); a refused cap-save advances patch_count with no receipt → Structure/Ledger faces drift
   (violates the crate's marquee receipts↔patches thesis). Call doc.edit_rope only in the Ok arm.
7. [T3, M, HIGH] deos-leptos gate.rs — superseded verdict API shipped as "THE load-bearing module", zero uses,
   passing tests give false confidence. Delete the dead half; fix the doc.
8. [correctness, M-L, MED-HIGH] deos-matrix live-backend cluster — MatrixHandle never overrides identity() →
   trust badge renders "?" for every sender; ↑-to-edit re-SENDS (never reads self.editing); no refresh timer +
   blocking_recv on the paint thread. Wire identity()→person_trust; add edit/redact; off-thread sync timer.
9. [provenance, S, MED] run_js accountability receipt rides Some(vec![]) — deos-hermes run_js.rs:226,299,451,623;
   witnesses THAT a run_js happened, not WHICH script. Witness EmitEvent{topic:"tool.run_js", data:[digest(script)]}.
10. [test-gap, M, MED-HIGH] highest-power paths untested — deos-js deos.server.*/deos.compose have ZERO JS-surface
    tests + the whole deos-js suite is OUTSIDE the default CI gate; the JS-throw→js_error contract untested; the 5
    live-doc renderers + 2 web-walker parity uncovered. (F1 fix just added the server.* red-team tests — extend.)

## Rest (worth doing, below top-10)
Robustness: Button gpui-id label-only collision (render.rs:489); SNAPSHOTS thread-local never cleared (js.rs:205);
boa native_fire .expect where SM returns error (runtime.rs:79,166) + one Context reused across runs (global leak,
runtime.rs:113); PdAcpTransport panic on fd-clone (confined.rs:621); deos-terminal "F5" uppercase typo drops the
key (keymap.rs:195, quick win) + resize desync + pty_ws truncation on child exit; deos-reflect reachable_from
self-cap contract violation (graph.rs:152); servo per-process Servo footgun (webview.rs:452) + netcap unbounded
read_to_end/chunked-gap/status unwrap_or(200) (netcap_http.rs:358,447).
Perf: deos-reflect graph_face O(N²) per cell (present.rs:166); deos-zed metadata full-file decode for a length
(firmament.rs:872) + rail refresh clones whole receipt log per notify (cockpit_surface.rs:124); deos-js recompiles
the 290-line PRELUDE every eval (js.rs:729); hermes rebuilds tool_specs every step (brain.rs:481).
Dup: open_permissions ×3, pack_u64 ×2, chunked heap-blob codec verbatim ×2, turn-build boilerplate ×4.

## FINE AS-IS (don't spend effort): matrix untrusted-event parse (fail-closed + forward-compat); deos-terminal
PTY/WS byte path (bounds-guarded, vte panic-free); deos-view mount cycle/depth/budget fail-safes + backend::walk;
hermes tee_fact (fail-closed TEE verifier); most raw unwrap/expect counts (test-only/infallible).

## Dispatch: T1 (items 1+2, shared codec — kills 8 panic sites) and #4 (agent-loop cap — live paid DoS) first;
then #6 (deos-zed rollback), #3 (web Tabs), #7/#9 (dead-code+provenance); the JS-engine unification (#5) is the
big L structural one. All sdk-dependent — verify on persvati.
