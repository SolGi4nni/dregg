# starbridge-v2 Improvement Backlog — 2026-07-24 (level-up, pre-Fable)

WHAT IT IS: the native dregg master interface — a standalone gpui workspace, ~158K LOC. Headless gpui-free
heart (~14K load-bearing): world.rs (embedded VERIFIED executor — wraps the real dregg_sdk::embed::DreggEngine,
runs real verified turns via commit_turn, per-agent receipt chains, dual-writes durable redb, emits dynamics),
dynamics.rs (append-only bounded-ring event log w/ absolute cursors), persistence.rs (durable redb weld,
inherits CrashRecovery.lean), replay.rs (verified re-exec tape + O(1) reify_to umem restore), reflect/affordance/
simulate/swarm/session (reflective object model). gpui presentation plane ~61K (feature-gated off the core).
TRUST MODEL: a LOCAL single-user cockpit core, NOT a network service; untrusted surfaces are the optional live-node
SSE/HTTP client, captp MirrorFrame/carry-envelope decoders, share-link URIs, the persisted redb image on reload.

VERDICT: the headless core is high-quality, mature, defensively-built code that EXCEEDS typical pre-Fable output —
fail-closed commit path with a fault-injection-tested durable unwind, cursor-safe bounded-ring dynamics, exemplary
Result/Option wire discipline (ZERO dangerous unwraps), time-travel already fixed its own O(N²) trap
(replay_to→reify_to), 978 unit tests. **BOTH expected headlines DISSOLVED under evidence:**
- The "dangerous subset of 1498 unwraps" — DOES NOT HOLD. Full triage of every untrusted-input surface (SSE decoder,
  MirrorFrame::decode, open_umem_envelope, decode_fragment, parse_uri, persist reload) found ZERO dangerous sites.
  client.rs has no unwrap/expect/panic (pure `?`); the hand-rolled SseParser is CRLF-safe (drain guarantees len≥1);
  every persistence.rs unwrap is #[cfg(test)]. The 1498 is dominated by .lock().unwrap(), encode .expect("serializable"),
  fixed-[u8;32] slicing, tests. Robustness is NOT the top theme — the opposite of the expectation.
- The "CLASS-3 E0061 6-vs-5 in starbridge-v2 lib" — NOT starbridge-v2's. It's clean+arity-clean at HEAD. The genuine
  build-path blocker is dregg-lean-ffi/build.rs (parallel-lane mid-migration: build_dregg2_archive grew to 7 params,
  a 7-vs-6 arity caught mid-save; already consistent at current disk). ACTION: confirm a clean cargo check on persvati
  once the dregg-lean-ffi migration lands — the break is theirs.

## THE REAL BACKLOG (all sdk-dependent — verify on persvati)
**HIGH**
1. [correctness, M] dynamics write-set completeness (HALF-APPLIED FIX) — world.rs:1312-1324 + :1203-1208. The
   BalanceFlowed/pre-balance loops iterate the SYNTACTIC `touched` over-approx, while the SOUND executor write-set
   (last_write_set()) is computed but used ONLY inside the `if will_dual_write` durable block. A runtime-resolved
   cell (a burn's issuer well absorbing −supply, a metered fee sink) mutates with NO WorldEvent naming it → a memoized
   inspector projection stays stale, violating the documented M2 "cache-soundness = dynamics-completeness" invariant
   (dynamics.rs:82-88). FIX: after execution, emit a conservative CellMutated for any last_write_set() cell not already
   named (works for ephemeral worlds too). **The single most-important correctness fix.**
2. [quality/decision, M] the symbolic-witness / collapse feature (~150 LOC load-bearing state + the collapse protocol
   + a bug cluster #3/#5/#6) has ZERO callers outside world.rs self-tests. DECIDE: wire it (after fixing) or explicitly
   SHELVE+gate it (#[doc(hidden)] / a `symbolic` feature) so it stops carrying latent bugs as live API. **The biggest
   level-up lever** — every genuine latent bug concentrates here.
3. [correctness, M] collapse() receipt-index bug — world.rs:1434-1459. Assumes the N buffered symbolic turns are the
   LAST N receipts (first = receipts.len()-n), but the supported `symbolic → set Full → Full commit → collapse` lands
   Full receipts at the tail, so collapse overwrites THOSE + mis-orders the tape. Latent (safe only because symbolic
   has no caller — #2). Buffer (receipt_index, turn) pairs.
4. [perf/frame, M] old ReplayPanelModel::build — replay.rs:886-946 → cockpit/panels_workspace.rs:2766,
   dock/card_surface.rs:749 — reconstructs via replay_to+diff = 3× genesis re-exec (per-turn crypto) PER FRAME while
   the Replay tab/card is visible. time_travel.rs:176 already routes the live scrub through O(1) reify_to. Consolidate
   the old panel onto reify_to. The one genuine per-frame perf win.
**MEDIUM**
5. [atomicity, M] collapse() mem::take before the loop — world.rs:1430; a mid-loop None/failed-convergence returns Err
   with buffer drained + receipts half-overwritten + witness_mode still Symbolic (torn state, no rollback). Stage
   re-derived receipts in a temp vec; commit after convergence passes.
6. [durability drift, M] commit_turn doc claims a symbolic turn "becomes durable only after collapse", but collapse
   never touches persist/dual_write and commit_turn only dual-writes when !is_symbolic() → buffered turns silently
   lost on reopen (world.rs:1186 vs :1429). Make collapse dual-write on a durable image, or refuse Symbolic on durable.
7. [perf, M] fork() clones the full ledger TWICE (world.rs:704+746) + simulate() forks per what-if (predict UX) —
   on a large live world every hover pays a double whole-ledger clone. Defer the record_ledger clone until commit.
8. [robustness, S] replay.rs:228 root_at(step) "Panics out of range" — every live caller already clamps, but make it
   return Option<[u8;32]> to remove the footgun.
**LOW (quality)**: nonce helper dedup (5×, add pub fn ledger_nonce); doc-label drift (world.rs:170 memo tuple,
reflect.rs:153 "16 slots"); undocumented accessors (world.rs:525-618). HOUSEKEEPING: the memory note
"persistence.rs has a stale #[ignore]" is ITSELF STALE — that test was fixed-forward into
a_mid_session_set_cell_program_on_a_touched_cell_is_refused + a reopen root-fix test; the only real #[ignore] is a
legit minutes-long microbench (world.rs:3671).

## TEST NOTE: headless core is STRONGLY covered (978 unit + 19 integration; suspend/resume, fork isolation,
symbolic→collapse round-trip, fault-injected durable unwind, dynamics eviction). Gaps are precisely the ADVERSARIAL
collapse paths (#3/#5/#6 — an adversarial symbolic→Full→collapse test would CATCH #3) + live-dynamics completeness (#1).

## Dispatch: #1 (dynamics completeness) + #2 (symbolic/collapse DECISION) are the two highest-value. If shelving
symbolic (#2), #3/#5/#6 become moot (gate the feature) — cheapest path. #4 is the clean perf win.
