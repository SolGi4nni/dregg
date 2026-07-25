# node/ (dregg-node) Examine + Improvement Audit — 2026-07-25

WHAT: dregg-node (~80K LOC, 64 modules) = the federation daemon — blocklace consensus loop (finality/tau +
catchup), localhost+gateway HTTP API, SSE receipt stream, gossip sync, + cell-program services (relay, channels,
storage, realm, trustline, DKG, equivocation court). Consensus finalizes over the VERIFIED Lean dregg_tau_order
(Rust ordering::tau is a differential sibling only), gated by a startup hard-check (lib.rs:1704) that REFUSES
full-mode start unless the verified archive is linked.

VERDICT: **high, self-aware quality.** Consensus core genuinely Lean-shadowed with real fail-closed gates
(startup hard-check, twin-#8, enrollment pin receive_block_pinned drops unenrolled blocks BEFORE the expensive
hybrid verify — no anon verify-amplification), equivocation FULLY adjudicated (detect→retain evidence→evict→
penalize→slash), vote de-dup first-write-wins. **Network-input crash-robustness is SOLVED** — a targeted grep
for request-data indexing/unwrap panics across all handlers returned NOTHING (decoders uniformly hex_decode().
map_err + guarded slices + serde-via-axum). The real work is RESOURCE-EXHAUSTION, in two tiers.

## CORRECTION to the wider-hunt backlog
The blocklace_sync.rs:1780 fail-open belt (flagged MEDIUM there) is DOWNSTREAM-PROTECTED: it only runs under
`!ordered_from_lean`; on a verified-role node the order is either Lean-authoritative (belt skipped) or empty
(primary twin-#8 fail-closed) — so it NEVER admits an unverified block. LOW-priority tidiness (extend the gate
to :1780 for symmetry), NOT a safety hole. The real finality-region risk is the LIVENESS stall (#6 below).

## THEME 1 — ANON DoS (highest-value, cheapest to exploit): rate-limiting is applied INCONSISTENTLY (devs armed
per-IP RateLimiters on /api/discharge + faithful-mirror but left equally-expensive reads anon+unthrottled, several
UNDER the global state.read() lock so a flood also starves writers).
- #1 [M] api.rs:4730 get_cell_proof — materializes+folds+serializes the ENTIRE leaf set per anon GET, holding
  state.read() throughout. Cache by ledger version + paginate + per-IP RateLimiter (mirror the discharge one).
- #2 [S] api.rs:1904 get_all_cells + get_blocklace_blocks — full-ledger/full-lace scan+serialize, anon, no limit.
- #3 [S/M] events.rs:141 events_stream — no cap on concurrent SSE conns; each re-acquires state.read() every drain.
  Global semaphore on live SSE + per-IP cap.
- #10 [S] relay_service.rs:1219 delivery_proofs.insert never evicted (GC skips it) — ring/TTL evict (economic-gated).
- #11 [S] channels_service.rs ~1315 post_subscribe registers a CALLER-SUPPLIED waiter with no roster check, unbounded
  — roster-gate + cap the wait table.

## THEME 2 — INSIDER (Byzantine-committee) resource bounds: every consensus-state map a committee member feeds is
UNBOUNDED → a single Byzantine member can OOM the federation.
- #4 [M] catchup.rs:125 OrphanBuffer::buffer — NO cap (confirmed no MAX_ORPHAN); signed blocks citing fake
  predecessors buffer forever + each spawns a Pull broadcast (network amplification). Cap + drop-oldest/TTL + bound pull fan-out.
- #5 [M] finalization_votes.rs:202,401,426 — the votes map AND the attested set have ZERO prune/retain, keyed by
  attacker-chosen block_id; an enrolled member votes for unlimited fabricated block_ids (each a valid hybrid sig).
  Prune below the finalized frontier + cap per member.
- #9 [S] dkg_service.rs:861 room.sealed.extend — uncapped sealed-share accumulation per ceremony. Cap per ceremony/dealer.

## THEME 3 — durability + liveness (softest GUARANTEES, harder fixes)
- #6 [L] blocklace_sync.rs:1576 — twin-#8 primary fails CLOSED on the O(history) tau-order FFI hitting the 2500ms
  budget; a Byzantine member producing a pathologically cross-linked lace pushes every poll over budget → finality
  CANNOT advance (liveness stall, sustainable). Incremental/bounded verified order; adaptive budget; DAG complexity cap.
- #7 [L] submit_queue_drainer.rs:632 (the #[ignore]'d falsifier is REAL) — the PG receipt sink + the in-memory ledger
  mutation are NOT one durable txn; a crash restores a receipt whose ledger mutation was never committed (receipt head
  outruns recovered nonce). Feature-gated pg-mirror-live. Route PG submissions through consensus finalization / a welded commit.
- #8 [M/L] blocklace_sync.rs:6795 execute_finalized_turn — deep-clones the ENTIRE ledger TWICE per finalized turn
  (O(N·T) though a turn touches a handful of cells). Working-set snapshot / copy-on-write ledger.

## FINE AS-IS (do not spend): HTTP/gossip decode robustness (zero network decode panics); the auth-header slice
(Bearer-guarded); SetField.value ([u8;32], [..4] safe); equivocation adjudication (complete); vote de-dup.

## Dispatch: THEME 1 (anon-DoS: #1-3,#10,#11) = ONE "cap+cache+paginate+rate-limit the expensive public reads"
pass, highest-value + cheapest exploit. THEME 2 (insider bounds: #4,#5,#9) = cap+prune the consensus maps. Both
additive, persvati-verifiable with flood falsifiers. THEME 3 (#6-8) = the harder guarantee follow-ups.
