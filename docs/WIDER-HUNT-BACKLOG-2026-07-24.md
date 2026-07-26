# Wider-Hunt Backlog — 2026-07-24 (4 read-only class-hunts, post twin-deletion campaign)

Four orthogonal adversarial lenses swept while the build lock was jammed. Verdicts: **arithmetic** and
**fail-open** classes are *largely already hardened* (the campaign paying dividends); **DoS** and the
**completeness/DEOS** survey found real new work. Dispatch routing: [RUST]=fix in Rust · [LEAN-AIR]=felt-width
emit path, NOT a Rust patch (tripwire) · [DEPLOY]=config/ops · [AUDIT]=needs a deep pass · [TWIN]=add to CI guard.

## 🔴 DoS / unbounded-resource — the rich hunt (live, ANON-reachable, DEPLOYED)
- **T1 [RUST, FIX FIRST]** dreggnet-telegram game-session host is UNBOUNDED — PlayerWorlds's deployed sibling.
  `dreggnet-telegram/src/runtime.rs:1292,1318 → telegram_default_host → dreggnet-catalog full_catalog_host →
  OfferingHost::new()` with `SessionPolicy::is_unbounded()`; `admit_fresh_open` (host.rs:891) skips every gate.
  ANY Telegram user opening games mints unbounded durable sessions (mem+disk). Fix: arm a bounded SessionPolicy
  (max_sessions + idle_ttl + max_opens_per_actor), mirroring dreggnet-web `resolve_web_policy`/`host.rs:924`.
- **W2 [RUST]** dreggnet-web `GET /session/{id}` (lib.rs:373, mounted :4610) mints a full DungeonSession per
  arbitrary path id, no cap/TTL — the SAME PlayerWorlds gap on the legacy offering-#0 surface (the fix armed
  the catalog host but not this map). Route through the capped OfferingHost or add the LRU+TTL cap.
- **W1 [RUST]** `POST /descent/submit` (descent.rs:771) accretes verified runs keyed by free-text `player`;
  `get_leaderboard` re-executes verify_completion for EVERY run on EVERY render under the global lock. Cap
  runs/day top-K, dedup best-per-player, rate-limit submit.
- **F1 [RUST]** node `get_cell_proof` (api.rs:4730) — anon GET rebuilds the whole ledger leaf-set + root fold +
  serializes every leaf, no cache/limit. Cache by ledger version; paginate; per-IP limit.
- **F4 [RUST]** node relay `delivery_proofs` (relay_service.rs:329,1219) — never-evicted map, +1 permanent entry
  per delivered message (GC skips it). Ring/TTL-evict.
- **S1 [RUST]** sandstorm-serve accept loop (surface.rs:250) — thread-per-connection, `max_connections` IGNORED,
  auth AFTER spawn. Enforce a semaphore at accept + gate before spawn.
- **D1 [RUST]** discord-bot CardApplets (viewnode_applet.rs:411,458) — unbounded per-user-id applet map. LRU+TTL.
- **D2 [RUST]** discord-bot deos_drive (deos_drive.rs:243) — `Vec::with_capacity(len)` from an untrusted decoded
  length. `len.min(bound)` / reject before alloc.
- **INSIDER (federation-wide, membership-gated):** F10 orphan buffer (catchup.rs:125) + network amplification;
  F11 vote map (finalization_votes.rs:401) keyed by attacker-chosen block_id; F5/F8 DKG/wake maps. Cap+prune+roster-check.
- Verified-BOUNDED (do not re-flag): dreggnet-web discord_activity TokenRateLimiter, the catalog/offerings capped
  path (host.rs:924), node /ws frame caps + GOSSIP_SEMAPHORE, SSE bounded broadcast, global 1 MiB body limit.
- Follow-up un-swept network surfaces: dregg-net/sdk-net gossip decode, directory, discharge-gateway,
  deos-homeserver, intent, starbridge-v2, dfa-federation, wire, webauth-core.

## 🟡 Completeness survey — next deep-audit targets (DEOS audit already LAUNCHED)
- **DEOS #1 [AUDIT, running]** applet/agent capability boundary. Confirmed smells: pty_ws local-RCE (below);
  applet turns commit `Unchecked` auth (deos-js-runtime/src/applet.rs:303,316 + deos-js:406,421) → in-band
  is_attenuation the only gate; **ToolGateway is a Rust twin of Lean delegAdmit with NO differential**
  (sdk/src/tool_gateway.rs:207 ↔ ToolAccessDelegation.lean:126) **[TWIN — add to CI guard]**; deos-zed raw std::fs.
- **pty_ws [RUST]** deos-terminal/src/bin/pty_ws.rs — spawns $SHELL per WebSocket with NO auth + NO Origin check
  (loopback default, not deployed, but a malicious web page → ws://localhost:7717 → shell). Add handshake token /
  Origin allowlist.
- Ranked next targets: (1) DEOS, (2) TEE/attestation verify crypto (tee-verify cert-chain/COSE/DCAP untouched —
  a bug = universal attestation forgery), (3) federation quorum/threshold-sig verify + equivocation (revocation
  hole was evidence), (4) pg-dregg SQL RLS/SECURITY DEFINER (workspace-excluded, dodged all gates), (5) cell-crypto
  value/note/nullifier substrate, (6) captp handoff fuzz. Reassuring: macaroon HAS a live Lean differential; the
  AIR-in-Lean law is CI-ratchet-enforced with a real p3 STARK/FRI verify_batch (the "57-bit calculator"
  descriptor_air_accepts is test/doc-only, no deployed caller).

## 🔵 Arithmetic-safety — core is overflow-SAFE; residuals split
- Core SAFE: execute_tree.rs:1031 checked_sub gate; cell/ledger/coord use checked/u128. No unguarded panic-DoS.
- [RUST] fee*3/10 u64 overflow (finalize.rs:762,1182 / execute.rs:29,796 — near-ceiling cell) → u128/checked_mul;
  composer.rs:322 `i64 .sum()` conservation gate wraps in release → checked_add fold; collective-choice/governance
  tally `.sum()` wraps → checked_add (quorum-bypass risk); economics.rs saturating hides supply overflow → checked+error.
- [LEAN-AIR] felt-width truncations at money/counter boundaries (WOUND-felt-width class, NOT Rust patches):
  effect_vm_bridge amount→30-bit felt (:399/499/370/594), fee→u32 (proof_verify.rs:1422), height/nonce→31-bit
  (rotation_witness.rs:121,245; commitment.rs:1191), balance 2×30-bit decode (proof_verify.rs:90). Fix in the emit path.
  NOTE atomic.rs:470 `unverified_rust_conservation_fallback` truncates |delta| as u32 on the no-Lean guest only.

## 🟢 Fail-open / error-swallowing — substantially CLOSED; one MEDIUM
- **[RUST] finality sibling fail-open** (blocklace_sync.rs:1780) — twin-#8 gated the primary tau-ORDER fallback
  (rust_tau_fallback_allowed at :1499) but the secondary consistency belt `VerifiedFinality::compute` at :1780 still
  fails OPEN per-poll on a runtime FFI fault (None → `if let Some(vf) {…}` no else). Extend the same gate to BOTH sites.
- LOW/informational: wire/src/server.rs:3089 delivery_signature discarded (inert, not trusted — remove/pin); CLI
  proof/vote display defaults true (cosmetic — flip to false); DREGG_ALLOW_UNVERIFIED_CONSENSUS escape (deploy hygiene).

## Dispatch plan (fixes need the build lock — jammed; batch when it frees)
FIX-FIRST: T1 (telegram unbounded sessions, ANON+deployed). Then the DoS [RUST] batch (W1/W2/F1/F4/S1/D1/D2),
the arithmetic [RUST] batch (fee*3/composer/tally), the finality sibling, pty_ws. Add ToolGateway to the CI twin
guard. Route the felt-width items to the Lean/felt-width campaign. The insider-tier + un-swept surfaces = a
follow-up round. DEOS + TEE + federation-internals + pg-dregg = the next megaswarms (survey-ranked).
