# Verified finality gate — the per-poll cost structure, what ships, and the remaining seam

**The question this answers.** Under GATE-ON (the verified Lean tau-order finality gate,
`DREGG_FINALITY_GATE` unset ⇒ default ON), why can a turn that is *accepted* (its block is in the
DAG) lag finalization as the DAG grows — with no reject, no Lean/Rust divergence, no fallback — and
what closes it?

**Verdict (one line).** Same class as `docs/N3-ROOTCAUSE.md`: not a rule bug, an order divergence,
or a consensus-liveness defect — the verified-Lean tau-order FFI is **O(history) per call**, the
finality executor is **serial**, and absent cross-poll reuse every poll pays the full recompute; the
shipped completion is the **cross-poll verified-order cache** (finality-keyed) plus the Lean
runtime's **HashMap fast path**, and the remaining seam is a **persistent cross-call cache** (true
O(Δ) per poll under sustained growth).

---

## 1. The per-call cost shape (grounded, file:line @ HEAD)

The finality executor is a single serial task; each iteration runs one full poll, then executes,
then sleeps on the notify:

- `node/src/blocklace_sync.rs:4007` `spawn_finality_executor` — one `tokio::spawn`ed loop: the
  notify fires on EVERY block produced or received, a 150 ms debounce coalesces the storm, then
  `poll_finalized_blocks().await` and the block-execution loop. It is **serial**: the next poll
  cannot start until this poll's FFI + execution finish.

Inside one poll (`poll_finalized_blocks`, `node/src/blocklace_sync.rs:968`), the verified-order
computation — when it runs — is O(history) in the total lace size N:

1. Clone the whole lace under the read lock — O(N).
2. `build_ordering_blocklace` (`:1743`) — sort all blocks + re-insert each — O(N log N); then the
   Rust `tau` over it (HashMap-backed `PastCache`, fast — the differential sibling whose ordered
   output also keys the cache, §2).
3. `spawn_blocking(VerifiedFinality::compute_order(...))` (`:1175`) — the authoritative verified
   order, the dominant cost:
   - `node/src/finality_gate.rs:150` `compute_order` → `build_wire` (`:90`): sort all blocks, build
     the interning tables, format the **entire lace** into one `"w=…;P=…;B=…"` wire string —
     O(N + E) string construction per call.
   - `dregg_lean_ffi::verified_tau_order` (`dregg-lean-ffi/src/distributed_ffi.rs:119`) →
     `ffi_tau::lean_tau_order` (`:294`): copies the whole wire into a `CString`, calls the Lean
     `String → String` export, and on a too-small buffer retries the entire call.
4. The second FFI (`VerifiedFinality::compute`, the `(creator,seq)` projection gate) is SKIPPED
   whenever the order came from Lean (`ordered_from_lean`), so it is not a steady-state cost.

**The Lean side rebuilds its memo on every call — by construction.** The export runs
`BlocklaceFinality.tauOrderFast` (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean:533`),
whose first two lines build `mkPastCache B` / `mkRoundCache B` over the entire lace, use them for
that fold, and discard them. The memo is a local of a pure function; no handle lets a later FFI
call reuse it. Two layers keep the single call fast:

- **The proof-carrying fast twins** — the `…C` cached functions with faithfulness lemmas
  (`cachedPast_eq` `:325`, `tauOrderFast_eq` `:542`), which killed the within-call exponential
  re-traversal. The pure `PastCache` is `List`-backed with linear `find?` (`:309-321`) and
  `computeRounds` is O(n²) over the `List` (`:97`) — but these are the *proof* representations.
- **The `@[implemented_by]` runtime twin** — `tauOrderFastImpl` (`:723`) builds the past + round
  maps as `Std.HashMap`s once (HashSet-BFS + one topological fold) and runs the same fold with O(1)
  lookups; `attribute [implemented_by tauOrderFastImpl] tauOrderFast` (`:736`) routes the exported
  `dregg_tau_order` / `dregg_blocklace_finalize` through it. Runtime-only, introduces no axioms
  (`#assert_axioms tauOrderFast_eq` stays clean); §9 differential `#guard`s witness value-identity
  against the pure `tauOrder` on concrete laces.

So one FFI call is fast in its constants but still **whole-lace**: absent cross-poll reuse, a
growing DAG makes the serial executor's finalization throughput fall below the block-production
rate, and the finalized prefix lags the frontier — exactly the round-2-stall shape diagnosed in
`docs/N3-ROOTCAUSE.md` §3. That is what the cache exists to prevent.

## 2. SHIPPED — the cross-poll verified-order cache (finality-keyed)

`BlocklaceHandle` (`node/src/blocklace_sync.rs:159`) carries the cache:
`last_order_fingerprint: Arc<RwLock<Option<u64>>>` (`:276`) and
`last_lean_order: Arc<RwLock<Option<Vec<BlockId>>>>` (`:280`). In `poll_finalized_blocks`
(`:1111-1230`), before the `spawn_blocking(compute_order)`:

- The fingerprint is computed over the **finalized order itself** — the ordered `rust_order` id
  sequence (`:1131`), which equals the verified `tauOrder` after the topological
  `build_ordering_blocklace` fix. A fingerprint HIT reuses `last_lean_order` and **skips the FFI
  entirely** (`:1141-1160`); a MISS runs the FFI and stores `(fingerprint, order)` (`:1213-1216`).
- **Why finality-keyed, not lace-keyed:** a whole-lace id-set fingerprint is busted by ANY new
  frontier block (an ack/heartbeat/round block not yet super-ratified) — and under continuous
  cross-machine catch-up the lace grows every poll, so a lace-keyed cache misses every poll while
  the finalized order barely moves (`docs/CROSS-MACHINE-FINALITY-FINDING.md` §3). Frontier-only
  growth leaves the finalized order unchanged ⇒ HIT ⇒ FFI skipped; the FFI runs only when finality
  actually ADVANCES or a catch-up block SHIFTS the prefix. Sound: an identical finalized order means
  an identical `tauOrder` (a pure function of the finalized causal DAG); any change recomputes, so
  the cache never serves a stale order for a moved prefix.

With the cache, gate-ON stops burning the window on redundant recomputes of the settled past: the
executor completes the poll that carries a new turn's ratification, and the verified rule stays the
decider on every poll.

## 3. NAMED SEAMS — design, not landed

These remain live design; each is stated with the reason it is its own piece of work.

1. **Incremental `build_wire`** (`node/src/finality_gate.rs:90-148`). A driver-owned `WireBuilder`
   retaining the interning tables and per-block wire fragments across polls would cut the Rust-side
   marshalling from O(N) to O(Δ) per cache-missing poll. Not built (grep `WireBuilder`: none); each
   FFI-running poll re-formats the whole lace.
2. **A persistent cross-call Lean cache — the true O(Δ) completion.** The export is a pure
   `String → String`; the HashMap maps of `tauOrderFastImpl` are rebuilt per call. Two sufficient
   shapes, either a Lean/FFI source change:
   - **(a) A stateful/resumable export** holding the past/round maps in a Lean object handle
     retained Rust-side, extended by only the new blocks per call — needs an extension-faithfulness
     lemma (`mkPastCache (B ++ Δ) = extend (mkPastCache B) Δ`) so `tauOrderFast_eq` (`:542`) still
     transfers.
   - **(b) A verified checkpoint-compaction** so the FFI runs on a bounded suffix. Note
     `Dregg2/Consensus/TauPrefixMonotone.lean` REFUTES unconditional prefix stability (honest
     catch-up can sort a late block mid-prefix), so this needs a bounded-window stability
     certificate, not naive truncation.
   Until one lands, the throughput ceiling under SUSTAINED growth at large N remains: the cache
   bounds the *frequency* of whole-lace recomputes, not their asymptotic.
3. **An in-flight recompute guard.** The debounce coalesces 150 ms of notifications; a stronger
   cadence rule ("no new O(N) recompute until the previous completed AND finality advanced") is
   subsumed in practice by the finality-keyed cache but remains available if a workload defeats it.

### FALLBACK — bounded-timeout (⚑ CORRECTED 2026-08-08: it IS built, and it IS the default)

**This section used to read "NOT built, NOT a default … gated on ember's explicit call". That is
false and has been for some time.** The bound is live in `node/src/blocklace_sync.rs`
(`tokio::time::timeout(verified_order_ffi_timeout(), ffi)`), the budget defaults to **2500 ms**
(`DREGG_FINALITY_ORDER_TIMEOUT_MS`), and it is on by default on every node. A reader who trusted
this page would have concluded the verified rule was unconditionally the decider. It is not.

What a miss actually does — and it is **not** the single "fail-open" this section described:

| node posture | `rust_tau_fallback_allowed` | a missed budget causes |
|---|---|---|
| `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` (e.g. `scripts/federation-local.sh:86`) | true | the **un-verified Rust `ordering::tau` order decides the poll** |
| Lean-linked, escape unset (`scripts/poa-devnet.sh` pins it to `0`) | false | the poll **FAILS CLOSED — finalizes nothing** |

Same trigger, opposite failure mode, opposite remedy. Two further defects the bound introduced,
both fixed 2026-08-08 (`node/src/blocklace_sync.rs`):

1. **The cache did not record provenance.** A fallback poll stored the un-verified Rust order in
   the cross-poll cache indistinguishably from a verified one, and because the cache is keyed on
   the finalized *order* (stable while finality is not advancing) every later poll served it under
   a `debug!("verified-order cache HIT")`. The WARN fired **once**, then silence. `last_lean_order`
   now carries `(order, verified: bool)`.
2. **`ordered_from_lean` was set `true` for the fallback**, disarming the belt-and-suspenders
   finality gate in precisely the case its own comment says it defends ("keep the belt ONLY for
   the Rust fallback"). It now carries the real provenance.

Accounting now exists where there was only a log line:
`dregg_consensus_order_polls_total{source=…}`, `dregg_consensus_order_over_budget_total`, and the
`/status` fields `consensus_order`, `consensus_order_budget_ms`,
`consensus_order_{verified,unverified,failed_closed,over_budget}_polls`.

**Raising the budget is not a fix** — it moves the crossing without changing whether the verified
path runs. The elevate-don't-degrade answer is still the seams in §3, plus the one this campaign
measured and named: the lace is `List Block` with an O(n) `Lace.lookup`
(`metatheory/Dregg2/Authority/Blocklace.lean`) called from the innermost loops of
`tauOrderFastImpl`, which builds `Std.HashMap` past/round maps but **no `BlockId → Block` index**.
That single missing index is the dominating term.
