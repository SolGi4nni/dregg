# Verified finality gate — the residual-slowness completion (gate-ON round-2 stall)

**Question.** Under GATE-ON (the verified Lean tau-order finality gate, `DREGG_FINALITY_GATE`
unset ⇒ default ON), a fresh client's caller-signed attested Transfer submitted at ROUND 2
is *accepted* (its block is in the DAG) but never enters tau's finalized prefix within the
window, on a LOCAL VERIFIED n=4 — while the same node under GATE-OFF (Rust `tau`) finalizes it
in ~25s, and round-1's faucet turn finalizes even gate-ON. Node stderr shows NO reject, NO
differential divergence, NO fallback. Why does round-1 finalize gate-ON but round-2 does not,
and what is the perf completion?

**Verdict (one line).** Same class as `docs/N3-ROOTCAUSE.md`: it is **not** a rule bug, an
order divergence, or a consensus-liveness defect — it is the **per-poll O(history) cost of the
verified-Lean tau-order FFI**, which is recomputed **entirely from scratch on every finality
poll** (nothing is cached across polls; the Lean `tauOrderFast` memo is rebuilt inside each FFI
call and thrown away). fix-1 (routing `compute_order` through the memoized `tauOrderFast`) removed
the *within-a-single-call* exponential blow-up — enough for round-1's small DAG — but did **not**
make the gate *incremental across polls*. By round-2 the DAG has grown (continuous
heartbeat/round production over the window), each poll pays the full recompute, and the serial
finality executor's finalization throughput falls below the block-production rate — so the
finalized prefix never reaches the frontier block where the round-2 client turn sits, inside the
window. Round-1 finalized because it happened while the DAG was small and one FFI call was fast.

---

## 1. Where the O(history)-per-poll is (grounded, file:line)

The finality executor is a single serial task; each iteration runs one full poll then executes,
then sleeps on the notify:

- `node/src/blocklace_sync.rs:3660` `spawn_finality_executor` — one `tokio::spawn`ed loop.
  `:3664` `finality_notify.notified().await` (fires on EVERY block produced or received),
  `:3676` a 150 ms debounce, `:3679` `poll_finalized_blocks().await`, then the block-execution
  loop `:3711-3727`. It is **serial**: the next poll cannot start until this poll's FFI +
  execution finish, so end-to-end finalization latency for a given block ≈ the FFI cost on the
  current-size DAG.

Inside one poll (`poll_finalized_blocks`, `node/src/blocklace_sync.rs:935`), the per-poll cost is
**O(N)+ in the total lace size N, recomputed from scratch every time**:

1. `:947-950` clone the whole lace under the read lock — O(N).
2. `:1024` `build_ordering_blocklace(&lace)` (`:1523`) — sort all blocks + re-`insert_unverified`
   each (recomputes every block id) — O(N log N); `:1025` Rust `tau` over it (HashMap-backed
   `PastCache`, fast, the differential sibling).
3. `:1038-1047` `spawn_blocking(VerifiedFinality::compute_order(&lace, &participants))` — the
   authoritative verified order. This is the dominant cost. It:
   - `node/src/finality_gate.rs:148` `compute_order` → `:149-151` `build_wire(lace, participants)`
     (`:88-140`): sort all blocks + build the interning tables + format the **entire lace** into
     one `"w=…;P=…;B=…"` wire string — O(N + E) string construction, every poll.
   - `:155` `dregg_lean_ffi::verified_tau_order(&wire)`
     (`dregg-lean-ffi/src/distributed_ffi.rs:119`) → `shadow_tau_order` → `ffi_tau::lean_tau_order`
     (`:194-211`): `CString::new(wire)` copies the **whole wire** (`:195`), calls the Lean
     `String → String` export `dregg_tau_order_str` (`:200`), and on a too-small buffer **retries
     the entire call** with a larger buffer (`:208-209`).
4. `:1149-1174` a SECOND FFI (`VerifiedFinality::compute`, the `(creator,seq)` projection gate) —
   already correctly SKIPPED when the order came from Lean (`ordered_from_lean`, `:1150`,
   `:1143-1148`), so it is not the round-2 cost.

**The Lean side rebuilds its whole-lace memo on every call.** The export runs
`BlocklaceFinality.tauOrderFast` (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean:531-535`),
whose FIRST two lines are `let cache := mkPastCache B` / `let rc := mkRoundCache B` (`:532-533`):
both whole-lace-derived maps are built **once per call over the entire lace `B`**, used for that
fold, then discarded. The memo lives inside the pure function; there is no handle by which a later
FFI call could reuse it. And the Lean lace is `List`-backed with a **linear** `find?`
(`PastCache = List (BlockId × List BlockId)`, `cachedPast` scans it, `:307-321`), and
`computeRounds`/the round map is O(n²) over the `List` (`:343-352`). So one FFI call is roughly
O(n²) in the lace size — polynomial, not exponential (fix-1 removed the exponential re-traversal),
but **still recomputed in full every poll**.

**No cache exists across polls.** `BlocklaceHandle` (`node/src/blocklace_sync.rs:159`) has no
last-order / fingerprint / cache field (grep: none). Every poll starts from zero.

## 2. Why round-1 finalizes gate-ON but round-2 does not

Nothing about the rule differs; the DAG size at the moment of the poll does.

- **Round-1 (faucet turn):** finalizes while the DAG is small — one `compute_order` FFI is fast
  (sub-second), a poll completes well inside the window, the turn enters the finalized prefix.
- **Round-2 (client turn):** by the time enough round-3 blocks exist to super-ratify the wave that
  finalizes the client's turn, the DAG has grown (heartbeats + round blocks accrue continuously
  over the ~25-30 s window). Each poll now pays the full O(n²)-ish recompute (build_wire + CString
  copy + Lean parse + `mkPastCache`/`mkRoundCache` rebuild + fold). Because the executor is serial
  (`:3660` loop) and a notification fires on every block, the executor is almost always mid-FFI on
  an ever-larger lace, and its **finalization throughput falls below the block-production rate**.
  The finalized prefix therefore lags the frontier and never reaches the round-2 client block
  inside the window. This is exactly the N3 finding's "the poll on the grown lace never completes
  in time" (`docs/N3-ROOTCAUSE.md` §3), one node count up.

This matches every observed signal: **no reject** (the block is legal and finalizable), **no
divergence** (Lean and Rust agree whenever a poll finishes — `:1078`/`:1096`), **no fallback**
(the FFI returns fine, just too rarely/slowly to land the round-2 block in the window).

## 3. The perf completion (PREFER fast-verified over fail-open)

### PRIMARY — Rust-only, ship first (reduces frequency + constant; likely closes the bounded payoff window)

Add a cross-poll verified-order cache in the finality driver so the O(N) FFI is not re-run
redundantly, and coalesce recomputes so the serial executor is not perpetually mid-FFI. Exact
sites:

1. **Cross-poll result cache keyed on a lace fingerprint** — new fields on `BlocklaceHandle`
   (`node/src/blocklace_sync.rs:159`): `last_order_fingerprint: Arc<RwLock<Option<u64>>>` and
   `last_lean_order: Arc<RwLock<Option<Vec<BlockId>>>>`. In `poll_finalized_blocks`, before the
   `spawn_blocking(compute_order)` at `:1038-1047`, compute a cheap fingerprint of the finalizable
   input (e.g. `(block_count, max_seq, xor/hash of frontier BlockIds)`). If it equals the last
   fingerprint, **reuse `last_lean_order` and skip both FFIs entirely**; else run the FFI and store
   `(fingerprint, order)`. This removes the redundant recompute on every notification that did not
   change the DAG's finalizable frontier (the debounced notification storm), freeing the executor
   to complete the poll that DOES include the round-2 ratification.

2. **Incremental `build_wire`** — `node/src/finality_gate.rs:88-140`. Retain the interning tables
   (`creator_ids`, `id_ids`) and the per-block wire fragments across polls in a driver-owned
   `WireBuilder`, appending only fragments for blocks not seen before. Cuts the Rust-side
   marshalling from O(N) to O(Δ) string work per poll. (The FFI parse itself is unchanged — see
   the DEEPER lever — but this removes the whole-lace re-format constant.)

3. **Bounded recompute cadence / in-flight guard** — in `spawn_finality_executor`
   (`:3660-3679`), skip launching a new verified recompute while one is already in flight for a
   not-yet-superseded snapshot, and cap the recompute rate (the debounce at `:3676` already
   coalesces 150 ms; extend it to "do not start a new O(N) recompute until the previous completed
   AND the frontier advanced"). Keeps the executor from starving itself on back-to-back full
   recomputes.

**Honest bound on the primary.** (1)-(3) cut the *frequency* of the full recompute and the Rust
*constant*; they do **not** change the O(n²)-per-recompute asymptotic of the Lean FFI, because it
is a pure whole-lace `String → String` that rebuilds `mkPastCache`/`mkRoundCache` each call. For a
BOUNDED payoff (submit → finalize within ~25-30 s on a bounded DAG) this is expected to close the
window: the executor stops burning the window on redundant recomputes of the settled past and
completes the poll that carries the round-2 client turn. For SUSTAINED operation at large N the
throughput ceiling remains — that is the DEEPER lever.

### DEEPER — the true incremental fix needs Lean (→ Alif)

To make per-poll cost O(Δ) (not O(history)) under sustained growth, the whole-lace memo must
**persist across FFI calls** — which the current pure `String → String` export cannot do. This is
a Lean/FFI source change and is **Alif's**, precisely:

- **What:** the exported entry runs `tauOrderFast`
  (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean:531-535`), which rebuilds
  `mkPastCache B` and `mkRoundCache B` (`:532-533`) over the entire lace every call. Two shapes,
  either sufficient:
  - **(a) A stateful/resumable export** that accepts the prior `PastCache`/`RoundCache` (a Lean
    object handle retained Rust-side across calls) plus only the new blocks, and EXTENDS the maps —
    turning the per-call cost from "rebuild over N" to "extend by Δ". Requires the caches to be
    proved extension-faithful (a `mkPastCache (B ++ Δ)` = `extend (mkPastCache B) Δ` lemma) so
    `tauOrderFast_eq` (`:540`) still transfers.
  - **(b) A verified checkpoint-compaction** so the FFI runs on a bounded SUFFIX: a proof that,
    past a stability depth, re-feeding a compacted prefix representation yields the same suffix
    order. Note `Dregg2/Consensus/TauPrefixMonotone.lean` REFUTES unconditional prefix stability
    (honest catch-up can sort a late block mid-prefix), so this needs a *bounded-window* stability
    certificate, not naive truncation.
- **Also worth flagging to Alif:** the Lean lace is `List`-backed with linear `find?`
  (`PastCache = List (BlockId × List BlockId)`, `cachedPast`, `:307-321`) and `computeRounds` is
  O(n²) (`:343-352`). Even without resumability, backing these by a map lowers the single-call
  constant materially.
- **Why not Rust-only:** the memo is a local of the pure Lean function; Rust cannot persist it
  without a new Lean export surface. The Rust PRIMARY above is the ceiling of what Rust can do
  without touching Lean.

### FALLBACK — bounded-timeout fail-open (⚠ FAIL-OPEN-LAW-sensitive — NOT a default; ember/consensus-owner's explicit call)

Only if the PRIMARY proves insufficient AND the DEEPER Lean change is not yet available: bound the
verified FFI at `poll_finalized_blocks:1041-1047` with `tokio::time::timeout(budget, …)`; on
timeout use the already-computed Rust `tau` order (`rust_order`, `:1025`) for that poll and record
a divergence-class metric + loud warn. **This WEAKENS the verification guarantee**: the verified
Lean rule stops being the decider on any poll that times out — the Rust order (unverified on the
commit path) finalizes instead. It is exactly the posture `DREGG_FINALITY_GATE=0` takes, but
per-poll and silent-until-warned, so it is FAIL-OPEN-LAW-sensitive. Do not ship it as a default;
it is an operator/consensus-owner lever, and the elevate-don't-degrade answer is PRIMARY + Alif's
DEEPER.

## 4. Expected effect

- **PRIMARY (Rust-only):** gate-ON completes far fewer redundant O(N) recomputes per window; the
  serial executor reaches the poll whose DAG super-ratifies the round-2 wave and finalizes the
  client turn WITHIN the window — the fully-verified payoff streams gate-ON (heights [1,1,1,1] →
  [2,2,2,2] cross-node under the verified Lean order), matching the gate-OFF behaviour but with the
  verified rule authoritative. Expected sufficient for the bounded payoff scenario.
- **DEEPER (Alif's Lean):** per-poll cost becomes O(Δ), so gate-ON finalizes under SUSTAINED growth
  (many waves, large N) without the throughput ceiling — the durable completion.
- **FALLBACK:** liveness always, but the verified gate is no longer the decider on timed-out polls
  (guarantee-weakening; ember's call only).

## 5. Rust-only or Alif's Lean?

**Both, layered.** The PRIMARY perf completion (cross-poll cache + incremental wire + bounded
recompute cadence) is **Rust-only** and should ship first — it is expected to close the bounded
payoff window without touching Lean. The **durable** O(Δ)-per-poll fix requires **Alif's Lean
change** (a resumable/stateful `tauOrderFast` export that persists `mkPastCache`/`mkRoundCache`
across calls, or a bounded-window checkpoint-compaction; and ideally map-backing the `List` caches).
The fail-open FALLBACK is neither — it is a guarantee-weakening operator lever gated on
ember/consensus-owner.

*Scope: read + diagnose + design only. The tree is RED (a concurrent terminal's
`circuit/src/garbled.rs` WIP does not compile), so no build/test was run; this is a
code-analysis diagnosis and a design, not an edit. No consensus/kernel/Lean source was changed.*
