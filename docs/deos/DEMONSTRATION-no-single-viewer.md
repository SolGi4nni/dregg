# Demonstration — real, distributed, no-single-viewer clearing

*Two runnable demonstrators, both committed, both independently re-run and verified (not agent-claimed).
This is the honest artifact behind the sentence: **the dealer cannot see the cards, the players cannot see
each other, and a cheater is caught and named.***

## The claim, stated exactly

> A committee of independent parties jointly holds a public encryption key whose secret **no one party (and no
> operator) ever possesses**. A *share-less* clearing house computes a private multilateral net **entirely on
> ciphertext** — it never sees an obligation — and the committee reveals **only** the net vector. A party that
> cheats the setup is **detected and attributed by name**, and the committee does not come up. Every signature
> is answered by the **audited** Lean ML-DSA/ML-KEM cores — never an unaudited fallback.

Nothing above is simulated hand-waving. Both demonstrators run the real `DistributedDkg` (PQ-authenticated
bivariate-VSS threshold keygen) and a real threshold decrypt, under the audited cores, with
`DREGG_ALLOW_UNAUDITED_PQ` asserted-absent (a green run *means the audited cores answered*).

## Demonstrator A — readable, single-binary (`fe2f43acc`)

The whole ceremony in one measurable binary: `N=4` party actors whose secrets live behind a private
`mod party` (Rust's privacy **compiler-enforces** that no orchestrator variable ever holds two parties'
secrets; `s = Σ sᵢ` is never materialized).

```
cargo run --example distributed_ceremony_demo --features verified-pq-runtime-tests -p fhegg-fhe
```

**Measured (release):** distributed keygen ~20 s · homomorphic netting of 128 member books **169 ms** ·
threshold decrypt + combine **18 ms** · `Σ nets = 0`, exact vs cleartext · a hostile dealer caught:
`VssCommitmentMismatch { dealer: 0, recipient: 1 }`.

Read this one to *understand* the ceremony.

## Demonstrator B — genuinely distributed, separate OS processes (`f84cee425`)

The same ceremony, but each party is its **own operating-system process** communicating only over TCP — so
"no single viewer" is enforced by the **OS**, not just by Rust. A share-less clearing house drives it.

```
cargo test -p fhegg-fhe --features verified-pq-runtime-tests \
    --test distributed_netting_processes -- --nocapture --test-threads=1
```

**Measured (verified by re-run):** `2 passed` in ~35 s · **4 custody parties in 4 distinct OS pids**, clearing
house holds no share · DKG over real TCP ~23 s · house-blind netting ~3 s · distributed decrypt across 3 party
processes ~6 s · `Σ nets = 0`, exact · tamper across processes: party 1's *process* refuses
`VssCommitmentMismatch { dealer: 0, recipient: 1 }`, exits 2, never readies. Each party's custody row lives in
its own address space and a `0600` secret file; peers exchange only sealed `Vec<u8>` envelopes.

Run this one to *believe* it — four processes, one net, nobody peeked.

## What is proved, and what is not (honest boundary)

**Proved, and shown:** real distributed threshold keygen with no single secret-holder; house-blind multilateral
netting computed by a share-less party; threshold decrypt revealing only the result; malice **detected and
attributed** across real process boundaries; audited PQ throughout.

**Not yet, and named:**
- **Scale numbers are honest-partial.** 128 members / 994 obligations is measured clean. The netting cost is
  `O(members)` (the fold), and obligations *amortize* into the SIMD-batched books (`O(members)`, not
  `O(obligations)`) — but a headline scale figure needs the fold timed separately from per-member encryption
  (which is per-client-parallel in reality, not the serial single-machine artifact). That instrumentation is
  the next crank, not done here.
- **Keygen ~20–23 s** is a real 4-party degree-4096 VSS cost, unoptimized — a one-time setup, not per-clearing.
- **Transport is process-local TCP + a rendezvous dir**, not a hardened network layer / WAN.
- The **multiplicative** halls (Dark Pool `x·y=k`) — where the measured GPU ct×ct wins (3.35–5.13×) apply —
  are a separate scenario; this netting is additive (GPU *loses* on the memory-bound fold; CPU is correct).

## Reproduce both

Needs the audited Lean cores (`dregg-lean-ffi`), which the `verified-pq-runtime-tests` feature links. A bare
`cargo test` stays green without the archive (Demonstrator B self-cfg-gates to an empty target). Neither path
will run if `DREGG_ALLOW_UNAUDITED_PQ` is set — by design.
