# Custody Bulletproof prover profile — 2026-07-22

This note records measured release-mode results for the exact BFV custody-share
proof used by the authenticated encrypted-order tooth.  It is a performance
record, not a change to the proof statement or a claim that the classical
Ristretto proof is post-quantum.

## Workload and gate

The focused gate is:

```sh
scripts/hbuild pq-bfv-native \
  env DREGG_BULLETPROOFS_PROFILE=1 \
  cargo nextest run --profile full --release -p fhegg-fhe \
  -E 'test(authenticated_encrypted_orders_gate_real_game_asset_settlement_crypto_tooth)' \
  --no-capture
```

It produces two custody shares concurrently.  Each share contains three
aggregated range proofs:

| proof | values | bits | inner-product dimension |
|---|---:|---:|---:|
| smudge low | 8,192 | 64 | 524,288 |
| smudge high | 8,192 | 32 | 262,144 |
| signed quotients | 32,768 | 64 | 2,097,152 |

The hbox run exposed 16 worker threads to Rayon.  Timings vary when other swarm
lanes share the host, so comparisons below name both the code state and the
observed contention rather than presenting a synthetic calendar estimate.

## Baseline

Before parallel generator derivation, the least-contended same-host release run
measured:

| phase | elapsed |
|---|---:|
| verified DKG | 2.596 s |
| prove two shares | 92.917 s |
| verify two shares, parallel | 18.942 s |
| verify two shares, serial reference | 32.542 s |
| complete tooth | 164.457 s |

An instrumented repeat under heavier hbox contention measured 122.026 s for the
same prove-two phase.  Its 32,768×64 range proofs spent 61.5–63.9 s per share in
the final inner-product assembly and 14.6–15.2 s in bit commitment.  The host
load sensitivity is why the focused phase counters are more useful than one
undifferentiated wall-clock number.

## Accepted optimization

Commit `612a9c56c` derives independent `BulletproofGens` party namespaces in
parallel when the already-enabled `parallel-prover` feature is active.  The
serial feature path is unchanged.  A differential test derives every sampled G
and H point again through the serial namespace chain and requires point-for-point
equality.

With that commit and the opt-in phase counters, the exact heavy tooth was green
with:

| phase | elapsed |
|---|---:|
| prove two shares | 43.38 s |
| verify two shares, parallel | 17.66 s |
| verify two shares, serial reference | 36.88 s |
| complete tooth | 120.33 s |

The clean-baseline proving comparison is 92.917 s → 43.38 s, approximately a
2.1× reduction.  This is an observed same-host result, not a universal speedup
constant.

After generator derivation, the three range proofs took approximately
6.6–6.75 s, 3.06–3.09 s, and 26.21–26.30 s per share.  Cumulatively, final
inner-product work accounts for about 27.1 s per share and bit commitment for
about 7.7 s; all other reported range-prover phases are below one second.

Commit `3ca40ec8d` then removed a second representation-only cost from the IPP
L/R wrapper.  The wrapper had copied millions of full extended Ristretto points
into a temporary vector before every chunked dalek MSM.  It now chunks borrowed
point references while retaining the same owned scalar vector, point order,
32,768-term boundaries, dalek calls, and deterministic group reduction.

In a consecutive same-lane before/after run, the largest 32,768×64 proof's IPP
phase moved from 20.238–20.246 s per share to 16.010–16.032 s, about 21%.  The
whole prove-two phase moved from 43.380 s to 39.838 s, about 8.2%, and the full
heavy tooth remained green at 94.84 s.  Vendor IPP tests, a forged final-scalar
rejection tooth, seeded serial/parallel proof-byte equality, and ordinary
verification were green.  As above, percentages are observations on that hbox
lane, not protocol constants.

## Rejected optimization

We tested replacing the local prover's many small constant-time `S_j` MSMs with
memory-bounded aggregate constant-time dalek MSM batches.  Seeded proof bytes
matched the serial reference, but the real hbox tooth regressed:

| candidate phase | observed result |
|---|---:|
| 32,768×64 bit commitment | about 21.4–21.6 s per share |
| prove two shares | 133.299 s |

The candidate was removed.  Exactness is necessary but not sufficient for an
optimization to survive.

The obvious CPU specialization of the remaining public two-point generator
fold was also measured before substitution.  Across 262,144 pairs on 16 hbox
threads, dalek's existing two-term variable-time MSM took 605,034 µs; spelling
the same public expression directly as `u⁻¹·L + u·R` took 1,133,728 µs.  Point
parity was exact, but the direct form was about 1.87× slower, so it too was
removed.  Any next win here needs a genuine fixed-scalar pointwise batch or
resident backend rather than a surface-level algebra rewrite.

## Security and next seam

- Secret-scalar commitments remain on dalek's constant-time CPU MSM path.
- The experimental branch-bearing WGPU public MSM remains opt-in and is not
  prover authority.
- Generator parallelism changes scheduling only; labels, chain offsets, points,
  transcript construction, and proof verification remain exact.
- Borrowed IPP point chunks change temporary storage only; they do not change
  scalar/point order, chunk arithmetic, transcript challenges, or authority.
- The largest remaining CPU seam is the inner-product generator fold.  It
  applies the same public transcript pair `(u, u⁻¹)` to millions of independent
  public G/H point pairs.  That is a plausible fixed-scalar pointwise CPU/GPU
  batch boundary.  It must be kept distinct from the L/R MSMs whose scalars are
  witness-derived.

Set `DREGG_BULLETPROOFS_PROFILE=1` to print per-proof `party-construct`,
`bit-commit`, `poly-commit`, `proof-share`, `inner-product`, and total timings.
The counters are silent otherwise.
