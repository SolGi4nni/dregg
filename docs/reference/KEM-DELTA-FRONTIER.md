# KEM-DELTA-FRONTIER — the compression ↔ δ ↔ ciphertext-size frontier (the KEM analog of the FRI param frontier)

> A tight decryption-failure `δ` bound is an EFFICIENCY lever, not just an exactness one. `δ` trades against
> ciphertext size through the compression parameters `(d_u, d_v)`: more compression → smaller ciphertext →
> larger rounding error → higher `δ`. The gap between our CONSERVATIVE proven `δ` and the TRUE (exact-convolution)
> `δ` is bandwidth left on the table — for any *tunable* variant. This file quantifies that frontier and states
> whether it is actionable for dregg's KEM. Model + grid: `scripts/kem_delta_frontier.py`.
> Related: [[DELTA-FUTURE]], [[project-pq-metatheory-connected]].

## 1. dregg's KEM deployment — STANDARD ML-KEM-768, FIPS-fixed

dregg deploys **standard ML-KEM-768 (FIPS 203)**, not a tunable lattice KEM:

- `dregg-pq/src/hybrid_kem.rs:61` — `use ml_kem::{… KemCore, MlKem768}` (the `ml-kem` v0.2.3 crate).
- `dregg-pq/src/hybrid_kem.rs:371-372` — `type Ek = <MlKem768 as KemCore>::EncapsulationKey` / `Dk`.
- `dregg-pq/src/lib.rs:24-27` — the KEM is the **X-Wing / TLS `X25519MLKEM768`** hybrid (X25519 + ML-KEM-768,
  concatenation-KDF combiner). ML-KEM-768 is the post-quantum half only.
- Sizes are the FIPS-203 ones: **1088-byte ciphertext**, 1184-byte encapsulation key, 2400-byte decapsulation
  key (`hybrid_kem.rs:336,438,448,640`).

The compression parameters are therefore **`d_u = 10, d_v = 4`, FIPS-fixed**. `ciphertext = 32·(d_u·k + d_v) =
32·(10·3 + 4) = 1088` bytes (`k = 3`). Tuning `(d_u, d_v)` is not a free knob here: it breaks byte-interop with
every conformant ML-KEM peer and voids the FIPS guarantee. **The compression lever applies to a CUSTOM variant,
not to the deployed KEM.**

## 2. The exact compression ↔ δ ↔ size model

The decryption-failure noise decomposition (`MlKemDelta.lean:11,556`):

```
e_total = eᵀr − sᵀe1 + e2 + Δv − sᵀΔu
```

with, per coefficient over `q = 3329`, `k = 3`, `n = 256`, `η1 = η2 = 2`:

- `eᵀr`, `sᵀe1` — each `k·n = 768` products `χ·χ` of CBD(2) values (`MlKemDelta.lean:563`),
- `sᵀΔu` — `768` products `χ · cErr_{d_u}` (`s_i` × the `d_u`-compression rounding error),
- `e2` — one CBD(2) term, `Δv` — one `cErr_{d_v}` term.

CBD(2) has weights `(1,4,6,4,1)/16` (`MlKemDelta.lean:812`). The compression error is the ACTUAL rounding error

```
cErr_d(x) = mod±_q( Decompress_d(Compress_d(x)) − x )      x uniform on ℤ_q
```

on the LITERAL FIPS-203 `Compress`/`Decompress` (`MlKemCodec.lean:141-148`, round-half-up), generalizing the
`d_v = 4` `cErr` of `MlKemDelta.lean:2738` to any `d`. The failure event is `|e_total| ≥ 832` (`MlKemDelta.lean:156`,
the `q/4` decode window).

`scripts/kem_delta_frontier.py` computes the EXACT per-coefficient `δ = Pr[|e_total| ≥ 832]` by direct
(non-negative) convolution of these PMFs — **not FFT**: FFT's signed inverse loses the ~`2⁻¹⁷⁰` tail to
double-precision cancellation, whereas convolving non-negative PMFs keeps every tail atom to relative error
~`10⁻¹⁵`, well above the `~10⁻⁵³` values we read. Assembled `δ` is the union bound over coefficients.

**Cross-check against the Lean (the model is faithful):** the script reproduces `cErr_4` support exactly
`[−104, 104]` (Lean `cErr_bound`, `MlKemDelta.lean:2793`) and max fiber count exactly `16` (Lean
`cErrFiber_le_16`, `MlKemDelta.lean:2785`). At standard `(10, 4)` it gives per-coefficient `δ = 2⁻¹⁷⁶`,
matching the "near-Gaussian convolution `≈ 2⁻¹⁸⁰`" ember/§19 estimate (`MlKemDelta.lean:77`).

## 3. The frontier (exact convolution; assembled over n = 256; `ct = 32·(d_u·3 + d_v)` bytes)

```
 du  dv   ct_B   log2 per-coeff   log2 assembled
  8   2    832        -17.40           -9.40
  8   3    864        -30.05          -22.05
  8   4    896        -37.63          -29.63
  9   3    960        -73.97          -65.97
  9   4    992        -96.46          -88.46
  9   5   1024       -108.45         -100.45
 10   2   1024        -65.71          -57.71
 10   3   1056       -133.49         -125.49
 10   4   1088       -176.25         -168.25   ← STANDARD ML-KEM-768
 10   5   1120       -199.40         -191.40
 11   3   1152       -160.36         -152.36
 11   4   1184       -211.96         -203.96
```

(Full `d_u ∈ [6,11], d_v ∈ [2,7]` grid in the script output.) Reading the frontier:

- A `d_v` bit costs **32 bytes** and buys ~20–40 bits of `δ` near standard params (`(10,3)→(10,4)`: +43 bits;
  `(10,4)→(10,5)`: +23 bits).
- A `d_u` bit costs **`k·32 = 96` bytes** and is worth far more `δ` (`(9,4)→(10,4)`: +80 bits) — `d_u`
  multiplies across the `k = 3` module rank, so it is the coarse knob; `d_v` is the fine one.
- The efficient frontier is the lower-left staircase: `(10,4)=1088 B` at `2⁻¹⁶⁸`, `(10,3)=1056 B` at `2⁻¹²⁵`,
  `(9,4)=992 B` at `2⁻⁸⁸`.

## 4. What the tight bound saves vs the conservative bound

Our deployed proven bound is `δ ≤ 2⁻¹⁵³` assembled (`rZ_decapsFailure_le_delta153`, `MlKemDelta.lean:3182`) —
the honest ceiling of the exact-MGF **Chernoff** route on the true `Δv` law. The EXACT assembled `δ` at the
same `(10,4)` is `2⁻¹⁶⁸`. So the conservative proof is **15.25 bits looser** than the truth — the Chernoff
method's `≈15.7σ` Bahadur–Rao prefactor slack (`MlKemDelta.lean:74-77`), roughly config-independent in bits.

(The task's "~27 bits" figure compares the ASSEMBLED conservative `2⁻¹⁵³` against the PER-COEFFICIENT true
`≈2⁻¹⁸⁰`, mixing the two union levels. Level-consistent, the unused margin is **15 bits assembled** (`2⁻¹⁵³` vs
`2⁻¹⁶⁸`) ≈ **13 bits per-coefficient** (`2⁻¹⁶³` vs `2⁻¹⁷⁶`). Same lever, stated at one level.)

Converting that margin into ciphertext bytes at each `δ` target (conservative surrogate = exact `δ` weakened by
the 15.25-bit method slack):

| δ target | tight (exact) config | conservative config | tight-bound saving |
|---|---|---|---|
| `2⁻¹⁶⁴` (FIPS ML-KEM-768) | `d_u=10, d_v=4` → **1088 B** | `d_u=10, d_v=5` → **1120 B** | **32 B / ciphertext (2.9%)** |
| `2⁻¹²⁸` (128-bit matched) | `d_u=10, d_v=4` → 1088 B | `d_u=10, d_v=4` → 1088 B | 0 B (grid too coarse here — the `d_v` step from `2⁻¹²⁵` to `2⁻¹⁶⁸` skips over the target) |

The actionable result: **15 bits of unused `δ` margin = exactly one `d_v` increment = 32 bytes/ciphertext (2.9%)**
at the FIPS-strength target. The margin is worth precisely one fine-knob step; it is not enough for a `d_u` step
(96 bytes / ~80 bits) and the integer `d_v` grid is chunky enough that at some targets the saving rounds to zero.

## 5. Applicability verdict — exactness now, bandwidth only for a future custom KEM

- **For the deployed KEM (standard ML-KEM-768): the tight-δ win is EXACTNESS ONLY, not bandwidth.** `(d_u, d_v) =
  (10, 4)` is FIPS-fixed; dregg cannot ship `(10, 3)` and stay interoperable with the `ml-kem` crate, X-Wing
  peers, or the FIPS guarantee. Firing the tight-δ formalization (the radix-2 interval-FFT campaign that would
  replace the Chernoff `2⁻¹⁵³` with the exact convolved `≈2⁻¹⁶⁸`) buys a *sharper proven number for the same
  1088 bytes* — real assurance value (it closes §19's residual **R1**), zero bandwidth value.

- **For a FUTURE dregg-native / custom lattice KEM (no FIPS interop constraint): the lever is real and worth
  ~one `d_v` step ≈ 32 bytes ≈ 2.9% of ciphertext** at 128–164-bit `δ` targets — and the exact-convolution
  machinery here is exactly what sizes it. A custom variant targeting `δ ≈ 2⁻¹²⁸` (rather than ML-KEM's
  conservative `2⁻¹⁶⁴`) could additionally drop toward `(10, 3) = 1056 B` on the frontier — but that is a
  *parameter-choice* saving (accepting a higher `δ` target), separate from the *tight-bound* saving (proving the
  true `δ` at a fixed target).

**Bottom line for the campaign decision:** the tight-δ formalization is worth firing for ASSURANCE (exact `δ`,
closing R1) and as the SIZING TOOL for any future custom KEM, but it does NOT unlock bandwidth on the deployed
FIPS-fixed ML-KEM-768. The bandwidth prize is real but conditional on building a non-FIPS variant, and it is
modest (~2.9%, one `d_v` bit) rather than dramatic — the compression grid is coarse and `δ` is steep in
`(d_u, d_v)`.
