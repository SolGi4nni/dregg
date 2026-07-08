# Post-Quantum Quorum Certificates — verified stack + deployment map

Two paths to a quantum-safe federation quorum certificate, one deployable now, one the compact future.
This document maps what is **machine-checked in Lean**, what is **implemented**, and — precisely — what
is **not yet done**. Nothing here is asserted beyond what a `#assert_axioms`-clean theorem or a passing
test supports.

## The two paths

| | scheme | carrier | QC size | status |
|---|---|---|---|---|
| **deployable now** | FIPS **hybrid**: ed25519 votes + ML-DSA-65 | DL + lattice (both mature/standardized) | `t × ~3.3 KB` (linear in committee) | verified spec + impl, 16/16 tests, staged |
| **compact future** | **Hermine** (lattice threshold) | MLWE / MSIS | one `~3 KB` cert (committee-independent) | verified to the line; reference impl |

The hybrid ships real quantum-safety today with crypto that has years of cryptanalysis behind it; Hermine
is the verified compact upgrade for when it matures (then it drops into the hybrid's PQ slot).

## The FIPS hybrid (deployable)

- **Security (Lean, `Crypto.HybridQuorum`).** `hybridVerify = classical ∧ pq`; `hybrid_unforgeable_of_either`
  (unforgeable if *either* half holds); `hybrid_survives_classical_break` (ed25519 **fully** broken by Shor
  → still unforgeable while ML-DSA holds). Non-vacuity is load-bearing (`both_broken_is_forgeable`).
- **Impl (`federation/src/frost.rs`).** `HybridQC` = ed25519 aggregate + per-signer `fips204` ML-DSA-65;
  `verify_hybrid_quorum` = both halves; `QuorumScheme::Hybrid`. 16/16 tests incl. the quantum-safety test
  (an *omniscient* adversary who reconstructs the whole classical group secret still cannot forge).
- **Design (decided).** Classical half = the existing ed25519 vote quorum (**no FROST DKG**); PQ half =
  per-member ML-DSA-65; don't persist old QCs. Cost is **size, not compute** (verify is a handful of fast
  checks); QC grows linearly with committee size — comfortable to n≈30–50, past which Hermine is the answer.

## Hermine (the verified compact-PQ scheme)

Everything above the irreducible MLWE/MSIS line is machine-checked (`#assert_axioms`-clean):

- **Correctness** — `HermineThreshold.hermine_cert_verifies_under_group_key` (the t-of-n cert verifies).
- **Unforgeability** — `HermineExtractor` (a forked forgery extracts a preimage of the key) →
  `HermineMSIS.forked_forgery_yields_msis_solution` (that preimage IS a short nonzero kernel vector =
  an MSIS solution: kernel unconditional, **short** via the norm-bound leg, nonzero via §discharge).
- **The `u ≠ 0` discharge** (`HermineDischarge`) — derived, not assumed, from **MLWE lossiness** +
  **challenge-difference invertibility**.
  - Lossiness (`HermineLossiness`) — **proven** by the pigeonhole (a compressing map has two distinct
    short preimages), with a decide-checked instance.
  - Invertibility (`HermineInvertibility`) — **proven** at n=2 (R_q a field for q≡3 mod 4);
    (`InvertibilityCRT`) the general-n **CRT skeleton** (invertibility ⟺ nonzero in each residue field),
    reducing n≥256 to its number-theoretic core.
- **t-privacy** (`ShamirPrivacy`) — a corrupt minority of t−1 learns nothing (unconditional, via Lagrange).
- **Key-hiding** (signing does not leak the secret):
  - `Smudging` — the noise-flooding lemma `SD(Uniform, shift) ≤ B/M` (uniform + total-variation).
  - `HermineHiding` — the signature is `B/M`-simulatable without the secret; un-linkable across secrets.
  - `RenyiHiding` — the tighter **Gaussian/Rényi** frame: order-2 divergence, multiplicativity over
    coordinates, and `renyi_probability_preservation` (`P(E)² ≤ R₂·Q(E)` — hardness transfers from the
    simulator to the real scheme).
- **Concrete** (`HermineConcrete`) — the whole reduction fires on real numbers (decide-checked witness).
- **Reference impl** (`crypto-hermine/`) — `R_q = ℤ_q[X]/(Xⁿ+1)` (N=64, Q=8380417 Dilithium prime), the
  `verify` symbol-for-symbol with the spec, trusted-dealer threshold, discrete-Gaussian **and** uniform
  noise-flooding; the key-hiding TV shrinks monotonically with the noise width (empirically demonstrated).

## The irreducible line, and the honest remainders

**Irreducible** (assumed, never proved — shared by *all* lattice crypto, FIPS ML-DSA included):
MLWE and MSIS hardness (`Crypto.Lattice.MSISHard` / `MLWESearchHard`).

**Scoped remainders** (stated precisely as interface hypotheses, not faked):
1. **n≥256 invertibility** — the CRT skeleton is proven; the number-theoretic core (a low-∞-norm nonzero
   element does not vanish mod any degree-d factor of `Xⁿ+1`) is the remaining Lyubashevsky–Seiler step.
2. **The discrete-Gaussian Rényi bound** — the Rényi framework + preservation are proven; the specific
   `R₂(D_σ, D_σ+δ) ≤ exp(…)` per-coordinate Gaussian bound (requires ℝ analysis) is the remaining step.
3. **Production impl** — CSPRNG, constant-time (data-independent) sampling, full-size (n≥256) parameters.
4. **External cryptanalysis / audit** — calendar-time; exactly why Hermine belongs *inside the hybrid*
   (hedged) rather than deployed solo.

## File index

- Spec: `metatheory/Dregg2/Crypto/{Frost, HermineThreshold, ShamirPrivacy, ThresholdReduction,
  SchnorrExtractor, HermineExtractor, ThresholdForking, HashSig, HashSigMerkle, Lattice, HermineMSIS,
  HermineDischarge, HermineConcrete, HermineLossiness, HermineInvertibility, InvertibilityCRT, Smudging,
  HermineHiding, RenyiHiding, HybridQuorum}.lean`
- Impl: `crypto-hermine/` (Hermine reference), `federation/src/frost.rs` (FROST + hybrid QC).
- Poster (build-in-public): `~/src/dregg-posters/post-quantum-quorum.txt`.
