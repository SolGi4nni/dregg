//! # crypto-tanuki — a correctness-first REFERENCE implementation of the
//! **Tanuki** two-round lattice threshold signature.
//!
//! Tanuki (NIST Workshop on Multi-Party Threshold Schemes, MPTS 2026;
//! Boschini, Espitau, Kaiser, Katsumata, Kaviani, Lai, Malavolta, Prest,
//! Schwabe, Takahashi, Takemure, Tibouchi) is a lattice threshold signature
//! that synthesizes two prior works:
//!
//! * **[EKT24]** T. Espitau, S. Katsumata, K. Takemure. *Two-round threshold
//!   signature from algebraic one-more learning with errors.* CRYPTO 2024.
//!   <https://eprint.iacr.org/2024/496>
//! * **[BKLMTT24] (Ringtail)** C. Boschini, D. Kaviani, R. W. F. Lai,
//!   G. Malavolta, A. Takahashi, M. Tibouchi. *Ringtail: Practical Two-Round
//!   Threshold Signatures from Learning with Errors.* IEEE S&P (Oakland) 2025.
//!   <https://eprint.iacr.org/2024/1113>
//!
//! It is a Raccoon-based ([dPKPR24] / [dPK+24] Threshold Raccoon), FROST-style
//! ([KG20]) two-round (1 offline + 1 online) scheme over
//! `R_q = ℤ_q[X]/(Xⁿ+1)`. This crate implements the construction from Fig.1
//! ("Tanuki Signing (Draft)", slide 10 of the MPTS-2026 talk), mapped symbol
//! for symbol in [`threshold`].
//!
//! ## The construction, mapped to Fig.1
//!
//! | Fig.1                                   | this crate |
//! |-----------------------------------------|------------|
//! | `t ← ⌊A·s + e⌉` (rounded MLWE key)      | [`threshold::keygen`], [`ring::Poly::round_drop`] |
//! | `(s_1..s_n) ← ShamirShare(s)` over `R_q`| [`shamir::share`] (constant eval points; unit differences) |
//! | `(sd_1..sd_n) ← SeedGen` (pairwise)     | [`threshold::keygen`] mask master → [`hash::mask_gen`] |
//! | `R_i,E_i ← Sample; W_i ← A·R_i + E_i`   | [`threshold::sign1`] (wide `W_i ∈ R_q^{k×rep}`, in the clear) |
//! | `ssid ← (T, {W_j}, m)`                  | `encode_ssid` in [`threshold`] |
//! | `b ← G(vk, ssid)`                       | [`hash::agg_vector`] (signed monomials, EKT24 instantiation) |
//! | `w ← ⌊W·b⌉ ; c ← H(vk, m, w)`           | [`threshold::sign2`], [`hash::challenge`] (fixed-weight ternary) |
//! | `m_i ← MaskGen(sd_i, ssid)`, `Σ m_j=0`  | [`hash::mask_gen`] (pairwise zero-sum) |
//! | `z_i ← c·λ_{T,i}·s_i + R_i·b + m_i`     | [`threshold::sign2`] |
//! | `z ← Σ z_j`; hint `h`; `σ=(c,z,h)`      | [`threshold::finalize`] |
//! | `w' ← ⌊A·z − c·t⌉ + h ; c =? H(..); ‖·‖≤B` | [`threshold::verify`] |
//!
//! ## HONEST BOUNDARY — what this crate is and is NOT
//!
//! This is a **deployable-shape correctness reference**: every structural
//! feature of Tanuki's two rounds is present and exercised on concrete `R_q`
//! numbers, so the scheme's shape can be studied and benchmarked. It is NOT
//! deployment-grade and must never sign live.
//!
//! * **The TS-UF-0 security proof is CITED, not re-proven here.** Tanuki's
//!   unforgeability (game-based TS-UF-X in the ROM [BTZ22], under MLWE + variants
//!   of MSIS, with Gaussian masks reduced via Hint-MLWE→MLWE [KLSS23]) is
//!   established in [EKT24]/[BKLMTT24]/[ZT25]. Nothing in this crate re-derives
//!   it; the tests witness *correctness and structural binding*, not security.
//! * **Reference parameters** ([`threshold::Params::reference`]): `n=256`,
//!   `q=8380417` (Dilithium prime, NTT-friendly), `k=ℓ=rep=4`, `n=5`, `t=3`,
//!   challenge weight `ω=20`, small half-widths `η=2`. These are illustrative,
//!   NOT the parameter-searched NIST-grade sets.
//! * **Acceptance bounds** (`z_bound`, `h_bound`) are calibrated so honest
//!   signatures pass with margin AND forged/random responses are rejected — they
//!   are NOT the security-derived `B`.
//! * **Reference samplers**: masks are drawn UNIFORM over `R_q` (a perfect,
//!   simple hiding for the zero-sum demonstration); small elements use a biased,
//!   non-constant-time `mod (2η+1)` sampler over a blake3 XOF (a PRG, not an
//!   audited CSPRNG seeded from OS entropy). Production Tanuki uses discrete
//!   Gaussian (or sum-of-uniform) masks/secrets whose exactness feeds the
//!   Hint-MLWE reduction. See [`hash`].
//! * **Trusted-dealer KeyGen**: `SeedGen`/sharing are done by a dealer; all
//!   signers hold a common mask master seed and derive pairwise seeds from it
//!   (real Tanuki distributes only a party's own pairwise seeds; a DKG replaces
//!   the dealer). See [`threshold::SignerKey`].
//! * **Rounding**: `⌊·⌉` keeps scale (rounds coefficients to the nearest
//!   multiple of `2^ν`, `ν = DROP_BITS`) with `ξ = 1`. The bandwidth-saving
//!   low-bit-discard variant and the EKT24 `×2`/`ξ=2` monomial convention are
//!   alternative (documented) instantiations, not implemented.
//! * **Not constant-time; no zeroization of secrets.**
//!
//! ## KEY DIFFERENCES from crypto-hermine (the reason this reference exists)
//!
//! Both are Raccoon+FROST two-round lattice threshold signatures; this crate is
//! the "what a cited-proven 2-round looks like" reference to benchmark Hermine's
//! commit-then-reveal 2-round against. The load-bearing differences:
//!
//! | aspect                | **Tanuki** (this crate)                          | **Hermine** (crypto-hermine)                     |
//! |-----------------------|--------------------------------------------------|--------------------------------------------------|
//! | round-1 commitment    | **wide** `W_i = A·R_i + E_i ∈ R_q^{k×rep}`, broadcast **in the clear** (no hash) | single-column `w_i = A·y_i`, hidden behind a **blake3 hash commitment** `cm_i` |
//! | rushing defense       | **hashed `b`-aggregation** `b ← G(vk, ssid)`; the challenge depends on all `W_j` via `ssid`, so a rusher cannot bias `w` | **BN06 commit-then-reveal**: reveal is checked against the prior `cm_i`, equivocation is detected |
//! | per-signer masking    | **pairwise zero-sum PRF masks** `m_i`, `Σ_{j∈T} m_j = 0` (needed because `R_i·b` cannot hide `c·λ_{T,i}·s_i`) | **noise-flooding** (smudging) masks `y_i`, wide/Gaussian |
//! | secret sharing        | **standard Shamir over `R_q`** with **large** shares & Lagrange coeffs (masks absorb the size) → threshold up to ~1024 | **short/small secret sharing** → easy identifiable abort, smaller thresholds |
//! | key                   | **rounded** `t = ⌊A·s + e⌉` (+ hint `h` at verify) | **exact** `t = A·s` |
//! | signature             | `(c, z, h)` — carries a rounding hint            | `(c, z)` over `A·z = w + c·t` (no hint)          |
//!
//! (This taxonomy matches the MPTS-2026 conclusion slide: "Tanuki: one-time
//! masks + standard Shamir ⇒ larger threshold ~1024 without IA; Hermine: short
//! secret sharing ⇒ easy IA with smaller thresholds".)
//!
//! ## FLAGGED — not completed precisely in this reference
//!
//! * The rounding uses the scale-keeping `ξ=1` convention, not EKT24's
//!   `×2`/signed-monomial `ξ` or the bandwidth-saving low-bit discard.
//! * Masks are uniform, not the Gaussian masks the Hint-MLWE proof assumes.
//! * KeyGen is a trusted dealer (no DKG), and `SeedGen` shares a global master.
//! * Norm bounds are empirically calibrated, not security-derived.
//! * No identifiable-abort / complaint handling; the network layer is absent
//!   (the API is message-shaped — round-1/round-2 broadcasts are explicit
//!   values — but there is no transport, timeouts, or misbehavior arbitration).

pub mod hash;
pub mod linalg;
pub mod ring;
pub mod shamir;
pub mod threshold;

pub use linalg::{PolyMatrix, PolyVec};
pub use ring::{Poly, DROP_BITS, N, Q};
pub use threshold::{
    finalize, keygen, run_ceremony, sign1, sign2, verify, KeyPackage, Params, Round1Public,
    Round1Secret, Round2Public, Signature, SignerKey, VerifyingKey,
};
