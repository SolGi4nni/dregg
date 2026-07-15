//! The CARRY-FREE ADDITIVE fold — codex Round-3 Q1's Tier-0 speed lever, MEASURED.
//!
//! The exact-integer TFHE clear (`crate::fhe_clear`) folds the per-order unary
//! price-bucket increments with `FheUint16::sum`, and the MEASURED envelope
//! (`MEASURED-ENVELOPE.md`, `HBOX-24CORE-ENVELOPE.md`) showed the load-bearing
//! finding: a multi-block radix add **carry-propagates**, and carry propagation
//! is PBS-class (~13 ms/element even in the deferred-carry tree-sum), so the
//! aggregation DOMINATES the clear (up to 45× the O(K) crossing). The estimates'
//! "addition ≈ µs, the cheap primitive" is only true for an ADDITIVE scheme.
//!
//! This module builds that additive scheme for real and measures it. The carrier
//! is **BFV** (`fhe.rs`) — an exact-quantized `R_q = Z_q[X]/(X^n+1)` ring scheme,
//! SIMD-batched into `n` plaintext slots, whose ciphertext addition is a native
//! modular polynomial add: **no carry propagation, no bootstrap, no PBS**. This
//! is exactly the "exact quantized BFV/BGV for the carry-free fold" of
//! `docs/deos/FHEGG-CODEX-ROUND3.md` §B/Q1 (CKKS is the approximate cousin, not
//! available in tfhe-rs; BFV is the exact additive path and the one codex named
//! for the *auction* fold specifically — CKKS is for the T-step PDHG search).
//!
//! The SIMD packing is the structural win over TFHE. TFHE packs one integer per
//! `FheUint16` and must sum each of the K buckets separately: 2·K bucket-sums,
//! each over ~N/2 carry-propagating adds → O(N·K) PBS-class work. BFV packs the
//! WHOLE K-bucket increment vector of one order into a SINGLE ciphertext (K ≤ n
//! slots), so folding N orders is just **N−2 ciphertext additions total** (one
//! running sum for demand, one for supply), each a carry-free poly add that
//! updates all K buckets at once. O(N) carry-free adds vs O(N·K) PBS adds.
//!
//! The crossing (`D[p] ≥ S[p]`) is a comparison, and — codex's hard boundary —
//! "there is no comparison from additive homomorphism alone." So the crossing is
//! NOT done here; it stays on TFHE (the measured ~10 s O(K) crossing) via a
//! scheme-switch (CHIMERA/PEGASUS). The correctness harness below recovers p*/V*
//! from the decrypted curves purely to CHECK the fold against the plaintext
//! reference — that clear-domain crossing is not part of the measured additive
//! cost and is labelled as such.
//!
//! Mint-safety: the fold's quantization is the deployable floor/ceil quantizer
//! proven mint-safe in `metatheory/Market/MintSafeQuantization.lean`
//! (`mint_safe_floor_ceil`: floor inputs, ceil outputs, at step Δ; the integer
//! gate `Σ⌈vout/Δ⌉ ≤ Σ⌊vin/Δ⌋` provably forbids `Σvout > Σvin`). See `mint_safe`.

use std::sync::Arc;
use std::time::{Duration, Instant};

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use rand_09::rngs::StdRng as StdRng09;
use rand_09::SeedableRng as SeedableRng09;

use crate::{order_increment, Order, Side};

/// Per-phase timing + op counts from one BFV additive fold (the honest envelope,
/// apples-to-apples with `crate::FheTiming` for the TFHE clear).
#[derive(Clone, Debug, Default)]
pub struct BfvFoldTiming {
    pub n: usize,
    pub k: usize,
    /// BFV ring degree n (= number of SIMD slots; must be ≥ K).
    pub degree: usize,
    /// BFV plaintext modulus t (bucket sums must stay < t: no wrap).
    pub plaintext_modulus: u64,
    /// wall time to generate the BFV keypair (one-time network setup).
    pub keygen: Duration,
    /// wall time to encrypt all N packed order increments (N ciphertexts total —
    /// each packs the FULL K-bucket vector, vs TFHE's N·K scalar ciphertexts).
    pub encrypt: Duration,
    /// wall time for the additive fold itself (the carry-free part under test).
    pub fold: Duration,
    /// number of homomorphic ciphertext ADDs in the fold. Each add folds ALL K
    /// buckets at once (SIMD), so this is ~N, NOT N·K.
    pub add_ops: usize,
    /// wall time to decrypt the two aggregate curve ciphertexts.
    pub decrypt: Duration,
    /// clearing price bucket p* recovered from the decrypted curves (clear-domain
    /// crossing — NOT part of the additive cost; the real crossing stays TFHE).
    pub p_star: usize,
    pub v_star: u32,
}

/// Pick a real 128-bit BFV parameter set: degree ≥ K slots, plaintext modulus t
/// with headroom over the largest bucket sum (no wrap), ample noise budget for an
/// N-deep additive fold (BFV additions grow noise ~linearly; no multiplications,
/// so no relin/bootstrap is needed). `fhe.rs`'s `default_parameters_128` yields
/// 128-bit sets at degrees 1024,2048,4096,8192,16384; we take the degree-4096
/// set (nth 2): 4096 slots (≥ any tested K), a ~109-bit ciphertext modulus q
/// (noise budget for millions of adds), plaintext modulus ≈ 2^plaintext_nbits.
pub fn pick_params(plaintext_nbits: usize) -> Arc<BfvParameters> {
    BfvParameters::default_parameters_128(plaintext_nbits)
        .expect("128-bit BFV params")
        .nth(2)
        .expect("degree-4096 parameter set")
}

/// The BFV additive fold. Each order is expanded (locally, trader-side) into its
/// K-bucket unary increment vector, packed into ONE SIMD ciphertext, and summed
/// homomorphically into the running demand/supply curve ciphertexts. Returns the
/// decrypted `(demand, supply)` curves (length K) and the timing. The keypair is
/// generated fresh here; in production it is the network/threshold key.
pub fn bfv_fold(
    orders: &[Order],
    k: usize,
    params: &Arc<BfvParameters>,
) -> (Vec<u64>, Vec<u64>, BfvFoldTiming) {
    let mut t = BfvFoldTiming {
        n: orders.len(),
        k,
        degree: params.degree(),
        plaintext_modulus: params.plaintext(),
        ..Default::default()
    };
    assert!(
        k <= params.degree(),
        "K={k} exceeds SIMD slot count {}",
        params.degree()
    );

    // Deterministic rng for the BFV randomness (keygen + encryption). The measured
    // fold cost is independent of the seed; a fixed seed keeps the run reproducible.
    let mut rng = StdRng09::seed_from_u64(0xB_F_74_C0DE);

    let t0 = Instant::now();
    let sk = SecretKey::random(params, &mut rng);
    let pk = PublicKey::new(&sk, &mut rng);
    t.keygen = t0.elapsed();

    // (0) Encrypt each order's packed K-bucket increment as ONE SIMD ciphertext.
    let t0 = Instant::now();
    let mut bid_cts: Vec<Ciphertext> = Vec::new();
    let mut ask_cts: Vec<Ciphertext> = Vec::new();
    for o in orders {
        let inc: Vec<u64> = order_increment(o, k)
            .into_iter()
            .map(|q| q as u64)
            .collect();
        let pt = Plaintext::try_encode(&inc, Encoding::simd(), params).expect("simd encode");
        let ct: Ciphertext = pk.try_encrypt(&pt, &mut rng).expect("encrypt");
        match o.side {
            Side::Bid => bid_cts.push(ct),
            Side::Ask => ask_cts.push(ct),
        }
    }
    t.encrypt = t0.elapsed();

    // (a) THE ADDITIVE FOLD — the carry-free part under test. D = Σ_bids, S =
    //     Σ_asks, each a running sum of packed ciphertexts. Every `+=` folds all K
    //     buckets at once via native modular poly-add: no carry, no PBS. This is
    //     N−2 ciphertext adds total, vs TFHE's 2·K deferred-carry bucket-sums over
    //     N/2 carry-propagating elements each.
    let t0 = Instant::now();
    let mut d_ct = Ciphertext::zero(params);
    for ct in &bid_cts {
        d_ct += ct;
    }
    let mut s_ct = Ciphertext::zero(params);
    for ct in &ask_cts {
        s_ct += ct;
    }
    t.fold = t0.elapsed();
    t.add_ops = bid_cts.len().saturating_sub(1) + ask_cts.len().saturating_sub(1);

    // (b) Decrypt the two aggregate curve ciphertexts (K slots each). In the
    //     no-viewer deployment the curves are NEVER opened — the crossing runs
    //     homomorphically on TFHE and only p*/V* are threshold-decrypted. Here we
    //     decrypt them ONLY to check the fold against the plaintext reference.
    let t0 = Instant::now();
    let d_pt = sk.try_decrypt(&d_ct).expect("decrypt D");
    let s_pt = sk.try_decrypt(&s_ct).expect("decrypt S");
    let d_full = Vec::<u64>::try_decode(&d_pt, Encoding::simd()).expect("decode D");
    let s_full = Vec::<u64>::try_decode(&s_pt, Encoding::simd()).expect("decode S");
    let demand: Vec<u64> = d_full[..k].to_vec();
    let supply: Vec<u64> = s_full[..k].to_vec();
    t.decrypt = t0.elapsed();

    // (c) CLEAR-DOMAIN crossing (NOT additive, NOT part of the measured cost — the
    //     real crossing stays TFHE, ~10 s O(K)). Recover p*/V* to CHECK the fold,
    //     under the uniform-price rule p* = argmax_p min(D[p],S[p]) (ties to the
    //     lowest p). V*==0 (usize::MAX sentinel) => the book never clears.
    let mut p_star = usize::MAX;
    let mut v_star = 0u32;
    for p in 0..k {
        let v = demand[p].min(supply[p]) as u32;
        if v > v_star {
            v_star = v;
            p_star = p;
        }
    }
    t.p_star = p_star;
    t.v_star = v_star;

    (demand, supply, t)
}

/// The mint-safe quantizer — the deployable floor/ceil rounding proven no-mint in
/// `metatheory/Market/MintSafeQuantization.lean`.
///
/// The additive fold's soundness discipline is NOT the fold's approximation
/// quality (that is COMPLETENESS / parameter sizing) but conservation: the
/// quantized settlement must never MINT the true (rational-valued) totals. The
/// Lean theorem `mint_safe_floor_ceil` (Δ > 0) proves the deployable rule:
///
///   floor the INPUTS  `qin_i  = ⌊vin_i  / Δ⌋`   (under-approximate),
///   ceil  the OUTPUTS  `qout_j = ⌈vout_j / Δ⌉`   (over-approximate),
///
/// then the cheap INTEGER gate `Σ qout ≤ Σ qin` — checked on the exact-integer
/// grid the BFV fold operates over — PROVABLY forbids a mint of the true values:
/// `Σ vout ≤ Σ vin`. The directionality is load-bearing (the Lean file's
/// `wrong_direction_admits_mint` shows flipping it lets a mint pass). The
/// companion `sufficient_surplus_passes_gate` bounds the completeness reserve at
/// `Δ·(n_in + n_out)`: an honest clearing whose true surplus exceeds that is
/// accepted, so Δ is the tunable precision/tolerance knob.
///
/// Values are carried as fixed-point integers (micro-units): `v` denotes `v/DEN`
/// of a unit and Δ is `delta` micro-units, so the ℚ arithmetic of the Lean is
/// reproduced exactly on `i128` with no float. Values are non-negative (market
/// value flows), so floor/ceil are the standard non-negative integer divisions.
pub mod mint_safe {
    /// `⌊v / Δ⌋` for the mint-safe INPUT direction (v ≥ 0, Δ > 0).
    #[inline]
    pub fn floor_div(v: i128, delta: i128) -> i128 {
        assert!(delta > 0 && v >= 0);
        v / delta
    }

    /// `⌈v / Δ⌉` for the mint-safe OUTPUT direction (v ≥ 0, Δ > 0).
    #[inline]
    pub fn ceil_div(v: i128, delta: i128) -> i128 {
        assert!(delta > 0 && v >= 0);
        (v + delta - 1) / delta
    }

    /// The cheap integer gate `Σ ⌈vout/Δ⌉ ≤ Σ ⌊vin/Δ⌋` — floor the inputs, ceil
    /// the outputs, at step Δ. Returns `(gate_passes, sum_qout, sum_qin)`. When it
    /// passes, `mint_safe_floor_ceil` (Lean) certifies `Σ vout ≤ Σ vin` — no mint
    /// of the true rational values within the quantization tolerance.
    pub fn floor_ceil_gate(vin: &[i128], vout: &[i128], delta: i128) -> (bool, i128, i128) {
        let sum_qin: i128 = vin.iter().map(|&v| floor_div(v, delta)).sum();
        let sum_qout: i128 = vout.iter().map(|&v| ceil_div(v, delta)).sum();
        (sum_qout <= sum_qin, sum_qout, sum_qin)
    }

    /// Direct check that the TRUE (rational, i.e. micro-unit) totals do not mint:
    /// `Σ vout ≤ Σ vin`. The gate is a SUFFICIENT cheap witness for this; this is
    /// the ground truth the gate is trusted to imply (via the Lean theorem).
    pub fn true_no_mint(vin: &[i128], vout: &[i128]) -> bool {
        let s_in: i128 = vin.iter().sum();
        let s_out: i128 = vout.iter().sum();
        s_out <= s_in
    }
}
