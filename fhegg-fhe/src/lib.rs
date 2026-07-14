//! fhEgg Stage-2 — NO-VIEWER FHE uniform-price clearing.
//!
//! The honest thesis under test (docs/deos/DREX-NO-VIEWER-SURPASS.md,
//! docs/deos/FHEGG-KERNEL.md): a batch uniform-price call auction is an
//! AGGREGATION, not a matching. Orders are unary price-bucket increments;
//! the aggregate demand/supply curves are a bootstrap-free homomorphic SUM
//! of those increments; and the clearing price is a single monotone crossing
//! that costs O(K) comparisons, independent of N.
//!
//! This module implements BOTH:
//!   * a plaintext reference clear (`reference_clear`) — the ground truth, and
//!   * the FHE clear (`fhe_clear`) — computed entirely on TFHE ciphertexts,
//!     decrypting ONLY the public clearing price p* and aggregate volume V*.
//!
//! The economic model (well-defined, monotone, so plaintext == FHE):
//!   * K public price buckets p = 0..K.
//!   * A BID order (buy) with limit L, qty q: willing to buy at any price
//!     p <= L. Its demand increment adds q to buckets 0..=L. So cumulative
//!     demand D[p] = sum of q over bids with L >= p, non-increasing in p.
//!   * An ASK order (sell) with limit L, qty q: willing to sell at any price
//!     p >= L. Its supply increment adds q to buckets L..K. So cumulative
//!     supply S[p] = sum of q over asks with L <= p, non-decreasing in p.
//!   * Matched volume at p is min(D[p], S[p]); it is maximized at the crossing.
//!     Because D is non-increasing and S non-decreasing, the predicate
//!     c[p] = [D[p] >= S[p]] is a single downward step (1..1,0..0). We define
//!     the clearing price p* = (#{p : D[p] >= S[p]}) - 1 = the largest p at
//!     which demand still meets supply. This makes the crossing a HOMOMORPHIC
//!     SUM of K comparison bits — exactly the "O(K) crossing" of the kernel.
//!
//! The unary-increment encoding is what keeps the limit L SECRET: the trader
//! locally expands the order into a K-vector of {0/q} and encrypts each entry.
//! The server never learns L; it only sums ciphertexts. This is the honest
//! "orders stay encrypted" model (Cryptobazaar unary encoding).

use std::time::{Duration, Instant};
use tfhe::prelude::*;
use tfhe::{ClientKey, FheUint16};

/// The CARRY-FREE ADDITIVE fold (BFV / fhe.rs) — codex Round-3 Q1's Tier-0 speed
/// lever, measured head-to-head against the exact-integer TFHE fold above.
pub mod additive;

pub type Qty = u16;

#[derive(Clone, Copy, Debug)]
pub enum Side {
    Bid,
    Ask,
}

#[derive(Clone, Copy, Debug)]
pub struct Order {
    pub side: Side,
    /// price-bucket limit in 0..K
    pub limit: usize,
    pub qty: Qty,
}

/// The plaintext demand/supply curves and clearing outcome — the reference.
#[derive(Clone, Debug)]
pub struct ClearOutcome {
    pub demand: Vec<u32>,
    pub supply: Vec<u32>,
    /// clearing price bucket p* (largest p with D[p] >= S[p]); None if the
    /// book never clears (no p with D[p] >= S[p]).
    pub p_star: Option<usize>,
    /// matched volume at p*, = min(D[p*], S[p*]).
    pub v_star: u32,
}

/// Unary increment for a single order across the K price buckets.
/// Bid: q on buckets 0..=limit. Ask: q on buckets limit..K.
pub fn order_increment(o: &Order, k: usize) -> Vec<Qty> {
    let mut v = vec![0 as Qty; k];
    match o.side {
        Side::Bid => {
            for p in 0..=o.limit.min(k - 1) {
                v[p] = o.qty;
            }
        }
        Side::Ask => {
            for p in o.limit.min(k - 1)..k {
                v[p] = o.qty;
            }
        }
    }
    v
}

/// Plaintext reference clearing — folds the unary increments and crosses once.
pub fn reference_clear(orders: &[Order], k: usize) -> ClearOutcome {
    let mut demand = vec![0u32; k];
    let mut supply = vec![0u32; k];
    for o in orders {
        let inc = order_increment(o, k);
        match o.side {
            Side::Bid => {
                for p in 0..k {
                    demand[p] += inc[p] as u32;
                }
            }
            Side::Ask => {
                for p in 0..k {
                    supply[p] += inc[p] as u32;
                }
            }
        }
    }
    // p* = largest p with D[p] >= S[p]  ==  (#{p: D>=S}) - 1
    let count = (0..k).filter(|&p| demand[p] >= supply[p]).count();
    let p_star = if count == 0 { None } else { Some(count - 1) };
    let v_star = match p_star {
        Some(p) => demand[p].min(supply[p]),
        None => 0,
    };
    ClearOutcome {
        demand,
        supply,
        p_star,
        v_star,
    }
}

/// Per-phase timing + op counts from one FHE clear (the honest envelope).
#[derive(Clone, Debug, Default)]
pub struct FheTiming {
    pub n: usize,
    pub k: usize,
    /// wall time to encrypt all N unary order vectors (N*K ciphertexts).
    pub encrypt: Duration,
    /// wall time for the aggregation fold (bootstrap-free homomorphic adds).
    pub aggregate: Duration,
    /// number of homomorphic ADD ops in the aggregation.
    pub add_ops: usize,
    /// wall time for the crossing (the K homomorphic comparisons + fold).
    pub crossing: Duration,
    /// number of homomorphic GE (comparison) ops in the crossing.
    pub ge_ops: usize,
    /// wall time to threshold/decrypt ONLY the public result (p*, V*).
    pub decrypt_result: Duration,
    /// the decrypted public clearing price bucket (as recovered under FHE).
    pub p_star: usize,
    pub v_star: u32,
}

/// The NO-VIEWER FHE clear. `ck` is used ONLY to (a) encrypt inputs as the
/// traders would locally, and (b) decrypt the FINAL public result. The
/// clearing computation itself touches only ciphertexts. In production the
/// input encryption is done by each trader under the network key and the
/// final decrypt is a threshold-FHE committee decrypt of p* alone.
///
/// The server key must already be installed via `set_server_key` on this thread.
pub fn fhe_clear(orders: &[Order], k: usize, ck: &ClientKey) -> FheTiming {
    let mut t = FheTiming {
        n: orders.len(),
        k,
        ..Default::default()
    };

    // (0) Encrypt each order's unary increment. This is the trader-side work;
    //     we time it so the envelope is honest end-to-end. We keep per-order
    //     vectors so the aggregation is a genuine fold of submitted ciphertexts.
    let t0 = Instant::now();
    let mut bid_cts: Vec<Vec<FheUint16>> = Vec::new();
    let mut ask_cts: Vec<Vec<FheUint16>> = Vec::new();
    for o in orders {
        let inc = order_increment(o, k);
        let row: Vec<FheUint16> = inc.iter().map(|&x| FheUint16::encrypt(x, ck)).collect();
        match o.side {
            Side::Bid => bid_cts.push(row),
            Side::Ask => ask_cts.push(row),
        }
    }
    t.encrypt = t0.elapsed();

    // (a) AGGREGATION — the cheap, (near-)bootstrap-free part. Fold the
    //     encrypted increments bucket-wise into the encrypted demand/supply
    //     curves: D[p] = Σ_bids row[p], S[p] = Σ_asks row[p]. We use
    //     `FheUint16::sum`, which is tfhe-rs's `unchecked_sum_ciphertexts_vec_
    //     parallelized`: a parallel tree-reduction with DEFERRED carry
    //     propagation (carries settled once at the end, not per add). This is
    //     the additive primitive the kernel's "aggregation is cheap" thesis
    //     refers to — NOT the sequential carry-propagating `+`, which pays a
    //     full PBS-class carry pass on every single addition.
    let t0 = Instant::now();
    let zero = FheUint16::encrypt(0u16, ck);
    let mut d: Vec<FheUint16> = Vec::with_capacity(k);
    let mut s: Vec<FheUint16> = Vec::with_capacity(k);
    for p in 0..k {
        if bid_cts.is_empty() {
            d.push(zero.clone());
        } else {
            let col: Vec<&FheUint16> = bid_cts.iter().map(|row| &row[p]).collect();
            d.push(FheUint16::sum(&col));
        }
        if ask_cts.is_empty() {
            s.push(zero.clone());
        } else {
            let col: Vec<&FheUint16> = ask_cts.iter().map(|row| &row[p]).collect();
            s.push(FheUint16::sum(&col));
        }
    }
    t.aggregate = t0.elapsed();
    // conceptual add count = (#bids-1 + #asks-1) per bucket
    t.add_ops = (bid_cts.len().saturating_sub(1) + ask_cts.len().saturating_sub(1)) * k;

    // (b) CROSSING — the small comparison part. For each bucket compute the
    //     bit c[p] = [D[p] >= S[p]] (one homomorphic GE each), then p* is the
    //     homomorphic SUM of those bits minus one. min(D,S) at p* is the
    //     matched volume; we recover V* via a homomorphic select on the bits.
    let t0 = Instant::now();
    let mut ge_ops = 0usize;
    let one = FheUint16::encrypt(1u16, ck);
    // c[p] as FheUint16 in {0,1}, via a homomorphic select on the GE bit.
    let mut cbits: Vec<FheUint16> = Vec::with_capacity(k);
    for p in 0..k {
        let bit = d[p].ge(&s[p]).if_then_else(&one, &zero);
        cbits.push(bit);
        ge_ops += 1;
    }
    // count = sum of bits  (deferred-carry parallel sum — the cheap primitive)
    let cbit_refs: Vec<&FheUint16> = cbits.iter().collect();
    let count = FheUint16::sum(&cbit_refs);
    t.crossing = t0.elapsed();
    t.ge_ops = ge_ops;

    // (c) THRESHOLD-DECRYPT ONLY THE RESULT. Decrypt p* = count - 1 and the
    //     matched volume V* = min(D[p*], S[p*]). NOTHING ELSE is decrypted:
    //     the orders, the per-order increments, and the full curves stay sealed.
    let t0 = Instant::now();
    let count_pt: u16 = count.decrypt(ck);
    let p_star = if count_pt == 0 {
        0
    } else {
        (count_pt - 1) as usize
    };
    // For V* we decrypt only the two aggregates at the (now public) index p*.
    // In production the committee decrypts min(D[p*],S[p*]); here we decrypt
    // the two scalars at the public index and take the min in the clear.
    let dstar: u16 = d[p_star.min(k - 1)].decrypt(ck);
    let sstar: u16 = s[p_star.min(k - 1)].decrypt(ck);
    let v_star = (dstar.min(sstar)) as u32;
    t.decrypt_result = t0.elapsed();
    t.p_star = if count_pt == 0 { usize::MAX } else { p_star };
    t.v_star = v_star;

    t
}
