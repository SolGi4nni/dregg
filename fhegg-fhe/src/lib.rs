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
//!   * Executed volume at p is V(p) = min(D[p], S[p]). The uniform-price
//!     call-auction rule clears at the price MAXIMIZING executed volume:
//!     p* = argmax_p V(p), ties broken to the LOWEST p, and cleared volume
//!     V* = min(D[p*], S[p*]). This is the textbook opening/closing-auction
//!     rule; it is individually rational (a bid trades at p <= its limit, an
//!     ask at p >= its limit) and, unlike a bare "largest crossing" heuristic
//!     (which mis-clears when the volume peak sits one bucket off the crossing
//!     edge), it always maximizes traded volume. The crossing is a MAX-SELECTION
//!     over the K encrypted volumes — one homomorphic min per bucket then an
//!     O(K) argmax — still O(K) and independent of N.
//!
//! The unary-increment encoding is what keeps the limit L SECRET: the trader
//! locally expands the order into a K-vector of {0/q} and encrypts each entry.
//! The server never learns L; it only sums ciphertexts. This is the honest
//! "orders stay encrypted" model (Cryptobazaar unary encoding).

use std::time::{Duration, Instant};
use tfhe::prelude::*;
use tfhe::{ClientKey, FheUint32};

/// The CARRY-FREE ADDITIVE fold (BFV / fhe.rs) — codex Round-3 Q1's Tier-0 speed
/// lever, measured head-to-head against the exact-integer TFHE fold above.
pub mod additive;

/// The OUTPUT-BOUNDARY MPC crossing (BFV / fhe.rs → additive shares → secret-shared
/// comparison) — codex Round-4 gold: adversarial no-viewer + the dissolved
/// scheme-switch seam. See `docs/deos/OUTPUT-BOUNDARY-MPC.md`.
pub mod mpc;

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
    /// clearing price bucket p* = argmax_p min(D[p], S[p]) (ties to the lowest
    /// p); None if the book never clears (max executable volume is 0).
    pub p_star: Option<usize>,
    /// executed volume at p*, = min(D[p*], S[p*]).
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
    // Uniform-price rule: p* = argmax_p min(D[p], S[p]), ties to the LOWEST p
    // (strict `>` update keeps the first/lowest maximizer). V*==0 => never clears.
    let mut best_p = 0usize;
    let mut best_v = 0u32;
    for p in 0..k {
        let v = demand[p].min(supply[p]);
        if v > best_v {
            best_v = v;
            best_p = p;
        }
    }
    let (p_star, v_star) = if best_v == 0 {
        (None, 0)
    } else {
        (Some(best_p), best_v)
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
    /// wall time for the crossing (K homomorphic min-selects + the K-way argmax).
    pub crossing: Duration,
    /// number of homomorphic comparison ops in the crossing (K mins + K-1 argmax).
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
    //     The aggregates are FheUint32 (not FheUint16): a bucket sum of legal
    //     u16 quantities can exceed 2^16 — e.g. two 32768-lot bids sum to 65536,
    //     which a 16-bit ciphertext would silently wrap to 0. u32 holds it. This
    //     matches `reference_clear`, whose demand/supply accumulate in u32.
    let t0 = Instant::now();
    let mut bid_cts: Vec<Vec<FheUint32>> = Vec::new();
    let mut ask_cts: Vec<Vec<FheUint32>> = Vec::new();
    for o in orders {
        let inc = order_increment(o, k);
        let row: Vec<FheUint32> = inc
            .iter()
            .map(|&x| FheUint32::encrypt(x as u32, ck))
            .collect();
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
    let zero = FheUint32::encrypt(0u32, ck);
    let mut d: Vec<FheUint32> = Vec::with_capacity(k);
    let mut s: Vec<FheUint32> = Vec::with_capacity(k);
    for p in 0..k {
        if bid_cts.is_empty() {
            d.push(zero.clone());
        } else {
            let col: Vec<&FheUint32> = bid_cts.iter().map(|row| &row[p]).collect();
            d.push(FheUint32::sum(&col));
        }
        if ask_cts.is_empty() {
            s.push(zero.clone());
        } else {
            let col: Vec<&FheUint32> = ask_cts.iter().map(|row| &row[p]).collect();
            s.push(FheUint32::sum(&col));
        }
    }
    t.aggregate = t0.elapsed();
    // conceptual add count = (#bids-1 + #asks-1) per bucket
    t.add_ops = (bid_cts.len().saturating_sub(1) + ask_cts.len().saturating_sub(1)) * k;

    // (b) CROSSING — the uniform-price rule: p* = argmax_p min(D[p],S[p]), ties
    //     to the LOWEST p; V* = min(D[p*],S[p*]). First the per-bucket executed
    //     volume v[p] = min(D[p],S[p]) (one homomorphic GE + select each), then a
    //     MAX-SELECTION over the K encrypted volumes (K-1 homomorphic GT + selects)
    //     yielding the encrypted argmax index and its volume. O(K), independent of
    //     N. (The old "sum of [D>=S] bits, minus one" clears at the largest
    //     crossing, which under-clears when the volume peak is one bucket above it.)
    let t0 = Instant::now();
    let mut ge_ops = 0usize;
    // v[p] = min(D[p], S[p]) = if D[p] >= S[p] then S[p] else D[p].
    let mut vol: Vec<FheUint32> = Vec::with_capacity(k);
    for p in 0..k {
        vol.push(d[p].ge(&s[p]).if_then_else(&s[p], &d[p]));
        ge_ops += 1;
    }
    // Oblivious argmax with lowest-p tie-break: scan the K volumes, replacing the
    // running (best_v, best_p) only on a STRICT increase, so ties keep the lower p.
    let mut best_v = vol[0].clone();
    let mut best_p = FheUint32::encrypt(0u32, ck);
    for p in 1..k {
        let greater = vol[p].gt(&best_v);
        best_p = greater.if_then_else(&FheUint32::encrypt(p as u32, ck), &best_p);
        best_v = greater.if_then_else(&vol[p], &best_v);
        ge_ops += 1;
    }
    t.crossing = t0.elapsed();
    t.ge_ops = ge_ops;

    // (c) THRESHOLD-DECRYPT ONLY THE RESULT (p*, V*). Nothing else is decrypted:
    //     the orders, the per-order increments, and the full curves stay sealed.
    //     A V* of 0 means the book never clears (no positive executable volume).
    let t0 = Instant::now();
    let v_star: u32 = best_v.decrypt(ck);
    let p_star_dec: u32 = best_p.decrypt(ck);
    t.decrypt_result = t0.elapsed();
    t.p_star = if v_star == 0 {
        usize::MAX
    } else {
        p_star_dec as usize
    };
    t.v_star = v_star;

    t
}

#[cfg(test)]
mod clearing_tests {
    use super::*;

    /// Build orders whose unary-increment aggregates reproduce the given monotone
    /// curves. Bid(limit=p) carries the adjacent demand drop D[p]-D[p+1] (D[k]=0);
    /// Ask(limit=p) carries the adjacent supply rise S[p]-S[p-1] (S[-1]=0). Only
    /// valid for non-increasing D and non-decreasing S (the encoded curves always
    /// are). Quantities must fit u16 here (the workbook/counter-witness do).
    fn orders_for(demand: &[u32], supply: &[u32]) -> (Vec<Order>, usize) {
        let k = demand.len();
        assert_eq!(k, supply.len());
        let mut orders = Vec::new();
        for p in 0..k {
            let next = if p + 1 < k { demand[p + 1] } else { 0 };
            let q = demand[p] - next; // D non-increasing => >= 0
            if q > 0 {
                orders.push(Order {
                    side: Side::Bid,
                    limit: p,
                    qty: q as Qty,
                });
            }
        }
        for p in 0..k {
            let prev = if p == 0 { 0 } else { supply[p - 1] };
            let q = supply[p] - prev; // S non-decreasing => >= 0
            if q > 0 {
                orders.push(Order {
                    side: Side::Ask,
                    limit: p,
                    qty: q as Qty,
                });
            }
        }
        (orders, k)
    }

    // ---- plaintext reference: the shared rule, on the two named witnesses ----

    #[test]
    fn reference_workbook() {
        // D=(10,10,6), S=(3,8,8) => min=(3,8,6) => p*=1, V*=8.
        let (orders, k) = orders_for(&[10, 10, 6], &[3, 8, 8]);
        let out = reference_clear(&orders, k);
        assert_eq!(out.demand, vec![10, 10, 6]);
        assert_eq!(out.supply, vec![3, 8, 8]);
        assert_eq!(out.p_star, Some(1));
        assert_eq!(out.v_star, 8);
    }

    #[test]
    fn reference_counter_witness() {
        // The witness that BREAKS the old largest-{D>=S} heuristic: D=(10,9),
        // S=(5,20) => min=(5,9) => argmax at p=1 (V*=9); largest-crossing gives p=0.
        let (orders, k) = orders_for(&[10, 9], &[5, 20]);
        let out = reference_clear(&orders, k);
        assert_eq!(out.demand, vec![10, 9]);
        assert_eq!(out.supply, vec![5, 20]);
        assert_eq!(out.p_star, Some(1));
        assert_eq!(out.v_star, 9);
    }

    #[test]
    fn reference_u32_no_overflow() {
        // Two 32768-lot bids and asks in one bucket => aggregate 65536 > 2^16.
        let orders = vec![
            Order {
                side: Side::Bid,
                limit: 0,
                qty: 32768,
            },
            Order {
                side: Side::Bid,
                limit: 0,
                qty: 32768,
            },
            Order {
                side: Side::Ask,
                limit: 0,
                qty: 32768,
            },
            Order {
                side: Side::Ask,
                limit: 0,
                qty: 32768,
            },
        ];
        let out = reference_clear(&orders, 1);
        assert_eq!(out.demand, vec![65536]);
        assert_eq!(out.supply, vec![65536]);
        assert_eq!(out.p_star, Some(0));
        assert_eq!(out.v_star, 65536);
    }
}

#[cfg(test)]
mod fhe_tests {
    use super::*;
    use tfhe::{generate_keys, set_server_key, ConfigBuilder};

    fn setup() -> ClientKey {
        let config = ConfigBuilder::default().build();
        let (ck, sk) = generate_keys(config);
        set_server_key(sk);
        ck
    }

    fn orders_for(demand: &[u32], supply: &[u32]) -> (Vec<Order>, usize) {
        let k = demand.len();
        let mut orders = Vec::new();
        for p in 0..k {
            let next = if p + 1 < k { demand[p + 1] } else { 0 };
            let q = demand[p] - next;
            if q > 0 {
                orders.push(Order {
                    side: Side::Bid,
                    limit: p,
                    qty: q as Qty,
                });
            }
        }
        for p in 0..k {
            let prev = if p == 0 { 0 } else { supply[p - 1] };
            let q = supply[p] - prev;
            if q > 0 {
                orders.push(Order {
                    side: Side::Ask,
                    limit: p,
                    qty: q as Qty,
                });
            }
        }
        (orders, k)
    }

    /// The FHE clear must agree with the plaintext reference on BOTH named
    /// witnesses — the workbook (1,8) and the counter-witness (1,9) that the old
    /// largest-crossing heuristic mis-clears.
    #[test]
    fn fhe_matches_reference_workbook_and_counter() {
        let ck = setup();
        for (d, s, ep, ev) in [
            (vec![10u32, 10, 6], vec![3u32, 8, 8], 1usize, 8u32),
            (vec![10u32, 9], vec![5u32, 20], 1usize, 9u32),
        ] {
            let (orders, k) = orders_for(&d, &s);
            let reference = reference_clear(&orders, k);
            assert_eq!(reference.p_star, Some(ep));
            assert_eq!(reference.v_star, ev);
            let t = fhe_clear(&orders, k, &ck);
            assert_eq!(t.p_star, ep, "fhe p* mismatch on D={d:?} S={s:?}");
            assert_eq!(t.v_star, ev, "fhe V* mismatch on D={d:?} S={s:?}");
        }
    }

    /// The FheUint32 widening: a bucket sum of 65536 (two 32768-lot bids/asks)
    /// must NOT wrap to 0 as it would under the old FheUint16 aggregate.
    #[test]
    fn fhe_no_u16_overflow() {
        let ck = setup();
        let orders = vec![
            Order {
                side: Side::Bid,
                limit: 0,
                qty: 32768,
            },
            Order {
                side: Side::Bid,
                limit: 0,
                qty: 32768,
            },
            Order {
                side: Side::Ask,
                limit: 0,
                qty: 32768,
            },
            Order {
                side: Side::Ask,
                limit: 0,
                qty: 32768,
            },
        ];
        let reference = reference_clear(&orders, 1);
        assert_eq!(reference.v_star, 65536);
        let t = fhe_clear(&orders, 1, &ck);
        assert_eq!(t.p_star, 0);
        assert_eq!(t.v_star, 65536, "FheUint32 aggregate wrapped");
    }
}
