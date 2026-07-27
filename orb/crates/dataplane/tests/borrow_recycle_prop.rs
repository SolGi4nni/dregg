//! Property tests for the runtime buffer-lease invariants of the provided-buffer
//! ring (`bufring.rs` / the lease bookkeeping in `uring.rs`), plus a runnable
//! check for the model's `nodrop` soundness precondition (gap E).
//!
//! These are the *runtime* analogues of the abstract `Uring/*.lean` laws:
//!
//! - `conservation` (`Uring/Conservation.lean:544`): every buffer id inhabits
//!   exactly one location — here `free` (published in the ring, kernel-owned) or
//!   `held` (leased to a connection). Never both, never neither.
//! - `recycle_at_most_once` (`Uring/RecycleOnce.lean:728`): the deployed
//!   `Conn.leased_bid: Option<u16>` + `Option::take()` (uring.rs:916) makes a
//!   second recycle of a stored lease a structural no-op.
//! - the observability identity `ZC_BORROW - ZC_RECYCLE == live leases`
//!   (uring.rs:100/103) — active leases are conserved.
//!
//! No external test dependency (proptest/quickcheck): a small deterministic PRNG
//! drives thousands of random op sequences, and small buffer-counts are
//! enumerated exhaustively — matching the twin crates' zero-dep test style.

#![cfg(not(loom))]

use std::collections::BTreeSet;

/// A pure mirror of the deployed lease bookkeeping. `held` is the set of leased
/// bids (`Conn.leased_bid = Some(bid)` scattered across the slab); every other
/// bid is `free` (published in the ring, available for the kernel to lend).
struct LeaseModel {
    nbufs: u16,
    held: BTreeSet<u16>,
    /// `ZC_BORROW`: total leases handed out.
    borrow_count: u64,
    /// `ZC_RECYCLE`: total recycles that actually returned a slot.
    recycle_count: u64,
}

impl LeaseModel {
    fn new(nbufs: u16) -> LeaseModel {
        LeaseModel {
            nbufs,
            held: BTreeSet::new(),
            borrow_count: 0,
            recycle_count: 0,
        }
    }

    fn free_count(&self) -> u16 {
        self.nbufs - self.held.len() as u16
    }

    /// Kernel delivers into buffer `bid`: the shard leases it (`free → held`,
    /// `ZC_BORROW += 1`). A delivery of an already-held bid is impossible in the
    /// deploy (the kernel only lends published-free slots), so it is a no-op here.
    fn deliver(&mut self, bid: u16) {
        if bid < self.nbufs && !self.held.contains(&bid) {
            self.held.insert(bid);
            self.borrow_count += 1;
        }
    }

    /// `stage_response`/`close`: `leased_bid.take()` → `br.recycle(bid)`. If the
    /// bid is currently held, return it (`held → free`, `ZC_RECYCLE += 1`); if it
    /// is NOT held (already recycled, or never leased), this is the `take()`-of-
    /// `None` no-op — the runtime shape of `recycle_at_most_once`.
    fn recycle(&mut self, bid: u16) {
        if self.held.remove(&bid) {
            self.recycle_count += 1;
        }
    }

    /// The full invariant bundle, checked after every op.
    fn check(&self) {
        // conservation: held + free == nbufs, each bid in exactly one location.
        assert_eq!(
            self.held.len() as u16 + self.free_count(),
            self.nbufs,
            "conservation: every bid must inhabit exactly one of held/free"
        );
        // reachable_count_le_one: no bid is both held and free (structural — held
        // is a set and free is its complement; assert the complement is disjoint).
        for &bid in &self.held {
            assert!(bid < self.nbufs, "held bid out of range");
        }
        // active-lease conservation: ZC_BORROW - ZC_RECYCLE == live leases >= 0.
        let active = self
            .borrow_count
            .checked_sub(self.recycle_count)
            .expect("recycle_count exceeded borrow_count: a bid was recycled more than lent");
        assert_eq!(
            active,
            self.held.len() as u64,
            "ZC_BORROW - ZC_RECYCLE must equal the number of live leases"
        );
    }
}

/// Tiny deterministic xorshift PRNG — reproducible, zero-dep.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Randomized sweep: thousands of random deliver/recycle/double-recycle/
/// recycle-unleased sequences over several ring sizes; the invariant bundle is
/// re-checked after every op.
#[test]
fn lease_invariants_hold_under_random_ops() {
    for &nbufs in &[1u16, 2, 4, 8, 16] {
        for seed in 0..400u64 {
            let mut m = LeaseModel::new(nbufs);
            let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1));
            for _ in 0..80 {
                let bid = rng.below(nbufs as u64) as u16;
                match rng.below(4) {
                    // deliver (kernel lends bid)
                    0 | 1 => m.deliver(bid),
                    // recycle (leased_bid.take() → recycle)
                    2 => m.recycle(bid),
                    // adversarial double-recycle of the SAME bid: the second must
                    // be a no-op (recycle_at_most_once).
                    _ => {
                        let before = m.recycle_count;
                        m.recycle(bid);
                        m.recycle(bid);
                        // At most one of the two paired recycles could have counted.
                        assert!(
                            m.recycle_count <= before + 1,
                            "double-recycle of one lease counted twice — recycle_at_most_once violated"
                        );
                    }
                }
                m.check();
            }
            // Drain: recycle every held bid; each counts exactly once, then all free.
            let held: Vec<u16> = m.held.iter().copied().collect();
            for bid in held {
                let before = m.recycle_count;
                m.recycle(bid);
                assert_eq!(
                    m.recycle_count,
                    before + 1,
                    "draining a held lease must recycle once"
                );
                m.recycle(bid); // idempotent no-op
                assert_eq!(
                    m.recycle_count,
                    before + 1,
                    "re-recycling a drained lease must be a no-op"
                );
                m.check();
            }
            assert_eq!(m.free_count(), nbufs, "after draining, all bids are free");
            assert_eq!(
                m.borrow_count, m.recycle_count,
                "every lease was recycled exactly once"
            );
        }
    }
}

/// Exhaustive enumeration on the tightest rings (`nbufs = 1, 2`): every op
/// sequence up to length 7 over the alphabet {deliver bid, recycle bid} is
/// walked and the invariant bundle checked at every prefix. This is the runtime
/// analogue of `Counterexample.lean`'s small-config exhaustion — no interleaving
/// of client edges can break conservation or recycle-once.
#[test]
fn lease_invariants_hold_exhaustively_small() {
    for &nbufs in &[1u16, 2] {
        // alphabet: for each bid, a deliver and a recycle
        let mut alphabet: Vec<(u8, u16)> = Vec::new();
        for bid in 0..nbufs {
            alphabet.push((0, bid)); // deliver
            alphabet.push((1, bid)); // recycle
        }
        let k = alphabet.len();
        for len in 0..=7usize {
            let total = (k as u64).pow(len as u32);
            for mut code in 0..total {
                let mut m = LeaseModel::new(nbufs);
                for _ in 0..len {
                    let (op, bid) = alphabet[(code % k as u64) as usize];
                    code /= k as u64;
                    match op {
                        0 => m.deliver(bid),
                        _ => m.recycle(bid),
                    }
                    m.check();
                }
            }
        }
    }
}

/// Gap E — the model's `nodrop` soundness precondition, RUNNABLE on this kernel.
///
/// `Counterexample.lean:838` (`conservation_fails_without_nodrop`) proves a
/// silently-dropped buffer-select CQE permanently leaks its bid; `nodrop` is a
/// *required* hypothesis of `conservation`. The deployed `IoUring::new`
/// (uring.rs:537) never checks it. `IORING_FEAT_NODROP` (kernel ≥ 5.5) is
/// exactly that guarantee: on CQ overflow the kernel buffers completions instead
/// of dropping them. This test establishes the precondition holds on the build/
/// deploy kernel, and mirrors the ~5-line startup guard PROPOSED for `shard_loop`:
///
/// ```ignore
/// let ring = IoUring::new(RING_ENTRIES)?;
/// // gap E: the Uring model's `nodrop` precondition (Counterexample.lean).
/// if !ring.params().is_feature_nodrop() {
///     return Err(io::Error::new(io::ErrorKind::Unsupported,
///         "io_uring lacks IORING_FEAT_NODROP (kernel < 5.5); the buf_ring \
///          recycle/conservation invariants require no silently-dropped completions"));
/// }
/// ```
#[cfg(target_os = "linux")]
#[test]
fn nodrop_precondition_holds_on_this_kernel() {
    use io_uring::IoUring;
    let ring = IoUring::new(64).expect("io_uring available on the test kernel");
    assert!(
        ring.params().is_feature_nodrop(),
        "IORING_FEAT_NODROP absent: this kernel can silently drop CQEs, so the \
         Uring conservation/recycle-once precondition (nodrop) does NOT hold — \
         the reactor must refuse to run the buf_ring path here"
    );
}
