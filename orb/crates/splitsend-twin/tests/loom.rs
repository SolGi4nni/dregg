//! Zero-copy **SplitSend** writev↔recycle handoff (`DRORB_SPAN=15`,
//! `crates/dataplane/src/uring.rs`): the borrowed request body is sent to the
//! socket as one `writev` gather straight from the still-held buf_ring lease
//! slot — never copied into an output buffer. The lease slot must stay leased
//! until the writev fully settles; a recycle-while-in-flight lets the kernel
//! re-lend the slot to another connection and overwrite the body bytes the
//! writev is still gathering onto this connection's socket — a cross-connection
//! *data disclosure*, the same class as the gap-F borrow↔recycle corner.
//!
//! Unlike gap-F (a cross-*thread* shard↔serve-worker handoff carried by the
//! serve mailbox), the SplitSend recycle runs on the SHARD thread itself, in
//! `on_split_send`, only after it reaps the writev CQE. The concurrent reader
//! is the KERNEL performing the `writev` gather; the completion signal is the
//! writev CQE — a syscall barrier, strictly stronger than the mailbox
//! Release/Acquire the gap-F model captures.
//!
//! Run with:
//! ```text
//! RUSTFLAGS="--cfg loom" cargo test -p splitsend-twin --release --test loom -- --test-threads=1
//! ```
//!
//! # What the real path is (uring.rs, drorb)
//!
//! 1. **shard thread**, `on_recv_br`: the kernel delivered conn A's request
//!    bytes into buffer `bid`; the shard sets `conn.leased_bid = Some(bid)` and
//!    `conn.req_len = n`, and dispatches the serve WITHOUT recycling the slot
//!    (uring.rs:2079).
//! 2. **serve worker**: computes the response HEAD only (no body append); the
//!    body will be spliced from the held slot.
//! 3. **shard thread**, `stage_split_response` (uring.rs:1036): keeps the lease
//!    HELD (`leased_bid` is read, NOT `take`n — uring.rs:1058), stores
//!    `conn.split = Some(SplitSend { body_bid, body_len, .. })`, and arms a
//!    `writev` (`split_send_sqe`, uring.rs:1083) whose second iovec is
//!    `br.slice(body_bid, body_len)` — a raw pointer into the mmap'd buf_ring
//!    slot (uring.rs:1094). The lease is the writev's body source.
//! 4. **kernel**: the `writev` gathers head ‖ body from the slot onto the
//!    socket. While it is in flight the slot bytes MUST NOT change.
//! 5. **shard thread**, `on_split_send` (uring.rs:1140): the writev CQE wakes
//!    it; `sp.sent += res`. On a SHORT write (`sent < head+body`) it re-arms
//!    (`push_split_send`, uring.rs:1157) — another kernel read of the SAME
//!    still-held slot — and does NOT recycle. Only once the whole response has
//!    settled does it `leased_bid.take()` → `br.recycle(bid)` (uring.rs:1160):
//!    a Release store on the buf_ring tail that republishes the slot, after
//!    which the **kernel may re-lend and overwrite it**.
//!
//! The safety claim (uring.rs:1056–1058 / 1092–1093 / 1159, doc-comments,
//! machine-checked nowhere before this model): *the kernel's writev read(s) of
//! the slot happen-before the shard's recycle*, carried by
//! `writev-gather-read → CQE (Release) → shard reap (Acquire) → recycle`, and
//! the recycle happens EXACTLY ONCE even across short-write re-arms
//! (`leased_bid.take()` at the final completion only). This model captures both
//! invariants on the *weakest* ordering that carries them (a Release/Acquire
//! completion count standing in for the CQE syscall barrier), so a green result
//! is conservative.
//!
//! # What THIS loom model covers vs the real deploy (read before trusting)
//!
//! - MODELS: (1) writev-settles-before-recycle — the kernel's gather-read of the
//!   borrowed slot happens-before the recycle, single-segment and across a
//!   short-write re-arm; (2) recycle-once — `leased_bid.take()` yields the lease
//!   exactly once at the FINAL completion, never at a re-arm; and the *strongest
//!   adversary* for the kernel overwrite (the re-lend fires immediately on
//!   recycle, earlier than any real kernel re-lend). The delivery direction
//!   (kernel wrote conn A's request bytes → shard observed the recv CQE → held
//!   the lease) is taken as already happens-before-established (the recv CQE is a
//!   syscall barrier), so it is encoded as an ordered write before the send
//!   begins.
//! - DOES NOT model: the io_uring SQ/CQ rings themselves (see `ring-twin`), the
//!   eventfd coalescing (see `wake-twin`), the cross-thread serve mailbox that
//!   produced the head (see `borrow-recycle-twin`, gap F), the appended/copying
//!   send fallback (`stage_response_appended`, uring.rs:978), the `res <= 0`
//!   error close, or the `bufring.rs` tail Release/Acquire against the *kernel*
//!   (that pairing is the trusted kernel-ABI floor). The writev gather is modeled
//!   as a single logical read per segment, not the kernel's byte-by-byte copy.
//!   This is loom evidence for TWO invariants on a faithful hand-model — NOT a
//!   proof that `uring.rs` is verified.
#![cfg(loom)]

use std::sync::atomic::{AtomicBool as StdBool, AtomicUsize as StdUsize, Ordering as StdOrd};

use loom::cell::UnsafeCell;
use loom::sync::Arc;
use loom::sync::atomic::{AtomicU32, Ordering};
use loom::thread;

/// Conn A's request/echo-body bytes — what the writev is entitled to gather from
/// the leased slot onto conn A's socket.
const GEN_A: u32 = 0xAA;
/// Conn B's bytes — what a re-lend of the recycled slot would overwrite with.
/// The writev gathering this value onto conn A's socket IS the cross-connection
/// disclosure.
const GEN_B: u32 = 0xBB;
/// The leased buffer id (`Conn.leased_bid = Some(BID)`, the writev body source).
const BID: u32 = 7;

/// Shared SplitSend writev↔recycle handoff state.
struct Handoff {
    /// The borrowed buf_ring slot's body bytes: non-atomic memory, exactly like
    /// the mmap'd `bufs` region `br.slice(body_bid, body_len)` points into.
    /// `UnsafeCell` so loom tracks every access and reports a
    /// gather-after-recycle as a concurrent load/store (a causality error) — not
    /// merely as a wrong value.
    buf: UnsafeCell<u32>,
    /// The writev completion count (`on_split_send` reaping the CQE): the kernel
    /// finished gathering the slot for one segment. Release on the kernel side /
    /// Acquire on the shard reap is the *weakest* ordering the CQE already
    /// provides; the real CQE syscall barrier is strictly stronger on top.
    cqe: AtomicU32,
    /// The per-connection lease (`Conn.leased_bid: Option<u16>`). 0 = None,
    /// nonzero = Some(bid); recycle-once = a single swap-to-0, at the final
    /// completion only.
    lease: AtomicU32,
}

/// Count of loom schedules explored, per test, for the report.
static ITERS_SINGLE: StdUsize = StdUsize::new(0);
static ITERS_REARM: StdUsize = StdUsize::new(0);

/// PRIMARY ASSURANCE (single-segment send). The deployed handoff: the shard
/// recycles (and the kernel re-lends + overwrites) only after it reaps the
/// writev CQE. loom explores every interleaving and every C11-permitted read;
/// the invariant asserted is **no gather-after-recycle** — enforced three ways:
///   (a) loom's `UnsafeCell` access tracking: the kernel's gather-read and the
///       shard's overwrite are never concurrent (ordered by the `cqe` handoff);
///   (b) value: the writev always gathers `GEN_A`, never the `GEN_B` re-lend;
///   (c) recycle-once: `lease.take()` yields `Some(BID)` exactly at the recycle.
/// Green over all schedules = the single-segment writev↔recycle handoff is
/// interleaving-safe for this model.
#[test]
fn split_send_recycle_is_interleaving_safe() {
    loom::model(|| {
        ITERS_SINGLE.fetch_add(1, StdOrd::Relaxed);

        let h = Arc::new(Handoff {
            // Delivery direction already established (recv CQE syscall barrier):
            // the kernel wrote conn A's request bytes into the leased slot.
            buf: UnsafeCell::new(GEN_A),
            cqe: AtomicU32::new(0),
            lease: AtomicU32::new(BID),
        });

        // KERNEL (writev gather engine): read the borrowed slot onto the socket,
        // then post the completion CQE.
        let hk = h.clone();
        let kernel = thread::spawn(move || {
            // The writev gather-read of the leased slot's body bytes.
            let gathered = hk.buf.with(|p| unsafe { *p });
            // The writev must gather conn A's OWN bytes onto conn A's socket.
            assert_eq!(
                gathered, GEN_A,
                "DISCLOSURE: writev gathered conn-B bytes onto conn-A's socket \
                 — cross-connection disclosure"
            );
            // `on_split_send` reaps this: post the writev completion.
            hk.cqe.store(1, Ordering::Release);
        });

        // SHARD (`on_split_send`): reap the writev CQE, then (whole response
        // written) recycle the lease exactly once, then — strongest adversary —
        // let the kernel re-lend + overwrite the slot immediately.
        while h.cqe.load(Ordering::Acquire) == 0 {
            loom::thread::yield_now();
        }
        // `sent >= head+body` → `leased_bid.take()` → `br.recycle(bid)`.
        let taken = h.lease.swap(0, Ordering::AcqRel);
        assert_eq!(taken, BID, "recycle-once: the lease is taken exactly here");
        // The recycle republished the slot (bufring `add`: Release store on the
        // ring tail); the kernel re-lends and overwrites with conn B's bytes NOW.
        h.buf.with_mut(|p| unsafe { *p = GEN_B });

        kernel.join().unwrap();
    });

    eprintln!(
        "loom: split_send_recycle_is_interleaving_safe — {} schedules explored, \
         no gather-after-recycle",
        ITERS_SINGLE.load(StdOrd::Relaxed)
    );
}

/// PRIMARY ASSURANCE (short-write re-arm — the SplitSend-specific corner gap-F
/// has no analogue for). `on_split_send` on a short write re-arms the writev
/// (`push_split_send`, uring.rs:1157): a SECOND kernel gather-read of the SAME
/// still-held slot, and it does NOT recycle. Only once the whole response has
/// settled does it recycle — exactly once. This model spawns a kernel that does
/// two gather-reads (a short write then the remainder), each posting its CQE;
/// the shard recycles only after BOTH have settled, and only once.
///
/// The invariant asserted, over every interleaving:
///   (a) `UnsafeCell`: neither gather-read is ever concurrent with the overwrite
///       (both are ordered before the final `cqe==2` the recycle waits on);
///   (b) value: both gather-reads see `GEN_A` — the re-lend never lands mid-send;
///   (c) recycle-once-across-re-arm: `lease.swap` yields `BID` exactly once,
///       reached ONLY at the final completion, never between the two segments.
#[test]
fn split_send_recycle_once_across_rearm() {
    loom::model(|| {
        ITERS_REARM.fetch_add(1, StdOrd::Relaxed);

        let h = Arc::new(Handoff {
            buf: UnsafeCell::new(GEN_A),
            cqe: AtomicU32::new(0),
            lease: AtomicU32::new(BID),
        });

        // KERNEL: two writev segments (a short write, then the remainder). Each
        // gathers the SAME still-held slot and posts its completion CQE.
        let hk = h.clone();
        let kernel = thread::spawn(move || {
            // Segment 1 (the short write): gather the slot.
            let g1 = hk.buf.with(|p| unsafe { *p });
            assert_eq!(
                g1, GEN_A,
                "DISCLOSURE: segment-1 writev gathered conn-B bytes"
            );
            hk.cqe.fetch_add(1, Ordering::Release);
            // Segment 2 (the remainder, re-armed by on_split_send): gather again.
            let g2 = hk.buf.with(|p| unsafe { *p });
            assert_eq!(
                g2, GEN_A,
                "DISCLOSURE: re-armed segment-2 writev gathered conn-B bytes"
            );
            hk.cqe.fetch_add(1, Ordering::Release);
        });

        // SHARD (`on_split_send`): reap segment 1 — `sent < head+body`, so RE-ARM
        // and do NOT recycle. Reap segment 2 — now the whole response is written,
        // so recycle the lease exactly once, then let the kernel re-lend the slot.
        while h.cqe.load(Ordering::Acquire) < 1 {
            loom::thread::yield_now();
        }
        // Re-arm boundary: the lease is STILL held here (no recycle on a short
        // write). `leased_bid` untouched — assert it, matching uring.rs:1160-only.
        assert_eq!(
            h.lease.load(Ordering::Acquire),
            BID,
            "recycle-once: the lease is NOT recycled at the short-write re-arm"
        );
        while h.cqe.load(Ordering::Acquire) < 2 {
            loom::thread::yield_now();
        }
        // Whole response settled: `leased_bid.take()` → `br.recycle(bid)`, once.
        let taken = h.lease.swap(0, Ordering::AcqRel);
        assert_eq!(
            taken, BID,
            "recycle-once: taken exactly once, at the final completion"
        );
        h.buf.with_mut(|p| unsafe { *p = GEN_B });

        kernel.join().unwrap();
    });

    eprintln!(
        "loom: split_send_recycle_once_across_rearm — {} schedules explored, \
         recycle-once across the re-arm, no gather-after-recycle",
        ITERS_REARM.load(StdOrd::Relaxed)
    );
}

/// TEETH. The *counter-model*: a BROKEN `on_split_send` that recycles on the
/// FIRST (short-write) CQE — treating a short write as done, or recycling at the
/// re-arm — instead of waiting for the whole response to settle. The re-armed
/// segment-2 writev is then still in flight (still gathering the slot) when the
/// shard recycles and the kernel re-lends + overwrites; the gather reads conn
/// B's `GEN_B` bytes onto conn A's socket. loom finds that interleaving. This
/// proves (a) the writev-settles-before-recycle / recycle-only-at-final-
/// completion invariant is real and violable, and (b) the green tests above are
/// meaningful: loom WOULD have caught a handoff that recycles a slot a writev is
/// still gathering.
///
/// `buf` is a relaxed atomic here (not `UnsafeCell`) so the disclosed *value* is
/// asserted directly — the same static-flag pattern `ring-twin`'s litmus and the
/// gap-F litmus use — rather than surfacing as a loom causality panic.
#[test]
fn recycle_before_writev_settles_discloses() {
    static DISCLOSURE_REACHED: StdBool = StdBool::new(false);

    loom::model(|| {
        let buf = Arc::new(AtomicU32::new(GEN_A));
        let cqe = Arc::new(AtomicU32::new(0));
        let lease = Arc::new(AtomicU32::new(BID));

        // KERNEL: two writev segments. Segment 2 is the still-in-flight gather
        // whose read races the premature re-lend.
        let (bk, ck) = (buf.clone(), cqe.clone());
        let kernel = thread::spawn(move || {
            let _g1 = bk.load(Ordering::Relaxed); // segment 1 (short write)
            ck.fetch_add(1, Ordering::Release); // its CQE
            bk.load(Ordering::Relaxed) // segment 2 gather — the disclosure-prone read
        });

        // SHARD (BROKEN): recycle after only the FIRST segment's CQE — before the
        // re-armed segment 2 has settled — then re-lend + overwrite the slot.
        while cqe.load(Ordering::Acquire) < 1 {
            loom::thread::yield_now();
        }
        let taken = lease.swap(0, Ordering::AcqRel);
        assert_eq!(taken, BID);
        buf.store(GEN_B, Ordering::Relaxed); // kernel re-lends + overwrites

        let seg2 = kernel.join().unwrap();
        if seg2 == GEN_B {
            // The still-in-flight segment-2 writev gathered a slot the kernel had
            // already re-lent to conn B.
            DISCLOSURE_REACHED.store(true, StdOrd::Relaxed);
        }
    });

    assert!(
        DISCLOSURE_REACHED.load(StdOrd::Relaxed),
        "loom found NO disclosure when recycling before the writev settles — the \
         teeth test is broken; the green safe tests no longer witness that waiting \
         for the final CQE is load-bearing"
    );
    eprintln!(
        "loom: recycle_before_writev_settles_discloses — disclosure REACHED \
         (as expected); waiting for the final writev CQE before recycle is \
         load-bearing"
    );
}
