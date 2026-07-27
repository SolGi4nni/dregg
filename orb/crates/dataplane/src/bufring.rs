//! A provided-buffer ring (`io_uring` buf_ring) for the receive path.
//!
//! This is the running counterpart of the proven `Uring` model (`Uring/Lts.lean`,
//! `Uring/RecycleOnce.lean`). The kernel *lends* a buffer to a receive completion
//! (the model's `deliver fd b more` edge); the shard holds that buffer id across
//! the parse + serve crossing (the model's `held` set); once the request has been
//! consumed the shard *recycles* the id back into the ring (`recycle b`, followed
//! by the tail publish `publish`). The discipline this type enforces — every lent
//! id is recycled exactly once, after its lease is done — is exactly what
//! `Uring.recycle_at_most_once` proves for the abstract ring.
//!
//! ## Layout
//!
//! A mask ring: `entries` buffer records (16 bytes each) laid out in one
//! page-aligned region, where the ring's shared `tail` counter lives in the
//! reserved 2 bytes of record 0 (it never collides with that record's addr/len/bid,
//! which the kernel reads only when it hands record 0 out as a buffer). A second
//! region holds the actual `entries * buf_size` bytes of buffer storage; record `b`
//! points at `bufs + b*buf_size`. Adding a buffer id `b` writes record
//! `tail & mask` and release-stores `tail+1`; the kernel acquire-loads `tail`
//! before selecting a buffer, so the record write is fully visible before the id
//! becomes selectable.
//!
//! The ring is single-producer (this shard) / single-consumer (the kernel); only
//! the owning shard thread ever touches it, so it is `!Send`/`!Sync` by its raw
//! pointers — which is correct: no other thread may recycle.

use std::io;
use std::sync::atomic::{AtomicU16, Ordering};

use io_uring::Submitter;
use io_uring::types::BufRingEntry;

/// One provided-buffer ring bound to a buffer-group id.
pub struct BufRing {
    /// Number of records / buffers (a power of two).
    entries: u16,
    mask: u16,
    /// Size in bytes of each buffer slot.
    buf_size: usize,
    /// Page-aligned ring-records region (`entries * 16` bytes rounded to a page).
    ring: *mut u8,
    ring_len: usize,
    /// Buffer storage region (`entries * buf_size` bytes).
    bufs: *mut u8,
    bufs_len: usize,
    /// Shadow of the ring tail we publish; the authoritative copy is the release
    /// store into the ring's tail field, which the kernel reads.
    tail: u16,
}

impl BufRing {
    /// Allocate a ring of `entries` buffers of `buf_size` bytes each for buffer
    /// group `bgid`, register it with `submitter`, and publish every buffer as
    /// free. `entries` must be a power of two, `<= 32768`.
    pub fn new(
        submitter: &Submitter<'_>,
        bgid: u16,
        entries: u16,
        buf_size: usize,
    ) -> io::Result<BufRing> {
        assert!(entries.is_power_of_two() && entries <= 32768);
        let page = 4096usize;
        let ring_len = {
            let raw = entries as usize * core::mem::size_of::<BufRingEntry>();
            (raw + page - 1) & !(page - 1)
        };
        let bufs_len = entries as usize * buf_size;

        // SAFETY: anonymous private maps of a fixed positive length; the returned
        // pointers are checked against MAP_FAILED. The ring region is page-aligned
        // (mmap guarantees it), as the buf_ring register contract requires.
        let ring = unsafe { mmap_anon(ring_len)? };
        let bufs = match unsafe { mmap_anon(bufs_len) } {
            Ok(p) => p,
            Err(e) => {
                // SAFETY: `ring`/`ring_len` name the mapping we just made.
                unsafe { libc::munmap(ring as *mut libc::c_void, ring_len) };
                return Err(e);
            }
        };

        // SAFETY: `ring`/`ring_len` are a valid page-aligned region that stays
        // mapped until this `BufRing` is dropped (and the ring fd closed), which
        // is what the register contract requires.
        if let Err(e) =
            unsafe { submitter.register_buf_ring_with_flags(ring as u64, entries, bgid, 0) }
        {
            // SAFETY: both maps are ours and no longer used on this error path.
            unsafe {
                libc::munmap(ring as *mut libc::c_void, ring_len);
                libc::munmap(bufs as *mut libc::c_void, bufs_len);
            }
            return Err(e);
        }

        let mut br = BufRing {
            entries,
            mask: entries - 1,
            buf_size,
            ring,
            ring_len,
            bufs,
            bufs_len,
            tail: 0,
        };
        // Publish all buffers as free (the initial fill).
        for bid in 0..entries {
            br.add(bid);
        }
        Ok(br)
    }

    /// A borrowed view of the `len` bytes the kernel wrote into buffer `bid`.
    ///
    /// # Safety
    ///
    /// The caller must not have recycled `bid` since the delivering completion,
    /// and `len` must be the completion's byte count (`<= buf_size`). The returned
    /// slice is valid only until [`recycle`](Self::recycle) of `bid`.
    pub unsafe fn slice(&self, bid: u16, len: usize) -> &[u8] {
        debug_assert!(bid < self.entries && len <= self.buf_size);
        // SAFETY: `bid < entries` bounds the offset within the mapped `bufs`
        // region and `len <= buf_size`, so the range lies inside buffer `bid`.
        unsafe { core::slice::from_raw_parts(self.bufs.add(bid as usize * self.buf_size), len) }
    }

    /// Recycle buffer `bid`: re-publish it as free so the kernel may lend it
    /// again. This is the model's `recycle b` + `publish` fused. Each lent id must
    /// be recycled exactly once per lease (`Uring.recycle_at_most_once`).
    pub fn recycle(&mut self, bid: u16) {
        self.add(bid);
    }

    /// Write buffer `bid` into the ring record at `tail & mask` and release-store
    /// the advanced tail — the equivalent of liburing's `io_uring_buf_ring_add`
    /// followed by `io_uring_buf_ring_advance(1)`.
    fn add(&mut self, bid: u16) {
        let idx = (self.tail & self.mask) as usize;
        // SAFETY: `idx < entries`, so the record is inside the mapped ring region;
        // writing addr/len/bid never touches record 0's reserved tail bytes.
        unsafe {
            let entry = (self.ring as *mut BufRingEntry).add(idx);
            (*entry).set_addr(self.bufs as u64 + bid as u64 * self.buf_size as u64);
            (*entry).set_len(self.buf_size as u32);
            (*entry).set_bid(bid);
        }
        self.tail = self.tail.wrapping_add(1);
        // SAFETY: `BufRingEntry::tail` points at the ring's tail field (record 0's
        // reserved u16); a release store there publishes the record writes above
        // before the kernel's acquire load of the tail can observe the new id.
        unsafe {
            let tail_ptr = BufRingEntry::tail(self.ring as *const BufRingEntry) as *const AtomicU16;
            (*tail_ptr).store(self.tail, Ordering::Release);
        }
    }
}

impl Drop for BufRing {
    fn drop(&mut self) {
        // The ring is unregistered implicitly when the owning `IoUring` fd closes;
        // here we only release the two maps. Shards live for the process, so this
        // runs at shutdown with no live borrows into `bufs`.
        // SAFETY: both regions were mmap'd with these exact lengths and are not
        // aliased after drop.
        unsafe {
            libc::munmap(self.ring as *mut libc::c_void, self.ring_len);
            libc::munmap(self.bufs as *mut libc::c_void, self.bufs_len);
        }
    }
}

/// Map `len` bytes of anonymous, private, read-write memory.
///
/// # Safety
///
/// `len` must be non-zero; the result is checked against `MAP_FAILED` before use.
unsafe fn mmap_anon(len: usize) -> io::Result<*mut u8> {
    // SAFETY: a fixed positive-length anonymous mapping; the result is checked
    // against MAP_FAILED before it is returned.
    let p = unsafe {
        libc::mmap(
            core::ptr::null_mut(),
            len,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_ANONYMOUS | libc::MAP_PRIVATE,
            -1,
            0,
        )
    };
    if p == libc::MAP_FAILED {
        Err(io::Error::last_os_error())
    } else {
        Ok(p as *mut u8)
    }
}
