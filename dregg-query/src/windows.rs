//! Windowed whole-log verification: stitch PAGED `GET /api/receipts/index/range`
//! responses into ONE certified whole-log read.
//!
//! [`crate::attested::answer_whole_log`] demands a SINGLE [`AttestedSlice`]
//! covering `[0, len-1]` — fine for small logs, but a real node serves its
//! receipt index in pages. This module verifies a *sequence* of windows as one
//! whole-log read, fail-closed (ported from the operated layer's consumer,
//! the prior operated layer, where the tiling
//! rules were red-teamed against hidden-revocation/truncation attacks):
//!
//! 1. every window's range certificate verifies against the SAME trusted root
//!    (each row's `receipt_hash` is the opened MMR leaf at its dense
//!    `chain_index`);
//! 2. every window pins the same root-derived log length;
//! 3. the windows **tile** `[0, len-1]` exactly — the first starts at 0, each
//!    next starts where the previous ended, the last reaches the head (no gap,
//!    no overlap, no truncated prefix or tail);
//! 4. each window carries exactly one row per certified position (a node that
//!    claims a wide `hi` but ships fewer rows is omitting certified positions —
//!    the hidden-revocation attack — and is rejected regardless of the
//!    range-count arithmetic).
//!
//! An empty `windows` is the empty log (no rows). On success the returned rows
//! are the whole genuine log in order — the same input a single
//! [`Coverage::WholeLog`](crate::attested::Coverage) slice would certify.
//!
//! ## Wiring
//!
//! Wired: `dregg-query/src/lib.rs` declares `pub mod windows;`. The node-side
//! paged source is `GET /api/receipts/index/range` (`node/src/api.rs`). No
//! extra dependencies (`serde_json` is already a dependency).

use crate::client::IndexRangeResponse;
use crate::mmr::{Blake3Mmr, MmrHasher};
use crate::receipt::ReceiptRecord;

/// Verify a windowed whole-log read against `trusted_root` and return the
/// certified receipt rows in log order (see the module docs for the four
/// fail-closed checks).
///
/// `windows` are the raw JSON bodies of consecutive
/// `GET /api/receipts/index/range` responses, in ascending position order.
/// Nothing about that assembly is trusted; this function re-checks everything.
pub fn verify_windows_with<H: MmrHasher>(
    hasher: &H,
    windows: &[String],
    trusted_root: &[u8; 32],
) -> Result<Vec<ReceiptRecord>, String> {
    let mut receipts: Vec<ReceiptRecord> = Vec::new();
    let mut expected_lo = 0u64;
    let mut pinned_len: Option<u64> = None;

    for (i, w) in windows.iter().enumerate() {
        let resp: IndexRangeResponse = serde_json::from_str(w)
            .map_err(|e| format!("window {i}: bad index-range JSON: {e}"))?;
        // Name the root mismatch before the MMR math: a node serving a
        // different log than the anchor pins fails here with both roots in the
        // message.
        let mut slice = resp
            .into_slice()
            .map_err(|e| format!("window {i}: bad hex in certificate: {e}"))?;
        if &slice.cert.root != trusted_root {
            return Err(format!(
                "window {i}: served index root {} != trusted index root {}",
                hex_root(&slice.cert.root),
                hex_root(trusted_root),
            ));
        }
        // Guard the tiling arithmetic BEFORE the MMR math: a certificate whose
        // `hi` is `u64::MAX` overflows `hi + 1` in the range-count check
        // (wrapping to 0 in a release build ⇒ an empty slice "covers" the whole
        // range; panicking under overflow-checks ⇒ a remote DoS). No honest
        // window ever needs a `hi` that cannot be incremented.
        if slice.cert.hi.checked_add(1).is_none() {
            return Err(format!(
                "window {i}: certificate hi {} is not a valid position",
                slice.cert.hi
            ));
        }
        let len = slice
            .verify(hasher, trusted_root)
            .map_err(|e| format!("window {i}: range certificate rejected: {e}"))?;
        match pinned_len {
            None => pinned_len = Some(len),
            Some(l) if l == len => {}
            Some(l) => {
                return Err(format!(
                    "window {i}: root-pinned log length {len} != prior windows' {l}"
                ));
            }
        }
        if slice.cert.lo != expected_lo {
            return Err(format!(
                "window {i}: starts at position {}, expected {} (gap or overlap in the tiling)",
                slice.cert.lo, expected_lo
            ));
        }
        // Bind the certified span to the receipt count the caller can see,
        // rather than trusting `cert.hi` to advance the coverage cursor. A
        // window over a dense log covers exactly one row per position in
        // `[lo, hi∧(len-1)]`; a node that claims a wide `hi` but ships fewer
        // rows is omitting certified positions (the hidden-revocation attack).
        let effective_hi = slice.cert.hi.min(len.saturating_sub(1));
        if effective_hi < slice.cert.lo {
            return Err(format!(
                "window {i}: certificate hi {} precedes lo {} (empty or inverted range)",
                slice.cert.hi, slice.cert.lo
            ));
        }
        let covered = effective_hi - slice.cert.lo + 1;
        if slice.receipts.len() as u64 != covered {
            return Err(format!(
                "window {i}: certificate covers {covered} positions [{}, {effective_hi}] \
                 but carries {} receipts (a node cannot omit certified rows)",
                slice.cert.lo,
                slice.receipts.len()
            ));
        }
        expected_lo = effective_hi + 1;
        receipts.append(&mut slice.receipts);
    }

    // Whole-log coverage: the tiling must reach the root-pinned head. Without
    // this a node could serve a verified but truncated prefix and hide the
    // revocation (or the grant) at the tail.
    if let Some(len) = pinned_len {
        if expected_lo < len {
            return Err(format!(
                "windows cover positions [0, {expected_lo}) of a length-{len} log — \
                 whole-log coverage required"
            ));
        }
    }
    Ok(receipts)
}

/// [`verify_windows_with`] over the crate's deployed [`Blake3Mmr`] hasher.
pub fn verify_windows(
    windows: &[String],
    trusted_root: &[u8; 32],
) -> Result<Vec<ReceiptRecord>, String> {
    verify_windows_with(&Blake3Mmr, windows, trusted_root)
}

/// Decode a 32-byte hex MMR root (the `GET /api/receipts/index/root` wire
/// form) into the trusted-root bytes [`verify_windows`] anchors on.
pub fn decode_root(hex: &str) -> Result<[u8; 32], String> {
    if hex.len() != 64 {
        return Err(format!("MMR root is not 32 hex-encoded bytes: {hex}"));
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
            .map_err(|_| format!("bad MMR root hex: {hex}"))?;
    }
    Ok(out)
}

fn hex_root(root: &[u8; 32]) -> String {
    root.iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mmr::Mmr;

    fn hex32(b: u8) -> String {
        std::iter::repeat_n(format!("{b:02x}"), 32).collect()
    }

    /// A log of `n` receipts; leaf `i` = `[0x10 + i; 32]`.
    fn log(n: usize) -> (Mmr<Blake3Mmr>, Vec<ReceiptRecord>) {
        let mut leaves = Vec::new();
        let mut recs = Vec::new();
        for i in 0..n {
            let leaf = [0x10 + i as u8; 32];
            recs.push(ReceiptRecord {
                chain_index: i as u64,
                receipt_hash: leaf.iter().map(|x| format!("{x:02x}")).collect(),
                height: i as u64 + 1,
                agent: hex32(0x07),
                effects: Vec::new(),
            });
            leaves.push(leaf);
        }
        (Mmr::from_values(Blake3Mmr, leaves), recs)
    }

    /// The certified window JSON for positions `[lo, hi]`.
    fn window(mmr: &Mmr<Blake3Mmr>, recs: &[ReceiptRecord], lo: u64, hi: u64) -> String {
        let (_v, opening) = mmr.open_range(lo, hi);
        serde_json::to_string(&IndexRangeResponse {
            receipts: recs[lo as usize..=hi as usize].to_vec(),
            root: hex_root(&mmr.root()),
            lo,
            hi,
            opening,
        })
        .unwrap()
    }

    #[test]
    fn tiled_windows_verify_and_return_the_whole_log() {
        let (mmr, recs) = log(7);
        let root = mmr.root();
        let windows = vec![
            window(&mmr, &recs, 0, 2),
            window(&mmr, &recs, 3, 4),
            window(&mmr, &recs, 5, 6),
        ];
        let out = verify_windows(&windows, &root).expect("a tiled whole-log read verifies");
        assert_eq!(out.len(), 7);
        for (i, r) in out.iter().enumerate() {
            assert_eq!(r.chain_index, i as u64, "rows come back in log order");
        }
    }

    #[test]
    fn a_single_whole_window_verifies() {
        let (mmr, recs) = log(4);
        let root = mmr.root();
        let out = verify_windows(&[window(&mmr, &recs, 0, 3)], &root).unwrap();
        assert_eq!(out.len(), 4);
    }

    #[test]
    fn empty_windows_is_the_empty_log() {
        let (mmr, _recs) = log(0);
        assert_eq!(verify_windows(&[], &mmr.root()).unwrap(), Vec::new());
    }

    #[test]
    fn a_truncated_tail_is_rejected() {
        // Serving a verified PREFIX and hiding the tail (where a revocation
        // could live) must fail the whole-log coverage check.
        let (mmr, recs) = log(6);
        let root = mmr.root();
        let windows = vec![window(&mmr, &recs, 0, 2), window(&mmr, &recs, 3, 4)];
        let err = verify_windows(&windows, &root).unwrap_err();
        assert!(err.contains("whole-log coverage required"), "{err}");
    }

    #[test]
    fn a_gap_in_the_tiling_is_rejected() {
        let (mmr, recs) = log(6);
        let root = mmr.root();
        let windows = vec![window(&mmr, &recs, 0, 1), window(&mmr, &recs, 3, 5)];
        let err = verify_windows(&windows, &root).unwrap_err();
        assert!(err.contains("gap or overlap"), "{err}");
    }

    #[test]
    fn an_overlap_in_the_tiling_is_rejected() {
        let (mmr, recs) = log(6);
        let root = mmr.root();
        let windows = vec![window(&mmr, &recs, 0, 3), window(&mmr, &recs, 2, 5)];
        let err = verify_windows(&windows, &root).unwrap_err();
        assert!(err.contains("gap or overlap"), "{err}");
    }

    #[test]
    fn a_window_from_a_different_log_is_rejected() {
        let (mmr, recs) = log(4);
        let (other, other_recs) = log(5);
        let windows = vec![window(&other, &other_recs, 0, 4)];
        // Anchored on the FIRST log's root: the foreign window's served root
        // mismatch is named before any MMR math.
        let err = verify_windows(&windows, &mmr.root()).unwrap_err();
        assert!(err.contains("!= trusted index root"), "{err}");
        let _ = recs;
    }

    #[test]
    fn omitted_certified_rows_are_rejected() {
        // A node claims positions [0, 3] but ships only 3 rows — omitting a
        // certified position (the hidden-revocation attack).
        let (mmr, recs) = log(4);
        let root = mmr.root();
        let (_v, opening) = mmr.open_range(0, 3);
        let w = serde_json::to_string(&IndexRangeResponse {
            receipts: recs[0..3].to_vec(), // one row short
            root: hex_root(&root),
            lo: 0,
            hi: 3,
            opening,
        })
        .unwrap();
        assert!(verify_windows(&[w], &root).is_err());
    }

    #[test]
    fn a_tampered_row_is_rejected() {
        let (mmr, mut recs) = log(3);
        let root = mmr.root();
        // Forge row 1's receipt hash: the opened MMR leaf no longer matches.
        recs[1].receipt_hash = hex32(0xEE);
        let err = verify_windows(&[window(&mmr, &recs, 0, 2)], &root).unwrap_err();
        assert!(err.contains("rejected"), "{err}");
    }

    #[test]
    fn a_u64_max_hi_is_rejected_not_overflowed() {
        let (mmr, recs) = log(2);
        let root = mmr.root();
        let (_v, opening) = mmr.open_range(0, 1);
        let w = serde_json::to_string(&IndexRangeResponse {
            receipts: recs.clone(),
            root: hex_root(&root),
            lo: 0,
            hi: u64::MAX,
            opening,
        })
        .unwrap();
        let err = verify_windows(&[w], &root).unwrap_err();
        assert!(err.contains("not a valid position"), "{err}");
    }

    #[test]
    fn decode_root_roundtrips_and_rejects_garbage() {
        let (mmr, _recs) = log(3);
        let root = mmr.root();
        assert_eq!(decode_root(&hex_root(&root)).unwrap(), root);
        assert!(decode_root("abc").is_err());
        assert!(decode_root(&"zz".repeat(32)).is_err());
    }
}
