//! **The candidate-set bundle: what the network served, written down so it can be re-judged.**
//!
//! A bundle is a directory holding, per responding peer, the VERBATIM `get_best_tip` v2 reply
//! (`cand-NN.besttip`, binprot `ProofCarryingDataStableV1`), the tip's `Protocol_state.Value`
//! extracted for the Lean decoder (`cand-NN.ps`), and a manifest (`candidates.tsv`).
//!
//! ⚑ **The manifest is a CLAIM the bundle refutes, never an input.** `verify_bundle` re-derives
//! every height and every hash from the bytes and refuses the bundle if a TSV row disagrees, and it
//! re-encodes the tip protocol state and refuses if the `.ps` file is not byte-identical. A bundle
//! whose manifest lied about a height would otherwise be a way to hand the fork-choice driver a
//! number no one checked — which is the shape of the hole this whole direction exists to avoid.
//!
//! ⚑ **This module SELECTS NOTHING.** It writes the set and it re-verifies the set. Which candidate
//! is canonical is Samasika's question, it is decided in Lean (`Dregg2.Bridge.MinaForkChoiceGate`),
//! and it is decided PAIRWISE against a persisted head — `MinaChainSelection.beats_not_transitive`
//! proves `select` has genuine 3-cycles at real Mina constants, so "the best of this set" is not a
//! function of the set. A `max_by` over `candidates.tsv` would be exactly the exploitable fold that
//! `bridge/src/mina_head.rs` refuses to be.

use std::path::{Path, PathBuf};

use mina_p2p_messages::binprot::{BinProtRead, BinProtWrite};
use mina_p2p_messages::list::List;
use mina_p2p_messages::v2;

use crate::chain::{verify_anchor, AnchoredCandidate, BestTipWithProof};

/// The manifest's column header. Any bundle whose first line differs is refused.
pub const TSV_HEADER: &str = "idx\tpeer\ttip_height\ttip_hash\ttip_hash_decimal\troot_height\troot_hash\troot_hash_decimal\tdepth\tanchor";

/// One row of the bundle, after the bytes have been re-judged.
#[derive(Clone, Debug)]
pub struct BundleEntry {
    /// Index within the bundle.
    pub idx: usize,
    /// The peer that served it (libp2p peer id), for attribution only. Never trusted.
    pub peer: String,
    /// The re-derived facts.
    pub anchored: AnchoredCandidate,
}

pub fn besttip_path(dir: &Path, idx: usize) -> PathBuf {
    dir.join(format!("cand-{idx:02}.besttip"))
}

pub fn ps_path(dir: &Path, idx: usize) -> PathBuf {
    dir.join(format!("cand-{idx:02}.ps"))
}

pub fn manifest_path(dir: &Path) -> PathBuf {
    dir.join("candidates.tsv")
}

/// Encode a value's binprot bytes.
pub fn binprot_bytes<T: BinProtWrite>(v: &T) -> Vec<u8> {
    let mut buf = Vec::new();
    v.binprot_write(&mut buf).expect("binprot write");
    buf
}

/// Write one candidate into a bundle directory. The caller has already anchor-verified it —
/// [`write_bundle`] is the only path that calls this and it refuses unanchored candidates before
/// reaching here.
pub fn write_candidate(
    dir: &Path,
    idx: usize,
    tip: &BestTipWithProof,
) -> std::io::Result<(usize, usize)> {
    let full = binprot_bytes(tip);
    let ps = binprot_bytes(&tip.data.header.protocol_state);
    std::fs::write(besttip_path(dir, idx), &full)?;
    std::fs::write(ps_path(dir, idx), &ps)?;
    Ok((full.len(), ps.len()))
}

/// Write the manifest. Rows are the RE-DERIVED values, so a later `verify` compares the bytes
/// against what the bytes said, not against what a peer said.
pub fn write_manifest(dir: &Path, entries: &[BundleEntry]) -> std::io::Result<()> {
    let mut s = String::from(TSV_HEADER);
    s.push('\n');
    for e in entries {
        s.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\tok\n",
            e.idx,
            e.peer,
            e.anchored.tip_height,
            e.anchored.tip_hash,
            e.anchored.tip_hash_decimal,
            e.anchored.root_height,
            e.anchored.root_hash,
            e.anchored.root_hash_decimal,
            e.anchored.depth,
        ));
    }
    std::fs::write(manifest_path(dir), s)
}

/// Read one candidate's verbatim reply back out of a bundle.
pub fn read_candidate(dir: &Path, idx: usize) -> Result<BestTipWithProof, String> {
    let p = besttip_path(dir, idx);
    let bytes = std::fs::read(&p).map_err(|e| format!("{}: {e}", p.display()))?;
    let mut slice = bytes.as_slice();
    BestTipWithProof::binprot_read(&mut slice)
        .map_err(|e| format!("{}: binprot decode failed: {e}", p.display()))
}

/// **Re-judge a whole bundle, offline.** Green or bust: any anchor that does not hold, any manifest
/// row that disagrees with the bytes, and any `.ps` that is not the tip's own re-encoding is an
/// `Err`, never a warning.
pub fn verify_bundle(dir: &Path) -> Result<Vec<BundleEntry>, String> {
    let mpath = manifest_path(dir);
    let text = std::fs::read_to_string(&mpath).map_err(|e| format!("{}: {e}", mpath.display()))?;
    let mut lines = text.lines();
    let header = lines
        .next()
        .ok_or_else(|| format!("{}: empty", mpath.display()))?;
    if header != TSV_HEADER {
        return Err(format!(
            "{}: manifest header is {header:?}, expected {TSV_HEADER:?}",
            mpath.display()
        ));
    }

    let mut out = Vec::new();
    for (lineno, line) in lines.enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() != 10 {
            return Err(format!(
                "{}:{}: {} fields, expected 10",
                mpath.display(),
                lineno + 2,
                f.len()
            ));
        }
        let idx: usize = f[0]
            .parse()
            .map_err(|e| format!("{}:{}: bad idx: {e}", mpath.display(), lineno + 2))?;

        // THE BYTES DECIDE. Decode the verbatim reply and re-run the anchor fold.
        let tip = read_candidate(dir, idx)?;
        let anchored =
            verify_anchor(&tip).map_err(|e| format!("candidate {idx} (peer {}): {e}", f[1]))?;

        // The manifest is a claim; refute it against what was just derived.
        let claimed = [f[2], f[3], f[4], f[5], f[6], f[7], f[8]];
        let derived = [
            anchored.tip_height.to_string(),
            anchored.tip_hash.clone(),
            anchored.tip_hash_decimal.clone(),
            anchored.root_height.to_string(),
            anchored.root_hash.clone(),
            anchored.root_hash_decimal.clone(),
            anchored.depth.to_string(),
        ];
        const FIELD: [&str; 7] = [
            "tip_height",
            "tip_hash",
            "tip_hash_decimal",
            "root_height",
            "root_hash",
            "root_hash_decimal",
            "depth",
        ];
        for k in 0..7 {
            if claimed[k] != derived[k] {
                return Err(format!(
                    "candidate {idx}: the manifest says {}={} but the BYTES say {}",
                    FIELD[k], claimed[k], derived[k]
                ));
            }
        }

        // The `.ps` the Lean decoder will read must be this tip's own protocol state, byte for
        // byte. Otherwise the anchor was checked on one object and the fork choice run on another.
        let ps_file = std::fs::read(ps_path(dir, idx))
            .map_err(|e| format!("{}: {e}", ps_path(dir, idx).display()))?;
        let ps_derived = binprot_bytes(&tip.data.header.protocol_state);
        if ps_file != ps_derived {
            return Err(format!(
                "candidate {idx}: cand-{idx:02}.ps is {} bytes and the tip's own protocol state \
                 re-encodes to {} bytes — the fork-choice input is not the object that was anchored",
                ps_file.len(),
                ps_derived.len()
            ));
        }

        out.push(BundleEntry {
            idx,
            peer: f[1].to_string(),
            anchored,
        });
    }

    if out.is_empty() {
        return Err(format!("{}: no candidates", mpath.display()));
    }
    Ok(out)
}

// ===========================================================================
// The RED path
// ===========================================================================

/// Which check a red leg must die on.
///
/// ⚑ THIS DISTINCTION IS THE ANTI-VACUITY CONTROL, and it exists because the first run of this
/// suite looked stronger than it was: three of five legs were being refused by the cheap
/// height/length arithmetic, which a forger simply would not trip. A leg declared [`Fold`] and
/// caught by a shape check means the POSEIDON FOLD — the only part of this that costs an adversary
/// anything — was never exercised by that leg, and `red_legs` fails the run rather than counting it.
///
/// [`Fold`]: Catcher::Fold
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Catcher {
    /// Must die on the merkle-list fold: every shape check passes and only the Poseidon chain
    /// refuses it. These are the legs that say the anchor is real.
    Fold,
    /// Dies on a shape refusal (heights, list length, emptiness). Cheap, and worth keeping because
    /// they are the cases openmina's own reducer waves through — but they prove nothing about the
    /// hash chain.
    Shape,
}

/// A mutation of a real, anchor-verified candidate that MUST be refused.
pub struct RedLeg {
    /// Short name, printed in the transcript.
    pub name: &'static str,
    /// What a peer would be doing if it sent this.
    pub what: &'static str,
    /// Which refusal this leg must produce. A leg that dies on the wrong check is a FAILURE.
    pub catcher: Catcher,
    /// The mutated object.
    pub mutated: BestTipWithProof,
}

/// **Build the red legs from a REAL candidate.** Each is a forgery a peer can attempt for free
/// against a client that reads only the tip; each must die on the anchor.
///
/// Returns an `Err` if the real candidate is too shallow to distinguish the legs (a chain proof of
/// depth < 2 cannot exhibit a replayed-block forgery), because a red suite that silently skips its
/// legs is the failure mode this repo has a name for.
pub fn red_legs(real: &BestTipWithProof) -> Result<Vec<RedLeg>, String> {
    let (body_hashes, root_block) = &real.proof;
    let hashes: Vec<v2::MinaBaseStateBodyHashStableV1> = body_hashes.iter().cloned().collect();
    if hashes.len() < 2 {
        return Err(format!(
            "the real candidate's chain proof has depth {} — at least 2 is needed to drive the \
             replayed-block leg, and a skipped red leg is not a red leg",
            hashes.len()
        ));
    }
    if hashes[0] == hashes[1] {
        return Err(
            "the first two body hashes of the real chain proof are EQUAL, so the replayed-block \
             mutation would be a no-op and the leg would be vacuous"
                .to_string(),
        );
    }

    let mut legs = Vec::new();

    // R1 — REPLAYED BLOCK. One body hash in the middle of the exhibited chain is swapped for
    // another block's. The peer still serves a chain of the right LENGTH, which is the only thing
    // `select` looks at, and the fold must catch it.
    {
        let mut h = hashes.clone();
        h[1] = h[0].clone();
        let mut m = real.clone();
        m.proof = (h.into_iter().collect::<List<_>>(), root_block.clone());
        legs.push(RedLeg {
            name: "R1 replayed-block",
            what: "one state body hash in the merkle list replaced by another block's",
            catcher: Catcher::Fold,
            mutated: m,
        });
    }

    // R6 — REORDERED CHAIN. The same 290 body hashes, in the reverse order. Length, heights and
    // root are ALL untouched, so every cheap check passes; the exhibited chain is a permutation of
    // a real one and only the Poseidon fold can tell. This is the leg that says the anchor is a
    // hash chain and not an arithmetic identity.
    {
        let mut h = hashes.clone();
        h.reverse();
        let mut m = real.clone();
        m.proof = (h.into_iter().collect::<List<_>>(), root_block.clone());
        legs.push(RedLeg {
            name: "R6 reordered-chain",
            what: "the SAME body hashes in reverse order — every shape check passes",
            catcher: Catcher::Fold,
            mutated: m,
        });
    }

    // R2 — GRAFTED ANCHOR. The root is replaced by the tip's own block: a peer claiming its
    // frontier root is the very block it is serving, i.e. an anchor that anchors nothing.
    {
        let mut m = real.clone();
        m.proof = (body_hashes.clone(), real.data.clone());
        legs.push(RedLeg {
            name: "R2 grafted-anchor",
            what: "the frontier root replaced by the tip block itself",
            catcher: Catcher::Shape,
            mutated: m,
        });
    }

    // R3 — SHORT MERKLE LIST. One element dropped: a chain proof that covers one fewer block than
    // the heights claim.
    {
        let mut h = hashes.clone();
        h.pop();
        let mut m = real.clone();
        m.proof = (h.into_iter().collect::<List<_>>(), root_block.clone());
        legs.push(RedLeg {
            name: "R3 short-list",
            what: "the merkle list truncated by one, so it no longer spans root..tip",
            catcher: Catcher::Shape,
            mutated: m,
        });
    }

    // R4 — THE EMPTY LIST. ⚑ This is openmina's own fail-open
    // (`p2p_callbacks_reducer.rs:568` guards the comparison with `if let Some(..) = hashes.last()`
    // over a list it has already shortened by one, so a 0- or 1-element list is accepted with the
    // anchor NEVER CHECKED). It must be a refusal here.
    {
        let mut m = real.clone();
        m.proof = (List::new(), root_block.clone());
        legs.push(RedLeg {
            name: "R4 empty-list",
            what: "an EMPTY merkle list — openmina's own reducer accepts this with the anchor unchecked",
            catcher: Catcher::Shape,
            mutated: m,
        });
    }

    // R5 — FOREIGN TIP ON A REAL ANCHOR. The tip is replaced by the root block: a genuine, signed,
    // decodable Mina block that simply is not the one this chain proof reaches. This is the
    // losing-fork shape — real bytes, real signatures, wrong chain.
    {
        let mut m = real.clone();
        m.data = root_block.clone();
        legs.push(RedLeg {
            name: "R5 foreign-tip",
            what: "a REAL signed block substituted for the tip, under the untouched chain proof",
            catcher: Catcher::Shape,
            mutated: m,
        });
    }

    Ok(legs)
}

// ===========================================================================
// The COVERAGE MAP
// ===========================================================================

/// One region of the encoded reply, and whether the anchor check binds it.
pub struct Region {
    /// Human name, printed in the transcript.
    pub name: &'static str,
    /// Byte range within the encoded `BestTipWithProof`.
    pub range: std::ops::Range<usize>,
    /// Whether flipping a bit here must be REFUSED.
    pub bound: bool,
}

/// **What the anchor check actually binds, measured rather than asserted.**
///
/// ⚑ THIS EXISTS BECAUSE THE OBJECT IS MOSTLY NOT EVIDENCE. A `get_best_tip` reply is tens of
/// kilobytes, and a reader who is told "the anchor verified" will assume all of it was checked.
/// Mina's state hash is over the PROTOCOL STATE alone, so a merkle-list chain proof cannot bind a
/// block's body or its Pickles proof and does not claim to. The regions below are derived from the
/// binprot encoding itself — not from constants that go stale the moment a block with a different
/// body size arrives, which is exactly how the first version of this map broke.
///
/// binprot writes struct fields in declaration order, so:
/// `data`(= tip block: `header.protocol_state` FIRST, then its proof and body) ‖ `proof.0`(the
/// merkle list) ‖ `proof.1`(= root block, same shape).
pub fn regions(t: &BestTipWithProof) -> Vec<Region> {
    let n_data = binprot_bytes(&t.data).len();
    let n_tip_ps = binprot_bytes(&t.data.header.protocol_state).len();
    let n_list = binprot_bytes(&t.proof.0).len();
    let n_root = binprot_bytes(&t.proof.1).len();
    let n_root_ps = binprot_bytes(&t.proof.1.header.protocol_state).len();
    let list_start = n_data;
    let root_start = n_data + n_list;
    vec![
        Region {
            name: "tip protocol state",
            range: 0..n_tip_ps,
            bound: true,
        },
        Region {
            name: "tip block body + Pickles proof",
            range: n_tip_ps..n_data,
            bound: false,
        },
        Region {
            name: "merkle list (the chain proof)",
            range: list_start..list_start + n_list,
            bound: true,
        },
        Region {
            name: "root protocol state",
            range: root_start..root_start + n_root_ps,
            bound: true,
        },
        Region {
            name: "root block body + Pickles proof",
            range: root_start + n_root_ps..root_start + n_root,
            bound: false,
        },
    ]
}

/// The result of probing one region.
pub struct RegionVerdict {
    /// The region.
    pub name: &'static str,
    /// Its byte range.
    pub range: std::ops::Range<usize>,
    /// Whether it was expected to be bound.
    pub bound: bool,
    /// How many sampled bit-flips were REFUSED.
    pub refused: usize,
    /// How many were sampled.
    pub sampled: usize,
}

/// Flip one bit at `samples` evenly-spaced offsets in each region, re-decode, and re-run the anchor.
///
/// A BOUND region must refuse EVERY sample. An UNBOUND region must accept at least one — an
/// "unbound" claim backed by zero accepted flips is not a measurement, it is a region nobody
/// probed. Returns an `Err` if any region contradicts its declaration.
pub fn probe_coverage(t: &BestTipWithProof, samples: usize) -> Result<Vec<RegionVerdict>, String> {
    let whole = binprot_bytes(t);
    let mut out = Vec::new();
    for r in regions(t) {
        let len = r.range.len();
        if len == 0 {
            return Err(format!(
                "region {:?} is empty — the layout model is wrong",
                r.name
            ));
        }
        let n = samples.min(len);
        let mut refused = 0usize;
        for k in 0..n {
            let off = r.range.start + (len * k) / n;
            let mut bytes = whole.clone();
            bytes[off] ^= 0x01;
            let mut slice = bytes.as_slice();
            let ok = match BestTipWithProof::binprot_read(&mut slice) {
                // A decode failure is a refusal too — the bytes never become a candidate.
                Err(_) => false,
                Ok(m) => verify_anchor(&m).is_ok(),
            };
            if !ok {
                refused += 1;
            }
        }
        if r.bound && refused != n {
            return Err(format!(
                "region {:?} ({}..{}) is declared BOUND but {} of {n} sampled bit-flips were \
                 ACCEPTED — the anchor does not cover what this map says it covers",
                r.name,
                r.range.start,
                r.range.end,
                n - refused
            ));
        }
        if !r.bound && refused == n {
            return Err(format!(
                "region {:?} ({}..{}) is declared UNBOUND but every one of {n} sampled bit-flips \
                 was refused — either the map is stale or the check got stronger; either way this \
                 line is now a false statement about the evidence",
                r.name, r.range.start, r.range.end
            ));
        }
        out.push(RegionVerdict {
            name: r.name,
            range: r.range,
            bound: r.bound,
            refused,
            sampled: n,
        });
    }
    Ok(out)
}
