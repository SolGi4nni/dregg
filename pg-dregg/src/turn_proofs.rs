//! S2 — the node-side whole-chain PROOF PRODUCER (`docs/PG-DREGG.md` §10.2).
//!
//! # Where this sits (the orthogonal soundness half)
//!
//! Tier C has two enforcement halves (`crate::attest` header). The per-row
//! STRUCTURAL chain tooth (`crate::mirror::verify_chain_step`) ships
//! unconditionally and is the realizable per-row half. THIS module is the producer
//! for the other half: the whole-chain IVC PROOF. When the node's finality
//! advances, it folds the newly-finalized turns into ONE recursive proof
//! (`circuit::ivc_turn_chain::prove_turn_chain_recursive` / the `fold_two_turns`
//! accumulator), serializes the verify-sufficient subset
//! ([`crate::attest::SerializedWholeChainProof`], the S1 transport), and writes it
//! — with its window bounds + publics — into the `dregg.turn_proofs` table the
//! range-attest SRF (`dregg_attest_range`) reads.
//!
//! # Why a SEAM, not a direct circuit call (the same discipline as [`crate::drainer::Producer`])
//!
//! `pg-dregg` deliberately does not link `dregg-circuit` in the default / `pgNN`
//! build (it depends only on `dregg-auth`, circuit-free + offline — the property
//! that makes the embeddable layer attractive). So, exactly like the PRODUCE gate
//! is a [`crate::drainer::Producer`] trait (the verified executor plugs in
//! node-side), the FOLD step here is a [`ChainFolder`] trait: the real circuit fold
//! plugs in where the circuit IS linked (the node, or a `tier-c` build), and the
//! postgres-free core proves the producer's OWN job — window-bounds discipline, the
//! `dregg.turn_proofs` row it emits, idempotent advancement, and the serialize →
//! write → (SRF reads) handoff — over a deterministic stand-in.
//!
//! What is FAITHFUL here regardless of which folder runs: the producer only ever
//! emits a row for a window it actually folded (no fabricated coverage), the row's
//! `[lo, hi]` are exactly the folded ordinals, and the bytes it writes are a
//! decodable [`crate::attest::SerializedWholeChainProof`] the SRF round-trips. What
//! the real circuit folder ADDS on top is that those bytes verify against the VK
//! anchor (the SRF's `tier-c` check) — i.e. the proof is SOUND, not merely
//! well-formed. The stand-in produces a well-formed-but-unverifiable transport, so
//! the postgres-free core proves the plumbing; a `tier-c`/node build supplies the
//! real fold whose bytes also verify.

use crate::attest::SerializedWholeChainProof;

// ============================================================================
// The finalized-turn handle the producer folds over.
// ============================================================================

/// One finalized turn, as the producer's queue sees it — the projection of a
/// `dregg.turns` row (or the node's `FinalizedBlock`) the fold needs to advance
/// the chain. The producer reads these in **finalized order** (the node's
/// `tau`/blocklace order); the FOLD seam consumes the underlying circuit artifact.
///
/// The producer itself needs only the ordinal + the chain roots (to bound the
/// window + sanity-check continuity before it asks the folder to prove the window);
/// the heavy per-turn descriptor proof the real fold consumes lives behind the
/// [`ChainFolder`] (node-side / `tier-c`), exactly as the executor lives behind
/// [`crate::drainer::Producer`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedTurnHandle {
    /// The turn ordinal (a `dregg.turns` row; the window the proof attests indexes
    /// by these).
    pub ordinal: u64,
    /// The pre-state root this turn chained onto (the prior turn's `ledger_root`).
    pub prev_root: [u8; 32],
    /// The post-state root this turn produced (the next turn's required `prev_root`).
    pub ledger_root: [u8; 32],
}

// ============================================================================
// The FOLD seam — the circuit's whole-chain recursion fold, as the producer sees it.
// ============================================================================

/// The whole-chain IVC fold, as the producer's PROVE step sees it: given a window
/// of finalized turns in finalized order, fold them into ONE recursive proof and
/// return its [`SerializedWholeChainProof`] transport (the S1 bytes the SRF reads)
/// — or refuse with a reason.
///
/// This is the adoptability seam between the postgres-resident producer machinery
/// (this crate) and the verified circuit fold (the node / a `tier-c` build, which
/// has `dregg-circuit`). It mirrors [`crate::drainer::Producer`] and
/// [`crate::workflow::Projector`]: the producer stays independent of HOW the fold
/// is computed, and the postgres-free core proves the producer's sequencing over a
/// deterministic stand-in ([`StandInFolder`]).
///
/// # Contract
///
/// * `fold` receives the window in finalized order (continuity already checked by
///   the producer: turn `i`'s `ledger_root == turn i+1`'s `prev_root`), and the
///   window's `(lo, hi)` ordinals.
/// * It returns `Ok(transport)` whose carried `genesis_root` is the window's first
///   `prev_root`, `final_root` is the window's last `ledger_root`, and `num_turns`
///   is the window length — or `Err(reason)` if the fold fails (a broken order, a
///   turn proof that does not verify, a recursion-layer failure).
/// * The real circuit folder (`tier-c`/node) calls
///   `circuit::ivc_turn_chain::prove_turn_chain_recursive(&turns)`, then
///   `postcard::to_allocvec(&whole.root.0)` + `…(&whole.binding_proof)` and the
///   `BabyBear → [u8;32]` publics mapping into [`SerializedWholeChainProof::new`].
pub trait ChainFolder {
    /// Fold the window `[lo, hi]` (the `turns` in finalized order) into one
    /// whole-chain proof transport, or refuse it with a reason.
    fn fold(
        &mut self,
        turns: &[FinalizedTurnHandle],
        lo: u64,
        hi: u64,
    ) -> Result<SerializedWholeChainProof, String>;
}

/// The deterministic stand-in [`ChainFolder`] for the postgres-free core — the
/// fold-side twin of [`crate::drainer::FoldProducer`].
///
/// It does NOT run the circuit (this crate has no `dregg-circuit`); instead it
/// produces a WELL-FORMED-BUT-UNVERIFIABLE [`SerializedWholeChainProof`]: real,
/// decodable transport bytes carrying the window's true `(genesis_root, final_root,
/// num_turns)` and deterministic placeholder proof-component blobs. This is enough
/// to prove the producer's OWN job — bound the window, emit the `dregg.turn_proofs`
/// row, advance the watermark, and hand the SRF a decodable transport — `cargo
/// test`-proven without the prover in the build. A real node / `tier-c` build
/// replaces it with the verified fold, whose bytes ALSO verify against the anchor.
#[derive(Clone, Debug, Default)]
pub struct StandInFolder;

impl ChainFolder for StandInFolder {
    fn fold(
        &mut self,
        turns: &[FinalizedTurnHandle],
        lo: u64,
        hi: u64,
    ) -> Result<SerializedWholeChainProof, String> {
        if turns.len() < 2 {
            return Err(format!(
                "a whole-chain fold needs >= 2 turns, the window [{lo}, {hi}] has {}",
                turns.len()
            ));
        }
        let genesis_root = turns.first().unwrap().prev_root;
        let final_root = turns.last().unwrap().ledger_root;
        // A deterministic placeholder digest over the window endpoints (NOT
        // cryptographic — the real fold's `chain_digest` is the in-circuit running
        // hash; the stand-in only needs the transport to be decodable + carry the
        // true window bounds).
        let mut chain_digest = [0u8; 32];
        for (i, b) in chain_digest.iter_mut().enumerate() {
            *b = genesis_root[i] ^ final_root[i] ^ (turns.len() as u8);
        }
        // Non-empty placeholder proof-component blobs so the transport passes the
        // S1 decode hygiene (the stub SRF never decodes them into circuit types).
        Ok(SerializedWholeChainProof::new(
            vec![0x5a; 8],
            vec![0xb1; 8],
            genesis_root,
            final_root,
            chain_digest,
            hi - lo + 1,
        ))
    }
}

// ============================================================================
// The proof row the producer writes into `dregg.turn_proofs`.
// ============================================================================

/// One `dregg.turn_proofs` row — a whole-chain proof attesting the window
/// `[lo, hi]`, the unit the producer writes and the SRF reads. The schema is
/// `dregg.turn_proofs(lo, hi, genesis_root, final_root, proof bytea, vk)`
/// (`docs/PG-DREGG.md` §10.2); this is its in-Rust projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TurnProofRow {
    /// The inclusive lower ordinal the proof attests.
    pub lo: u64,
    /// The inclusive upper ordinal the proof attests.
    pub hi: u64,
    /// The window's genesis (pre-)root (`= prev_root` of `lo`).
    pub genesis_root: [u8; 32],
    /// The window's final (post-)root (`= ledger_root` of `hi`).
    pub final_root: [u8; 32],
    /// The serialized whole-chain proof transport bytes
    /// ([`SerializedWholeChainProof::to_bytes`]) — the `proof bytea` column.
    pub proof: Vec<u8>,
    /// The VK anchor the SRF verifies this proof against (the light client's trust
    /// root; an honest-setup party publishes it). 32 bytes
    /// (`circuit::plonky3_recursion_impl::RecursionVk`).
    pub vk: [u8; 32],
}

impl TurnProofRow {
    /// The number of turns this row attests.
    pub fn num_turns(&self) -> u64 {
        self.hi - self.lo + 1
    }
}

// ============================================================================
// The producer — fold finalized windows into `dregg.turn_proofs` rows.
// ============================================================================

/// Why producing a proof row failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProduceProofError {
    /// The window was empty or too small (< 2 turns — a chain fold needs >= 2).
    WindowTooSmall { lo: u64, hi: u64, count: usize },
    /// The supplied turns are not contiguous / not in finalized order: turn `index`
    /// does not continue the chain (its `prev_root` is not the prior turn's
    /// `ledger_root`, or its ordinal is not the prior + 1). The producer refuses to
    /// fold a window it cannot vouch is the dense finalized prefix.
    NonContiguous {
        index: usize,
        expected_prev_root: [u8; 32],
        found_prev_root: [u8; 32],
    },
    /// The window does not start where the producer last left off (a gap or an
    /// overlap with already-proven turns) — the producer only extends from its
    /// watermark, so a non-monotone window is refused.
    NotFromWatermark { watermark: u64, window_lo: u64 },
    /// The [`ChainFolder`] refused to fold the window (a broken order, a turn proof
    /// that did not verify, a recursion-layer failure).
    FoldFailed { reason: String },
}

impl core::fmt::Display for ProduceProofError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProduceProofError::WindowTooSmall { lo, hi, count } => write!(
                f,
                "window [{lo}, {hi}] has {count} turn(s); a whole-chain fold needs >= 2"
            ),
            ProduceProofError::NonContiguous {
                index,
                expected_prev_root,
                found_prev_root,
            } => write!(
                f,
                "turn at window index {index} is non-contiguous: prev_root {} != prior turn's \
                 ledger_root {}",
                hex(found_prev_root),
                hex(expected_prev_root)
            ),
            ProduceProofError::NotFromWatermark {
                watermark,
                window_lo,
            } => write!(
                f,
                "window starts at {window_lo} but the producer watermark is {watermark} \
                 (the producer only extends from its watermark; a gap/overlap is refused)"
            ),
            ProduceProofError::FoldFailed { reason } => {
                write!(f, "the chain fold refused the window: {reason}")
            }
        }
    }
}

impl std::error::Error for ProduceProofError {}

/// The whole-chain proof producer (`docs/PG-DREGG.md` §10.2, S2). It tails the
/// node's finalized turns in order and, each time finality advances by a foldable
/// window, folds the new turns ([`ChainFolder`]) into ONE proof and yields the
/// [`TurnProofRow`] to write into `dregg.turn_proofs`.
///
/// It maintains a `watermark` — the next ordinal not yet covered by a proof row —
/// so successive windows are dense and non-overlapping (a row attests `[lo, hi]`,
/// the next attests `[hi+1, …]`). The live wiring reads `(lo, hi, …)` of the
/// max-`hi` `dregg.turn_proofs` row to resume the watermark; a fresh store starts
/// at 0.
pub struct TurnProofProducer<F: ChainFolder> {
    /// The fold seam (the verified circuit fold, or the stand-in).
    folder: F,
    /// The next ordinal NOT yet covered by a written proof row — the resume point.
    /// A window must start exactly here (else [`ProduceProofError::NotFromWatermark`]).
    watermark: u64,
    /// The VK anchor every produced row carries (the light client trust root the
    /// SRF verifies against). The honest-setup party configures it; the producer
    /// stamps it onto each row so the SRF reads `(proof, vk)` from one place.
    vk: [u8; 32],
    /// How many proof rows this producer has yielded (observability).
    produced: u64,
}

impl<F: ChainFolder> TurnProofProducer<F> {
    /// A fresh producer at watermark 0 (genesis) with the given fold seam + VK
    /// anchor. `produce` over the first finalized window yields the first
    /// `dregg.turn_proofs` row covering `[0, hi]`.
    pub fn new(folder: F, vk: [u8; 32]) -> Self {
        TurnProofProducer {
            folder,
            watermark: 0,
            vk,
            produced: 0,
        }
    }

    /// Resume the producer from the durable `dregg.turn_proofs` head — the restart
    /// path. The live worker reads the max-`hi` row and passes `hi + 1` here so the
    /// next produced window extends exactly from where the proof store left off.
    pub fn resume_watermark(&mut self, next_uncovered_ordinal: u64) {
        self.watermark = next_uncovered_ordinal;
    }

    /// The next ordinal not yet covered by a produced proof row.
    pub fn watermark(&self) -> u64 {
        self.watermark
    }

    /// How many proof rows this producer has yielded.
    pub fn produced(&self) -> u64 {
        self.produced
    }

    /// Borrow the fold seam (e.g. to inspect a stand-in in a test).
    pub fn folder(&self) -> &F {
        &self.folder
    }

    /// Fold a window of newly-finalized turns into ONE `dregg.turn_proofs` row.
    ///
    /// `turns` must be the dense finalized prefix STARTING at the producer's
    /// watermark, in finalized order. The producer:
    ///   1. checks the window is foldable (>= 2 turns, starts at the watermark);
    ///   2. checks structural continuity (turn `i`'s `ledger_root` == turn `i+1`'s
    ///      `prev_root`, ordinals dense) — it refuses to ask the folder to prove a
    ///      window it cannot itself vouch is contiguous;
    ///   3. asks the [`ChainFolder`] to fold the window into a proof transport;
    ///   4. binds the transport's carried window bounds to the ACTUAL window (the
    ///      folder cannot claim a different `(genesis, final, num_turns)` than the
    ///      window the producer handed it — the anti-fabrication tooth), and
    ///   5. on success advances the watermark to `hi + 1` and yields the row.
    ///
    /// A refusal NEVER advances the watermark (so a failed fold can be retried).
    pub fn produce(
        &mut self,
        turns: &[FinalizedTurnHandle],
    ) -> Result<TurnProofRow, ProduceProofError> {
        if turns.len() < 2 {
            let (lo, hi) = window_bounds(turns);
            return Err(ProduceProofError::WindowTooSmall {
                lo,
                hi,
                count: turns.len(),
            });
        }
        let lo = turns.first().unwrap().ordinal;
        let hi = turns.last().unwrap().ordinal;

        // (1) the window must start exactly at the watermark — dense, non-overlapping.
        if lo != self.watermark {
            return Err(ProduceProofError::NotFromWatermark {
                watermark: self.watermark,
                window_lo: lo,
            });
        }

        // (2) structural continuity: ordinals dense AND roots chain. The producer
        // refuses to ask the folder to prove a window it cannot vouch is contiguous.
        for i in 1..turns.len() {
            let prev = &turns[i - 1];
            let this = &turns[i];
            if this.ordinal != prev.ordinal + 1 || this.prev_root != prev.ledger_root {
                return Err(ProduceProofError::NonContiguous {
                    index: i,
                    expected_prev_root: prev.ledger_root,
                    found_prev_root: this.prev_root,
                });
            }
        }
        let genesis_root = turns.first().unwrap().prev_root;
        let final_root = turns.last().unwrap().ledger_root;

        // (3) fold the window.
        let transport = self
            .folder
            .fold(turns, lo, hi)
            .map_err(|reason| ProduceProofError::FoldFailed { reason })?;

        // (4) ANTI-FABRICATION: the folder's carried bounds must equal the ACTUAL
        // window the producer handed it — a folder cannot widen/relabel coverage.
        let want_turns = hi - lo + 1;
        if transport.num_turns != want_turns
            || transport.genesis_root != genesis_root
            || transport.final_root != final_root
        {
            return Err(ProduceProofError::FoldFailed {
                reason: format!(
                    "fold returned bounds (num_turns={}, genesis={}, final={}) that do not match \
                     the window [{lo}, {hi}] (want num_turns={want_turns}, genesis={}, final={})",
                    transport.num_turns,
                    hex(&transport.genesis_root),
                    hex(&transport.final_root),
                    hex(&genesis_root),
                    hex(&final_root),
                ),
            });
        }

        // (5) advance + yield the row.
        let row = TurnProofRow {
            lo,
            hi,
            genesis_root,
            final_root,
            proof: transport.to_bytes(),
            vk: self.vk,
        };
        self.watermark = hi + 1;
        self.produced += 1;
        Ok(row)
    }
}

/// `(lo, hi)` of a window (`(0, 0)` for an empty window — only used in the
/// too-small error before the real bounds are known).
fn window_bounds(turns: &[FinalizedTurnHandle]) -> (u64, u64) {
    match (turns.first(), turns.last()) {
        (Some(f), Some(l)) => (f.ordinal, l.ordinal),
        _ => (0, 0),
    }
}

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ============================================================================
// Tests — the producer's job over the stand-in fold (the REAL S2 sequencing).
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    const VK: [u8; 32] = [0x77; 32];

    /// A dense finalized window `[lo, hi]` whose roots chain (turn k: prev = root(k),
    /// ledger = root(k+1)), the shape the producer's continuity check accepts.
    fn window(lo: u64, hi: u64) -> Vec<FinalizedTurnHandle> {
        (lo..=hi)
            .map(|o| FinalizedTurnHandle {
                ordinal: o,
                prev_root: root(o),
                ledger_root: root(o + 1),
            })
            .collect()
    }

    fn root(seed: u64) -> [u8; 32] {
        let mut r = [0u8; 32];
        r[..8].copy_from_slice(&seed.to_le_bytes());
        r
    }

    #[test]
    fn produces_a_proof_row_for_a_dense_window() {
        let mut p = TurnProofProducer::new(StandInFolder, VK);
        let row = p.produce(&window(0, 4)).expect("a dense window folds");
        assert_eq!(row.lo, 0);
        assert_eq!(row.hi, 4);
        assert_eq!(row.num_turns(), 5);
        assert_eq!(row.genesis_root, root(0));
        assert_eq!(row.final_root, root(5));
        assert_eq!(row.vk, VK);
        // The proof bytes are a decodable S1 transport carrying the true window.
        let t = SerializedWholeChainProof::from_bytes(&row.proof).expect("transport decodes");
        assert_eq!(t.num_turns, 5);
        assert_eq!(t.genesis_root, root(0));
        assert_eq!(t.final_root, root(5));
        // The watermark advanced past the window.
        assert_eq!(p.watermark(), 5);
        assert_eq!(p.produced(), 1);
    }

    #[test]
    fn successive_windows_are_dense_and_non_overlapping() {
        let mut p = TurnProofProducer::new(StandInFolder, VK);
        let r0 = p.produce(&window(0, 3)).expect("first window");
        assert_eq!((r0.lo, r0.hi), (0, 3));
        assert_eq!(p.watermark(), 4);
        // The next window must start at the watermark (4); it does.
        let r1 = p.produce(&window(4, 9)).expect("second window");
        assert_eq!((r1.lo, r1.hi), (4, 9));
        assert_eq!(p.watermark(), 10);
        // The two proof rows tile the ordinals [0,9] with no gap, no overlap.
        assert_eq!(r0.hi + 1, r1.lo);
    }

    #[test]
    fn a_window_not_at_the_watermark_is_refused() {
        let mut p = TurnProofProducer::new(StandInFolder, VK);
        p.produce(&window(0, 3)).expect("first window");
        // A window that overlaps already-proven turns (starts at 2, not 4) is refused.
        let err = p
            .produce(&window(2, 6))
            .expect_err("an overlapping window is refused");
        assert!(matches!(
            err,
            ProduceProofError::NotFromWatermark {
                watermark: 4,
                window_lo: 2
            }
        ));
        // And a gap (starts at 6, watermark is 4) is refused too.
        let err = p
            .produce(&window(6, 9))
            .expect_err("a gapped window is refused");
        assert!(matches!(
            err,
            ProduceProofError::NotFromWatermark {
                watermark: 4,
                window_lo: 6
            }
        ));
        // Fail-closed: the watermark never moved on a refusal.
        assert_eq!(p.watermark(), 4);
    }

    #[test]
    fn a_too_small_window_is_refused() {
        let mut p = TurnProofProducer::new(StandInFolder, VK);
        // Zero turns.
        let err = p.produce(&[]).expect_err("empty window refused");
        assert!(matches!(
            err,
            ProduceProofError::WindowTooSmall { count: 0, .. }
        ));
        // One turn (a chain fold needs >= 2).
        let one = window(0, 0);
        let err = p.produce(&one).expect_err("single-turn window refused");
        assert!(matches!(
            err,
            ProduceProofError::WindowTooSmall { count: 1, .. }
        ));
        assert_eq!(
            p.watermark(),
            0,
            "a refused fold never advances the watermark"
        );
    }

    #[test]
    fn a_non_contiguous_window_is_refused() {
        let mut p = TurnProofProducer::new(StandInFolder, VK);
        // Build a window whose 3rd turn's prev_root does NOT chain (a reorder/gap in
        // the supplied turns) — the producer refuses to fold it.
        let mut turns = window(0, 4);
        turns[2].prev_root = [0xde; 32]; // breaks turn 1's ledger == turn 2's prev
        let err = p
            .produce(&turns)
            .expect_err("a non-contiguous window is refused");
        assert!(matches!(
            err,
            ProduceProofError::NonContiguous { index: 2, .. }
        ));
        assert_eq!(p.watermark(), 0);
    }

    #[test]
    fn resume_continues_from_the_durable_proof_head() {
        // The proof store already covers [0, 9]; resume the watermark to 10 and the
        // next produced window must start there.
        let mut p = TurnProofProducer::new(StandInFolder, VK);
        p.resume_watermark(10);
        assert_eq!(p.watermark(), 10);
        let row = p.produce(&window(10, 14)).expect("resumed window folds");
        assert_eq!((row.lo, row.hi), (10, 14));
        assert_eq!(p.watermark(), 15);
        // A window that does not start at the resumed watermark is refused.
        let err = p
            .produce(&window(0, 4))
            .expect_err("pre-watermark window refused");
        assert!(matches!(
            err,
            ProduceProofError::NotFromWatermark {
                watermark: 15,
                window_lo: 0
            }
        ));
    }

    /// A FOLDER that lies about the window it folded (claims wider coverage than the
    /// window it was handed) — the producer's anti-fabrication tooth must refuse it,
    /// so a (buggy or malicious) folder cannot smuggle a row attesting more turns
    /// than it proved.
    struct LyingFolder;
    impl ChainFolder for LyingFolder {
        fn fold(
            &mut self,
            turns: &[FinalizedTurnHandle],
            _lo: u64,
            _hi: u64,
        ) -> Result<SerializedWholeChainProof, String> {
            let genesis_root = turns.first().unwrap().prev_root;
            let final_root = turns.last().unwrap().ledger_root;
            // LIE: claim 1000 turns regardless of the real window length.
            Ok(SerializedWholeChainProof::new(
                vec![1],
                vec![1],
                genesis_root,
                final_root,
                [0; 32],
                1000,
            ))
        }
    }

    #[test]
    fn a_folder_overclaiming_coverage_is_refused() {
        let mut p = TurnProofProducer::new(LyingFolder, VK);
        let err = p
            .produce(&window(0, 4))
            .expect_err("a folder claiming wider coverage than the window is refused");
        assert!(matches!(err, ProduceProofError::FoldFailed { .. }));
        let ProduceProofError::FoldFailed { reason } = err else {
            unreachable!()
        };
        assert!(reason.contains("num_turns=1000"), "{reason}");
        assert_eq!(
            p.watermark(),
            0,
            "the fabricated row never advanced the watermark"
        );
    }
}
