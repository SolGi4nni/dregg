//! **The candidate set, and the anchor that makes a candidate a CHAIN rather than a tip.**
//!
//! # The gap this closes
//!
//! Until this module, `mina-tip` fetched ONE peer's `get_best_tip` and threw away the half of the
//! response that says anything about a chain. `GetBestTipV2`'s reply is
//! `ProofCarryingDataStableV1<Block, (List<StateBodyHash>, Block)>` — a tip, **and a merkle-list
//! proof anchoring that tip to the root of the serving peer's transition frontier**. `main.rs` read
//! `tip.data.header.protocol_state` and dropped `tip.proof` on the floor.
//!
//! So the light client's evidence was "a peer said this is its tip, and the bytes decode". A peer
//! can say that about bytes describing any height it likes, and `select` prefers the longer
//! `blockchain_length` — the one field a liar controls for free. The anchor is the thing that costs
//! something to forge, and it was not being read.
//!
//! # What an anchor establishes, exactly
//!
//! `verify_anchor` reproduces the fold openmina's own node performs
//! (`crates/node/src/p2p/callbacks/p2p_callbacks_reducer.rs:541-582`), which is Mina's
//! `Merkle_list_verifier.verify`: starting from the ROOT block's state hash, absorb each state
//! **body** hash in order,
//!
//! ```text
//!   h_0     = state_hash(root_block)
//!   h_{i+1} = Poseidon("MinaProtoState")[h_i, body_hashes[i]]
//! ```
//!
//! and require `h_n == state_hash(tip_block)`. Every step is openmina's
//! `v2::StateHash::try_from_hashes`, i.e. Mina's own Poseidon, not a transcription.
//!
//! What that buys: the peer exhibited a chain of `n` blocks it must actually possess, ending at the
//! tip it claims. It cannot inflate `blockchain_length` without producing the body hashes to match,
//! and it cannot graft a foreign tip onto someone else's anchor.
//!
//! ⚠ **AND WHAT IT DOES NOT BUY, said plainly.** The root is the peer's own frontier root, `k = 290`
//! blocks back at most — not genesis. So the anchor is *relative*: "this tip descends from a block
//! this peer also serves". It is not "this tip descends from the block you pinned". Closing THAT
//! requires the root to reach the operator's weak-subjectivity pin, and a public node only holds its
//! ~290-block transition frontier, so it cannot be asked for more in one hop. The bound is a
//! property of what the network serves, not of this code.
//!
//! # ⚑ STRICTER THAN openmina, deliberately, and here is the divergence
//!
//! openmina's reducer guards the comparison with `if let Some(pred_hash) = hashes.last()`
//! (`p2p_callbacks_reducer.rs:568`) over a list it first shortens by one
//! (`.take(len.saturating_sub(1))`). A merkle list of length 0 or 1 therefore produces an EMPTY
//! `hashes`, the `if let` does not fire, and the response is accepted **with the anchor never
//! checked**. That is a fail-open on the exact input a hostile peer controls.
//!
//! [`verify_anchor`] REFUSES an empty list ([`AnchorError::Empty`]) and folds every element rather
//! than dropping the last, so the tip's own body hash is bound too. `--self-test` drives that case
//! (`R4`) and requires a refusal.

use mina_p2p_messages::hash::MinaHash;
use mina_p2p_messages::list::List;
use mina_p2p_messages::rpc::ProofCarryingDataStableV1;
use mina_p2p_messages::v2;

/// The exact wire object `get_best_tip` v2 returns, minus the `Option`.
///
/// Keeping the openmina type rather than a local struct is the point: the bundle this tool writes
/// is the peer's reply verbatim, so an offline re-verification reads what came off the wire and not
/// a re-rendering of it.
pub type BestTipWithProof = ProofCarryingDataStableV1<
    v2::MinaBlockBlockStableV2,
    (
        List<v2::MinaBaseStateBodyHashStableV1>,
        v2::MinaBlockBlockStableV2,
    ),
>;

/// Why a candidate is not an anchored chain. Every variant is a REFUSAL — there is no arm that
/// returns a candidate with the anchor unchecked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnchorError {
    /// The merkle list is empty. ⚑ This is openmina's fail-open (see the module header) and it is a
    /// refusal here: an empty list anchors the tip to nothing at all.
    Empty,
    /// A field element in the tip, the root or the list is not a canonical Pasta element.
    NotCanonical(&'static str),
    /// The fold ran and did not reach the tip. Carries what it reached and what it needed.
    Mismatch {
        /// The hash the fold arrived at, from the root, over the served body hashes.
        reached: String,
        /// The tip's own state hash, derived from the tip's bytes.
        expected: String,
        /// How many body hashes were folded.
        steps: usize,
    },
    /// The root is at or above the tip. A chain proof must go somewhere.
    NotDescending {
        /// The root block's height.
        root: u32,
        /// The tip block's height.
        tip: u32,
    },
    /// The number of body hashes does not match the height difference. A merkle list that skips
    /// blocks proves a chain that is not the one the heights describe.
    LengthDisagreesWithHeights {
        /// `tip - root`.
        span: u32,
        /// `body_hashes.len()`.
        steps: usize,
    },
}

impl std::fmt::Display for AnchorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(
                f,
                "the transition-chain proof is EMPTY — the tip is anchored to nothing (openmina's \
                 own reducer accepts this case; we do not)"
            ),
            Self::NotCanonical(w) => write!(f, "{w} is not a canonical Pasta field element"),
            Self::Mismatch {
                reached,
                expected,
                steps,
            } => write!(
                f,
                "the merkle-list fold over {steps} body hashes reached {reached} but the tip's own \
                 state hash is {expected} — this tip does not descend from the root the peer served"
            ),
            Self::NotDescending { root, tip } => write!(
                f,
                "the chain proof's root is at height {root} and the tip at {tip}: a chain proof \
                 must descend"
            ),
            Self::LengthDisagreesWithHeights { span, steps } => write!(
                f,
                "the heights span {span} blocks but the merkle list has {steps} entries: the proof \
                 does not describe the chain the heights claim"
            ),
        }
    }
}

impl std::error::Error for AnchorError {}

impl AnchorError {
    /// Whether this refusal came from the POSEIDON FOLD or from a cheap shape check.
    ///
    /// Used by `verify-bestchain --self-test` to require that the legs aimed at the fold actually
    /// reach it. A red suite in which every leg dies on an integer comparison has not exercised the
    /// hash chain at all, and would stay green if the fold were deleted.
    pub fn came_from_the_fold(&self) -> bool {
        matches!(self, Self::Mismatch { .. })
    }
}

/// What an anchor-verified candidate is, once the fold has held.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnchoredCandidate {
    /// The tip's height (`blockchain_length`).
    pub tip_height: u32,
    /// The tip's state hash, DERIVED from its bytes (never taken from a peer's word for it).
    pub tip_hash: String,
    /// ⚑ The same hash as a DECIMAL field element — the form the Lean fork-choice gate consumes.
    ///
    /// `MinaForkChoiceGate.decodeSide?` recomputes the state hash from the protocol-state bytes and
    /// refuses the side unless the `eh=`/`ch=` field on the wire equals it *as a decimal `Nat`*. A
    /// bundle that recorded only the Base58Check `3N…` form would hand the next stage a value the
    /// gate structurally refuses — and because `"ERR"` renders as `KeepExisting`, that refusal
    /// would look exactly like "the rule preferred the head". So the decimal is recorded here.
    pub tip_hash_decimal: String,
    /// The frontier root's height.
    pub root_height: u32,
    /// The frontier root's state hash, derived.
    pub root_hash: String,
    /// The root's state hash as a decimal field element.
    pub root_hash_decimal: String,
    /// How many blocks the exhibited chain covers — the peer's visible frontier depth.
    ///
    /// ⚠ Bounded by Mina's `k` (290): a public node serves only its transition frontier, so this
    /// number is what the network will hand a light client in one hop, not a chain to genesis.
    pub depth: usize,
}

/// openmina's own state hash for a protocol state.
fn state_hash(ps: &v2::MinaStateProtocolStateValueStableV2) -> Result<v2::StateHash, AnchorError> {
    let h = MinaHash::try_hash(ps).map_err(|_| AnchorError::NotCanonical("a protocol state"))?;
    Ok(v2::StateHash::from(v2::DataHashLibStateHashStableV1(
        h.into(),
    )))
}

/// The same hash as the DECIMAL field element the Lean gate's wire grammar requires.
fn state_hash_decimal(ps: &v2::MinaStateProtocolStateValueStableV2) -> Result<String, AnchorError> {
    let h = MinaHash::try_hash(ps).map_err(|_| AnchorError::NotCanonical("a protocol state"))?;
    Ok(v2::DataHashLibStateHashStableV1(h.into()).0.to_decimal())
}

fn height(ps: &v2::MinaStateProtocolStateValueStableV2) -> u32 {
    ps.body.consensus_state.blockchain_length.as_u32()
}

/// **The anchor check.** Fold the served body hashes from the root and require the tip.
///
/// This is Mina's `Merkle_list_verifier.verify` on openmina's `StateHash::try_from_hashes`, with
/// the two extra refusals named in the module header (empty list; every element folded rather than
/// the last dropped) and two shape refusals that cost nothing and close obvious slack (the root
/// must be below the tip; the list length must equal the height span).
pub fn verify_anchor(t: &BestTipWithProof) -> Result<AnchoredCandidate, AnchorError> {
    let (body_hashes, root_block) = &t.proof;
    let tip_ps = &t.data.header.protocol_state;
    let root_ps = &root_block.header.protocol_state;

    if body_hashes.is_empty() {
        return Err(AnchorError::Empty);
    }

    let tip_h = height(tip_ps);
    let root_h = height(root_ps);
    if root_h >= tip_h {
        return Err(AnchorError::NotDescending {
            root: root_h,
            tip: tip_h,
        });
    }
    let span = tip_h - root_h;
    if span as usize != body_hashes.len() {
        return Err(AnchorError::LengthDisagreesWithHeights {
            span,
            steps: body_hashes.len(),
        });
    }

    let target = state_hash(tip_ps)?;
    let mut acc = state_hash(root_ps)?;
    for bh in body_hashes.iter() {
        acc = v2::StateHash::try_from_hashes(&acc, bh)
            .map_err(|_| AnchorError::NotCanonical("a state body hash in the merkle list"))?;
    }

    if acc != target {
        return Err(AnchorError::Mismatch {
            reached: acc.to_string(),
            expected: target.to_string(),
            steps: body_hashes.len(),
        });
    }

    Ok(AnchoredCandidate {
        tip_height: tip_h,
        tip_hash: target.to_string(),
        tip_hash_decimal: state_hash_decimal(tip_ps)?,
        root_height: root_h,
        root_hash: state_hash(root_ps)?.to_string(),
        root_hash_decimal: state_hash_decimal(root_ps)?,
        depth: body_hashes.len(),
    })
}
