//! **The per-CHECKPOINT Mina verification loop** — a two-tier light client whose expensive check
//! runs at a cadence the operator chooses, and whose cheap tier is proven unable to move the
//! ratchet.
//!
//! # The insight this module is built on
//!
//! **Mina's Pickles proof is recursive: block N's Step proof verifies block N−1's Wrap proof.**
//! Verifying ONE block's Wrap proof therefore attests the VALIDITY of the whole chain behind it —
//! every transition, every in-circuit density update, every leader-election check, back to genesis.
//!
//! So the client does not need per-block verification at Mina's 180 s cadence. It needs
//! per-CHECKPOINT verification at whatever cadence it picks, and **the cost of a longer cadence is
//! latency and liveness, not safety** — provided nothing a longer cadence leaves unverified can move
//! the finalized point. That proviso is a theorem, not a convention:
//! `MinaCheckpoint.provisional_never_ratchets` says a provisional step is *definitionally* unable to
//! touch the verified head, and `runSteps_finalized_monotone` says the ratchet survives any
//! interleaving of the two tiers under any presentation order.
//!
//! # ⚑ THE CADENCE TABLE — and the number that makes it easy
//!
//! `k = 290` and a slot is 180 s, so **Mina's own finality latency is `290 × 180 s ≈ 14.5 hours`.**
//! The finalized height this client ratchets is `blockchain_length − k`. A checkpoint every `C`
//! blocks delays a given height's finalization by at most `C × 180 s` *on top of that 14.5 hours* —
//! so any cadence well below `k` costs a rounding error against a latency Mina already imposes.
//!
//! | cadence | `C` blocks | added latency | as a fraction of Mina's own 14.5 h | what it costs |
//! |---|---|---|---|---|
//! | **10 min** | 3 | +9 min | **+1.0 %** | essentially nothing; the tightest cadence a compiled Wrap verify supports comfortably |
//! | **1 hour** | 20 | +1 h | **+6.9 %** | the recommended default: a settlement is confirmable within an hour of Mina's own finality |
//! | **1 day** | 480 | +24 h | **+166 %** | ⚑ this one hurts — it more than doubles end-to-end settlement latency, and it stretches the unverified provisional run to 480 blocks |
//!
//! What a longer cadence does **not** cost: safety. What it *does* cost, precisely:
//!
//! 1. **Settlement latency**, as tabulated.
//! 2. **The length of the unverified provisional run.** Between checkpoints the tip moves on cheap
//!    checks alone, and `select` is a TOURNAMENT with genuine 3-cycles at real mainnet constants
//!    (`MinaChainSelection.beats_not_transitive`), so a peer controlling presentation order can walk
//!    the tip around a cycle. That is contained — the ratchet cannot follow it — but a UI or a
//!    speculative execution reading the tip is reading a guess, and a longer cadence means a longer
//!    guess. [`CheckpointCadence::run_cap`] bounds it and past the cap the cheap tier REFUSES.
//! 3. **Detection latency for a fork the cheap checks cannot see.** The cheap tier catches a broken
//!    parent link, a fabricated density window, non-canonical field elements and carried constants
//!    that disagree with the pin. It does not catch an invalid *transaction* or a stolen block
//!    reward — only the Wrap proof does. A longer cadence is a longer window in which the tip could
//!    be on a chain that is well-formed and not valid.
//!
//! # What each tier checks
//!
//! | tier | runs | checks | may move |
//! |---|---|---|---|
//! | **provisional** | every block | binprot decode + canonicality, carried-constants pin, `previous_state_hash` link, the density window **re-derived from the parent** by `MinaSlidingWindow.step`, `select` | the tip only |
//! | **checkpoint** | every `C` blocks | all of the above **plus the Wrap proof's arithmetic** | the verified head, and therefore `finalized` |
//!
//! ⚑ The density row closes `docs/MINA-LIGHT-CLIENT.md` row 7 for the cheap tier. Until now the head
//! consumed a *served* window and bound-checked it; it now recomputes the one value the daemon's own
//! `update_min_window_density` produces from the parent. And the reason a checkpoint does **not**
//! need two consecutive headers for that is the recursion: the density update is inside the
//! blockchain SNARK's transition function, so a verified tip's density is verified all the way back.
//! **The cheap check and the expensive check discharge the same obligation by different means.**
//!
//! # ⚑ WHAT STAYS TRUSTED — at every cadence, and a cadence table must not hide it
//!
//! 1. **The Wrap verifier index.** [`crate::mina_pickles::MinaWrapIndexParams::DEVNET_BLOCKCHAIN`]
//!    and the 56 `VK_INDEX` field elements behind it. The largest single trusted object under the
//!    whole proof story; nothing derives it from the chain and P8/P9 is not started. A wrong VK
//!    makes every checkpoint at every cadence a verification of the wrong claim, silently.
//! 2. **`state_hash` is not re-derived anywhere.** The four hashes on the gate wire are SUPPLIED by
//!    the peer's framing (`docs/MINA-LIGHT-CLIENT.md` row 12). `previous_state_hash` IS decoded and
//!    IS a genuine parent link, so a *run* is checkable; a tip's own identity is not.
//! 3. **Leader election is not checkable by any verifier.** `vrf_output` needs the delegator's
//!    secret scalar and Mina ships no standalone VRF verifier. A client that verifies the Pickles
//!    proof INHERITS the threshold check — which is how Mina itself works, and is not a defect here.
//! 4. **The SRS**, and **the byte source for availability only.**
//!
//! # ⚑ WHAT IS NOT DONE, and no cadence fixes it
//!
//! [`WrapVerdict`] is the checkpoint's expensive conjunct, and the thing that produces it does not
//! exist yet. `Dregg2.Bridge.MinaWrapChallenges` derives a block's own IPA challenges per block from
//! wire data — that part is written — but its `public_comm` argument needs the 40-word public input,
//! **six of whose words are `expand_deferred`'s outputs and exist nowhere in this tree**
//! (`Dregg2.Bridge.MinaWrapPublicInput` is the census). Until they do, [`WrapProver`] has exactly
//! one implementation that can say `Verified` — the pinned-height one — and every other height is
//! [`WrapVerdict::Unavailable`], which this module treats as a refusal. The loop is real and the
//! evidence it demands is not yet producible at arbitrary heights. Said here rather than implied by
//! a passing test.
//!
//! # Fail closed
//!
//! An unavailable gate, an unavailable byte source, an unavailable prover and a refused candidate
//! are four distinct errors and all four leave both tiers where they were. There is no
//! `allow_unverified`, no stale-checkpoint grace period, and no environment variable that opens one.

use crate::mina_head::{
    HeadError, MIN_PROTOCOL_STATE_BYTES, MinaProtocolStateSource, MinaSourceError, hex_of,
};

// ===========================================================================
// Cadence
// ===========================================================================

/// Mina's slot time in seconds. Not a tuning knob: it is the protocol's.
pub const SLOT_SECONDS: u64 = 180;

/// Mina's depth of finality, `k`, in blocks — the `mainnet`/devnet constant the Lean gate pins
/// (`MinaChainSelection.mainnet.k`) and the amount the ratchet subtracts.
pub const FINALITY_DEPTH_BLOCKS: u64 = 290;

/// **How often the expensive tier runs**, in blocks, plus the cap on how far the cheap tier may
/// walk without one.
///
/// ⚑ The cap is not the cadence. A cadence of 20 with a cap of 20 would refuse the moment a single
/// checkpoint is late, which converts every hiccup into a stall; a cap of `2 × cadence` tolerates
/// one missed checkpoint and refuses the second. That is a liveness/safety trade and it is stated
/// rather than buried in a constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointCadence {
    /// Blocks between checkpoints.
    pub blocks: u64,
    /// The greatest provisional run the client will accept before refusing to move the tip at all.
    pub run_cap: u64,
}

impl CheckpointCadence {
    /// ~10 minutes of Mina. Added settlement latency +1.0 % against Mina's own `k`.
    pub const TEN_MINUTES: Self = Self {
        blocks: 3,
        run_cap: 6,
    };

    /// ~1 hour of Mina. **The recommended default**: +6.9 % against Mina's own `k`, and a
    /// provisional run short enough that the tip is never far from a verified point.
    pub const ONE_HOUR: Self = Self {
        blocks: 20,
        run_cap: 40,
    };

    /// ~1 day of Mina. ⚑ Costs +166 % end-to-end settlement latency and leaves a 480-block
    /// unverified provisional run. Offered because it is the cadence a *kernel*-`decide` Wrap
    /// verification could actually sustain, and naming that is more useful than pretending the
    /// compiled path already exists everywhere.
    pub const ONE_DAY: Self = Self {
        blocks: 480,
        run_cap: 960,
    };

    /// Added settlement latency in seconds, worst case: a height finalizes at the next checkpoint.
    pub fn added_latency_seconds(&self) -> u64 {
        self.blocks * SLOT_SECONDS
    }

    /// Mina's own finality latency in seconds — `k` slots. The denominator the added latency should
    /// always be read against, because it is the cost the client pays whatever cadence it picks.
    pub fn mina_own_finality_seconds() -> u64 {
        FINALITY_DEPTH_BLOCKS * SLOT_SECONDS
    }

    /// Added latency as a percentage of Mina's own finality latency, rounded down.
    pub fn added_latency_percent(&self) -> u64 {
        self.added_latency_seconds() * 100 / Self::mina_own_finality_seconds()
    }

    /// The duty cycle a checkpoint of `verify_seconds` implies at this cadence, in parts per
    /// million of wall time. A client whose duty cycle approaches 1_000_000 cannot keep up.
    pub fn duty_cycle_ppm(&self, verify_seconds: u64) -> u64 {
        let window = self.blocks * SLOT_SECONDS;
        if window == 0 {
            return u64::MAX;
        }
        verify_seconds.saturating_mul(1_000_000) / window
    }

    /// Whether a checkpoint costing `verify_seconds` can be sustained at this cadence at all.
    pub fn sustainable(&self, verify_seconds: u64) -> bool {
        verify_seconds < self.blocks * SLOT_SECONDS
    }
}

// ===========================================================================
// The expensive conjunct
// ===========================================================================

/// **What the Wrap arithmetic said about a candidate block.**
///
/// ⚑ [`Self::Unavailable`] is a DIFFERENT answer from [`Self::Refused`] and the distinction is the
/// whole fail-closed posture: "we could not ask" and "we asked and the answer was no" are different
/// facts, and conflating them is exactly how a fail-open gate gets built. Both are refusals here;
/// only one of them is a bug report about the chain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WrapVerdict {
    /// The block's Wrap proof verified.
    Verified,
    /// The Wrap proof was exhibited and did not verify. ⚑ This is a statement about the CHAIN.
    Refused(String),
    /// No verdict could be obtained — today, the ordinary case at every height but the pinned one,
    /// because `expand_deferred`'s six public-input words do not exist in this tree. ⚑ A statement
    /// about US, not about the chain.
    Unavailable(String),
}

impl WrapVerdict {
    /// The bit the Lean gate reads. Only [`Self::Verified`] is true.
    pub fn ok(&self) -> bool {
        matches!(self, Self::Verified)
    }
}

/// The seam that produces a [`WrapVerdict`].
///
/// One method, so an implementation that cannot verify a height has exactly one way to say so.
pub trait WrapProver {
    /// Verify the Wrap proof of the block at `height`, whose `protocol_state` and raw
    /// `proof_bytes` are supplied.
    fn verify_wrap(&self, height: u64, protocol_state: &[u8], proof_bytes: &[u8]) -> WrapVerdict;
}

/// A prover that verifies nothing and says so.
///
/// ⚑ NOT a fallback and not a default: it exists so a client can be *constructed* before the
/// arithmetic lands and be observably unable to finalize anything, rather than being constructed
/// with something that quietly returns `Verified`. Every checkpoint against it is
/// [`CheckpointOutcome::Refused`].
#[derive(Clone, Copy, Debug, Default)]
pub struct UnavailableWrapProver;

impl WrapProver for UnavailableWrapProver {
    fn verify_wrap(&self, height: u64, _protocol_state: &[u8], _proof_bytes: &[u8]) -> WrapVerdict {
        WrapVerdict::Unavailable(format!(
            "no Wrap arithmetic is wired for height {height}: the 40-word public input needs \
             `expand_deferred`'s six words (combined_inner_product, b, zeta_to_srs_length, \
             zeta_to_domain_size, perm, xi) and they exist nowhere in this tree — see \
             Dregg2.Bridge.MinaWrapPublicInput"
        ))
    }
}

// ===========================================================================
// The verified gate seam
// ===========================================================================

/// `dregg_mina_checkpoint_advance`, as a seam so this module is testable without the archive.
///
/// ⚑ The seam is for TESTS, not for a fallback. There is exactly one production implementation and
/// it calls the Lean export; an absent archive is `Err`, and every caller turns that into a refusal.
pub trait MinaCheckpointGate {
    /// Run `dregg_mina_checkpoint_advance`. `Err` means the archive does not export it.
    fn checkpoint_advance(&self, wire: &str) -> Result<String, String>;
}

/// What the gate answered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointAnswer {
    /// The provisional tip moved.
    pub moved: bool,
    /// The verified checkpoint moved — and therefore the ratchet may have risen.
    pub advanced: bool,
    /// The new finalized height. Never below the persisted one.
    pub finalized: u64,
    /// The new provisional run counter.
    pub run: u64,
}

/// Parse the gate's `"mv=B;adv=B;fin=N;rn=N"` answer. Strict: anything else is an error, never a
/// default.
pub fn parse_checkpoint_answer(out: &str) -> Result<CheckpointAnswer, String> {
    let mut parts = out.split(';');
    let mv = parts.next().ok_or("missing mv")?;
    let adv = parts.next().ok_or("missing adv")?;
    let fin = parts.next().ok_or("missing fin")?;
    let rn = parts.next().ok_or("missing rn")?;
    if parts.next().is_some() {
        return Err(format!("trailing fields in {out:?}"));
    }
    let bit = |s: &str, key: &str| -> Result<bool, String> {
        match s.strip_prefix(key) {
            Some("1") => Ok(true),
            Some("0") => Ok(false),
            _ => Err(format!("bad {key} field {s:?}")),
        }
    };
    let num = |s: &str, key: &str| -> Result<u64, String> {
        s.strip_prefix(key)
            .ok_or_else(|| format!("bad {key} field {s:?}"))?
            .parse::<u64>()
            .map_err(|e| format!("bad {key} value: {e}"))
    };
    Ok(CheckpointAnswer {
        moved: bit(mv, "mv=")?,
        advanced: bit(adv, "adv=")?,
        finalized: num(fin, "fin=")?,
        run: num(rn, "rn=")?,
    })
}

/// Build the wire `dregg_mina_checkpoint_advance` reads.
///
/// ⚑ Rust supplies NO verdict bit except `wk` (the Wrap arithmetic, which is arithmetic Rust did not
/// do either — it comes from a prover). The cheap-tier verdict — the parent link, the density
/// re-derivation — is computed inside the gate from the decoded parent and candidate, because a bit
/// Rust computed and handed over would be a carrier for a decision, and the decision lives in Lean.
#[allow(clippy::too_many_arguments)]
pub fn checkpoint_wire(
    checkpoint: bool,
    wrap_ok: bool,
    finalized: u64,
    run: u64,
    run_cap: u64,
    parent_hash: &str,
    tip_hash: &str,
    verified_hash: &str,
    candidate_hash: &str,
    parent: &[u8],
    tip: &[u8],
    verified: &[u8],
    candidate: &[u8],
) -> String {
    format!(
        "md={};wk={};fz={finalized};rn={run};rc={run_cap};ph={parent_hash};th={tip_hash};\
         vh={verified_hash};ch={candidate_hash};p={};t={};v={};c={}",
        if checkpoint { "c" } else { "p" },
        u8::from(wrap_ok),
        hex_of(parent),
        hex_of(tip),
        hex_of(verified),
        hex_of(candidate),
    )
}

// ===========================================================================
// The client
// ===========================================================================

/// A candidate block as the client receives it: the protocol state, its parent's protocol state, the
/// two supplied hashes, and the raw Wrap proof bytes.
///
/// ⚑ The PARENT is required, not optional. It is what the density re-derivation reads, and making it
/// optional would produce a client that silently degrades to a bound check whenever a peer declines
/// to serve one.
#[derive(Clone, Debug)]
pub struct MinaCandidate {
    /// The candidate's `Protocol_state.Value` binprot prefix.
    pub protocol_state: Vec<u8>,
    /// The candidate's state hash as a decimal field element. ⚑ SUPPLIED — see the module header.
    pub state_hash: String,
    /// The candidate's block height, for the prover and for the receipt.
    pub height: u64,
    /// The PARENT's `Protocol_state.Value` binprot prefix.
    pub parent_protocol_state: Vec<u8>,
    /// The parent's state hash as a decimal field element.
    pub parent_state_hash: String,
    /// The candidate's raw `Mina_base.Proof.Stable.V2` bytes.
    pub proof_bytes: Vec<u8>,
}

/// The persisted two-tier head — the Rust mirror of `MinaCheckpoint.CheckpointHead`, carrying bytes
/// where Lean carries decoded structures.
///
/// ⚑ `finalized` is a RATCHET and is not maintained here: it comes back from the gate, where
/// `runSteps_finalized_monotone` proves it never decreases under any interleaving. Rust stores what
/// the gate returned and refuses an answer that lowered it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaCheckpointHead {
    /// The last VERIFIED checkpoint's protocol state.
    pub verified_state: Vec<u8>,
    /// …and its supplied state hash.
    pub verified_hash: String,
    /// The provisional tip's protocol state. Decides nothing.
    pub tip_state: Vec<u8>,
    /// …and its supplied state hash.
    pub tip_hash: String,
    /// The greatest height ever finalized. Never decreases.
    pub finalized: u64,
    /// Blocks accepted onto the tip since the last checkpoint.
    pub run: u64,
}

/// What one offered candidate did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckpointOutcome {
    /// The provisional tip moved; the ratchet did not. The ordinary between-checkpoint result.
    TipAdvanced {
        /// The new provisional run length.
        run: u64,
    },
    /// ⚑ A CHECKPOINT CLOSED: the Wrap arithmetic verified and the verified head moved.
    CheckpointClosed {
        /// The new finalized height.
        finalized: u64,
    },
    /// Nothing moved. The gate said no, or the Wrap verdict was not `Verified`.
    Refused {
        /// Why, at the resolution the caller can act on.
        why: String,
    },
}

/// Why a candidate could not be judged at all — as distinct from being judged and refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckpointError {
    /// No bytes.
    Source(MinaSourceError),
    /// The Lean archive does not export `dregg_mina_checkpoint_advance`. There is NO Rust twin;
    /// neither tier can move.
    VerifiedGateUnavailable(String),
    /// The gate answered something that is not its grammar.
    GateProtocol(String),
    /// A candidate was structurally unusable before any gate saw it.
    Malformed(String),
}

impl std::fmt::Display for CheckpointError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source(e) => write!(f, "{e}"),
            Self::VerifiedGateUnavailable(m) => write!(
                f,
                "the verified Mina checkpoint gate is not in the linked archive ({m}); NEITHER the \
                 tip NOR the finalized point can move, and there is no unverified path that would \
                 let them"
            ),
            Self::GateProtocol(m) => write!(f, "verified gate answered off-grammar: {m}"),
            Self::Malformed(m) => write!(f, "unusable candidate: {m}"),
        }
    }
}

impl std::error::Error for CheckpointError {}

impl From<HeadError> for CheckpointError {
    fn from(e: HeadError) -> Self {
        match e {
            HeadError::Source(s) => Self::Source(s),
            HeadError::VerifiedGateUnavailable(m) => Self::VerifiedGateUnavailable(m),
            HeadError::GateProtocol(m) => Self::GateProtocol(m),
        }
    }
}

/// **The client.** Holds the two-tier head and the cadence; decides nothing itself.
#[derive(Clone, Debug)]
pub struct MinaCheckpointClient {
    /// The persisted head.
    pub head: MinaCheckpointHead,
    /// How often the expensive tier runs.
    pub cadence: CheckpointCadence,
}

impl MinaCheckpointClient {
    /// Start following from a pinned checkpoint. ⚑ This is the weak-subjectivity act and it is the
    /// operator's: a light client cannot bootstrap trust from nothing. Both tiers start at the pin.
    pub fn pinned(
        protocol_state: Vec<u8>,
        state_hash: impl Into<String>,
        finalized: u64,
        cadence: CheckpointCadence,
    ) -> Self {
        let h = state_hash.into();
        Self {
            head: MinaCheckpointHead {
                verified_state: protocol_state.clone(),
                verified_hash: h.clone(),
                tip_state: protocol_state,
                tip_hash: h,
                finalized,
                run: 0,
            },
            cadence,
        }
    }

    /// Whether the next accepted block is due to be a checkpoint.
    pub fn checkpoint_due(&self) -> bool {
        self.head.run + 1 >= self.cadence.blocks
    }

    /// **Offer one candidate.**
    ///
    /// The whole decision — including the parent link, the density re-derivation and `select` —
    /// happens inside the Lean archive. This function decides only *which tier to ask for*, which is
    /// a scheduling question and not a verdict.
    ///
    /// ⚑ ONE candidate against the CURRENT tip. Never a fold: `select` has genuine 3-cycles at real
    /// mainnet constants, so "the best of a candidate set" is not a function of the set.
    pub fn offer(
        &mut self,
        cand: &MinaCandidate,
        prover: &dyn WrapProver,
        gate: &dyn MinaCheckpointGate,
    ) -> Result<CheckpointOutcome, CheckpointError> {
        if cand.protocol_state.len() < MIN_PROTOCOL_STATE_BYTES
            || cand.parent_protocol_state.len() < MIN_PROTOCOL_STATE_BYTES
        {
            return Err(CheckpointError::Malformed(format!(
                "candidate {} B / parent {} B: below the {MIN_PROTOCOL_STATE_BYTES} B floor for a \
                 Protocol_state.Value",
                cand.protocol_state.len(),
                cand.parent_protocol_state.len()
            )));
        }

        let checkpoint = self.checkpoint_due();
        // The expensive conjunct is only ASKED FOR at a checkpoint — that is the whole saving. On a
        // provisional step it is not consulted and the gate ignores it.
        let verdict = if checkpoint {
            prover.verify_wrap(cand.height, &cand.protocol_state, &cand.proof_bytes)
        } else {
            WrapVerdict::Verified
        };

        let wire = checkpoint_wire(
            checkpoint,
            verdict.ok(),
            self.head.finalized,
            self.head.run,
            self.cadence.run_cap,
            &cand.parent_state_hash,
            &self.head.tip_hash,
            &self.head.verified_hash,
            &cand.state_hash,
            &cand.parent_protocol_state,
            &self.head.tip_state,
            &self.head.verified_state,
            &cand.protocol_state,
        );

        let out = gate
            .checkpoint_advance(&wire)
            .map_err(CheckpointError::VerifiedGateUnavailable)?;
        if out == "ERR" {
            // A malformed wire, carried constants that disagree with the pin, a density out of
            // bounds, a non-canonical field element. All refusals; both tiers stay.
            return Ok(CheckpointOutcome::Refused {
                why: "the verified gate refused the candidate (decode, carried constants, density \
                      bound, or canonicality)"
                    .into(),
            });
        }
        let ans = parse_checkpoint_answer(&out).map_err(CheckpointError::GateProtocol)?;

        // ⚑ The ratchet is the GATE's, but an answer that lowered it would be a protocol violation
        // and is refused here rather than stored. `runSteps_finalized_monotone` says this cannot
        // happen; a check that cannot fire is still the right place to notice if the archive ever
        // stops being the thing that theorem is about.
        if ans.finalized < self.head.finalized {
            return Err(CheckpointError::GateProtocol(format!(
                "gate returned a finalized height {} BELOW the persisted {}: the ratchet is proven \
                 monotone, so this archive is not the gate it claims to be",
                ans.finalized, self.head.finalized
            )));
        }
        if !checkpoint && ans.advanced {
            return Err(CheckpointError::GateProtocol(
                "gate advanced the VERIFIED head on a PROVISIONAL call: \
                 `provisional_never_ratchets` says this cannot happen"
                    .into(),
            ));
        }

        self.head.finalized = ans.finalized;
        self.head.run = ans.run;

        if ans.advanced {
            self.head.verified_state = cand.protocol_state.clone();
            self.head.verified_hash = cand.state_hash.clone();
            self.head.tip_state = cand.protocol_state.clone();
            self.head.tip_hash = cand.state_hash.clone();
            return Ok(CheckpointOutcome::CheckpointClosed {
                finalized: ans.finalized,
            });
        }
        if ans.moved {
            self.head.tip_state = cand.protocol_state.clone();
            self.head.tip_hash = cand.state_hash.clone();
            return Ok(CheckpointOutcome::TipAdvanced { run: ans.run });
        }
        Ok(CheckpointOutcome::Refused {
            why: match verdict {
                WrapVerdict::Verified => {
                    "the verified gate kept the head (select preferred the current tip, the parent \
                     link failed, or the density did not follow the parent)"
                        .into()
                }
                WrapVerdict::Refused(w) => format!("the Wrap proof did not verify: {w}"),
                WrapVerdict::Unavailable(w) => {
                    format!("NOTHING WAS DECIDED — no Wrap verdict was obtainable: {w}")
                }
            },
        })
    }

    /// Pull the peer's current best tip and offer it. Needs the parent and the proof from the same
    /// source, which is why this takes a candidate builder rather than a bare byte source.
    pub fn follow_once(
        &mut self,
        source: &dyn MinaProtocolStateSource,
        build: &dyn Fn(Vec<u8>) -> Result<MinaCandidate, MinaSourceError>,
        prover: &dyn WrapProver,
        gate: &dyn MinaCheckpointGate,
    ) -> Result<CheckpointOutcome, CheckpointError> {
        let bytes = source
            .best_tip_protocol_state()
            .map_err(CheckpointError::Source)?;
        let cand = build(bytes).map_err(CheckpointError::Source)?;
        self.offer(&cand, prover, gate)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct ScriptedGate {
        answer: String,
    }

    impl MinaCheckpointGate for ScriptedGate {
        fn checkpoint_advance(&self, _wire: &str) -> Result<String, String> {
            Ok(self.answer.clone())
        }
    }

    struct AbsentGate;

    impl MinaCheckpointGate for AbsentGate {
        fn checkpoint_advance(&self, _wire: &str) -> Result<String, String> {
            Err("dregg_mina_checkpoint_advance not exported by the linked archive".into())
        }
    }

    struct AlwaysVerified;

    impl WrapProver for AlwaysVerified {
        fn verify_wrap(&self, _h: u64, _p: &[u8], _b: &[u8]) -> WrapVerdict {
            WrapVerdict::Verified
        }
    }

    fn client(cadence: CheckpointCadence) -> MinaCheckpointClient {
        MinaCheckpointClient::pinned(vec![0xaa; 1544], "12345", 100, cadence)
    }

    fn cand(hash: &str, height: u64) -> MinaCandidate {
        MinaCandidate {
            protocol_state: vec![0xbb; 1544],
            state_hash: hash.into(),
            height,
            parent_protocol_state: vec![0xaa; 1544],
            parent_state_hash: "12345".into(),
            proof_bytes: vec![0u8; 11138],
        }
    }

    /// ⚑ THE CADENCE ARITHMETIC, which is the design's whole claim. Mina's own finality is 14.5 h;
    /// 10 min and 1 h are rounding errors against it and a day is not.
    #[test]
    fn the_cadence_table_is_the_one_the_docs_state() {
        assert_eq!(CheckpointCadence::mina_own_finality_seconds(), 52_200);
        assert_eq!(CheckpointCadence::TEN_MINUTES.added_latency_seconds(), 540);
        assert_eq!(CheckpointCadence::ONE_HOUR.added_latency_seconds(), 3_600);
        assert_eq!(CheckpointCadence::ONE_DAY.added_latency_seconds(), 86_400);
        assert_eq!(CheckpointCadence::TEN_MINUTES.added_latency_percent(), 1);
        assert_eq!(CheckpointCadence::ONE_HOUR.added_latency_percent(), 6);
        assert_eq!(CheckpointCadence::ONE_DAY.added_latency_percent(), 165);
        // A 60 s compiled checkpoint is sustainable at every cadence; a 3.5 h kernel one at none
        // below a day. This is the number that decides which cadences are real.
        assert!(CheckpointCadence::TEN_MINUTES.sustainable(60));
        assert!(!CheckpointCadence::TEN_MINUTES.sustainable(12_600));
        assert!(!CheckpointCadence::ONE_HOUR.sustainable(12_600));
        assert!(CheckpointCadence::ONE_DAY.sustainable(12_600));
        assert_eq!(CheckpointCadence::ONE_HOUR.duty_cycle_ppm(60), 16_666);
    }

    /// ⚑ THE DEFAULT PROVER FINALIZES NOTHING, and says why. A client built today is observably
    /// unable to close a checkpoint rather than quietly closing one.
    #[test]
    fn the_default_prover_is_unavailable_not_verified() {
        let v = UnavailableWrapProver.verify_wrap(540_186, &[], &[]);
        assert!(!v.ok());
        assert!(matches!(v, WrapVerdict::Unavailable(_)));
        let WrapVerdict::Unavailable(why) = v else {
            unreachable!()
        };
        assert!(why.contains("expand_deferred"), "{why}");
    }

    #[test]
    fn the_wire_matches_the_lean_grammar() {
        let w = checkpoint_wire(
            false,
            true,
            7,
            2,
            32,
            "1",
            "2",
            "3",
            "4",
            &[0xde],
            &[0xad],
            &[0xbe],
            &[0xef],
        );
        assert_eq!(
            w,
            "md=p;wk=1;fz=7;rn=2;rc=32;ph=1;th=2;vh=3;ch=4;p=de;t=ad;v=be;c=ef"
        );
        let c = checkpoint_wire(true, false, 0, 0, 6, "1", "2", "3", "4", &[], &[], &[], &[]);
        assert!(c.starts_with("md=c;wk=0;"), "{c}");
    }

    #[test]
    fn off_grammar_gate_output_is_refused() {
        for bad in [
            "",
            "yes",
            "mv=1;adv=0;fin=1",
            "mv=2;adv=0;fin=1;rn=0",
            "mv=1;adv=0;fin=x;rn=0",
            "mv=1;adv=0;fin=1;rn=0;extra",
        ] {
            assert!(
                parse_checkpoint_answer(bad).is_err(),
                "{bad:?} must not parse"
            );
        }
        assert_eq!(
            parse_checkpoint_answer("mv=1;adv=0;fin=539897;rn=4").unwrap(),
            CheckpointAnswer {
                moved: true,
                advanced: false,
                finalized: 539_897,
                run: 4
            }
        );
    }

    /// A provisional step moves the tip and leaves the ratchet — the Rust mirror of
    /// `provisional_never_ratchets`.
    #[test]
    fn a_provisional_step_moves_the_tip_and_not_the_ratchet() {
        let mut c = client(CheckpointCadence::ONE_HOUR);
        let g = ScriptedGate {
            answer: "mv=1;adv=0;fin=100;rn=1".into(),
        };
        let out = c.offer(&cand("999", 540_187), &AlwaysVerified, &g).unwrap();
        assert_eq!(out, CheckpointOutcome::TipAdvanced { run: 1 });
        assert_eq!(c.head.tip_hash, "999");
        assert_eq!(
            c.head.verified_hash, "12345",
            "the checkpoint must not move"
        );
        assert_eq!(c.head.finalized, 100);
    }

    /// A checkpoint closes, re-anchors both tiers and raises the ratchet.
    #[test]
    fn a_checkpoint_closes_and_reanchors() {
        let mut c = client(CheckpointCadence::TEN_MINUTES);
        c.head.run = 2; // the next block is due to be a checkpoint
        assert!(c.checkpoint_due());
        let g = ScriptedGate {
            answer: "mv=1;adv=1;fin=539897;rn=0".into(),
        };
        let out = c.offer(&cand("999", 540_187), &AlwaysVerified, &g).unwrap();
        assert_eq!(
            out,
            CheckpointOutcome::CheckpointClosed { finalized: 539_897 }
        );
        assert_eq!(c.head.verified_hash, "999");
        assert_eq!(c.head.tip_hash, "999");
        assert_eq!(c.head.run, 0);
    }

    /// ⚑ AN UNAVAILABLE WRAP VERDICT IS A REFUSAL WITH ITS OWN MESSAGE, not an `Ok` that means
    /// "checked nothing". This is the arm the whole module exists to keep closed, and today it is
    /// the arm every real height takes.
    #[test]
    fn an_unavailable_wrap_verdict_refuses_the_checkpoint() {
        let mut c = client(CheckpointCadence::TEN_MINUTES);
        c.head.run = 2;
        let before = c.head.clone();
        // The gate is told `wk=0` and answers accordingly.
        let g = ScriptedGate {
            answer: "mv=0;adv=0;fin=100;rn=2".into(),
        };
        let out = c
            .offer(&cand("999", 540_187), &UnavailableWrapProver, &g)
            .unwrap();
        match out {
            CheckpointOutcome::Refused { why } => {
                assert!(why.contains("NOTHING WAS DECIDED"), "{why}");
                assert!(why.contains("expand_deferred"), "{why}");
            }
            other => panic!("must refuse, got {other:?}"),
        }
        assert_eq!(
            c.head, before,
            "a refused checkpoint must not be half-applied"
        );
    }

    /// ⚑ An absent archive is a REFUSAL, not a skipped check, and NEITHER tier moves.
    #[test]
    fn an_absent_gate_freezes_both_tiers() {
        let mut c = client(CheckpointCadence::ONE_HOUR);
        let before = c.head.clone();
        let e = c
            .offer(&cand("999", 540_187), &AlwaysVerified, &AbsentGate)
            .unwrap_err();
        assert!(matches!(e, CheckpointError::VerifiedGateUnavailable(_)));
        assert!(e.to_string().contains("NEITHER"), "{e}");
        assert_eq!(c.head, before);
    }

    /// ⚑ A gate that raised the VERIFIED head on a provisional call is refused, not stored.
    /// `provisional_never_ratchets` says the real gate cannot do this; the check exists so an
    /// archive that is no longer that gate is noticed instead of obeyed.
    #[test]
    fn a_gate_that_advances_on_a_provisional_call_is_refused() {
        let mut c = client(CheckpointCadence::ONE_HOUR);
        let before = c.head.clone();
        let g = ScriptedGate {
            answer: "mv=1;adv=1;fin=200;rn=1".into(),
        };
        let e = c
            .offer(&cand("999", 540_187), &AlwaysVerified, &g)
            .unwrap_err();
        assert!(matches!(e, CheckpointError::GateProtocol(_)));
        assert_eq!(c.head, before);
    }

    /// ⚑ A gate that lowered the ratchet is refused rather than stored.
    #[test]
    fn a_gate_that_lowers_the_ratchet_is_refused() {
        let mut c = client(CheckpointCadence::ONE_HOUR);
        let before = c.head.clone();
        let g = ScriptedGate {
            answer: "mv=1;adv=0;fin=99;rn=1".into(),
        };
        let e = c
            .offer(&cand("999", 540_187), &AlwaysVerified, &g)
            .unwrap_err();
        assert!(matches!(e, CheckpointError::GateProtocol(_)));
        assert_eq!(c.head, before);
    }

    /// A candidate served without its parent cannot be judged: the density re-derivation has
    /// nothing to read, and a client that proceeded would have silently degraded to a bound check.
    #[test]
    fn a_candidate_without_a_real_parent_is_malformed() {
        let mut c = client(CheckpointCadence::ONE_HOUR);
        let mut bad = cand("999", 540_187);
        bad.parent_protocol_state = vec![];
        let g = ScriptedGate {
            answer: "mv=1;adv=0;fin=100;rn=1".into(),
        };
        let e = c.offer(&bad, &AlwaysVerified, &g).unwrap_err();
        assert!(matches!(e, CheckpointError::Malformed(_)));
    }

    /// `checkpoint_due` really fires on the cadence and not on a fencepost.
    #[test]
    fn checkpoint_due_fires_on_the_cadence() {
        let mut c = client(CheckpointCadence::TEN_MINUTES); // blocks = 3
        assert!(!c.checkpoint_due(), "run 0 -> next block is 1 of 3");
        c.head.run = 1;
        assert!(!c.checkpoint_due());
        c.head.run = 2;
        assert!(c.checkpoint_due(), "run 2 -> next block is the 3rd");
    }
}
