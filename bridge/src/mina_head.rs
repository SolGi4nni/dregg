//! **The Mina byte source, and the persisted verified head that rolls forward.**
//!
//! # What this module is for
//!
//! `mina_observer` is an *anchored-segment verifier*: hand it a segment and it checks the segment.
//! A light client does something else — it holds a head, is offered candidates, and decides for
//! itself which one is canonical. This module is that difference.
//!
//! # ⚑ Rust decides nothing, and does not even PARSE
//!
//! Every decision below crosses into the Lean archive:
//!
//!   * **which tip is canonical** — `dregg_mina_better_tip`
//!     (`Dregg2.Bridge.MinaForkChoiceGate`), Samasika's `select` as the daemon writes it,
//!   * **whether the head may move, and what the new finalized height is** —
//!     `dregg_mina_head_advance`,
//!   * **what the bytes MEAN** — `Dregg2.Bridge.MinaBinprot`, a Lean binprot decoder for
//!     `Protocol_state.Value.Stable.V2`.
//!
//! That last one is the unusual boundary and it is deliberate. A Rust decoder would be a hand-
//! written rendering of what a Mina consensus state *is* — which bytes are `min_window_density`
//! and which are `epoch_count` — and its correctness would be established by DIFFERENTIAL TESTING
//! against openmina's `p2p-messages`. That is a mirror. The parse is semantics, so the parse is in
//! Lean, and `MinaBinprot.decodeProtocolState` returns `MinaChainSelection.ConsensusState` — the
//! exact structure `select` is proven over, with no conversion in between.
//!
//! So this file hex-encodes bytes and reads a verdict string. It contains no notion of a field.
//!
//! # ⚑ PAIRWISE. NEVER A FOLD.
//!
//! `MinaChainSelection.beats_not_transitive` proves `select` has genuine 3-cycles at real mainnet
//! constants, `decide`-checked, by two independent mechanisms. "The best of a candidate SET" is
//! therefore not a function of the set — it depends on presentation order, and a peer that controls
//! that order can walk a node around the cycle. [`MinaVerifiedHead::offer`] compares ONE candidate
//! against the CURRENT head. Do not "improve" it into a `fold` or a `max_by`.
//!
//! What survives the cycle is the ratchet: `rollHead_finalized_monotone` proves the finalized
//! height never decreases on any input, and `the_cycle_moves_the_head_but_not_the_finalized_point`
//! executes three genuine advances that return the head to exactly its starting value while the
//! finalized height holds. The head is a preference; the finalized point is a ratchet.
//!
//! # Where the bytes come from
//!
//! [`MinaProtocolStateSource`] is the seam. The bytes must be a binprot
//! `Protocol_state.Value.Stable.V2`, which is what Mina's peer-to-peer RPC carries and what the
//! public GraphQL cannot produce: `subWindowDensities` is **not a field of the GraphQL
//! `ConsensusState`** (`proof_of_stake.ml:2449-2536` has no resolver for it), so Samasika's
//! long-range branch cannot be evaluated from that surface at all.
//!
//! ⚑ **The byte source is a SUBPROCESS, and that is on purpose.** The protocol is
//! `TCP → pnet(XSalsa20 under the chain-id PSK) → multistream-select → Noise XX → /coda/yamux/1.0.0
//! → coda/rpcs/0.0.1 → get_best_tip v2`. openmina is a complete Rust implementation of exactly that
//! and it is on this machine; hand-writing Salsa20, a Noise XX state machine and a yamux muxer into
//! this crate would be reconstructing a thing that already exists, which is the same mistake as a
//! Rust binprot decoder wearing different clothes. [`CommandProtocolStateSource`] runs an
//! operator-configured helper and takes its stdout. The helper shipped here is
//! `bridge/tools/mina-tip` — a small Rust bin that LINKS openmina's audited stack (it does not
//! reimplement it), replacing the retired `mina-besttip.py` Python transport.
//!
//! # Fail closed
//!
//! There is no `bestChain` fallback and no path that proceeds without a verdict. An unavailable
//! source, an unavailable archive, and a rejected candidate are three distinct errors and all three
//! leave the head where it was. This repo has a named class for gates that log and proceed; this is
//! not one.

use std::path::PathBuf;
use std::process::Command;

// ===========================================================================
// The byte source
// ===========================================================================

/// Why no protocol-state bytes could be obtained. Every variant is a REFUSAL.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MinaSourceError {
    /// The configured source could not be run at all (missing helper, spawn failure).
    Unavailable(String),
    /// The source ran and failed.
    Failed(String),
    /// The source produced something that cannot be a protocol state.
    Malformed(String),
}

impl std::fmt::Display for MinaSourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unavailable(m) => write!(f, "Mina protocol-state source unavailable: {m}"),
            Self::Failed(m) => write!(f, "Mina protocol-state source failed: {m}"),
            Self::Malformed(m) => write!(f, "Mina protocol-state source returned garbage: {m}"),
        }
    }
}

impl std::error::Error for MinaSourceError {}

/// A source of raw binprot `Protocol_state.Value.Stable.V2` bytes.
///
/// The contract is deliberately thin: **bytes, or an error.** Nothing about a Mina consensus state
/// appears in this trait, because nothing about it appears anywhere in this crate — the meaning of
/// the bytes lives in `Dregg2.Bridge.MinaBinprot`.
pub trait MinaProtocolStateSource {
    /// The peer's current best tip, as the `Protocol_state.Value` prefix of its block header. A
    /// trailing remainder (the Wrap proof, the block body) is fine and is ignored by the decoder.
    fn best_tip_protocol_state(&self) -> Result<Vec<u8>, MinaSourceError>;
}

/// A source that runs an external helper and takes its stdout as the bytes.
///
/// The helper speaks Mina's peer-to-peer stack. `bridge/tools/mina-tip besttip` is the one this is
/// built against and the one measured: it LINKS openmina (`~/dev/mina-rust`) — the maintained Rust
/// implementation of the Mina protocol the ecosystem runs — negotiates pnet / Noise XX / yamux /
/// `coda/rpcs/0.0.1`, issues `get_best_tip` v2, and writes the tip's raw `Protocol_state.Value`
/// binprot to stdout.
///
/// ⚑ The byte source is now the AUDITED Rust stack, not a hand-written transport. `mina-tip`
/// depends on openmina's `mina-transport`, `mina-p2p-messages` and `libp2p-rpc-behaviour` crates by
/// path and calls their real RPC client; it reimplements no protocol. (The retired
/// `mina-besttip.py` was a small dependency-light Python transport — correct, but not audited and
/// not a production path.)
///
/// ⚑ The source is TRUSTED FOR AVAILABILITY ONLY, not for content — and that fact is not
/// transmutable, because no light client can be defended against a withholding peer. It cannot make
/// the client accept a chain: every byte it produces goes through the Lean decoder's canonicality,
/// bound and carried-constants refusals and then through `select`. The worst a malicious source
/// achieves is to be refused, or to withhold.
#[derive(Clone, Debug)]
pub struct CommandProtocolStateSource {
    /// The helper binary.
    pub program: PathBuf,
    /// Arguments (typically the peer multiaddr).
    pub args: Vec<String>,
}

impl MinaProtocolStateSource for CommandProtocolStateSource {
    fn best_tip_protocol_state(&self) -> Result<Vec<u8>, MinaSourceError> {
        let out = Command::new(&self.program)
            .args(&self.args)
            .output()
            .map_err(|e| {
                MinaSourceError::Unavailable(format!("{}: {e}", self.program.display()))
            })?;
        if !out.status.success() {
            return Err(MinaSourceError::Failed(format!(
                "{} exited {}: {}",
                self.program.display(),
                out.status,
                String::from_utf8_lossy(&out.stderr).trim()
            )));
        }
        if out.stdout.len() < MIN_PROTOCOL_STATE_BYTES {
            return Err(MinaSourceError::Malformed(format!(
                "{} bytes is too short to be a protocol state",
                out.stdout.len()
            )));
        }
        Ok(out.stdout)
    }
}

/// A source over bytes already in hand — a capture, or a test vector.
///
/// Not a mock: the bytes are real wire bytes and they go through the same Lean decoder. This is how
/// the offline path and the tests get a genuine `Protocol_state.Value`.
#[derive(Clone, Debug)]
pub struct StaticProtocolStateSource(pub Vec<u8>);

impl MinaProtocolStateSource for StaticProtocolStateSource {
    fn best_tip_protocol_state(&self) -> Result<Vec<u8>, MinaSourceError> {
        if self.0.len() < MIN_PROTOCOL_STATE_BYTES {
            return Err(MinaSourceError::Malformed(format!(
                "{} bytes is too short to be a protocol state",
                self.0.len()
            )));
        }
        Ok(self.0.clone())
    }
}

/// A floor below which a byte string cannot be a `Protocol_state.Value`.
///
/// Measured, not guessed: devnet block 540186's protocol state is **1544 bytes** (openmina
/// re-encoded it to exactly that, and the Lean decoder consumes exactly that). The floor is set
/// well below it because the size varies with the failure tables and amount widths; it exists to
/// turn an empty or truncated helper output into a REFUSAL here rather than a decoder error later.
pub const MIN_PROTOCOL_STATE_BYTES: usize = 512;

// ===========================================================================
// The persisted verified head
// ===========================================================================

/// The light client's persisted state — the Rust mirror of `MinaForkChoiceGate.Head`, carrying
/// bytes where Lean carries a decoded structure.
///
/// ⚑ `finalized_height` is a RATCHET. It is not maintained here: it comes back from
/// `dregg_mina_head_advance`, which is where `rollHead_finalized_monotone` proves it never
/// decreases. Rust stores what the gate returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaVerifiedHead {
    /// The head tip's `Protocol_state.Value` binprot bytes.
    pub protocol_state: Vec<u8>,
    /// The head tip's state hash as a decimal field element. ⚑ Passed to the gate, which
    /// RE-DERIVES it from `protocol_state` and refuses the pair on a mismatch — see
    /// [`tip_wire`]. A head that ever held a hash its own bytes do not have could not have
    /// advanced into that position, because the wire that put it there was checked.
    pub state_hash: String,
    /// The greatest height this client has ever finalized. Never decreases.
    pub finalized_height: u64,
}

/// What happened when a candidate was offered to the head.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HeadOutcome {
    /// The head moved. Carries the new finalized height (≥ the old one, by
    /// `rollHead_finalized_monotone`).
    Advanced {
        /// The new finalized height.
        finalized_height: u64,
    },
    /// The head did not move, and why is not interesting to the caller beyond "the verified gate
    /// said no": the candidate lost `select`, or its segment was not accepted.
    Kept,
}

/// Why a candidate could not be judged. ⚑ Distinct from [`HeadOutcome::Kept`] on purpose: "the
/// rule refused it" and "there was no rule available" are different facts, and conflating them is
/// exactly how a fail-open gate is built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HeadError {
    /// No bytes.
    Source(MinaSourceError),
    /// The Lean archive does not export the fork-choice gate. There is NO Rust twin; the head
    /// cannot move, and this is a refusal rather than a skipped check.
    VerifiedGateUnavailable(String),
    /// The gate answered something that is not its grammar.
    GateProtocol(String),
}

impl std::fmt::Display for HeadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source(e) => write!(f, "{e}"),
            Self::VerifiedGateUnavailable(m) => write!(
                f,
                "the verified Mina fork-choice gate is not in the linked archive ({m}); the head \
                 CANNOT advance and there is no unverified path that would let it"
            ),
            Self::GateProtocol(m) => write!(f, "verified gate answered off-grammar: {m}"),
        }
    }
}

impl std::error::Error for HeadError {}

/// Lowercase hex, two digits per byte. The gate's wire encoding for a protocol state.
pub fn hex_of(bytes: &[u8]) -> String {
    const D: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push(D[usize::from(b >> 4)] as char);
        s.push(D[usize::from(b & 0x0f)] as char);
    }
    s
}

/// Build the `TIP` half of both gate wires.
///
/// ⚑ **`existing_hash`/`candidate_hash` are CHECKED, not accepted** (since 2026-07-30). They used
/// to be the one supplied input on this wire: `state_hash =
/// Poseidon("MinaProtoState")[previous_state_hash, body_hash]` was re-derived nowhere, so the peer
/// named both the bytes and the identity of the block those bytes are.
/// `Dregg2.Bridge.MinaStateHashDerive` recomputes it inside the archive and
/// `MinaForkChoiceGate.decodeSide?` returns `"ERR"` on a disagreement, so what these two strings
/// carry is now a claim the gate refutes rather than an input it trusts.
///
/// That matters for exactly the use `select` puts them to: they are the FINAL tie-break, after
/// `blockchain_length` and the Blake2b VRF digest have both tied, and it is a numeric comparison —
/// so a peer that could name its own hash could win every tie by claiming a larger one while
/// serving whatever bytes it liked.
///
/// They are still *passed in* rather than returned by the gate. Deleting the fields entirely — the
/// gate derives both identities from the bytes and the wire stops carrying a hash at all — is the
/// remaining hygiene, and it no longer changes what an adversary can do.
pub fn tip_wire(
    existing_hash: &str,
    candidate_hash: &str,
    existing: &[u8],
    candidate: &[u8],
) -> String {
    format!(
        "eh={existing_hash};ch={candidate_hash};e={};c={}",
        hex_of(existing),
        hex_of(candidate)
    )
}

/// The wire `dregg_mina_head_advance` reads.
pub fn head_advance_wire(
    segment_ok: bool,
    finalized_height: u64,
    existing_hash: &str,
    candidate_hash: &str,
    existing: &[u8],
    candidate: &[u8],
) -> String {
    format!(
        "sg={};fz={finalized_height};{}",
        u8::from(segment_ok),
        tip_wire(existing_hash, candidate_hash, existing, candidate)
    )
}

/// Parse the gate's `"adv=B;fin=N"` answer. Strict: anything else is an error, never a default.
pub fn parse_head_advance(out: &str) -> Result<(bool, u64), String> {
    let mut parts = out.split(';');
    let adv = parts.next().ok_or("missing adv")?;
    let fin = parts.next().ok_or("missing fin")?;
    if parts.next().is_some() {
        return Err(format!("trailing fields in {out:?}"));
    }
    let adv = match adv {
        "adv=1" => true,
        "adv=0" => false,
        other => return Err(format!("bad adv field {other:?}")),
    };
    let fin = fin
        .strip_prefix("fin=")
        .ok_or_else(|| format!("bad fin field {fin:?}"))?
        .parse::<u64>()
        .map_err(|e| format!("bad fin value: {e}"))?;
    Ok((adv, fin))
}

impl MinaVerifiedHead {
    /// Start following from a pinned head. ⚑ This is the weak-subjectivity act and it is the
    /// operator's: a light client cannot bootstrap trust from nothing, and pretending otherwise is
    /// how a Nomad-shaped hole gets built. Everything after this point is decided by the rule.
    pub fn pinned(protocol_state: Vec<u8>, state_hash: impl Into<String>, finalized: u64) -> Self {
        Self {
            protocol_state,
            state_hash: state_hash.into(),
            finalized_height: finalized,
        }
    }

    /// **Offer one candidate to the head.**
    ///
    /// `segment_ok` is the anchored-segment verdict — `dregg_mina_lc_verify` having returned `"1"`
    /// for the segment that reaches this candidate. It is a required conjunct, not a hint: fork
    /// choice presupposes both tips are VALID, and running `select` on an unvalidated tip is just
    /// believing a stranger's arithmetic. An unavailable segment gate supplies `false`, and
    /// `rollHead_fails_closed_without_the_segment` proves that moves nothing.
    ///
    /// ⚑ ONE candidate, against the CURRENT head. Never a fold — see the module header.
    ///
    /// The whole decision, including the parse of both protocol states, happens inside the Lean
    /// archive. This function hex-encodes, calls, and stores.
    pub fn offer(
        &mut self,
        candidate: &[u8],
        candidate_hash: &str,
        segment_ok: bool,
        gate: &dyn MinaForkChoiceGate,
    ) -> Result<HeadOutcome, HeadError> {
        let wire = head_advance_wire(
            segment_ok,
            self.finalized_height,
            &self.state_hash,
            candidate_hash,
            &self.protocol_state,
            candidate,
        );
        let out = gate
            .head_advance(&wire)
            .map_err(HeadError::VerifiedGateUnavailable)?;
        if out == "ERR" {
            // A malformed wire, a block whose carried constants disagree with the pin, a density
            // out of bounds, a non-canonical field element. All refusals; the head stays.
            return Ok(HeadOutcome::Kept);
        }
        let (advance, finalized) = parse_head_advance(&out).map_err(HeadError::GateProtocol)?;
        // ⚑ The ratchet is the GATE's, but a gate answer that lowered it would be a protocol
        // violation and is refused here rather than stored. `rollHead_finalized_monotone` says
        // this cannot happen; a check that cannot fire is still the right place to notice if the
        // archive ever stops being the thing that theorem is about.
        if finalized < self.finalized_height {
            return Err(HeadError::GateProtocol(format!(
                "gate returned a finalized height {finalized} BELOW the persisted {}: the ratchet \
                 is proven monotone, so this archive is not the gate it claims to be",
                self.finalized_height
            )));
        }
        self.finalized_height = finalized;
        if advance {
            self.protocol_state = candidate.to_vec();
            self.state_hash = candidate_hash.to_string();
            Ok(HeadOutcome::Advanced {
                finalized_height: finalized,
            })
        } else {
            Ok(HeadOutcome::Kept)
        }
    }

    /// **Offer a whole candidate set, one pairwise offer at a time.**
    ///
    /// # ⚑ THIS IS NOT A FOLD, AND THE DIFFERENCE IS THE WHOLE POINT
    ///
    /// A `max_by` over a candidate set would be exploitable: `MinaChainSelection.beats_not_transitive`
    /// proves `select` has genuine 3-cycles at real Mina constants, so "the best of this set" is
    /// not a function of the set — it is a function of the ORDER. This method does not compute a
    /// maximum. It replays exactly what a light client does when candidates arrive over time: each
    /// one is offered to the CURRENT head, one at a time, by [`Self::offer`].
    ///
    /// What that means for the caller, stated rather than implied: **the resulting head depends on
    /// `candidates`' order.** That is not a defect here, it is the protocol. The object that does
    /// not depend on order is `finalized_height`, and `rollHead_finalized_monotone` is why.
    ///
    /// # The anchor is a precondition, not a hint
    ///
    /// A candidate whose `anchored` flag is false is **never offered to the gate at all** — it is
    /// counted in [`CandidateSetOutcome::unanchored`] and skipped. That flag is not this crate's to
    /// invent: it comes from `mina-tip verify-bestchain`, which folds the peer's transition-chain
    /// proof from that peer's frontier root to the tip, on openmina's own Poseidon
    /// (`bridge/tools/mina-tip/src/chain.rs::verify_anchor`).
    ///
    /// ⚑ Without it, `select`'s short-range branch reads `blockchain_length` off bytes a peer
    /// composed and nothing else — the one field a liar controls for free. The anchor is what costs
    /// something to forge.
    pub fn follow_candidate_set(
        &mut self,
        candidates: &[MinaCandidateTip],
        gate: &dyn MinaForkChoiceGate,
    ) -> Result<CandidateSetOutcome, HeadError> {
        let mut out = CandidateSetOutcome {
            offered: 0,
            advanced: 0,
            kept: 0,
            unanchored: 0,
            finalized_height: self.finalized_height,
        };
        for c in candidates {
            if !c.anchored {
                out.unanchored += 1;
                continue;
            }
            out.offered += 1;
            match self.offer(&c.protocol_state, &c.state_hash, c.segment_ok, gate)? {
                HeadOutcome::Advanced { finalized_height } => {
                    out.advanced += 1;
                    out.finalized_height = finalized_height;
                }
                HeadOutcome::Kept => out.kept += 1,
            }
        }
        out.finalized_height = self.finalized_height;
        Ok(out)
    }

    /// Pull the peer's current best tip and offer it. The one-call "follow the chain" step.
    pub fn follow_once(
        &mut self,
        source: &dyn MinaProtocolStateSource,
        candidate_hash: &str,
        segment_ok: bool,
        gate: &dyn MinaForkChoiceGate,
    ) -> Result<HeadOutcome, HeadError> {
        let bytes = source
            .best_tip_protocol_state()
            .map_err(HeadError::Source)?;
        self.offer(&bytes, candidate_hash, segment_ok, gate)
    }
}

/// **One member of a candidate set** — a tip a peer served, with the two facts that decide whether
/// it may be judged at all.
///
/// ⚑ `anchored` and `segment_ok` are inputs BECAUSE THEY ARE OTHER GATES' VERDICTS, and neither is
/// computed here. Conflating "no one checked" with "it checked out" is exactly how a fail-open gate
/// is built, so both default to the refusing value in every constructor this module offers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaCandidateTip {
    /// The tip's `Protocol_state.Value` binprot bytes — `cand-NN.ps` in a `mina-tip` bundle.
    pub protocol_state: Vec<u8>,
    /// The tip's state hash. ⚑ CHECKED by the gate against `protocol_state`, never trusted — see
    /// [`tip_wire`].
    pub state_hash: String,
    /// Whether this tip's transition-chain proof folded from the serving peer's frontier root to
    /// the tip, on openmina's own Poseidon. `mina-tip verify-bestchain` is what decides it.
    ///
    /// **False means the candidate is never offered to the fork-choice gate.**
    pub anchored: bool,
    /// The anchored-SEGMENT verdict (`dregg_mina_lc_verify`). A different question from `anchored`:
    /// that one asks "does this tip descend from the root its peer served", this one asks "is the
    /// segment reaching it valid". Fork choice presupposes both.
    pub segment_ok: bool,
    /// The peer that served it. Attribution only.
    pub peer: String,
}

impl MinaCandidateTip {
    /// A candidate that has passed NOTHING. Both verdicts start at the refusing value; a caller
    /// that wants them true must have a gate that said so.
    pub fn unjudged(
        protocol_state: Vec<u8>,
        state_hash: impl Into<String>,
        peer: impl Into<String>,
    ) -> Self {
        Self {
            protocol_state,
            state_hash: state_hash.into(),
            anchored: false,
            segment_ok: false,
            peer: peer.into(),
        }
    }
}

/// What happened across a whole candidate set.
///
/// ⚑ `offered + unanchored` is the set size, and the split is reported rather than summed away: a
/// run in which every candidate was unanchored looks identical to a run with no candidates if you
/// only read `advanced`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateSetOutcome {
    /// How many reached the fork-choice gate.
    pub offered: usize,
    /// How many moved the head.
    pub advanced: usize,
    /// How many the rule refused.
    pub kept: usize,
    /// ⚑ How many were NEVER OFFERED because their transition-chain proof did not fold.
    pub unanchored: usize,
    /// The finalized height after the walk. Never below where it started.
    pub finalized_height: u64,
}

/// The verified gate, as a seam so this module is testable without the archive.
///
/// ⚑ The seam is for TESTS, not for a fallback. There is exactly one production implementation and
/// it calls the Lean export; an absent archive is `Err`, and every caller turns that into a
/// refusal.
pub trait MinaForkChoiceGate {
    /// Run `dregg_mina_head_advance`. `Err` means the archive does not export it.
    fn head_advance(&self, wire: &str) -> Result<String, String>;

    /// Run `dregg_mina_better_tip`. `Err` means the archive does not export it.
    fn better_tip(&self, wire: &str) -> Result<String, String>;
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A stand-in that implements the GRAMMAR, so the Rust plumbing (wire assembly, strict output
    /// parsing, ratchet storage, fail-closed arms) is tested without the archive. It decides
    /// nothing about Mina — the real decisions are `native_decide`-checked on real devnet bytes in
    /// `Dregg2.Bridge.MinaBinprotRealBlock`.
    struct ScriptedGate {
        answer: String,
    }

    impl MinaForkChoiceGate for ScriptedGate {
        fn head_advance(&self, _wire: &str) -> Result<String, String> {
            Ok(self.answer.clone())
        }
        fn better_tip(&self, _wire: &str) -> Result<String, String> {
            Ok(self.answer.clone())
        }
    }

    struct AbsentGate;

    impl MinaForkChoiceGate for AbsentGate {
        fn head_advance(&self, _wire: &str) -> Result<String, String> {
            Err("dregg_mina_head_advance not exported by the linked archive".into())
        }
        fn better_tip(&self, _wire: &str) -> Result<String, String> {
            Err("dregg_mina_better_tip not exported by the linked archive".into())
        }
    }

    fn head() -> MinaVerifiedHead {
        MinaVerifiedHead::pinned(vec![0xaa; 600], "12345", 100)
    }

    #[test]
    fn hex_encoding_is_lowercase_two_digits_per_byte() {
        assert_eq!(hex_of(&[0x00, 0x0f, 0xa0, 0xff]), "000fa0ff");
        assert_eq!(hex_of(&[]), "");
    }

    #[test]
    fn the_tip_wire_matches_the_lean_grammar() {
        let w = tip_wire("1", "2", &[0xde, 0xad], &[0xbe, 0xef]);
        assert_eq!(w, "eh=1;ch=2;e=dead;c=beef");
        let h = head_advance_wire(true, 7, "1", "2", &[0xde, 0xad], &[0xbe, 0xef]);
        assert_eq!(h, "sg=1;fz=7;eh=1;ch=2;e=dead;c=beef");
        assert!(head_advance_wire(false, 0, "1", "2", &[], &[]).starts_with("sg=0;fz=0;"));
    }

    #[test]
    fn the_head_advances_and_stores_the_gates_finalized_height() {
        let mut h = head();
        let g = ScriptedGate {
            answer: "adv=1;fin=539897".into(),
        };
        let out = h.offer(&[0xbb; 600], "999", true, &g).unwrap();
        assert_eq!(
            out,
            HeadOutcome::Advanced {
                finalized_height: 539_897
            }
        );
        assert_eq!(h.state_hash, "999");
        assert_eq!(h.protocol_state, vec![0xbb; 600]);
        assert_eq!(h.finalized_height, 539_897);
    }

    #[test]
    fn a_kept_head_does_not_move_but_the_ratchet_may_still_rise() {
        let mut h = head();
        let g = ScriptedGate {
            answer: "adv=0;fin=100".into(),
        };
        assert_eq!(
            h.offer(&[0xbb; 600], "999", true, &g).unwrap(),
            HeadOutcome::Kept
        );
        assert_eq!(h.state_hash, "12345");
        assert_eq!(h.protocol_state, vec![0xaa; 600]);
        assert_eq!(h.finalized_height, 100);
    }

    /// ⚑ An absent archive is a REFUSAL, not a skipped check, and it is a DIFFERENT error from
    /// "the rule said no". There is no Rust twin to fall back to and no arm that advances.
    #[test]
    fn an_absent_gate_is_a_refusal_and_the_head_does_not_move() {
        let mut h = head();
        let before = h.clone();
        let e = h.offer(&[0xbb; 600], "999", true, &AbsentGate).unwrap_err();
        assert!(matches!(e, HeadError::VerifiedGateUnavailable(_)));
        assert!(
            e.to_string().contains("CANNOT advance"),
            "the message must say the head cannot move: {e}"
        );
        assert_eq!(h, before);
    }

    /// ⚑ `"ERR"` — a malformed wire, or a block whose carried constants disagree with the pin — is
    /// a KEPT head, never an advance.
    #[test]
    fn a_gate_error_string_keeps_the_head() {
        let mut h = head();
        let before = h.clone();
        let g = ScriptedGate {
            answer: "ERR".into(),
        };
        assert_eq!(
            h.offer(&[0xbb; 600], "999", true, &g).unwrap(),
            HeadOutcome::Kept
        );
        assert_eq!(h, before);
    }

    /// ⚑ A gate that tried to LOWER the finalized height is refused rather than stored.
    /// `rollHead_finalized_monotone` proves the real gate cannot do this; the check exists so that
    /// an archive which is no longer that gate is noticed instead of obeyed.
    #[test]
    fn a_gate_that_lowers_the_ratchet_is_refused() {
        let mut h = head();
        let before = h.clone();
        let g = ScriptedGate {
            answer: "adv=1;fin=99".into(),
        };
        let e = h.offer(&[0xbb; 600], "999", true, &g).unwrap_err();
        assert!(matches!(e, HeadError::GateProtocol(_)));
        assert_eq!(h, before, "a refused answer must not be half-applied");
    }

    #[test]
    fn off_grammar_gate_output_is_refused() {
        for bad in [
            "",
            "yes",
            "adv=1",
            "adv=2;fin=1",
            "adv=1;fin=x",
            "adv=1;fin=1;extra",
        ] {
            assert!(
                parse_head_advance(bad).is_err(),
                "{bad:?} must not parse as a head-advance answer"
            );
        }
        assert_eq!(
            parse_head_advance("adv=1;fin=539897").unwrap(),
            (true, 539_897)
        );
        assert_eq!(parse_head_advance("adv=0;fin=0").unwrap(), (false, 0));
    }

    /// ⚑ An unavailable SOURCE is its own refusal and never a fall back to a node's own answer.
    /// The class this avoids is the one `mina_observer` was built on: asking a node which chain is
    /// canonical and calling the reply a verification.
    #[test]
    fn an_unavailable_source_is_a_refusal() {
        let mut h = head();
        let before = h.clone();
        let src = CommandProtocolStateSource {
            program: PathBuf::from("/nonexistent/mina-tip"),
            args: vec![],
        };
        let g = ScriptedGate {
            answer: "adv=1;fin=999999".into(),
        };
        let e = h.follow_once(&src, "999", true, &g).unwrap_err();
        assert!(matches!(
            e,
            HeadError::Source(MinaSourceError::Unavailable(_))
        ));
        assert_eq!(h, before);
    }

    /// A source that returns too few bytes to be a protocol state is refused before the gate.
    #[test]
    fn a_truncated_source_is_refused() {
        let src = StaticProtocolStateSource(vec![0u8; 8]);
        assert!(matches!(
            src.best_tip_protocol_state(),
            Err(MinaSourceError::Malformed(_))
        ));
        // 1544 is the measured size of devnet block 540186's protocol state.
        let ok = StaticProtocolStateSource(vec![0u8; 1544]);
        assert_eq!(ok.best_tip_protocol_state().unwrap().len(), 1544);
    }

    /// ⚑ `segment_ok = false` — what an unavailable anchored-segment gate supplies — reaches the
    /// gate as `sg=0`. The Lean side proves that moves nothing
    /// (`rollHead_fails_closed_without_the_segment`); this asserts Rust actually sends it.
    #[test]
    fn an_unverified_segment_is_sent_as_sg_zero() {
        let w = head_advance_wire(false, 100, "1", "2", &[0x01], &[0x02]);
        assert!(w.starts_with("sg=0;"), "{w}");
    }

    /// A gate that COUNTS how many times it was asked, so "never offered" is provable rather than
    /// asserted. A skip that still reaches the gate is not a skip.
    struct CountingGate {
        answer: String,
        calls: std::cell::Cell<usize>,
    }

    impl MinaForkChoiceGate for CountingGate {
        fn head_advance(&self, _wire: &str) -> Result<String, String> {
            self.calls.set(self.calls.get() + 1);
            Ok(self.answer.clone())
        }
        fn better_tip(&self, _wire: &str) -> Result<String, String> {
            self.calls.set(self.calls.get() + 1);
            Ok(self.answer.clone())
        }
    }

    fn cand(peer: &str, hash: &str, anchored: bool) -> MinaCandidateTip {
        MinaCandidateTip {
            protocol_state: vec![0xbb; 1544],
            state_hash: hash.into(),
            anchored,
            segment_ok: true,
            peer: peer.into(),
        }
    }

    /// ⚑ **THE UNANCHORED CANDIDATE NEVER REACHES THE RULE.** This is the whole point of reading
    /// the transition-chain proof: a tip whose merkle list does not fold from its peer's frontier
    /// root is not a weaker candidate, it is not a candidate. Proved by COUNTING gate calls, so a
    /// future refactor that "skips" it by offering it and ignoring the answer goes red here.
    #[test]
    fn an_unanchored_candidate_is_never_offered_to_the_fork_choice_gate() {
        let mut h = head();
        let before = h.clone();
        let g = CountingGate {
            answer: "adv=1;fin=999999".into(),
            calls: std::cell::Cell::new(0),
        };
        let set = [cand("peerA", "777", false), cand("peerB", "888", false)];
        let out = h.follow_candidate_set(&set, &g).unwrap();
        assert_eq!(g.calls.get(), 0, "an unanchored candidate reached the gate");
        assert_eq!(out.unanchored, 2);
        assert_eq!(out.offered, 0);
        assert_eq!(out.advanced, 0);
        assert_eq!(
            h, before,
            "the head moved on a set with no anchored candidate"
        );
    }

    /// ⚑ **A LOSING FORK IS REFUSED, AND THE RATCHET DOES NOT DROP.** The gate keeps the head; the
    /// walk must report `kept`, leave the head where it was, and never lower `finalized_height`.
    #[test]
    fn a_losing_fork_is_offered_refused_and_moves_nothing() {
        let mut h = head();
        let before = h.clone();
        let g = CountingGate {
            answer: "adv=0;fin=100".into(),
            calls: std::cell::Cell::new(0),
        };
        let set = [cand("peerA", "777", true), cand("peerB", "888", true)];
        let out = h.follow_candidate_set(&set, &g).unwrap();
        assert_eq!(g.calls.get(), 2, "both anchored candidates must be judged");
        assert_eq!(out.offered, 2);
        assert_eq!(out.kept, 2);
        assert_eq!(out.advanced, 0);
        assert_eq!(out.unanchored, 0);
        assert_eq!(h.protocol_state, before.protocol_state);
        assert_eq!(h.state_hash, before.state_hash);
        assert!(h.finalized_height >= before.finalized_height);
    }

    /// A mixed set: only the anchored members are judged, and the counts add up to the set size.
    #[test]
    fn only_the_anchored_members_of_a_set_are_judged() {
        let mut h = head();
        let g = CountingGate {
            answer: "adv=1;fin=539897".into(),
            calls: std::cell::Cell::new(0),
        };
        let set = [
            cand("peerA", "777", true),
            cand("peerB", "888", false),
            cand("peerC", "999", true),
        ];
        let out = h.follow_candidate_set(&set, &g).unwrap();
        assert_eq!(g.calls.get(), 2);
        assert_eq!(out.offered + out.unanchored, set.len());
        assert_eq!(out.unanchored, 1);
        assert_eq!(out.advanced, 2);
        assert_eq!(out.finalized_height, 539_897);
        assert_eq!(h.finalized_height, 539_897);
    }

    /// ⚑ An ABSENT archive refuses the whole set, and it refuses it on the FIRST anchored
    /// candidate rather than walking the rest and reporting a tidy zero.
    #[test]
    fn an_absent_gate_refuses_the_whole_candidate_set() {
        let mut h = head();
        let before = h.clone();
        let set = [cand("peerA", "777", true), cand("peerB", "888", true)];
        let e = h.follow_candidate_set(&set, &AbsentGate).unwrap_err();
        assert!(matches!(e, HeadError::VerifiedGateUnavailable(_)));
        assert_eq!(h, before);
    }

    /// ⚑ **`unjudged` DEFAULTS TO REFUSING.** A constructor whose defaults were `true` would make
    /// every caller that forgot a field into a fail-open.
    #[test]
    fn a_freshly_built_candidate_has_passed_nothing() {
        let c = MinaCandidateTip::unjudged(vec![0u8; 1544], "1", "peerA");
        assert!(!c.anchored, "anchored must default to the refusing value");
        assert!(
            !c.segment_ok,
            "segment_ok must default to the refusing value"
        );
    }

    /// ⚑ THE LIVE openmina PAIR, THROUGH THE LEAN BINPROT DECODER + SAMASIKA, OVER THE C ABI.
    ///
    /// This is the measured half of the byte-source transmutation. `bridge/tools/mina-tip` — which
    /// LINKS openmina's audited Rust p2p stack (`~/dev/mina-rust`) instead of a hand-written Python
    /// transport — captured a GENUINE consecutive devnet pair, 540478 → 540479, off `get_best_tip`
    /// v2 and `get_transition_chain` v2. Those exact bytes go here through `dregg_mina_better_tip`,
    /// which DECODES each `Protocol_state.Value` IN LEAN (`Dregg2.Bridge.MinaBinprot`) and runs
    /// Samasika `select`. A non-`ERR` verdict is proof the verified decoder read openmina's bytes;
    /// the one-block-longer child must be taken, the reverse presentation must not (`select_asymm`),
    /// and a tip must not displace itself (`select_irrefl`). REGENERATE the fixtures with
    /// `mina-tip pair --parent-out … --child-out …`.
    ///
    /// UNGATED like its sibling `mina_fork_choice_decides_on_real_devnet_bytes_through_the_real_ffi`:
    /// archive-absence routes through `demand_lean` (which PANICS under `DREGG_TEST_REQUIRE_LEAN=1`)
    /// rather than the test silently ceasing to check anything.
    ///
    /// ⚑ **THIS TEST WAS STRUCTURALLY UNPASSABLE UNTIL 2026-08-02, AND TWO OF ITS THREE
    /// ASSERTIONS WERE PASSING FOR THE WRONG REASON.** It passed `"1"` and `"2"` as the two
    /// sides' state hashes. Since 2026-07-30 `MinaForkChoiceGate.decodeSide?` RE-DERIVES each
    /// side's hash from its own bytes and returns `none` unless the wire's `eh=`/`ch=` field
    /// equals it, so every call here decoded to `"ERR"`. `verified_mina_better_tip` maps every
    /// non-`"1"` output to `KeepExisting` — correctly, fail-closed — which means the two
    /// assertions expecting `KeepExisting` (`select_irrefl`, `select_asymm`) were satisfied by a
    /// REFUSAL and would have stayed green with the decoder deleted. Only the third could fail,
    /// and the first time this test was actually run against an archive exporting the gate, it
    /// did.
    ///
    /// The hashes below are the REAL ones, as decimal field elements, printed by
    /// `mina-tip verify-pair` from these exact fixtures. `select_irrefl`/`select_asymm` now mean
    /// what their names say, because the sides now decode.
    #[test]
    fn the_live_openmina_pair_decodes_and_selects_through_the_real_lean_gate() {
        use dregg_lean_ffi::MinaForkChoiceVerdict;
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::mina_better_tip_available(),
            "dregg_mina_better_tip on the openmina-captured devnet pair",
        ) {
            return;
        }
        // Captured by `mina-tip` off openmina's stack; the same bytes `mina-tip verify-pair` checks.
        let parent = include_bytes!("../tools/fixtures/mina-pair-parent.bin").to_vec();
        let child = include_bytes!("../tools/fixtures/mina-pair-child.bin").to_vec();
        assert_eq!(
            parent.len(),
            1544,
            "openmina parent fixture is not the 1544-byte protocol state"
        );
        assert_eq!(
            child.len(),
            1544,
            "openmina child fixture is not the 1544-byte protocol state"
        );

        // ⚑ THE REAL STATE HASHES, as decimal field elements. `mina-tip verify-pair --parent
        // … --child …` prints exactly these two lines from exactly these two files. Anything
        // else and `decodeSide?` refuses the side and the gate answers `"ERR"`.
        const PARENT_HASH: &str =
            "11651804881993560809984162371324456189064676022942805929239967859377150046164";
        const CHILD_HASH: &str =
            "28710974526978334901564261647210572137992533146705698353351415462787901990308";

        // ⚑ NON-VACUITY CONTROL, FIRST. A WRONG hash must be REFUSED — otherwise every
        // `KeepExisting` below could be a refusal wearing a verdict's clothes, which is precisely
        // the defect this test had. `"1"` is the value the old test passed for both sides.
        assert_eq!(
            dregg_lean_ffi::verified_mina_better_tip("1", "1", &parent, &parent),
            Ok(MinaForkChoiceVerdict::KeepExisting),
            "a bogus served hash must not yield TakeCandidate"
        );
        assert_eq!(
            dregg_lean_ffi::verified_mina_better_tip("1", "2", &parent, &child),
            Ok(MinaForkChoiceVerdict::KeepExisting),
            "⚑ the served-hash check must REFUSE a pair labelled with hashes its bytes do not \
             have — if this ever returns TakeCandidate, decodeSide? has stopped re-deriving"
        );

        // A tip does not displace itself (select_irrefl) — the side DECODES and select says no.
        assert_eq!(
            dregg_lean_ffi::verified_mina_better_tip(PARENT_HASH, PARENT_HASH, &parent, &parent),
            Ok(MinaForkChoiceVerdict::KeepExisting),
            "a tip must not displace itself"
        );
        // The one-block-longer child (540479) decodes under Lean and wins select over 540478.
        assert_eq!(
            dregg_lean_ffi::verified_mina_better_tip(PARENT_HASH, CHILD_HASH, &parent, &child),
            Ok(MinaForkChoiceVerdict::TakeCandidate),
            "the live openmina child must decode under the Lean binprot decoder and win select"
        );
        // Reverse presentation must not also win (select_asymm).
        assert_eq!(
            dregg_lean_ffi::verified_mina_better_tip(CHILD_HASH, PARENT_HASH, &child, &parent),
            Ok(MinaForkChoiceVerdict::KeepExisting),
            "presentation order must not make both sides win"
        );
    }
}
