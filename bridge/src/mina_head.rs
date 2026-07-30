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
//! ⚑ **The in-repo socket implementation is a SUBPROCESS, and that is on purpose.** The protocol is
//! `TCP → pnet(XSalsa20 under the chain-id PSK) → multistream-select → Noise XX → /coda/yamux/1.0.0
//! → coda/rpcs/0.0.1 → get_best_tip v2`. openmina is a complete Rust implementation of exactly that
//! and it is on this machine; hand-writing Salsa20, a Noise XX state machine and a yamux muxer into
//! this crate would be reconstructing a thing that already exists, which is the same mistake as a
//! Rust binprot decoder wearing different clothes. [`CommandProtocolStateSource`] runs an
//! operator-configured helper and takes its stdout. The helper shipped here is
//! `bridge/tools/mina-besttip.py` — a small Python client, deliberately not a second Rust
//! implementation of a stack openmina already implements.
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
/// The helper speaks Mina's peer-to-peer stack. `bridge/tools/mina-besttip.py --emit-protocol-state`
/// is the one this was built against and the one measured: it connects to a devnet seed, negotiates
/// pnet / Noise XX / yamux / `coda/rpcs/0.0.1`, issues `get_best_tip` v2, and writes the response
/// payload from the Option tag onward to stdout.
///
/// ⚑ That helper is a small dependency-light Python client, NOT audited crypto and NOT the
/// production path. openmina (`~/dev/mina-rust`) is a complete, maintained Rust implementation of
/// the same stack and is what to link when this leaves `tools/`. Naming the real thing here rather
/// than implying a Rust helper exists: it does not.
///
/// ⚑ The helper is TRUSTED FOR AVAILABILITY ONLY, not for content. It cannot make the client accept
/// a chain: every byte it produces goes through the Lean decoder's canonicality, bound and
/// carried-constants refusals and then through `select`. The worst a malicious helper achieves is
/// to be refused, or to withhold — and withholding is the one thing no light client can be
/// defended against by any means.
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
            program: PathBuf::from("/nonexistent/mina-besttip"),
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
}
