//! # `mina_opening_check` — **the callable path that proves dregg verified a Mina block's
//! `⟨s, srs.g⟩` opening leg.**
//!
//! ## Substrate, said out loud
//!
//! **The AIR is LEAN-AUTHORED.** The four descriptors this module resolves are
//! `Dregg2.Circuit.Emit.PastaMsmScalarDerive.deriveRowDesc 15 10922 k 3 256 MinaWrapSrsG.SRS_G`
//! at `k = 0, 3640, 7281, 10921`, emitted by `metatheory/EmitPastaDerive.lean` — 1309 constraints
//! / 2131 columns / 164 public inputs / 1024 rows each. **Nothing in this file, and nothing in
//! [`dregg_circuit::mina_opening_witness`], authors a constraint, a `Builder` gadget or an
//! `air_accepts` predicate.** Rust parses the emitted bytes, fills trace CELLS, and calls the
//! deployed prover and the deployed verifier.
//!
//! ## The gap this closes
//!
//! Measured 2026-07-30: `grep -rln "pasta-rcb-sg|PastaMsm|minaOpeningCheck" node/ bridge/src/
//! circuit-prove/src/ dregg-lean-ffi/src/` was **EMPTY**. dregg had a circuit that forces Mina's
//! real Wrap SRS generators, forces the block's own CANONICAL s-vector from its 15 IPA challenges,
//! forces both operands onto the curve, folds them with the actual group law and refuses five
//! distinct forgeries — and no node, bridge or prover path ever invoked it. It was a proof we
//! could produce and never ask for. [`prove_block_opening_check`] is the ask.
//!
//! ## ⚑⚑ WHERE THE CHALLENGES COME FROM, and the measurement that decided it
//!
//! The 15 IPA challenges are **public inputs** (slots 29..163) — `PastaMsmScalarDerive`'s
//! `chalPinGates` binds them to the wire, so the party that supplies them is the VERIFIER, not
//! the prover and not the emitter. So a runtime path has to get them from somewhere, and the
//! obvious somewhere is the block. **It is not there.**
//!
//! MEASURED, on the six real devnet blocks in `metatheory/mina_state_hash_binding.json`
//! (539508 and 539795–539799), against `MinaWrapOpeningGate.IPA_PRECHALS` — block 539508's actual
//! 15 raw IPA prechallenges:
//!
//! ```text
//!   IPA_PRECHALS == block.mnw_raw_chals[0..15]        0 / 6
//!   IPA_PRECHALS == block.mnw_raw_chals[15..30]       0 / 6
//!   IPA_PRECHALS == block.bulletproof_challenges[..]  0 / 6
//! ```
//!
//! A Wrap proof's own IPA opening challenges are Fiat–Shamir outputs of **its own transcript**:
//! `MinaWrapOpeningGate` derives them by picking the phase-1 sponge up at the state `SRS::verify`
//! receives it in and running it forward through `absorb_fr(shift_scalar(cip))`, `challenge_fq`,
//! the 15 `absorb_g(L)/absorb_g(R)/squeeze` rounds and `absorb_g(delta)`. That needs the verifier
//! index, the SRS and the 47 commitments — none of which are on the wire, and the in-kernel cost
//! is 153 s per block. They are consequently **not decodable**, and a runtime path cannot invent
//! them.
//!
//! (Incidental, and it corroborates the decode: `mnw_raw_chals[15..30]` is IDENTICAL across all
//! four adjacent pairs 539795→539799 while `[0..15]` moves — the transaction-SNARK accumulator's
//! half, exactly as [`crate::mina_pickles::WrapProofShape::acc_comm`] documents for `[1]`.)
//!
//! ### So the resolution is PINNED, and that is the fail-closed choice
//!
//! [`PINNED_CHALLENGES`] carries the challenge vector for the ONE height whose transcript this
//! tree has actually run — devnet **539508**, `MinaWrapOpeningGate.CHAL_F`, emitted by
//! `metatheory/EmitPastaDeriveChals.lean` and sha256-pinned below. Every other height returns
//! [`MinaOpeningCheckError::ChallengesUnavailable`] and **proves nothing**. That is deliberate:
//! proving the MSM over a challenge vector nobody derived from the block would be a green badge
//! for an unbound statement, which is worse than a refusal.
//!
//! What binds the *served* block to that pinned vector is [`MinaObserver::check_header_binding`],
//! which recomputes public-input words 12 and 11 from the served `stateHash` and the served proof
//! bytes through the verified Lean gate and refuses a re-labelled proof.
//! [`MinaObserver::prove_opening_check`] runs it FIRST and will not prove without it.
//!
//! ## How the DESCRIPTOR is resolved, and why that way
//!
//! Compiled in, byte-pinned, no filesystem read: `include_str!` of
//! `metatheory/emitted/mina-opening/*.json`, with the sha256 of every artifact checked on the way
//! in ([`MinaOpeningCheckError::ArtifactDrift`]) and every number of the emitted shape re-asserted
//! against the parsed object ([`MinaOpeningCheckError::DescriptorShapeMismatch`]).
//!
//! **Why not `circuit/descriptors/by-name/`.** `scripts/emit_descriptors.py` stamps that tree with
//! `DESC.rglob("*")` and `--verify-by-name-routing` demands an emitter for every file it finds, so
//! landing there would drag `MinaWrapSrsG`'s **32,768 pinned SRS points** into the drift gate's hot
//! path on every `check-descriptor-drift.sh` run. Their drift gate is instead
//! `scripts/regen-pasta-derive.sh --check`, which re-emits from Lean on hbox and diffs — the same
//! guarantee, off the hot path.
//!
//! **The cost, stated:** 4 × ~1.44 MB of JSON as `&'static str` in `dregg-bridge`'s rodata, and a
//! parse on every call. Both are measured and reported in the receipt
//! ([`MinaOpeningCheckReceipt::descriptor_bytes`], `resolve`), never remembered.
//!
//! ## Fail closed
//!
//! Every arm of [`MinaOpeningCheckError`] is a refusal. There is no accept path that skips a
//! check, no `Option` that degrades to "proved nothing, returned Ok", and no logging-and-proceeding
//! — the class this repo names `minted-fail-open-gate-class`. In particular
//! [`MinaOpeningCheckError::ChallengesUnavailable`] (we cannot ask) is a DIFFERENT variant from
//! [`MinaOpeningCheckError::ProofRefused`] (we asked and the prover said no), the same distinction
//! [`crate::mina_observer::ObserveError::VerifiedGateUnavailable`] draws against
//! `WrapProofNotChained`.

use std::time::{Duration, Instant};

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, parse_vm_descriptor2, prove_vm_descriptors2_batch,
    verify_vm_descriptors2_batch,
};
use dregg_circuit::mina_opening_witness::{
    self as opening, DERIVE_CONSTRAINTS, DERIVE_PI_COUNT, DERIVE_WIDTH, HEIGHT, KS,
};
use dregg_circuit::pasta_windowed_witness::U256;
use sha2::{Digest, Sha256};

// =================================================================================================
// The Lean-emitted artifacts, byte-pinned
// =================================================================================================

/// One embedded Lean-emitted artifact and the sha256 this build was written against.
#[derive(Clone, Copy, Debug)]
pub struct PinnedArtifact {
    /// The file name under `metatheory/emitted/mina-opening/`.
    pub name: &'static str,
    /// Its bytes, compiled in.
    pub json: &'static str,
    /// The sha256 `scripts/regen-pasta-derive.sh` last produced.
    pub sha256: &'static str,
}

/// The four SCALAR-DERIVED descriptors of the proved cut, in `KS` order.
///
/// ⚑ The pins ARE the gate. A re-emit turns [`resolve_descriptors`] red until they are re-pinned;
/// that is the intended failure mode, and it is the same pin
/// `circuit/tests/pasta_derive_prove.rs::lean_artifacts_are_pinned` carries.
pub const DESCRIPTORS: [PinnedArtifact; 4] = [
    PinnedArtifact {
        name: "pasta-rcb-sg-derive-0-of-10922.json",
        json: include_str!(
            "../../metatheory/emitted/mina-opening/pasta-rcb-sg-derive-0-of-10922.json"
        ),
        sha256: "b45b12f9e043d2c6e2b5acc6a623ffc00d05f71a4185ac20083d16113ea5e649",
    },
    PinnedArtifact {
        name: "pasta-rcb-sg-derive-3640-of-10922.json",
        json: include_str!(
            "../../metatheory/emitted/mina-opening/pasta-rcb-sg-derive-3640-of-10922.json"
        ),
        sha256: "1ae911d2a38054fba124729eda8d56e6b2fafc139c37b8d07b981bf03e92ebbf",
    },
    PinnedArtifact {
        name: "pasta-rcb-sg-derive-7281-of-10922.json",
        json: include_str!(
            "../../metatheory/emitted/mina-opening/pasta-rcb-sg-derive-7281-of-10922.json"
        ),
        sha256: "0c4148a144f7cfe799ce1ba9c5ead81d30907fa2ebbac3b21b615f2ad4477631",
    },
    PinnedArtifact {
        name: "pasta-rcb-sg-derive-10921-of-10922.json",
        json: include_str!(
            "../../metatheory/emitted/mina-opening/pasta-rcb-sg-derive-10921-of-10922.json"
        ),
        sha256: "95a94ccb0869dfd6b98970c013557be7a716936c72ede5e9886e9dcb8bbf0d89",
    },
];

/// A challenge vector pinned to a block height, with its provenance stated.
#[derive(Clone, Copy, Debug)]
pub struct PinnedChallenges {
    /// The devnet block height these challenges belong to.
    pub block_height: u64,
    /// The emitted artifact.
    pub artifact: PinnedArtifact,
    /// **Where the vector came from** — this is the load-bearing field, not decoration. A caller
    /// reading a receipt needs to know whether the challenges were derived from the block or
    /// asserted about it.
    pub provenance: &'static str,
}

/// ⚑ **The whole pinned set — ONE height.** Say the scope out loud: the opening check is provable
/// at exactly the height whose Fiat–Shamir transcript this tree has run in-kernel. Anything else
/// is [`MinaOpeningCheckError::ChallengesUnavailable`].
pub const PINNED_CHALLENGES: [PinnedChallenges; 1] = [PinnedChallenges {
    block_height: 539_508,
    artifact: PinnedArtifact {
        name: "chals-block0.json",
        json: include_str!("../../metatheory/emitted/mina-opening/chals-block0.json"),
        sha256: "69b820d49b2b29d0e17c5569ae174a7a7f4964baf97b5ff51af3d2ac7d8bcaff",
    },
    provenance: "Dregg2.Circuit.Emit.MinaWrapOpeningGate.CHAL_F — devnet block 539508's own 15 \
                 IPA prechallenges, derived by running the block's Fq sponge forward in the Lean \
                 kernel (`ipaTranscript CIP_SHIFTED LR_XY DELTA_XY == (T_FQ, IPA_PRECHALS, C_PRE)`) \
                 and lifted through `endoMap ENDO_R` (`derived_ipa_challenges`). NOT on the wire; \
                 see this module's header for the 0/6 measurement.",
}];

/// ⚑ **A DIFFERENT BLOCK'S CHALLENGE VECTOR — a counter-example, never a production input.**
///
/// `metatheory/EmitPastaDeriveChals.lean 1`: the same vector with one round's challenge bumped,
/// i.e. a vector that is well-formed, is a real 15-tuple of reduced Pallas scalars, and is simply
/// **not this block's**. It exists so the falsifier can fire THROUGH the wiring rather than only in
/// the circuit crate's unit tests: handed to [`prove_block_opening_check`] it must be REFUSED.
///
/// Public for the same reason [`dregg_circuit::pasta_windowed_witness::put_on_curve_block_forged`]
/// is: a falsifier that cannot build the best forgery measures nothing.
#[doc(hidden)]
pub const COUNTER_EXAMPLE_CHALLENGES: PinnedArtifact = PinnedArtifact {
    name: "chals-block1.json",
    json: include_str!("../../metatheory/emitted/mina-opening/chals-block1.json"),
    sha256: "3a8bb88fe2cdea76c039491a341b11849884461d41400656efa59ffc6e8e693a",
};

// =================================================================================================
// Refusals
// =================================================================================================

/// **Every arm is a refusal.** Nothing here degrades to a warning or an accept.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MinaOpeningCheckError {
    /// An embedded Lean-emitted artifact is not the one this build was pinned against. A silent
    /// re-emit cannot slide under a green runtime.
    ArtifactDrift {
        /// The artifact's file name.
        artifact: &'static str,
        /// The sha256 the pin declares.
        want: &'static str,
        /// The sha256 the compiled-in bytes actually have.
        got: String,
    },
    /// The deployed IR-v2 checker could not parse an emitted descriptor.
    DescriptorMalformed {
        /// The artifact's file name.
        artifact: &'static str,
        /// What the parser said.
        why: String,
    },
    /// A parsed descriptor is not the emitted shape this path knows how to witness — a different
    /// width, constraint count, PI count, name or manifest height. Refused rather than witnessed
    /// on a guess.
    DescriptorShapeMismatch {
        /// The artifact's file name.
        artifact: &'static str,
        /// Which number moved.
        why: String,
    },
    /// ⚑ **NOTHING WAS DECIDED.** No challenge vector is pinned for this height, and a Wrap
    /// proof's own IPA challenges are not on its wire (see the module header's 0/6 measurement).
    /// Deliberately NOT [`Self::ProofRefused`]: that one means the prover ran and said no.
    ChallengesUnavailable {
        /// The height that was asked for.
        block_height: u64,
        /// The heights that are pinned.
        pinned_heights: Vec<u64>,
    },
    /// The pinned challenge JSON did not parse as 15 reduced Pallas scalars.
    ChallengesMalformed {
        /// What the parser said.
        why: String,
    },
    /// ⚑ **THE CHALLENGES DID NOT PRODUCE THIS DESCRIPTOR.** The manifest's declared digit column
    /// is not the s-vector of the supplied challenge vector, or the trace could not be assembled.
    /// This fires BEFORE the prover, so a wrong challenge vector is a legible refusal rather than
    /// an opaque `LookupError`.
    WitnessRefused {
        /// Which slice, and why.
        why: String,
    },
    /// The deployed prover refused — including its unconditional producer-side self-verify, which
    /// is what turns a green prove into a verify.
    ProofRefused {
        /// The prover's message.
        why: String,
    },
    /// The deployed verifier refused a proof the prover produced. Distinct from
    /// [`Self::ProofRefused`] because it would mean the two disagree, which is a different and
    /// much louder fact.
    VerifyRefused {
        /// The verifier's message.
        why: String,
    },
}

impl std::fmt::Display for MinaOpeningCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ArtifactDrift {
                artifact,
                want,
                got,
            } => write!(
                f,
                "the Lean-emitted artifact `{artifact}` drifted: pinned {want}, compiled-in bytes \
                 hash to {got}. Re-read the Lean and re-pin (scripts/regen-pasta-derive.sh)"
            ),
            Self::DescriptorMalformed { artifact, why } => write!(
                f,
                "the deployed IR-v2 checker refused to parse `{artifact}`: {why}"
            ),
            Self::DescriptorShapeMismatch { artifact, why } => write!(
                f,
                "`{artifact}` is not the emitted shape this witness builder knows: {why}"
            ),
            Self::ChallengesUnavailable {
                block_height,
                pinned_heights,
            } => write!(
                f,
                "REFUSED, nothing decided: no IPA challenge vector is pinned for Mina block \
                 {block_height} (pinned: {pinned_heights:?}). A Wrap proof's own opening \
                 challenges are Fiat-Shamir outputs of its own transcript and are NOT on the \
                 wire (measured 0/6 against IPA_PRECHALS on six real devnet blocks), so this \
                 path will not invent them and proves nothing here"
            ),
            Self::ChallengesMalformed { why } => {
                write!(f, "the pinned challenge vector is malformed: {why}")
            }
            Self::WitnessRefused { why } => write!(
                f,
                "REFUSED before proving: {why} — the supplied challenge vector did not produce \
                 this Lean-emitted descriptor, so the instance has no satisfying trace"
            ),
            Self::ProofRefused { why } => write!(
                f,
                "the LEAN-AUTHORED opening-check AIR REFUSED this block's witness: {why}"
            ),
            Self::VerifyRefused { why } => write!(
                f,
                "the DEPLOYED VERIFIER refused a proof the prover produced (prover and verifier \
                 disagree, which is far worse than a refusal): {why}"
            ),
        }
    }
}

impl std::error::Error for MinaOpeningCheckError {}

// =================================================================================================
// The receipt
// =================================================================================================

/// What a successful [`prove_block_opening_check`] returns. Every cost figure is MEASURED on the
/// call that produced it, never a remembered number.
#[derive(Clone, Debug)]
pub struct MinaOpeningCheckReceipt {
    /// The Mina block height the challenge vector is pinned to.
    pub block_height: u64,
    /// The descriptor names proved, in `KS` order.
    pub descriptor_names: Vec<String>,
    /// Total bytes of compiled-in descriptor JSON parsed on this call.
    pub descriptor_bytes: usize,
    /// The challenge vector's provenance, carried forward so a reader of the receipt cannot mistake
    /// a pinned vector for a decoded one.
    pub challenge_provenance: &'static str,
    /// sha256 of the challenge artifact actually used.
    pub challenges_sha256: String,
    /// Trace cells across the whole cut (`slices × rows × columns`).
    pub cells: usize,
    /// The batch proof, postcard-serialized — a transportable receipt, and what `proof_bytes`
    /// measures.
    pub proof: Vec<u8>,
    /// Wall time to sha-check and parse the four descriptors.
    pub resolve: Duration,
    /// Wall time to build the four traces and their public inputs.
    pub witness: Duration,
    /// Wall time in `prove_vm_descriptors2_batch` (which self-verifies unconditionally).
    pub prove: Duration,
    /// Wall time in `verify_vm_descriptors2_batch`.
    pub verify: Duration,
}

impl MinaOpeningCheckReceipt {
    /// Total wall time of the call.
    pub fn total(&self) -> Duration {
        self.resolve + self.witness + self.prove + self.verify
    }

    /// A one-line cost summary, for a driver that wants to print rather than format.
    pub fn cost_line(&self) -> String {
        format!(
            "block {} | {} slices x {HEIGHT} x {DERIVE_WIDTH} = {} cells | descriptors {} B \
             resolve {:?} | witness {:?} | prove {:?} | verify {:?} | proof {} B | total {:?}",
            self.block_height,
            KS.len(),
            self.cells,
            self.descriptor_bytes,
            self.resolve,
            self.witness,
            self.prove,
            self.verify,
            self.proof.len(),
            self.total(),
        )
    }
}

// =================================================================================================
// Resolution
// =================================================================================================

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    h.finalize().iter().map(|b| format!("{b:02x}")).collect()
}

fn check_pin(a: &PinnedArtifact) -> Result<(), MinaOpeningCheckError> {
    let got = sha256_hex(a.json.as_bytes());
    if got != a.sha256 {
        return Err(MinaOpeningCheckError::ArtifactDrift {
            artifact: a.name,
            want: a.sha256,
            got,
        });
    }
    Ok(())
}

/// **Resolve the four Lean-emitted descriptors**: sha-check the compiled-in bytes, parse them with
/// the deployed IR-v2 checker, and re-assert every number of the emitted shape.
///
/// No filesystem read, no network, no fallback. A drifted or misshapen artifact is a refusal.
pub fn resolve_descriptors() -> Result<Vec<EffectVmDescriptor2>, MinaOpeningCheckError> {
    let mut out = Vec::with_capacity(DESCRIPTORS.len());
    for (i, a) in DESCRIPTORS.iter().enumerate() {
        check_pin(a)?;
        let d = parse_vm_descriptor2(a.json).map_err(|why| {
            MinaOpeningCheckError::DescriptorMalformed {
                artifact: a.name,
                why,
            }
        })?;
        let bad = |why: String| MinaOpeningCheckError::DescriptorShapeMismatch {
            artifact: a.name,
            why,
        };
        let want_name = opening::descriptor_name(KS[i]);
        if d.name != want_name {
            return Err(bad(format!("name is `{}`, expected `{want_name}`", d.name)));
        }
        if d.trace_width != DERIVE_WIDTH {
            return Err(bad(format!(
                "trace width {} is not PastaMsmScalarDerive.WD = {DERIVE_WIDTH}",
                d.trace_width
            )));
        }
        if d.public_input_count != DERIVE_PI_COUNT {
            return Err(bad(format!(
                "public input count {} is not 29 + 9*15 = {DERIVE_PI_COUNT}",
                d.public_input_count
            )));
        }
        if d.constraints.len() != DERIVE_CONSTRAINTS {
            return Err(bad(format!(
                "constraint count {} is not {DERIVE_CONSTRAINTS}",
                d.constraints.len()
            )));
        }
        let manifest = opening::manifest_of(&d).map_err(bad)?;
        if manifest.len() != HEIGHT {
            return Err(bad(format!(
                "manifest has {} rows, expected {HEIGHT}",
                manifest.len()
            )));
        }
        out.push(d);
    }
    Ok(out)
}

/// The pinned challenge vector for a Mina block height, or `None`.
///
/// ⚑ `None` is the fail-closed answer, and every caller must treat it as a refusal — never as
/// "carry on without". This is the `descriptor_by_name` discipline: a miss returns nothing, never
/// a stand-in.
pub fn pinned_challenges_for(block_height: u64) -> Option<&'static PinnedChallenges> {
    PINNED_CHALLENGES
        .iter()
        .find(|p| p.block_height == block_height)
}

/// The heights a challenge vector is pinned for.
pub fn pinned_heights() -> Vec<u64> {
    PINNED_CHALLENGES.iter().map(|p| p.block_height).collect()
}

// =================================================================================================
// ⚑⚑ THE ASK
// =================================================================================================

/// ⚑⚑ **Prove — and verify — Mina's `⟨s, srs.g⟩` opening leg for `block_height`.**
///
/// The whole path, fail-closed at every step:
///
/// 1. resolve the four LEAN-AUTHORED descriptors (sha-pinned, shape-checked);
/// 2. resolve the pinned challenge vector for this height, or REFUSE
///    ([`MinaOpeningCheckError::ChallengesUnavailable`]);
/// 3. cross-check the descriptors' manifests against those challenges — the s-vector recomputed
///    row by row — and build the four traces and public-input vectors;
/// 4. run the DEPLOYED prover, whose unconditional producer-side self-verify means a green prove
///    IS a verify;
/// 5. run the DEPLOYED verifier on the produced proof anyway, so the receipt is a verified one.
///
/// What a returned receipt says, stated at its real resolution: *for the 15 IPA challenges of
/// devnet block 539508, four chosen 3-generator slices of Mina's real 32,768-point Wrap SRS fold,
/// under the canonical s-vector those challenges derive, to the published accumulator values —
/// and a STARK proof of that was produced and checked.* It does **not** say the whole `⟨s, srs.g⟩`
/// MSM holds (12 of 32,768 generators are bound), and it does not discharge the FRI/STARK
/// soundness floor beneath the proof system itself.
pub fn prove_block_opening_check(
    block_height: u64,
) -> Result<MinaOpeningCheckReceipt, MinaOpeningCheckError> {
    let pinned = pinned_challenges_for(block_height).ok_or_else(|| {
        MinaOpeningCheckError::ChallengesUnavailable {
            block_height,
            pinned_heights: pinned_heights(),
        }
    })?;
    check_pin(&pinned.artifact)?;
    let chals = opening::parse_challenges(pinned.artifact.json)
        .map_err(|why| MinaOpeningCheckError::ChallengesMalformed { why })?;
    prove_opening_check_with_challenges(block_height, pinned, &chals)
}

/// [`prove_block_opening_check`] with the challenge vector supplied explicitly.
///
/// ⚑ **NOT a production entry point.** It exists so a falsifier can drive the REAL wiring with a
/// challenge vector that is well-formed and simply not this block's, and watch it refuse —
/// otherwise the runtime path's only red arm would be one nothing exercises. The production entry
/// is [`prove_block_opening_check`], which sources the vector from [`PINNED_CHALLENGES`] and from
/// nowhere else.
#[doc(hidden)]
pub fn prove_opening_check_with_challenges(
    block_height: u64,
    pinned: &PinnedChallenges,
    chals: &[U256],
) -> Result<MinaOpeningCheckReceipt, MinaOpeningCheckError> {
    let t_resolve = Instant::now();
    let descs = resolve_descriptors()?;
    let resolve = t_resolve.elapsed();
    let descriptor_bytes: usize = DESCRIPTORS.iter().map(|a| a.json.len()).sum();

    // (3) the manifests ARE this challenge vector's s-vector — checked on the bytes, row by row,
    //     before a prover is entered. `build_opening_cut` refuses otherwise.
    let t_witness = Instant::now();
    let (traces, pis) = opening::build_opening_cut(&descs, chals)
        .map_err(|why| MinaOpeningCheckError::WitnessRefused { why })?;
    let witness = t_witness.elapsed();

    // (4) the DEPLOYED prover. `prove_vm_descriptors2_batch` self-verifies unconditionally.
    let refs: Vec<&[Vec<BabyBear>]> = traces.iter().map(|t| t.as_slice()).collect();
    let t_prove = Instant::now();
    let proof = prove_vm_descriptors2_batch(&descs, &refs, &pis)
        .map_err(|why| MinaOpeningCheckError::ProofRefused { why })?;
    let prove = t_prove.elapsed();

    // (5) …and the DEPLOYED verifier on the object it produced.
    let t_verify = Instant::now();
    verify_vm_descriptors2_batch(&descs, &proof, &pis)
        .map_err(|why| MinaOpeningCheckError::VerifyRefused { why })?;
    let verify = t_verify.elapsed();

    let bytes =
        postcard::to_allocvec(&proof).map_err(|e| MinaOpeningCheckError::VerifyRefused {
            why: format!("the verified proof did not serialize: {e}"),
        })?;

    Ok(MinaOpeningCheckReceipt {
        block_height,
        descriptor_names: descs.iter().map(|d| d.name.clone()).collect(),
        descriptor_bytes,
        challenge_provenance: pinned.provenance,
        challenges_sha256: sha256_hex(pinned.artifact.json.as_bytes()),
        cells: opening::cut_cells(),
        proof: bytes,
        resolve,
        witness,
        prove,
        verify,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The compiled-in artifacts are the ones this module was written against, and the deployed
    /// checker parses them into the emitted shape. Cheap, and it is the pin.
    #[test]
    fn the_embedded_lean_artifacts_are_pinned_and_parse() {
        let descs = resolve_descriptors().expect("the pinned descriptors must resolve");
        assert_eq!(descs.len(), KS.len());
        for (i, d) in descs.iter().enumerate() {
            assert_eq!(d.name, opening::descriptor_name(KS[i]));
        }
        for p in &PINNED_CHALLENGES {
            check_pin(&p.artifact).expect("the pinned challenge vector must not have drifted");
            let cs = opening::parse_challenges(p.artifact.json).expect("15 reduced Pallas scalars");
            assert_eq!(cs.len(), 15);
        }
        check_pin(&COUNTER_EXAMPLE_CHALLENGES).expect("the counter-example must not have drifted");
        println!(
            "[resolve] {} descriptors, {} B compiled in, pinned heights {:?}",
            descs.len(),
            DESCRIPTORS.iter().map(|a| a.json.len()).sum::<usize>(),
            pinned_heights()
        );
    }

    /// ⚑ **THE FAIL-CLOSED ARM, on the runtime path.** A height with no pinned challenge vector
    /// proves NOTHING and says so with its own variant — it does not fall back, log, or return an
    /// `Ok` that means "checked nothing".
    #[test]
    fn an_unpinned_height_is_refused_and_nothing_is_proved() {
        for h in [0u64, 1, 539_507, 539_509, 539_795, u64::MAX] {
            match prove_block_opening_check(h) {
                Err(MinaOpeningCheckError::ChallengesUnavailable {
                    block_height,
                    pinned_heights,
                }) => {
                    assert_eq!(block_height, h);
                    assert_eq!(pinned_heights, vec![539_508]);
                }
                other => panic!("height {h} must be REFUSED as unavailable, got {other:?}"),
            }
        }
    }

    /// The counter-example vector really is a different block's — otherwise the falsifier in
    /// `mina_observer` would be measuring nothing.
    #[test]
    fn the_counter_example_challenges_are_a_different_blocks() {
        let a = opening::parse_challenges(PINNED_CHALLENGES[0].artifact.json).expect("block A");
        let b = opening::parse_challenges(COUNTER_EXAMPLE_CHALLENGES.json).expect("block B");
        assert_ne!(a, b, "the counter-example must actually differ");
        let moved = a.iter().zip(b.iter()).filter(|(x, y)| x != y).count();
        assert_eq!(moved, 1, "exactly one round's challenge is bumped");
        // …and it moves the s-vector, which is what the manifest cross-check reads.
        let differing = (0..8)
            .filter(|i| {
                dregg_circuit::pasta_windowed_witness::derive_scalar(&a, *i)
                    != dregg_circuit::pasta_windowed_witness::derive_scalar(&b, *i)
            })
            .count();
        assert!(
            differing > 0,
            "the two vectors must derive different s-vectors"
        );
        println!("[counter] 1 of 15 challenges moved; {differing} of the first 8 s-entries move");
    }
}
