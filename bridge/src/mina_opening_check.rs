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

/// ⚑ **THE REFERENCE SET — one height, and since 2026-07-30 it is a COMPARAND, not a SOURCE.**
///
/// This used to be the only way a challenge vector could reach the prover, and every other height
/// was a refusal *because it was not in this table*. That is no longer the shape:
/// [`derive_challenges_for_block`] runs the per-block derivation for EVERY height, this vector is
/// what the derivation is CHECKED AGAINST at the one height where both exist
/// ([`MinaOpeningCheckError::DerivationDisagreesWithReference`]), and a height's absence from the
/// table is not by itself a reason to refuse anything.
///
/// It remains a fallback source at its own height while the derivation's remaining legs land, and
/// the receipt says which one produced the vector ([`MinaOpeningCheckReceipt::challenge_provenance`])
/// — never both silently.
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
    /// ⚑ **NOTHING WAS DECIDED.** The per-block derivation could not run to the end, and no
    /// reference vector exists for this height either.
    ///
    /// ⚑ The payload is a STAGE, not a height table, and that is the change of 2026-07-30. The old
    /// shape said "no challenge vector is pinned for this height" — which described a lookup, so
    /// every height that missed the table was one undifferentiated refusal and the reader could
    /// not tell a missing config constant from an unmeasured sponge from a routing decision.
    /// [`DerivationStage`] names which leg stopped, per block.
    ///
    /// Deliberately NOT [`Self::ProofRefused`]: that one means the prover ran and said no.
    ChallengesUnavailable {
        /// The height that was asked for.
        block_height: u64,
        /// ⚑ Which leg of the per-block derivation could not run.
        stage: DerivationStage,
        /// What the leg said.
        why: String,
    },
    /// ⚑ **THE DERIVATION AND THE REFERENCE VECTOR DISAGREE.** Reachable only at a height that has
    /// both, and it is the loudest refusal in this file: it means the compiled per-block path and
    /// the in-kernel one produced different challenges for the same block, so at least one of them
    /// is wrong about what a Mina Wrap transcript is.
    DerivationDisagreesWithReference {
        /// The height where they disagreed.
        block_height: u64,
        /// How many of the fifteen differ.
        differing: usize,
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
                stage,
                why,
            } => write!(
                f,
                "REFUSED, nothing decided: the per-block IPA challenge derivation for Mina block \
                 {block_height} stopped at {stage} — {why}. A Wrap proof's own opening challenges \
                 are Fiat-Shamir outputs of its own transcript, so this path will not invent them \
                 and proves nothing here"
            ),
            Self::DerivationDisagreesWithReference {
                block_height,
                differing,
            } => write!(
                f,
                "the per-block DERIVATION and the in-kernel REFERENCE vector disagree at Mina \
                 block {block_height} on {differing} of 15 challenges. One of the two is wrong \
                 about what a Wrap transcript is; nothing is proved until that is settled"
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
// TRUSTED CONFIG, named where a reader trips over it
// =================================================================================================

/// ⚑ **`index.digest::<EFqSponge>()` of the devnet blockchain Wrap verifier index.**
///
/// One `Fp` element, and the largest trusted object under this whole story: it is the compressed
/// form of the 56 `VK_INDEX` elements and it is the FIRST thing the phase-1 sponge absorbs. A wrong
/// digest produces a complete, self-consistent, entirely wrong challenge vector and nothing
/// downstream can tell. Same value as `Dregg2.Circuit.Emit.MinaRealBlockTranscript.VKDIGEST`.
pub const WRAP_VK_DIGEST: &str =
    "27413372650305777331568266454809682207773200268004525410015286142538704636274";

/// ⚑ **Pallas's `endo_r`** — the scalar the `ScalarChallenge` lift multiplies by
/// (`Dregg2.Circuit.Emit.PastaCurve.lambdaPallas`). CONFIG, carried so the wire record is complete;
/// the derivation returns RAW prechallenges and the lift is the consumer's.
pub const PALLAS_ENDO_R: &str =
    "26005156700822196841419187675678338661165322343552424574062261873906994770353";

// =================================================================================================
// ⚑⚑ THE PER-BLOCK DERIVATION — the thing that replaces a height table
// =================================================================================================

/// ⚑ **Which leg of the per-block derivation a refusal stopped at.**
///
/// The point of naming these is that they are NOT the same kind of missing. One is a config
/// constant somebody has to extract; one is a sponge nobody has welded to a real block; one is a
/// topology decision about a dependency graph. A single `ChallengesUnavailable` per height said
/// none of that, and a reader could not tell how far from done the path was.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DerivationStage {
    /// The block's decoded proof did not supply an argument the derivation needs — a shape the
    /// decoder walks past today rather than keeping.
    WireIncomplete,
    /// The STEP side's `ft_eval0`, which produces public-input word 0 and therefore the whole
    /// public input. ⚑ Blocked on ONE config object: the seven Tick coset `shifts` at
    /// `domain_log2 = 16`. They are Blake2b-derived per domain
    /// (`kimchi/src/circuits/polynomials/permutation.rs` `Shifts::new`), so this is an extractor
    /// line against openmina's Step verifier index, not a formalization.
    /// `Dregg2.Bridge.MinaWrapFtEval0Weld` §6 exhibits the hole as a refusal.
    StepFtEval0,
    /// `public_comm` — the 40-point Lagrange MSM over the public-input words
    /// (`Dregg2.Bridge.MinaWrapPublicInput.publicCommOf`). It EXISTS and is welded; what is not
    /// settled is where the group arithmetic runs. See this module's header.
    PublicComm,
    /// The WRAP side's ξ and r — `KimchiVerify.deriveVU` over the phase-2 Fr-sponge stream. The
    /// function exists and reproduces a synthetic Vesta proof's `v`/`u`
    /// (`KimchiPoseidonGate`); it has never been welded to a real Mina block's stream.
    WrapPolyscale,
    /// The WRAP side's `ft_eval0` and `combined_inner_product`, hence `shift_scalar(cip)`.
    WrapFtEval0,
    /// The phase-1 Fq-sponge and the IPA transcript — `dregg_mina_wrap_challenges`.
    Transcript,
    /// The verified gate is not in the linked archive at all.
    GateUnavailable,
}

impl std::fmt::Display for DerivationStage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::WireIncomplete => "the decoded wire (an argument the decoder walks past)",
            Self::StepFtEval0 => {
                "the STEP-side ft_eval0 (blocked on ONE config object: the 7 Tick coset shifts \
                 at domain_log2 = 16)"
            }
            Self::PublicComm => "public_comm, the 40-point Lagrange MSM",
            Self::WrapPolyscale => {
                "the WRAP-side Fr-sponge (xi, r) — deriveVU, never welded to a \
                                    real block"
            }
            Self::WrapFtEval0 => "the WRAP-side ft_eval0 / combined_inner_product",
            Self::Transcript => "the phase-1 sponge and the IPA transcript",
            Self::GateUnavailable => "the verified gate, which is not in the linked archive",
        };
        f.write_str(s)
    }
}

/// **Everything the per-block challenge derivation needs from ONE served block**, as decimals.
///
/// ⚑ Decimals and not field elements, deliberately: `mina_pickles.rs` renders a decoded 32-byte
/// little-endian coordinate with `decimal_of_le32`, which is a base conversion and not field
/// arithmetic. There is no Pasta operation on this side of the boundary to drift from the Lean.
#[derive(Clone, Debug, Default)]
pub struct MinaWrapWire {
    /// `index.digest::<EFqSponge>()`. ⚑ TRUSTED CONFIG, one `Fp` element.
    pub vk_digest: String,
    /// The Pallas `endo_r`. ⚑ CONFIG.
    pub endo_r: String,
    /// `messages_for_next_step_proof.challenge_polynomial_commitments`, flat — 4 numbers.
    pub prev_comm: Vec<String>,
    /// `commitments.w_comm`, flat — 30.
    pub w_comm: Vec<String>,
    /// `commitments.z_comm`, flat — 2.
    pub z_comm: Vec<String>,
    /// `commitments.t_comm`, flat — 14.
    pub t_comm: Vec<String>,
    /// `bulletproof.lr`, FLAT — 60. Re-chunked inside the archive.
    pub lr_flat: Vec<String>,
    /// `bulletproof.delta`, flat — 2.
    pub delta: Vec<String>,
    /// `public_comm`'s `(x, y)`. ⚑ Not on the wire; the [`DerivationStage::PublicComm`] leg.
    pub public_comm: Vec<String>,
    /// `shift_scalar(combined_inner_product)`. ⚑ Not on the wire; the
    /// [`DerivationStage::WrapFtEval0`] leg.
    pub cip_shifted: String,
}

impl MinaWrapWire {
    /// The shapes the archive's own gate will check, checked here first so the refusal names the
    /// FIELD rather than arriving as an undifferentiated `"ERR"`.
    ///
    /// ⚑ This duplicates no arithmetic and makes no decision: `phase1WireOk` and `openingWireOk`
    /// remain the authority and still run. This is a diagnostic pre-check, and the gate refusing
    /// after it passes is still a refusal.
    fn first_incomplete_field(&self) -> Option<(DerivationStage, &'static str)> {
        let checks: [(usize, usize, DerivationStage, &'static str); 8] = [
            (
                self.prev_comm.len(),
                4,
                DerivationStage::WireIncomplete,
                "prev_comm (2 points)",
            ),
            (
                self.w_comm.len(),
                30,
                DerivationStage::WireIncomplete,
                "w_comm (15 points)",
            ),
            (
                self.z_comm.len(),
                2,
                DerivationStage::WireIncomplete,
                "z_comm",
            ),
            (
                self.t_comm.len(),
                14,
                DerivationStage::WireIncomplete,
                "t_comm (7 chunks)",
            ),
            (
                self.lr_flat.len(),
                60,
                DerivationStage::WireIncomplete,
                "lr (15 rounds x 4)",
            ),
            (
                self.delta.len(),
                2,
                DerivationStage::WireIncomplete,
                "delta",
            ),
            (
                self.public_comm.len(),
                2,
                DerivationStage::PublicComm,
                "public_comm",
            ),
            (
                usize::from(!self.cip_shifted.is_empty()),
                1,
                DerivationStage::WrapFtEval0,
                "cip_shifted",
            ),
        ];
        checks
            .into_iter()
            .find(|(got, want, _, _)| got != want)
            .map(|(_, _, stage, what)| (stage, what))
    }
}

/// Parse a canonical decimal into a [`U256`], refusing rather than panicking.
///
/// ⚑ `U256::from_dec` PANICS on a non-digit or on overflow past 256 bits and says so in its own
/// doc comment — it is a compile-time-constant helper. A value crossing the C ABI is not a
/// compile-time constant, so it is bounded here first: 77 digits cannot reach `2^256`.
fn u256_from_decimal(s: &str) -> Result<U256, String> {
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("`{s}` is not a canonical decimal"));
    }
    if s.len() > 77 {
        return Err(format!(
            "`{s}` has {} digits and cannot be a 256-bit value",
            s.len()
        ));
    }
    Ok(U256::from_dec(s))
}

/// ⚑⚑ **DERIVE this block's own 15 IPA challenges.** No height table, no lookup.
///
/// The whole path runs inside the archive: `dregg_mina_wrap_challenges` picks the phase-1 Fq-sponge
/// up from the block's absorbed coordinates and runs it forward through the opening transcript.
/// Rust formats decimals and reads back fifteen; it computes nothing.
///
/// Every failure is a REFUSAL naming its [`DerivationStage`], and there is no arm that returns a
/// vector this function did not get from the gate.
pub fn derive_challenges_for_block(
    block_height: u64,
    wire: &MinaWrapWire,
) -> Result<Vec<U256>, MinaOpeningCheckError> {
    if !dregg_lean_ffi::mina_wrap_challenges_available() {
        return Err(MinaOpeningCheckError::ChallengesUnavailable {
            block_height,
            stage: DerivationStage::GateUnavailable,
            why: "dregg_mina_wrap_challenges is not exported by the linked archive; there is NO \
                  Rust fallback and there must not be one"
                .to_string(),
        });
    }
    if let Some((stage, what)) = wire.first_incomplete_field() {
        return Err(MinaOpeningCheckError::ChallengesUnavailable {
            block_height,
            stage,
            why: format!("the assembled wire has no usable `{what}`"),
        });
    }
    let derived = dregg_lean_ffi::verified_mina_wrap_challenges(
        &wire.vk_digest,
        &wire.endo_r,
        &wire.prev_comm,
        &wire.public_comm,
        &wire.w_comm,
        &wire.z_comm,
        &wire.t_comm,
        &wire.cip_shifted,
        &wire.lr_flat,
        &wire.delta,
    )
    .map_err(|why| MinaOpeningCheckError::ChallengesUnavailable {
        block_height,
        stage: DerivationStage::Transcript,
        why,
    })?;
    derived
        .ipa_prechallenges
        .iter()
        .map(|c| u256_from_decimal(c))
        .collect::<Result<Vec<U256>, String>>()
        .map_err(|why| MinaOpeningCheckError::ChallengesMalformed { why })
}

/// ⚑ **THE DIFFERENTIAL.** Where a height has both a derivation and a reference vector, they must
/// agree — and a disagreement is louder than either being absent.
///
/// This is what makes [`PINNED_CHALLENGES`] worth keeping after it stopped being a source: it is
/// the in-kernel answer for one block, and the compiled per-block path has to reproduce it.
pub fn cross_check_against_reference(
    block_height: u64,
    derived: &[U256],
) -> Result<(), MinaOpeningCheckError> {
    let Some(reference) = pinned_challenges_for(block_height) else {
        return Ok(());
    };
    check_pin(&reference.artifact)?;
    let want = opening::parse_challenges(reference.artifact.json)
        .map_err(|why| MinaOpeningCheckError::ChallengesMalformed { why })?;
    let differing = want
        .iter()
        .zip(derived.iter())
        .filter(|(a, b)| a != b)
        .count()
        + want.len().abs_diff(derived.len());
    if differing != 0 {
        return Err(MinaOpeningCheckError::DerivationDisagreesWithReference {
            block_height,
            differing,
        });
    }
    Ok(())
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
    wire: &MinaWrapWire,
) -> Result<MinaOpeningCheckReceipt, MinaOpeningCheckError> {
    // (a) ⚑ THE PER-BLOCK PATH IS TRIED FIRST, AT EVERY HEIGHT. It is not conditioned on a table.
    match derive_challenges_for_block(block_height, wire) {
        Ok(chals) => {
            // …and where a reference vector exists, it must agree. A disagreement refuses.
            cross_check_against_reference(block_height, &chals)?;
            let provenance: &'static str = "DERIVED per block by Dregg2.Bridge.MinaWrapChallenges from this block's own                  absorbed coordinates, through dregg_mina_wrap_challenges. Cross-checked against                  the in-kernel reference vector wherever one exists.";
            prove_opening_check_with_challenges(
                block_height,
                &PinnedChallenges {
                    block_height,
                    artifact: PINNED_CHALLENGES[0].artifact,
                    provenance,
                },
                &chals,
            )
        }
        // (b) The derivation stopped at a named leg. At a height that has an in-kernel reference
        //     vector we can still prove — and the receipt SAYS the vector was asserted about the
        //     block rather than derived from it, which is the whole job of `challenge_provenance`.
        //     Everywhere else the stage-named refusal propagates and nothing is proved.
        Err(stopped) => {
            let Some(reference) = pinned_challenges_for(block_height) else {
                return Err(stopped);
            };
            check_pin(&reference.artifact)?;
            let chals = opening::parse_challenges(reference.artifact.json)
                .map_err(|why| MinaOpeningCheckError::ChallengesMalformed { why })?;
            prove_opening_check_with_challenges(block_height, reference, &chals)
        }
    }
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

    /// ⚑ **THE FAIL-CLOSED ARM, on the runtime path.** A height whose per-block derivation cannot
    /// run, and which has no reference vector either, proves NOTHING — and the refusal NAMES THE
    /// LEG rather than reporting a table miss. It does not fall back, log, or return an `Ok` that
    /// means "checked nothing".
    #[test]
    fn a_height_whose_derivation_cannot_run_is_refused_and_names_the_leg() {
        // An empty wire: nothing was decoded, so the derivation cannot even be attempted.
        let empty = MinaWrapWire::default();
        for h in [0u64, 1, 539_507, 539_509, 539_795, u64::MAX] {
            match prove_block_opening_check(h, &empty) {
                Err(MinaOpeningCheckError::ChallengesUnavailable {
                    block_height,
                    stage,
                    ..
                }) => {
                    assert_eq!(block_height, h);
                    assert!(
                        matches!(
                            stage,
                            DerivationStage::WireIncomplete | DerivationStage::GateUnavailable
                        ),
                        "an empty wire must stop at the wire or at an absent gate, got {stage:?}"
                    );
                }
                other => panic!("height {h} must be REFUSED as unavailable, got {other:?}"),
            }
        }
    }

    /// ⚑ The stage really discriminates: an empty wire and a wire that is complete except for
    /// `public_comm` are DIFFERENT refusals, which is the whole reason the payload changed.
    #[test]
    fn the_derivation_stage_discriminates_between_legs() {
        if !dregg_lean_ffi::mina_wrap_challenges_available() {
            return; // a cold archive; `GateUnavailable` is then the only reachable stage.
        }
        let mut w = MinaWrapWire {
            vk_digest: "1".into(),
            endo_r: "1".into(),
            prev_comm: vec!["1".into(); 4],
            w_comm: vec!["1".into(); 30],
            z_comm: vec!["1".into(); 2],
            t_comm: vec!["1".into(); 14],
            lr_flat: vec!["1".into(); 60],
            delta: vec!["1".into(); 2],
            public_comm: Vec::new(),
            cip_shifted: String::new(),
        };
        match derive_challenges_for_block(1, &w) {
            Err(MinaOpeningCheckError::ChallengesUnavailable { stage, .. }) => {
                assert_eq!(stage, DerivationStage::PublicComm)
            }
            other => panic!("a missing public_comm must name its own leg, got {other:?}"),
        }
        w.public_comm = vec!["1".into(); 2];
        match derive_challenges_for_block(1, &w) {
            Err(MinaOpeningCheckError::ChallengesUnavailable { stage, .. }) => {
                assert_eq!(stage, DerivationStage::WrapFtEval0)
            }
            other => panic!("a missing cip_shifted must name its own leg, got {other:?}"),
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
