//! Tier-C PROOF gate — the whole-chain IVC range attestation (`docs/PG-DREGG.md`
//! §10.2), the crate-side shape behind the `tier-c` feature.
//!
//! # The two halves of Tier C, and which one this is
//!
//! Tier C's spine is "no state row exists except as a verified-turn post-image".
//! It has TWO independent enforcement halves, and they live in different places:
//!
//! 1. **The per-row STRUCTURAL chain re-validation** — [`crate::mirror::
//!    verify_chain_step`], lifted into SQL as the `dregg_verify_turn` extern and
//!    the `dregg.commit_log` `BEFORE INSERT` trigger. It runs UNCONDITIONALLY (no
//!    feature), is circuit-free, and is the realizable per-row gate: a turn's
//!    `ordinal` is the next expected one AND its `prev_root` equals the head, so a
//!    tampered/reordered/forged batch is refused by the database engine. This is
//!    the load-bearing half that ships in every build.
//!
//! 2. **The whole-chain PROOF attestation** — THIS module. A `CommitRecord`
//!    carries no per-turn STARK (§10.2), so the per-row gate can NOT re-prove a
//!    turn's execution. The *proof* soundness is the whole-chain IVC light client
//!    (`circuit::ivc_turn_chain::verify_turn_chain_recursive`): ONE succinct
//!    recursive proof attesting that ALL K finalized turns in a receipt RANGE
//!    executed correctly and the root chain advanced from `genesis_root` to
//!    `final_root`. The verifier checks only the root; cost is independent of K.
//!    This is the orthogonal M3 item the doc names — surfaced here, behind
//!    `tier-c`, as a *range-attest* set-returning function (NOT a per-row STARK,
//!    which would be both impossible — no per-turn proof exists — and the wrong
//!    cost model).
//!
//! # Why a RANGE attestation, not a per-row one
//!
//! The IVC artifact is whole-chain by construction: a single recursive fold over
//! a *window* of finalized turns. Its natural SQL shape is therefore a function
//! that takes (the serialized proof, the trust-anchor VK, the claimed range
//! bounds) and, if the proof verifies against the anchor, RETURNS the attested
//! range as rows — `(ordinal, prev_root, ledger_root)` for each turn the range
//! covers, every row tagged `proof_attested = true`. A consumer JOINs that
//! against `dregg.turns` to learn "these ordinals are not merely chain-consistent
//! (the structural tooth) but PROOF-attested (every turn executed correctly,
//! verified in-circuit)". One proof attests a whole window; the SRF explodes the
//! window into rows so SQL can use it.
//!
//! # The honest boundary (named, not hidden) — the circuit-link settle item
//!
//! The IVC verifier `verify_turn_chain_recursive(proof: &WholeChainProof,
//! expected_vk: &RecursionVk)` takes an **in-memory** `WholeChainProof` — a Rust
//! struct holding plonky3 proof objects (`RecursionOutput`,
//! `RecursionCompatibleProof`). That struct is **not** `Serialize`/`Deserialize`
//! today, so a `WholeChainProof` cannot yet cross the SQL boundary as `bytea`.
//! What CAN cross now is:
//!
//! * the **VK anchor** — `RecursionVk(pub [u8; 32])`, a 32-byte fingerprint the
//!   honest-setup party publishes as the light client's trust root (exactly like
//!   a SNARK VK), and
//! * the **claimed publics** — `genesis_root` / `final_root` / `num_turns` /
//!   `chain_digest`, the bound window summary.
//!
//! So this module ships the **range-attest SRF shape** in full — the
//! [`RangeAttestation`] request/verdict types, the [`AttestedTurn`] row the SRF
//! returns, the [`attest_range`] entry the pg-extern calls, and the fail-closed
//! discipline — with the proof-bytes leg STUBBED behind a single, loud seam:
//! [`verify_serialized_proof`]. Wiring that leg is a *bounded* settle item, named
//! precisely below and in `docs/PG-DREGG.md` §10.2:
//!
//!   (S1) add a serialization to `circuit::ivc_turn_chain::WholeChainProof` (the
//!        plonky3 proof objects are postcard/serde-encodable; the struct just
//!        needs the derives + a versioned envelope), so the node can ship a proof
//!        as `bytea` and the SRF can `decode → verify_turn_chain_recursive`;
//!   (S2) the node-side PRODUCER: when finality advances, fold the new finalized
//!        turns (`prove_turn_chain_recursive` / the `fold_two_turns` accumulator)
//!        and write the serialized proof + its window bounds into a
//!        `dregg.turn_proofs(lo, hi, genesis_root, final_root, proof bytea, vk)`
//!        table the SRF reads;
//!   (S3) the `tier-c` feature pulls `dregg-circuit` (Lean-free — `--features
//!        verifier`/`recursion`, NO executor, NO Lean runtime; §8.1 authorizes the
//!        circuit link for Tier C) so [`verify_serialized_proof`] becomes the real
//!        `verify_turn_chain_recursive` instead of the stub.
//!
//! Until S1–S3 land, the SRF FAILS CLOSED: with the stub it attests nothing
//! (`verify_serialized_proof` returns "not yet wired" and the SRF returns zero
//! rows / an honest verdict), which is the only safe default — a labeled proof
//! gate that does NOT yet verify must return "unattested", never "attested". That
//! is the §10.3 discipline (a stubbed verifier that returns TRUE is the forbidden
//! failure mode; this stub returns the SAFE direction).
//!
//! Everything here is plain Rust, postgres-free, `cargo test`-proven. The
//! `#[pg_extern]` SRF in [`crate`] marshals `bytea`/`bigint` into [`attest_range`].

use serde::{Deserialize, Serialize};

/// The 32-byte recursion VK fingerprint — the light client's trust anchor, the
/// SQL-crossable mirror of `circuit::plonky3_recursion_impl::RecursionVk`. An
/// honest-setup party extracts it ONCE from a locally produced fold and publishes
/// it; a verifier compares the presented proof's root fingerprint against THIS
/// (never against an anchor taken from the artifact being verified — that is the
/// whole point of a pinned VK). Here it is opaque bytes; the `tier-c` build
/// converts it into the circuit's `RecursionVk` for the real check.
pub type VkAnchor = [u8; 32];

/// A turn the range attestation covers, exploded into a SQL row. The SRF returns
/// one of these per ordinal in `[lo, hi]` when the proof verifies, each tagged
/// `proof_attested = true` so a consumer JOINs it against `dregg.turns` to mark
/// the proof-attested prefix (distinct from the merely chain-consistent rows the
/// structural tooth admits).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedTurn {
    /// The turn ordinal (a row of `dregg.turns`).
    pub ordinal: u64,
    /// The pre-state root the turn chained onto.
    pub prev_root: [u8; 32],
    /// The post-state root the turn produced (the next turn's `prev_root`).
    pub ledger_root: [u8; 32],
    /// Always `true` for a row the SRF emits — it is emitted ONLY when the
    /// whole-chain proof verified the window this ordinal lies in. (The column
    /// exists so a `UNION` with un-attested `dregg.turns` rows is unambiguous.)
    pub proof_attested: bool,
}

/// The request a caller makes of the range-attest SRF: the serialized whole-chain
/// proof, the trust anchor to verify it against, and the window bounds the caller
/// claims it attests. The bounds are checked AGAINST the proof's own attested
/// publics (a caller cannot claim a wider window than the proof covers — that is
/// the anti-overclaim tooth, [`RangeAttestation::check_window`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttestRequest<'a> {
    /// The serialized `WholeChainProof` bytes (the node-produced artifact). Empty
    /// / malformed ⇒ fail closed.
    pub proof_bytes: &'a [u8],
    /// The light client's published VK anchor.
    pub vk_anchor: VkAnchor,
    /// The inclusive lower ordinal the caller asks the SRF to attest.
    pub lo: u64,
    /// The inclusive upper ordinal the caller asks the SRF to attest.
    pub hi: u64,
}

/// The verdict of attempting a range attestation. Either the proof verified and
/// the SRF should emit the [`AttestedTurn`] rows for the attested window, or it
/// was refused with a named reason (fail-closed — the SRF emits NO rows on a
/// refusal, never a partial or an unverified row).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RangeAttestation {
    /// The proof verified against the anchor and covers `[lo, hi]`. The carried
    /// window publics (`genesis_root` is the pre-root of `lo`, `final_root` is the
    /// post-root of `hi`, `num_turns` is the count) are what the proof bound under
    /// Fiat–Shamir, so they are trustworthy.
    Attested {
        lo: u64,
        hi: u64,
        genesis_root: [u8; 32],
        final_root: [u8; 32],
        num_turns: u64,
    },
    /// The attestation was refused; the string names which requirement failed
    /// (bad anchor, proof did not verify, claimed window not covered, malformed
    /// bytes, or — until the circuit link lands — "proof verification not yet
    /// wired (Tier-C circuit-link settle item)").
    Refused(String),
}

impl RangeAttestation {
    /// `true` iff the proof verified for the requested window.
    pub fn attested(&self) -> bool {
        matches!(self, RangeAttestation::Attested { .. })
    }

    /// The human-readable reason, for the explain/audit surface.
    pub fn reason(&self) -> String {
        match self {
            RangeAttestation::Attested {
                lo, hi, num_turns, ..
            } => {
                format!("attested: turns [{lo}, {hi}] ({num_turns} turns) proof-verified")
            }
            RangeAttestation::Refused(r) => r.clone(),
        }
    }

    /// The anti-overclaim tooth: a verified proof attests EXACTLY the window its
    /// publics bind. A caller's claimed `[lo, hi]` is honoured only if it lies
    /// within the proof's covered window — i.e. the proof's `num_turns` spans at
    /// least `hi - lo + 1` turns ending at the proof's `final_root`. This stops a
    /// caller presenting a proof for turns [0, 100] and claiming it attests
    /// [0, 1000]. (The exact ordinal binding is sharpened when S2 ties the proof's
    /// window publics to concrete ordinals; today the proof publics carry the
    /// root pair + count, and the SRF binds the claimed count to them.)
    fn check_window(claimed_lo: u64, claimed_hi: u64, proof_num_turns: u64) -> Result<(), String> {
        if claimed_hi < claimed_lo {
            return Err(format!(
                "claimed window is empty/inverted: lo={claimed_lo} > hi={claimed_hi}"
            ));
        }
        let claimed_span = claimed_hi - claimed_lo + 1;
        if claimed_span > proof_num_turns {
            return Err(format!(
                "claimed window spans {claimed_span} turns but the proof attests only \
                 {proof_num_turns} — a proof cannot attest more than it covers"
            ));
        }
        Ok(())
    }
}

/// The publics a verified whole-chain proof binds (the SQL-crossable summary of
/// `circuit::ivc_turn_chain::WholeChainProof`'s attested fields). The real
/// `tier-c` verify path fills this from the verified proof; the stub fills it from
/// nothing (it never reaches here). Fiat–Shamir binds these into the proof, so a
/// verified proof's publics are trustworthy.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofPublics {
    pub genesis_root: [u8; 32],
    pub final_root: [u8; 32],
    pub chain_digest: [u8; 32],
    pub num_turns: u64,
}

// ============================================================================
// S1 — the SQL-crossable transport for a whole-chain proof.
// ============================================================================
//
// docs/PG-DREGG.md §10.2 names S1 as "serialize WholeChainProof". The honest
// shape of that, established by reading the circuit:
//
//   `circuit::ivc_turn_chain::WholeChainProof` is
//       { root: RecursionOutput<SC>, binding_proof: RecursionCompatibleProof,
//         genesis_root: BabyBear, final_root: BabyBear,
//         chain_digest: BabyBear, num_turns: usize }
//   where `RecursionOutput<SC>(pub BatchStarkProof<SC>, pub Rc<CircuitProverData<SC>>)`.
//
// `BatchStarkProof` (`root.0`) and `RecursionCompatibleProof` (= a uni-STARK
// `Proof`, the `binding_proof`) BOTH derive `Serialize`/`Deserialize`
// (`#[serde(bound = "")]`); the four publics are `BabyBear`/`usize`. The ONLY
// non-serde field is `root.1` — `Rc<CircuitProverData>`, the PROVER-CHAINING
// data. And the verifier never reads it: `verify_turn_chain_recursive` touches
// only `root.0`, `binding_proof`, and the four publics (the three teeth —
// `recursion_vk_fingerprint(&root.0)`, the binding-proof publics check, and
// `verify_recursive_batch_proof_with_config(&root.0, …)`). So the
// VERIFY-SUFFICIENT subset of a `WholeChainProof` is `{root.0, binding_proof,
// 4 publics}` — and every member of that subset IS serde.
//
// Therefore the transport carries exactly that subset, with the two proof
// components as opaque postcard blobs (so this crate's transport type needs NO
// circuit types — the default build stays circuit-free), plus the publics in the
// SQL-crossable byte form. The `tier-c` real leg decodes the two blobs into the
// concrete circuit types and verifies from the PARTS.
//
// The one residual that is genuinely circuit-side (NOT reachable from
// `pg-dregg/src/`, named precisely): a `WholeChainProof` VALUE cannot be
// reconstructed from these bytes, because `root.1` (`Rc<CircuitProverData>`) is
// not serde and is prover-only. So the circuit must expose a parts verifier —
// `verify_turn_chain_recursive_from_parts(root_0: &BatchStarkProof, binding: &Proof,
// genesis/final/digest: BabyBear, num_turns)` — a ~6-line split of the existing
// `verify_turn_chain_recursive` body (which already only uses those parts). That
// wrapper is the remaining S3 circuit-dep line; the producer/transport/decode are
// done and `cargo test`-proven here.

/// The on-the-wire version tag of [`SerializedWholeChainProof`]. Bumped if the
/// transport layout changes, so a stale producer's bytes are refused (fail-closed)
/// rather than misread.
pub const WHOLE_CHAIN_PROOF_TRANSPORT_V1: u16 = 1;

/// The versioned, `bytea`-crossable transport of a whole-chain IVC proof — the S1
/// artifact (`docs/PG-DREGG.md` §10.2). It carries the VERIFY-SUFFICIENT subset of
/// `circuit::ivc_turn_chain::WholeChainProof` (the prover-only `root.1`
/// `Rc<CircuitProverData>` is omitted — the verifier never reads it), so the node
/// (S2) ships a proof as `bytea` and the SRF (S3) decodes + verifies it from the
/// parts.
///
/// The two proof components ride as opaque postcard blobs so THIS crate's transport
/// type needs no circuit types (the default build stays circuit-free); the `tier-c`
/// real leg postcard-decodes `root_proof` into a `BatchStarkProof<DreggRecursionConfig>`
/// and `binding_proof` into a `Proof<DreggRecursionConfig>`. The four publics are the
/// SQL-crossable hints the SRF/`dregg.turn_proofs` row index by; they are NOT trusted
/// blindly — tooth 2 of the verifier re-checks them against the binding proof's
/// Fiat–Shamir-bound publics, so a relabeled hint is refused at verify.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SerializedWholeChainProof {
    /// The transport version ([`WHOLE_CHAIN_PROOF_TRANSPORT_V1`]).
    pub version: u16,
    /// Postcard bytes of `WholeChainProof.root.0` — the root `BatchStarkProof`
    /// (`#[serde(bound = "")]`, so it postcard-encodes). The verifier's tooth 1
    /// (VK-fingerprint pin) and tooth 3 (root batch verify) both read exactly this.
    pub root_proof: Vec<u8>,
    /// Postcard bytes of `WholeChainProof.binding_proof` — the chain-binding
    /// uni-STARK `Proof`. Tooth 2 verifies the carried publics AS its public inputs.
    pub binding_proof: Vec<u8>,
    /// The genesis root the chain starts from (the `BabyBear` packed little-endian
    /// into 32 bytes — a `BabyBear` is one field element; the high bytes are zero).
    pub genesis_root: [u8; 32],
    /// The final root the chain reaches.
    pub final_root: [u8; 32],
    /// The running digest committing to the ordered (old_root, new_root) pairs.
    pub chain_digest: [u8; 32],
    /// The number of finalized turns folded.
    pub num_turns: u64,
}

impl SerializedWholeChainProof {
    /// Build a transport from already-serialized proof-component blobs + the publics.
    /// The producer (S2) calls this with `postcard::to_allocvec(&whole.root.0)` and
    /// `postcard::to_allocvec(&whole.binding_proof)` (done in the `tier-c` build,
    /// where the circuit types are in scope) and the four publics mapped to bytes.
    pub fn new(
        root_proof: Vec<u8>,
        binding_proof: Vec<u8>,
        genesis_root: [u8; 32],
        final_root: [u8; 32],
        chain_digest: [u8; 32],
        num_turns: u64,
    ) -> Self {
        SerializedWholeChainProof {
            version: WHOLE_CHAIN_PROOF_TRANSPORT_V1,
            root_proof,
            binding_proof,
            genesis_root,
            final_root,
            chain_digest,
            num_turns,
        }
    }

    /// Encode the transport to `bytea`-ready bytes (postcard). Infallible (the alloc
    /// serializer never fails on a well-formed value).
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("SerializedWholeChainProof postcard-encodes")
    }

    /// Decode a transport from `bytea` bytes. Fail-closed: malformed bytes, a wrong
    /// version, or an empty proof component is an `Err` (never a silently-accepted
    /// half-proof) — so the SRF/seam refuses rather than verifying garbage.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.is_empty() {
            return Err("empty whole-chain proof transport".to_string());
        }
        let t: SerializedWholeChainProof = postcard::from_bytes(bytes)
            .map_err(|e| format!("whole-chain proof transport does not decode: {e}"))?;
        if t.version != WHOLE_CHAIN_PROOF_TRANSPORT_V1 {
            return Err(format!(
                "unsupported whole-chain proof transport version {} (this build reads v{})",
                t.version, WHOLE_CHAIN_PROOF_TRANSPORT_V1
            ));
        }
        if t.root_proof.is_empty() {
            return Err("whole-chain proof transport carries an empty root proof".to_string());
        }
        if t.binding_proof.is_empty() {
            return Err("whole-chain proof transport carries an empty binding proof".to_string());
        }
        Ok(t)
    }
}

/// The ONE seam the circuit link plugs into. Verify a serialized whole-chain
/// proof against the VK anchor and, on success, return the publics it bound.
///
/// Both builds now DECODE the [`SerializedWholeChainProof`] transport (the S1
/// artifact) first — a malformed / wrong-version / empty-component transport is
/// refused identically in both, so the SRF never even reaches the circuit check on
/// garbage. They differ only in whether the decoded parts are then verified:
///
/// * **`tier-c` OFF (default):** after decode, returns `Err("…not yet wired…")` —
///   the SAFE direction. The Tier-A/B/chain-gate build stays circuit-free, the
///   range-attest SRF honestly attests nothing (fail-closed). This is NOT the §10.3
///   forbidden failure mode: that is a stub returning *success* (attesting forged
///   state); this returns *refusal* (attesting nothing) even on a well-formed
///   transport.
///
/// * **`tier-c` ON (the settle item):** postcard-decodes the transport's
///   `root_proof` into `BatchStarkProof<DreggRecursionConfig>` and `binding_proof`
///   into `Proof<DreggRecursionConfig>`, maps `vk_anchor` to `RecursionVk`, and runs
///   the circuit's PARTS verifier (`verify_turn_chain_recursive_from_parts` — the
///   named ~6-line split of `verify_turn_chain_recursive`, which already uses only
///   `root.0` + `binding_proof` + the publics, never the prover-only `root.1`). On
///   `Ok(())` returns the transport's `{genesis_root, final_root, chain_digest,
///   num_turns}`. On any error returns `Err(reason)`.
///
/// The signature is identical in both builds, so [`attest_range`] is written ONCE
/// against this seam and does not branch on the feature.
pub fn verify_serialized_proof(
    proof_bytes: &[u8],
    vk_anchor: &VkAnchor,
) -> Result<ProofPublics, String> {
    // S1: decode the transport (shared by both builds — fail-closed on malformed,
    // wrong-version, or empty-component bytes). This is real in EVERY build, so the
    // `bytea` → typed-parts boundary is exercised by plain `cargo test`.
    let transport = SerializedWholeChainProof::from_bytes(proof_bytes)?;
    let _ = vk_anchor;

    #[cfg(not(feature = "tier-c"))]
    {
        // SAFE DIRECTION. The circuit verifier is not linked in the default build;
        // the transport decoded fine, but we attest NOTHING (refusal), never a false
        // attest. Turning on `tier-c` + wiring the parts verifier replaces this arm.
        let _ = &transport;
        Err(
            "proof verification not yet wired (Tier-C circuit-link settle item, \
             docs/PG-DREGG.md §10.2): the transport decoded, but the whole-chain IVC \
             parts verifier (circuit::ivc_turn_chain::verify_turn_chain_recursive_from_parts) \
             is not linked in this build — the range-attest SRF fails closed (attests nothing)"
                .to_string(),
        )
    }

    #[cfg(feature = "tier-c")]
    {
        // THE REAL LEG. With `tier-c` on, this arm links the Lean-FREE circuit
        // verifier (§8.1) and verifies the decoded PARTS. It compiles once the
        // `dregg-circuit` dep is wired into the `tier-c` feature AND the circuit
        // exposes `verify_turn_chain_recursive_from_parts` (the named split of the
        // existing `verify_turn_chain_recursive`, which already uses only these
        // parts). The flip is then mechanical — the transport decode above and the
        // publics mapping below are already live + tested.
        //
        // ```ignore
        // use dregg_circuit::ivc_turn_chain::verify_turn_chain_recursive_from_parts;
        // use dregg_circuit::plonky3_recursion_impl::{RecursionVk, RecursionCompatibleProof};
        // use dregg_circuit::p3_circuit_prover::BatchStarkProof;
        // use dregg_circuit::plonky3_recursion_impl::DreggRecursionConfig;
        // let root_proof: BatchStarkProof<DreggRecursionConfig> =
        //     postcard::from_bytes(&transport.root_proof)
        //         .map_err(|e| format!("root proof does not decode: {e}"))?;
        // let binding_proof: RecursionCompatibleProof =
        //     postcard::from_bytes(&transport.binding_proof)
        //         .map_err(|e| format!("binding proof does not decode: {e}"))?;
        // let vk = RecursionVk(*vk_anchor);
        // verify_turn_chain_recursive_from_parts(
        //     &root_proof, &binding_proof,
        //     bytes_to_babybear(&transport.genesis_root),
        //     bytes_to_babybear(&transport.final_root),
        //     bytes_to_babybear(&transport.chain_digest),
        //     transport.num_turns as usize,
        //     &vk,
        // ).map_err(|e| format!("proof did not verify against the anchor: {e}"))?;
        // return Ok(ProofPublics {
        //     genesis_root: transport.genesis_root,
        //     final_root:   transport.final_root,
        //     chain_digest: transport.chain_digest,
        //     num_turns:    transport.num_turns,
        // });
        // ```
        let _ = &transport;
        Err(
            "tier-c feature is enabled but the circuit dep is not yet wired (settle \
             item: add the dregg-circuit verifier/recursion dep + the circuit-side \
             verify_turn_chain_recursive_from_parts split, docs/PG-DREGG.md §10.2) — \
             fails closed"
                .to_string(),
        )
    }
}

/// The range-attest entry the pg-extern SRF calls. Verifies the proof against the
/// anchor (via [`verify_serialized_proof`]), checks the claimed window does not
/// over-claim the proof's coverage, and returns the verdict. The SRF emits
/// [`AttestedTurn`] rows ONLY on [`RangeAttestation::Attested`]; on
/// [`RangeAttestation::Refused`] it emits nothing (fail-closed).
///
/// This is the load-bearing logic, written ONCE against the [`verify_serialized_proof`]
/// seam, so it is the SAME in the stub and the wired build. The settle item flips
/// the seam, not this function.
pub fn attest_range(req: &AttestRequest<'_>) -> RangeAttestation {
    if req.hi < req.lo {
        return RangeAttestation::Refused(format!(
            "empty/inverted window: lo={} > hi={}",
            req.lo, req.hi
        ));
    }
    let publics = match verify_serialized_proof(req.proof_bytes, &req.vk_anchor) {
        Ok(p) => p,
        Err(e) => return RangeAttestation::Refused(e),
    };
    if let Err(e) = RangeAttestation::check_window(req.lo, req.hi, publics.num_turns) {
        return RangeAttestation::Refused(e);
    }
    RangeAttestation::Attested {
        lo: req.lo,
        hi: req.hi,
        genesis_root: publics.genesis_root,
        final_root: publics.final_root,
        num_turns: publics.num_turns,
    }
}

/// Build the [`AttestedTurn`] rows for an [`RangeAttestation::Attested`] verdict,
/// reading the per-ordinal roots from the caller-supplied `turns` slice (which the
/// SRF populates by querying `dregg.turns` for the attested window — the proof
/// attests the WINDOW; the roots are the recorded ones, re-tagged `proof_attested`).
/// Returns empty for a refused verdict (fail-closed) or if the recorded turns do
/// not cover the attested window (a defensive guard: the proof says these ordinals
/// are attested, but if the table lacks them, attest nothing rather than fabricate).
pub fn attested_rows(verdict: &RangeAttestation, recorded: &[AttestedTurn]) -> Vec<AttestedTurn> {
    let RangeAttestation::Attested { lo, hi, .. } = verdict else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for ord in *lo..=*hi {
        match recorded.iter().find(|t| t.ordinal == ord) {
            Some(t) => out.push(AttestedTurn {
                ordinal: t.ordinal,
                prev_root: t.prev_root,
                ledger_root: t.ledger_root,
                proof_attested: true,
            }),
            // Defensive: the attested window references an ordinal the store does
            // not have. Do NOT fabricate a row — attest nothing for the gap.
            None => return Vec::new(),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn req<'a>(bytes: &'a [u8], lo: u64, hi: u64) -> AttestRequest<'a> {
        AttestRequest {
            proof_bytes: bytes,
            vk_anchor: [7u8; 32],
            lo,
            hi,
        }
    }

    /// A WELL-FORMED transport carrying `num_turns` (non-empty placeholder proof
    /// blobs — the transport hygiene only requires non-empty components; the actual
    /// proof verify is the `tier-c` circuit's job, stubbed off here). Used to prove
    /// that even a structurally-valid transport attests NOTHING under the default
    /// (circuit-free) build — the real safe-direction property, not "garbage bytes
    /// happen to be refused".
    fn good_transport(num_turns: u64) -> Vec<u8> {
        SerializedWholeChainProof::new(
            vec![0xa1, 0xa2, 0xa3], // non-empty root-proof blob (stub never decodes it)
            vec![0xb1, 0xb2],       // non-empty binding-proof blob
            [1u8; 32],              // genesis_root hint
            [9u8; 32],              // final_root hint
            [5u8; 32],              // chain_digest hint
            num_turns,
        )
        .to_bytes()
    }

    #[test]
    fn empty_window_is_refused() {
        let r = attest_range(&req(&[1, 2, 3], 5, 4));
        assert!(!r.attested());
        assert!(r.reason().contains("inverted"));
    }

    #[test]
    fn empty_proof_bytes_fail_closed() {
        // No proof ⇒ never attested, regardless of window.
        let r = attest_range(&req(&[], 0, 0));
        assert!(!r.attested());
        assert!(r.reason().to_lowercase().contains("empty"));
    }

    #[test]
    fn malformed_transport_bytes_fail_closed() {
        // Raw garbage that is NOT a valid transport ⇒ refused at the S1 decode
        // (fail-closed), before any circuit check. The reason names the decode.
        let r = attest_range(&req(&[0xde, 0xad, 0xbe, 0xef], 0, 10));
        assert!(!r.attested(), "garbage bytes must never attest");
        assert!(
            r.reason().contains("does not decode") || r.reason().contains("transport"),
            "the refusal names the transport decode: {}",
            r.reason()
        );
        assert!(attested_rows(&r, &recorded(0, 10)).is_empty());
    }

    #[test]
    fn well_formed_transport_attests_nothing_fail_closed() {
        // THE LOAD-BEARING SAFETY PROPERTY: with the circuit link unwired (the
        // default build), a STRUCTURALLY-VALID transport (it decodes fine) STILL
        // attests NOTHING — the stub returns the SAFE direction (refusal), never a
        // false attest. This is the §10.3 discipline: a labeled proof gate that does
        // not verify must say "unattested", never "attested". (The transport decodes;
        // it is the circuit *verify* that is stubbed off.)
        let t = good_transport(11); // 11 turns ⇒ would cover [0,10] IF it verified
        let r = attest_range(&req(&t, 0, 10));
        assert!(
            !r.attested(),
            "a valid transport must STILL not attest with the verifier unwired: {}",
            r.reason()
        );
        assert!(
            r.reason().contains("not yet wired") || r.reason().contains("settle item"),
            "the refusal names the circuit-link settle item, not a decode error: {}",
            r.reason()
        );
        // And it emits zero rows.
        assert!(attested_rows(&r, &recorded(0, 10)).is_empty());
    }

    #[test]
    fn window_overclaim_is_refused() {
        // The anti-overclaim tooth, exercised directly on the verdict logic: a
        // claimed window wider than the proof covers is refused. (We drive
        // check_window directly since the stub never reaches it; the wired build
        // reaches it after a real verify.)
        assert!(
            RangeAttestation::check_window(0, 9, 10).is_ok(),
            "10 turns covers [0,9]"
        );
        assert!(
            RangeAttestation::check_window(0, 10, 10).is_err(),
            "[0,10] is 11 turns > 10"
        );
        assert!(
            RangeAttestation::check_window(0, 1000, 100).is_err(),
            "a proof for 100 turns cannot attest a 1001-turn window"
        );
        let err = RangeAttestation::check_window(5, 4, 10).unwrap_err();
        assert!(err.contains("inverted"));
    }

    #[test]
    fn attested_rows_are_tagged_and_gap_fails_closed() {
        // A (hand-built) Attested verdict explodes into per-ordinal rows, all
        // tagged proof_attested=true — and a missing recorded ordinal yields NO
        // rows (never a fabricated one).
        let verdict = RangeAttestation::Attested {
            lo: 0,
            hi: 2,
            genesis_root: [0u8; 32],
            final_root: [9u8; 32],
            num_turns: 3,
        };
        let rows = attested_rows(&verdict, &recorded(0, 2));
        assert_eq!(rows.len(), 3);
        assert!(rows.iter().all(|t| t.proof_attested));
        assert_eq!(rows[0].ordinal, 0);
        assert_eq!(rows[2].ordinal, 2);

        // A gap in the recorded turns (ordinal 1 missing) ⇒ attest nothing.
        let recorded_with_gap = vec![recorded_one(0), recorded_one(2)];
        assert!(
            attested_rows(&verdict, &recorded_with_gap).is_empty(),
            "a recorded gap must fail closed, not fabricate the missing row"
        );
    }

    #[test]
    fn refused_verdict_emits_no_rows() {
        let verdict = RangeAttestation::Refused("nope".to_string());
        assert!(attested_rows(&verdict, &recorded(0, 5)).is_empty());
    }

    // ── S1: the whole-chain-proof transport (encode/decode round-trip + hygiene) ──

    #[test]
    fn transport_round_trips() {
        // The S1 artifact: the verify-sufficient subset of a WholeChainProof crosses
        // the SQL boundary as bytes and decodes back bit-identically.
        let t = SerializedWholeChainProof::new(
            vec![1, 2, 3, 4, 5],
            vec![9, 8, 7],
            [0x11; 32],
            [0x22; 32],
            [0x33; 32],
            42,
        );
        let bytes = t.to_bytes();
        let back = SerializedWholeChainProof::from_bytes(&bytes).expect("decodes");
        assert_eq!(back, t, "transport round-trips through postcard");
        assert_eq!(back.version, WHOLE_CHAIN_PROOF_TRANSPORT_V1);
        assert_eq!(back.num_turns, 42);
        assert_eq!(back.genesis_root, [0x11; 32]);
    }

    #[test]
    fn transport_decode_is_fail_closed() {
        // Empty bytes ⇒ refused.
        assert!(SerializedWholeChainProof::from_bytes(&[]).is_err());
        // Garbage that is not a valid postcard transport ⇒ refused (named).
        let e = SerializedWholeChainProof::from_bytes(&[0xff, 0xff, 0xff, 0xff]).unwrap_err();
        assert!(
            e.contains("does not decode") || e.contains("transport"),
            "{e}"
        );
        // A transport with an EMPTY root proof component ⇒ refused (a half-proof is
        // never silently accepted).
        let empty_root =
            SerializedWholeChainProof::new(vec![], vec![1], [0; 32], [0; 32], [0; 32], 1);
        let e = SerializedWholeChainProof::from_bytes(&empty_root.to_bytes()).unwrap_err();
        assert!(e.contains("empty root proof"), "{e}");
        // ... and an empty binding proof component ⇒ refused.
        let empty_bind =
            SerializedWholeChainProof::new(vec![1], vec![], [0; 32], [0; 32], [0; 32], 1);
        let e = SerializedWholeChainProof::from_bytes(&empty_bind.to_bytes()).unwrap_err();
        assert!(e.contains("empty binding proof"), "{e}");
    }

    #[test]
    fn transport_wrong_version_is_refused() {
        // A transport tagged with an unknown version is refused (fail-closed) rather
        // than misread — the staged-format discipline.
        let mut t = SerializedWholeChainProof::new(vec![1], vec![1], [0; 32], [0; 32], [0; 32], 1);
        t.version = 9999;
        let e = SerializedWholeChainProof::from_bytes(&t.to_bytes()).unwrap_err();
        assert!(e.contains("unsupported") && e.contains("version"), "{e}");
    }

    fn recorded_one(ord: u64) -> AttestedTurn {
        AttestedTurn {
            ordinal: ord,
            prev_root: [ord as u8; 32],
            ledger_root: [(ord + 1) as u8; 32],
            proof_attested: false, // the recorded row's tag is irrelevant; attested_rows re-tags
        }
    }

    fn recorded(lo: u64, hi: u64) -> Vec<AttestedTurn> {
        (lo..=hi).map(recorded_one).collect()
    }
}
