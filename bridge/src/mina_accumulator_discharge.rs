//! # `mina_accumulator_discharge` — **dregg's own discharge of the claim Pickles defers.**
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **Nothing here is an AIR, and that is the whole design.** Halo/Pickles never evaluate the SRS
//! multi-scalar multiplication in-circuit — the deferral IS the innovation. The real check is
//! discharged **once, natively, batched**, amortised over a long chain of proofs. This module is
//! that discharge. It authors no constraint, no `Builder` gadget and no `air_accepts` predicate; it
//! calls [`dregg_circuit::pasta_msm`] (native group arithmetic) and routes the resulting bit
//! through the LEAN-AUTHORED decision `dregg_mina_deferral_ok`
//! (`Dregg2.Circuit.Emit.PastaIpaDeferral` §5).
//!
//! ## What is being discharged, read at source
//!
//! For each proof, with
//!   * `C  = statement.proof_state.messages_for_next_wrap_proof.challenge_polynomial_commitment`
//!     — a **Vesta** point (`mina-rust/crates/ledger/src/proofs/accumulator_check.rs:44-53`), and
//!   * `u⃗ = statement.proof_state.deferred_values.bulletproof_challenges` — **16** prechallenges
//!     endo-lifted to `Fp` by `ScalarChallenge::limbs_to_field` (`accumulator_check.rs:23-38`),
//!
//! ```text
//!     C == ⟨ b_poly_coefficients(u⃗), srs.g ⟩       |srs.g| = 2^16 = 65536 Vesta generators
//! ```
//!
//! and the BATCH of `N` such claims is discharged by ONE MSM over `|G| + N` points
//! (`urs_utils.rs:34-67`):
//!
//! ```text
//!     Σ_i r^i·C_i  −  ⟨ Σ_i r^i·s(u⃗_i), G ⟩  ==  O
//! ```
//!
//! That is `PicklesRecursion.accumulatorMsm`, and `PastaIpaDeferral.discharge_touches_srs_plus_
//! batch` is the theorem that the point list is `|G| + N` and not `N·|G|`.
//!
//! ⚑ **This is the Step/Tick leg — the one Pickles ACTUALLY defers.** The Wrap/Tock `opening.sg`
//! leg is *not* deferred: kimchi folds it into its own terminal MSM with `sg_rand_base`
//! (`poly-commitment/src/ipa.rs:173-178, 219-240` at tag 0.3.0).
//!
//! ## The gap this closes, measured
//!
//! Until 2026-08-04, `dregg_mina_deferral_ok` shipped in `libdregg_lean.a` (imported by
//! `Dregg2/FFI.lean:78`) with **zero references in any `.rs` file**, and its `d=` field — the one
//! that says the batched MSM was evaluated and found to vanish — was read straight off a wire
//! string. The gate checked well-formedness and TRUSTED an assertion of discharge. It computed no
//! MSM, so `PastaIpaDeferral.opening_is_vacuous_when_sg_is_free` applied to the live runtime.
//!
//! [`discharge`] is what earns that bit. The `d=` field is now produced by evaluating the MSM, and
//! [`DischargeReceipt::wire`] is built by [`Verdict::wire_for`] which is the ONLY constructor of
//! `d=1` in this tree.
//!
//! ## Fail closed
//!
//! Every arm of [`DischargeError`] is a refusal. There is no accept path that skips the MSM, no
//! `Option` that degrades to "discharged nothing, returned Ok", and — the distinction
//! `minted-fail-open-gate-class` turns on — [`DischargeError::VerifiedGateUnavailable`] (the Lean
//! archive does not export the gate, so we cannot ASK) is a different variant from
//! [`DischargeError::Refused`] (we asked and the answer was no). Neither is an accept.

use std::time::Instant;

use dregg_circuit::pasta_msm::{
    PastaCurve, add_mod, b_poly_coefficients_at, best_window, bucketed_add_count, is_identity,
    msm_with_cost, mul_mod, naive_horner_add_count, on_curve_at, sub_mod,
};
use dregg_circuit::pasta_windowed_witness::{Pt, U256};
use sha2::{Digest, Sha256};

// =================================================================================================
// The emitted artifacts, byte-pinned
// =================================================================================================

/// The 65,536 Vesta SRS generators as `x‖y`, 32-byte little-endian canonical integers.
///
/// Provenance: `metatheory/fixtures/pickles-extractors/src/bin/accumulator_discharge_export.rs`,
/// which reads them from openmina's own `get_srs::<Fp>()` (rev `82480cd468`) and asserts
/// `accumulator_check` on seven real block proofs before writing a byte.
pub const VESTA_SRS_G_BIN: &[u8] =
    include_bytes!("../../metatheory/emitted/mina-accumulator/vesta_srs_g.bin");

/// The sha256 this build was written against. ⚑ The pin IS the gate: a re-emit turns
/// [`vesta_srs_g`] red until it is re-pinned.
pub const VESTA_SRS_G_SHA256: &str =
    "f28a8a9136eb087645fb250238f5ae70d8bf3d6abf68a0ad90ab3463450c271a";

/// The seven real Mina block accumulator claims (six devnet including the hardfork genesis, one
/// mainnet), each already accepted by openmina's own `accumulator_check`.
pub const ACCUMULATOR_CLAIMS_JSON: &str =
    include_str!("../../metatheory/emitted/mina-accumulator/accumulator_claims.json");

/// `|srs.g|` — `Fq::SRS_DEPTH` (`mina-rust/crates/ledger/src/proofs/field.rs:125`).
pub const SRS_LEN: usize = 65_536;
/// IPA rounds per Step/Tick claim (`BACKEND_TICK_ROUNDS_N`, `proofs/mod.rs:33`).
pub const ROUNDS: usize = 16;

// =================================================================================================
// Errors — every one a refusal
// =================================================================================================

/// Why a discharge did not happen, or did and said no.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DischargeError {
    /// The compiled-in SRS blob does not hash to [`VESTA_SRS_G_SHA256`].
    SrsDrift {
        /// the sha256 actually computed
        got: String,
    },
    /// The SRS blob is not `SRS_LEN` points of 64 bytes.
    SrsShape(String),
    /// A generator is not on `y² = x³ + 5` over `q`, or is the point at infinity.
    SrsPointOffCurve(usize),
    /// The claim set is empty, ragged, or a challenge/commitment is out of range.
    MalformedClaims(String),
    /// The batched MSM did not vanish. **The discharge ran and REFUSED.**
    Refused(String),
    /// The linked Lean archive does not export `dregg_mina_deferral_ok`, so the verified decision
    /// cannot be asked for. This is NOT an accept and NOT a `Refused` — we could not ask.
    VerifiedGateUnavailable(String),
    /// The verified gate answered something other than the discharge we computed, or `ERR`.
    GateDisagreed {
        /// what the MSM said
        computed: bool,
        /// what `dregg_mina_deferral_ok` returned
        gate: String,
    },
    /// ⚑ An in-circuit accumulator fold ROOT was offered for this claim, and the chain it proves
    /// does not START at this claim's commitment. See [`root_entry_binds_claim`].
    RootClaimMismatch {
        /// which of the 96 sound-encoding limbs first disagreed
        lane: usize,
        /// what the claim's `C` carries there
        want: u32,
        /// what the root published there
        got: u32,
    },
    /// The root's published entry accumulator is not 96 lanes, so it is not a projective Vesta
    /// point in the sound encoding and nothing can be compared against it.
    RootClaimShape(String),
}

impl std::fmt::Display for DischargeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DischargeError::SrsDrift { got } => {
                write!(f, "Vesta SRS blob drifted: sha256 {got}")
            }
            DischargeError::SrsShape(m) => write!(f, "Vesta SRS blob shape: {m}"),
            DischargeError::SrsPointOffCurve(i) => {
                write!(f, "SRS generator {i} is not on Vesta")
            }
            DischargeError::MalformedClaims(m) => write!(f, "malformed accumulator claims: {m}"),
            DischargeError::Refused(m) => write!(f, "accumulator discharge REFUSED: {m}"),
            DischargeError::VerifiedGateUnavailable(m) => {
                write!(f, "dregg_mina_deferral_ok unavailable: {m}")
            }
            DischargeError::GateDisagreed { computed, gate } => write!(
                f,
                "the verified gate disagreed with the MSM (computed {computed}, gate {gate:?})"
            ),
            DischargeError::RootClaimMismatch { lane, want, got } => write!(
                f,
                "the accumulator fold root does not start at this claim's commitment: sound-\
                 encoding lane {lane} is {got}, the claim carries {want}"
            ),
            DischargeError::RootClaimShape(m) => {
                write!(f, "the accumulator fold root's entry point: {m}")
            }
        }
    }
}

impl std::error::Error for DischargeError {}

// =================================================================================================
// Claims
// =================================================================================================

/// One deferred accumulator claim: `C == ⟨b_poly_coefficients(u⃗), srs.g⟩`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccumulatorClaim {
    /// Where it came from, for the receipt. Never load-bearing.
    pub label: String,
    /// The block height it was carried by.
    pub height: String,
    /// `C` — the accumulator commitment, a Vesta point in projective form.
    pub comm: Pt,
    /// `u⃗` — the endo-lifted bulletproof challenges, `ROUNDS` of them, in `Fp`.
    pub chals: Vec<U256>,
}

/// Parse the embedded seven real block claims.
pub fn embedded_claims() -> Result<Vec<AccumulatorClaim>, DischargeError> {
    parse_claims(ACCUMULATOR_CLAIMS_JSON)
}

fn field_str<'a>(hay: &'a str, key: &str, from: usize) -> Option<(&'a str, usize)> {
    let pat = format!("\"{key}\": \"");
    let s = hay[from..].find(&pat)? + from + pat.len();
    let e = hay[s..].find('"')? + s;
    Some((&hay[s..e], e))
}

/// Hand-rolled, for the same reason [`dregg_circuit::mina_opening_witness::parse_challenges`] is:
/// the verify floor keeps no JSON dependency, and a claim list that does not parse must REFUSE
/// rather than panic.
pub fn parse_claims(json: &str) -> Result<Vec<AccumulatorClaim>, DischargeError> {
    let mut out = Vec::new();
    let mut cur = 0usize;
    while let Some((label, p)) = field_str(json, "label", cur) {
        let (height, p) = field_str(json, "height", p)
            .ok_or_else(|| DischargeError::MalformedClaims("claim has no height".into()))?;
        let (cx, p) = field_str(json, "comm_x", p)
            .ok_or_else(|| DischargeError::MalformedClaims("claim has no comm_x".into()))?;
        let (cy, p) = field_str(json, "comm_y", p)
            .ok_or_else(|| DischargeError::MalformedClaims("claim has no comm_y".into()))?;
        const CK: &str = "\"challenges\": [";
        let s = json[p..]
            .find(CK)
            .ok_or_else(|| DischargeError::MalformedClaims("claim has no challenges".into()))?
            + p
            + CK.len();
        let e = json[s..]
            .find(']')
            .ok_or_else(|| DischargeError::MalformedClaims("unterminated challenges".into()))?
            + s;
        let chals: Vec<U256> = json[s..e]
            .split(',')
            .map(|t| U256::from_dec(t.trim().trim_matches('"')))
            .collect();
        if chals.len() != ROUNDS {
            return Err(DischargeError::MalformedClaims(format!(
                "claim {label} carries {} challenges, expected {ROUNDS}",
                chals.len()
            )));
        }
        out.push(AccumulatorClaim {
            label: label.to_string(),
            height: height.to_string(),
            comm: Pt {
                x: U256::from_dec(cx),
                y: U256::from_dec(cy),
                z: U256::ONE,
            },
            chals,
        });
        cur = e;
    }
    if out.is_empty() {
        return Err(DischargeError::MalformedClaims(
            "no claims parsed — an empty batch discharges nothing and must not read as an accept"
                .into(),
        ));
    }
    Ok(out)
}

// =================================================================================================
// The SRS
// =================================================================================================

/// Decode and CHECK the compiled-in Vesta SRS.
///
/// The sha256 pin is checked first, then the shape, then — `spot` generators at a stride — that the
/// point is actually on `y² = x³ + 5` over `q`. `spot = 0` checks all 65,536 (about 0.5 s); the
/// default runtime path checks a stride so the load is not the cost.
pub fn vesta_srs_g(spot: usize) -> Result<Vec<Pt>, DischargeError> {
    let mut h = Sha256::new();
    h.update(VESTA_SRS_G_BIN);
    let got = hex(&h.finalize());
    if got != VESTA_SRS_G_SHA256 {
        return Err(DischargeError::SrsDrift { got });
    }
    if VESTA_SRS_G_BIN.len() != SRS_LEN * 64 {
        return Err(DischargeError::SrsShape(format!(
            "{} bytes, expected {}",
            VESTA_SRS_G_BIN.len(),
            SRS_LEN * 64
        )));
    }
    let q = PastaCurve::Vesta.base();
    let mut g = Vec::with_capacity(SRS_LEN);
    for i in 0..SRS_LEN {
        let b = &VESTA_SRS_G_BIN[i * 64..i * 64 + 64];
        let p = Pt {
            x: le_u256(&b[..32]),
            y: le_u256(&b[32..]),
            z: U256::ONE,
        };
        if !(p.x < q && p.y < q) {
            return Err(DischargeError::SrsPointOffCurve(i));
        }
        g.push(p);
    }
    let stride = if spot == 0 { 1 } else { SRS_LEN / spot.max(1) };
    for i in (0..SRS_LEN).step_by(stride.max(1)) {
        if !on_curve_at(&q, &g[i]) {
            return Err(DischargeError::SrsPointOffCurve(i));
        }
    }
    Ok(g)
}

fn le_u256(b: &[u8]) -> U256 {
    let mut l = [0u64; 4];
    for (i, chunk) in b.chunks_exact(8).enumerate() {
        l[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    U256(l)
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

// =================================================================================================
// THE DISCHARGE
// =================================================================================================

/// What the MSM said. Constructed only by [`discharge_msm`]; there is no other way to make a
/// [`Verdict::Discharged`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The batched MSM evaluated to the identity.
    Discharged,
    /// It did not. `PastaIpaDeferral` §3b: an outstanding claim makes the opening VACUOUS, so this
    /// must refuse rather than report.
    NotDischarged,
}

impl Verdict {
    /// The `PastaIpaDeferral` §5b wire this verdict earns.
    ///
    /// ⚑ **The ONLY constructor of `d=1` in this tree.** `d` is the one field of that grammar that
    /// is not a shape read, and the caller must have earned it — this function is where it is
    /// earned and nowhere else.
    pub fn wire_for(self, srs_len: usize, rounds: usize, chal_lens: &[usize]) -> String {
        let c = chal_lens
            .iter()
            .map(|n| n.to_string())
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "n={srs_len};k={rounds};c={c};d={}",
            match self {
                Verdict::Discharged => "1",
                Verdict::NotDischarged => "0",
            }
        )
    }
}

/// Everything a caller needs to audit a discharge, measured rather than remembered.
#[derive(Clone, Debug)]
pub struct DischargeReceipt {
    /// How many claims were folded into the one MSM.
    pub claims: usize,
    /// `|srs.g|`.
    pub srs_len: usize,
    /// `|srs.g| + N` — the point list the theorem says it is.
    pub msm_points: usize,
    /// Pippenger window width used.
    pub window: usize,
    /// Complete additions actually performed.
    pub adds: usize,
    /// …of which inter-window doublings.
    pub doublings: usize,
    /// What the emitted NAIVE bit-plane scan would have cost at the same width
    /// (`PastaMsmLayouts.hornerRcbAdds`).
    pub naive_adds: usize,
    /// Wall-clock of the fold + MSM.
    pub elapsed_ms: f64,
    /// The MSM's verdict.
    pub verdict: Verdict,
    /// The `PastaIpaDeferral` §5b wire handed to the verified gate.
    pub wire: String,
    /// What `dregg_mina_deferral_ok` returned for that wire.
    pub gate_answer: String,
}

/// **The batched discharge, arithmetic only.** `batch_dlog_accumulator_check`
/// (`urs_utils.rs:11-68`) with `r` supplied by the caller.
///
/// ```text
///   points  = srs.g ‖ [C_0 … C_{N-1}]                      (|G| + N)
///   scalars = [ −Σ_i r^i·s(u⃗_i)_j ]_j ‖ [ r^i ]_i          (|G| + N)
///   verdict = ( ⟨scalars, points⟩ == O )
/// ```
///
/// ⚑ The amortisation is structural and visible here: all `N` coefficient vectors are folded into
/// ONE `|G|`-length scalar array before a single group operation happens. That is
/// `PastaIpaDeferral.discharge_touches_srs_plus_batch`.
pub fn discharge_msm(
    srs_g: &[Pt],
    claims: &[AccumulatorClaim],
    r: &U256,
) -> Result<DischargeReceipt, DischargeError> {
    if claims.is_empty() {
        return Err(DischargeError::MalformedClaims(
            "an empty batch discharges nothing".into(),
        ));
    }
    let base = PastaCurve::Vesta.base();
    let scalar = PastaCurve::Vesta.scalar();
    let n = srs_g.len();
    let rounds = claims[0].chals.len();
    if 1usize << rounds != n {
        return Err(DischargeError::MalformedClaims(format!(
            "2^{rounds} != |srs.g| = {n}; the s-vector would not tile the SRS"
        )));
    }
    for c in claims {
        if c.chals.len() != rounds {
            return Err(DischargeError::MalformedClaims(format!(
                "claim {} carries {} challenges, the batch is at {rounds}",
                c.label,
                c.chals.len()
            )));
        }
        if !(c.comm.x < base && c.comm.y < base) {
            return Err(DischargeError::MalformedClaims(format!(
                "claim {}'s commitment is not a reduced Vesta coordinate pair",
                c.label
            )));
        }
        if !on_curve_at(&base, &c.comm) {
            return Err(DischargeError::MalformedClaims(format!(
                "claim {}'s commitment is not on Vesta",
                c.label
            )));
        }
        if !(*r < scalar) {
            return Err(DischargeError::MalformedClaims(
                "the batching scalar is not reduced".into(),
            ));
        }
    }

    let t0 = Instant::now();

    // rs = [1, r, r², …]
    let mut rs = Vec::with_capacity(claims.len());
    let mut acc = U256::ONE;
    for _ in 0..claims.len() {
        rs.push(acc);
        acc = mul_mod(&scalar, &acc, r);
    }

    // ONE |G|-length vector, folded before any group element is touched.
    let mut srs_scalars = vec![U256::ZERO; n];
    for (i, c) in claims.iter().enumerate() {
        let s = b_poly_coefficients_at(&scalar, &c.chals);
        debug_assert_eq!(s.len(), n);
        for j in 0..n {
            let t = mul_mod(&scalar, &s[j], &rs[i]);
            srs_scalars[j] = sub_mod(&scalar, &srs_scalars[j], &t);
        }
    }

    let mut points: Vec<Pt> = Vec::with_capacity(n + claims.len());
    points.extend_from_slice(srs_g);
    points.extend(claims.iter().map(|c| c.comm));
    let mut scalars = srs_scalars;
    scalars.extend_from_slice(&rs);

    let c = best_window(points.len(), 255);
    let (out, cost) = msm_with_cost(&base, &points, &scalars, c);
    let elapsed_ms = t0.elapsed().as_secs_f64() * 1e3;

    let verdict = if is_identity(&out) {
        Verdict::Discharged
    } else {
        Verdict::NotDischarged
    };
    let chal_lens: Vec<usize> = claims.iter().map(|c| c.chals.len()).collect();

    Ok(DischargeReceipt {
        claims: claims.len(),
        srs_len: n,
        msm_points: points.len(),
        window: cost.window,
        adds: cost.adds,
        doublings: cost.doublings,
        naive_adds: naive_horner_add_count(points.len(), 255),
        elapsed_ms,
        verdict,
        wire: verdict.wire_for(n, rounds, &chal_lens),
        gate_answer: String::new(),
    })
}

/// **The full discharge: compute, then ask the VERIFIED gate, then refuse unless both say yes.**
///
/// The order is the point. The MSM runs first and its result BUILDS the wire; the Lean gate
/// `dregg_mina_deferral_ok` then re-decides the whole batch shape (`2^k = |srs.g|`, non-empty,
/// every claim at exactly `k` challenges, AND discharged) over that wire. A disagreement between
/// the two is [`DischargeError::GateDisagreed`] — never a silent preference for either.
pub fn discharge(
    srs_g: &[Pt],
    claims: &[AccumulatorClaim],
    r: &U256,
) -> Result<DischargeReceipt, DischargeError> {
    let mut receipt = discharge_msm(srs_g, claims, r)?;
    let answer = dregg_lean_ffi::bridge_lc_ffi::run_mina_deferral_ok(&receipt.wire)
        .map_err(DischargeError::VerifiedGateUnavailable)?;
    receipt.gate_answer = answer.clone();
    let computed = receipt.verdict == Verdict::Discharged;
    // ⚑ A NON-VERDICT ANSWER IS NOT A `no`, AND MUST NOT BE COMPARED AS ONE.
    //
    // Until 2026-08-08 this read `let gate_ok = answer == "1";`, which folded `"ERR"` — the gate
    // REFUSING TO READ the wire — into the same `false` as a genuine `"0"`. That defeated this
    // function's entire purpose on the negative polarity: when the MSM refused (`computed =
    // false`) and the gate answered `"ERR"`, `gate_ok == computed` held, `GateDisagreed` did NOT
    // fire, and `discharge` went on to report `Refused("the batched MSM … did not vanish")` as
    // though the verified gate had CONCURRED — when in truth the gate had never decided anything.
    // The cross-check could only ever fire on the positive polarity, which is the half that needs
    // it least. `GateDisagreed`'s own docblock already said "or `ERR`"; the code could not.
    //
    // Decoding to a two-valued verdict FIRST makes the fusion unrepresentable: `gate_ok` is now
    // constructible only from an answer that actually is a verdict.
    let gate_ok = match answer.as_str() {
        "1" => true,
        "0" => false,
        _ => {
            return Err(DischargeError::GateDisagreed {
                computed,
                gate: answer,
            });
        }
    };
    if gate_ok != computed {
        return Err(DischargeError::GateDisagreed {
            computed,
            gate: answer,
        });
    }
    if !computed {
        return Err(DischargeError::Refused(format!(
            "the batched MSM over {} points did not vanish ({} claims, {} complete adds)",
            receipt.msm_points, receipt.claims, receipt.adds
        )));
    }
    Ok(receipt)
}

/// Whether the linked archive exports the verified gate. Absent, [`discharge`] REFUSES; there is
/// no fallback that decides in Rust.
pub fn verified_gate_available() -> bool {
    dregg_lean_ffi::bridge_lc_ffi::mina_deferral_ok_available()
}

/// The bucketed-vs-naive comparison at a stated width, for reporting. Returns
/// `(naive_adds, bucketed_adds, best_window)`.
pub fn cost_comparison(n: usize, nbits: usize) -> (usize, usize, usize) {
    let c = best_window(n, nbits);
    (
        naive_horner_add_count(n, nbits),
        bucketed_add_count(n, nbits, c),
        c,
    )
}

/// Displace a claim's commitment by a Vesta point — the forgery the falsifier tests use.
///
/// Exposed because a discharge that only ever accepts has measured nothing, and the refusal
/// polarity has to be constructible from outside this module (the example driver builds it).
pub fn forge_commitment(claim: &AccumulatorClaim, by: &Pt) -> AccumulatorClaim {
    let base = PastaCurve::Vesta.base();
    let mut c = claim.clone();
    c.comm = dregg_circuit::pasta_msm::complete_add(&base, &c.comm, by);
    // renormalise z to 1 is unnecessary — the MSM is projective throughout
    c.label = format!("{} [FORGED sg]", c.label);
    c
}

// =================================================================================================
// ⚑ THE SEAM TO THE IN-CIRCUIT CHECK — whose claim is the chain the circuit proved?
// =================================================================================================

/// Limbs per Pasta field element in the sound encoding (`PastaFieldSound.SK`).
pub const SOUND_SK: usize = 32;
/// A projective point is `3 · SOUND_SK` limbs — the width
/// `Dregg2.Circuit.Emit.MinaAccumulatorAir` publishes at `PI[0..95]` and the width a fold node
/// carries with `cb.connect`.
pub const SOUND_POINT_LIMBS: usize = 3 * SOUND_SK;

/// The 32 little-endian 8-bit limbs of a reduced coordinate — `PastaFieldSound.limbAt`, which is
/// what `rcbSoundRow` writes into a trace cell and therefore what a segment publishes.
fn sound_limbs(v: &U256) -> [u32; SOUND_SK] {
    let mut out = [0u32; SOUND_SK];
    for (j, slot) in out.iter_mut().enumerate() {
        *slot = u32::from((v.0[j / 8] >> (8 * (j % 8))) as u8);
    }
    out
}

/// ⚑ **THE 96 LANES A CLAIM'S COMMITMENT OCCUPIES AS THE CHAIN'S ENTRY ACCUMULATOR.**
///
/// Read the batched discharge as a running sum and the claim IS the initial accumulator:
///
/// ```text
///     acc_0 = C  ;  acc_{r+1} = acc_r + A_r  ;  acc_n = O
/// ```
///
/// so `C` in projective form `(x : y : 1)` is what `MinaAccumulatorAir`'s first-row pins publish.
/// `z = 1` is not a convention chosen here: [`parse_claims`] builds every commitment with
/// `z: U256::ONE`, and the sound encoding of `1` is `[1, 0, …, 0]`.
pub fn claim_entry_limbs(claim: &AccumulatorClaim) -> [u32; SOUND_POINT_LIMBS] {
    let mut out = [0u32; SOUND_POINT_LIMBS];
    out[..SOUND_SK].copy_from_slice(&sound_limbs(&claim.comm.x));
    out[SOUND_SK..2 * SOUND_SK].copy_from_slice(&sound_limbs(&claim.comm.y));
    out[2 * SOUND_SK..].copy_from_slice(&sound_limbs(&claim.comm.z));
    out
}

/// ⚑⚑ **REFUSE UNLESS THE CIRCUIT'S CHAIN STARTS AT *THIS* CLAIM.**
///
/// An accumulator fold root publishes `acc_in(96) ‖ acc_out(96)`
/// (`dregg_recursion_verify::accumulator_root`). A verified root with a vanishing `acc_out` says
/// *"some chain of complete additions, starting at the point I published, reached infinity"* — and
/// **which point that is** is the whole difference between *some* claim discharging and *this
/// block's* claim discharging.
///
/// This is that comparison: **96 lanes, elementwise, no digest and therefore no birthday bound** —
/// the shape `LightClientMinaAir`'s `TIP_STATE` seam already takes, and the shape the `ANCHOR_STATE`
/// lanes are refused at. It is a REFUSAL made by the consumer, not a gate; say it that way.
///
/// ⚠ And say what it still does not reach. Binding `acc_in` to the claim does NOT bind the ADDENDS
/// to the SRS — the routing residual `MinaAccumulatorAir` §4 prices — nor does it relate the claim
/// to a tracked head. A caller that holds `C` from this block's
/// `messages_for_next_wrap_proof.challenge_polynomial_commitment` and calls this has closed the
/// first of those three, and only the first.
///
/// `root_acc_in` is the root's published entry block as plain canonical field values, so this
/// crate needs no recursion edge to make the comparison
/// (`scripts/check-recursion-closure.py` stays as it is).
pub fn root_entry_binds_claim(
    root_acc_in: &[u32],
    claim: &AccumulatorClaim,
) -> Result<(), DischargeError> {
    if root_acc_in.len() != SOUND_POINT_LIMBS {
        return Err(DischargeError::RootClaimShape(format!(
            "{} lane(s), expected {SOUND_POINT_LIMBS} (three coordinates of {SOUND_SK} limbs)",
            root_acc_in.len()
        )));
    }
    let want = claim_entry_limbs(claim);
    for (lane, (&got, &w)) in root_acc_in.iter().zip(want.iter()).enumerate() {
        if got != w {
            return Err(DischargeError::RootClaimMismatch { lane, want: w, got });
        }
    }
    Ok(())
}

/// The Vesta generator `(−1, 2)`, for building forgeries.
pub fn vesta_generator() -> Pt {
    let q = PastaCurve::Vesta.base();
    Pt {
        x: sub_mod(&q, &U256::ZERO, &U256::ONE),
        y: add_mod(&q, &U256::ONE, &U256::ONE),
        z: U256::ONE,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A cut-down SRS and a claim honestly built against it. `2^rounds` generators taken from the
    /// real Vesta SRS, so the arithmetic is the real arithmetic; only the WIDTH is reduced so the
    /// default test profile stays fast. The full-width run over the seven real Mina claims is
    /// `bridge/examples/mina_accumulator_discharge.rs` and the `#[ignore]`d test below.
    fn small_batch(rounds: usize, howmany: usize) -> (Vec<Pt>, Vec<AccumulatorClaim>) {
        let g = vesta_srs_g(64).expect("srs");
        let sub: Vec<Pt> = g[..1usize << rounds].to_vec();
        let scalar = PastaCurve::Vesta.scalar();
        let base = PastaCurve::Vesta.base();
        let claims = (0..howmany)
            .map(|i| {
                let chals: Vec<U256> = (0..rounds)
                    .map(|j| U256::from_u64(1 + (i as u64) * 7919 + (j as u64) * 104_729))
                    .collect();
                let s = b_poly_coefficients_at(&scalar, &chals);
                let comm = msm_with_cost(&base, &sub, &s, 5).0;
                AccumulatorClaim {
                    label: format!("synthetic-{i}"),
                    height: format!("{i}"),
                    comm,
                    chals,
                }
            })
            .collect();
        (sub, claims)
    }

    #[test]
    fn srs_blob_is_pinned_and_on_curve() {
        let g = vesta_srs_g(256).expect("the pinned Vesta SRS must load");
        assert_eq!(g.len(), SRS_LEN);
        let q = PastaCurve::Vesta.base();
        for i in [0usize, 1, 12_345, SRS_LEN - 1] {
            assert!(on_curve_at(&q, &g[i]), "generator {i} is not on Vesta");
            assert!(!is_identity(&g[i]));
        }
    }

    #[test]
    fn the_seven_real_claims_parse() {
        let claims = embedded_claims().expect("claims parse");
        assert_eq!(claims.len(), 7, "expected seven real block claims");
        let q = PastaCurve::Vesta.base();
        for c in &claims {
            assert_eq!(c.chals.len(), ROUNDS);
            assert!(
                on_curve_at(&q, &c.comm),
                "claim {} commitment is not on Vesta",
                c.label
            );
        }
        assert!(claims.iter().any(|c| c.height == "539508"));
        assert!(claims.iter().any(|c| c.label.contains("mainnet")));
    }

    /// ⚑ **BOTH POLARITIES, at reduced width.** An honest batch discharges; a forged commitment is
    /// REFUSED. This is the pair the whole module exists for.
    #[test]
    fn honest_discharges_and_forged_sg_is_refused() {
        let (srs, claims) = small_batch(10, 3);
        let r = U256::from_u64(0x5EED_1DEA_ACC0_0001);

        let ok = discharge_msm(&srs, &claims, &r).expect("honest batch");
        assert_eq!(
            ok.verdict,
            Verdict::Discharged,
            "an honest batch was refused"
        );
        assert_eq!(ok.msm_points, srs.len() + claims.len());
        assert!(ok.wire.ends_with(";d=1"));

        // the forgery `PastaIpaDeferral.opening_is_vacuous_when_sg_is_free` says is otherwise free
        for i in 0..claims.len() {
            let mut forged = claims.clone();
            forged[i] = forge_commitment(&claims[i], &vesta_generator());
            let bad = discharge_msm(&srs, &forged, &r).expect("forged batch still computes");
            assert_eq!(
                bad.verdict,
                Verdict::NotDischarged,
                "a FORGED commitment at slot {i} was accepted"
            );
            assert!(bad.wire.ends_with(";d=0"));
        }

        // …and a tampered CHALLENGE, which moves the s-vector rather than the commitment
        let mut ch = claims.clone();
        ch[1].chals[4] = add_mod(&PastaCurve::Vesta.scalar(), &ch[1].chals[4], &U256::ONE);
        assert_eq!(
            discharge_msm(&srs, &ch, &r).unwrap().verdict,
            Verdict::NotDischarged,
            "a tampered challenge was accepted"
        );

        // …and swapping two claims' commitments
        let mut sw = claims.clone();
        sw.swap(0, 2);
        let swapped_comms: Vec<AccumulatorClaim> = claims
            .iter()
            .enumerate()
            .map(|(i, c)| AccumulatorClaim {
                comm: sw[i].comm,
                ..c.clone()
            })
            .collect();
        assert_eq!(
            discharge_msm(&srs, &swapped_comms, &r).unwrap().verdict,
            Verdict::NotDischarged,
            "swapped commitments were accepted"
        );
    }

    /// The batching is not a formality: the SAME forgery must be caught at several `r`, and the
    /// honest batch must discharge at all of them.
    #[test]
    fn the_verdict_does_not_depend_on_the_batching_scalar() {
        let (srs, claims) = small_batch(9, 4);
        let mut forged = claims.clone();
        forged[2] = forge_commitment(&claims[2], &vesta_generator());
        for seed in [1u64, 2, 3, 0xDEAD_BEEF, 0x1234_5678_9ABC_DEF0] {
            let r = U256::from_u64(seed);
            assert_eq!(
                discharge_msm(&srs, &claims, &r).unwrap().verdict,
                Verdict::Discharged
            );
            assert_eq!(
                discharge_msm(&srs, &forged, &r).unwrap().verdict,
                Verdict::NotDischarged,
                "the forgery survived r = {seed}"
            );
        }
    }

    /// A single claim is `r`-free (`r^0 = 1`), so the one-claim case is the DETERMINISTIC check and
    /// must behave identically.
    #[test]
    fn one_claim_is_the_deterministic_check() {
        let (srs, claims) = small_batch(10, 1);
        for seed in [1u64, 7, 99] {
            assert_eq!(
                discharge_msm(&srs, &claims, &U256::from_u64(seed))
                    .unwrap()
                    .verdict,
                Verdict::Discharged
            );
        }
        let forged = vec![forge_commitment(&claims[0], &vesta_generator())];
        assert_eq!(
            discharge_msm(&srs, &forged, &U256::ONE).unwrap().verdict,
            Verdict::NotDischarged
        );
    }

    /// Shape refusals, each its own variant.
    #[test]
    fn malformed_batches_refuse() {
        let (srs, claims) = small_batch(9, 2);
        assert!(matches!(
            discharge_msm(&srs, &[], &U256::ONE),
            Err(DischargeError::MalformedClaims(_))
        ));
        let mut short = claims.clone();
        short[1].chals.pop();
        assert!(matches!(
            discharge_msm(&srs, &short, &U256::ONE),
            Err(DischargeError::MalformedClaims(_))
        ));
        // an SRS that the s-vector does not tile
        assert!(matches!(
            discharge_msm(&srs[..100], &claims, &U256::ONE),
            Err(DischargeError::MalformedClaims(_))
        ));
        // a commitment off the curve
        let mut off = claims.clone();
        off[0].comm.y = add_mod(&PastaCurve::Vesta.base(), &off[0].comm.y, &U256::ONE);
        assert!(matches!(
            discharge_msm(&srs, &off, &U256::ONE),
            Err(DischargeError::MalformedClaims(_))
        ));
    }

    /// `d=1` has exactly one constructor, and it is gated on the verdict.
    #[test]
    fn the_discharged_bit_is_earned() {
        assert!(
            Verdict::Discharged
                .wire_for(65536, 16, &[16, 16])
                .ends_with(";d=1")
        );
        assert!(
            Verdict::NotDischarged
                .wire_for(65536, 16, &[16, 16])
                .ends_with(";d=0")
        );
        assert_eq!(
            Verdict::Discharged.wire_for(1024, 10, &[10]),
            "n=1024;k=10;c=10;d=1"
        );
    }

    /// ⚑ **THE EXPORT, ACTUALLY CALLED.** Both polarities routed through the LEAN gate rather than
    /// only through our arithmetic: an honest batch's `d=1` wire must come back `"1"`, and a forged
    /// one's `d=0` must come back `"0"` and surface as [`DischargeError::Refused`].
    ///
    /// Uses the crate-wide `DREGG_TEST_REQUIRE_LEAN` arming rather than a private skip: unarmed and
    /// archive-absent it reports and returns, armed it PANICS. That is the same contract every
    /// other verified-decision test in this tree has, so this one cannot be the quiet exception.
    #[test]
    fn both_polarities_through_the_verified_lean_gate() {
        if !dregg_lean_ffi::demand_lean(verified_gate_available(), "dregg_mina_deferral_ok") {
            return;
        }
        let (srs, claims) = small_batch(10, 3);
        let r = U256::from_u64(0x5EED_1DEA_ACC0_0001);

        let ok =
            discharge(&srs, &claims, &r).expect("the verified gate must ACCEPT an honest batch");
        assert_eq!(ok.gate_answer, "1");
        assert_eq!(ok.verdict, Verdict::Discharged);

        let mut forged = claims.clone();
        forged[1] = forge_commitment(&claims[1], &vesta_generator());
        match discharge(&srs, &forged, &r) {
            Err(DischargeError::Refused(_)) => {}
            other => panic!("a FORGED sg was not refused by the full path: {other:?}"),
        }

        // …and the gate refuses an undischarged batch on its own terms, which is
        // `deferral_gate_refuses_undischarged` exercised over the C ABI rather than only proved.
        assert_eq!(
            dregg_lean_ffi::bridge_lc_ffi::run_mina_deferral_ok("n=1024;k=10;c=10,10,10;d=0")
                .unwrap(),
            "0"
        );
        assert_eq!(
            dregg_lean_ffi::bridge_lc_ffi::run_mina_deferral_ok("n=1024;k=10;c=10,10,10;d=1")
                .unwrap(),
            "1"
        );
        // a mistiled SRS, an empty batch, a short claim — each its own refusal
        assert_eq!(
            dregg_lean_ffi::bridge_lc_ffi::run_mina_deferral_ok("n=1000;k=10;c=10;d=1").unwrap(),
            "0"
        );
        assert_eq!(
            dregg_lean_ffi::bridge_lc_ffi::run_mina_deferral_ok("n=1024;k=10;c=;d=1").unwrap(),
            "ERR"
        );
        assert_eq!(
            dregg_lean_ffi::bridge_lc_ffi::run_mina_deferral_ok("n=1024;k=10;c=10,9;d=1").unwrap(),
            "0"
        );
        // the real Step/Tick shape
        assert_eq!(
            dregg_lean_ffi::bridge_lc_ffi::run_mina_deferral_ok("n=65536;k=16;c=16;d=1").unwrap(),
            "1"
        );
    }

    /// ⚑ **THE SOUND ENCODING IS THE ONE THE AIR PUBLISHES** — 32 little-endian bytes per
    /// coordinate, and `z = 1` really is `[1, 0, …]`. If this drifted, the seam below would compare
    /// two encodings of the same point and refuse an honest root.
    #[test]
    fn the_entry_limbs_are_the_sound_encoding() {
        let claims = embedded_claims().expect("claims");
        let l = claim_entry_limbs(&claims[0]);
        assert_eq!(l.len(), 96);
        // z = 1
        assert_eq!(l[64], 1);
        assert!(l[65..].iter().all(|&b| b == 0), "z is (1, 0, ..., 0)");
        // every lane is a byte
        assert!(l.iter().all(|&b| b < 256));
        // and the x block really recomposes to C.x
        let x = claims[0].comm.x;
        for j in 0..32usize {
            assert_eq!(l[j], u32::from((x.0[j / 8] >> (8 * (j % 8))) as u8));
        }
    }

    /// ⚑⚑ **BOTH POLARITIES OF THE CLAIM-TO-ROOT SEAM.**
    ///
    /// A root that starts at this claim's `C` is accepted; a root displaced in ANY ONE of the 96
    /// lanes is refused, and the refusal names the lane. Every one of the seven real block claims
    /// drives it, and every claim is checked to refuse against every OTHER claim — so the seam is
    /// discriminating between real Mina commitments, not merely between a value and a scribble.
    #[test]
    fn the_root_entry_seam_binds_the_claim_in_both_polarities() {
        let claims = embedded_claims().expect("claims");
        assert_eq!(claims.len(), 7);

        for c in &claims {
            let honest = claim_entry_limbs(c);
            root_entry_binds_claim(&honest, c).expect("an honest root entry must be accepted");

            // one displaced lane, anywhere in the 96
            for lane in [0usize, 1, 31, 32, 63, 64, 95] {
                let mut bad = honest;
                bad[lane] = (bad[lane] + 1) % 256;
                assert_ne!(bad[lane], honest[lane], "the tamper must MOVE the lane");
                match root_entry_binds_claim(&bad, c) {
                    Err(DischargeError::RootClaimMismatch { lane: got, .. }) => {
                        assert_eq!(got, lane, "the refusal must name the lane that moved")
                    }
                    other => panic!("a displaced entry lane was not refused: {other:?}"),
                }
            }
        }

        // ⚑ and it discriminates between REAL claims: no block's root entry satisfies another's.
        for (i, a) in claims.iter().enumerate() {
            for (j, b) in claims.iter().enumerate() {
                if i == j {
                    continue;
                }
                assert!(
                    root_entry_binds_claim(&claim_entry_limbs(a), b).is_err(),
                    "claim {i}'s entry point satisfied claim {j}'s bind — the seam is not \
                     discriminating between real Mina commitments"
                );
            }
        }

        // a shape fault is its own variant, not a mismatch
        assert!(matches!(
            root_entry_binds_claim(&[0u32; 95], &claims[0]),
            Err(DischargeError::RootClaimShape(_))
        ));
    }

    /// The bucketed-vs-naive numbers, at the two widths this campaign quotes.
    #[test]
    fn bucketing_is_about_ten_times_cheaper() {
        for (n, nbits) in [(65536usize, 255usize), (32768, 255), (32768, 128)] {
            let (naive, bucketed, c) = cost_comparison(n, nbits);
            assert!(
                bucketed * 9 < naive,
                "n={n} nbits={nbits} c={c}: {naive} -> {bucketed} is under 9x"
            );
        }
    }

    /// ⚑ THE FULL-WIDTH RUN over the SEVEN REAL MINA CLAIMS. `#[ignore]`d only because it is
    /// minutes of native Pasta arithmetic in one test; `bridge/examples/mina_accumulator_discharge`
    /// is the driver that runs it and prints the measurement.
    #[test]
    #[ignore = "full 2^16 native discharge — minutes; run the example driver instead"]
    fn real_mina_claims_discharge_and_a_forged_one_does_not() {
        let srs = vesta_srs_g(0).expect("srs");
        let claims = embedded_claims().expect("claims");
        let r = U256::from_u64(0x5EED_1DEA_ACC0_0001);
        assert_eq!(
            discharge_msm(&srs, &claims, &r).unwrap().verdict,
            Verdict::Discharged
        );
        let mut forged = claims.clone();
        forged[3] = forge_commitment(&claims[3], &vesta_generator());
        assert_eq!(
            discharge_msm(&srs, &forged, &r).unwrap().verdict,
            Verdict::NotDischarged
        );
    }
}
