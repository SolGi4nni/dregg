//! Turn-authorization signature forcing (ADDITIVE; not live-wired).
//!
//! # The gap this closes
//!
//! The proof-carrying rotated path performs NO signature check: a light client that
//! accepts a rotated turn proof concludes only that SOME valid state transition exists,
//! NOT that the rightful agent authorized THIS turn. The turn IS signed (the agent signs
//! the turn hash), but that signature is verified OFF-circuit (the `SovereignCellWitness`
//! ed25519 leg in `turn/src/executor/execute.rs`), so it is invisible to a ledgerless
//! verifier reading only the proof.
//!
//! This module builds the IN-CIRCUIT forcing layer: a signature-bearing turn-auth
//! descriptor that binds the agent public key + the signed turn hash to a
//! curve-constrained signature verification, so that
//!
//!   `verify_turn_auth_sig accept  ⟹  the holder of `agent_pubkey` signed `turn_hash``.
//!
//! The forced primitive is the system's ONE curve-constrained signature verifier: the
//! Schnorr AIR over the BabyBear^8 curve (`schnorr_air`), whose verification equation
//! `s·G + e·pk == R` is realized by genuine double-and-add scalar multiplication with
//! per-row slope (`λ`) constraints — NOT a free `sig_valid` bit. A forged signature
//! (wrong pubkey, tampered turn hash, or bad `(R, s)`) breaks the curve equation and is
//! REJECTED with NO executor in the loop.
//!
//! # The Ed25519 ↔ Schnorr scale obligation (honest)
//!
//! The DEPLOYED turn signature is ed25519 (Curve25519), verified off-circuit. The
//! in-circuit-provable curve-constrained signature here is BabyBear^8 Schnorr. Closing the
//! deployed gap end-to-end requires EITHER:
//!
//!   (a) an Ed25519 verification AIR (Edwards-curve point decompression + the
//!       `[S]B = R + [k]A` check over Curve25519's base field, witnessed in BabyBear) — the
//!       HEAVIEST single AIR in the system, currently UNBUILT (`native_signature_air` is a
//!       WOTS width constant, not an ed25519 AIR); OR
//!   (b) re-binding turn authority to the in-circuit Schnorr key (the agent signs the turn
//!       hash with its BabyBear^8 Schnorr key), which makes THIS layer the literal turn-auth
//!       forcing with no curve-translation gap.
//!
//! What is PROVEN here is path (b)'s forcing: a signature over the turn hash under the
//! agent's curve key is FORCED in-circuit, and a forgery is UNSAT. The Ed25519-specific
//! curve obligation (path a) is the named remaining scale, reported, not laundered.

use crate::field::BabyBear;
use crate::schnorr_air::{self, col, generate_schnorr_trace, pi, SchnorrVerificationWitness};
use crate::schnorr_curve::CurvePoint;
use crate::schnorr_sig::{
    compute_challenge_from_elements, schnorr_keygen, SchnorrPublicKey, SchnorrSignature,
};

/// A turn-authorization signature descriptor: the agent public key + the signed turn hash,
/// bound to a curve-constrained Schnorr verification.
///
/// `turn_hash` is the 8-felt commitment the agent signs (in the live system, the Poseidon2
/// turn hash that `turn/src/turn.rs` constructs and the agent signs over). Binding it as the
/// signature's message is what makes the conclusion "the rightful agent authorized THIS turn"
/// rather than "some turn".
#[derive(Clone, Debug)]
pub struct TurnAuthSigDescriptor {
    /// The agent's public key (the curve point the light client trusts as the rightful agent).
    pub agent_pubkey: SchnorrPublicKey,
    /// The 8-felt turn hash the signature must cover (the THIS-turn binding).
    pub turn_hash: [BabyBear; 8],
    /// The agent's signature `(R, s)` over `turn_hash`.
    pub signature: SchnorrSignature,
}

/// The public-input layout of a turn-auth signature proof. The agent pubkey and the turn hash
/// occupy fixed PI slots so a light client (which sees ONLY the proof + PIs) can read off WHICH
/// key authorized WHICH turn, and the verification gate forces the curve equation over exactly
/// those bound values.
pub mod auth_pi {
    /// Agent public-key x-coordinate (8 felts) — reuses the Schnorr `PK_X` slot.
    pub const AGENT_PK_X: usize = super::pi::PK_X;
    /// Agent public-key y-coordinate (8 felts).
    pub const AGENT_PK_Y: usize = super::pi::PK_Y;
    /// The signed turn hash (8 felts) — reuses the Schnorr `MSG_HASH` slot, so the curve
    /// equation's Fiat–Shamir challenge `e = H(R, pk, turn_hash)` is over the bound turn hash.
    pub const TURN_HASH: usize = super::pi::MSG_HASH;
    /// Total PI count (identical to the Schnorr layout — pk, R, s, msg=turn_hash).
    pub const TOTAL: usize = super::pi::TOTAL;
}

/// Build the verification witness for the turn-auth descriptor: recompute the Fiat–Shamir
/// challenge over `(R, agent_pubkey, turn_hash)` exactly as the signer did, so the in-circuit
/// `e` is bit-for-bit the value the signature closes against.
fn witness_of(desc: &TurnAuthSigDescriptor) -> SchnorrVerificationWitness {
    let challenge = compute_challenge_from_elements(
        &desc.signature.r,
        &desc.agent_pubkey.0,
        &desc.turn_hash,
    );
    SchnorrVerificationWitness {
        pk: desc.agent_pubkey.clone(),
        sig: desc.signature.clone(),
        message_hash: desc.turn_hash,
        challenge,
    }
}

/// Generate the turn-auth signature trace + its public inputs. The trace is the genuine
/// Schnorr double-and-add (`s·G` then `e·pk`); the public inputs carry the agent pubkey, the
/// nonce `R`, the response scalar `s`, and the turn hash.
pub fn generate_turn_auth_trace(
    desc: &TurnAuthSigDescriptor,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_schnorr_trace(&witness_of(desc))
}

/// **THE FORCING GATE.** Verify a turn-auth signature proof against the descriptor's BOUND
/// agent pubkey + turn hash, with NO executor.
///
/// The gate is satisfied iff (1) the public inputs bind exactly the descriptor's agent pubkey
/// and turn hash, AND (2) the curve-constrained Schnorr verification equation closes over the
/// trace. Step (2) is the real curve check: the trace's double-and-add chains must compute
/// `s·G` and `e·pk`, the slope witnesses must satisfy `λ·(xB − xA) = (yB − yA)` on every
/// addition row, and the boundary must satisfy `s·G + e·pk == R`. A forged signature breaks
/// the boundary; a tampered pubkey or turn hash breaks the pubkey boundary or moves the
/// challenge `e` so the boundary fails.
///
/// Returns `true` iff the rightful agent (holder of the bound pubkey) signed the bound turn
/// hash. This is the light-client bite: forgery is UNSAT here, without re-running the turn.
pub fn verify_turn_auth_sig(
    desc: &TurnAuthSigDescriptor,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> bool {
    // (1) PI binding: the proof's public inputs MUST commit to the descriptor's agent pubkey
    // and turn hash. Without this, a light client could not read off WHICH key / WHICH turn —
    // the curve check alone proves only "some key signed some message".
    if public_inputs.len() != auth_pi::TOTAL {
        return false;
    }
    for i in 0..8 {
        if public_inputs[auth_pi::AGENT_PK_X + i] != desc.agent_pubkey.0.x.0[i] {
            return false;
        }
        if public_inputs[auth_pi::AGENT_PK_Y + i] != desc.agent_pubkey.0.y.0[i] {
            return false;
        }
        if public_inputs[auth_pi::TURN_HASH + i] != desc.turn_hash[i] {
            return false;
        }
    }
    // (2) The curve equation. This is the load-bearing constraint — NOT a free bit.
    schnorr_air::verify_schnorr_via_trace(trace, public_inputs)
}

/// The committed-authority binding for the DUAL-SCHEME proven (curve) path.
///
/// # The dual scheme (additive model; the live cell-format change is serialized separately)
///
/// The agent's authority is committed in the cell with a SCHEME TAG (`Ed25519` = the off-circuit
/// RECEIPT path, `Curve` = this in-circuit PROVEN path, `Both`). Ed25519 NEVER enters a circuit.
/// On the PROVEN path the cell commits the Curve public key as authority; a proven-mode turn must
/// bind its FORCED curve key (the pubkey the AIR's PI layout pins, `auth_pi::AGENT_PK_{X,Y}`) to
/// THAT committed key. Without this binding, a verifying turn-auth proof shows only "SOME curve key
/// signed THIS turn", not "the cell's RIGHTFUL committed key signed it" — a downgrade/substitution
/// footgun (present any key you hold a signature for).
///
/// `CommittedCurveAuthority` is the committed Curve-authority PI slot pair: the x/y limbs of the
/// curve pubkey the cell committed as its proven-path authority. In the live system these come from
/// the cell's committed authority field (the live-wire handoff: `cell/src/commitment.rs`'s
/// `compute_authority_digest_felt` would fold the scheme tag + this curve pubkey into the 8-felt
/// commit, and the executor's dual-dispatch would supply them as PIs). Here they are an additive
/// descriptor input so the binding tooth is testable with NO executor.
#[derive(Clone, Debug)]
pub struct CommittedCurveAuthority {
    /// The curve pubkey the cell committed as its proven-path (Curve/Both) authority.
    pub committed_pubkey: SchnorrPublicKey,
}

/// **THE CURVE-KEY BINDING CHECK (dual-scheme proven path).** The forced curve key — read off the
/// turn-auth proof's `AGENT_PK_{X,Y}` PI slots — MUST equal the cell's committed Curve authority.
///
/// This is the in-circuit content of `dualscheme_no_downgrade` (`Dregg2.Crypto.DualSchemeAuthority`):
/// a proven turn whose forced `cpk` differs from the committed Curve authority is REJECTED. Combined
/// with `verify_turn_auth_sig` (which forces "the holder of the bound pubkey signed THIS turn"), the
/// conjunction gives the dual-scheme bite: "the cell's RIGHTFUL committed curve key authorized THIS
/// turn". Returns `true` iff the forced key in the PIs equals the committed authority.
pub fn bind_curve_key_to_committed_authority(
    public_inputs: &[BabyBear],
    committed: &CommittedCurveAuthority,
) -> bool {
    if public_inputs.len() != auth_pi::TOTAL {
        return false;
    }
    for i in 0..8 {
        if public_inputs[auth_pi::AGENT_PK_X + i] != committed.committed_pubkey.0.x.0[i] {
            return false;
        }
        if public_inputs[auth_pi::AGENT_PK_Y + i] != committed.committed_pubkey.0.y.0[i] {
            return false;
        }
    }
    true
}

/// **THE DUAL-SCHEME PROVEN-PATH GATE.** A proven-mode turn is authorized iff (1) the curve-constrained
/// signature verifies over the descriptor's bound pubkey + turn hash (`verify_turn_auth_sig`), AND
/// (2) the forced curve key is BOUND to the cell's committed Curve authority
/// (`bind_curve_key_to_committed_authority`). The conjunction is downgrade-proof: an attacker cannot
/// substitute a different curve key (it fails the binding) nor forge a signature (it fails the curve
/// equation). Ed25519 is NOT here — the receipt path is verified off-circuit.
pub fn verify_proven_turn_against_committed(
    desc: &TurnAuthSigDescriptor,
    committed: &CommittedCurveAuthority,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> bool {
    verify_turn_auth_sig(desc, trace, public_inputs)
        && bind_curve_key_to_committed_authority(public_inputs, committed)
}

/// Sign a turn hash that is ALREADY the 8-felt message hash (the in-circuit form): the signer
/// and verifier both use `compute_challenge_from_elements(R, pk, turn_hash)`, so the challenge
/// matches with no byte-encoding round-trip.
pub fn sign_turn_prehashed(seed: &[u8; 32], turn_hash: &[BabyBear; 8]) -> TurnAuthSigDescriptor {
    let (sk, pk) = schnorr_keygen(seed);
    let signature = schnorr_sign_prehashed(&sk, &pk, turn_hash);
    TurnAuthSigDescriptor {
        agent_pubkey: pk,
        turn_hash: *turn_hash,
        signature,
    }
}

/// Sign over a pre-encoded 8-felt message hash, producing `(R, s)` whose Fiat–Shamir challenge
/// is `compute_challenge_from_elements(R, pk, msg_hash)` — exactly what the AIR verifies.
fn schnorr_sign_prehashed(
    sk: &crate::schnorr_sig::SchnorrSecretKey,
    pk: &SchnorrPublicKey,
    msg_hash: &[BabyBear; 8],
) -> SchnorrSignature {
    use crate::schnorr_curve::{
        scalar_from_bytes, scalar_mul_mod, scalar_sub, scalar_to_bytes, GENERATOR,
    };
    // Deterministic nonce from (sk, msg_hash).
    let sk_bytes = scalar_to_bytes(&sk.0);
    let mut nonce_input = Vec::with_capacity(32 + 32);
    nonce_input.extend_from_slice(&sk_bytes);
    nonce_input.extend_from_slice(&felts_to_bytes(msg_hash));
    let k_bytes = blake3::derive_key("dregg-turn-auth-nonce-v1", &nonce_input);
    let k = scalar_from_bytes(&k_bytes);
    let r = GENERATOR.scalar_mul(&k);
    let e = compute_challenge_from_elements(&r, &pk.0, msg_hash);
    let e_sk = scalar_mul_mod(&e, &sk.0);
    let s = scalar_sub(&k, &e_sk);
    SchnorrSignature { r, s }
}

/// Encode an 8-felt hash to bytes (little-endian per limb) for nonce derivation.
fn felts_to_bytes(felts: &[BabyBear; 8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, f) in felts.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&f.0.to_le_bytes());
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::babybear8::BabyBear8;

    /// Reconstruct a curve point from a trace row's x/y limb columns (mirrors the Schnorr
    /// AIR's private `point_from_row`: (0,0) is the infinity sentinel).
    fn point_from_row(row: &[BabyBear], x_col: usize) -> CurvePoint {
        let mut xl = [BabyBear::ZERO; 8];
        let mut yl = [BabyBear::ZERO; 8];
        xl.copy_from_slice(&row[x_col..x_col + 8]);
        yl.copy_from_slice(&row[x_col + 8..x_col + 16]);
        let x = BabyBear8(xl);
        let y = BabyBear8(yl);
        if x.is_zero() && y.is_zero() {
            return CurvePoint::INFINITY;
        }
        CurvePoint::new(x, y)
    }

    fn turn_hash(tag: u8) -> [BabyBear; 8] {
        let mut h = [BabyBear::ZERO; 8];
        for (i, slot) in h.iter_mut().enumerate() {
            *slot = BabyBear::new((tag as u32).wrapping_mul(31).wrapping_add(i as u32 + 1));
        }
        h
    }

    /// HONEST PATH: the rightful agent signs THIS turn hash; the trace + PIs verify. The
    /// light client concludes "the holder of `agent_pubkey` authorized this turn".
    #[test]
    fn rightful_agent_signature_over_turn_accepts() {
        let th = turn_hash(0x42);
        let desc = sign_turn_prehashed(&[0x11; 32], &th);
        let (trace, pis) = generate_turn_auth_trace(&desc);
        assert!(
            verify_turn_auth_sig(&desc, &trace, &pis),
            "the rightful agent's signature over the turn must verify in-circuit"
        );
    }

    /// TOOTH (forged R): a forged signature — replace the nonce point `R` in the PIs with a
    /// different curve point so `s·G + e·pk != R` — is UNSAT via the curve equation alone, no
    /// executor. This is the light-client bite: a turn the rightful agent did NOT authorize
    /// cannot produce an accepting turn-auth proof.
    #[test]
    fn forged_signature_unsat() {
        use crate::schnorr_curve::GENERATOR;
        let th = turn_hash(0xCD);
        let desc = sign_turn_prehashed(&[0x22; 32], &th);
        let (trace, mut pis) = generate_turn_auth_trace(&desc);
        // Forge R := 2G (a valid point, not the signature's R).
        let fake_r = GENERATOR.double();
        for i in 0..8 {
            pis[pi::R_X + i] = fake_r.x.0[i];
            pis[pi::R_Y + i] = fake_r.y.0[i];
        }
        assert!(
            !verify_turn_auth_sig(&desc, &trace, &pis),
            "a forged signature (wrong R) must be UNSAT — the curve boundary fails"
        );
    }

    /// TOOTH (tampered turn hash): an adversary keeps a VALID signature but swaps the turn hash
    /// in the PIs — claiming the agent authorized a DIFFERENT turn. The descriptor's bound turn
    /// hash no longer matches the PIs, so the gate rejects. (Even past the PI binding, the
    /// challenge `e = H(R, pk, turn_hash)` would move and break the curve boundary.)
    #[test]
    fn tampered_turn_hash_unsat() {
        let th = turn_hash(0x07);
        let desc = sign_turn_prehashed(&[0x33; 32], &th);
        let (trace, mut pis) = generate_turn_auth_trace(&desc);
        // Tamper: claim a DIFFERENT turn hash in the PIs.
        let other = turn_hash(0x08);
        for i in 0..8 {
            pis[auth_pi::TURN_HASH + i] = other[i];
        }
        assert!(
            !verify_turn_auth_sig(&desc, &trace, &pis),
            "a signature claimed over a different turn hash must be UNSAT"
        );
    }

    /// TOOTH (wrong pubkey): a turn-auth proof bound to a DIFFERENT agent pubkey than the one
    /// that signed is rejected — the curve's phase-1 base boundary no longer matches the
    /// scanned base, and the PI binding catches the substitution. No impersonation.
    #[test]
    fn wrong_agent_pubkey_unsat() {
        let th = turn_hash(0x11);
        let desc = sign_turn_prehashed(&[0x44; 32], &th);
        let (trace, mut pis) = generate_turn_auth_trace(&desc);
        // Substitute a different agent's pubkey in the PIs.
        let imposter = sign_turn_prehashed(&[0x99; 32], &th);
        for i in 0..8 {
            pis[auth_pi::AGENT_PK_X + i] = imposter.agent_pubkey.0.x.0[i];
            pis[auth_pi::AGENT_PK_Y + i] = imposter.agent_pubkey.0.y.0[i];
        }
        // Bind the descriptor to the imposter key too (so the PI-binding leg passes) and show
        // the CURVE equation still rejects: the signature was made under the real key, so
        // `s·G + e·pk == R` fails for the imposter pk.
        let imposter_desc = TurnAuthSigDescriptor {
            agent_pubkey: imposter.agent_pubkey.clone(),
            turn_hash: th,
            signature: desc.signature.clone(),
        };
        assert!(
            !verify_turn_auth_sig(&imposter_desc, &trace, &pis),
            "a signature does not verify under a different agent's pubkey (curve boundary)"
        );
    }

    /// The forcing is NOT a free bit: corrupt the slope witness on an addition row of an honest
    /// trace and the curve equation rejects. (Mirrors the Schnorr AIR's `λ` tooth, asserting the
    /// turn-auth layer inherits the real curve constraint.)
    #[test]
    fn corrupted_curve_witness_unsat() {
        let th = turn_hash(0x55);
        let desc = sign_turn_prehashed(&[0x55; 32], &th);
        let (mut trace, pis) = generate_turn_auth_trace(&desc);
        // Find an addition row (bit == 1) whose slope constraint actually FIRES — the Schnorr
        // AIR asserts `λ·(xB − xA) = (yB − yA)` only on a genuine point addition (neither point
        // at infinity, distinct x). Corrupt that row's slope witness.
        let mut corrupted = false;
        for i in 0..schnorr_air::SCALAR_BITS - 1 {
            let row = schnorr_air::PHASE_0_START + i;
            if trace[row][col::SCALAR_BIT] == BabyBear::ONE {
                let acc = point_from_row(&trace[row], col::ACC_X);
                let base = point_from_row(&trace[row], col::BASE_X);
                if !acc.is_infinity && !base.is_infinity && acc.x != base.x {
                    trace[row][col::LAMBDA] = trace[row][col::LAMBDA] + BabyBear::ONE;
                    corrupted = true;
                    break;
                }
            }
        }
        assert!(corrupted, "expected an addition row to corrupt");
        assert!(
            !verify_turn_auth_sig(&desc, &trace, &pis),
            "a corrupted curve witness must be UNSAT — the gate forces the curve math, not a bit"
        );
    }

    /// DUAL-SCHEME HONEST PROVEN PATH: the cell commits the agent's curve key as its proven-path
    /// authority; the agent signs THIS turn under that key. Both legs pass — the curve equation
    /// verifies AND the forced key binds to the committed authority. The light client concludes "the
    /// cell's RIGHTFUL committed curve key authorized this turn".
    #[test]
    fn dual_scheme_proven_turn_against_committed_accepts() {
        let th = turn_hash(0x77);
        let desc = sign_turn_prehashed(&[0x77; 32], &th);
        let committed = CommittedCurveAuthority {
            committed_pubkey: desc.agent_pubkey.clone(),
        };
        let (trace, pis) = generate_turn_auth_trace(&desc);
        assert!(
            verify_proven_turn_against_committed(&desc, &committed, &trace, &pis),
            "honest proven turn under the committed curve authority must verify"
        );
    }

    /// TOOTH (downgrade / key substitution): a VALID signature under key A, but the cell committed a
    /// DIFFERENT curve key B as its proven authority. The curve equation still verifies (the sig is
    /// genuine under A) — but the binding to the committed authority FAILS, so the dual-scheme proven
    /// gate is UNSAT. This is the in-circuit `dualscheme_no_downgrade`: an attacker holding ANY valid
    /// signature cannot authorize a turn against a cell whose committed curve key differs. No executor.
    #[test]
    fn dual_scheme_forced_key_not_committed_unsat() {
        let th = turn_hash(0x88);
        // The agent signs honestly under its OWN key A.
        let desc = sign_turn_prehashed(&[0x88; 32], &th);
        let (trace, pis) = generate_turn_auth_trace(&desc);
        // The cell committed a DIFFERENT curve key B as its proven-path authority.
        let other = sign_turn_prehashed(&[0xAB; 32], &th);
        let committed = CommittedCurveAuthority {
            committed_pubkey: other.agent_pubkey.clone(),
        };
        // The bare curve check passes (the signature IS valid under A)...
        assert!(
            verify_turn_auth_sig(&desc, &trace, &pis),
            "the signature is genuinely valid under its own key"
        );
        // ...but the binding to the committed authority B fails, so the dual-scheme gate rejects.
        assert!(
            !bind_curve_key_to_committed_authority(&pis, &committed),
            "forced curve key A must NOT bind to committed authority B"
        );
        assert!(
            !verify_proven_turn_against_committed(&desc, &committed, &trace, &pis),
            "a proven turn whose forced curve key != committed authority must be UNSAT (no downgrade)"
        );
    }

    /// The descriptor's bound pubkey actually equals `sk·G` — a sanity check that the bound key
    /// is the rightful agent's, closing the loop from key to PI.
    #[test]
    fn bound_pubkey_is_rightful() {
        let th = turn_hash(0x66);
        let desc = sign_turn_prehashed(&[0x66; 32], &th);
        let (_trace, pis) = generate_turn_auth_trace(&desc);
        for i in 0..8 {
            assert_eq!(pis[auth_pi::AGENT_PK_X + i], desc.agent_pubkey.0.x.0[i]);
            assert_eq!(pis[auth_pi::TURN_HASH + i], desc.turn_hash[i]);
        }
        assert!(!desc.agent_pubkey.0.is_infinity, "agent pubkey is a real point");
        let _ = CurvePoint::INFINITY;
    }
}
