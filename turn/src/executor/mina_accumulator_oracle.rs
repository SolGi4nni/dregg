//! # The Mina DEFERRED-IPA-ACCUMULATOR oracle — the leg Pickles never evaluates in-circuit.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **Nothing here is an AIR, and that is the whole design.** Halo/Pickles never evaluate the SRS
//! multi-scalar multiplication in-circuit — the deferral IS the innovation, and the real check is
//! discharged once, natively, batched, amortised over a long chain of proofs. This module authors
//! no constraint, no `Builder` gadget and no `air_accepts` predicate. It declares the *seam* at
//! which a turn's acceptance is made to depend on that discharge having happened, and it fails
//! closed when it has not.
//!
//! ## What upstream does that this closes
//!
//! `mina-rust`'s verifier `&&`s `Ipa::Step::accumulator_check` into `batch_step_dlog_check`
//! (`verify.ml:135-146`). For each accepted proof, with `C` the challenge-polynomial commitment and
//! `u⃗` the sixteen endo-lifted bulletproof challenges,
//!
//! ```text
//!     C == ⟨ b_poly_coefficients(u⃗), srs.g ⟩       |srs.g| = 2^16 = 65536 Vesta generators
//! ```
//!
//! and a BATCH of `N` claims is discharged by ONE MSM over `|G| + N` points. Until 2026-08-05 the
//! dregg Mina light client did not evaluate it at all: the discharge existed, was measured on seven
//! real block proofs, and had **zero callers** outside an example binary and its own `#[cfg(test)]`.
//! `mina_head_verifier`'s own module docs said so — *"Not the accumulator … it is not part of this
//! bind."* This trait is the seam that makes it part of the bind.
//!
//! ## ⚑ WHY A SEAM AND NOT A DIRECT CALL — read before "simplifying" this away
//!
//! The discharge needs two things `dregg-turn` cannot have:
//!
//! 1. **A 4 MB Vesta SRS blob** (65 536 generators, byte-pinned by sha256), and
//! 2. **the verified Lean decision `dregg_mina_deferral_ok`**, which lives in `libdregg_lean.a`.
//!
//! `dregg-turn` cannot link the archive — the same reason
//! [`super::conservation_oracle`] exists, stated at `node/src/lib.rs`: *"`dregg-cell`/`dregg-turn`
//! cannot link the archive (wasm32 + SP1 zkVM guest), so the backend comes from `dregg-exec-lean`
//! at native startup."* `dregg-bridge`, where the discharge implementation lives, depends ON
//! `dregg-turn`, so a direct call would also be a dependency CYCLE.
//!
//! So the backend is installed, exactly like the conservation oracle: `dregg-exec-lean` owns the
//! arithmetic and the FFI, `dregg-node` arms it at startup, and this crate holds only the trait and
//! the refusal.
//!
//! ## ⚑⚑ FAIL CLOSED, AND THE POLARITY IS THE POINT
//!
//! **An absent oracle is a REJECTION, never a skip.** A node that cannot discharge the accumulator
//! cannot know whether the terminal opening is vacuous
//! (`PastaIpaDeferral.opening_is_vacuous_when_sg_is_free`), so it refuses the Mina head rather than
//! accepting the carrier on the prover's word. This repo's fail-open catalogue is long and every
//! entry looked like a reasonable degrade at the time; there is no `Option` here that reads as
//! "discharged nothing, returned Ok".
//!
//! `turn/tests/mina_accumulator_fails_closed_without_oracle.rs` drives that pole: it exhibits a
//! wire whose STARK legs are all well-formed being refused for exactly this reason, and the same
//! wire being refused again when an oracle IS installed but the claim does not discharge.
//!
//! ## What this does NOT establish — and it is a named residual, not a hidden assumption
//!
//! ⚠ **The claim is not bound in-circuit to THIS head.** `minaLcVerifyDesc` publishes no PI slot
//! for the accumulator commitment, so what the descriptor forces is unchanged by this module. What
//! the CONSUMER now forces is that the prover exhibited *some* claim that really does discharge
//! against the real Vesta SRS — which is strictly more than the zero it forced this morning, and
//! strictly less than "this block's accumulator is discharged". Closing it is a PI block on the
//! head descriptor (nine `Faithful9` lanes of a commitment to the claim, the same shape
//! `PI_SUB_PI` already uses for the Fq-transcript sub-proof) and it is the next rung, not a thing
//! this seam pretends to have done.

use std::sync::OnceLock;

/// The number of endo-lifted bulletproof challenges a Step/Tick accumulator claim carries —
/// `BACKEND_TICK_ROUNDS_N` (`mina-rust`, `proofs/mod.rs:33`). `2^16 = |srs.g|`, which is the
/// relation the batch shape check re-derives.
pub const MINA_ACCUMULATOR_ROUNDS: usize = 16;

/// One deferred IPA accumulator claim, as it travels on the wire.
///
/// Coordinates and challenges are 32-byte little-endian canonical integers — the encoding
/// `accumulator_discharge_export` writes and the discharge's `U256` reads. This type deliberately
/// carries NO curve type: `dregg-turn` does no Pasta arithmetic, and a `Pt` here would be a second
/// definition of a point that `dregg-circuit` already owns.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct WireAccumulatorClaim {
    /// `C.x` — the challenge-polynomial commitment's x coordinate, on Vesta.
    pub comm_x: [u8; 32],
    /// `C.y`.
    pub comm_y: [u8; 32],
    /// `u⃗` — the endo-lifted bulletproof challenges, [`MINA_ACCUMULATOR_ROUNDS`] of them.
    pub chals: Vec<[u8; 32]>,
}

impl WireAccumulatorClaim {
    /// The one shape check `dregg-turn` can make without curve arithmetic: the challenge count.
    ///
    /// ⚠ This is NOT a discharge and must never be mistaken for one. It exists so a malformed wire
    /// is refused at the codec boundary with a precise message instead of reaching the oracle and
    /// coming back as a generic arithmetic refusal. Everything that matters — on-curve, reduced,
    /// and the MSM itself — is the oracle's, because it is the side that has the SRS.
    pub fn check_arity(&self) -> Result<(), String> {
        if self.chals.len() != MINA_ACCUMULATOR_ROUNDS {
            return Err(format!(
                "the Mina accumulator claim carries {} bulletproof challenges; a Step/Tick claim \
                 has exactly {MINA_ACCUMULATOR_ROUNDS} (2^{MINA_ACCUMULATOR_ROUNDS} = |srs.g|)",
                self.chals.len()
            ));
        }
        Ok(())
    }
}

/// A discharge procedure for Mina's deferred IPA accumulator claims.
///
/// `Ok(())` means: the batched MSM over the byte-pinned Vesta SRS was **evaluated** and found to
/// vanish for this claim, AND the verified Lean gate `dregg_mina_deferral_ok` agreed with that
/// result over the `PastaIpaDeferral` §5b wire. Anything else is `Err(reason)` — including "the
/// archive does not export the gate, so we could not ask", which is a refusal and not an accept.
pub trait MinaAccumulatorOracle: Send + Sync {
    /// Discharge one claim. See the trait docs for what `Ok(())` is allowed to mean.
    fn discharged(&self, claim: &WireAccumulatorClaim) -> Result<(), String>;
}

static ORACLE: OnceLock<Box<dyn MinaAccumulatorOracle>> = OnceLock::new();

/// Install the process-wide Mina accumulator oracle (once). Called by `dregg-exec-lean` /
/// `dregg-node` at startup with the native-MSM + verified-Lean backend. Returns `Err` if one is
/// already installed.
pub fn install_mina_accumulator_oracle(
    oracle: Box<dyn MinaAccumulatorOracle>,
) -> Result<(), &'static str> {
    ORACLE
        .set(oracle)
        .map_err(|_| "Mina accumulator oracle already installed")
}

/// The installed oracle, if any.
///
/// ⚑ `None` is NOT a degrade path. Its only consumer
/// ([`super::mina_head_verifier::MinaAnchoredHeadStarkVerifier::verify`]) turns `None` into a
/// rejection of the turn. There is no Rust fallback that decides this in the absence of the
/// backend, because deciding it requires the SRS the backend is carrying.
#[inline]
pub fn installed_mina_accumulator_oracle() -> Option<&'static dyn MinaAccumulatorOracle> {
    ORACLE.get().map(|b| b.as_ref())
}

/// Whether a Mina accumulator oracle is installed. Used by reality-gate tests to confirm the
/// route-through is armed, and by node startup to report the disposition.
pub fn mina_accumulator_oracle_installed() -> bool {
    ORACLE.get().is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn claim(n: usize) -> WireAccumulatorClaim {
        WireAccumulatorClaim {
            comm_x: [1u8; 32],
            comm_y: [2u8; 32],
            chals: vec![[3u8; 32]; n],
        }
    }

    /// BOTH POLARITIES of the one check this crate can make for itself.
    #[test]
    fn arity_is_checked_in_both_directions() {
        assert!(claim(MINA_ACCUMULATOR_ROUNDS).check_arity().is_ok());
        for wrong in [0usize, 1, 15, 17, 32] {
            let e = claim(wrong)
                .check_arity()
                .expect_err("a claim that is not 16 challenges must be refused");
            assert!(
                e.contains("bulletproof challenges"),
                "the refusal must say what was wrong: {e}"
            );
        }
    }

    /// ⚑ `2^ROUNDS` IS `|srs.g|`. The batch shape check the Lean gate re-derives depends on this
    /// equality, so it is stated here rather than remembered — a claim carrying a different round
    /// count would not tile the SRS and the s-vector fold would be meaningless.
    #[test]
    fn rounds_tile_the_srs() {
        assert_eq!(1usize << MINA_ACCUMULATOR_ROUNDS, 65_536);
    }

    /// The registry starts EMPTY, and the accessor says so. This is the state every wasm32 / zkVM
    /// build and every `dregg-turn` unit test runs in, and it is the state in which a Mina head
    /// must be REFUSED — `mina_head_verifier`'s tests exhibit that refusal.
    #[test]
    fn no_oracle_is_installed_by_default_in_this_crates_tests() {
        assert!(
            !mina_accumulator_oracle_installed(),
            "dregg-turn's own test process must never have a backend installed: the fail-closed \
             pole is what these tests exist to drive"
        );
        assert!(installed_mina_accumulator_oracle().is_none());
    }
}
