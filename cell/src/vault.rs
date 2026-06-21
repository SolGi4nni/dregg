//! Conditional timelock vault — value locked until a release condition is met,
//! then claimable exactly once by the beneficiary.
//!
//! # The capacity (Track 2)
//!
//! An autonomous agent living inside dregg needs to *lock value with a release
//! rule*: savings it cannot touch until a date, a vested/scheduled release, a
//! commitment device ("I cannot spend this until block N"), a deadbolt fund that
//! only opens when a secret/proof is presented. The danger is symmetric:
//!
//!  * **early release** — claiming the value before the release condition is
//!    genuinely met (block height not yet reached, or no valid proof); and
//!  * a **forged condition-proof** — presenting a witness that does NOT satisfy
//!    the locked condition (the wrong preimage) and having it accepted; and
//!  * a **double-claim / replay** — claiming a vault that has already settled, so
//!    the locked value is released twice; and
//!  * a **forged lock** — a claim whose committed vault state does not reflect the
//!    real lock (a tampered amount or condition).
//!
//! A conditional vault closes all four. The terms (`beneficiary`, `amount`,
//! `release_height`, `condition`) are sealed into the cell's commitment, and a
//! `claim` step is **gated on the genuine satisfaction of the committed
//! condition** and **one-shot**: it releases the value to the beneficiary and
//! flips a committed `settled` flag, and any later claim of a settled vault is
//! REJECTED. A holder of the commitment can tell, for any block + witness,
//! whether the vault is genuinely claimable — so an early claim is detectable, a
//! forged proof diverges from the committed condition digest, and a replay finds
//! the settled flag already set.
//!
//! # The weld (what already existed, disconnected)
//!
//! This is built, not memoed — it welds onto substrate already in the tree, the
//! same vehicles [`crate::escrow_sealed`], [`crate::allowance`], and
//! [`crate::obligation_standing`] use:
//!
//!  * **The committed heap** ([`crate::state::CellState::set_heap`] /
//!    [`crate::state::compute_heap_root`]) is an openable sorted-Poseidon2
//!    `(collection, key) → FieldElement` map ALREADY folded into the canonical
//!    state commitment. We reserve a collection id ([`VAULT_COLL`]) for the vault
//!    ledger: the terms digest, the locked `amount`, the `release_height`, the
//!    condition kind + condition digest, and the one-shot `settled` flag all live
//!    there — bound into the cell's commitment FOR FREE, no commitment-version
//!    bump. (Same heap-binding discipline as `ESCROW_COLL` / `ALLOWANCE_COLL`.)
//!
//!  * **The signed `i64` balance ledger** is the value primitive: the vault locks
//!    an `amount` of value (exactly the quantity [`crate::state::CellState::balance`]
//!    carries), released to the beneficiary on a genuine claim.
//!
//!  * **Block height** is the time clock: an [`Condition::AtHeight`] vault is
//!    claimable only at a presented block `>= release_height` — the same
//!    block-height clock [`crate::allowance`] derives its epochs from.
//!
//!  * **The nullifier / one-shot spend discipline** (the escrow leg-`Consumed`
//!    tooth) is the shape the `settled` flag takes: a claim flips the committed
//!    `settled` bit, and every claim path checks it first — a settled vault is a
//!    spent nullifier and cannot be re-claimed.
//!
//!  * **A blake3 domain-separated digest** (the escrow terms digest, the obligation
//!    condition digest) is the shape the [`Condition::OnProof`] hashlock takes: the
//!    committed condition digest is `H(witness)` for the genuine preimage, so a
//!    forged witness hashes to a different value and is REJECTED.
//!
//! # The soundness story (what binds the lock)
//!
//! A vault is a [`VaultTerms`] (`beneficiary`, `asset`, `amount`,
//! `release_height`, [`Condition`]) whose digest is sealed at [`KEY_TERMS_DIGEST`],
//! plus the committed lock fields and the `settled` flag. Against a holder of the
//! commitment + heap openings, the binding enforces:
//!
//! 1. **No early release.** A claim presents a block `at_block` and (optionally) a
//!    witness. For an `AtHeight` vault, the claim is admitted only when
//!    `at_block >= release_height`; for an `OnProof` vault, only when the presented
//!    witness hashes to the committed condition digest. A claim that meets neither
//!    is REJECTED.
//! 2. **No forged proof.** The condition digest is committed; a forged witness
//!    (wrong preimage) hashes to a value that diverges from the committed digest
//!    and is REJECTED — the same hashing the honest claim runs.
//! 3. **One-shot.** The vault carries a `settled` flag in the commitment. A
//!    genuine claim flips it; any later claim of a settled vault is REJECTED. The
//!    value cannot be released twice.
//! 4. **No forged lock.** The released amount is the *committed* amount, and the
//!    condition is the *committed* condition: a claim cannot release more than the
//!    vault locked, nor reinterpret the vault under a different condition — both
//!    diverge from the bound terms digest and are REJECTED.
//!
//! The honest-accept path ([`claim`] accepting) and every forge-reject path run
//! through the SAME [`VaultState::check_claim`] verification core, so a stub in
//! either direction fails one polarity (non-vacuity by construction).
//!
//! # The minimal genuine slice (this module)
//!
//! - A single-beneficiary, single-asset vault with ONE condition — either a height
//!   timelock (`AtHeight`) or a hashlock (`OnProof`). Full HTLC chains (paired
//!   hashlock + refund timelock + counterparty), multi-stage vesting curves, and
//!   partial/streamed release are the named next slice, not stubs here.
//!
//! # The next slice (named, not built here)
//!
//! The executor-level check here is the genuine forge-rejection. The remaining
//! slice is the **in-circuit witness**: a light client verifying a *batch* should
//! see release-conditionality enforced by the EffectVM circuit rather than an
//! out-of-band executor check. That requires (a) a `ClaimVault` effect descriptor
//! whose gate binds "condition genuinely met (`at_block >= release_height` ∨
//! `H(witness) == condition_digest`) ∧ not-yet-settled ⟹ settled ∧ value released"
//! into the commitment, and (b) the Lean rung `verifyBatch accept ⟹ vault released
//! only when its condition was genuinely met` joining the circuit-soundness
//! obligation table in `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`. See
//! `docs/deos/CONDITIONAL-VAULT.md` §"Next slice: circuit binding".

use serde::{Deserialize, Serialize};

use crate::cell::Cell;
use crate::id::CellId;
use crate::state::FieldElement;

/// Reserved heap collection id for the conditional vault ledger. Lives inside the
/// cell's committed heap (so the whole vault is folded into the canonical state
/// commitment). Chosen high to avoid colliding with application heap collections,
/// in the same spirit as [`crate::escrow_sealed::ESCROW_COLL`].
pub const VAULT_COLL: u32 = 0x0_5A_F_E0_u32; // a fixed reserved id ("vAultsAFE0")

/// Heap key holding the 32-byte digest of the vault's [`VaultTerms`]. Binds
/// *which* lock (beneficiary, amount, release rule) this cell carries.
pub const KEY_TERMS_DIGEST: u32 = 0;
/// Heap key: the locked `amount` (canonical little-endian `i64`). The value
/// released to the beneficiary on a genuine claim — the released amount is bounded
/// by this committed value.
pub const KEY_AMOUNT: u32 = 1;
/// Heap key: the `settled` flag — `0` = locked (claimable), `1` = settled (the
/// one-shot terminal state; any further claim is refused).
pub const KEY_SETTLED: u32 = 2;

/// The release condition a vault is locked under. The minimal genuine slice is
/// one of two: a height timelock or a hashlock.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Condition {
    /// Released at/after a block height. The vault is claimable when the presented
    /// `at_block >= release_height`. No witness is required (an empty witness is
    /// fine). The "savings until block N" / "vested at block N" lock.
    AtHeight,
    /// Released when a preimage hashing to `digest` is presented. The vault is
    /// claimable when the presented witness `w` satisfies `H(w) == digest`. The
    /// "deadbolt fund opened by a secret/proof" lock. `digest` is the committed
    /// hashlock target.
    OnProof {
        /// The committed hashlock target: `H(genuine_preimage)`.
        digest: FieldElement,
    },
}

impl Condition {
    /// A height timelock: claimable at/after the vault's `release_height`.
    pub fn at_height() -> Self {
        Condition::AtHeight
    }

    /// A hashlock on `preimage`: claimable when that exact preimage is presented.
    /// The committed target is the domain-separated hash of the preimage, so the
    /// preimage itself is never stored in the clear.
    pub fn on_proof(preimage: &[u8]) -> Self {
        Condition::OnProof {
            digest: hash_witness(preimage),
        }
    }

    /// The kind tag stored (one felt) in the committed heap, distinguishing the
    /// two condition variants without revealing the hashlock target separately
    /// from the terms digest.
    fn kind_tag(&self) -> i64 {
        match self {
            Condition::AtHeight => 1,
            Condition::OnProof { .. } => 2,
        }
    }
}

/// The domain-separated hash of a witness/preimage. The committed hashlock target
/// for [`Condition::OnProof`] is `hash_witness(genuine_preimage)`, and a claim's
/// presented witness is admitted only when its `hash_witness` equals the committed
/// digest. Domain-separated so it can never collide with the terms digest preimage.
pub fn hash_witness(witness: &[u8]) -> FieldElement {
    let mut h = blake3::Hasher::new_derive_key("dregg.conditional-vault.witness.v1");
    h.update(witness);
    *h.finalize().as_bytes()
}

/// The sealed terms of a conditional vault: who may claim, in what asset, how much
/// is locked, the release height (used by [`Condition::AtHeight`]), and the
/// release condition. The digest of these terms is bound into the cell's
/// commitment, so the granter and beneficiary cannot disagree about the lock.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VaultTerms {
    /// The cell permitted to claim the released value.
    pub beneficiary: CellId,
    /// The asset the vault is denominated in.
    pub asset: CellId,
    /// The locked value, released to the beneficiary on a genuine claim. Must be `> 0`.
    pub amount: i64,
    /// The block height at/after which an [`Condition::AtHeight`] vault is
    /// claimable. For an [`Condition::OnProof`] vault this is unused by the gate
    /// (the hashlock governs release) but still bound into the digest.
    pub release_height: i64,
    /// The release condition the vault is locked under.
    pub condition: Condition,
}

impl VaultTerms {
    /// A height-timelock vault: `beneficiary` may claim `amount` of `asset` at/after
    /// block `release_height`.
    pub fn at_height(beneficiary: CellId, asset: CellId, amount: i64, release_height: i64) -> Self {
        VaultTerms {
            beneficiary,
            asset,
            amount,
            release_height,
            condition: Condition::AtHeight,
        }
    }

    /// A hashlock vault: `beneficiary` may claim `amount` of `asset` by presenting
    /// the `preimage`. `release_height` is recorded (and bound) but the hashlock
    /// governs release. Use `0` for `release_height` when only the proof gates.
    pub fn on_proof(
        beneficiary: CellId,
        asset: CellId,
        amount: i64,
        release_height: i64,
        preimage: &[u8],
    ) -> Self {
        VaultTerms {
            beneficiary,
            asset,
            amount,
            release_height,
            condition: Condition::on_proof(preimage),
        }
    }

    /// Whether these terms are internally well-formed (positive amount,
    /// non-negative release height). Ill-formed terms cannot be opened.
    pub fn is_well_formed(&self) -> bool {
        self.amount > 0 && self.release_height >= 0
    }

    /// A 32-byte canonical digest of the terms. Domain-separated so it can never
    /// collide with any other heap value's preimage. This is what gets bound at
    /// [`KEY_TERMS_DIGEST`]; it folds in the condition kind AND the hashlock target,
    /// so a vault cannot be reinterpreted under a different condition.
    pub fn digest(&self) -> FieldElement {
        let mut h = blake3::Hasher::new_derive_key("dregg.conditional-vault.terms.v1");
        h.update(self.beneficiary.as_bytes());
        h.update(self.asset.as_bytes());
        h.update(&self.amount.to_le_bytes());
        h.update(&self.release_height.to_le_bytes());
        h.update(&self.condition.kind_tag().to_le_bytes());
        match &self.condition {
            Condition::AtHeight => {
                h.update(&[0u8; 32]);
            }
            Condition::OnProof { digest } => {
                h.update(digest);
            }
        }
        *h.finalize().as_bytes()
    }
}

/// A claim presented to release the vault: the beneficiary asserts it is claiming
/// at block `at_block`, presenting `witness` (the preimage for an `OnProof` vault;
/// ignored, may be empty, for an `AtHeight` vault). The verifier checks the claim
/// against the committed condition WITHOUT trusting any field — the height is
/// compared to the committed `release_height`, the witness is hashed and compared
/// to the committed condition digest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Claim {
    /// The party making the claim (must be the vault's committed beneficiary).
    pub claimant: CellId,
    /// The block height at the moment of the claim. Gates an `AtHeight` release.
    pub at_block: i64,
    /// The witness/preimage presented. Gates an `OnProof` release (hashed and
    /// compared to the committed digest). Empty for a pure height timelock.
    pub witness: Vec<u8>,
}

impl Claim {
    /// A height-timelock claim by `claimant` at block `at_block` (no witness).
    pub fn at_height(claimant: CellId, at_block: i64) -> Self {
        Claim {
            claimant,
            at_block,
            witness: Vec::new(),
        }
    }
    /// A hashlock claim by `claimant` presenting `preimage` at block `at_block`.
    pub fn on_proof(claimant: CellId, at_block: i64, preimage: &[u8]) -> Self {
        Claim {
            claimant,
            at_block,
            witness: preimage.to_vec(),
        }
    }
}

/// Why a vault operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VaultError {
    /// The cell carries no vault binding (no terms digest in its heap).
    NotAVault,
    /// The supplied terms' digest does not match the one bound in the cell — the
    /// verifier was handed the wrong terms (or a forged condition) for this vault.
    TermsMismatch,
    /// The terms are not well-formed (non-positive amount, negative height).
    IllFormedTerms,
    /// The claimant is not the vault's committed beneficiary.
    WrongBeneficiary,
    /// THE EARLY-RELEASE REJECTION: an `AtHeight` vault claimed before its
    /// `release_height`.
    HeightNotReached {
        /// The block at which the claim was presented.
        at_block: i64,
        /// The release height that has not yet been reached.
        release_height: i64,
    },
    /// THE FORGED-PROOF REJECTION: an `OnProof` vault claimed with a witness whose
    /// hash does not match the committed condition digest (the wrong preimage).
    ProofMismatch,
    /// THE ONE-SHOT REJECTION: the vault has already been settled (claimed); it
    /// cannot be claimed again. The value cannot be released twice.
    AlreadySettled,
}

impl std::fmt::Display for VaultError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VaultError::NotAVault => write!(f, "cell carries no conditional vault binding"),
            VaultError::TermsMismatch => write!(f, "supplied terms do not match the bound vault"),
            VaultError::IllFormedTerms => write!(f, "vault terms are not well-formed"),
            VaultError::WrongBeneficiary => write!(f, "claimant is not the vault's beneficiary"),
            VaultError::HeightNotReached { at_block, release_height } => write!(
                f,
                "early release: claimed at block {at_block} but release height is {release_height}"
            ),
            VaultError::ProofMismatch => {
                write!(f, "forged condition-proof: witness does not satisfy the committed condition")
            }
            VaultError::AlreadySettled => {
                write!(f, "vault already settled (one-shot): cannot be claimed twice")
            }
        }
    }
}

impl std::error::Error for VaultError {}

/// Encode an `i64` as a 32-byte heap [`FieldElement`] (little-endian, low 8
/// bytes). Round-trips with [`decode_i64`].
pub fn encode_i64(value: i64) -> FieldElement {
    let mut f = [0u8; 32];
    f[0..8].copy_from_slice(&value.to_le_bytes());
    f
}

/// Decode a heap field back to the `i64` it encodes (low 8 bytes).
pub fn decode_i64(f: &FieldElement) -> i64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&f[0..8]);
    i64::from_le_bytes(buf)
}

/// The result of admitting a claim: the value released to the beneficiary. Returned
/// by [`VaultState::check_claim`] (the shared verification core) so the honest path
/// and the mutating [`claim`] release exactly what the verifier computed — no
/// second, divergent computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClaimOutcome {
    /// The value released to the beneficiary (the committed locked amount).
    pub released: i64,
}

/// A read-only view of a vault's committed state, recovered from the cell's heap.
/// The single source of truth every verification path consults — the honest accept
/// and every forge reject run through THIS, so a stub in either direction fails one
/// polarity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VaultState {
    /// The bound terms digest.
    pub terms_digest: FieldElement,
    /// The committed locked amount.
    pub amount: i64,
    /// Whether the vault has been settled (claimed) — the one-shot flag.
    pub settled: bool,
}

impl VaultState {
    /// Recover a vault's committed state from a cell, or [`VaultError::NotAVault`].
    pub fn read(cell: &Cell) -> Result<VaultState, VaultError> {
        let terms_digest = cell
            .state
            .get_heap(VAULT_COLL, KEY_TERMS_DIGEST)
            .ok_or(VaultError::NotAVault)?;
        let amount = cell
            .state
            .get_heap(VAULT_COLL, KEY_AMOUNT)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let settled = cell
            .state
            .get_heap(VAULT_COLL, KEY_SETTLED)
            .map(|f| decode_i64(&f) != 0)
            .unwrap_or(false);
        Ok(VaultState {
            terms_digest,
            amount,
            settled,
        })
    }

    /// **The claim forge-detector.** Verify a [`Claim`] against the committed vault
    /// and the terms WITHOUT mutating anything. Returns the [`ClaimOutcome`] (the
    /// value released) only when:
    ///
    /// - the presented terms match the committed digest (no forged lock /
    ///   reinterpreted condition — the digest folds in the condition);
    /// - the claimant is the committed beneficiary;
    /// - the vault is NOT already settled (the one-shot tooth);
    /// - the release condition is GENUINELY met: for `AtHeight`, the claim's block
    ///   is at/after `release_height`; for `OnProof`, the claim's witness hashes to
    ///   the committed condition digest.
    ///
    /// The condition is read from the *terms* (whose digest is committed and
    /// checked here), the amount from the *committed* state — so a forged witness,
    /// an early block, a replayed settled vault, or a tampered amount/condition all
    /// diverge from what the verifier reads.
    pub fn check_claim(
        &self,
        terms: &VaultTerms,
        claim: &Claim,
    ) -> Result<ClaimOutcome, VaultError> {
        if !terms.is_well_formed() {
            return Err(VaultError::IllFormedTerms);
        }
        // NO FORGED LOCK: the presented terms (incl. the condition) must match the
        // committed digest. A tampered amount or a swapped condition changes the
        // digest and is rejected here.
        if self.terms_digest != terms.digest() {
            return Err(VaultError::TermsMismatch);
        }
        if claim.claimant != terms.beneficiary {
            return Err(VaultError::WrongBeneficiary);
        }
        // ONE-SHOT: a settled vault cannot be claimed again.
        if self.settled {
            return Err(VaultError::AlreadySettled);
        }
        // THE RELEASE GATE: the condition must be genuinely met. This is the SAME
        // gate the honest claim passes — there is no separate "accept" path.
        match &terms.condition {
            Condition::AtHeight => {
                // NO EARLY RELEASE: the block must reach the release height.
                if claim.at_block < terms.release_height {
                    return Err(VaultError::HeightNotReached {
                        at_block: claim.at_block,
                        release_height: terms.release_height,
                    });
                }
            }
            Condition::OnProof { digest } => {
                // NO FORGED PROOF: the presented witness must hash to the committed
                // condition digest. A wrong preimage hashes elsewhere and is rejected.
                if &hash_witness(&claim.witness) != digest {
                    return Err(VaultError::ProofMismatch);
                }
            }
        }
        // The released value is the COMMITTED amount — a claim cannot release more
        // than the vault locked.
        Ok(ClaimOutcome { released: self.amount })
    }
}

/// **Open** a conditional vault on a cell: seal the terms digest, the locked
/// amount, and the (unsettled) flag. After this the cell's commitment binds the
/// lock; the value is locked and not yet claimable. Rejects ill-formed terms.
pub fn open_vault(cell: &mut Cell, terms: &VaultTerms) -> Result<(), VaultError> {
    if !terms.is_well_formed() {
        return Err(VaultError::IllFormedTerms);
    }
    let st = &mut cell.state;
    st.set_heap(VAULT_COLL, KEY_TERMS_DIGEST, terms.digest());
    st.set_heap(VAULT_COLL, KEY_AMOUNT, encode_i64(terms.amount));
    st.set_heap(VAULT_COLL, KEY_SETTLED, encode_i64(0));
    Ok(())
}

/// **Claim** the vault: verify the release condition is genuinely met and the vault
/// is unsettled (via [`VaultState::check_claim`]), then flip the committed `settled`
/// flag one-shot and return the released amount. After a genuine claim the vault's
/// committed status is `settled`, so the one-shot tooth refuses any replay.
///
/// Returns the `released` amount the caller (the executor) moves to the
/// beneficiary. If `check_claim` rejects, nothing is mutated.
pub fn claim(cell: &mut Cell, terms: &VaultTerms, step: &Claim) -> Result<i64, VaultError> {
    let view = VaultState::read(cell)?;
    let outcome = view.check_claim(terms, step)?;
    cell.state
        .set_heap(VAULT_COLL, KEY_SETTLED, encode_i64(1));
    Ok(outcome.released)
}

/// Whether a vault is genuinely claimable at `at_block` with `witness`, as a holder
/// of the commitment computes it: a convenience over [`VaultState::check_claim`] for
/// read-only inspection (it constructs the beneficiary's claim and checks it).
pub fn is_claimable_at(
    state: &VaultState,
    terms: &VaultTerms,
    at_block: i64,
    witness: &[u8],
) -> bool {
    let probe = Claim {
        claimant: terms.beneficiary,
        at_block,
        witness: witness.to_vec(),
    };
    state.check_claim(terms, &probe).is_ok()
}

/// Whether a cell carries a conditional vault binding (a terms digest in its
/// reserved heap collection). A plain cell returns `false`.
pub fn is_vault(cell: &Cell) -> bool {
    cell.state.get_heap(VAULT_COLL, KEY_TERMS_DIGEST).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }
    fn vault_cell() -> Cell {
        // A plain cell to host the vault ledger; its balance is irrelevant to the
        // heap binding the lock.
        Cell::with_balance([7u8; 32], [7u8; 32], 0)
    }

    /// Beneficiary cell 1 may claim 500 of asset 9 at/after block 11_000.
    fn height_terms() -> VaultTerms {
        VaultTerms::at_height(cid(1), cid(9), 500, 11_000)
    }
    /// Beneficiary cell 1 may claim 500 of asset 9 by presenting the secret.
    fn proof_terms() -> VaultTerms {
        VaultTerms::on_proof(cid(1), cid(9), 500, 0, b"the-secret-preimage")
    }

    // ── THE HONEST PATH (must pass before any reject test is meaningful) ─────

    /// THE HONEST PATH: a height-locked vault claimed at/after its release height
    /// ACCEPTS, releases the locked value, and marks the vault settled. This MUST
    /// pass before any reject test is meaningful — the same `check_claim` core gates
    /// both polarities.
    #[test]
    fn honest_height_claim_after_release_accepts_and_settles() {
        let terms = height_terms();
        let mut cell = vault_cell();
        open_vault(&mut cell, &terms).unwrap();
        assert!(is_vault(&cell));

        // before release, not claimable; at release, claimable.
        let view = VaultState::read(&cell).unwrap();
        assert!(!is_claimable_at(&view, &terms, 10_999, b""), "not yet claimable");
        assert!(is_claimable_at(&view, &terms, 11_000, b""), "claimable at release");

        let released = claim(&mut cell, &terms, &Claim::at_height(cid(1), 11_500))
            .expect("a height claim after release must accept");
        assert_eq!(released, 500);

        let settled = VaultState::read(&cell).unwrap();
        assert!(settled.settled, "the vault is marked settled after a genuine claim");
    }

    /// BONUS HONEST PATH: a hashlock vault claimed with the GENUINE preimage
    /// ACCEPTS, releases, and settles. The same `check_claim` core that rejects a
    /// forged preimage accepts the genuine one (non-vacuity by construction).
    #[test]
    fn honest_proof_claim_with_genuine_preimage_accepts_and_settles() {
        let terms = proof_terms();
        let mut cell = vault_cell();
        open_vault(&mut cell, &terms).unwrap();

        let view = VaultState::read(&cell).unwrap();
        assert!(
            is_claimable_at(&view, &terms, 0, b"the-secret-preimage"),
            "claimable with the genuine preimage"
        );

        let released = claim(
            &mut cell,
            &terms,
            &Claim::on_proof(cid(1), 0, b"the-secret-preimage"),
        )
        .expect("a hashlock claim with the genuine preimage must accept");
        assert_eq!(released, 500);
        assert!(VaultState::read(&cell).unwrap().settled);
    }

    /// The whole vault is bound into the canonical commitment: claiming changes the
    /// cell commitment (a light client sees the vault settle). This is WHY a forge
    /// cannot be hidden — the vault state is part of what is verified.
    #[test]
    fn vault_state_is_bound_into_commitment() {
        let terms = height_terms();
        let mut cell = vault_cell();
        let bare = cell.state_commitment();
        open_vault(&mut cell, &terms).unwrap();
        let opened = cell.state_commitment();
        assert_ne!(bare, opened, "opening the vault seals it into the commitment");
        claim(&mut cell, &terms, &Claim::at_height(cid(1), 11_500)).unwrap();
        let claimed = cell.state_commitment();
        assert_ne!(opened, claimed, "claiming re-seals the commitment (the settle is visible)");
    }

    // ── FORGE-DETECTOR 1: early release (height not reached) ─────────────────

    /// An early claim — before the release height, no proof — is REJECTED. The
    /// honest claim at exactly the release height is asserted live first
    /// (non-vacuity), and the mutating path leaves the vault unsettled on reject.
    #[test]
    fn early_height_claim_is_rejected() {
        let terms = height_terms(); // release at 11_000
        let mut cell = vault_cell();
        open_vault(&mut cell, &terms).unwrap();

        let view = VaultState::read(&cell).unwrap();
        // honest: exactly at the release height WOULD accept (non-vacuity).
        assert_eq!(
            view.check_claim(&terms, &Claim::at_height(cid(1), 11_000)),
            Ok(ClaimOutcome { released: 500 }),
            "a claim exactly at the release height is live"
        );
        // early: one block before the release height.
        assert_eq!(
            view.check_claim(&terms, &Claim::at_height(cid(1), 10_999)),
            Err(VaultError::HeightNotReached { at_block: 10_999, release_height: 11_000 }),
            "cannot release before the timelock"
        );
        // the mutating path refuses too, leaving the vault unsettled.
        assert_eq!(
            claim(&mut cell, &terms, &Claim::at_height(cid(1), 10_999)),
            Err(VaultError::HeightNotReached { at_block: 10_999, release_height: 11_000 })
        );
        assert!(!VaultState::read(&cell).unwrap().settled, "an early claim does not settle");
    }

    // ── FORGE-DETECTOR 2: forged condition-proof (wrong preimage) ────────────

    /// A forged condition-proof — a witness that is NOT the genuine preimage — is
    /// REJECTED. The honest preimage is asserted live first (non-vacuity); the same
    /// `check_claim` hashing rejects every wrong witness.
    #[test]
    fn forged_proof_is_rejected() {
        let terms = proof_terms();
        let mut cell = vault_cell();
        open_vault(&mut cell, &terms).unwrap();

        let view = VaultState::read(&cell).unwrap();
        // honest: the genuine preimage WOULD accept (non-vacuity).
        assert_eq!(
            view.check_claim(&terms, &Claim::on_proof(cid(1), 0, b"the-secret-preimage")),
            Ok(ClaimOutcome { released: 500 }),
            "the genuine preimage is live"
        );
        // forged: a wrong preimage.
        assert_eq!(
            view.check_claim(&terms, &Claim::on_proof(cid(1), 0, b"WRONG-preimage")),
            Err(VaultError::ProofMismatch),
            "a wrong preimage does not satisfy the hashlock"
        );
        // an empty witness against a hashlock is also rejected.
        assert_eq!(
            view.check_claim(&terms, &Claim::on_proof(cid(1), 0, b"")),
            Err(VaultError::ProofMismatch)
        );
        // the mutating path refuses too, leaving the vault unsettled.
        assert_eq!(
            claim(&mut cell, &terms, &Claim::on_proof(cid(1), 0, b"WRONG-preimage")),
            Err(VaultError::ProofMismatch)
        );
        assert!(!VaultState::read(&cell).unwrap().settled);
    }

    // ── FORGE-DETECTOR 3: double-claim / replay of a settled vault ───────────

    /// After an honest claim settles the vault, a replay claim is REJECTED by the
    /// one-shot tooth. The SAME `check_claim` core that accepted before settlement
    /// now rejects — the value cannot be released twice.
    #[test]
    fn double_claim_of_settled_vault_is_rejected() {
        let terms = height_terms();
        let mut cell = vault_cell();
        open_vault(&mut cell, &terms).unwrap();

        // before settlement, the claim is live (non-vacuity).
        let live = VaultState::read(&cell).unwrap();
        assert_eq!(
            live.check_claim(&terms, &Claim::at_height(cid(1), 11_500)),
            Ok(ClaimOutcome { released: 500 }),
            "the first claim is live"
        );

        // the honest claim settles the vault.
        assert_eq!(claim(&mut cell, &terms, &Claim::at_height(cid(1), 11_500)), Ok(500));

        // now the replay is rejected by the one-shot flag.
        let settled = VaultState::read(&cell).unwrap();
        assert_eq!(
            settled.check_claim(&terms, &Claim::at_height(cid(1), 11_500)),
            Err(VaultError::AlreadySettled),
            "a settled vault cannot be claimed again (one-shot)"
        );
        // and the mutating path refuses the replay too.
        assert_eq!(
            claim(&mut cell, &terms, &Claim::at_height(cid(1), 11_500)),
            Err(VaultError::AlreadySettled)
        );
    }

    // ── FORGE-DETECTOR 4: forged lock (tampered amount / swapped condition) ──

    /// A claim presented against FORGED terms — a tampered amount, or a swapped
    /// condition (claiming an `OnProof` vault is `AtHeight` so a bare height claim
    /// releases it) — is REJECTED at the terms digest. The condition is folded into
    /// the digest, so it cannot be reinterpreted; the honest terms accept (the same
    /// digest check), the forged terms diverge.
    #[test]
    fn forged_lock_is_rejected() {
        let terms = proof_terms(); // an OnProof vault locked by a secret
        let mut cell = vault_cell();
        open_vault(&mut cell, &terms).unwrap();

        let view = VaultState::read(&cell).unwrap();

        // FORGE A: tamper the amount up (claim 9_999 instead of the locked 500).
        let bigger = VaultTerms::on_proof(cid(1), cid(9), 9_999, 0, b"the-secret-preimage");
        assert_eq!(
            view.check_claim(&bigger, &Claim::on_proof(cid(1), 0, b"the-secret-preimage")),
            Err(VaultError::TermsMismatch),
            "a forged-up amount diverges from the committed terms digest"
        );

        // FORGE B: swap the condition to AtHeight to bypass the hashlock with a bare
        // height claim. The condition is folded into the digest → rejected.
        let swapped = VaultTerms::at_height(cid(1), cid(9), 500, 0);
        assert_eq!(
            view.check_claim(&swapped, &Claim::at_height(cid(1), 1)),
            Err(VaultError::TermsMismatch),
            "swapping the condition diverges from the committed terms digest"
        );

        // honest terms still accept (the same digest check — non-vacuity).
        assert_eq!(
            view.check_claim(&terms, &Claim::on_proof(cid(1), 0, b"the-secret-preimage")),
            Ok(ClaimOutcome { released: 500 })
        );
    }

    // ── additional teeth ─────────────────────────────────────────────────────

    /// A claim by someone other than the committed beneficiary is REJECTED — only
    /// the beneficiary may claim the released value.
    #[test]
    fn wrong_beneficiary_is_rejected() {
        let terms = height_terms();
        let mut cell = vault_cell();
        open_vault(&mut cell, &terms).unwrap();
        let view = VaultState::read(&cell).unwrap();
        // cell 2 is not the beneficiary (cell 1).
        assert_eq!(
            view.check_claim(&terms, &Claim::at_height(cid(2), 11_500)),
            Err(VaultError::WrongBeneficiary)
        );
    }

    /// Opening ill-formed terms is refused (non-positive amount, negative height).
    #[test]
    fn ill_formed_terms_are_rejected() {
        let mut cell = vault_cell();
        assert_eq!(
            open_vault(&mut cell, &VaultTerms::at_height(cid(1), cid(9), 0, 11_000)),
            Err(VaultError::IllFormedTerms),
            "zero amount is ill-formed"
        );
        assert_eq!(
            open_vault(&mut cell, &VaultTerms::at_height(cid(1), cid(9), 500, -1)),
            Err(VaultError::IllFormedTerms),
            "negative release height is ill-formed"
        );
    }

    /// `read`/`check_claim` on a non-vault cell reports NotAVault.
    #[test]
    fn non_vault_cell_is_rejected() {
        let cell = vault_cell();
        assert_eq!(VaultState::read(&cell), Err(VaultError::NotAVault));
    }

    /// The terms digest distinguishes the two condition variants AND the hashlock
    /// target: an `AtHeight` vault and an `OnProof` vault with otherwise-identical
    /// fields have different digests, and two hashlocks on different secrets differ.
    #[test]
    fn condition_is_bound_into_the_digest() {
        let height = VaultTerms::at_height(cid(1), cid(9), 500, 11_000);
        let proof = VaultTerms::on_proof(cid(1), cid(9), 500, 11_000, b"secret-a");
        let proof_b = VaultTerms::on_proof(cid(1), cid(9), 500, 11_000, b"secret-b");
        assert_ne!(height.digest(), proof.digest(), "condition kind distinguishes");
        assert_ne!(proof.digest(), proof_b.digest(), "hashlock target distinguishes");
    }

    /// The i64 amount encode/decode round-trips, including negatives.
    #[test]
    fn amount_encoding_roundtrips() {
        for v in [0i64, 1, -1, 500, 11_000, i64::MAX, i64::MIN] {
            assert_eq!(decode_i64(&encode_i64(v)), v);
        }
    }
}
