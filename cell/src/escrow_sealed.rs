//! Sealed conditional escrow — an atomic two-party value exchange a sovereign
//! agent can use to safely pay-for / trade.
//!
//! # The capacity (Track 2)
//!
//! An autonomous agent living inside dregg needs to *exchange* value with a
//! counterparty it does not trust: "I give you X iff you give me Y". The danger
//! is the half-open trade — A hands over its leg and B never reciprocates, or B
//! claims A's leg without ever having locked its own. A **sealed escrow** closes
//! that gap. Each party locks one *leg* of the trade into the escrow cell's
//! committed state; the exchange COMPLETES atomically only when both conforming
//! legs are present; and until completion each party may *reclaim* its own leg.
//! No party can ever walk away holding the counterparty's leg without having
//! genuinely deposited its own conforming leg, and no leg is ever claimable
//! twice.
//!
//! # The weld (what already existed, disconnected)
//!
//! This is built, not memoed — it welds onto substrate already in the tree:
//!
//!  * **The committed heap** ([`crate::state::CellState::set_heap`] /
//!    [`crate::state::compute_heap_root`])
//!    is an openable sorted-Poseidon2 `(collection, key) → FieldElement` map
//!    ALREADY folded into the canonical state commitment. We reserve a
//!    collection id ([`ESCROW_COLL`]) inside it for the escrow ledger — so the
//!    escrow's terms, its locked legs, and its one-shot consumed flags are bound
//!    into the cell's commitment FOR FREE, with no commitment-version bump.
//!    This mirrors [`crate::derived`]'s heap-binding discipline exactly.
//!
//!  * **The signed `i64` balance ledger** is the value primitive: a leg locks an
//!    `amount` of value, exactly the quantity [`crate::state::CellState::balance`]
//!    carries.
//!
//!  * **The nullifier / one-shot spend discipline** (the note/membrane "consume
//!    exactly once" tooth) is the shape the leg-consumed flag takes: settling or
//!    reclaiming a leg flips a per-leg consumed bit in the committed heap, and
//!    every claim path checks it first — a settled leg is a spent nullifier.
//!
//! # The soundness story (what binds the exchange)
//!
//! An escrow is a pair of [`Leg`]s — `a` (party A's deposit, conditioned on
//! receiving B's) and `b` (party B's, conditioned on receiving A's) — plus the
//! [`EscrowTerms`] (who the two parties are and what each leg's value/asset
//! must be). The terms' digest, each leg's deposited/consumed state, and each
//! leg's amount are written into [`ESCROW_COLL`], hence into the cell's
//! commitment. The binding enforces, against a holder of the commitment + heap
//! openings:
//!
//! 1. **No claim without a conforming own deposit.** To claim the counterparty's
//!    leg you must present a [`Claim`] whose own deposited leg matches the terms
//!    (right party, right asset, amount `>=` the terms' required amount). A
//!    claim from a party who never deposited (or under-deposited) is REJECTED.
//! 2. **Atomic settlement.** [`settle`] completes the exchange only when BOTH
//!    legs are present and conforming; it then consumes both legs in one step.
//!    There is no partial settlement.
//! 3. **One-shot.** Each leg carries a `consumed` flag in the commitment.
//!    Settling or reclaiming consumes it; any later claim/settle/reclaim of an
//!    already-consumed leg is REJECTED. A settled leg cannot be replayed, and a
//!    reclaimed leg cannot also be settled (and vice-versa).
//! 4. **No over-claim.** The claimed value is bounded by the locked leg's
//!    committed amount: a claim asserting more than the leg actually holds
//!    diverges from the committed amount and is REJECTED — the same way a forged
//!    derived value diverges from its sources in [`crate::derived`].
//!
//! The honest-accept path ([`settle`] accepting) and every forge-reject path run
//! through the SAME [`EscrowState::check_claim`] / [`EscrowState::settlement`]
//! verification core, so a stub in either direction fails one polarity.
//!
//! # The minimal genuine slice (this module)
//!
//! - A **2-of-2 atomic swap**: A locks leg `a`, B locks leg `b`, settlement
//!   moves each leg to its counterparty atomically. HTLC timelocks / k-of-n /
//!   multi-asset baskets are the named next slice, not stubs here.
//!
//! # The next slice (named, not built here)
//!
//! The executor-level check here is the genuine forge-rejection. The remaining
//! slice is the **in-circuit witness**: a light client verifying a *batch*
//! should see settlement-atomicity enforced by the EffectVM circuit rather than
//! an out-of-band executor check. That requires (a) a `SettleEscrow` effect
//! descriptor whose gate binds "both legs present ∧ conforming ∧ not-yet-consumed
//! ⟹ both consumed" into the commitment, and (b) the Lean rung
//! `verifyBatch accept ⟹ exchange atomic` joining the circuit-soundness
//! obligation table. See `docs/deos/SEALED-ESCROW.md` §"Next slice: circuit
//! binding".

use serde::{Deserialize, Serialize};

use crate::cell::Cell;
use crate::id::CellId;
use crate::state::FieldElement;

/// Reserved heap collection id for the escrow ledger. Lives inside the cell's
/// committed heap (so the whole escrow is folded into the canonical state
/// commitment). Chosen high to avoid colliding with application heap
/// collections, in the same spirit as [`crate::derived::DERIVATION_COLL`].
pub const ESCROW_COLL: u32 = 0x005E_5CE0_u32; // a fixed reserved id ("ESCRoW")

/// Heap key holding the 32-byte digest of the escrow's [`EscrowTerms`]. Binds
/// *which* exchange this cell escrows.
pub const KEY_TERMS_DIGEST: u32 = 0;
/// Heap key: leg A's deposited amount (canonical little-endian `i64`).
pub const KEY_LEG_A_AMOUNT: u32 = 1;
/// Heap key: leg B's deposited amount (canonical little-endian `i64`).
pub const KEY_LEG_B_AMOUNT: u32 = 2;
/// Heap key: leg A's status flag — `0` = empty, `1` = deposited, `2` = consumed.
pub const KEY_LEG_A_STATUS: u32 = 3;
/// Heap key: leg B's status flag — `0` = empty, `1` = deposited, `2` = consumed.
pub const KEY_LEG_B_STATUS: u32 = 4;

/// A leg's lifecycle status, as stored (one felt) in the committed heap.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LegStatus {
    /// No leg deposited yet.
    Empty,
    /// A conforming leg is locked and unconsumed — claimable / settleable.
    Deposited,
    /// The leg has been consumed (settled to the counterparty OR reclaimed).
    /// The one-shot terminal state: any further claim/settle/reclaim is refused.
    Consumed,
}

impl LegStatus {
    fn to_felt(self) -> FieldElement {
        encode_i64(match self {
            LegStatus::Empty => 0,
            LegStatus::Deposited => 1,
            LegStatus::Consumed => 2,
        })
    }
    fn from_felt(f: &FieldElement) -> LegStatus {
        match decode_i64(f) {
            1 => LegStatus::Deposited,
            2 => LegStatus::Consumed,
            _ => LegStatus::Empty,
        }
    }
}

/// Which of the two legs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Side {
    /// Party A's leg.
    A,
    /// Party B's leg.
    B,
}

impl Side {
    /// The counterparty side.
    pub fn other(self) -> Side {
        match self {
            Side::A => Side::B,
            Side::B => Side::A,
        }
    }
    fn amount_key(self) -> u32 {
        match self {
            Side::A => KEY_LEG_A_AMOUNT,
            Side::B => KEY_LEG_B_AMOUNT,
        }
    }
    fn status_key(self) -> u32 {
        match self {
            Side::A => KEY_LEG_A_STATUS,
            Side::B => KEY_LEG_B_STATUS,
        }
    }
}

/// One leg of the exchange: a party deposits `amount` of `asset`.
///
/// The leg is the unit of value locked into the escrow. For the genuine 2-of-2
/// slice each leg is a single (party, asset, amount); multi-asset baskets are
/// the next slice.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Leg {
    /// The party that owns and deposits this leg.
    pub party: CellId,
    /// The asset this leg is denominated in.
    pub asset: CellId,
    /// How much value this leg locks. Must be `> 0` to be a real deposit.
    pub amount: i64,
}

impl Leg {
    /// A leg in which `party` locks `amount` of `asset`.
    pub fn new(party: CellId, asset: CellId, amount: i64) -> Self {
        Leg {
            party,
            asset,
            amount,
        }
    }
    /// Does this leg conform to the terms' requirement for `side`? (Right party,
    /// right asset, AND at least the required amount.) This is the conformance
    /// gate shared by deposit and claim — a leg that under-pays, names the wrong
    /// party, or names the wrong asset does NOT conform.
    fn conforms_to(&self, req: &LegRequirement) -> bool {
        self.party == req.party
            && self.asset == req.asset
            && self.amount >= req.min_amount
            && self.amount > 0
    }
}

/// What the terms REQUIRE of a leg on one side: who must deposit, in what asset,
/// at least how much.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LegRequirement {
    /// The party that must deposit this leg.
    pub party: CellId,
    /// The asset this leg must be denominated in.
    pub asset: CellId,
    /// The minimum amount that must be locked for the leg to conform.
    pub min_amount: i64,
}

impl LegRequirement {
    /// Require `party` to lock at least `min_amount` of `asset`.
    pub fn new(party: CellId, asset: CellId, min_amount: i64) -> Self {
        LegRequirement {
            party,
            asset,
            min_amount,
        }
    }
}

/// The terms of the exchange: what each side must lock. The digest of these
/// terms is bound into the escrow cell's commitment, so the two parties cannot
/// disagree on what the trade was.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EscrowTerms {
    /// Requirement on leg A (party A's deposit).
    pub a: LegRequirement,
    /// Requirement on leg B (party B's deposit).
    pub b: LegRequirement,
}

impl EscrowTerms {
    /// A 2-of-2 swap: A must lock `a`, B must lock `b`.
    pub fn swap(a: LegRequirement, b: LegRequirement) -> Self {
        EscrowTerms { a, b }
    }

    /// The requirement for one side.
    pub fn requirement(&self, side: Side) -> &LegRequirement {
        match side {
            Side::A => &self.a,
            Side::B => &self.b,
        }
    }

    /// A 32-byte canonical digest of the terms. Domain-separated so it can never
    /// collide with any other heap value's preimage. This is what gets bound at
    /// [`KEY_TERMS_DIGEST`] in the escrow cell's heap.
    pub fn digest(&self) -> FieldElement {
        let mut h = blake3::Hasher::new_derive_key("dregg.sealed-escrow.terms.v1");
        for req in [&self.a, &self.b] {
            h.update(req.party.as_bytes());
            h.update(req.asset.as_bytes());
            h.update(&req.min_amount.to_le_bytes());
        }
        *h.finalize().as_bytes()
    }
}

/// A claim presented to take the counterparty's leg. To take side `take`'s leg,
/// the claimant `claimant` must present the OWN leg it deposited (`own_leg`),
/// which the verifier checks conforms to the terms for the claimant's own side.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Claim {
    /// The party making the claim (must be the owner of its own side's leg).
    pub claimant: CellId,
    /// Which leg the claimant wants to TAKE (the counterparty's leg).
    pub take: Side,
    /// The leg the claimant asserts it deposited (its OWN side's leg). The
    /// verifier requires this to conform to the terms — you cannot take the
    /// counterparty leg without having locked your own conforming leg.
    pub own_leg: Leg,
    /// The value the claimant asserts the taken leg is worth. Bounded by the
    /// taken leg's committed amount: over-claiming is rejected.
    pub claimed_value: i64,
}

/// Why an escrow operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EscrowError {
    /// The cell carries no escrow binding (no terms digest in its heap).
    NotAnEscrow,
    /// The supplied terms' digest does not match the one bound in the cell —
    /// the verifier was handed the wrong terms for this escrow.
    TermsMismatch,
    /// A deposited leg does not conform to the terms (wrong party / asset /
    /// under the minimum amount).
    LegNonConforming(Side),
    /// A required leg is not deposited.
    LegNotDeposited(Side),
    /// THE ONE-SHOT REJECTION: the leg has already been consumed (settled or
    /// reclaimed); it cannot be claimed/settled/reclaimed again.
    LegAlreadyConsumed(Side),
    /// THE NO-CONFORMING-DEPOSIT REJECTION: the claimant's own leg does not
    /// conform — it never genuinely deposited (or under-deposited), so it may
    /// not take the counterparty's leg.
    NoConformingOwnDeposit,
    /// The claimant is not the owner of the side it claims to have deposited.
    WrongClaimant,
    /// THE OVER-CLAIM REJECTION: the claimed value exceeds the taken leg's
    /// committed amount.
    OverClaim {
        /// What the claim asserts the taken leg is worth.
        claimed: i64,
        /// What the leg actually committed to.
        locked: i64,
    },
    /// Reclaim refused: the leg is being reclaimed by someone other than its
    /// depositor.
    NotYourLeg(Side),
}

impl std::fmt::Display for EscrowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EscrowError::NotAnEscrow => write!(f, "cell carries no escrow binding"),
            EscrowError::TermsMismatch => write!(f, "supplied terms do not match the bound escrow"),
            EscrowError::LegNonConforming(s) => {
                write!(f, "leg {s:?} does not conform to the terms")
            }
            EscrowError::LegNotDeposited(s) => write!(f, "leg {s:?} is not deposited"),
            EscrowError::LegAlreadyConsumed(s) => {
                write!(
                    f,
                    "leg {s:?} already consumed (one-shot): cannot be claimed twice"
                )
            }
            EscrowError::NoConformingOwnDeposit => write!(
                f,
                "claimant has not deposited a conforming own leg; cannot take the counterparty leg"
            ),
            EscrowError::WrongClaimant => write!(f, "claimant is not the owner of its own leg"),
            EscrowError::OverClaim { claimed, locked } => {
                write!(
                    f,
                    "over-claim: claims {claimed} but leg only locks {locked}"
                )
            }
            EscrowError::NotYourLeg(s) => {
                write!(f, "leg {s:?} can only be reclaimed by its depositor")
            }
        }
    }
}

impl std::error::Error for EscrowError {}

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

/// **Open** an escrow on a cell: bind the terms digest and mark both legs empty.
/// After this the cell's commitment binds the exchange terms; no value is locked
/// yet. A turn opening an escrow MUST call this — it is what seals the terms.
pub fn open_escrow(cell: &mut Cell, terms: &EscrowTerms) {
    let st = &mut cell.state;
    st.set_heap(ESCROW_COLL, KEY_TERMS_DIGEST, terms.digest());
    st.set_heap(ESCROW_COLL, KEY_LEG_A_STATUS, LegStatus::Empty.to_felt());
    st.set_heap(ESCROW_COLL, KEY_LEG_B_STATUS, LegStatus::Empty.to_felt());
    st.set_heap(ESCROW_COLL, KEY_LEG_A_AMOUNT, encode_i64(0));
    st.set_heap(ESCROW_COLL, KEY_LEG_B_AMOUNT, encode_i64(0));
}

/// **Deposit** a conforming leg into the escrow, locking its value into the
/// committed heap. Rejects a leg that does not conform to the terms, or one
/// that would overwrite an already-deposited / consumed leg (a re-deposit is a
/// double-lock and is refused — the slot is one-shot from `Empty`).
///
/// On success the cell's commitment binds the locked leg's amount and a
/// `Deposited` status. A light client sees value has entered the escrow.
pub fn deposit_leg(
    cell: &mut Cell,
    terms: &EscrowTerms,
    side: Side,
    leg: &Leg,
) -> Result<(), EscrowError> {
    let view = EscrowState::read(cell)?;
    if view.terms_digest != terms.digest() {
        return Err(EscrowError::TermsMismatch);
    }
    // The slot must be empty: cannot re-deposit over a live or consumed leg.
    match view.status(side) {
        LegStatus::Empty => {}
        LegStatus::Deposited => return Err(EscrowError::LegNonConforming(side)),
        LegStatus::Consumed => return Err(EscrowError::LegAlreadyConsumed(side)),
    }
    if !leg.conforms_to(terms.requirement(side)) {
        return Err(EscrowError::LegNonConforming(side));
    }
    let st = &mut cell.state;
    st.set_heap(ESCROW_COLL, side.amount_key(), encode_i64(leg.amount));
    st.set_heap(
        ESCROW_COLL,
        side.status_key(),
        LegStatus::Deposited.to_felt(),
    );
    Ok(())
}

/// A read-only view of an escrow's committed state, recovered from the cell's
/// heap. The single source of truth that every verification path consults — the
/// honest accept and every forge reject run through THIS, so a stub in either
/// direction fails one polarity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EscrowState {
    /// The bound terms digest.
    pub terms_digest: FieldElement,
    /// Leg A's status.
    pub status_a: LegStatus,
    /// Leg B's status.
    pub status_b: LegStatus,
    /// Leg A's committed amount.
    pub amount_a: i64,
    /// Leg B's committed amount.
    pub amount_b: i64,
}

impl EscrowState {
    /// Recover an escrow's committed state from a cell, or [`EscrowError::NotAnEscrow`].
    pub fn read(cell: &Cell) -> Result<EscrowState, EscrowError> {
        let terms_digest = cell
            .state
            .get_heap(ESCROW_COLL, KEY_TERMS_DIGEST)
            .ok_or(EscrowError::NotAnEscrow)?;
        let status_a = cell
            .state
            .get_heap(ESCROW_COLL, KEY_LEG_A_STATUS)
            .map(|f| LegStatus::from_felt(&f))
            .unwrap_or(LegStatus::Empty);
        let status_b = cell
            .state
            .get_heap(ESCROW_COLL, KEY_LEG_B_STATUS)
            .map(|f| LegStatus::from_felt(&f))
            .unwrap_or(LegStatus::Empty);
        let amount_a = cell
            .state
            .get_heap(ESCROW_COLL, KEY_LEG_A_AMOUNT)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let amount_b = cell
            .state
            .get_heap(ESCROW_COLL, KEY_LEG_B_AMOUNT)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        Ok(EscrowState {
            terms_digest,
            status_a,
            status_b,
            amount_a,
            amount_b,
        })
    }

    /// The status of one leg.
    pub fn status(&self, side: Side) -> LegStatus {
        match side {
            Side::A => self.status_a,
            Side::B => self.status_b,
        }
    }

    /// The committed amount of one leg.
    pub fn amount(&self, side: Side) -> i64 {
        match side {
            Side::A => self.amount_a,
            Side::B => self.amount_b,
        }
    }

    /// **The claim forge-detector.** Verify a [`Claim`] against the committed
    /// escrow and the terms WITHOUT mutating anything: it returns `Ok` only when
    /// the claimant has genuinely deposited a conforming own leg, the taken leg
    /// is live (deposited and not consumed), and the claimed value does not
    /// exceed the taken leg's committed amount.
    ///
    /// Rejects, in order:
    /// - [`EscrowError::TermsMismatch`] (wrong terms presented),
    /// - [`EscrowError::WrongClaimant`] (claimant ≠ own-side owner),
    /// - [`EscrowError::NoConformingOwnDeposit`] (own leg does not conform),
    /// - [`EscrowError::LegNotDeposited`] (own or taken leg never deposited),
    /// - [`EscrowError::LegAlreadyConsumed`] (taken leg one-shot already spent),
    /// - [`EscrowError::OverClaim`] (claims more than the taken leg locks).
    pub fn check_claim(&self, terms: &EscrowTerms, claim: &Claim) -> Result<i64, EscrowError> {
        if self.terms_digest != terms.digest() {
            return Err(EscrowError::TermsMismatch);
        }
        let own = claim.take.other(); // the claimant's own side
        let own_req = terms.requirement(own);

        // The claimant must own the side it claims to have deposited.
        if claim.claimant != own_req.party || claim.own_leg.party != own_req.party {
            return Err(EscrowError::WrongClaimant);
        }
        // 1. NO CLAIM WITHOUT A CONFORMING OWN DEPOSIT: the presented own leg
        //    must conform to the terms AND actually be deposited+live in the
        //    commitment at the committed amount.
        if !claim.own_leg.conforms_to(own_req) {
            return Err(EscrowError::NoConformingOwnDeposit);
        }
        match self.status(own) {
            LegStatus::Deposited => {}
            LegStatus::Empty => return Err(EscrowError::LegNotDeposited(own)),
            LegStatus::Consumed => return Err(EscrowError::LegAlreadyConsumed(own)),
        }
        // The presented own leg must match the committed amount: you cannot
        // claim to have deposited X while the commitment only locked Y.
        if claim.own_leg.amount != self.amount(own) {
            return Err(EscrowError::NoConformingOwnDeposit);
        }
        // 2. The taken (counterparty) leg must be live (deposited, not consumed).
        match self.status(claim.take) {
            LegStatus::Deposited => {}
            LegStatus::Empty => return Err(EscrowError::LegNotDeposited(claim.take)),
            LegStatus::Consumed => return Err(EscrowError::LegAlreadyConsumed(claim.take)),
        }
        // 3. NO OVER-CLAIM: the claimed value is bounded by the taken leg's
        //    committed amount.
        let locked = self.amount(claim.take);
        if claim.claimed_value > locked {
            return Err(EscrowError::OverClaim {
                claimed: claim.claimed_value,
                locked,
            });
        }
        Ok(locked)
    }

    /// **The settlement forge-detector.** Verify that the exchange is ready to
    /// complete atomically: BOTH legs deposited, conforming, and unconsumed.
    /// Returns the `(amount_a, amount_b)` that will move. This is the accept
    /// path for [`settle`]; it shares the leg-state checks with
    /// [`EscrowState::check_claim`], so the same constraint biting rejects a stub.
    pub fn settlement(&self, terms: &EscrowTerms) -> Result<(i64, i64), EscrowError> {
        if self.terms_digest != terms.digest() {
            return Err(EscrowError::TermsMismatch);
        }
        for side in [Side::A, Side::B] {
            match self.status(side) {
                LegStatus::Deposited => {}
                LegStatus::Empty => return Err(EscrowError::LegNotDeposited(side)),
                LegStatus::Consumed => return Err(EscrowError::LegAlreadyConsumed(side)),
            }
            // Each locked amount must still meet the terms' minimum.
            if self.amount(side) < terms.requirement(side).min_amount || self.amount(side) <= 0 {
                return Err(EscrowError::LegNonConforming(side));
            }
        }
        Ok((self.amount_a, self.amount_b))
    }
}

/// **Settle** the exchange atomically: verify both legs are present, conforming,
/// and unconsumed (via [`EscrowState::settlement`]), then consume BOTH legs in
/// one step. After settlement each leg's committed status is `Consumed`, so the
/// one-shot tooth refuses any replay.
///
/// Returns the `(amount_a, amount_b)` that the caller (the executor) moves to
/// the counterparties. There is no partial settlement: if `settlement` rejects,
/// nothing is consumed.
pub fn settle(cell: &mut Cell, terms: &EscrowTerms) -> Result<(i64, i64), EscrowError> {
    let view = EscrowState::read(cell)?;
    let moved = view.settlement(terms)?;
    let st = &mut cell.state;
    st.set_heap(ESCROW_COLL, KEY_LEG_A_STATUS, LegStatus::Consumed.to_felt());
    st.set_heap(ESCROW_COLL, KEY_LEG_B_STATUS, LegStatus::Consumed.to_felt());
    Ok(moved)
}

/// **Reclaim** one's own leg before settlement. Permitted only to the leg's
/// depositor, only while the leg is still `Deposited` (not yet consumed by a
/// settlement or a prior reclaim). Consumes the leg one-shot, so it can never
/// also be settled or reclaimed again.
///
/// Returns the reclaimed amount.
pub fn reclaim_leg(
    cell: &mut Cell,
    terms: &EscrowTerms,
    side: Side,
    by: CellId,
) -> Result<i64, EscrowError> {
    let view = EscrowState::read(cell)?;
    if view.terms_digest != terms.digest() {
        return Err(EscrowError::TermsMismatch);
    }
    if by != terms.requirement(side).party {
        return Err(EscrowError::NotYourLeg(side));
    }
    match view.status(side) {
        LegStatus::Deposited => {}
        LegStatus::Empty => return Err(EscrowError::LegNotDeposited(side)),
        LegStatus::Consumed => return Err(EscrowError::LegAlreadyConsumed(side)),
    }
    let amount = view.amount(side);
    cell.state.set_heap(
        ESCROW_COLL,
        side.status_key(),
        LegStatus::Consumed.to_felt(),
    );
    Ok(amount)
}

/// Whether a cell carries an escrow binding (a terms digest in its reserved heap
/// collection). A plain (non-escrow) cell returns `false`.
pub fn is_escrow(cell: &Cell) -> bool {
    cell.state.get_heap(ESCROW_COLL, KEY_TERMS_DIGEST).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }
    fn escrow_cell() -> Cell {
        // A plain cell to host the escrow ledger; its balance is irrelevant to
        // the escrow heap binding.
        Cell::with_balance([9u8; 32], [9u8; 32], 0)
    }

    /// Party A: cell 1, locks 100 of asset 10.
    /// Party B: cell 2, locks 250 of asset 20.
    fn sample_terms() -> EscrowTerms {
        EscrowTerms::swap(
            LegRequirement::new(cid(1), cid(10), 100),
            LegRequirement::new(cid(2), cid(20), 250),
        )
    }
    fn leg_a() -> Leg {
        Leg::new(cid(1), cid(10), 100)
    }
    fn leg_b() -> Leg {
        Leg::new(cid(2), cid(20), 250)
    }

    /// THE HONEST PATH: both legs deposited conforming, the exchange settles
    /// atomically, both legs end consumed. This MUST pass before any reject test
    /// is meaningful — the same `settlement` core gates both polarities.
    #[test]
    fn honest_two_leg_exchange_completes() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        assert!(is_escrow(&cell));

        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        deposit_leg(&mut cell, &terms, Side::B, &leg_b()).unwrap();

        let moved = settle(&mut cell, &terms).expect("honest two-leg exchange must settle");
        assert_eq!(moved, (100, 250));

        // Both legs now consumed.
        let view = EscrowState::read(&cell).unwrap();
        assert_eq!(view.status(Side::A), LegStatus::Consumed);
        assert_eq!(view.status(Side::B), LegStatus::Consumed);
    }

    /// The whole escrow is bound into the canonical commitment: depositing a leg
    /// changes the cell commitment (a light client sees value enter). This is
    /// WHY a forge cannot be hidden — the escrow state is part of what is
    /// verified.
    #[test]
    fn escrow_state_is_bound_into_commitment() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        let before = cell.state_commitment();
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        let after = cell.state_commitment();
        assert_ne!(before, after, "depositing a leg re-seals the commitment");
    }

    // ── FORGE-DETECTOR 1: claim without a conforming own deposit ─────────────

    /// Party B tries to claim A's leg WITHOUT having deposited its own leg. The
    /// claim is rejected: you cannot take the counterparty leg without a
    /// conforming own deposit. (Only A's leg is present.)
    #[test]
    fn claim_without_own_deposit_is_rejected() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        // Only A deposits. B never deposits but tries to take A's leg.
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();

        let view = EscrowState::read(&cell).unwrap();
        let claim = Claim {
            claimant: cid(2),
            take: Side::A,
            own_leg: leg_b(), // B *asserts* its leg, but never deposited it
            claimed_value: 100,
        };
        assert_eq!(
            view.check_claim(&terms, &claim),
            Err(EscrowError::LegNotDeposited(Side::B)),
            "B has not deposited its own leg; it cannot take A's leg"
        );
    }

    /// A subtler forge: B *under-deposits* (locks 1 instead of the required
    /// 250), then claims its leg conforms. The conformance gate rejects it — the
    /// SAME gate the honest deposit passed.
    #[test]
    fn under_deposited_own_leg_cannot_claim() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();

        // B's under-deposit does not even pass deposit (conformance), so force a
        // forged committed state: pretend B deposited a conforming amount but
        // its presented own_leg under-pays.
        let view = EscrowState::read(&cell).unwrap();
        let claim = Claim {
            claimant: cid(2),
            take: Side::A,
            own_leg: Leg::new(cid(2), cid(20), 1), // below the 250 minimum
            claimed_value: 100,
        };
        assert_eq!(
            view.check_claim(&terms, &claim),
            Err(EscrowError::NoConformingOwnDeposit),
            "an under-paying own leg does not conform; cannot claim"
        );

        // And the deposit path itself refuses the under-payment up front.
        let mut cell2 = escrow_cell();
        open_escrow(&mut cell2, &terms);
        assert_eq!(
            deposit_leg(&mut cell2, &terms, Side::B, &Leg::new(cid(2), cid(20), 1)),
            Err(EscrowError::LegNonConforming(Side::B))
        );
    }

    // ── FORGE-DETECTOR 2: double-claim / replay of a settled leg ─────────────

    /// After an honest settlement consumes both legs, a replay claim of the
    /// (now consumed) leg is rejected by the one-shot tooth. The SAME
    /// `check_claim`/leg-state core that accepted before settlement now rejects.
    #[test]
    fn replay_of_settled_leg_is_rejected() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        deposit_leg(&mut cell, &terms, Side::B, &leg_b()).unwrap();

        // Before settlement, B's claim of A's leg WOULD accept (proves the path
        // is live — non-vacuity by construction).
        let live = EscrowState::read(&cell).unwrap();
        let claim = Claim {
            claimant: cid(2),
            take: Side::A,
            own_leg: leg_b(),
            claimed_value: 100,
        };
        assert_eq!(
            live.check_claim(&terms, &claim),
            Ok(100),
            "pre-settle claim is live"
        );

        // Settle (consumes both legs).
        settle(&mut cell, &terms).unwrap();

        // Now the replay of the consumed leg is rejected.
        let settled = EscrowState::read(&cell).unwrap();
        assert_eq!(
            settled.check_claim(&terms, &claim),
            Err(EscrowError::LegAlreadyConsumed(Side::B)),
            "a settled leg cannot be claimed again (one-shot)"
        );

        // And settlement itself cannot be replayed.
        assert_eq!(
            settle(&mut cell, &terms),
            Err(EscrowError::LegAlreadyConsumed(Side::A))
        );
    }

    /// A reclaimed leg cannot then be settled, and a settled leg cannot be
    /// reclaimed — the one-shot flag is shared across both consumption paths.
    #[test]
    fn reclaim_and_settle_are_mutually_exclusive_one_shot() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        deposit_leg(&mut cell, &terms, Side::B, &leg_b()).unwrap();

        // A reclaims its leg.
        assert_eq!(reclaim_leg(&mut cell, &terms, Side::A, cid(1)), Ok(100));
        // Reclaiming again is refused.
        assert_eq!(
            reclaim_leg(&mut cell, &terms, Side::A, cid(1)),
            Err(EscrowError::LegAlreadyConsumed(Side::A))
        );
        // Settlement now refuses — A's leg is gone.
        assert_eq!(
            settle(&mut cell, &terms),
            Err(EscrowError::LegAlreadyConsumed(Side::A))
        );
    }

    /// Reclaim by the wrong party is refused (you can only reclaim YOUR leg).
    #[test]
    fn reclaim_of_anothers_leg_is_rejected() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        // B (cid 2) tries to reclaim A's leg.
        assert_eq!(
            reclaim_leg(&mut cell, &terms, Side::A, cid(2)),
            Err(EscrowError::NotYourLeg(Side::A))
        );
    }

    // ── FORGE-DETECTOR 3: over-claim of a leg ────────────────────────────────

    /// B deposits its leg, then claims A's leg is worth MORE than A locked. The
    /// over-claim is rejected: the claimed value is bounded by the committed
    /// amount.
    #[test]
    fn over_claim_is_rejected() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        deposit_leg(&mut cell, &terms, Side::B, &leg_b()).unwrap();

        let view = EscrowState::read(&cell).unwrap();
        // honest claim of exactly the locked amount accepts (non-vacuity).
        let honest = Claim {
            claimant: cid(2),
            take: Side::A,
            own_leg: leg_b(),
            claimed_value: 100,
        };
        assert_eq!(view.check_claim(&terms, &honest), Ok(100));

        // over-claim: 100 locked, claims 9999.
        let forged = Claim {
            claimant: cid(2),
            take: Side::A,
            own_leg: leg_b(),
            claimed_value: 9_999,
        };
        assert_eq!(
            view.check_claim(&terms, &forged),
            Err(EscrowError::OverClaim {
                claimed: 9_999,
                locked: 100,
            }),
            "cannot claim more than the leg actually locks"
        );
    }

    // ── additional teeth ─────────────────────────────────────────────────────

    /// A claim presented against the WRONG terms is rejected at the terms digest
    /// (you cannot re-interpret an escrow under different terms than it bound).
    #[test]
    fn wrong_terms_is_rejected() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        deposit_leg(&mut cell, &terms, Side::B, &leg_b()).unwrap();

        let other_terms = EscrowTerms::swap(
            LegRequirement::new(cid(1), cid(10), 100),
            LegRequirement::new(cid(2), cid(20), 999), // different minimum
        );
        let view = EscrowState::read(&cell).unwrap();
        let claim = Claim {
            claimant: cid(2),
            take: Side::A,
            own_leg: leg_b(),
            claimed_value: 100,
        };
        assert_eq!(
            view.check_claim(&other_terms, &claim),
            Err(EscrowError::TermsMismatch)
        );
        assert_eq!(
            settle(&mut cell, &other_terms),
            Err(EscrowError::TermsMismatch)
        );
    }

    /// Settlement before BOTH legs are present is refused (no half-open trade).
    #[test]
    fn settlement_before_both_legs_is_rejected() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        // Only A is in; B has not deposited.
        assert_eq!(
            settle(&mut cell, &terms),
            Err(EscrowError::LegNotDeposited(Side::B))
        );
    }

    /// A non-owner cannot present someone else's identity as its own leg's party
    /// (the claimant must own the side it deposited).
    #[test]
    fn wrong_claimant_is_rejected() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        deposit_leg(&mut cell, &terms, Side::B, &leg_b()).unwrap();

        let view = EscrowState::read(&cell).unwrap();
        // cid(3) claims to be taking A's leg with B's own leg — but it is not B.
        let claim = Claim {
            claimant: cid(3),
            take: Side::A,
            own_leg: leg_b(),
            claimed_value: 100,
        };
        assert_eq!(
            view.check_claim(&terms, &claim),
            Err(EscrowError::WrongClaimant)
        );
    }

    /// A leg presented with the wrong asset does not conform (you cannot satisfy
    /// the terms by depositing a different asset).
    #[test]
    fn wrong_asset_leg_is_rejected() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        // B deposits asset 99 instead of the required asset 20.
        assert_eq!(
            deposit_leg(&mut cell, &terms, Side::B, &Leg::new(cid(2), cid(99), 250)),
            Err(EscrowError::LegNonConforming(Side::B))
        );
    }

    /// Re-depositing over a live leg is refused (a deposit slot is one-shot from
    /// Empty — no double-lock).
    #[test]
    fn redeposit_over_live_leg_is_rejected() {
        let terms = sample_terms();
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        assert_eq!(
            deposit_leg(&mut cell, &terms, Side::A, &leg_a()),
            Err(EscrowError::LegNonConforming(Side::A))
        );
    }

    /// `check_claim` on a non-escrow cell reports NotAnEscrow.
    #[test]
    fn non_escrow_cell_is_rejected() {
        let cell = escrow_cell();
        assert_eq!(EscrowState::read(&cell), Err(EscrowError::NotAnEscrow));
    }

    /// The i64 amount encode/decode round-trips, including negatives.
    #[test]
    fn amount_encoding_roundtrips() {
        for v in [0i64, 1, -1, 100, 250, i64::MAX, i64::MIN] {
            assert_eq!(decode_i64(&encode_i64(v)), v);
        }
    }

    /// **The Lean rung: this executor invariant is PROVEN, not just smoke-tested.**
    ///
    /// The atomic-swap invariant enforced here — both legs deposited makes the
    /// settlement gate ready and binds BOTH leg amounts, a settled leg is one-shot
    /// (replay refused), a non-conforming own deposit cannot claim, and an
    /// over-claim is bounded by the locked amount — is the EXECUTOR image of the
    /// proven Lean rung `metatheory/Dregg2/Deos/SealedEscrow.lean`, grounded BY
    /// REUSE of the committed-heap root (`Substrate.Heap.root_binds_get`) + the
    /// one-shot Consumed discipline. This test mirrors that rung's `#guard`
    /// witnesses (leg A locks 100, leg B locks 250) so the Rust is checked against
    /// the proven statement:
    ///
    ///   * `deposit_both_ready` + `deposit_binds_amounts` — both legs deposited ⇒
    ///     settlement ready at the committed `(100, 250)`;
    ///   * `replay_rejected` — a settled (consumed) leg is no longer ready, and the
    ///     consumption MOVES the committed root (`forged_leg_moves_root`);
    ///   * `consumed_taken_leg_rejected` — a claim against the now-consumed taken
    ///     leg is refused;
    ///   * `over_claim_rejected` — claiming 9999 of a leg locking 100 is refused;
    ///   * `nonconforming_claim_rejected` — a claimant that never deposited a
    ///     conforming own leg cannot take the counterparty leg.
    #[test]
    fn invariant_matches_lean_rung() {
        let terms = sample_terms();

        // `deposit_both_ready` + `deposit_binds_amounts`: both legs deposited makes
        // settlement ready, binding the committed (100, 250).
        let mut cell = escrow_cell();
        open_escrow(&mut cell, &terms);
        deposit_leg(&mut cell, &terms, Side::A, &leg_a()).unwrap();
        deposit_leg(&mut cell, &terms, Side::B, &leg_b()).unwrap();
        let ready = EscrowState::read(&cell).unwrap();
        assert_eq!(ready.status(Side::A), LegStatus::Deposited);
        assert_eq!(ready.status(Side::B), LegStatus::Deposited);
        assert_eq!(ready.amount(Side::A), 100);
        assert_eq!(ready.amount(Side::B), 250);
        assert_eq!(ready.settlement(&terms), Ok((100, 250)));

        // `honest_claim_accepts`: B takes A's leg presenting its own, claiming
        // exactly the 100 A locked.
        let honest = Claim {
            claimant: cid(2),
            take: Side::A,
            own_leg: leg_b(),
            claimed_value: 100,
        };
        assert_eq!(ready.check_claim(&terms, &honest), Ok(100));

        // `over_claim_rejected`: claiming 9999 of a leg locking 100 is refused.
        let over = Claim {
            claimed_value: 9_999,
            ..honest.clone()
        };
        assert!(matches!(
            ready.check_claim(&terms, &over),
            Err(EscrowError::OverClaim {
                claimed: 9_999,
                locked: 100
            })
        ));

        // `replay_rejected` + `forged_leg_moves_root`: settling consumes both legs,
        // the escrow is no longer ready, and the consumption MOVED the root.
        let before = cell.state_commitment();
        settle(&mut cell, &terms).unwrap();
        let after = cell.state_commitment();
        assert_ne!(
            before, after,
            "forged_leg_moves_root: settlement moves the root"
        );
        let settled = EscrowState::read(&cell).unwrap();
        assert_eq!(settled.status(Side::A), LegStatus::Consumed);
        assert_eq!(
            settled.settlement(&terms),
            Err(EscrowError::LegAlreadyConsumed(Side::A))
        );

        // `consumed_taken_leg_rejected`: a claim after settlement fails the one-shot
        // tooth — both legs are consumed (the own-leg B check trips first).
        assert_eq!(
            settled.check_claim(&terms, &honest),
            Err(EscrowError::LegAlreadyConsumed(Side::B))
        );

        // `nonconforming_claim_rejected`: only A deposits; B never locks its leg
        // yet tries to take A's — refused (B's own leg is not deposited).
        let mut only_a = escrow_cell();
        open_escrow(&mut only_a, &terms);
        deposit_leg(&mut only_a, &terms, Side::A, &leg_a()).unwrap();
        let view = EscrowState::read(&only_a).unwrap();
        assert_eq!(view.status(Side::B), LegStatus::Empty);
        assert_eq!(
            view.check_claim(&terms, &honest),
            Err(EscrowError::LegNotDeposited(Side::B))
        );
    }
}
