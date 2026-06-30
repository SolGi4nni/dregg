//! The COMMITTED bridge mirror-ledger: the concurrency-safe core of the
//! Solana/Stripe token mirror (`docs/deos/BRIDGE-ARCHITECTURE-SOUNDNESS.md` §3).
//!
//! # The double-mint gap this closes
//!
//! A `dregg_bridge::solana_mirror::MirrorState` (and its Stripe twin) held the
//! backing relationship — `currently_locked`, `live_supply`, and the
//! `seen_locks` replay set — as **in-memory, per-relayer** Rust fields. Two
//! relayers each holding the mirror's mint-cap, each with their own
//! `MirrorState`, would each see a fresh `seen_locks` and each mint against the
//! SAME Solana lock / Stripe payment: `2·amount` circulating against `amount` of
//! real backing. The kernel's per-turn serialization did not help, because the
//! accounting was off-ledger — the kernel saw only two independently-authorized,
//! independently-conserving `Effect::Mint`s.
//!
//! # The fix (no new kernel verb — composes existing committed primitives)
//!
//! [`TurnExecutor::bridge_mint_against_lock`] performs the whole bridge mint as
//! ONE atomic, serialized operation over **committed** state:
//!
//! 1. **`lock_id` as a consume-once nullifier.** The caller (the bridge layer)
//!    derives a domain-separated nullifier from `(spl_mint, lock_id)` /
//!    `(asset, payment_intent_id)` and passes it here. We consume it against the
//!    EXACT committed `note_nullifiers` set that `Effect::NoteSpend` /
//!    `Effect::BridgeMint` ride — atomic contains-then-insert, double-spend
//!    reject, journaled + rollback-safe. The first relayer to land consumes the
//!    nullifier; every racing relayer is rejected by COMMITTED state, regardless
//!    of how many relayer processes run or what their RAM `MirrorState` believes.
//!
//! 2. **A committed mirror-ledger cell** ([`read_supply`]) is the single source
//!    of truth for `currently_locked` + `live_supply`. It is an ordinary dregg
//!    cell in the committed state root, so every node/light-client sees the same
//!    numbers. The mint debits/credits it inside the same turn and asserts
//!    `live_supply + amount ≤ currently_locked` against the COMMITTED value — so
//!    the invariant holds globally, not per-process.
//!
//! 3. **The conserving `Effect::Mint`** (well debit + recipient credit, cap-
//!    gated by [`TurnExecutor::apply_mint`]) runs in the SAME critical section.
//!    Any failure rolls back the nullifier consume AND the ledger-cell debit via
//!    the existing [`LedgerJournal`], so the three legs commit together-or-not.
//!
//! Because all three are one serialized operation over committed state, the
//! executor's per-turn serialization IS the global serialization point. N
//! relayers become safe and even desirable (liveness/redundancy): they all race
//! to land the bridge mint; the committed nullifier lets exactly one win per
//! `lock_id`; the committed cell is the single arithmetic source of truth.

use super::*;
use dregg_cell::{Cell, CellId, Ledger, Nullifier};

/// Field slot in the committed mirror-ledger cell holding `currently_locked`
/// (the real backing locked on Solana / cleared on Stripe).
pub const LOCKED_FIELD: usize = 0;
/// Field slot in the committed mirror-ledger cell holding `live_supply`
/// (mirror value circulating inside dregg).
pub const LIVE_FIELD: usize = 1;

/// Encode a `u64` supply quantity into a committed [`FieldElement`] slot
/// (little-endian in the low 8 bytes; the rest is zero).
pub fn encode_u64(v: u64) -> [u8; 32] {
    let mut f = [0u8; 32];
    f[..8].copy_from_slice(&v.to_le_bytes());
    f
}

/// Decode the low-8-byte little-endian `u64` a [`FieldElement`] supply slot holds.
pub fn decode_u64(f: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[..8]);
    u64::from_le_bytes(b)
}

/// Read `(currently_locked, live_supply)` from a committed mirror-ledger cell.
/// A fresh cell (all-zero fields) reads `(0, 0)`.
pub fn read_supply(cell: &Cell) -> (u64, u64) {
    let locked = cell
        .state
        .get_field(LOCKED_FIELD)
        .map(decode_u64)
        .unwrap_or(0);
    let live = cell
        .state
        .get_field(LIVE_FIELD)
        .map(decode_u64)
        .unwrap_or(0);
    (locked, live)
}

/// Construct a fresh committed mirror-ledger cell (`currently_locked = 0`,
/// `live_supply = 0`). It is an ordinary cell whose fields 0/1 carry the
/// bridge's two committed supply scalars; `token_id` should be a domain
/// distinct from the mirror's own asset (it is a scalar store, not a well).
pub fn new_mirror_ledger_cell(public_key: [u8; 32], token_id: [u8; 32]) -> Cell {
    Cell::with_balance(public_key, token_id, 0)
}

/// Domain-separated derivation of the **escrow** nullifier from a lock's mint
/// nullifier. The committed bridge accounting has TWO consume-once legs over the
/// same `note_nullifiers` set: the ESCROW leg (raises `currently_locked`, deduped
/// here so one lock can never inflate the backing twice) and the MINT leg (raises
/// `live_supply`, deduped by the `lock_nullifier` — the double-mint guard). They
/// must be distinct values so the same lock can drive each exactly once; this
/// folds the mint nullifier under a fresh domain to get the escrow key.
pub fn escrow_nullifier_for(mint_nullifier: &Nullifier) -> Nullifier {
    let mut h = blake3::Hasher::new_derive_key("dregg-bridge-escrow-nullifier-v1");
    h.update(&mint_nullifier.0);
    Nullifier(*h.finalize().as_bytes())
}

/// One independently-verified escrow over committed state — the INDEPENDENT
/// source of `currently_locked` (red-team BR-2/BR-3). Recording an escrow raises
/// the committed backing; minting later DRAWS against it. Because the two are
/// separate operations (not one fused credit-both-legs), the conservation
/// backstop in [`TurnExecutor::bridge_mint_against_lock`] is genuinely reachable.
#[derive(Clone, Debug)]
pub struct BridgeEscrowRecord {
    /// The committed mirror-ledger cell whose `currently_locked` this raises.
    pub ledger_cell: CellId,
    /// The domain-separated consume-once escrow nullifier (see
    /// [`escrow_nullifier_for`]). Consumed against the committed `note_nullifiers`
    /// set so the same lock cannot record its escrow twice.
    pub escrow_nullifier: Nullifier,
    /// The independently-verified locked amount to credit the backing.
    pub escrowed: u64,
    /// The caller attests the escrow evidence reached the bridge's REQUIRED trust
    /// level — for the Solana RPC path this is
    /// [`LockProofTrust::ConsensusVerified`](crate::action), NOT a bare
    /// `StructureOnly` RPC echo. A `false` here is refused with
    /// [`BridgeMintError::TrustTooLow`], so an un-consensus-verified RPC cannot
    /// raise the backing it would then mint against.
    pub consensus_verified: bool,
}

/// The committed outcome of a successful [`TurnExecutor::bridge_record_escrow`].
#[derive(Clone, Debug)]
pub struct BridgeEscrowReceipt {
    /// `currently_locked` after this escrow (committed).
    pub currently_locked: u64,
    /// The amount of backing recorded.
    pub escrowed: u64,
}

/// One concurrency-safe bridge mint over committed state.
#[derive(Clone, Debug)]
pub struct BridgeMintRequest {
    /// The cell that holds the mirror asset's control-grade mint-cap (the
    /// relayer / bridge cell). Authorized exactly like any other minter by
    /// [`TurnExecutor::apply_mint`] — the bridge gets no special path.
    pub actor: CellId,
    /// The committed mirror-ledger cell (single source of truth for the two
    /// supply scalars).
    pub ledger_cell: CellId,
    /// The domain-separated consume-once nullifier derived from the bridge
    /// event id (`lock_id` / `payment_intent_id`). Consumed against the
    /// committed `note_nullifiers` set — the double-mint guard.
    pub lock_nullifier: Nullifier,
    /// The dregg cell credited the mirrored asset.
    pub recipient: CellId,
    /// Amount to mint (atomic units). The mint DRAWS this against the
    /// independently-recorded `currently_locked`; a draw exceeding the backing is
    /// refused with [`BridgeMintError::InsufficientLocked`].
    pub amount: u64,
    /// The caller attests the lock evidence reached the bridge's REQUIRED trust
    /// level — for the Solana RPC path this is
    /// [`LockProofTrust::ConsensusVerified`](crate::action), NOT a bare
    /// `StructureOnly` RPC echo. A `false` here is refused with
    /// [`BridgeMintError::TrustTooLow`] BEFORE any state changes, so a
    /// forged/MITM RPC that only reaches `StructureOnly` cannot mint (red-team
    /// BR-1). Defence in depth with the escrow gate: even a spurious `true` mint
    /// can only draw against an independently consensus-verified escrow leg.
    pub consensus_verified: bool,
}

/// The committed outcome of a successful [`TurnExecutor::bridge_mint_against_lock`].
#[derive(Clone, Debug)]
pub struct BridgeMintReceipt {
    /// `currently_locked` after this mint (committed).
    pub currently_locked: u64,
    /// `live_supply` after this mint (committed).
    pub live_supply: u64,
    /// The amount minted.
    pub amount: u64,
    /// The recipient credited.
    pub recipient: CellId,
    /// The conserving `Effect::Mint` that was applied (well debit + recipient
    /// credit, Σδ=0). Returned for the record, mirroring `MirrorMint.effect`.
    pub effect: Effect,
}

/// Why a committed bridge mint was refused. The state is left unchanged on
/// every error (atomic rollback).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BridgeMintError {
    /// The committed mirror-ledger cell does not exist.
    LedgerCellNotFound(CellId),
    /// The `lock_id` nullifier is already in the committed `note_nullifiers`
    /// set — this lock was already mirrored by SOME (possibly other) relayer.
    /// This is the double-mint reject.
    DuplicateLock,
    /// Minting `amount` would push committed `live_supply` above committed
    /// `currently_locked` (the conservation invariant). Now genuinely reachable:
    /// the mint draws against an INDEPENDENTLY-recorded escrow leg, so a draw with
    /// no (or insufficient) backing is refused here (red-team BR-2).
    InsufficientLocked { live: u64, locked: u64, amount: u64 },
    /// The lock/escrow evidence did not reach the bridge's required trust level
    /// (e.g. a Solana `StructureOnly` RPC echo rather than `ConsensusVerified`).
    /// Refused before any state change (red-team BR-1).
    TrustTooLow,
    /// A supply addition overflowed `u64`.
    Overflow,
    /// The conserving `Effect::Mint` was refused (e.g. the actor does not hold
    /// the mint-cap, or a liveness/authority gate failed). Everything is rolled
    /// back.
    MintFailed(String),
}

impl std::fmt::Display for BridgeMintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LedgerCellNotFound(id) => {
                write!(f, "committed mirror-ledger cell {id} not found")
            }
            Self::DuplicateLock => {
                write!(
                    f,
                    "lock_id already consumed in committed note_nullifiers (double-mint prevented)"
                )
            }
            Self::InsufficientLocked {
                live,
                locked,
                amount,
            } => write!(
                f,
                "committed mint of {amount} would break conservation: live {live} + {amount} > locked {locked}"
            ),
            Self::TrustTooLow => write!(
                f,
                "lock/escrow evidence below the required trust level (StructureOnly RPC echo, not ConsensusVerified) — refused"
            ),
            Self::Overflow => write!(f, "committed supply accounting overflow"),
            Self::MintFailed(e) => write!(f, "conserving Effect::Mint refused: {e}"),
        }
    }
}

impl std::error::Error for BridgeMintError {}

impl TurnExecutor {
    /// Atomically mirror-mint against a bridge lock, over COMMITTED state.
    ///
    /// This is the concurrency-safe replacement for the per-relayer
    /// `MirrorState::mint_against_lock` RAM path: the consume-once `lock_id`
    /// nullifier and the supply ledger now live in the committed state root, so
    /// the executor's per-turn serialization is the global serialization point.
    /// See the module docs for the three legs (nullifier consume + committed
    /// ledger debit + conserving mint) and why N relayers are now safe.
    ///
    /// On any error the committed state (nullifier set, ledger cell, balances)
    /// is left exactly as it was.
    pub fn bridge_mint_against_lock(
        &self,
        ledger: &mut Ledger,
        req: &BridgeMintRequest,
    ) -> Result<BridgeMintReceipt, BridgeMintError> {
        // (0) Trust gate (red-team BR-1): a lock the relayer only verified to
        //     `StructureOnly` over a plain/forged/MITM RPC cannot mint. The caller
        //     sets `consensus_verified` ONLY from a `ConsensusVerified` proof (or a
        //     trusted-oracle attestation). Refuse before touching any state.
        if !req.consensus_verified {
            return Err(BridgeMintError::TrustTooLow);
        }

        // (1) The committed mirror-ledger cell must exist and gives us the
        //     authoritative supply numbers (NOT a per-relayer u64).
        let (locked, live) = match ledger.get(&req.ledger_cell) {
            Some(c) => read_supply(c),
            None => return Err(BridgeMintError::LedgerCellNotFound(req.ledger_cell)),
        };
        let new_live = live
            .checked_add(req.amount)
            .ok_or(BridgeMintError::Overflow)?;

        let mut journal = LedgerJournal::new();

        // (2) Consume-once the lock nullifier against the COMMITTED
        //     note_nullifiers set — the exact atomic contains-then-insert +
        //     double-spend reject NoteSpend/BridgeMint ride. This is the AUTHORITY
        //     on double-mint: a racing relayer replaying the SAME lock_id is
        //     rejected here regardless of its in-RAM MirrorState (it runs before
        //     the conservation check so a replay reports `DuplicateLock`, the
        //     precise cause).
        {
            let mut set = self.note_nullifiers.lock().unwrap();
            if set.contains(&req.lock_nullifier) {
                return Err(BridgeMintError::DuplicateLock);
            }
            set.insert(req.lock_nullifier)
                .map_err(|_| BridgeMintError::DuplicateLock)?;
        }
        journal.record_note_nullifier_inserted(req.lock_nullifier);

        // (3) DRAW against the independently-recorded backing: enforce `live +
        //     amount <= currently_locked`. This is the NON-vacuous conservation
        //     backstop (red-team BR-2): the mint does NOT credit `currently_locked`
        //     itself — that leg is raised separately by `bridge_record_escrow` from
        //     independently-verified consensus — so a (fresh-lock) mint with no or
        //     insufficient escrow is refused, and its nullifier is rolled back so a
        //     later escrow can still let it mint.
        if new_live > locked {
            journal.rollback(ledger, &self.bridged_nullifiers, &self.note_nullifiers);
            return Err(BridgeMintError::InsufficientLocked {
                live,
                locked,
                amount: req.amount,
            });
        }

        // (4) Raise the committed `live_supply` leg only (journaled, so a later
        //     failure unwinds it together with the nullifier consume).
        {
            let cell = match ledger.get_mut(&req.ledger_cell) {
                Some(c) => c,
                None => {
                    journal.rollback(ledger, &self.bridged_nullifiers, &self.note_nullifiers);
                    return Err(BridgeMintError::LedgerCellNotFound(req.ledger_cell));
                }
            };
            let old_live = *cell
                .state
                .get_field(LIVE_FIELD)
                .expect("fixed slot 1 always present");
            journal.record_set_field(req.ledger_cell, LIVE_FIELD, Some(old_live));
            cell.state.set_field(LIVE_FIELD, encode_u64(new_live));
        }

        // (5) The conserving Effect::Mint (well debit + recipient credit, cap-
        //     gated). SAME critical section: a failure rolls back legs (3)+(4).
        if let Err((e, _path)) = self.apply_mint(
            ledger,
            &[],
            &req.actor,
            &mut journal,
            &req.recipient,
            0,
            req.amount,
        ) {
            journal.rollback(ledger, &self.bridged_nullifiers, &self.note_nullifiers);
            return Err(BridgeMintError::MintFailed(e.to_string()));
        }

        Ok(BridgeMintReceipt {
            currently_locked: locked,
            live_supply: new_live,
            amount: req.amount,
            recipient: req.recipient,
            effect: Effect::Mint {
                target: req.recipient,
                slot: 0,
                amount: req.amount,
            },
        })
    }

    /// Record an INDEPENDENTLY-verified escrow over committed state, raising
    /// `currently_locked` (the conservation backing) by `req.escrowed`.
    ///
    /// This is the independent source of `currently_locked` (red-team BR-2/BR-3):
    /// the caller MUST have verified — to `ConsensusVerified`, not `StructureOnly`
    /// — that `escrowed` was genuinely locked into the bridge's vault BEFORE
    /// calling. The mint draws against this backing SEPARATELY via
    /// [`Self::bridge_mint_against_lock`], so the two legs are distinct
    /// accumulators and conservation is a real constraint (not the old
    /// credit-both-legs-by-the-same-amount vacuity).
    ///
    /// Deduped by `req.escrow_nullifier` against the committed `note_nullifiers`
    /// set so one lock can never inflate the backing twice. On any error the
    /// committed state is left exactly as it was.
    pub fn bridge_record_escrow(
        &self,
        ledger: &mut Ledger,
        req: &BridgeEscrowRecord,
    ) -> Result<BridgeEscrowReceipt, BridgeMintError> {
        // (0) Trust gate (red-team BR-1): only consensus-verified escrow may raise
        //     the backing. A StructureOnly RPC echo cannot record locked supply.
        if !req.consensus_verified {
            return Err(BridgeMintError::TrustTooLow);
        }

        // (1) Authoritative current backing.
        let (locked, _live) = match ledger.get(&req.ledger_cell) {
            Some(c) => read_supply(c),
            None => return Err(BridgeMintError::LedgerCellNotFound(req.ledger_cell)),
        };
        let new_locked = locked
            .checked_add(req.escrowed)
            .ok_or(BridgeMintError::Overflow)?;

        let mut journal = LedgerJournal::new();

        // (2) Consume-once the ESCROW nullifier — one lock records its escrow once.
        {
            let mut set = self.note_nullifiers.lock().unwrap();
            if set.contains(&req.escrow_nullifier) {
                return Err(BridgeMintError::DuplicateLock);
            }
            set.insert(req.escrow_nullifier)
                .map_err(|_| BridgeMintError::DuplicateLock)?;
        }
        journal.record_note_nullifier_inserted(req.escrow_nullifier);

        // (3) Raise the committed `currently_locked` leg only.
        {
            let cell = match ledger.get_mut(&req.ledger_cell) {
                Some(c) => c,
                None => {
                    journal.rollback(ledger, &self.bridged_nullifiers, &self.note_nullifiers);
                    return Err(BridgeMintError::LedgerCellNotFound(req.ledger_cell));
                }
            };
            let old_locked = *cell
                .state
                .get_field(LOCKED_FIELD)
                .expect("fixed slot 0 always present");
            journal.record_set_field(req.ledger_cell, LOCKED_FIELD, Some(old_locked));
            cell.state.set_field(LOCKED_FIELD, encode_u64(new_locked));
        }

        Ok(BridgeEscrowReceipt {
            currently_locked: new_locked,
            escrowed: req.escrowed,
        })
    }
}
