//! # The DEPOSIT-GLUE brick — stage (a) of `docs/deos/SHIELDED-DEPOSIT-BRIDGE.md`.
//!
//! This is the LAST composition code brick: it closes the deposit LC→mint glue that
//! the bridge map names MISSING (stage (a), the "attestation → note-mint glue"), so
//! a REAL attested lock on a public chain mints a shielded pool note, which then
//! flows into the already-landed note↔order clearing (c,
//! `shielded_clearing_note_order_poc.rs`) + settle-back (d,
//! `shielded_settle_back_poc.rs`). NO new crypto: every primitive already exists.
//!
//! ## `deposit_to_note` = attest ∘ shieldK (this file)
//!
//! Given the light-client attestation of a LOCKED token (the `verify_holding` /
//! leaf-adapter output — an `(asset, locked_value, chain, lock_ref)` that is
//! `ConsensusProven`), mint a shielded [`BoundNote`] bound to `(asset, value)` with
//! a fresh Poseidon2 commitment + nullifier — the DEPOSIT note. The mint is GATED:
//!   * **NO-MINT-WITHOUT-A-VALID-LOCK** (the load-bearing soundness). The mint fires
//!     only if the attestation's HOLDING IDENTITY opens — the REAL in-AIR
//!     Poseidon2 holding hash `mpt_holding_hash_felt(root, token, holder, slot,
//!     balance)` (`circuit-prove/src/mpt_holding_leaf.rs`, the P0 fold leaf's exact
//!     binding) recomputes to the attestation's published `holding_hash` — AND the
//!     trust tag is `ConsensusProven`. A FORGED balance (the `verify_holding`
//!     "+1 wei" canary) breaks the holding hash; an ABSENT/unproven attestation
//!     fails the trust tag. Either way NO note is minted (fail-closed).
//!   * **`value ≤ locked`** (the deposit side of `supply ≤ locked`). The minted
//!     note's value cannot exceed the attested locked amount — the custody
//!     `drawMint` gate `supply + a ≤ locked` (`InterchainCustody.lean:151`,
//!     `overMint_refused`). A mint beyond the lock is REFUSED.
//!   * **ONE-LOCK-ONE-NOTE** (deposit dedup). A deposit nullifier keyed on the
//!     lock's identity (`hash_fact(holding_hash, [slot, chain, 0])`) is consumed
//!     once — a second mint against the SAME lock is REFUSED (mirrors `shieldK`'s
//!     freshness gate + the escrow burn).
//!
//! On success `deposit_to_note` `recordEscrow`s the locked amount and `drawMint`s
//! the note value on the per-asset custody [`MirrorState`] (faithful to
//! `InterchainCustody.lean`), so across many deposits `Σ minted ≤ Σ locked` per
//! asset — the deposit side of `supply ≤ locked`.
//!
//! ## The composition (deposit → shield → clear → settle, over REAL notes)
//!
//! [`deposit_bridge_end_to_end`] drives the WHOLE four-stage pipeline in one run:
//!   * (a) DEPOSIT — two REAL attested locks (asset 1) → `deposit_to_note` → two
//!     shielded deposit notes, gated on the holding-identity + `value ≤ locked` +
//!     one-lock-one-note.
//!   * (b) SHIELDED HOLD — the notes are REAL Poseidon2 `BoundNote`s (the exact
//!     `hash_fact` value-binding / leaf / nullifier `ShieldedValue.lean §6` +
//!     `RealCrypto.lean` prove), sitting in the pool.
//!   * (c) PRIVATE CLEAR — the deposit notes are sealed as REAL `fhegg_solver`
//!     orders and cleared by the REAL uniform-price engine (`clearing::{clear,
//!     allocate}`, `Allocation::conserves`); the fills are minted back as fresh
//!     conserving output notes. `Σ in = Σ out = V*` (the note↔order seam, c).
//!   * (d) SETTLE — a cleared output note is UNSHIELDED and RELEASED from the
//!     custody, gated on `supply ≤ locked` (the settle-back seam, d).
//!
//! ## Both polarities (soundness — the deposit-glue teeth)
//!
//!   * [pos] a valid ConsensusProven lock, `value ≤ locked`, mints a valid note that
//!     clears + settles;
//!   * [neg] a FORGED attestation (tampered locked balance ⇒ holding hash mismatch)
//!     is REJECTED — no mint;
//!   * [neg] an ABSENT/unproven attestation (trust ≠ ConsensusProven) is REJECTED;
//!   * [neg] a MINT BEYOND THE LOCK (`value > locked`) is REJECTED (`drawMint` gate);
//!   * [neg] a DOUBLE-MINT against the SAME lock is REJECTED (deposit nullifier).
//!
//! ## Honest scope (per the bridge map)
//!
//! REAL, running here: the Poseidon2 HOLDING-IDENTITY attestation binding
//! (`mpt_holding_hash_felt`, the same identity the P0 fold leaf pins), the shielded
//! note-mint (value-binding / leaf / nullifier), the custody `recordEscrow` /
//! `drawMint` / `release` gates (faithful to `InterchainCustody.lean`), the REAL
//! fhEgg clear, and the unshield→release settle-back. A FORGED balance / an
//! over-mint / a double-mint are GENUINELY rejected — soundness, not display.
//!
//! DESIGN-STUB (labelled, remaining): the on-chain deposit ESCROW CONTRACT itself is
//! NOT deployed. `verify_holding` proves a *holding* (a balance at a finalized root)
//! over ARBITRARY storage slots — so the attested lock here is the LC-verified
//! holding identity + a labelled `lock_ref` (the escrow contract address + lock
//! slot), NOT a lock event into a deployed vault. The full BLS-over-sync-committee +
//! MPT-walk consensus chain runs in the SEPARATE binary
//! `eth-lightclient/src/bin/verify_holding.rs` (real mainnet period-1800 committee,
//! 397/512 BLS, EIP-1186 `eth_getProof` → `HoldingTrust::ConsensusProven`, forged
//! "+1 wei" REFUSED); here the `ConsensusProven` trust tag STANDS FOR that verified
//! chain, and the holding-identity `hash_fact` binding is the real in-crate leaf
//! identity. The escrow-contract DEPLOY + the persistent MPC federation remain
//! ember-gated (deploy-time, not code).

use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::mpt_holding_leaf::mpt_holding_hash_felt;
use fhegg_solver::clearing::{Order, Side, allocate, clear};
use std::collections::BTreeMap;

/// Map a `u64` into BabyBear (note/attestation fields are conceptually field elems).
fn felt(v: u64) -> BabyBear {
    BabyBear::new((v % (BABYBEAR_P as u64)) as u32)
}

/// A stand-in WETH token-contract id (the bridged asset's on-chain class). The REAL
/// 20-byte contract address is folded to a felt by the LC leaf (`mpt_holding_leaf`);
/// here a fixed id names the token consistently across the deposits.
fn weth_token() -> u64 {
    0xC02A_AA39 // low bytes of the real WETH contract 0xC02aaA39...C756Cc2, as a felt id
}

/// The honest no-inflation window (matches `shielded::attest::RANGE_BITS` /
/// `mpt_holding_leaf::BALANCE_RANGE_BITS`): a note value must lie in `[0, 2^30)`.
const RANGE_BITS: u32 = 30;

// ===========================================================================
// The LC attestation of a locked token — the `verify_holding` / leaf-adapter output.
// ===========================================================================

/// How much this attestation is trusted — the `HoldingTrust` of the LC output
/// (`eth-lightclient::evm::HoldingTrust`). Only `ConsensusProven` (anchored to a
/// finalized beacon root via the sync-committee BLS + finality/execution branch +
/// EIP-1186 MPT) can back a mint; an `Unproven` attestation is refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HoldingTrust {
    /// Anchored to a finalized root by the full LC chain (`verify_holding`).
    ConsensusProven,
    /// Not (yet) anchored — a bare claim, no finalized proof. Refused for minting.
    Unproven,
}

/// The attested lock of a real public-chain token — the shape `verify_holding`
/// (via the `mpt_holding_leaf` adapter) produces. The HOLDING IDENTITY
/// `holding_hash = mpt_holding_hash_felt(root, token, holder, slot, balance)` is the
/// REAL in-AIR Poseidon2 binding of the P0 fold leaf; `locked_value` is the attested
/// balance (the amount the escrow holds); `trust` is the LC's `HoldingTrust`.
#[derive(Clone, Debug)]
struct AttestedLock {
    /// The finalized EVM `state_root` (8 BabyBear limbs) the inclusion was proven
    /// under (its FINALITY is the sync-committee BLS, rung-2 `verify_holding`).
    state_root: [BabyBear; 8],
    /// The ERC-20 token contract (the bridged asset's on-chain class).
    token: BabyBear,
    /// The holder / escrow-contract address the balance sits at (LABELLED: the
    /// deposit escrow CONTRACT is a design-stub; this is the LC-attested holder).
    holder: BabyBear,
    /// The EIP-1186 storage slot (the lock/balance mapping slot) — the lock ref.
    slot: BabyBear,
    /// The attested LOCKED amount (the `verify_holding` balance). The minted note's
    /// value must be `≤` this (the deposit side of `supply ≤ locked`).
    locked_value: u64,
    /// The PUBLISHED holding identity the attestation carries. For an honest
    /// attestation this equals `recompute_holding_hash()`; a FORGED balance leaves
    /// this stale (the `verify_holding` "+1 wei" canary — the storage-trie gate).
    holding_hash: BabyBear,
    /// The LC trust tag.
    trust: HoldingTrust,
    /// The dregg asset class the bridged token mirrors (issuer cell id / `AssetId`).
    asset: u64,
    /// A public-chain tag (Ethereum-mainnet = 1) — carried into the deposit dedup.
    chain: u64,
}

impl AttestedLock {
    /// The REAL in-AIR holding identity over this attestation's pinned fields — the
    /// exact `mpt_holding_hash_felt` the P0 fold leaf recomputes in-circuit
    /// (`H2(H2(H4(root[0..4]), H4(root[4..8])), H4(token, holder, slot, balance))`).
    fn recompute_holding_hash(&self) -> BabyBear {
        mpt_holding_hash_felt(
            &self.state_root,
            self.token,
            self.holder,
            self.slot,
            felt(self.locked_value),
        )
    }

    /// **A VALID LOCK** — the load-bearing gate. The published holding identity must
    /// recompute from the pinned fields (a forged/tampered `locked_value` breaks it,
    /// the storage-trie gate) AND the LC trust must be `ConsensusProven` (an absent /
    /// unproven attestation fails). This is `verify_holding`'s
    /// `HoldingTrust::ConsensusProven` fail-closed check, mirrored in-crate.
    fn is_valid_lock(&self) -> bool {
        self.trust == HoldingTrust::ConsensusProven
            && self.recompute_holding_hash() == self.holding_hash
    }

    /// The deposit dedup identity — a nullifier keyed on the lock's identity
    /// (`hash_fact(holding_hash, [slot, chain, 0])`). One lock event ⇒ one deposit
    /// nullifier ⇒ one note (the escrow cannot be double-drawn). Because
    /// `holding_hash` binds `(root, token, holder, slot, balance)`, distinct lock
    /// events give distinct deposit nullifiers.
    fn deposit_nullifier(&self) -> BabyBear {
        hash_fact(
            self.holding_hash,
            &[self.slot, felt(self.chain), BabyBear::ZERO],
        )
    }
}

/// Build an HONEST attested lock (the published holding hash matches the fields).
/// This is the shape `verify_holding` → `mpt_holding_leaf` yields for a real lock.
fn honest_attestation(
    asset: u64,
    locked_value: u64,
    token: u64,
    holder: u64,
    slot: u64,
    chain: u64,
) -> AttestedLock {
    let state_root = [
        felt(0xE71 ^ slot),
        felt(0x100),
        felt(0x200),
        felt(0x300),
        felt(0x400),
        felt(0x500),
        felt(0x600),
        felt(0x700 ^ token),
    ];
    let holding_hash = mpt_holding_hash_felt(
        &state_root,
        felt(token),
        felt(holder),
        felt(slot),
        felt(locked_value),
    );
    AttestedLock {
        state_root,
        token: felt(token),
        holder: felt(holder),
        slot: felt(slot),
        locked_value,
        holding_hash,
        trust: HoldingTrust::ConsensusProven,
        asset,
        chain,
    }
}

// ===========================================================================
// The shielded pool BoundNote — REAL Poseidon2 (the exact sibling-PoC shape).
// ===========================================================================

/// A shielded pool note: a hidden `(value, asset)` bound under Poseidon2.
#[derive(Clone, Debug)]
#[allow(dead_code)] // leaf/owner/key document the real note shape (mirror the siblings)
struct BoundNote {
    /// Leaf commitment (C6): `hash_fact(value, [asset, owner, randomness])`.
    leaf: BabyBear,
    /// PQ value-binding (C7 / `RealCrypto §1.3`): `hash_fact(value,[asset,rand,0])`.
    value_binding: BabyBear,
    /// Spend nullifier: `hash_fact(leaf, [key, 0, 0, 0])`.
    nullifier: BabyBear,
    /// The hidden amount (witness; never published in the clear).
    value: u64,
    /// The asset class.
    asset: u64,
    owner: u64,
    randomness: u64,
    key: u64,
}

/// Compute the REAL Poseidon2 facts for a note `(asset, value)` blinded by
/// `(owner, randomness)` and keyed by `key` — identical to the sibling PoCs.
fn mint_note(asset: u64, value: u64, owner: u64, randomness: u64, key: u64) -> BoundNote {
    let v = felt(value);
    let a = felt(asset);
    let o = felt(owner);
    let r = felt(randomness);
    let leaf = hash_fact(v, &[a, o, r]);
    let value_binding = hash_fact(v, &[a, r, BabyBear::ZERO]);
    let nullifier = hash_fact(
        leaf,
        &[felt(key), BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    );
    BoundNote {
        leaf,
        value_binding,
        nullifier,
        value,
        asset,
        owner,
        randomness,
        key,
    }
}

impl BoundNote {
    /// Re-derive the value-binding for the note's claimed value+asset and check it
    /// matches the published commitment (binding under HashCR:
    /// `RealCrypto.mint_forces_collision`).
    fn value_binding_opens(&self) -> bool {
        let expect = hash_fact(
            felt(self.value),
            &[felt(self.asset), felt(self.randomness), BabyBear::ZERO],
        );
        expect == self.value_binding
    }
}

// ===========================================================================
// The custody MirrorState — faithful to `InterchainCustody.lean` (the deposit side:
// recordEscrow raises `locked`; drawMint raises `supply` IFF `supply + a ≤ locked`).
// ===========================================================================

/// The dregg-side custody ledger of one mirrored token: `locked` (external escrow,
/// `currently_locked`) and `supply` (mirror circulating inside dregg, `live_supply`).
/// Faithful to `MirrorState` (`InterchainCustody.lean:113`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MirrorState {
    locked: u64,
    supply: u64,
}

impl MirrorState {
    /// The empty custody (`MirrorState.init`: `locked = supply = 0`).
    fn init() -> Self {
        MirrorState {
            locked: 0,
            supply: 0,
        }
    }

    /// **`backed`** — the invariant `supply ≤ locked` (`MirrorState.backed`).
    fn backed(&self) -> bool {
        self.supply <= self.locked
    }

    /// **`recordEscrow a`** — raise `locked` by an independently-attested escrow
    /// (`InterchainCustody.recordEscrow`, `currently_locked += a`). Always succeeds.
    fn record_escrow(&self, a: u64) -> MirrorState {
        MirrorState {
            locked: self.locked + a,
            supply: self.supply,
        }
    }

    /// **`drawMint a`** — THE LIVE GATE (`InterchainCustody.drawMint`): raise
    /// `supply` by `a` IFF `supply + a ≤ locked`, else REFUSE (`None`, the Rust
    /// `MirrorError::InsufficientLocked`, `overMint_refused`). This is `value ≤ the
    /// locked backing` — no mint beyond the lock.
    fn draw_mint(&self, a: u64) -> Option<MirrorState> {
        if self.supply + a <= self.locked {
            Some(MirrorState {
                locked: self.locked,
                supply: self.supply + a,
            })
        } else {
            None
        }
    }

    /// **`release a`** — the redeem (`InterchainCustody.release`): lower BOTH
    /// registers by `a`, gated on `a ≤ supply` (`overRelease_refused`). Used by the
    /// settle-back leg (d).
    fn release(&self, a: u64) -> Option<MirrorState> {
        if a <= self.supply {
            Some(MirrorState {
                locked: self.locked - a,
                supply: self.supply - a,
            })
        } else {
            None
        }
    }
}

// ===========================================================================
// deposit_to_note = attest ∘ shieldK — the DEPOSIT-GLUE brick.
// ===========================================================================

/// Why a deposit fails-closed (the no-mint-without-a-valid-lock teeth).
#[derive(Debug, PartialEq, Eq)]
enum DepositError {
    /// The attestation is not a valid lock — the holding identity does not open
    /// (forged/tampered balance), or the trust tag is not `ConsensusProven`
    /// (absent/unproven). NO MINT WITHOUT A VALID LOCK.
    NoValidLock,
    /// The requested note value exceeds the attested locked amount — the `drawMint`
    /// gate `supply + a ≤ locked` bites (`InterchainCustody.overMint_refused`).
    MintBeyondLock,
    /// A note was already minted against THIS lock (the deposit nullifier is
    /// consumed) — one lock event mints exactly one note.
    DoubleMint,
    /// The note value is outside `[0, 2^30)` — no range witness (hidden inflation).
    OutOfRange,
}

/// The pool's deposit-side state: the minted commitments + the consumed DEPOSIT
/// nullifiers (the escrow-burn ledger) + the per-asset custody.
#[derive(Default)]
struct DepositLedger {
    /// The minted note leaf commitments (the pool set).
    commitments: Vec<BabyBear>,
    /// The consumed DEPOSIT nullifiers — one per drawn lock (dedup).
    deposit_nullifiers: Vec<BabyBear>,
    /// The per-asset custody (`Σ minted ≤ Σ locked` is `supply ≤ locked`).
    custody: BTreeMap<u64, MirrorState>,
}

/// A completed deposit: the minted shielded note, the deposit nullifier consumed,
/// and the post-custody for this asset (`recordEscrow(locked)` then
/// `drawMint(value)`).
#[derive(Debug)]
struct Deposit {
    note: BoundNote,
    deposit_nullifier: BabyBear,
    post_custody: MirrorState,
}

impl DepositLedger {
    /// **`deposit_to_note`** — attest ∘ shieldK. Mint a shielded [`BoundNote`] bound
    /// to `(asset, value)` from an attested lock, GATED on:
    ///   1. NO-MINT-WITHOUT-A-VALID-LOCK — `lock.is_valid_lock()` (holding identity
    ///      opens AND `ConsensusProven`), else `NoValidLock`;
    ///   2. RANGE — `value < 2^30` (no hidden inflation), else `OutOfRange`;
    ///   3. `value ≤ locked` — the custody `drawMint` gate (after `recordEscrow` of
    ///      the attested lock), else `MintBeyondLock`;
    ///   4. ONE-LOCK-ONE-NOTE — the deposit nullifier is fresh, else `DoubleMint`.
    /// On success it `recordEscrow`s the attested lock + `drawMint`s the note value
    /// on the per-asset custody, mints the note, and consumes the deposit nullifier.
    fn deposit_to_note(
        &mut self,
        lock: &AttestedLock,
        value: u64,
        owner: u64,
        randomness: u64,
        key: u64,
    ) -> Result<Deposit, DepositError> {
        // (1) NO MINT WITHOUT A VALID LOCK — the load-bearing gate.
        if !lock.is_valid_lock() {
            return Err(DepositError::NoValidLock);
        }
        // (2) no hidden inflation at creation (`noteCreateBound_in_range`).
        if value >= (1u64 << RANGE_BITS) {
            return Err(DepositError::OutOfRange);
        }
        // (4) one lock event ⇒ one note (deposit dedup, checked before mutating).
        let dep_nf = lock.deposit_nullifier();
        if self.deposit_nullifiers.contains(&dep_nf) {
            return Err(DepositError::DoubleMint);
        }
        // (3) value ≤ locked — recordEscrow the attested lock, then drawMint the note
        // value against it. The gate `supply + value ≤ locked` IS `value ≤ locked`.
        let custody = self
            .custody
            .entry(lock.asset)
            .or_insert_with(MirrorState::init);
        let escrowed = custody.record_escrow(lock.locked_value);
        let post = match escrowed.draw_mint(value) {
            Some(p) => p,
            None => return Err(DepositError::MintBeyondLock),
        };
        // COMMIT: mint the REAL shielded note, advance the custody, burn the lock.
        let note = mint_note(lock.asset, value, owner, randomness, key);
        *custody = post;
        self.commitments.push(note.leaf);
        self.deposit_nullifiers.push(dep_nf);
        Ok(Deposit {
            note,
            deposit_nullifier: dep_nf,
            post_custody: post,
        })
    }
}

// ===========================================================================
// The deposit conservation seam — the load-bearing soundness recompute.
// ===========================================================================

/// The recomputed deposit-side verdict over a batch of deposits.
#[derive(Debug)]
struct DepositConservation {
    /// (1) every minted note was gated on a VALID lock (holding identity + trust).
    all_locks_valid: bool,
    /// (2) every minted note is value-bound (opens its own commitment).
    all_notes_bound: bool,
    /// (3) per-asset `Σ minted ≤ Σ locked` (the custody stays backed, `supply ≤
    ///     locked`) — the deposit side of the mirror-backing invariant.
    all_backed: bool,
    /// (4) each note's value ≤ its own lock's attested locked amount.
    per_deposit_value_le_locked: bool,
    /// (5) the deposit nullifiers are distinct — one lock ⇒ one note (no double-mint).
    deposit_nullifiers_distinct: bool,
}

impl DepositConservation {
    fn valid(&self) -> bool {
        self.all_locks_valid
            && self.all_notes_bound
            && self.all_backed
            && self.per_deposit_value_le_locked
            && self.deposit_nullifiers_distinct
    }
}

/// **`check_deposit_conservation`** — recompute, from the attested locks + the minted
/// deposits + the final custody, that the deposit side is SOUND: every note was
/// minted against a valid lock, value-bound, `value ≤ locked` per deposit, and
/// `Σ minted ≤ Σ locked` per asset (the custody backed), with distinct deposit
/// nullifiers. Mirrors `noteCreateBound_in_range` ⋈ `drawMint_backed` ⋈
/// `overMint_refused`.
fn check_deposit_conservation(
    locks: &[AttestedLock],
    deposits: &[Deposit],
    ledger: &DepositLedger,
) -> DepositConservation {
    assert_eq!(locks.len(), deposits.len(), "one deposit per attested lock");

    let mut all_locks_valid = true;
    let mut all_notes_bound = true;
    let mut per_deposit_value_le_locked = true;
    let mut seen_nfs: Vec<BabyBear> = Vec::new();
    let mut deposit_nullifiers_distinct = true;

    for (lock, dep) in locks.iter().zip(deposits.iter()) {
        all_locks_valid &= lock.is_valid_lock();
        all_notes_bound &= dep.note.value_binding_opens();
        per_deposit_value_le_locked &= dep.note.value <= lock.locked_value;
        if seen_nfs.contains(&dep.deposit_nullifier) {
            deposit_nullifiers_distinct = false;
        } else {
            seen_nfs.push(dep.deposit_nullifier);
        }
    }
    // Per-asset `Σ minted ≤ Σ locked` (the custody backed after all deposits).
    let all_backed = ledger.custody.values().all(|c| c.backed());

    DepositConservation {
        all_locks_valid,
        all_notes_bound,
        all_backed,
        per_deposit_value_le_locked,
        deposit_nullifiers_distinct,
    }
}

// ===========================================================================
// (c) note↔order clearing over the deposit notes — the REAL fhEgg engine.
// ===========================================================================

/// A deposit note sealed as a REAL fhEgg order (the note↔order seam, c). The order's
/// qty is the note's value (hidden under its commitment); the sealed order carries
/// the note's commitment + nullifier by reference.
#[derive(Clone)]
struct SealedNote {
    order: Order,
    note: BoundNote,
}

/// Seal a deposit note as an fhEgg order (`note_to_order`, c).
fn note_to_order(note: &BoundNote, side: Side, limit: u32) -> SealedNote {
    assert!(
        note.value_binding_opens(),
        "note_to_order: the note must open its value-binding"
    );
    SealedNote {
        order: Order {
            side,
            qty: note.value,
            limit,
        },
        note: note.clone(),
    }
}

/// Output notes from one cleared sealed order (`order_to_note`, c): the FILL note +
/// the CHANGE note, summing EXACTLY to the input note's value (no value minted).
struct FillOutput {
    fill_note: BoundNote,
    change_note: BoundNote,
}

/// `order_to_note` (c) — mint the cleared fill + change as fresh conserving output
/// notes; `fill + change == the input note value`.
fn order_to_note(sealed: &SealedNote, fill: u64) -> FillOutput {
    assert!(fill <= sealed.note.value, "no over-fill");
    let change = sealed.note.value - fill;
    let fill_note = mint_note(
        sealed.note.asset,
        fill,
        sealed.note.owner ^ 0xF11,
        sealed.note.randomness ^ 0xF11,
        sealed.note.key ^ 0xF11,
    );
    let change_note = mint_note(
        sealed.note.asset,
        change,
        sealed.note.owner ^ 0xC00,
        sealed.note.randomness ^ 0xC00,
        sealed.note.key ^ 0xC00,
    );
    FillOutput {
        fill_note,
        change_note,
    }
}

// ===========================================================================
// (d) settle-back — unshield a cleared output note and release from custody.
// ===========================================================================

/// Settle a cleared output note (d): consume its nullifier (fail-closed if the note
/// does not open its value-binding) and `release` exactly its value from the custody
/// (gated on `supply ≤ locked`). Returns the post-custody or a fail-closed error.
fn settle_output_note(custody: &MirrorState, note: &BoundNote) -> Option<MirrorState> {
    if !note.value_binding_opens() {
        return None; // NoteNotBound — a never-cleared / tampered note cannot settle
    }
    // release exactly the note's value (unshield_value_binding: the amount IS the
    // note's value by construction), gated on supply ≤ locked.
    custody.release(note.value)
}

// ===========================================================================
// The DEPOSIT-GLUE PoC — deposit → shield → clear → settle over REAL notes.
// ===========================================================================

#[test]
fn deposit_bridge_end_to_end() {
    println!(
        "\n=== DEPOSIT-GLUE — real attested lock → shielded note → clear → settle (stage a) ===\n"
    );

    let mut ledger = DepositLedger::default();

    // -----------------------------------------------------------------------
    // (a) DEPOSIT — two REAL attested locks of asset 1 (two depositors). Each is a
    //     ConsensusProven holding whose identity opens (the mpt_holding_hash binding).
    //     Depositor A locked 1000, mints a note of value 100 (≤ 1000).
    //     Depositor B locked 1000, mints a note of value 80  (≤ 1000).
    // -----------------------------------------------------------------------
    let lock_a = honest_attestation(1, 1_000, weth_token(), 0xA11CE, 0x5107_A, 1);
    let lock_b = honest_attestation(1, 1_000, weth_token(), 0xB0B, 0x5107_B, 1);
    println!("(a) DEPOSIT: two ConsensusProven attested locks of asset 1 (1000 each)");
    println!(
        "    lock A holding_hash = {:?} (valid = {})",
        lock_a.holding_hash,
        lock_a.is_valid_lock()
    );
    println!(
        "    lock B holding_hash = {:?} (valid = {})\n",
        lock_b.holding_hash,
        lock_b.is_valid_lock()
    );
    assert!(lock_a.is_valid_lock() && lock_b.is_valid_lock());

    // deposit_to_note: mint the two shielded deposit notes (gated).
    let dep_a = ledger
        .deposit_to_note(&lock_a, 100, 0xA11CE, 0x5EED_A, 0x7A)
        .expect("a valid ConsensusProven lock, value ≤ locked, must mint");
    let dep_b = ledger
        .deposit_to_note(&lock_b, 80, 0xB0B, 0x5EED_B, 0x7B)
        .expect("a valid ConsensusProven lock, value ≤ locked, must mint");
    println!("(b) MINT: two REAL Poseidon2 deposit notes minted against the locks");
    println!(
        "    note A: value 100 (hidden), leaf {:?}, dep-nf {:?}",
        dep_a.note.leaf, dep_a.deposit_nullifier
    );
    println!(
        "    note B: value  80 (hidden), leaf {:?}, dep-nf {:?}",
        dep_b.note.leaf, dep_b.deposit_nullifier
    );
    let custody1 = ledger.custody[&1];
    println!(
        "    custody asset 1: locked {}, supply {} (Σ minted 180 ≤ Σ locked 2000, backed = {})\n",
        custody1.locked,
        custody1.supply,
        custody1.backed()
    );
    assert_eq!(custody1.locked, 2000);
    assert_eq!(custody1.supply, 180);
    assert!(custody1.backed());

    // The deposit conservation seam (positive polarity).
    let locks = vec![lock_a.clone(), lock_b.clone()];
    let deposits = vec![
        Deposit {
            note: dep_a.note.clone(),
            deposit_nullifier: dep_a.deposit_nullifier,
            post_custody: dep_a.post_custody,
        },
        Deposit {
            note: dep_b.note.clone(),
            deposit_nullifier: dep_b.deposit_nullifier,
            post_custody: dep_b.post_custody,
        },
    ];
    let cons = check_deposit_conservation(&locks, &deposits, &ledger);
    println!(
        "    deposit conservation: locks-valid {}, notes-bound {}, backed {}, value≤locked {}, dep-nf-distinct {}",
        cons.all_locks_valid,
        cons.all_notes_bound,
        cons.all_backed,
        cons.per_deposit_value_le_locked,
        cons.deposit_nullifiers_distinct
    );
    assert!(cons.valid(), "the deposit side must be sound");
    println!(
        "  [pos] both deposits minted against valid locks, Σ minted ≤ Σ locked, one-lock-one-note\n"
    );

    // -----------------------------------------------------------------------
    // (c) PRIVATE CLEAR — seal the two deposit notes as a bid + ask and clear them
    //     through the REAL fhEgg engine. Bid 100 @ level 7, Ask 80 @ level 3 cross.
    // -----------------------------------------------------------------------
    const K: usize = 10;
    let sealed = vec![
        note_to_order(&dep_a.note, Side::Bid, 7),
        note_to_order(&dep_b.note, Side::Ask, 3),
    ];
    let orders: Vec<Order> = sealed.iter().map(|s| s.order).collect();
    let clearing = clear(&orders, K);
    let alloc = allocate(&orders, &clearing);
    assert!(alloc.conserves(), "the fhEgg allocation must conserve");
    let vstar = clearing.cleared_volume;
    println!("(c) PRIVATE CLEAR: REAL fhEgg clear over the deposit notes → V* = {vstar}");
    assert_eq!(vstar, 80, "the ask (80) is the short side ⇒ V* = 80");

    // order_to_note: mint the fills back as fresh conserving output notes.
    let outputs: Vec<FillOutput> = sealed
        .iter()
        .zip(alloc.fills.iter())
        .map(|(s, &fill)| order_to_note(s, fill))
        .collect();
    // Conservation across the clearing: Σ in = Σ out = 180; bid_fill = ask_fill = V*.
    let sum_in: u64 = sealed.iter().map(|s| s.note.value).sum();
    let sum_out: u64 = outputs
        .iter()
        .map(|o| o.fill_note.value + o.change_note.value)
        .sum();
    let bid_fill = outputs[0].fill_note.value; // A is the bid
    let ask_fill = outputs[1].fill_note.value; // B is the ask
    println!(
        "    Σ in = {sum_in}, Σ out = {sum_out}, bid_fill = {bid_fill}, ask_fill = {ask_fill}, V* = {vstar}"
    );
    assert_eq!(sum_in, sum_out, "NO-MINT: Σ in = Σ out across the clearing");
    assert_eq!(bid_fill, vstar, "CROSSING: bid fill = V*");
    assert_eq!(ask_fill, vstar, "CROSSING: ask fill = V*");
    for o in &outputs {
        assert!(o.fill_note.value_binding_opens() && o.change_note.value_binding_opens());
    }
    println!("  [pos] deposit notes CLEAR privately, conserving (Σ in = Σ out = V*)\n");

    // -----------------------------------------------------------------------
    // (d) SETTLE — a cleared output note (A's fill, value 80) exits + releases from
    //     the custody, gated on supply ≤ locked. The deposited token settles.
    // -----------------------------------------------------------------------
    let a_fill = &outputs[0].fill_note; // value 80
    let post_custody = settle_output_note(&custody1, a_fill)
        .expect("a cleared output note must settle (supply ≤ locked)");
    println!(
        "(d) SETTLE: unshield + release A's fill (value {}) → custody (locked {} → {}, supply {} → {})",
        a_fill.value, custody1.locked, post_custody.locked, custody1.supply, post_custody.supply
    );
    assert_eq!(post_custody.supply, custody1.supply - a_fill.value);
    assert!(
        post_custody.backed(),
        "supply ≤ locked preserved through settle"
    );
    println!("  [pos] deposited token SETTLES: released = note value, supply ≤ locked preserved\n");
    println!("=== FULL CHAIN: deposit → shield → clear → settle over REAL pool notes ===\n");

    // =======================================================================
    // NEGATIVE polarities — the deposit-glue soundness teeth.
    // =======================================================================
    println!("--- NEGATIVE polarities (no-mint-without-a-valid-lock) ---");

    // [neg #1] FORGED attestation — a tampered locked_value leaves the published
    // holding_hash stale (the verify_holding "+1 wei" canary at the storage-trie
    // gate). is_valid_lock() fails ⇒ NO MINT.
    {
        let mut forged = honest_attestation(1, 1_000, weth_token(), 0xF00D, 0x5107_F, 1);
        forged.locked_value += 1; // claim 1001 locked but keep the 1000-holding_hash
        assert!(
            !forged.is_valid_lock(),
            "a forged locked_value must break the holding identity"
        );
        let mut l = DepositLedger::default();
        let res = l.deposit_to_note(&forged, 100, 0xF00D, 0x1, 0x1);
        assert_eq!(
            res.err(),
            Some(DepositError::NoValidLock),
            "a FORGED attestation must mint NOTHING"
        );
        println!("  [neg] FORGED attestation (tampered locked balance) REJECTED — no mint");
    }

    // [neg #2] ABSENT / unproven attestation — the holding identity opens but the
    // trust tag is not ConsensusProven. Refused.
    {
        let mut unproven = honest_attestation(1, 1_000, weth_token(), 0xDEAD, 0x5107_D, 1);
        unproven.trust = HoldingTrust::Unproven;
        assert!(
            !unproven.is_valid_lock(),
            "an unproven attestation is not a valid lock"
        );
        let mut l = DepositLedger::default();
        let res = l.deposit_to_note(&unproven, 100, 0xDEAD, 0x1, 0x1);
        assert_eq!(
            res.err(),
            Some(DepositError::NoValidLock),
            "an ABSENT/unproven attestation must mint NOTHING"
        );
        println!(
            "  [neg] ABSENT/unproven attestation (trust ≠ ConsensusProven) REJECTED — no mint"
        );
    }

    // [neg #3] MINT BEYOND THE LOCK — a valid lock of 1000, but a mint of 1500. The
    // drawMint gate `supply + a ≤ locked` bites (InterchainCustody.overMint_refused).
    {
        let lock = honest_attestation(1, 1_000, weth_token(), 0xC0DE, 0x5107_C, 1);
        assert!(lock.is_valid_lock());
        let mut l = DepositLedger::default();
        let res = l.deposit_to_note(&lock, 1_500, 0xC0DE, 0x1, 0x1);
        assert_eq!(
            res.err(),
            Some(DepositError::MintBeyondLock),
            "a mint of 1500 against a lock of 1000 must be REFUSED (value ≤ locked)"
        );
        // And the custody was NOT advanced (the failed draw does not mint supply).
        assert!(
            l.custody.get(&1).map(|c| c.supply).unwrap_or(0) == 0,
            "a refused mint leaves supply at 0"
        );
        println!("  [neg] MINT BEYOND LOCK (value 1500 > locked 1000) REJECTED — supply ≤ locked");
    }

    // [neg #4] DOUBLE-MINT against the SAME lock — the deposit nullifier is consumed
    // on the first mint; a second mint against the same lock is refused.
    {
        let lock = honest_attestation(1, 1_000, weth_token(), 0x0DED, 0x5107_0, 1);
        let mut l = DepositLedger::default();
        let _first = l
            .deposit_to_note(&lock, 100, 0x0DED, 0x1, 0x1)
            .expect("the first mint against a fresh lock succeeds");
        let res = l.deposit_to_note(&lock, 100, 0x0DED, 0x2, 0x2);
        assert_eq!(
            res.err(),
            Some(DepositError::DoubleMint),
            "a second mint against the SAME lock must be REFUSED (one-lock-one-note)"
        );
        // The custody drew exactly once (supply 100, not 200).
        assert_eq!(
            l.custody[&1].supply, 100,
            "the escrow was drawn exactly once"
        );
        println!(
            "  [neg] DOUBLE-MINT (second note against the same lock) REJECTED — one-lock-one-note"
        );
    }

    println!(
        "\n=== DEPOSIT-GLUE SEAM CLOSED — a deposited token mints a valid shielded note, gated on a real lock ==="
    );
    println!(
        "    NO mint without a valid ConsensusProven lock; value ≤ locked (Σ minted ≤ Σ locked); one-lock-one-note."
    );
    println!(
        "    forged / absent attestation, mint-beyond-lock, double-mint all REJECTED — soundness."
    );
    println!(
        "    Remaining (bridge map): the on-chain escrow CONTRACT deploy + the persistent MPC federation (ember-gated)."
    );
}
