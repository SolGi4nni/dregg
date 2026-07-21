//! # `dreggnet-asset` — the canonical VERIFIABLE ASSET layer.
//!
//! An **asset** is an OWNED, TRANSFER-GATED, PROVENANCE-CHAINED, cross-cell-ADDRESSED
//! primitive — the thing new genres want (a TCG card, an RPG loot drop, an item-market
//! listing, a betting stake). This crate makes it a real dregg construction over the
//! tooth ISA (`cell/src/program/types.rs`) + the real
//! [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor).
//!
//! ## The shape: a note (UTXO) lineage, so authority genuinely MOVES
//!
//! On this substrate a cell's `AuthRequired::Signature` turns must verify against the
//! **cell's own birth pubkey** (`turn/src/executor/authorize.rs`
//! `verify_ed25519_signature`) — so a cell has exactly ONE authorizing key, fixed at
//! birth. Ownership therefore cannot mutate *inside* a single cell; to move authority we
//! move to a **successor** cell owned by the new holder. An asset is thus a **lineage of
//! note versions**, each version a sovereign cell owned by its current holder:
//!
//! ```text
//!   v0 (owner = minter)  ──transfer──▶  v1 (owner = bob)  ──transfer──▶  v2 (owner = carol)
//!    spent := 1                          spent := 1                        (live / holdable)
//!    prev  = 0 (origin)                  prev  = note_digest(v0)           prev = note_digest(v1)
//!    asset_id ─────────────────────── carried unchanged (WriteOnce) ───────────────────────▶
//! ```
//!
//! * **OWNED** — a version cell is owned by the current holder's key. The executor admits
//!   a transfer turn on it IFF the turn's signature verifies under that key. A forged /
//!   non-owner transfer produces an invalid signature → a real executor refusal. THIS is
//!   the ownership gate — cryptographic, not app bookkeeping.
//! * **TRANSFER-GATED** — a transfer is one real committed, owner-signed turn that SPENDS
//!   the current version (sets its `spent` flag `0 → 1`). The version's program (a
//!   `CellProgram::Cases` `transfer` case) gates the spend with `StrictMonotonic(spent)` +
//!   `FieldEquals(spent, 1)` — so the spend lands exactly once and a **double-spend**
//!   (re-spending an already-spent version) is refused (`1 → 1` is not a strict increase).
//! * **PROVENANCE-CHAINED** — every version carries `prev = note_digest(predecessor)`, a
//!   blake3 content address of the predecessor's immutable identity, plus the carried
//!   `minter` and `asset_id`. The lineage is a hash chain any third party recomputes
//!   ([`verify_desc_chain`]); a single tampered version breaks the recomputation. The live
//!   predecessor cells are *also* re-read to confirm each was really `spent` on-chain
//!   (executor-refereed, not just replayed data).
//! * **cross-cell ADDRESSED** — the [`AssetId`] is a stable content address
//!   (`blake3(minter_pubkey ‖ mint_seed)`), carried `WriteOnce` into every successor and
//!   independent of the (changing) cell ids. It is the handle a market / a second game /
//!   a frontend names the asset by.
//!
//! ## How it uses `dregg-schema`
//!
//! The note's slot layout is a [`dregg_schema::Schema`] of `identity` components
//! (asset_id / minter / owner / prev / serial / **trait_root** / **soulbound**) + one
//! field for the mutable `spent` flag, lowered by the **verified allocator**
//! ([`dregg_schema::allocate_checked`]) to a Legal (disjoint + in-bounds, the
//! `RotatedLayout` discipline) register layout. The
//! *transfer-method* dispatch + the `StrictMonotonic(spent)` double-spend tooth fall
//! outside `emit_program`'s fixed genesis+move shape, so the [`CellProgram`] is
//! hand-rolled over the allocator-resolved slot indices (honest partial reuse: the
//! keystone owns the *layout legality*, this crate owns the *transfer semantics*).
//!
//! ## First-class asset properties (beyond the lineage core)
//!
//! * **`trait_root` (E1 closed)** — a first-class committed 32-byte content root every
//!   version carries `WriteOnce`. A visual/stat layer (the sprite / gear crates)
//!   reads it via [`AssetWorld::trait_root_of`] and draws deterministic traits from the
//!   asset's *committed* identity, instead of re-deriving from the raw [`AssetId`] bytes as
//!   a TCB workaround. [`AssetWorld::mint`] populates it with a deterministic derivation of
//!   the id; [`AssetWorld::mint_with_traits`] commits an explicit root (a stat block digest).
//! * **`soulbound` (first-class non-transferability)** — a committed 0/1 flag. The transfer
//!   case gates on `FieldEquals(soulbound, 0)`, so a note minted via
//!   [`AssetWorld::mint_soulbound`] refuses every transfer turn *at the ISA* — the
//!   cryptographic property an earned-credential layer (the cheevo crate) wants, rather
//!   than re-implementing a no-transfer rule one layer up.
//! * **batch mint** — [`AssetWorld::mint_batch`] mints a collection (a pack, a loot table
//!   drop) in one call.
//! * **revocation** — [`AssetWorld::revoke`] lets a minter burn a *mis-minted* asset while
//!   they still hold the untransferred origin, via a real minter-signed spend (no successor).
//!   A non-owner revoke, or a revoke after the asset was handed off, is refused.
//!
//! ## Honest scope — what is real, what is a named seam
//!
//! REAL: the owned + transfer-gated + provenance-chained + content-addressed asset, plus
//! the committed `trait_root` / `soulbound` properties, batch mint and minter revocation —
//! executor-refereed on every gate (owner-signature, double-spend, forged-owner, soulbound
//! non-transfer, non-owner revoke), driven and asserted in `tests/asset_layer.rs`.
//!
//! Each holder runs its own sovereign [`EmbeddedExecutor`] (ledger) — a note lives in its
//! current holder's ledger and the lineage links across them by content address, exactly
//! the sovereign-note model. NAMED SEAMS (not built here):
//! * a **market / exchange** over the asset — `starbridge-apps/escrow-market` is the
//!   trustless trade primitive; an atomic asset↔value swap binds a transfer here to a
//!   sealed-escrow leg there;
//! * **cross-GAME** use — a second game consumes an [`AssetId`] as a foreign holding
//!   (the address is already game-independent);
//! * a **shared federated ledger** — here provenance binds sovereign ledgers
//!   cryptographically; a single federation replicating the versions is the deployment;
//! * the **frontend** (a wallet / inventory view over a holder's live notes);
//! * **expiry / lease semantics** — a committed expiry needs an ambient temporal clock
//!   (a `TemporalGate`-style ISA gate over a context height) that the sovereign-ledger
//!   `AssetWorld` does not yet carry; a first-class expiry field is the next-resolution
//!   step, deliberately not built this pass (it would be a placeholder clock without it).

use std::collections::HashMap;

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellProgram, Effect, EmbeddedExecutor,
    StateConstraint, TransitionCase, TransitionGuard, TurnReceipt, field_from_u64, symbol,
};
use dregg_cell::Cell;
use dregg_cell::state::FIELD_ZERO;
use dregg_schema::{Schema, Slot, allocate_checked};
use zeroize::Zeroizing;

/// The federation every asset-note turn commits under (identity is carried by the
/// holder key, not the federation).
const ASSET_FEDERATION: [u8; 32] = [0xA5; 32];

/// The dispatch method a transfer (spend) turn presents. Its `CellProgram::Cases` case
/// carries the double-spend teeth; every other method default-denies (a version can ONLY
/// be moved by a transfer).
pub const TRANSFER_METHOD: &str = "asset/transfer";

/// A stable, content-addressed asset identity — the cross-cell / cross-game address.
/// `blake3_derive_key("dreggnet-asset-id-v1") over (minter_pubkey ‖ mint_seed)`. Carried
/// `WriteOnce` into every successor version, independent of the (changing) cell ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct AssetId(pub [u8; 32]);

impl AssetId {
    fn compute(minter_pk: &[u8; 32], mint_seed: &[u8]) -> Self {
        let mut h = blake3::Hasher::new_derive_key("dreggnet-asset-id-v1");
        h.update(minter_pk);
        h.update(mint_seed);
        AssetId(*h.finalize().as_bytes())
    }
    /// The raw 32-byte address.
    pub fn bytes(&self) -> [u8; 32] {
        self.0
    }
}

/// The IMMUTABLE identity of one note version — the data that content-addresses the
/// version (its cell token) and forms the provenance chain. The mutable `spent` flag is
/// NOT part of the digest (it flips during the version's life).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct NoteDesc {
    /// The stable asset id (carried across the whole lineage).
    pub asset_id: [u8; 32],
    /// The original minter's pubkey (the provenance root, carried across the lineage).
    pub minter: [u8; 32],
    /// This version's holder pubkey (the key that authorizes spending it).
    pub owner: [u8; 32],
    /// The predecessor version's [`note_digest`]; [`FIELD_ZERO`] at the origin.
    pub prev: [u8; 32],
    /// The version index (1 at the origin mint, +1 per transfer).
    pub serial: u64,
    /// **The first-class committed trait root (E1).** A 32-byte content commitment the
    /// asset carries `WriteOnce` across its whole lineage — the stable handle a visual /
    /// stat layer (the sprite / gear crates) draws deterministic traits from.
    /// Committed as a real note field (in [`note_digest`] + gated `WriteOnce` in the
    /// program), so a consumer reads it from the asset's committed identity rather than
    /// re-deriving traits from the raw [`AssetId`] bytes as a TCB workaround. A plain
    /// [`AssetWorld::mint`] sets it to a deterministic derivation of the asset id (so the
    /// field is always meaningful); [`AssetWorld::mint_with_traits`] commits an explicit
    /// content root (a stat block's digest, a card's data hash).
    pub trait_root: [u8; 32],
    /// **The first-class soulbound flag.** `1` iff this asset is non-transferable — the
    /// transfer case gates on `FieldEquals(soulbound, 0)`, so a transfer turn on a
    /// soulbound note is refused by the executor at the ISA (not by app bookkeeping one
    /// layer up). Carried `WriteOnce` across the lineage. A soulbound asset stays bound to
    /// its minter/earner forever — the property the cheevo crate wants first-class.
    pub soulbound: u8,
}

/// The content address of a note VERSION — `blake3` over its immutable identity. Used as
/// the version cell's token (so distinct versions are distinct cells) and as the
/// `prev` link a successor carries.
pub fn note_digest(d: &NoteDesc) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dreggnet-asset-note-v1");
    h.update(&d.asset_id);
    h.update(&d.minter);
    h.update(&d.owner);
    h.update(&d.prev);
    h.update(&d.serial.to_le_bytes());
    h.update(&d.trait_root);
    h.update(&[d.soulbound]);
    *h.finalize().as_bytes()
}

/// The default committed [`NoteDesc::trait_root`] for a plainly-minted asset — a
/// deterministic derivation of the asset id, so the first-class field is always populated
/// even when the minter does not supply an explicit content root. A visual/stat layer
/// that reads [`AssetWorld::trait_root_of`] gets this stable value.
pub fn default_trait_root(asset_id: &AssetId) -> [u8; 32] {
    blake3::derive_key("dregg-asset-trait-root-v1", &asset_id.0)
}

/// The allocator-resolved register indices of the note's fields.
#[derive(Clone, Copy, Debug)]
struct Slots {
    asset_id: u8,
    minter: u8,
    owner: u8,
    prev: u8,
    serial: u8,
    trait_root: u8,
    soulbound: u8,
    spent: u8,
}

/// The note component schema — seven write-once identity fields (the five lineage
/// invariants + the first-class `trait_root` and `soulbound` commitments) + the mutable
/// `spent` flag — lowered by the VERIFIED allocator to a Legal register layout.
fn note_schema() -> Schema {
    Schema::new("dreggnet-asset-note")
        .identity("asset_id")
        .identity("minter")
        .identity("owner")
        .identity("prev")
        .identity("serial")
        // E1: the first-class committed trait root (a WriteOnce identity field).
        .identity("trait_root")
        // The first-class soulbound flag (0/1), gated WriteOnce; the transfer case
        // additionally requires it be 0, so a soulbound note refuses transfer at the ISA.
        .identity("soulbound")
        // `spent` is the double-spend flag; `resource` reserves a register slot for it
        // (its transfer-time StrictMonotonic tooth is hand-rolled below, outside the
        // archetype vocabulary).
        .resource("spent")
}

fn resolve_slots() -> Slots {
    let layout = allocate_checked(&note_schema())
        .expect("the note schema is a legal register layout (7 identities + 1 resource)");
    let reg = |name: &str| match layout.resolve(name).expect("component resolves") {
        Slot::Register(r) => r,
        Slot::Heap(_) => panic!("note fields are register-placed"),
    };
    Slots {
        asset_id: reg("asset_id"),
        minter: reg("minter"),
        owner: reg("owner"),
        prev: reg("prev"),
        serial: reg("serial"),
        trait_root: reg("trait_root"),
        soulbound: reg("soulbound"),
        spent: reg("spent"),
    }
}

/// The note version program: a single `transfer`-method case. Its teeth freeze the
/// version's immutable identity (`WriteOnce` on every identity field, including the
/// first-class `trait_root` + `soulbound` commitments) and gate the spend
/// (`StrictMonotonic(spent)` + `FieldEquals(spent, 1)`) so a transfer lands exactly once —
/// a double-spend (`1 → 1`) is refused. The case ALSO requires `FieldEquals(soulbound, 0)`,
/// so a **soulbound** note (`soulbound = 1`) refuses a transfer turn cryptographically at
/// the ISA (the executor evaluates the case constraints and the turn fails). Every
/// non-`transfer` method default-denies (a `Cases` program with a method-dispatching case
/// rejects an unmatched method), so a version can be moved ONLY by a transfer.
fn note_program(s: &Slots) -> CellProgram {
    let transfer = TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(TRANSFER_METHOD),
        },
        constraints: vec![
            StateConstraint::WriteOnce { index: s.asset_id },
            StateConstraint::WriteOnce { index: s.minter },
            StateConstraint::WriteOnce { index: s.owner },
            StateConstraint::WriteOnce { index: s.prev },
            StateConstraint::WriteOnce { index: s.serial },
            StateConstraint::WriteOnce {
                index: s.trait_root,
            },
            StateConstraint::WriteOnce { index: s.soulbound },
            // SOULBOUND GATE: a note minted soulbound (soulbound = 1) can never satisfy
            // this, so its transfer turn is refused by the executor — non-transferability
            // is a first-class ISA property, not app bookkeeping one layer up.
            StateConstraint::FieldEquals {
                index: s.soulbound,
                value: field_from_u64(0),
            },
            // 0 → 1 once; a re-spend (1 → 1) is not a strict increase → refused.
            StateConstraint::StrictMonotonic { index: s.spent },
            // the transfer must actually mark the version spent.
            StateConstraint::FieldEquals {
                index: s.spent,
                value: field_from_u64(1),
            },
        ],
    };
    CellProgram::Cases(vec![transfer])
}

/// A holder identity + its sovereign ledger (a real [`EmbeddedExecutor`]). Deterministic
/// in the label, so re-deriving a holder reproduces its key.
struct Holder {
    cclerk: AppCipherclerk,
    exec: EmbeddedExecutor,
}

impl Holder {
    fn new(label: &str) -> Self {
        let key = blake3::derive_key("dreggnet-asset-holder-v1", label.as_bytes());
        let cclerk = AppCipherclerk::new(
            AgentCipherclerk::from_key_bytes(Zeroizing::new(key)),
            ASSET_FEDERATION,
        );
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        Holder { cclerk, exec }
    }

    fn pubkey(&self) -> [u8; 32] {
        self.cclerk.public_key().0
    }

    /// Mint a note version cell into THIS holder's ledger, owned by this holder's key,
    /// seeded from `desc` (setup writes, not a turn — mirrors how flagship apps seed cell
    /// config before play). Returns the version cell id (content-addressed to `desc`).
    fn install_note(&self, desc: &NoteDesc, slots: &Slots, program: &CellProgram) -> CellId {
        debug_assert_eq!(
            desc.owner,
            self.pubkey(),
            "a note is minted by its own owner"
        );
        let owner = self.pubkey();
        let token = note_digest(desc);
        let cell = CellId::derive_raw(&owner, &token);
        let agent = self.cclerk.cell_id();
        self.exec.with_ledger_mut(|ledger| {
            if ledger.get(&cell).is_none() {
                let _ = ledger.insert_cell(Cell::new(owner, token));
            }
            if let Some(agent_cell) = ledger.get_mut(&agent) {
                agent_cell.capabilities.grant(cell, AuthRequired::Signature);
            }
        });
        self.exec.install_program(cell, program.clone());
        self.exec.with_ledger_mut(|ledger| {
            if let Some(c) = ledger.get_mut(&cell) {
                c.state.set_field(slots.asset_id as usize, desc.asset_id);
                c.state.set_field(slots.minter as usize, desc.minter);
                c.state.set_field(slots.owner as usize, desc.owner);
                c.state.set_field(slots.prev as usize, desc.prev);
                c.state
                    .set_field(slots.serial as usize, field_from_u64(desc.serial));
                c.state
                    .set_field(slots.trait_root as usize, desc.trait_root);
                c.state.set_field(
                    slots.soulbound as usize,
                    field_from_u64(desc.soulbound as u64),
                );
                // `spent` defaults to FIELD_ZERO (0) — the version starts unspent.
            }
        });
        cell
    }

    /// Read a version cell's committed `spent` flag (true once it has been transferred).
    fn is_spent(&self, cell: CellId, slots: &Slots) -> bool {
        self.exec
            .cell_state(cell)
            .map(|s| s.fields[slots.spent as usize] != FIELD_ZERO)
            .unwrap_or(false)
    }
}

/// One committed version in an asset's lineage: which holder's ledger it lives in, its
/// cell id, and its immutable descriptor.
#[derive(Clone)]
struct Version {
    holder: String,
    cell: CellId,
    desc: NoteDesc,
}

/// Why an asset operation could not complete.
#[derive(Clone, Debug)]
pub enum AssetError {
    /// The real executor refused the transfer turn — a forged / non-owner signature, a
    /// double-spend, or an otherwise-inadmissible move. The receipt-why is carried.
    Refused(String),
    /// No asset with this id has been minted in this world.
    UnknownAsset,
}

impl std::fmt::Display for AssetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AssetError::Refused(r) => write!(f, "asset turn refused: {r}"),
            AssetError::UnknownAsset => write!(f, "unknown asset id"),
        }
    }
}

impl std::error::Error for AssetError {}

/// The receipt of a completed transfer: the committed spend turn on the predecessor plus
/// the newly-minted successor version's identity.
#[derive(Clone, Debug)]
pub struct TransferReceipt {
    /// The real committed turn that spent the predecessor version.
    pub spend: TurnReceipt,
    /// The new holder's pubkey.
    pub new_owner: [u8; 32],
    /// The successor version's serial (= predecessor serial + 1).
    pub serial: u64,
}

/// The verdict of re-verifying an asset's provenance chain by replay + on-chain re-read.
#[derive(Clone, Debug)]
pub struct ProvenanceReport {
    /// Whether the whole lineage verifies (content-addressed links + on-chain spent
    /// re-reads).
    pub verified: bool,
    /// The number of versions in the lineage (mint = 1, then +1 per transfer).
    pub length: usize,
    /// The current holder's pubkey (the tail version's owner).
    pub current_owner: [u8; 32],
    /// Whether this asset was revoked (burned by its minter). A revoked lineage verifies
    /// iff its content-address chain re-derives AND every version — including the tail — is
    /// spent on-chain (the burn genuinely happened).
    pub revoked: bool,
    /// Per-failure reasons (empty on a clean verify).
    pub reasons: Vec<String>,
}

/// Why a descriptor chain failed the pure content-address re-derivation ([`verify_desc_chain`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProvenanceBreak {
    /// The chain is empty.
    Empty,
    /// The asset id does not match the origin's declared asset id.
    AssetIdMismatch,
    /// The origin is malformed (prev != 0, owner != minter, or serial != 1).
    BadOrigin { reason: &'static str },
    /// Version `index`'s `prev` is not the content address of its predecessor.
    BrokenLink { index: usize },
    /// Version `index` does not carry the origin's asset id / minter, or its serial is
    /// not predecessor + 1.
    Inconsistent { index: usize, reason: &'static str },
}

/// **Re-derive a descriptor chain, content-address link by content-address link** — the
/// PURE provenance check anyone can run over the published descriptors alone (no
/// executor). A single tampered version (a swapped owner, a rewritten asset id, a forged
/// `prev`) breaks the recomputation. The origin must be a genuine mint (owner = minter,
/// prev = 0, serial = 1) under `asset_id`; each successor must link to its predecessor's
/// [`note_digest`], carry the origin's asset id + minter, and increment the serial.
pub fn verify_desc_chain(descs: &[NoteDesc], asset_id: AssetId) -> Result<(), ProvenanceBreak> {
    let origin = descs.first().ok_or(ProvenanceBreak::Empty)?;
    if origin.asset_id != asset_id.0 {
        return Err(ProvenanceBreak::AssetIdMismatch);
    }
    if origin.prev != FIELD_ZERO {
        return Err(ProvenanceBreak::BadOrigin {
            reason: "origin prev is not zero",
        });
    }
    if origin.owner != origin.minter {
        return Err(ProvenanceBreak::BadOrigin {
            reason: "origin owner is not the minter",
        });
    }
    if origin.serial != 1 {
        return Err(ProvenanceBreak::BadOrigin {
            reason: "origin serial is not 1",
        });
    }
    for i in 1..descs.len() {
        let prev = &descs[i - 1];
        let cur = &descs[i];
        if cur.prev != note_digest(prev) {
            return Err(ProvenanceBreak::BrokenLink { index: i });
        }
        if cur.asset_id != origin.asset_id {
            return Err(ProvenanceBreak::Inconsistent {
                index: i,
                reason: "asset id not carried",
            });
        }
        if cur.minter != origin.minter {
            return Err(ProvenanceBreak::Inconsistent {
                index: i,
                reason: "minter not carried",
            });
        }
        if cur.trait_root != origin.trait_root {
            return Err(ProvenanceBreak::Inconsistent {
                index: i,
                reason: "trait_root not carried",
            });
        }
        if cur.soulbound != origin.soulbound {
            return Err(ProvenanceBreak::Inconsistent {
                index: i,
                reason: "soulbound flag not carried",
            });
        }
        if cur.serial != prev.serial + 1 {
            return Err(ProvenanceBreak::Inconsistent {
                index: i,
                reason: "serial did not increment by one",
            });
        }
    }
    Ok(())
}

/// **The verifiable asset world** — the mint / transfer / verify surface over a set of
/// sovereign holder ledgers. Every gate is executor-refereed: a transfer is a real
/// owner-signed turn, a non-owner / double-spend is a real refusal, and provenance
/// re-verification re-reads the live cells' spent flags.
pub struct AssetWorld {
    slots: Slots,
    program: CellProgram,
    holders: HashMap<String, Holder>,
    lineages: HashMap<[u8; 32], Vec<Version>>,
    /// Assets the minter has revoked (burned while still holding the untransferred origin).
    /// A revoked asset has no live holder and refuses transfer.
    revoked: std::collections::HashSet<[u8; 32]>,
}

impl Default for AssetWorld {
    fn default() -> Self {
        Self::new()
    }
}

impl AssetWorld {
    /// A fresh asset world (no holders, no assets). The note layout is allocated + Legal-
    /// checked once here (the verified allocator keystone).
    pub fn new() -> Self {
        let slots = resolve_slots();
        let program = note_program(&slots);
        AssetWorld {
            slots,
            program,
            holders: HashMap::new(),
            lineages: HashMap::new(),
            revoked: std::collections::HashSet::new(),
        }
    }

    /// Build an executor-independent staging image of this asset world.
    ///
    /// The clone reproduces every note descriptor, live/spent bit, holder
    /// identity, lineage, and revocation in fresh embedded executors. It is
    /// intentionally a *state* clone rather than a receipt-history clone: prior
    /// per-holder receipt chains are not copied, while every subsequently staged
    /// transfer produces a new real executor receipt in the detached image.
    /// This is the process-local transaction substrate used by composed market
    /// settlement; dropping the image cannot mutate the source world.
    pub fn detached_state_clone(&self) -> Self {
        let mut staged = Self::new();
        for label in self.holders.keys() {
            staged.ensure_holder(label);
        }
        staged.revoked = self.revoked.clone();
        for (asset, versions) in &self.lineages {
            let mut staged_versions = Vec::with_capacity(versions.len());
            for version in versions {
                staged.ensure_holder(&version.holder);
                let cell = staged.holders[&version.holder].install_note(
                    &version.desc,
                    &staged.slots,
                    &staged.program,
                );
                debug_assert_eq!(cell, version.cell);
                if self.holders[&version.holder].is_spent(version.cell, &self.slots) {
                    staged.holders[&version.holder]
                        .exec
                        .with_ledger_mut(|ledger| {
                            ledger
                                .get_mut(&cell)
                                .expect("the detached note was installed")
                                .state
                                .set_field(staged.slots.spent as usize, field_from_u64(1));
                        });
                }
                staged_versions.push(version.clone());
            }
            staged.lineages.insert(*asset, staged_versions);
        }
        staged
    }

    /// Canonical process-local audit digest of every economically relevant
    /// asset-world state item. HashMap iteration is sorted before hashing.
    pub fn state_audit_digest(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dreggnet-asset/state-audit/v1");
        let mut holders = self.holders.keys().collect::<Vec<_>>();
        holders.sort();
        hasher.update(&(holders.len() as u64).to_be_bytes());
        for label in holders {
            hasher.update(&(label.len() as u64).to_be_bytes());
            hasher.update(label.as_bytes());
            hasher.update(&self.holders[label].pubkey());
        }
        let mut assets = self.lineages.iter().collect::<Vec<_>>();
        assets.sort_by_key(|(asset, _)| **asset);
        hasher.update(&(assets.len() as u64).to_be_bytes());
        for (asset, versions) in assets {
            hasher.update(asset);
            hasher.update(&(versions.len() as u64).to_be_bytes());
            for version in versions {
                hasher.update(&(version.holder.len() as u64).to_be_bytes());
                hasher.update(version.holder.as_bytes());
                hasher.update(version.cell.as_bytes());
                hasher.update(&version.desc.asset_id);
                hasher.update(&version.desc.minter);
                hasher.update(&version.desc.owner);
                hasher.update(&version.desc.prev);
                hasher.update(&version.desc.serial.to_be_bytes());
                hasher.update(&version.desc.trait_root);
                hasher.update(&[version.desc.soulbound]);
                hasher.update(&[
                    self.holders[&version.holder].is_spent(version.cell, &self.slots) as u8,
                ]);
            }
            hasher.update(&[self.revoked.contains(asset) as u8]);
        }
        *hasher.finalize().as_bytes()
    }

    fn ensure_holder(&mut self, label: &str) {
        self.holders
            .entry(label.to_string())
            .or_insert_with(|| Holder::new(label));
    }

    /// The deterministic pubkey of `label` (creating the holder identity if new).
    pub fn pubkey_of(&mut self, label: &str) -> [u8; 32] {
        self.ensure_holder(label);
        self.holders[label].pubkey()
    }

    /// **MINT an asset**, owned by `minter_label`. The origin version (serial 1, prev 0,
    /// owner = minter) is a note cell in the minter's ledger. The committed
    /// [`NoteDesc::trait_root`] is a deterministic derivation of the asset id
    /// ([`default_trait_root`]) and the asset is transferable (`soulbound = 0`). Returns the
    /// stable, content-addressed [`AssetId`] — the cross-cell address every later transfer
    /// carries.
    pub fn mint(&mut self, minter_label: &str, mint_seed: &[u8]) -> AssetId {
        let asset_id = self.peek_asset_id(minter_label, mint_seed);
        let trait_root = default_trait_root(&asset_id);
        self.mint_inner(minter_label, mint_seed, trait_root, false)
    }

    /// **MINT an asset with an explicit committed trait root (E1).** Identical to
    /// [`Self::mint`] but commits `trait_root` as the asset's first-class
    /// [`NoteDesc::trait_root`] — the content root a stat/visual layer binds to (e.g.
    /// the gear crate commits a `StatBlock`'s digest, so the item's stats are bound to the
    /// asset's committed identity, not re-derived from raw address bytes). The root is
    /// carried `WriteOnce` across the whole lineage.
    pub fn mint_with_traits(
        &mut self,
        minter_label: &str,
        mint_seed: &[u8],
        trait_root: [u8; 32],
    ) -> AssetId {
        self.mint_inner(minter_label, mint_seed, trait_root, false)
    }

    /// **MINT a soulbound (non-transferable) asset**, owned by `minter_label`. The note is
    /// minted with `soulbound = 1`; the transfer case gates on `FieldEquals(soulbound, 0)`,
    /// so any transfer turn on it is refused by the executor at the ISA. This is the
    /// first-class non-transferability an earned-credential layer (the cheevo crate) wants
    /// — it stays bound to its minter/earner forever, enforced cryptographically rather than
    /// re-implemented one layer up.
    pub fn mint_soulbound(&mut self, minter_label: &str, mint_seed: &[u8]) -> AssetId {
        let asset_id = self.peek_asset_id(minter_label, mint_seed);
        let trait_root = default_trait_root(&asset_id);
        self.mint_inner(minter_label, mint_seed, trait_root, true)
    }

    /// **MINT a soulbound asset with an explicit committed trait root** — the union of
    /// [`Self::mint_soulbound`] and [`Self::mint_with_traits`].
    pub fn mint_soulbound_with_traits(
        &mut self,
        minter_label: &str,
        mint_seed: &[u8],
        trait_root: [u8; 32],
    ) -> AssetId {
        self.mint_inner(minter_label, mint_seed, trait_root, true)
    }

    /// **BATCH-MINT a collection**, all owned by `minter_label`, one asset per seed. Each is
    /// an independent origin note (no shared lineage); the returned ids are in seed order.
    /// A convenience over repeated [`Self::mint`] for a pack / a set / a loot table drop.
    pub fn mint_batch(&mut self, minter_label: &str, seeds: &[&[u8]]) -> Vec<AssetId> {
        seeds.iter().map(|s| self.mint(minter_label, s)).collect()
    }

    /// The asset id a mint of `(minter_label, mint_seed)` would produce (ensuring the holder
    /// identity exists), without minting. Used internally to derive the default trait root.
    fn peek_asset_id(&mut self, minter_label: &str, mint_seed: &[u8]) -> AssetId {
        self.ensure_holder(minter_label);
        AssetId::compute(&self.holders[minter_label].pubkey(), mint_seed)
    }

    /// The shared mint tail: install the origin note carrying `trait_root` + `soulbound`.
    fn mint_inner(
        &mut self,
        minter_label: &str,
        mint_seed: &[u8],
        trait_root: [u8; 32],
        soulbound: bool,
    ) -> AssetId {
        self.ensure_holder(minter_label);
        let pk = self.holders[minter_label].pubkey();
        let asset_id = AssetId::compute(&pk, mint_seed);
        let desc = NoteDesc {
            asset_id: asset_id.0,
            minter: pk,
            owner: pk,
            prev: FIELD_ZERO,
            serial: 1,
            trait_root,
            soulbound: soulbound as u8,
        };
        let cell = self.holders[minter_label].install_note(&desc, &self.slots, &self.program);
        self.lineages.entry(asset_id.0).or_default().push(Version {
            holder: minter_label.to_string(),
            cell,
            desc,
        });
        asset_id
    }

    /// **TRANSFER an asset** from `from_label` to `to_label`. Drives a real, owner-signed
    /// spend turn on the current (tail) version — the executor admits it IFF the turn's
    /// signature verifies under the tail version's owner key, so a `from` that is NOT the
    /// current owner is a real [`AssetError::Refused`] (a forged owner) and a re-transfer
    /// of an already-spent version is refused (double-spend). On the committed spend a
    /// successor version owned by `to` is minted, carrying the content-addressed provenance
    /// link + the stable asset id.
    pub fn transfer(
        &mut self,
        asset_id: AssetId,
        from_label: &str,
        to_label: &str,
    ) -> Result<TransferReceipt, AssetError> {
        if !self.lineages.contains_key(&asset_id.0) {
            return Err(AssetError::UnknownAsset);
        }
        if self.revoked.contains(&asset_id.0) {
            // The origin is already spent (burned); the executor would also refuse the
            // double-spend. Report the specific reason.
            return Err(AssetError::Refused("asset was revoked".to_string()));
        }
        self.ensure_holder(from_label);
        self.ensure_holder(to_label);
        let tail = self.lineages[&asset_id.0]
            .last()
            .expect("a minted asset has at least the origin version")
            .clone();

        // The spend action is signed by `from` (its key). It is submitted through the
        // note's OWN ledger (the tail owner's executor) as the turn envelope, so the
        // refusal, when `from` is not the owner, is precisely the signature-vs-cell-pubkey
        // ownership gate.
        let effects = vec![Effect::SetField {
            cell: tail.cell,
            index: self.slots.spent as u64,
            value: field_from_u64(1),
        }];
        let action =
            self.holders[from_label]
                .cclerk
                .make_action(tail.cell, TRANSFER_METHOD, effects);
        let tail_holder = &self.holders[&tail.holder];
        let spend = tail_holder
            .exec
            .submit_action(&tail_holder.cclerk, action)
            .map_err(|e| AssetError::Refused(e.to_string()))?;

        // The spend committed → mint the successor version owned by `to`.
        let to_pk = self.holders[to_label].pubkey();
        let ndesc = NoteDesc {
            asset_id: asset_id.0,
            minter: tail.desc.minter,
            owner: to_pk,
            prev: note_digest(&tail.desc),
            serial: tail.desc.serial + 1,
            // The first-class commitments ride the lineage unchanged (WriteOnce-gated).
            trait_root: tail.desc.trait_root,
            soulbound: tail.desc.soulbound,
        };
        let ncell = self.holders[to_label].install_note(&ndesc, &self.slots, &self.program);
        self.lineages
            .get_mut(&asset_id.0)
            .expect("lineage exists")
            .push(Version {
                holder: to_label.to_string(),
                cell: ncell,
                desc: ndesc,
            });

        Ok(TransferReceipt {
            spend,
            new_owner: to_pk,
            serial: ndesc.serial,
        })
    }

    /// **Attempt to re-spend a specific version** (an adversarial double-spend probe): the
    /// version's own holder signs a fresh spend on it. If the version is already spent the
    /// `StrictMonotonic(spent)` tooth refuses it (`1 → 1`). `version_index` is the position
    /// in the lineage (0 = the origin). Returns `Ok` only if the spend commits.
    pub fn attempt_respend(
        &self,
        asset_id: AssetId,
        version_index: usize,
    ) -> Result<TurnReceipt, AssetError> {
        let chain = self
            .lineages
            .get(&asset_id.0)
            .ok_or(AssetError::UnknownAsset)?;
        let v = chain.get(version_index).ok_or(AssetError::UnknownAsset)?;
        let holder = &self.holders[&v.holder];
        let effects = vec![Effect::SetField {
            cell: v.cell,
            index: self.slots.spent as u64,
            value: field_from_u64(1),
        }];
        let action = holder.cclerk.make_action(v.cell, TRANSFER_METHOD, effects);
        holder
            .exec
            .submit_action(&holder.cclerk, action)
            .map_err(|e| AssetError::Refused(e.to_string()))
    }

    /// The current holder's pubkey for `asset_id` (the tail version's owner), or `None` if
    /// the asset was revoked (burned by its minter).
    pub fn current_owner(&self, asset_id: AssetId) -> Option<[u8; 32]> {
        if self.revoked.contains(&asset_id.0) {
            return None;
        }
        self.lineages
            .get(&asset_id.0)
            .and_then(|c| c.last())
            .map(|v| v.desc.owner)
    }

    /// The committed first-class trait root ([`NoteDesc::trait_root`]) of `asset_id` — the
    /// content commitment a visual/stat layer draws from. Carried unchanged across the
    /// lineage, so any version's root serves; read from the origin. `None` for an unknown
    /// asset. **This is the E1 accessor**: a consumer reads the asset's *committed* trait
    /// root here instead of re-deriving traits from raw [`AssetId`] bytes.
    pub fn trait_root_of(&self, asset_id: AssetId) -> Option<[u8; 32]> {
        self.lineages
            .get(&asset_id.0)
            .and_then(|c| c.first())
            .map(|v| v.desc.trait_root)
    }

    /// Whether `asset_id` was minted soulbound (non-transferable). A soulbound asset refuses
    /// every transfer turn at the ISA (`FieldEquals(soulbound, 0)` in the transfer case).
    pub fn is_soulbound(&self, asset_id: AssetId) -> bool {
        self.lineages
            .get(&asset_id.0)
            .and_then(|c| c.first())
            .map(|v| v.desc.soulbound != 0)
            .unwrap_or(false)
    }

    /// Whether `asset_id` was revoked (burned by its minter).
    pub fn is_revoked(&self, asset_id: AssetId) -> bool {
        self.revoked.contains(&asset_id.0)
    }

    /// **REVOKE a mis-minted asset** — the minter burns it while they still hold the
    /// untransferred origin. Drives a real, minter-signed spend turn on the origin version
    /// (marking it `spent`) but mints NO successor: the asset is gone. This is gated exactly
    /// like a transfer — the minter must be the *current owner* (i.e. the asset has not been
    /// handed off), so the executor refuses a revoke by a non-owner, and a revoke after a
    /// transfer is impossible (the origin is already spent → the executor refuses the
    /// double-spend). A soulbound asset can still be revoked by its minter (revocation is
    /// the minter's own burn, not a transfer of authority away).
    pub fn revoke(
        &mut self,
        asset_id: AssetId,
        minter_label: &str,
    ) -> Result<TurnReceipt, AssetError> {
        let chain = self
            .lineages
            .get(&asset_id.0)
            .ok_or(AssetError::UnknownAsset)?;
        let tail = chain
            .last()
            .expect("a minted asset has at least the origin version")
            .clone();
        self.ensure_holder(minter_label);
        let revoker_pk = self.holders[minter_label].pubkey();
        // Only the minter, and only while they still hold the untransferred asset, may
        // revoke. (If it has been transferred, the origin is spent and revoker_pk is not the
        // tail owner anyway; the executor would refuse. This guard gives a clear reason.)
        if tail.desc.minter != revoker_pk || tail.desc.owner != revoker_pk {
            return Err(AssetError::Refused(
                "only the minter, while still holding the untransferred asset, may revoke it"
                    .to_string(),
            ));
        }
        // The real gated burn: a minter-signed spend on the origin, no successor.
        let effects = vec![Effect::SetField {
            cell: tail.cell,
            index: self.slots.spent as u64,
            value: field_from_u64(1),
        }];
        let action =
            self.holders[minter_label]
                .cclerk
                .make_action(tail.cell, TRANSFER_METHOD, effects);
        let holder = &self.holders[&tail.holder];
        let receipt = holder
            .exec
            .submit_action(&holder.cclerk, action)
            .map_err(|e| AssetError::Refused(e.to_string()))?;
        self.revoked.insert(asset_id.0);
        Ok(receipt)
    }

    /// The current holder's label for `asset_id`.
    pub fn current_holder_label(&self, asset_id: AssetId) -> Option<&str> {
        self.lineages
            .get(&asset_id.0)
            .and_then(|c| c.last())
            .map(|v| v.holder.as_str())
    }

    /// The number of versions in `asset_id`'s lineage (1 after mint, +1 per transfer).
    pub fn lineage_len(&self, asset_id: AssetId) -> usize {
        self.lineages.get(&asset_id.0).map(|c| c.len()).unwrap_or(0)
    }

    /// The published immutable descriptors of `asset_id`'s lineage — the input to the pure
    /// [`verify_desc_chain`] re-derivation.
    pub fn provenance_descs(&self, asset_id: AssetId) -> Vec<NoteDesc> {
        self.lineages
            .get(&asset_id.0)
            .map(|c| c.iter().map(|v| v.desc).collect())
            .unwrap_or_default()
    }

    /// **Re-verify an asset's provenance chain** — the content-addressed hash-chain
    /// re-derivation ([`verify_desc_chain`]) PLUS an on-chain re-read that every
    /// non-tail version's cell is really `spent` (the transfer genuinely happened) and the
    /// tail version is still live. Executor-refereed, not just replayed data. For a REVOKED
    /// asset the tail expectation flips: the tail must be spent too (the minter's burn
    /// genuinely happened), so a clean revocation still verifies.
    pub fn verify_provenance(&self, asset_id: AssetId) -> ProvenanceReport {
        let revoked = self.revoked.contains(&asset_id.0);
        let chain = match self.lineages.get(&asset_id.0) {
            Some(c) if !c.is_empty() => c,
            _ => {
                return ProvenanceReport {
                    verified: false,
                    length: 0,
                    current_owner: [0u8; 32],
                    revoked,
                    reasons: vec!["no such asset".to_string()],
                };
            }
        };
        let mut reasons = Vec::new();

        let descs: Vec<NoteDesc> = chain.iter().map(|v| v.desc).collect();
        if let Err(b) = verify_desc_chain(&descs, asset_id) {
            reasons.push(format!("descriptor chain broke: {b:?}"));
        }

        // Every non-tail version must be SPENT on-chain; the tail must be live (or, for a
        // revoked asset, spent — the burn). And each live cell's id must be the content
        // address of its descriptor (binds the live cell to the replayed identity).
        for (i, v) in chain.iter().enumerate() {
            let holder = &self.holders[&v.holder];
            let expected_cell = CellId::derive_raw(&v.desc.owner, &note_digest(&v.desc));
            if expected_cell != v.cell {
                reasons.push(format!("version {i} cell id is not its content address"));
            }
            let spent = holder.is_spent(v.cell, &self.slots);
            let is_tail = i + 1 == chain.len();
            if is_tail {
                if revoked && !spent {
                    reasons.push(format!(
                        "version {i} is the revoked tail but was never burned on-chain"
                    ));
                }
                if !revoked && spent {
                    reasons.push(format!("tail version {i} is spent (asset is gone)"));
                }
            } else if !spent {
                reasons.push(format!(
                    "version {i} was never spent on-chain (transfer not real)"
                ));
            }
        }

        ProvenanceReport {
            verified: reasons.is_empty(),
            length: chain.len(),
            current_owner: chain.last().map(|v| v.desc.owner).unwrap_or([0u8; 32]),
            revoked,
            reasons,
        }
    }
}

#[cfg(test)]
mod unit {
    //! Unit teeth for the pure surface (content addresses + the descriptor re-derivation).
    //! The executor-driven gates live in `tests/asset_layer.rs`.
    use super::*;

    fn origin(asset_id: [u8; 32], minter: [u8; 32]) -> NoteDesc {
        NoteDesc {
            asset_id,
            minter,
            owner: minter,
            prev: FIELD_ZERO,
            serial: 1,
            trait_root: [0x11; 32],
            soulbound: 0,
        }
    }

    #[test]
    fn asset_id_is_deterministic_and_seed_minter_sensitive() {
        let a = AssetId::compute(&[1u8; 32], b"seed");
        let a2 = AssetId::compute(&[1u8; 32], b"seed");
        assert_eq!(a, a2, "same (minter, seed) ⇒ same id");
        assert_ne!(a, AssetId::compute(&[1u8; 32], b"other-seed"));
        assert_ne!(a, AssetId::compute(&[2u8; 32], b"seed"));
    }

    #[test]
    fn note_digest_depends_on_every_immutable_field() {
        let d = origin([7u8; 32], [9u8; 32]);
        let base = note_digest(&d);
        // Every immutable field is in the digest — flipping any one changes the address.
        let mut mutations: Vec<NoteDesc> = Vec::new();
        let mut m = d;
        m.asset_id = [8u8; 32];
        mutations.push(m);
        let mut m = d;
        m.minter = [8u8; 32];
        mutations.push(m);
        let mut m = d;
        m.owner = [8u8; 32];
        mutations.push(m);
        let mut m = d;
        m.prev = [8u8; 32];
        mutations.push(m);
        let mut m = d;
        m.serial = 2;
        mutations.push(m);
        let mut m = d;
        m.trait_root = [0x22; 32];
        mutations.push(m);
        let mut m = d;
        m.soulbound = 1;
        mutations.push(m);
        for m in mutations {
            assert_ne!(
                note_digest(&m),
                base,
                "a changed immutable field must change the content address"
            );
        }
    }

    #[test]
    fn default_trait_root_is_deterministic_in_the_asset_id() {
        let id = AssetId::compute(&[3u8; 32], b"x");
        assert_eq!(default_trait_root(&id), default_trait_root(&id));
        let id2 = AssetId::compute(&[3u8; 32], b"y");
        assert_ne!(default_trait_root(&id), default_trait_root(&id2));
    }

    #[test]
    fn verify_desc_chain_accepts_a_clean_two_link_chain() {
        let aid = AssetId([5u8; 32]);
        let o = origin(aid.0, [1u8; 32]);
        let v1 = NoteDesc {
            asset_id: aid.0,
            minter: o.minter,
            owner: [2u8; 32],
            prev: note_digest(&o),
            serial: 2,
            trait_root: o.trait_root,
            soulbound: o.soulbound,
        };
        assert!(verify_desc_chain(&[o, v1], aid).is_ok());
    }

    #[test]
    fn verify_desc_chain_rejects_an_uncarried_trait_root() {
        let aid = AssetId([5u8; 32]);
        let o = origin(aid.0, [1u8; 32]);
        let mut v1 = NoteDesc {
            asset_id: aid.0,
            minter: o.minter,
            owner: [2u8; 32],
            prev: note_digest(&o),
            serial: 2,
            trait_root: o.trait_root,
            soulbound: o.soulbound,
        };
        // A successor that recomputes prev but rewrites the committed trait root is caught.
        v1.trait_root = [0xFF; 32];
        v1.prev = note_digest(&o);
        assert_eq!(
            verify_desc_chain(&[o, v1], aid),
            Err(ProvenanceBreak::Inconsistent {
                index: 1,
                reason: "trait_root not carried",
            })
        );
    }

    #[test]
    fn verify_desc_chain_rejects_an_uncarried_soulbound_flag() {
        let aid = AssetId([6u8; 32]);
        let o = origin(aid.0, [1u8; 32]);
        let v1 = NoteDesc {
            asset_id: aid.0,
            minter: o.minter,
            owner: [2u8; 32],
            prev: note_digest(&o),
            serial: 2,
            trait_root: o.trait_root,
            soulbound: 1, // origin was 0
        };
        assert_eq!(
            verify_desc_chain(&[o, v1], aid),
            Err(ProvenanceBreak::Inconsistent {
                index: 1,
                reason: "soulbound flag not carried",
            })
        );
    }

    #[test]
    fn verify_desc_chain_empty_and_asset_id_mismatch() {
        assert_eq!(
            verify_desc_chain(&[], AssetId([0; 32])),
            Err(ProvenanceBreak::Empty)
        );
        let o = origin([1u8; 32], [2u8; 32]);
        assert_eq!(
            verify_desc_chain(&[o], AssetId([9u8; 32])),
            Err(ProvenanceBreak::AssetIdMismatch)
        );
    }

    #[test]
    fn note_schema_is_a_legal_layout_with_distinct_slots() {
        let s = resolve_slots();
        let all = [
            s.asset_id,
            s.minter,
            s.owner,
            s.prev,
            s.serial,
            s.trait_root,
            s.soulbound,
            s.spent,
        ];
        for i in 0..all.len() {
            for j in (i + 1)..all.len() {
                assert_ne!(all[i], all[j], "the allocator gives disjoint slots");
            }
        }
    }
}
