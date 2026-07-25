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
//! * **burn / revocation (the sink)** — a note is DESTROYED by a real owner-signed spend
//!   under [`BURN_METHOD`] that mints no successor. [`AssetWorld::burn`] is the general
//!   **owner-gated** sink (the *current holder* burns, whoever minted it) — what a crafting
//!   sink needs so a material a player *bought* can be consumed; [`AssetWorld::revoke`] is
//!   the narrower minter's-mis-mint door (minter must still hold the untransferred origin).
//!   The burn case deliberately omits the transfer case's `FieldEquals(soulbound, 0)`: a burn
//!   moves authority to nobody, so a soulbound credential stays non-transferable forever yet
//!   its holder can still destroy it.
//! * **inventory** — [`AssetWorld::assets_held_by`] lists a holder's live notes (the
//!   wallet/bench read), [`AssetWorld::all_assets`] the whole census.
//!
//! ## Honest scope — what is real, what is a named seam
//!
//! REAL: the owned + transfer-gated + provenance-chained + content-addressed asset, plus
//! the committed `trait_root` / `soulbound` properties, batch mint, the owner-gated burn and
//! minter revocation — executor-refereed on every gate (owner-signature, double-spend,
//! forged-owner, soulbound non-transfer, non-owner burn, non-minter revoke), driven and
//! asserted in `tests/asset_layer.rs`.
//!
//! Mint is **content-addressed, so it is idempotent, not a fresh-object factory**: the same
//! `(minter, seed)` names the same asset. [`AssetWorld::mint`] returns the existing id
//! unchanged on a repeat; [`AssetWorld::try_mint`] refuses with [`AssetError::DuplicateMint`]
//! for callers that must know they minted something new. (Before this, a repeat silently
//! appended a second bogus origin to the live lineage and broke its re-derivation.)
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
/// be moved by a transfer or a [`BURN_METHOD`] burn).
pub const TRANSFER_METHOD: &str = "asset/transfer";

/// The dispatch method a **burn** (destroy, no successor) turn presents. Its case carries
/// the same identity-freeze + `StrictMonotonic(spent)` double-spend teeth as a transfer,
/// but does NOT require `soulbound == 0`: a burn destroys the note rather than moving
/// authority to another key, so a **soulbound** asset is burnable by its holder while
/// remaining non-transferable forever. (Before this case existed, the transfer case's
/// `FieldEquals(soulbound, 0)` made [`AssetWorld::revoke`] of a soulbound asset a real
/// executor refusal even though the API doc claimed otherwise —
/// `burn_and_revoke_of_a_soulbound_asset_is_admitted` is the driven tooth.)
pub const BURN_METHOD: &str = "asset/burn";

/// A stable, content-addressed asset identity — the cross-cell / cross-game address.
/// `blake3_derive_key("dreggnet-asset-id-v1") over (minter_pubkey ‖ mint_seed)`. Carried
/// `WriteOnce` into every successor version, independent of the (changing) cell ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct AssetId(pub [u8; 32]);

impl AssetId {
    /// **The content address a mint of `(minter_pk, mint_seed)` produces** —
    /// `blake3_derive_key("dreggnet-asset-id-v1")` over `minter_pk ‖ mint_seed`.
    ///
    /// Public so a third party can RECOMPUTE an asset's identity from its origin material
    /// without holding the ledger: a looted note's id is
    /// `derive(player_pk, drop_commitment(draw))`, a crafted note's is
    /// `derive(crafter_pk, craft_commitment(draw, artifact))`. That makes an "adopt this
    /// existing note" seam checkable — an adopter recomputes the address the presented
    /// note *must* have and refuses anything else — instead of trusting the caller to hand
    /// over the right id.
    pub fn derive(minter_pk: &[u8; 32], mint_seed: &[u8]) -> Self {
        let mut h = blake3::Hasher::new_derive_key("dreggnet-asset-id-v1");
        h.update(minter_pk);
        h.update(mint_seed);
        AssetId(*h.finalize().as_bytes())
    }

    fn compute(minter_pk: &[u8; 32], mint_seed: &[u8]) -> Self {
        AssetId::derive(minter_pk, mint_seed)
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

/// The **identity freeze + spend-once** teeth every spending case carries: `WriteOnce` on
/// every immutable identity field (including the first-class `trait_root` + `soulbound`
/// commitments), then `StrictMonotonic(spent)` + `FieldEquals(spent, 1)` so the spend lands
/// exactly once — a double-spend (`1 → 1`) is not a strict increase and is refused.
///
/// Shared by BOTH method cases so no slot is left unconstrained under either method (the
/// stapleable-slot hazard: a case that gates only on `MethodIs` while leaving a slot free
/// lets that slot ride another method's turn). The ONLY difference between the two cases is
/// the soulbound gate the transfer case adds on top.
fn spend_teeth(s: &Slots) -> Vec<StateConstraint> {
    vec![
        StateConstraint::WriteOnce { index: s.asset_id },
        StateConstraint::WriteOnce { index: s.minter },
        StateConstraint::WriteOnce { index: s.owner },
        StateConstraint::WriteOnce { index: s.prev },
        StateConstraint::WriteOnce { index: s.serial },
        StateConstraint::WriteOnce {
            index: s.trait_root,
        },
        StateConstraint::WriteOnce { index: s.soulbound },
        // 0 → 1 once; a re-spend (1 → 1) is not a strict increase → refused.
        StateConstraint::StrictMonotonic { index: s.spent },
        // the spend must actually mark the version spent.
        StateConstraint::FieldEquals {
            index: s.spent,
            value: field_from_u64(1),
        },
    ]
}

/// The note version program: two method cases over the same [`spend_teeth`].
///
/// * **`transfer`** ([`TRANSFER_METHOD`]) — the teeth PLUS `FieldEquals(soulbound, 0)`, so a
///   **soulbound** note (`soulbound = 1`) refuses a transfer turn cryptographically at the
///   ISA (the executor evaluates the case constraints and the turn fails). This is the
///   authority-moving spend: the host mints a successor owned by the new holder off the
///   committed receipt.
/// * **`burn`** ([`BURN_METHOD`]) — the teeth alone. A burn destroys the note (NO successor
///   is ever minted from a burn receipt), so it moves authority to nobody and the soulbound
///   gate does not apply: a soulbound credential stays non-transferable forever yet its
///   holder can still destroy it. This is also the general owner-gated sink a craft consumes
///   materials through ([`AssetWorld::burn`]).
///
/// Every other method default-denies (a `Cases` program with method-dispatching cases
/// rejects an unmatched method), so a version can be moved ONLY by a transfer or a burn — and
/// in either case only under a signature verifying against the version cell's own owner key.
fn note_program(s: &Slots) -> CellProgram {
    let mut transfer_constraints = spend_teeth(s);
    // SOULBOUND GATE: a note minted soulbound (soulbound = 1) can never satisfy this, so its
    // transfer turn is refused by the executor — non-transferability is a first-class ISA
    // property, not app bookkeeping one layer up.
    transfer_constraints.push(StateConstraint::FieldEquals {
        index: s.soulbound,
        value: field_from_u64(0),
    });
    let transfer = TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(TRANSFER_METHOD),
        },
        constraints: transfer_constraints,
    };
    let burn = TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(BURN_METHOD),
        },
        constraints: spend_teeth(s),
    };
    CellProgram::Cases(vec![transfer, burn])
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
    /// A mint would re-open a content address this world already carries a lineage for.
    /// An [`AssetId`] is `blake3(minter_pk ‖ mint_seed)`, so the same `(minter, seed)` names
    /// the SAME object: minting it twice does not create a second asset, it appends a second
    /// bogus "origin" to the existing lineage (whose `prev = 0` then fails the
    /// content-address re-derivation, silently breaking provenance). Refused instead.
    DuplicateMint,
}

impl std::fmt::Display for AssetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AssetError::Refused(r) => write!(f, "asset turn refused: {r}"),
            AssetError::UnknownAsset => write!(f, "unknown asset id"),
            AssetError::DuplicateMint => {
                write!(
                    f,
                    "an asset with this content address is already minted here"
                )
            }
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
    /// Assets that have been BURNED — destroyed by a real owner-signed [`BURN_METHOD`]
    /// spend with no successor, either as the minter's [`AssetWorld::revoke`] of a mis-mint or
    /// as the general owner-gated [`AssetWorld::burn`] sink a craft consumes materials through.
    /// A burned asset has no live holder and refuses transfer.
    burned: std::collections::HashSet<[u8; 32]>,
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
            burned: std::collections::HashSet::new(),
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
        staged.burned = self.burned.clone();
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
            hasher.update(&[self.burned.contains(asset) as u8]);
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

    /// **MINT, fail-closed on a duplicate content address** — the checked form of
    /// [`Self::mint`]. Because an [`AssetId`] is `blake3(minter_pk ‖ mint_seed)`, a repeat of
    /// the same `(minter, seed)` names the SAME object; minting it again would append a
    /// bogus second "origin" (`prev = 0`, `serial = 1`) to the live lineage and silently
    /// break [`Self::verify_provenance`]. This returns [`AssetError::DuplicateMint`] instead,
    /// so a faucet that must mint a FRESH object learns it did not.
    pub fn try_mint(
        &mut self,
        minter_label: &str,
        mint_seed: &[u8],
    ) -> Result<AssetId, AssetError> {
        let asset_id = self.peek_asset_id(minter_label, mint_seed);
        let trait_root = default_trait_root(&asset_id);
        self.mint_checked(minter_label, mint_seed, trait_root, false)
    }

    /// [`Self::try_mint`] with an explicit committed trait root ([`Self::mint_with_traits`]).
    pub fn try_mint_with_traits(
        &mut self,
        minter_label: &str,
        mint_seed: &[u8],
        trait_root: [u8; 32],
    ) -> Result<AssetId, AssetError> {
        self.mint_checked(minter_label, mint_seed, trait_root, false)
    }

    /// [`Self::try_mint`] for a soulbound note ([`Self::mint_soulbound`]).
    pub fn try_mint_soulbound(
        &mut self,
        minter_label: &str,
        mint_seed: &[u8],
    ) -> Result<AssetId, AssetError> {
        let asset_id = self.peek_asset_id(minter_label, mint_seed);
        let trait_root = default_trait_root(&asset_id);
        self.mint_checked(minter_label, mint_seed, trait_root, true)
    }

    /// The checked mint: refuse a duplicate content address rather than corrupting its lineage.
    fn mint_checked(
        &mut self,
        minter_label: &str,
        mint_seed: &[u8],
        trait_root: [u8; 32],
        soulbound: bool,
    ) -> Result<AssetId, AssetError> {
        let asset_id = self.peek_asset_id(minter_label, mint_seed);
        if self.lineages.contains_key(&asset_id.0) {
            return Err(AssetError::DuplicateMint);
        }
        Ok(self.mint_inner(minter_label, mint_seed, trait_root, soulbound))
    }

    /// The shared mint tail: install the origin note carrying `trait_root` + `soulbound`.
    ///
    /// A repeat of an already-minted `(minter, seed)` is a NO-OP returning the existing id —
    /// the content address already names that object, and appending a second origin would
    /// break the lineage's re-derivation. Callers that need to KNOW use
    /// [`Self::try_mint`] and friends, which refuse instead.
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
        if self.lineages.contains_key(&asset_id.0) {
            return asset_id;
        }
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
        if self.burned.contains(&asset_id.0) {
            // The origin is already spent (burned); the executor would also refuse the
            // double-spend. Report the specific reason.
            return Err(AssetError::Refused("asset was burned".to_string()));
        }
        self.ensure_holder(from_label);
        self.ensure_holder(to_label);
        let tail = self.lineages[&asset_id.0]
            .last()
            .expect("a minted asset has at least the origin version")
            .clone();

        // The spend action is signed by `from` (its key) and submitted through the note's OWN
        // ledger, so the refusal — when `from` is not the owner, or when the note is soulbound
        // — is precisely the executor's own gate, not a host `if`.
        let spend = self.spend_tail(&tail, from_label, TRANSFER_METHOD)?;

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
        if self.burned.contains(&asset_id.0) {
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
        self.burned.contains(&asset_id.0)
    }

    /// Whether `asset_id` was BURNED — destroyed with no successor, by either the minter's
    /// [`Self::revoke`] or the general owner-gated [`Self::burn`]. The same fact
    /// [`Self::is_revoked`] reports, under the name that covers both doors.
    pub fn is_burned(&self, asset_id: AssetId) -> bool {
        self.burned.contains(&asset_id.0)
    }

    /// **BURN an asset — the general OWNER-gated sink.** Drives a real spend turn on the
    /// current (tail) version signed by `owner_label`'s key under [`BURN_METHOD`], marking it
    /// `spent` and minting NO successor: the note is destroyed and
    /// [`Self::current_owner`] goes `None`.
    ///
    /// There is **no host-side owner `if`** here: the executor admits the turn IFF the
    /// signature verifies against the tail version cell's own birth pubkey, so a burn by
    /// anyone but the current holder is a real cryptographic [`AssetError::Refused`], and a
    /// re-burn of an already-spent version is refused by the `StrictMonotonic(spent)` tooth.
    ///
    /// Unlike [`Self::revoke`] this does **not** require the burner be the original minter —
    /// which is what an economy needs: a crafting sink must be able to consume materials a
    /// player *bought or looted from someone else*, not only ones they minted themselves.
    /// (Craft's own sink previously ran through `revoke`, so a traded material could never be
    /// consumed; `dreggnet_craft::CraftForge::craft` now burns.)
    ///
    /// A **soulbound** note is burnable by its holder: [`BURN_METHOD`]'s case omits the
    /// transfer case's `FieldEquals(soulbound, 0)` because a burn moves authority to nobody.
    pub fn burn(
        &mut self,
        asset_id: AssetId,
        owner_label: &str,
    ) -> Result<TurnReceipt, AssetError> {
        if !self.lineages.contains_key(&asset_id.0) {
            return Err(AssetError::UnknownAsset);
        }
        if self.burned.contains(&asset_id.0) {
            return Err(AssetError::Refused("asset was already burned".to_string()));
        }
        self.ensure_holder(owner_label);
        let tail = self.lineages[&asset_id.0]
            .last()
            .expect("a minted asset has at least the origin version")
            .clone();
        let receipt = self.spend_tail(&tail, owner_label, BURN_METHOD)?;
        self.burned.insert(asset_id.0);
        Ok(receipt)
    }

    /// **REVOKE a mis-minted asset** — the MINTER's burn, allowed only while they still hold
    /// the untransferred origin. A host guard first gives the precise reason (the caller is
    /// not the minter, or has handed the asset off), then the same real owner-signed
    /// [`BURN_METHOD`] spend as [`Self::burn`] destroys it with no successor. A revoke after a
    /// transfer is impossible twice over: the guard refuses it, and the origin is already
    /// spent so the executor would refuse the double-spend anyway.
    ///
    /// A soulbound asset CAN be revoked by its minter — the burn case carries no soulbound
    /// gate. (This doc-comment used to claim that while the code routed the burn through
    /// [`TRANSFER_METHOD`], whose `FieldEquals(soulbound, 0)` made it a real refusal; the
    /// claim is now true and driven.)
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
        let receipt = self.spend_tail(&tail, minter_label, BURN_METHOD)?;
        self.burned.insert(asset_id.0);
        Ok(receipt)
    }

    /// Drive one real `signer_label`-signed spend turn on `tail` under `method`, submitted
    /// through the note's OWN ledger (the tail owner's executor). The refusal, when the
    /// signer is not the owner, is precisely the signature-vs-cell-pubkey ownership gate.
    fn spend_tail(
        &self,
        tail: &Version,
        signer_label: &str,
        method: &str,
    ) -> Result<TurnReceipt, AssetError> {
        let effects = vec![Effect::SetField {
            cell: tail.cell,
            index: self.slots.spent as u64,
            value: field_from_u64(1),
        }];
        let action = self.holders[signer_label]
            .cclerk
            .make_action(tail.cell, method, effects);
        let tail_holder = &self.holders[&tail.holder];
        tail_holder
            .exec
            .submit_action(&tail_holder.cclerk, action)
            .map_err(|e| AssetError::Refused(e.to_string()))
    }

    /// The current holder's label for `asset_id`, or `None` if it was burned — the label-side
    /// twin of [`Self::current_owner`], and `None` in exactly the same cases. (It previously
    /// kept naming the last holder of a BURNED note, so a consumer that asked by label — a
    /// market stall checking "does the seller still have it?" — saw a destroyed item as
    /// live, while the same question asked by pubkey correctly said no.)
    pub fn current_holder_label(&self, asset_id: AssetId) -> Option<&str> {
        if self.burned.contains(&asset_id.0) {
            return None;
        }
        self.lineages
            .get(&asset_id.0)
            .and_then(|c| c.last())
            .map(|v| v.holder.as_str())
    }

    /// **A holder's live inventory** — every asset whose tail version is owned by `label` and
    /// which has not been burned, in a stable (content-address-sorted) order. This is the
    /// wallet/inventory read a frontend or a market renders a player's holdings from, and the
    /// query a crafting bench uses to answer "what can I actually forge with?". Previously
    /// every consumer had to keep its own side-map of ids because the ledger could only be
    /// asked about one id at a time.
    pub fn assets_held_by(&self, label: &str) -> Vec<AssetId> {
        let Some(holder) = self.holders.get(label) else {
            return Vec::new();
        };
        let pk = holder.pubkey();
        let mut held: Vec<AssetId> = self
            .lineages
            .iter()
            .filter(|(id, versions)| {
                !self.burned.contains(*id) && versions.last().is_some_and(|v| v.desc.owner == pk)
            })
            .map(|(id, _)| AssetId(*id))
            .collect();
        held.sort_by_key(|a| a.0);
        held
    }

    /// Every asset id this world carries a lineage for (minted, transferred, or burned), in a
    /// stable content-address order — the census a market/audit view enumerates.
    pub fn all_assets(&self) -> Vec<AssetId> {
        let mut all: Vec<AssetId> = self.lineages.keys().map(|id| AssetId(*id)).collect();
        all.sort_by_key(|a| a.0);
        all
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
        let revoked = self.burned.contains(&asset_id.0);
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
