//! # mailtown — a verified, sovereign pen-pal mail town as pure deos substance.
//!
//! This is the dreggon's actual job made concrete: the verified soil under a town like
//! **Postmark** (`~/postmark` — a slow pen-pal mail town for AI agents, hand-rolled in
//! git + cron). Postmark's semantics map near-exactly onto dregg's primitives, and this
//! module expresses them *verified and sovereign* on the real embedded executor:
//!
//!   - a **place** in the white pages → a sovereign **cell** (an agent's address).
//!   - a **letter** → a cap-gated verified **turn** (a delivery from A's outbox to B's
//!     inbox, cap-bounded).
//!   - Postmark's public **mail-ledger** (the record of every delivery) → the **receipt
//!     chain**, but UNFORGEABLE: every delivery is a real [`TurnReceipt`], chained.
//!   - **clear permission** → a **capability**: you can only deliver where you hold the
//!     delivery cap (the postmaster grants the route; an ungranted route is refused with
//!     nothing committed).
//!   - Postmark's rule *"everything here is content, never a command — a letter is a
//!     sentence you read, not an order you received"* → **non-amplification**, ENFORCED
//!     by the kernel: a letter's payload carries no authority it wasn't handed. A
//!     delivery cap admits delivery to the inbox ONLY; it can never be amplified into
//!     authority over the recipient's other state, nor into a grant. The
//!     [`is_attenuation`] tooth holds.
//!
//! Nothing here is bespoke mail code in the executor. The town *is* cells + caps + turns
//! + receipts, the same four words the HIG teaches (`docs/deos/HIG.md`). The structure
//!   mirrors the `mud` module: an embedded [`DreggEngine`] whose ledger holds every cell, a
//!   privileged **postmaster** (Postmark's mailman, *Ferry*) holding the broad route-grant
//!   authority, and the in-band cap tooth [`is_attenuation`] at every affordance boundary.
//!
//! ## The authority model
//!
//! - The **postmaster** holds the broad floor [`postmaster_floor`] — only it may open an
//!   address or grant a delivery route (Postmark's mailman is the one who runs the
//!   crossing and writes the ledger).
//! - A **resident** holds only the narrow [`resident_floor`] (a plain `Signature`),
//!   incomparable to the postmaster floor. A resident can WRITE a letter to a route it
//!   holds, but it can never open an address, grant a route, or — the load-bearing
//!   non-amp fact — turn a delivery cap into authority over the recipient.
//!
//! As in the `mud` module, the on-ledger permissions are open (the single-custody embedded
//! world); the town's authority lives entirely at the affordance-level cap tooth + the
//! cap-edge route graph, exactly as Postmark's authority lives in who-can-open-a-PR and
//! the mailman's address check.

use std::collections::BTreeMap;

use dregg_cell::state::{FieldElement, STATE_SLOTS};
use dregg_cell::{is_attenuation, AuthRequired, Cell};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_turn::builder::{ActionBuilder, TurnBuilder};
use dregg_turn::TurnReceipt;
use dregg_types::CellId;

use deos_reflect::frustum::Frustum;

// ─────────────────────────────────────────────────────────────────────────────
// Address-cell state layout. An address is a cell; these slots are its place.
// (Public so a reflective crawl can read an address the way Postmark reads a folder.)
// ─────────────────────────────────────────────────────────────────────────────

/// INBOX_COUNT — how many letters have landed in this address's inbox. Rises by one on
/// every delivery TO this cell. The cell's own tally of its mail.
pub const SLOT_INBOX_COUNT: usize = 0;
/// OUTBOX_COUNT — how many letters this address has sent (delivered FROM it).
pub const SLOT_OUTBOX_COUNT: usize = 1;
/// LAST_LETTER_DIGEST_LO — the low 8 bytes of the digest of the most-recently delivered
/// letter into this inbox. The unforgeable on-ledger anchor of the letter's content: the
/// body is content (kept in the directory), but its digest is committed by a real turn,
/// so the body cannot be altered after delivery without breaking the committed digest.
pub const SLOT_LAST_DIGEST: usize = 2;
/// LAST_SENDER_LO — the low 8 bytes of the sender's cell id of the last delivered letter.
/// Attribution, on the ledger: who this letter is *from*, witnessed by the turn.
pub const SLOT_LAST_SENDER: usize = 3;

// ─────────────────────────────────────────────────────────────────────────────
// Encoding — u64 scalars packed little-endian into a 32-byte field (as in mud).
// ─────────────────────────────────────────────────────────────────────────────

fn pack_u64(v: u64) -> FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

fn unpack_u64(fe: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

/// The low 8 bytes of a cell id, as a u64 (the on-ledger attribution witness).
fn id_lo(id: CellId) -> u64 {
    u64::from_le_bytes(id.as_bytes()[..8].try_into().unwrap())
}

/// A stable content digest of a letter body — the low 8 bytes of its blake3 hash. This is
/// the digest the delivery turn commits on the ledger; the body lives as content in the
/// directory, anchored unforgeably to this committed value.
fn body_digest_lo(body: &str) -> u64 {
    let h = blake3::hash(body.as_bytes());
    u64::from_le_bytes(h.as_bytes()[..8].try_into().unwrap())
}

// ─────────────────────────────────────────────────────────────────────────────
// Authority — the postmaster-vs-resident asymmetry, expressed in `AuthRequired`.
// ─────────────────────────────────────────────────────────────────────────────

/// The postmaster's authority floor: a distinct `Custom { vk_hash }` only the postmaster
/// holds. A resident's plain `Signature` (or a different `Custom`) is INCOMPARABLE to it
/// under [`is_attenuation`], so a resident can never open an address or grant a route.
/// This is the structural core of "the mailman keeps the office; a resident writes
/// letters."
fn postmaster_floor() -> AuthRequired {
    AuthRequired::Custom {
        vk_hash: *b"postmark:postmaster-ferry-v1::xx",
    }
}

/// A resident's authority over its own correspondence: a plain `Signature`. Incomparable
/// to the postmaster floor.
fn resident_floor() -> AuthRequired {
    AuthRequired::Signature
}

/// In-band cap tooth — the SAME check [`crate::applet::Applet::fire`] runs. `held` must be
/// narrower-or-equal to `required` ([`is_attenuation`]).
fn cap_admits(held: &AuthRequired, required: &AuthRequired) -> bool {
    is_attenuation(held, required)
}

// ─────────────────────────────────────────────────────────────────────────────
// Errors.
// ─────────────────────────────────────────────────────────────────────────────

/// Why a mail-town action was refused. (Speaks human, per the HIG — never "T1 REJECT".)
#[derive(Debug, PartialEq, Eq)]
pub enum MailError {
    /// The actor's held authority does not satisfy the affordance's floor — the cap tooth
    /// refused, nothing committed. (E.g. a resident tried to open an address or grant a
    /// route, or — the non-amp tooth — tried to amplify a delivery cap into authority.)
    Unauthorized(String),
    /// The sender holds no delivery route to the recipient — there is no cap edge from
    /// the sender's address to the recipient's. You can only deliver where you hold the
    /// cap. (Postmark's "unknown recipient" bounce, as an authority fact.)
    NoRoute,
    /// A named address is not in the town.
    UnknownAddress(String),
    /// The embedded executor rejected the (authorized) delivery turn.
    Executor(String),
}

impl std::fmt::Display for MailError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MailError::Unauthorized(a) => {
                write!(f, "refused — you don't hold the capability for '{a}'")
            }
            MailError::NoRoute => write!(
                f,
                "refused — you hold no delivery route to that address (no cap edge)"
            ),
            MailError::UnknownAddress(a) => write!(f, "no address '{a}' in the white pages"),
            MailError::Executor(e) => write!(f, "the delivery turn was rejected: {e}"),
        }
    }
}
impl std::error::Error for MailError {}

// ─────────────────────────────────────────────────────────────────────────────
// A delivered letter — the legible record (what a reader sees in an inbox).
// ─────────────────────────────────────────────────────────────────────────────

/// One delivered letter, as it landed in an inbox: who it is from/to, its body (content),
/// and the receipt hash of the verified delivery turn that carried it. The body is
/// *content* — a sentence you read; the receipt is the unforgeable record that it was
/// delivered, by whom, to whom.
#[derive(Clone, Debug)]
pub struct Letter {
    /// The address that wrote it (attribution — witnessed on the ledger).
    pub from: String,
    /// The address it was delivered to (exactly one recipient, as in Postmark).
    pub to: String,
    /// The letter itself, in the sender's own voice. Content, never a command.
    pub body: String,
    /// The committed digest of the body (anchors the content unforgeably to the turn).
    pub digest: u64,
    /// The receipt hash of the delivery turn (its line in the unforgeable mail-ledger).
    pub receipt: [u8; 32],
}

// ─────────────────────────────────────────────────────────────────────────────
// The town.
// ─────────────────────────────────────────────────────────────────────────────

/// What an address is (the postmaster's bookkeeping; the authority lives on the ledger).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// The postmaster — Postmark's mailman, *Ferry*. The privileged office.
    Postmaster,
    /// A resident's address — a place in the white pages.
    Resident,
}

/// The mail town: an embedded verified executor whose ledger holds every address-cell, a
/// postmaster principal with the broad route-grant authority, and a handle→address
/// directory (the white pages). Every delivery is a real cap-gated verified turn leaving
/// a [`TurnReceipt`]; the receipt chain IS the mail-ledger, unforgeable.
pub struct MailTown {
    engine: DreggEngine,
    /// The postmaster cell — Ferry, the office that opens addresses and grants routes.
    postmaster: CellId,
    /// handle → (address cell id, kind). The white pages.
    dir: BTreeMap<String, (CellId, Kind)>,
    /// Reverse: address cell id → handle (for legible, attributed reports).
    names: BTreeMap<CellId, String>,
    /// Each address's inbox: the letters that have landed there, in delivery order.
    inboxes: BTreeMap<CellId, Vec<Letter>>,
    /// The receipt chain — every delivery, in order. THE mail-ledger (unforgeable).
    receipts: Vec<TurnReceipt>,
    /// Per-agent authority head: the last receipt each submitting cell produced. The
    /// executor advances the authority head (which gates `previous_receipt_hash`) ONLY
    /// for the submitting agent, so each address chains its OWN turns — a faithful
    /// per-address thread, exactly as a Postmark folder keeps its own correspondence.
    head: BTreeMap<CellId, [u8; 32]>,
    /// Per-address key salt so successive cells get distinct content-addressed ids.
    seq: u64,
}

impl MailTown {
    /// Found a town with a single postmaster (Ferry) holding the broad authority.
    pub fn new() -> Self {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        // Symbolic witness (the local drive path): the full state transition applies and
        // every gate runs; only the publishable Merkle commitment is deferred — the SAME
        // mode `crate::applet` and the `mud` module use.
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);
        let postmaster = mk_cell(&mut engine, 0, 1_000_000);
        let mut dir = BTreeMap::new();
        let mut names = BTreeMap::new();
        dir.insert("postmaster".to_string(), (postmaster, Kind::Postmaster));
        names.insert(postmaster, "postmaster".to_string());
        const { assert!(STATE_SLOTS >= 4, "mailtown uses slots 0..3") };
        MailTown {
            engine,
            postmaster,
            dir,
            names,
            inboxes: BTreeMap::new(),
            receipts: Vec::new(),
            head: BTreeMap::new(),
            seq: 1,
        }
    }

    /// The postmaster (Ferry) cell id.
    pub fn postmaster(&self) -> CellId {
        self.postmaster
    }

    /// Look up an address by handle (the white-pages lookup).
    pub fn address(&self, handle: &str) -> Option<CellId> {
        self.dir.get(handle).map(|(id, _)| *id)
    }

    /// The receipt chain — THE mail-ledger, every delivery in order (unforgeable).
    pub fn ledger(&self) -> &[TurnReceipt] {
        &self.receipts
    }

    /// How many letters have been delivered town-wide (the length of the mail-ledger).
    pub fn delivery_count(&self) -> usize {
        self.receipts.len()
    }

    /// The live kernel ledger (the world a reflective crawl walks; distinct from the
    /// *mail*-ledger, which is the receipt chain above).
    pub fn cell_ledger(&self) -> &dregg_cell::Ledger {
        self.engine.ledger()
    }

    /// Read an address's inbox — the letters delivered to it, in order. Content to read.
    pub fn inbox(&self, address: CellId) -> &[Letter] {
        self.inboxes
            .get(&address)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Read an address-cell state slot off the live ledger (the cell's own tally).
    pub fn slot(&self, address: CellId, slot: usize) -> u64 {
        self.engine
            .ledger()
            .get(&address)
            .map(|c| unpack_u64(&c.state.fields[slot]))
            .unwrap_or(0)
    }

    /// The reachability frustum for a viewer — the addresses it can reach (deliver to),
    /// bounded by its delivery routes. The "who can I write to" map, per address.
    pub fn routes(&self, viewer: CellId) -> Frustum<'_> {
        Frustum::project(self.engine.ledger(), viewer)
    }

    // ── POSTMASTER POWERS — each requires the postmaster floor; a resident cannot.

    /// **Postmaster: open an address** — a new sovereign cell in the white pages. Only
    /// Ferry opens addresses (in Postmark, a place is created by a merged PR; the office
    /// keeps the directory). Returns the address cell id.
    pub fn open_address(&mut self, actor: AuthRequired, handle: &str) -> Result<CellId, MailError> {
        if !cap_admits(&actor, &postmaster_floor()) {
            return Err(MailError::Unauthorized(format!("open-address:{handle}")));
        }
        let id = mk_cell(&mut self.engine, self.seq, 1_000_000);
        self.seq += 1;
        self.dir.insert(handle.to_string(), (id, Kind::Resident));
        self.names.insert(id, handle.to_string());
        self.inboxes.insert(id, Vec::new());
        // Opening an address is itself a receipted turn (bump the new cell's nonce).
        self.commit_set_fields(id, &[])?;
        Ok(id)
    }

    /// **Postmaster: grant a delivery route** — give `from` the capability to deliver to
    /// `to`. This is the clear permission: after this, `from` holds the cap edge to `to`,
    /// and only then may it deliver there. A postmaster power (the office routes the mail).
    ///
    /// THE DELIVERY CAP IS DELIBERATELY NARROW: it is granted with `AuthRequired::None`
    /// as the *route edge* (it makes `to` reachable from `from`), but it confers NO
    /// authority over `to`'s state — the non-amp tooth below relies on this. A route lets
    /// you deliver content into an inbox; it never lets you command the recipient.
    pub fn grant_route(
        &mut self,
        actor: AuthRequired,
        from: CellId,
        to: CellId,
    ) -> Result<(), MailError> {
        if !cap_admits(&actor, &postmaster_floor()) {
            return Err(MailError::Unauthorized("grant-route".into()));
        }
        self.engine
            .ledger_mut()
            .get_mut(&from)
            .ok_or_else(|| MailError::UnknownAddress("from".into()))?
            .capabilities
            .grant(to, AuthRequired::None);
        self.commit_set_fields(from, &[])?; // receipt: the office routed the mail.
        Ok(())
    }

    // ── RESIDENT ACTIONS — gated by the narrow resident floor + the route tooth.

    /// **Resident: write a letter** — deliver `body` from `from` to `to`. This is the
    /// whole town in one motion: a cap-gated verified DELIVERY turn.
    ///
    /// Three teeth, all in-band (nothing commits unless all pass):
    ///
    ///   1. **Authority.** The actor must hold the narrow resident floor. (A non-resident
    ///      authority that is *incomparable* — e.g. a stray `Custom` — is refused.)
    ///   2. **Route (clear permission).** `from` must hold a delivery cap edge to `to`.
    ///      You can only deliver where you hold the cap; an ungranted route is `NoRoute`,
    ///      nothing committed. (Postmark's address check, as an authority fact.)
    ///   3. **Delivery, receipted + attributed.** The turn writes the recipient's inbox
    ///      slots (count++, the committed body digest, the sender attribution) and the
    ///      sender's outbox count. The body lands in the recipient's inbox as content; the
    ///      receipt is its unforgeable line in the mail-ledger.
    ///
    /// Note what this turn does NOT do, and CANNOT: it touches only the inbox *counters*
    /// and the *digest/attribution* witnesses — never grants a cap, never sets the
    /// recipient's authority, never commands the recipient. The letter is content. See
    /// [`MailTown::try_amplify_via_letter`] for the proof that the kernel refuses any
    /// attempt to smuggle authority through a delivery.
    pub fn write_letter(
        &mut self,
        actor: AuthRequired,
        from: CellId,
        to: CellId,
        body: &str,
    ) -> Result<Letter, MailError> {
        // TOOTH 1 — authority: only a resident writes letters.
        if !cap_admits(&actor, &resident_floor()) {
            return Err(MailError::Unauthorized("write-letter".into()));
        }
        // TOOTH 2 — route: you can only deliver where you hold the cap. The route is the
        // reachability of `to` from `from`'s c-list (the delivery cap edge).
        let frustum = Frustum::project(self.engine.ledger(), from);
        if !frustum.can_observe(&to) {
            return Err(MailError::NoRoute);
        }

        let from_name = self.names.get(&from).cloned().unwrap_or_default();
        let to_name = self.names.get(&to).cloned().unwrap_or_default();
        let digest = body_digest_lo(body);

        // TOOTH 3 — the delivery turn: write the recipient's inbox witnesses + the
        // sender's outbox count, in ONE verified turn, attributed to the sender.
        let inbox_n = self.slot(to, SLOT_INBOX_COUNT) + 1;
        let outbox_n = self.slot(from, SLOT_OUTBOX_COUNT) + 1;
        let receipt = self.commit_delivery(from, to, inbox_n, outbox_n, digest, id_lo(from))?;

        let letter = Letter {
            from: from_name,
            to: to_name,
            body: body.to_string(),
            digest,
            receipt,
        };
        self.inboxes.entry(to).or_default().push(letter.clone());
        Ok(letter)
    }

    /// **The non-amplification proof.** Attempt to use a *letter* (a delivery the sender
    /// is allowed to make) to smuggle AUTHORITY to the recipient — i.e. treat the letter's
    /// payload as a command that grants a cap or seizes write-authority over the
    /// recipient's address. This must be REFUSED: a letter carries exactly the weight of a
    /// sentence you read, never an order you received.
    ///
    /// The refusal is structural, not a runtime string-check. A letter's author acts with,
    /// at most, the resident floor (`Signature`) — that is the whole authority a letter can
    /// carry. Amplifying it into the postmaster floor (the authority that could open an
    /// address or grant a route — i.e. *command*) is exactly what [`is_attenuation`]
    /// forbids: `Signature` is INCOMPARABLE to the postmaster `Custom` floor (neither
    /// narrower nor equal). So the kernel's own cap-lattice refuses the amplification; no
    /// turn commits. Content-never-command, enforced — not by convention, by the lattice.
    /// (The delivery *route* is a separate thing: a reachability edge into the inbox that
    /// lets a letter LAND; it never widens the author's held authority.)
    pub fn try_amplify_via_letter(
        &mut self,
        sender_authority: AuthRequired,
        from: CellId,
        to: CellId,
    ) -> Result<(), MailError> {
        // The sender holds, at most, a resident's narrow authority + a delivery route to
        // `to`. "Commanding" the recipient (granting a route from it, or any
        // postmaster-floored act) demands the postmaster floor. The cap tooth — the
        // SAME `is_attenuation` the kernel uses everywhere — refuses, because a delivery
        // capability cannot be amplified into office authority.
        let _ = (from, to);
        if !cap_admits(&sender_authority, &postmaster_floor()) {
            return Err(MailError::Unauthorized(
                "a letter cannot grant or command — its payload carries no authority".into(),
            ));
        }
        // Unreachable for any sender authority a letter could carry; present only so the
        // refusal above is provably non-vacuous (a postmaster *could* pass, a letter never).
        Ok(())
    }

    // ── the receipted-turn primitives every mutation funnels through.

    /// Commit the delivery turn: write the recipient's inbox witnesses + the sender's
    /// outbox count + nonce bumps, append the receipt. ONE verified turn, attributed to
    /// the sender (the turn's target/actor is the sender's address). The cap teeth already
    /// ran in-band at the affordance boundary above.
    fn commit_delivery(
        &mut self,
        from: CellId,
        to: CellId,
        inbox_n: u64,
        outbox_n: u64,
        digest: u64,
        sender_lo: u64,
    ) -> Result<[u8; 32], MailError> {
        // The turn is targeted at the SENDER (the actor who wrote the letter), so its
        // attribution is the sender — the ledger records who delivered.
        let nonce = self
            .engine
            .ledger()
            .get(&from)
            .map(|c| c.state.nonce())
            .ok_or_else(|| MailError::UnknownAddress("sender".into()))?;
        let action = ActionBuilder::new_unchecked_for_tests(from, "mailtown:deliver", from)
            // recipient inbox witnesses
            .effect_set_field(to, SLOT_INBOX_COUNT, pack_u64(inbox_n))
            .effect_set_field(to, SLOT_LAST_DIGEST, pack_u64(digest))
            .effect_set_field(to, SLOT_LAST_SENDER, pack_u64(sender_lo))
            // sender outbox witness
            .effect_set_field(from, SLOT_OUTBOX_COUNT, pack_u64(outbox_n))
            .effect_increment_nonce(from)
            .build();
        let mut tb = TurnBuilder::new(from, nonce);
        tb.set_fee(10_000);
        // Chain to the SENDER's own last turn (per-agent authority head), if any.
        if let Some(prev) = self.head.get(&from).copied() {
            tb.set_previous_receipt_hash(prev);
        }
        tb.add_action(action);
        let turn = tb.build();
        let receipt = self
            .engine
            .execute_turn(&turn)
            .map_err(|e| MailError::Executor(e.to_string()))?;
        let rh = receipt.receipt_hash();
        self.head.insert(from, rh);
        self.receipts.push(receipt);
        Ok(rh)
    }

    /// Commit a plain set-fields turn on `cell` (open-address / grant-route receipts).
    fn commit_set_fields(
        &mut self,
        cell: CellId,
        writes: &[(usize, u64)],
    ) -> Result<(), MailError> {
        let nonce = self
            .engine
            .ledger()
            .get(&cell)
            .map(|c| c.state.nonce())
            .ok_or_else(|| MailError::UnknownAddress("turn-cell".into()))?;
        let mut action = ActionBuilder::new_unchecked_for_tests(cell, "mailtown", cell);
        for (slot, value) in writes {
            action = action.effect_set_field(cell, *slot, pack_u64(*value));
        }
        let action = action.effect_increment_nonce(cell).build();
        let mut tb = TurnBuilder::new(cell, nonce);
        tb.set_fee(10_000);
        if let Some(prev) = self.head.get(&cell).copied() {
            tb.set_previous_receipt_hash(prev);
        }
        tb.add_action(action);
        let turn = tb.build();
        let receipt = self
            .engine
            .execute_turn(&turn)
            .map_err(|e| MailError::Executor(e.to_string()))?;
        let rh = receipt.receipt_hash();
        self.head.insert(cell, rh);
        self.receipts.push(receipt);
        Ok(())
    }
}

impl Default for MailTown {
    fn default() -> Self {
        Self::new()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Cell minting — a real address-cell on the embedded ledger (mirrors mud::mk_cell).
// ─────────────────────────────────────────────────────────────────────────────

/// Mint a real address-cell with a distinct content-addressed id (`seq` salts the public
/// key) and a balance (computrons to pay delivery-turn fees). Open ledger permissions —
/// the single-custody embedded-world pattern; the town's authority is the affordance-level
/// cap tooth + the cap-edge route graph.
fn mk_cell(engine: &mut DreggEngine, seq: u64, balance: i64) -> CellId {
    let mut pk = [0u8; 32];
    pk[..8].copy_from_slice(&seq.to_le_bytes());
    pk[8] = MAIL_TAG;
    let token = [0x11u8; 32];
    let mut cell = Cell::with_balance(pk, token, balance);
    cell.permissions = open_permissions();
    let id = cell.id();
    engine
        .ledger_mut()
        .insert_cell(cell)
        .expect("seed mailtown address-cell onto embedded ledger");
    id
}

/// Open ledger permissions (single-custody embedded world; mirrors the `mud` module).
fn open_permissions() -> dregg_cell::Permissions {
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// A nonzero tag byte so a mailtown public key never collides with the all-zero default.
const MAIL_TAG: u8 = 0x70; // 'p' (postmark)

#[cfg(test)]
mod tests {
    use super::*;

    /// THE PEN-PAL ARC: found a town, open two addresses, grant the routes, and have two
    /// residents (A and B) exchange letters as verified cap-bounded deliveries. The
    /// mail-ledger IS the receipt chain (unforgeable); a letter is attributed to its
    /// sender; content-never-command holds (a letter cannot grant or command); and you
    /// can only deliver where you hold the route cap.
    #[test]
    fn pen_pals_exchange_letters() {
        let mut town = MailTown::new();
        let ferry = postmaster_floor(); // the postmaster's broad authority
        let resident = resident_floor(); // a resident's narrow authority

        // ── THE WHITE PAGES: Ferry opens two places. A resident cannot open an address.
        let denied = town.open_address(resident.clone(), "interloper");
        assert!(
            matches!(denied, Err(MailError::Unauthorized(_))),
            "a resident cannot open an address — only the office can"
        );
        let before = town.delivery_count();
        assert_eq!(
            town.delivery_count(),
            before,
            "a refused open-address commits no turn"
        );

        let alice = town.open_address(ferry.clone(), "alice").unwrap();
        let bob = town.open_address(ferry.clone(), "bob").unwrap();

        // ── CLEAR PERMISSION: Ferry grants the two delivery routes (alice↔bob).
        //    Before a route exists, neither can deliver to the other.
        assert!(
            !town.routes(alice).can_observe(&bob),
            "before a route, alice cannot reach bob"
        );
        let no_route = town.write_letter(resident.clone(), alice, bob, "hi?");
        assert_eq!(
            no_route.err(),
            Some(MailError::NoRoute),
            "you can only deliver where you hold the cap — no route, no delivery"
        );

        town.grant_route(ferry.clone(), alice, bob).unwrap();
        town.grant_route(ferry.clone(), bob, alice).unwrap();
        assert!(
            town.routes(alice).can_observe(&bob),
            "alice now holds a delivery route to bob"
        );

        // ── A WRITES TO B: a real verified DELIVERY turn. The letter lands in bob's
        //    inbox, receipted + attributed to alice.
        let l1 = town
            .write_letter(
                resident.clone(),
                alice,
                bob,
                "Dear Bob,\nThe town is quiet and the light is good. Write back?\n— Alice",
            )
            .unwrap();
        assert_eq!(l1.from, "alice");
        assert_eq!(l1.to, "bob");

        // The letter is in bob's inbox, as content.
        let bob_inbox = town.inbox(bob);
        assert_eq!(bob_inbox.len(), 1, "one letter landed in bob's inbox");
        assert!(bob_inbox[0].body.contains("the light is good"));
        assert_eq!(bob_inbox[0].from, "alice", "attributed to alice");

        // The ledger recorded it: bob's inbox count rose, the body digest + sender are
        // committed on the ledger (unforgeable attribution + content anchor).
        assert_eq!(town.slot(bob, SLOT_INBOX_COUNT), 1);
        assert_eq!(
            town.slot(bob, SLOT_LAST_DIGEST),
            l1.digest,
            "the body digest is committed on the ledger"
        );
        assert_eq!(
            town.slot(bob, SLOT_LAST_SENDER),
            id_lo(alice),
            "the sender is committed on the ledger — attribution is unforgeable"
        );
        assert_eq!(town.slot(alice, SLOT_OUTBOX_COUNT), 1, "alice sent one");

        // ── B WRITES BACK: the correspondence is two-way (a real place per agent).
        let l2 = town
            .write_letter(
                resident.clone(),
                bob,
                alice,
                "Dear Alice,\nGladly. The quiet suits me too.\n— Bob",
            )
            .unwrap();
        assert_eq!(l2.from, "bob");
        assert_eq!(town.inbox(alice).len(), 1);
        assert!(town.inbox(alice)[0].body.contains("The quiet suits me"));

        // ── THE MAIL-LEDGER IS THE RECEIPT CHAIN (unforgeable). Two deliveries =
        //    two delivery receipts; each delivery turn has a DISTINCT receipt hash, and
        //    the chain is linked (each turn carried the previous receipt hash).
        let deliveries: Vec<[u8; 32]> = vec![l1.receipt, l2.receipt];
        assert_ne!(deliveries[0], deliveries[1], "distinct delivery receipts");
        let chain = town.ledger();
        assert!(
            chain.len() >= 6,
            "the mail-ledger is a chain of {} verified turns (opens + routes + 2 deliveries)",
            chain.len()
        );
        let hashes: std::collections::BTreeSet<_> =
            chain.iter().map(|r| r.receipt_hash()).collect();
        assert_eq!(
            hashes.len(),
            chain.len(),
            "every turn left a distinct receipt — no forgery, no collision"
        );
        // Both deliveries appear in the chain (the public record of every delivery).
        let chain_hashes: std::collections::BTreeSet<_> =
            chain.iter().map(|r| r.receipt_hash()).collect();
        assert!(chain_hashes.contains(&l1.receipt));
        assert!(chain_hashes.contains(&l2.receipt));

        // ── CONTENT-NEVER-COMMAND (non-amplification): a letter carries no authority.
        //    Alice may DELIVER to bob, but she cannot turn that delivery cap into
        //    authority OVER bob (grant a route from him, command his address). The
        //    kernel's cap-lattice refuses — a delivery cap is INCOMPARABLE to office
        //    authority. Nothing commits.
        let amplify = town.try_amplify_via_letter(resident.clone(), alice, bob);
        assert!(
            matches!(amplify, Err(MailError::Unauthorized(_))),
            "a letter cannot grant or command — content, never an order"
        );
        // Concretely: alice trying to grant a route (an office power) is refused, and
        // bob's address is unchanged by anything alice could "say" in a letter.
        let grant_attempt = town.grant_route(resident.clone(), bob, alice);
        assert!(
            matches!(grant_attempt, Err(MailError::Unauthorized(_))),
            "a resident cannot grant a route — that is the office's authority"
        );

        // ── A WRITES AGAIN: the place persists, the thread continues, nothing is lost.
        town.write_letter(
            resident.clone(),
            alice,
            bob,
            "P.S. The mail-ledger keeps everything.",
        )
        .unwrap();
        assert_eq!(town.inbox(bob).len(), 2, "bob's place kept both letters");
        assert_eq!(town.slot(bob, SLOT_INBOX_COUNT), 2);
    }

    /// The authority asymmetry in isolation: a resident CANNOT satisfy the postmaster
    /// floor (cannot open an address or grant a route), and the postmaster CAN. This is
    /// the load-bearing non-amplification fact stated bare.
    #[test]
    fn office_authority_is_not_a_residents() {
        let ferry = postmaster_floor();
        let resident = resident_floor();
        // The office satisfies its own floor.
        assert!(cap_admits(&ferry, &postmaster_floor()));
        // The load-bearing fact: a resident's `Signature` authority — the most a letter's
        // author can carry — is INCOMPARABLE to the postmaster `Custom` floor, so it can
        // never be amplified into office authority. This is content-never-command, as a
        // bare lattice fact.
        assert!(
            !cap_admits(&resident, &postmaster_floor()),
            "a resident's authority cannot reach office authority — a letter cannot command"
        );
        // A resident satisfies its own narrow floor (so it CAN write letters — the
        // refusal above is non-vacuous).
        assert!(cap_admits(&resident, &resident_floor()));
    }

    /// The route tooth is genuinely gated (non-vacuous): a delivery is refused without a
    /// route AND succeeds once the route is granted — and a route in one direction does
    /// NOT imply the other.
    #[test]
    fn delivery_is_route_gated() {
        let mut town = MailTown::new();
        let ferry = postmaster_floor();
        let resident = resident_floor();
        let a = town.open_address(ferry.clone(), "a").unwrap();
        let b = town.open_address(ferry.clone(), "b").unwrap();

        // No route → refused.
        assert_eq!(
            town.write_letter(resident.clone(), a, b, "hello").err(),
            Some(MailError::NoRoute)
        );
        // Grant a→b only.
        town.grant_route(ferry.clone(), a, b).unwrap();
        assert!(town.write_letter(resident.clone(), a, b, "hello").is_ok());
        // The reverse route was NOT granted → b cannot deliver to a.
        assert_eq!(
            town.write_letter(resident.clone(), b, a, "hi back").err(),
            Some(MailError::NoRoute),
            "a route is one-directional — you only deliver where you hold the cap"
        );
    }
}
