//! **Multi-cell agent turns** — hyperdreggmedia authoring surface #2
//! (`docs/deos/HYPERDREGGMEDIA-NOTES.md` §6).
//!
//! Today an [`Applet`](crate::Applet) authors ONE cell, and a
//! [`CardEditor`](crate::CardEditor) authors ONE card. This module lets the agent
//! (or a user) author a STORY that spans MULTIPLE cells in one coherent gesture —
//! mint a card, grant a cap to a peer, set a field on a third cell — each leg a real
//! cap-gated *verified turn*, the whole composition bounded by the author's `held`
//! authority. The unifying truth holds across cells: *every authoring gesture is an
//! affordance; every affordance is a turn; every turn is a receipt.*
//!
//! ## The cap tooth, generalised to multiple cells
//!
//! [`Applet::fire`](crate::Applet::fire) keeps the cap tooth by checking ONE
//! affordance's `required` against the driver's `held`, and binds the turn to the
//! applet's OWN cell (a fire cannot cross to another vessel). A multi-cell story has
//! TWO over-reach faces, and this module refuses BOTH in-band:
//!
//!   1. **authority over-reach** — a step whose `required` authority is NOT narrower-
//!      or-equal to the author's `held` ([`dregg_cell::is_attenuation`], the exact
//!      tooth `Applet::fire` uses). The author cannot author a step it lacks the cap
//!      level for.
//!   2. **scope over-reach** — a step that touches a cell OUTSIDE the author's
//!      capped scope (`held_cells`): a SetField on a foreign vessel's cell, a grant
//!      FROM a cell the author does not hold. The author's authority is bounded to a
//!      set of cells; a leg reaching past that set is refused.
//!
//! ## All-or-nothing: PRE-SCREEN atomic, then step-wise commit
//!
//! The executor IS atomic within ONE turn (a multi-action/multi-effect `Turn` rolls
//! back ALL effects on any action failure — `turn/src/executor/execute.rs`). So two
//! composition shapes are genuinely available:
//!
//!   * **one atomic turn** carrying every leg's effects → true all-or-nothing at the
//!     ledger; but a created cell defaults to `set_state: Signature` permissions
//!     (`cell::Permissions::default`), so a same-turn create+setField on the NEW cell
//!     would trip the cross-cell `set_state` gate under the unchecked embedded driver.
//!     Atomic-turn composition is therefore subtle to get right and is NOT what this
//!     module commits (flagged below).
//!   * **step-wise turns, atomically PRE-SCREENED** — what we do. EVERY leg is checked
//!     against `held` + scope BEFORE ANY turn commits ([`MultiCellAuthor::compose`]).
//!     An over-reaching leg ABORTS the whole composition in-band: NO turn for ANY leg,
//!     no partial commit of an unauthorized leg ([`ComposeError::OverReach`]). Only a
//!     fully-authorised story commits; then each leg lands as its OWN verified turn
//!     with its OWN receipt, all attributed to the author cell.
//!
//! This is the SAME `applet`/`attach` machinery — `is_attenuation` as the tooth,
//! `ActionBuilder`/`TurnBuilder` for each turn, `DreggEngine::execute_turn` for the
//! real receipt — not a parallel model. The single-custody embedded world seeds the
//! author's capped cells with [`open_permissions`]-shaped permissions (as
//! `Applet::mint` does), so the executor admits the author's writes and the cap tooth
//! lives HERE in deos-js.

use std::collections::BTreeSet;

use dregg_cell::capability::CapabilityRef;
use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_turn::builder::{ActionBuilder, TurnBuilder};
use dregg_turn::TurnReceipt;
use dregg_types::CellId;

use crate::applet::Slot;

/// A single leg of a multi-cell story. Each leg names the cell(s) it touches (so the
/// scope tooth can refuse a leg reaching past `held_cells`) and carries the authority
/// it `requires` (so the cap tooth can refuse a leg whose `required` over-reaches
/// `held`).
pub enum Step {
    /// **Mint a card** — create a fresh cell (a new applet) the author becomes capped
    /// over. The new cell is seeded into the author's world with open (single-custody)
    /// permissions and `seed_fields` as its genesis model. After a successful compose,
    /// the new cell id is reported (see [`Composition::minted`]) and IS added to the
    /// author's scope for subsequent legs in the SAME story.
    MintCard {
        /// The new cell's public key (its principal).
        public_key: [u8; 32],
        /// The new cell's token domain.
        token_id: [u8; 32],
        /// The genesis model fields written into the new cell's state.
        seed_fields: Vec<(Slot, FieldElement)>,
        /// The authority minting requires (the cap tooth checks `held ⊒ required`).
        required: AuthRequired,
    },
    /// **Set a field** on a cell — a real `SetField` verified turn writing `slot :=
    /// value` on `cell`. `cell` must be in the author's scope (a SetField on a foreign
    /// vessel's cell is the scope over-reach the tooth refuses).
    SetField {
        /// The cell whose model field is written (must be in scope).
        cell: CellId,
        /// The model slot.
        slot: Slot,
        /// The new value (packed as a field element by the caller, or via
        /// [`crate::applet::pack_u64`]).
        value: FieldElement,
        /// The authority the write requires.
        required: AuthRequired,
    },
    /// **Grant a capability** from one of the author's cells TO a peer cell. The
    /// `from` cell must be in the author's scope (you may only grant from a cell you
    /// hold); `to` may be any peer (granting INTO a peer is the point — extending
    /// authority outward). The granted `cap`'s `permissions` is the authority being
    /// handed over and is itself cap-checked: it must be narrower-or-equal to `held`
    /// (you cannot grant authority you do not hold).
    GrantCap {
        /// The author-held cell the grant issues FROM (must be in scope).
        from: CellId,
        /// The peer cell receiving the capability (need NOT be in scope — this is the
        /// outward reach of the story).
        to: CellId,
        /// The capability granted. Its `permissions` is the authority handed over and
        /// is cap-checked against `held` (no granting authority you lack).
        cap: CapabilityRef,
        /// The authority issuing the grant requires.
        required: AuthRequired,
    },
}

impl Step {
    /// The authority this step requires (what the cap tooth checks against `held`).
    fn required(&self) -> &AuthRequired {
        match self {
            Step::MintCard { required, .. }
            | Step::SetField { required, .. }
            | Step::GrantCap { required, .. } => required,
        }
    }

    /// A short human method name carried as the turn's action method (the audit label).
    fn method(&self) -> &'static str {
        match self {
            Step::MintCard { .. } => "mint_card",
            Step::SetField { .. } => "set_field",
            Step::GrantCap { .. } => "grant_cap",
        }
    }
}

/// Why a multi-cell composition was refused. An over-reach is reported IN-BAND with
/// NOTHING committed — the cap tooth held before any turn ran.
#[derive(Debug)]
pub enum ComposeError {
    /// The cap tooth refused a step: either its `required` authority is not narrower-
    /// or-equal to `held` (authority over-reach), or it touches a cell outside the
    /// author's scope (scope over-reach), or it grants authority the author does not
    /// hold. Carries the 0-based step index and a reason. NO turn committed for ANY
    /// leg (the whole story aborts — no partial commit of an unauthorized leg).
    OverReach { step: usize, reason: String },
    /// A leg cleared the cap tooth but the embedded executor rejected its turn. The
    /// legs committed BEFORE it have landed (step-wise commit); this names the failed
    /// leg's index and the executor's reason. (Pre-screening removes authority/scope
    /// rejections; this is the residual executor-side failure surface, e.g. budget.)
    Executor { step: usize, reason: String },
}

impl std::fmt::Display for ComposeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComposeError::OverReach { step, reason } => {
                write!(
                    f,
                    "step {step} over-reaches the author's held authority: {reason}"
                )
            }
            ComposeError::Executor { step, reason } => {
                write!(f, "step {step} refused by the embedded executor: {reason}")
            }
        }
    }
}
impl std::error::Error for ComposeError {}

/// The record of a committed multi-cell story: every leg's receipt (in order, all
/// attributed to the author cell), and the ids of any cells minted along the way.
#[derive(Debug, Clone)]
pub struct Composition {
    /// The committed receipt of each leg, in step order. One leg = one verified turn =
    /// one receipt.
    pub receipts: Vec<TurnReceipt>,
    /// The cell ids minted by `MintCard` legs, in order (each is now in the author's
    /// scope).
    pub minted: Vec<CellId>,
}

impl Composition {
    /// The number of verified turns the story committed (= the number of legs).
    pub fn len(&self) -> usize {
        self.receipts.len()
    }
    /// Whether the story was empty (no legs).
    pub fn is_empty(&self) -> bool {
        self.receipts.is_empty()
    }
    /// The receipt hashes, in order (the audit tape the story left).
    pub fn receipt_hashes(&self) -> Vec<[u8; 32]> {
        self.receipts.iter().map(|r| r.receipt_hash()).collect()
    }
}

/// A **multi-cell author** — bound to a `held` authority over a World of cells it is
/// capped for, composing stories that span those cells (and reach OUTWARD via grants).
///
/// Like [`Applet`](crate::Applet) it owns an embedded [`DreggEngine`] (single-custody)
/// and runs Symbolic by default (the cheap local witness mode). Unlike `Applet` it
/// holds a SET of cells (`held_cells`) — the author's authority scope — and an `author`
/// cell that is the agent of every committed turn. The cap tooth ([`dregg_cell::is_attenuation`])
/// lives here, exactly as in `Applet::fire`.
pub struct MultiCellAuthor {
    /// The embedded verified executor — the substance. Each leg leaves a REAL receipt.
    engine: DreggEngine,
    /// The author cell — the agent of every committed turn (the principal the story is
    /// attributed to). It is itself in `held_cells`.
    author: CellId,
    /// The held authority the author wields (every step's `required` is checked against
    /// this; every granted cap's `permissions` is checked against this).
    held: AuthRequired,
    /// The author's authority SCOPE — the cells it may touch. A leg touching a cell
    /// outside this set is the scope over-reach the tooth refuses. `MintCard` grows it.
    held_cells: BTreeSet<CellId>,
    /// The chain head, threaded into each leg's `previous_receipt_hash`.
    prev_receipt: Option<[u8; 32]>,
    /// Every committed receipt hash, in order (the audit tape across the whole story).
    receipts: Vec<[u8; 32]>,
}

impl MultiCellAuthor {
    /// Mint a multi-cell author over a fresh embedded World seeded with the author cell,
    /// its pre-declared `scope` cells (the cards it holds + may author over), and any
    /// `peers` (foreign vessels the story reaches toward via grants, NOT in scope).
    /// `held` is the author's wielded authority; `held_cells` starts as
    /// `{author} ∪ scope`.
    ///
    /// THE EXECUTOR-STANDING SEED (why scope is pre-declared). A cross-cell write
    /// (author → a scope card) is gated by the executor's OWN tooth
    /// (`check_cross_cell_permission`, `turn/src/executor/apply.rs`): the author cell
    /// must HOLD an access capability to the target in its c-list, AND the target's
    /// permission for the action must be open. So `mint`:
    ///   * seeds the author cell with a fee balance + open single-custody permissions
    ///     (as [`Applet::mint`](crate::Applet::mint) does);
    ///   * creates each `scope` card with open permissions; and
    ///   * grants the author cell an access capability to each scope card (a real
    ///     `CapabilitySet` entry — the author's genesis c-list standing).
    ///     `peers` are seeded with DEFAULT (foreign) permissions and NO author c-list entry
    ///     — the author does NOT hold them; a `SetField`/grant-FROM on one is refused by the
    ///     in-band scope tooth BEFORE any turn (and the executor would also refuse it).
    pub fn mint(
        author_public_key: [u8; 32],
        author_token_id: [u8; 32],
        held: AuthRequired,
        scope: &[([u8; 32], [u8; 32])],
        peers: &[([u8; 32], [u8; 32])],
    ) -> Self {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);

        let author = CellId::derive_raw(&author_public_key, &author_token_id);
        let mut held_cells = BTreeSet::new();
        held_cells.insert(author);

        // The author cell — open permissions (single-custody), a fee balance. Its c-list
        // is seeded below with access to each scope card (the standing a cross-cell
        // write needs).
        let mut author_cell = Cell::with_balance(author_public_key, author_token_id, 1_000_000);
        author_cell.permissions = open_permissions();

        // Scope cards — open permissions, no balance. The author gets a c-list access
        // entry to each (its genesis standing over its own scope).
        for (pk, tok) in scope {
            let id = CellId::derive_raw(pk, tok);
            let mut card = Cell::with_balance(*pk, *tok, 0);
            card.permissions = open_permissions();
            let _ = engine.ledger_mut().insert_cell(card);
            // The author HOLDS this card — an access capability in its c-list, so the
            // executor's cross-cell tooth grants standing (and `held_cells` mirrors it).
            author_cell.capabilities.grant(id, AuthRequired::None);
            held_cells.insert(id);
        }

        engine
            .ledger_mut()
            .insert_cell(author_cell)
            .expect("seed the author cell onto the embedded ledger");

        // Peer cells — default (foreign) permissions, no author c-list entry. They exist
        // so a `GrantCap { to: peer }` has a real recipient; NOT in the author's scope.
        for (pk, tok) in peers {
            let peer = Cell::with_balance(*pk, *tok, 0);
            let _ = engine.ledger_mut().insert_cell(peer);
        }

        MultiCellAuthor {
            engine,
            author,
            held,
            held_cells,
            prev_receipt: None,
            receipts: Vec::new(),
        }
    }

    /// The author cell (the agent of every committed turn).
    pub fn author(&self) -> CellId {
        self.author
    }

    /// The author's held authority.
    pub fn held(&self) -> &AuthRequired {
        &self.held
    }

    /// Whether `cell` is in the author's authority scope (the cells it may touch).
    pub fn holds_cell(&self, cell: &CellId) -> bool {
        self.held_cells.contains(cell)
    }

    /// The author's current scope (the cells it holds), sorted.
    pub fn held_cells(&self) -> Vec<CellId> {
        self.held_cells.iter().copied().collect()
    }

    /// The live ledger (a witnessed, read-only view of the World — the SAME ledger the
    /// legs commit onto).
    pub fn ledger(&self) -> &dregg_cell::Ledger {
        self.engine.ledger()
    }

    /// The committed receipt tape across every story (in order).
    pub fn receipts(&self) -> &[[u8; 32]] {
        &self.receipts
    }

    /// The number of verified turns committed in total.
    pub fn receipt_count(&self) -> usize {
        self.receipts.len()
    }

    /// Read a model field of any cell in the World as a u64 (the scalar shape).
    pub fn get_u64(&self, cell: &CellId, slot: Slot) -> u64 {
        crate::applet::CellModel::from_ledger(self.engine.ledger(), cell).field_u64(slot)
    }

    /// **Compose a multi-cell story** — author `steps` spanning the author's cells (and
    /// reaching outward via grants) as a sequence of cap-gated verified turns.
    ///
    /// THE CAP TOOTH, generalised + ATOMIC pre-screen (the all-or-nothing face):
    ///
    /// 1. PRE-SCREEN every step against `held` (the authority tooth — `is_attenuation`)
    ///    AND the author's scope (the scope tooth — every touched cell must be held; a
    ///    `MintCard` grows the projected scope so a later leg can touch the cell it
    ///    mints). A granted cap's `permissions` is ALSO checked against `held` (no
    ///    granting authority you lack). ANY over-reach ⇒ [`ComposeError::OverReach`]
    ///    and NOTHING is committed — no turn for ANY leg, no partial commit of an
    ///    unauthorized leg.
    /// 2. Only when EVERY step clears, commit each leg as its OWN verified turn (the
    ///    chain head threaded, the fee stamped), agent = the author cell, collecting
    ///    the real receipts. A `MintCard` adds its new cell to the live scope.
    ///
    /// Returns the [`Composition`] (every leg's receipt + the minted cell ids) on full
    /// success.
    pub fn compose(&mut self, steps: Vec<Step>) -> Result<Composition, ComposeError> {
        // ── (1) ATOMIC PRE-SCREEN — refuse any over-reach before ANY turn commits. ──
        // We project the scope forward (a MintCard adds the cell it WILL create), so a
        // story may mint-then-write its own new cell, but may NOT touch a foreign cell.
        let mut projected_scope: BTreeSet<CellId> = self.held_cells.clone();
        for (i, step) in steps.iter().enumerate() {
            // 1a. authority tooth: required ⊑ held.
            if !dregg_cell::is_attenuation(&self.held, step.required()) {
                return Err(ComposeError::OverReach {
                    step: i,
                    reason: format!(
                        "step '{}' requires an authority not narrower-or-equal to held",
                        step.method()
                    ),
                });
            }
            // 1b. scope tooth + leg-specific checks.
            match step {
                Step::MintCard {
                    public_key,
                    token_id,
                    ..
                } => {
                    // The minted cell joins the projected scope for later legs.
                    projected_scope.insert(CellId::derive_raw(public_key, token_id));
                }
                Step::SetField { cell, .. } => {
                    if !projected_scope.contains(cell) {
                        return Err(ComposeError::OverReach {
                            step: i,
                            reason: format!(
                                "set_field touches cell {cell} outside the author's held scope"
                            ),
                        });
                    }
                }
                Step::GrantCap { from, cap, .. } => {
                    if !projected_scope.contains(from) {
                        return Err(ComposeError::OverReach {
                            step: i,
                            reason: format!(
                                "grant issues FROM cell {from} outside the author's held scope"
                            ),
                        });
                    }
                    // You cannot grant authority you do not hold: the granted cap's
                    // permissions must be narrower-or-equal to `held`.
                    if !dregg_cell::is_attenuation(&self.held, &cap.permissions) {
                        return Err(ComposeError::OverReach {
                            step: i,
                            reason: "grant hands over an authority wider than held".into(),
                        });
                    }
                }
            }
        }

        // ── (2) COMMIT — every leg cleared; commit each as its own verified turn. ──
        let mut receipts = Vec::with_capacity(steps.len());
        let mut minted = Vec::new();
        for (i, step) in steps.into_iter().enumerate() {
            let (receipt, new_cell) = self
                .commit_step(step)
                .map_err(|reason| ComposeError::Executor { step: i, reason })?;
            if let Some(id) = new_cell {
                self.held_cells.insert(id);
                minted.push(id);
            }
            receipts.push(receipt);
        }

        Ok(Composition { receipts, minted })
    }

    /// Commit ONE leg as a real verified turn (agent = the author cell, chain head
    /// threaded, fee stamped). Returns the receipt and, for a `MintCard`, the id of the
    /// cell it created. The cap tooth has ALREADY cleared in the pre-screen.
    fn commit_step(&mut self, step: Step) -> Result<(TurnReceipt, Option<CellId>), String> {
        let method = step.method();
        // The author cell's current nonce drives the turn (it is the agent).
        let nonce =
            crate::applet::CellModel::from_ledger(self.engine.ledger(), &self.author).nonce();

        let mut action = ActionBuilder::new_unchecked_for_tests(self.author, method, self.author);
        let mut new_cell: Option<CellId> = None;

        // A MintCard leg carries genesis configuration (open the new cell + seed its
        // model + give the author standing) applied AFTER the CreateCell turn commits —
        // single-custody genesis, the SAME seam `mint`/`Applet::with_cell_mut` use. We
        // capture what to configure here and apply it post-commit.
        let mut genesis: Option<(CellId, Vec<(Slot, FieldElement)>)> = None;

        match step {
            Step::MintCard {
                public_key,
                token_id,
                seed_fields,
                ..
            } => {
                // CreateCell mints a zero-balance cell (the executor refuses a non-zero
                // create balance). The new cell's open-permissions + genesis model +
                // the author's c-list standing are applied as GENESIS CONFIG right after
                // this turn commits (a cross-cell SetField/SetPermissions on a brand-new
                // cell in the SAME action would trip the executor's cross-cell tooth,
                // since standing does not yet exist and the new cell's default perms are
                // `Signature` until SetPermissions applies LAST — see module docs).
                let id = CellId::derive_raw(&public_key, &token_id);
                action = action.effect_create_cell(public_key, token_id, 0);
                new_cell = Some(id);
                genesis = Some((id, seed_fields));
            }
            Step::SetField {
                cell, slot, value, ..
            } => {
                action = action.effect_set_field(cell, slot as u64, value);
            }
            Step::GrantCap { from, to, cap, .. } => {
                action = action.effect_grant_capability(from, to, cap);
            }
        }

        // Bump the AUTHOR's nonce so each leg chains + the agent's progress witnesses.
        let action = action.effect_increment_nonce(self.author).build();

        let mut tb = TurnBuilder::new(self.author, nonce);
        tb.set_fee(10_000);
        if let Some(prev) = self.prev_receipt {
            tb.set_previous_receipt_hash(prev);
        }
        tb.add_action(action);
        let turn = tb.build();

        let receipt = self.engine.execute_turn(&turn).map_err(|e| e.to_string())?;

        // Post-commit genesis configuration of a freshly-minted card (single-custody):
        // open its permissions, seed its genesis model, and give the AUTHOR a c-list
        // access entry so later cross-cell legs have executor standing.
        if let Some((id, seed_fields)) = genesis {
            self.engine
                .ledger_mut()
                .update_with(&id, |c| {
                    c.permissions = open_permissions();
                    for (slot, value) in &seed_fields {
                        c.state.set_field(*slot, *value);
                    }
                })
                .map_err(|e| format!("genesis-config the minted card: {e}"))?;
            let author = self.author;
            self.engine
                .ledger_mut()
                .update_with(&author, |a| {
                    a.capabilities.grant(id, AuthRequired::None);
                })
                .map_err(|e| format!("grant the author standing over the minted card: {e}"))?;
        }

        let rh = receipt.receipt_hash();
        self.prev_receipt = Some(rh);
        self.receipts.push(rh);
        Ok((receipt, new_cell))
    }
}

/// Open (single-custody) permissions for an embedded author/minted cell — every slot
/// `AuthRequired::None`, so the executor admits the author's writes and the cap tooth
/// lives in deos-js (the SAME shape `applet::open_permissions` uses).
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

/// Build a plain bearer capability ref pointing at `target` with `permissions` (a
/// convenience for [`Step::GrantCap`] callers). Slot 0, no breadstuff/expiry/facet.
pub fn bearer_cap(target: CellId, permissions: AuthRequired) -> CapabilityRef {
    CapabilityRef {
        target,
        slot: 0,
        permissions,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
        provenance: dregg_cell::derivation::cap_provenance(
            &(target),
            (0),
            &dregg_cell::derivation::mint_provenance(),
            &[0u8; 32],
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::applet::pack_u64;

    fn pk(b: u8) -> [u8; 32] {
        let mut k = [0u8; 32];
        k[0] = b;
        k
    }
    fn tok(b: u8) -> [u8; 32] {
        let mut t = [0u8; 32];
        t[0] = b;
        t
    }

    /// THE KEYSTONE: a bounded author composes a multi-cell story (mint a card + set a
    /// field on it + grant a cap to a peer) spanning ≥2 cells. Every leg commits as a
    /// real verified turn, every receipt is attributed to the author, and the cap tooth
    /// held throughout.
    #[test]
    fn multi_cell_story_commits_across_cells() {
        // A peer the story will grant TO (foreign — not in the author's scope).
        let peer = CellId::derive_raw(&pk(9), &tok(9));
        let mut author = MultiCellAuthor::mint(
            pk(1),
            tok(1),
            // `Either` is the wide held authority (admits Signature/Proof grants below).
            AuthRequired::Either,
            &[],                // no pre-declared scope cards — this story MINTS its card.
            &[(pk(9), tok(9))], // one foreign peer to grant TO.
        );
        let author_id = author.author();
        let new_card = CellId::derive_raw(&pk(2), &tok(2));

        let story = vec![
            // leg 1: MINT a new card (a second cell), seeded with model field 0 = 7.
            Step::MintCard {
                public_key: pk(2),
                token_id: tok(2),
                seed_fields: vec![(0, pack_u64(7))],
                required: AuthRequired::Signature,
            },
            // leg 2: SET a field on the JUST-MINTED card (in-scope after the mint).
            Step::SetField {
                cell: new_card,
                slot: 1,
                value: pack_u64(42),
                required: AuthRequired::Signature,
            },
            // leg 3: SET a field on the AUTHOR's own cell (a third write, in-scope).
            Step::SetField {
                cell: author_id,
                slot: 2,
                value: pack_u64(99),
                required: AuthRequired::Signature,
            },
            // leg 4: GRANT a cap FROM the author TO the peer (the outward reach).
            Step::GrantCap {
                from: author_id,
                to: peer,
                cap: bearer_cap(new_card, AuthRequired::Signature),
                required: AuthRequired::Signature,
            },
        ];

        let comp = author.compose(story).expect("the bounded story commits");

        // Four legs ⇒ four verified turns ⇒ four receipts, all in order.
        assert_eq!(comp.len(), 4, "one verified turn per leg");
        assert_eq!(author.receipt_count(), 4);
        // The minted card was reported and joined the author's scope.
        assert_eq!(comp.minted, vec![new_card]);
        assert!(
            author.holds_cell(&new_card),
            "the minted card is now in scope"
        );
        assert!(author.holds_cell(&author_id));
        assert!(!author.holds_cell(&peer), "the peer stays foreign");

        // Every receipt is attributed to the AUTHOR cell (the agent of every turn).
        for r in &comp.receipts {
            assert_eq!(r.agent, author_id, "every leg is the author's turn");
        }

        // The writes landed across cells: card field 0 = 7 (seed), field 1 = 42; the
        // author cell field 2 = 99. A re-read off the live ledger proves it.
        assert_eq!(author.get_u64(&new_card, 0), 7, "the seed model survived");
        assert_eq!(
            author.get_u64(&new_card, 1),
            42,
            "leg-2 write landed on the new card"
        );
        assert_eq!(
            author.get_u64(&author_id, 2),
            99,
            "leg-3 write landed on the author"
        );
    }

    /// THE RED-TEAM LEG: a step that reaches PAST the author's `held` scope (a SetField
    /// on a foreign vessel's cell) is refused IN-BAND — no turn for ANY leg, no partial
    /// commit. The cap tooth held.
    #[test]
    fn scope_over_reach_refused_in_band_no_partial_commit() {
        let foreign = CellId::derive_raw(&pk(9), &tok(9));
        let mut author = MultiCellAuthor::mint(
            pk(1),
            tok(1),
            AuthRequired::Either,
            &[],                // no scope cards.
            &[(pk(9), tok(9))], // the foreign vessel exists but is NOT in scope.
        );
        let author_id = author.author();

        let story = vec![
            // leg 1: a perfectly authorized write on the author's own cell.
            Step::SetField {
                cell: author_id,
                slot: 0,
                value: pack_u64(1),
                required: AuthRequired::Signature,
            },
            // leg 2: OVER-REACH — a write on a foreign vessel's cell (out of scope).
            Step::SetField {
                cell: foreign,
                slot: 0,
                value: pack_u64(2),
                required: AuthRequired::Signature,
            },
        ];

        let err = author
            .compose(story)
            .expect_err("the over-reach is refused");
        match err {
            ComposeError::OverReach { step, .. } => {
                assert_eq!(step, 1, "the SECOND leg is the over-reach");
            }
            other => panic!("expected an OverReach refusal, got {other}"),
        }

        // NO partial commit: the AUTHORIZED leg-1 turn did NOT land either — the whole
        // story aborts before ANY turn commits (the all-or-nothing pre-screen).
        assert_eq!(
            author.receipt_count(),
            0,
            "nothing committed — no partial leg"
        );
        assert_eq!(
            author.get_u64(&author_id, 0),
            0,
            "leg-1 write never happened"
        );
    }

    /// THE AUTHORITY TOOTH: a step whose `required` authority is NOT narrower-or-equal
    /// to the author's `held` is refused in-band (the exact `is_attenuation` tooth
    /// `Applet::fire` uses), no turn, no partial commit.
    #[test]
    fn authority_over_reach_refused_in_band() {
        // A NARROW author: holds only `Signature`. It cannot author a step requiring
        // the wider `Either`.
        let mut author = MultiCellAuthor::mint(pk(1), tok(1), AuthRequired::Signature, &[], &[]);
        let author_id = author.author();

        let story = vec![Step::SetField {
            cell: author_id,
            slot: 0,
            value: pack_u64(5),
            required: AuthRequired::Either, // wider than held Signature ⇒ over-reach.
        }];

        let err = author
            .compose(story)
            .expect_err("the authority over-reach is refused");
        assert!(matches!(err, ComposeError::OverReach { step: 0, .. }));
        assert_eq!(author.receipt_count(), 0, "nothing committed");
    }

    /// THE GRANT TOOTH: an author cannot grant authority WIDER than it holds — a
    /// `GrantCap` whose cap permissions exceed `held` is refused in-band.
    #[test]
    fn cannot_grant_authority_wider_than_held() {
        let peer = CellId::derive_raw(&pk(9), &tok(9));
        let mut author = MultiCellAuthor::mint(
            pk(1),
            tok(1),
            AuthRequired::Signature, // narrow.
            &[],
            &[(pk(9), tok(9))],
        );
        let author_id = author.author();

        let story = vec![Step::GrantCap {
            from: author_id,
            to: peer,
            // Granting `Either` (wider than held Signature) ⇒ refused.
            cap: bearer_cap(author_id, AuthRequired::Either),
            required: AuthRequired::Signature,
        }];

        let err = author
            .compose(story)
            .expect_err("granting wider-than-held is refused");
        assert!(matches!(err, ComposeError::OverReach { step: 0, .. }));
        assert_eq!(author.receipt_count(), 0);
    }
}
