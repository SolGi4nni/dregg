//! **The interactive ViewNode loop, in Discord** — a Discord button press → a REAL
//! cap-gated verified dregg turn → the card embed re-renders from the new committed
//! state.
//!
//! The landed `69e15322` backend gave the bot the *projection* half: a `deos_view`
//! [`ViewNode`] card renders to a serenity embed + button components, and each
//! [`ViewNode::Button`]'s affordance `{turn, arg}` rides back in the component
//! custom-id as `deosturn:<turn>:<arg>` ([`deos_view::discord::affordance_custom_id`]).
//! This module is the *interactive* half: it DECODES that custom-id
//! ([`deos_view::discord::parse_affordance_id`]) and FIRES it as a genuine verified
//! turn, then re-renders the SAME card with the advanced bound value.
//!
//! ## What is real
//!
//! Firing is the EXACT shape the native applet ([`deos_js::applet::Applet::fire`])
//! commits, reproduced here gpui-/deos-js-FREE over the SDK's embedded verified
//! executor ([`dregg_sdk::embed::DreggEngine`]):
//!
//!   1. the affordance resolves (an unknown direction = no turn);
//!   2. the **cap tooth runs in-band** — the held authority must satisfy the
//!      affordance's `required` ([`dregg_cell::is_attenuation`]); an under-authorized
//!      press commits NOTHING (the anti-ghost tooth);
//!   3. the writes are a pure function of the LIVE model (the cell state);
//!   4. a real verified turn executes on the embedded executor, leaving a genuine
//!      [`TurnReceipt`]; the new model is read straight back off the committed ledger
//!      and the card re-renders (the bound value updates).
//!
//! The applet cell's principal is the pressing user's custodial cipherclerk
//! ([`crate::cipherclerk::UserCipherclerk`]), so the turn is tied to — and cap-gated
//! to — the pressing user's dregg identity: each user drives their OWN card.
//!
//! ## The seam (named)
//!
//! The model lives on a per-(user, card) **in-process** embedded executor held in
//! [`CardApplets`] (the SAME in-process attested substance `deos_surface.rs` names its
//! seam at): the verified turn + receipt are genuine, but the state is process-local
//! (lost on restart) rather than committed to the live devnet node. Driving the turn
//! all the way to the node's executor (so the receipt is the node's own) is the same
//! dispatch seam every bot op touches the executor at — the gate that decides *whether
//! the turn may fire at all* is the real `is_attenuation`, in-band, HERE.

use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;

use serenity::all::{
    ComponentInteraction, Context, CreateEmbedFooter, CreateInteractionResponse,
    CreateInteractionResponseMessage,
};

use dregg_cell::state::{FieldElement, STATE_SLOTS};
use dregg_cell::{AuthRequired, Cell, Ledger, Permissions, is_attenuation};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_turn::TurnReceipt;
use dregg_turn::builder::{ActionBuilder, TurnBuilder};
use dregg_types::CellId;

use deos_view::ViewNode;
use deos_view::discord::{DiscordCard, parse_affordance_id, render_card};

use crate::cipherclerk::UserCipherclerk;
use crate::embeds;

/// A model slot (a cell-state index). The card's bound values read these.
type Slot = usize;

/// Pack a u64 into a [`FieldElement`] (little-endian low 8 bytes) — the scalar shape
/// of the card's bound model (a tally count), matching the native applet's packing.
fn pack_u64(v: u64) -> FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// Read a u64 back out of a [`FieldElement`].
fn unpack_u64(fe: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

/// A read-only projection of the card applet's MODEL (the cell's live state) — the
/// positions of the polynomial-functor interface, read off the embedded ledger.
pub struct CardModel {
    fields: BTreeMap<Slot, FieldElement>,
    nonce: u64,
}

impl CardModel {
    fn from_ledger(ledger: &Ledger, cell_id: &CellId) -> Self {
        let mut fields = BTreeMap::new();
        let mut nonce = 0;
        if let Some(cell) = ledger.get(cell_id) {
            for slot in 0..STATE_SLOTS {
                if let Some(fe) = cell.state.get_field(slot) {
                    if *fe != [0u8; 32] {
                        fields.insert(slot, *fe);
                    }
                }
            }
            nonce = cell.state.nonce();
        }
        CardModel { fields, nonce }
    }

    /// Read a model field as a u64 (the card's scalar shape).
    pub fn field_u64(&self, slot: Slot) -> u64 {
        unpack_u64(self.fields.get(&slot).unwrap_or(&[0u8; 32]))
    }

    /// The cell's nonce — bumps once per committed turn.
    pub fn nonce(&self) -> u64 {
        self.nonce
    }
}

/// A named **affordance** — a direction of the card's interface. Firing it commits ONE
/// cap-gated verified turn. `apply` is a *pure* function of the live model producing the
/// (slot, new-value) writes; `required` is the authority the press must satisfy.
struct CardAffordance {
    required: AuthRequired,
    apply: Box<dyn Fn(&CardModel, i64) -> Vec<(Slot, FieldElement)> + Send>,
}

/// Why firing an affordance failed (the same three faces the native applet names).
#[derive(Debug)]
pub enum FireError {
    /// No affordance with that name is registered (an undefined direction).
    UnknownAffordance(String),
    /// The cap tooth refused: the held authority does not satisfy `required`.
    Unauthorized { affordance: String },
    /// The embedded executor rejected the (authorized) turn.
    Executor(String),
}

impl std::fmt::Display for FireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FireError::UnknownAffordance(n) => {
                write!(
                    f,
                    "unknown affordance `{n}` (no such direction on this card)"
                )
            }
            FireError::Unauthorized { affordance } => write!(
                f,
                "`{affordance}` was REFUSED by the real `is_attenuation` cap-gate (never run)"
            ),
            FireError::Executor(r) => write!(f, "the verified executor rejected the turn: {r}"),
        }
    }
}
impl std::error::Error for FireError {}

/// One sovereign card cell on an embedded verified executor: its state is the model,
/// its affordances are the only mutators (each a cap-gated verified turn).
pub struct CardApplet {
    engine: DreggEngine,
    cell: CellId,
    /// The driver's held authority (what fires are checked against). For a user's own
    /// card this is the root right ([`AuthRequired::None`]); the cap tooth still REFUSES
    /// an affordance whose `required` is stricter than what is held.
    held: AuthRequired,
    affordances: BTreeMap<String, CardAffordance>,
    /// The card's view-tree (renderer-independent); rendered to a Discord embed.
    tree: ViewNode,
    /// The embed title.
    title: String,
    /// The model slots the card's `bind` nodes read, in tree-walk order.
    bind_slots: Vec<Slot>,
    /// The chain head, threaded into each turn's `previous_receipt_hash`.
    prev_receipt: Option<[u8; 32]>,
    /// Every committed receipt hash, in order (the audit tape).
    receipts: Vec<[u8; 32]>,
}

impl CardApplet {
    /// The canonical **tally card**: a counter bound to slot 0 with `+1`/`−1` buttons
    /// firing the `bump` affordance and a `reset` button firing the owner-only `reset`
    /// affordance. The exact shape `deos-view`'s renderer doc cites — authored once,
    /// rendered to a Discord embed, driven by real verified turns.
    pub fn tally(public_key: [u8; 32], token_id: [u8; 32], name: &str) -> Self {
        const COUNT: Slot = 0;

        let tree = ViewNode::VStack(vec![
            ViewNode::Row(vec![
                ViewNode::Text(name.to_string()),
                ViewNode::Bind {
                    slot: COUNT,
                    label: "count: ".to_string(),
                },
                ViewNode::Button {
                    label: "+1".to_string(),
                    turn: "bump".to_string(),
                    arg: 1,
                },
                ViewNode::Button {
                    label: "\u{2212}1".to_string(),
                    turn: "bump".to_string(),
                    arg: -1,
                },
            ]),
            ViewNode::Row(vec![
                ViewNode::Text("admin".to_string()),
                ViewNode::Button {
                    label: "reset".to_string(),
                    turn: "reset".to_string(),
                    arg: 0,
                },
            ]),
        ]);

        let mut affordances: BTreeMap<String, CardAffordance> = BTreeMap::new();
        // `bump`: any authenticated holder (Signature) — count := max(0, count + arg).
        affordances.insert(
            "bump".to_string(),
            CardAffordance {
                required: AuthRequired::Signature,
                apply: Box::new(|model, arg| {
                    let cur = model.field_u64(COUNT) as i64;
                    let next = (cur + arg).max(0) as u64;
                    vec![(COUNT, pack_u64(next))]
                }),
            },
        );
        // `reset`: the owner-only (root) direction — count := 0. With a non-root held
        // authority this is REFUSED in-band (the anti-ghost tooth).
        affordances.insert(
            "reset".to_string(),
            CardAffordance {
                required: AuthRequired::None,
                apply: Box::new(|_model, _arg| vec![(COUNT, pack_u64(0))]),
            },
        );

        Self::mint(
            public_key,
            token_id,
            &[(COUNT, pack_u64(0))],
            affordances,
            tree,
            name.to_string(),
            vec![COUNT],
            // The user owns their own card → holds the root right; the cap tooth still
            // bites for an affordance stricter than what is held (proved in tests).
            AuthRequired::None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn mint(
        public_key: [u8; 32],
        token_id: [u8; 32],
        seed_fields: &[(Slot, FieldElement)],
        affordances: BTreeMap<String, CardAffordance>,
        tree: ViewNode,
        title: String,
        bind_slots: Vec<Slot>,
        held: AuthRequired,
    ) -> Self {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        // The local drive path defers the witness (Symbolic): the state transition fully
        // applies and every gate (authority/conservation/freshness) runs identically; the
        // publishable commitment collapses to real Merkle roots only at a publish
        // boundary. The cheap local end of the Φ×WitnessMode spectrum (as the applet).
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);

        let mut cell = Cell::with_balance(public_key, token_id, 1_000_000);
        cell.permissions = open_permissions();
        for (slot, value) in seed_fields {
            cell.state.set_field(*slot, *value);
        }
        let cell_id = cell.id();
        engine
            .ledger_mut()
            .insert_cell(cell)
            .expect("seed the card-applet cell onto the embedded ledger");

        CardApplet {
            engine,
            cell: cell_id,
            held,
            affordances,
            tree,
            title,
            bind_slots,
            prev_receipt: None,
            receipts: Vec::new(),
        }
    }

    /// A witnessed read of the live model off the embedded ledger.
    fn model(&self) -> CardModel {
        CardModel::from_ledger(self.engine.ledger(), &self.cell)
    }

    /// Read one bound model field as a u64 (the card's scalar shape).
    pub fn get_u64(&self, slot: Slot) -> u64 {
        self.model().field_u64(slot)
    }

    /// The bound values, in tree-walk order — exactly what [`render_card`] reads to paint
    /// the live `bind` nodes.
    pub fn bind_values(&self) -> Vec<u64> {
        let model = self.model();
        self.bind_slots
            .iter()
            .map(|s| model.field_u64(*s))
            .collect()
    }

    /// Render the card to a Discord [`DiscordCard`] from the CURRENT committed state — the
    /// SAME renderer the desktop/web/seL4 backends share (the bound values are the live
    /// model).
    pub fn render(&self) -> DiscordCard {
        render_card(&self.title, &self.tree, &self.bind_values())
    }

    /// **Fire an affordance** — commit ONE cap-gated verified turn on the embedded
    /// executor (the same shape [`deos_js::applet::Applet::fire`] commits):
    ///
    /// 1. resolve the affordance (unknown = no turn);
    /// 2. CAP TOOTH in-band — `held` must satisfy `required` ([`is_attenuation`]); refused
    ///    ⇒ nothing committed;
    /// 3. writes = pure function of the live model;
    /// 4. build + execute the verified turn (the affordance name is the action method, the
    ///    chain head threaded); on success a real [`TurnReceipt`] returns and the new model
    ///    is on the ledger.
    pub fn fire(&mut self, affordance: &str, arg: i64) -> Result<TurnReceipt, FireError> {
        let aff = self
            .affordances
            .get(affordance)
            .ok_or_else(|| FireError::UnknownAffordance(affordance.to_string()))?;

        // (2) the real `is_attenuation`, in-band. Refused ⇒ nothing committed.
        if !is_attenuation(&self.held, &aff.required) {
            return Err(FireError::Unauthorized {
                affordance: affordance.to_string(),
            });
        }

        // (3) writes = pure function of the live model.
        let model = self.model();
        let writes = (aff.apply)(&model, arg);
        let nonce = model.nonce();

        // (4) build + execute the verified turn. Single-custody embedded world: the action
        // carries the affordance name as its method and `Unchecked` authorization (the cap
        // tooth already ran in-band above); the agent is the card cell.
        let mut action = ActionBuilder::new_unchecked_for_tests(self.cell, affordance, self.cell);
        for (slot, value) in writes {
            action = action.effect_set_field(self.cell, slot, value);
        }
        let action = action.effect_increment_nonce(self.cell).build();

        let mut tb = TurnBuilder::new(self.cell, nonce);
        tb.set_fee(10_000);
        if let Some(prev) = self.prev_receipt {
            tb.set_previous_receipt_hash(prev);
        }
        tb.add_action(action);
        let turn = tb.build();

        let receipt = self
            .engine
            .execute_turn(&turn)
            .map_err(|e| FireError::Executor(e.to_string()))?;

        let rh = receipt.receipt_hash();
        self.prev_receipt = Some(rh);
        self.receipts.push(rh);
        Ok(receipt)
    }

    /// How many verified turns have committed (the audit-tape length).
    pub fn receipt_count(&self) -> usize {
        self.receipts.len()
    }
}

/// Open (single-custody) permissions for an embedded card-applet cell — the same shape
/// the native applet seeds (all directions `None`; the affordance-level cap tooth is the
/// real gate).
fn open_permissions() -> Permissions {
    Permissions {
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

/// The per-(user, card) registry of live embedded card applets — the in-process
/// substance the interactive loop drives (the named seam). Keyed by Discord user id +
/// card name so each user drives their OWN card with its OWN receipt chain.
#[derive(Default)]
pub struct CardApplets {
    map: Mutex<HashMap<(u64, String), CardApplet>>,
}

/// A rendered card plus the receipt readout of the turn that produced it.
pub struct RenderedCard {
    /// The embed + button components to post / update.
    pub card: DiscordCard,
    /// Short hex of the firing turn's receipt hash (empty for a no-fire render).
    pub receipt_short: String,
    /// How many verified turns this card has fired.
    pub receipt_count: usize,
    /// The card's current bound count (slot 0).
    pub count: u64,
}

impl CardApplets {
    /// An empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get-or-create the user's tally card, render it WITHOUT firing (the entry point a
    /// `/card` command posts).
    pub fn ensure_and_render(&self, user_id: u64, cclerk: &UserCipherclerk) -> RenderedCard {
        let mut map = self.map.lock().expect("card-applet registry mutex");
        let applet = map
            .entry((user_id, "tally".to_string()))
            .or_insert_with(|| new_tally(cclerk));
        RenderedCard {
            card: applet.render(),
            receipt_short: String::new(),
            receipt_count: applet.receipt_count(),
            count: applet.get_u64(0),
        }
    }

    /// **Fire `turn(arg)` on the user's card and re-render** — the parse→fire→re-render
    /// loop's core. The cap gate is the real `is_attenuation`, in-band; an under-authorized
    /// or unknown press is [`Err`] (never committed).
    pub fn fire_and_render(
        &self,
        user_id: u64,
        cclerk: &UserCipherclerk,
        turn: &str,
        arg: i64,
    ) -> Result<RenderedCard, FireError> {
        let mut map = self.map.lock().expect("card-applet registry mutex");
        let applet = map
            .entry((user_id, "tally".to_string()))
            .or_insert_with(|| new_tally(cclerk));
        let receipt = applet.fire(turn, arg)?;
        Ok(RenderedCard {
            card: applet.render(),
            receipt_short: short_hash(&receipt.receipt_hash()),
            receipt_count: applet.receipt_count(),
            count: applet.get_u64(0),
        })
    }
}

/// Build the user's tally card cell, its principal bound to the user's custodial
/// cipherclerk (so the verified turn is tied to the pressing user's dregg identity).
fn new_tally(cclerk: &UserCipherclerk) -> CardApplet {
    CardApplet::tally(cclerk.app.public_key().0, cclerk.cell_id_bytes(), "Tally")
}

/// Short hex of a 32-byte hash (first 12 hex chars) for the embed footer.
fn short_hash(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(12);
    for b in bytes.iter().take(6) {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// The embed footer naming the verified turn that produced the rendered card.
fn turn_footer(turn: &str, rendered: &RenderedCard) -> CreateEmbedFooter {
    CreateEmbedFooter::new(format!(
        "verified turn · {turn} · receipt {} · turns fired: {}",
        rendered.receipt_short, rendered.receipt_count
    ))
}

/// **Handle a `deosturn:<turn>:<arg>` component press** — the interactive ViewNode loop
/// in Discord:
///
///   1. decode the affordance with [`parse_affordance_id`] (a non-`deosturn:` id returns
///      `None` and is ignored — the router gives those to other handlers);
///   2. resolve the pressing user's custodial cipherclerk (the cap-gated identity);
///   3. fire it as a REAL cap-gated verified turn on the user's card applet;
///   4. UPDATE the message in place with the re-rendered card (the bound value advances)
///      — or, on a refusal (the anti-ghost tooth), reply ephemerally with the reason.
pub async fn handle_deosturn_component(
    ctx: &Context,
    component: &ComponentInteraction,
    state: &crate::BotState,
) {
    let Some((turn, arg)) = parse_affordance_id(&component.data.custom_id) else {
        return;
    };

    let user_id = component.user.id.get();
    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);

    let response = match state
        .card_applets
        .fire_and_render(user_id, &cclerk, &turn, arg)
    {
        Ok(rendered) => {
            let embed = rendered
                .card
                .embed
                .clone()
                .footer(turn_footer(&turn, &rendered));
            CreateInteractionResponse::UpdateMessage(
                CreateInteractionResponseMessage::new()
                    .embed(embed)
                    .components(rendered.card.components.clone()),
            )
        }
        Err(e) => CreateInteractionResponse::Message(
            CreateInteractionResponseMessage::new()
                .embed(embeds::error_embed(
                    "Turn Refused (anti-ghost)",
                    &e.to_string(),
                ))
                .ephemeral(true),
        ),
    };

    let _ = component.create_response(&ctx.http, response).await;
}

/// The embed-with-footer for an initial (`/card`) post — re-used by the command handler.
pub fn render_with_footer(rendered: &RenderedCard) -> serenity::all::CreateEmbed {
    rendered
        .card
        .embed
        .clone()
        .footer(CreateEmbedFooter::new(format!(
            "interactive card · {} verified turn(s) fired · press a button to fire one",
            rendered.receipt_count
        )))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_cclerk() -> UserCipherclerk {
        UserCipherclerk::derive(&[7u8; 32], 4242, [0u8; 32])
    }

    // The custom-id the backend mints round-trips back into its affordance — the decode
    // half of the loop (`deosturn:<turn>:<arg>` ⇄ `(turn, arg)`).
    #[test]
    fn deosturn_custom_id_round_trips_to_its_affordance() {
        let id = deos_view::discord::affordance_custom_id("bump", -1);
        assert_eq!(id, "deosturn:bump:-1");
        assert_eq!(parse_affordance_id(&id), Some(("bump".to_string(), -1)));
        // A non-ours id is ignored (the router hands it elsewhere).
        assert_eq!(parse_affordance_id("deos:abcd:approve"), None);
    }

    // THE FULL LOOP: parse → fire a REAL verified turn → re-render from the new committed
    // state, the bound value advanced. The headline this module exists to make real.
    #[test]
    fn parse_fire_rerender_advances_the_bound_value() {
        let cclerk = test_cclerk();
        let mut applet = new_tally(&cclerk);

        // Initial render: count 0 (the seeded model).
        let before = render_card(&applet.title, &applet.tree, &applet.bind_values());
        let before_json = serde_json::to_value(&before.embed).unwrap();
        let before_val = before_json["fields"][0]["value"].as_str().unwrap();
        assert!(
            before_val.contains("count: 0"),
            "starts at 0, got {before_val}"
        );
        assert_eq!(applet.receipt_count(), 0);

        // Decode `deosturn:bump:1` and FIRE it — a real verified turn leaving a receipt.
        let (turn, arg) =
            parse_affordance_id(&deos_view::discord::affordance_custom_id("bump", 1)).unwrap();
        let receipt = applet.fire(&turn, arg).expect("an authorized bump fires");
        assert_eq!(receipt.receipt_hash().len(), 32, "a real receipt returned");
        assert_eq!(applet.receipt_count(), 1, "the audit tape grew by one turn");
        assert_eq!(applet.get_u64(0), 1, "the committed model advanced to 1");

        // RE-RENDER from the new committed state — the bound value updated.
        let after = render_card(&applet.title, &applet.tree, &applet.bind_values());
        let after_json = serde_json::to_value(&after.embed).unwrap();
        let after_val = after_json["fields"][0]["value"].as_str().unwrap();
        assert!(
            after_val.contains("count: 1"),
            "re-rendered to 1, got {after_val}"
        );

        // The re-rendered buttons still carry routable affordances (the loop continues).
        let rows = serde_json::to_value(&after.components).unwrap();
        let plus = &rows[0]["components"][0]["custom_id"];
        assert_eq!(plus, "deosturn:bump:1");
    }

    // The receipt chain threads across presses (each turn chains the previous receipt).
    #[test]
    fn successive_fires_chain_and_accumulate() {
        let cclerk = test_cclerk();
        let mut applet = new_tally(&cclerk);
        for _ in 0..3 {
            applet.fire("bump", 1).expect("bump fires");
        }
        assert_eq!(applet.get_u64(0), 3);
        assert_eq!(applet.receipt_count(), 3);
        // `−1` decrements; the count never goes below 0 (saturating model).
        applet.fire("bump", -1).expect("decrement fires");
        assert_eq!(applet.get_u64(0), 2);
        for _ in 0..10 {
            applet.fire("bump", -1).expect("decrement fires");
        }
        assert_eq!(applet.get_u64(0), 0, "the count saturates at 0");
    }

    // The owner clears the root-gated `reset`; an under-authorized holder is REFUSED
    // in-band (the anti-ghost tooth — nothing committed).
    #[test]
    fn cap_tooth_refuses_an_underauthorized_fire() {
        let cclerk = test_cclerk();

        // The user owns their card (held = None / root): `reset` (req None) clears.
        let mut owner = new_tally(&cclerk);
        owner.fire("bump", 5).unwrap();
        assert_eq!(owner.get_u64(0), 5);
        owner.fire("reset", 0).expect("the owner may reset");
        assert_eq!(owner.get_u64(0), 0, "reset zeroed the committed model");

        // A weaker holder (Signature, not root) is REFUSED `reset` (req None) — nothing
        // commits — but may still `bump` (req Signature).
        let mut member =
            CardApplet::tally(cclerk.app.public_key().0, cclerk.cell_id_bytes(), "Tally");
        member.held = AuthRequired::Signature;
        member.fire("bump", 1).expect("a member may bump");
        assert_eq!(member.get_u64(0), 1);
        let refused = member.fire("reset", 0);
        assert!(
            matches!(refused, Err(FireError::Unauthorized { .. })),
            "reset must be refused for a non-root holder, got {refused:?}"
        );
        assert_eq!(member.get_u64(0), 1, "a refused fire committed nothing");
    }

    // An unknown affordance is no turn (an undefined direction).
    #[test]
    fn unknown_affordance_is_no_turn() {
        let cclerk = test_cclerk();
        let mut applet = new_tally(&cclerk);
        assert!(matches!(
            applet.fire("nonexistent", 0),
            Err(FireError::UnknownAffordance(_))
        ));
        assert_eq!(applet.receipt_count(), 0, "no turn committed");
    }
}
