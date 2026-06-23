//! The **applet** — ember's factoring made concrete over the embedded verified executor.
//!
//! A `cell` is a SOVEREIGNTY/DISTRIBUTION boundary, NOT a DOM node. ONE cell is a
//! whole interactive subgraph (an "applet"). The cell is a polynomial-functor
//! interface:
//!
//!   - **positions** = the views/states it presents (the cell's *model* = its state);
//!   - **directions** = the affordances (named turns) it accepts.
//!
//! The applet's MODEL is the cell's state on the [`DreggEngine`] ledger. The ONLY
//! mutators are its affordances = cap-gated *verified turns* (each leaves a real
//! [`TurnReceipt`]). Ephemeral view-state (draft text, hover) is held [`ViewState`]
//! side and NEVER touches the ledger — no turn.
//!
//! Applets COMPOSE via transclusion (the cap-gated, provenanced distributed DOM):
//! [`Applet::transclude`] reuses the REAL `WholeCellTransclusion` primitive
//! (`starbridge-web-surface`'s `TranscludedField` — content → commitment → receipt →
//! receipt-stream-root → quorum) so a compose carries verified provenance, never a
//! raw copy.

use std::collections::BTreeMap;

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_turn::builder::{ActionBuilder, TurnBuilder};
use dregg_turn::TurnReceipt;
use dregg_types::CellId;

use starbridge_web_surface::transclusion::{Provenance, TranscludedField};
use starbridge_web_surface::web_of_cells::{DreggUri, WebOfCells};

/// A named field of the applet's *model* (= cell state). Slots map to cell-state
/// indices; the value is a 32-byte field element (we pack a u64 into the low bytes
/// for the counter/todo-count shape).
pub type Slot = usize;

/// Pack a u64 into a [`FieldElement`] (little-endian low 8 bytes) — the model's
/// scalar shape for the spike's counter.
pub fn pack_u64(v: u64) -> FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// Read a u64 back out of a [`FieldElement`].
pub fn unpack_u64(fe: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

/// An **affordance** — a named direction of the polynomial-functor interface. Firing
/// it commits ONE cap-gated verified turn. The `apply` closure is a *pure* function
/// of the live model (the cell state) producing the field-writes the turn carries;
/// `required` is the authority the fire must satisfy (the cap tooth).
pub struct Affordance {
    pub name: String,
    pub required: AuthRequired,
    /// Pure: live model → the (slot, new-value) writes this affordance produces.
    /// `arg` is the JS-supplied argument (e.g. the increment amount).
    pub apply: Box<dyn Fn(&CellModel, i64) -> Vec<(Slot, FieldElement)>>,
}

/// A read-only view of the applet's MODEL (the cell's live state), the positions of
/// the polynomial functor. Built from the engine ledger on demand.
pub struct CellModel {
    fields: BTreeMap<Slot, FieldElement>,
    nonce: u64,
}

impl CellModel {
    /// Read a model field as a raw element.
    pub fn field(&self, slot: Slot) -> FieldElement {
        self.fields.get(&slot).copied().unwrap_or([0u8; 32])
    }
    /// Read a model field as a u64 (the scalar shape).
    pub fn field_u64(&self, slot: Slot) -> u64 {
        unpack_u64(&self.field(slot))
    }
    /// The cell's nonce — bumps once per committed turn (the "how many affordances
    /// have fired" witness).
    pub fn nonce(&self) -> u64 {
        self.nonce
    }
}

/// EPHEMERAL view-state — draft text, hover, focus. A plain in-memory map. Setting it
/// is a plain JS/Rust change that does NOT touch the ledger (NO turn, NO receipt).
/// This is the load-bearing distinction: ephemeral UI state is NOT cell state.
#[derive(Default)]
pub struct ViewState {
    pub map: BTreeMap<String, String>,
}

/// Why firing an affordance failed.
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
            FireError::UnknownAffordance(n) => write!(f, "unknown affordance '{n}'"),
            FireError::Unauthorized { affordance } => {
                write!(f, "affordance '{affordance}' refused by the cap-gate")
            }
            FireError::Executor(r) => write!(f, "turn refused by the embedded executor: {r}"),
        }
    }
}
impl std::error::Error for FireError {}

/// An **applet** — one sovereign cell on the embedded verified executor, presenting
/// its state as the model and its affordances as the only mutators.
pub struct Applet {
    /// The embedded verified executor — the substance. ONE turn here leaves a REAL
    /// `TurnReceipt`; reads are witnessed off the live ledger.
    engine: DreggEngine,
    /// The applet's cell — the sovereignty boundary, the agent of every turn.
    cell: CellId,
    public_key: [u8; 32],
    token_id: [u8; 32],
    affordances: BTreeMap<String, Affordance>,
    /// The held authority of THIS applet's driver (what fires are checked against).
    held: AuthRequired,
    /// Ephemeral view-state — never a turn.
    pub view: ViewState,
    /// The chain head — threaded into each turn's `previous_receipt_hash`.
    prev_receipt: Option<[u8; 32]>,
    /// Every committed receipt hash, in order (the audit tape).
    receipts: Vec<[u8; 32]>,
}

impl Applet {
    /// Mint ONE applet-cell on a fresh embedded executor, seeding `seed_fields` as the
    /// cell's model and registering `affordances`. `held` is the driver's authority
    /// (single-custody: `AuthRequired::None` admits all of this applet's own fires —
    /// the cap tooth still REFUSES an affordance whose `required` is stricter than
    /// `held`).
    pub fn mint(
        public_key: [u8; 32],
        token_id: [u8; 32],
        seed_fields: &[(Slot, FieldElement)],
        affordances: Vec<Affordance>,
        held: AuthRequired,
    ) -> Self {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());

        // Seed the applet-cell with a balance (so a metered turn has a fee source) and
        // OPEN permissions (single-custody embedded world), then write the genesis
        // model fields. This IS the cell's initial model.
        let mut cell = Cell::with_balance(public_key, token_id, 1_000_000);
        cell.permissions = open_permissions();
        for (slot, value) in seed_fields {
            cell.state.set_field(*slot, *value);
        }
        let cell_id = cell.id();
        engine
            .ledger_mut()
            .insert_cell(cell)
            .expect("seed applet cell onto embedded ledger");

        let affordances = affordances
            .into_iter()
            .map(|a| (a.name.clone(), a))
            .collect();

        Applet {
            engine,
            cell: cell_id,
            public_key,
            token_id,
            affordances,
            held,
            view: ViewState::default(),
            prev_receipt: None,
            receipts: Vec::new(),
        }
    }

    /// The applet's cell id (the sovereignty boundary).
    pub fn cell(&self) -> CellId {
        self.cell
    }

    /// The live ledger this applet's cell lives on (the "world" the reflective crawl
    /// walks). A witnessed, read-only view — the SAME ledger `fire` commits onto.
    pub fn ledger(&self) -> &dregg_cell::Ledger {
        self.engine.ledger()
    }

    /// The receipt tape (the provenance lineage the reflective `present()` reads).
    pub fn receipts(&self) -> &[[u8; 32]] {
        &self.receipts
    }

    /// A witnessed read of the live model off the embedded ledger (the SAME read the
    /// inspector makes). The positions of the polynomial functor.
    pub fn model(&self) -> CellModel {
        let cell = self
            .engine
            .ledger()
            .get(&self.cell)
            .expect("applet cell present on its own ledger");
        // Project the cell's fixed state slots into the model map. (STATE_SLOTS is the
        // bounded fixed-field array; the spike's counter/todo live in low slots.)
        let mut fields = BTreeMap::new();
        for slot in 0..dregg_cell::state::STATE_SLOTS {
            if let Some(fe) = cell.state.get_field(slot) {
                if *fe != [0u8; 32] {
                    fields.insert(slot, *fe);
                }
            }
        }
        CellModel {
            fields,
            nonce: cell.state.nonce(),
        }
    }

    /// Witnessed read of one model field as a u64.
    pub fn get_u64(&self, slot: Slot) -> u64 {
        self.model().field_u64(slot)
    }

    /// **Fire an affordance** — commit ONE cap-gated verified turn on the embedded
    /// executor.
    ///
    /// 1. resolve the affordance (an unknown name = no turn);
    /// 2. CAP TOOTH, in-band: `held` must satisfy the affordance's `required`
    ///    ([`dregg_cell::is_attenuation`]) — an unheld fire commits NOTHING;
    /// 3. compute the writes as a pure function of the LIVE model;
    /// 4. build the turn (carrying the affordance name as the action method, the
    ///    chain head threaded) and execute it on the embedded executor.
    ///
    /// On success the cell's new model is on the ledger AND a real [`TurnReceipt`]
    /// returns — its `receipt_hash()` is appended to the audit tape.
    pub fn fire(&mut self, affordance: &str, arg: i64) -> Result<TurnReceipt, FireError> {
        let aff = self
            .affordances
            .get(affordance)
            .ok_or_else(|| FireError::UnknownAffordance(affordance.to_string()))?;

        // (2) CAP TOOTH — the REAL is_attenuation, in-band. Refused ⇒ nothing committed.
        if !dregg_cell::is_attenuation(&self.held, &aff.required) {
            return Err(FireError::Unauthorized {
                affordance: affordance.to_string(),
            });
        }

        // (3) writes = pure function of the live model.
        let model = self.model();
        let writes = (aff.apply)(&model, arg);

        // (4) build + execute the verified turn. Single-custody embedded world:
        // the action carries the affordance name as its method and `Unchecked`
        // authorization (the cap tooth already ran in-band above). The agent is the
        // applet cell; the nonce is the cell's current nonce.
        let nonce = model.nonce();
        let mut action = ActionBuilder::new_unchecked_for_tests(self.cell, affordance, self.cell);
        for (slot, value) in writes {
            action = action.effect_set_field(self.cell, slot, value);
        }
        // Bump the cell nonce so the next turn chains and the model witnesses the fire.
        let action = action.effect_increment_nonce(self.cell).build();

        // The turn carries a fee that covers its computron cost (action_base + the
        // per-effect costs); the executor rejects a turn whose fee underpays
        // (`BudgetExceeded`). The applet cell was seeded with 1M computrons, so a
        // comfortable flat fee is well within budget for the spike's small turns.
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

    /// The number of verified turns that have committed (= the audit tape length).
    pub fn receipt_count(&self) -> usize {
        self.receipts.len()
    }

    /// The most recent receipt hash, if any.
    pub fn last_receipt(&self) -> Option<[u8; 32]> {
        self.receipts.last().copied()
    }

    /// **Set ephemeral view-state** — a plain in-memory change. This does NOT touch
    /// the ledger: no turn, no receipt. The load-bearing distinction (view-state is
    /// NOT cell state).
    pub fn set_view(&mut self, key: &str, value: &str) {
        self.view.map.insert(key.to_string(), value.to_string());
    }

    /// Read ephemeral view-state.
    pub fn get_view(&self, key: &str) -> Option<&str> {
        self.view.map.get(key).map(|s| s.as_str())
    }

    /// **Transclude another applet** — the cap-gated, provenanced compose (the
    /// distributed DOM). Reuses the REAL transclusion primitive:
    ///
    ///   - publish the OTHER applet's committed surface (a content-addressed view of
    ///     its model) into a [`WebOfCells`] — its committed `content_hash` is the
    ///     origin's commitment;
    ///   - `TranscludedField::include` performs the verified `dregg://` finalized read
    ///     (content → commitment → receipt → receipt-stream-root → quorum). A forged
    ///     or non-finalized surface REFUSES; on success the embed carries [`Provenance`]
    ///     (the citation that dates it), NOT a raw copy.
    ///
    /// Returns the verified transclusion handle whose `cite()` is the provenance.
    pub fn transclude(&self, other: &Applet) -> Result<Transclusion, TranscludeError> {
        // A quorum-of-1 web-of-cells (structural quorum meets `has_quorum` → finalized).
        let mut web = WebOfCells::new(1);
        // The other applet's committed surface: a deterministic content-address of its
        // live model (its cell id + the model field bytes). This IS the source's
        // committed content; the transclusion pins its hash, not a copy.
        let surface = other.surface_bytes();
        let uri: DreggUri = web.publish(
            0x5E,
            &surface,
            &format!("dregg://applet/{}", hex32(&other.cell.0)),
        );

        // THE VERIFIED FINALIZED READ — the genuine anti-forge tooth. A forged or
        // non-finalized surface fails HERE.
        let field = TranscludedField::include(&web, &uri)
            .map_err(|e| TranscludeError(format!("{e:?}")))?;

        // The bytes the embed displays ARE the source's committed bytes
        // (content-addressed) — proven, not assumed.
        debug_assert_eq!(field.quoted_bytes(), &surface[..]);

        Ok(Transclusion {
            host: self.cell,
            source: other.cell,
            provenance: field.cite().clone(),
            quoted: field.quoted_bytes().to_vec(),
        })
    }

    /// The applet's committed *surface* — a content-addressed snapshot of its model
    /// (cell id ‖ each non-empty model field). What a transclusion pins.
    fn surface_bytes(&self) -> Vec<u8> {
        let model = self.model();
        let mut out = Vec::new();
        out.extend_from_slice(&self.cell.0);
        out.extend_from_slice(&model.nonce().to_le_bytes());
        for (slot, fe) in &model.fields {
            out.extend_from_slice(&(*slot as u64).to_le_bytes());
            out.extend_from_slice(fe);
        }
        out
    }

    /// The applet's public key (the principal the cell commits to).
    pub fn public_key(&self) -> [u8; 32] {
        self.public_key
    }
    /// The applet's token id.
    pub fn token_id(&self) -> [u8; 32] {
        self.token_id
    }
    /// The held authority of the applet's driver.
    pub fn held(&self) -> &AuthRequired {
        &self.held
    }
}

/// A verified, provenanced whole-applet transclusion — the cap-gated compose. Carries
/// the source's [`Provenance`] (the citation), NOT a raw copy.
pub struct Transclusion {
    /// The host applet's cell (the document doing the embedding).
    pub host: CellId,
    /// The source applet's cell (what is embedded).
    pub source: CellId,
    /// The immutable provenance — source ref + content commitment + receipt + finalized.
    pub provenance: Provenance,
    /// The source's committed surface bytes (content-addressed; `== blake3⁻¹` of the
    /// commitment). NOT a copy that can diverge.
    pub quoted: Vec<u8>,
}

impl Transclusion {
    /// Is the embed finalized (quorum-attested)?
    pub fn finalized(&self) -> bool {
        self.provenance.finalized
    }
    /// The content commitment the source finalized (the anti-forge pin).
    pub fn content_hash(&self) -> [u8; 32] {
        self.provenance.content_hash
    }
    /// A human badge: "EMBED dregg://<source> @ receipt R; finalized=…".
    pub fn badge(&self) -> String {
        format!(
            "EMBED dregg://applet/{} (content {}…, receipt {}…, finalized={})",
            hex32(&self.source.0),
            hex8(&self.provenance.content_hash),
            hex8(&self.provenance.receipt_hash),
            self.provenance.finalized,
        )
    }
}

/// Why a transclusion compose failed (a forged or non-finalized source surface).
#[derive(Debug)]
pub struct TranscludeError(pub String);
impl std::fmt::Display for TranscludeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "transclusion refused: {}", self.0)
    }
}
impl std::error::Error for TranscludeError {}

/// Open (single-custody) permissions for an embedded applet cell.
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

fn hex32(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
fn hex8(b: &[u8; 32]) -> String {
    b[..4].iter().map(|x| format!("{x:02x}")).collect()
}
