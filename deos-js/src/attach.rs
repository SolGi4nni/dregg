//! ATTACH — run JS over a PROVIDED live World, not deos-js's own embedded engine.
//!
//! [`Applet`](crate::Applet) mints its OWN [`DreggEngine`](dregg_sdk::embed::DreggEngine):
//! a fresh, single-cell world. That proves the agent-runs-JS-bound-to-its-cap shape
//! end-to-end, but the JS only ever crawls + drives ITS OWN private image.
//!
//! THE ATTACH PATH binds the runtime to a **provided** World — the live cockpit's
//! real ledger (the operator's actual cells), or a fork of it (safe experimentation)
//! — through a thin [`WorldSink`] the host implements. The JS then:
//!
//!   * `deos.world.cells()` / `deos.cell(id).reflect()` crawl the ATTACHED World's
//!     REAL cells (via [`crate::reflect_binding`] over [`WorldSink::ledger`]); and
//!   * `app.fire("name", n)` commits a real cap-gated verified turn ON THAT World
//!     (via [`WorldSink::commit_turn`]) — a receipt that lands on the live ledger.
//!
//! ## The red-team invariant is KEPT
//!
//! The cap tooth ([`dregg_cell::is_attenuation`]) lives HERE, in deos-js, exactly as
//! in [`Applet::fire`]: a fire is admitted iff the AGENT'S `held` authority satisfies
//! the affordance's `required`. The runtime is mounted under that attenuated `held`,
//! never the World's root. An over-reach (a `required` the agent does not hold) is
//! refused IN-BAND — no turn, no receipt — and a fire is bound to the agent's OWN
//! cell, so it cannot cross to another vessel. (`docs/deos/AGENT-CONFINEMENT-REDTEAM.md`.)
//!
//! deos-js does NOT depend on starbridge-v2 (the dependency runs the other way), so
//! the live `World` is reached through this trait, not a direct type — the host
//! crate (or deos-hermes) supplies the `impl WorldSink`.

use std::collections::BTreeSet;

use dregg_cell::capability::CapabilityRef;
use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Ledger};
use dregg_turn::action::Effect;
use dregg_types::CellId;

use crate::applet::{CellModel, FireError, Slot};

/// The host's live World, reduced to exactly what an attached applet needs: a
/// witnessed read surface (the crawl) and a commit primitive (the fire).
///
/// starbridge-v2's `World` implements this (its `ledger()` + a `commit_turn`-backed
/// adapter); a `World::fork()` implements it identically (the safe sandbox variant).
/// The implementor owns the verified executor — every [`fire_effects`](Self::fire_effects)
/// runs the SAME conservation / ocap / authority gate the live world would.
pub trait WorldSink {
    /// Read the live ledger the reflective crawl walks (the SAME ledger a fire commits
    /// onto) by running `f` over a borrow of it. Closure-passing (rather than handing
    /// back a `&Ledger`) so a host holding the World behind an `Rc<RefCell<World>>`
    /// can borrow it for exactly the read's duration — the crawl is synchronous, so
    /// `f` produces its JSON (or whatever) and the borrow ends.
    fn with_ledger(&self, f: &mut dyn FnMut(&Ledger));

    /// Commit ONE verified turn on `agent`'s cell carrying `effects`, named `method`,
    /// against the live verified executor. The host builds the turn with its OWN
    /// `World::turn` shape (so the live turn is byte-shaped exactly like every other
    /// cockpit turn: the agent's nonce, the chain head threaded, the World's fee
    /// stamped) and commits it through `World::commit_turn`. Returns the real receipt
    /// hash on commit, or the executor's rejection reason.
    ///
    /// The cap tooth has ALREADY run in deos-js before this is called (the over-reach
    /// is refused in-band, never reaching here) — this is the authorized commit only.
    fn fire_effects(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String>;

    /// **Mint an OPEN, funded world cell** — the GM superpower of standing up a fresh
    /// vessel in its world (a room, a player character, an NPC, a dungeon-instance room).
    ///
    /// The cell is derived deterministically from `seed` (hashed to the cell pubkey
    /// against the host's token domain), minted with `funding` balance and fully-open
    /// permissions (every action `AuthRequired::None`). OPEN is the load-bearing choice:
    /// a spawned cell's pubkey is `hash(seed)` (not a signable Ed25519 key), so the only
    /// way the GM can later stamp its stats — and the only way a player holding a granted
    /// cap can write it — is for the cell to require NO signature (`set_state: None`). The
    /// funding lets the cell pay the computron fee on its own self-stamp turns.
    ///
    /// This is the GM's BROAD authority over its world made concrete: minting a world
    /// vessel is the host operator's privilege (the same direct open-perms mint a node
    /// does at genesis), distinct from a player's cap-bounded signed turn. The cells it
    /// produces then transact through REAL verified turns (the GM's self-stamps, the
    /// player's signed move/gain-xp, the GM's level-up) — only the vessel's creation is
    /// the privileged superpower. Idempotent: re-minting an existing id is a no-op.
    ///
    /// Returns the new cell id. The default errs (an embedded engine has no host ledger
    /// to mint into); the attach host (`NodeWorldSink`) implements it.
    fn mint_open_cell(&mut self, _seed: &str, _funding: u64) -> Result<CellId, String> {
        Err("mint_open_cell requires an attached host ledger".into())
    }
}

/// One affordance on an attached applet: its name, the authority a viewer must HOLD
/// to fire it, and the effects a fire commits.
///
/// `effects` empty ⇒ the historical counter-bump (slot `counter_slot += arg`,
/// nonce++). `effects` non-empty ⇒ those literal effects are the turn (the arbitrary
/// shape `deos.server.defineAffordance` registers). A fire ALWAYS targets the agent's
/// own cell as its actor, but the effects may name any cell the executor authorizes.
#[derive(Clone, Debug)]
pub struct AttachedAffordance {
    pub name: String,
    pub required: AuthRequired,
    pub effects: Vec<Effect>,
}

impl AttachedAffordance {
    /// A counter-bump affordance (no explicit effects — the spike's default shape).
    pub fn counter(name: impl Into<String>, required: AuthRequired) -> Self {
        AttachedAffordance {
            name: name.into(),
            required,
            effects: Vec::new(),
        }
    }

    /// An affordance carrying arbitrary effects (the generalized shape).
    pub fn with_effects(
        name: impl Into<String>,
        required: AuthRequired,
        effects: Vec<Effect>,
    ) -> Self {
        AttachedAffordance {
            name: name.into(),
            required,
            effects,
        }
    }
}

/// An applet whose substance is a PROVIDED live World (the attach path), in contrast
/// to [`Applet`](crate::Applet) which owns a fresh embedded engine.
///
/// It carries the agent's identity (`agent` cell), its `held` authority (the cap the
/// runtime is mounted under), and the named affordance surface (`required` per name —
/// the cap tooth a fire is checked against). A fire builds the SAME counter-bump turn
/// shape [`Applet::fire`] builds, but commits it through the [`WorldSink`] onto the
/// LIVE ledger.
pub struct AttachedApplet {
    sink: Box<dyn WorldSink>,
    /// The agent's cell — the agent of every committed turn (its OWN vessel: a fire
    /// binds this cell, so it cannot cross to another).
    agent: CellId,
    /// The held authority the runtime is mounted under (the red-team invariant: the
    /// caller's ATTENUATED cap, never the World's root).
    held: AuthRequired,
    /// The agent's affordance surface. A fire of `name` is gated on `required` (an
    /// unheld `required` is the over-reach the cap tooth refuses); on admission it
    /// commits THIS affordance's `effects`. An empty `effects` falls back to the
    /// historical counter-bump on `counter_slot` (so the spike's bump shape stays
    /// expressible), while a non-empty `effects` carries ARBITRARY effects — the
    /// generalization the `deos.server.defineAffordance` keystone needs.
    affordances: Vec<AttachedAffordance>,
    /// The slot a fire's counter-bump writes when an affordance carries no explicit
    /// effects (the spike's default mutating shape).
    counter_slot: Slot,
    /// The committed receipt hashes, in order (the audit tape the JS left on the live
    /// World).
    receipts: Vec<[u8; 32]>,
    /// Ephemeral view-state — never a turn (the load-bearing distinction).
    view: std::collections::BTreeMap<String, String>,
}

impl AttachedApplet {
    /// Attach an applet to a provided live World (`sink`), driving the agent cell
    /// `agent` under `held`, with the named `affordances` surface. `counter_slot` is
    /// the state slot a fire bumps (the counter shape; reuse the same slot the host's
    /// affordance writes).
    pub fn attach(
        sink: Box<dyn WorldSink>,
        agent: CellId,
        held: AuthRequired,
        affordances: Vec<(String, AuthRequired)>,
        counter_slot: Slot,
    ) -> Self {
        let affordances = affordances
            .into_iter()
            .map(|(name, required)| AttachedAffordance::counter(name, required))
            .collect();
        AttachedApplet {
            sink,
            agent,
            held,
            affordances,
            counter_slot,
            receipts: Vec::new(),
            view: std::collections::BTreeMap::new(),
        }
    }

    /// Attach with affordances that carry ARBITRARY effects (the generalized shape the
    /// `deos.server.*` natives register). Each [`AttachedAffordance`] is the cap-gated
    /// `(name, required, effects)` the surface fires. `counter_slot` is the fallback
    /// slot for any affordance that carries no explicit effects.
    pub fn attach_with(
        sink: Box<dyn WorldSink>,
        agent: CellId,
        held: AuthRequired,
        affordances: Vec<AttachedAffordance>,
        counter_slot: Slot,
    ) -> Self {
        AttachedApplet {
            sink,
            agent,
            held,
            affordances,
            counter_slot,
            receipts: Vec::new(),
            view: std::collections::BTreeMap::new(),
        }
    }

    /// The agent cell (the applet's sovereignty boundary on the attached World).
    pub fn cell(&self) -> CellId {
        self.agent
    }

    /// The held authority the runtime is mounted under.
    pub fn held(&self) -> &AuthRequired {
        &self.held
    }

    /// Read the attached World's live ledger (the crawl surface) by running `f` over
    /// it. The SAME ledger a fire commits onto — the reflective read is of the REAL
    /// cells.
    pub fn with_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
        self.sink.with_ledger(f);
    }

    /// The registered affordance specs (name + required authority) — the cap-gated
    /// message surface the reflective `affordances(viewer)` projects.
    pub fn affordance_specs(&self) -> Vec<(String, AuthRequired)> {
        let mut specs: Vec<(String, AuthRequired)> = self
            .affordances
            .iter()
            .map(|a| (a.name.clone(), a.required.clone()))
            .collect();
        specs.sort_by(|a, b| a.0.cmp(&b.0));
        specs
    }

    /// The committed receipt tape (what the JS left on the live World).
    pub fn receipts(&self) -> &[[u8; 32]] {
        &self.receipts
    }

    /// The number of verified turns committed onto the attached World.
    pub fn receipt_count(&self) -> usize {
        self.receipts.len()
    }

    /// The most recent committed receipt hash, if any.
    pub fn last_receipt(&self) -> Option<[u8; 32]> {
        self.receipts.last().copied()
    }

    /// A witnessed read of the agent cell's live model off the attached ledger.
    pub fn model(&self) -> CellModel {
        let mut model = CellModel::from_ledger_empty();
        let agent = self.agent;
        self.sink
            .with_ledger(&mut |l| model = CellModel::from_ledger(l, &agent));
        model
    }

    /// Witnessed read of one model field as a u64 (the scalar shape) — direct off the
    /// attached ledger, with no whole-cell `CellModel`/`BTreeMap` projection for a
    /// single scalar (called per `bind` per frame).
    pub fn get_u64(&self, slot: Slot) -> u64 {
        let agent = self.agent;
        let mut v = 0u64;
        self.sink
            .with_ledger(&mut |l| v = CellModel::field_u64_direct(l, &agent, slot));
        v
    }

    /// **Fire an affordance** — commit ONE cap-gated verified turn ON THE LIVE WORLD.
    ///
    /// 1. resolve the affordance (an unknown name = no turn);
    /// 2. CAP TOOTH, in-band: `held` must satisfy the affordance's `required`
    ///    ([`dregg_cell::is_attenuation`]) — an over-reach commits NOTHING;
    /// 3. build the counter-bump turn (agent = the agent's OWN cell, the chain head
    ///    threaded from the live World, the fee stamped) and commit it through the
    ///    [`WorldSink`] — landing the receipt on the live ledger.
    pub fn fire(&mut self, affordance: &str, arg: i64) -> Result<[u8; 32], FireError> {
        let aff = self
            .affordances
            .iter()
            .find(|a| a.name == affordance)
            .cloned()
            .ok_or_else(|| FireError::UnknownAffordance(affordance.to_string()))?;

        // (2) CAP TOOTH — the REAL is_attenuation, in-band. Refused ⇒ nothing committed,
        // and (crucially on a LIVE world) nothing reaches the executor at all.
        if !dregg_cell::is_attenuation(&self.held, &aff.required) {
            return Err(FireError::Unauthorized {
                affordance: affordance.to_string(),
            });
        }

        // (3) THE EFFECTS. An affordance carrying explicit `effects` fires THOSE (the
        //     generalized shape — arbitrary effects on the cells the affordance names,
        //     each re-checked by the executor's authority gate). An affordance with NO
        //     explicit effects falls back to the counter-bump on the agent's OWN cell
        //     (the historical spike shape). The turn's ACTOR is always the agent's cell
        //     (a fire cannot cross to another vessel).
        let effects = if aff.effects.is_empty() {
            // Read just the counter slot directly (no whole-cell model projection).
            let cur = self.get_u64(self.counter_slot) as i64;
            let next = (cur + arg).max(0) as u64;
            let value: FieldElement = crate::applet::pack_u64(next);
            vec![
                Effect::SetField {
                    cell: self.agent,
                    index: self.counter_slot,
                    value,
                },
                Effect::IncrementNonce { cell: self.agent },
            ]
        } else {
            aff.effects.clone()
        };

        // (4) commit through the host's World (its own turn shape — the chain head,
        //     nonce + fee threaded host-side). The receipt lands on the live ledger.
        let rh = self
            .sink
            .fire_effects(self.agent, affordance, effects)
            .map_err(FireError::Executor)?;
        self.receipts.push(rh);
        Ok(rh)
    }

    /// **Fire RAW effects** — commit ONE verified turn carrying `effects` directly,
    /// bypassing the named-affordance surface (the GM-superpower path: `spawnCell` /
    /// `grant` build their effects in-host and commit them as the agent). The turn's
    /// ACTOR is the agent's own cell; the effects may name any cell the executor
    /// authorizes. Records the receipt on the audit tape.
    ///
    /// There is NO affordance-level cap tooth here (the caller IS the agent driving its
    /// own surface, e.g. the GM program's privileged setup) — the executor's authority
    /// gate is the binding check on every effect.
    pub fn fire_raw_effects(
        &mut self,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], FireError> {
        self.fire_raw_effects_as(self.agent, method, effects)
    }

    /// As [`Self::fire_raw_effects`], but commit the turn under `actor` rather than the
    /// applet's own agent — the GM superpower of acting AS a cell it governs (e.g. a
    /// self-grant from a door cell the GM spawned). The executor's authority gate is the
    /// binding check; the GM's broad authority is what lets it drive its own world's cells.
    pub fn fire_raw_effects_as(
        &mut self,
        actor: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], FireError> {
        let rh = self
            .sink
            .fire_effects(actor, method, effects)
            .map_err(FireError::Executor)?;
        self.receipts.push(rh);
        Ok(rh)
    }

    /// Mint an OPEN, funded world cell through the host (the GM superpower — see
    /// [`WorldSink::mint_open_cell`]). Returns the new cell id.
    pub fn mint_open_cell(&mut self, seed: &str, funding: u64) -> Result<CellId, FireError> {
        self.sink
            .mint_open_cell(seed, funding)
            .map_err(FireError::Executor)
    }

    /// Set ephemeral view-state — a plain in-memory change (NO turn, NO receipt).
    pub fn set_view(&mut self, key: &str, value: &str) {
        self.view.insert(key.to_string(), value.to_string());
    }

    /// Read ephemeral view-state.
    pub fn get_view(&self, key: &str) -> Option<&str> {
        self.view.get(key).map(|s| s.as_str())
    }
}

// ───────────────────────── the bounded multi-cell composer ──────────────────
//
// `multi_cell::MultiCellAuthor` composes a multi-cell story (mint + setField + grant)
// on its OWN embedded engine. THE COMPOSE PATH lifts that exact tooth — the cap tooth
// (`is_attenuation`), the scope tooth (a leg may only touch a held cell), and the
// atomic all-or-nothing PRE-SCREEN — onto a PROVIDED live World, so the agent's brain
// can decide-and-execute a genuinely useful multi-cell task (e.g. "stand up a shared
// notebook for me and a collaborator" = mint the cell + seed its title + grant the
// collaborator a cap) as ONE bounded, receipted gesture on the cockpit's real ledger.
//
// This is the bounded sibling of the `deos.server.*` GM superpowers (`fire_raw_effects`):
// those act AS each governed cell with NO `held` bound (the GM's own-world privilege);
// the composer is mounted under the agent's ATTENUATED `held` and refuses an over-reach
// (or a foreign-cell touch) IN-BAND, with NOTHING committed — the same red-team invariant
// `AttachedApplet::fire` keeps, generalised to a multi-leg story.

/// One leg of a multi-cell story committed on the live World. Each leg names the cell(s)
/// it touches (so the scope tooth can refuse a leg reaching past the agent's scope) and
/// carries the authority it `required`s (so the cap tooth can refuse a leg whose `required`
/// over-reaches `held`).
pub enum ComposeStep {
    /// **Mint a card** — stand up a fresh OPEN, funded cell (via [`WorldSink::mint_open_cell`])
    /// the agent becomes capped over. The new cell joins the agent's scope for later legs in
    /// the SAME story (so a story may mint-then-seed its own new cell). Reported in
    /// [`LiveComposition::minted`].
    MintCard {
        /// The deterministic seed the new cell's id derives from (`hash(seed)`).
        seed: String,
        /// The genesis model fields written into the new cell right after it is minted.
        seed_fields: Vec<(Slot, FieldElement)>,
        /// The funding stipend the minted cell carries (to pay its own self-stamp fees).
        funding: u64,
        /// The authority minting requires (the cap tooth checks `held ⊒ required`).
        required: AuthRequired,
    },
    /// **Set a field** on a cell in the agent's scope — a real `SetField` verified turn.
    /// `cell` must be held (a SetField on a foreign vessel's cell is the scope over-reach).
    SetField {
        /// The cell whose model field is written (must be in scope).
        cell: CellId,
        /// The model slot.
        slot: Slot,
        /// The new value (a u64 packed into a field element).
        value: u64,
        /// The authority the write requires.
        required: AuthRequired,
    },
    /// **Grant a capability** over one of the agent's held cells TO a peer. The `from` cell
    /// must be in the agent's scope (you may only grant FROM a cell you hold); `to` may be
    /// any peer (granting OUTWARD is the point). The granted authority is itself cap-checked
    /// against `held` (you cannot grant authority you do not hold).
    GrantCap {
        /// The held cell the grant issues FROM (must be in scope).
        from: CellId,
        /// The peer cell receiving the capability (need NOT be in scope — the outward reach).
        to: CellId,
        /// The authority handed over (cap-checked against `held` — no granting what you lack).
        granted: AuthRequired,
        /// The authority issuing the grant requires.
        required: AuthRequired,
    },
}

impl ComposeStep {
    fn required(&self) -> &AuthRequired {
        match self {
            ComposeStep::MintCard { required, .. }
            | ComposeStep::SetField { required, .. }
            | ComposeStep::GrantCap { required, .. } => required,
        }
    }

    fn method(&self) -> &'static str {
        match self {
            ComposeStep::MintCard { .. } => "mint_card",
            ComposeStep::SetField { .. } => "set_field",
            ComposeStep::GrantCap { .. } => "grant_cap",
        }
    }
}

/// Why a live multi-cell composition was refused. An over-reach is reported IN-BAND with
/// NOTHING committed (the pre-screen held before any turn reached the live executor).
#[derive(Debug)]
pub enum ComposeError {
    /// The cap/scope tooth refused a leg: its `required` is not narrower-or-equal to `held`,
    /// OR it touches a cell outside the agent's scope, OR it grants authority the agent does
    /// not hold. Carries the 0-based leg index and a reason. NO turn committed for ANY leg —
    /// no partial commit of an unauthorized leg.
    OverReach { step: usize, reason: String },
    /// A leg cleared the tooth but the live executor rejected its turn. The legs committed
    /// BEFORE it have landed (step-wise commit on the live ledger); this names the failed
    /// leg + the executor's reason (the residual executor-side surface, e.g. fee/budget).
    Executor { step: usize, reason: String },
}

impl std::fmt::Display for ComposeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComposeError::OverReach { step, reason } => {
                write!(f, "step {step} over-reaches the agent's held authority: {reason}")
            }
            ComposeError::Executor { step, reason } => {
                write!(f, "step {step} refused by the live executor: {reason}")
            }
        }
    }
}
impl std::error::Error for ComposeError {}

/// The record of a multi-cell story committed on the live World: every leg's receipt hash
/// (in order, all under the agent cell) and the ids of any cells minted along the way.
#[derive(Debug, Clone, Default)]
pub struct LiveComposition {
    /// The committed receipt hash of each leg, in step order. One leg = one verified turn.
    pub receipts: Vec<[u8; 32]>,
    /// The cell ids minted by `MintCard` legs, in order (each now in the agent's scope).
    pub minted: Vec<CellId>,
}

impl LiveComposition {
    /// The number of verified turns the story committed (= the number of legs).
    pub fn len(&self) -> usize {
        self.receipts.len()
    }
    /// Whether the story was empty (no legs).
    pub fn is_empty(&self) -> bool {
        self.receipts.is_empty()
    }
}

/// A **bounded multi-cell composer** over a PROVIDED live World — the brain composes a
/// story spanning the agent's held cells (and reaching OUTWARD via grants) as a sequence
/// of cap-gated verified turns on the cockpit's real ledger.
///
/// It carries the agent's identity (`agent`), its `held` authority (the cap the runtime is
/// mounted under — the red-team invariant: the attenuated cap, never the World's root), and
/// the agent's authority SCOPE (`held_cells` — the cells it may touch). The tooth lives
/// HERE, exactly as in [`AttachedApplet::fire`] and `multi_cell::MultiCellAuthor::compose`.
pub struct AttachedComposer {
    sink: Box<dyn WorldSink>,
    /// The agent cell — the agent of every committed turn (the principal the story is
    /// attributed to). It is itself in `held_cells`.
    agent: CellId,
    /// The held authority the agent wields (every leg's `required` is checked against this;
    /// every granted authority is checked against this).
    held: AuthRequired,
    /// The agent's authority SCOPE — the cells it may touch. A leg touching a cell outside
    /// this set is the scope over-reach the tooth refuses. `MintCard` grows it.
    held_cells: BTreeSet<CellId>,
    /// Every committed receipt hash, in order (the audit tape across the whole story).
    receipts: Vec<[u8; 32]>,
}

impl AttachedComposer {
    /// Build a composer over a live World (`sink`), driving `agent` under `held`, whose
    /// initial scope is `{agent} ∪ scope` (the cells the agent already holds — its own cell
    /// plus any cards pre-granted to it). A `MintCard` leg grows the scope with the cell it
    /// stands up.
    pub fn attach(
        sink: Box<dyn WorldSink>,
        agent: CellId,
        held: AuthRequired,
        scope: &[CellId],
    ) -> Self {
        let mut held_cells = BTreeSet::new();
        held_cells.insert(agent);
        for c in scope {
            held_cells.insert(*c);
        }
        AttachedComposer {
            sink,
            agent,
            held,
            held_cells,
            receipts: Vec::new(),
        }
    }

    /// The agent cell (the agent of every committed turn).
    pub fn agent(&self) -> CellId {
        self.agent
    }

    /// The held authority.
    pub fn held(&self) -> &AuthRequired {
        &self.held
    }

    /// Whether `cell` is in the agent's scope (the cells it may touch).
    pub fn holds_cell(&self, cell: &CellId) -> bool {
        self.held_cells.contains(cell)
    }

    /// The committed receipt tape across every story (in order).
    pub fn receipts(&self) -> &[[u8; 32]] {
        &self.receipts
    }

    /// The number of verified turns committed in total.
    pub fn receipt_count(&self) -> usize {
        self.receipts.len()
    }

    /// Read a model field of any cell in the World as a u64 (the scalar shape) — a witnessed
    /// read off the live ledger.
    pub fn get_u64(&self, cell: &CellId, slot: Slot) -> u64 {
        let mut v = 0u64;
        self.sink
            .with_ledger(&mut |l| v = CellModel::field_u64_direct(l, cell, slot));
        v
    }

    /// **Compose a multi-cell story on the live World** — author `steps` spanning the agent's
    /// cells (and reaching outward via grants) as cap-gated verified turns on the real ledger.
    ///
    /// THE TOOTH, generalised + ATOMIC pre-screen (the all-or-nothing face):
    ///
    /// 1. PRE-SCREEN every leg against `held` (the authority tooth — [`dregg_cell::is_attenuation`])
    ///    AND the agent's scope (the scope tooth — every touched cell must be held; a
    ///    `MintCard` grows the PROJECTED scope so a later leg may touch the cell it will
    ///    mint). A granted authority is ALSO checked against `held`. ANY over-reach ⇒
    ///    [`ComposeError::OverReach`] and NOTHING is committed — no turn for ANY leg.
    /// 2. Only when EVERY leg clears, commit each as its OWN verified turn through the
    ///    [`WorldSink`] (agent = the agent cell), collecting the live receipts. A `MintCard`
    ///    mints its OPEN funded cell and adds it to the live scope.
    pub fn compose(&mut self, steps: Vec<ComposeStep>) -> Result<LiveComposition, ComposeError> {
        // ── (1) ATOMIC PRE-SCREEN — refuse any over-reach before ANY turn commits. ──
        // The projected scope grows with each MintCard (the cell it WILL create), so a
        // story may mint-then-write its own new cell, but may NOT touch a foreign cell.
        let mut projected: BTreeSet<CellId> = self.held_cells.clone();
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
                ComposeStep::MintCard { seed, .. } => {
                    projected.insert(mint_id_of(seed));
                }
                ComposeStep::SetField { cell, .. } => {
                    if !projected.contains(cell) {
                        return Err(ComposeError::OverReach {
                            step: i,
                            reason: format!(
                                "set_field touches cell {cell} outside the agent's held scope"
                            ),
                        });
                    }
                }
                ComposeStep::GrantCap { from, granted, .. } => {
                    if !projected.contains(from) {
                        return Err(ComposeError::OverReach {
                            step: i,
                            reason: format!(
                                "grant issues FROM cell {from} outside the agent's held scope"
                            ),
                        });
                    }
                    if !dregg_cell::is_attenuation(&self.held, granted) {
                        return Err(ComposeError::OverReach {
                            step: i,
                            reason: "grant hands over an authority wider than held".into(),
                        });
                    }
                }
            }
        }

        // ── (2) COMMIT — every leg cleared; commit each as its own verified turn. ──
        let mut comp = LiveComposition::default();
        for (i, step) in steps.into_iter().enumerate() {
            let (rh, new_cell) = self
                .commit_step(step)
                .map_err(|reason| ComposeError::Executor { step: i, reason })?;
            if let Some(id) = new_cell {
                self.held_cells.insert(id);
                comp.minted.push(id);
            }
            self.receipts.push(rh);
            comp.receipts.push(rh);
        }
        Ok(comp)
    }

    /// Commit ONE leg as a real verified turn on the live World. The tooth has ALREADY
    /// cleared in the pre-screen. Returns the receipt hash and, for a `MintCard`, the new
    /// cell id. A `MintCard` mints an OPEN funded cell (so a later in-story `SetField` on it
    /// authorizes); a `SetField`/`GrantCap` commits the matching effect AS the touched cell
    /// (the open-perms self-write/self-grant the live executor admits — the same shape the
    /// `deos.server.*` superpowers use, here bounded by the pre-screen).
    fn commit_step(&mut self, step: ComposeStep) -> Result<([u8; 32], Option<CellId>), String> {
        match step {
            ComposeStep::MintCard {
                seed,
                seed_fields,
                funding,
                ..
            } => {
                let id = self.sink.mint_open_cell(&seed, funding)?;
                // Seed the genesis model: one SetField per field, committed AS the new
                // (open) cell. An empty seed still bumps the agent's nonce so the mint leg
                // leaves a receipt of its own.
                let mut effects: Vec<Effect> = seed_fields
                    .into_iter()
                    .map(|(index, value)| Effect::SetField { cell: id, index, value })
                    .collect();
                effects.push(Effect::IncrementNonce { cell: id });
                let rh = self.sink.fire_effects(id, "mint_card", effects)?;
                Ok((rh, Some(id)))
            }
            ComposeStep::SetField {
                cell, slot, value, ..
            } => {
                let effects = vec![
                    Effect::SetField {
                        cell,
                        index: slot,
                        value: crate::applet::pack_u64(value),
                    },
                    Effect::IncrementNonce { cell },
                ];
                let rh = self.sink.fire_effects(cell, "set_field", effects)?;
                Ok((rh, None))
            }
            ComposeStep::GrantCap {
                from, to, granted, ..
            } => {
                let cap = CapabilityRef {
                    target: from,
                    slot: 0,
                    permissions: granted,
                    breadstuff: None,
                    expires_at: None,
                    allowed_effects: None,
                    stored_epoch: None,
                };
                // Commit the grant AS the `from` cell (a self-grant: from == actor == target),
                // whose `delegate` permission the executor checks. For an open held cell this
                // authorizes; the pre-screen has already bounded `granted` ⊑ `held`.
                let effects = vec![Effect::GrantCapability { from, to, cap }];
                let rh = self.sink.fire_effects(from, "grant_cap", effects)?;
                Ok((rh, None))
            }
        }
    }
}

/// The deterministic cell id a `MintCard { seed }` leg stands up: `hash(seed)` against the
/// host's default token domain — the SAME derivation [`WorldSink::mint_open_cell`] uses, so
/// the pre-screen can project the minted cell into scope before the mint commits.
pub fn mint_id_of(seed: &str) -> CellId {
    let public_key = *blake3::hash(seed.as_bytes()).as_bytes();
    let token_id = *blake3::hash(b"default").as_bytes();
    CellId::derive_raw(&public_key, &token_id)
}
