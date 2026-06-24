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

    /// Witnessed read of one model field as a u64 (the scalar shape).
    pub fn get_u64(&self, slot: Slot) -> u64 {
        self.model().field_u64(slot)
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
            let model = self.model();
            let cur = model.field_u64(self.counter_slot) as i64;
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
