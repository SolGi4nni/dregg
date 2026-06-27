//! **The app→World commit bridge** — re-point a launched starbridge-app's seed
//! cell AND its affordance turns onto the cockpit's LIVE [`crate::world::World`]
//! ledger, so the app's cells + receipts show in the cockpit's OWN cell inspector
//! (`World::ledger()` / `World::receipts()`), not the app framework's side-ledger.
//!
//! ## Why this exists
//!
//! [`crate::app_registry`] launches a [`dregg_app_framework::DeosApp`] over an
//! [`crate::app_registry::AppSubstrate`] — a real, receipted, SHARED ledger, but
//! the app FRAMEWORK's ledger (an `Arc<Mutex<Ledger>>` inside the
//! `EmbeddedExecutor`'s `AgentRuntime`), DISTINCT from the cockpit's `World`/
//! `DreggEngine` ledger. So an app's turns never appear in the cockpit's own
//! inspector. This module closes that gap exactly the way the editor lane did with
//! `WorldSpine` (`dock/editor_surface.rs`): seed the app's cell onto `World` as
//! genesis, then commit each affordance's effect-set through `World::turn` →
//! `World::commit_turn` (the SAME live path the inspector reads).
//!
//! ## The seam shape (mirrors `WorldSpine`)
//!
//! The app's primary cell is the AGENT cell of every fire (`cipherclerk.cell_id()`
//! == `executor.cell_id()`); the affordance effects target that same cell. So:
//!
//!   1. **seed onto World** ([`AppWorldSpine::seed`]) — install the app's primary
//!      cell with OPEN permissions onto `World` as genesis (`World::genesis_install`),
//!      install the app's [`dregg_cell::CellProgram`] on it (`World::set_cell_program`,
//!      so `World`'s executor RE-ENFORCES the app's invariants — the state tooth),
//!      and apply the app's genesis field-writes (the seeded phase / curator / seller).
//!   2. **commit an affordance** ([`AppWorldSpine::commit`]) — run the affordance's
//!      cap-gate IN-BAND first (anti-ghost), compute the effect-set against `World`'s
//!      LIVE state, and commit it via `World::turn(app_cell, effects)` →
//!      `World::commit_turn`. The cell + the receipt now live on `World`'s ledger.
//!
//! The cap-gate is the app framework's REAL `is_attenuation`
//! ([`dregg_app_framework::CellAffordance::authorized_for`]); the state-gate is the
//! REAL `CellProgram::evaluate` that `World`'s executor re-enforces when the turn
//! runs. Both teeth bite, exactly as on the framework executor — only the LEDGER is
//! the cockpit's now.
//!
//! Single-threaded (`Rc<RefCell<World>>`), matching the cockpit's own ownership.

use std::cell::RefCell;
use std::rc::Rc;

use dregg_app_framework::{
    symbol, AuthRequired, CellProgram, Effect, FireExecuteError, Turn, TurnReceipt,
};
use dregg_cell::state::FieldElement;
use dregg_turn::action::WitnessBlob;
use dregg_types::CellId;

use crate::world::{open_permissions, CommitOutcome, World};

/// The token-domain id the app framework's `EmbeddedExecutor` derives its primary
/// cell over: `blake3("default")` (the `"default"` domain `AppSubstrate::new` uses).
/// The app's primary cell id is `CellId::derive_raw(public_key, DEFAULT_DOMAIN_TOKEN)`
/// — the SAME derivation `Cell::with_balance` uses — so seeding the cell on `World`
/// at this id makes it equal `cipherclerk.cell_id()` (the agent of every fire).
pub fn default_domain_token() -> [u8; 32] {
    *blake3::hash(b"default").as_bytes()
}

/// A genesis field-write the app seeds onto its primary cell (slot → value). The
/// app-framework seed runs these against the framework ledger; the World bridge
/// replays the SAME writes onto `World` so the seeded baseline (phase, curator,
/// seller, …) is identical on both — the cap∧state gate then reads the same state.
#[derive(Clone, Copy, Debug)]
pub struct SeedField {
    pub slot: usize,
    pub value: FieldElement,
}

/// Why an app→World fire failed — the cockpit-side analogue of the framework's
/// [`FireExecuteError`]. Either the affordance's cap-gate refused it (nothing
/// committed — anti-ghost), or `World`'s executor rejected the (authorized) turn
/// (e.g. the app program's state tooth bit).
#[derive(Debug)]
pub enum WorldFireError {
    /// The cap-gate refused the fire — the turn was NEVER built. The actor lacked
    /// the affordance's `required_rights`.
    Gate(FireExecuteError),
    /// The gate passed but `World`'s executor refused the committed turn (a program
    /// constraint bit, a non-conservation, a chain mismatch). Carries the reason the
    /// real executor reported.
    World { reason: String },
}

impl std::fmt::Display for WorldFireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WorldFireError::Gate(e) => write!(f, "app affordance refused by the cap-gate: {e}"),
            WorldFireError::World { reason } => {
                write!(
                    f,
                    "app turn refused by the cockpit World executor: {reason}"
                )
            }
        }
    }
}

impl std::error::Error for WorldFireError {}

/// **The app→World spine** — the cockpit-`World` realization of an app substrate.
///
/// Holds the live `World` (shared `Rc<RefCell<…>>`) and the app's primary cell id
/// (the agent of every fire). Construct it with [`AppWorldSpine::seed`] (which
/// installs the cell + program + genesis state onto `World`), then commit
/// affordance turns with [`AppWorldSpine::commit`].
pub struct AppWorldSpine {
    world: Rc<RefCell<World>>,
    /// The app's primary cell id — the agent of every affordance turn AND the cell
    /// the effects target. Installed on `World` once at [`AppWorldSpine::seed`].
    app_cell: CellId,
}

impl AppWorldSpine {
    /// **Seed the app's primary cell onto the live `World`** — the genesis path.
    ///
    /// - installs `app_cell` with OPEN permissions onto `World` (`genesis_install`),
    ///   so the operator-authority (single-custody) embedded world admits its turns;
    /// - installs `program` on it (`set_cell_program`), so `World`'s executor
    ///   RE-ENFORCES the app's invariants on every touching turn (the state tooth);
    /// - applies `seed_fields` (the app's genesis writes: phase, curator, seller, …)
    ///   so the cap∧state gate reads the SAME baseline the framework seed laid.
    ///
    /// The cell is installed at `app_cell`'s REAL derived id (built from the app's
    /// public key + token id), so it matches `cipherclerk.cell_id()` — the agent
    /// the affordance effects target. Returns the spine ready to commit fires.
    pub fn seed(
        world: Rc<RefCell<World>>,
        app_cell: CellId,
        public_key: [u8; 32],
        token_id: [u8; 32],
        program: CellProgram,
        seed_fields: &[SeedField],
    ) -> Self {
        {
            let mut w = world.borrow_mut();
            // Build the app's primary cell at its REAL derived id (so it equals
            // `cipherclerk.cell_id()`), with open permissions + a starting balance
            // matching the framework's `AgentRuntime` default (1M computrons), so a
            // metered turn has a balance to pay its fee from. Apply the app's genesis
            // field writes (phase / curator / seller …) onto the cell's state BEFORE
            // install, so the seeded baseline is part of the genesis cell itself — the
            // cap∧state gate + the executor then read the SAME baseline as the
            // framework seed, and the program installed below sees a valid pre-state.
            let mut cell = dregg_cell::Cell::with_balance(public_key, token_id, 1_000_000);
            cell.permissions = open_permissions();
            cell.program = program;
            for sf in seed_fields {
                cell.state.set_field(sf.slot, sf.value);
            }
            debug_assert_eq!(
                cell.id(),
                app_cell,
                "the installed app cell id must equal the app's cipherclerk cell id"
            );
            // ONE genesis install carries the program + the seeded state onto World's
            // authoritative engine ledger AND the replay tape (so the inspector + the
            // time-travel tape both see the app cell from genesis).
            w.genesis_install(cell);
        }
        AppWorldSpine { world, app_cell }
    }

    /// The app's primary cell id (the agent + the inspector's pointer).
    pub fn app_cell(&self) -> CellId {
        self.app_cell
    }

    /// A clone of the app cell's LIVE [`dregg_cell::state::CellState`] off `World`'s
    /// ledger (the SAME read the cockpit inspector makes), if present. The
    /// affordance's effect-builder is a pure function of this.
    pub fn live_state(&self) -> Option<dregg_cell::state::CellState> {
        self.world
            .borrow()
            .ledger()
            .get(&self.app_cell)
            .map(|c| c.state.clone())
    }

    /// **Commit one affordance fire through the live `World`.**
    ///
    /// 1. the CAP tooth runs IN-BAND first: `held` must satisfy `required_rights`
    ///    ([`dregg_cell::is_attenuation`]). An unheld fire is [`WorldFireError::Gate`]
    ///    and NOTHING is committed (anti-ghost), exactly like the framework path.
    /// 2. the effect-set is computed against `World`'s LIVE state by `effects` (so an
    ///    accumulating fire — the gallery's next-free-slot — reads the cockpit ledger,
    ///    not the framework one).
    /// 3. the turn is built carrying `method` (the affordance name symbol — so an
    ///    operation-scoped `CellProgram::Cases` re-enforced by `World`'s executor
    ///    DISPATCHES on it, exactly as the framework's `make_action(cell, name, …)`
    ///    does) and committed via `World::commit_turn` — the SAME live path the
    ///    inspector reads. `World`'s executor independently RE-ENFORCES the app
    ///    program (the state tooth); a stale-state fire is refused as
    ///    [`WorldFireError::World`].
    ///
    /// On success the executor's OWN receipt is returned AND lands in
    /// `World::receipts()`; the app cell's new state is in `World::ledger()`.
    pub fn commit<F>(
        &self,
        method: &str,
        held: &AuthRequired,
        required_rights: &AuthRequired,
        effects: F,
    ) -> Result<TurnReceipt, WorldFireError>
    where
        F: FnOnce(&dregg_cell::state::CellState) -> Vec<Effect>,
    {
        // Tooth 1 (CAP): the REAL is_attenuation, in-band. Refused ⇒ nothing committed.
        if !dregg_cell::is_attenuation(held, required_rights) {
            return Err(WorldFireError::Gate(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized {
                    affordance: method.to_string(),
                    required: required_rights.clone(),
                    held: held.clone(),
                },
            )));
        }
        // The live state off World's ledger — the effect-builder's pure input.
        let live = self.live_state().ok_or_else(|| WorldFireError::World {
            reason: "app cell has no live state on the World ledger (was it seeded?)".to_string(),
        })?;
        let produced = effects(&live);
        // Tooth 2 (STATE) is World's executor re-enforcing the app program on commit.
        // Build the turn carrying `method` so a method-dispatched `Cases` program (the
        // gallery/auction/bounty lifecycle) matches its operation case — `World::turn`'s
        // bare action carries an EMPTY method (no case matches → default-deny). The
        // chain head is threaded by `World::commit_turn`; we thread the nonce here.
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = self.method_turn(&w, method, produced);
            w.commit_turn(turn)
        };
        match outcome {
            CommitOutcome::Committed { receipt, .. } => Ok(*receipt),
            CommitOutcome::Rejected { reason, .. } => Err(WorldFireError::World { reason }),
            CommitOutcome::Queued { .. } => Err(WorldFireError::World {
                reason: "app turn queued (World is suspended)".to_string(),
            }),
        }
    }

    /// **Commit one AUTHENTICATED affordance fire through the live `World`** — the
    /// sender-bound path for affordances whose installed `CellProgram` reads the turn's
    /// SENDER (`SenderInSlot` / `SenderAuthorized` / `SenderMemberOf`).
    ///
    /// Identical to [`AppWorldSpine::commit`] in its two teeth (the in-band cap-gate, then
    /// `World`'s executor re-enforcing the app program), with ONE addition: the action
    /// carries `witness_blobs` — the membership proof a `SenderAuthorized` clause's
    /// `MerkleMembership` verifier (or a `BlindedSet`/`ProofBytes` clause) binds and checks.
    ///
    /// ## What carries the sender
    ///
    /// The cockpit's `World` is single-custody (`Authorization::Unchecked`); it does NOT
    /// sign turns. But the executor does NOT read the sender from the action's
    /// `Authorization` for the `CellProgram` re-enforcement — it reads it from the AGENT
    /// CELL's public key (`turn/src/executor/execute_tree.rs`: `parent_pk_opt = ledger
    /// .get(parent_cell).public_key()` → `EvalContext.sender`). The agent cell IS the app
    /// cell ([`Self::app_cell`]), seeded on `World` as `Cell::with_balance(public_key, …)`,
    /// so `ctx.sender == public_key` — the SAME pubkey the app crates pass to
    /// `single_member_authorized_root` when seeding the slot root. Hence a `SenderInSlot`
    /// affordance is satisfied by seeding `slot := public_key`, and a `SenderAuthorized`
    /// affordance by seeding `slot := single_member_authorized_root(public_key)` and
    /// attaching `single_member_membership_proof(public_key)` here as a `MerklePath` blob.
    ///
    /// `sender` is the principal the slot/root commits to (for the caller's clarity and a
    /// debug-assert that it matches the live agent pubkey); the executor's `ctx.sender` is
    /// the agent pubkey regardless, so passing the wrong one cannot forge authority — it
    /// would simply make the affordance's sender clause REFUSE (fail-closed).
    pub fn commit_as<F>(
        &self,
        sender: [u8; 32],
        method: &str,
        held: &AuthRequired,
        required_rights: &AuthRequired,
        witness_blobs: Vec<WitnessBlob>,
        effects: F,
    ) -> Result<TurnReceipt, WorldFireError>
    where
        F: FnOnce(&dregg_cell::state::CellState) -> Vec<Effect>,
    {
        // Tooth 1 (CAP): the REAL is_attenuation, in-band. Refused ⇒ nothing committed.
        if !dregg_cell::is_attenuation(held, required_rights) {
            return Err(WorldFireError::Gate(FireExecuteError::Gate(
                dregg_app_framework::FireError::Unauthorized {
                    affordance: method.to_string(),
                    required: required_rights.clone(),
                    held: held.clone(),
                },
            )));
        }
        let live = self.live_state().ok_or_else(|| WorldFireError::World {
            reason: "app cell has no live state on the World ledger (was it seeded?)".to_string(),
        })?;
        // The executor derives `ctx.sender` from the agent cell's pubkey; assert the caller's
        // declared `sender` matches it, so a `SenderInSlot`/`SenderAuthorized` seed that
        // commits a DIFFERENT principal is caught here (rather than as an opaque program
        // refusal). This binds the seeded root + the proof to the actual signing principal.
        debug_assert_eq!(
            self.world
                .borrow()
                .ledger()
                .get(&self.app_cell)
                .map(|c| *c.public_key()),
            Some(sender),
            "commit_as sender must equal the app (agent) cell's public key — the executor's ctx.sender"
        );
        let produced = effects(&live);
        let outcome = {
            let mut w = self.world.borrow_mut();
            let mut turn = self.method_turn(&w, method, produced);
            // Stamp the membership/sender witness onto the (single) root action so the
            // `SenderAuthorized` evaluator binds it (it requires a UNIQUE MerklePath/
            // ProofBytes blob). `SenderInSlot` needs no blob (it reads ctx.sender directly),
            // so an empty `witness_blobs` is fine for that case.
            if let Some(root) = turn.call_forest.roots.get_mut(0) {
                root.action.witness_blobs = witness_blobs;
            }
            w.commit_turn(turn)
        };
        match outcome {
            CommitOutcome::Committed { receipt, .. } => Ok(*receipt),
            CommitOutcome::Rejected { reason, .. } => Err(WorldFireError::World { reason }),
            CommitOutcome::Queued { .. } => Err(WorldFireError::World {
                reason: "app turn queued (World is suspended)".to_string(),
            }),
        }
    }

    /// Build a single-action [`Turn`] from the app cell carrying `method` (the
    /// affordance name symbol) over `effects`, threading the agent's CURRENT nonce
    /// off `World`'s ledger. The action targets the app cell with
    /// `Authorization::Unchecked` (the single-custody operator path the cockpit uses
    /// for `World::turn`); the load-bearing gate is the app program `World`'s
    /// executor re-enforces (the cap-gate already passed in-band above). `World::commit_turn`
    /// threads the receipt-chain head, so we leave it `None` here.
    fn method_turn(&self, world: &World, method: &str, effects: Vec<Effect>) -> Turn {
        let nonce = world
            .ledger()
            .get(&self.app_cell)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        // Reuse the cockpit's canonical bare-turn shape (agent = target = app cell,
        // `Authorization::Unchecked`, the single-custody operator path), then stamp the
        // affordance METHOD onto the action so the app's method-dispatched `Cases`
        // program matches its operation case. `bare_turn`'s action carries an empty
        // method; everything else (the full `Turn`/`Action` field set) is exactly what
        // `World::turn` produces — we do not hand-roll the struct.
        let mut turn = crate::world::bare_turn(self.app_cell, nonce, effects);
        if let Some(root) = turn.call_forest.roots.get_mut(0) {
            root.action.method = symbol(method);
        }
        turn
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The spine seeds an app cell onto World and a committed affordance turn lands
    /// on World's OWN ledger + receipts (the cockpit inspector path), proven with a
    /// trivial in-module program (a free SetField) — the bridge mechanics, isolated
    /// from any specific app crate.
    #[test]
    fn an_affordance_commits_onto_the_world_ledger_and_receipts() {
        let world = Rc::new(RefCell::new(World::new()));

        // A trivial "app": one cell, no program (admits any transition), seeded with
        // slot 0 = 7. Its id is the derived id of (pk, token).
        let pk = [0xA9u8; 32];
        let token = [0u8; 32];
        let app_cell = dregg_cell::Cell::with_balance(pk, token, 1_000_000).id();

        let spine = AppWorldSpine::seed(
            Rc::clone(&world),
            app_cell,
            pk,
            token,
            CellProgram::None,
            &[SeedField {
                slot: 0,
                value: {
                    let mut v = [0u8; 32];
                    v[31] = 7;
                    v
                },
            }],
        );

        // The cell is on World's ledger with the seeded field (inspector read).
        let before = spine.live_state().expect("seeded cell is live on World");
        assert_eq!(before.fields[0][31], 7, "the genesis field write landed");
        let receipts_before = world.borrow().receipts().len();

        // Fire one affordance (cap held = root) — a SetField writing slot 1.
        let receipt = spine
            .commit(
                "write_slot",
                &AuthRequired::None,
                &AuthRequired::Either,
                |_live| {
                    let mut v = [0u8; 32];
                    v[31] = 42;
                    vec![Effect::SetField {
                        cell: app_cell,
                        index: 1,
                        value: v,
                    }]
                },
            )
            .expect("the affordance commits through World");

        // The receipt is real and authored by the app cell.
        assert_eq!(receipt.agent, app_cell);
        assert!(receipt.action_count >= 1);

        // THE COCKPIT INSPECTOR PATH: World::receipts() grew AND World::ledger() shows
        // the new cell state — the SAME reads the cockpit's cell inspector makes.
        assert_eq!(
            world.borrow().receipts().len(),
            receipts_before + 1,
            "the turn landed in World::receipts() (the inspector's receipt log)"
        );
        let after = spine.live_state().expect("app cell still live on World");
        assert_eq!(
            after.fields[1][31], 42,
            "the fire's write is on World's ledger"
        );
        assert_ne!(
            before.fields, after.fields,
            "the cell state advanced on World"
        );
    }

    /// An unheld affordance is refused by the cap-gate IN-BAND — nothing is
    /// committed to World (anti-ghost): the receipt log does not grow.
    #[test]
    fn an_unheld_affordance_is_refused_without_touching_world() {
        let world = Rc::new(RefCell::new(World::new()));
        let pk = [0x5Cu8; 32];
        let token = [0u8; 32];
        let app_cell = dregg_cell::Cell::with_balance(pk, token, 1_000_000).id();
        let spine = AppWorldSpine::seed(
            Rc::clone(&world),
            app_cell,
            pk,
            token,
            CellProgram::None,
            &[],
        );
        let receipts_before = world.borrow().receipts().len();

        // held = Signature does NOT satisfy required = None (root) — refused in-band.
        let refused = spine.commit(
            "write_slot",
            &AuthRequired::Signature,
            &AuthRequired::None,
            |_live| {
                vec![Effect::SetField {
                    cell: app_cell,
                    index: 0,
                    value: [1u8; 32],
                }]
            },
        );
        assert!(matches!(refused, Err(WorldFireError::Gate(_))));
        assert_eq!(
            world.borrow().receipts().len(),
            receipts_before,
            "an unheld fire commits NOTHING to World (anti-ghost)"
        );
    }
}
