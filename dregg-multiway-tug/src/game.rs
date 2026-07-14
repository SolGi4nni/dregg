//! # `MultiwayTug` — the game deployed and DRIVEN on the real executor.
//!
//! Deploys the [`crate::state`] story on a real [`spween_dregg::WorldCell`] (the deployed
//! `EmbeddedExecutor` + ledger), seeds the round under the permissive `genesis` method,
//! and commits each play as ONE cap-bounded turn the executor admits IFF the play teeth
//! pass. The mover is the [`crate::reference::Engine`]: it computes the next projection
//! off-circuit and the driver commits it; the executor's teeth re-check conservation /
//! one-action / monotonicity / the win against the witnessed post-state (the portfolio's
//! translation-validation shape). An illegal play is a real [`WorldError::Refused`].
//!
//! Phase 0 hides the hand only by NON-REVEAL on this trusted host — the counters are
//! public, the card identities live in the reference mover. The zk hidden-hand
//! (`Witnessed{MerkleMembership}` + a sealed-auction opponent pick), cards-as-owned
//! assets, the STARK fold, the Lean refinement, and the Offering are the named later
//! phases (see the crate docs).

use std::sync::Arc;

use dregg_app_framework::{CellId, Effect, TurnReceipt, field_from_u64};
use spween_dregg::{WorldCell, WorldError};

use crate::reference::{ActionKind, N_GUILDS, Player, Projection};
use crate::state::{Deployment, GENESIS, SCORE};

/// A deployed multiway-tug game on a real world-cell.
pub struct MultiwayTug {
    dep: Deployment,
    world: WorldCell,
}

impl MultiwayTug {
    /// Deploy the story on a real world-cell (deterministic in `SCENE_ID` + `seed`).
    pub fn deploy(seed: u8) -> Result<Self, WorldError> {
        let dep = Deployment::new();
        let story = dep.story();
        let world = WorldCell::deploy_compiled(Arc::new(story), seed)?;
        Ok(MultiwayTug { dep, world })
    }

    pub fn dep(&self) -> &Deployment {
        &self.dep
    }
    pub fn world(&self) -> &WorldCell {
        &self.world
    }
    pub fn cell(&self) -> CellId {
        self.world.cell_id()
    }

    /// Every `SetField` effect that writes `proj` in full (16 registers + 22 heap keys).
    fn effects_for(&self, proj: &Projection) -> Vec<Effect> {
        let cell = self.cell();
        let mut effects = Vec::with_capacity(16 + 8 + 2 * N_GUILDS);
        let mut set = |name: &str, v: u64| {
            effects.push(Effect::SetField {
                cell,
                index: self.dep.reg(name) as usize,
                value: field_from_u64(v),
            });
        };
        set("deck", proj.deck);
        set("oop", proj.oop);
        set("a_hand", proj.hand[0]);
        set("b_hand", proj.hand[1]);
        set("a_secret", proj.secret_count[0]);
        set("b_secret", proj.secret_count[1]);
        set("a_board", proj.board[0]);
        set("b_board", proj.board[1]);
        set("a_charm", proj.charm[0]);
        set("b_charm", proj.charm[1]);
        set("a_guilds", proj.guilds_controlled[0]);
        set("b_guilds", proj.guilds_controlled[1]);
        set("winner", proj.winner);
        set("current", proj.current);
        set("round_actions", proj.round_actions);
        set("scored", proj.scored);
        drop(set);
        for p in [Player::A, Player::B] {
            for a in [
                ActionKind::Secret,
                ActionKind::Discard,
                ActionKind::Gift,
                ActionKind::Competition,
            ] {
                effects.push(Effect::SetField {
                    cell,
                    index: self.dep.flag_key(p, a) as usize,
                    value: field_from_u64(proj.flag[p.idx()][a.idx()]),
                });
            }
        }
        for g in 0..N_GUILDS {
            for p in [Player::A, Player::B] {
                effects.push(Effect::SetField {
                    cell,
                    index: self.dep.score_key(g, p) as usize,
                    value: field_from_u64(proj.score[g][p.idx()]),
                });
            }
        }
        effects
    }

    /// Seed the initial round state under the permissive genesis method.
    pub fn seed(&self, proj: &Projection) -> Result<TurnReceipt, WorldError> {
        self.world.apply_raw(GENESIS, self.effects_for(proj))
    }

    /// Commit a full projection under `method` — the primitive every play uses.
    pub fn commit_projection(
        &self,
        method: &str,
        proj: &Projection,
    ) -> Result<TurnReceipt, WorldError> {
        self.world.apply_raw(method, self.effects_for(proj))
    }

    /// Commit the scoring turn.
    pub fn commit_score(&self, proj: &Projection) -> Result<TurnReceipt, WorldError> {
        self.commit_projection(SCORE, proj)
    }

    /// Drive a raw turn (for the illegal-play tests): whatever `effects`, under `method`.
    pub fn commit_raw(
        &self,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<TurnReceipt, WorldError> {
        self.world.apply_raw(method, effects)
    }

    /// A `SetField` on a named register (illegal-play test builder).
    pub fn reg_effect(&self, name: &str, v: u64) -> Effect {
        Effect::SetField {
            cell: self.cell(),
            index: self.dep.reg(name) as usize,
            value: field_from_u64(v),
        }
    }

    /// A `SetField` on a heap key (illegal-play test builder).
    pub fn heap_effect(&self, key: u64, v: u64) -> Effect {
        Effect::SetField {
            cell: self.cell(),
            index: key as usize,
            value: field_from_u64(v),
        }
    }

    pub fn read_reg(&self, name: &str) -> u64 {
        self.world.snapshot()[self.dep.reg(name) as usize]
    }

    pub fn read_heap_key(&self, key: u64) -> u64 {
        self.world.read_heap(key).unwrap_or(0)
    }

    /// Reconstruct the committed projection off the cell state — compared to the
    /// reference to prove the executor reproduces the game exactly.
    pub fn read_projection(&self) -> Projection {
        let mut score = [[0u64; 2]; N_GUILDS];
        for g in 0..N_GUILDS {
            for p in [Player::A, Player::B] {
                score[g][p.idx()] = self.read_heap_key(self.dep.score_key(g, p));
            }
        }
        let mut flag = [[0u64; 4]; 2];
        for p in [Player::A, Player::B] {
            for a in [
                ActionKind::Secret,
                ActionKind::Discard,
                ActionKind::Gift,
                ActionKind::Competition,
            ] {
                flag[p.idx()][a.idx()] = self.read_heap_key(self.dep.flag_key(p, a));
            }
        }
        Projection {
            deck: self.read_reg("deck"),
            oop: self.read_reg("oop"),
            hand: [self.read_reg("a_hand"), self.read_reg("b_hand")],
            secret_count: [self.read_reg("a_secret"), self.read_reg("b_secret")],
            board: [self.read_reg("a_board"), self.read_reg("b_board")],
            charm: [self.read_reg("a_charm"), self.read_reg("b_charm")],
            guilds_controlled: [self.read_reg("a_guilds"), self.read_reg("b_guilds")],
            winner: self.read_reg("winner"),
            current: self.read_reg("current"),
            round_actions: self.read_reg("round_actions"),
            scored: self.read_reg("scored"),
            score,
            flag,
        }
    }
}
