//! # `authorized_descent` — every descent turn CARRIES the authority that fired it
//!
//! ⚑ SUBSTRATE: this module authors **no rules**. The Descent's rules — what the executor
//! ADMITS — remain the Lean-authored `metatheory/Dregg2/Games/{Dungeon,DungeonProgram}.lean`
//! emitted to `program/dungeon_program.json` and installed by [`crate::descent`]. Everything
//! here lives strictly ABOVE the admitted turn: it decides *which admitted move is
//! submitted* and *records who was entitled to submit it*. A move that the Lean teeth refuse
//! is refused exactly as before; a move they admit is admitted exactly as before.
//!
//! ## The gap this closes
//!
//! A [`Descent`](crate::descent::Descent) is ONE world-cell with ONE writer. That is the
//! right shape for a solo run and the wrong shape for a crew: when four players share a run,
//! "the Striker struck" and "the crew voted to go deeper" are claims about *authority*, and
//! a single-writer world records neither. A host layer can check them, but a host check is
//! a host promise — it leaves no evidence, so a replay cannot tell an authorized move from
//! an invented one.
//!
//! [`AuthorizedDescent`] fixes that by making the authority ride the turn. Each verb commits
//! with an [`Effect::EmitEvent`](dregg_app_framework::Effect::EmitEvent) in the SAME executor
//! turn as the move's projection, carrying a 32-byte **authorization commitment** — whatever
//! the caller's layer says entitled this move (a seat's custody signature over its own role
//! move, a quorum certificate for a collective one). Emitted events are absorbed into
//! `receipt_hash` under the canonical prefix-free encoding and the receipt is
//! executor-signed, so the commitment cannot be stripped or swapped after the fact. A
//! verifier holding the public authorization material recomputes the commitment and checks
//! the receipt ([`receipt_carries_authorization`]) — the run's own receipt chain answers
//! "who was this move made by, and what entitled it".
//!
//! This is the same binding shape the crate already uses twice: the narrator's content
//! commitment on a campaign turn, and [`crate::collective`]'s certified-decision commitment
//! pinned in the world turn it authored.
//!
//! ## Honest scope
//!
//! * The commitment binds the move to the authorization **the caller computed**. It does not
//!   make the executor CHECK the authorization: the Descent's cell has no per-seat
//!   capabilities to check one against. What it buys is EVIDENCE — a receipt chain in which
//!   every move names its warrant, so an unwarranted move is visible on replay rather than
//!   indistinguishable. The authority layer itself (who may sign, what a quorum is) is
//!   [`dreggnet_party::crew_descent`](../../dreggnet_party/crew_descent/index.html)'s job.
//! * One authorization per turn: the emitted event carries a single commitment, so a caller
//!   that wants to bind several facts hashes them together first.

use dregg_app_framework::{Event, TurnReceipt, field_from_u64, symbol};
use procgen_dregg::CommittedSeed;
use spween_dregg::WorldError;

use crate::descent::{BankedRelicMint, DELVE, Descent, FLEE, LOOT, SMITE, Sim, UNLOCK};
use crate::loot::{LootError, LootVault};

/// The event topic every authorized descent turn emits under. Distinct from the campaign
/// narration topic so an authorization is never mistaken for a narration commitment.
pub const AUTHORIZATION_TOPIC: &str = "dungeon-on-dregg/authorized-descent/authorization/v1";

/// One admitted descent verb, with its argument. This is exactly the Lean-authored verb set
/// ([`crate::descent`]) — this module adds none and removes none.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verb {
    /// Descend one floor. Burns a breath, tightens the carry ceiling (`pack + depth ≤ CAP`),
    /// and cannot be undone: there is no ascent verb, only [`Verb::Flee`].
    Delve,
    /// Exercise the carried key-relic for `way`.
    Unlock {
        /// The way to open (`2..=FLOORS`).
        way: u64,
    },
    /// Wound the standing floor's guardian by one. Costs two breath.
    Smite,
    /// Take `relic` from the standing floor's hoard into the pack.
    Loot {
        /// The relic slot to take.
        relic: usize,
    },
    /// Bank the pack and end the run. Terminal.
    Flee,
}

impl Verb {
    /// The executor method this verb commits under (the Lean-emitted case guard's method).
    pub const fn method(self) -> &'static str {
        match self {
            Verb::Delve => DELVE,
            Verb::Unlock { .. } => UNLOCK,
            Verb::Smite => SMITE,
            Verb::Loot { .. } => LOOT,
            Verb::Flee => FLEE,
        }
    }

    /// A stable tag for this verb, for hashing an authorization over it.
    pub const fn tag(self) -> u8 {
        match self {
            Verb::Delve => 0,
            Verb::Unlock { .. } => 1,
            Verb::Smite => 2,
            Verb::Loot { .. } => 3,
            Verb::Flee => 4,
        }
    }

    /// The verb's argument (the way, the relic slot, or `0`), for hashing.
    pub const fn arg(self) -> u64 {
        match self {
            Verb::Unlock { way } => way,
            Verb::Loot { relic } => relic as u64,
            Verb::Delve | Verb::Smite | Verb::Flee => 0,
        }
    }

    /// Project this verb off the mover — the same `Sim` transition [`Descent`] itself uses.
    /// A verb the mover refuses never reaches the executor and commits nothing.
    fn project(self, sim: &Sim) -> Result<Sim, &'static str> {
        match self {
            Verb::Delve => sim.delve(),
            Verb::Unlock { way } => sim.unlock(way),
            Verb::Smite => sim.smite(),
            Verb::Loot { relic } => sim.loot(relic),
            Verb::Flee => sim.flee(),
        }
    }
}

/// **A descent whose every committed turn carries the authorization that fired it.**
///
/// Wraps a real [`Descent`] — the Lean-loaded teeth, the real `WorldCell`, every verb one
/// cap-bounded turn — and adds exactly one thing: a monotone STEP counter and an emitted
/// authorization commitment on each move. The step is the move ordinal an authority layer
/// binds its signatures/certificates to, so a warrant minted for step `n` is spendable only
/// at step `n` and only once (a refused move does not advance it; anti-ghost).
pub struct AuthorizedDescent {
    descent: Descent,
    step: u64,
}

impl AuthorizedDescent {
    /// Deploy on the map the committed `day_seed` draws (the daily entry —
    /// [`Descent::deploy_on_day`]).
    pub fn deploy(seed: u8, day_seed: [u8; 32]) -> Result<AuthorizedDescent, WorldError> {
        Ok(AuthorizedDescent {
            descent: Descent::deploy_on_day(seed, CommittedSeed::from_bytes(day_seed))?,
            step: 0,
        })
    }

    /// Deploy on an EXPLICIT family index, still binding `day_seed` as the run's provenance
    /// root ([`Descent::deploy_on_world`]) — the reproducible entry for a fixed script.
    pub fn deploy_on_map(
        seed: u8,
        day_seed: [u8; 32],
        day: usize,
    ) -> Result<AuthorizedDescent, WorldError> {
        Ok(AuthorizedDescent {
            descent: Descent::deploy_on_world(seed, CommittedSeed::from_bytes(day_seed), day)?,
            step: 0,
        })
    }

    /// The live descent (read-only): the mover's state, the day's map, the committed
    /// registers, the receipt chain.
    pub fn descent(&self) -> &Descent {
        &self.descent
    }

    /// The mover's committed state.
    pub fn sim(&self) -> &Sim {
        self.descent.sim()
    }

    /// The move ordinal the NEXT authorization must be minted for. Advances only on a
    /// committed turn.
    pub fn step(&self) -> u64 {
        self.step
    }

    /// **Commit one admitted verb, binding `authorization` into the very same turn.**
    ///
    /// The projection is the mover's ([`Descent`]'s own), the referee is the installed
    /// Lean-sourced program, and the emitted event rides the receipt hash. A move the mover
    /// or the executor refuses commits nothing and does NOT advance [`step`](Self::step), so
    /// a warrant is never burned by a refusal.
    pub fn commit(
        &mut self,
        verb: Verb,
        authorization: [u8; 32],
    ) -> Result<TurnReceipt, WorldError> {
        let next = verb.project(self.descent.sim());
        let event = Event::new(
            symbol(AUTHORIZATION_TOPIC),
            vec![authorization, field_from_u64(self.step)],
        );
        let receipt = self
            .descent
            .commit_projected_with_event(verb.method(), next, event)?;
        self.step += 1;
        Ok(receipt)
    }

    /// Mint the run's banked relics as real owned loot notes
    /// ([`Descent::mint_banked_relics`]) — the bank → asset wire, unchanged.
    pub fn mint_banked_relics(
        &self,
        vault: &mut LootVault,
        player: &str,
    ) -> Result<Vec<BankedRelicMint>, LootError> {
        self.descent.mint_banked_relics(vault, player)
    }
}

/// **The authorization tooth** — does this committed turn carry `authorization`?
///
/// Recomputable by anyone: the caller derives the expected commitment from the PUBLIC
/// authorization material (the crew, the seat that signed, the certified decision) and checks
/// it against the receipt's emitted events. Emitted events are absorbed prefix-free into
/// `receipt_hash`, and the receipt carries the executor's signature over that hash, so a turn
/// cannot acquire, lose, or swap its warrant after the fact.
pub fn receipt_carries_authorization(receipt: &TurnReceipt, authorization: &[u8; 32]) -> bool {
    receipt.emitted_events.iter().any(|event| {
        event.topic == symbol(AUTHORIZATION_TOPIC)
            && event.data.first().is_some_and(|d| d == authorization)
    })
}

/// The authorization commitment a committed turn carries, if any — for a reader that wants to
/// EXHIBIT the warrant rather than check a guess.
pub fn receipt_authorization(receipt: &TurnReceipt) -> Option<[u8; 32]> {
    receipt
        .emitted_events
        .iter()
        .find(|event| event.topic == symbol(AUTHORIZATION_TOPIC))
        .and_then(|event| event.data.first().copied())
}

#[cfg(test)]
mod tests {
    use super::*;

    const DAY_SEED: [u8; 32] = [0x5E; 32];

    /// The warrant RIDES the turn: a committed move carries exactly the commitment it was
    /// submitted with, a different guess does not match, and the descent state advanced for
    /// real (this is a genuine Lean-refereed turn, not a bookkeeping entry).
    #[test]
    fn a_committed_move_carries_its_authorization_and_a_wrong_guess_does_not_match() {
        let mut run = AuthorizedDescent::deploy_on_map(7, DAY_SEED, 0).expect("deploy");
        let warrant = [0xA1u8; 32];
        assert_eq!(run.step(), 0);

        let receipt = run.commit(Verb::Delve, warrant).expect("the first delve");
        assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine committed turn");
        assert_eq!(run.sim().depth, 1, "the world really moved");
        assert_eq!(run.step(), 1, "the ordinal advanced");

        assert!(
            receipt_carries_authorization(&receipt, &warrant),
            "the turn carries the warrant it was submitted with"
        );
        assert!(
            !receipt_carries_authorization(&receipt, &[0xA2u8; 32]),
            "a different warrant does not match — the check is not vacuous"
        );
        assert_eq!(receipt_authorization(&receipt), Some(warrant));
    }

    /// A REFUSED move burns nothing: no turn, no state, and the ordinal does not advance, so
    /// the warrant minted for that ordinal is still spendable. (Delving to floor 2 without
    /// exercising way 2's key is refused by the rules — the Lean model's `way is shut`.)
    #[test]
    fn a_refused_move_does_not_advance_the_ordinal() {
        let mut run = AuthorizedDescent::deploy_on_map(8, DAY_SEED, 0).expect("deploy");
        run.commit(Verb::Delve, [1u8; 32]).expect("floor 1");
        assert_eq!(run.step(), 1);

        let refused = run.commit(Verb::Delve, [2u8; 32]);
        assert!(
            refused.is_err(),
            "way 2 is shut — its key was never exercised: {refused:?}"
        );
        assert_eq!(run.sim().depth, 1, "anti-ghost: the world did not move");
        assert_eq!(run.step(), 1, "the ordinal did not advance on a refusal");
        assert_eq!(
            run.descent().read_reg("depth"),
            1,
            "the committed ledger agrees"
        );
    }

    /// **NON-VACUITY for the replay tooth.** A move driven AROUND this wrapper — a bare
    /// [`Descent`] verb — carries no warrant at all, so a chain walk that requires one
    /// genuinely discriminates. Without this, "every turn carries its warrant" would be a
    /// property of the emitter rather than a check on the ledger.
    #[test]
    fn a_move_driven_around_the_wrapper_carries_no_warrant() {
        let mut plain =
            Descent::deploy_on_world(10, CommittedSeed::from_bytes(DAY_SEED), 0).expect("deploy");
        let receipt = plain.delve().expect("a bare delve commits");
        assert_ne!(
            receipt.turn_hash, [0u8; 32],
            "it is a genuine committed turn"
        );
        assert_eq!(
            receipt_authorization(&receipt),
            None,
            "and it names no authority whatsoever"
        );
        assert!(!receipt_carries_authorization(&receipt, &[0u8; 32]));
    }

    /// The ordinal is the anti-replay handle: two moves are two DIFFERENT ordinals, so a
    /// warrant minted over one is not a warrant for the other even for the identical verb.
    #[test]
    fn each_committed_move_gets_its_own_ordinal() {
        let mut run = AuthorizedDescent::deploy_on_map(9, DAY_SEED, 0).expect("deploy");
        let first = run.commit(Verb::Delve, [3u8; 32]).expect("floor 1");
        let second = run.commit(Verb::Smite, [4u8; 32]).expect("the guardian");
        assert_ne!(first.turn_hash, second.turn_hash);
        assert_eq!(run.step(), 2);
        assert!(receipt_carries_authorization(&first, &[3u8; 32]));
        assert!(
            !receipt_carries_authorization(&second, &[3u8; 32]),
            "the second move does not inherit the first's warrant"
        );
    }
}
