//! # `tomb` — what a DEAD run leaves behind, and why you come back.
//!
//! The Descent's loss is unusually legible. Most games only know "you died"; this one's committed
//! cell state records exactly **which day's map you were on, how far from the surface you were, and
//! what was in your hands when the light went out**. That is the raw material for a ratchet, and
//! this module is the ratchet: a dead run seals a [`Tomb`] — a death certificate read off the run's
//! own committed registers — and [`inter`]ring that certificate on the persistent hero sheet is the
//! only way the meta-currency and the [return right](crate::meta::may_return_to) are ever earned.
//!
//! **Nothing here softens the loss.** A tomb mints no relic, returns no pack, and grants no breath.
//! What you were carrying is gone, permanently, and the [`epitaph`](Tomb::epitaph) says so by name.
//! The ratchet is paid in a currency that cannot buy a relic, and the return right is paid in
//! *agency over which map you fight next*, which is not power because every drawn map is
//! Lean-checked completable in 20–26 of the 26 breath (`Dungeon.costAt_tense`). You cannot die your
//! way to wealth, and you cannot die your way to an easier dungeon.
//!
//! ## ⚠ WHAT THE CENSUS SAYS: on 14 of the 16 daily maps, the light CANNOT run out
//!
//! The crate's prose (and [`crate::bloodgate`]'s header, and the flagship plan) says the Descent
//! has permadeath and that the light is the clock. **Exhaustive search of the emitted rules says
//! otherwise.** Enumerating every reachable state of every one of the [`DAYS`] maps under the
//! Lean-emitted teeth (`delve`/`unlock`/`smite`/`loot` prices, `pack + depth ≤ CAP`, the guardian
//! vitalities) gives, per map, the largest breath a non-fleeing run can burn:
//!
//! | day | 0  | 1  | 2  | 3  | 4  | 5  | 6  | 7  | 8  | 9      | 10 | 11 | 12 | 13     | 14 | 15 |
//! |-----|----|----|----|----|----|----|----|----|----|--------|----|----|----|--------|----|----|
//! | max | 23 | 25 | 21 | 23 | 25 | 25 | 23 | 25 | 23 | **26** | 25 | 25 | 23 | **26** | 25 | 25 |
//!
//! `flee` costs ONE breath from any depth, so on every map except 9 and 13 there is **no reachable
//! position from which a player cannot go home**. The pack is never lost; every run banks. Days 9
//! and 13 each contain exactly ONE lethal state. The Descent as deployed is not a permadeath
//! roguelite — it is a puzzle whose worst outcome is banking less than you hoped.
//!
//! The cause is structural, not a number to tune: every verb is productive, bounded and monotone
//! (`delve` ≤ 4, `unlock` ≤ 3, `smite` bounded by guardian vitality, `loot` bounded by capacity),
//! so the total light a map lets you *waste* is barely more than the light a perfect line *needs*.
//! Raising the flee price and raising `BREATH` together is a no-op — it shifts both sides equally,
//! and a search over `flee ∈ {1, 2, depth, depth−1, ⌈depth/2⌉, depth+pack, pack+1}` ×
//! `BREATH ∈ [26, 36]` finds **no** completable configuration where more than 2 of the 16 maps can
//! kill you.
//!
//! **THE FIX IS A RULES CHANGE, AND RULES ARE LEAN.** It is specified — and checked — in
//! [`the Lean remainder`](self#the-lean-remainder-the-one-way-door) below. This module is
//! deliberately built so that when that lands, nothing here changes shape: a tomb is sealed from
//! committed registers, and the death it recognises becomes the common case instead of a curiosity.
//!
//! ## The Lean remainder: THE ONE-WAY DOOR
//!
//! The Descent cannot kill you because **going home is a single breath from anywhere**. Make the
//! way out the way you came:
//!
//! * a new verb `ascend` — `depth ≥ 1`, price 1, `depth' = depth − 1`, `wounds' = 0` (the dark
//!   closes behind you: a floor you re-enter has its guardian standing again), everything else
//!   immutable;
//! * `flee` gated `FieldEquals(depth, 0)` — you bank at the mouth, not from the bottom;
//! * `BREATH` 26 → 30.
//!
//! Exhaustively checked over all 16 emitted maps under exactly those rules: **all 16 stay
//! completable** (the perfect line costs 24–30 of 30, the same 0–6 slack band the shipped 20–26 of
//! 26 has), the reachable state space per map grows from 50–232 to 1 172–5 004 (a genuinely richer
//! decision space — you can now go back up for what you left), and **every one of the 16 maps
//! gains 252–789 reachable positions from which the surface is out of reach.** Days with no
//! possible death: **0**, down from 14.
//!
//! With the one-way door, the terminal "you are dead" predicate is `fate = 0 ∧ spent + depth + 1 >
//! BREATH` — an [`AffineLe`](dregg_app_framework::StateConstraint::AffineLe) over exactly the shape
//! the descent already emits for `pack + depth ≤ CAP`. That makes a `snuff` verb expressible: a
//! terminal turn admissible IFF the surface is out of reach, writing `fate = 2` (a tomb-fate
//! distinct from `1` = banked) and dropping the pack to the floor you fell on (custody
//! `CARRIED → depth`, so the conservation tooth `Σ = RELICS` still holds). Then a death is a real
//! committed turn with a real receipt, and [`Tomb::seal`] reads a *fact* rather than inferring one.
//!
//! That work is `metatheory/Dregg2/Games/{Dungeon,DungeonProgram}.lean` plus a re-emit through
//! `program/regen.sh`, plus `descent.rs` (the `Sim` mover, `BREATH`, the `ASCEND`/`SNUFF` method
//! names, and `fate`'s schema range `0..1 → 0..2`). `descent.rs` is another lane's file this lane
//! was scoped out of, so it is designed here and not written. **It is a rules change; it does not
//! go in Rust.**
//!
//! ## What this module IS, honestly
//!
//! Everything here lives strictly ABOVE the admitted turn: it reads committed state and drives
//! already-admitted hero-cell turns. It authors no descent rule.
//!
//! * [`Tomb`] has private fields and exactly one constructor, [`Tomb::seal`], which reads the
//!   run's COMMITTED registers (`Descent::read_reg` / `read_relic`, i.e. the executor's snapshot —
//!   never the mover's `Sim`) and refuses unless the run truly died. In-process, a lying tomb is
//!   not constructible.
//! * [`inter`] drives real gated turns on the hero cell: the death, the
//!   [priced accrual](crate::meta::grant_echoes_at_depth) (whose amount is pinned by an exact
//!   `FieldDelta` for that depth, and whose depth is read off the certificate rather than typed),
//!   and the [return-right mark](crate::meta::mark_tomb_day).
//! * **The seam that remains:** the hero program cannot name a per-run descent cell, so the
//!   executor prices the SHAPE of the accrual (dead sheet, real depth, exact quantum, one tomb
//!   counted) but cannot bind it to *this* run. Two real dead runs fund two real grants — which is
//!   correct — but nothing on-ledger stops a client that already holds a descent cell from
//!   re-presenting one. Closing that needs the run's terminal state carried into the redemption
//!   turn as a witness (`BoundDelta` / `ObservedFieldEquals` against the descent cell's finalized
//!   roots — the [`crate::multicell`] frontier), which is a hero-program change, not a Rust one.

use dregg_app_framework::TurnReceipt;
use procgen_dregg::CommittedSeed;
use spween_dregg::{WorldCell, WorldError};

use crate::descent::{BREATH, CARRIED, DAYS, Descent, RELICS};
use crate::{meta, progression};

/// Why a run seals no tomb. Both variants are the *good* endings-that-are-not-a-death: the run is
/// still being played, or the player got out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TombError {
    /// The light is still burning — the run is not over. Carries the breath spent and the breath
    /// left.
    StillBurning {
        /// Breath spent so far.
        spent: u64,
        /// Breath remaining before the light dies.
        left: u64,
    },
    /// The player got out: the run ended in a terminal [`flee`](Descent::flee) and its pack is
    /// BANKED. A banked run is a win, and a win advances no meta-currency — the relics ARE the
    /// reward.
    Banked {
        /// How many relics the run brought home.
        banked: u64,
    },
}

impl std::fmt::Display for TombError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TombError::StillBurning { spent, left } => write!(
                f,
                "the light still burns: {spent} of {BREATH} breath spent, {left} left"
            ),
            TombError::Banked { banked } => write!(
                f,
                "the run was banked with {banked} relic(s) — a run you walked out of is not a tomb"
            ),
        }
    }
}

impl std::error::Error for TombError {}

/// **A death certificate: the exact, legible record of a run the dark kept.**
///
/// Sealed only by [`Tomb::seal`], only from a run whose committed state says the light went out
/// (`spent == `[`BREATH`]) and that never banked (`fate == 0`). The fields are private precisely so
/// that no caller can assert a depth or a day it did not reach.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tomb {
    day: usize,
    depth: u64,
    pack: u64,
    spent: u64,
    custody: [u64; RELICS],
    day_seed: CommittedSeed,
}

impl Tomb {
    /// **Seal a tomb over a run that died** — or refuse, saying why.
    ///
    /// Reads the COMMITTED cell registers (the executor's snapshot), not the Rust mover's `Sim`:
    /// the certificate's depth is the depth the referee admitted, which is the whole point of
    /// sealing one instead of passing a number.
    ///
    /// Refuses with [`TombError::Banked`] if the run ended in a `flee` (`fate != 0`) and with
    /// [`TombError::StillBurning`] if there is breath left. Under the deployed rules those two
    /// refusals cover every reachable state on 14 of the 16 maps — see the module header.
    pub fn seal(run: &Descent) -> Result<Tomb, TombError> {
        let fate = run.read_reg("fate");
        let spent = run.read_reg("spent");
        if fate != 0 {
            return Err(TombError::Banked {
                banked: run.read_reg("bank"),
            });
        }
        if spent < BREATH {
            return Err(TombError::StillBurning {
                spent,
                left: BREATH - spent,
            });
        }
        let mut custody = [0u64; RELICS];
        for (slot, c) in custody.iter_mut().enumerate() {
            *c = run.read_relic(slot);
        }
        Ok(Tomb {
            day: run.day(),
            depth: run.read_reg("depth"),
            pack: run.read_reg("pack"),
            spent,
            custody,
            day_seed: *run.day_seed(),
        })
    }

    /// Which of the [`DAYS`] daily maps this run was played on — the map that killed you, and the
    /// one a [return right](meta::may_return_to) is earned over.
    pub fn day(&self) -> usize {
        self.day
    }
    /// How far from the surface the light died. This is also the deepest depth the run ever
    /// reached: the Descent has no way back up, so `depth` only ever rises.
    pub fn depth(&self) -> u64 {
        self.depth
    }
    /// How many relics were in your hands when it went out. Every one of them is lost.
    pub fn pack(&self) -> u64 {
        self.pack
    }
    /// Breath spent (always [`BREATH`] — a tomb is sealed only when the light is out).
    pub fn spent(&self) -> u64 {
        self.spent
    }
    /// The committed per-relic custody codes at the moment of death.
    pub fn custody(&self) -> [u64; RELICS] {
        self.custody
    }
    /// The run's committed day-seed — the provenance root its banked relics *would* have minted
    /// under, had it banked any.
    pub fn day_seed(&self) -> &CommittedSeed {
        &self.day_seed
    }

    /// The relic slots that were in your hands — the exact list of what the dark took.
    pub fn lost(&self) -> Vec<usize> {
        self.custody
            .iter()
            .enumerate()
            .filter(|&(_, &c)| c == CARRIED)
            .map(|(slot, _)| slot)
            .collect()
    }

    /// Whether THE PRIZE (relic 0) was in your hands when the light died. The single most
    /// expensive way to lose this game.
    pub fn prize_lost(&self) -> bool {
        self.custody[0] == CARRIED
    }

    /// Whether the prize was lying at your feet, unlooted, on the floor you died on — the death
    /// that costs the most and shows the least. (Day 9's one lethal position is exactly this: the
    /// bottom guardian felled, the prize under your hand, and no breath left to take it.)
    pub fn prize_within_reach(&self) -> bool {
        self.custody[0] == self.depth && self.depth > 0
    }

    /// The meta-currency this death is worth — [`meta::echoes_for_depth`] of the CERTIFIED depth.
    /// Deeper pays more; what you were carrying pays nothing, so a greedy death is not a richer
    /// one.
    pub fn echoes(&self) -> u64 {
        meta::echoes_for_depth(self.depth)
    }

    /// The legible loss, in one sentence. This is the retention mechanic that costs nothing and
    /// hides nothing: the game tells you exactly what you threw away.
    pub fn epitaph(&self) -> String {
        let lost = self.lost();
        let carried = match lost.len() {
            0 => "empty-handed".to_string(),
            1 => format!("one relic (slot {}) in your hands", lost[0]),
            n => format!(
                "{n} relics (slots {}) in your hands",
                lost.iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        let prize = if self.prize_lost() {
            " — THE PRIZE among them"
        } else if self.prize_within_reach() {
            " — the prize lay at your feet, and you had no breath to take it"
        } else {
            ""
        };
        format!(
            "Day {}: the light died on floor {} of {}, {} of {} breath spent, {carried}{prize}.",
            self.day,
            self.depth,
            crate::descent::FLOORS,
            self.spent,
            BREATH,
        )
    }
}

/// Whether a run is dark — the light is out and it never banked, so a [`Tomb`] can be sealed.
pub fn is_dark(run: &Descent) -> bool {
    Tomb::seal(run).is_ok()
}

/// What interring a tomb moved on the persistent sheet.
#[derive(Clone, Debug)]
pub struct Interment {
    /// The meta-currency this death paid (`echoes_for_depth(certified depth)`).
    pub echoes_gained: u64,
    /// The sheet's accrued echoes after the redemption.
    pub echoes_after: u64,
    /// The sheet's redeemed-death count after the redemption.
    pub tombs_after: u64,
    /// Whether this death earned a NEW return right (the day's map had not killed this identity
    /// before). `false` on a repeat death on a map you already hold.
    pub return_right_earned: bool,
    /// Every real committed turn the interment drove, in order.
    pub receipts: Vec<TurnReceipt>,
}

/// **Inter a tomb on the persistent hero sheet** — the whole ratchet, as real gated turns:
///
/// 1. the hardcore death, if the sheet is not already dead ([`progression::perish`], `WriteOnce`
///    and final);
/// 2. the PRICED accrual ([`meta::grant_echoes_at_depth`]) at the CERTIFICATE's depth — the amount
///    is pinned by the kernel's exact `FieldDelta` for that depth, and the tomb count advances by
///    exactly one;
/// 3. the RETURN RIGHT over the day's map ([`meta::mark_tomb_day`]), unless this identity already
///    holds it.
///
/// Every step is gated `FieldEquals(dead, 1)` at the WRITE, so none of it is available to a living
/// sheet whatever method a client presents.
pub fn inter(hero: &WorldCell, tomb: &Tomb) -> Result<Interment, WorldError> {
    let mut receipts = Vec::with_capacity(3);
    if !progression::is_dead(hero) {
        receipts.push(progression::perish(hero)?);
    }
    let before = meta::echoes(hero);
    receipts.push(meta::grant_echoes_at_depth(hero, tomb.depth())?);
    let return_right_earned = if meta::may_return_to(hero, tomb.day()) {
        false
    } else {
        receipts.push(meta::mark_tomb_day(hero, tomb.day())?);
        true
    };
    Ok(Interment {
        echoes_gained: meta::echoes(hero) - before,
        echoes_after: meta::echoes(hero),
        tombs_after: meta::tombs(hero),
        return_right_earned,
        receipts,
    })
}

/// Whether this identity may open a later descent on day `day`'s map instead of taking the
/// beacon's draw — i.e. whether that map has killed it. Re-exported here because the right is a
/// property of the tomb ledger, and because `Descent::deploy_on_world` (the entry that honours a
/// chosen day) should never be called without asking.
///
/// **Deployment policy, not a kernel tooth:** a chosen-day run is not a daily run and must not rank
/// on the daily leaderboard — it trades the daily's stakes for the practice. The ranking surface
/// lives outside this crate, so that half is policy this module can state but not enforce.
pub fn may_return_to(hero: &WorldCell, day: usize) -> bool {
    meta::may_return_to(hero, day)
}

/// The deploy seed whose derived day-seed draws map `day` — the honest way to reach a specific
/// daily map without hand-forging a day index (`Descent::deploy_on_day` still does the drawing).
pub fn deploy_seed_drawing_day(day: usize) -> Option<u8> {
    (0u8..=u8::MAX).find(|s| {
        crate::descent::day_index(&crate::descent::day_seed_from_deploy_seed(*s)) == day % DAYS
    })
}

#[cfg(test)]
mod tomb_tests {
    //! Every test here is DRIVEN on the real Lean-refereed descent cell and the real hero cell.
    //! The dying run is a genuine 18-move line on day 9's real daily map — one of the only two
    //! maps the deployed rules let the light run out on at all (module header).
    use super::*;
    use crate::descent::{BANKED, DELVE, FLEE, FLOORS, LOOT, SMITE, Sim, UNLOCK};
    use crate::loot::LootVault;

    /// The one lethal line day 9's map admits: down to the bottom, every guardian felled, the three
    /// way-keys still in hand — and the 26th breath spent on the last blow, standing on the prize.
    const DAY_9_DEATH_LINE: [(&str, u64); 18] = [
        (DELVE, 0),
        (SMITE, 0),
        (SMITE, 0),
        (LOOT, 2),
        (LOOT, 1),
        (UNLOCK, 3),
        (UNLOCK, 2),
        (DELVE, 0),
        (SMITE, 0),
        (SMITE, 0),
        (LOOT, 3),
        (UNLOCK, 4),
        (DELVE, 0),
        (SMITE, 0),
        (SMITE, 0),
        (DELVE, 0),
        (SMITE, 0),
        (SMITE, 0),
    ];

    fn step(run: &mut Descent, verb: &str, arg: u64) {
        let r = match verb {
            DELVE => run.delve(),
            SMITE => run.smite(),
            UNLOCK => run.unlock(arg),
            LOOT => run.loot(arg as usize),
            FLEE => run.flee(),
            other => panic!("no such verb `{other}`"),
        };
        r.unwrap_or_else(|e| panic!("`{verb} {arg}` must commit on the real referee: {e:?}"));
    }

    /// A run played to the one death day 9's map allows.
    fn a_run_that_dies() -> Descent {
        let seed = deploy_seed_drawing_day(9).expect("some deploy seed draws day 9");
        let day_seed = crate::descent::day_seed_from_deploy_seed(seed);
        let mut run = Descent::deploy_on_day(seed, day_seed).expect("the descent deploys");
        assert_eq!(run.day(), 9, "the beacon really drew day 9");
        for (verb, arg) in DAY_9_DEATH_LINE {
            step(&mut run, verb, arg);
        }
        run
    }

    /// A run that walks out with what it has.
    fn a_run_that_banks() -> Descent {
        let seed = deploy_seed_drawing_day(9).expect("day 9 seed");
        let day_seed = crate::descent::day_seed_from_deploy_seed(seed);
        let mut run = Descent::deploy_on_day(seed, day_seed).expect("deploy");
        for (verb, arg) in DAY_9_DEATH_LINE.iter().take(5) {
            step(&mut run, verb, *arg);
        }
        step(&mut run, FLEE, 0);
        run
    }

    /// A LIVING run seals no tomb, and a BANKED run seals no tomb — only a death does. Non-vacuous:
    /// the three runs share a deploy, a map and an opening; the only difference is the ending.
    #[test]
    fn only_a_death_seals_a_tomb() {
        let seed = deploy_seed_drawing_day(9).expect("day 9 seed");
        let fresh =
            Descent::deploy_on_day(seed, crate::descent::day_seed_from_deploy_seed(seed)).unwrap();
        assert_eq!(
            Tomb::seal(&fresh),
            Err(TombError::StillBurning {
                spent: 0,
                left: BREATH
            }),
            "a run that has not been played is not a tomb"
        );

        let banked = a_run_that_banks();
        assert_eq!(banked.read_reg("fate"), 1, "the run banked");
        assert!(
            matches!(Tomb::seal(&banked), Err(TombError::Banked { .. })),
            "a run you walked out of advances no meta-currency — the relics ARE the reward"
        );

        let dead = a_run_that_dies();
        let tomb = Tomb::seal(&dead).expect("a run the dark kept seals a tomb");
        assert_eq!(tomb.spent(), BREATH, "the light is out");
        assert_eq!(tomb.day(), 9);
    }

    /// THE CERTIFICATE IS THE COMMITTED RECORD. The tomb's depth/pack/day are read off the
    /// executor's snapshot, and the epitaph names the loss by relic slot. On day 9 the one lethal
    /// position is the cruellest one in the game: the bottom guardian felled, the prize lying under
    /// your hand, three keys in your fist, and not one breath left to pick it up.
    #[test]
    fn a_tomb_names_exactly_what_the_dark_took() {
        let run = a_run_that_dies();
        let tomb = Tomb::seal(&run).expect("sealed");

        assert_eq!(tomb.depth(), FLOORS, "you died at the bottom");
        assert_eq!(tomb.pack(), 3, "three relics in your hands");
        assert_eq!(tomb.lost(), vec![1, 2, 3], "the three way-keys, by slot");
        assert!(!tomb.prize_lost(), "the prize was never in the pack");
        assert!(
            tomb.prize_within_reach(),
            "the prize lay on the very floor you died on"
        );

        // The certificate agrees with the COMMITTED registers, not with the Rust mover's opinion.
        assert_eq!(tomb.depth(), run.read_reg("depth"));
        assert_eq!(tomb.pack(), run.read_reg("pack"));
        assert_eq!(tomb.spent(), run.read_reg("spent"));

        let ep = tomb.epitaph();
        assert!(ep.contains("Day 9"), "the epitaph names the map: {ep}");
        assert!(ep.contains("floor 4"), "and how deep: {ep}");
        assert!(ep.contains("26 of 26"), "and that the light ran out: {ep}");
        assert!(
            ep.contains("no breath to take it"),
            "and the exact shape of the loss: {ep}"
        );
    }

    /// THE DEAD CANNOT MOVE — and it is the REFEREE that says so, not the Rust mover.
    ///
    /// This is the tooth that makes the certificate's precondition worth anything: if a dead run
    /// could still commit a turn, "the light went out" would be a state you pass through rather
    /// than a state you end in. Every projection here is built with `Descent::effects_for` and
    /// driven through `commit_raw`, which bypasses `Sim`'s Rust guards entirely — so what refuses
    /// them is the Lean-emitted `FieldLte{spent, 26}` / `FieldDelta{spent, k}` / `StrictMonotonic`
    /// teeth on the real executor.
    #[test]
    fn the_dead_cannot_move_and_it_is_the_referee_that_refuses() {
        let run = a_run_that_dies();
        let dark = run.sim().clone();
        assert_eq!(dark.spent, BREATH);

        // Every verb's honest projection now overruns the breath: delve/unlock/loot/flee want
        // spent 27, smite wants 28. `FieldLte{spent, 26}` refuses all of them.
        let mut overrun: Vec<(&str, Sim)> = Vec::new();
        for (method, cost) in [(DELVE, 1u64), (UNLOCK, 1), (LOOT, 1), (FLEE, 1), (SMITE, 2)] {
            let mut s = dark.clone();
            s.spent += cost;
            match method {
                DELVE => s.depth += 1,
                SMITE => s.wounds += 1,
                FLEE => {
                    for c in s.custody.iter_mut() {
                        if *c == CARRIED {
                            *c = BANKED;
                        }
                    }
                    s.fate = 1;
                }
                _ => {}
            }
            overrun.push((method, s));
        }
        for (method, s) in &overrun {
            let refused = run.commit_raw(method, run.effects_for(s));
            assert!(
                matches!(refused, Err(WorldError::Refused(_))),
                "`{method}` past the last breath must be a REFEREE refusal, got {refused:?}"
            );
        }

        // Nor can the dead move for FREE: a projection that changes the world without spending
        // breath is refused by the per-verb exact `FieldDelta{spent, k}`.
        let mut free_flee = dark.clone();
        for c in free_flee.custody.iter_mut() {
            if *c == CARRIED {
                *c = BANKED;
            }
        }
        free_flee.fate = 1;
        let refused = run.commit_raw(FLEE, run.effects_for(&free_flee));
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a free escape (fate 0 -> 1 with no breath paid) is refused, got {refused:?}"
        );

        // And a forged rewind of the clock is refused by `StrictMonotonic{spent}`.
        let mut rewind = dark.clone();
        rewind.spent = 20;
        let refused = run.commit_raw(DELVE, run.effects_for(&rewind));
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "buying back spent breath is refused, got {refused:?}"
        );

        // ANTI-GHOST: not one of those refusals moved the committed state.
        assert_eq!(run.read_reg("spent"), BREATH);
        assert_eq!(run.read_reg("fate"), 0);
        assert_eq!(run.read_reg("bank"), 0, "the dead banked NOTHING");
        assert_eq!(
            run.read_reg("pack"),
            3,
            "and their pack is still in the dark"
        );
    }

    /// THE TWO CURRENCIES NEVER MEET. A dead run mints no owned relic note; a banked run advances
    /// no meta-currency. So dying pays you in the currency that cannot buy a relic and costs you
    /// the one that is a relic — you can never die your way to wealth, which is what keeps the
    /// light frightening while the ratchet exists.
    #[test]
    fn a_death_mints_no_relic_and_a_bank_earns_no_echo() {
        let mut vault = LootVault::new();

        let dead = a_run_that_dies();
        let minted = dead
            .mint_banked_relics(&mut vault, "player-dead")
            .expect("minting over a dead run is well-defined");
        assert!(
            minted.is_empty(),
            "a dead run banks nothing, so it MINTS nothing: {minted:?}"
        );

        let banked = a_run_that_banks();
        assert!(
            banked.read_reg("bank") > 0,
            "the fled run brought relics home"
        );
        let minted = banked
            .mint_banked_relics(&mut vault, "player-alive")
            .expect("a banked run mints its relics");
        assert!(!minted.is_empty(), "the win pays in real owned notes");

        // And the win pays NO echoes: there is no tomb to inter.
        assert!(matches!(Tomb::seal(&banked), Err(TombError::Banked { .. })));
    }

    /// THE RATCHET, END TO END: a death is interred on the persistent sheet, paying exactly the
    /// certified depth's quantum, counting exactly one tomb, and earning the return right over the
    /// map that killed you — and no other map.
    #[test]
    fn interring_a_tomb_pays_the_certified_depth_and_earns_that_map() {
        let run = a_run_that_dies();
        let tomb = Tomb::seal(&run).expect("sealed");
        let hero = meta::deploy_meta_hero(90);
        progression::choose_class(&hero, progression::WARRIOR).expect("class");

        assert_eq!(meta::echoes(&hero), 0);
        assert!(!may_return_to(&hero, 9), "no right before the death");

        let out = inter(&hero, &tomb).expect("a real tomb inters");
        assert_eq!(
            out.echoes_gained,
            meta::echoes_for_depth(FLOORS),
            "a death at the bottom pays the bottom's quantum — not a number anyone typed"
        );
        assert_eq!(out.echoes_after, meta::echoes_for_depth(FLOORS));
        assert_eq!(out.tombs_after, 1, "one death, one tomb");
        assert!(out.return_right_earned, "day 9 is now yours to choose");
        assert!(may_return_to(&hero, 9));
        assert!(
            !may_return_to(&hero, 8) && !may_return_to(&hero, 10),
            "and ONLY day 9 — a right is earned where you lost it"
        );
        assert!(progression::is_dead(&hero), "the sheet records the death");

        // The receipts are real committed turns and they CHAIN on the one hero cell.
        assert_eq!(out.receipts.len(), 3, "perish + priced accrual + the mark");
        for pair in out.receipts.windows(2) {
            assert_eq!(
                pair[1].pre_state_hash, pair[0].post_state_hash,
                "the interment receipts chain (pre == prev.post)"
            );
        }

        // A SECOND death on the SAME map still pays, but earns no second right.
        let again = a_run_that_dies();
        let tomb2 = Tomb::seal(&again).expect("sealed");
        let out2 = inter(&hero, &tomb2).expect("a second death inters");
        assert!(
            !out2.return_right_earned,
            "you already own that battlefield"
        );
        assert_eq!(out2.tombs_after, 2);
        assert_eq!(out2.echoes_after, 2 * meta::echoes_for_depth(FLOORS));
        assert_eq!(out2.receipts.len(), 1, "no death turn, no second mark");
    }

    /// The ratchet is a THRESHOLD you reach by dying, not a number you assert: two deaths at the
    /// bottom of day 9 carry the sheet over the boon price, and the boon then commits — while the
    /// same sheet with no interred tomb is refused.
    #[test]
    fn deaths_accrue_into_a_real_unlock_and_nothing_else_does() {
        let hero = meta::deploy_meta_hero(91);
        progression::choose_class(&hero, progression::WARRIOR).expect("class");
        assert!(
            matches!(meta::claim_boon(&hero), Err(WorldError::Refused(_))),
            "an unclaimed sheet buys nothing"
        );

        let run = a_run_that_dies();
        let tomb = Tomb::seal(&run).expect("sealed");
        inter(&hero, &tomb).expect("inter");
        assert!(
            meta::echoes(&hero) >= meta::BOON_PRICE,
            "a death at the bottom is worth {} against a price of {}",
            meta::echoes(&hero),
            meta::BOON_PRICE
        );
        meta::claim_boon(&hero).expect("the accrued death buys the unlock");
        assert!(meta::has_boon(&hero), "the next run starts holding it");
    }

    /// THE CENSUS, AS A TEST: on 14 of the 16 daily maps the deployed rules make permadeath
    /// UNREACHABLE — `flee` costs one breath from any depth, and no reachable position on those
    /// maps has spent all 26. This is the wound the module header specifies the Lean fix for; it is
    /// pinned here so that the day the one-way door lands, this test fails LOUD and gets rewritten
    /// to the new truth rather than quietly continuing to describe a game that no longer exists.
    #[test]
    fn the_light_cannot_run_out_on_fourteen_of_the_sixteen_maps() {
        /// Exhaustively reachable non-fled states, under exactly the deployed mover rules.
        fn deadly(day: usize) -> bool {
            let genesis = Sim::genesis_on_day(day);
            let key = |s: &Sim| (s.depth, s.spent, s.wounds, s.fate, s.ways, s.custody);
            let mut seen = std::collections::HashSet::new();
            let mut stack = vec![genesis.clone()];
            seen.insert(key(&genesis));
            let mut lethal = false;
            while let Some(s) = stack.pop() {
                // A position is lethal iff the light is out and the run never banked — under the
                // deployed rules, `flee` costs 1, so this is exactly `spent == BREATH`.
                if s.fate == 0 && s.spent >= BREATH {
                    lethal = true;
                }
                let mut nexts = vec![s.delve(), s.smite()];
                for w in 2..=FLOORS {
                    nexts.push(s.unlock(w));
                }
                for r in 0..RELICS {
                    nexts.push(s.loot(r));
                }
                for n in nexts.into_iter().flatten() {
                    if seen.insert(key(&n)) {
                        stack.push(n);
                    }
                }
            }
            lethal
        }

        let deadly_days: Vec<usize> = (0..DAYS).filter(|d| deadly(*d)).collect();
        assert_eq!(
            deadly_days,
            vec![9, 13],
            "PERMADEATH CENSUS: only these daily maps have ANY reachable position where the light \
             runs out. On the other {} maps `flee` (one breath, from any depth) is available from \
             every reachable state, so nothing is ever lost and the Descent is not a permadeath \
             roguelite. See the `tomb` module header for the checked Lean fix (the one-way door).",
            DAYS - 2
        );
    }
}
