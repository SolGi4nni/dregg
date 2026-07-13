//! # `session` — SESSION-KEY play onboarding as MACAROON ATTENUATION.
//!
//! The accessibility unlock (`docs/GAME-STRATEGY.md` decision #2): a normal person plays a
//! **whole session** without re-signing every move and without gas. This is NOT a new trust
//! model — it is the existing macaroon attenuation applied to *play*:
//!
//! > **a session key = a caveat-bounded delegation of the player's play cap; the paymaster =
//! > the existing run-credit ledger.**
//!
//! ## The play cap, as a macaroon grant
//!
//! A [`PlayGrant`] is the byte-faithful play analogue of the SDK's tool mandate
//! ([`dregg_sdk::tool_gateway::ToolGrant`], itself the Rust mirror of the Lean
//! `Dregg2.Apps.ToolAccessDelegation.Grant`). Where the tool mandate is
//! `{tool_id, deadline, rate_limit}`, a play grant is `{scope, deadline, turn_budget}`:
//!
//! * **SCOPE** ([`PlayScope`]) — which offering(s) the cap may play. The root player cap is
//!   [`PlayScope::Any`] (any offering in the catalog); a session key narrows it to
//!   [`PlayScope::Offering`] (one game).
//! * **DEADLINE** — the session's expiry (a clock/height caveat): a turn presented after it is
//!   refused.
//! * **TURN BUDGET** — the RATE: at most `turn_budget` committed turns ride this key.
//!
//! [`play_admit`] is the folded admission predicate, the play mirror of
//! [`dregg_sdk::tool_gateway::deleg_admit`]:
//! `SCOPE(target) ∧ now ≤ deadline ∧ new = old+1 ∧ 0 ≤ old ∧ new ≤ turn_budget`. Every conjunct
//! fail-closed, each negation a named leg ([`PlayRefusal`]) so an audit sees which caveat bit.
//!
//! ## The two teeth that make it a delegation, not just a config
//!
//! 1. **Non-amplification** ([`refines`]) — a session key is minted by [`open_session`], which
//!    REFUSES a child grant that would *widen* the parent (a broader scope, a later deadline, a
//!    bigger turn budget). Attenuation only narrows — the macaroon law. This is the tooth the
//!    SDK's `deleg_admit` alone does not carry (it checks a *fixed* grant); a delegation must
//!    also prove the grant it hands down is no stronger than the one it holds.
//! 2. **No per-move re-sign** — a whole session's turns commit under ONE [`SessionKey`]. Each
//!    [`SessionKey::play`] admits the turn against the key's caveats and advances the key's own
//!    turn counter; the player signs (opens) once, then plays a session's worth of moves. The
//!    substrate turn itself still commits under the world cap and the real executor referees the
//!    move — the session key gates *authorization to advance*, it does not replace the executor.
//!
//! ## The paymaster (gasless from the player's view)
//!
//! [`SessionKey::play`] draws the move's [`crate::RunCost`] from a [`Paymaster`] — the play cost
//! is covered by a pre-funded credit balance, so the player never signs or funds a per-move
//! transaction. [`CreditPaymaster`] is the real binding over [`dregg_pay::CreditLedger`] (the
//! existing run-credit ledger): a paid move is a real `CreditLedger::debit`. A refused move
//! (out-of-scope / past-deadline / over-budget, OR an executor refusal of the game move itself)
//! costs NOTHING — the charge only lands on a genuinely committed turn (anti-ghost).
//!
//! ## Custodial / passkey onboarding (the named seam)
//!
//! [`Custodian`] is the deriving identity: a service holds the root play cap and mints
//! per-session attenuated keys for custodial players, who never touch a wallet. `identity_for`
//! is where a passkey / WebAuthn assertion would derive the player's stable identity — here it
//! derives a stable identity from an opaque handle (a Discord id, a credential id). **What's
//! real:** the attenuated, non-amplifying delegation and the credit paymaster. **The named
//! seam:** the passkey/WebAuthn UX and the operational custody of the custodian's key (an
//! operator secret-store concern, not built here).

use crate::{Action, DreggIdentity, Offering, Outcome, RunCost};

// ─────────────────────────────────────────────────────────────────────────────
// SCOPE — which offering(s) a play cap may play.
// ─────────────────────────────────────────────────────────────────────────────

/// **The SCOPE caveat** — which offering(s) a play cap authorizes. The root player cap is
/// [`PlayScope::Any`]; a session key narrows it to exactly one [`PlayScope::Offering`]. An
/// offering is named by a stable id ([`PlayScope::of_offering`], `blake3(key)` low bits), so the
/// SAME offering key always maps to the SAME scope id across processes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlayScope {
    /// The whole catalog — the root player cap may play any offering. Narrowable to one offering.
    Any,
    /// Scoped to exactly one offering (`blake3(offering_key)` low bits).
    Offering(i64),
}

impl PlayScope {
    /// The stable scope id for an offering key (`"dungeon"`, `"council"`, …) — `blake3(key)`'s
    /// low 8 bytes as an `i64` (masked non-negative so it reads as a plain id). The SAME key
    /// always yields the SAME [`PlayScope::Offering`].
    pub fn of_offering(key: &str) -> PlayScope {
        let h = blake3::hash(key.as_bytes());
        let b = h.as_bytes();
        let raw = u64::from_le_bytes(b[..8].try_into().unwrap());
        PlayScope::Offering((raw >> 1) as i64)
    }

    /// The raw offering id a specific scope carries (`None` for [`PlayScope::Any`]).
    pub fn offering_id(&self) -> Option<i64> {
        match self {
            PlayScope::Any => None,
            PlayScope::Offering(id) => Some(*id),
        }
    }

    /// Does this scope ADMIT playing the offering identified by `target`? [`PlayScope::Any`]
    /// admits any target; [`PlayScope::Offering`] admits only its own id. (The scope conjunct of
    /// [`play_admit`], the play analogue of `tool == g.tool_id`.)
    pub fn admits(&self, target: i64) -> bool {
        match self {
            PlayScope::Any => true,
            PlayScope::Offering(id) => *id == target,
        }
    }

    /// Does this (parent) scope COVER `child` — i.e. is `child` no wider than `self`? `Any`
    /// covers everything; a specific offering covers only itself; a specific offering does NOT
    /// cover `Any` (that would widen). The scope leg of the non-amplification law ([`refines`]).
    pub fn covers(&self, child: &PlayScope) -> bool {
        match (self, child) {
            (PlayScope::Any, _) => true,
            (PlayScope::Offering(a), PlayScope::Offering(b)) => a == b,
            (PlayScope::Offering(_), PlayScope::Any) => false,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE PLAY GRANT — the caveat-bounded play cap (the macaroon).
// ─────────────────────────────────────────────────────────────────────────────

/// **A play cap, as a macaroon grant** — the play analogue of
/// [`dregg_sdk::tool_gateway::ToolGrant`]. A root player cap and every session key are both
/// `PlayGrant`s; a session key is just a *narrower* one ([`open_session`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlayGrant {
    /// The SCOPE caveat — which offering(s) this cap may play.
    pub scope: PlayScope,
    /// The DEADLINE caveat — the expiry height/clock; a turn at `now > deadline` is refused.
    pub deadline: i64,
    /// The RATE — the maximum number of committed turns that may ride this cap.
    pub turn_budget: i64,
}

impl PlayGrant {
    /// A **root player cap** over `scope`, valid until `deadline`, good for `turn_budget` turns.
    /// The thing a player (or a [`Custodian`] on their behalf) holds and delegates session keys
    /// from.
    pub fn root(scope: PlayScope, deadline: i64, turn_budget: i64) -> PlayGrant {
        PlayGrant {
            scope,
            deadline,
            turn_budget,
        }
    }
}

/// **The folded play-admission predicate** — the play mirror of
/// [`dregg_sdk::tool_gateway::deleg_admit`] (the Rust twin of the Lean
/// `Dregg2.Apps.ToolAccessDelegation.delegAdmit`). Returns `true` IFF the grant admits the turn
/// advancing the counter `old → new`, presented at height `now` to play offering `target`.
/// Fail-closed on every conjunct, in the SAME order as the tool mandate:
///
/// 1. SCOPE — `g.scope.admits(target)`;
/// 2. DEADLINE — `now <= g.deadline`;
/// 3. single-step increment — `new == old + 1`;
/// 4. sane prior count — `0 <= old`;
/// 5. RATE — `new <= g.turn_budget`.
pub fn play_admit(g: &PlayGrant, now: i64, target: i64, old: i64, new: i64) -> bool {
    g.scope.admits(target)
        && now <= g.deadline
        && new == old + 1
        && 0 <= old
        && new <= g.turn_budget
}

// ─────────────────────────────────────────────────────────────────────────────
// NON-AMPLIFICATION — attenuation only narrows.
// ─────────────────────────────────────────────────────────────────────────────

/// Why a delegation was REFUSED for AMPLIFYING — the child grant would be *stronger* than the
/// parent on some caveat. Each variant is one leg of the non-amplification law ([`refines`]),
/// the macaroon guarantee that attenuation only narrows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Amplification {
    /// SCOPE widened — the child would play an offering (or the whole catalog) the parent may not.
    ScopeWidened {
        /// The parent's scope.
        parent: PlayScope,
        /// The wider child scope the delegation asked for.
        child: PlayScope,
    },
    /// DEADLINE extended — the child would live past the parent's expiry.
    DeadlineExtended {
        /// The parent's deadline.
        parent: i64,
        /// The later child deadline the delegation asked for.
        child: i64,
    },
    /// TURN BUDGET raised — the child would grant more turns than the parent holds.
    BudgetRaised {
        /// The parent's turn budget.
        parent: i64,
        /// The larger child budget the delegation asked for.
        child: i64,
    },
}

impl std::fmt::Display for Amplification {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Amplification::ScopeWidened { parent, child } => write!(
                f,
                "delegation amplifies SCOPE: parent {parent:?} does not cover child {child:?}"
            ),
            Amplification::DeadlineExtended { parent, child } => write!(
                f,
                "delegation amplifies DEADLINE: child expiry {child} is past parent expiry {parent}"
            ),
            Amplification::BudgetRaised { parent, child } => write!(
                f,
                "delegation amplifies TURN BUDGET: child {child} exceeds parent {parent}"
            ),
        }
    }
}

impl std::error::Error for Amplification {}

/// **The non-amplification law** — `child` REFINES `parent` iff it only narrows every caveat:
/// its scope is covered, its deadline is no later, its turn budget no larger. Returns the named
/// [`Amplification`] leg on the first violation. This is the macaroon attenuation guarantee: a
/// delegated cap can never be stronger than the one it was minted from.
pub fn refines(parent: &PlayGrant, child: &PlayGrant) -> Result<(), Amplification> {
    if !parent.scope.covers(&child.scope) {
        return Err(Amplification::ScopeWidened {
            parent: parent.scope,
            child: child.scope,
        });
    }
    if child.deadline > parent.deadline {
        return Err(Amplification::DeadlineExtended {
            parent: parent.deadline,
            child: child.deadline,
        });
    }
    if child.turn_budget > parent.turn_budget {
        return Err(Amplification::BudgetRaised {
            parent: parent.turn_budget,
            child: child.turn_budget,
        });
    }
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// THE SESSION KEY — the minted, attenuated play delegation.
// ─────────────────────────────────────────────────────────────────────────────

/// Why the SESSION KEY refused a turn IN-BAND — the negation of one [`play_admit`] conjunct.
/// The play mirror of [`dregg_sdk::tool_gateway::GatewayRefusal`]. A refusal is a value (never a
/// panic), and NO turn advances and NO credit is charged (anti-ghost).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlayRefusal {
    /// SCOPE: the offering played is not the one this session key is scoped to.
    OutOfScope {
        /// The offering id the turn tried to play.
        presented: i64,
        /// The scope the session key grants.
        grant: PlayScope,
    },
    /// DEADLINE: the turn was presented after the session's expiry.
    PastDeadline {
        /// The height the turn was presented at.
        now: i64,
        /// The session's expiry height.
        deadline: i64,
    },
    /// RATE: the turn budget is exhausted (the counter is already at the granted ceiling).
    OverTurnBudget {
        /// The committed-turn count before this (refused) turn.
        turns_taken: i64,
        /// The granted turn budget.
        turn_budget: i64,
    },
}

impl std::fmt::Display for PlayRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlayRefusal::OutOfScope { presented, grant } => write!(
                f,
                "turn out of scope: played offering {presented}, session key grants {grant:?}"
            ),
            PlayRefusal::PastDeadline { now, deadline } => write!(
                f,
                "turn past deadline: presented at height {now}, session expired at {deadline}"
            ),
            PlayRefusal::OverTurnBudget {
                turns_taken,
                turn_budget,
            } => write!(
                f,
                "turn over budget: {turns_taken} turns already taken, session grants {turn_budget}"
            ),
        }
    }
}

impl std::error::Error for PlayRefusal {}

/// **A SESSION KEY — a caveat-bounded delegation of the player's play cap.** Minted by
/// [`open_session`] (or [`Custodian::open_session_for`]) as a *narrowing* of a root
/// [`PlayGrant`], it authorizes a whole session's worth of turns for one `holder` WITHOUT a
/// per-move re-sign: [`SessionKey::play`] admits each turn against the key's caveats and advances
/// its own turn counter. The player opens once; the substrate still refs every move.
#[derive(Clone, Debug)]
pub struct SessionKey {
    /// The attenuated grant (scope ∧ deadline ∧ turn budget) — no wider than the parent it was
    /// minted from ([`refines`]).
    grant: PlayGrant,
    /// The identity every turn under this key is attributed to (the player — self-custody or
    /// custodial). The paymaster charges this holder's balance.
    holder: DreggIdentity,
    /// The committed-turn counter (the RATE meter). Advances only when a turn actually commits;
    /// a refused move does not consume budget (matching `deleg_admit`'s committed-call count).
    turns_taken: i64,
}

impl SessionKey {
    /// The attenuated grant this key carries.
    pub fn grant(&self) -> &PlayGrant {
        &self.grant
    }

    /// The player this key plays for.
    pub fn holder(&self) -> &DreggIdentity {
        &self.holder
    }

    /// Committed turns taken so far under this key.
    pub fn turns_taken(&self) -> i64 {
        self.turns_taken
    }

    /// Turns remaining on the key (`turn_budget - turns_taken`).
    pub fn turns_remaining(&self) -> i64 {
        self.grant.turn_budget - self.turns_taken
    }

    /// **Admit a turn under this session key** (no re-sign) — the in-band caveat gate. Returns
    /// `Ok(())` iff [`play_admit`] holds for playing `target` at height `now` advancing the
    /// counter; otherwise the named [`PlayRefusal`] leg. Does NOT advance the counter (a landed
    /// turn does, via [`SessionKey::play`] / [`SessionKey::record_committed_turn`]).
    pub fn admit(&self, now: i64, target: i64) -> Result<(), PlayRefusal> {
        let old = self.turns_taken;
        let new = old + 1;
        if play_admit(&self.grant, now, target, old, new) {
            Ok(())
        } else {
            Err(self.diagnose(now, target))
        }
    }

    /// The named leg that bit (fail-closed diagnosis, SCOPE → DEADLINE → RATE, matching the
    /// admit order).
    fn diagnose(&self, now: i64, target: i64) -> PlayRefusal {
        if !self.grant.scope.admits(target) {
            PlayRefusal::OutOfScope {
                presented: target,
                grant: self.grant.scope,
            }
        } else if now > self.grant.deadline {
            PlayRefusal::PastDeadline {
                now,
                deadline: self.grant.deadline,
            }
        } else {
            PlayRefusal::OverTurnBudget {
                turns_taken: self.turns_taken,
                turn_budget: self.grant.turn_budget,
            }
        }
    }

    /// Advance the committed-turn counter — called after a turn genuinely commits. Public so a
    /// caller driving an offering with a bespoke advance signature (e.g.
    /// [`crate::character::AdventurerOffering::advance`]) can use [`SessionKey::admit`] + its own
    /// advance + this, without routing through [`SessionKey::play`].
    pub fn record_committed_turn(&mut self) {
        self.turns_taken += 1;
    }

    /// **Play ONE turn under this session key** — the whole gasless, no-re-sign move, over any
    /// [`Offering`]:
    ///
    /// 1. **admit** the turn against the key's caveats ([`SessionKey::admit`] for `target`) —
    ///    a refusal returns [`PlayOutcome::Refused`] with NO advance and NO charge (anti-ghost);
    /// 2. **check the paymaster can cover** the move's [`RunCost`] — if not,
    ///    [`PlayOutcome::Unpaid`] with NO advance (anti-ghost);
    /// 3. **advance the real offering** (`offering.advance` — the executor is the referee);
    /// 4. iff it LANDED, **charge the paymaster** (the real credit debit) and **advance the key's
    ///    turn counter**. An executor refusal of the game move itself costs nothing and consumes
    ///    no budget.
    ///
    /// `target` is the scope id of the offering being played (e.g.
    /// `PlayScope::of_offering("dungeon").offering_id()`); playing an offering the key is not
    /// scoped to is the out-of-scope tooth.
    pub fn play<O: Offering, P: Paymaster>(
        &mut self,
        target: i64,
        offering: &O,
        session: &mut O::Session,
        input: Action,
        now: i64,
        paymaster: &P,
    ) -> PlayOutcome {
        // §1 — the session-key caveat gate (SCOPE ∧ DEADLINE ∧ RATE). No advance, no charge.
        if let Err(refusal) = self.admit(now, target) {
            return PlayOutcome::Refused(refusal);
        }

        // §2 — the paymaster must be able to cover the move BEFORE we touch the substrate, so an
        // unpayable move commits nothing (anti-ghost). The price is the offering's own RunCost.
        let cost = offering.price(&input);
        if !paymaster.can_cover(&self.holder, cost) {
            return PlayOutcome::Unpaid(PaymasterError::Insufficient {
                who: self.holder.clone(),
                needed: cost.credits,
                balance: paymaster.balance(&self.holder),
            });
        }

        // §3 — the real turn on the substrate, attributed to the holder. The executor is the
        // sole referee: an illegal game move is a real refusal here.
        let outcome = offering.advance(session, input, self.holder.clone());

        match &outcome {
            Outcome::Landed { .. } => {
                // §4 — a genuine committed turn: charge the paymaster (the real ledger move) and
                // advance the key's counter. The charge cannot fail here (we pre-checked cover,
                // single-threaded), but a real Err is surfaced honestly rather than swallowed.
                match paymaster.charge(&self.holder, cost) {
                    Ok(credits_left) => {
                        self.record_committed_turn();
                        PlayOutcome::Committed {
                            outcome,
                            charged: cost,
                            credits_left,
                            turns_taken: self.turns_taken,
                        }
                    }
                    Err(e) => PlayOutcome::Unpaid(e),
                }
            }
            // The executor refused the game move itself — no charge, no counter advance.
            Outcome::Refused(_) => PlayOutcome::ExecutorRefused(outcome),
        }
    }
}

/// **Mint a session key from a parent play cap** — the attenuating delegation. Builds the child
/// grant `{scope, deadline, turn_budget}` and admits it ONLY if it [`refines`] the parent (the
/// non-amplification tooth): a wider scope, a later deadline, or a bigger turn budget is refused
/// with the named [`Amplification`] leg. On success the returned [`SessionKey`] carries the
/// narrowed grant for `holder`, with a fresh (zero) turn counter.
pub fn open_session(
    parent: &PlayGrant,
    holder: DreggIdentity,
    scope: PlayScope,
    deadline: i64,
    turn_budget: i64,
) -> Result<SessionKey, Amplification> {
    let child = PlayGrant {
        scope,
        deadline,
        turn_budget,
    };
    refines(parent, &child)?;
    Ok(SessionKey {
        grant: child,
        holder,
        turns_taken: 0,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// CUSTODIAL / PASSKEY ONBOARDING — the deriving identity (the named seam).
// ─────────────────────────────────────────────────────────────────────────────

/// **A CUSTODIAN — the deriving identity for custodial onboarding.** A service (the bot) holds a
/// ROOT play cap and mints per-session attenuated keys on behalf of custodial players, who never
/// touch a wallet: they authenticate with a passkey (or a platform login), and the custodian
/// derives their stable identity, holds their session key, and plays their moves under it.
///
/// **What's real here:** the identity derivation ([`Custodian::identity_for`], a stable
/// `blake3` handle→identity — the SAME player always resolves to the SAME identity + credit
/// account) and the attenuated, non-amplifying delegation ([`Custodian::open_session_for`],
/// which cannot exceed the custodian's root cap).
///
/// **The named seam:** the passkey / WebAuthn UX that turns a browser credential assertion into
/// the opaque `handle` fed here, and the operational CUSTODY of the custodian's own root key /
/// the players' credit accounts (an operator secret-store / KMS concern). Those are the
/// onboarding UX + key-management remainder — not built in this core.
#[derive(Clone, Debug)]
pub struct Custodian {
    /// The root play cap the custodian delegates session keys from. Every minted key
    /// [`refines`] this — a custodian cannot hand out authority it does not hold.
    root: PlayGrant,
}

impl Custodian {
    /// A custodian holding `root` — the authority ceiling every session key it mints stays under.
    pub fn new(root: PlayGrant) -> Custodian {
        Custodian { root }
    }

    /// The custodian's root play cap.
    pub fn root(&self) -> &PlayGrant {
        &self.root
    }

    /// **Derive a custodial player's stable identity from an opaque handle** — a passkey
    /// credential id, a Discord user id, a platform login subject. `blake3(handle)` hex, so the
    /// SAME player always maps to the SAME [`DreggIdentity`] (and thus the same credit account at
    /// the [`Paymaster`]). This is the seam a passkey/WebAuthn assertion feeds: verify the
    /// assertion, then derive the identity from its credential id.
    pub fn identity_for(handle: &str) -> DreggIdentity {
        DreggIdentity(blake3::hash(handle.as_bytes()).to_hex().to_string())
    }

    /// **Mint a per-session key for a custodial player** — scoped to one offering, time-boxed by
    /// `deadline`, budgeted to `turn_budget` turns, and NON-AMPLIFYING over the custodian's root
    /// cap ([`open_session`] refuses a delegation that would exceed the root). The player's
    /// identity is derived from `handle` (the passkey/login seam). The custodian holds the
    /// returned key and plays the player's session under it.
    pub fn open_session_for(
        &self,
        handle: &str,
        scope: PlayScope,
        deadline: i64,
        turn_budget: i64,
    ) -> Result<SessionKey, Amplification> {
        let holder = Self::identity_for(handle);
        open_session(&self.root, holder, scope, deadline, turn_budget)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE PLAY OUTCOME.
// ─────────────────────────────────────────────────────────────────────────────

/// The outcome of a [`SessionKey::play`] — the four honest terminals of a gasless, no-re-sign
/// move.
#[derive(Debug, Clone)]
pub enum PlayOutcome {
    /// The session key admitted the turn, the paymaster covered it, and the real move LANDED: a
    /// genuine committed [`Outcome::Landed`], a real credit charge, and the key's counter
    /// advanced.
    Committed {
        /// The underlying committed move outcome (carries the real [`crate::TurnReceipt`]).
        outcome: Outcome,
        /// What the paymaster charged (the move's [`RunCost`]; `0` for the free tier).
        charged: RunCost,
        /// The holder's credit balance after the charge.
        credits_left: u64,
        /// The key's committed-turn counter after this turn.
        turns_taken: i64,
    },
    /// The SESSION KEY refused the turn in-band (out-of-scope / past-deadline / over-budget) —
    /// nothing advanced, nothing charged (anti-ghost).
    Refused(PlayRefusal),
    /// The PAYMASTER could not cover the move — nothing advanced, nothing charged (anti-ghost).
    Unpaid(PaymasterError),
    /// The session key admitted + the paymaster could have covered, but the EXECUTOR refused the
    /// game move itself (an illegal move). No charge, no budget consumed — the real substrate
    /// refusal carried through.
    ExecutorRefused(Outcome),
}

impl PlayOutcome {
    /// Did this play commit a real turn (charge + advance)?
    pub fn committed(&self) -> bool {
        matches!(self, PlayOutcome::Committed { .. })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE PAYMASTER — the run cost drawn from the credit ledger (gasless play).
// ─────────────────────────────────────────────────────────────────────────────

/// Why a [`Paymaster`] could not cover a move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PaymasterError {
    /// The holder's credit balance is below the move's cost.
    Insufficient {
        /// The holder that could not pay.
        who: DreggIdentity,
        /// The credits the move needed.
        needed: u64,
        /// The holder's balance at the time.
        balance: u64,
    },
}

impl std::fmt::Display for PaymasterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PaymasterError::Insufficient {
                who,
                needed,
                balance,
            } => write!(
                f,
                "paymaster cannot cover {needed} credits for {who:?} (balance {balance})"
            ),
        }
    }
}

impl std::error::Error for PaymasterError {}

/// **The paymaster seam** — where a move's [`RunCost`] is drawn, so play is gasless from the
/// player's view (no per-move signature, no per-move on-chain fee; a pre-funded credit balance
/// covers it). The production binding is [`CreditPaymaster`] over the existing
/// [`dregg_pay::CreditLedger`]; a test/free-tier binding can be trivial.
pub trait Paymaster {
    /// The holder's current credit balance.
    fn balance(&self, who: &DreggIdentity) -> u64;

    /// Can the holder cover `cost` right now? (A pre-check so an unpayable move never touches the
    /// substrate.) The free tier (`cost.credits == 0`) is always coverable.
    fn can_cover(&self, who: &DreggIdentity, cost: RunCost) -> bool {
        cost.credits == 0 || self.balance(who) >= cost.credits
    }

    /// **Charge `cost` to the holder** — the real ledger move. Returns the balance remaining, or
    /// [`PaymasterError::Insufficient`]. The free tier debits nothing and returns the balance.
    fn charge(&self, who: &DreggIdentity, cost: RunCost) -> Result<u64, PaymasterError>;
}

/// **The free-tier paymaster** — every move is free (`RunCost::free`); nothing is ever charged.
/// The default for a scripted/local narration offering, and a convenience for tests of the pure
/// session-key teeth (scope / deadline / budget) that do not exercise the credit ledger.
#[derive(Clone, Copy, Debug, Default)]
pub struct FreePaymaster;

impl Paymaster for FreePaymaster {
    fn balance(&self, _who: &DreggIdentity) -> u64 {
        u64::MAX
    }
    fn charge(&self, _who: &DreggIdentity, _cost: RunCost) -> Result<u64, PaymasterError> {
        Ok(u64::MAX)
    }
}

/// **The real credit paymaster** — a [`Paymaster`] over the existing run-credit ledger
/// ([`dregg_pay::CreditLedger`]). A paid move is a real `CreditLedger::debit`; the credits were
/// pre-funded (a player's earlier `$DREGG`/USDC payment the watcher credited, or, in the
/// custodial model, credits the operator funded on the player's behalf), so play is gasless from
/// the player's view — no per-move signature, no per-move on-chain fee.
///
/// A [`DreggIdentity`] maps to the ledger's [`dregg_pay::UserId`] by its opaque handle, so the
/// SAME player the frontend derives is the SAME credit account. Borrows the ledger (`&`); the
/// ledger's own interior mutability serializes the debits.
pub struct CreditPaymaster<'a, S: dregg_pay::CreditStore> {
    ledger: &'a dregg_pay::CreditLedger<S>,
}

impl<'a, S: dregg_pay::CreditStore> CreditPaymaster<'a, S> {
    /// Bind a paymaster to a run-credit `ledger`.
    pub fn new(ledger: &'a dregg_pay::CreditLedger<S>) -> Self {
        CreditPaymaster { ledger }
    }

    /// The ledger user-id for a play identity (the opaque handle IS the credit account key).
    fn user(who: &DreggIdentity) -> dregg_pay::UserId {
        dregg_pay::UserId(who.as_str().to_string())
    }
}

impl<'a, S: dregg_pay::CreditStore> Paymaster for CreditPaymaster<'a, S> {
    fn balance(&self, who: &DreggIdentity) -> u64 {
        self.ledger.balance(&Self::user(who))
    }

    fn charge(&self, who: &DreggIdentity, cost: RunCost) -> Result<u64, PaymasterError> {
        let user = Self::user(who);
        let balance = self.ledger.balance(&user);
        if balance < cost.credits {
            return Err(PaymasterError::Insufficient {
                who: who.clone(),
                needed: cost.credits,
                balance,
            });
        }
        // The ledger debits one credit at a time; draw the move's cost. Pre-checked above, so no
        // debit fails mid-move (the ledger serializes; this call path is single-threaded).
        let mut remaining = balance;
        for _ in 0..cost.credits {
            remaining = self
                .ledger
                .debit(&user)
                .map_err(|_| PaymasterError::Insufficient {
                    who: who.clone(),
                    needed: cost.credits,
                    balance,
                })?;
        }
        Ok(remaining)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dungeon::{DungeonOffering, TURN_CHOOSE};
    use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE};

    /// The scope id the dungeon offering plays under (its catalog key hashed).
    fn dungeon_scope() -> i64 {
        PlayScope::of_offering("dungeon").offering_id().unwrap()
    }

    fn choose(arg: usize) -> Action {
        Action::new("move", TURN_CHOOSE, arg as i64, true)
    }

    /// A far-future deadline (height) and a generous root cap for the "in-window" cases.
    const FAR: i64 = 1_000_000;

    /// A root player cap over the whole catalog: any offering, far deadline, many turns.
    fn root_cap() -> PlayGrant {
        PlayGrant::root(PlayScope::Any, FAR, 100)
    }

    /// SCOPED + TIME-BOXED, NON-VACUOUS: a session key scoped to the dungeon and valid until a
    /// deadline. In-scope, in-window turns COMMIT; an out-of-scope turn is REFUSED; a
    /// past-deadline turn is REFUSED — the caveats bite both ways.
    #[test]
    fn a_session_key_is_scoped_and_time_boxed_non_vacuously() {
        let off = DungeonOffering::new();
        let mut s = off.open(crate::SessionConfig::with_seed(3)).expect("open");
        let holder = DreggIdentity("player-alice".to_string());

        // Mint a session key scoped to the dungeon, valid until height 100.
        let mut key = open_session(
            &root_cap(),
            holder,
            PlayScope::of_offering("dungeon"),
            100,
            10,
        )
        .expect("a narrowing delegation is admitted");

        let free = FreePaymaster;
        let dungeon = dungeon_scope();

        // IN-SCOPE, IN-WINDOW (now=1 <= 100): the move commits under the session key.
        let out = key.play(dungeon, &off, &mut s, choose(KP_PRESS_ON), 1, &free);
        assert!(out.committed(), "in-scope in-window turn commits: {out:?}");
        assert_eq!(key.turns_taken(), 1, "one committed turn metered");

        // OUT OF SCOPE: play some OTHER offering id → refused, nothing commits, no budget spent.
        let other = PlayScope::of_offering("council").offering_id().unwrap();
        let out = key.play(other, &off, &mut s, choose(KP_CLAIM_RED), 2, &free);
        assert!(
            matches!(out, PlayOutcome::Refused(PlayRefusal::OutOfScope { .. })),
            "an out-of-scope offering is refused: {out:?}"
        );
        assert_eq!(key.turns_taken(), 1, "a refused turn consumes no budget");

        // PAST DEADLINE: an otherwise-legal in-scope move at now=101 (> 100) → refused.
        let out = key.play(dungeon, &off, &mut s, choose(KP_CLAIM_RED), 101, &free);
        assert!(
            matches!(out, PlayOutcome::Refused(PlayRefusal::PastDeadline { .. })),
            "a past-deadline turn is refused: {out:?}"
        );
        assert_eq!(key.turns_taken(), 1, "a refused turn consumes no budget");

        // Back IN WINDOW again: the same move now commits (non-vacuous: the deadline was the only
        // thing stopping it).
        let out = key.play(dungeon, &off, &mut s, choose(KP_CLAIM_RED), 50, &free);
        assert!(out.committed(), "in-window again commits: {out:?}");
        assert_eq!(key.turns_taken(), 2);
    }

    /// NO PER-MOVE RE-SIGN: a whole winning dungeon line commits under ONE session key — four
    /// moves, one open, and the key's own counter meters them.
    #[test]
    fn a_whole_session_commits_under_one_session_key() {
        let off = DungeonOffering::new();
        let mut s = off.open(crate::SessionConfig::with_seed(3)).expect("open");
        let holder = DreggIdentity("player-bob".to_string());

        let mut key = open_session(
            &root_cap(),
            holder,
            PlayScope::of_offering("dungeon"),
            FAR,
            10,
        )
        .expect("delegation");
        let free = FreePaymaster;
        let dungeon = dungeon_scope();

        // The full winning line — press on, claim the crown, descend, seize the hoard — all under
        // the SAME key, no re-open, no per-move re-sign.
        for (i, arg) in [KP_PRESS_ON, KP_CLAIM_RED, KP_DESCEND, KP_SEIZE]
            .into_iter()
            .enumerate()
        {
            let out = key.play(dungeon, &off, &mut s, choose(arg), 1, &free);
            assert!(
                out.committed(),
                "move {i} ({arg}) commits under one key: {out:?}"
            );
        }
        assert_eq!(key.turns_taken(), 4, "four turns metered on one key");
        // The dungeon's own chain re-verifies — the moves are real committed turns.
        assert!(off.verify(&s).verified, "the session's chain re-verifies");
    }

    /// THE NON-AMPLIFICATION TOOTH: from a NARROW parent cap (one offering, deadline 100, budget
    /// 5), a delegation that WIDENS any caveat is refused with the named leg; a narrowing one is
    /// admitted.
    #[test]
    fn a_session_key_cannot_amplify_the_parent_grant() {
        let holder = DreggIdentity("player-carol".to_string());
        let parent = PlayGrant::root(PlayScope::of_offering("dungeon"), 100, 5);

        // Widen SCOPE: parent is one offering, ask for Any → refused.
        let amp = open_session(&parent, holder.clone(), PlayScope::Any, 100, 5);
        assert!(
            matches!(amp, Err(Amplification::ScopeWidened { .. })),
            "widening scope to Any is refused: {amp:?}"
        );

        // Widen SCOPE to a DIFFERENT offering → refused.
        let amp = open_session(
            &parent,
            holder.clone(),
            PlayScope::of_offering("council"),
            100,
            5,
        );
        assert!(
            matches!(amp, Err(Amplification::ScopeWidened { .. })),
            "widening scope to another offering is refused: {amp:?}"
        );

        // Extend DEADLINE past the parent → refused.
        let amp = open_session(
            &parent,
            holder.clone(),
            PlayScope::of_offering("dungeon"),
            101,
            5,
        );
        assert!(
            matches!(amp, Err(Amplification::DeadlineExtended { .. })),
            "extending the deadline is refused: {amp:?}"
        );

        // Raise TURN BUDGET past the parent → refused.
        let amp = open_session(
            &parent,
            holder.clone(),
            PlayScope::of_offering("dungeon"),
            100,
            6,
        );
        assert!(
            matches!(amp, Err(Amplification::BudgetRaised { .. })),
            "raising the turn budget is refused: {amp:?}"
        );

        // A genuinely NARROWING delegation (same scope, earlier deadline, smaller budget) is
        // admitted — non-vacuous: the tooth refuses amplification, not every delegation.
        let ok = open_session(&parent, holder, PlayScope::of_offering("dungeon"), 50, 3);
        assert!(ok.is_ok(), "a narrowing delegation is admitted: {ok:?}");
        let key = ok.unwrap();
        assert_eq!(key.grant().deadline, 50);
        assert_eq!(key.grant().turn_budget, 3);
    }

    /// CUSTODIAL ONBOARDING: a custodian derives a STABLE identity from an opaque handle (the
    /// passkey/login seam), mints a scoped + time-boxed session key on the player's behalf, and
    /// the custodial player plays a whole session under it (no wallet, no per-move re-sign). The
    /// custodian CANNOT mint a key exceeding its root cap (non-amplification through the custody
    /// path).
    #[test]
    fn a_custodian_onboards_a_custodial_player_within_its_root_cap() {
        // The service's root cap: the whole catalog, far deadline, many turns.
        let custodian = Custodian::new(PlayGrant::root(PlayScope::Any, FAR, 100));

        // A passkey/login handle derives a STABLE identity (same handle → same identity).
        let handle = "passkey:credential-id-abc123";
        let id1 = Custodian::identity_for(handle);
        let id2 = Custodian::identity_for(handle);
        assert_eq!(id1, id2, "the derived custodial identity is stable");
        assert_ne!(
            id1,
            Custodian::identity_for("passkey:someone-else"),
            "a different handle derives a different identity"
        );

        // Mint a per-session key scoped to the dungeon, time-boxed, within the root.
        let mut key = custodian
            .open_session_for(handle, PlayScope::of_offering("dungeon"), 1_000, 5)
            .expect("a session within the root cap is minted");
        assert_eq!(key.holder(), &id1, "the key plays for the derived identity");

        // The custodial player plays a winning line under it — no wallet, no per-move re-sign.
        let off = DungeonOffering::new();
        let mut s = off.open(crate::SessionConfig::with_seed(3)).expect("open");
        let free = FreePaymaster;
        let dungeon = dungeon_scope();
        for arg in [KP_PRESS_ON, KP_CLAIM_RED, KP_DESCEND, KP_SEIZE] {
            assert!(
                key.play(dungeon, &off, &mut s, choose(arg), 1, &free)
                    .committed(),
                "the custodial player's move commits under the minted key"
            );
        }
        assert!(off.verify(&s).verified, "the custodial session re-verifies");

        // The custodian CANNOT mint a key that exceeds a NARROWER root (non-amplification).
        let narrow = Custodian::new(PlayGrant::root(PlayScope::of_offering("dungeon"), 100, 3));
        assert!(
            matches!(
                narrow.open_session_for(handle, PlayScope::Any, 100, 3),
                Err(Amplification::ScopeWidened { .. })
            ),
            "a custodian cannot delegate wider scope than its root"
        );
        assert!(
            matches!(
                narrow.open_session_for(handle, PlayScope::of_offering("dungeon"), 100, 4),
                Err(Amplification::BudgetRaised { .. })
            ),
            "a custodian cannot delegate more turns than its root"
        );
    }

    /// A move the EXECUTOR refuses (an illegal game move) costs nothing and consumes no budget —
    /// the anti-ghost tooth reaches through the session key to the substrate referee.
    #[test]
    fn an_executor_refused_move_costs_nothing() {
        let off = DungeonOffering::new();
        let mut s = off.open(crate::SessionConfig::with_seed(3)).expect("open");
        let holder = DreggIdentity("player-dave".to_string());
        let mut key = open_session(
            &root_cap(),
            holder,
            PlayScope::of_offering("dungeon"),
            FAR,
            10,
        )
        .expect("delegation");
        let free = FreePaymaster;
        let dungeon = dungeon_scope();

        // An out-of-range choice index is a real executor refusal (not on the ballot).
        let out = key.play(dungeon, &off, &mut s, choose(99), 1, &free);
        assert!(
            matches!(out, PlayOutcome::ExecutorRefused(_)),
            "an illegal game move is an executor refusal: {out:?}"
        );
        assert_eq!(
            key.turns_taken(),
            0,
            "an executor-refused move consumes no budget"
        );
    }
}
