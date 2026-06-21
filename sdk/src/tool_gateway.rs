//! # ORGAN 4 — THE GATEWAY: a live tool-calling agent becomes a mandated inhabitant.
//!
//! A clean Rust seam that turns an inbound, untrusted tool-call into a
//! cap-gated, metered, receipted DELEGATED turn on the verified executor — or an
//! IN-BAND refusal. Any external loop (a buildr agent, a hermes agent, an MCP
//! host) drives it through one method: [`ToolGateway::invoke`]. The gateway holds
//! no policy of its own; the GRANTOR pins the mandate ([`ToolGrant`]) at
//! delegation time, and every call is admitted IFF the delegated policy admits
//! it.
//!
//! ## What this welds (REUSE, not rebuild)
//!
//! * The PROVEN admission crown — `metatheory/Dregg2/Apps/ToolAccessDelegation.lean`:
//!   `delegAdmit g now tool old new = SCOPE ∧ DEADLINE ∧ rate(new = old+1 ∧ 0 ≤ old ∧ new ≤ rateLimit)`,
//!   and `tool_invocation_commit_iff_admit` (the executor's caveat gate commits a
//!   metered `calls_made : c → c+1` write IFF that predicate holds), with the
//!   over-rate / past-deadline / out-of-scope rejection TEETH. [`deleg_admit`] in
//!   this module is the byte-faithful Rust mirror of that Lean predicate; the
//!   `tool_gateway_admit_mirrors_lean_delegadmit` test pins the SAME decision
//!   vector the Lean `#guard`s witness.
//! * The cap-gated executor path — [`crate::SubAgent`] / [`crate::AgentRuntime::spawn_sub_agent_scoped`]:
//!   the worker carries a public-key biscuit credential scoped to EXACTLY the
//!   granted tool method, presented as `Authorization::Token`, so the EXECUTOR
//!   (`verify_token_authorization`) — not an out-of-band `cap.verify()` — admits
//!   the metered write. A call under any other method is rejected by the executor
//!   with `TokenInsufficientCapability`.
//!
//! ## The two enforcement surfaces, both load-bearing
//!
//! A tool invocation is a single scalar write: the worker cell's `calls_made`
//! slot advances `c → c+1`. Admission folds the WHOLE delegated policy:
//!
//! 1. **In-band, before submission** — [`deleg_admit`] decides SCOPE ∧ DEADLINE ∧
//!    RATE exactly as the Lean predicate. A FALSE verdict is a
//!    [`GatewayRefusal`] returned as an `Err` (the anti-ghost tooth — a `Result`
//!    error, NEVER a panic, and NO turn is submitted, so no spend, no counter
//!    advance).
//! 2. **In the executor** — the worker cell carries a [`mandate_program`]
//!    (`FieldLte { calls_made ≤ rateLimit }` ∧ `Monotonic { calls_made }`): even
//!    if a caller bypassed [`deleg_admit`], the executor's own cell-program check
//!    rejects an over-rate or rolled-back counter write. The rate ceiling is
//!    bound into the committed transition, not merely pre-checked.
//!
//! A granted call therefore COMMITS with a receipt and a conserved spend (the
//! counter moves, total balance does not), and an out-of-mandate call is REFUSED
//! in-band — the exact both-polarity shape the Lean crown proves.

use dregg_cell::program::{field_from_u64, CellProgram, StateConstraint};
use dregg_cell::CellId;
use dregg_token::Attenuation;
use dregg_turn::{Effect, TurnReceipt};

use crate::cipherclerk::HeldToken;
use crate::error::SdkError;
use crate::runtime::{AgentRuntime, SubAgent};

/// The slot index on the worker cell that holds the rate counter `calls_made`.
///
/// Mirrors the Lean `callsMadeSlot` (`"calls_made"`); here it is a fixed cell
/// field slot so the executor's `FieldLte` / `Monotonic` constraints bite on it.
/// Slot 4 is the conventional first general-purpose slot (slots 0..3 are commonly
/// reserved by other programs); the gateway owns the worker cell, so this choice
/// is private to the mandate.
pub const CALLS_MADE_SLOT: u8 = 4;

/// The grantor's pinned delegation parameters — the immutable bundle fixed at
/// delegation time. The byte-faithful Rust mirror of the Lean `Grant`
/// (`Dregg2.Apps.ToolAccessDelegation.Grant`).
///
/// * `tool_id` — the single allowlisted tool / MCP id the worker is scoped to
///   (the SCOPE). An invocation presenting any other tool id is refused.
/// * `rate_limit` — the granted invocation ceiling `N`: at most `N` calls under
///   this mandate (the RATE).
/// * `deadline` — the expiry height/clock: an invocation presented at
///   `now > deadline` is refused (the DEADLINE).
/// * `tool_method` — the executor-level method verb the worker's biscuit
///   credential is scoped to. This is the SCOPE's executor face: the cap_token
///   covers exactly this method, so the executor rejects a turn under any other
///   verb with `TokenInsufficientCapability`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToolGrant {
    /// The single allowlisted tool / MCP id (the SCOPE, in-band face).
    pub tool_id: i64,
    /// The granted invocation ceiling `N` (the RATE).
    pub rate_limit: i64,
    /// The expiry height/clock (the DEADLINE).
    pub deadline: i64,
    /// The executor method verb the worker's credential is scoped to (the
    /// SCOPE's executor face).
    pub tool_method: String,
}

/// **`deleg_admit`** — the folded delegated-policy predicate, the byte-faithful
/// Rust mirror of the Lean `delegAdmit g now tool old new`
/// (`Dregg2.Apps.ToolAccessDelegation.delegAdmit`).
///
/// Returns `true` IFF the delegated policy admits the invocation that advances
/// the rate counter `old → new`, presented at height `now` for tool `tool` under
/// grant `g`. Fail-closed on every conjunct, in the SAME order as the Lean:
///
/// 1. SCOPE — `tool == g.tool_id`;
/// 2. DEADLINE — `now <= g.deadline`;
/// 3. single-step increment — `new == old + 1`;
/// 4. sane prior count — `0 <= old`;
/// 5. RATE — `new <= g.rate_limit`.
pub fn deleg_admit(g: &ToolGrant, now: i64, tool: i64, old: i64, new: i64) -> bool {
    tool == g.tool_id
        && now <= g.deadline
        && new == old + 1
        && 0 <= old
        && new <= g.rate_limit
}

/// The mandate cell program installed on the worker cell — the executor-side
/// half of the rate enforcement.
///
/// `FieldLte { calls_made <= rate_limit }` binds the RATE ceiling into the
/// committed transition (the executor rejects any write whose post-state counter
/// exceeds `rate_limit`), and `Monotonic { calls_made }` forbids rolling the
/// counter back to forge head-room. Together they are the executor's own
/// realization of the rate conjunct of [`deleg_admit`] — so even a caller that
/// bypassed the in-band check cannot drive the counter past the granted ceiling.
///
/// (SCOPE and DEADLINE are enforced in-band by [`deleg_admit`] and at the
/// executor by the worker's method-scoped biscuit credential / the runtime's
/// block height; the cell program carries the rate + no-rollback invariants that
/// are purely intrinsic to the counter slot.)
pub fn mandate_program(rate_limit: i64) -> CellProgram {
    let ceiling = if rate_limit < 0 { 0 } else { rate_limit as u64 };
    CellProgram::Predicate(vec![
        // RATE: the post-state counter never exceeds the granted ceiling.
        StateConstraint::FieldLte {
            index: CALLS_MADE_SLOT,
            value: field_from_u64(ceiling),
        },
        // NO ROLLBACK: the counter can never decrease (no forged head-room).
        StateConstraint::Monotonic {
            index: CALLS_MADE_SLOT,
        },
    ])
}

/// Why the gateway refused a tool call IN-BAND (returned as the `Err` of
/// [`ToolGateway::invoke`] — the anti-ghost tooth: a refusal is a value, never a
/// panic, and NO turn is submitted).
///
/// Each variant is the negation of one [`deleg_admit`] conjunct, named so the
/// caller (and an audit trail) can see exactly which leg of the mandate bit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GatewayRefusal {
    /// SCOPE: the presented tool id is not the granted one.
    OutOfScope {
        /// The tool id the call presented.
        presented: i64,
        /// The single tool id the grant allows.
        granted: i64,
    },
    /// DEADLINE: the call was presented after the granted expiry.
    PastDeadline {
        /// The height the call was presented at.
        now: i64,
        /// The granted expiry height.
        deadline: i64,
    },
    /// RATE: the rate budget is exhausted (the counter is already at the
    /// granted ceiling, so the next call would exceed it).
    OverRate {
        /// The counter value before this (refused) call.
        calls_made: i64,
        /// The granted ceiling `N`.
        rate_limit: i64,
    },
}

impl std::fmt::Display for GatewayRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GatewayRefusal::OutOfScope { presented, granted } => write!(
                f,
                "tool call out of scope: presented tool {presented}, mandate grants only {granted}"
            ),
            GatewayRefusal::PastDeadline { now, deadline } => write!(
                f,
                "tool call past deadline: presented at height {now}, mandate expired at {deadline}"
            ),
            GatewayRefusal::OverRate {
                calls_made,
                rate_limit,
            } => write!(
                f,
                "tool call over rate: {calls_made} calls already made, mandate grants {rate_limit}"
            ),
        }
    }
}

impl std::error::Error for GatewayRefusal {}

/// The outcome of an admitted, committed tool invocation: the executor receipt
/// proving the metered turn committed, plus the new counter value.
#[derive(Clone, Debug)]
pub struct ToolReceipt {
    /// The executor receipt for the metered turn (proof the call committed).
    pub receipt: TurnReceipt,
    /// The rate counter AFTER this call (`calls_made` post-invocation).
    pub calls_made: i64,
    /// How many calls remain on the mandate (`rate_limit - calls_made`).
    pub remaining: i64,
}

/// The error surface of [`ToolGateway::invoke`]: either an in-band mandate
/// refusal, or an underlying SDK/executor error (spawn / submission failure).
#[derive(Debug)]
pub enum ToolCallError {
    /// The delegated policy refused the call IN-BAND (the anti-ghost tooth).
    Refused(GatewayRefusal),
    /// An underlying SDK/executor error (e.g. the executor rejected the metered
    /// write — the cell-program rate/monotonic backstop, or a credential failure).
    Sdk(SdkError),
}

impl std::fmt::Display for ToolCallError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ToolCallError::Refused(r) => write!(f, "mandate refused tool call: {r}"),
            ToolCallError::Sdk(e) => write!(f, "tool call execution error: {e}"),
        }
    }
}

impl std::error::Error for ToolCallError {}

impl From<SdkError> for ToolCallError {
    fn from(e: SdkError) -> Self {
        ToolCallError::Sdk(e)
    }
}

/// THE GATEWAY — a mandated inhabitant wrapping a cap-gated worker.
///
/// Construct one with [`ToolGateway::admit`] (the grantor delegates a
/// [`ToolGrant`] to a freshly spawned worker). Then any external loop drives
/// inbound tool-calls through [`ToolGateway::invoke`]: a granted call commits
/// with a [`ToolReceipt`]; an out-of-mandate call is refused in-band as a
/// [`GatewayRefusal`].
///
/// The gateway owns the worker [`SubAgent`] (its biscuit credential is scoped to
/// `grant.tool_method`) and tracks the rate counter; the worker cell carries the
/// [`mandate_program`] backstop.
pub struct ToolGateway {
    /// The grantor's pinned mandate.
    grant: ToolGrant,
    /// The cap-gated worker the gateway drives.
    worker: SubAgent,
    /// The worker cell id (the mandate cell carrying `calls_made`).
    worker_cell: CellId,
    /// The rate counter, kept in lock-step with the worker cell's
    /// `calls_made` slot (advanced only on a committed invocation).
    calls_made: i64,
}

impl ToolGateway {
    /// Admit a worker into the world under a delegated tool mandate.
    ///
    /// The grantor (`runtime`, holding `parent_token`) delegates `grant` to a
    /// freshly spawned [`SubAgent`] scoped to `grant.tool_method`, installs the
    /// [`mandate_program`] (rate ceiling + monotonic counter) on the worker
    /// cell, and returns a gateway ready to admit inbound tool-calls.
    ///
    /// The worker's biscuit credential is the executor-enforced SCOPE: a turn
    /// under any verb other than `grant.tool_method` is rejected by the executor
    /// itself. The cell program is the executor-enforced RATE backstop.
    pub fn admit(
        runtime: &AgentRuntime,
        parent_token: &HeldToken,
        grant: ToolGrant,
    ) -> Result<Self, SdkError> {
        // Spawn a worker scoped to EXACTLY the granted tool method. Its biscuit
        // credential covers only `grant.tool_method`, so the executor rejects a
        // call under any other verb with `TokenInsufficientCapability`.
        let worker = runtime.spawn_sub_agent_scoped(
            &Attenuation::default(),
            parent_token,
            &[grant.tool_method.as_str()],
        )?;
        let worker_cell = worker.cell_id();

        // Install the mandate program (rate ceiling + monotonic counter) on the
        // worker cell — the executor's own realization of the rate conjunct, the
        // backstop under the in-band `deleg_admit`. The worker cell lives in the
        // runtime's shared ledger, so we reach it via the runtime handle.
        {
            let mut ledger = runtime.ledger().lock().unwrap();
            ledger
                .update_with(&worker_cell, |cell| {
                    cell.program = mandate_program(grant.rate_limit);
                })
                .map_err(|e| SdkError::Rejected(format!("install mandate program: {e}")))?;
        }

        Ok(ToolGateway {
            grant,
            worker,
            worker_cell,
            calls_made: 0,
        })
    }

    /// The grantor's pinned mandate.
    pub fn grant(&self) -> &ToolGrant {
        &self.grant
    }

    /// The worker cell id (the mandate cell).
    pub fn worker_cell(&self) -> CellId {
        self.worker_cell
    }

    /// The calls made so far under this mandate.
    pub fn calls_made(&self) -> i64 {
        self.calls_made
    }

    /// Test-only direct access to the cap-gated worker, used to exercise the
    /// EXECUTOR-side cell-program backstop independently of the in-band
    /// [`deleg_admit`] check (a bypass an in-band-skipping caller would attempt).
    #[doc(hidden)]
    pub fn worker_for_test(&self) -> &SubAgent {
        &self.worker
    }

    /// The calls remaining on the mandate (`rate_limit - calls_made`).
    pub fn remaining(&self) -> i64 {
        self.grant.rate_limit - self.calls_made
    }

    /// THE SEAM — admit an inbound tool-call.
    ///
    /// `tool` is the tool/MCP id the call presents; `now` is the presentation
    /// height/clock; `work` is the effects the call performs on the worker cell
    /// (the tool's actual work, beyond the metered counter advance — pass an
    /// empty `Vec` for a pure metered invocation).
    ///
    /// Admission folds the WHOLE delegated policy via [`deleg_admit`] (SCOPE ∧
    /// DEADLINE ∧ RATE):
    ///
    /// * **granted** (`deleg_admit == true`) — the metered `calls_made : c → c+1`
    ///   write (plus `work`) is submitted through the cap-gated worker; on commit
    ///   it returns a [`ToolReceipt`] (proof + conserved spend). The cell-program
    ///   rate/monotonic backstop and the worker's method-scoped credential are
    ///   the executor's independent enforcement of the same policy.
    /// * **refused** (`deleg_admit == false`) — NO turn is submitted; the call
    ///   returns `Err(ToolCallError::Refused(..))` naming the leg that bit (the
    ///   anti-ghost tooth: a `Result` error, never a panic, no spend, no counter
    ///   advance).
    pub fn invoke(
        &mut self,
        tool: i64,
        now: i64,
        mut work: Vec<Effect>,
    ) -> Result<ToolReceipt, ToolCallError> {
        let old = self.calls_made;
        let new = old + 1;

        // §1 — IN-BAND admission (the byte-faithful Lean `delegAdmit` mirror).
        // Fail-closed, naming the leg that bit. NO turn is submitted on refusal.
        if !deleg_admit(&self.grant, now, tool, old, new) {
            return Err(ToolCallError::Refused(self.diagnose_refusal(tool, now, old)));
        }

        // §2 — the metered write: advance the rate counter `c → c+1`. The
        // worker presents its method-scoped biscuit credential; the executor's
        // token path admits it, and the cell-program rate/monotonic backstop
        // re-checks the counter. `work` rides the same turn (the tool's payload).
        let mut effects = Vec::with_capacity(work.len() + 1);
        effects.push(Effect::SetField {
            cell: self.worker_cell,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64(new as u64),
        });
        effects.append(&mut work);

        let receipt = self
            .worker
            .execute_method(&self.grant.tool_method, effects)?;

        // The call committed: advance the tracked counter in lock-step.
        self.calls_made = new;
        Ok(ToolReceipt {
            receipt,
            calls_made: new,
            remaining: self.remaining(),
        })
    }

    /// Decide which mandate leg refused a call (for the [`GatewayRefusal`]). Only
    /// reached when [`deleg_admit`] returned `false`; reports the conjuncts in
    /// the same precedence the predicate checks them (scope, then deadline, then
    /// rate), so the most fundamental violation is surfaced first.
    fn diagnose_refusal(&self, tool: i64, now: i64, old: i64) -> GatewayRefusal {
        if tool != self.grant.tool_id {
            GatewayRefusal::OutOfScope {
                presented: tool,
                granted: self.grant.tool_id,
            }
        } else if now > self.grant.deadline {
            GatewayRefusal::PastDeadline {
                now,
                deadline: self.grant.deadline,
            }
        } else {
            // The only remaining way `deleg_admit` is false (given new = old+1,
            // 0 <= old by construction) is `new > rate_limit` — the rate is
            // exhausted.
            GatewayRefusal::OverRate {
                calls_made: old,
                rate_limit: self.grant.rate_limit,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The demo grant from the Lean §8 witness: tool 77, rate 3, deadline 100.
    fn demo_grant() -> ToolGrant {
        ToolGrant {
            tool_id: 77,
            rate_limit: 3,
            deadline: 100,
            tool_method: "search".to_string(),
        }
    }

    #[test]
    fn tool_gateway_admit_mirrors_lean_delegadmit() {
        // BOTH-POLARITY at the predicate level: this is the EXACT decision vector
        // the Lean `#guard`s witness in `ToolAccessDelegation.lean §8`. A drift on
        // either side is a divergence between the Rust seam and the proven crown.
        let g = demo_grant();

        // The three legal advances (in-scope tool 77, in-time now 50, 1..3 <= 3):
        assert!(deleg_admit(&g, 50, 77, 0, 1), "invocation 1 admitted");
        assert!(deleg_admit(&g, 50, 77, 1, 2), "invocation 2 admitted");
        assert!(deleg_admit(&g, 50, 77, 2, 3), "invocation 3 admitted (the last)");

        // The TEETH (each negated conjunct), matching the Lean `== false` guards:
        assert!(!deleg_admit(&g, 50, 77, 3, 4), "invocation 4 over-rate (4 > 3)");
        assert!(!deleg_admit(&g, 50, 99, 0, 1), "out-of-scope tool 99");
        assert!(!deleg_admit(&g, 101, 77, 0, 1), "past-deadline now 101 > 100");

        // Non-single-step and negative-old also fail closed (the increment +
        // sane-prior conjuncts):
        assert!(!deleg_admit(&g, 50, 77, 0, 2), "not a single-step increment");
        assert!(!deleg_admit(&g, 50, 77, -1, 0), "negative prior count");
    }

    #[test]
    fn mandate_program_carries_rate_and_monotonic() {
        // The installed program is exactly the rate ceiling + monotonic counter
        // (the executor-side backstop) — non-vacuous: two real constraints on the
        // calls_made slot.
        match mandate_program(3) {
            CellProgram::Predicate(cs) => {
                assert_eq!(cs.len(), 2);
                assert!(matches!(
                    cs[0],
                    StateConstraint::FieldLte { index, .. } if index == CALLS_MADE_SLOT
                ));
                assert!(matches!(
                    cs[1],
                    StateConstraint::Monotonic { index } if index == CALLS_MADE_SLOT
                ));
            }
            other => panic!("expected a Predicate program, got {other:?}"),
        }
    }
}
