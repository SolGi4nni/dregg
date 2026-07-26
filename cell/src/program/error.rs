use super::*;

/// Error from evaluating a cell program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramError {
    /// A state constraint was violated.
    ConstraintViolated {
        constraint: StateConstraint,
        description: String,
    },
    /// A field index in a constraint is out of bounds.
    InvalidFieldIndex { index: u8 },
    /// A circuit proof is required but was not provided.
    CircuitProofRequired { circuit_hash: [u8; 32] },
    /// Custom constraint cannot be evaluated locally (no registered IR).
    CustomConstraintUnevaluable { ir_hash: [u8; 32] },
    /// Immutable / transition constraint cannot be verified without prior state.
    /// Fail-closed: if there is no old_state to compare against, the constraint
    /// cannot be satisfied (unless this is a fresh cell with nonce == 0).
    TransitionCheckRequiresOldState {
        constraint: StateConstraint,
        index: u8,
    },
    /// Replay-sensitive constraint missing context.
    MissingContextField { field: &'static str },
    /// Cross-cell binding (`BoundDelta`) requires γ.2 wiring that is not yet
    /// available at this evaluation site.
    BoundDeltaNotWired { peer_cell: crate::id::CellId },
    /// `TemporalPredicate` requires an attached witness proof.
    TemporalPredicateWitnessMissing { dsl_hash: [u8; 32] },
    /// A `Witnessed { wp }` constraint cannot be evaluated locally
    /// because the executor's per-action witness-binding pass has not
    /// run yet (the executor's witnessed-predicate registry verifies
    /// the proof; the static evaluator only declares the requirement).
    WitnessedPredicateRequiresExecutor { kind_name: &'static str },
    /// `CellProgram::Cases(_)` was evaluated against a transition where
    /// no case matched. Default-deny per Cav-Codex Block 4.
    NoTransitionCaseMatched,
    /// The witnessed-predicate registry returned a verifier rejection
    /// (proof was malformed or the verifier rejected the input).
    WitnessedPredicateRejected {
        kind_name: &'static str,
        reason: String,
    },
    /// `SenderAuthorized` requires a Merkle-membership witness blob but
    /// the action did not carry one at the expected index.
    SenderMembershipWitnessMissing,
    /// The action did not carry the `PreimageGate`'s expected preimage
    /// blob, or it was at the wrong witness index / wrong type.
    PreimageWitnessMissing,
    /// A `Custom { ir_hash }` predicate requires a registered custom
    /// program verifier; either the action did not carry a proof at
    /// the expected witness index or no verifier matched the
    /// declared vk hash.
    CustomProgramProofRejected { ir_hash: [u8; 32], reason: String },
    /// `CapabilityUniqueness` cannot be enforced by the scalar
    /// `(old_state, new_state)` evaluator: structural "exactly one /
    /// no-duplicate" enforcement needs the cell's actual
    /// [`crate::capability::CapabilitySet`], which is only reachable from
    /// the executor. The scalar evaluator fails **closed** with this
    /// sentinel so the constraint can never silently pass; the executor
    /// (`execute_tree::validate_capability_uniqueness`) performs the real
    /// check against the cap set and binds the declared cap-set-root slot
    /// to the canonical capability root.
    CapabilityUniquenessRequiresExecutor { cap_set_root_slot: u8 },
    /// A `SimpleStateConstraint::Not` reached the `StateConstraint` lift
    /// (`lift_simple`), which has no `Not` variant to lift it into.
    /// Unreachable from `evaluate_simple_constraint`, which peels every
    /// negation and lifts only the atom beneath it — this variant is the
    /// fail-closed floor under that argument rather than a `panic!`,
    /// because the constraint being lifted is decoded from untrusted
    /// wire bytes and no reachability argument should be load-bearing
    /// for whether a node stays up.
    NegationNotLiftable,
    /// A Lean-subset `StateConstraint` was evaluated on a NATIVE node with NO
    /// constraint oracle installed. The Lean-evaluated subset's admission MUST
    /// be decided by the verified `dregg_constraint_admits`
    /// (`Dregg2.Exec.DeployedConstraint.admits`), installed via
    /// [`super::oracle::install_constraint_oracle`]. When the oracle is absent
    /// on a native build, the deployed evaluator FAILS CLOSED with this sentinel
    /// rather than silently deciding the subset in the hand-written Rust `match`
    /// (the fail-OPEN the game-proof audit found). A production node MUST install
    /// the oracle; the class-c witness/crypto/executor-state variants remain the
    /// named trusted-Rust slot and are unaffected. (wasm32 / the SP1 zkVM guest
    /// cannot link the archive and keep the Rust subset arms, labeled unverified.)
    ConstraintOracleUnavailable { constraint: StateConstraint },
}

impl core::fmt::Display for ProgramError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProgramError::ConstraintViolated { description, .. } => {
                write!(f, "program constraint violated: {description}")
            }
            ProgramError::InvalidFieldIndex { index } => {
                write!(f, "program references invalid field index: {index}")
            }
            ProgramError::CircuitProofRequired { .. } => {
                write!(
                    f,
                    "circuit program requires a proof in the action authorization"
                )
            }
            ProgramError::CustomConstraintUnevaluable { .. } => {
                write!(f, "custom constraint cannot be evaluated locally")
            }
            ProgramError::TransitionCheckRequiresOldState { index, .. } => {
                write!(
                    f,
                    "transition constraint on field[{index}] cannot be verified without prior state"
                )
            }
            ProgramError::MissingContextField { field } => {
                write!(f, "missing EvalContext field for slot caveat: {field}")
            }
            ProgramError::BoundDeltaNotWired { .. } => {
                write!(f, "BoundDelta peer-cell wiring is not yet available")
            }
            ProgramError::TemporalPredicateWitnessMissing { .. } => {
                write!(f, "TemporalPredicate requires an attached witness proof")
            }
            ProgramError::WitnessedPredicateRequiresExecutor { kind_name } => {
                write!(
                    f,
                    "witnessed predicate ({kind_name}) requires executor-side registry dispatch"
                )
            }
            ProgramError::NoTransitionCaseMatched => {
                write!(
                    f,
                    "Cases program: no transition case matched the action — default-deny"
                )
            }
            ProgramError::WitnessedPredicateRejected { kind_name, reason } => {
                write!(
                    f,
                    "witnessed predicate ({kind_name}) rejected by registered verifier: {reason}"
                )
            }
            ProgramError::SenderMembershipWitnessMissing => {
                write!(
                    f,
                    "SenderAuthorized requires a Merkle-membership witness blob; action did not carry one"
                )
            }
            ProgramError::PreimageWitnessMissing => {
                write!(
                    f,
                    "PreimageGate requires a 32-byte Preimage32 witness blob; action did not carry one"
                )
            }
            ProgramError::CustomProgramProofRejected { reason, .. } => {
                write!(f, "custom program proof rejected: {reason}")
            }
            ProgramError::CapabilityUniquenessRequiresExecutor { cap_set_root_slot } => {
                write!(
                    f,
                    "CapabilityUniqueness on slot {cap_set_root_slot} requires executor-side cap-set enforcement; the scalar state evaluator cannot verify structural uniqueness and fails closed"
                )
            }
            ProgramError::NegationNotLiftable => {
                write!(
                    f,
                    "SimpleStateConstraint::Not has no StateConstraint lift; evaluate it through evaluate_simple_constraint, which peels the negation chain"
                )
            }
            // ⚑ PLAYER-FACING. This string is not an operator diagnostic: it travels up as
            // `TurnError::ProgramViolation { reason }` and lands verbatim on a human's screen —
            // measured 2026-07-26, when someone typed `/adventure dungeon start` on the live
            // Discord bot and was shown the name of an internal Rust function to call. Whoever
            // reads this cannot install anything; the sentence has to tell them what happened,
            // whose fault it is, and that the actionable detail exists somewhere they can point
            // an operator at. The operator's half is
            // [`ProgramError::operator_diagnostic`], logged at the executor's refusal site.
            ProgramError::ConstraintOracleUnavailable { .. } => {
                write!(
                    f,
                    "this world cannot judge a move on this server: the verified rule-checker it needs is not installed, so it refuses every move rather than guess at one. That is a fault in how this server was built, not in what you did — the server log names the missing piece"
                )
            }
        }
    }
}

impl std::error::Error for ProgramError {}

impl ProgramError {
    /// **The OPERATOR half of a refusal whose cause is MISSING SERVER MACHINERY** — `Some(detail)`
    /// for the small class of refusals that say nothing about the caller's move and everything about
    /// how this binary was built, `None` for every ordinary constraint violation.
    ///
    /// Two audiences were sharing one string. `Display` is what a refusal shows a player (it reaches
    /// a Discord embed / a Telegram message / a web toast through
    /// `TurnError::ProgramViolation { reason }`), so it must be a sentence a human can act on. The
    /// export names, the function to call and the archive to rebuild belong in a log line, which is
    /// what this returns: `dregg-turn`'s executor emits it at `tracing::error!` the moment the
    /// refusal is produced, so an operator gets the fix at the same instant a player gets the
    /// apology.
    ///
    /// A NEW variant belongs here iff no input the caller could have chosen would have avoided it.
    pub fn operator_diagnostic(&self) -> Option<String> {
        match self {
            ProgramError::ConstraintOracleUnavailable { constraint } => {
                // The refusing constraint is the single most useful datum (which tooth, on which
                // slot), but it is decoded from untrusted wire bytes and an `AffineLe` term list is
                // unbounded — so it is truncated rather than allowed to flood a log. Truncated by
                // CHARS, not bytes: a `Custom` variant can carry attacker-chosen UTF-8 from the
                // wire, and `String::truncate` PANICS on a non-char-boundary index — a panic in the
                // logging path of a fail-closed refusal.
                let full = format!("{constraint:?}");
                let mut which: String = full.chars().take(200).collect();
                if which.len() < full.len() {
                    which.push('…');
                }
                Some(format!(
                    "no constraint oracle installed: this native RELEASE build refuses the whole \
                     Lean-evaluated constraint subset (here: {which}) because the verified \
                     `dregg_constraint_admits` oracle is absent — fail-closed, so EVERY \
                     programmed-cell turn (the Descent, the dungeon, the campaign) will refuse. \
                     Arm it at startup with `dregg_exec_lean::register_constraint_oracle()`; the \
                     SDK already does that from `AgentRuntime::new`, so a `false` return means the \
                     linked `libdregg_lean.a` does not export `dregg_constraint_admits` — this \
                     binary was built without a HEAD-matching Lean archive (e.g. \
                     `DREGG_REQUIRE_LEAN=0`) and cannot serve turns"
                ))
            }
            _ => None,
        }
    }
}

/// Backwards-compatible alias for the v0 error name (kept so existing match
/// arms in `turn::executor::handle_program_violation` keep compiling). The
/// new name is `TransitionCheckRequiresOldState` — semantically broader,
/// since the same shape applies to all `(old, new)` transition variants.
#[allow(non_upper_case_globals)]
impl ProgramError {
    /// Legacy constructor name preserved for backwards compatibility.
    #[doc(hidden)]
    pub fn immutable_check_requires_old_state(index: u8) -> Self {
        ProgramError::TransitionCheckRequiresOldState {
            constraint: StateConstraint::Immutable { index },
            index,
        }
    }
}
