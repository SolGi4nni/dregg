//! # The authorized turn builder — the SDK's one public turn shape.
//!
//! ```text
//! Identity → .turn() → typed verb builders → .sign() → .submit() → Receipt
//! ```
//!
//! [`AgentRuntime::turn()`](crate::AgentRuntime::turn) opens a
//! [`TurnBuilder`]; the typed verbs ([`transfer`](TurnBuilder::transfer),
//! [`write`](TurnBuilder::write), [`grant`](TurnBuilder::grant), …, or a
//! [`factories`](crate::factories)/[`polis`](crate::polis) plan via
//! [`effects`](TurnBuilder::effects)) accumulate the act;
//! [`sign()`](TurnBuilder::sign) binds it to the identity's Ed25519 key over
//! the canonical signing message (federation-bound, replay-separated); and
//! [`submit()`](AuthorizedTurn::submit) executes it and returns the
//! [`Receipt`] noun.
//!
//! **An unauthorized act is inexpressible here.** There is no method on this
//! surface that yields an unsigned action — by the time anything reaches the
//! executor it carries a real `Authorization::Signature`. The raw vocabulary
//! (including the genesis-only `Authorization::Unchecked`) lives behind the
//! sealed [`raw`](crate::raw) module.
//!
//! The anti-blind-signing affordance rides along:
//! [`AuthorizedTurn::explain()`] renders the clerk's faithful, total
//! explanation of exactly what was signed.

use dregg_cell::state::FieldElement;
use dregg_cell::{CapabilityRef, CellId, field_from_u64};
use dregg_turn::Effect;

use crate::error::SdkError;
use crate::raw;
use crate::receipt::Receipt;
use crate::runtime::AgentRuntime;

/// Who acts and pays for the turn being built.
#[derive(Clone, Copy, Debug)]
enum Acting {
    /// Ordinary agent turn: the runtime's own agent cell acts and pays.
    Agent,
    /// Agent-paid turn whose ACTION targets another cell the identity
    /// administers (signature verified against the target's `owner_pubkey`;
    /// parent-gate capability required). The production shape for driving
    /// factory-born cells.
    On(CellId),
    /// Cell-agent turn: `cell` is the turn agent AND action target, paying
    /// `fee` from its own balance (the one-time adopt bootstrap shape).
    AsCell(CellId, u64),
}

/// The typed verb builder. Open one with
/// [`AgentRuntime::turn()`](crate::AgentRuntime::turn); finish with
/// [`sign()`](Self::sign).
#[derive(Debug)]
pub struct TurnBuilder<'rt> {
    runtime: &'rt AgentRuntime,
    acting: Acting,
    method: String,
    effects: Vec<Effect>,
    witness_blobs: Vec<dregg_turn::action::WitnessBlob>,
    fee: Option<u64>,
}

impl<'rt> TurnBuilder<'rt> {
    pub(crate) fn new(runtime: &'rt AgentRuntime) -> Self {
        TurnBuilder {
            runtime,
            acting: Acting::Agent,
            method: "execute".to_string(),
            effects: Vec::new(),
            witness_blobs: Vec::new(),
            fee: None,
        }
    }

    /// The cell whose authority this turn exercises (the default `from` /
    /// write target for the typed verbs).
    fn acting_cell(&self) -> CellId {
        match self.acting {
            Acting::Agent => self.runtime.cell_id(),
            Acting::On(t) => t,
            Acting::AsCell(c, _) => c,
        }
    }

    /// Target another cell the identity administers (the action targets
    /// `target`; this agent signs and pays). The executor verifies the
    /// signature against `target`'s `owner_pubkey` and requires the agent's
    /// c-list capability on it — the [`AgentRuntime::execute_on`] shape.
    pub fn on(mut self, target: CellId) -> Self {
        self.acting = Acting::On(target);
        self
    }

    /// Act AS `cell` (cell-agent turn): `cell` is the turn agent and pays
    /// `fee` from its own balance — the [`AgentRuntime::execute_as`] shape
    /// used for the one-time factory adopt bootstrap.
    pub fn as_cell(mut self, cell: CellId, fee: u64) -> Self {
        self.acting = Acting::AsCell(cell, fee);
        self
    }

    /// Set the action's method verb (default `"execute"`). Workers under a
    /// scoped capability credential are admitted per-method.
    pub fn method(mut self, name: &str) -> Self {
        self.method = name.to_string();
        self
    }

    /// Set the turn fee (computron budget). Defaults to the runtime's
    /// standard fee (or the `as_cell` fee).
    pub fn fee(mut self, fee: u64) -> Self {
        self.fee = Some(fee);
        self
    }

    // ─── typed verbs ───

    /// Transfer `amount` computrons from the acting cell to `to`.
    pub fn transfer(mut self, to: CellId, amount: u64) -> Self {
        let from = self.acting_cell();
        self.effects.push(Effect::Transfer { from, to, amount });
        self
    }

    /// Transfer with an explicit source cell (must still be within this
    /// identity's authority — the executor checks, not the builder).
    pub fn transfer_from(mut self, from: CellId, to: CellId, amount: u64) -> Self {
        self.effects.push(Effect::Transfer { from, to, amount });
        self
    }

    /// Write state slot `index` of the acting cell (the `write` verb;
    /// admitted only where the cell's installed program allows).
    pub fn write(mut self, index: usize, value: FieldElement) -> Self {
        let cell = self.acting_cell();
        self.effects.push(Effect::SetField { cell, index, value });
        self
    }

    /// [`write`](Self::write) with a numeric value (encoded like
    /// [`field_from_u64`]).
    pub fn write_u64(self, index: usize, value: u64) -> Self {
        self.write(index, field_from_u64(value))
    }

    /// Grant a capability from the acting cell to `to` (the `grant` verb —
    /// non-amplifying: the executor admits only grants within held
    /// authority).
    pub fn grant(mut self, to: CellId, cap: CapabilityRef) -> Self {
        let from = self.acting_cell();
        self.effects.push(Effect::GrantCapability { from, to, cap });
        self
    }

    /// Bump the acting cell's nonce (a deliberate no-op state advance).
    pub fn increment_nonce(mut self) -> Self {
        let cell = self.acting_cell();
        self.effects.push(Effect::IncrementNonce { cell });
        self
    }

    /// Append one prebuilt effect (escape for verbs without dedicated
    /// sugar; the executor's gates apply identically).
    pub fn effect(mut self, effect: Effect) -> Self {
        self.effects.push(effect);
        self
    }

    /// Append a prebuilt effect list — the splice point for the
    /// [`factories`](crate::factories) / [`polis`](crate::polis) /
    /// [`program`](crate::program) plan builders (`plan.create_effects`,
    /// `release_escrow(..)`, `propose(..)`, …).
    pub fn effects(mut self, effects: impl IntoIterator<Item = Effect>) -> Self {
        self.effects.extend(effects);
        self
    }

    /// Exhibit a 32-byte preimage witness with this turn (the `reveal`
    /// verb). The blob rides `Action::witness_blobs` UNDER the signature
    /// and is what `PreimageGate` / `KeyRotationGate` cell programs verify
    /// against the committed digest — the identity pre-rotation rotate
    /// turn carries the presented key-set commitment this way.
    pub fn reveal(mut self, preimage: [u8; 32]) -> Self {
        self.witness_blobs.push(dregg_turn::action::WitnessBlob {
            kind: dregg_turn::action::WitnessKind::Preimage32,
            bytes: preimage.to_vec(),
        });
        self
    }

    // ─── terminal ───

    /// Sign the built action with this identity's key over the canonical
    /// federation-bound signing message, yielding an [`AuthorizedTurn`]
    /// ready to [`submit`](AuthorizedTurn::submit).
    ///
    /// After this point the act is credentialed; there is no way back to an
    /// unauthorized shape.
    pub fn sign(self) -> Result<AuthorizedTurn<'rt>, SdkError> {
        if self.effects.is_empty() {
            return Err(SdkError::Rejected(
                "refusing to sign an empty turn (no effects staged)".to_string(),
            ));
        }
        let target = self.acting_cell();
        let mut unsigned = raw::unsigned_action_named(target, &self.method, self.effects);
        // Witnesses are attached BEFORE signing so the signature covers
        // them (the `set_field_with_preimage` shape in the executor's
        // coverage tests).
        unsigned.witness_blobs = self.witness_blobs;
        // The signature binds the turn nonce (`dregg-action-sig-v3`): the
        // runtime counter for agent-paid turns, the CELL's on-ledger replay
        // counter for `.as_cell(..)` turns — the same values `submit` stamps
        // on the turn.
        let turn_nonce = match self.acting {
            Acting::Agent | Acting::On(_) => self.runtime.next_agent_turn_nonce(),
            Acting::AsCell(cell, _) => {
                let ledger = self.runtime.ledger().lock().unwrap();
                ledger
                    .get(&cell)
                    .ok_or(SdkError::Turn(dregg_turn::TurnError::CellNotFound {
                        id: cell,
                    }))?
                    .state
                    .nonce()
            }
        };
        let action = self.runtime.sign_action_for_runtime(unsigned, turn_nonce);
        Ok(AuthorizedTurn {
            runtime: self.runtime,
            acting: self.acting,
            action,
            fee: self.fee,
        })
    }
}

/// A signed, ready-to-submit turn. Produced by [`TurnBuilder::sign`];
/// consumed by [`submit`](Self::submit).
#[derive(Debug)]
pub struct AuthorizedTurn<'rt> {
    runtime: &'rt AgentRuntime,
    acting: Acting,
    action: dregg_turn::Action,
    fee: Option<u64>,
}

impl AuthorizedTurn<'_> {
    /// The clerk's faithful, total explanation of exactly what was signed
    /// (the anti-blind-signing reading; see [`crate::explain`]).
    pub fn explain(&self) -> String {
        crate::explain::explain_action(&self.action)
    }

    /// The signed action (inspection only — `submit` consumes `self`).
    pub fn action(&self) -> &dregg_turn::Action {
        &self.action
    }

    /// Execute the turn and return the [`Receipt`] noun.
    ///
    /// Routing follows the builder's acting mode: an ordinary agent turn
    /// (or `.on(target)`) is agent-paid and appended to the identity's
    /// receipt chain; an `.as_cell(..)` turn is paid by the cell and
    /// belongs to the cell's history.
    pub fn submit(self) -> Result<Receipt, SdkError> {
        let receipt = match self.acting {
            Acting::Agent | Acting::On(_) => self
                .runtime
                .submit_signed_action_as_agent(self.action, self.fee.unwrap_or(10_000))?,
            Acting::AsCell(cell, cell_fee) => self.runtime.submit_signed_action_as_cell(
                cell,
                self.action,
                self.fee.unwrap_or(cell_fee),
            )?,
        };
        Ok(Receipt::new(receipt))
    }
}
