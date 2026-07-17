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

use dregg_cell::factory::FactoryCreationParams;
use dregg_cell::lifecycle::{ArchivalAttestation, DeathCertificate};
use dregg_cell::state::FieldElement;
use dregg_cell::{
    CapabilityRef, CellId, NoteCommitment, Nullifier, Permissions, VerificationKey, field_from_u64,
};
use dregg_turn::Effect;
use dregg_turn::action::{Event, RefusalReason, Symbol};

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

    /// Revoke the capability at `slot` in the acting cell's c-list
    /// (lowers to [`Effect::RevokeCapability`]).
    pub fn revoke(mut self, slot: u32) -> Self {
        let cell = self.acting_cell();
        self.effects.push(Effect::RevokeCapability { cell, slot });
        self
    }

    /// Emit an event from the acting cell (lowers to
    /// [`Effect::EmitEvent`]). Events are logged in the receipt, indexed
    /// by `topic`, and do NOT modify ledger state. Hash a string topic
    /// with [`dregg_turn::action::symbol`].
    pub fn emit_event(mut self, topic: Symbol, data: Vec<FieldElement>) -> Self {
        let cell = self.acting_cell();
        self.effects.push(Effect::EmitEvent {
            cell,
            event: Event { topic, data },
        });
        self
    }

    /// Create a new cell in the ledger (lowers to [`Effect::CreateCell`]).
    /// `balance` is debited from the acting cell by the executor's
    /// conservation gate — creation is not minting.
    pub fn create_cell(mut self, public_key: [u8; 32], token_id: [u8; 32], balance: u64) -> Self {
        self.effects.push(Effect::CreateCell {
            public_key,
            token_id,
            balance,
        });
        self
    }

    /// Replace the acting cell's permissions (lowers to
    /// [`Effect::SetPermissions`]). SECURITY: the executor applies this
    /// LAST within the action and checks every effect against the
    /// ORIGINAL (pre-action) permissions, so a turn cannot weaken
    /// permissions and exploit the weakening in the same action.
    pub fn set_permissions(mut self, new_permissions: Permissions) -> Self {
        let cell = self.acting_cell();
        self.effects.push(Effect::SetPermissions {
            cell,
            new_permissions,
        });
        self
    }

    /// Replace (or clear, with `None`) the acting cell's verification key
    /// (lowers to [`Effect::SetVerificationKey`]). Applied LAST within the
    /// action, like [`set_permissions`](Self::set_permissions).
    pub fn set_verification_key(mut self, new_vk: Option<VerificationKey>) -> Self {
        let cell = self.acting_cell();
        self.effects
            .push(Effect::SetVerificationKey { cell, new_vk });
        self
    }

    /// Spend (consume) a note by revealing its nullifier (lowers to
    /// [`Effect::NoteSpend`]). `spending_proof` is the serialized STARK
    /// spending proof; `value_commitment` opts into the committed
    /// (Pedersen) conservation path — within one turn, all notes must
    /// either carry commitments or all lack them (the executor rejects a
    /// mix).
    pub fn note_spend(
        mut self,
        nullifier: Nullifier,
        note_tree_root: [u8; 32],
        value: u64,
        asset_type: u64,
        spending_proof: Vec<u8>,
        value_commitment: Option<[u8; 32]>,
    ) -> Self {
        self.effects.push(Effect::NoteSpend {
            nullifier,
            note_tree_root,
            value,
            asset_type,
            spending_proof,
            value_commitment,
        });
        self
    }

    /// Create a new note (add its commitment to the note tree; lowers to
    /// [`Effect::NoteCreate`]). When `value_commitment` is present a
    /// `range_proof` is REQUIRED (the executor closes the hidden-inflation
    /// hole by refusing a commitment without one).
    pub fn note_create(
        mut self,
        commitment: NoteCommitment,
        value: u64,
        asset_type: u64,
        encrypted_note: Vec<u8>,
        value_commitment: Option<[u8; 32]>,
        range_proof: Option<Vec<u8>>,
    ) -> Self {
        self.effects.push(Effect::NoteCreate {
            commitment,
            value,
            asset_type,
            encrypted_note,
            value_commitment,
            range_proof,
        });
        self
    }

    /// Exercise the capability at `cap_slot` in the acting cell's c-list,
    /// running `inner_effects` against the capability's target in one
    /// atomic step (lowers to [`Effect::ExerciseViaCapability`] — the
    /// eval map: lookup + permission check + sub-effects, no two-step
    /// lookup-then-submit).
    pub fn exercise_capability(mut self, cap_slot: u32, inner_effects: Vec<Effect>) -> Self {
        self.effects.push(Effect::ExerciseViaCapability {
            cap_slot,
            inner_effects,
        });
        self
    }

    /// Transition the acting cell to sovereign mode (lowers to
    /// [`Effect::MakeSovereign`]): the federation keeps only the 32-byte
    /// state commitment and deletes the full state — the agent becomes
    /// responsible for providing cell state thereafter.
    pub fn make_sovereign(mut self) -> Self {
        let cell = self.acting_cell();
        self.effects.push(Effect::MakeSovereign { cell });
        self
    }

    /// Create a new cell from a deployed factory (lowers to
    /// [`Effect::CreateCellFromFactory`]). `params` are validated against
    /// the factory's registered constraints; the created cell records the
    /// factory in its provenance. For the full plan shape (escrow,
    /// settlement) prefer the [`factories`](crate::factories) builders.
    pub fn create_cell_from_factory(
        mut self,
        factory_vk: [u8; 32],
        owner_pubkey: [u8; 32],
        token_id: [u8; 32],
        params: FactoryCreationParams,
    ) -> Self {
        self.effects.push(Effect::CreateCellFromFactory {
            factory_vk,
            owner_pubkey,
            token_id,
            params,
        });
        self
    }

    /// Seal the acting cell (lowers to [`Effect::CellSeal`]): it rejects
    /// new effects until unsealed; state and history are preserved.
    /// `reason` is a 32-byte commitment to the sealing reason (cleartext
    /// stays off-chain). The variant requires `target == action.target`;
    /// this sugar guarantees it by using the acting cell.
    pub fn seal(mut self, reason: [u8; 32]) -> Self {
        let target = self.acting_cell();
        self.effects.push(Effect::CellSeal { target, reason });
        self
    }

    /// Reverse a seal on the acting cell (lowers to
    /// [`Effect::CellUnseal`]); rejected if the cell is not sealed.
    pub fn unseal(mut self) -> Self {
        let target = self.acting_cell();
        self.effects.push(Effect::CellUnseal { target });
        self
    }

    /// Permanently retire the acting cell (lowers to
    /// [`Effect::CellDestroy`]). The certificate's `cell_id` must match
    /// the acting cell; destruction is terminal (no later transition, all
    /// subsequent effects rejected).
    pub fn destroy(mut self, certificate: DeathCertificate) -> Self {
        let target = self.acting_cell();
        self.effects.push(Effect::CellDestroy {
            target,
            certificate,
        });
        self
    }

    /// Declare the acting cell's receipt-chain prefix up to
    /// `prefix_end_height` archived under `checkpoint` (lowers to
    /// [`Effect::ReceiptArchive`]). The attestation's `cell_id` must match
    /// the action target and its `archive_end_height` must equal
    /// `prefix_end_height` — the executor refuses a mismatch.
    pub fn receipt_archive(
        mut self,
        prefix_end_height: u64,
        checkpoint: ArchivalAttestation,
    ) -> Self {
        self.effects.push(Effect::ReceiptArchive {
            prefix_end_height,
            checkpoint,
        });
        self
    }

    /// Record a proof of NON-action on the acting cell (lowers to
    /// [`Effect::Refusal`] — evidence of absence, not a cancellation).
    /// `proof_witness_index` indexes into this turn's witness blobs
    /// (attach them via [`reveal`](Self::reveal) or the raw surface); the
    /// carried witness must bind the absence to
    /// `offered_action_commitment` and is verified through the
    /// `WitnessedPredicateRegistry`.
    pub fn refuse(
        mut self,
        offered_action_commitment: [u8; 32],
        refusal_reason: RefusalReason,
        proof_witness_index: u32,
    ) -> Self {
        let cell = self.acting_cell();
        self.effects.push(Effect::Refusal {
            cell,
            offered_action_commitment,
            refusal_reason,
            proof_witness_index,
        });
        self
    }

    /// Apply a custom-program transition to the acting (sovereign) cell
    /// (lowers to [`Effect::Custom`] — the Custom-VK door). Authority
    /// rides ONLY through the paired `CustomProgramProof` at the same
    /// index in `Turn::custom_program_proofs` on the proof-carrying
    /// sovereign path; the classical apply path REFUSES this effect
    /// fail-closed (`CustomEffectRequiresProofCarryingTurn`). Target a
    /// sovereign cell with [`on`](Self::on).
    pub fn custom(mut self, program_vk_hash: [u8; 32], proof_commitment: [u8; 32]) -> Self {
        let cell = self.acting_cell();
        self.effects.push(Effect::Custom {
            cell,
            program_vk_hash,
            proof_commitment,
        });
        self
    }

    /// Append one prebuilt effect — the escape hatch for the verbs still
    /// without dedicated sugar (`SetProgram`, `SpawnWithDelegation`,
    /// `RefreshDelegation`, `RevokeDelegation`, `BridgeMint`, `Introduce`,
    /// `PipelinedSend`, `Burn`, `Mint`, `AttenuateCapability`, `Promise`,
    /// `Notify`, `React`, `ShieldedTransfer`); the executor's gates apply
    /// identically.
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

#[cfg(test)]
mod typed_verb_teeth {
    //! Round-trip tooth per typed verb: builder → `Effect` → postcard →
    //! back, asserting the EXACT variant + fields on the round-tripped
    //! value (so both the lowering and the wire survival are checked; a
    //! field swap, variant swap, or serde asymmetry goes RED).

    use super::*;
    use crate::cipherclerk::AgentCipherclerk;
    use dregg_cell::CellMode;
    use dregg_cell::lifecycle::DeathReason;

    fn rt(domain: &str) -> AgentRuntime {
        AgentRuntime::new_simple(AgentCipherclerk::new(), domain)
    }

    /// Take the single staged effect, push it through postcard (the
    /// durable index-sensitive codec) and hand back the round-tripped
    /// value; re-serialization must be byte-identical.
    fn lowered_roundtripped(builder: TurnBuilder<'_>) -> Effect {
        assert_eq!(
            builder.effects.len(),
            1,
            "expected exactly one staged effect"
        );
        let effect = builder.effects.into_iter().next().unwrap();
        let bytes = postcard::to_stdvec(&effect).expect("serialize");
        let back: Effect = postcard::from_bytes(&bytes).expect("deserialize");
        let rebytes = postcard::to_stdvec(&back).expect("re-serialize");
        assert_eq!(bytes, rebytes, "postcard round-trip not byte-stable");
        back
    }

    #[test]
    fn revoke_lowers_to_revoke_capability() {
        let rt = rt("verb-revoke");
        let me = rt.cell_id();
        match lowered_roundtripped(rt.turn().revoke(7)) {
            Effect::RevokeCapability { cell, slot } => {
                assert_eq!(cell, me);
                assert_eq!(slot, 7);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn emit_event_lowers_to_emit_event() {
        let rt = rt("verb-emit-event");
        let me = rt.cell_id();
        let topic = dregg_turn::action::symbol("price-updated");
        let data = vec![field_from_u64(42), field_from_u64(7)];
        match lowered_roundtripped(rt.turn().emit_event(topic, data.clone())) {
            Effect::EmitEvent { cell, event } => {
                assert_eq!(cell, me);
                assert_eq!(event.topic, topic);
                assert_eq!(event.data, data);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn create_cell_lowers_to_create_cell() {
        let rt = rt("verb-create-cell");
        match lowered_roundtripped(rt.turn().create_cell([3u8; 32], [4u8; 32], 555)) {
            Effect::CreateCell {
                public_key,
                token_id,
                balance,
            } => {
                assert_eq!(public_key, [3u8; 32]);
                assert_eq!(token_id, [4u8; 32]);
                assert_eq!(balance, 555);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn set_permissions_lowers_to_set_permissions() {
        let rt = rt("verb-set-permissions");
        let me = rt.cell_id();
        let perms = Permissions::default_user();
        match lowered_roundtripped(rt.turn().set_permissions(perms.clone())) {
            Effect::SetPermissions {
                cell,
                new_permissions,
            } => {
                assert_eq!(cell, me);
                assert_eq!(new_permissions, perms);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn set_verification_key_lowers_to_set_verification_key() {
        let rt = rt("verb-set-vk");
        let me = rt.cell_id();
        let vk = VerificationKey {
            hash: [9u8; 32],
            data: vec![1, 2, 3],
        };
        match lowered_roundtripped(rt.turn().set_verification_key(Some(vk.clone()))) {
            Effect::SetVerificationKey { cell, new_vk } => {
                assert_eq!(cell, me);
                assert_eq!(new_vk, Some(vk));
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn note_spend_lowers_to_note_spend() {
        let rt = rt("verb-note-spend");
        match lowered_roundtripped(rt.turn().note_spend(
            Nullifier([5u8; 32]),
            [6u8; 32],
            1_000,
            2,
            vec![0xAA, 0xBB],
            Some([7u8; 32]),
        )) {
            Effect::NoteSpend {
                nullifier,
                note_tree_root,
                value,
                asset_type,
                spending_proof,
                value_commitment,
            } => {
                assert_eq!(nullifier, Nullifier([5u8; 32]));
                assert_eq!(note_tree_root, [6u8; 32]);
                assert_eq!(value, 1_000);
                assert_eq!(asset_type, 2);
                assert_eq!(spending_proof, vec![0xAA, 0xBB]);
                assert_eq!(value_commitment, Some([7u8; 32]));
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn note_create_lowers_to_note_create() {
        let rt = rt("verb-note-create");
        match lowered_roundtripped(rt.turn().note_create(
            NoteCommitment([8u8; 32]),
            2_000,
            3,
            vec![0xCC],
            Some([1u8; 32]),
            Some(vec![0xDD, 0xEE]),
        )) {
            Effect::NoteCreate {
                commitment,
                value,
                asset_type,
                encrypted_note,
                value_commitment,
                range_proof,
            } => {
                assert_eq!(commitment, NoteCommitment([8u8; 32]));
                assert_eq!(value, 2_000);
                assert_eq!(asset_type, 3);
                assert_eq!(encrypted_note, vec![0xCC]);
                assert_eq!(value_commitment, Some([1u8; 32]));
                assert_eq!(range_proof, Some(vec![0xDD, 0xEE]));
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn exercise_capability_lowers_to_exercise_via_capability() {
        let rt = rt("verb-exercise");
        let inner_cell = CellId([2u8; 32]);
        match lowered_roundtripped(
            rt.turn()
                .exercise_capability(4, vec![Effect::IncrementNonce { cell: inner_cell }]),
        ) {
            Effect::ExerciseViaCapability {
                cap_slot,
                inner_effects,
            } => {
                assert_eq!(cap_slot, 4);
                assert_eq!(inner_effects.len(), 1);
                match &inner_effects[0] {
                    Effect::IncrementNonce { cell } => assert_eq!(*cell, inner_cell),
                    other => panic!("wrong inner variant: {other:?}"),
                }
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn make_sovereign_lowers_to_make_sovereign() {
        let rt = rt("verb-make-sovereign");
        let me = rt.cell_id();
        match lowered_roundtripped(rt.turn().make_sovereign()) {
            Effect::MakeSovereign { cell } => assert_eq!(cell, me),
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn create_cell_from_factory_lowers_exactly() {
        let rt = rt("verb-factory-create");
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: Some([2u8; 32]),
            initial_fields: vec![(0, 11), (3, 12)],
            initial_caps: vec![],
            owner_pubkey: [3u8; 32],
        };
        match lowered_roundtripped(rt.turn().create_cell_from_factory(
            [1u8; 32],
            [3u8; 32],
            [4u8; 32],
            params.clone(),
        )) {
            Effect::CreateCellFromFactory {
                factory_vk,
                owner_pubkey,
                token_id,
                params: p,
            } => {
                assert_eq!(factory_vk, [1u8; 32]);
                assert_eq!(owner_pubkey, [3u8; 32]);
                assert_eq!(token_id, [4u8; 32]);
                assert_eq!(p, params);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn seal_lowers_to_cell_seal_on_acting_cell() {
        let rt = rt("verb-seal");
        let me = rt.cell_id();
        match lowered_roundtripped(rt.turn().seal([0xEE; 32])) {
            Effect::CellSeal { target, reason } => {
                assert_eq!(
                    target, me,
                    "seal must target the acting cell (== action.target)"
                );
                assert_eq!(reason, [0xEE; 32]);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn unseal_lowers_to_cell_unseal() {
        let rt = rt("verb-unseal");
        let me = rt.cell_id();
        match lowered_roundtripped(rt.turn().unseal()) {
            Effect::CellUnseal { target } => assert_eq!(target, me),
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn destroy_lowers_to_cell_destroy() {
        let rt = rt("verb-destroy");
        let me = rt.cell_id();
        let cert = DeathCertificate {
            cell_id: me,
            last_receipt_hash: [1u8; 32],
            final_state_commitment: [2u8; 32],
            destroyed_at_height: 99,
            reason: DeathReason::Voluntary,
        };
        match lowered_roundtripped(rt.turn().destroy(cert.clone())) {
            Effect::CellDestroy {
                target,
                certificate,
            } => {
                assert_eq!(target, me);
                assert_eq!(certificate, cert);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn receipt_archive_lowers_exactly() {
        let rt = rt("verb-receipt-archive");
        let me = rt.cell_id();
        let checkpoint = ArchivalAttestation {
            cell_id: me,
            archive_start_height: 1,
            archive_end_height: 50,
            archive_blob_hash: [4u8; 32],
            archive_terminal_commitment: [5u8; 32],
            archive_terminal_receipt_hash: [6u8; 32],
        };
        match lowered_roundtripped(rt.turn().receipt_archive(50, checkpoint.clone())) {
            Effect::ReceiptArchive {
                prefix_end_height,
                checkpoint: cp,
            } => {
                assert_eq!(prefix_end_height, 50);
                assert_eq!(cp, checkpoint);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn refuse_lowers_to_refusal() {
        let rt = rt("verb-refuse");
        let me = rt.cell_id();
        match lowered_roundtripped(
            rt.turn()
                .refuse([0xAB; 32], RefusalReason::WindowExpired, 2),
        ) {
            Effect::Refusal {
                cell,
                offered_action_commitment,
                refusal_reason,
                proof_witness_index,
            } => {
                assert_eq!(cell, me);
                assert_eq!(offered_action_commitment, [0xAB; 32]);
                assert_eq!(refusal_reason, RefusalReason::WindowExpired);
                assert_eq!(proof_witness_index, 2);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }

    #[test]
    fn custom_lowers_to_custom_and_respects_on_target() {
        let rt = rt("verb-custom");
        let sovereign = CellId([0x50; 32]);
        match lowered_roundtripped(rt.turn().on(sovereign).custom([0x11; 32], [0x22; 32])) {
            Effect::Custom {
                cell,
                program_vk_hash,
                proof_commitment,
            } => {
                assert_eq!(
                    cell, sovereign,
                    ".on(target) must route Custom to the target"
                );
                assert_eq!(program_vk_hash, [0x11; 32]);
                assert_eq!(proof_commitment, [0x22; 32]);
            }
            other => panic!("wrong variant: {other:?}"),
        }
    }
}
