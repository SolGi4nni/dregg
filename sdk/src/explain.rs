//! `explain`: the cipherclerk's third reading of a turn (W4 — the clerk that
//! cannot misstate what a turn does; DREGG3 §2.4).
//!
//! A turn term has three readings: it can be **executed** (the executor walks
//! the call forest and applies effects), it can be **proved** (the circuit
//! witnesses the same evolution), and — here — it can be **explained**: a
//! deterministic rendering of exactly what the turn does, in text a citizen's
//! cipherclerk can show before authorizing. This is the seed that ends
//! blind-signing: the description on the screen is another reading of the very
//! term that executes, not a hand-written caption that can drift from it.
//!
//! # Guarantee
//!
//! The honest scope (DREGG3 §6 R6) is two structural properties, NOT
//! natural-language meaning:
//!
//! 1. **Totality.** Every [`Effect`], every [`Action`], and every [`Turn`]
//!    renders to a `String` with no panic, for all inputs. The per-effect
//!    match is exhaustive with no `_ =>` arm, so a contributor who adds an
//!    `Effect` variant is forced by the compiler to give it a reading. Every
//!    field access used here is total (slice/hex/format), so there is no
//!    `unwrap`/`expect`/indexing that could trip.
//!
//! 2. **Injectivity-on-semantics.** If two actions render to the *same* text,
//!    they have the *same* effect-semantics. Formally, with
//!    `sem(a) := a.hash()` (the canonical semantic digest the executor and the
//!    prover both bind — see [`Action::hash`]):
//!
//!    ```text
//!    explain_action(a) == explain_action(b)  ⇒  sem(a) == sem(b)
//!    ```
//!
//!    equivalently, the contrapositive that matters for the wallet:
//!
//!    ```text
//!    sem(a) != sem(b)  ⇒  explain_action(a) != explain_action(b)
//!    ```
//!
//!    so the screen **cannot show identical text for two turns that would do
//!    different things.** This is enforced structurally: each rendering carries
//!    a canonical `[sem <digest>]` tag derived from the term's own hash, so
//!    equal text implies equal digest implies equal semantic hash. The
//!    human-readable body is the part a person reads; the tag is the part that
//!    makes the reading *faithful*.
//!
//! What is **not** claimed: that the prose is a correct natural-language
//! account of intent. "Transfer 5 from A to B" is rendered structurally; the
//! guarantee is that no *other* turn renders to that same string unless it has
//! the same semantics.

use dregg_turn::{Action, Authorization, Effect, Turn};

/// Width of the canonical semantic digest tag, in hex characters (the full
/// 32-byte BLAKE3 hash → 64 hex chars). The full hash is embedded so the
/// injectivity-on-semantics guarantee rests on the executor/prover hash, not
/// on a truncation.
const SEM_TAG_HEX_LEN: usize = 64;

/// Render a short, total hex of a 32-byte identity for display.
fn hx32(b: &[u8; 32]) -> String {
    hex::encode(b)
}

/// Render the canonical semantic-digest tag for a 32-byte hash.
///
/// This is the faithfulness-carrying suffix: two renderings that share it
/// share the underlying [`Action::hash`]/[`Effect::hash`], and the digest is
/// the same value the executor and circuit bind, so equal tag ⇒ equal
/// semantics.
fn sem_tag(hash: &[u8; 32]) -> String {
    let h = hx32(hash);
    debug_assert_eq!(h.len(), SEM_TAG_HEX_LEN);
    format!("[sem {h}]")
}

/// One-line human-readable summary of a single [`Effect`]'s body — the prose a
/// citizen reads. The faithfulness tag is appended by [`explain_effect`]; this
/// helper is the structural reading of the variant's fields.
///
/// The match is exhaustive with NO `_ =>` arm: every present `Effect` variant
/// has a reading, and every future variant is forced to acquire one at compile
/// time (mirroring the discipline of [`dregg_turn::LinearityClass`]).
fn effect_body(effect: &Effect) -> String {
    match effect {
        Effect::SetField { cell, index, value } => format!(
            "set state field #{index} of cell {} to 0x{}",
            hx32(cell.as_bytes()),
            hx32(value)
        ),
        Effect::Transfer { from, to, amount } => format!(
            "transfer {amount} computrons from cell {} to cell {}",
            hx32(from.as_bytes()),
            hx32(to.as_bytes())
        ),
        Effect::GrantCapability { from, to, cap } => format!(
            "grant capability (target {} slot {}) from cell {} to cell {}",
            hx32(cap.target.as_bytes()),
            cap.slot,
            hx32(from.as_bytes()),
            hx32(to.as_bytes())
        ),
        Effect::RevokeCapability { cell, slot } => format!(
            "revoke capability in slot {slot} of cell {}",
            hx32(cell.as_bytes())
        ),
        Effect::EmitEvent { cell, event } => format!(
            "emit event (topic 0x{}, {} data field(s)) from cell {}",
            hx32(&event.topic),
            event.data.len(),
            hx32(cell.as_bytes())
        ),
        Effect::IncrementNonce { cell } => {
            format!("increment the nonce of cell {}", hx32(cell.as_bytes()))
        }
        Effect::CreateCell {
            public_key,
            token_id,
            balance,
        } => format!(
            "create a new cell (owner 0x{}, token 0x{}) with balance {balance}",
            hx32(public_key),
            hx32(token_id)
        ),
        Effect::SetPermissions { cell, .. } => format!(
            "set the permissions of cell {} (applied last in the action)",
            hx32(cell.as_bytes())
        ),
        Effect::SetVerificationKey { cell, new_vk } => format!(
            "set the verification key of cell {} to {} (applied last in the action)",
            hx32(cell.as_bytes()),
            if new_vk.is_some() { "a key" } else { "none" }
        ),
        Effect::NoteSpend {
            value, asset_type, ..
        } => format!("spend a private note (value {value}, asset {asset_type})"),
        Effect::NoteCreate {
            value, asset_type, ..
        } => format!("create a private note (value {value}, asset {asset_type})"),

        Effect::SpawnWithDelegation {
            child_public_key,
            max_staleness,
            ..
        } => format!(
            "spawn a child cell (owner 0x{}) with a delegation snapshot (max staleness {max_staleness}s)",
            hx32(child_public_key)
        ),
        Effect::RefreshDelegation => {
            "refresh this cell's delegation snapshot from its parent".to_string()
        }
        Effect::RevokeDelegation { child } => format!(
            "revoke delegation to child cell {} (by bumping the parent epoch)",
            hx32(child.as_bytes())
        ),
        Effect::BridgeMint { .. } => {
            "mint a note locally from a portable cross-federation spend proof".to_string()
        }

        Effect::Introduce {
            introducer,
            recipient,
            target,
            ..
        } => format!(
            "introduce cell {} to cell {} on target cell {}",
            hx32(introducer.as_bytes()),
            hx32(recipient.as_bytes()),
            hx32(target.as_bytes())
        ),
        Effect::PipelinedSend { action, .. } => format!(
            "pipeline a send to an eventual ref, carrying {} sub-effect(s)",
            action.effects.len()
        ),

        Effect::ExerciseViaCapability {
            cap_slot,
            inner_effects,
        } => format!(
            "exercise the capability in slot {cap_slot}, performing {} inner effect(s)",
            inner_effects.len()
        ),
        Effect::MakeSovereign { cell } => format!(
            "make cell {} sovereign (store only its state commitment)",
            hx32(cell.as_bytes())
        ),
        Effect::CreateCellFromFactory {
            factory_vk,
            owner_pubkey,
            token_id,
            ..
        } => format!(
            "create a cell from factory 0x{} (owner 0x{}, token 0x{})",
            hx32(factory_vk),
            hx32(owner_pubkey),
            hx32(token_id)
        ),

        Effect::Refusal {
            cell,
            offered_action_commitment,
            ..
        } => format!(
            "record a refusal on cell {} of offered action 0x{}",
            hx32(cell.as_bytes()),
            hx32(offered_action_commitment)
        ),

        Effect::CellSeal { target, reason } => format!(
            "seal cell {} (reason commitment 0x{})",
            hx32(target.as_bytes()),
            hx32(reason)
        ),
        Effect::CellUnseal { target } => {
            format!(
                "unseal cell {} (return it to live)",
                hx32(target.as_bytes())
            )
        }
        Effect::CellDestroy { target, .. } => format!(
            "permanently destroy cell {} (bind its death certificate)",
            hx32(target.as_bytes())
        ),
        Effect::Burn {
            target,
            slot,
            amount,
        } => format!(
            "burn {amount} from slot {slot} of cell {} (supply reduced, disclosed)",
            hx32(target.as_bytes())
        ),
        Effect::AttenuateCapability { cell, slot, .. } => format!(
            "narrow (attenuate) the capability in slot {slot} of cell {}",
            hx32(cell.as_bytes())
        ),
        Effect::ReceiptArchive {
            prefix_end_height, ..
        } => format!("archive this cell's receipt-chain prefix up to height {prefix_end_height}"),
    }
}

/// Render a single [`Effect`] to a faithful, total description.
///
/// The result is the human-readable body followed by the canonical
/// `[sem <digest>]` tag derived from [`Effect::hash`]. Two effects that render
/// identically therefore have the same effect hash — hence the same semantics
/// the executor and circuit bind.
pub fn explain_effect(effect: &Effect) -> String {
    format!("{} {}", effect_body(effect), sem_tag(&effect.hash()))
}

/// Render the [`Authorization`] mode of an action (the *how-authorized*
/// reading). Total and discriminant-complete with no `_ =>` arm.
fn auth_mode(auth: &Authorization) -> &'static str {
    match auth {
        Authorization::Signature(_, _) => "an Ed25519 signature",
        Authorization::Proof { .. } => "a zero-knowledge proof",
        Authorization::Breadstuff(_) => "a capability token",
        Authorization::Bearer(_) => "a bearer capability (delegation chain)",
        Authorization::Unchecked => "NO authorization (unchecked — only valid if the cell permits)",
        Authorization::CapTpDelivered { .. } => "a verified CapTP delivery certificate",
        Authorization::Custom { .. } => "an app-defined witnessed predicate",
        Authorization::OneOf { .. } => "one of several candidate authorizations",
        Authorization::Stealth { .. } => "a one-time stealth key",
        Authorization::Token { .. } => "a biscuit/macaroon credential",
    }
}

/// Render a single [`Action`] to a faithful, total description.
///
/// Includes the target cell, the authorization mode, each effect's reading,
/// and the action-level `[sem <digest>]` tag derived from [`Action::hash`].
/// Two actions that render identically have the same [`Action::hash`].
pub fn explain_action(action: &Action) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "Action on cell {}, authorized by {}",
        hx32(action.target.as_bytes()),
        auth_mode(&action.authorization)
    ));
    if let Some(delta) = action.balance_change {
        out.push_str(&format!(", balance change {delta}"));
    }
    out.push_str(&format!(":\n  {} effect(s):\n", action.effects.len()));
    for (i, effect) in action.effects.iter().enumerate() {
        out.push_str(&format!("    {}. {}\n", i + 1, explain_effect(effect)));
    }
    // The action-level faithfulness tag binds ALL of: target, method, args,
    // authorization, preconditions, effects, delegation/commitment mode,
    // balance_change, and witness blobs (see `Action::hash`). Equal text here
    // ⇒ equal action hash ⇒ equal semantics.
    out.push_str(&format!("  {}", sem_tag(&action.hash())));
    out
}

/// Render an entire [`Turn`] to a faithful, total description: the agent, the
/// nonce, the fee, and every action in the call forest.
///
/// Each action carries its own `[sem <digest>]`, so two turns that render
/// identically have the same per-action semantics throughout the forest.
pub fn explain_turn(turn: &Turn) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "Turn by agent {} (nonce {}, fee {})",
        hx32(turn.agent.as_bytes()),
        turn.nonce,
        turn.fee
    ));
    if let Some(memo) = &turn.memo {
        out.push_str(&format!(" memo {memo:?}"));
    }
    out.push('\n');
    // Depth-first pre-order over the call forest: every action, in execution
    // order, including children of every tree node.
    let trees: Vec<&dregg_turn::CallTree> = turn.call_forest.iter_dfs().collect();
    out.push_str(&format!("{} action(s) in the call forest:\n", trees.len()));
    for (i, tree) in trees.iter().enumerate() {
        out.push_str(&format!("[{}] {}\n", i, explain_action(&tree.action)));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::permissions::AuthRequired;
    use dregg_cell::{CapabilityRef, CellId, NoteCommitment, Nullifier, Preconditions};
    use dregg_turn::action::{Event, RefusalReason};
    use dregg_turn::{Action, Authorization, CommitmentMode, DelegationMode, Effect};

    fn cid(n: u8) -> CellId {
        CellId([n; 32])
    }

    /// A corpus that exercises EVERY `Effect` variant. If a variant is added
    /// and not given a reading, `effect_body`'s exhaustive match fails to
    /// compile; if it is added here, the totality test covers it.
    fn effect_corpus() -> Vec<Effect> {
        let cap = CapabilityRef {
            target: cid(9),
            slot: 3,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        vec![
            Effect::SetField {
                cell: cid(1),
                index: 2,
                value: [7u8; 32],
            },
            Effect::Transfer {
                from: cid(1),
                to: cid(2),
                amount: 5,
            },
            Effect::GrantCapability {
                from: cid(1),
                to: cid(2),
                cap: cap.clone(),
            },
            Effect::RevokeCapability {
                cell: cid(1),
                slot: 4,
            },
            Effect::EmitEvent {
                cell: cid(1),
                event: Event {
                    topic: [3u8; 32],
                    data: vec![[1u8; 32]],
                },
            },
            Effect::IncrementNonce { cell: cid(1) },
            Effect::CreateCell {
                public_key: [1u8; 32],
                token_id: [2u8; 32],
                balance: 100,
            },
            Effect::SetPermissions {
                cell: cid(1),
                new_permissions: dregg_cell::Permissions::default(),
            },
            Effect::SetVerificationKey {
                cell: cid(1),
                new_vk: None,
            },
            Effect::NoteSpend {
                nullifier: Nullifier([5u8; 32]),
                note_tree_root: [0u8; 32],
                value: 10,
                asset_type: 0,
                spending_proof: vec![],
                value_commitment: None,
            },
            Effect::NoteCreate {
                commitment: NoteCommitment([6u8; 32]),
                value: 10,
                asset_type: 0,
                encrypted_note: vec![],
                value_commitment: None,
                range_proof: None,
            },
            Effect::SpawnWithDelegation {
                child_public_key: [1u8; 32],
                child_token_id: [2u8; 32],
                max_staleness: 60,
            },
            Effect::RefreshDelegation,
            Effect::RevokeDelegation { child: cid(2) },
            Effect::BridgeMint {
                portable_proof: portable_proof(),
            },
            Effect::Introduce {
                introducer: cid(1),
                recipient: cid(2),
                target: cid(3),
                permissions: AuthRequired::Signature,
            },
            Effect::PipelinedSend {
                target: dregg_turn::eventual::EventualRef::new([9u8; 32], 0),
                action: Box::new(sample_action(vec![Effect::IncrementNonce { cell: cid(1) }])),
            },
            Effect::ExerciseViaCapability {
                cap_slot: 0,
                inner_effects: vec![Effect::IncrementNonce { cell: cid(3) }],
            },
            Effect::MakeSovereign { cell: cid(1) },
            Effect::CreateCellFromFactory {
                factory_vk: [13u8; 32],
                owner_pubkey: [1u8; 32],
                token_id: [2u8; 32],
                params: factory_params(),
            },
            Effect::Refusal {
                cell: cid(1),
                offered_action_commitment: [18u8; 32],
                refusal_reason: RefusalReason::Declined,
                proof_witness_index: 0,
            },
            Effect::CellSeal {
                target: cid(1),
                reason: [20u8; 32],
            },
            Effect::CellUnseal { target: cid(1) },
            Effect::CellDestroy {
                target: cid(1),
                certificate: death_cert(),
            },
            Effect::Burn {
                target: cid(1),
                slot: 0,
                amount: 5,
            },
            Effect::AttenuateCapability {
                cell: cid(1),
                slot: 0,
                narrower_permissions: AuthRequired::Signature,
                narrower_effects: None,
                narrower_expiry: None,
            },
            Effect::ReceiptArchive {
                prefix_end_height: 42,
                checkpoint: archival_attestation(),
            },
        ]
    }

    // ---- minimal valid constructors for nested witness types ----

    fn attested_root() -> dregg_types::AttestedRoot {
        dregg_types::AttestedRoot {
            merkle_root: [0u8; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 1,
            timestamp: 0,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 0,
            federation_id: dregg_types::FederationId::PLACEHOLDER,
            receipt_stream_root: None,
        }
    }

    fn portable_proof() -> dregg_cell::note_bridge::PortableNoteProof {
        dregg_cell::note_bridge::PortableNoteProof {
            nullifier: [5u8; 32],
            destination_federation: [8u8; 32],
            source_root: attested_root(),
            spending_proof: vec![],
            destination_commitment: NoteCommitment([6u8; 32]),
            value: 10,
            asset_type: 0,
        }
    }

    fn death_cert() -> dregg_cell::lifecycle::DeathCertificate {
        dregg_cell::lifecycle::DeathCertificate {
            cell_id: cid(1),
            last_receipt_hash: [0u8; 32],
            final_state_commitment: [0u8; 32],
            destroyed_at_height: 0,
            reason: dregg_cell::lifecycle::DeathReason::Voluntary,
        }
    }

    fn archival_attestation() -> dregg_cell::lifecycle::ArchivalAttestation {
        dregg_cell::lifecycle::ArchivalAttestation {
            cell_id: cid(1),
            archive_start_height: 0,
            archive_end_height: 42,
            archive_blob_hash: [0u8; 32],
            archive_terminal_commitment: [0u8; 32],
            archive_terminal_receipt_hash: [0u8; 32],
        }
    }

    fn factory_params() -> dregg_cell::factory::FactoryCreationParams {
        dregg_cell::factory::FactoryCreationParams {
            mode: dregg_cell::CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: [1u8; 32],
        }
    }

    fn sample_action(effects: Vec<Effect>) -> Action {
        Action {
            target: cid(1),
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        }
    }

    /// TOTALITY: every effect in the corpus renders to a non-empty string and
    /// carries the faithfulness tag — no panic, for every variant.
    #[test]
    fn explain_effect_is_total_over_corpus() {
        for effect in effect_corpus() {
            let s = explain_effect(&effect);
            assert!(!s.is_empty(), "empty rendering for {effect:?}");
            assert!(
                s.contains("[sem "),
                "missing faithfulness tag for {effect:?}: {s}"
            );
        }
    }

    /// INJECTIVITY-ON-SEMANTICS (effect level): the rendering refines the
    /// semantic digest. For every distinct pair in the corpus, distinct
    /// `Effect::hash` ⇒ distinct rendering. (The corpus is constructed so all
    /// members have distinct hashes; we assert renderings stay distinct too.)
    #[test]
    fn explain_effect_injective_on_semantics() {
        let corpus = effect_corpus();
        for (i, a) in corpus.iter().enumerate() {
            for (j, b) in corpus.iter().enumerate() {
                if i == j {
                    continue;
                }
                if a.hash() != b.hash() {
                    assert_ne!(
                        explain_effect(a),
                        explain_effect(b),
                        "distinct-semantics effects #{i} and #{j} rendered identically"
                    );
                }
            }
        }
    }

    /// INJECTIVITY-ON-SEMANTICS (action level): the precise guarantee. Two
    /// actions with the same rendering have the same `Action::hash` (the
    /// digest the executor and circuit bind). We verify the contrapositive on
    /// a corpus of single-effect actions plus targeted near-collisions that
    /// differ ONLY in a semantic field.
    #[test]
    fn explain_action_injective_on_semantics() {
        let mut actions: Vec<Action> = effect_corpus()
            .into_iter()
            .map(|e| sample_action(vec![e]))
            .collect();

        // Near-collision pairs: bodies identical except a semantic field the
        // structural prose elides (e.g. a hidden proof/witness payload, a
        // sealed-box ciphertext). The `[sem ...]` tag must still separate
        // them.
        actions.push(sample_action(vec![Effect::NoteSpend {
            nullifier: Nullifier([5u8; 32]),
            note_tree_root: [0u8; 32],
            value: 10,
            asset_type: 0,
            spending_proof: vec![1, 2, 3], // differs only in proof bytes
            value_commitment: None,
        }]));
        actions.push(sample_action(vec![Effect::NoteCreate {
            commitment: NoteCommitment([6u8; 32]),
            value: 10,
            asset_type: 0,
            encrypted_note: vec![9, 9, 9], // differs only in elided ciphertext
            value_commitment: None,
            range_proof: None,
        }]));
        // Same effects, different authorization mode (semantic).
        let mut alt_auth = sample_action(vec![Effect::IncrementNonce { cell: cid(1) }]);
        alt_auth.authorization = Authorization::Signature([1u8; 32], [2u8; 32]);
        actions.push(alt_auth);
        // Same effects, different balance_change (semantic).
        let mut alt_bal = sample_action(vec![Effect::IncrementNonce { cell: cid(1) }]);
        alt_bal.balance_change = Some(7);
        actions.push(alt_bal);

        for (i, a) in actions.iter().enumerate() {
            for (j, b) in actions.iter().enumerate() {
                if i == j {
                    continue;
                }
                if a.hash() != b.hash() {
                    assert_ne!(
                        explain_action(a),
                        explain_action(b),
                        "actions #{i} and #{j} differ in semantics but render identically"
                    );
                }
            }
        }
    }

    /// Faithfulness tag presence: the action rendering carries the canonical
    /// digest, and identical text implies identical hash by construction.
    #[test]
    fn explain_action_carries_sem_tag() {
        let a = sample_action(vec![Effect::IncrementNonce { cell: cid(1) }]);
        let rendered = explain_action(&a);
        assert!(rendered.contains(&hx32(&a.hash())));
    }

    /// Non-vacuity of the injectivity test: at least one near-collision pair
    /// has identical prose body but distinct sem-tag (so the tag, not the
    /// prose, is what discriminates).
    #[test]
    fn sem_tag_discriminates_when_prose_collides() {
        let a = Effect::NoteSpend {
            nullifier: Nullifier([5u8; 32]),
            note_tree_root: [0u8; 32],
            value: 10,
            asset_type: 0,
            spending_proof: vec![],
            value_commitment: None,
        };
        let b = Effect::NoteSpend {
            nullifier: Nullifier([5u8; 32]),
            note_tree_root: [0u8; 32],
            value: 10,
            asset_type: 0,
            spending_proof: vec![1, 2, 3], // only the elided proof differs
            value_commitment: None,
        };
        // Prose bodies collide (proof bytes are elided from the human text)...
        assert_eq!(effect_body(&a), effect_body(&b));
        // ...but the semantics differ, and so the full renderings differ.
        assert_ne!(a.hash(), b.hash());
        assert_ne!(explain_effect(&a), explain_effect(&b));
    }
}
