//! Atomic history linkage for private semantic graph reductions.
//!
//! A hiding proof establishes one Lean-authored bounded rewrite. This module
//! supplies the distributed-history teeth around those proofs: every receipt in
//! one history has the same domain, session, and private ruleset root; indices
//! advance exactly once; and each accepted `old_root` is the preceding
//! `new_root`. A batch is fully verified against a staged head before the real
//! history changes, so a bad suffix cannot partially land a good prefix.

use dregg_circuit::field::BABYBEAR_P;
use dregg_circuit_prove::private_graph_rewrite::{
    PrivateGraphRewriteZkProof, PublicStatement, verify_postcard,
};
use dregg_circuit_prove::private_quest_graph::PrivateQuestGraphZkProof;
use serde::{Deserialize, Serialize};

/// Opaque proof bytes plus the exact public statement they claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateGraphRewriteReceipt {
    pub statement: PublicStatement,
    proof_bytes: Vec<u8>,
}

impl PrivateGraphRewriteReceipt {
    pub fn from_proof(
        proof: &PrivateGraphRewriteZkProof,
        statement: PublicStatement,
    ) -> Result<Self, PrivateGraphRewriteHistoryError> {
        Ok(Self {
            statement,
            proof_bytes: proof
                .to_postcard()
                .map_err(PrivateGraphRewriteHistoryError::InvalidProof)?,
        })
    }

    /// Construct a receipt for the Warden-rules-pinned specialization.  The
    /// wire shape is intentionally identical; the history's verifier policy,
    /// not attacker-controlled receipt bytes, selects the descriptor/VK.
    pub fn from_quest_proof(
        proof: &PrivateQuestGraphZkProof,
        statement: PublicStatement,
    ) -> Result<Self, PrivateGraphRewriteHistoryError> {
        Ok(Self {
            statement,
            proof_bytes: proof
                .to_postcard()
                .map_err(PrivateGraphRewriteHistoryError::InvalidProof)?,
        })
    }

    /// Import a receipt from its wire parts. No trust is placed in either part
    /// until the history verifier checks it.
    pub fn from_wire_parts(statement: PublicStatement, proof_bytes: Vec<u8>) -> Self {
        Self {
            statement,
            proof_bytes,
        }
    }

    pub fn proof_bytes(&self) -> &[u8] {
        &self.proof_bytes
    }

    /// Stable transport form.  The statement is encoded as the descriptor's
    /// exact public-input vector rather than as a duplicate Rust struct layout.
    pub fn to_wire(&self) -> PrivateGraphRewriteWireReceipt {
        PrivateGraphRewriteWireReceipt {
            public_inputs: self.statement.as_u32_vec(),
            proof_bytes: self.proof_bytes.clone(),
        }
    }
}

/// Network/storage representation of one private rewrite receipt.
///
/// Decoding checks the exact 29-field descriptor ABI (including protocol
/// version, shape, and BabyBear canonicality).  Cryptographic validity remains
/// the history verifier's job: merely decoding this type never accepts a step.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivateGraphRewriteWireReceipt {
    pub public_inputs: Vec<u32>,
    pub proof_bytes: Vec<u8>,
}

impl PrivateGraphRewriteWireReceipt {
    pub fn to_postcard(&self) -> Result<Vec<u8>, PrivateGraphRewriteHistoryError> {
        postcard::to_allocvec(self).map_err(|error| {
            PrivateGraphRewriteHistoryError::WireFormat(format!(
                "cannot encode private rewrite receipt: {error}"
            ))
        })
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, PrivateGraphRewriteHistoryError> {
        postcard::from_bytes(bytes).map_err(|error| {
            PrivateGraphRewriteHistoryError::WireFormat(format!(
                "cannot decode private rewrite receipt: {error}"
            ))
        })
    }

    pub fn into_receipt(
        self,
    ) -> Result<PrivateGraphRewriteReceipt, PrivateGraphRewriteHistoryError> {
        let statement = PublicStatement::try_from_u32s(&self.public_inputs)
            .map_err(PrivateGraphRewriteHistoryError::InvalidStatement)?;
        Ok(PrivateGraphRewriteReceipt::from_wire_parts(
            statement,
            self.proof_bytes,
        ))
    }
}

/// The public continuation point of one private rewrite history.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivateGraphRewriteHead {
    pub domain: u32,
    pub session: u32,
    pub ruleset_root: [u32; 8],
    pub next_index: u32,
    pub current_root: [u32; 8],
}

/// Verifier policy fixed by a history at creation/import.  Receipts do not
/// carry this tag, so a generic proof cannot ask a Warden history to downgrade
/// itself.  `GenericV1` remains the serde default for old snapshots.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrivateGraphRewriteVerifier {
    #[default]
    GenericV1,
    WardenQuestV1,
}

/// Durable history image.  It carries only the origin and proof receipts; the
/// current head is deliberately absent and is recomputed by verification on
/// import, so a cached endpoint cannot be forged independently of the proofs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivateGraphRewriteHistorySnapshot {
    pub origin: PrivateGraphRewriteHead,
    #[serde(default)]
    pub verifier: PrivateGraphRewriteVerifier,
    pub receipts: Vec<PrivateGraphRewriteWireReceipt>,
}

impl PrivateGraphRewriteHistorySnapshot {
    pub fn to_postcard(&self) -> Result<Vec<u8>, PrivateGraphRewriteHistoryError> {
        postcard::to_allocvec(self).map_err(|error| {
            PrivateGraphRewriteHistoryError::WireFormat(format!(
                "cannot encode private rewrite history: {error}"
            ))
        })
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, PrivateGraphRewriteHistoryError> {
        postcard::from_bytes(bytes).map_err(|error| {
            PrivateGraphRewriteHistoryError::WireFormat(format!(
                "cannot decode private rewrite history: {error}"
            ))
        })
    }

    /// Rebuild a live history by checking every stored proof and linkage seam.
    pub fn verify(self) -> Result<PrivateGraphRewriteHistory, PrivateGraphRewriteHistoryError> {
        let mut history =
            PrivateGraphRewriteHistory::new_with_verifier(self.origin, self.verifier)?;
        let receipts = self
            .receipts
            .into_iter()
            .map(PrivateGraphRewriteWireReceipt::into_receipt)
            .collect::<Result<Vec<_>, _>>()?;
        history.append_batch_verified(&receipts)?;
        history.audit()?;
        Ok(history)
    }
}

#[derive(Clone, Debug)]
pub struct PrivateGraphRewriteHistory {
    origin: PrivateGraphRewriteHead,
    head: PrivateGraphRewriteHead,
    verifier: PrivateGraphRewriteVerifier,
    statements: Vec<PublicStatement>,
    receipts: Vec<PrivateGraphRewriteReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateGraphRewriteHistoryError {
    NonCanonicalHead,
    InvalidStatement(String),
    WireFormat(String),
    CorruptHistory,
    DomainMismatch { expected: u32, claimed: u32 },
    SessionMismatch { expected: u32, claimed: u32 },
    RulesetMismatch,
    IndexMismatch { expected: u32, claimed: u32 },
    OldRootMismatch,
    IndexOverflow,
    InvalidProof(String),
}

impl std::fmt::Display for PrivateGraphRewriteHistoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NonCanonicalHead => write!(f, "private rewrite history head is noncanonical"),
            Self::InvalidStatement(reason) => {
                write!(f, "private rewrite statement is invalid: {reason}")
            }
            Self::WireFormat(reason) => write!(f, "private rewrite wire format refused: {reason}"),
            Self::CorruptHistory => write!(f, "private rewrite stored history is inconsistent"),
            Self::DomainMismatch { expected, claimed } => write!(
                f,
                "private rewrite domain mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::SessionMismatch { expected, claimed } => write!(
                f,
                "private rewrite session mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::RulesetMismatch => write!(f, "private rewrite ruleset root mismatch"),
            Self::IndexMismatch { expected, claimed } => write!(
                f,
                "private rewrite index mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::OldRootMismatch => write!(f, "private rewrite old root is not the history head"),
            Self::IndexOverflow => write!(f, "private rewrite history index overflow"),
            Self::InvalidProof(reason) => write!(f, "private rewrite proof refused: {reason}"),
        }
    }
}

impl std::error::Error for PrivateGraphRewriteHistoryError {}

impl PrivateGraphRewriteHistory {
    pub fn new(head: PrivateGraphRewriteHead) -> Result<Self, PrivateGraphRewriteHistoryError> {
        Self::new_with_verifier(head, PrivateGraphRewriteVerifier::GenericV1)
    }

    pub fn new_with_verifier(
        head: PrivateGraphRewriteHead,
        verifier: PrivateGraphRewriteVerifier,
    ) -> Result<Self, PrivateGraphRewriteHistoryError> {
        let canonical = [head.domain, head.session, head.next_index]
            .into_iter()
            .chain(head.ruleset_root)
            .chain(head.current_root)
            .all(|value| value < BABYBEAR_P);
        if !canonical {
            return Err(PrivateGraphRewriteHistoryError::NonCanonicalHead);
        }
        Ok(Self {
            origin: head,
            head,
            verifier,
            statements: Vec::new(),
            receipts: Vec::new(),
        })
    }

    pub const fn origin(&self) -> PrivateGraphRewriteHead {
        self.origin
    }

    pub const fn head(&self) -> PrivateGraphRewriteHead {
        self.head
    }

    pub const fn verifier(&self) -> PrivateGraphRewriteVerifier {
        self.verifier
    }

    pub fn statements(&self) -> &[PublicStatement] {
        &self.statements
    }

    /// The complete replay evidence, not just the public endpoints.
    pub fn receipts(&self) -> &[PrivateGraphRewriteReceipt] {
        &self.receipts
    }

    /// Export the minimal durable image.  Import never trusts a cached head;
    /// [`PrivateGraphRewriteHistorySnapshot::verify`] reconstructs it.
    pub fn snapshot(&self) -> PrivateGraphRewriteHistorySnapshot {
        PrivateGraphRewriteHistorySnapshot {
            origin: self.origin,
            verifier: self.verifier,
            receipts: self
                .receipts
                .iter()
                .map(PrivateGraphRewriteReceipt::to_wire)
                .collect(),
        }
    }

    /// Exact verifier identity for the compact standalone 29-PI receipts stored
    /// in this history.  This is deliberately distinct from the 45-PI custom-
    /// cell carrier VK, which additionally binds real cell pre/post roots and
    /// the stored application root.
    pub fn verification_key() -> [u8; 32] {
        dregg_circuit_prove::private_graph_rewrite::canonical_vk_hash()
    }

    /// Exact VK selected for this history.  This is part of durable policy,
    /// never inferred from a submitted proof.
    pub fn selected_verification_key(&self) -> [u8; 32] {
        match self.verifier {
            PrivateGraphRewriteVerifier::GenericV1 => Self::verification_key(),
            PrivateGraphRewriteVerifier::WardenQuestV1 => {
                dregg_circuit_prove::private_quest_graph::canonical_vk_hash()
            }
        }
    }

    pub fn verify_next(
        &self,
        receipt: &PrivateGraphRewriteReceipt,
    ) -> Result<PrivateGraphRewriteHead, PrivateGraphRewriteHistoryError> {
        verify_against(self.head, self.verifier, receipt)
    }

    pub fn append_verified(
        &mut self,
        receipt: PrivateGraphRewriteReceipt,
    ) -> Result<(), PrivateGraphRewriteHistoryError> {
        let next = self.verify_next(&receipt)?;
        self.head = next;
        self.statements.push(receipt.statement);
        self.receipts.push(receipt);
        Ok(())
    }

    /// Verify a whole suffix before committing any of it. This is the history
    /// analog of an atomic turn: one bad proof or seam leaves both the head and
    /// the receipt log byte-for-byte unchanged.
    pub fn append_batch_verified(
        &mut self,
        receipts: &[PrivateGraphRewriteReceipt],
    ) -> Result<(), PrivateGraphRewriteHistoryError> {
        let mut staged = self.head;
        for receipt in receipts {
            staged = verify_against(staged, self.verifier, receipt)?;
        }
        self.head = staged;
        self.statements
            .extend(receipts.iter().map(|receipt| receipt.statement));
        self.receipts.extend_from_slice(receipts);
        Ok(())
    }

    /// Re-verify the complete retained proof log from its immutable origin.
    /// This is suitable for restart/import auditing and detects any mismatch
    /// between the stored evidence, public statement log, and cached head.
    pub fn audit(&self) -> Result<(), PrivateGraphRewriteHistoryError> {
        if self.statements.len() != self.receipts.len() {
            return Err(PrivateGraphRewriteHistoryError::CorruptHistory);
        }
        let mut replayed = self.origin;
        for (statement, receipt) in self.statements.iter().zip(&self.receipts) {
            if statement != &receipt.statement {
                return Err(PrivateGraphRewriteHistoryError::CorruptHistory);
            }
            replayed = verify_against(replayed, self.verifier, receipt)?;
        }
        if replayed != self.head {
            return Err(PrivateGraphRewriteHistoryError::CorruptHistory);
        }
        Ok(())
    }
}

fn verify_against(
    head: PrivateGraphRewriteHead,
    verifier: PrivateGraphRewriteVerifier,
    receipt: &PrivateGraphRewriteReceipt,
) -> Result<PrivateGraphRewriteHead, PrivateGraphRewriteHistoryError> {
    let statement = receipt.statement;
    statement
        .validate()
        .map_err(PrivateGraphRewriteHistoryError::InvalidStatement)?;
    if statement.domain != head.domain {
        return Err(PrivateGraphRewriteHistoryError::DomainMismatch {
            expected: head.domain,
            claimed: statement.domain,
        });
    }
    if statement.session != head.session {
        return Err(PrivateGraphRewriteHistoryError::SessionMismatch {
            expected: head.session,
            claimed: statement.session,
        });
    }
    if statement.ruleset_root != head.ruleset_root {
        return Err(PrivateGraphRewriteHistoryError::RulesetMismatch);
    }
    if statement.index != head.next_index {
        return Err(PrivateGraphRewriteHistoryError::IndexMismatch {
            expected: head.next_index,
            claimed: statement.index,
        });
    }
    if statement.old_root != head.current_root {
        return Err(PrivateGraphRewriteHistoryError::OldRootMismatch);
    }
    let next_index = head
        .next_index
        .checked_add(1)
        .filter(|value| *value < BABYBEAR_P)
        .ok_or(PrivateGraphRewriteHistoryError::IndexOverflow)?;
    match verifier {
        PrivateGraphRewriteVerifier::GenericV1 => {
            verify_postcard(receipt.proof_bytes(), &statement.as_u32_vec())
        }
        PrivateGraphRewriteVerifier::WardenQuestV1 => {
            dregg_circuit_prove::private_quest_graph::verify_postcard(
                receipt.proof_bytes(),
                &statement.as_u32_vec(),
            )
        }
    }
    .map_err(PrivateGraphRewriteHistoryError::InvalidProof)?;
    Ok(PrivateGraphRewriteHead {
        next_index,
        current_root: statement.new_root,
        ..head
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit_prove::private_graph_rewrite::{
        BoundedContext, BoundedGraph, BoundedPattern, BoundedRule, HostEdgeSlot,
        PrivateGraphRewriteWitness, RuleEdgeSlot, prove_zk,
    };

    fn pattern(slots: [RuleEdgeSlot; 2]) -> BoundedPattern {
        BoundedPattern { slots }
    }

    fn two_step_witnesses() -> (PrivateGraphRewriteWitness, PrivateGraphRewriteWitness) {
        let sigma = [4, 5, 6, 7];
        let context = BoundedContext {
            slots: [HostEdgeSlot::edge(4, 7, 8), HostEdgeSlot::edge(5, 8, 9)],
        };
        let rules = [
            BoundedRule {
                lhs: pattern([RuleEdgeSlot::edge(1, 0, 1), RuleEdgeSlot::padding()]),
                rhs: pattern([RuleEdgeSlot::edge(2, 0, 1), RuleEdgeSlot::edge(3, 1, 2)]),
            },
            BoundedRule {
                lhs: pattern([RuleEdgeSlot::edge(2, 0, 1), RuleEdgeSlot::edge(3, 1, 2)]),
                rhs: pattern([RuleEdgeSlot::edge(8, 0, 2), RuleEdgeSlot::padding()]),
            },
        ];
        let middle = BoundedGraph {
            slots: [
                context.slots[0],
                context.slots[1],
                HostEdgeSlot::edge(2, 4, 5),
                HostEdgeSlot::edge(3, 5, 6),
            ],
        };
        let first = PrivateGraphRewriteWitness {
            old_graph: BoundedGraph {
                slots: [
                    HostEdgeSlot::edge(1, 4, 5),
                    context.slots[0],
                    HostEdgeSlot::padding(),
                    context.slots[1],
                ],
            },
            new_graph: middle,
            rules,
            sigma,
            context,
            old_blind: [101, 102, 103, 104],
            new_blind: [201, 202, 203, 204],
            rule_blinds: [[301, 302, 303, 304], [401, 402, 403, 404]],
            rule_slot: false,
        };
        let second = PrivateGraphRewriteWitness {
            old_graph: middle,
            new_graph: BoundedGraph {
                slots: [
                    context.slots[0],
                    context.slots[1],
                    HostEdgeSlot::edge(8, 4, 6),
                    HostEdgeSlot::padding(),
                ],
            },
            rules,
            sigma,
            context,
            old_blind: first.new_blind,
            new_blind: [501, 502, 503, 504],
            rule_blinds: first.rule_blinds,
            rule_slot: true,
        };
        (first, second)
    }

    fn receipts() -> [PrivateGraphRewriteReceipt; 2] {
        let (first, second) = two_step_witnesses();
        let (proof0, statement0) = prove_zk(11, 77, 0, &first).expect("first private rewrite");
        let (proof1, statement1) = prove_zk(11, 77, 1, &second).expect("second private rewrite");
        assert_eq!(statement0.ruleset_root, statement1.ruleset_root);
        assert_eq!(statement0.new_root, statement1.old_root);
        [
            PrivateGraphRewriteReceipt::from_proof(&proof0, statement0).unwrap(),
            PrivateGraphRewriteReceipt::from_proof(&proof1, statement1).unwrap(),
        ]
    }

    fn history_for(receipts: &[PrivateGraphRewriteReceipt; 2]) -> PrivateGraphRewriteHistory {
        let first = receipts[0].statement;
        PrivateGraphRewriteHistory::new(PrivateGraphRewriteHead {
            domain: first.domain,
            session: first.session,
            ruleset_root: first.ruleset_root,
            next_index: first.index,
            current_root: first.old_root,
        })
        .unwrap()
    }

    #[test]
    fn two_hiding_reductions_append_as_one_exact_semantic_history() {
        let receipts = receipts();
        let mut history = history_for(&receipts);
        history.append_batch_verified(&receipts).unwrap();
        assert_eq!(history.statements().len(), 2);
        assert_eq!(history.receipts(), &receipts);
        assert_eq!(history.head().next_index, 2);
        assert_eq!(history.head().current_root, receipts[1].statement.new_root);
        history.audit().unwrap();
        assert_eq!(
            PrivateGraphRewriteHistory::verification_key(),
            dregg_circuit_prove::private_graph_rewrite::canonical_vk_hash()
        );
        assert_ne!(
            PrivateGraphRewriteHistory::verification_key(),
            crate::private_graph_rewrite_custom::vk_hash(),
            "standalone receipts must not masquerade as the cell carrier"
        );
    }

    #[test]
    fn warden_history_refuses_a_valid_generic_proof_instead_of_downgrading() {
        let receipts = receipts();
        let first = receipts[0].statement;
        let mut history = PrivateGraphRewriteHistory::new_with_verifier(
            PrivateGraphRewriteHead {
                domain: first.domain,
                session: first.session,
                ruleset_root: first.ruleset_root,
                next_index: first.index,
                current_root: first.old_root,
            },
            PrivateGraphRewriteVerifier::WardenQuestV1,
        )
        .unwrap();
        assert_ne!(
            history.selected_verification_key(),
            PrivateGraphRewriteHistory::verification_key()
        );
        assert!(matches!(
            history.append_verified(receipts[0].clone()),
            Err(PrivateGraphRewriteHistoryError::InvalidProof(_))
        ));
        assert_eq!(history.head().next_index, first.index);
        assert!(history.receipts().is_empty());
    }

    #[test]
    fn receipt_wire_roundtrip_retains_replayable_hiding_evidence() {
        let receipts = receipts();
        let encoded = receipts[0].to_wire().to_postcard().unwrap();
        let decoded = PrivateGraphRewriteWireReceipt::from_postcard(&encoded)
            .unwrap()
            .into_receipt()
            .unwrap();
        assert_eq!(decoded, receipts[0]);

        let mut history = history_for(&receipts);
        history.append_verified(decoded).unwrap();
        history.audit().unwrap();

        let mut wrong_shape = receipts[1].to_wire();
        wrong_shape.public_inputs[3] += 1;
        assert!(matches!(
            wrong_shape.into_receipt(),
            Err(PrivateGraphRewriteHistoryError::InvalidStatement(_))
        ));

        let mut malformed = receipts[1].to_wire().to_postcard().unwrap();
        malformed.truncate(malformed.len() / 2);
        assert!(matches!(
            PrivateGraphRewriteWireReceipt::from_postcard(&malformed),
            Err(PrivateGraphRewriteHistoryError::WireFormat(_))
        ));
    }

    #[test]
    fn durable_snapshot_recomputes_head_and_refuses_forged_history() {
        let receipts = receipts();
        let mut history = history_for(&receipts);
        history.append_batch_verified(&receipts).unwrap();

        let bytes = history.snapshot().to_postcard().unwrap();
        let restored = PrivateGraphRewriteHistorySnapshot::from_postcard(&bytes)
            .unwrap()
            .verify()
            .unwrap();
        assert_eq!(restored.origin(), history.origin());
        assert_eq!(restored.head(), history.head());
        assert_eq!(restored.statements(), history.statements());
        restored.audit().unwrap();

        // A storage attacker cannot swap an endpoint, ruleset, proof, or origin
        // while retaining the cached final head: import has no cached-head field
        // and derives it afresh from the verified proof sequence.
        for mutate in 0..3 {
            let mut snapshot = history.snapshot();
            match mutate {
                0 => snapshot.origin.current_root[0] += 1,
                1 => snapshot.receipts[1].public_inputs[13] += 1,
                2 => {
                    let at = snapshot.receipts[1].proof_bytes.len() / 2;
                    snapshot.receipts[1].proof_bytes[at] ^= 1;
                }
                _ => unreachable!(),
            }
            assert!(snapshot.verify().is_err(), "mutation {mutate} imported");
        }
    }

    #[test]
    fn bad_suffix_or_proof_is_atomic_and_every_history_seam_refuses() {
        let receipts = receipts();
        for mutate in 0..6 {
            let mut attempt = receipts.clone();
            match mutate {
                0 => attempt[1].statement.domain += 1,
                1 => attempt[1].statement.session += 1,
                2 => attempt[1].statement.ruleset_root[0] += 1,
                3 => attempt[1].statement.index += 1,
                4 => attempt[1].statement.old_root[0] += 1,
                5 => {
                    let at = attempt[1].proof_bytes.len() / 2;
                    attempt[1].proof_bytes[at] ^= 1;
                }
                _ => unreachable!(),
            }
            let mut history = history_for(&receipts);
            let before = history.head();
            assert!(history.append_batch_verified(&attempt).is_err());
            assert_eq!(history.head(), before, "mutation {mutate} changed head");
            assert!(
                history.statements().is_empty(),
                "mutation {mutate} logged a prefix"
            );
            assert!(
                history.receipts().is_empty(),
                "mutation {mutate} retained a proof prefix"
            );
            history.audit().unwrap();
        }
    }
}
