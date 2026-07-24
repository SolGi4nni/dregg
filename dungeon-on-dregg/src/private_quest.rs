//! Hidden quest/raid state reduced through the real private graph-rewrite prover.
//!
//! The game state is a four-slot directed labelled graph.  Two preserved context
//! edges bind the party and its still-locked reward; the other two slots carry a
//! hidden quest phase.  A successful raid performs two match-driven replacements:
//!
//! ```text
//! sealed approach  ->  revealed trail + engaged warden  ->  broken seal
//! ```
//!
//! Each move is proved by
//! [`dregg_circuit_prove::private_graph_rewrite::prove_zk`] against the exact
//! Lean-emitted descriptor, then appended through
//! [`dregg_turn_prover::private_graph_rewrite_history::PrivateGraphRewriteHistory`].
//! Public callers receive only the descriptor's roots/bindings and an opaque
//! HidingFri proof.  Graph edges, the injective match, selected rule, and
//! commitment blindings remain owned by [`PrivateQuestRaid`].
//!
//! Honest scope: this is the descriptor's bounded 4-host-slot / 2-pattern-slot,
//! two-rule relation.  It is match-driven replacement, **not full DPO**: it does
//! not claim freshness or dangling-condition machinery.

use dregg_circuit_prove::private_graph_rewrite::{
    BoundedContext, BoundedGraph, BoundedRule, HostEdgeSlot, PrivateGraphRewriteWitness,
    PublicStatement, fresh_blind4, statement,
};
use dregg_circuit_prove::private_quest_graph::{prove_zk, warden_rules};
use dregg_turn_prover::private_graph_rewrite_history::{
    PrivateGraphRewriteHead, PrivateGraphRewriteHistory, PrivateGraphRewriteHistoryError,
    PrivateGraphRewriteHistorySnapshot, PrivateGraphRewriteReceipt, PrivateGraphRewriteVerifier,
    PrivateGraphRewriteWireReceipt,
};

/// Game-domain separator inside the graph-rewrite public statement.
pub const PRIVATE_QUEST_DOMAIN: u32 = 0x51_55_45_53;
/// The exact number of hidden reductions in this bounded quest.
pub const PRIVATE_QUEST_STEPS: u32 = 2;

const LABEL_SEALED_APPROACH: u8 = 1;
const LABEL_REVEALED_TRAIL: u8 = 2;
const LABEL_ENGAGED_WARDEN: u8 = 3;
const LABEL_BROKEN_SEAL: u8 = 8;
const LABEL_PARTY_BOUND: u8 = 12;
const LABEL_REWARD_LOCKED: u8 = 13;

const MATCH: [u8; 4] = [4, 5, 6, 7];

/// A private move submitted to the quest prover.  The move name is not part of
/// the public proof statement: observers learn only that one rule in the pinned
/// two-rule set matched and advanced the committed root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateQuestMove {
    /// Replace the sealed approach with a revealed trail and an engaged warden.
    ScoutVeiledRoute,
    /// Replace the revealed-trail/warden match with the broken-seal state.
    BreakWardenSeal,
}

/// Optimistic-concurrency binding carried by a private quest command.  It makes
/// stale tabs and cross-session/ruleset replays refuse before proof production;
/// the resulting receipt is independently checked again by the real history.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateQuestCommand {
    pub move_: PrivateQuestMove,
    pub session: u32,
    pub ruleset_root: [u32; 8],
    pub index: u32,
    pub old_root: [u32; 8],
}

/// Public, durable quest history.  This wrapper delegates verification,
/// linkage, and head reconstruction to `dregg-turn`; it does not implement a
/// second verifier.
#[derive(Clone, Debug)]
pub struct PrivateQuestPublicHistory {
    history: PrivateGraphRewriteHistory,
}

impl PrivateQuestPublicHistory {
    fn new(origin: PrivateGraphRewriteHead) -> Result<Self, PrivateQuestError> {
        Ok(Self {
            history: PrivateGraphRewriteHistory::new_with_verifier(
                origin,
                PrivateGraphRewriteVerifier::WardenQuestV1,
            )?,
        })
    }

    fn append(&mut self, receipt: PrivateGraphRewriteReceipt) -> Result<(), PrivateQuestError> {
        self.history.append_verified(receipt)?;
        Ok(())
    }

    /// Establish a public quest from its first independently produced receipt.
    /// The receipt selects only randomized public roots: the verifier policy is
    /// fixed here to the Warden descriptor before any attacker-controlled proof
    /// bytes are checked.  This is the consumer-side entry point used by hosted
    /// web/Telegram/Discord sessions whose proof producer owns the hidden graph.
    pub fn begin_verified(receipt: PrivateGraphRewriteReceipt) -> Result<Self, PrivateQuestError> {
        if receipt.statement.domain != PRIVATE_QUEST_DOMAIN {
            return Err(PrivateQuestError::DomainMismatch {
                expected: PRIVATE_QUEST_DOMAIN,
                claimed: receipt.statement.domain,
            });
        }
        if receipt.statement.index != 0 {
            return Err(PrivateQuestError::IndexMismatch {
                expected: 0,
                claimed: receipt.statement.index,
            });
        }
        let mut history = PrivateGraphRewriteHistory::new_with_verifier(
            PrivateGraphRewriteHead {
                domain: receipt.statement.domain,
                session: receipt.statement.session,
                ruleset_root: receipt.statement.ruleset_root,
                next_index: 0,
                current_root: receipt.statement.old_root,
            },
            PrivateGraphRewriteVerifier::WardenQuestV1,
        )?;
        history.append_verified(receipt)?;
        Ok(Self { history })
    }

    /// Append one externally produced opaque receipt under the already pinned
    /// Warden verifier and exact continuation head.
    pub fn append_verified(
        &mut self,
        receipt: PrivateGraphRewriteReceipt,
    ) -> Result<(), PrivateQuestError> {
        if self.receipt_count() >= PRIVATE_QUEST_STEPS as usize {
            return Err(PrivateQuestError::AlreadyComplete);
        }
        self.append(receipt)
    }

    /// Whether both descriptor-pinned reductions have been accepted.
    pub fn is_complete(&self) -> bool {
        self.receipt_count() == PRIVATE_QUEST_STEPS as usize
    }

    /// The only live quest state disclosed publicly: chain identity, next index,
    /// and current commitment root.
    pub const fn head(&self) -> PrivateGraphRewriteHead {
        self.history.head()
    }

    /// Number of opaque, verified reduction receipts retained for replay.
    pub fn receipt_count(&self) -> usize {
        self.history.receipts().len()
    }

    /// Root-only public statements, one per verified reduction.
    pub fn statements(&self) -> &[PublicStatement] {
        self.history.statements()
    }

    /// Persist the immutable origin plus opaque proof receipts.  No cached final
    /// head is serialized; import derives it again from verified evidence.
    pub fn to_postcard(&self) -> Result<Vec<u8>, PrivateQuestError> {
        self.history.snapshot().to_postcard().map_err(Into::into)
    }

    /// Restore and cryptographically replay a persisted public quest history.
    pub fn from_postcard(bytes: &[u8]) -> Result<Self, PrivateQuestError> {
        let snapshot = PrivateGraphRewriteHistorySnapshot::from_postcard(bytes)?;
        Ok(Self {
            history: snapshot.verify()?,
        })
    }

    /// Recheck the retained receipt log from its immutable origin.
    pub fn audit(&self) -> Result<(), PrivateQuestError> {
        self.history.audit().map_err(Into::into)
    }

    /// Identity of the standalone base-receipt verifier.  This is intentionally
    /// not advertised as an `Effect::Custom` cell-transition VK.
    pub fn verification_key() -> [u8; 32] {
        dregg_circuit_prove::private_quest_graph::canonical_vk_hash()
    }
}

/// Canonical opaque receipt bytes shared by every hosted frontend.
pub fn encode_private_quest_receipt(
    receipt: &PrivateGraphRewriteReceipt,
) -> Result<Vec<u8>, PrivateQuestError> {
    receipt.to_wire().to_postcard().map_err(Into::into)
}

/// Decode the stable 29-public-input wire form and reject alternate postcard
/// encodings before the pinned quest verifier sees it.
pub fn decode_private_quest_receipt(
    bytes: &[u8],
) -> Result<PrivateGraphRewriteReceipt, PrivateQuestError> {
    let wire = PrivateGraphRewriteWireReceipt::from_postcard(bytes)?;
    let canonical = wire.to_postcard()?;
    if canonical != bytes {
        return Err(PrivateQuestError::NonCanonicalWire);
    }
    wire.into_receipt().map_err(Into::into)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HiddenPhase {
    Sealed,
    WardenEngaged,
    Cleared,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct HiddenQuestState {
    phase: HiddenPhase,
    graph: BoundedGraph,
    graph_blind: [u32; 4],
    rules: [BoundedRule; 2],
    rule_blinds: [[u32; 4]; 2],
    context: BoundedContext,
}

impl HiddenQuestState {
    fn fresh() -> Result<Self, PrivateQuestError> {
        let context = BoundedContext {
            slots: [
                HostEdgeSlot::edge(LABEL_PARTY_BOUND, MATCH[3], 8),
                HostEdgeSlot::edge(LABEL_REWARD_LOCKED, 8, 9),
            ],
        };
        let rules = warden_rules();
        Ok(Self {
            phase: HiddenPhase::Sealed,
            // Intentionally noncanonical slot order: the descriptor must derive
            // a real match/permutation, not treat replacement as positional.
            graph: BoundedGraph {
                slots: [
                    HostEdgeSlot::edge(LABEL_SEALED_APPROACH, MATCH[0], MATCH[1]),
                    context.slots[0],
                    HostEdgeSlot::padding(),
                    context.slots[1],
                ],
            },
            graph_blind: fresh_blind4().map_err(PrivateQuestError::Prover)?,
            rules,
            rule_blinds: [
                fresh_blind4().map_err(PrivateQuestError::Prover)?,
                fresh_blind4().map_err(PrivateQuestError::Prover)?,
            ],
            context,
        })
    }

    fn expected_move(&self) -> Option<PrivateQuestMove> {
        match self.phase {
            HiddenPhase::Sealed => Some(PrivateQuestMove::ScoutVeiledRoute),
            HiddenPhase::WardenEngaged => Some(PrivateQuestMove::BreakWardenSeal),
            HiddenPhase::Cleared => None,
        }
    }

    fn next_graph(&self, move_: PrivateQuestMove) -> BoundedGraph {
        match move_ {
            PrivateQuestMove::ScoutVeiledRoute => BoundedGraph {
                slots: [
                    self.context.slots[0],
                    self.context.slots[1],
                    HostEdgeSlot::edge(LABEL_REVEALED_TRAIL, MATCH[0], MATCH[1]),
                    HostEdgeSlot::edge(LABEL_ENGAGED_WARDEN, MATCH[1], MATCH[2]),
                ],
            },
            PrivateQuestMove::BreakWardenSeal => BoundedGraph {
                slots: [
                    self.context.slots[0],
                    self.context.slots[1],
                    HostEdgeSlot::edge(LABEL_BROKEN_SEAL, MATCH[0], MATCH[2]),
                    HostEdgeSlot::padding(),
                ],
            },
        }
    }

    fn witness(
        &self,
        move_: PrivateQuestMove,
        new_graph: BoundedGraph,
        new_blind: [u32; 4],
    ) -> PrivateGraphRewriteWitness {
        PrivateGraphRewriteWitness {
            old_graph: self.graph,
            new_graph,
            rules: self.rules,
            sigma: MATCH,
            context: self.context,
            old_blind: self.graph_blind,
            new_blind,
            rule_blinds: self.rule_blinds,
            rule_slot: matches!(move_, PrivateQuestMove::BreakWardenSeal),
        }
    }

    fn commit(&mut self, move_: PrivateQuestMove, graph: BoundedGraph, blind: [u32; 4]) {
        self.phase = match move_ {
            PrivateQuestMove::ScoutVeiledRoute => HiddenPhase::WardenEngaged,
            PrivateQuestMove::BreakWardenSeal => HiddenPhase::Cleared,
        };
        self.graph = graph;
        self.graph_blind = blind;
    }
}

/// The executable private quest engine.  Secret graph material is never
/// returned; public durability lives in [`PrivateQuestPublicHistory`].
pub struct PrivateQuestRaid {
    session: u32,
    hidden: HiddenQuestState,
    public: PrivateQuestPublicHistory,
}

// Do not let a convenience formatter disclose the hidden graph, match, selected
// rule, or blindings.  Debug output is the same root-only view an observer has.
impl std::fmt::Debug for PrivateQuestRaid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateQuestRaid")
            .field("public_head", &self.public.head())
            .field("receipt_count", &self.public.receipt_count())
            .field("complete", &self.is_complete())
            .finish_non_exhaustive()
    }
}

impl PrivateQuestRaid {
    /// Start a fresh hidden raid in `session`.  The public origin commits to the
    /// initial hidden graph and the complete blinded two-rule set.
    pub fn new(session: u32) -> Result<Self, PrivateQuestError> {
        let hidden = HiddenQuestState::fresh()?;
        // The scratch new blind affects only a discarded preview endpoint; the
        // origin needs the statement's old root and ruleset root.  Real moves
        // always draw a fresh hiding blind below.
        let preview_graph = hidden.next_graph(PrivateQuestMove::ScoutVeiledRoute);
        let preview = hidden.witness(
            PrivateQuestMove::ScoutVeiledRoute,
            preview_graph,
            [1, 2, 3, 4],
        );
        let first = statement(PRIVATE_QUEST_DOMAIN, session, 0, &preview)
            .map_err(PrivateQuestError::Prover)?;
        let public = PrivateQuestPublicHistory::new(PrivateGraphRewriteHead {
            domain: first.domain,
            session: first.session,
            ruleset_root: first.ruleset_root,
            next_index: first.index,
            current_root: first.old_root,
        })?;
        Ok(Self {
            session,
            hidden,
            public,
        })
    }

    /// Root-only public view of the current quest continuation point.
    pub const fn public_head(&self) -> PrivateGraphRewriteHead {
        self.public.head()
    }

    pub const fn public_history(&self) -> &PrivateQuestPublicHistory {
        &self.public
    }

    /// Bind a private move to the exact public continuation it was prepared for.
    pub fn command(&self, move_: PrivateQuestMove) -> PrivateQuestCommand {
        let head = self.public.head();
        PrivateQuestCommand {
            move_,
            session: head.session,
            ruleset_root: head.ruleset_root,
            index: head.next_index,
            old_root: head.current_root,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.hidden.phase == HiddenPhase::Cleared
    }

    /// Prove and atomically land one hidden quest reduction.  Every cheap
    /// binding/phase refusal occurs before fresh randomness or proof production.
    /// The hidden graph mutates only after the real history accepts the proof.
    pub fn advance(
        &mut self,
        command: PrivateQuestCommand,
    ) -> Result<PrivateGraphRewriteReceipt, PrivateQuestError> {
        let head = self.public.head();
        validate_binding(head, command)?;
        let Some(expected) = self.hidden.expected_move() else {
            return Err(PrivateQuestError::AlreadyComplete);
        };
        if command.move_ != expected {
            return Err(PrivateQuestError::WrongMove {
                expected,
                attempted: command.move_,
            });
        }

        let new_graph = self.hidden.next_graph(command.move_);
        let new_blind = fresh_blind4().map_err(PrivateQuestError::Prover)?;
        let witness = self.hidden.witness(command.move_, new_graph, new_blind);
        let (proof, public) = prove_zk(
            PRIVATE_QUEST_DOMAIN,
            self.session,
            head.next_index,
            &witness,
        )
        .map_err(PrivateQuestError::Prover)?;
        let receipt = PrivateGraphRewriteReceipt::from_quest_proof(&proof, public)?;

        // append_verified checks the proof plus domain/session/ruleset/index/root
        // seams.  Only after it succeeds does the secret state advance.
        self.public.append(receipt.clone())?;
        self.hidden.commit(command.move_, new_graph, new_blind);
        Ok(receipt)
    }
}

fn validate_binding(
    head: PrivateGraphRewriteHead,
    command: PrivateQuestCommand,
) -> Result<(), PrivateQuestError> {
    if command.session != head.session {
        return Err(PrivateQuestError::SessionMismatch {
            expected: head.session,
            claimed: command.session,
        });
    }
    if command.ruleset_root != head.ruleset_root {
        return Err(PrivateQuestError::RulesetMismatch);
    }
    if command.index != head.next_index {
        return Err(PrivateQuestError::IndexMismatch {
            expected: head.next_index,
            claimed: command.index,
        });
    }
    if command.old_root != head.current_root {
        return Err(PrivateQuestError::OldRootMismatch);
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateQuestError {
    AlreadyComplete,
    DomainMismatch {
        expected: u32,
        claimed: u32,
    },
    NonCanonicalWire,
    WrongMove {
        expected: PrivateQuestMove,
        attempted: PrivateQuestMove,
    },
    SessionMismatch {
        expected: u32,
        claimed: u32,
    },
    RulesetMismatch,
    IndexMismatch {
        expected: u32,
        claimed: u32,
    },
    OldRootMismatch,
    Prover(String),
    History(PrivateGraphRewriteHistoryError),
}

impl From<PrivateGraphRewriteHistoryError> for PrivateQuestError {
    fn from(error: PrivateGraphRewriteHistoryError) -> Self {
        Self::History(error)
    }
}

impl std::fmt::Display for PrivateQuestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyComplete => write!(f, "private quest is already complete"),
            Self::DomainMismatch { expected, claimed } => write!(
                f,
                "private quest domain mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::NonCanonicalWire => {
                write!(f, "private quest receipt is not canonically encoded")
            }
            Self::WrongMove {
                expected,
                attempted,
            } => write!(
                f,
                "private quest move {attempted:?} refused; expected {expected:?}"
            ),
            Self::SessionMismatch { expected, claimed } => write!(
                f,
                "private quest session mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::RulesetMismatch => write!(f, "private quest ruleset root mismatch"),
            Self::IndexMismatch { expected, claimed } => write!(
                f,
                "private quest index mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::OldRootMismatch => write!(f, "private quest old root mismatch"),
            Self::Prover(reason) => write!(f, "private quest proof refused: {reason}"),
            Self::History(error) => write!(f, "private quest history refused: {error}"),
        }
    }
}

impl std::error::Error for PrivateQuestError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_quest_two_step_reduction_persists_root_only_history() {
        let mut raid = PrivateQuestRaid::new(77).unwrap();
        let origin = raid.public_head();
        assert_eq!(origin.domain, PRIVATE_QUEST_DOMAIN);
        assert_eq!(origin.session, 77);
        assert_eq!(origin.next_index, 0);
        assert_eq!(raid.public_history().receipt_count(), 0);
        let debug = format!("{raid:?}");
        assert!(debug.contains("public_head"));
        assert!(!debug.contains("graph_blind"));
        assert!(!debug.contains("rule_blinds"));

        let first = raid
            .advance(raid.command(PrivateQuestMove::ScoutVeiledRoute))
            .unwrap();
        assert_eq!(first.statement.session, origin.session);
        assert_eq!(first.statement.ruleset_root, origin.ruleset_root);
        assert_eq!(first.statement.index, 0);
        assert_eq!(first.statement.old_root, origin.current_root);
        assert!(!first.proof_bytes().is_empty());

        let middle = raid.public_head();
        assert_eq!(middle.next_index, 1);
        assert_eq!(middle.current_root, first.statement.new_root);
        let second = raid
            .advance(raid.command(PrivateQuestMove::BreakWardenSeal))
            .unwrap();
        assert_eq!(second.statement.session, origin.session);
        assert_eq!(second.statement.ruleset_root, origin.ruleset_root);
        assert_eq!(second.statement.index, 1);
        assert_eq!(second.statement.old_root, first.statement.new_root);

        let final_head = raid.public_head();
        assert_eq!(final_head.next_index, PRIVATE_QUEST_STEPS);
        assert_eq!(final_head.current_root, second.statement.new_root);
        assert!(raid.is_complete());
        assert_eq!(raid.public_history().receipt_count(), 2);

        // Persistence carries only origin + public statements + opaque proofs.
        // Import recomputes the endpoint by replaying both real proofs.
        let bytes = raid.public_history().to_postcard().unwrap();
        let restored = PrivateQuestPublicHistory::from_postcard(&bytes).unwrap();
        assert_eq!(restored.head(), final_head);
        assert_eq!(restored.statements(), raid.public_history().statements());
        assert_eq!(restored.receipt_count(), 2);
    }

    #[test]
    fn private_quest_binding_and_order_refusals_mutate_nothing() {
        let mut raid = PrivateQuestRaid::new(91).unwrap();

        let attempts = {
            let valid = raid.command(PrivateQuestMove::ScoutVeiledRoute);
            let mut wrong_session = valid;
            wrong_session.session += 1;
            let mut wrong_ruleset = valid;
            wrong_ruleset.ruleset_root[0] ^= 1;
            let mut wrong_index = valid;
            wrong_index.index += 1;
            let mut wrong_root = valid;
            wrong_root.old_root[0] ^= 1;
            [
                (
                    raid.command(PrivateQuestMove::BreakWardenSeal),
                    "wrong move",
                ),
                (wrong_session, "wrong session"),
                (wrong_ruleset, "wrong ruleset"),
                (wrong_index, "wrong index"),
                (wrong_root, "wrong root"),
            ]
        };

        for (command, label) in attempts {
            let before_head = raid.public_head();
            let before_bytes = raid.public_history().to_postcard().unwrap();
            let before_hidden = raid.hidden.clone();
            assert!(raid.advance(command).is_err(), "{label} landed");
            assert_eq!(raid.public_head(), before_head, "{label} changed head");
            assert_eq!(
                raid.public_history().to_postcard().unwrap(),
                before_bytes,
                "{label} changed durable history"
            );
            assert_eq!(raid.hidden, before_hidden, "{label} changed hidden state");
        }
    }

    #[test]
    fn private_quest_completed_and_forged_persistence_refuse_without_mutation() {
        let mut raid = PrivateQuestRaid::new(123).unwrap();
        raid.advance(raid.command(PrivateQuestMove::ScoutVeiledRoute))
            .unwrap();
        raid.advance(raid.command(PrivateQuestMove::BreakWardenSeal))
            .unwrap();

        let before_head = raid.public_head();
        let before_bytes = raid.public_history().to_postcard().unwrap();
        let before_hidden = raid.hidden.clone();
        assert!(matches!(
            raid.advance(raid.command(PrivateQuestMove::BreakWardenSeal)),
            Err(PrivateQuestError::AlreadyComplete)
        ));
        assert_eq!(raid.public_head(), before_head);
        assert_eq!(raid.public_history().to_postcard().unwrap(), before_bytes);
        assert_eq!(raid.hidden, before_hidden);

        // A persisted endpoint cannot be rewritten independently of the proof
        // chain: there is no cached-head field, and a changed receipt seam fails.
        let mut forged = raid.public.history.snapshot();
        forged.receipts[1].public_inputs[4] += 1;
        let forged_bytes = forged.to_postcard().unwrap();
        assert!(PrivateQuestPublicHistory::from_postcard(&forged_bytes).is_err());
        assert_eq!(raid.public_head(), before_head);
        assert_eq!(raid.public_history().to_postcard().unwrap(), before_bytes);
    }
}
