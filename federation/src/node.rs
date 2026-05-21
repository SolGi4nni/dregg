//! Federation node implementation.
//!
//! A federation node is a process that:
//! - Holds an authority keypair
//! - Maintains a local revocation accumulator (Merkle tree of revoked token IDs)
//! - Participates in Morpheus consensus to agree on the current revocation root
//! - Exposes an API for: `revoke(token_id)`, `get_attested_root()`,
//!   `verify_non_membership(token_id)`
//!
//! Each node maintains its own copy of the revocation tree. After consensus
//! finalizes a block of revocations, all nodes apply the same set of
//! revocations to their local trees, ensuring they converge on the same root.

use crate::consensus::{ConsensusConfig, ConsensusOrchestrator, ConsensusState, PendingStateRoots};
use crate::revocation::{RevocationTree, RevocationVerifier};
use crate::types::*;

// =============================================================================
// Federation Node
// =============================================================================

/// A single federation node that participates in revocation consensus.
#[derive(Clone)]
pub struct FederationNode {
    /// The node's identity.
    pub identity: NodeIdentity,
    /// The node's signing key.
    pub signing_key: SigningKey,
    /// The local revocation tree (Merkle tree of revoked token IDs).
    pub revocation_tree: RevocationTree,
    /// The latest attested root (after consensus finalization).
    pub attested_root: Option<AttestedRoot>,
    /// Tokens minted by this node.
    pub minted_tokens: Vec<Token>,
    /// Whether this node is online.
    pub is_online: bool,
}

impl FederationNode {
    /// Create a new federation node.
    pub fn new(name: &str, id: usize) -> Self {
        let (signing_key, public_key) = generate_keypair();

        Self {
            identity: NodeIdentity {
                name: name.to_string(),
                id,
                public_key,
            },
            signing_key,
            revocation_tree: RevocationTree::new(),
            attested_root: None,
            minted_tokens: Vec::new(),
            is_online: true,
        }
    }

    /// Mint a new token.
    pub fn mint_token(&mut self, holder: &str) -> Token {
        let mut id_bytes = [0u8; 16];
        getrandom::fill(&mut id_bytes).expect("getrandom failed");
        let token_id = hex_encode(&id_bytes[..8]);

        let sig_message = format!("mint:{}", token_id);
        let signature = sign(&self.signing_key, sig_message.as_bytes());

        let token = Token {
            id: token_id,
            holder: holder.to_string(),
            issuer_id: self.identity.id,
            issuer_key: self.identity.public_key.clone(),
            signature,
        };

        self.minted_tokens.push(token.clone());
        token
    }

    /// Create a revocation event (to be submitted to consensus).
    pub fn create_revocation_event(&self, token_id: &str) -> RevocationEvent {
        let revoke_message = format!("revoke:{}", token_id);
        let signature = sign(&self.signing_key, revoke_message.as_bytes());

        RevocationEvent {
            token_id: token_id.to_string(),
            authority_id: self.identity.id,
            signature,
        }
    }

    /// Apply a finalized block of revocations to the local tree.
    pub fn apply_finalized_block(&mut self, block: &RevocationBlock) {
        let token_ids: Vec<String> = block.events.iter().map(|e| e.token_id.clone()).collect();
        self.revocation_tree.revoke_batch(&token_ids);
    }

    /// Compute the current state root (revocation tree Merkle root).
    /// This is the pre-state root before any new events are applied.
    pub fn compute_state_root(&mut self) -> [u8; 32] {
        self.revocation_tree.root()
    }

    /// Update the attested root after consensus finalization.
    pub fn update_attested_root(&mut self, qc: &QuorumCertificate, nodes: &[NodeIdentity]) {
        let merkle_root = self.revocation_tree.root();
        let timestamp = current_timestamp();

        let quorum_signatures = qc.quorum_signatures(nodes);

        self.attested_root = Some(AttestedRoot {
            merkle_root,
            note_tree_root: None,
            nullifier_set_root: None,
            height: qc.height,
            timestamp,
            threshold_qc: qc
                .aggregate_qc
                .as_ref()
                .map(|q| pyana_types::ThresholdQC(q.to_bytes())),
            quorum_signatures,
            threshold: qc.threshold,
        });
    }

    /// Get the current attested root.
    pub fn get_attested_root(&self) -> Option<&AttestedRoot> {
        self.attested_root.as_ref()
    }

    /// Verify that a token is NOT revoked (produces a non-membership proof).
    pub fn verify_non_membership(&self, token_id: &str) -> Option<RevocationProof> {
        let attested_root = self.attested_root.as_ref()?;
        RevocationVerifier::build_proof(&self.revocation_tree, attested_root, token_id)
    }

    /// Check if a token is in the local revocation set.
    pub fn is_revoked(&self, token_id: &str) -> bool {
        self.revocation_tree.is_revoked(token_id)
    }

    /// Get the current Merkle root of the revocation tree.
    pub fn current_root(&mut self) -> [u8; 32] {
        self.revocation_tree.root()
    }

    /// Set the node's online status.
    pub fn set_online(&mut self, online: bool) {
        self.is_online = online;
    }
}

// =============================================================================
// Federation
// =============================================================================

/// A federation of multiple nodes participating in revocation consensus.
pub struct Federation {
    /// The federation nodes.
    pub nodes: Vec<FederationNode>,
    /// Consensus states for each node.
    pub consensus_states: Vec<ConsensusState>,
    /// The consensus orchestrator.
    pub orchestrator: ConsensusOrchestrator,
    /// The consensus configuration.
    pub config: ConsensusConfig,
    /// History of all finalized blocks.
    pub finalized_history: Vec<(RevocationBlock, QuorumCertificate)>,
}

impl Federation {
    /// Create a new federation with the given node names.
    pub fn new(names: &[&str]) -> Self {
        let n = names.len();
        let config = ConsensusConfig::new(n);

        let nodes: Vec<FederationNode> = names
            .iter()
            .enumerate()
            .map(|(i, name)| FederationNode::new(name, i))
            .collect();

        let consensus_states: Vec<ConsensusState> = nodes
            .iter()
            .map(|node| {
                ConsensusState::new(node.identity.id, node.signing_key.clone(), config.clone())
            })
            .collect();

        let orchestrator = ConsensusOrchestrator::new(config.clone());

        Self {
            nodes,
            consensus_states,
            orchestrator,
            config,
            finalized_history: Vec::new(),
        }
    }

    /// Get the node identities for QC signature resolution.
    pub fn node_identities(&self) -> Vec<NodeIdentity> {
        self.nodes.iter().map(|n| n.identity.clone()).collect()
    }

    /// Submit a revocation event from a specific node.
    pub fn submit_revocation(&mut self, from_node: usize, token_id: &str) {
        let event = self.nodes[from_node].create_revocation_event(token_id);
        // Submit to the node's consensus state.
        self.consensus_states[from_node].submit_revocation(event);
    }

    /// Run a consensus round and apply the result to all nodes.
    /// Returns the finalized block and QC, or None if consensus failed.
    pub fn run_consensus_round(&mut self) -> Option<(RevocationBlock, QuorumCertificate)> {
        // Sync online status and local state roots for divergence detection.
        for (i, node) in self.nodes.iter_mut().enumerate() {
            if i < self.consensus_states.len() {
                self.consensus_states[i].set_online(node.is_online);
                // Update the consensus state's local_state_root from the node's
                // revocation tree. This enables divergence detection in validate_block().
                let root = node.compute_state_root();
                self.consensus_states[i].set_local_state_root(root);
            }
        }

        // Run the consensus round.
        let result = self.orchestrator.run_round(&mut self.consensus_states)?;
        let (block, qc) = result;

        // Apply the finalized block to all online nodes.
        let identities = self.node_identities();
        for node in &mut self.nodes {
            if node.is_online {
                node.apply_finalized_block(&block);
                node.update_attested_root(&qc, &identities);
            }
        }

        // Keep Federation.config in sync if the orchestrator applied a reconfig.
        if self.config.epoch != self.orchestrator.config.epoch {
            self.config = self.orchestrator.config.clone();
        }

        self.finalized_history.push((block.clone(), qc.clone()));
        Some((block, qc))
    }

    /// Run a consensus round with state root commitments.
    ///
    /// This variant computes pre/post state roots for the proposing node,
    /// enabling divergence detection and light client verification.
    pub fn run_consensus_round_with_state_roots(
        &mut self,
    ) -> Option<(RevocationBlock, QuorumCertificate, LightClientProof)> {
        // Sync online status and local state roots for divergence detection.
        for (i, node) in self.nodes.iter_mut().enumerate() {
            if i < self.consensus_states.len() {
                self.consensus_states[i].set_online(node.is_online);
                let root = node.compute_state_root();
                self.consensus_states[i].set_local_state_root(root);
            }
        }

        // Determine leader and compute pre_state_root from the leader's tree.
        let view = self.consensus_states.iter().find(|s| s.is_online)?.current_view;
        let leader_id = self.config.leader_for_view(view);
        if leader_id >= self.nodes.len() || !self.nodes[leader_id].is_online {
            // Fall back to standard round if leader identification fails.
            return self
                .run_consensus_round()
                .map(|(b, qc)| {
                    let proof = LightClientProof::from_block(&b, &qc);
                    (b, qc, proof)
                });
        }

        let pre_state_root = self.nodes[leader_id].compute_state_root();

        // Simulate what events will be included: gather all pending events
        // and apply them to a clone of the leader's tree to get post_state_root.
        let pending_events: Vec<RevocationEvent> = self
            .consensus_states
            .iter()
            .filter(|s| s.is_online)
            .flat_map(|s| s.pending_events.clone())
            .collect();

        let mut tree_clone = self.nodes[leader_id].revocation_tree.clone();
        let token_ids: Vec<String> = pending_events.iter().map(|e| e.token_id.clone()).collect();
        tree_clone.revoke_batch(&token_ids);
        let post_state_root = tree_clone.root();

        // Note tree and nullifier set roots are not managed by the federation
        // revocation tree directly -- they come from the store layer. For now,
        // we use zero roots (the node crate can override these when it has store access).
        let note_tree_root = [0u8; 32];
        let nullifier_set_root = [0u8; 32];

        // Inject state roots into the leader's consensus state for proposal creation.
        // We do this by temporarily overriding the create_proposal path.
        // Actually, we need to use the orchestrator which calls create_proposal internally.
        // The cleanest approach: set state roots on the consensus state, then let
        // run_round use them. Let's add support for that.

        // Store the state roots on the leader's consensus state for the orchestrator.
        self.consensus_states[leader_id].pending_state_roots = Some(PendingStateRoots {
            pre_state_root,
            post_state_root,
            note_tree_root,
            nullifier_set_root,
        });

        // Run the consensus round.
        let result = self.orchestrator.run_round(&mut self.consensus_states)?;
        let (block, qc) = result;

        // Apply the finalized block to all online nodes.
        let identities = self.node_identities();
        for node in &mut self.nodes {
            if node.is_online {
                node.apply_finalized_block(&block);
                node.update_attested_root(&qc, &identities);
            }
        }

        // Keep Federation.config in sync if the orchestrator applied a reconfig.
        if self.config.epoch != self.orchestrator.config.epoch {
            self.config = self.orchestrator.config.clone();
        }

        let proof = LightClientProof::from_block(&block, &qc);
        self.finalized_history.push((block.clone(), qc.clone()));
        Some((block, qc, proof))
    }

    /// Mint a token at a specific node.
    pub fn mint_token(&mut self, node_id: usize, holder: &str) -> Token {
        self.nodes[node_id].mint_token(holder)
    }

    /// Crash a node (take it offline for Byzantine fault simulation).
    pub fn crash_node(&mut self, node_id: usize) {
        self.nodes[node_id].set_online(false);
        self.consensus_states[node_id].set_online(false);
    }

    /// Recover a crashed node.
    pub fn recover_node(&mut self, node_id: usize) {
        self.nodes[node_id].set_online(true);
        self.consensus_states[node_id].set_online(true);
    }

    /// Get the number of online nodes.
    pub fn online_count(&self) -> usize {
        self.nodes.iter().filter(|n| n.is_online).count()
    }

    /// Verify a token's non-revocation from a specific node's perspective.
    pub fn verify_non_membership_from(
        &self,
        verifier_node: usize,
        token_id: &str,
    ) -> Option<RevocationProof> {
        self.nodes[verifier_node].verify_non_membership(token_id)
    }

    /// Check if all online nodes agree on the same root.
    pub fn roots_agree(&mut self) -> bool {
        let mut roots: Vec<[u8; 32]> = Vec::new();
        for node in &mut self.nodes {
            if node.is_online {
                roots.push(node.current_root());
            }
        }
        if roots.is_empty() {
            return true;
        }
        roots.windows(2).all(|w| w[0] == w[1])
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::revocation::RevocationVerifier;

    #[test]
    fn create_federation() {
        let fed = Federation::new(&["alpha", "beta", "gamma", "delta"]);
        assert_eq!(fed.nodes.len(), 4);
        assert_eq!(fed.config.threshold, 3);
        assert_eq!(fed.config.max_faults, 1);
    }

    #[test]
    fn mint_tokens() {
        let mut fed = Federation::new(&["a", "b", "c", "d"]);
        let t1 = fed.mint_token(0, "Alice");
        let t2 = fed.mint_token(1, "Bob");
        assert_ne!(t1.id, t2.id);
        assert_eq!(t1.issuer_id, 0);
        assert_eq!(t2.issuer_id, 1);
    }

    #[test]
    fn revocation_consensus() {
        let mut fed = Federation::new(&["a", "b", "c", "d"]);
        let t1 = fed.mint_token(0, "Alice");

        // Submit revocation.
        fed.submit_revocation(0, &t1.id);

        // Run consensus.
        let result = fed.run_consensus_round();
        assert!(result.is_some());

        let (block, qc) = result.unwrap();
        assert_eq!(block.events.len(), 1);
        assert_eq!(block.events[0].token_id, t1.id);
        assert!(qc.is_valid());

        // All nodes should agree on the root.
        assert!(fed.roots_agree());

        // Token should be revoked on all nodes.
        for node in &fed.nodes {
            assert!(node.is_revoked(&t1.id));
        }
    }

    #[test]
    fn non_membership_proof_after_revocation() {
        let mut fed = Federation::new(&["a", "b", "c", "d"]);
        let t1 = fed.mint_token(0, "Alice");
        let t2 = fed.mint_token(1, "Bob");

        // Revoke t1.
        fed.submit_revocation(0, &t1.id);
        fed.run_consensus_round();

        // t2 should have a valid non-membership proof.
        let proof = fed.verify_non_membership_from(2, &t2.id);
        assert!(proof.is_some());

        let proof = proof.unwrap();
        let verification = RevocationVerifier::verify(&proof);
        assert!(verification.valid);

        // t1 should NOT have a non-membership proof (it's revoked).
        let no_proof = fed.verify_non_membership_from(2, &t1.id);
        assert!(no_proof.is_none());
    }

    #[test]
    fn byzantine_fault_tolerance() {
        let mut fed = Federation::new(&["a", "b", "c", "d"]);
        let t1 = fed.mint_token(0, "Alice");

        // Crash one node.
        fed.crash_node(3);

        // Submit revocation.
        fed.submit_revocation(0, &t1.id);

        // Should still reach consensus.
        let result = fed.run_consensus_round();
        assert!(result.is_some());

        // Online nodes should agree.
        let mut online_roots: Vec<[u8; 32]> = Vec::new();
        for node in &mut fed.nodes {
            if node.is_online {
                online_roots.push(node.current_root());
            }
        }
        assert_eq!(online_roots.len(), 3);
        assert!(online_roots.windows(2).all(|w| w[0] == w[1]));
    }
}
