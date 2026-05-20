//! Intent gossip: propagation and local pool management.
//!
//! Intents propagate through the gossip network (Plumtree lazy-push) so that
//! all connected wallets can attempt local matching. The IntentPool manages
//! the set of known intents with expiry-based garbage collection.
//!
//! # Privacy properties
//!
//! - Intents themselves are PUBLIC: everyone sees "someone needs X"
//! - The creator is anonymous (CommitmentId, not an identity)
//! - Matches are PRIVATE: never broadcast, sent directly to the creator

use std::collections::HashMap;

use crate::{CommitmentId, Intent, IntentKind, Match, MatchSpec};
use crate::matcher::{HeldCapability, MatchResult, match_intent};

/// Configuration for the intent pool.
#[derive(Clone, Debug)]
pub struct IntentPoolConfig {
    /// Maximum number of intents to hold in the pool.
    pub max_intents: usize,
    /// How often to run garbage collection (seconds).
    pub gc_interval_secs: u64,
    /// Whether to automatically match incoming intents against held tokens.
    pub auto_match: bool,
}

impl Default for IntentPoolConfig {
    fn default() -> Self {
        Self {
            max_intents: 10_000,
            gc_interval_secs: 60,
            auto_match: true,
        }
    }
}

/// Policy for auto-fulfillment when a match is found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AutoFulfillPolicy {
    /// Never auto-fulfill; always ask the user.
    Never,
    /// Auto-fulfill for intents matching these resource patterns.
    ForPatterns(Vec<String>),
    /// Auto-fulfill everything (dangerous, but useful for automated agents).
    Always,
}

/// Callback type for match notifications.
pub type MatchCallback = Box<dyn Fn(&Intent, &Match) + Send + Sync>;

/// The local pool of known intents (like a mempool for capabilities).
///
/// Stores active intents, performs garbage collection on expired ones,
/// and triggers local matching when new intents arrive.
pub struct IntentPool {
    /// Active intents indexed by their content-addressed ID.
    intents: HashMap<[u8; 32], Intent>,
    /// Our wallet's held capabilities (for matching).
    held_tokens: Vec<HeldCapability>,
    /// Our anonymous commitment identity.
    our_commitment: CommitmentId,
    /// Pool configuration.
    config: IntentPoolConfig,
    /// Auto-fulfillment policy.
    auto_fulfill: AutoFulfillPolicy,
    /// Pending matches waiting for user approval or auto-fulfillment.
    pending_matches: Vec<(Intent, Match)>,
    /// Intents we have broadcast (to avoid re-matching our own).
    our_intent_ids: Vec<[u8; 32]>,
}

impl IntentPool {
    /// Create a new intent pool.
    pub fn new(
        our_commitment: CommitmentId,
        config: IntentPoolConfig,
        auto_fulfill: AutoFulfillPolicy,
    ) -> Self {
        Self {
            intents: HashMap::new(),
            held_tokens: Vec::new(),
            our_commitment,
            config,
            auto_fulfill,
            pending_matches: Vec::new(),
            our_intent_ids: Vec::new(),
        }
    }

    /// Update the wallet's held capabilities (call when tokens change).
    pub fn update_held_tokens(&mut self, tokens: Vec<HeldCapability>) {
        self.held_tokens = tokens;
    }

    /// Broadcast a new intent from this wallet.
    ///
    /// Returns the intent (with computed ID) ready for gossip propagation.
    pub fn broadcast_intent(
        &mut self,
        kind: IntentKind,
        matcher: MatchSpec,
        expiry: u64,
        proof_of_stake: Option<pyana_cell::NoteCommitment>,
    ) -> Intent {
        let intent = Intent::new(kind, matcher, self.our_commitment, expiry, proof_of_stake);
        self.our_intent_ids.push(intent.id);
        self.intents.insert(intent.id, intent.clone());
        intent
    }

    /// Receive an intent from the gossip network.
    ///
    /// Adds it to the pool and (if auto_match is enabled) triggers local matching.
    /// Returns any match found.
    pub fn receive_intent(&mut self, intent: Intent, now: u64) -> Option<Match> {
        // Don't process expired intents
        if intent.is_expired(now) {
            return None;
        }

        // Don't match our own intents
        if self.our_intent_ids.contains(&intent.id) {
            return None;
        }

        // Don't process duplicates
        if self.intents.contains_key(&intent.id) {
            return None;
        }

        // Enforce pool size limit (drop oldest if full)
        if self.intents.len() >= self.config.max_intents {
            self.gc(now);
            // If still full after GC, drop the oldest
            if self.intents.len() >= self.config.max_intents {
                if let Some(oldest_id) = self.find_oldest_intent() {
                    self.intents.remove(&oldest_id);
                }
            }
        }

        // Store the intent
        self.intents.insert(intent.id, intent.clone());

        // Auto-match if enabled
        if self.config.auto_match {
            let result = match_intent(
                &intent,
                &self.held_tokens,
                self.our_commitment,
                crate::VerificationMode::Trusted,
                now,
            );

            if let MatchResult::Matched { matched, .. } = result {
                // Check auto-fulfill policy
                if self.should_auto_fulfill(&intent) {
                    return Some(matched);
                } else {
                    // Store as pending for user approval
                    self.pending_matches.push((intent, matched.clone()));
                    return Some(matched);
                }
            }
        }

        None
    }

    /// Run garbage collection: remove expired intents.
    pub fn gc(&mut self, now: u64) {
        self.intents.retain(|_, intent| !intent.is_expired(now));
    }

    /// Get all active (non-expired) intents in the pool.
    pub fn active_intents(&self, now: u64) -> Vec<&Intent> {
        self.intents
            .values()
            .filter(|i| !i.is_expired(now))
            .collect()
    }

    /// Get the number of intents in the pool.
    pub fn len(&self) -> usize {
        self.intents.len()
    }

    /// Check if the pool is empty.
    pub fn is_empty(&self) -> bool {
        self.intents.is_empty()
    }

    /// Get pending matches waiting for user approval.
    pub fn pending_matches(&self) -> &[(Intent, Match)] {
        &self.pending_matches
    }

    /// Approve a pending match (remove from pending, return for fulfillment).
    pub fn approve_match(&mut self, intent_id: &[u8; 32]) -> Option<(Intent, Match)> {
        if let Some(idx) = self
            .pending_matches
            .iter()
            .position(|(i, _)| &i.id == intent_id)
        {
            Some(self.pending_matches.remove(idx))
        } else {
            None
        }
    }

    /// Reject a pending match.
    pub fn reject_match(&mut self, intent_id: &[u8; 32]) {
        self.pending_matches.retain(|(i, _)| &i.id != intent_id);
    }

    /// Get a specific intent by ID.
    pub fn get_intent(&self, id: &[u8; 32]) -> Option<&Intent> {
        self.intents.get(id)
    }

    /// Re-evaluate all pool intents against current held tokens.
    ///
    /// Useful after wallet state changes (new tokens provisioned, etc.)
    pub fn rematch_all(&mut self, now: u64) -> Vec<Match> {
        let mut matches = Vec::new();
        let intent_ids: Vec<[u8; 32]> = self.intents.keys().copied().collect();

        for id in intent_ids {
            if self.our_intent_ids.contains(&id) {
                continue;
            }
            if let Some(intent) = self.intents.get(&id) {
                let result = match_intent(
                    intent,
                    &self.held_tokens,
                    self.our_commitment,
                    crate::VerificationMode::Trusted,
                    now,
                );
                if let MatchResult::Matched { matched, .. } = result {
                    matches.push(matched);
                }
            }
        }

        matches
    }

    /// Check if a match should be auto-fulfilled based on policy.
    fn should_auto_fulfill(&self, intent: &Intent) -> bool {
        match &self.auto_fulfill {
            AutoFulfillPolicy::Never => false,
            AutoFulfillPolicy::Always => true,
            AutoFulfillPolicy::ForPatterns(patterns) => {
                if let Some(ref resource_pattern) = intent.matcher.resource_pattern {
                    patterns.iter().any(|p| {
                        globset::Glob::new(p)
                            .map(|g| g.compile_matcher().is_match(resource_pattern))
                            .unwrap_or(false)
                    })
                } else {
                    false
                }
            }
        }
    }

    /// Find the oldest intent by expiry (for eviction).
    fn find_oldest_intent(&self) -> Option<[u8; 32]> {
        self.intents
            .iter()
            .min_by_key(|(_, i)| i.expiry)
            .map(|(id, _)| *id)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ActionPattern, CommitmentId, IntentKind, MatchSpec, VerificationMode};

    fn test_pool() -> IntentPool {
        IntentPool::new(
            CommitmentId([0x11; 32]),
            IntentPoolConfig {
                max_intents: 100,
                gc_interval_secs: 60,
                auto_match: true,
            },
            AutoFulfillPolicy::Always,
        )
    }

    fn test_token(actions: &[&str], resource: &str) -> HeldCapability {
        HeldCapability {
            token_id: "tok_1".into(),
            actions: actions.iter().map(|s| s.to_string()).collect(),
            resource: resource.into(),
            app_id: None,
            service: None,
            user_id: None,
            features: vec![],
            oauth_provider: None,
            expiry: None,
            budget: None,
        }
    }

    #[test]
    fn test_broadcast_adds_to_pool() {
        let mut pool = test_pool();
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = pool.broadcast_intent(IntentKind::Need, spec, 9999, None);
        assert_eq!(pool.len(), 1);
        assert!(pool.get_intent(&intent.id).is_some());
    }

    #[test]
    fn test_receive_triggers_matching() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![test_token(&["read", "write"], "*")]);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x22; 32]), // different creator
            9999,
            None,
        );

        let result = pool.receive_intent(intent, 100);
        assert!(result.is_some());
    }

    #[test]
    fn test_own_intents_not_matched() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = pool.broadcast_intent(IntentKind::Need, spec, 9999, None);

        // Now "receive" it as if from gossip -- should be ignored
        let result = pool.receive_intent(intent, 100);
        assert!(result.is_none());
    }

    #[test]
    fn test_expired_intent_rejected() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x33; 32]),
            50, // expires at t=50
            None,
        );

        let result = pool.receive_intent(intent, 100); // now=100, expired
        assert!(result.is_none());
    }

    #[test]
    fn test_gc_removes_expired() {
        let mut pool = test_pool();

        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };

        // Add intent that expires at t=200
        let intent = Intent::new(
            IntentKind::Need,
            spec.clone(),
            CommitmentId([0x44; 32]),
            200,
            None,
        );
        pool.intents.insert(intent.id, intent);

        // Add intent that expires at t=500
        let intent2 = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x55; 32]),
            500,
            None,
        );
        pool.intents.insert(intent2.id, intent2);

        assert_eq!(pool.len(), 2);
        pool.gc(300); // t=300: first expired, second still valid
        assert_eq!(pool.len(), 1);
    }

    #[test]
    fn test_duplicate_intent_ignored() {
        let mut pool = test_pool();
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x66; 32]),
            9999,
            None,
        );

        let r1 = pool.receive_intent(intent.clone(), 100);
        assert!(r1.is_some());

        // Receiving same intent again should return None (duplicate)
        let r2 = pool.receive_intent(intent, 100);
        assert!(r2.is_none());
    }

    #[test]
    fn test_rematch_all() {
        let mut pool = test_pool();
        // Initially no tokens
        pool.update_held_tokens(vec![]);

        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let intent = Intent::new(
            IntentKind::Need,
            spec,
            CommitmentId([0x77; 32]),
            9999,
            None,
        );
        pool.intents.insert(intent.id, intent);

        // No matches yet (no tokens)
        let matches = pool.rematch_all(100);
        assert!(matches.is_empty());

        // Now add a token
        pool.update_held_tokens(vec![test_token(&["read"], "*")]);

        // Rematch should find it
        let matches = pool.rematch_all(100);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn test_pool_size_limit() {
        let mut pool = IntentPool::new(
            CommitmentId([0x11; 32]),
            IntentPoolConfig {
                max_intents: 3,
                gc_interval_secs: 60,
                auto_match: false,
            },
            AutoFulfillPolicy::Never,
        );

        for i in 0..5u8 {
            let spec = MatchSpec {
                actions: vec![ActionPattern {
                    action: Some(format!("action_{i}")),
                    resource: None,
                }],
                constraints: vec![],
                min_budget: None,
                resource_pattern: None,
            };
            let intent = Intent::new(
                IntentKind::Need,
                spec,
                CommitmentId([i + 0x80; 32]),
                (1000 + i as u64) * 10,
                None,
            );
            pool.receive_intent(intent, 100);
        }

        // Pool should not exceed max_intents
        assert!(pool.len() <= 3);
    }

    #[test]
    fn test_active_intents_filters_expired() {
        let mut pool = test_pool();

        let spec1 = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let i1 = Intent::new(IntentKind::Need, spec1.clone(), CommitmentId([0xA0; 32]), 200, None);
        let i2 = Intent::new(IntentKind::Need, spec1, CommitmentId([0xB0; 32]), 500, None);

        pool.intents.insert(i1.id, i1);
        pool.intents.insert(i2.id, i2);

        let active = pool.active_intents(300);
        assert_eq!(active.len(), 1);
    }
}
