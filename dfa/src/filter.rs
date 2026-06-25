//! Pattern-based filters used by gossip and capability-secure revocation.
//!
//! - [`TopicFilter`] — a wrapper around a compiled DFA that classifies the
//!   leading bytes of a message. Used by `intent::gossip` and by CapTP
//!   pre-/post-filters.
//! - [`FilterTree`] — a tree of DFA filters supporting revocation by
//!   marking a node inactive and recompiling the combined-intersection DFA.
//!   Lifted from `rbg::routing` with light changes.

use std::sync::Arc;

use crate::compiler::{Dfa, Pattern};
use crate::derivative::Re;

// ---------------------------------------------------------------------------
// TopicFilter
// ---------------------------------------------------------------------------

/// A compiled topic filter for gossip dispatch.
///
/// The filter is generic over what "topic bytes" mean for a given crate —
/// `intent::gossip` uses a 32-byte topic id; CapTP could use a 4-byte
/// framing prefix; an HTTP layer could use a path. The filter doesn't
/// prescribe a layout; it just matches its compiled pattern against the
/// leading `n` bytes of any input.
#[derive(Clone, Debug)]
pub struct TopicFilter {
    pattern: Pattern,
    compiled: Arc<Dfa>,
}

impl TopicFilter {
    /// Compile a topic filter from an arbitrary pattern.
    pub fn from_pattern(pattern: Pattern) -> Self {
        let compiled = Arc::new(pattern.compile());
        TopicFilter { pattern, compiled }
    }

    /// Match against an exact topic id.
    pub fn exact(topic: &[u8]) -> Self {
        Self::from_pattern(Pattern::word(topic))
    }

    /// Match any topic in `[low, high]` for its first byte, with the remaining
    /// `tail_len` bytes free. Mirrors `rbg::routing::TopicFilter::topic_namespace`.
    pub fn first_byte_range(low: u8, high: u8, tail_len: usize) -> Self {
        let mut parts = vec![Pattern::range(low, high)];
        for _ in 0..tail_len {
            parts.push(Pattern::any_byte());
        }
        Self::from_pattern(Pattern::seq(parts))
    }

    /// Match a fixed prefix followed by anything.
    pub fn prefix(prefix: &[u8]) -> Self {
        Self::from_pattern(Pattern::prefix_of(Pattern::word(prefix)))
    }

    /// True iff the filter accepts the message.
    pub fn matches(&self, message: &[u8]) -> bool {
        self.compiled.matches(message)
    }

    /// Match the leading `len` bytes only.
    pub fn matches_prefix_bytes(&self, message: &[u8], len: usize) -> bool {
        if message.len() < len {
            return false;
        }
        self.compiled.matches(&message[..len])
    }

    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    pub fn dfa(&self) -> &Dfa {
        &self.compiled
    }
}

// ---------------------------------------------------------------------------
// FilterTree (capability-secure filter revocation)
// ---------------------------------------------------------------------------

/// A tree of filters that compose by intersection along each root→leaf path.
/// Revoking a node marks it inactive (intersection identity → accept-all) and a
/// subsequent `compile_combined` rebuilds the active intersection.
///
/// Each node holds its filter as a byte regex ([`Re`]), and `compile_combined`
/// folds the active subtree with the **derivative `inter` constructor**
/// (`Re::and`) — the design's re-grounding (`DERIVATIVE-MATCHING-DESIGN.md`
/// §2.2). Only the final, combined `Re` is determinized, **once**, via the lazy
/// derivative path ([`Re::compile`]). This avoids the eager `dfa_intersection`
/// k-fold product (`O(∏|Sᵢ|)` states — the latent state-explosion site) and
/// makes a revoked-namespace *deny* filter (`base ⋒ ~revoked`) expressible. The
/// emitted flat [`Dfa`] is the same table the in-circuit AIR consumes.
pub struct FilterTree {
    nodes: Vec<FilterNode>,
    root: usize,
}

struct FilterNode {
    re: Re,
    children: Vec<usize>,
    active: bool,
}

impl FilterTree {
    /// Construct a fresh tree whose root accepts everything.
    pub fn new() -> Self {
        FilterTree {
            nodes: vec![FilterNode {
                re: accept_all_re(),
                children: Vec::new(),
                active: true,
            }],
            root: 0,
        }
    }

    /// Add a child filter under `parent`, given as an already-compiled [`Dfa`].
    /// The DFA is lifted to an equivalent [`Re`] (state elimination) so it
    /// participates in the lazy `inter` fold. Prefer [`FilterTree::add_pattern`]
    /// / [`FilterTree::add_re`] to avoid the recovery step. Returns the new
    /// node index.
    pub fn add_filter(&mut self, parent: usize, dfa: Dfa) -> usize {
        self.add_node(parent, Re::from_dfa(&dfa))
    }

    /// Add a child filter under `parent`, given as a [`Pattern`]. Lowered to a
    /// byte regex directly — the native, blow-up-free path (and the only one
    /// that can carry a [`Pattern::Not`] deny-filter). Returns the new node
    /// index.
    pub fn add_pattern(&mut self, parent: usize, pattern: &Pattern) -> usize {
        self.add_node(parent, pattern.to_re())
    }

    /// Add a child filter under `parent`, given directly as a byte regex
    /// ([`Re`]). Returns the new node index.
    pub fn add_re(&mut self, parent: usize, re: Re) -> usize {
        self.add_node(parent, re)
    }

    fn add_node(&mut self, parent: usize, re: Re) -> usize {
        let idx = self.nodes.len();
        self.nodes.push(FilterNode {
            re,
            children: Vec::new(),
            active: true,
        });
        self.nodes[parent].children.push(idx);
        idx
    }

    /// Mark `node_idx` inactive.
    pub fn revoke(&mut self, node_idx: usize) {
        self.nodes[node_idx].active = false;
    }

    /// Fold the active subtree into one combined byte regex (the derivative
    /// `inter` of every active node), then determinize **once** via the lazy
    /// derivative path.
    pub fn compile_combined(&self) -> Dfa {
        self.combined_re(self.root).compile()
    }

    /// The combined regex of the active subtree rooted at `node_idx`, folded
    /// with `Re::and` (the derivative intersection). An inactive node
    /// contributes accept-all (the intersection identity), exactly as before.
    fn combined_re(&self, node_idx: usize) -> Re {
        let node = &self.nodes[node_idx];
        if !node.active {
            return accept_all_re();
        }
        let mut combined = node.re.clone();
        for &child_idx in &node.children {
            combined = combined.and(self.combined_re(child_idx));
        }
        combined
    }
}

impl Default for FilterTree {
    fn default() -> Self {
        Self::new()
    }
}

/// The accept-all byte regex (`any*`) — the intersection identity.
fn accept_all_re() -> Re {
    Re::any_byte().star()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_topic_filter() {
        let f = TopicFilter::exact(b"hello");
        assert!(f.matches(b"hello"));
        assert!(!f.matches(b"hellp"));
    }

    #[test]
    fn first_byte_range_filter() {
        let f = TopicFilter::first_byte_range(0x10, 0x1F, 3);
        assert!(f.matches(&[0x10, 0xAA, 0xBB, 0xCC]));
        assert!(f.matches(&[0x1F, 0x00, 0x00, 0x00]));
        assert!(!f.matches(&[0x20, 0x00, 0x00, 0x00]));
        assert!(!f.matches(&[0x10, 0xAA])); // too short
    }

    #[test]
    fn prefix_filter() {
        let f = TopicFilter::prefix(b"topic:auth:");
        assert!(f.matches(b"topic:auth:login"));
        assert!(!f.matches(b"topic:data:event"));
    }

    #[test]
    fn filter_tree_deny_filter_via_not() {
        // FilterTree gains the deny-filter: base accepts the "/cells/" space,
        // a child intersects in "NOT under /cells/secret/". The combined filter
        // accepts /cells/alpha but denies /cells/secret/key.
        let mut tree = FilterTree::new();
        let base = tree.add_pattern(0, &Pattern::path_prefix("/cells/"));
        let _deny = tree.add_pattern(base, &Pattern::not(Pattern::path_prefix("/cells/secret/")));

        let combined = tree.compile_combined();
        assert!(combined.matches(b"/cells/alpha"));
        assert!(combined.matches(b"/cells/beta/x"));
        assert!(!combined.matches(b"/cells/secret/key"));
        assert!(!combined.matches(b"/other")); // base requires /cells/ prefix
    }

    #[test]
    fn filter_tree_lazy_intersection_air_neutral() {
        // The combined table from the lazy derivative FilterTree must verify
        // through the UNCHANGED air.rs machinery — proof side untouched.
        use crate::air::{generate_air_trace, verify_air_trace};

        let mut tree = FilterTree::new();
        let a = tree.add_pattern(
            0,
            &Pattern::seq(vec![
                Pattern::word(b"A"),
                Pattern::any_byte(),
                Pattern::any_byte(),
            ]),
        );
        let _b = tree.add_pattern(
            a,
            &Pattern::not(Pattern::seq(vec![
                Pattern::any_byte(),
                Pattern::any_byte(),
                Pattern::word(b"Z"),
            ])),
        );
        let dfa = tree.compile_combined();

        // "AxY": starts with A, last byte not Z → accepted by base ∩ ~(..Z).
        let accept_in = b"AxY";
        assert!(dfa.matches(accept_in));
        let trace = generate_air_trace(&dfa, accept_in);
        assert!(
            verify_air_trace(&dfa, accept_in, &trace),
            "AIR trace for the derivative-built table failed to verify"
        );

        // "AxZ": last byte Z → denied by the complement; trace verifies as a
        // (correct) non-acceptance.
        let reject_in = b"AxZ";
        assert!(!dfa.matches(reject_in));
        let trace = generate_air_trace(&dfa, reject_in);
        assert!(
            !verify_air_trace(&dfa, reject_in, &trace),
            "AIR trace wrongly accepted a denied word"
        );
    }

    #[test]
    fn filter_tree_revocation_restores_acceptance() {
        let mut tree = FilterTree::new();
        let a = Pattern::seq(vec![
            Pattern::word(b"A"),
            Pattern::any_byte(),
            Pattern::any_byte(),
        ])
        .compile();
        let z = Pattern::seq(vec![
            Pattern::any_byte(),
            Pattern::any_byte(),
            Pattern::word(b"Z"),
        ])
        .compile();
        let _na = tree.add_filter(0, a);
        let nz = tree.add_filter(0, z);

        let combined = tree.compile_combined();
        assert!(combined.matches(b"AxZ"));
        assert!(!combined.matches(b"BxZ"));
        assert!(!combined.matches(b"AxY"));

        tree.revoke(nz);
        let after = tree.compile_combined();
        assert!(after.matches(b"AxZ"));
        assert!(after.matches(b"AxY"));
        assert!(!after.matches(b"BxZ"));
    }
}
