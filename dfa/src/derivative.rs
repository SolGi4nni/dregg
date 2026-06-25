//! Derivative-based DFA compiler over the byte alphabet.
//!
//! This is the Rust realization of the Brzozowski/Antimirov **symbolic
//! derivative** front-end designed in
//! `docs/deos/DERIVATIVE-MATCHING-DESIGN.md` (§2, §5.1 Stage 2). It exists to
//! give the [`crate::compiler::Pattern`] / [`crate::filter::FilterTree`] layer
//! two capabilities the eager `Pattern → Nfa → Dfa` product path cannot offer:
//!
//! * **complement (`~` / [`crate::compiler::Pattern::Not`])** — the cap-secure
//!   *deny* filter ("match everything except a revoked namespace"), which is
//!   *inexpressible* in the NFA-product world (Thompson NFAs have no
//!   complement constructor).
//! * **intersection without the eager product blow-up** — `inter` is a
//!   *derivative constructor* (`der b (l ∩ r) = der b l ∩ der b r`), so a
//!   `k`-fold intersection determinizes **lazily**: only the reachable product
//!   states are ever materialized, and structural normalization collapses the
//!   ones that denote the same residual language.
//!
//! The output is the **same flat [`Dfa`]** the rest of the crate (and, crucially,
//! the in-circuit DFA-AIR — `air.rs`, `metatheory/Dregg2/Crypto/Dfa.lean`)
//! already consumes: `transitions[state * 256 + byte] -> next_state`, dead
//! state at index 0, start state at index 1. Nothing about the table layout,
//! the AIR trace shape, or the proof side changes — the derivative theory is a
//! *new way to build the table*, living entirely in the compiler.
//!
//! ## How the byte alphabet stays cheap
//!
//! A naïve derivative determinizer would take `der b R` for all 256 `b` at
//! every state. Instead we compute, per regex node, the set of **derivative
//! classes** — the byte-boundaries at which `der b R` can change — from the
//! leaf byte-class predicates, take the derivative once per class
//! representative, and fan the result out across the 256-wide flat row. This is
//! the symbolic/lazy determinization the design calls for: work is proportional
//! to the number of distinct byte-classes, not to 256.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use crate::compiler::{DEAD_STATE, Dfa, StateId};

// ---------------------------------------------------------------------------
// Byte-class predicate (the `sym` leaf)
// ---------------------------------------------------------------------------

/// A predicate over a single byte: the union of inclusive ranges it accepts.
///
/// This is the `sym φ` leaf of the design's `PredRE` specialized to the byte
/// alphabet — `Pred` over a byte is exactly a finite union of byte ranges
/// (`Range(low,high)` is a `Pred` over a byte, `DERIVATIVE-MATCHING-DESIGN.md`
/// §2.3). Stored as a sorted, disjoint, merged set of `[low, high]` ranges so
/// equality is canonical (two `ByteClass`es are equal iff they accept the same
/// byte set), which the similarity quotient relies on.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ByteClass {
    /// Sorted, disjoint, gap-separated inclusive ranges.
    ranges: Vec<(u8, u8)>,
}

impl ByteClass {
    /// The empty class — accepts no byte.
    pub fn empty() -> Self {
        ByteClass { ranges: Vec::new() }
    }

    /// The full class — accepts every byte.
    pub fn full() -> Self {
        ByteClass {
            ranges: vec![(0, 255)],
        }
    }

    /// A single inclusive range `[low, high]`. Empty if `low > high`.
    pub fn range(low: u8, high: u8) -> Self {
        if low > high {
            ByteClass::empty()
        } else {
            ByteClass {
                ranges: vec![(low, high)],
            }
        }
    }

    /// A single byte.
    pub fn byte(b: u8) -> Self {
        ByteClass::range(b, b)
    }

    /// Build from an arbitrary list of inclusive ranges (canonicalized).
    pub fn from_ranges(ranges: Vec<(u8, u8)>) -> Self {
        ByteClass::normalize(ranges)
    }

    pub fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    /// True iff `b` is in the class.
    pub fn contains(&self, b: u8) -> bool {
        self.ranges.iter().any(|&(lo, hi)| lo <= b && b <= hi)
    }

    /// Canonicalize: sort and merge adjacent/overlapping ranges.
    fn normalize(mut ranges: Vec<(u8, u8)>) -> Self {
        ranges.retain(|&(lo, hi)| lo <= hi);
        ranges.sort_unstable();
        let mut merged: Vec<(u8, u8)> = Vec::with_capacity(ranges.len());
        for (lo, hi) in ranges {
            if let Some(last) = merged.last_mut() {
                // merge if overlapping or directly adjacent (last.1 + 1 == lo)
                if lo <= last.1 || (last.1 < 255 && last.1 + 1 == lo) {
                    if hi > last.1 {
                        last.1 = hi;
                    }
                    continue;
                }
            }
            merged.push((lo, hi));
        }
        ByteClass { ranges: merged }
    }

    /// Set complement (within `[0, 255]`).
    pub fn complement(&self) -> Self {
        let mut out = Vec::new();
        let mut cursor: u16 = 0;
        for &(lo, hi) in &self.ranges {
            if (lo as u16) > cursor {
                out.push((cursor as u8, (lo - 1)));
            }
            cursor = hi as u16 + 1;
        }
        if cursor <= 255 {
            out.push((cursor as u8, 255));
        }
        ByteClass { ranges: out }
    }
}

// ---------------------------------------------------------------------------
// Re — the byte regex with native intersection and complement
// ---------------------------------------------------------------------------

/// A regular expression over the byte alphabet, with native intersection and
/// complement — the design's `PredRE` specialized to `σ := byte`
/// (`DERIVATIVE-MATCHING-DESIGN.md` §1.2).
///
/// Held behind `Box` for the recursive arms. Equality / ordering are
/// structural over the (already canonicalized) tree, which is what makes the
/// similarity quotient — and therefore Brzozowski-finiteness — work in
/// practice: smart constructors keep the tree in a canonical form so that
/// derivatives that denote the same residual language compare equal.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Re {
    /// `∅` — matches nothing (the empty language).
    Empty,
    /// `ε` — matches the empty word only.
    Epsilon,
    /// `sym φ` — one byte satisfying the byte-class `φ`.
    Sym(ByteClass),
    /// Concatenation `l · r`.
    Cat(Box<Re>, Box<Re>),
    /// Alternation `l ⋓ r` (union of languages).
    Alt(Box<Re>, Box<Re>),
    /// Intersection `l ⋒ r` (the FilterTree product, as a derivative ctor).
    Inter(Box<Re>, Box<Re>),
    /// Complement `~r` (the deny-filter — newly expressible).
    Neg(Box<Re>),
    /// Kleene star `r*`.
    Star(Box<Re>),
}

impl Re {
    pub fn empty() -> Re {
        Re::Empty
    }
    pub fn epsilon() -> Re {
        Re::Epsilon
    }
    /// One byte satisfying `class`.
    pub fn sym(class: ByteClass) -> Re {
        if class.is_empty() {
            Re::Empty
        } else {
            Re::Sym(class)
        }
    }
    /// One byte in `[low, high]`.
    pub fn range(low: u8, high: u8) -> Re {
        Re::sym(ByteClass::range(low, high))
    }
    /// Exactly the byte `b`.
    pub fn byte(b: u8) -> Re {
        Re::sym(ByteClass::byte(b))
    }
    /// Any single byte.
    pub fn any_byte() -> Re {
        Re::sym(ByteClass::full())
    }
    /// `ε` if the word is empty; matches the literal byte sequence otherwise.
    pub fn word(bytes: &[u8]) -> Re {
        let mut re = Re::Epsilon;
        for &b in bytes {
            re = re.then(Re::byte(b));
        }
        re
    }

    // --- smart constructors (keep the tree canonical for the ~ quotient) ---

    /// `self · other`, with the standard `∅`/`ε` absorption/identity laws.
    pub fn then(self, other: Re) -> Re {
        match (self, other) {
            (Re::Empty, _) | (_, Re::Empty) => Re::Empty,
            (Re::Epsilon, r) => r,
            (l, Re::Epsilon) => l,
            (l, r) => Re::Cat(Box::new(l), Box::new(r)),
        }
    }

    /// `self ⋓ other`, with `∅` identity, idempotence, and commutativity
    /// (canonical ordering of the operands) — the ACI normalization the
    /// similarity quotient needs.
    pub fn or(self, other: Re) -> Re {
        match (self, other) {
            (Re::Empty, r) => r,
            (l, Re::Empty) => l,
            (l, r) if l == r => l,
            (l, r) => {
                // canonical order so `a|b` and `b|a` share a representative
                let (a, b) = if l <= r { (l, r) } else { (r, l) };
                Re::Alt(Box::new(a), Box::new(b))
            }
        }
    }

    /// `self ⋒ other`, with `∅` absorption, idempotence, commutativity.
    pub fn and(self, other: Re) -> Re {
        match (self, other) {
            (Re::Empty, _) | (_, Re::Empty) => Re::Empty,
            (l, r) if l == r => l,
            (l, r) => {
                let (a, b) = if l <= r { (l, r) } else { (r, l) };
                Re::Inter(Box::new(a), Box::new(b))
            }
        }
    }

    /// `~self`, with double-negation elimination.
    pub fn not(self) -> Re {
        match self {
            Re::Neg(inner) => *inner,
            r => Re::Neg(Box::new(r)),
        }
    }

    /// `self*`, with `∅* = ε* = ε` and `r** = r*` idempotence.
    pub fn star(self) -> Re {
        match self {
            Re::Empty | Re::Epsilon => Re::Epsilon,
            Re::Star(_) => self,
            r => Re::Star(Box::new(r)),
        }
    }

    /// `self · any*` — the `prefix/*` wildcard.
    pub fn prefix_of(self) -> Re {
        self.then(Re::any_byte().star())
    }

    // --- nullability + derivative ---

    /// `null R` — does `R` match the empty word? (location-free; we have no
    /// lookaround — `DERIVATIVE-MATCHING-DESIGN.md` §1.3).
    pub fn nullable(&self) -> bool {
        match self {
            Re::Empty => false,
            Re::Epsilon => true,
            Re::Sym(_) => false,
            Re::Cat(l, r) => l.nullable() && r.nullable(),
            Re::Alt(l, r) => l.nullable() || r.nullable(),
            Re::Inter(l, r) => l.nullable() && r.nullable(),
            Re::Neg(r) => !r.nullable(),
            Re::Star(_) => true,
        }
    }

    /// `der b R` — the Brzozowski derivative w.r.t. byte `b`. Built through the
    /// smart constructors so the result is canonical (the similarity quotient).
    pub fn derive(&self, b: u8) -> Re {
        match self {
            Re::Empty | Re::Epsilon => Re::Empty,
            Re::Sym(class) => {
                if class.contains(b) {
                    Re::Epsilon
                } else {
                    Re::Empty
                }
            }
            Re::Cat(l, r) => {
                let dl = l.derive(b).then((**r).clone());
                if l.nullable() { dl.or(r.derive(b)) } else { dl }
            }
            Re::Alt(l, r) => l.derive(b).or(r.derive(b)),
            Re::Inter(l, r) => l.derive(b).and(r.derive(b)),
            Re::Neg(r) => r.derive(b).not(),
            Re::Star(r) => r.derive(b).then(self.clone()),
        }
    }

    /// Decide whether `word` matches by iterating the derivative
    /// (`derives w R = null (der* w R)` — the streaming matcher).
    pub fn matches(&self, word: &[u8]) -> bool {
        let mut cur = self.clone();
        for &b in word {
            cur = cur.derive(b);
            if let Re::Empty = cur {
                return false;
            }
        }
        cur.nullable()
    }

    /// The set of byte-boundaries at which `der b R` can change behavior — the
    /// **derivative classes**. We collect the endpoints of every leaf range and
    /// determinize one representative per resulting cell, instead of all 256
    /// bytes. The returned vector is a partition of `[0, 255]` into maximal
    /// intervals on which the derivative is constant.
    fn derivative_classes(&self) -> Vec<(u8, u8)> {
        let mut cuts: BTreeSet<u16> = BTreeSet::new();
        cuts.insert(0);
        cuts.insert(256); // sentinel = "one past the last byte"
        self.collect_cuts(&mut cuts);
        let sorted: Vec<u16> = cuts.into_iter().collect();
        let mut out = Vec::new();
        for win in sorted.windows(2) {
            let lo = win[0];
            let hi = win[1] - 1;
            if lo <= hi && lo <= 255 {
                out.push((lo as u8, hi.min(255) as u8));
            }
        }
        out
    }

    /// Gather range start/end+1 boundaries from every `Sym` leaf.
    fn collect_cuts(&self, cuts: &mut BTreeSet<u16>) {
        match self {
            Re::Empty | Re::Epsilon => {}
            Re::Sym(class) => {
                for &(lo, hi) in &class.ranges {
                    cuts.insert(lo as u16);
                    cuts.insert(hi as u16 + 1);
                }
            }
            Re::Cat(l, r) | Re::Alt(l, r) | Re::Inter(l, r) => {
                l.collect_cuts(cuts);
                r.collect_cuts(cuts);
            }
            Re::Neg(r) | Re::Star(r) => r.collect_cuts(cuts),
        }
    }
}

// ---------------------------------------------------------------------------
// Dfa → Re recovery (state elimination)
// ---------------------------------------------------------------------------

impl Re {
    /// Recover a byte regex recognizing the same language as `dfa`, via the
    /// classic **state-elimination** construction. Used by [`crate::filter::FilterTree`]
    /// as a compatibility shim so a node added as an already-compiled [`Dfa`]
    /// can still participate in the lazy derivative `inter` fold.
    ///
    /// The preferred path is to add filters as patterns/`Re`s directly (no
    /// recovery needed); this exists only to keep the `add_filter(Dfa)` API
    /// working without an eager product.
    pub fn from_dfa(dfa: &Dfa) -> Re {
        let n = dfa.num_states as usize;
        // Generalized-NFA transition matrix `g[i][j]` = Re from state i to j.
        // Add a fresh source `S` (index n) and sink `T` (index n+1).
        let src = n;
        let sink = n + 1;
        let total = n + 2;
        let mut g: Vec<Vec<Re>> = vec![vec![Re::Empty; total]; total];

        // Edge from each state on each byte-class (group bytes by target).
        for s in 0..n {
            if s == DEAD_STATE as usize {
                continue; // dead state has no useful outgoing edges
            }
            // Group bytes by their next state into classes.
            let mut by_target: BTreeMap<StateId, Vec<(u8, u8)>> = BTreeMap::new();
            for b in 0u16..=255u16 {
                let next = dfa.transitions[s * 256 + b as usize];
                if next == DEAD_STATE {
                    continue;
                }
                let entry = by_target.entry(next).or_default();
                // extend a run if contiguous
                if let Some(last) = entry.last_mut() {
                    if last.1 as u16 + 1 == b {
                        last.1 = b as u8;
                        continue;
                    }
                }
                entry.push((b as u8, b as u8));
            }
            for (target, ranges) in by_target {
                let class = ByteClass::from_ranges(ranges);
                let edge = Re::sym(class);
                g[s][target as usize] = g[s][target as usize].clone().or(edge);
            }
        }

        // Source → start (ε); each accepting state → sink (ε).
        g[src][dfa.start as usize] = Re::Epsilon;
        for &acc in &dfa.accepting {
            g[acc as usize][sink] = g[acc as usize][sink].clone().or(Re::Epsilon);
        }

        // Eliminate every real state (0..n), keeping src and sink.
        let mut eliminated = vec![false; total];
        for k in 0..n {
            eliminated[k] = true;
            let loop_re = g[k][k].clone().star();
            for i in 0..total {
                if eliminated[i] || g[i][k] == Re::Empty {
                    continue;
                }
                for j in 0..total {
                    if eliminated[j] || g[k][j] == Re::Empty {
                        continue;
                    }
                    // new path i→j: existing  ⋓  (i→k)(k→k)*(k→j)
                    let through = g[i][k].clone().then(loop_re.clone()).then(g[k][j].clone());
                    g[i][j] = g[i][j].clone().or(through);
                }
            }
        }

        g[src][sink].clone()
    }
}

// ---------------------------------------------------------------------------
// Lazy determinization: Re → flat Dfa
// ---------------------------------------------------------------------------

impl Re {
    /// Lazily determinize this regex into the crate's flat [`Dfa`], visiting
    /// only reachable derivative-states. The emitted table is the exact shape
    /// the rest of the crate and the in-circuit AIR consume:
    /// `transitions[state * 256 + byte]`, dead state 0, start state 1.
    ///
    /// State = a similarity-class of derivatives (canonicalized `Re`). The dead
    /// state is the `Re::Empty` class, mapped to index 0. Because `Neg` is a
    /// real constructor, the dead state is reachable *and complementable* — a
    /// complemented pattern produces an explicit accepting "trap" with
    /// self-loops on every byte, which is exactly what makes deny-filters total.
    pub fn compile(&self) -> Dfa {
        let mut state_ids: HashMap<Re, StateId> = HashMap::new();
        let mut order: Vec<Re> = Vec::new();
        let mut transitions: Vec<StateId> = Vec::new();
        let mut accepting: BTreeSet<StateId> = BTreeSet::new();

        // Dead state (index 0) is the Empty regex: it loops to itself on every
        // byte and never accepts.
        state_ids.insert(Re::Empty, DEAD_STATE);
        order.push(Re::Empty);
        transitions.extend(std::iter::repeat_n(DEAD_STATE, 256));

        // Start state (index 1).
        let start_re = self.clone();
        let start_id: StateId = 1;
        // If the start regex happens to *be* Empty, the whole language is ∅;
        // start is still 1 (a fresh dead-equivalent) for table-shape parity
        // with the eager compiler, which always reserves state 1 as start.
        state_ids.insert(start_re.clone(), start_id);
        // Guard: if start collided with Empty above (language is ∅), the insert
        // above is a no-op and start_id below would be wrong. Handle explicitly.
        let language_empty = matches!(start_re, Re::Empty);
        if !language_empty {
            order.push(start_re.clone());
            transitions.extend(std::iter::repeat_n(DEAD_STATE, 256));
            if start_re.nullable() {
                accepting.insert(start_id);
            }
        } else {
            // Empty language: a 2-state table (dead 0, empty start 1) that
            // never accepts. Mirrors the eager compiler's "accept nothing".
            order.push(Re::Star(Box::new(Re::Empty))); // placeholder distinct key
            transitions.extend(std::iter::repeat_n(DEAD_STATE, 256));
        }

        let mut worklist: VecDeque<StateId> = VecDeque::new();
        worklist.push_back(start_id);

        while let Some(cur_id) = worklist.pop_front() {
            let cur_re = order[cur_id as usize].clone();
            // Empty/placeholder states stay dead-looping; nothing to expand.
            if matches!(cur_re, Re::Empty) || (language_empty && cur_id == start_id) {
                continue;
            }

            // Compute the derivative once per byte-class, then fan it across the
            // 256-wide flat row — the lazy/symbolic determinization.
            let classes = cur_re.derivative_classes();
            for (lo, hi) in classes {
                let next_re = cur_re.derive(lo);
                let next_id = match state_ids.get(&next_re) {
                    Some(&id) => id,
                    None => {
                        let id = order.len() as StateId;
                        state_ids.insert(next_re.clone(), id);
                        if next_re.nullable() {
                            accepting.insert(id);
                        }
                        order.push(next_re.clone());
                        transitions.extend(std::iter::repeat_n(DEAD_STATE, 256));
                        worklist.push_back(id);
                        id
                    }
                };
                // Fill every byte in [lo, hi] of this state's row.
                let base = (cur_id as usize) * 256;
                for b in lo..=hi {
                    transitions[base + b as usize] = next_id;
                }
            }
        }

        Dfa {
            num_states: order.len() as u32,
            transitions,
            start: start_id,
            accepting,
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_class_complement_roundtrip() {
        let c = ByteClass::range(b'a', b'z');
        let comp = c.complement();
        assert!(!comp.contains(b'a'));
        assert!(!comp.contains(b'z'));
        assert!(comp.contains(b'A'));
        assert!(comp.contains(0));
        assert!(comp.contains(255));
        // double complement is the original
        assert_eq!(comp.complement(), c);
    }

    #[test]
    fn byte_class_normalize_merges_adjacent() {
        let c = ByteClass::normalize(vec![(0, 5), (6, 10), (3, 7)]);
        assert_eq!(c, ByteClass::range(0, 10));
    }

    #[test]
    fn word_matches_via_derivative() {
        let re = Re::word(b"hello");
        assert!(re.matches(b"hello"));
        assert!(!re.matches(b"hell"));
        assert!(!re.matches(b"helloo"));
        assert!(!re.matches(b""));
    }

    #[test]
    fn star_and_prefix() {
        let re = Re::word(b"/x/").prefix_of();
        assert!(re.matches(b"/x/"));
        assert!(re.matches(b"/x/anything"));
        assert!(!re.matches(b"/y/"));
    }

    #[test]
    fn intersection_via_derivative() {
        // [a-z].. ∩ ..[0-9]  (3 bytes: first lowercase, last digit)
        let l = Re::range(b'a', b'z')
            .then(Re::any_byte())
            .then(Re::any_byte());
        let r = Re::any_byte()
            .then(Re::any_byte())
            .then(Re::range(b'0', b'9'));
        let re = l.and(r);
        assert!(re.matches(b"ab1"));
        assert!(!re.matches(b"ab_"));
        assert!(!re.matches(b"1b1"));
    }

    #[test]
    fn complement_denies() {
        // ~(word "no") — match everything EXCEPT exactly "no".
        let re = Re::word(b"no").not();
        assert!(!re.matches(b"no"));
        assert!(re.matches(b"yes"));
        assert!(re.matches(b"n"));
        assert!(re.matches(b"nope"));
        assert!(re.matches(b""));
    }

    #[test]
    fn deny_filter_intersection() {
        // any* ∩ ~(prefix "/blocked/") — accept anything that is NOT under
        // the /blocked/ namespace. The canonical capability-secure deny filter.
        let allow_all = Re::any_byte().star();
        let blocked = Re::word(b"/blocked/").prefix_of();
        let re = allow_all.and(blocked.not());
        assert!(re.matches(b"/cells/alpha"));
        assert!(!re.matches(b"/blocked/secret"));
        assert!(re.matches(b"/blocked")); // not under the / boundary
        assert!(re.matches(b""));
    }

    #[test]
    fn compiled_dfa_matches_derivative() {
        // Compile to the flat table and confirm the table agrees with the
        // streaming matcher on a corpus — this is the table the AIR consumes.
        let re = Re::word(b"/blocked/").prefix_of().not();
        let dfa = re.compile();
        for w in [
            &b""[..],
            b"/blocked/x",
            b"/blocked",
            b"/cells",
            b"/blocked/",
            b"hello world",
        ] {
            assert_eq!(
                dfa.matches(w),
                re.matches(w),
                "table vs derivative disagree on {:?}",
                w
            );
        }
    }

    #[test]
    fn lazy_intersection_is_small() {
        // A k-fold intersection of "first byte in disjoint-ish ranges" — the
        // eager product would multiply state counts; the lazy derivative path
        // collapses equivalent residuals. Just assert it compiles to a modest
        // size and matches correctly.
        let parts: Vec<Re> = (0..6)
            .map(|i| {
                // each constrains a different position to a wide range, free elsewhere
                let mut seq = Re::epsilon();
                for j in 0..6 {
                    if j == i {
                        seq = seq.then(Re::range(b'a', b'y'));
                    } else {
                        seq = seq.then(Re::any_byte());
                    }
                }
                seq
            })
            .collect();
        let re = parts.into_iter().reduce(|a, b| a.and(b)).unwrap();
        let dfa = re.compile();
        assert!(re.matches(b"abcdef"));
        assert!(!re.matches(b"abcdez")); // last pos must be a..y, z fails the i=5 part? z>y
        // Sanity: 6-byte words only; state growth is linear-ish in length, not
        // exponential in the number of intersected parts.
        assert!(
            dfa.num_states < 40,
            "lazy intersection blew up: {} states",
            dfa.num_states
        );
        assert_eq!(dfa.matches(b"abcdef"), re.matches(b"abcdef"));
    }

    #[test]
    fn empty_language_compiles() {
        let re = Re::empty();
        let dfa = re.compile();
        assert!(!dfa.matches(b""));
        assert!(!dfa.matches(b"x"));
    }

    #[test]
    fn epsilon_language_compiles() {
        let re = Re::epsilon();
        let dfa = re.compile();
        assert!(dfa.matches(b""));
        assert!(!dfa.matches(b"x"));
    }
}
