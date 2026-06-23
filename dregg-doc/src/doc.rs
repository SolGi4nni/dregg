//! The ergonomic authoring path — author a document by typing TEXT.
//!
//! The patch core ([`crate::Patch`], [`crate::History`]) is authored by
//! hand-assembling `Add` / `Delete` / `Connect` ops. That is the right *algebra*
//! but the wrong *surface* for a human writing prose: nobody wants to mint atom
//! ids and thread order-edges by hand. [`Doc`] closes that gap. You hold a `Doc`,
//! you call [`Doc::edit`] with the *new full text*, and the diff against the
//! current text is turned into the minimal `Add`/`Delete` patch automatically —
//! the same patch you would have authored by hand, committed to the history.
//!
//! ## How the diff becomes a patch
//!
//! 1. **Tokenize** the current text and the new text at the chosen
//!    [`Granularity`] (the spec, §4.4, says *start span-coarse*: the default is
//!    [`Granularity::Line`]). Tokenization keeps its delimiters (a `Line` token
//!    carries its trailing `'\n'`; a `Word` token carries its trailing
//!    whitespace) so concatenating the tokens reproduces the text exactly.
//! 2. **LCS** (classic dynamic-programming longest-common-subsequence, no
//!    external crate) aligns the two token streams. The tokens *in* the LCS are
//!    KEPT; the current-side tokens not in it are DELETED; the new-side tokens
//!    not in it are INSERTED.
//! 3. **Map kept tokens to their existing atom ids** — never re-mint them. The
//!    current atom-id sequence in document order comes from
//!    [`crate::walk_atoms`] (one atom per token, by construction, so the mapping
//!    is positional and exact).
//! 4. **Deletes** become [`Op::Delete`]; **inserts** become an [`Op::Add`]
//!    anchored after the running predecessor (a kept atom, a freshly-inserted
//!    atom, or [`AtomId::ROOT`] at the head) plus an [`Op::Connect`] threading
//!    the insertion back into the successor chain (the `insert_in_the_middle`
//!    pattern).
//!
//! ## The stable-atom-id trap (the load-bearing correctness issue)
//!
//! [`AtomId::derive`] keys *only* on `(seed, content)` — there is no position in
//! it. So two identical tokens (the word "the" written twice) would derive to the
//! SAME id under a fixed seed, collapsing into one atom: deleting the first "the"
//! would tombstone *both*, and you cannot order an atom before itself. For prose,
//! where repeats are everywhere, that is catastrophic.
//!
//! The fix: when minting a *new* inserted atom's id, the seed is derived from the
//! **predecessor atom id** (the atom this insertion is anchored after), not from
//! a global counter. Because every inserted atom is anchored after a *distinct*
//! predecessor (an insert chains after the previous insert), identical tokens at
//! different positions get different seeds and therefore different ids. Kept
//! tokens keep their EXISTING ids (matched in step 3, never re-derived). This
//! makes "a b a" -> "b a" delete only the *first* "a" while the *second* "a"
//! survives — they are genuinely distinct atoms (see the test below).

use crate::atom::{AtomId, Author, PatchId};
use crate::content::{content, walk_atoms};
use crate::history::History;
use crate::patch::{Op, Patch};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// The atom granularity for text authoring: how [`Doc::edit`] splits text into
/// tokens (= one atom each). The spec (§4.4) leaves this an empirical choice and
/// says to *start span-coarse*, so [`Doc::new`]'s callers default to
/// [`Granularity::Line`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Granularity {
    /// One atom per line (split keeping the trailing `'\n'`). The coarse default.
    Line,
    /// One atom per word (split on whitespace, keeping the trailing whitespace as
    /// part of the token so re-rendering is byte-exact).
    Word,
}

/// A document you author by typing text. Holds a patch-[`History`]; each
/// [`Doc::edit`] diffs the new text against the current rendered text and commits
/// the resulting minimal `Add`/`Delete` patch.
#[derive(Clone, Debug)]
pub struct Doc {
    history: History,
    granularity: Granularity,
}

impl Doc {
    /// A fresh, empty document at the given granularity.
    pub fn new(g: Granularity) -> Self {
        Doc {
            history: History::new(),
            granularity: g,
        }
    }

    /// A document over an EXISTING patch-history (e.g. one produced by a
    /// [`History::stitch`] of two branches). Subsequent [`Doc::edit`]s chain off the
    /// folded state of this history. This is the constructor the program-source weld
    /// needs after a merge: it adopts the stitched history so the merged source stays
    /// editable.
    pub fn from_history(history: History, g: Granularity) -> Self {
        Doc {
            history,
            granularity: g,
        }
    }

    /// The current rendered text: the clean content of the folded history. (A
    /// document with an unresolved conflict has no single linear text; this
    /// flattens the clean segments, which for the single-author text-editing path
    /// is the whole document.)
    pub fn text(&self) -> String {
        let rendered = content(&self.history.replay());
        rendered
            .segments
            .iter()
            .filter_map(|s| match s {
                crate::content::Segment::Clean(t) => Some(t.as_str()),
                crate::content::Segment::Conflict(_) => None,
            })
            .collect()
    }

    /// Access the underlying patch-history (read-only) — for inspection,
    /// time-travel, branching, or merging with another author's branch.
    pub fn history(&self) -> &History {
        &self.history
    }

    /// THE ergonomic edit: diff the current text into `new_text` and commit the
    /// resulting `Add`/`Delete` patch, authored by `author`. Returns the new tip
    /// [`PatchId`]. If the text is unchanged the patch is empty (a no-op commit
    /// whose tip is the empty-patch id).
    pub fn edit(&mut self, author: Author, new_text: &str) -> PatchId {
        let ops = diff_history_to_ops(&self.history, new_text, self.granularity);
        self.history.commit(Patch::by(author, ops))
    }
}

/// THE shared diff-to-patch core: diff a [`History`]'s current rendered content
/// against `new_text` (tokenized at `g`) and return the minimal `Add`/`Delete`/
/// `Connect` ops. Both [`Doc::edit`] and the `ropey` bridge ([`crate::rope`])
/// ride this — the rope bridge feeds `new_text = new_rope.to_string()`, so the
/// editor's real buffer becomes a patch through exactly the same alignment.
pub(crate) fn diff_history_to_ops(history: &History, new_text: &str, g: Granularity) -> Vec<Op> {
    let graph = history.replay();
    // The current alive atoms in document order — one atom per token by
    // construction, so `cur_ids[i]` is the atom holding `cur_tokens[i]`.
    let walked = walk_atoms(&graph);
    let cur_ids: Vec<AtomId> = walked.iter().map(|(id, _)| *id).collect();
    let cur_text: String = walked.iter().map(|(_, c)| c.as_str()).collect();

    let cur_tokens = tokenize(&cur_text, g);
    let new_tokens = tokenize(new_text, g);

    // Sanity: the walked atom sequence must align 1:1 with the tokenization of
    // the text it renders (it does, because we always author one atom per token).
    // If it ever didn't, mapping kept tokens to ids would be wrong.
    debug_assert_eq!(cur_tokens.len(), cur_ids.len(), "one atom per token invariant");

    diff_to_ops(&cur_tokens, &cur_ids, &new_tokens)
}

/// Split `text` into tokens, keeping the delimiters so the tokens concatenate
/// back to `text` exactly.
///
/// - [`Granularity::Line`]: each token is a line *including* its trailing `'\n'`
///   (the final line has none if the text doesn't end in `'\n'`).
/// - [`Granularity::Word`]: each token is a run of non-whitespace *followed by*
///   the run of whitespace up to the next word, so the whitespace travels with
///   the word before it (leading whitespace forms its own token).
pub(crate) fn tokenize(text: &str, g: Granularity) -> Vec<String> {
    match g {
        Granularity::Line => split_keep_newlines(text),
        Granularity::Word => split_words_keep_ws(text),
    }
}

/// Lines, each carrying its trailing `'\n'`.
fn split_keep_newlines(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for ch in text.chars() {
        cur.push(ch);
        if ch == '\n' {
            out.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// Words, each a run of non-whitespace plus the trailing whitespace run that
/// follows it. A leading whitespace run (no preceding word) is its own token.
fn split_words_keep_ws(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    // True once we are in the trailing-whitespace tail of a word; a non-ws char
    // arriving then closes the current token and starts a new word.
    let mut in_trailing_ws = false;
    for ch in text.chars() {
        if ch.is_whitespace() {
            cur.push(ch);
            in_trailing_ws = !cur.chars().all(char::is_whitespace);
        } else {
            if in_trailing_ws {
                out.push(std::mem::take(&mut cur));
                in_trailing_ws = false;
            }
            cur.push(ch);
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// The classic LCS dynamic program over two token slices. Returns the list of
/// matched index pairs `(i, j)` (i in `a`, j in `b`) in increasing order — the
/// alignment skeleton the diff is read off of.
fn lcs_pairs(a: &[String], b: &[String]) -> Vec<(usize, usize)> {
    let n = a.len();
    let m = b.len();
    // dp[i][j] = LCS length of a[i..] and b[j..].
    let mut dp = vec![vec![0u32; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            dp[i][j] = if a[i] == b[j] {
                dp[i + 1][j + 1] + 1
            } else {
                dp[i + 1][j].max(dp[i][j + 1])
            };
        }
    }
    let mut pairs = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < n && j < m {
        if a[i] == b[j] {
            pairs.push((i, j));
            i += 1;
            j += 1;
        } else if dp[i + 1][j] >= dp[i][j + 1] {
            i += 1;
        } else {
            j += 1;
        }
    }
    pairs
}

/// Fold a predecessor atom id into a derivation seed. This is the heart of the
/// stable-id scheme: an inserted atom's id is `AtomId::derive(seed(pred),
/// content)`, so identical content anchored after *different* predecessors gets
/// *different* ids — the duplicate-token trap is closed.
fn seed_from(pred: AtomId) -> u64 {
    let mut h = DefaultHasher::new();
    0xD0C_5EEDu64.hash(&mut h);
    pred.0.hash(&mut h);
    h.finish()
}

/// Turn the token-level diff into the `Add`/`Delete`/`Connect` ops.
///
/// Walks the new-token stream. A matched (kept) token reuses its existing atom
/// id and advances the predecessor cursor. An unmatched (inserted) new token
/// mints a fresh atom — `Add` anchored after the current predecessor, with a
/// `Connect` from it to the successor chain so the insertion threads in — and
/// becomes the new predecessor (so a run of inserts chains, and identical
/// inserted tokens stay distinct). Current tokens not in the LCS are deleted.
pub(crate) fn diff_to_ops(
    cur_tokens: &[String],
    cur_ids: &[AtomId],
    new_tokens: &[String],
) -> Vec<Op> {
    let pairs = lcs_pairs(cur_tokens, new_tokens);

    // Which new-index is matched to which current-id (kept tokens).
    let mut kept_new_to_cur: Vec<Option<usize>> = vec![None; new_tokens.len()];
    let mut kept_cur: Vec<bool> = vec![false; cur_tokens.len()];
    for &(ci, nj) in &pairs {
        kept_new_to_cur[nj] = Some(ci);
        kept_cur[ci] = true;
    }

    let mut ops = Vec::new();

    // Deletes: every current token NOT in the LCS gets tombstoned.
    for (ci, kept) in kept_cur.iter().enumerate() {
        if !*kept {
            ops.push(Op::Delete { id: cur_ids[ci] });
        }
    }

    // Adds + Connects: walk the new stream, threading inserts after the running
    // predecessor and into the next kept successor.
    let mut pred = AtomId::ROOT;
    for (nj, token) in new_tokens.iter().enumerate() {
        match kept_new_to_cur[nj] {
            Some(ci) => {
                // A kept token: reuse the existing atom, advance the predecessor.
                pred = cur_ids[ci];
            }
            None => {
                // An inserted token: mint a fresh atom anchored after `pred`,
                // its id seeded by the predecessor so duplicates stay distinct.
                let id = AtomId::derive(seed_from(pred), token);
                ops.push(Op::Add {
                    id,
                    content: token.clone(),
                    after: pred,
                });
                // Thread into the successor chain: connect this new atom to the
                // next KEPT atom (the existing successor the insert lands before),
                // so the walk passes through the insert rather than around it.
                if let Some(next_id) = next_kept_after(nj, new_tokens, &kept_new_to_cur, cur_ids) {
                    ops.push(Op::Connect {
                        from: id,
                        to: next_id,
                    });
                }
                pred = id;
            }
        }
    }

    ops
}

/// The atom id of the first KEPT new-token after position `nj` — the existing
/// successor an insertion at `nj` must thread into. `None` if the insertion is at
/// the tail (no kept successor follows).
fn next_kept_after(
    nj: usize,
    new_tokens: &[String],
    kept_new_to_cur: &[Option<usize>],
    cur_ids: &[AtomId],
) -> Option<AtomId> {
    ((nj + 1)..new_tokens.len()).find_map(|k| kept_new_to_cur[k].map(|ci| cur_ids[ci]))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line_doc() -> Doc {
        Doc::new(Granularity::Line)
    }

    #[test]
    fn new_doc_is_empty() {
        let d = line_doc();
        assert_eq!(d.text(), "");
    }

    #[test]
    fn edit_from_empty_round_trips() {
        let mut d = line_doc();
        d.edit(Author(1), "hello world");
        assert_eq!(d.text(), "hello world");
    }

    #[test]
    fn edit_multiline_round_trips() {
        let mut d = line_doc();
        d.edit(Author(1), "one\ntwo\nthree\n");
        assert_eq!(d.text(), "one\ntwo\nthree\n");
    }

    #[test]
    fn insert_a_line_in_the_middle() {
        let mut d = line_doc();
        d.edit(Author(1), "one\nthree\n");
        d.edit(Author(1), "one\ntwo\nthree\n");
        assert_eq!(d.text(), "one\ntwo\nthree\n");
    }

    #[test]
    fn delete_a_line() {
        let mut d = line_doc();
        d.edit(Author(1), "one\ntwo\nthree\n");
        d.edit(Author(1), "one\nthree\n");
        assert_eq!(d.text(), "one\nthree\n");
    }

    #[test]
    fn insert_at_head_and_tail() {
        let mut d = line_doc();
        d.edit(Author(1), "middle\n");
        d.edit(Author(1), "top\nmiddle\nbottom\n");
        assert_eq!(d.text(), "top\nmiddle\nbottom\n");
    }

    #[test]
    fn edit_then_edit_sequence() {
        let mut d = line_doc();
        d.edit(Author(1), "a\nb\nc\n");
        d.edit(Author(1), "a\nB\nc\n"); // change middle line
        d.edit(Author(1), "a\nB\nc\nd\n"); // append
        d.edit(Author(1), "B\nc\nd\n"); // drop head
        assert_eq!(d.text(), "B\nc\nd\n");
    }

    // ── THE LOAD-BEARING TEST: duplicate-token survival ──────────────────────

    #[test]
    fn duplicate_tokens_are_distinct_atoms() {
        // "a b a" has the word "a" twice. AtomId::derive keys on (seed, content)
        // with no position, so a naive scheme would collapse both "a"s into one
        // atom — deleting the first would tombstone both. The predecessor-seeded
        // scheme keeps them distinct: deleting the FIRST "a" leaves the SECOND.
        let mut d = Doc::new(Granularity::Word);
        d.edit(Author(1), "a b a");
        assert_eq!(d.text(), "a b a");

        // Now delete the first "a": the new text is "b a".
        d.edit(Author(1), "b a");
        assert_eq!(d.text(), "b a", "the second 'a' SURVIVED — distinct atoms");
    }

    #[test]
    fn duplicate_tokens_survive_in_line_mode() {
        // The same trap one granularity up: a repeated line.
        let mut d = Doc::new(Granularity::Line);
        d.edit(Author(1), "x\ny\nx\n");
        d.edit(Author(1), "y\nx\n"); // drop the first "x"
        assert_eq!(d.text(), "y\nx\n");
    }

    #[test]
    fn three_identical_tokens_each_distinct() {
        let mut d = Doc::new(Granularity::Word);
        d.edit(Author(1), "go go go stop");
        d.edit(Author(1), "go go stop"); // drop one "go"
        assert_eq!(d.text(), "go go stop");
        d.edit(Author(1), "go stop"); // drop another
        assert_eq!(d.text(), "go stop");
    }

    // ── Word granularity + provenance ────────────────────────────────────────

    #[test]
    fn word_granularity_round_trips_and_edits() {
        let mut d = Doc::new(Granularity::Word);
        d.edit(Author(1), "the quick brown fox");
        assert_eq!(d.text(), "the quick brown fox");
        d.edit(Author(1), "the slow brown fox"); // replace one word
        assert_eq!(d.text(), "the slow brown fox");
        d.edit(Author(1), "the slow brown lazy fox"); // insert a word
        assert_eq!(d.text(), "the slow brown lazy fox");
    }

    #[test]
    fn inserted_atoms_carry_the_editing_author() {
        // Provenance flows: a word inserted by Author(7) is stamped with 7.
        let mut d = Doc::new(Granularity::Word);
        d.edit(Author(1), "alpha gamma");
        d.edit(Author(7), "alpha beta gamma"); // "beta " inserted by 7
        assert_eq!(d.text(), "alpha beta gamma");

        let g = d.history().replay();
        let beta = g
            .atoms()
            .find(|a| a.is_alive() && a.content == "beta ")
            .expect("the inserted 'beta ' atom exists");
        assert_eq!(
            beta.provenance.author,
            Author(7),
            "the inserted atom carries the editing author"
        );
        // And a KEPT word still carries its original author (not re-authored).
        let alpha = g
            .atoms()
            .find(|a| a.is_alive() && a.content == "alpha ")
            .expect("the kept 'alpha ' atom exists");
        assert_eq!(alpha.provenance.author, Author(1), "kept atoms keep author");
    }

    #[test]
    fn no_op_edit_keeps_text() {
        let mut d = line_doc();
        d.edit(Author(1), "stable\n");
        let pid = d.edit(Author(1), "stable\n"); // identical re-edit
        assert_eq!(d.text(), "stable\n");
        let _ = pid; // an empty patch; text is unchanged
    }

    #[test]
    fn full_replace_then_text() {
        let mut d = line_doc();
        d.edit(Author(1), "old line\n");
        d.edit(Author(1), "completely different\n");
        assert_eq!(d.text(), "completely different\n");
    }
}
