//! Thorough tests for the patch core.
//!
//! Coverage:
//! - apply round-trips (build content from patches; deletes tombstone; order
//!   follows the connect-edges; compose == sequential);
//! - **patch invertibility** (RCCS reversibility: `invert` round-trips an edit);
//! - **history as the content fold** (`replay` / `replay_to` time-travel;
//!   `branch` / `stitch` = the pushout into the shared document);
//! - **merge is total + commutative + associative + idempotent** (the pushout
//!   property), checked on disjoint, overlapping, and conflicting forks;
//! - a genuine prose conflict (two concurrent inserts at one position) becomes a
//!   first-class [`ConflictRegion`] with **provenance** — NOT a panic/failure;
//! - **the two-regime split**: a single-valued field clash is a `Regime::Field`
//!   conflict (needs consensus); a prose antichain is `Regime::Prose`;
//! - resolution patches collapse the antichain / the field clash (by ordering,
//!   by choosing, by settling a field), and the model is closed under its own
//!   conflicts.

use crate::*;

/// A two-atom document "Hello world" built from an empty doc, authored.
fn hello_world() -> (DocGraph, AtomId, AtomId) {
    let mut g = DocGraph::new();
    let (h, op_h) = Patch::add(1, "Hello ", AtomId::ROOT);
    let (w, op_w) = Patch::add(2, "world", h);
    Patch::by(Author(1), [op_h]).apply(&mut g);
    Patch::by(Author(1), [op_w]).apply(&mut g);
    (g, h, w)
}

// ── apply round-trips ────────────────────────────────────────────────────────

#[test]
fn apply_builds_linear_content() {
    let (g, _, _) = hello_world();
    assert_eq!(content(&g).to_marked_string(), "Hello world");
    assert!(!content(&g).has_conflict());
}

#[test]
fn empty_doc_renders_empty() {
    let g = DocGraph::new();
    assert_eq!(content(&g).to_marked_string(), "");
    assert_eq!(g.atom_count(), 1); // just ROOT
}

#[test]
fn delete_tombstones_not_removes() {
    let (mut g, h, w) = hello_world();
    let before = g.atom_count();
    Patch::from_ops([Op::Delete { id: w }]).apply(&mut g);
    assert_eq!(g.atom_count(), before, "tombstoned, not physically gone");
    assert_eq!(g.atom(w).unwrap().status, Status::Dead);
    assert_eq!(content(&g).to_marked_string(), "Hello ");
    let _ = h;
}

#[test]
fn delete_is_idempotent_and_monotone() {
    let (mut g, _, w) = hello_world();
    Patch::from_ops([Op::Delete { id: w }]).apply(&mut g);
    let once = g.clone();
    Patch::from_ops([Op::Delete { id: w }]).apply(&mut g);
    assert_eq!(g, once, "deleting twice == deleting once");
}

#[test]
fn add_is_idempotent_same_id() {
    let base = DocGraph::new();
    let (_id, op) = Patch::add(7, "x", AtomId::ROOT);
    let once = Patch::from_ops([op.clone()]).apply_to(&base);
    let twice = Patch::from_ops([op.clone(), op]).apply_to(&base);
    // Provenance differs (the 1-op and 2-op patches hash differently), but the
    // content-addressed *document* is the same: idempotence lives in
    // structural equality.
    assert!(
        once.structural_eq(&twice),
        "the same content-addressed add applied twice == once"
    );
}

#[test]
fn insert_in_the_middle() {
    let (mut g, h, w) = hello_world();
    let (b, op) = Patch::add(3, "big ", h);
    let mut p = Patch::from_ops([op]);
    p.push(Op::Connect { from: b, to: w });
    p.apply(&mut g);
    assert_eq!(content(&g).to_marked_string(), "Hello big world");
}

#[test]
fn compose_equals_sequential_apply() {
    let base = DocGraph::new();
    let p1 = Patch::from_ops([Patch::add(1, "a", AtomId::ROOT).1]);
    let aid = Patch::add(1, "a", AtomId::ROOT).0;
    let p2 = Patch::from_ops([Patch::add(2, "b", aid).1]);
    let composed = p1.compose(&p2).apply_to(&base);
    let sequential = p2.apply_to(&p1.apply_to(&base));
    // The composite patch and the two-step application produce the same
    // document (provenance differs since the composite is one patch).
    assert!(composed.structural_eq(&sequential));
}

#[test]
fn atoms_carry_provenance() {
    let mut g = DocGraph::new();
    let (h, op) = Patch::add(1, "hi", AtomId::ROOT);
    let p = Patch::by(Author(42), [op]);
    p.apply(&mut g);
    let a = g.atom(h).unwrap();
    assert_eq!(a.provenance.author, Author(42), "author recorded");
    assert_eq!(a.provenance.patch, p.id(), "authoring patch recorded");
}

// ── invertibility (RCCS reversibility) ───────────────────────────────────────

#[test]
fn invert_round_trips_an_add() {
    let base = hello_world().0;
    let w = hello_world().2;
    let p = Patch::by(Author(1), [Patch::add(9, " !", w).1]);
    let edited = p.apply_to(&base);
    assert_ne!(
        content(&edited).to_marked_string(),
        content(&base).to_marked_string()
    );
    let undone = p.invert().apply_to(&edited);
    // The added atom is dropped from the walk; content matches the pre-edit doc.
    assert_eq!(
        content(&undone).to_marked_string(),
        content(&base).to_marked_string(),
        "invert undoes the add"
    );
}

#[test]
fn invert_round_trips_a_delete() {
    let (base, _h, w) = hello_world();
    let p = Patch::by(Author(1), [Op::Delete { id: w }]);
    let deleted = p.apply_to(&base);
    assert_eq!(content(&deleted).to_marked_string(), "Hello ");
    let resurrected = p.invert().apply_to(&deleted);
    assert_eq!(
        content(&resurrected).to_marked_string(),
        "Hello world",
        "invert resurrects the tombstone"
    );
}

#[test]
fn invert_round_trips_a_field_set() {
    let base = DocGraph::new();
    let p = Patch::by(
        Author(1),
        [Op::SetField {
            name: "title".into(),
            value: "Draft".into(),
            superseding: false,
        }],
    );
    let set = p.apply_to(&base);
    assert_eq!(set.field("title").len(), 1);
    let undone = p.invert().apply_to(&set);
    assert_eq!(undone.field("title").len(), 0, "invert retracts the field");
}

// ── history: content = the patch fold; branch/stitch = the pushout ───────────

#[test]
fn history_replay_is_the_content_fold() {
    let mut h = History::new();
    h.commit(Patch::by(
        Author(1),
        [Patch::add(1, "Hello ", AtomId::ROOT).1],
    ));
    let hello = Patch::add(1, "Hello ", AtomId::ROOT).0;
    h.commit(Patch::by(Author(1), [Patch::add(2, "world", hello).1]));
    assert_eq!(content(&h.replay()).to_marked_string(), "Hello world");
    assert_eq!(h.len(), 2);
}

#[test]
fn replay_to_is_time_travel() {
    let mut h = History::new();
    let p1 = Patch::by(Author(1), [Patch::add(1, "Hello ", AtomId::ROOT).1]);
    let cursor1 = h.commit(p1);
    let hello = Patch::add(1, "Hello ", AtomId::ROOT).0;
    h.commit(Patch::by(Author(1), [Patch::add(2, "world", hello).1]));
    // Replaying only to the first patch shows the earlier state.
    assert_eq!(content(&h.replay_to(cursor1)).to_marked_string(), "Hello ");
    assert_eq!(content(&h.replay()).to_marked_string(), "Hello world");
}

#[test]
fn branch_then_stitch_is_the_pushout() {
    // Shared base, two authors branch and edit disjoint regions, then publish.
    let mut main = History::new();
    main.commit(Patch::by(
        Author(1),
        [Patch::add(1, "base", AtomId::ROOT).1],
    ));
    let base_atom = Patch::add(1, "base", AtomId::ROOT).0;

    let mut draft = main.branch();
    draft.commit(Patch::by(Author(2), [Patch::add(2, " +ext", base_atom).1]));

    // Stitch the draft into main = the merge of the two folds (the pushout).
    let merged = main.stitch(&draft);
    assert!(!content(&merged).has_conflict(), "disjoint stitch is clean");
    assert_eq!(content(&merged).to_marked_string(), "base +ext");
    // The shared history reproduces the published content.
    assert_eq!(content(&main.replay()).to_marked_string(), "base +ext");
}

// ── merge: the pushout property (total / commutative / associative / idempotent)

fn forks() -> (DocGraph, DocGraph, DocGraph) {
    let (base, h, w) = hello_world();
    let a = Patch::by(Author(1), [Patch::add(10, "!", w).1]).apply_to(&base);
    let (b_atom, b_op) = Patch::add(11, "there ", h);
    let mut bp = Patch::by(Author(2), [b_op]);
    bp.push(Op::Connect {
        from: b_atom,
        to: w,
    });
    let b = bp.apply_to(&base);
    let c = Patch::by(Author(3), [Op::Delete { id: w }]).apply_to(&base);
    (a, b, c)
}

#[test]
fn merge_is_total_on_every_fork_pair() {
    let (a, b, c) = forks();
    for (x, y) in [(&a, &b), (&a, &c), (&b, &c), (&a, &a)] {
        let m = merge(x, y);
        assert!(m.atom_count() >= 1);
        let _ = content(&m); // never panics, conflicted or not
    }
}

#[test]
fn merge_is_commutative() {
    let (a, b, c) = forks();
    assert_eq!(merge(&a, &b), merge(&b, &a));
    assert_eq!(merge(&a, &c), merge(&c, &a));
    assert_eq!(merge(&b, &c), merge(&c, &b));
}

#[test]
fn merge_is_associative() {
    let (a, b, c) = forks();
    assert_eq!(merge(&merge(&a, &b), &c), merge(&a, &merge(&b, &c)));
}

#[test]
fn merge_is_idempotent() {
    let (a, b, _) = forks();
    assert_eq!(merge(&a, &a), a);
    let m = merge(&a, &b);
    assert_eq!(merge(&m, &m), m);
    assert_eq!(merge(&m, &a), m);
}

#[test]
fn merge_all_is_order_independent() {
    let (a, b, c) = forks();
    let abc = merge_all([&a, &b, &c]);
    let cba = merge_all([&c, &b, &a]);
    let bca = merge_all([&b, &c, &a]);
    assert_eq!(abc, cba);
    assert_eq!(abc, bca);
}

#[test]
fn disjoint_edits_merge_clean() {
    let (base, h, w) = hello_world();
    let (p, pop) = Patch::add(20, "Oh, ", AtomId::ROOT);
    let mut pp = Patch::by(Author(1), [pop]);
    pp.push(Op::Connect { from: p, to: h });
    let left = pp.apply_to(&base);
    let right = Patch::by(Author(2), [Patch::add(21, "!", w).1]).apply_to(&base);
    let m = merge(&left, &right);
    assert!(
        !content(&m).has_conflict(),
        "disjoint edits do not conflict"
    );
    assert_eq!(content(&m).to_marked_string(), "Oh, Hello world!");
}

// ── prose conflict as a first-class STATE (with provenance) ──────────────────

/// Two authors append concurrently at the tail (after `w`) — a genuine 2-way
/// antichain with no pre-existing successor.
fn conflicting_merge() -> (DocGraph, AtomId, AtomId, AtomId) {
    let (base, _h, w) = hello_world();
    let a = Patch::by(Author(1), [Patch::add(30, " ALPHA", w).1]).apply_to(&base);
    let b = Patch::by(Author(2), [Patch::add(31, " BETA", w).1]).apply_to(&base);
    let alt_a = Patch::add(30, " ALPHA", w).0;
    let alt_b = Patch::add(31, " BETA", w).0;
    (merge(&a, &b), w, alt_a, alt_b)
}

#[test]
fn concurrent_inserts_become_a_conflict_region_not_a_panic() {
    let (m, _w, alt_a, alt_b) = conflicting_merge();
    let r = content(&m); // does not panic
    assert!(r.has_conflict(), "the merge carries a first-class conflict");
    let region = r.prose_conflicts().next().expect("one prose conflict");
    assert_eq!(region.regime, Regime::Prose);
    assert_eq!(
        region.alternatives.len(),
        2,
        "an antichain of two alternatives"
    );
    let heads = region.heads();
    assert!(heads.contains(&alt_a) && heads.contains(&alt_b));
    assert!(region.alternatives.iter().any(|a| a.text.contains("ALPHA")));
    assert!(region.alternatives.iter().any(|a| a.text.contains("BETA")));
}

#[test]
fn conflict_alternatives_carry_provenance() {
    // "who wrote which alternative" is a FACT (§3.5).
    let (m, _w, _a, _b) = conflicting_merge();
    let region = content(&m).prose_conflicts().next().unwrap().clone();
    let authors: Vec<Author> = region
        .alternatives
        .iter()
        .map(|a| a.provenance.author)
        .collect();
    assert!(authors.contains(&Author(1)), "ALPHA's author attributed");
    assert!(authors.contains(&Author(2)), "BETA's author attributed");
}

#[test]
fn conflicted_doc_is_still_usable_around_the_conflict() {
    let (m, _w, _a, _b) = conflicting_merge();
    let s = content(&m).to_marked_string();
    assert!(s.starts_with("Hello world"), "clean prefix: {s}");
    assert!(s.contains("prose"), "the contested region is marked: {s}");
}

#[test]
fn conflict_state_is_stable_under_remerge() {
    let (m, _w, _a, _b) = conflicting_merge();
    assert_eq!(merge(&m, &m), m);
    assert!(content(&merge(&m, &m)).has_conflict());
}

// ── the two-regime split: field clash is a REAL conflict ─────────────────────

#[test]
fn concurrent_field_writes_are_a_field_conflict_needing_consensus() {
    // Two authors set the canonical title differently => a non-monotone clash.
    let base = DocGraph::new();
    let a = Patch::by(
        Author(1),
        [Op::SetField {
            name: "title".into(),
            value: "Cats".into(),
            superseding: false,
        }],
    )
    .apply_to(&base);
    let b = Patch::by(
        Author(2),
        [Op::SetField {
            name: "title".into(),
            value: "Dogs".into(),
            superseding: false,
        }],
    )
    .apply_to(&base);
    let m = merge(&a, &b);
    assert_eq!(
        m.field("title").len(),
        2,
        "both assignments survive (a clash)"
    );
    let r = content(&m);
    let fc = r.field_conflicts().next().expect("a field conflict");
    assert_eq!(fc.regime, Regime::Field);
    assert!(
        fc.regime.needs_consensus(),
        "a field clash may need consensus"
    );
    assert_eq!(fc.field.as_deref(), Some("title"));
    // Both clashing values are attributed.
    let authors: Vec<Author> = fc
        .alternatives
        .iter()
        .map(|a| a.provenance.author)
        .collect();
    assert!(authors.contains(&Author(1)) && authors.contains(&Author(2)));
}

#[test]
fn same_field_value_does_not_conflict() {
    // The I-confluent case: both authors set the SAME value => no clash.
    let base = DocGraph::new();
    let mk = |auth| {
        Patch::by(
            Author(auth),
            [Op::SetField {
                name: "title".into(),
                value: "Same".into(),
                superseding: false,
            }],
        )
        .apply_to(&base)
    };
    let m = merge(&mk(1), &mk(2));
    assert_eq!(m.field("title").len(), 1, "identical value merges clean");
    assert!(!content(&m).has_conflict());
}

// ── resolution collapses the conflict ────────────────────────────────────────

#[test]
fn resolve_by_ordering_collapses_a_prose_conflict() {
    let (mut m, _w, _a, _b) = conflicting_merge();
    let heads = content(&m).prose_conflicts().next().unwrap().heads();
    assert_eq!(heads.len(), 2);
    resolve_connect(&heads).apply(&mut m); // resolution is JUST ANOTHER PATCH
    let r = content(&m);
    assert!(!r.has_conflict(), "ordering resolves the conflict");
    let s = r.to_marked_string();
    assert!(
        s.contains("ALPHA") && s.contains("BETA"),
        "both kept, linearized: {s}"
    );
}

#[test]
fn resolve_by_choosing_keeps_one_drops_the_other() {
    let (mut m, _w, _a, _b) = conflicting_merge();
    let region = content(&m).prose_conflicts().next().unwrap().clone();
    let keep = region
        .alternatives
        .iter()
        .find(|a| a.text.contains("ALPHA"))
        .unwrap()
        .head;
    let drop = region
        .alternatives
        .iter()
        .find(|a| a.text.contains("BETA"))
        .unwrap()
        .head;
    resolve_keep(keep, &[drop]).apply(&mut m);
    let r = content(&m);
    assert!(!r.has_conflict());
    let s = r.to_marked_string();
    assert!(
        s.contains("ALPHA") && !s.contains("BETA"),
        "kept ALPHA, dropped BETA: {s}"
    );
}

#[test]
fn resolve_field_settles_the_clash() {
    let base = DocGraph::new();
    let a = Patch::by(
        Author(1),
        [Op::SetField {
            name: "title".into(),
            value: "Cats".into(),
            superseding: false,
        }],
    )
    .apply_to(&base);
    let b = Patch::by(
        Author(2),
        [Op::SetField {
            name: "title".into(),
            value: "Dogs".into(),
            superseding: false,
        }],
    )
    .apply_to(&base);
    let mut m = merge(&a, &b);
    assert!(content(&m).has_conflict());
    // A settling authority chooses the canonical value.
    resolve_field(Author(99), "title", "Pets").apply(&mut m);
    assert_eq!(
        m.field("title").len(),
        1,
        "the clash collapses to one value"
    );
    assert_eq!(m.field("title")[0].value, "Pets");
    assert!(!content(&m).has_conflict());
}

#[test]
fn resolution_is_witnessed_by_remerge() {
    // The resolved graph re-merges with the conflicted one idempotently — the
    // resolution patch's edges are additive over the conflict union.
    let (m, _w, _a, _b) = conflicting_merge();
    let heads = content(&m).prose_conflicts().next().unwrap().heads();
    let resolved = resolve_connect(&heads).apply_to(&m);
    let remerged = merge(&m, &resolved);
    assert_eq!(remerged, resolved);
    assert!(!content(&remerged).has_conflict());
}

#[test]
fn concurrent_resolutions_yield_a_state_still() {
    // Two parties propose DIFFERENT orderings of the same antichain (a -> b AND
    // b -> a, a cycle). The union is total: content() must not panic, and the
    // result is still a first-class STATE (idempotent re-merge).
    let (m, _w, _a, _b) = conflicting_merge();
    let heads = content(&m).prose_conflicts().next().unwrap().heads();
    let res_ab = resolve_connect(&[heads[0], heads[1]]).apply_to(&m);
    let res_ba = resolve_connect(&[heads[1], heads[0]]).apply_to(&m);
    let both = merge(&res_ab, &res_ba);
    let _ = content(&both); // total even on a cyclic order
    assert_eq!(merge(&both, &both), both);
}

// ── conflict-as-state soundness: the commitment binds provenance ─────────────

/// A title-clash document used by the commitment tests.
fn title_clash() -> DocGraph {
    let base = DocGraph::new();
    let a = Patch::by(
        Author(1),
        [Op::SetField {
            name: "title".into(),
            value: "Cats".into(),
            superseding: false,
        }],
    )
    .apply_to(&base);
    let b = Patch::by(
        Author(2),
        [Op::SetField {
            name: "title".into(),
            value: "Dogs".into(),
            superseding: false,
        }],
    )
    .apply_to(&base);
    merge(&a, &b)
}

#[test]
fn commit_is_canonical_construction_order_independent() {
    // Building the SAME document two ways (merge order swapped) commits equal:
    // the BTree canonical ordering makes the commitment construction-independent.
    let base = DocGraph::new();
    let a = Patch::by(Author(1), [Patch::add(1, "Hello ", AtomId::ROOT).1]).apply_to(&base);
    let h = Patch::add(1, "Hello ", AtomId::ROOT).0;
    let b = Patch::by(Author(2), [Patch::add(2, "world", h).1]).apply_to(&base);
    let ab = merge(&a, &b);
    let ba = merge(&b, &a);
    assert_eq!(ab, ba, "fully equal (incl. provenance)");
    assert_eq!(commit(&ab), commit(&ba), "equal docs commit equal");
}

#[test]
fn commit_anti_forge_provenance() {
    // THE ANTI-FORGE TOOTH: a conflict whose alternatives render IDENTICALLY but
    // whose authorship is forged MUST change the commitment. A light client
    // cannot be shown a conflict that lies about who authored an alternative.
    let m = title_clash();
    let c0 = commit(&m);

    let mut forged = m.clone();
    forged.forge_field_provenance("title", "Dogs", Author(7)); // was Author(2)

    // The RENDER is byte-identical: same two values, same field.
    let render_eq = {
        let r0 = content(&m);
        let rf = content(&forged);
        let vals = |r: &Rendered| -> Vec<String> {
            r.field_conflicts()
                .flat_map(|c| c.alternatives.iter().map(|a| a.text.clone()))
                .collect()
        };
        // values render the same even though the author differs
        let mut a = vals(&r0);
        let mut b = vals(&rf);
        a.sort();
        b.sort();
        a == b
    };
    assert!(
        render_eq,
        "the forged conflict renders the same alternative values"
    );

    // ...but the commitment DIFFERS — the forge cannot hide under an equal render.
    assert_ne!(
        commit(&forged),
        c0,
        "forging an alternative's author changes the commitment"
    );
}

#[test]
fn commit_anti_forge_dropped_alternative() {
    // Hiding an alternative (dropping one side of the clash) also changes the
    // commitment — you cannot show a light client a "resolved" doc that secretly
    // dropped a co-author's value while claiming to be the same document.
    let m = title_clash();
    let c0 = commit(&m);

    let mut hidden = m.clone();
    hidden.drop_field_assignment("title", "Dogs");
    assert_eq!(hidden.field("title").len(), 1, "one alternative hidden");

    assert_ne!(
        commit(&hidden),
        c0,
        "dropping an alternative changes the commitment"
    );
}

#[test]
fn commit_binds_prose_alternative_provenance() {
    // The prose-conflict analogue: two concurrent inserts by different authors.
    // The commitment binds each atom's provenance, so swapping which author
    // wrote an alternative changes the commitment even at equal rendered text.
    let (m, _w, _a, _b) = conflicting_merge();
    let c0 = commit(&m);
    // Re-author the SAME document with the conflict alternatives' authors swapped
    // by rebuilding from the other side: a structurally-equal doc with different
    // provenance must NOT commit equal.
    let (base, _h, w) = hello_world();
    let a = Patch::by(Author(2), [Patch::add(30, " ALPHA", w).1]).apply_to(&base); // swapped author
    let b = Patch::by(Author(1), [Patch::add(31, " BETA", w).1]).apply_to(&base);
    let swapped = merge(&a, &b);
    assert!(
        swapped.structural_eq(&m),
        "same content/edges (structural), only provenance differs"
    );
    assert_ne!(
        commit(&swapped),
        c0,
        "provenance is bound: swapped authors -> different commitment"
    );
}

#[test]
fn commit_stable_under_remerge() {
    // The commitment of a conflicted doc is stable under idempotent re-merge
    // (the conflict is a STATE with a fixed commitment, not a transient).
    let m = title_clash();
    assert_eq!(commit(&merge(&m, &m)), commit(&m));
}

// ── blame / annotate (authorship that survives moves + merges) ───────────────

#[test]
fn blame_attributes_each_atom_to_its_real_author() {
    // Author(1) wrote "Hello ", Author(2) wrote "world".
    let mut g = DocGraph::new();
    let (h, op_h) = Patch::add(1, "Hello ", AtomId::ROOT);
    let (_w, op_w) = Patch::add(2, "world", h);
    Patch::by(Author(1), [op_h]).apply(&mut g);
    Patch::by(Author(2), [op_w]).apply(&mut g);

    let lines = blame(&g);
    assert_eq!(lines.len(), 2);
    assert_eq!(lines[0].content, "Hello ");
    assert_eq!(lines[0].author, Author(1));
    assert_eq!(lines[1].content, "world");
    assert_eq!(lines[1].author, Author(2));
    // Each line's patch is the real introducing patch (non-genesis).
    assert_ne!(lines[0].patch, PatchId::GENESIS);
    assert_ne!(lines[1].patch, PatchId::GENESIS);
}

#[test]
fn blame_does_not_reassign_on_a_middle_insert() {
    // THE CORRECTNESS PROPERTY. git-blame smears authorship when surrounding
    // text shifts; here the atom id is content-addressed and stable, so a third
    // author inserting in the MIDDLE leaves the original two atoms' blame exactly
    // where it was.
    let mut g = DocGraph::new();
    let (h, op_h) = Patch::add(1, "Hello ", AtomId::ROOT);
    let (w, op_w) = Patch::add(2, "world", h);
    Patch::by(Author(1), [op_h]).apply(&mut g);
    Patch::by(Author(2), [op_w]).apply(&mut g);

    let before = blame(&g);

    // Author(3) inserts "big " in the middle, threading the order
    // (after "Hello ", connected before "world") so it lands cleanly.
    let (big, op_big) = Patch::add(3, "big ", h);
    let mut p = Patch::by(Author(3), [op_big]);
    p.push(Op::Connect { from: big, to: w });
    p.apply(&mut g);

    let after = blame(&g);
    // The doc now reads "Hello big world" (the insert landed in the middle).
    assert_eq!(content(&g).to_marked_string(), "Hello big world");

    // The ORIGINAL two atoms keep their ids, content, AND authors — unmoved.
    let find = |b: &[BlameLine], a: AtomId| b.iter().find(|l| l.atom == a).cloned().unwrap();
    assert_eq!(find(&before, h).author, Author(1));
    assert_eq!(
        find(&after, h).author,
        Author(1),
        "middle insert did NOT reassign Hello"
    );
    assert_eq!(find(&before, w).author, Author(2));
    assert_eq!(
        find(&after, w).author,
        Author(2),
        "middle insert did NOT reassign world"
    );
    // The inserted atom is correctly the only one attributed to Author(3).
    assert!(after.iter().filter(|l| l.author == Author(3)).count() == 1);
    assert_eq!(
        after
            .iter()
            .find(|l| l.author == Author(3))
            .unwrap()
            .content,
        "big "
    );
}

#[test]
fn blame_summary_tallies_contributions() {
    let mut g = DocGraph::new();
    let (h, op_h) = Patch::add(1, "Hello ", AtomId::ROOT);
    let (w, op_w) = Patch::add(2, "world", h);
    let (_b, op_b) = Patch::add(3, " big", h);
    Patch::by(Author(1), [op_h]).apply(&mut g);
    Patch::by(Author(2), [op_w]).apply(&mut g);
    Patch::by(Author(1), [op_b]).apply(&mut g); // Author(1) again
    let _ = w;

    let tally = blame_summary(&g);
    assert_eq!(tally.get(&Author(1)), Some(&2), "Hello + big");
    assert_eq!(tally.get(&Author(2)), Some(&1), "world");
    assert_eq!(tally.get(&Author::SYSTEM), None, "ROOT is not counted");
}

#[test]
fn blame_attributes_both_conflict_alternatives() {
    // In a merge conflict, blame still attributes EACH atom (both alternatives)
    // to its real author — conflict is a state, not a blame-erasing event.
    let (m, _w, alt_a, alt_b) = conflicting_merge();
    let tally = blame_summary(&m);
    // " ALPHA" by Author(1), " BETA" by Author(2), plus the two clean atoms
    // (Hello / world) both by Author(1).
    assert_eq!(tally.get(&Author(1)), Some(&3));
    assert_eq!(tally.get(&Author(2)), Some(&1));
    // The alternative atoms carry their real authors on the graph.
    assert_eq!(m.atom(alt_a).unwrap().provenance.author, Author(1));
    assert_eq!(m.atom(alt_b).unwrap().provenance.author, Author(2));
}

// ── three-way / diff3 conflict view (BASE + OURS + THEIRS) ───────────────────

/// A common base "Hello world", forked into two branches that each replace the
/// tail differently — a genuine 3-way conflict over the tail position.
fn three_way_setup() -> (History, History, History) {
    let mut base = History::new();
    let (h, op_h) = Patch::add(1, "Hello ", AtomId::ROOT);
    let (w, op_w) = Patch::add(2, "world", h);
    base.commit(Patch::by(Author(1), [op_h]));
    base.commit(Patch::by(Author(1), [op_w]));

    // Both branches append concurrently after `w` (the ancestor's tail).
    let mut ours = base.branch();
    ours.commit(Patch::by(Author(1), [Patch::add(30, " ALPHA", w).1]));
    let mut theirs = base.branch();
    theirs.commit(Patch::by(Author(2), [Patch::add(31, " BETA", w).1]));
    (base, ours, theirs)
}

#[test]
fn merge_base_is_the_longest_common_prefix() {
    let (base, ours, theirs) = three_way_setup();
    let mb = merge_base(&ours, &theirs);
    assert_eq!(
        mb.patches(),
        base.patches(),
        "the shared prefix is exactly base"
    );
    assert_eq!(mb.len(), 2);
    // The merge base of identical histories is the whole history.
    assert_eq!(merge_base(&ours, &ours).patches(), ours.patches());
}

#[test]
fn render_three_way_shows_base_and_both_sides() {
    let (base, ours, theirs) = three_way_setup();
    let merged = three_way(&base, &ours, &theirs);
    assert!(content(&merged).has_conflict());

    let views = render_three_way(&merged, &base.replay());
    assert_eq!(views.len(), 1, "one three-way conflict over the tail");
    let v = &views[0];
    // BASE: the ancestor carried nothing after the tail (a concurrent insert).
    assert_eq!(v.base_text, "");
    // Both sides present, with their real authors and diverging text.
    assert_eq!(v.sides.len(), 2);
    assert!(
        v.sides
            .iter()
            .any(|s| s.author == Author(1) && s.text.contains("ALPHA"))
    );
    assert!(
        v.sides
            .iter()
            .any(|s| s.author == Author(2) && s.text.contains("BETA"))
    );
}

#[test]
fn render_three_way_recovers_nonempty_ancestor_text() {
    // A base whose tail atom is REPLACED on both branches (each tombstones the
    // ancestor's tail and adds its own after the head) — the BASE column then
    // recovers the ancestor's real content "world".
    let mut base = History::new();
    let (h, op_h) = Patch::add(1, "Hello ", AtomId::ROOT);
    let (w, op_w) = Patch::add(2, "world", h);
    base.commit(Patch::by(Author(1), [op_h]));
    base.commit(Patch::by(Author(1), [op_w]));

    let mut ours = base.branch();
    ours.commit(Patch::by(
        Author(1),
        [Op::Delete { id: w }, Patch::add(40, "Mars", h).1],
    ));
    let mut theirs = base.branch();
    theirs.commit(Patch::by(
        Author(2),
        [Op::Delete { id: w }, Patch::add(41, "Venus", h).1],
    ));

    let merged = three_way(&base, &ours, &theirs);
    assert!(content(&merged).has_conflict());
    let views = render_three_way(&merged, &base.replay());
    assert_eq!(views.len(), 1);
    // BASE recovers what the common ancestor had at the fork point after `h`.
    assert_eq!(views[0].base_text, "world");
    assert!(views[0].sides.iter().any(|s| s.text.contains("Mars")));
    assert!(views[0].sides.iter().any(|s| s.text.contains("Venus")));
}

#[test]
fn render_three_way_clean_merge_yields_no_conflicts() {
    // Disjoint edits at DIFFERENT, linearly-ordered positions: one branch
    // inserts between atom1 and atom2, the other between atom2 and atom3. The
    // two inserts are ordered (not concurrent), so the union linearizes cleanly
    // — NO three-way conflict entries.
    let mut base = History::new();
    let (a1, op1) = Patch::add(1, "one", AtomId::ROOT);
    let (a2, op2) = Patch::add(2, "two", a1);
    let (a3, op3) = Patch::add(3, "three", a2);
    base.commit(Patch::by(Author(1), [op1]));
    base.commit(Patch::by(Author(1), [op2]));
    base.commit(Patch::by(Author(1), [op3]));

    // Each insert threads the order (after the anchor, Connect-ed before the
    // anchor's existing successor) so it lands as an ordered middle-insert, not a
    // bare Add that leaves an antichain at the anchor.
    let (x, xop) = Patch::add(50, "X", a1); // between "one" and "two"
    let mut ours = base.branch();
    ours.commit(Patch::by(Author(1), [xop, Op::Connect { from: x, to: a2 }]));
    let (y, yop) = Patch::add(51, "Y", a2); // between "two" and "three"
    let mut theirs = base.branch();
    theirs.commit(Patch::by(Author(2), [yop, Op::Connect { from: y, to: a3 }]));

    let merged = three_way(&base, &ours, &theirs);
    assert!(
        !content(&merged).has_conflict(),
        "disjoint ordered edits merge clean"
    );
    assert!(render_three_way(&merged, &base.replay()).is_empty());
}
