//! **THE DRIVEN GAUNTLET** — the collaborative-document offering, exercised end to
//! end against the REAL substrate: open a document, several actors edit it (each
//! edit one genuine executor turn), a conflicting edit and an unauthorized edit are
//! REFUSED (non-vacuously — the same edit, made legally, lands), the document
//! reproduces from its edits under `verify()`, and a FORGED edit fails.
//!
//! Nothing here is a stub: every landed edit is a `dregg_turn::TurnExecutor::execute`
//! turn through `dregg_doc::ExecutorDrivenDoc` with a `Finality::Final` receipt, and
//! every refusal is either the executor's own in-band cap refusal or dregg-doc's own
//! conflict semantics.

use dregg_doc::{AtomId, Author, History, Op, Patch, PullRequest, Regime};
use dregg_turn::Finality;
use dreggnet_doc::{
    DocOffering, DocSession, FIELD_TITLE, Role, TURN_DELETE, TURN_INSERT, TURN_ORDER_CONFLICT,
    TURN_RESOLVE_TITLE, TURN_SET_TITLE,
};
use dreggnet_offerings::mock::{MockEvent, MockFrontend};
use dreggnet_offerings::{
    Action, DreggIdentity, Frontend, Offering, Outcome, RecordVerify, RunCost, SessionConfig,
    SessionId,
};

fn who(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

/// Open a document with a small crew: two editors (cap-holders) and one commenter
/// (no edit cap).
fn open_crew(off: &DocOffering) -> (DocSession, DreggIdentity, DreggIdentity, DreggIdentity) {
    let mut s = off
        .open(SessionConfig::with_seed(7))
        .expect("the doc opens");
    let (ann, bo, cyd) = (who("ann"), who("bo"), who("cyd"));
    s.invite(ann.clone(), Role::Editor);
    s.invite(bo.clone(), Role::Editor);
    s.invite(cyd.clone(), Role::Commenter);
    (s, ann, bo, cyd)
}

fn insert(text: &str, anchor: i64) -> Action {
    Action::new(text, TURN_INSERT, anchor, true)
}

fn landed(out: &Outcome) -> &dregg_turn::TurnReceipt {
    match out {
        Outcome::Landed { receipt, .. } => receipt,
        Outcome::Refused(why) => panic!("expected the edit to land, got Refused({why})"),
    }
}

fn refusal(out: &Outcome) -> &str {
    match out {
        Outcome::Refused(why) => why,
        Outcome::Landed { .. } => panic!("expected the edit to be REFUSED, but it landed"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. MULTI-ACTOR EDITING — each edit is a real, finalized executor turn.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn several_actors_edit_one_document_and_each_edit_is_a_real_finalized_turn() {
    let off = DocOffering::new();
    let (mut s, ann, bo, _cyd) = open_crew(&off);

    let genesis_commitment = s.commitment();

    // ANN opens the document (an insert at the start).
    let r1 = off.advance(&mut s, insert("The quorum ", 0), ann.clone());
    let rec1 = landed(&r1);
    assert_eq!(
        rec1.finality,
        Finality::Final,
        "driving through the real executor finalizes the receipt"
    );
    assert_ne!(
        rec1.pre_state_hash, rec1.post_state_hash,
        "the turn moved real ledger state"
    );
    assert!(rec1.action_count >= 1);
    assert_ne!(rec1.turn_hash, [0u8; 32]);

    // BO continues it (an insert at the tip — one live cell so far).
    let r2 = off.advance(&mut s, insert("is the referee.", 1), bo.clone());
    let rec2 = landed(&r2);
    assert_eq!(rec2.finality, Finality::Final);

    // ANN titles it (the single-valued field — the non-monotone fragment).
    let r3 = off.advance(
        &mut s,
        Action::new("Charter", TURN_SET_TITLE, 0, true),
        ann.clone(),
    );
    assert_eq!(landed(&r3).finality, Finality::Final);

    // THE DOCUMENT REFLECTS THEM.
    assert_eq!(s.text(), "The quorum is the referee.");
    assert_eq!(s.title(), vec!["Charter".to_string()]);
    assert_eq!(s.turns(), 3, "three real committed turns");
    assert_eq!(
        s.history().len(),
        3,
        "three patches in the document history"
    );
    assert_eq!(s.cells().len(), 2, "two live content cells");
    assert!(s.conflicts().is_empty(), "the shared document is clean");

    // The document's real commitment MOVED, and every edit's committed commitment
    // is distinct (a genuine chain, not a constant).
    assert_ne!(s.commitment(), genesis_commitment);
    let commits: Vec<[u8; 32]> = s.edits().iter().map(|e| e.doc_commitment).collect();
    assert_eq!(commits.len(), 3);
    assert_ne!(commits[0], commits[1]);
    assert_ne!(commits[1], commits[2]);
    assert_eq!(
        *commits.last().unwrap(),
        s.commitment(),
        "the last edit's commitment IS the document's commitment"
    );

    // Two distinct authors contributed (blame off content-addressed atoms).
    let contrib = s.contributions();
    assert_eq!(contrib.len(), 2, "two authors contributed live atoms");

    // Each edit is attributed to the actor who made it.
    assert_eq!(s.edits()[0].actor, ann);
    assert_eq!(s.edits()[1].actor, bo);

    // And the whole chain re-verifies.
    let report = off.verify(&s);
    assert!(report.verified, "the chain re-verifies: {}", report.detail);
    assert_eq!(report.turns, 3);
}

#[test]
fn a_delete_tombstones_a_cell_as_a_real_turn() {
    let off = DocOffering::new();
    let (mut s, ann, bo, _cyd) = open_crew(&off);

    assert!(
        off.advance(&mut s, insert("keep. ", 0), ann.clone())
            .landed()
    );
    assert!(off.advance(&mut s, insert("drop.", 1), bo.clone()).landed());
    assert_eq!(s.text(), "keep. drop.");

    // BO deletes their own cell (cell #2) — a monotone tombstone, one real turn.
    let out = off.advance(
        &mut s,
        Action::new("delete", TURN_DELETE, 2, true),
        bo.clone(),
    );
    assert_eq!(landed(&out).finality, Finality::Final);
    assert_eq!(s.text(), "keep. ", "the tombstoned cell left the content");
    assert_eq!(s.cells().len(), 1);
    assert_eq!(s.turns(), 3);
    assert!(off.verify(&s).verified);
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. THE CAP TOOTH — an unauthorized edit is refused BY THE EXECUTOR.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn an_edit_by_an_actor_without_the_region_edit_cap_is_refused_in_band_by_the_executor() {
    let off = DocOffering::new();
    let (mut s, ann, _bo, cyd) = open_crew(&off);

    assert!(
        off.advance(&mut s, insert("The quorum ", 0), ann.clone())
            .landed()
    );
    let before_text = s.text();
    let before_commit = s.commitment();
    let before_turns = s.turns();

    // CYD is a COMMENTER: her editor cell does not hold the document region's
    // c-list capability, so the executor's cross-cell permission gate refuses her
    // edit IN-BAND. Nothing commits.
    let refused = off.advance(&mut s, insert("is a suggestion.", 1), cyd.clone());
    let why = refusal(&refused);
    assert!(
        why.contains("CapabilityNotHeld"),
        "the refusal must be the executor's own cap refusal, got: {why}"
    );

    // ANTI-GHOST: the document is byte-untouched.
    assert_eq!(s.text(), before_text);
    assert_eq!(s.commitment(), before_commit);
    assert_eq!(s.turns(), before_turns, "no turn was recorded");
    assert_eq!(s.history().len(), 1, "no patch entered the history");

    // AN ACTOR WHO IS NOT ON THE ROSTER AT ALL — same gate, same refusal (the
    // executor sees a real editor cell with no capability; we do not pre-filter).
    let stranger = who("mallory");
    assert!(s.role_of(&stranger).is_none());
    let refused = off.advance(&mut s, insert("is a suggestion.", 1), stranger);
    assert!(refusal(&refused).contains("CapabilityNotHeld"));
    assert_eq!(s.turns(), before_turns);

    // NON-VACUOUS: the SAME edit, made by a cap-holding editor, LANDS.
    let out = off.advance(&mut s, insert("is a suggestion.", 1), ann.clone());
    assert_eq!(landed(&out).finality, Finality::Final);
    assert_eq!(s.text(), "The quorum is a suggestion.");
    assert!(off.verify(&s).verified);
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. THE DOC-SOUNDNESS TOOTH — a conflicting edit is refused.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn a_concurrent_edit_at_a_stale_anchor_is_refused_as_an_unresolved_prose_conflict() {
    let off = DocOffering::new();
    let (mut s, ann, bo, _cyd) = open_crew(&off);

    // ANN writes the opening; BO extends it at the tip (clean).
    assert!(
        off.advance(&mut s, insert("The quorum ", 0), ann.clone())
            .landed()
    );
    assert!(
        off.advance(&mut s, insert("is the referee.", 1), bo.clone())
            .landed()
    );
    let before_text = s.text();
    let before_commit = s.commitment();

    // BO now edits from a STALE base: he anchors after cell #1 ("The quorum "),
    // where ann's continuation already lives. The pushout of that is an ANTICHAIN —
    // two live, mutually-unordered alternatives at one position. The shared document
    // will not carry it: REFUSED, nothing commits.
    let refused = off.advance(&mut s, insert("is advisory.", 1), bo.clone());
    let why = refusal(&refused);
    assert!(
        why.contains("PROSE") && why.contains("conflict"),
        "the refusal must name the prose antichain, got: {why}"
    );

    // ANTI-GHOST.
    assert_eq!(s.text(), before_text);
    assert_eq!(s.commitment(), before_commit);
    assert_eq!(s.turns(), 2);
    assert!(s.conflicts().is_empty());

    // NON-VACUOUS: the SAME text by the SAME actor, re-anchored at the TIP, lands.
    let out = off.advance(&mut s, insert(" is advisory.", 2), bo.clone());
    assert_eq!(landed(&out).finality, Finality::Final);
    assert_eq!(s.text(), "The quorum is the referee. is advisory.");
    assert!(off.verify(&s).verified);
}

#[test]
fn a_second_differing_title_is_refused_as_a_field_authority_clash() {
    let off = DocOffering::new();
    let (mut s, ann, bo, _cyd) = open_crew(&off);

    assert!(
        off.advance(&mut s, insert("a doc", 0), ann.clone())
            .landed()
    );
    assert!(
        off.advance(
            &mut s,
            Action::new("Charter", TURN_SET_TITLE, 0, true),
            ann.clone()
        )
        .landed()
    );
    let before_commit = s.commitment();

    // BO assigns the SAME single-valued field a different value: not a benign
    // antichain but a CONSERVATION / AUTHORITY clash — the non-monotone boundary
    // dregg-doc's two-regime classifier says needs consensus. REFUSED.
    let refused = off.advance(
        &mut s,
        Action::new("Manifesto", TURN_SET_TITLE, 0, true),
        bo.clone(),
    );
    let why = refusal(&refused);
    assert!(
        why.contains("FIELD") && why.contains(FIELD_TITLE),
        "the refusal must name the field clash, got: {why}"
    );
    assert_eq!(s.title(), vec!["Charter".to_string()], "the title stands");
    assert_eq!(s.commitment(), before_commit);
    assert_eq!(s.turns(), 2);

    // NON-VACUOUS: a SUPERSEDING resolution (the settle-the-field patch) collapses
    // the assignment set and LANDS as a real turn — a conflict is settled by a
    // later patch, not by a merge failure.
    let out = off.advance(
        &mut s,
        Action::new("Manifesto", TURN_RESOLVE_TITLE, 0, true),
        bo.clone(),
    );
    assert_eq!(landed(&out).finality, Finality::Final);
    assert_eq!(s.title(), vec!["Manifesto".to_string()]);
    assert_ne!(s.commitment(), before_commit);
    assert!(off.verify(&s).verified);
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. CONFLICTS AS FIRST-CLASS STATE (the other policy) — carried, then resolved.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn a_prose_antichain_can_be_carried_as_first_class_state_and_resolved_by_a_later_patch() {
    // The dregg-doc doctrine face: a benign prose conflict is not a failure, it is a
    // STATE the document carries (with who wrote which alternative) until a later
    // patch orders it. A field clash is still refused (it needs consensus).
    let off = DocOffering::new().carrying_prose_conflicts();
    let (mut s, ann, bo, _cyd) = open_crew(&off);

    assert!(
        off.advance(&mut s, insert("The quorum ", 0), ann.clone())
            .landed()
    );
    assert!(
        off.advance(&mut s, insert("is the referee.", 1), ann.clone())
            .landed()
    );

    // BO edits from the stale base — and here the antichain COMMITS.
    let out = off.advance(&mut s, insert("is advisory.", 1), bo.clone());
    assert_eq!(landed(&out).finality, Finality::Final);

    let conflicts = s.conflicts();
    assert_eq!(conflicts.len(), 1, "one first-class conflict region");
    assert_eq!(conflicts[0].regime, Regime::Prose);
    assert_eq!(conflicts[0].alternatives.len(), 2);
    // Who wrote which alternative is a FACT (provenance off the atom).
    let authors: Vec<u64> = conflicts[0]
        .alternatives
        .iter()
        .map(|a| a.provenance.author.0)
        .collect();
    assert!(authors.contains(&1) && authors.contains(&2), "both authors");
    assert!(s.rendered().has_conflict());

    // The rest of the document is untouched and usable.
    assert!(s.text().starts_with("The quorum "));

    // A LATER PATCH RESOLVES IT: order the antichain into a chain (Op::Connect).
    let out = off.advance(
        &mut s,
        Action::new("order", TURN_ORDER_CONFLICT, 0, true),
        ann.clone(),
    );
    assert_eq!(landed(&out).finality, Finality::Final);
    assert!(
        s.conflicts().is_empty(),
        "the resolution patch collapsed the antichain: {}",
        s.text()
    );
    assert_eq!(s.turns(), 4);

    // The WHOLE chain — including the carried conflict and its resolution —
    // re-verifies.
    let report = off.verify(&s);
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.turns, 4);
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. VERIFY — the document reproduces from its edits; a forged edit fails.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn verify_re_drives_the_whole_edit_chain_and_a_forged_edit_fails() {
    let off = DocOffering::new();
    let (mut s, ann, bo, cyd) = open_crew(&off);

    assert!(
        off.advance(&mut s, insert("The quorum ", 0), ann.clone())
            .landed()
    );
    assert!(
        off.advance(&mut s, insert("is the referee.", 1), bo.clone())
            .landed()
    );
    assert!(
        off.advance(
            &mut s,
            Action::new("Charter", TURN_SET_TITLE, 0, true),
            ann.clone()
        )
        .landed()
    );

    // The authentic record re-verifies (the document reproduces from its edits).
    let record = off.export_record(&s);
    let ok = off.verify_record(&s, &record);
    assert!(
        ok.verified,
        "the authentic chain re-verifies: {}",
        ok.detail
    );
    assert_eq!(ok.turns, 3);

    // (a) A FORGED EDIT — the first edit's text is rewritten. The atom id is
    //     content-addressed, so the patch's effects, the turn, and the document's
    //     commitment all move: replay breaks.
    let mut forged = record.clone();
    forged.edits[0].patch = Patch::by(Author(1), [Patch::add(1, "The council ", AtomId::ROOT).1]);
    let broken = off.verify_record(&s, &forged);
    assert!(
        !broken.verified,
        "a forged edit must fail replay, got: {broken:?}"
    );

    // (b) A FORGED AUTHOR — the recorded edit is re-attributed to the commenter (who
    //     has no edit cap). The re-drive puts it through the SAME executor gate: the
    //     roster (not the record) decides who holds the cap, so it is refused → the
    //     chain does not re-drive.
    let mut forged = record.clone();
    forged.edits[1].actor = cyd.clone();
    let broken = off.verify_record(&s, &forged);
    assert!(
        !broken.verified,
        "an edit re-attributed to a non-cap-holder must fail"
    );

    // (c) A REORDERED CHAIN — the edits are swapped. The second edit anchored after
    //     the first's atom, which no longer exists at that point: the turn/effects/
    //     commitment do not reproduce.
    let mut forged = record.clone();
    forged.edits.swap(0, 1);
    let broken = off.verify_record(&s, &forged);
    assert!(!broken.verified, "a reordered chain must fail replay");

    // (d) A TAMPERED COMMITMENT — the record claims a document the edits do not
    //     produce.
    let mut forged = record.clone();
    forged.commitment = [0xAB; 32];
    let broken = off.verify_record(&s, &forged);
    assert!(!broken.verified, "a tampered final commitment must fail");

    // (e) A DROPPED EDIT — the chain is truncated but still claims the full
    //     document's commitment.
    let mut forged = record.clone();
    forged.edits.pop();
    let broken = off.verify_record(&s, &forged);
    assert!(
        !broken.verified,
        "a truncated chain must not reproduce the commitment"
    );

    // And the authentic record still verifies (the forgeries were on copies).
    assert!(off.verify(&s).verified);
}

// ─────────────────────────────────────────────────────────────────────────────
// 6. THE SURFACE — cap-gated affordances, and the frontend round-trip.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn the_surface_shows_the_cap_tooth_rather_than_hiding_it() {
    let off = DocOffering::new();
    let (mut s, ann, _bo, cyd) = open_crew(&off);
    assert!(
        off.advance(&mut s, insert("a line", 0), ann.clone())
            .landed()
    );

    // An EDITOR sees live affordances.
    let for_ann = off.actions_for(&s, Some(&ann));
    assert!(for_ann.iter().all(|a| a.enabled));
    assert!(for_ann.iter().any(|a| a.turn == TURN_INSERT));
    assert!(for_ann.iter().any(|a| a.turn == TURN_DELETE));

    // A COMMENTER sees the SAME affordances, DIMMED — the cap tooth shown, not
    // hidden. It is only a decoration: firing one still lands a real executor
    // refusal (proved in the cap test above).
    let for_cyd = off.actions_for(&s, Some(&cyd));
    assert_eq!(for_cyd.len(), for_ann.len());
    assert!(for_cyd.iter().all(|a| !a.enabled));

    // The rendered surface is a real deos view-tree naming the doc + its turns.
    let surface = off.render_for(&s, Some(&cyd));
    let painted = format!("{:?}", surface.view());
    assert!(
        painted.contains("a line"),
        "the document's text is on the surface"
    );
    assert!(painted.contains("Collaborators"));
    assert!(painted.contains("Verified edits"));
}

#[test]
fn a_frontend_presses_a_presented_affordance_and_it_lands_as_a_real_turn() {
    // The frontend-agnostic seam: a MockFrontend presents the offering's Surface +
    // Actions, a synthetic press is collected back into a typed Action, and the core
    // resolves it on the substrate. No Discord, no prose — the executor referees.
    let off = DocOffering::new();
    let mut fe = MockFrontend::new();
    let slot = SessionId::new("doc-thread-1");

    let mut s = off
        .open(SessionConfig::with_seed(11))
        .expect("the doc opens");
    // The frontend derives the identity; the session grants the cap to THAT identity.
    let ann = fe.identity("ann".to_string());
    s.invite(ann.clone(), Role::Editor);

    assert!(
        off.advance(&mut s, insert("keep. ", 0), ann.clone())
            .landed()
    );
    assert!(
        off.advance(&mut s, insert("drop.", 1), ann.clone())
            .landed()
    );

    fe.spin_session(slot.clone());
    fe.present(
        &slot,
        &off.render_for(&s, Some(&ann)),
        &off.actions_for(&s, Some(&ann)),
    );
    assert!(fe.is_open(&slot));

    // A press of the presented "delete cell #2" affordance.
    let ev = MockEvent::press(&slot, "ann", TURN_DELETE, 2);
    let (session_id, action, actor) = fe.collect(ev).expect("the affordance was presented");
    assert_eq!(session_id, slot);
    assert_eq!(actor, ann);

    let out = off.advance(&mut s, action, actor);
    assert_eq!(landed(&out).finality, Finality::Final);
    assert_eq!(s.text(), "keep. ");
    assert!(off.verify(&s).verified);
}

#[test]
fn the_offering_prices_an_edit_and_never_taxes_a_resolution() {
    let free = DocOffering::new();
    assert_eq!(free.price(&insert("x", 0)), RunCost::free());

    let paid = DocOffering::paid(2);
    assert_eq!(paid.price(&insert("x", 0)), RunCost::credits(2));
    assert_eq!(
        paid.price(&Action::new("t", TURN_SET_TITLE, 0, true)),
        RunCost::credits(2)
    );
    // Settling a conflict is FREE.
    assert_eq!(
        paid.price(&Action::new("t", TURN_RESOLVE_TITLE, 0, true)),
        RunCost::free()
    );
    assert_eq!(
        paid.price(&Action::new("order", TURN_ORDER_CONFLICT, 0, true)),
        RunCost::free()
    );
}

#[test]
fn an_ill_formed_edit_is_refused_without_reaching_the_executor() {
    let off = DocOffering::new();
    let (mut s, ann, _bo, _cyd) = open_crew(&off);

    // An unknown affordance verb.
    let refused = off.advance(&mut s, Action::new("x", "teleport", 0, true), ann.clone());
    assert!(refusal(&refused).contains("not a well-formed edit"));

    // An out-of-range anchor.
    let refused = off.advance(&mut s, insert("hi", 99), ann.clone());
    assert!(refusal(&refused).contains("not a well-formed edit"));

    // An empty span.
    let refused = off.advance(&mut s, insert("   ", 0), ann.clone());
    assert!(refusal(&refused).contains("not a well-formed edit"));

    assert_eq!(s.turns(), 0, "nothing committed");
    assert!(
        off.verify(&s).verified,
        "an empty document trivially verifies"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 7. THE FIXED WART, PINNED — a superseding resolution now LANDS through the PR
//    pushout on a fast-forward (dregg-doc's three_way now honors its base).
// ─────────────────────────────────────────────────────────────────────────────

/// A live single-document session is the FAST-FORWARD case: the new history is the
/// old history plus one patch. dregg-doc's `three_way` previously ignored its base,
/// so `PullRequest`'s pushout re-unioned the base's assignment that a *superseding*
/// `SetField` had collapsed — a resolution could NEVER land through the PR path on a
/// fast-forward. That is now FIXED upstream (three_way honors its base: the
/// superseding side is authoritative), so the resolution LANDS. (`dreggnet-doc`
/// still gates the live 1-patch edit on the FOLD with dregg-doc's conflict DETECTOR
/// — simplest for a fast-forward — but the PR path is now correct for this case too.)
#[test]
fn a_superseding_resolution_now_lands_through_the_pr_pushout_on_a_fast_forward() {
    let mut base = History::new();
    base.commit(Patch::by(
        Author(1),
        [Patch::add(1, "a doc", AtomId::ROOT).1],
    ));
    base.commit(Patch::by(
        Author(1),
        [Op::SetField {
            name: FIELD_TITLE.to_string(),
            value: "Charter".to_string(),
            superseding: false,
        }],
    ));

    // The head is the base plus ONE superseding resolution (a strict fast-forward).
    let mut head = base.branch();
    head.commit(Patch::by(
        Author(2),
        [Op::SetField {
            name: FIELD_TITLE.to_string(),
            value: "Manifesto".to_string(),
            superseding: true,
        }],
    ));

    // The FOLD of the head is clean — the supersede collapsed the assignment set.
    assert_eq!(
        head.replay()
            .field(FIELD_TITLE)
            .iter()
            .map(|a| a.value.clone())
            .collect::<Vec<_>>(),
        vec!["Manifesto".to_string()],
        "the fold of a superseding resolution is a single value"
    );

    // dregg-doc's three_way now honors its base, so the PR pushout LANDS the
    // superseding resolution instead of manufacturing a phantom clash.
    let pr = PullRequest::open(base, head);
    match pr.merge() {
        Ok(merged) => {
            assert!(
                !merged.patches.is_empty(),
                "the superseding resolution's patches landed through the PR path"
            );
        }
        Err(e) => panic!(
            "expected the fast-forward supersede to LAND through the fixed PR pushout, got {:?}",
            e
        ),
    }
}
