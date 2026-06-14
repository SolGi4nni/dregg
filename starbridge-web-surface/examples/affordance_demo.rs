//! End-to-end demo of **cell affordances — htmx on crack + the frustum-snapshot**.
//! Run with:
//!
//! ```text
//! cd starbridge-web-surface && cargo run --example affordance_demo
//! # or, for a quiet self-check that exits 0/1:
//! cd starbridge-web-surface && cargo run --example affordance_demo -- --headless
//! ```
//!
//! `docs/deos/DEOS.md` — the deos interaction model, made into steel. In htmx an
//! element declares `hx-post="/x"` and the server returns a fragment; in deos a
//! **cell declares affordances** (named effect-templates) and an interaction is a
//! **capability-gated verified turn**. This shows, on the REAL dregg cap +
//! attestation + membrane primitives:
//!
//! (i)   a doc cell publishes an affordance-surface {view, comment, edit, admin};
//! (ii)  two agents with DIFFERENT caps `project_for` → see DIFFERENT affordance
//!       sets over the SAME surface (progressive enhancement → progressive
//!       ATTENUATION);
//! (iii) a frustum-snapshot is taken (tiny — a sturdyref + the culling boundary)
//!       and rehydrated by each agent → the per-viewer LIVE affordance surface,
//!       with its `Rehydration` liveness-type;
//! (iv)  firing an authorized affordance yields a verified-turn intent (a real
//!       `Effect`); firing an unauthorized one is REFUSED (the anti-ghost tooth).

use starbridge_web_surface::{
    rehydrate_affordances, AffordanceSnapshot, AffordanceSurface, AuthRequired, CellAffordance,
    CellId, DreggUri, Effect, EffectSummary, FireError, InteractionLog, Membrane, Rehydration,
    Sturdyref, SurfaceCapability, WebOfCells,
};

fn cid(b: u8) -> CellId {
    let mut k = [0u8; 32];
    k[0] = b;
    CellId::derive_raw(&k, &[0u8; 32])
}

/// Build a GENUINE, structurally-valid attestation to witness a `dregg://`
/// interaction — produced by actually publishing+fetching, so it is the REAL
/// `AttestedRoot` the web-of-cells emits (v4-complete + quorum), not a forged struct.
fn real_witness() -> starbridge_web_surface::AttestedRoot {
    let mut web = WebOfCells::new(3);
    let uri = web.publish(250, b"a witnessed turn", "dregg://witnessed");
    let (resource, _chrome) = web.fetch(&uri).expect("fetch resolves");
    assert!(resource.verify().is_ok());
    resource.attested_root
}

// ── the REAL effect-templates: the genuine turns the executor would run. ──

/// A read logs an access event (a real `EmitEvent` turn).
fn emit_event(cell: CellId) -> Effect {
    Effect::EmitEvent {
        cell,
        event: starbridge_web_surface::dregg_turn_reexport::Event {
            topic: [1u8; 32],
            data: vec![],
        },
    }
}

/// An edit writes a state field (a real `SetField` turn).
fn set_field(cell: CellId, index: usize) -> Effect {
    Effect::SetField {
        cell,
        index,
        value: [7u8; 32],
    }
}

/// An admin grant hands out a capability (a real `GrantCapability` turn).
fn grant_cap(from: CellId, to: CellId) -> Effect {
    Effect::GrantCapability {
        from,
        to,
        cap: starbridge_web_surface::dregg_turn_reexport::CapabilityRef {
            target: to,
            slot: 0,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// The canonical DOC-cell affordance surface: {view, comment, edit, admin} on the
/// clean three-tier rights chain `Signature ⊂ Either ⊂ None` — view at tier-1,
/// comment+edit at tier-2 (the editor tier), admin at tier-3 (root). Each carries a
/// REAL `dregg_turn::Effect` template.
fn doc_surface(doc: CellId, admin_grantee: CellId) -> AffordanceSurface {
    AffordanceSurface::new(doc)
        .declare(CellAffordance::new(
            "view",
            AuthRequired::Signature,
            emit_event(doc),
        ))
        .declare(CellAffordance::new(
            "comment",
            AuthRequired::Either,
            emit_event(doc),
        ))
        .declare(CellAffordance::new(
            "edit",
            AuthRequired::Either,
            set_field(doc, 1),
        ))
        .declare(CellAffordance::new(
            "admin",
            AuthRequired::None,
            grant_cap(doc, admin_grantee),
        ))
}

fn names(affs: &[CellAffordance]) -> Vec<String> {
    let mut n: Vec<String> = affs.iter().map(|a| a.name.clone()).collect();
    n.sort();
    n
}

fn main() {
    let headless = std::env::args().any(|a| a == "--headless");
    macro_rules! say {
        ($($t:tt)*) => { if !headless { println!($($t)*); } };
    }
    let mut ok = true;
    macro_rules! check {
        ($cond:expr, $msg:expr) => {
            if !($cond) {
                ok = false;
                eprintln!("SELF-CHECK FAILED: {}", $msg);
            }
        };
    }

    say!("== Cell affordances: htmx on crack + the frustum-snapshot ==\n");

    // ── (i) a doc cell publishes an affordance-surface. ───────────────────────
    say!("(i) a doc cell publishes an affordance-surface {{view, comment, edit, admin}}\n");

    let mut web = WebOfCells::new(3); // a 3-of-3 federation quorum
    let doc_body = b"<!doctype html><h1>a shared doc</h1><p>an interactive cell surface</p>";
    let uri = web.publish(10, doc_body, "dregg://doc");
    let doc = uri.cell;
    let admin_grantee = cid(99); // who an admin grant hands a cap to
    let surface = doc_surface(doc, admin_grantee);

    say!("    doc cell               : {}", uri.to_uri_string());
    say!("    declared affordances   : {:?}", surface.all_names());
    for a in &surface.affordances {
        say!(
            "      · {:<8} requires rights={:<10?} fires {:?}",
            a.name,
            a.required_rights,
            a.effect_summary()
        );
    }
    say!("    → each affordance is an effect-TEMPLATE: a REAL dregg_turn::Effect (the");
    say!("      turn the executor would run), cap-gated by the REAL is_attenuation.\n");
    check!(surface.all_names() == vec!["admin", "comment", "edit", "view"], "the surface declares all four affordances");
    // The effect-templates are genuine effects (not stubs).
    check!(matches!(surface.get("edit").unwrap().effect_template, Effect::SetField { .. }), "edit fires a real SetField");
    check!(matches!(surface.get("admin").unwrap().effect_template, Effect::GrantCapability { .. }), "admin fires a real GrantCapability");

    // ── (ii) two agents project_for → DIFFERENT affordance sets. ──────────────
    say!("(ii) two agents project_for the SAME surface → DIFFERENT affordance sets (progressive ATTENUATION)\n");

    // VIEWER holds tier-1 (Signature). EDITOR holds tier-2 (Either). ADMIN holds root (None).
    let viewer_held = SurfaceCapability::root(cid(20), AuthRequired::Signature);
    let editor_held = SurfaceCapability::root(cid(21), AuthRequired::Either);
    let admin_held = SurfaceCapability::root(cid(22), AuthRequired::None);

    let viewer_sees = surface.project_for(&viewer_held);
    let editor_sees = surface.project_for(&editor_held);
    let admin_sees = surface.project_for(&admin_held);

    say!("    VIEWER (holds Signature): sees {:?}", names(&viewer_sees));
    say!("    EDITOR (holds Either)   : sees {:?}", names(&editor_sees));
    say!("    ADMIN  (holds None/root): sees {:?}", names(&admin_sees));
    say!(
        "    → SAME surface, DIFFERENT affordance sets: viewer {} editor\n",
        if names(&viewer_sees) != names(&editor_sees) { "≠" } else { "==(BUG)" }
    );

    check!(names(&viewer_sees) == vec!["view"], "viewer sees only {view}");
    check!(names(&editor_sees) == vec!["comment", "edit", "view"], "editor sees {view, comment, edit}");
    check!(names(&admin_sees) == vec!["admin", "comment", "edit", "view"], "admin sees all four");
    check!(names(&viewer_sees) != names(&editor_sees), "the two viewers genuinely diverge");
    // progressive attenuation is MONOTONE: viewer ⊂ editor ⊂ admin.
    check!(names(&viewer_sees).iter().all(|n| names(&editor_sees).contains(n)), "viewer's set ⊂ editor's");
    check!(names(&editor_sees).iter().all(|n| names(&admin_sees).contains(n)), "editor's set ⊂ admin's");

    // ── (iii) a frustum-snapshot → rehydrate per-viewer to the live surface. ──
    say!("(iii) a frustum-snapshot (tiny — a sturdyref + the boundary) rehydrates PER-VIEWER\n");

    // The source context was confined: every external interaction was an attested
    // `dregg://` fetch → it will replay deterministically (sources gone).
    let witness = real_witness();
    let mut confined_log = InteractionLog::new();
    confined_log.record_attested_fetch(DreggUri::new(cid(60)), witness.clone());
    confined_log.record_attested_fetch(DreggUri::new(cid(61)), witness);

    // The publisher's authority lineage (root over the doc cell) + the sturdyref.
    let lineage = SurfaceCapability::root(doc, AuthRequired::None);
    let sturdyref = Sturdyref::new(uri, lineage, confined_log, /* sources_reachable */ false);

    // THE SNAPSHOT: tiny by construction — a sturdyref + the culling boundary
    // (cell + affordance NAMES), NOT the effect-templates, NOT any projection.
    let snapshot = AffordanceSnapshot::take(&surface, sturdyref);
    say!("    snapshot embeds        : a Sturdyref (the cap-handle) + the culling boundary");
    say!("    sturdyref ref          : {}", snapshot.sturdyref.uri.to_uri_string());
    say!("    boundary (the frustum) : {} affordance names {:?}",
        snapshot.boundary_extent(),
        snapshot.boundary.affordance_names
    );
    say!("    → the snapshot carries NO effect-templates and NO viewer projection:");
    say!("      it is tiny; the surface re-expands per-viewer at rehydration.\n");
    check!(snapshot.boundary_extent() == 4, "the boundary names all four affordances");
    check!(snapshot.boundary.affordance_names == surface.all_names(), "the boundary is the surface's names");

    // Each agent rehydrates the SAME snapshot through its OWN membrane → the
    // per-viewer live affordance surface + the liveness-type.
    let viewer_m = Membrane::new(viewer_held.clone());
    let editor_m = Membrane::new(editor_held.clone());

    let (viewer_live_aff, viewer_liveness) =
        rehydrate_affordances(&snapshot, &surface, &viewer_m, &web).expect("viewer rehydrates");
    let (editor_live_aff, editor_liveness) =
        rehydrate_affordances(&snapshot, &surface, &editor_m, &web).expect("editor rehydrates");

    say!("    VIEWER rehydrates      : live affordances {:?}", names(&viewer_live_aff));
    say!("      liveness-type        : {:?}  ({})", viewer_liveness, viewer_liveness.badge());
    say!("    EDITOR rehydrates      : live affordances {:?}", names(&editor_live_aff));
    say!("      liveness-type        : {:?}", editor_liveness);
    say!(
        "    → ONE snapshot, TWO different live interactive surfaces (the frustum-cull made real).\n"
    );

    check!(names(&viewer_live_aff) == vec!["view"], "viewer's re-expanded surface is {view}");
    check!(names(&editor_live_aff) == vec!["comment", "edit", "view"], "editor's re-expanded surface is {view, comment, edit}");
    check!(names(&viewer_live_aff) != names(&editor_live_aff), "the re-expansions diverge per-viewer");
    // the round-trip equals the direct projection.
    check!(names(&viewer_live_aff) == surface.visible_names(&viewer_held), "snapshot→rehydrate round-trips the viewer's set");
    check!(names(&editor_live_aff) == surface.visible_names(&editor_held), "snapshot→rehydrate round-trips the editor's set");
    // the liveness-type carries through (confined source → ReplayedDeterministic).
    check!(viewer_liveness == Rehydration::ReplayedDeterministic, "the confined source replays deterministically");
    check!(viewer_liveness.is_faithful(), "the carried liveness-type is faithful-by-construction");

    // ── (iv) firing: authorized → a verified-turn intent; unauthorized → REFUSED. ─
    say!("(iv) firing an affordance — authorized yields a verified-turn intent; unauthorized is REFUSED\n");

    // The EDITOR fires `edit` (authorized: Either ⊇ Either). → a real SetField turn.
    let edit_intent = surface
        .fire("edit", cid(21), &editor_held)
        .expect("editor fires edit (authorized)");
    say!("    EDITOR fires `edit`    : ADMITTED → verified-turn intent");
    say!("      actor                : the editor cell");
    say!("      effect (the turn)    : {:?}", edit_intent.effect_summary());
    say!("      → a REAL dregg_turn::Effect, ready to hand to the TurnExecutor (the seam).");
    check!(matches!(edit_intent.effect, Effect::SetField { .. }), "firing edit yields a real SetField turn");
    check!(edit_intent.effect_summary() == EffectSummary::SetField { cell: doc, index: 1 }, "the intent carries the doc's edit effect");

    // The VIEWER tries to fire `admin` (req None / root) — REFUSED (anti-ghost).
    let refused = surface.fire("admin", cid(20), &viewer_held);
    say!("    VIEWER fires `admin`   : {}",
        match &refused {
            Err(FireError::Unauthorized { required, .. }) =>
                format!("REFUSED (Unauthorized — needs rights={required:?}, viewer lacks them) ✓"),
            Err(e) => { ok = false; format!("WRONG ERROR: {e:?}") }
            Ok(_) => { ok = false; "WRONGLY ADMITTED (anti-ghost tooth FAILED)".to_string() }
        }
    );
    say!("      → the anti-ghost tooth: an unauthorized fire is refused by the SAME");
    say!("        is_attenuation gate, in-band — never an out-of-band role check.\n");
    check!(
        matches!(refused, Err(FireError::Unauthorized { ref required, .. }) if *required == AuthRequired::None),
        "the viewer's admin fire is refused (Unauthorized)"
    );
    // The viewer CAN fire what it holds (`view`) — yielding the real EmitEvent turn.
    let view_intent = surface.fire("view", cid(20), &viewer_held).expect("viewer fires view");
    check!(matches!(view_intent.effect, Effect::EmitEvent { .. }), "the viewer's authorized view fire yields a real EmitEvent turn");

    // ── (v) bonus — confinement before relation: an unattested scene yields NO surface. ─
    say!("(v) bonus — confinement before relation: an UNATTESTED scene re-expands to NOTHING (any caps)\n");

    let web2 = WebOfCells::new(3);
    let dead_cell = cid(80);
    let dead_surface = doc_surface(dead_cell, admin_grantee);
    let dead_ref = Sturdyref::new(
        DreggUri::new(dead_cell),
        SurfaceCapability::root(dead_cell, AuthRequired::None),
        InteractionLog::new(),
        false,
    );
    let dead_snapshot = AffordanceSnapshot::take(&dead_surface, dead_ref);
    let full = Membrane::new(SurfaceCapability::root(cid(41), AuthRequired::None)); // full authority
    let unattested = rehydrate_affordances(&dead_snapshot, &dead_surface, &full, &web2);
    say!("    full-authority viewer on a dead/unattested snapshot → {}",
        if unattested.is_err() { "NO interactive surface (the fetch did not verify) ✓" } else { "RE-EXPANDED (BUG)" }
    );
    check!(unattested.is_err(), "an unattested scene must yield NO interactive surface even with full caps");

    if ok {
        say!("\nOK — cell affordances run on the real dregg cap + attestation + membrane primitives:");
        say!("  · rendering an affordance is CAP-GATED by the REAL is_attenuation (required ⊆ held);");
        say!("  · firing one yields a verified-turn intent carrying a REAL dregg_turn::Effect;");
        say!("  · the frustum-snapshot is tiny and re-expands per-viewer through the membrane,");
        say!("    carrying the derived liveness-type — the dregg-only novelty made real.");
        // A loud, greppable success marker even in --headless.
        println!("affordance_demo: ALL CHECKS PASSED");
        std::process::exit(0);
    } else {
        eprintln!("affordance_demo: SELF-CHECK FAILURES — see above");
        std::process::exit(1);
    }
}
