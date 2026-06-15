//! EXAMPLE deos app + end-to-end loop: a **doc cell** with `view`/`comment`/
//! `edit`/`admin` affordances, cap-gated, with two viewers that DIVERGE.
//!
//! This is the smallest thing that EXERCISES the deos app model (DEOS-APPS.md
//! §"the deos app model") on the framework's REAL bones and proves the loop:
//!
//!   1. **Define the app as affordances.** `doc_app()` declares an
//!      [`AffordanceSurface`] over a doc cell: four cap-gated affordances on the
//!      `Signature ⊂ Either ⊂ None` rights chain, each carrying a REAL
//!      [`dregg_turn::action::Effect`] (the turn the executor would run).
//!   2. **Register through `register(ctx)`.** The app registers its surface on a
//!      [`StarbridgeAppContext`] — alongside factories/inspectors — exactly as a
//!      starbridge-app's `register(ctx)` hook does.
//!   3. **Render via webgen.** The surface's descriptor renders to anti-drift JS
//!      (`AFFORDANCES`) the page reads — endpoints + required rights from the Rust
//!      source of truth.
//!   4. **Two viewers diverge (per-viewer projection).** Over the SAME surface, a
//!      viewer (Signature) sees `{view}`; an editor (Either) sees
//!      `{comment, edit, view}` — the deos confinement property, gated by the REAL
//!      `is_attenuation`.
//!   5. **Fire = a real verified turn.** Firing an authorized affordance through the
//!      HTTP endpoint executes the effect through the framework's [`EmbeddedExecutor`]
//!      and returns the executor's OWN receipt; an unauthorized fire is 403 and
//!      NOTHING executes (anti-ghost).
//!
//! The whole loop runs against the framework's genuine primitives — no parallel cap
//! model, no stub effect, the dispatch seam closed.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt; // oneshot

use dregg_app_framework::{
    AffordanceEndpoint, AffordanceSurface, AgentCipherclerk, AppCipherclerk, AuthRequired,
    CapabilityRef, CellAffordance, CellId, ConstantsModule, Effect, EmbeddedExecutor, Event,
    HELD_RIGHTS_HEADER, StarbridgeAppContext,
};

// ── the example app: a doc cell with four cap-gated affordances ───────────────

/// A real `EmitEvent` effect (the genuine turn for a view/comment — logs an
/// access/comment event onto the doc cell).
fn emit_event(cell: CellId) -> Effect {
    Effect::EmitEvent {
        cell,
        event: Event {
            topic: [7u8; 32],
            data: vec![],
        },
    }
}

/// A real `SetField` effect (the genuine turn for an edit — writes the doc body
/// slot).
fn set_body(cell: CellId) -> Effect {
    Effect::SetField {
        cell,
        index: 1,
        value: [42u8; 32],
    }
}

/// The stable recipient of the admin affordance's capability grant. The admin
/// grants a cap *to its own doc cell* (the implicit-authority own-cell-share case
/// the executor admits for a signed action) to this recipient, which the admin
/// test ensures exists in the ledger first.
fn admin_grant_recipient() -> CellId {
    CellId::derive_raw(&[99u8; 32], &[0u8; 32])
}

/// A real `GrantCapability` effect (the genuine turn for an admin grant): grant the
/// recipient `to` a capability over the doc cell `from` itself. `cap.target == from`
/// is the own-cell share — authorized by the doc owner's signature, so it executes
/// without the granter needing to pre-hold a cap for a third party.
fn grant_cap(from: CellId, to: CellId) -> Effect {
    Effect::GrantCapability {
        from,
        to,
        cap: CapabilityRef {
            target: from,
            slot: 0,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// The example deos app: a doc cell exposing {view, comment, edit, admin}.
///
/// Rights chain `Signature ⊂ Either ⊂ None`: view at the reader tier, comment+edit
/// at the editor tier, admin at the root tier. The doc cell is the agent's OWN cell
/// so the embedded ledger has it (fires actually execute).
fn doc_app(doc: CellId) -> AffordanceSurface {
    AffordanceSurface::named(doc, "doc")
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
            set_body(doc),
        ))
        .declare(CellAffordance::new(
            "admin",
            AuthRequired::None,
            grant_cap(doc, admin_grant_recipient()),
        ))
}

/// The app's `register(ctx)` hook — registers the doc affordance surface on the
/// shared context, exactly like a starbridge-app registers factories/inspectors.
fn register(ctx: &StarbridgeAppContext, doc: CellId) -> [u8; 32] {
    ctx.register_affordance_surface(doc_app(doc))
}

// ── helpers ───────────────────────────────────────────────────────────────────

fn agent() -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [11u8; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

async fn body_json(resp: axum::response::Response) -> serde_json::Value {
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    serde_json::from_slice(&bytes).unwrap_or(serde_json::Value::Null)
}

// ── 1+2: define + register through `register(ctx)` ────────────────────────────

#[test]
fn the_app_registers_its_affordance_surface_through_the_context() {
    let (cclerk, executor) = agent();
    let doc = cclerk.cell_id();
    let ctx = StarbridgeAppContext::new(cclerk, executor);

    let key = register(&ctx, doc);
    assert_eq!(
        key,
        *doc.as_bytes(),
        "the surface is keyed by its backing cell"
    );
    assert_eq!(ctx.affordance_registry().len(), 1);

    let surface = ctx.affordance_registry().get(&doc).expect("registered");
    assert_eq!(
        surface.all_names(),
        vec![
            "admin".to_string(),
            "comment".to_string(),
            "edit".to_string(),
            "view".to_string()
        ]
    );
}

// ── 3: render via webgen (anti-drift) ─────────────────────────────────────────

#[test]
fn webgen_renders_the_doc_surface_anti_drift() {
    let (cclerk, _executor) = agent();
    let doc = cclerk.cell_id();
    let surface = doc_app(doc);

    let js = ConstantsModule::new("doc-app")
        .slot("DOC_BODY_SLOT", 1)
        .affordance_surface(surface.descriptor("/doc-affordances"))
        .render_js();

    // The page reads AFFORDANCES.doc — endpoints + rights from the Rust source.
    assert!(js.contains("export const AFFORDANCES = Object.freeze("));
    assert!(js.contains("\"doc\": Object.freeze("));
    assert!(js.contains("name: \"edit\","));
    assert!(js.contains("requiredRights: \"Either\","));
    assert!(js.contains("effectKind: \"SetField\","));
    assert!(js.contains("fireEndpoint: \"/doc-affordances/fire/edit\","));
    assert!(js.contains("name: \"admin\","));
    assert!(js.contains("effectKind: \"GrantCapability\","));
    assert!(js.contains("fireEndpoint: \"/doc-affordances/fire/admin\","));
}

// ── 4+5: the HTTP loop — two viewers diverge; authorized fire executes a real
//    verified turn; unauthorized is refused (anti-ghost). ──────────────────────

fn endpoint_router(cclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> axum::Router {
    // Mount the endpoint router nested under its prefix, exactly as an app would via
    // `AppServer::nest("/doc-affordances", endpoint.router("/doc-affordances"))`.
    let doc = cclerk.cell_id();
    let endpoint = AffordanceEndpoint::new(doc_app(doc), cclerk.clone(), executor.clone());
    axum::Router::new().nest("/doc-affordances", endpoint.router("/doc-affordances"))
}

#[tokio::test]
async fn two_viewers_diverge_over_http() {
    let (cclerk, executor) = agent();

    // Viewer (Signature) sees only {view}.
    let viewer = endpoint_router(&cclerk, &executor)
        .oneshot(
            Request::get("/doc-affordances/projected")
                .header(HELD_RIGHTS_HEADER, "signature")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(viewer.status(), StatusCode::OK);
    let vv = body_json(viewer).await;
    assert_eq!(vv["visible"], serde_json::json!(["view"]));

    // Editor (Either) sees {comment, edit, view}.
    let editor = endpoint_router(&cclerk, &executor)
        .oneshot(
            Request::get("/doc-affordances/projected")
                .header(HELD_RIGHTS_HEADER, "either")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    let ev = body_json(editor).await;
    assert_eq!(
        ev["visible"],
        serde_json::json!(["comment", "edit", "view"])
    );

    // The two viewers genuinely DIVERGE over the SAME surface.
    assert_ne!(vv["visible"], ev["visible"]);
}

#[tokio::test]
async fn editor_fires_edit_as_a_real_verified_turn() {
    let (cclerk, executor) = agent();

    // The editor (Either) fires `edit` (req Either): authorized → executes the real
    // SetField turn through the embedded executor → the executor's OWN receipt.
    let resp = endpoint_router(&cclerk, &executor)
        .oneshot(
            Request::post("/doc-affordances/fire/edit")
                .header(HELD_RIGHTS_HEADER, "either")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(resp.status(), StatusCode::OK);
    let v = body_json(resp).await;
    assert_eq!(v["fired"], "edit");
    assert_eq!(v["action_count"], 1);
    // The actor is the agent; the receipt is the executor's own (non-zero turn_hash).
    assert_eq!(v["actor"], hex(cclerk.cell_id().as_bytes()));
    assert_ne!(v["turn_hash"].as_str().unwrap(), "0".repeat(64));
}

#[tokio::test]
async fn viewer_cannot_fire_edit_403_anti_ghost() {
    let (cclerk, executor) = agent();

    // The viewer (Signature) tries to fire `edit` (req Either): Signature ⊄ Either →
    // 403, REFUSED by the real gate, nothing executed.
    let resp = endpoint_router(&cclerk, &executor)
        .oneshot(
            Request::post("/doc-affordances/fire/edit")
                .header(HELD_RIGHTS_HEADER, "signature")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(resp.status(), StatusCode::FORBIDDEN);
}

#[tokio::test]
async fn admin_fires_admin_grant_cap_turn() {
    let (cclerk, executor) = agent();

    // The admin grant's recipient must exist in the ledger (you cannot grant a cap
    // to a nonexistent cell). Ensure it — this is real app setup, not a stub: the
    // GrantCapability effect that fires is the genuine one.
    let recipient = dregg_cell::Cell::new([99u8; 32], [0u8; 32]);
    assert_eq!(
        recipient.id(),
        admin_grant_recipient(),
        "recipient id derivation"
    );
    executor
        .ensure_cell(recipient)
        .expect("ensure recipient cell");

    // The admin (root / None) fires `admin` (req None): authorized → executes the
    // real GrantCapability turn through the embedded executor.
    let resp = endpoint_router(&cclerk, &executor)
        .oneshot(
            Request::post("/doc-affordances/fire/admin")
                .header(HELD_RIGHTS_HEADER, "root")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    assert_eq!(resp.status(), StatusCode::OK, "admin grant must execute");
    let v = body_json(resp).await;
    assert_eq!(v["fired"], "admin");
    assert_eq!(v["action_count"], 1);
}

/// A custom held-rights resolver proves the proof/cap boundary is pluggable: this
/// one ignores headers and always grants editor (Either) authority — standing in
/// for a resolver backed by the verified presentation. The gate is unchanged.
#[test]
fn the_held_rights_resolver_is_pluggable() {
    use dregg_app_framework::HeldRightsResolver;

    struct AlwaysEditor;
    impl HeldRightsResolver for AlwaysEditor {
        fn held(&self, _headers: &axum::http::HeaderMap) -> Option<AuthRequired> {
            Some(AuthRequired::Either)
        }
    }

    let (cclerk, executor) = agent();
    let doc = cclerk.cell_id();
    let _endpoint = AffordanceEndpoint::new(doc_app(doc), cclerk, executor)
        .with_resolver(Arc::new(AlwaysEditor))
        .router("/doc-affordances");
    // (Construction with a custom resolver compiles + builds the router; the gate
    // applied to the resolver's value is the same real is_attenuation.)
}

fn hex(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes.iter() {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
