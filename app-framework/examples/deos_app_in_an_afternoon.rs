//! `deos_app_in_an_afternoon` — the composed deos app, end-to-end, runnable.
//!
//! `docs/deos/DEOS-APPS.md`'s promise made concrete: "a useful deos app in an
//! afternoon." This example builds a real composed [`DeosApp`] from a one-screen
//! spec, then narrates the WHOLE deos app model on it:
//!
//!   - the per-viewer affordance projection (a consumer, a publisher, the owner each
//!     see a DIFFERENT slice of the SAME feed);
//!   - a real verified-turn fire (a publish executes through the embedded executor;
//!     an unauthorized publish is refused — anti-ghost);
//!   - the interactive-tempo bridge (predict locally → settle at the boundary);
//!   - the web-of-cells publish (the feed cell becomes a `dregg://` sturdyref);
//!   - the rehydratable frustum-snapshot (a cold snapshot re-expands per-viewer,
//!     respecting the lattice, carrying its DERIVED liveness-type);
//!   - the generated `<dregg-affordance-surface>` web component (the htmx-on-crack
//!     surface the embedded servo web-surface mounts).
//!
//! Run it:
//!
//! ```sh
//! cargo run -p dregg-app-framework --example deos_app_in_an_afternoon            # narrate
//! cargo run -p dregg-app-framework --example deos_app_in_an_afternoon -- --serve # + HTTP
//! ```
//!
//! Without `--serve` it narrates and exits 0 (CI-friendly). With `--serve` it also
//! binds the composed router so you can `curl localhost:PORT/manifest` and open the
//! web component.

use dregg_app_framework::{
    AffordanceSpec, AgentCipherclerk, AppCipherclerk, AppSpec, AuthRequired, CapTpServer, CellSpec,
    DeosApp, EmbeddedExecutor, FederationId, Interaction, InteractionLog,
};

/// The app, declaratively — the builder writes THIS; the framework wires everything
/// else (verified state, the SDK surface, distribution, rehydration, the web surface).
fn feed_spec() -> AppSpec {
    AppSpec::new("afternoon-feed")
        .cell(
            CellSpec::new("feed")
                .affordance(AffordanceSpec::emit("consume", "signature", "consumed"))
                .affordance(AffordanceSpec::edit("publish", "either", 1))
                .affordance(AffordanceSpec::emit(
                    "grant_publisher",
                    "none",
                    "publisher-granted",
                ))
                .publish("signature"),
        )
        .discoverable(vec!["pubsub".into()])
}

#[tokio::main]
async fn main() {
    let serve = std::env::args().any(|a| a == "--serve");

    // The SDK surface: a cipherclerk + an embedded executor (the in-process verified
    // ledger). A captp server makes the feed cell publishable into the web-of-cells.
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0xAF; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let captp = CapTpServer::new(FederationId([0xAF; 32]));

    // The composition: the spec → a live DeosApp, with the web-of-cells server wired.
    // (`into_app` backs the sole cell with the agent's own cell so fires execute.)
    let app = {
        let base = feed_spec()
            .into_app(cclerk.clone(), executor.clone())
            .expect("the feed spec is valid");
        // Re-build with the captp server attached (so publish_all exports the feed).
        let feed = &base.cells()[0];
        DeosApp::builder("afternoon-feed", cclerk.clone(), executor.clone())
            .web_of_cells(captp)
            .discoverable(vec!["pubsub".into()])
            .cell(feed.clone())
            .build()
    };
    let feed = app.cells()[0].clone();
    let actor = cclerk.cell_id();

    println!("== {} — a composed deos app ==\n", app.name());

    // 1) The per-viewer projection: three tiers, three different feeds, ONE surface.
    println!("per-viewer projection (the same feed, gated by the REAL is_attenuation):");
    for (label, held) in [
        ("consumer (Signature)", AuthRequired::Signature),
        ("publisher (Either)", AuthRequired::Either),
        ("owner     (root)", AuthRequired::None),
    ] {
        let names = feed.surface().visible_names(&held);
        println!("  {label:<22} sees {names:?}");
    }
    println!();

    // 2) A real verified-turn fire (the publisher publishes) + the anti-ghost refusal.
    let fire = feed
        .predict_fire("publish", actor, &AuthRequired::Either)
        .expect("publisher predicts publish");
    println!(
        "optimistic publish (interactive tempo): predicted {:?}",
        fire.predicted_effect()
    );
    match fire.settle(feed.surface(), &cclerk, &executor) {
        s if s.is_confirmed() => {
            let r = s.receipt().unwrap();
            println!(
                "  settled at the boundary: CONFIRMED — turn {}…\n",
                hex8(&r.turn_hash)
            );
        }
        s => println!("  settled: ROLLED BACK ({s:?})\n"),
    }
    let refused = feed.predict_fire("publish", actor, &AuthRequired::Signature);
    println!(
        "a consumer firing publish: {} (anti-ghost — never executes)\n",
        if refused.is_err() {
            "REFUSED"
        } else {
            "??unexpectedly allowed"
        }
    );

    // 3) The web-of-cells: the feed cell becomes a dregg:// sturdyref.
    let uris = app.publish_all(100).await;
    println!("web-of-cells publish: {} sturdyref(s):", uris.len());
    for u in &uris {
        println!("  {u}");
    }
    println!();

    // 4) The rehydratable frustum-snapshot: a cold snapshot, re-expanded per-viewer.
    let log = InteractionLog::new().record(Interaction::witnessed_turn(feed.cell(), [9u8; 32]));
    let snap = feed.snapshot(log, /* sources_reachable */ false);
    println!(
        "frustum-snapshot of the feed (lineage {:?}, liveness: {}):",
        snap.lineage,
        snap.liveness().badge()
    );
    let consumer_view = feed.rehydrate(&snap, AuthRequired::Signature).unwrap();
    println!(
        "  a consumer rehydrates {:?} (the snapshot respects the lattice)",
        consumer_view.visible_names()
    );
    match feed.rehydrate(&snap, AuthRequired::Custom { vk_hash: [7u8; 32] }) {
        Err(_) => println!(
            "  an incomparable-identity viewer: CANNOT peek (membrane mints no projection)\n"
        ),
        Ok(_) => println!("  ??incomparable viewer unexpectedly rehydrated\n"),
    }

    // 5) The generated web component (the first line, as a witness it's real).
    let surface_js = dregg_app_framework::render_surface_component(&app);
    let first = surface_js.lines().nth(1).unwrap_or("");
    println!("web surface (`/surface.js`, a <dregg-affordance-surface> custom element):");
    println!("  {first}");
    println!(
        "  …{} bytes of htmx-on-crack web component\n",
        surface_js.len()
    );

    if serve {
        use dregg_app_framework::server::{AppConfig, AppServer};
        let config = AppConfig::default().with_listen("127.0.0.1:0");
        let addr = AppServer::new(config)
            .service_name("afternoon-feed")
            .with_health()
            .with_cors()
            .with_cipherclerk(cclerk)
            .with_embedded_executor(executor)
            .routes(app.mount())
            .serve_background()
            .await
            .expect("bind");
        println!("serving the composed surface on http://{addr}");
        println!("  try:  curl http://{addr}/manifest");
        println!("        curl -H 'x-dregg-held-rights: either' http://{addr}/feed/projected");
        println!("        curl http://{addr}/surface.js");
        println!("(ctrl-c to stop)");
        tokio::signal::ctrl_c().await.ok();
    } else {
        println!("(run with --serve to bind the composed router over HTTP)");
    }
}

fn hex8(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(16);
    for b in bytes.iter().take(8) {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
