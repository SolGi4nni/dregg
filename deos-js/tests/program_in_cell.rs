//! THE PROGRAM-IN-CELL WELD, PROVEN BY RUNNING: a deos-js applet is a PORTABLE
//! CELL-BLOB. Its program (affordances + view source) is stored IN the cell; a fresh
//! deos-js runtime loads the cell bytes, reconstitutes the applet from the stored
//! program, and fires an affordance — a REAL cap-gated verified turn on the LOADED cell.
//!
//! The chain proven here:
//!   (1) mint a counter applet from a manifest → its JS view source + affordance
//!       declarations are written into the cell's committed heap (the heap-blob storage);
//!   (2) `to_cell_bytes` serializes the whole cell (model + program) to a portable blob;
//!   (3) in a SEPARATE/fresh deos-js runtime, `from_cell` reads the program out of the
//!       cell, rebuilds the affordances, and stands a fresh executor over the loaded cell;
//!   (4) firing `inc` on the loaded applet advances the model AND leaves a real receipt;
//!   (5) the loaded program is the SAME program (same affordances, same view source).

use deos_js::js::{set_current_applet, take_current_applet};
use deos_js::portable::{read_program_blob, AppletManifest, PortableApplet, PROGRAM_COLL};
use deos_js::{AffordanceSpec, ApplyOp, JsRuntime};
use dregg_cell::AuthRequired;

/// The portable manifest of a "counter" applet: slot 0 is the count; `inc`/`dec` mutate
/// it (require Signature, which the driver holds); `reset` requires Proof (incomparable,
/// so the cap tooth refuses it). The `view_source` is the JS program text the applet
/// carries — a column of [the count, a +1 button] — stored verbatim in the cell.
fn counter_manifest() -> AppletManifest {
    let view_source = r#"
        deos.ui.vstack(
            deos.ui.text("Counter"),
            deos.ui.bind(function() { return app.get(0); }),
            deos.ui.button("+1", "inc", 1)
        )
    "#;
    AppletManifest {
        seed_fields: vec![(0usize, 0u64)],
        affordances: vec![
            AffordanceSpec {
                name: "inc".into(),
                required: AuthRequired::Signature,
                op: ApplyOp::AddToSlot { slot: 0 },
            },
            AffordanceSpec {
                name: "dec".into(),
                required: AuthRequired::Signature,
                op: ApplyOp::SubFromSlot { slot: 0 },
            },
            AffordanceSpec {
                name: "reset".into(),
                required: AuthRequired::Proof,
                op: ApplyOp::SetSlot { slot: 0, value: 0 },
            },
        ],
        held: AuthRequired::Signature,
        view_source: view_source.to_string(),
    }
}

/// Pure substance (no JS engine): mint a program-carrying cell, serialize it, load it in
/// a fresh applet, fire a verified turn — the whole load-and-run loop, proven by running.
#[test]
fn applet_program_is_a_portable_cell_blob() {
    let manifest = counter_manifest();

    // ── (1) MINT: the program is stored IN the cell (the heap blob). ────────────────
    let mut pk = [0u8; 32];
    pk[0] = 0xA7;
    let token = [0u8; 32];
    let mut origin = PortableApplet::mint(pk, token, &manifest);

    // Advance the ORIGINAL applet's model so we can prove the loaded blob carries the
    // PROGRAM, not the (later) model: load reconstitutes from the SOURCE, runs fresh.
    origin.fire("inc", 5).unwrap();
    origin.fire("inc", 2).unwrap(); // origin model = 7
    assert_eq!(origin.get_u64(0), 7);

    // The program blob really lives in the cell's committed heap (collection PROGRAM_COLL).
    let origin_cell = origin.ledger().get(&origin.cell()).expect("origin cell");
    assert!(
        origin_cell.state.get_heap(PROGRAM_COLL, 0).is_some(),
        "the program header leaf is present in the cell heap"
    );
    let blob = read_program_blob(origin_cell).expect("program blob reads back from the heap");
    let stored_size = blob.len();
    println!("stored counter program: {stored_size} bytes (in the cell's committed heap)");
    // The stored blob round-trips to the SAME manifest (the program survived the cell).
    let stored_manifest = AppletManifest::from_bytes(&blob).expect("blob parses to a manifest");
    assert_eq!(
        stored_manifest, manifest,
        "the cell carries the exact program manifest"
    );

    // ── (2) SERIALIZE the whole cell to a portable blob (model + program). ──────────
    let cell_bytes = PortableApplet::to_cell_bytes(&origin);
    println!("portable cell blob: {} bytes (model + program)", cell_bytes.len());
    assert!(!cell_bytes.is_empty());

    // ── (3) LOAD in a FRESH applet (a separate executor): reconstitute from the cell. ─
    let (mut loaded, loaded_manifest) =
        PortableApplet::from_cell(&cell_bytes).expect("load the applet from the cell blob");

    // (5) THE LOADED PROGRAM IS THE SAME PROGRAM: same affordances, same view source.
    assert_eq!(
        loaded_manifest, manifest,
        "the loaded program is byte-identical to the minted program (same affordances + view source)"
    );
    let mut loaded_aff_names: Vec<String> = loaded
        .affordance_specs()
        .into_iter()
        .map(|(n, _)| n)
        .collect();
    loaded_aff_names.sort();
    assert_eq!(
        loaded_aff_names,
        vec!["dec".to_string(), "inc".to_string(), "reset".to_string()],
        "the loaded applet exposes the SAME affordances"
    );
    // The loaded model is the cell's loaded state: the origin's count (7) traveled too.
    assert_eq!(
        loaded.get_u64(0),
        7,
        "the loaded cell carries the model state at serialization time"
    );
    // The loaded applet committed NO turns yet (fresh executor, fresh audit tape).
    assert_eq!(loaded.receipt_count(), 0, "a freshly-loaded applet has an empty audit tape");

    // ── (4) FIRE on the LOADED applet → a REAL cap-gated verified turn. ─────────────
    let receipt = loaded.fire("inc", 10).expect("the loaded program's inc fires a real turn");
    assert_ne!(receipt.receipt_hash(), [0u8; 32], "the loaded fire left a real receipt");
    assert_eq!(loaded.get_u64(0), 17, "the loaded model advanced (7 + 10) via a verified turn");
    assert_eq!(loaded.receipt_count(), 1, "exactly one verified turn committed on the loaded cell");

    // The cap tooth is INTACT on the loaded applet: `reset` requires Proof, the driver
    // holds Signature (incomparable) → REFUSED, nothing committed (anti-ghost).
    let refused = loaded.fire("reset", 0);
    assert!(
        matches!(refused, Err(deos_js::FireError::Unauthorized { .. })),
        "the loaded program's cap tooth still refuses the over-reach"
    );
    assert_eq!(loaded.get_u64(0), 17, "the refused turn changed nothing");
    assert_eq!(loaded.receipt_count(), 1, "the refused fire committed nothing (anti-ghost)");
}

/// THE LOAD-AND-RUN loop driven through a REAL SpiderMonkey runtime: load an applet from
/// a cell blob, install it as the runtime's applet, and drive its (loaded) affordances
/// from JS — the program ran from a cell-blob, witnessed by the engine.
#[test]
fn js_drives_an_applet_loaded_from_a_cell_blob() {
    // SpiderMonkey needs a large, thread-bound native stack (see the sibling spike test).
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(js_load_and_run_body)
        .expect("spawn big-stack JS thread")
        .join()
        .expect("JS load-and-run thread");
}

fn js_load_and_run_body() {
    let manifest = counter_manifest();

    // Mint + persist program in the cell, advance the model, serialize to a portable blob.
    let mut pk = [0u8; 32];
    pk[0] = 0xB8;
    let mut origin = PortableApplet::mint(pk, [0u8; 32], &manifest);
    origin.fire("inc", 3).unwrap(); // origin model = 3
    let cell_bytes = PortableApplet::to_cell_bytes(&origin);

    // FRESH RUNTIME, FRESH APPLET reconstituted from the cell bytes.
    let mut rt = JsRuntime::new().expect("boot SpiderMonkey");
    let (loaded, loaded_manifest) =
        PortableApplet::from_cell(&cell_bytes).expect("load applet from cell blob");
    // The view source the cell carried is the program text a renderer would run.
    assert!(
        loaded_manifest.view_source.contains("deos.ui.vstack"),
        "the loaded cell carries the JS view source"
    );
    set_current_applet(loaded);

    // Drive the LOADED program from JS: declare it by its (loaded) affordance names and
    // fire — a real verified turn on the loaded cell.
    let js = r#"
        var app = deos.applet({ affordances: ["inc", "dec", "reset"] });
        app.inc(4);            // loaded model 3 -> 7, a real turn
        app.fire("reset", 0);  // REFUSED (Proof vs held Signature): -1, no receipt
        app.get(0);            // witnessed read: 7
    "#;
    let result = rt.eval(js).expect("JS drives the loaded applet");
    assert_eq!(result, Some(7), "the loaded program advanced its model via a verified turn from JS");

    let driven = take_current_applet().expect("loaded applet present");
    assert_eq!(driven.get_u64(0), 7, "the loaded cell's model = 7 after the JS-driven turn");
    assert_eq!(
        driven.receipt_count(),
        1,
        "one verified turn committed (inc); the Proof-gated reset was refused — the cap tooth ran"
    );
    let last = driven.last_receipt().expect("a real receipt landed on the loaded cell");
    assert_ne!(last, [0u8; 32]);
    println!(
        "loaded-from-cell program fired a REAL turn; receipt: {}",
        last.iter().map(|b| format!("{b:02x}")).collect::<String>()
    );
}
