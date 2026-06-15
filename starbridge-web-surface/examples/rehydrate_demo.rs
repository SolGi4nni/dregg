//! End-to-end demo of **rehydratable surfaces** — run with:
//!
//! ```text
//! cd starbridge-web-surface && cargo run --example rehydrate_demo
//! # or, for a quiet self-check that exits 0/1:
//! cd starbridge-web-surface && cargo run --example rehydrate_demo -- --headless
//! ```
//!
//! `docs/desktop-os-research/REHYDRATABLE-SURFACES.md`, made into steel. A dregg
//! "screenshot" is the present render of a certified compositor over a
//! witness-graph; what it embeds is a **sturdyref behind a membrane**; "opening" it
//! is the membrane-negotiated, per-viewer reacquisition of the witnessed state it
//! was always a certified projection of. This shows, on the REAL dregg cap +
//! attestation primitives:
//!
//! 1. **publish → sturdyref:** a surface is published into a real cell; the frame
//!    embeds a `Sturdyref` (a `dregg://` cap-handle + the publisher's authority
//!    lineage + the source context's witness-log).
//! 2. **per-viewer frustum:** two agents rehydrate the SAME sturdyref through
//!    membranes holding DIFFERENT caps → DIFFERENT projections (the frustum is
//!    re-derived per-viewer at the membrane from (their authority) ∧ (the graph's
//!    permitted projections)).
//! 3. **the anti-ghost tooth:** a reshare A→B→C that tries to AMPLIFY (C asks for
//!    more than B held) is REFUSED — the membrane re-applies the REAL
//!    `is_attenuation` per hop.
//! 4. **the liveness-type as a confinement readout:** a context whose fetches were
//!    all attested rehydrates `ReplayedDeterministic` ("everything went through the
//!    membrane"); one that touched ambient state gets `ReconstructedApproximate` —
//!    DERIVED from the witness-log, not hand-set.

use std::collections::BTreeSet;

use starbridge_web_surface::{
    rehydrate, AttestedRoot, AuthRequired, CellId, DreggUri, InteractionLog, Membrane,
    RehydrateError, Rehydration, Sturdyref, SurfaceCapability, WebOfCells,
};

fn cid(b: u8) -> CellId {
    let mut k = [0u8; 32];
    k[0] = b;
    CellId::derive_raw(&k, &[0u8; 32])
}

fn origins(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|s| s.to_string()).collect()
}

/// Build a GENUINE, structurally-valid attestation to use as a witness for a
/// witnessed `dregg://` interaction — produced by actually publishing+fetching, so
/// it is the REAL `AttestedRoot` the web-of-cells emits (v4-complete + quorum), not
/// a hand-forged struct.
fn real_witness() -> AttestedRoot {
    let mut web = WebOfCells::new(3);
    let uri = web.publish(250, b"a witnessed turn", "dregg://witnessed");
    let (resource, _chrome) = web.fetch(&uri).expect("fetch resolves");
    assert!(resource.verify().is_ok());
    resource.attested_root
}

fn main() {
    let headless = std::env::args().any(|a| a == "--headless");
    macro_rules! say {
        ($($t:tt)*) => { if !headless { println!($($t)*); } };
    }

    // Track failures so --headless can exit non-zero, while a narrated run still
    // shows every scene.
    let mut ok = true;
    macro_rules! check {
        ($cond:expr, $msg:expr) => {
            if !($cond) {
                ok = false;
                eprintln!("SELF-CHECK FAILED: {}", $msg);
            }
        };
    }

    say!("== Rehydratable surfaces: a sturdyref behind a membrane ==\n");

    // ── (i) publish a surface → get a sturdyref. ──────────────────────────────
    say!("(i) publish a surface → a sturdyref (the cap-handle the 'screenshot' embeds)\n");

    let mut web = WebOfCells::new(3); // a 3-of-3 federation quorum
    let scene_body = b"<!doctype html><h1>a rehydratable scene</h1><p>served from a dregg cell</p>";
    let uri = web.publish(10, scene_body, "dregg://scene");

    // The publisher's authority lineage: the surface the frame was a certified
    // projection of. It permits two origins (a + b) under read-only `Signature`
    // rights. Every viewer's projection is re-derived as an attenuation of THIS.
    let lineage = SurfaceCapability::scoped(
        uri.cell,
        AuthRequired::Either,
        origins(&["https://a.example.com", "https://b.example.com"]),
        [],
    );

    // The source context's witness-log: every external interaction it made was a
    // `dregg://` attested fetch (witnessed) — so it is the confined fragment.
    let witness = real_witness();
    let mut confined_log = InteractionLog::new();
    confined_log.record_attested_fetch(DreggUri::new(cid(60)), witness.clone());
    confined_log.record_attested_fetch(DreggUri::new(cid(61)), witness);

    // The sturdyref: handed to someone cold, it re-establishes the connection. The
    // sources are GONE (sessions ended) → it will replay/reconstruct, not reconnect.
    let sturdyref = Sturdyref::new(
        uri,
        lineage.clone(),
        confined_log,
        /* sources_reachable */ false,
    );

    say!(
        "    published link        : {}",
        sturdyref.uri.to_uri_string()
    );
    say!(
        "    lineage permits       : {{a, b}} under rights={:?}",
        sturdyref.lineage.window.rights
    );
    say!(
        "    witness-log           : {} interactions, {} ambient (fully confined)",
        sturdyref.witness_log.len(),
        sturdyref.witness_log.ambient_count()
    );
    say!(
        "    derived liveness      : {:?}  ({})\n",
        sturdyref.liveness(),
        sturdyref.liveness().badge()
    );
    check!(
        sturdyref.liveness() == Rehydration::ReplayedDeterministic,
        "a fully-confined, sources-gone sturdyref must derive ReplayedDeterministic"
    );

    // ── (ii) two agents rehydrate it → DIFFERENT per-viewer projections. ──────
    say!("(ii) two agents rehydrate the SAME sturdyref → DIFFERENT projections (per-viewer frustum)\n");

    // Agent ALICE holds {a} only. Agent BOB holds {b} only.
    let alice = Membrane::new(SurfaceCapability::scoped(
        cid(20),
        AuthRequired::Either,
        origins(&["https://a.example.com"]),
        [],
    ));
    let bob = Membrane::new(SurfaceCapability::scoped(
        cid(21),
        AuthRequired::Either,
        origins(&["https://b.example.com"]),
        [],
    ));

    let pa = rehydrate(&sturdyref, &alice, &web).expect("alice rehydrates");
    let pb = rehydrate(&sturdyref, &bob, &web).expect("bob rehydrates");

    say!("    ALICE (holds {{a}}):");
    say!(
        "      may fetch a.example.com? {}",
        pa.surface.may_fetch("https://a.example.com")
    );
    say!(
        "      may fetch b.example.com? {}  (NOT in her caps)",
        pa.surface.may_fetch("https://b.example.com")
    );
    say!("      origin badge          : {}", pa.chrome.badge());
    say!("      liveness              : {:?}", pa.liveness);
    say!("    BOB   (holds {{b}}):");
    say!(
        "      may fetch a.example.com? {}  (NOT in his caps)",
        pb.surface.may_fetch("https://a.example.com")
    );
    say!(
        "      may fetch b.example.com? {}",
        pb.surface.may_fetch("https://b.example.com")
    );
    say!(
        "    → SAME sturdyref, DIFFERENT projections: {}\n",
        pa.surface != pb.surface
    );

    check!(
        pa.surface != pb.surface,
        "two different-cap viewers must get different projections"
    );
    check!(
        pa.surface.may_fetch("https://a.example.com")
            && !pa.surface.may_fetch("https://b.example.com"),
        "alice's frustum is {a}"
    );
    check!(
        pb.surface.may_fetch("https://b.example.com")
            && !pb.surface.may_fetch("https://a.example.com"),
        "bob's frustum is {b}"
    );
    check!(
        pa.surface.cell() == Some(sturdyref.uri.cell)
            && pb.surface.cell() == Some(sturdyref.uri.cell),
        "both projections are bound to the SAME origin cell"
    );

    // ── (iii) a reshare A→B→C that tries to AMPLIFY is REFUSED. ───────────────
    say!("(iii) a reshare chain A→B→C — an amplifying reshare is REFUSED (the is_attenuation tooth)\n");

    // A holds {a, b}. A reshares to B narrowing to {a} (admitted). B tries to
    // reshare to C amplifying back to {a, b} (refused — C cannot exceed what B held).
    let a_membrane = Membrane::new(SurfaceCapability::scoped(
        cid(30),
        AuthRequired::Either,
        origins(&["https://a.example.com", "https://b.example.com"]),
        [],
    ));
    say!("    A holds {{a, b}}");

    let b_membrane = a_membrane
        .reshare(SurfaceCapability::scoped(
            cid(31),
            AuthRequired::Either,
            origins(&["https://a.example.com"]),
            [],
        ))
        .expect("A→B (narrow to {a}) is admitted");
    say!("    A→B  narrow to {{a}}                       → ADMITTED");

    // B→C amplify back to {a, b}: REFUSED.
    let amplify = b_membrane.reshare(SurfaceCapability::scoped(
        cid(32),
        AuthRequired::Either,
        origins(&["https://a.example.com", "https://b.example.com"]),
        [],
    ));
    say!(
        "    B→C  try to amplify back to {{a, b}}       → {}",
        match &amplify {
            Err(RehydrateError::Amplification) => "REFUSED (Amplification) ✓",
            Err(e) => {
                ok = false;
                eprintln!("expected Amplification, got {e:?}");
                "WRONG ERROR"
            }
            Ok(_) => {
                ok = false;
                eprintln!("an amplifying reshare must be refused");
                "WRONGLY ADMITTED"
            }
        }
    );
    check!(
        amplify == Err(RehydrateError::Amplification),
        "B→C amplification must be refused"
    );

    // B→C narrowing further to {} is admitted (attenuation always may narrow).
    let c_membrane = b_membrane
        .reshare(SurfaceCapability::scoped(
            cid(33),
            AuthRequired::Either,
            origins(&[]),
            [],
        ))
        .expect("B→C (narrow to {}) is admitted");
    say!("    B→C  narrow to {{}}                        → ADMITTED");
    say!(
        "    → C may fetch a.example.com? {} (narrowed to nothing by the chain)\n",
        c_membrane.held().may_fetch("https://a.example.com")
    );
    check!(
        !c_membrane.held().may_fetch("https://a.example.com"),
        "the narrowed chain leaves C with nothing"
    );

    // ── (iv) the liveness-type reads out confinement on both polarities. ──────
    say!("(iv) the liveness-type reads out CONFINEMENT (derived from witnessed-vs-ambient)\n");

    // A CONFINED context: every interaction was a `dregg://` attested fetch.
    let witness = real_witness();
    let mut confined = InteractionLog::new();
    confined.record_attested_fetch(DreggUri::new(cid(70)), witness.clone());
    confined.record_attested_fetch(DreggUri::new(cid(71)), witness.clone());
    let confined_liveness = Rehydration::classify(&confined, /* sources_reachable */ false);
    say!(
        "    confined context  ({} interactions, {} ambient): {:?}",
        confined.len(),
        confined.ambient_count(),
        confined_liveness
    );
    say!("      → {}", confined_liveness.badge());
    check!(
        confined_liveness == Rehydration::ReplayedDeterministic,
        "a confined context derives ReplayedDeterministic"
    );

    // A LEAKY context: one interaction reached outside the membrane (ambient).
    let mut leaky = InteractionLog::new();
    leaky.record_attested_fetch(DreggUri::new(cid(72)), witness); // witnessed
    leaky.record_ambient("raw fetch https://ad-network.example  (NOT through the membrane)");
    let leaky_liveness = Rehydration::classify(&leaky, /* sources_reachable */ false);
    say!(
        "    leaky context     ({} interactions, {} ambient): {:?}",
        leaky.len(),
        leaky.ambient_count(),
        leaky_liveness
    );
    say!("      → {}", leaky_liveness.badge());
    check!(
        leaky_liveness == Rehydration::ReconstructedApproximate,
        "a context that touched ambient state derives ReconstructedApproximate"
    );
    check!(
        !leaky_liveness.is_faithful(),
        "the reconstructed liveness is the honest 'not the same' signal"
    );

    say!(
        "\n    → ReplayedDeterministic == \"everything this context did went through the membrane\";"
    );
    say!("      the enum is a DERIVED confinement metric, not a hand-set label.\n");

    // ── confinement-before-relation: an unattested scene yields NO projection. ─
    say!("(v) bonus — confinement before relation: an UNVERIFIED scene yields NO projection (any caps)\n");

    // A sturdyref into a cell that was never published (a dead `dregg://` ref): the
    // fetch is a VERIFIED turn, so it fails BEFORE any projection is minted. A
    // viewer with FULL authority (None) still gets nothing — confinement (the fetch
    // must verify) comes before relation (the per-viewer projection).
    let web2 = WebOfCells::new(3);
    let dead_uri = DreggUri::new(cid(40));
    let dead_ref = Sturdyref::new(
        dead_uri.clone(),
        SurfaceCapability::root(dead_uri.cell, AuthRequired::Either),
        InteractionLog::new(),
        false,
    );
    let full = Membrane::new(SurfaceCapability::root(cid(41), AuthRequired::None));
    let unverified = rehydrate(&dead_ref, &full, &web2);
    say!("    full-authority viewer on a dead/unverified ref → {unverified:?}");
    check!(
        matches!(unverified, Err(RehydrateError::Fetch(_))),
        "an unverified scene must yield NO projection even with full caps"
    );

    if ok {
        say!("\nOK — rehydratable surfaces run on the real dregg cap + attestation primitives:");
        say!("  · the membrane composes the REAL is_attenuation per hop (proven lattice);");
        say!("  · the liveness-type is DERIVED from witnessed-vs-ambient interactions.");
        // A loud, greppable success marker even in --headless.
        println!("rehydrate_demo: ALL CHECKS PASSED");
        std::process::exit(0);
    } else {
        eprintln!("rehydrate_demo: SELF-CHECK FAILURES — see above");
        std::process::exit(1);
    }
}
