//! The reflective crawl, proven over a real ledger: crawl cells, read the four
//! substances, build the ocap graph, project a per-viewer FRUSTUM (cap-bounded), and
//! present the moldable faces — all gpui-free, off a bare `dregg_cell::Ledger`.

use deos_reflect::{
    Affordance, AffordanceSurface, Frustum, OcapGraph, PresentationKind, ReflectedCell,
};
use dregg_cell::{AuthRequired, Cell, Ledger};
use dregg_turn::action::Effect;
use dregg_types::CellId;

fn cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    Cell::with_balance(pk, [0u8; 32], balance)
}

/// Build a small ledger: a treasury cell that holds a capability over a leaf cell.
fn ledger_with_grant() -> (Ledger, CellId, CellId) {
    let mut ledger = Ledger::new();
    let leaf = cell(0x10, 100);
    let leaf_id = leaf.id();

    let mut treasury = cell(0x20, 1_000_000);
    // Grant the treasury a capability over the leaf (an ocap edge).
    let _slot = treasury
        .capabilities
        .grant(leaf_id, AuthRequired::Signature)
        .expect("grant cap");
    let treasury_id = treasury.id();

    ledger.insert_cell(leaf).unwrap();
    ledger.insert_cell(treasury).unwrap();
    (ledger, treasury_id, leaf_id)
}

#[test]
fn crawl_reads_four_substances() {
    let (ledger, treasury_id, _leaf) = ledger_with_grant();
    let c = ledger.get(&treasury_id).unwrap();
    let inspectable = deos_reflect::reflect_cell(&treasury_id, c);

    // value substance
    assert!(inspectable.fields.iter().any(|f| f.key == "balance"));
    // authority substance — the granted cap shows as a CapEdge
    assert!(inspectable.fields.iter().any(|f| f.key.starts_with("cap[")));
    // evidence substance
    assert!(inspectable.fields.iter().any(|f| f.key == "lifecycle"));
    assert_eq!(inspectable.kind, deos_reflect::ObjectKind::Cell);
}

#[test]
fn ocap_graph_has_the_grant_edge() {
    let (ledger, treasury_id, leaf_id) = ledger_with_grant();
    let g = OcapGraph::build(&ledger);

    assert_eq!(g.node_count(), 2, "two cells = two nodes");
    assert_eq!(g.edge_count(), 1, "one cap grant = one edge");
    let edge = &g.edges()[0];
    assert_eq!(edge.holder, treasury_id);
    assert_eq!(edge.target, leaf_id);
    // the treasury reaches the leaf
    assert!(g.reachable_from(&treasury_id).contains(&leaf_id));
    // the leaf reaches nothing
    assert_eq!(g.reach_count(&leaf_id), 0);
}

#[test]
fn self_cap_does_not_leak_root_into_its_own_reach() {
    // A cell holding a capability over ITSELF (a self-grant — a legitimate ocap
    // shape) creates a `root -> root` edge in the adjacency. `reachable_from`
    // documents that "`root` itself is NOT included", and the transitive loop
    // guards `t != root` — but the FIRST hop (direct neighbours) did not, so a
    // self-cap leaked `root` into its own reachable set (contract violation).
    let mut ledger = Ledger::new();
    let mut selfish = cell(0x30, 500);
    let selfish_id = selfish.id();
    // Grant the cell a capability over ITSELF (the self-targeting edge).
    selfish
        .capabilities
        .grant(selfish_id, AuthRequired::Signature)
        .expect("grant self-cap");
    ledger.insert_cell(selfish).unwrap();

    let g = OcapGraph::build(&ledger);
    assert_eq!(g.edge_count(), 1, "the self-grant is one edge");

    let reach = g.reachable_from(&selfish_id);
    assert!(
        !reach.contains(&selfish_id),
        "root must be EXCLUDED from its own reach even when it holds a self-cap"
    );
    assert_eq!(
        g.reach_count(&selfish_id),
        0,
        "a self-only cap reaches no OTHER cell — the blast radius is empty"
    );
}

#[test]
fn self_cap_hop_still_reaches_beyond() {
    // The self-cap must not SUPPRESS legitimate onward reach: a cell that holds
    // BOTH a self-cap and a cap over a leaf still reaches the leaf (root excluded,
    // leaf included).
    let mut ledger = Ledger::new();
    let leaf = cell(0x11, 10);
    let leaf_id = leaf.id();
    let mut holder = cell(0x31, 500);
    let holder_id = holder.id();
    holder
        .capabilities
        .grant(holder_id, AuthRequired::Signature)
        .expect("grant self-cap");
    holder
        .capabilities
        .grant(leaf_id, AuthRequired::Signature)
        .expect("grant leaf cap");
    ledger.insert_cell(leaf).unwrap();
    ledger.insert_cell(holder).unwrap();

    let g = OcapGraph::build(&ledger);
    let reach = g.reachable_from(&holder_id);
    assert!(!reach.contains(&holder_id), "root excluded");
    assert!(
        reach.contains(&leaf_id),
        "onward reach to the leaf is preserved"
    );
    assert_eq!(g.reach_count(&holder_id), 1, "exactly the leaf");
}

#[test]
fn frustum_is_cap_bounded() {
    let (ledger, treasury_id, leaf_id) = ledger_with_grant();

    // The treasury's frustum: it observes itself + the leaf it holds a cap over.
    let treasury_view = Frustum::project(&ledger, treasury_id);
    assert!(treasury_view.can_observe(&treasury_id));
    assert!(
        treasury_view.can_observe(&leaf_id),
        "holds a cap path to the leaf"
    );
    assert_eq!(treasury_view.visible_count(), 2);
    assert!(treasury_view.reflect(&leaf_id).is_some());

    // The leaf's frustum: it holds NO caps, so it observes ONLY itself — it CANNOT
    // crawl up to the treasury (no authority path). Cap-bounded, not omniscient.
    let leaf_view = Frustum::project(&ledger, leaf_id);
    assert!(leaf_view.can_observe(&leaf_id));
    assert!(
        !leaf_view.can_observe(&treasury_id),
        "the leaf has no authority path to the treasury — it is NOT in the frustum"
    );
    assert_eq!(leaf_view.visible_count(), 1);
    assert!(
        leaf_view.reflect(&treasury_id).is_none(),
        "reflecting an unobservable cell yields None (absence, not forgery)"
    );
}

#[test]
fn affordance_surface_projects_per_viewer() {
    let leaf = cell(0x10, 100);
    let leaf_id = leaf.id();

    // A surface with two affordances: a public `view` (None — open to everyone) and
    // a privileged `admin` (Proof). The attenuation lattice: `None` (held) is the
    // BROADEST authority and satisfies any requirement; a `Signature` holder satisfies
    // `Signature`/`None` requirements but NOT a `Proof` one (incomparable).
    let surface = AffordanceSurface::new(leaf_id)
        .declare(Affordance::new(
            "view",
            AuthRequired::None,
            Effect::IncrementNonce { cell: leaf_id },
        ))
        .declare(Affordance::new(
            "admin",
            AuthRequired::Proof,
            Effect::SetField {
                cell: leaf_id,
                index: 0,
                value: [0u8; 32],
            },
        ));

    // A holder of `Proof` sees BOTH (Proof satisfies Proof; None is open to all).
    let proof_holder = surface.visible_names(&AuthRequired::Proof);
    assert!(proof_holder.contains(&"view".to_string()));
    assert!(proof_holder.contains(&"admin".to_string()));

    // A holder of `Signature` sees only `view` — the `admin` affordance requires
    // `Proof`, which is INCOMPARABLE to a held `Signature`, so the cap tooth hides it.
    let sig_holder = surface.visible_names(&AuthRequired::Signature);
    assert!(sig_holder.contains(&"view".to_string()));
    assert!(
        !sig_holder.contains(&"admin".to_string()),
        "the cap tooth hides the Proof-gated affordance from a Signature-only viewer"
    );
}

#[test]
fn present_emits_the_moldable_faces() {
    let (ledger, treasury_id, _leaf) = ledger_with_grant();
    let reflected = ReflectedCell::from_ledger(&ledger, treasury_id).unwrap();
    let faces = reflected.present(&ledger, &[]);

    let kinds: Vec<PresentationKind> = faces.iter().map(|p| p.kind).collect();
    assert!(
        kinds.contains(&PresentationKind::RawFields),
        "the mandatory floor"
    );
    assert!(kinds.contains(&PresentationKind::Graph));
    assert!(kinds.contains(&PresentationKind::DomainVisual));
    assert!(kinds.contains(&PresentationKind::Provenance));
}
