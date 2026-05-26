//! Userspace builder-API example for `dregg-dfa`.
//!
//! This example walks through the three authoring idioms that cover the
//! majority of starbridge-app routing needs:
//!
//! 1. **URL-style prefix routes** — most HTTP-like dispatch (`/health`,
//!    `/cells/stablecoin/*`).
//! 2. **Userspace destinations** — apps that need to smuggle their own
//!    destination type (e.g., `RouteClass`, cell IDs) through the DFA's
//!    opaque `payload` field.
//! 3. **Pattern-based routes** — binary protocol framing, bit-field
//!    matching, alternation.
//!
//! The example ends with a brief governance-round trip: how a starbridge-app
//! swaps its route table under a `GovernedRouter` using a `GovernanceProof`
//! CAS (compare-and-swap).
//!
//! Run with:
//!
//! ```text
//! cargo run --example builder_api -p dregg-dfa
//! ```

use dregg_dfa::{
    GovernanceProof, GovernedRouter, KindRegistry, Pattern, RouteTableBuilder, RouteTarget,
};

// ---------------------------------------------------------------------------
// 1. URL-style prefix dispatch (simplest case)
// ---------------------------------------------------------------------------

fn demo_url_prefix_routing() {
    println!("--- URL-prefix routing ---");

    let table = RouteTableBuilder::new()
        .route("/health", RouteTarget::handler("health_check"))
        .route(
            "/cells/stablecoin/*",
            RouteTarget::handler("cell:stablecoin"),
        )
        .route("/admin/*", RouteTarget::Drop)
        .compile();

    let router = GovernedRouter::new(table);

    let cases: &[(&[u8], &str)] = &[
        (b"/health", "health_check → allow"),
        (b"/cells/stablecoin/transfer", "cell:stablecoin → allow"),
        (b"/admin/secret", "admin/* → drop"),
        (b"/unknown/path", "no match → deny"),
    ];

    for (path, label) in cases {
        let result = router.classify_path(path);
        println!(
            "  classify({:?}) => {:?}   [{}]",
            std::str::from_utf8(path).unwrap_or("<binary>"),
            result.map(|c| format!("{:?}", c.target)),
            label
        );
    }
    println!();
}

// ---------------------------------------------------------------------------
// 2. Userspace destinations — encode app-defined types as postcard payloads
// ---------------------------------------------------------------------------

/// The app's destination type: which handler pool to dispatch to.
#[derive(Debug, Clone, PartialEq, Eq)]
enum PoolKind {
    AuthPool,
    SwapPool,
    StakingPool,
}

impl PoolKind {
    const KIND: &'static str = "pool_kind";

    fn to_payload(&self) -> Vec<u8> {
        match self {
            PoolKind::AuthPool => vec![0],
            PoolKind::SwapPool => vec![1],
            PoolKind::StakingPool => vec![2],
        }
    }

    fn from_payload(b: &[u8]) -> Option<Self> {
        match b {
            [0] => Some(PoolKind::AuthPool),
            [1] => Some(PoolKind::SwapPool),
            [2] => Some(PoolKind::StakingPool),
            _ => None,
        }
    }
}

fn demo_userspace_destinations() {
    println!("--- Userspace destinations ---");

    let table = RouteTableBuilder::new()
        .route(
            "/intents/auth/*",
            RouteTarget::userspace(PoolKind::KIND, PoolKind::AuthPool.to_payload()),
        )
        .route(
            "/intents/swap/*",
            RouteTarget::userspace(PoolKind::KIND, PoolKind::SwapPool.to_payload()),
        )
        .route(
            "/intents/stake/*",
            RouteTarget::userspace(PoolKind::KIND, PoolKind::StakingPool.to_payload()),
        )
        .compile();

    // Register the kind so auditors can verify all userspace kinds are known.
    let mut registry = KindRegistry::new();
    registry.register(PoolKind::KIND);

    let mut router = GovernedRouter::new(table);
    router.set_kind_registry(registry);

    let paths: &[&[u8]] = &[
        b"/intents/auth/login",
        b"/intents/swap/USDC-ETH",
        b"/intents/stake/delegate",
        b"/intents/unknown/op",
    ];

    for path in paths {
        let label = std::str::from_utf8(path).unwrap();
        match router.classify_path(path) {
            Some(c) => match c.target {
                RouteTarget::Userspace(u) if u.kind == PoolKind::KIND => {
                    let pool = PoolKind::from_payload(&u.payload).unwrap();
                    println!("  {label} => pool {:?}", pool);
                }
                other => println!("  {label} => {:?}", other),
            },
            None => println!("  {label} => no match (deny)"),
        }
    }
    println!();
}

// ---------------------------------------------------------------------------
// 3. Pattern-based routes — binary framing, alternation, bit fields
// ---------------------------------------------------------------------------

fn demo_pattern_routes() {
    println!("--- Pattern-based routes ---");

    // Protocol framing: byte 0 selects the message family.
    // Family 0x01 → CapTP messages; family 0x02 → gossip; everything else → drop.
    let table = RouteTableBuilder::new()
        .route_pattern(
            // Accept any message whose first byte is 0x01, regardless of tail.
            Pattern::prefix_of(Pattern::word(&[0x01])),
            RouteTarget::handler("captp"),
        )
        .route_pattern(
            // Accept first byte 0x02.
            Pattern::prefix_of(Pattern::word(&[0x02])),
            RouteTarget::handler("gossip"),
        )
        // Alternation: accept the two specific 3-byte control codes.
        .route_pattern(
            Pattern::any(vec![
                Pattern::word(&[0xFF, 0x00, 0x00]),
                Pattern::word(&[0xFF, 0x00, 0x01]),
            ]),
            RouteTarget::handler("control"),
        )
        // Everything else is dropped.
        .route_pattern(Pattern::prefix_of(Pattern::any_byte()), RouteTarget::Drop)
        .compile();

    let router = GovernedRouter::new(table);

    let messages: &[(&[u8], &str)] = &[
        (&[0x01, 0xAB, 0xCD], "CapTP message"),
        (&[0x02, 0x00], "Gossip message"),
        (&[0xFF, 0x00, 0x01], "Control code"),
        (&[0x03, 0x00], "Unknown family → drop"),
    ];

    for (msg, label) in messages {
        let result = router.classify(msg);
        println!(
            "  {:02X?} ({}) => {:?}",
            msg,
            label,
            result.map(|c| format!("{:?}", c.target))
        );
    }
    println!();
}

// ---------------------------------------------------------------------------
// 4. Governance round-trip: CAS-based table swap via GovernedRouter
// ---------------------------------------------------------------------------

fn demo_governance_swap() {
    println!("--- Governance table swap ---");

    // Initial table: only /v1/* exists.
    let initial_table = RouteTableBuilder::new()
        .route("/v1/*", RouteTarget::handler("api_v1"))
        .compile();
    let initial_commitment = initial_table.commitment;

    let mut router = GovernedRouter::new(initial_table);

    // Confirm /v1/ is routed before the swap.
    assert!(router.classify_path(b"/v1/hello").is_some());
    assert!(router.classify_path(b"/v2/hello").is_none());
    println!("  Before swap: /v1/hello routed, /v2/hello unrouted ✓");

    // Governance produces a new table (adds /v2/*) and a proof that
    // authenticates the transition.
    let new_table = RouteTableBuilder::new()
        .route("/v1/*", RouteTarget::handler("api_v1"))
        .route("/v2/*", RouteTarget::handler("api_v2"))
        .compile();

    // GovernanceProof carries the old commitment for CAS verification.
    // In production, `proof_data` is a threshold-signed message; here we
    // use a stub because the `StubVerifier` accepts anything.
    let proof = GovernanceProof {
        expected_old_commitment: initial_commitment,
        proof_data: vec![0xCA, 0xFE],
    };

    router
        .update_routes(new_table, &proof)
        .expect("governance CAS should succeed with matching commitment");

    // Confirm /v2/ is now routed.
    assert!(router.classify_path(b"/v2/hello").is_some());
    println!("  After swap:  /v2/hello routed ✓");

    // A stale proof (wrong old commitment) is rejected.
    let stale_proof = GovernanceProof {
        expected_old_commitment: initial_commitment, // now stale
        proof_data: vec![],
    };
    let new_new_table = RouteTableBuilder::new()
        .route("/v3/*", RouteTarget::handler("api_v3"))
        .compile();
    let result = router.update_routes(new_new_table, &stale_proof);
    assert!(result.is_err(), "stale CAS must be rejected");
    println!("  Stale CAS correctly rejected ✓");

    println!("  Commitment after swap: {}", hex(&router.commitment()[..]));
    println!();
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect::<String>()
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

fn main() {
    demo_url_prefix_routing();
    demo_userspace_destinations();
    demo_pattern_routes();
    demo_governance_swap();

    println!("All demos completed.");
}
