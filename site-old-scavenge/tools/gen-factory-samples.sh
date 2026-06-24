#!/usr/bin/env bash
# gen-factory-samples.sh — regenerate the Studio's factory worked examples.
#
# Emits site/src/_includes/studio/factory-samples.generated.json by RUNNING the
# real Rust descriptor constructors (no hand-written JSON):
#   * cell/src/blueprint.rs        — escrow_factory_descriptor / obligation_factory_descriptor
#   * starbridge-apps/polis        — council_factory_descriptor / constitution_factory_descriptor
#
# The emitted `descriptor` values are the exact serde_json wire shape that the
# wasm `deploy_factory_descriptor` binding deserializes (dregg_cell::factory::
# FactoryDescriptor), so the Studio's factory composer export/import round-trips
# against ground truth. Identities are deterministic samples
# (blake3("dregg-site-sample:<name>")) so regeneration is byte-stable.
#
# This builds a throwaway cargo crate in a temp dir (path-deps into the repo);
# the repo itself is not modified beyond the generated JSON.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OUT="$ROOT/site/src/_includes/studio/factory-samples.generated.json"
WORK="$(mktemp -d /tmp/dregg-factory-samples.XXXXXX)"
trap 'rm -rf "$WORK"' EXIT

mkdir -p "$WORK/src"
cat > "$WORK/Cargo.toml" <<EOF
[package]
name = "dump-factory-samples"
version = "0.1.0"
edition = "2021"

[dependencies]
dregg-cell = { path = "$ROOT/cell", default-features = false }
starbridge-polis = { path = "$ROOT/starbridge-apps/polis" }
serde_json = "1"
blake3 = "1"

[workspace]
EOF

cat > "$WORK/src/main.rs" <<'EOF'
use dregg_cell::blueprint::*;
use dregg_cell::program::field_from_u64;
use dregg_cell::CellId;
use starbridge_polis::council::{self, CouncilCharter};
use starbridge_polis::constitution::{self, ConstitutionParams};

fn ident(tag: &str) -> [u8; 32] {
    *blake3::hash(format!("dregg-site-sample:{tag}").as_bytes()).as_bytes()
}
fn hex(b: &[u8; 32]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }

fn main() {
    let escrow = escrow_factory_descriptor(&EscrowTerms {
        amount: 250,
        depositor: ident("alice"),
        beneficiary: ident("bob"),
        condition: field_from_u64(7),
        timeout_height: 4096,
    }).unwrap();
    let obligation = obligation_factory_descriptor(&ObligationTerms {
        bond: 500,
        obligor: ident("carol"),
        obligee: ident("dave"),
        condition: field_from_u64(11),
        deadline_height: 8192,
    }).unwrap();
    let charter = CouncilCharter {
        members: vec![CellId(ident("council-alice")), CellId(ident("council-bob")), CellId(ident("council-carol"))],
        threshold: 2,
    };
    let council_desc = council::council_factory_descriptor(&charter).unwrap();
    let constitution_desc = constitution::constitution_factory_descriptor(&ConstitutionParams {
        version: 1,
        council_threshold: 2,
        amendment_delay: 1024,
        treasury_cap: 10_000,
    }).unwrap();
    let out = serde_json::json!({
        "schema": "dregg-factory-samples-v1",
        "_note": "GENERATED worked examples - produced by running the REAL Rust descriptor constructors (cell/src/blueprint.rs escrow_factory_descriptor / obligation_factory_descriptor; starbridge-apps/polis council_factory_descriptor / constitution_factory_descriptor) with deterministic sample identities (blake3('dregg-site-sample:<name>')). Each `descriptor` is the exact serde_json wire shape the wasm `deploy_factory_descriptor` binding accepts. Do not edit by hand - regenerate with site/tools/gen-factory-samples.sh.",
        "escrow": {
            "title": "Escrow (per-deal settlement cell)",
            "source": "cell/src/blueprint.rs escrow_factory_descriptor — Lean twin Dregg2.Apps.EscrowFactory",
            "terms": { "amount": 250, "depositor": "blake3('dregg-site-sample:alice')", "beneficiary": "blake3('dregg-site-sample:bob')", "condition": "field_from_u64(7)", "timeout_height": 4096 },
            "descriptor_hash": hex(&escrow.hash()),
            "descriptor": escrow,
        },
        "obligation": {
            "title": "Obligation (bonded-proof settlement cell)",
            "source": "cell/src/blueprint.rs obligation_factory_descriptor — Lean twin Dregg2.Apps.ObligationFactory",
            "terms": { "bond": 500, "obligor": "blake3('dregg-site-sample:carol')", "obligee": "blake3('dregg-site-sample:dave')", "condition": "field_from_u64(11)", "deadline_height": 8192 },
            "descriptor_hash": hex(&obligation.hash()),
            "descriptor": obligation,
        },
        "council": {
            "title": "Council proposal (M-of-N governance cell)",
            "source": "starbridge-apps/polis council_factory_descriptor — DRAFT→PROPOSED→{REJECTED, APPROVED→EXECUTED}, 2-of-3",
            "terms": { "members": 3, "threshold": 2 },
            "descriptor_hash": hex(&council_desc.hash()),
            "descriptor": council_desc,
        },
        "constitution": {
            "title": "Constitution (per-version parameter cell)",
            "source": "starbridge-apps/polis constitution_factory_descriptor — UNINIT→ACTIVE→SUPERSEDED, params pinned for life",
            "terms": { "version": 1, "council_threshold": 2, "amendment_delay": 1024, "treasury_cap": 10000 },
            "descriptor_hash": hex(&constitution_desc.hash()),
            "descriptor": constitution_desc,
        },
    });
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
}
EOF

(cd "$WORK" && cargo run -q 2>/dev/null) | python3 -c "
import json, sys
d = json.load(sys.stdin)
with open('$OUT', 'w') as f:
    json.dump(d, f, indent=2, sort_keys=True)
    f.write('\n')
print('wrote', '$OUT')
"
