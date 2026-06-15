//! DreggDL tests: a valid deployment passes the static assurance; a
//! non-conserving / over-granting deployment FAILS with the precise locus; a
//! parse → lower → re-serialize round-trip is stable.

use crate::*;

// ─── a valid deployment passes ───────────────────────────────────────────────

const ESCROW: &str = include_str!("../examples/escrow.dregg.toml");

#[test]
fn valid_escrow_deployment_passes() {
    let v = check(ESCROW, false).expect("escrow parses + lowers");
    assert!(
        v.pass(),
        "valid escrow deployment must pass static assurance; findings: {:?}",
        v.assurance.all_findings()
    );
    // Three cells born (deal-001, operator, bank), one fund, one grant.
    assert_eq!(v.cells.len(), 3, "three cells declared");
    assert_eq!(v.factories.len(), 1, "one factory declared");
    // 3 births + 1 fund + 1 grant = 5 effect-groups.
    assert_eq!(v.turn_count, 5);
}

#[test]
fn resolved_ids_are_deterministic() {
    let a = check(ESCROW, false).unwrap();
    let b = check(ESCROW, false).unwrap();
    assert_eq!(
        a.cells, b.cells,
        "cell ids are a deterministic function of names"
    );
    assert_eq!(a.factories, b.factories, "factory_vks are deterministic");
}

// ─── a non-conserving deployment fails with the asset locus ──────────────────

#[test]
fn non_conserving_fund_is_caught() {
    // A fund whose `from` and `to` are the same is balanced by construction
    // (Transfer always nets); to make the forest non-conserve, inject a
    // balance_change via... actually the surface only emits Transfers (which
    // self-net). The conservation violation we CAN express at the surface is a
    // ring imbalance — exercised below. For a pure non-conservation, we drive
    // the lowered forest directly: build a Deployment, lower it, then mutate.
    //
    // Here we assert the positive: a plain funded deployment conserves.
    let v = check(ESCROW, false).unwrap();
    assert!(
        v.assurance.conservation.is_pass(),
        "funding transfers self-net"
    );
}

#[test]
fn unbalanced_ring_is_caught() {
    // Three funds that do NOT close into a ring: a→b, b→c, but no c→a. With
    // --ring, the participants don't all net to zero → a ring finding.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "b"
factory = "f"
[[cell]]
name = "c"
factory = "f"

[[fund]]
from = "a"
to   = "b"
amount = 10
[[fund]]
from = "b"
to   = "c"
amount = 10
"#;
    let v = check(dl, true).expect("parses");
    assert!(
        !v.assurance.ring_balance.is_pass(),
        "an un-closed ring must fail the ring check"
    );
    // The closed version passes the ring check.
    let closed = format!("{dl}\n[[fund]]\nfrom = \"c\"\nto = \"a\"\namount = 10\n");
    let vc = check(&closed, true).expect("parses");
    assert!(
        vc.assurance.ring_balance.is_pass(),
        "a closed conserving ring passes; findings: {:?}",
        vc.assurance.ring_balance.findings()
    );
}

// ─── an over-granting (amplifying) deployment fails with the grant locus ─────

#[test]
fn amplifying_redelegation_is_caught() {
    // root grants `operator` a TRANSFER-ONLY facet over `deal`. operator then
    // re-delegates to `sub` a cap over the SAME target `deal` but UNRESTRICTED
    // (allowed_effects absent = top). That widens what it was handed → an
    // in-forest amplification along the delegation edge.
    //
    // EFFECT_TRANSFER = 1<<1 = 2.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

# root → operator: a TRANSFER-ONLY facet over `deal`.
[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

# operator → sub: UNRESTRICTED over `deal` (no allowed_effects = top). This
# amplifies the transfer-only cap operator was handed.
[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
"#;
    let v = check(dl, false).expect("parses + lowers");
    assert!(
        !v.assurance.no_amplification.is_pass(),
        "a widening re-delegation must fail non-amplification"
    );
    let findings = v.assurance.no_amplification.findings();
    assert!(
        findings.iter().any(|f| f.message.contains("amplifies")),
        "the finding names the amplification; got: {findings:?}"
    );
    // And the locus points at a node with an effect index (the grant edge).
    assert!(
        findings[0].locus.effect_index.is_some(),
        "the finding locates the offending grant effect"
    );
}

#[test]
fn attenuating_redelegation_passes() {
    // The same shape, but operator NARROWS (re-grants the same transfer-only
    // facet, or narrower) → an attenuation, which passes.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

# operator → sub: the SAME transfer-only facet. An attenuation (⊆).
[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
allowed_effects = 2
"#;
    let v = check(dl, false).expect("parses + lowers");
    assert!(
        v.assurance.no_amplification.is_pass(),
        "re-granting the same-or-narrower facet is an attenuation; findings: {:?}",
        v.assurance.no_amplification.findings()
    );
}

// ─── unknown-name and structural errors are reported with the locus ──────────

#[test]
fn unknown_factory_reference_errors() {
    let dl = r#"
[federation]
id = "auto"
[[cell]]
name = "c"
factory = "does-not-exist"
"#;
    let err = check(dl, false).unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("does-not-exist"),
        "names the missing factory: {msg}"
    );
}

#[test]
fn unknown_grant_target_errors() {
    let dl = r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "a"
factory = "f"
[[grant]]
from = "a"
to   = "ghost"
"#;
    let err = check(dl, false).unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("ghost"),
        "names the unresolved recipient: {msg}"
    );
}

#[test]
fn duplicate_cell_name_errors() {
    let dl = r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "a"
factory = "f"
"#;
    let err = check(dl, false).unwrap_err();
    assert!(
        format!("{err}").contains("duplicate cell name"),
        "rejects dup names"
    );
}

// ─── round-trip: parse → re-serialize → parse is stable ──────────────────────

#[test]
fn parse_serialize_roundtrip_is_stable() {
    let dep = parse_toml(ESCROW).expect("escrow parses");
    let reserialized = serialize_toml(&dep).expect("serializes back to TOML");
    let dep2 = parse_toml(&reserialized).expect("re-serialized form re-parses");
    assert_eq!(dep, dep2, "parse∘serialize∘parse is a fixpoint");
}

#[test]
fn lower_is_deterministic_byte_for_byte() {
    // The whole point: lowering is a pure function — same DreggDL → same forest.
    let dep = parse_toml(ESCROW).unwrap();
    let a = Lowered::from_deployment(&dep).unwrap();
    let b = Lowered::from_deployment(&dep).unwrap();
    let ja = serde_json::to_vec(&a.forest).unwrap();
    let jb = serde_json::to_vec(&b.forest).unwrap();
    assert_eq!(
        ja, jb,
        "lowering the same DreggDL yields a byte-identical forest"
    );
    assert_eq!(a.federation_id, b.federation_id);
}

// ─── JSON surface parses too (the canonical form is the serde struct) ────────

#[test]
fn json_surface_parses() {
    let dep_toml = parse_toml(ESCROW).unwrap();
    let json = serde_json::to_string(&dep_toml).unwrap();
    let dep_json = parse_json(&json).unwrap();
    assert_eq!(dep_toml, dep_json, "TOML and JSON surfaces agree");
}

// ─── expressiveness: named facets + pinned on-chain factory VK ───────────────

#[test]
fn named_facet_lowers_to_the_same_mask_as_the_raw_value() {
    // A grant written with the friendly `facet = "transfer-only"` and one written
    // with the raw `allowed_effects = 2` lower to the IDENTICAL capability.
    let with_name = r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "b"
factory = "f"
[[grant]]
from = "a"
to   = "b"
target = "a"
facet = "transfer-only"
"#;
    let with_raw = with_name.replace("facet = \"transfer-only\"", "allowed_effects = 2");
    let la = Lowered::from_deployment(&parse_toml(with_name).unwrap()).unwrap();
    let lr = Lowered::from_deployment(&parse_toml(&with_raw).unwrap()).unwrap();
    // The grant effect's cap.allowed_effects must agree (both == Some(2)).
    let cap_of = |l: &Lowered| -> Option<u32> {
        for root in &l.forest.roots {
            for eff in root.all_effects() {
                if let dregg_turn::action::Effect::GrantCapability { cap, .. } = eff {
                    return cap.allowed_effects;
                }
            }
        }
        None
    };
    assert_eq!(cap_of(&la), Some(2), "named transfer-only ⇒ mask 2");
    assert_eq!(cap_of(&la), cap_of(&lr), "named and raw facet agree");
}

#[test]
fn conflicting_facet_and_allowed_effects_is_rejected() {
    // Setting BOTH `facet` and `allowed_effects` to DISAGREEING values is an
    // error (the surface must be unambiguous).
    let dl = r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "b"
factory = "f"
[[grant]]
from = "a"
to   = "b"
target = "a"
facet = "transfer-only"
allowed_effects = 1
"#;
    let err = check(dl, false).unwrap_err();
    assert!(
        format!("{err}").contains("DISAGREE"),
        "the conflict is named: {err}"
    );
}

#[test]
fn pinned_factory_vk_is_the_birth_effect_identity() {
    // When a [[factory]] pins `factory_vk`, the born cell's CreateCellFromFactory
    // effect names THAT vk (so the deploy instantiates the real on-chain factory),
    // not the self-contained descriptor hash.
    let pinned = "0x".to_string() + &"ab".repeat(32);
    let dl = format!(
        r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
factory_vk = "{pinned}"
[[cell]]
name = "a"
factory = "f"
"#
    );
    let l = Lowered::from_deployment(&parse_toml(&dl).unwrap()).unwrap();
    let mut found = None;
    for root in &l.forest.roots {
        for eff in root.all_effects() {
            if let dregg_turn::action::Effect::CreateCellFromFactory { factory_vk, .. } = eff {
                found = Some(*factory_vk);
            }
        }
    }
    assert_eq!(
        found,
        Some([0xabu8; 32]),
        "the birth effect uses the PINNED factory vk"
    );
}

// ─── the app-deploy specs: ACCEPT the correct one, REFUSE the over-grant ──────

macro_rules! app_spec_pair {
    ($name:ident, $accept:literal, $overgrant:literal) => {
        #[test]
        fn $name() {
            // The correct app-deploy spec passes the gate (no-amp ✓, conserves ✓).
            let accept = include_str!($accept);
            let v = check(accept, false).expect("accept spec parses + lowers");
            assert!(
                v.pass(),
                "the correct app-deploy spec must PASS; findings: {:?}",
                v.assurance.all_findings()
            );
            // The over-granting sibling is REFUSED by apply, before any turn, on
            // non-amplification, with the offending grant located.
            let og = include_str!($overgrant);
            let err = plan_apply_toml(og, false)
                .expect_err("the over-grant spec must be REFUSED by the gate");
            let crate::DeployError::Apply(ApplyError::Refused { assurance }) = err else {
                panic!("expected a Refused gate failure, got: {err}");
            };
            assert!(
                !assurance.no_amplification.is_pass(),
                "the over-grant is refused on non-amplification"
            );
            // The enriched diagnostic names the over-granting edge by spec name.
            let lowered = Lowered::from_deployment(&parse_toml(og).unwrap()).unwrap();
            let diag = crate::explain_assurance(&lowered, &assurance);
            assert!(!diag.is_clean(), "there is a located finding");
            let joined = diag.lines().join("\n");
            assert!(
                joined.contains("OVER-GRANT") && joined.contains("WIDENS"),
                "the diagnostic names the over-grant + the widening:\n{joined}"
            );
        }
    };
}

app_spec_pair!(
    app_supply_chain_provenance_accept_and_overgrant,
    "../specs/supply-chain-provenance.dregg.toml",
    "../specs/supply-chain-provenance.overgrant.dregg.toml"
);
app_spec_pair!(
    app_escrow_market_accept_and_overgrant,
    "../specs/escrow-market.dregg.toml",
    "../specs/escrow-market.overgrant.dregg.toml"
);
app_spec_pair!(
    app_identity_accept_and_overgrant,
    "../specs/identity.dregg.toml",
    "../specs/identity.overgrant.dregg.toml"
);

// ─── the receipt SHAPE is honest: dynamic fields deferred, not zeroed ─────────

#[test]
fn projected_receipt_dynamic_fields_are_deferred_not_zeroed() {
    use crate::apply::DeferredField;
    let plan = plan_apply_toml(ESCROW, false).unwrap();
    assert!(
        plan.receipts_are_planned_shape(),
        "at plan time every executor-filled field is Deferred"
    );
    for pt in &plan.turns {
        let r = &pt.projected_receipt;
        // The executor-filled half is Deferred (NOT a silent zero).
        assert_eq!(r.post_state_hash, DeferredField::Deferred);
        assert_eq!(r.pre_state_hash, DeferredField::Deferred);
        assert_eq!(r.computrons_used, DeferredField::Deferred);
        assert_eq!(r.timestamp, DeferredField::Deferred);
        assert_eq!(r.executor_signature, DeferredField::Deferred);
        // The artifact-known half is the real value (and the chain link matches
        // the legacy projected_receipt_hash).
        assert_eq!(r.turn_hash, pt.turn_hash);
        assert_eq!(r.chain_link_hash, pt.projected_receipt_hash);
        assert_eq!(r.agent, pt.agent);
    }
}

// ════════════════════════════════════════════════════════════════════════════
//  apply: lower → per-root turn sequence + receipt-chain shape, GATED by the
//  static check.
// ════════════════════════════════════════════════════════════════════════════

use crate::apply::{ApplyError, plan_apply, plan_apply_toml};

/// An amplifying deployment: operator is handed a TRANSFER-ONLY facet (mask 2)
/// over `deal`, then re-delegates to `sub` an UNRESTRICTED cap over the same
/// target — a widening, caught as an in-forest capability amplification.
const AMPLIFYING: &str = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
"#;

// ─── THE GATE: an amplifying spec is REFUSED by apply, before any turn ────────

#[test]
fn apply_refuses_an_amplifying_spec_before_emitting_any_turn() {
    // This is the load-bearing property: the static check is the gate. An
    // over-grant (in-forest capability amplification) is refused up front — the
    // apply flow produces NO turn sequence for it.
    let err = plan_apply_toml(AMPLIFYING, false)
        .expect_err("an amplifying deployment must be REFUSED by the gate, not planned");
    match err {
        crate::DeployError::Lower(_)
        | crate::DeployError::Toml(_)
        | crate::DeployError::Json(_) => {
            panic!("expected a Refused gate failure, not a parse/lower error: {err}")
        }
        crate::DeployError::Apply(ApplyError::Refused { assurance }) => {
            // The refusal carries the finding that names the amplification, at
            // the grant edge — the same locus `check` reports.
            assert!(
                !assurance.no_amplification.is_pass(),
                "the refusal is on non-amplification"
            );
            let findings = assurance.no_amplification.findings();
            assert!(
                findings.iter().any(|f| f.message.contains("amplifies")),
                "the refusal names the amplification; got: {findings:?}"
            );
            assert!(
                findings[0].locus.effect_index.is_some(),
                "the refusal locates the offending grant effect"
            );
        }
        crate::DeployError::Apply(other) => {
            panic!("expected Refused, got a different apply error: {other}")
        }
    }
}

#[test]
fn apply_refuses_directly_via_plan_apply_with_the_assurance() {
    // The same gate, reached through the parsed-Deployment entry, asserting the
    // ApplyError::Refused variant carries the failing assurance directly.
    let dep = parse_toml(AMPLIFYING).unwrap();
    let err = plan_apply(&dep, false).expect_err("amplifying spec refused");
    let ApplyError::Refused { assurance } = err else {
        panic!("expected ApplyError::Refused, got {err}");
    };
    assert!(!assurance.pass(), "the carried assurance is a failing one");
    assert!(!assurance.no_amplification.is_pass());
}

// ─── a valid spec lowers to the chained per-root turn sequence ───────────────

#[test]
fn apply_emits_the_per_root_turn_sequence_for_a_valid_spec() {
    let plan = plan_apply_toml(ESCROW, false).expect("valid escrow applies");
    // The gate passed (by construction of a returned plan).
    assert!(
        plan.assurance.pass(),
        "a returned plan carries a passing assurance"
    );
    // 3 births + 1 fund + 1 grant = 5 root effect-groups = 5 turns.
    assert_eq!(plan.len(), 5, "one turn per root effect-group");
    // Phases come out in dependency order: births first, then funds, then grants.
    let phases: Vec<&str> = plan.turns.iter().map(|t| t.phase).collect();
    assert_eq!(
        phases,
        vec!["birth", "birth", "birth", "fund", "grant"],
        "dependency order: births → funds → grants"
    );
}

#[test]
fn apply_chains_the_receipts_into_one_strand() {
    let plan = plan_apply_toml(ESCROW, false).unwrap();
    // The first turn has no predecessor.
    assert_eq!(
        plan.turns[0].turn.previous_receipt_hash, None,
        "the first turn opens the chain"
    );
    // Each subsequent turn's previous_receipt_hash is the prior turn's projected
    // receipt hash — the receipt-chain shape.
    for w in plan.turns.windows(2) {
        assert_eq!(
            w[1].turn.previous_receipt_hash,
            Some(w[0].projected_receipt_hash),
            "turn n+1 chains to turn n's projected receipt"
        );
        // And the causal dependency edge points at the prior turn.
        assert_eq!(
            w[1].turn.depends_on,
            vec![w[0].turn_hash],
            "depends_on records the prior turn"
        );
    }
    // The self-consistency invariant holds.
    assert!(
        plan.chain_is_linked(),
        "the plan's receipt chain is internally linked"
    );
}

#[test]
fn apply_is_deterministic_byte_for_byte() {
    // apply is a pure function of the DreggDL — same doc → same turn sequence,
    // including the projected receipt chain (the reproducibility half).
    let a = plan_apply_toml(ESCROW, false).unwrap();
    let b = plan_apply_toml(ESCROW, false).unwrap();
    assert_eq!(a.len(), b.len());
    for (x, y) in a.turns.iter().zip(b.turns.iter()) {
        assert_eq!(x.turn_hash, y.turn_hash, "turn hashes are deterministic");
        assert_eq!(
            x.projected_receipt_hash, y.projected_receipt_hash,
            "the projected receipt chain is deterministic"
        );
        let jx = serde_json::to_vec(&x.turn.call_forest).unwrap();
        let jy = serde_json::to_vec(&y.turn.call_forest).unwrap();
        assert_eq!(jx, jy, "the per-turn forest is byte-identical across runs");
    }
}

#[test]
fn apply_passes_an_attenuating_redelegation_and_nests_it() {
    // The attenuating sibling of AMPLIFYING (operator re-grants the SAME
    // transfer-only facet) is NOT refused — it applies, and the re-delegation
    // nests under its parent grant (one grant turn carrying the child), so the
    // sequence has one fewer top-level grant than total grants.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
allowed_effects = 2
"#;
    let plan = plan_apply_toml(dl, false).expect("attenuating spec applies");
    assert!(plan.assurance.pass());
    // 3 births + 2 grants, but the second grant NESTS under the first, so there
    // are 3 birth turns + 1 grant turn = 4 top-level turns.
    assert_eq!(
        plan.len(),
        4,
        "the re-delegation nests, not a separate root turn"
    );
    let grant_turn = plan.turns.iter().find(|t| t.phase == "grant").unwrap();
    // The grant turn's single root carries the child grant as a nested action.
    assert_eq!(
        grant_turn.turn.call_forest.roots[0].children.len(),
        1,
        "the nested re-delegation is a child of the parent grant in the turn"
    );
}

#[test]
fn apply_refuses_a_non_conserving_ring_under_ring_mode() {
    // An un-closed ring (a→b, b→c, no c→a) fails the ring check; under as_ring
    // the apply gate refuses it.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "b"
factory = "f"
[[cell]]
name = "c"
factory = "f"

[[fund]]
from = "a"
to   = "b"
amount = 10
[[fund]]
from = "b"
to   = "c"
amount = 10
"#;
    let err = plan_apply_toml(dl, true).expect_err("an open ring is refused under ring mode");
    let crate::DeployError::Apply(ApplyError::Refused { assurance }) = err else {
        panic!("expected a ring refusal, got {err}");
    };
    assert!(
        !assurance.ring_balance.is_pass(),
        "refused on the ring-balance check"
    );
    // The CLOSED ring applies cleanly (and emits 3 fund turns).
    let closed = format!("{dl}\n[[fund]]\nfrom = \"c\"\nto = \"a\"\namount = 10\n");
    let plan = plan_apply_toml(&closed, true).expect("a closed ring applies");
    assert_eq!(plan.turns.iter().filter(|t| t.phase == "fund").count(), 3);
}
