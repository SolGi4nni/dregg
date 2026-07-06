//! # SECURITY-PROPERTY NON-VACUITY META-GATE (Elevated-Assurance Pillar 4b).
//!
//! The poster's law: *"a green only counts if it reds when the thing it guards breaks."* dregg proves
//! this per-keystone — every `@[load_bearing_keystone]` carries a `*_satisfiable` (fires on a real
//! instance) + a `*_teeth` (reds on a hostile forge) companion, swept in-band by Lean's
//! `#keystone_audit_tagged` (`Dregg2/Verify/KeystoneLint.lean`). But that discipline was
//! PER-KEYSTONE: there was **no total gate that EVERY load-bearing security-property theorem HAS a
//! biting non-vacuity tooth**. A new security-property apex could land toothless and pass CI.
//!
//! This gate makes the discipline TOTAL. It is a STATIC LEDGER (the same idiom as
//! `keystone_descriptor_deployment_gate.rs` / `producer_descriptor_coverage_gate.rs`): one reviewed
//! row per load-bearing security-property theorem (the ones from `docs/audit/SECURITY-PROPERTY-MAP.md`
//! that claim a WORLD property — not a refinement), each pinned to its non-vacuity companions. Lean
//! theorems are not reflectively enumerable from Rust, so the enumeration is an explicit
//! allowlist-with-reason (like the keystone-deployment gate) — a new security property forces a
//! conscious tooth-or-justify decision here.
//!
//! Two teeth make THIS gate non-vacuous (a coverage gate that passes vacuously is the exact sin it
//! polices):
//!   1. **Registration totality** — a `Missing` row (a security property with no companion) FAILS; a
//!      `SpotCheckedOnly` row must carry a `promote:` closure lane; a `HasBitingTooth` row must name
//!      BOTH companions.
//!   2. **Source grounding** — every named companion is cross-checked against the ACTUAL metatheory
//!      Lean source: the gate scans `metatheory/**/*.lean` for the declaration and REDS if a named
//!      tooth is missing/renamed/deleted. So the ledger cannot go stale silently — deleting a Lean
//!      tooth reds this gate.
//!
//! Run: `cargo test -p dregg-circuit --test security_property_nonvacuity_gate`.

use std::collections::HashSet;
use std::path::PathBuf;

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE LEDGER MODEL
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// The non-vacuity tooth status of one load-bearing security-property theorem.
#[derive(Clone, Debug)]
enum Tooth {
    /// The theorem carries a NAMED, axiom-clean non-vacuity companion (`fires` — its hypotheses are
    /// jointly satisfiable AND its conclusion is exercised on a concrete instance) AND a NAMED biting
    /// companion (`bites` — a hostile forge/mutation that makes the guarded property FALSE, so the
    /// theorem is two-valued, not `:= True`). Both names are cross-checked against the Lean source.
    HasBitingTooth {
        fires: &'static str,
        bites: &'static str,
    },
    /// The property is witnessed ONLY by `#guard` / `example` witnesses (they DO red at Lean
    /// elaboration, but are not NAMED companions a gate can register). Permitted ONLY with a reason
    /// carrying a `promote:` closure lane (promote the guards to named theorems). A bare reason FAILS.
    #[allow(dead_code)]
    SpotCheckedOnly(&'static str),
    /// No non-vacuity companion at all — a hollow security claim. Always FAILS the build. The `&str`
    /// is the finding (what tooth is owed).
    #[allow(dead_code)]
    Missing(&'static str),
}

/// One reviewed row: `(theorem @ file:line, its non-vacuity status)`.
#[derive(Clone, Debug)]
struct Row {
    /// The load-bearing security-property theorem, `name @ file:line`.
    theorem: &'static str,
    tooth: Tooth,
}

/// THE MANIFEST — every load-bearing security-property theorem (the WORLD-property set from
/// `docs/audit/SECURITY-PROPERTY-MAP.md`) + its registered non-vacuity tooth. Grounded to HEAD; see
/// `docs/audit/NON-VACUITY-MANIFEST.md` for the human-readable table + the classification rationale.
fn security_property_manifest() -> Vec<Row> {
    use Tooth::*;
    vec![
        // ── the five AssuranceCase guarantees (Dregg2/AssuranceCase.lean) ──────────────────────────
        Row {
            theorem: "authority_guarantee @ AssuranceCase.lean:166",
            tooth: HasBitingTooth {
                fires: "attenuate_non_amplifying_satisfiable",
                bites: "attenuate_non_amplifying_teeth",
            },
        },
        Row {
            theorem: "conservation_guarantee @ AssuranceCase.lean:259",
            tooth: HasBitingTooth {
                // NEW this lane: the value-law biting tooth was #guard-only before Pillar 4b.
                fires: "reachable_total_zero_satisfiable",
                bites: "reachable_total_zero_teeth",
            },
        },
        Row {
            theorem: "freshness_guarantee @ AssuranceCase.lean:581",
            tooth: HasBitingTooth {
                fires: "noteSpendStmt_no_double_spend_satisfiable",
                bites: "noteSpendStmt_teeth",
            },
        },
        Row {
            theorem: "unfoolability_guarantee @ AssuranceCase.lean:666",
            tooth: HasBitingTooth {
                fires: "light_client_fires_on_real_chain",
                bites: "tampered_aggregate_cannot_bind",
            },
        },
        Row {
            // Integrity is a receipt-binding REFINEMENT, but it is load-bearing and carries a tooth
            // (an observable receipt that discriminates), so it is registered here too.
            theorem: "integrity_guarantee @ AssuranceCase.lean:412",
            tooth: HasBitingTooth {
                fires: "writeCell0_receipt_eq",
                bites: "writeCell0_receipt_observable",
            },
        },
        // ── the standalone property apexes ──────────────────────────────────────────────────────────
        Row {
            theorem: "introduce_non_amplifying (IsNonAmplifying) @ Exec/EffectsAuthority.lean:197",
            tooth: HasBitingTooth {
                fires: "introduce_non_amplifying_satisfiable",
                bites: "introduce_non_amplifying_teeth",
            },
        },
        Row {
            theorem: "reshareN_attenuates @ Deos/Membrane.lean:122",
            tooth: HasBitingTooth {
                // NEW this lane: the n-hop non-vacuity fires was #guard-only before Pillar 4b.
                fires: "reshareN_attenuates_satisfiable",
                bites: "reshare_refuses_amplification",
            },
        },
        Row {
            theorem: "reachable_total_zero @ Exec/ReachableConservation.lean:49",
            tooth: HasBitingTooth {
                fires: "reachable_total_zero_satisfiable",
                bites: "reachable_total_zero_teeth",
            },
        },
        Row {
            theorem: "deposit_price_non_decreasing @ Deos/Vault.lean:187",
            tooth: HasBitingTooth {
                fires: "established_deposit_accepts",
                bites: "dilution_rejected",
            },
        },
        Row {
            theorem: "settlement_soundness @ Metatheory/SettlementSoundness.lean:153",
            tooth: HasBitingTooth {
                fires: "deployedSettle_nonvacuous",
                bites: "deployedSettle_revoke_unsettleable",
            },
        },
        Row {
            theorem: "mintA_authorized (supply) @ Circuit/Spec/SupplyCreation.lean",
            tooth: HasBitingTooth {
                fires: "mintA_authorized_satisfiable",
                bites: "mintA_rejects_unauthorized",
            },
        },
        Row {
            theorem: "captp/token/custom_sound (AuthModes) @ Exec/AuthModes.lean",
            tooth: HasBitingTooth {
                fires: "custom_sound_satisfiable",
                bites: "custom_sound_teeth",
            },
        },
        // ── the eight carrier BindingFromFolds (Dregg2/Circuit/*BindingFromFold.lean) ───────────────
        // Each: honest_companion_fires (a real aggregate verifies) + forged_*_unsat_demo (a forged
        // fold is UNSAT — the biting refutation). All #assert_axioms-clean under the FRI/CR floor.
        Row {
            theorem: "custom_binding_from_fold @ Circuit/CustomBindingFromFold.lean:147",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires",
                bites: "forged_unsat_demo",
            },
        },
        Row {
            theorem: "factory_binding_from_fold @ Circuit/FactoryBindingFromFold.lean:145",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires",
                bites: "forged_childvk_unsat_demo",
            },
        },
        Row {
            theorem: "bridge_binding_from_fold @ Circuit/BridgeBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires",
                bites: "forged_mint_hash_unsat_demo",
            },
        },
        Row {
            theorem: "sovereign_binding_from_fold @ Circuit/SovereignBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires",
                bites: "forged_keycommit_unsat_demo",
            },
        },
        Row {
            theorem: "membership_binding_from_fold @ Circuit/MembershipBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires",
                bites: "forged_tuple_unsat_demo",
            },
        },
        Row {
            theorem: "dsl_binding_from_fold @ Circuit/DslBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires",
                bites: "forged_rc_unsat_demo",
            },
        },
        Row {
            theorem: "hatchery_binding_from_fold @ Circuit/HatcheryBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires",
                bites: "forged_contract_unsat_demo",
            },
        },
        Row {
            theorem: "deco_binding_from_fold @ Circuit/DecoBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires",
                bites: "forged_payment_hash_unsat_demo",
            },
        },
        // ── SealedEscrow's economic no-theft world-property (Deos/SealedEscrow.lean §9) ──────────────
        // The escrow analogue of Vault's no-dilution / Lease's budget conservation (survey gap #3):
        // a reachability invariant over the deployed op set (deposit/settle/reclaim). fires — a
        // reachable honest settle legitimately extracts to the counterparties; bites — the half-open
        // theft (taking a leg without funding one's own) is UNREACHABLE.
        Row {
            theorem: "sealedescrow_no_theft @ Deos/SealedEscrow.lean:753",
            tooth: HasBitingTooth {
                fires: "honest_swap_reachable",
                bites: "halfopen_theft_unreachable",
            },
        },
    ]
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE CHECKER (pure — shared by the real gate and the bite-proof test)
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// The verdict on one row, given the set of declaration names present in the Lean source.
/// Returns `Some(finding)` when the row is UNCOVERED (the gate must red), else `None`.
fn row_finding(row: &Row, known: &HashSet<String>) -> Option<String> {
    match &row.tooth {
        Tooth::Missing(what) => Some(format!(
            "MISSING non-vacuity tooth — {} — a hollow security claim (owed: {what})",
            row.theorem
        )),
        Tooth::SpotCheckedOnly(reason) => {
            if reason.trim().is_empty() || !reason.contains("promote:") {
                Some(format!(
                    "SPOT-CHECKED-ONLY without a `promote:` closure lane — {} — reason: {reason:?}",
                    row.theorem
                ))
            } else {
                None
            }
        }
        Tooth::HasBitingTooth { fires, bites } => {
            let mut problems = Vec::new();
            if fires.trim().is_empty() {
                problems.push("empty `fires` companion name".to_string());
            } else if !known.contains(*fires) {
                problems.push(format!(
                    "`fires` companion `{fires}` NOT FOUND in metatheory Lean source (stale/renamed/deleted tooth)"
                ));
            }
            if bites.trim().is_empty() {
                problems.push("empty `bites` companion name".to_string());
            } else if !known.contains(*bites) {
                problems.push(format!(
                    "`bites` companion `{bites}` NOT FOUND in metatheory Lean source (stale/renamed/deleted tooth)"
                ));
            }
            if problems.is_empty() {
                None
            } else {
                Some(format!("{} — {}", row.theorem, problems.join("; ")))
            }
        }
    }
}

/// Every uncovered row (the gate reds iff this is non-empty).
fn uncovered(rows: &[Row], known: &HashSet<String>) -> Vec<String> {
    rows.iter().filter_map(|r| row_finding(r, known)).collect()
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE LEAN-SOURCE SCAN (grounds the ledger to the real tree)
// ─────────────────────────────────────────────────────────────────────────────────────────────────

fn metatheory_dir() -> PathBuf {
    // `<workspace>/circuit/` is CARGO_MANIFEST_DIR; the Lean tree is a sibling.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("metatheory")
}

/// Collect every `theorem`/`lemma`/`def`/`abbrev` declaration NAME under `metatheory/**/*.lean`.
/// Names are matched as bare identifiers (the companions are referenced unqualified in the ledger).
fn scan_lean_decl_names(root: &std::path::Path) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                // Skip build artifacts / vendored attic.
                let skip = matches!(
                    path.file_name().and_then(|s| s.to_str()),
                    Some(".lake") | Some("_attic") | Some("build") | Some("target")
                );
                if !skip {
                    stack.push(path);
                }
            } else if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                if let Ok(src) = std::fs::read_to_string(&path) {
                    collect_decl_names(&src, &mut names);
                }
            }
        }
    }
    names
}

/// Extract declaration names from Lean source. Matches lines whose first token (after optional
/// `private`/`protected`/`noncomputable`) is a decl keyword, taking the following identifier.
fn collect_decl_names(src: &str, out: &mut HashSet<String>) {
    for raw in src.lines() {
        let line = raw.trim_start();
        let mut toks = line.split_whitespace();
        let Some(mut first) = toks.next() else {
            continue;
        };
        // step over decl modifiers
        while matches!(first, "private" | "protected" | "noncomputable" | "@[simp]") {
            match toks.next() {
                Some(t) => first = t,
                None => break,
            }
        }
        if matches!(first, "theorem" | "lemma" | "def" | "abbrev") {
            if let Some(name) = toks.next() {
                // strip anything after the identifier (`:`, `(`, `{`, etc.)
                let ident: String = name
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'' || *c == '.')
                    .collect();
                if !ident.is_empty() {
                    // register both the fully-qualified tail and the bare last segment
                    if let Some(last) = ident.rsplit('.').next() {
                        out.insert(last.to_string());
                    }
                    out.insert(ident);
                }
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE GATE
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// THE META-GATE: every load-bearing security-property theorem in the manifest has a registered,
/// source-grounded biting non-vacuity tooth. A `Missing` row, an un-laned `SpotCheckedOnly`, or a
/// `HasBitingTooth` naming a companion absent from the Lean source, REDS this test.
#[test]
fn every_security_property_has_biting_tooth() {
    let manifest = security_property_manifest();
    assert!(
        manifest.len() >= 20,
        "manifest shrank below the known load-bearing set ({} rows) — a security property was \
         dropped from the gate (see docs/audit/SECURITY-PROPERTY-MAP.md)",
        manifest.len()
    );

    let root = metatheory_dir();
    let known = scan_lean_decl_names(&root);
    assert!(
        known.len() > 500,
        "Lean-source scan found only {} decls under {} — the metatheory tree is missing or \
         unreadable; the source-grounding leg of this gate cannot run (fail loudly, never skip)",
        known.len(),
        root.display()
    );

    let findings = uncovered(&manifest, &known);
    assert!(
        findings.is_empty(),
        "SECURITY-PROPERTY NON-VACUITY GATE RED — {} load-bearing theorem(s) lack a registered, \
         source-grounded biting tooth (a green that would not red when the guard breaks):\n  - {}",
        findings.len(),
        findings.join("\n  - ")
    );
}

/// PROOF THAT THE GATE BITES — the meta-gate is itself non-vacuous. A coverage gate that only ever
/// passes is the exact laundering it forbids, so we exhibit every way it must RED and assert it does.
#[test]
fn meta_gate_bites() {
    // A rich known-set (so a HasBitingTooth with real names would pass) EXCEPT the fakes below.
    let known: HashSet<String> = ["real_fires", "real_bites"]
        .into_iter()
        .map(String::from)
        .collect();

    // (a) a Missing row REDS.
    let missing = vec![Row {
        theorem: "fake_property @ Nowhere.lean:1",
        tooth: Tooth::Missing("owes a teeth"),
    }];
    assert!(
        !uncovered(&missing, &known).is_empty(),
        "gate FAILED TO BITE a Missing row — it would pass a hollow security claim"
    );

    // (b) a SpotCheckedOnly row WITHOUT a `promote:` lane REDS; WITH one, passes.
    let spot_bad = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::SpotCheckedOnly("only #guards exist"),
    }];
    assert!(
        !uncovered(&spot_bad, &known).is_empty(),
        "gate FAILED TO BITE an un-laned SpotCheckedOnly row"
    );
    let spot_ok = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::SpotCheckedOnly("only #guards; promote: name the theorems next sprint"),
    }];
    assert!(
        uncovered(&spot_ok, &known).is_empty(),
        "a SpotCheckedOnly row WITH a promote: lane must be allowlisted"
    );

    // (c) a HasBitingTooth naming a companion ABSENT from the source REDS (the stale-ledger catch —
    //     deleting/renaming a Lean tooth must red this gate).
    let stale = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::HasBitingTooth {
            fires: "real_fires",
            bites: "companion_that_was_deleted",
        },
    }];
    assert!(
        !uncovered(&stale, &known).is_empty(),
        "gate FAILED TO BITE a HasBitingTooth naming a deleted companion — the ledger could go stale"
    );

    // (d) an empty companion name REDS.
    let empty = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::HasBitingTooth {
            fires: "real_fires",
            bites: "",
        },
    }];
    assert!(
        !uncovered(&empty, &known).is_empty(),
        "gate FAILED TO BITE an empty `bites` companion name"
    );

    // (e) a fully-grounded HasBitingTooth PASSES (the gate is not red-for-everything).
    let good = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::HasBitingTooth {
            fires: "real_fires",
            bites: "real_bites",
        },
    }];
    assert!(
        uncovered(&good, &known).is_empty(),
        "gate REDS a fully-grounded row — it is red-for-everything (vacuously failing), not discriminating"
    );

    // (f) THE DECISIVE BITE: take the REAL manifest and DELETE one real tooth name from the known-set
    //     (simulating a removed Lean companion). The gate must red on exactly that row.
    let manifest = security_property_manifest();
    let mut known_full: HashSet<String> = scan_lean_decl_names(&metatheory_dir());
    if known_full.len() > 500 {
        let removed = known_full.remove("reachable_total_zero_teeth");
        assert!(
            removed,
            "expected the newly-added `reachable_total_zero_teeth` tooth to be present in the source"
        );
        let findings = uncovered(&manifest, &known_full);
        assert!(
            findings
                .iter()
                .any(|f| f.contains("reachable_total_zero_teeth")),
            "removing the real `reachable_total_zero_teeth` tooth did NOT red the gate — it is not \
             genuinely source-grounded"
        );
    }
}

/// Visibility probe: the two tooths this lane ADDED are present and grounded (so a future edit that
/// deletes them must consciously touch this gate).
#[test]
fn pillar_4b_added_tooths_are_grounded() {
    let known = scan_lean_decl_names(&metatheory_dir());
    if known.len() <= 500 {
        return; // scan unavailable in this environment; the main gate already fails loudly.
    }
    for t in [
        "reachable_total_zero_teeth",
        "nonzero_state_unreachable",
        "reshareN_attenuates_satisfiable",
    ] {
        assert!(
            known.contains(t),
            "Pillar-4b tooth `{t}` is missing from the metatheory source — added this lane, must persist"
        );
    }
}
