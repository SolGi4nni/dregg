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
//! ## What the source-grounding leg checks (STRENGTHENED after the adversarial meta-review)
//!
//! `docs/audit/META-REVIEW-GATE-AND-DECOUC.md` §1.2 found the old grounding was a *bare-name existence
//! check over the whole tree*: a companion registered as `def bites := True`, or a companion that had
//! moved to a different file, would still pass; and the eight carriers sharing one `fires` name meant
//! deleting seven of eight would not red. Each companion is now written `name @ Relative/Path.lean`, and
//! the scan records every declaration's **(name, kind, relative-file)**. A companion is grounded IFF a
//! declaration of that name exists that is (1) a `theorem`/`lemma` (NOT a `def`/`abbrev` — closes the
//! `def := True` hole) AND (2) in the exact file the row names (closes the wrong-file / carrier-
//! multiplicity holes). The gate still cannot read a Lean *proof* to certify non-vacuity — that stays
//! Lean's job (`#assert_axioms`, `#keystone_audit_tagged`) — but it now enforces that each registered
//! tooth is a *proposition-carrying theorem in its stated home*, not merely a name present somewhere.
//!
//! ## Two ledgers
//!
//!   1. **World-property teeth** (`security_property_manifest`): every load-bearing security theorem has
//!      a NAMED `fires` + `bites`, each source-grounded (theorem-kind, right-file).
//!   2. **Accept-satisfiability** (`satisfiability_manifest`): every `GovernedDynamics` instance in the
//!      unified schema (`Metatheory/Adversary/*`) has a NAMED `∃ c, accept (run c)` companion — proven
//!      concretely, or an explicit `_of_floor` companion where accept folds a realizability floor. This
//!      closes the vacuous-governance hole (`*_bites` prove `accept ≠ True` but NOT `∃ c, accept c`, so
//!      an instance whose accept is UNSATISFIABLE would govern vacuously and go undetected).
//!
//! Run: `cargo test -p dregg-circuit --test security_property_nonvacuity_gate`.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE LEAN-SOURCE MODEL (kind + file, so grounding can enforce theorem-in-its-home)
// ─────────────────────────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Theorem,
    Lemma,
    Def,
    Abbrev,
}

impl Kind {
    /// Only a `theorem`/`lemma` carries a proposition the manifest can lean on. A `def`/`abbrev`
    /// (e.g. `def bites := True`) is NOT a biting tooth — this is the theorem-kind gate.
    fn is_proposition(self) -> bool {
        matches!(self, Kind::Theorem | Kind::Lemma)
    }
}

/// One declaration seen in the Lean source: its kind and the file (relative to `metatheory/`, `/`-sep).
#[derive(Clone, Debug)]
struct DeclLoc {
    kind: Kind,
    file: String,
}

/// name → every place it is declared (a name can recur across files, e.g. `honest_companion_fires`).
type DeclIndex = HashMap<String, Vec<DeclLoc>>;

/// A registered companion: a NAME pinned to the FILE it must live in (`"name @ Rel/Path.lean"`).
#[derive(Clone, Copy, Debug)]
struct Companion {
    name: &'static str,
    file: &'static str,
}

/// Parse a `"name @ Rel/Path.lean"` companion spec. A missing `@ file` is a hard authoring error
/// (every companion must pin its home), surfaced as a finding rather than silently name-only.
fn parse_companion(spec: &'static str) -> Companion {
    match spec.split_once(" @ ") {
        Some((name, file)) => Companion {
            name: name.trim(),
            file: file.trim(),
        },
        None => Companion {
            name: spec.trim(),
            file: "", // empty file → the grounding check reports "missing @ file pin"
        },
    }
}

/// Is `want` (a row's pinned relative path) the home of `decl_file` (a scanned relative path)?
/// Both are relative to `metatheory/` with `/` separators; compared after stripping a leading `./`.
fn same_file(decl_file: &str, want: &str) -> bool {
    let norm = |s: &str| s.trim_start_matches("./").to_string();
    norm(decl_file) == norm(want)
}

/// Ground one companion against the scanned index. `Some(problem)` when it is NOT grounded.
fn companion_problem(spec: &'static str, index: &DeclIndex) -> Option<String> {
    let c = parse_companion(spec);
    if c.name.is_empty() {
        return Some("empty companion name".to_string());
    }
    if c.file.is_empty() {
        return Some(format!(
            "companion `{}` has no `@ file` pin (write `name @ Relative/Path.lean`)",
            c.name
        ));
    }
    let locs = match index.get(c.name) {
        Some(v) => v,
        None => {
            return Some(format!(
                "companion `{}` NOT FOUND in metatheory Lean source (stale/renamed/deleted tooth)",
                c.name
            ));
        }
    };
    // Must be a theorem/lemma IN the pinned file (both conditions on the SAME declaration).
    let in_file: Vec<&DeclLoc> = locs.iter().filter(|d| same_file(&d.file, c.file)).collect();
    if in_file.is_empty() {
        let seen: Vec<&str> = locs.iter().map(|d| d.file.as_str()).collect();
        return Some(format!(
            "companion `{}` is not declared in `{}` (found only in: {}) — wrong-file / stale pin",
            c.name,
            c.file,
            seen.join(", ")
        ));
    }
    if !in_file.iter().any(|d| d.kind.is_proposition()) {
        return Some(format!(
            "companion `{}` in `{}` is a `{:?}`, not a theorem/lemma — a `def`/`abbrev` is not a biting tooth",
            c.name, c.file, in_file[0].kind
        ));
    }
    None
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// LEDGER 1 — WORLD-PROPERTY TEETH
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// The non-vacuity tooth status of one load-bearing security-property theorem.
#[derive(Clone, Debug)]
enum Tooth {
    /// A NAMED `fires` (its hypotheses are jointly satisfiable AND its conclusion is exercised on a
    /// concrete instance) AND a NAMED biting `bites` (a hostile forge/mutation making the guarded
    /// property FALSE). Both are `"name @ Rel/Path.lean"` and cross-checked against the source for
    /// theorem-kind + file-locality.
    HasBitingTooth {
        fires: &'static str,
        bites: &'static str,
    },
    /// The property is witnessed ONLY by `#guard` / `example` witnesses (they DO red at Lean
    /// elaboration, but are not NAMED companions a gate can register). Permitted ONLY with a reason
    /// carrying a `promote:` closure lane. A bare reason FAILS.
    #[allow(dead_code)]
    SpotCheckedOnly(&'static str),
    /// No non-vacuity companion at all — a hollow security claim. Always FAILS the build.
    #[allow(dead_code)]
    Missing(&'static str),
}

/// One reviewed row: `(theorem @ file:line, its non-vacuity status)`.
#[derive(Clone, Debug)]
struct Row {
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
                fires: "attenuate_non_amplifying_satisfiable @ Dregg2/Exec/EffectsAuthority.lean",
                bites: "attenuate_non_amplifying_teeth @ Dregg2/Exec/EffectsAuthority.lean",
            },
        },
        Row {
            theorem: "conservation_guarantee @ AssuranceCase.lean:259",
            tooth: HasBitingTooth {
                fires: "reachable_total_zero_satisfiable @ Dregg2/Verify/KeystoneAuditConservation.lean",
                bites: "reachable_total_zero_teeth @ Dregg2/Verify/KeystoneAuditConservation.lean",
            },
        },
        Row {
            theorem: "freshness_guarantee @ AssuranceCase.lean:581",
            tooth: HasBitingTooth {
                fires: "noteSpendStmt_no_double_spend_satisfiable @ Dregg2/Circuit/Argus/Effects/NoteSpend.lean",
                bites: "noteSpendStmt_teeth @ Dregg2/Circuit/Argus/Effects/NoteSpend.lean",
            },
        },
        Row {
            theorem: "unfoolability_guarantee @ AssuranceCase.lean:666",
            tooth: HasBitingTooth {
                fires: "light_client_fires_on_real_chain @ Dregg2/Circuit/RecursiveAggregation.lean",
                bites: "tampered_aggregate_cannot_bind @ Dregg2/Circuit/RecursiveAggregation.lean",
            },
        },
        Row {
            // Integrity is a receipt-binding REFINEMENT, but it is load-bearing and carries a tooth
            // (an observable receipt that discriminates), so it is registered here too.
            theorem: "integrity_guarantee @ AssuranceCase.lean:412",
            tooth: HasBitingTooth {
                fires: "writeCell0_receipt_eq @ Dregg2/Circuit/Argus/Receipt.lean",
                bites: "writeCell0_receipt_observable @ Dregg2/Circuit/Argus/Receipt.lean",
            },
        },
        // ── the standalone property apexes ──────────────────────────────────────────────────────────
        Row {
            theorem: "introduce_non_amplifying (IsNonAmplifying) @ Exec/EffectsAuthority.lean:197",
            tooth: HasBitingTooth {
                fires: "introduce_non_amplifying_satisfiable @ Dregg2/Exec/EffectsAuthority.lean",
                bites: "introduce_non_amplifying_teeth @ Dregg2/Exec/EffectsAuthority.lean",
            },
        },
        Row {
            theorem: "reshareN_attenuates @ Deos/Membrane.lean:122",
            tooth: HasBitingTooth {
                fires: "reshareN_attenuates_satisfiable @ Dregg2/Deos/Membrane.lean",
                bites: "reshare_refuses_amplification @ Dregg2/Deos/Membrane.lean",
            },
        },
        Row {
            theorem: "reachable_total_zero @ Exec/ReachableConservation.lean:49",
            tooth: HasBitingTooth {
                fires: "reachable_total_zero_satisfiable @ Dregg2/Verify/KeystoneAuditConservation.lean",
                bites: "reachable_total_zero_teeth @ Dregg2/Verify/KeystoneAuditConservation.lean",
            },
        },
        Row {
            theorem: "deposit_price_non_decreasing @ Deos/Vault.lean:187",
            tooth: HasBitingTooth {
                fires: "established_deposit_accepts @ Dregg2/Deos/Vault.lean",
                bites: "dilution_rejected @ Dregg2/Deos/Vault.lean",
            },
        },
        // ── budget_never_overdrawn (PrepaidLease, the Lease economic world-property) ──────────────────
        // Survey gap #4 (`META-REVIEW-GATE-AND-DECOUC.md` §1.3): a load-bearing economic invariant the
        // manifest's OWN row-21 comment named as a Vault/escrow peer, yet had no gate row. fires — an
        // honest opened-lease discharge is ACCEPTED (`opened_discharge_accepts`); bites — a discharge
        // whose committed remaining budget cannot cover the rent is REJECTED (`insufficient_budget_rejected`,
        // the refusal half the theorem's own docstring names).
        Row {
            theorem: "budget_never_overdrawn @ Deos/PrepaidLease.lean:378",
            tooth: HasBitingTooth {
                fires: "opened_discharge_accepts @ Dregg2/Deos/PrepaidLease.lean",
                bites: "insufficient_budget_rejected @ Dregg2/Deos/PrepaidLease.lean",
            },
        },
        Row {
            theorem: "settlement_soundness @ Metatheory/SettlementSoundness.lean:153",
            tooth: HasBitingTooth {
                fires: "deployedSettle_nonvacuous @ Metatheory/SettlementSoundness.lean",
                bites: "deployedSettle_revoke_unsettleable @ Metatheory/SettlementSoundness.lean",
            },
        },
        Row {
            theorem: "mintA_authorized (supply) @ Circuit/Spec/SupplyCreation.lean",
            tooth: HasBitingTooth {
                fires: "mintA_authorized_satisfiable @ Dregg2/Verify/KeystoneAuditSupply.lean",
                bites: "mintA_rejects_unauthorized @ Dregg2/Circuit/Spec/supplycreation.lean",
            },
        },
        Row {
            theorem: "captp/token/custom_sound (AuthModes) @ Exec/AuthModes.lean",
            tooth: HasBitingTooth {
                fires: "custom_sound_satisfiable @ Dregg2/Exec/AuthModes.lean",
                bites: "custom_sound_teeth @ Dregg2/Exec/AuthModes.lean",
            },
        },
        // ── the eight carrier BindingFromFolds (Dregg2/Circuit/*BindingFromFold.lean) ───────────────
        // Each: honest_companion_fires (a real aggregate verifies) + forged_*_unsat_demo (a forged
        // fold is UNSAT — the biting refutation). The eight share the `honest_companion_fires` name, so
        // each row now PINS the carrier's own file — deleting any one carrier's fires reds the gate.
        Row {
            theorem: "custom_binding_from_fold @ Circuit/CustomBindingFromFold.lean:147",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires @ Dregg2/Circuit/CustomBindingFromFold.lean",
                bites: "forged_unsat_demo @ Dregg2/Circuit/CustomBindingFromFold.lean",
            },
        },
        Row {
            theorem: "factory_binding_from_fold @ Circuit/FactoryBindingFromFold.lean:145",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires @ Dregg2/Circuit/FactoryBindingFromFold.lean",
                bites: "forged_childvk_unsat_demo @ Dregg2/Circuit/FactoryBindingFromFold.lean",
            },
        },
        Row {
            theorem: "bridge_binding_from_fold @ Circuit/BridgeBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires @ Dregg2/Circuit/BridgeBindingFromFold.lean",
                bites: "forged_mint_hash_unsat_demo @ Dregg2/Circuit/BridgeBindingFromFold.lean",
            },
        },
        Row {
            theorem: "sovereign_binding_from_fold @ Circuit/SovereignBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires @ Dregg2/Circuit/SovereignBindingFromFold.lean",
                bites: "forged_keycommit_unsat_demo @ Dregg2/Circuit/SovereignBindingFromFold.lean",
            },
        },
        Row {
            theorem: "membership_binding_from_fold @ Circuit/MembershipBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires @ Dregg2/Circuit/MembershipBindingFromFold.lean",
                bites: "forged_tuple_unsat_demo @ Dregg2/Circuit/MembershipBindingFromFold.lean",
            },
        },
        Row {
            theorem: "dsl_binding_from_fold @ Circuit/DslBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires @ Dregg2/Circuit/DslBindingFromFold.lean",
                bites: "forged_rc_unsat_demo @ Dregg2/Circuit/DslBindingFromFold.lean",
            },
        },
        Row {
            theorem: "hatchery_binding_from_fold @ Circuit/HatcheryBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires @ Dregg2/Circuit/HatcheryBindingFromFold.lean",
                bites: "forged_contract_unsat_demo @ Dregg2/Circuit/HatcheryBindingFromFold.lean",
            },
        },
        Row {
            theorem: "deco_binding_from_fold @ Circuit/DecoBindingFromFold.lean",
            tooth: HasBitingTooth {
                fires: "honest_companion_fires @ Dregg2/Circuit/DecoBindingFromFold.lean",
                bites: "forged_payment_hash_unsat_demo @ Dregg2/Circuit/DecoBindingFromFold.lean",
            },
        },
        // ── SealedEscrow's economic no-theft world-property (Deos/SealedEscrow.lean §9) ──────────────
        Row {
            theorem: "sealedescrow_no_theft @ Deos/SealedEscrow.lean:753",
            tooth: HasBitingTooth {
                fires: "honest_swap_reachable @ Dregg2/Deos/SealedEscrow.lean",
                bites: "halfopen_theft_unreachable @ Dregg2/Deos/SealedEscrow.lean",
            },
        },
        // ── DECO payment-attestation UNFORGEABILITY (survey gap #1, rung 4 — the REAL reduction) ──────
        Row {
            theorem: "deco_attestation_unforgeable @ Crypto/DecoUnforgeable.lean",
            tooth: HasBitingTooth {
                fires: "attestation_fires @ Dregg2/Crypto/DecoUnforgeable.lean",
                bites: "attestation_bites @ Dregg2/Crypto/DecoUnforgeable.lean",
            },
        },
        // ── DECO attestation "UC" — DOWNGRADED: a wrapper-of-22, not a distinct summit ────────────────
        // The meta-review found the rung-5 "UC-realization" delta over rung-4 was a `rfl`-vacuous
        // conjunct; `UCRealizesFAtt` is now DEFINITIONALLY `AttRealizes` (rung-4 soundness). This row is
        // retained ONLY to keep its (real, soundness-conjunct) teeth registered — it is NOT counted as a
        // distinct world-property. `decoSim_works` fires the toy simulator's accept; `forge_not_ucRealizes`
        // bites the soundness leg over the forge kernel (identical content to row 22's `attestation_bites`).
        Row {
            theorem: "decoUC_realizes (wrapper-of-22, computational UC UNBUILT) @ Crypto/DecoUC.lean",
            tooth: HasBitingTooth {
                fires: "decoSim_works @ Dregg2/Crypto/DecoUC.lean",
                bites: "forge_not_ucRealizes @ Dregg2/Crypto/DecoUC.lean",
            },
        },
    ]
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// LEDGER 2 — ACCEPT-SATISFIABILITY (every GovernedDynamics instance's accept is inhabited)
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// One `GovernedDynamics` instance + its `∃ c, accept (run c)` satisfiability companion.
#[derive(Clone, Debug)]
struct SatRow {
    /// The schema instance whose accept-set must be shown inhabited.
    instance: &'static str,
    /// The NAMED satisfiability theorem `"name @ Rel/Path.lean"`. A `*_of_floor` name marks that
    /// satisfiability rests on an explicit realizability floor (the vacuity risk made VISIBLE).
    satisfiable: &'static str,
    /// Whether accept folds a realizability floor (PROVEN concrete vs NAMED-FLOOR) — for the report.
    #[allow(dead_code)]
    rests_on_floor: bool,
}

/// THE SATISFIABILITY LEDGER — one row per `GovernedDynamics` instance in `Metatheory/Adversary/*`.
/// A `*_bites` tooth proves `accept ≠ True`; it does NOT prove `∃ c, accept c`. So an instance whose
/// accept is UNSATISFIABLE would satisfy `governed_holds` vacuously and escape the world-property gate.
/// Each row pins the instance's satisfiability witness (proven concrete, or a named `_of_floor`).
fn satisfiability_manifest() -> Vec<SatRow> {
    vec![
        SatRow {
            instance: "polisDynamics",
            satisfiable: "polis_accept_satisfiable @ Metatheory/Adversary/Schema.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "circuitDynamics",
            satisfiable: "circuit_accept_satisfiable_of_floor @ Metatheory/Adversary/Schema.lean",
            rests_on_floor: true, // accept folds WitnessDecodes
        },
        SatRow {
            instance: "settlementDynamics",
            satisfiable: "settlement_accept_satisfiable @ Metatheory/Adversary/Instances.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "wholeHistoryDynamics",
            satisfiable: "wholeHistory_accept_satisfiable_of_floor @ Metatheory/Adversary/Instances.lean",
            rests_on_floor: true, // accept folds EngineSound
        },
        // The eight carriers — each carrier file's `honestSat` is a CONCRETE satisfying fold at the
        // honest engine (accept := Sat*Fold holds at honestFold). Pinned per-carrier-file.
        SatRow {
            instance: "customCarrierDynamics",
            satisfiable: "honestSat @ Dregg2/Circuit/CustomBindingFromFold.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "factoryCarrierDynamics",
            satisfiable: "honestSat @ Dregg2/Circuit/FactoryBindingFromFold.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "sovereignCarrierDynamics",
            satisfiable: "honestSat @ Dregg2/Circuit/SovereignBindingFromFold.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "membershipCarrierDynamics",
            satisfiable: "honestSat @ Dregg2/Circuit/MembershipBindingFromFold.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "dslCarrierDynamics",
            satisfiable: "honestSat @ Dregg2/Circuit/DslBindingFromFold.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "bridgeCarrierDynamics",
            satisfiable: "honestSat @ Dregg2/Circuit/BridgeBindingFromFold.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "hatcheryCarrierDynamics",
            satisfiable: "honestSat @ Dregg2/Circuit/HatcheryBindingFromFold.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "decoCarrierDynamics",
            satisfiable: "honestSat @ Dregg2/Circuit/DecoBindingFromFold.lean",
            rests_on_floor: false,
        },
        SatRow {
            instance: "assuranceApexDynamics",
            satisfiable: "apex_accept_satisfiable_of_floor @ Metatheory/Adversary/Instances.lean",
            rests_on_floor: true, // accept folds hcov/EngineSound/genesis
        },
        SatRow {
            instance: "attestationDynamics",
            satisfiable: "attestation_accept_satisfiable @ Metatheory/Adversary/Instances.lean",
            rests_on_floor: false,
        },
        SatRow {
            // Same accept-set as attestationDynamics (KD.verify); the reference witness covers both.
            instance: "attestationUCDynamics",
            satisfiable: "attestation_accept_satisfiable @ Metatheory/Adversary/Instances.lean",
            rests_on_floor: false,
        },
    ]
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE CHECKERS (pure — shared by the real gates and the bite-proof tests)
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// The verdict on one world-property row. `Some(finding)` when UNCOVERED (the gate must red).
fn row_finding(row: &Row, index: &DeclIndex) -> Option<String> {
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
            if let Some(p) = companion_problem(fires, index) {
                problems.push(format!("fires: {p}"));
            }
            if let Some(p) = companion_problem(bites, index) {
                problems.push(format!("bites: {p}"));
            }
            if problems.is_empty() {
                None
            } else {
                Some(format!("{} — {}", row.theorem, problems.join("; ")))
            }
        }
    }
}

/// Every uncovered world-property row (the gate reds iff this is non-empty).
fn uncovered(rows: &[Row], index: &DeclIndex) -> Vec<String> {
    rows.iter().filter_map(|r| row_finding(r, index)).collect()
}

/// The verdict on one satisfiability row. `Some(finding)` when the companion is not grounded.
fn sat_finding(row: &SatRow, index: &DeclIndex) -> Option<String> {
    companion_problem(row.satisfiable, index)
        .map(|p| format!("{} (accept satisfiability) — {}", row.instance, p))
}

fn sat_uncovered(rows: &[SatRow], index: &DeclIndex) -> Vec<String> {
    rows.iter().filter_map(|r| sat_finding(r, index)).collect()
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE LEAN-SOURCE SCAN (grounds the ledger to the real tree, with kind + relative-file)
// ─────────────────────────────────────────────────────────────────────────────────────────────────

fn metatheory_dir() -> PathBuf {
    // `<workspace>/circuit/` is CARGO_MANIFEST_DIR; the Lean tree is a sibling.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("metatheory")
}

/// Collect every `theorem`/`lemma`/`def`/`abbrev` declaration under `metatheory/**/*.lean` with its
/// kind and file (relative to the metatheory root, `/`-separated).
fn scan_lean_decls(root: &Path) -> DeclIndex {
    let mut index: DeclIndex = HashMap::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                let skip = matches!(
                    path.file_name().and_then(|s| s.to_str()),
                    Some(".lake") | Some("_attic") | Some("build") | Some("target")
                );
                if !skip {
                    stack.push(path);
                }
            } else if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                let rel = path
                    .strip_prefix(root)
                    .unwrap_or(&path)
                    .to_string_lossy()
                    .replace('\\', "/");
                if let Ok(src) = std::fs::read_to_string(&path) {
                    collect_decls(&src, &rel, &mut index);
                }
            }
        }
    }
    index
}

/// Extract declarations from Lean source. Matches lines whose first token (after `private`/`protected`/
/// `noncomputable` and any `@[...]` attribute tokens) is a decl keyword, recording the following ident.
fn collect_decls(src: &str, rel_file: &str, index: &mut DeclIndex) {
    for raw in src.lines() {
        let line = raw.trim_start();
        let mut toks = line.split_whitespace();
        let Some(mut first) = toks.next() else {
            continue;
        };
        // step over decl modifiers and attribute tokens
        while matches!(first, "private" | "protected" | "noncomputable") || first.starts_with('@') {
            match toks.next() {
                Some(t) => first = t,
                None => break,
            }
        }
        let kind = match first {
            "theorem" => Kind::Theorem,
            "lemma" => Kind::Lemma,
            "def" => Kind::Def,
            "abbrev" => Kind::Abbrev,
            _ => continue,
        };
        if let Some(name) = toks.next() {
            let ident: String = name
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'' || *c == '.')
                .collect();
            if ident.is_empty() {
                continue;
            }
            // register both the fully-qualified tail and the bare last segment (companions are
            // referenced unqualified in the ledger).
            let loc = DeclLoc {
                kind,
                file: rel_file.to_string(),
            };
            if let Some(last) = ident.rsplit('.').next() {
                index.entry(last.to_string()).or_default().push(loc.clone());
            }
            index.entry(ident).or_default().push(loc);
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE GATES
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// THE META-GATE (world-property teeth): every load-bearing security-property theorem in the manifest
/// has a registered, source-grounded (theorem-kind + right-file) biting non-vacuity tooth.
#[test]
fn every_security_property_has_biting_tooth() {
    let manifest = security_property_manifest();
    assert!(
        manifest.len() >= 24,
        "manifest shrank below the known load-bearing set ({} rows) — a security property was \
         dropped from the gate (see docs/audit/SECURITY-PROPERTY-MAP.md)",
        manifest.len()
    );

    let root = metatheory_dir();
    let index = scan_lean_decls(&root);
    assert!(
        index.len() > 500,
        "Lean-source scan found only {} decls under {} — the metatheory tree is missing or \
         unreadable; the source-grounding leg of this gate cannot run (fail loudly, never skip)",
        index.len(),
        root.display()
    );

    let findings = uncovered(&manifest, &index);
    assert!(
        findings.is_empty(),
        "SECURITY-PROPERTY NON-VACUITY GATE RED — {} load-bearing theorem(s) lack a registered, \
         source-grounded biting tooth (a green that would not red when the guard breaks):\n  - {}",
        findings.len(),
        findings.join("\n  - ")
    );
}

/// THE SATISFIABILITY GATE: every `GovernedDynamics` instance has a NAMED, source-grounded
/// `∃ c, accept (run c)` companion — so no instance governs vacuously via an unsatisfiable accept.
#[test]
fn every_governed_instance_has_satisfiable_accept() {
    let manifest = satisfiability_manifest();
    assert!(
        manifest.len() >= 15,
        "satisfiability manifest shrank below the known GovernedDynamics instance set ({} rows) — an \
         instance lost its accept-satisfiability companion (see Metatheory/Adversary/*)",
        manifest.len()
    );

    let root = metatheory_dir();
    let index = scan_lean_decls(&root);
    assert!(
        index.len() > 500,
        "Lean-source scan found only {} decls under {} — the source-grounding leg cannot run",
        index.len(),
        root.display()
    );

    let findings = sat_uncovered(&manifest, &index);
    assert!(
        findings.is_empty(),
        "ACCEPT-SATISFIABILITY GATE RED — {} GovernedDynamics instance(s) lack a source-grounded \
         `∃ c, accept c` companion (an instance whose accept is unsatisfiable governs vacuously):\n  - {}",
        findings.len(),
        findings.join("\n  - ")
    );
}

/// PROOF THAT THE GATE BITES — the meta-gate is itself non-vacuous, and each STRENGTHENED check is
/// exhibited to red the way it is supposed to (a coverage gate that only ever passes is the exact
/// laundering it forbids).
#[test]
fn meta_gate_bites() {
    // A rich index (so a fully-grounded row would pass) EXCEPT for the fakes below. Every real decl is
    // a THEOREM in its home file `X.lean`.
    let home = |kind: Kind| DeclLoc {
        kind,
        file: "X.lean".to_string(),
    };
    let mut index: DeclIndex = HashMap::new();
    index.insert("real_fires".into(), vec![home(Kind::Theorem)]);
    index.insert("real_bites".into(), vec![home(Kind::Theorem)]);
    // a name that exists ONLY as a `def` in its home (the def-downgrade fake).
    index.insert("def_bites".into(), vec![home(Kind::Def)]);
    // a name that exists as a theorem, but in a DIFFERENT file (the wrong-file fake).
    index.insert(
        "moved_bites".into(),
        vec![DeclLoc {
            kind: Kind::Theorem,
            file: "Elsewhere.lean".to_string(),
        }],
    );

    let good_fires = "real_fires @ X.lean";
    let good_bites = "real_bites @ X.lean";

    // (a) a Missing row REDS.
    let missing = vec![Row {
        theorem: "fake_property @ Nowhere.lean:1",
        tooth: Tooth::Missing("owes a teeth"),
    }];
    assert!(
        !uncovered(&missing, &index).is_empty(),
        "gate FAILED TO BITE a Missing row — it would pass a hollow security claim"
    );

    // (b) a SpotCheckedOnly row WITHOUT a `promote:` lane REDS; WITH one, passes.
    let spot_bad = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::SpotCheckedOnly("only #guards exist"),
    }];
    assert!(
        !uncovered(&spot_bad, &index).is_empty(),
        "gate FAILED TO BITE an un-laned SpotCheckedOnly row"
    );
    let spot_ok = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::SpotCheckedOnly("only #guards; promote: name the theorems next sprint"),
    }];
    assert!(
        uncovered(&spot_ok, &index).is_empty(),
        "a SpotCheckedOnly row WITH a promote: lane must be allowlisted"
    );

    // (c) a HasBitingTooth naming a companion ABSENT from the source REDS (the stale-ledger catch).
    let stale = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::HasBitingTooth {
            fires: good_fires,
            bites: "companion_that_was_deleted @ X.lean",
        },
    }];
    assert!(
        !uncovered(&stale, &index).is_empty(),
        "gate FAILED TO BITE a HasBitingTooth naming a deleted companion — the ledger could go stale"
    );

    // (d) an empty companion name REDS.
    let empty = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::HasBitingTooth {
            fires: good_fires,
            bites: " @ X.lean",
        },
    }];
    assert!(
        !uncovered(&empty, &index).is_empty(),
        "gate FAILED TO BITE an empty `bites` companion name"
    );

    // (e) THE NEW def-downgrade BITE: a companion registered against a name that exists only as a
    //     `def` (e.g. `def bites := True`) REDS — the old bare-name check would have PASSED this.
    let downgraded = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::HasBitingTooth {
            fires: good_fires,
            bites: "def_bites @ X.lean",
        },
    }];
    let f = uncovered(&downgraded, &index);
    assert!(
        f.iter().any(|s| s.contains("not a theorem/lemma")),
        "gate FAILED TO BITE a `def`-downgraded tooth (must reject non-theorem companions): {f:?}"
    );

    // (f) THE NEW wrong-file BITE: a companion whose theorem exists but in a DIFFERENT file than the
    //     row pins REDS — the old global-name scan would have PASSED this.
    let wrong_file = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::HasBitingTooth {
            fires: good_fires,
            bites: "moved_bites @ X.lean", // really lives in Elsewhere.lean
        },
    }];
    let f = uncovered(&wrong_file, &index);
    assert!(
        f.iter().any(|s| s.contains("wrong-file")),
        "gate FAILED TO BITE a wrong-file tooth (must reject a companion outside its pinned home): {f:?}"
    );

    // (g) a fully-grounded HasBitingTooth (theorem, right file) PASSES (not red-for-everything).
    let good = vec![Row {
        theorem: "fake @ X.lean:1",
        tooth: Tooth::HasBitingTooth {
            fires: good_fires,
            bites: good_bites,
        },
    }];
    assert!(
        uncovered(&good, &index).is_empty(),
        "gate REDS a fully-grounded row — it is red-for-everything (vacuously failing), not discriminating"
    );

    // (h) THE DECISIVE REAL BITE: take the REAL manifest and DELETE one real tooth name from the
    //     index (simulating a removed Lean companion). The gate must red on exactly that row.
    let manifest = security_property_manifest();
    let mut index_full = scan_lean_decls(&metatheory_dir());
    if index_full.len() > 500 {
        let removed = index_full.remove("reachable_total_zero_teeth");
        assert!(
            removed.is_some(),
            "expected `reachable_total_zero_teeth` to be present in the real source"
        );
        let findings = uncovered(&manifest, &index_full);
        assert!(
            findings
                .iter()
                .any(|f| f.contains("reachable_total_zero_teeth")),
            "removing the real `reachable_total_zero_teeth` tooth did NOT red the gate — not genuinely \
             source-grounded"
        );

        // (i) THE DECISIVE REAL FILE-MOVE BITE: relocate a real carrier's `honest_companion_fires` to a
        //     WRONG file only; the file-pinned gate must red the carrier row it no longer lives in.
        let mut index_moved = scan_lean_decls(&metatheory_dir());
        index_moved.insert(
            "honest_companion_fires".into(),
            vec![DeclLoc {
                kind: Kind::Theorem,
                file: "Dregg2/Circuit/CustomBindingFromFold.lean".to_string(),
            }],
        );
        let findings = uncovered(&manifest, &index_moved);
        assert!(
            findings
                .iter()
                .any(|f| f.contains("factory_binding_from_fold")
                    || f.contains("bridge_binding_from_fold")),
            "collapsing all 8 carriers' `honest_companion_fires` to ONE file did NOT red the other \
             carriers — per-carrier file pinning is not enforced"
        );
    }
}

/// Visibility probe: the tooths this program relies on are present and grounded (theorem-kind, right
/// file), so a future edit that deletes/moves them must consciously touch this gate.
#[test]
fn pillar_4b_added_tooths_are_grounded() {
    let index = scan_lean_decls(&metatheory_dir());
    if index.len() <= 500 {
        return; // scan unavailable in this environment; the main gate already fails loudly.
    }
    // (name, pinned file) pairs added/strengthened by the non-vacuity lanes.
    for spec in [
        "reachable_total_zero_teeth @ Dregg2/Verify/KeystoneAuditConservation.lean",
        "reshareN_attenuates_satisfiable @ Dregg2/Deos/Membrane.lean",
        // fix 4 — the newly-registered Lease economic world-property tooth.
        "insufficient_budget_rejected @ Dregg2/Deos/PrepaidLease.lean",
        "opened_discharge_accepts @ Dregg2/Deos/PrepaidLease.lean",
        // fix 2 — the accept-satisfiability companions.
        "polis_accept_satisfiable @ Metatheory/Adversary/Schema.lean",
        "settlement_accept_satisfiable @ Metatheory/Adversary/Instances.lean",
        "attestation_accept_satisfiable @ Metatheory/Adversary/Instances.lean",
    ] {
        assert!(
            companion_problem(spec, &index).is_none(),
            "grounded tooth `{spec}` is missing/mis-kinded/moved — added by a non-vacuity lane, must persist"
        );
    }
}
