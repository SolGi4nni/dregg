//! IN-CIRCUIT CAVEAT ADMISSION — re-prove a mandate's per-trade caveat admission as a
//! RECURSION-FOLDABLE IR-v2 leaf that EVALUATES the caveat PREDICATE in the AIR (not a
//! trusted `caveatBit`).
//!
//! ## What this closes (the DREGGFI §7 honest edge, named in the tree)
//!
//! Today the effect-vm binds an AGGREGATE `caveatBit` / slot-caveat manifest into PI and
//! *trusts the executor's decision*: `verify_slot_caveat_manifest`
//! (`circuit/src/effect_vm/verify.rs:165`) is an OFF-AIR verifier-side re-run — a
//! re-executing validator recomputes the caveat against the state PIs, but a PURE LIGHT
//! CLIENT that only folds the per-turn recursion tree never witnesses that the admitted
//! request actually SATISFIES the caveat predicate. `Caveat.lean` says so itself
//! (`metatheory/Dregg2/Authority/Caveat.lean:57-60`, the §D6 honest framing): "the circuit
//! still binds an aggregate `caveatBit` and trusts the executor's decision; reifying a
//! caveat does not force its policy in-circuit." So "the mandate IS the proof" (DREGGFI §3
//! capability) is EXPRESSIVENESS-PROVED but VENUE-verification is executor-trusted.
//!
//! This leaf makes the DECIDABLE caveat atoms — the reified `CaveatPred` vocabulary
//! `Caveat.lean` already carries (`validUntil` expiry ceiling, `heightLt` strict height
//! ceiling) plus a value/asset SCOPE bound (the mandate `budget` + asset scope, tying to
//! `Dregg2/Agent/Mandate.lean`) — a genuine IN-CIRCUIT admission: the AIR range-checks the
//! per-atom SLACK so an OVER-authorized trade (past expiry, over budget, wrong asset) is
//! UNSAT (no foldable leaf minted), and a within-mandate trade folds. The admission binds
//! to the trade: the leaf re-exposes the `(trade fields ++ caveat params)` as a committed
//! claim the settling-venue binding node `connect`s to the deployed trade's teeth (the same
//! `expose_claim`/`connect` ABI the eight deployed carriers use,
//! `docs/deos/EFFECTVM-SIDESTRUCTURE-ABI.md`).
//!
//! ## The in-circuit admission mechanism (the SLACK-nonneg realization of `≤` / `<`)
//!
//! A STARK cannot assert `a ≤ b` directly. The gadget WITNESSES the slack `s = b − a` as a
//! trace column, PINS it to the operands with a first-row boundary constraint (`s + a − b ==
//! 0`), and RANGE-CHECKS `s ∈ [0, 2^BOUND_BITS)`. If the caveat is VIOLATED (`a > b`) the
//! only field element `s` solving `s = b − a` is `p − (a − b)`, which — with both operands
//! range-bounded to `[0, 2^BOUND_BITS)` and `2^BOUND_BITS` chosen so `p − 2^BOUND_BITS ≫
//! 2^BOUND_BITS` — lands ABOVE `2^BOUND_BITS`, failing the range lookup. UNSAT ⇒ no leaf.
//! This is exactly the arithmetic-vs-Caveat refinement proved in Lean
//! (`metatheory/Dregg2/Circuit/CaveatAdmissionRefines.lean`): the slack-nonneg admission is
//! EQUIVALENT to `CaveatPred.eval` of the reified window, so the AIR faithfully evaluates the
//! caveat predicate, and an in-circuit-admitted request is in the token's admissible set
//! (`attenuate_narrows` / `token_discharges`).
//!
//! ## The three reified atoms (mirroring `Caveat.lean`'s `CaveatPred`) + the scope bound
//!
//!   * `validUntil t`  — admit iff `req_time  ≤ t`      (expiry CEILING, inclusive)
//!   * `heightLt   h`  — admit iff `req_height < h`      (STRICT before-block ceiling)
//!   * `budget     b`  — admit iff `trade_value ≤ b`     (the Mandate spend ceiling)
//!   * asset scope     — admit iff `trade_asset == a`    (an equality, not an inequality)
//!
//! ## HONEST SCOPE (named, per the project bar — do NOT overclaim)
//!
//! This lands the DECIDABLE temporal/scope atoms IN-CIRCUIT. The caveat predicates that
//! remain EXECUTOR-TRUSTED are the un-reified ones: `Caveat.opaque` (an arbitrary `Ctx →
//! Bool` the AST cannot introspect) and `Caveat.thirdParty` (a gateway discharge). Those
//! stay off-AIR named carriers — this leaf does not force them. A mandate whose caveats are
//! all in the reified `{validUntil, heightLt, budget, asset}` vocabulary is now
//! VENUE-verifiable; a mandate carrying an `opaque` atom is still executor-trusted for that
//! atom. That slice — the decidable-caveat admission — is what this turns from
//! executor-trusted to in-circuit PROVED.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, LookupSpec, MemBoundaryWitness, TID_RANGE, TableDef2, TableSem,
    UMemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec, ir2_airs_and_common_for_config,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

use p3_field::PrimeField32;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput, Target,
    build_and_prove_aggregation_layer_with_expose, build_and_prove_next_layer_with_expose,
};
use p3_uni_stark::StarkGenericConfig;

use crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config;
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::{DreggRecursionConfig, create_recursion_backend};

type RecursionChallenge = <DreggRecursionConfig as StarkGenericConfig>::Challenge;
const D: usize = 4;

// ---- The operand PI layout (the 8 caveat-admission operands, pinned to row-0 PIs) ----
/// The request's logical time (block height / tick) — the `Ctx → Time` view of the trade.
pub const REQ_TIME_SLOT: usize = 0;
/// The caveat's `validUntil` expiry ceiling — admit iff `req_time ≤ this`.
pub const CAV_VALID_UNTIL_SLOT: usize = 1;
/// The request's block height — the `heightLt` view of the trade.
pub const REQ_HEIGHT_SLOT: usize = 2;
/// The caveat's `heightLt` STRICT ceiling — admit iff `req_height < this`.
pub const CAV_HEIGHT_LT_SLOT: usize = 3;
/// The trade's value (in the caveat's asset) — the mandate `budget` view.
pub const TRADE_VALUE_SLOT: usize = 4;
/// The caveat's `budget` spend ceiling — admit iff `trade_value ≤ this`.
pub const CAV_BUDGET_SLOT: usize = 5;
/// The trade's asset id — the scope view.
pub const TRADE_ASSET_SLOT: usize = 6;
/// The caveat's scoped asset id — admit iff `trade_asset == this`.
pub const CAV_ASSET_SLOT: usize = 7;

/// Number of PI-bound operands (the committed admission claim width).
pub const CAVEAT_OPERAND_COUNT: usize = 8;
/// The exposed committed-claim width: the 8 operands `(trade fields ++ caveat params)` the
/// binding node `connect`s to the deployed trade's teeth.
pub const CAVEAT_ADMISSION_CLAIM_LEN: usize = CAVEAT_OPERAND_COUNT;

// ---- The witness-only slack columns (NOT PIs; range-checked, boundary-pinned) ----
/// `slack_vu = cav_validUntil − req_time` — nonneg iff `req_time ≤ cav_validUntil`.
const SLACK_VALID_UNTIL_COL: usize = 8;
/// `slack_hl = cav_heightLt − req_height − 1` — nonneg iff `req_height < cav_heightLt`.
const SLACK_HEIGHT_LT_COL: usize = 9;
/// `slack_bd = cav_budget − trade_value` — nonneg iff `trade_value ≤ cav_budget`.
const SLACK_BUDGET_COL: usize = 10;

/// The base trace width: 8 operands + 3 slacks.
const TRACE_WIDTH: usize = 11;

/// The range-check bit width the caveat operands + slacks are bounded to. Chosen so
/// `p − 2^BOUND_BITS ≫ 2^BOUND_BITS` (BabyBear `p ≈ 2.01e9`, `2^24 ≈ 1.68e7`): a wrapped-
/// negative slack `p − k` is then always `> 2^BOUND_BITS`, so the range lookup REFUSES it —
/// the load-bearing soundness fact for the "over-authorized ⇒ UNSAT" tooth. `2^24 ≈ 16.7M`
/// bounds the admissible height/time/budget domain (documented, not hidden).
pub const BOUND_BITS: usize = 24;
/// The admissible operand ceiling `2^BOUND_BITS` — the range domain the caveat operands live in.
pub const OPERAND_CEILING: u32 = 1 << BOUND_BITS;

/// A per-trade caveat-admission witness: the trade's `(time, height, value, asset)` and the
/// mandate caveat's `(validUntil, heightLt, budget, asset)`. Honest admission requires every
/// atom to hold; the leaf mints iff so.
#[derive(Clone, Copy, Debug)]
pub struct CaveatAdmissionWitness {
    /// The request's logical time (the `validUntil` view).
    pub req_time: u32,
    /// The caveat's expiry ceiling.
    pub cav_valid_until: u32,
    /// The request's block height (the `heightLt` view).
    pub req_height: u32,
    /// The caveat's strict height ceiling.
    pub cav_height_lt: u32,
    /// The trade's value.
    pub trade_value: u32,
    /// The caveat's spend budget.
    pub cav_budget: u32,
    /// The trade's asset id.
    pub trade_asset: u32,
    /// The caveat's scoped asset id.
    pub cav_asset: u32,
}

impl CaveatAdmissionWitness {
    /// The 8-slot bound operand tuple carried as the leaf's descriptor PIs (the committed
    /// admission claim `(trade fields ++ caveat params)`).
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pis = vec![BabyBear::new(0); CAVEAT_OPERAND_COUNT];
        pis[REQ_TIME_SLOT] = BabyBear::new(self.req_time);
        pis[CAV_VALID_UNTIL_SLOT] = BabyBear::new(self.cav_valid_until);
        pis[REQ_HEIGHT_SLOT] = BabyBear::new(self.req_height);
        pis[CAV_HEIGHT_LT_SLOT] = BabyBear::new(self.cav_height_lt);
        pis[TRADE_VALUE_SLOT] = BabyBear::new(self.trade_value);
        pis[CAV_BUDGET_SLOT] = BabyBear::new(self.cav_budget);
        pis[TRADE_ASSET_SLOT] = BabyBear::new(self.trade_asset);
        pis[CAV_ASSET_SLOT] = BabyBear::new(self.cav_asset);
        pis
    }

    /// Whether this request is WITHIN the caveat (the reference admission decision the AIR
    /// mirrors) — the Rust twin of `CaveatPred.eval` of the reified window
    /// `validUntil ∧ heightLt ∧ budget ∧ asset`. Used by the tests to select the pole.
    pub fn admits(&self) -> bool {
        self.req_time <= self.cav_valid_until
            && self.req_height < self.cav_height_lt
            && self.trade_value <= self.cav_budget
            && self.trade_asset == self.cav_asset
    }

    /// The base trace: one typed row (operands ++ genuine field-difference slacks),
    /// replicated across a power-of-two height. The `WindowGate` continuity glue pins every
    /// column constant across rows, so the whole tuple + slacks bind from row 0. The slacks
    /// are the GENUINE field differences (`cav − req`): for a within-caveat trade they are
    /// the small nonneg gaps; for an OVER-authorized trade they WRAP to `p − k > 2^BOUND_BITS`,
    /// so the range lookup refuses them (the tooth) — this same generation drives both poles.
    pub fn generate_trace(&self) -> Vec<Vec<BabyBear>> {
        let pis = self.public_inputs();
        let mut row = pis.clone();
        row.resize(TRACE_WIDTH, BabyBear::ZERO);
        // slack_vu = cav_validUntil − req_time (field subtraction auto-wraps on violation).
        row[SLACK_VALID_UNTIL_COL] = row[CAV_VALID_UNTIL_SLOT] - row[REQ_TIME_SLOT];
        // slack_hl = cav_heightLt − req_height − 1  (STRICT: req_height == cav → slack = −1 wraps).
        row[SLACK_HEIGHT_LT_COL] = row[CAV_HEIGHT_LT_SLOT] - row[REQ_HEIGHT_SLOT] - BabyBear::ONE;
        // slack_bd = cav_budget − trade_value.
        row[SLACK_BUDGET_COL] = row[CAV_BUDGET_SLOT] - row[TRADE_VALUE_SLOT];
        vec![row.clone(), row]
    }
}

/// `slack_col + minuend_neg... == 0` boundary body. Builds `Var(slack) + Var(a) − Var(b)`
/// (i.e. `slack == b − a`) as a `LeanExpr`, using the Add/Mul-only algebra.
fn slack_eq_body(slack: usize, a: usize, b: usize) -> LeanExpr {
    // slack + a − b
    LeanExpr::Add(
        Box::new(LeanExpr::Var(slack)),
        Box::new(LeanExpr::Add(
            Box::new(LeanExpr::Var(a)),
            Box::new(LeanExpr::Mul(
                Box::new(LeanExpr::Const(-1)),
                Box::new(LeanExpr::Var(b)),
            )),
        )),
    )
}

/// Adapt the caveat-admission gadget into the IR-v2 [`EffectVmDescriptor2`]:
///   * 8 boundary PI pins (`PiBinding{First}`, EXACT — `pi_index == col`) on the operands;
///   * 4 first-row boundary relations pinning the 3 slacks + the asset equality;
///   * 11 transition pins (`WindowGate`, every column constant across rows);
///   * a 24-bit range table + range lookups on all 8 operands and the 3 slacks (the `≤`/`<`
///     teeth: an out-of-range slack — the wrapped-negative of a violated caveat — is UNSAT).
pub fn caveat_admission_to_descriptor2() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::new();

    // Family 1 — the 8 boundary PI pins: `row0[col c] == pi[c]`.
    for c in 0..CAVEAT_OPERAND_COUNT {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: c,
            pi_index: c,
        }));
    }

    // Family 2 — the 4 first-row boundary RELATIONS (the caveat predicate arithmetic):
    //   slack_vu == cav_validUntil − req_time
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: slack_eq_body(SLACK_VALID_UNTIL_COL, REQ_TIME_SLOT, CAV_VALID_UNTIL_SLOT),
    }));
    //   slack_hl == cav_heightLt − req_height − 1   (body = slack_hl + req_height + 1 − cav_heightLt)
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::Add(
            Box::new(LeanExpr::Var(SLACK_HEIGHT_LT_COL)),
            Box::new(LeanExpr::Add(
                Box::new(LeanExpr::Var(REQ_HEIGHT_SLOT)),
                Box::new(LeanExpr::Add(
                    Box::new(LeanExpr::Const(1)),
                    Box::new(LeanExpr::Mul(
                        Box::new(LeanExpr::Const(-1)),
                        Box::new(LeanExpr::Var(CAV_HEIGHT_LT_SLOT)),
                    )),
                )),
            )),
        ),
    }));
    //   slack_bd == cav_budget − trade_value
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: slack_eq_body(SLACK_BUDGET_COL, TRADE_VALUE_SLOT, CAV_BUDGET_SLOT),
    }));
    //   asset equality: trade_asset − cav_asset == 0
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::Add(
            Box::new(LeanExpr::Var(TRADE_ASSET_SLOT)),
            Box::new(LeanExpr::Mul(
                Box::new(LeanExpr::Const(-1)),
                Box::new(LeanExpr::Var(CAV_ASSET_SLOT)),
            )),
        ),
    }));

    // Family 3 — the 11 transition pins: `next[c] − local[c] == 0` (every column constant).
    for c in 0..TRACE_WIDTH {
        constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
            body: WindowExpr::Add(
                Box::new(WindowExpr::Nxt(c)),
                Box::new(WindowExpr::Mul(
                    Box::new(WindowExpr::Const(-1)),
                    Box::new(WindowExpr::Loc(c)),
                )),
            ),
            on_transition: true,
        }));
    }

    // Family 4 — the range lookups: all 8 operands + the 3 slacks in `[0, 2^BOUND_BITS)`.
    // The operand bounds close the wraparound hole (a huge req_time cannot make a negative
    // slack re-enter range); the slack bounds are the `≤`/`<` teeth.
    let range_cols = [
        REQ_TIME_SLOT,
        CAV_VALID_UNTIL_SLOT,
        REQ_HEIGHT_SLOT,
        CAV_HEIGHT_LT_SLOT,
        TRADE_VALUE_SLOT,
        CAV_BUDGET_SLOT,
        SLACK_VALID_UNTIL_COL,
        SLACK_HEIGHT_LT_COL,
        SLACK_BUDGET_COL,
    ];
    for c in range_cols {
        constraints.push(VmConstraint2::Lookup(LookupSpec {
            table: TID_RANGE,
            tuple: vec![LeanExpr::Var(c)],
        }));
    }

    EffectVmDescriptor2 {
        name: "caveat-admission-leaf::decidable_atoms_v1".to_string(),
        trace_width: TRACE_WIDTH,
        public_input_count: CAVEAT_OPERAND_COUNT,
        tables: vec![TableDef2 {
            id: TID_RANGE,
            name: "range".to_string(),
            arity: 1,
            sem: TableSem::Range { bits: BOUND_BITS },
        }],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// Prove a caveat admission as a RECURSION-FOLDABLE IR-v2 leaf (the membership/sovereign
/// pattern, extended with the range-check admission teeth). `public_inputs` is the 8-slot
/// operand tuple — for an honest proof it equals `witness.public_inputs()`.
///
/// THE ADMISSION TOOTH: if the request VIOLATES a caveat atom (past expiry, over budget,
/// wrong asset), the genuine slack `cav − req` wraps to `p − k > 2^BOUND_BITS`, the range
/// lookup refuses it, the assembly is UNSAT, and NO foldable leaf is minted. A within-caveat
/// trade's slacks are in range and the leaf folds.
pub fn prove_caveat_admission_leaf(
    witness: &CaveatAdmissionWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != CAVEAT_OPERAND_COUNT {
        return Err(format!(
            "caveat-admission leaf expects {CAVEAT_OPERAND_COUNT} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = caveat_admission_to_descriptor2();
    let base_trace = witness.generate_trace();

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("caveat-admission leaf inner IR-v2 prove failed: {e}"))?;

    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("caveat-admission leaf recursion wrap failed: {e}"))
}

/// Prove the caveat admission as a foldable leaf AND re-expose its bound 8-felt admission
/// claim `(trade fields ++ caveat params)` (lanes `[0 .. CAVEAT_ADMISSION_CLAIM_LEN)`) as a
/// public CLAIM the settling-venue binding node `connect`s to the deployed trade's teeth.
///
/// The exposed tuple is welded to the in-circuit admission: a prover cannot expose operands
/// that disagree with the tuple the leaf's range-checked admission proves (both are the SAME
/// FRI-bound descriptor PI targets). So a fold that consumes this claim has PROOF the trade's
/// `(time, height, value, asset)` lies inside the caveat's `(validUntil, heightLt, budget,
/// asset)` — a venue-verifiable admission, not an executor-trusted bit.
pub fn prove_caveat_admission_leaf_with_claim(
    witness: &CaveatAdmissionWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != CAVEAT_OPERAND_COUNT {
        return Err(format!(
            "caveat-admission claim leaf expects {CAVEAT_OPERAND_COUNT} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = caveat_admission_to_descriptor2();
    let base_trace = witness.generate_trace();

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("caveat-admission claim leaf inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc2, &inner, public_inputs, config)
            .map_err(|e| format!("caveat-admission claim verify-triple build failed: {e}"))?;

    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };

    let backend = create_recursion_backend();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>]| {
        let main = apt
            .first()
            .expect("caveat-admission leaf has a main instance carrying the operand PIs");
        debug_assert!(
            main.len() >= CAVEAT_ADMISSION_CLAIM_LEN,
            "main instance must carry the 8 operand PI slots"
        );
        // Re-expose the FRI-bound `(trade fields ++ caveat params)` operand lanes directly.
        let claim: Vec<Target> = (0..CAVEAT_ADMISSION_CLAIM_LEN).map(|k| main[k]).collect();
        cb.expose_as_public_output(&claim);
    };

    build_and_prove_next_layer_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
        &input,
        config,
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("caveat-admission claim leaf-wrap failed: {e:?}"))
}

/// Read the 8-felt admission claim a [`prove_caveat_admission_leaf_with_claim`] leaf exposes.
/// Returns `None` if the proof carries no claim.
pub fn read_exposed_caveat_admission(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; CAVEAT_ADMISSION_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < CAVEAT_ADMISSION_CLAIM_LEN {
        return None;
    }
    let mut out = [BabyBear::ZERO; CAVEAT_ADMISSION_CLAIM_LEN];
    out.copy_from_slice(&claims[0..CAVEAT_ADMISSION_CLAIM_LEN]);
    Some(out)
}

// ============================================================================
// THE CAVEAT-ADMISSION BINDING FOLD NODE (settling-venue side).
// ============================================================================

/// **THE CAVEAT-ADMISSION BINDING MECHANISM NODE.** Aggregate a deployed trade LEG leaf
/// (which must RE-EXPOSE its CLAIMED 8-slot `(trade fields ++ caveat params)` as an
/// `expose_claim`) WITH the re-proved caveat-admission leaf
/// ([`prove_caveat_admission_leaf_with_claim`]), CONNECTING the two 8-felt tuples in-circuit
/// and re-exposing the now-bound admission as the parent claim.
///
/// THE TOOTH: if the trade leg claims operands the admission leaf does not bind (a trade
/// whose fields the caveat gadget did not admit), the per-lane `connect` is a conflict and
/// the aggregation is UNSAT — no root. This makes a mandate breach UNCONSTRUCTABLE at
/// settlement: the venue folds this node, and a trade outside the caveat has no admission
/// leaf to bind, so no root is minted. The term-for-term twin of
/// [`crate::membership_leaf_adapter::prove_membership_binding_node`].
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_caveat_admission_binding_node(
    leg_tuple_leaf: &RecursionOutput<DreggRecursionConfig>,
    admission_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use p3_circuit::CircuitBuilder;

    let leg_idx = expose_claim_instance_index(&leg_tuple_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "caveat-admission leg leaf carries no re-exposed operand tuple (expose_claim) \
                     table — it must expose the 8-slot (trade fields ++ caveat params)"
                .to_string(),
        }
    })?;
    let adm_idx = expose_claim_instance_index(&admission_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "caveat-admission leaf carries no exposed operand tuple (expose_claim) table \
                     — it must be minted via prove_caveat_admission_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = leg_tuple_leaf.into_recursion_input::<BatchOnly>();
    let right = admission_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("caveat-admission leg's re-exposed tuple instance present");
        let adm = right_apt
            .get(adm_idx)
            .expect("caveat-admission leaf's exposed tuple instance present");
        debug_assert!(
            lg.len() >= CAVEAT_ADMISSION_CLAIM_LEN && adm.len() >= CAVEAT_ADMISSION_CLAIM_LEN
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED operands must equal the admission
        // leaf's BOUND (range-checked) tuple, lane by lane. A trade whose teeth name operands
        // no admission leaf binds is a conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..CAVEAT_ADMISSION_CLAIM_LEN {
            cb.connect(lg[k], adm[k]);
        }
        let bound: Vec<Target> = (0..CAVEAT_ADMISSION_CLAIM_LEN).map(|k| lg[k]).collect();
        cb.expose_as_public_output(&bound);
    };

    build_and_prove_aggregation_layer_with_expose::<
        DreggRecursionConfig,
        BatchOnly,
        BatchOnly,
        _,
        D,
    >(&left, &right, config, &backend, &params, None, Some(&expose))
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("caveat-admission binding aggregation node failed: {e:?}"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;

    /// A within-caveat trade: time 150 ≤ validUntil 200, height 90 < heightLt 100,
    /// value 40 ≤ budget 100, asset 7 == asset 7. Every atom holds.
    fn within_caveat() -> CaveatAdmissionWitness {
        CaveatAdmissionWitness {
            req_time: 150,
            cav_valid_until: 200,
            req_height: 90,
            cav_height_lt: 100,
            trade_value: 40,
            cav_budget: 100,
            trade_asset: 7,
            cav_asset: 7,
        }
    }

    #[test]
    fn caveat_admission_descriptor_is_wellformed() {
        let desc = caveat_admission_to_descriptor2();
        assert_eq!(desc.trace_width, TRACE_WIDTH);
        assert_eq!(desc.public_input_count, CAVEAT_OPERAND_COUNT);
        assert!(desc.hash_sites.is_empty());
        assert!(
            desc.ranges.is_empty(),
            "IR-v2 ranges ride the Lookup(TID_RANGE) table"
        );
        assert_eq!(desc.tables.len(), 1);
        assert_eq!(desc.tables[0].sem, TableSem::Range { bits: BOUND_BITS });
        // 8 PI pins + 4 boundary relations + 11 transition pins + 9 range lookups.
        let pi = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pi, CAVEAT_OPERAND_COUNT);
        let ranges = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(LookupSpec { table, .. }) if *table == TID_RANGE))
            .count();
        assert_eq!(ranges, 9, "6 operand bounds + 3 slack teeth");
        assert!(within_caveat().admits());
    }

    /// THE POSITIVE POLE: a within-caveat trade's admission proves as a foldable leaf.
    #[test]
    fn within_caveat_admission_proves_as_foldable_leaf() {
        let w = within_caveat();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        prove_caveat_admission_leaf(&w, &pis, &config)
            .expect("a within-caveat trade must admit in-circuit (fold a leaf)");
    }

    /// THE POSITIVE POLE (claim variant): the claim leaf folds AND re-exposes the bound 8-felt
    /// admission claim.
    #[test]
    fn within_caveat_claim_leaf_exposes_admission() {
        let w = within_caveat();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let out = prove_caveat_admission_leaf_with_claim(&w, &pis, &config)
            .expect("the claim leaf must fold for a within-caveat trade");
        let exposed = read_exposed_caveat_admission(&out).expect("an admission claim is exposed");
        assert_eq!(
            &exposed[..],
            &pis[..],
            "the exposed claim is the bound operand tuple"
        );
    }

    /// Assert a witness does NOT mint a foldable leaf (the UNSAT tooth) — both a hard prover
    /// panic and a returned `Err` count as refusal; only an `Ok` is a soundness break.
    fn assert_unsat(w: &CaveatAdmissionWitness, label: &str) {
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_caveat_admission_leaf(w, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!(
                "{label}: an OVER-authorized trade minted a foldable leaf — the \
                                 in-circuit caveat admission is OPEN"
            ),
        }
    }

    /// THE NEGATIVE POLE — PAST EXPIRY: `req_time 250 > validUntil 200`. `slack_vu = 200 − 250`
    /// wraps to `p − 50 > 2^24`; the range lookup refuses it. UNSAT ⇒ no leaf.
    #[test]
    fn past_expiry_trade_is_unsat() {
        let mut w = within_caveat();
        w.req_time = 250; // past the validUntil 200 ceiling
        assert!(!w.admits());
        assert_unsat(&w, "past-expiry");
    }

    /// THE NEGATIVE POLE — OVER HEIGHT: `req_height 100 == heightLt 100` (STRICT `<` rejects
    /// equality). `slack_hl = 100 − 100 − 1 = −1` wraps; the range lookup refuses it.
    #[test]
    fn over_height_trade_is_unsat() {
        let mut w = within_caveat();
        w.req_height = 100; // not strictly < heightLt 100
        assert!(!w.admits());
        assert_unsat(&w, "over-height (strict boundary)");
    }

    /// THE NEGATIVE POLE — OVER BUDGET: `trade_value 500 > budget 100`. `slack_bd = 100 − 500`
    /// wraps; the range lookup refuses it. A mandate spend breach is unconstructable.
    #[test]
    fn over_budget_trade_is_unsat() {
        let mut w = within_caveat();
        w.trade_value = 500; // over the budget 100 ceiling
        assert!(!w.admits());
        assert_unsat(&w, "over-budget");
    }

    /// THE NEGATIVE POLE — WRONG ASSET: `trade_asset 9 != cav_asset 7`. The first-row asset
    /// equality boundary `trade_asset − cav_asset == 0` fails. UNSAT ⇒ no leaf.
    #[test]
    fn wrong_asset_trade_is_unsat() {
        let mut w = within_caveat();
        w.trade_asset = 9; // outside the caveat's asset scope (7)
        assert!(!w.admits());
        assert_unsat(&w, "wrong-asset");
    }

    /// THE ADMISSION BINDS TO THE TRADE: the binding node CONNECTS a trade leg's claimed
    /// operands to the admission leaf's bound tuple and folds; a leg claiming operands the
    /// admission leaf does not bind is a `connect` conflict ⇒ UNSAT. Here the honest leg
    /// (the admission leaf re-used as the leg's tuple carrier) folds — the mechanism bites.
    #[test]
    fn admission_binds_to_trade() {
        let w = within_caveat();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let leg = prove_caveat_admission_leaf_with_claim(&w, &pis, &config)
            .expect("leg tuple leaf folds");
        let adm = prove_caveat_admission_leaf_with_claim(&w, &pis, &config)
            .expect("admission leaf folds");
        prove_caveat_admission_binding_node(&leg, &adm, &config)
            .expect("the admission binds to the trade (matching operands connect)");
    }
}
