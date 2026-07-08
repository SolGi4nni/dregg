//! The zkOracle CONTENT-COMMITMENT recursion leaf — a member of the leaf-adapter
//! family ([`crate::deco_leaf_adapter`]'s exact pattern): a Poseidon2-only commitment
//! AIR that recomputes, IN-AIR via `TID_P2` chip lookups, a chain commitment over the
//! witnessed **attestation response body**, and exposes it (plus the body length in
//! limbs) as PI-pinned claim lanes through
//! [`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`].
//!
//! ## ⚠ THE NAMED DIVERGENCE — `zkoracle_leaf_commit` is NOT `hash_bytes`
//!
//! The zkOracle attestation's cross-leg commitment is
//! `zkoracle-prove/src/attestation.rs::content_commitment(body) =
//! dregg_circuit::poseidon2::hash_bytes(body)` — a rate-4 sponge (`hash_many`) whose
//! absorb ADDS each 4-limb chunk into the rate lanes of the PREVIOUS permutation's
//! full 16-lane state (`circuit/src/poseidon2.rs:377-393`): all 16 state lanes
//! (including the 12 capacity lanes) carry between permutations. The `TID_P2` chip
//! bus exposes only **8** output lanes per permutation
//! (`descriptor_ir2.rs::CHIP_TUPLE_LEN = 1 + CHIP_RATE + 8`, `CHIP_OUT_LANES = 8`),
//! so a multi-block `hash_many` chain — any body over 16 bytes — CANNOT be expressed
//! with the available chip shapes: the capacity lanes `state[8..16]` are not on the
//! bus to seed the next permutation. Per the family's honesty rule we do NOT fake it.
//!
//! This leaf instead proves the CLOSEST EXPRESSIBLE chain commitment, named
//! **`zkoracle_leaf_commit`** — the blessed wide 8-felt Merkle–Damgård shape the chip
//! was designed for (`CHIP_WIDE_ARITY = 11`, the same step
//! `poseidon2::wire_commit_8_chip` chains on):
//!
//! ```text
//! limbs  = BabyBear::from_bytes_packed(body)          // hash_bytes' OWN 4-byte-LE packing
//! d8     = chip_absorb(4,  [0x5A4F52, n_limbs, 0, 0]) // domain-marked, LENGTH-absorbing head
//! d8     = chip_absorb(11, d8 ‖ limbs[3j..3j+3])      // per 3-limb group (final group 0-padded;
//!                                                     //   safe: n is absorbed in the head)
//! commit = d8[0]
//! ```
//!
//! Every intermediate carrier is 8 felts (no 31-bit chain waist); the head binds the
//! limb COUNT so a truncated/extended body cannot collide by padding. The exposed
//! commitment lane is 1 felt — the same width `content_commitment` itself has.
//!
//! **The named follow-up (NOT done here):** welding this leaf to the attestation's
//! `content_commitment` requires ONE of: (a) re-pointing the attestation's cross-leg
//! commitment at `zkoracle_leaf_commit` (a `zkoracle-prove` change — another lane's
//! working set), or (b) widening the chip bus to carry all 16 permutation lanes so
//! `hash_many` becomes expressible (a `circuit/` change — also another lane's working
//! set). Until that weld, the fold-level connect target is THIS leaf's
//! `zkoracle_leaf_commit`, not `content_commitment` — they are DIFFERENT functions of
//! the same body, and the tests pin that divergence explicitly
//! (`zkoracle_leaf_commit_is_not_hash_bytes`).
//!
//! ## What this leaf proves (exactly)
//!
//! For claim tuple `[n_limbs, commit]` (lanes [`ZKORACLE_LEAF_LEN_PI`],
//! [`ZKORACLE_LEAF_COMMIT_PI`]):
//!
//! * the prover knows a body of EXACTLY `n_limbs` BabyBear limbs (the length column is
//!   both PI-pinned and gate-welded to the descriptor's structural limb count);
//! * `commit = zkoracle_leaf_commit` over those witnessed limbs, recomputed IN-AIR by
//!   `1 + ⌈n/3⌉` chip lookups whose 8-lane carriers are equality-bound by the chip AIR
//!   — a claim lane disagreeing with the witnessed body is UNSAT at the leaf.
//!
//! What is NOT bound here: the body's authenticity/well-formedness/injection-freedom
//! (the attestation's three legs stay executor-verified, exactly the DECO posture),
//! the byte↔limb packing injectivity (`from_bytes_packed` reduces each 4-byte word mod
//! p — a property `hash_bytes` itself has), and the `content_commitment` weld above.
//!
//! ## Trace budget
//!
//! The body is bounded at [`ZKORACLE_MAX_BODY_LIMBS`] = 1024 limbs = 4 KiB. At the
//! bound: trace width `1 + 1024 + (342 + 1)·8 = 3769` columns over 4 rows, with 343
//! chip permutation sites per row.

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, CHIP_WIDE_ARITY, EffectVmDescriptor2, LookupSpec,
    MemBoundaryWitness, TID_P2, UMemBoundaryWitness, VmConstraint2, WIDE_K, chip_absorb_all_lanes,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

use p3_field::PrimeField32;
use p3_recursion::RecursionOutput;

use crate::ivc_turn_chain::{
    prove_descriptor_leaf_rotated_with_config, prove_descriptor_leaf_with_pi_slice_expose,
};
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

/// The leaf's trace budget: max body limbs (4 bytes each) = 4 KiB of response body.
pub const ZKORACLE_MAX_BODY_LIMBS: usize = 1024;

/// The head's domain-separation mark (`"ZOR"` ASCII), absorbed at lane 0 of the head
/// permutation so a `zkoracle_leaf_commit` chain value never collides with a bare
/// `wire_commit_8_chip` head (whose lane 0 is a data limb) by construction.
const ZKORACLE_DOMAIN_MARK: u32 = 0x5A_4F52;

/// The exposed claim width: `[n_limbs, commit]`.
pub const ZKORACLE_CLAIM_LEN: usize = 2;
/// Claim lane of the body length in limbs (so a truncated body cannot expose the same
/// claim — the length is absorbed in the head AND exposed).
pub const ZKORACLE_LEAF_LEN_PI: usize = 0;
/// Claim lane of the in-AIR-recomputed `zkoracle_leaf_commit` (the connect target).
pub const ZKORACLE_LEAF_COMMIT_PI: usize = 1;

// ---- Base trace columns (before the per-site carrier groups). ----
/// The body length in limbs, PI-pinned to claim lane 0 and gate-welded to the
/// descriptor's structural limb count.
const COL_LEN: usize = 0;
/// Base of the `n` witnessed body-limb columns.
const COL_LIMB_BASE: usize = 1;

/// `x − y` as a `LeanExpr` (no subtraction node: `x + (−1)·y`).
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// A vanishing `Base(Gate(body))` constraint.
fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// A First-row `PiBinding` welding trace column `col` to descriptor PI `pi`.
fn first_pin(col: usize, pi: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col,
        pi_index: pi,
    })
}

/// Build an UNCONDITIONAL `TID_P2` chip lookup for one chain permutation: `inputs`
/// (≤ `CHIP_RATE`, `Const(0)`-padded — the chip AIR pins lanes beyond the arity to
/// zero) and the site's 8-lane output carrier at columns `out_group .. out_group + 8`
/// (lane 0 is the digest). Every row of this leaf is a firing row.
fn chain_site(
    arity: usize,
    inputs: &[LeanExpr],
    out_group: usize,
) -> Result<VmConstraint2, String> {
    if inputs.len() > CHIP_RATE {
        return Err(format!(
            "zkoracle chain site expects <= {CHIP_RATE} input lanes, got {}",
            inputs.len()
        ));
    }
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(arity as i64));
    for i in 0..CHIP_RATE {
        tuple.push(inputs.get(i).cloned().unwrap_or(LeanExpr::Const(0)));
    }
    // The 8 genuine permutation output lanes the chip AIR EQUALITY-binds: out0 (the
    // digest) + lanes 1..7 — together the NEXT step's 8-felt carrier.
    for j in 0..CHIP_OUT_LANES {
        tuple.push(LeanExpr::Var(out_group + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    Ok(VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    }))
}

/// The witness this leaf proves over: the attestation response body as BabyBear limbs
/// (`from_bytes_packed`'s 4-byte-LE packing — the SAME packing `hash_bytes` uses),
/// bounded at [`ZKORACLE_MAX_BODY_LIMBS`]. No blinding: the exposed lane IS the public
/// commitment (the attestation already publishes `content_commit`), so the chain is
/// unkeyed — there is no opening to hide, unlike the DECO leaf's transcript salt.
#[derive(Clone, Debug)]
pub struct ZkOracleLeafWitness {
    /// The body limbs (`1 ..= ZKORACLE_MAX_BODY_LIMBS`).
    pub body_limbs: Vec<BabyBear>,
}

impl ZkOracleLeafWitness {
    /// Pack a raw response body into the witness (4-byte-LE limbs, `hash_bytes`' own
    /// packing). Refuses an empty body or one past the 4 KiB trace budget.
    pub fn from_body_bytes(body: &[u8]) -> Result<Self, String> {
        let body_limbs = BabyBear::from_bytes_packed(body);
        check_limb_count(body_limbs.len())?;
        Ok(Self { body_limbs })
    }

    /// The off-circuit twin of the in-AIR chain: `zkoracle_leaf_commit` over this
    /// witness's limbs.
    pub fn commit(&self) -> BabyBear {
        zkoracle_leaf_commit(&self.body_limbs)
            .expect("witness limb count validated at construction")
    }
}

fn check_limb_count(n: usize) -> Result<(), String> {
    if n == 0 {
        return Err("zkoracle leaf refuses an empty body".to_string());
    }
    if n > ZKORACLE_MAX_BODY_LIMBS {
        return Err(format!(
            "zkoracle leaf body is {n} limbs, over the {ZKORACLE_MAX_BODY_LIMBS}-limb \
             (4 KiB) trace budget"
        ));
    }
    Ok(())
}

/// Every 8-felt carrier of the `zkoracle_leaf_commit` chain, head first — the values
/// the base trace writes into the per-site carrier groups (`1 + ⌈n/3⌉` entries). Each
/// step is [`chip_absorb_all_lanes`] — BYTE-IDENTICAL to what the chip table derives
/// for the corresponding lookup, so the AIR's `out[i] == lane[i]` equality holds.
pub fn zkoracle_leaf_commit_carriers(
    limbs: &[BabyBear],
) -> Result<Vec<[BabyBear; CHIP_OUT_LANES]>, String> {
    let n = limbs.len();
    check_limb_count(n)?;
    let mut carriers = Vec::with_capacity(1 + n.div_ceil(WIDE_K));
    // Head: the domain mark + the limb COUNT (arity 4 → the chip seeds st[4] with the
    // arity tag, capacity lanes zero).
    let mut d = chip_absorb_all_lanes(
        4,
        &[
            BabyBear::new(ZKORACLE_DOMAIN_MARK),
            BabyBear::new(n as u32),
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    );
    carriers.push(d);
    // Body: the wide Merkle–Damgård step `d8 ← perm(d8 ‖ 3 limbs)[0..8]` (arity 11 =
    // CHIP_WIDE_ARITY; final group zero-padded — safe, n is absorbed in the head).
    let mut col = 0usize;
    while col < n {
        let mut seed = [BabyBear::ZERO; CHIP_WIDE_ARITY];
        seed[..CHIP_OUT_LANES].copy_from_slice(&d);
        for k in 0..WIDE_K {
            seed[CHIP_OUT_LANES + k] = limbs.get(col + k).copied().unwrap_or(BabyBear::ZERO);
        }
        col += WIDE_K;
        d = chip_absorb_all_lanes(CHIP_WIDE_ARITY, &seed);
        carriers.push(d);
    }
    Ok(carriers)
}

/// **`zkoracle_leaf_commit`** — the leaf's chain commitment over the body limbs (lane 0
/// of the final carrier). ⚠ NOT [`dregg_circuit::poseidon2::hash_bytes`] — see the
/// module header for the divergence and the named weld follow-up.
pub fn zkoracle_leaf_commit(limbs: &[BabyBear]) -> Result<BabyBear, String> {
    Ok(zkoracle_leaf_commit_carriers(limbs)?
        .last()
        .expect("chain has a head")[0])
}

/// [`zkoracle_leaf_commit`] over a raw byte body (via `hash_bytes`' own
/// `from_bytes_packed` limb packing).
pub fn zkoracle_leaf_commit_bytes(body: &[u8]) -> Result<BabyBear, String> {
    zkoracle_leaf_commit(&BabyBear::from_bytes_packed(body))
}

/// The HONEST `ZKORACLE_CLAIM_LEN`-slot claim tuple for a witness: `[n_limbs, commit]`.
pub fn zkoracle_leaf_public_inputs(witness: &ZkOracleLeafWitness) -> Vec<BabyBear> {
    vec![
        BabyBear::new(witness.body_limbs.len() as u32),
        witness.commit(),
    ]
}

/// Build the zkOracle content-commitment leaf descriptor for a body of EXACTLY
/// `n_limbs` limbs: the length pin + structural-length gate, the head chip site, one
/// wide chip site per 3-limb group, and the commitment pin. The descriptor is
/// per-length (the chain's site count is structural), which is why the length is both
/// gate-welded here and exposed as claim lane 0.
pub fn zkoracle_to_descriptor2(n_limbs: usize) -> Result<EffectVmDescriptor2, String> {
    check_limb_count(n_limbs)?;
    let steps = n_limbs.div_ceil(WIDE_K);
    let sites_base = COL_LIMB_BASE + n_limbs;
    let group = |j: usize| sites_base + j * CHIP_OUT_LANES;

    let mut constraints: Vec<VmConstraint2> = Vec::with_capacity(steps + 4);
    // The body length: PI-pinned AND welded to the structural limb count.
    constraints.push(first_pin(COL_LEN, ZKORACLE_LEAF_LEN_PI));
    constraints.push(gate(sub(
        LeanExpr::Var(COL_LEN),
        LeanExpr::Const(n_limbs as i64),
    )));

    // Head site (arity 4): [MARK, n, 0, 0] → carrier group 0.
    constraints.push(chain_site(
        4,
        &[
            LeanExpr::Const(ZKORACLE_DOMAIN_MARK as i64),
            LeanExpr::Var(COL_LEN),
        ],
        group(0),
    )?);

    // Wide chain sites (arity 11): previous 8-lane carrier ‖ next 3 limb columns
    // (Const(0)-padded final group) → the next carrier group.
    for j in 0..steps {
        let prev = group(j);
        let mut inputs: Vec<LeanExpr> = (0..CHIP_OUT_LANES)
            .map(|k| LeanExpr::Var(prev + k))
            .collect();
        for k in 0..WIDE_K {
            let idx = j * WIDE_K + k;
            inputs.push(if idx < n_limbs {
                LeanExpr::Var(COL_LIMB_BASE + idx)
            } else {
                LeanExpr::Const(0)
            });
        }
        constraints.push(chain_site(CHIP_WIDE_ARITY, &inputs, group(j + 1))?);
    }

    // Pin the final carrier's digest lane to the commitment claim lane.
    constraints.push(first_pin(group(steps), ZKORACLE_LEAF_COMMIT_PI));

    Ok(EffectVmDescriptor2 {
        name: "zkoracle-content-commitment-leaf::dregg-zkoracle-v1".to_string(),
        trace_width: group(steps) + CHIP_OUT_LANES,
        public_input_count: ZKORACLE_CLAIM_LEN,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    })
}

/// Build the base trace: four identical rows (the family's small power-of-two height;
/// every row fires every site, the First-row pins bind row 0). ALL columns are
/// prefilled — length, limbs, and every 8-lane carrier group (via the same
/// [`chip_absorb_all_lanes`] chain the chip table derives) — so the prover's
/// descriptor-driven lane weld (`fill_chip_lanes`, idempotent) rewrites identical
/// values.
fn zkoracle_base_trace(witness: &ZkOracleLeafWitness) -> Result<Vec<Vec<BabyBear>>, String> {
    let n = witness.body_limbs.len();
    let carriers = zkoracle_leaf_commit_carriers(&witness.body_limbs)?;
    let sites_base = COL_LIMB_BASE + n;
    let width = sites_base + carriers.len() * CHIP_OUT_LANES;
    let mut row = vec![BabyBear::ZERO; width];
    row[COL_LEN] = BabyBear::new(n as u32);
    row[COL_LIMB_BASE..sites_base].copy_from_slice(&witness.body_limbs);
    for (j, c) in carriers.iter().enumerate() {
        let base = sites_base + j * CHIP_OUT_LANES;
        row[base..base + CHIP_OUT_LANES].copy_from_slice(c);
    }
    Ok(vec![row.clone(), row.clone(), row.clone(), row])
}

/// The shared inner IR-v2 prove (descriptor + trace + batch mint under the recursion
/// config type). A claim tuple disagreeing with the witnessed body is exactly a forged
/// commitment: the `PiBinding{First}` pins + the chip-recomputed carrier chain make
/// the mismatch UNSAT — no foldable leaf is minted (the leaf-level tooth).
fn prove_zkoracle_inner(
    witness: &ZkOracleLeafWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<
    (
        EffectVmDescriptor2,
        dregg_circuit::descriptor_ir2::Ir2BatchProof<DreggRecursionConfig>,
    ),
    String,
> {
    if public_inputs.len() != ZKORACLE_CLAIM_LEN {
        return Err(format!(
            "zkoracle leaf expects {ZKORACLE_CLAIM_LEN} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = zkoracle_to_descriptor2(witness.body_limbs.len())?;
    let base_trace = zkoracle_base_trace(witness)?;
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("zkoracle leaf inner IR-v2 prove failed: {e}"))?;
    Ok((desc2, inner))
}

/// Prove the zkOracle content commitment as a RECURSION-FOLDABLE IR-v2 leaf (no claim
/// re-expose).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_zkoracle_leaf(
    witness: &ZkOracleLeafWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_zkoracle_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("zkoracle leaf recursion wrap failed: {e}"))
}

/// Prove the zkOracle content-commitment leaf AND RE-EXPOSE its
/// `ZKORACLE_CLAIM_LEN`-slot claim tuple `[n_limbs, commit]` as an in-circuit
/// `expose_claim` (lanes `[0 .. ZKORACLE_CLAIM_LEN)`), read from the leaf's own
/// FRI-bound descriptor PIs — the zkOracle analog of
/// [`crate::deco_leaf_adapter::prove_deco_leaf_with_claim`]. Lane
/// [`ZKORACLE_LEAF_COMMIT_PI`] is the in-AIR-recomputed [`zkoracle_leaf_commit`].
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_zkoracle_leaf_with_claim(
    witness: &ZkOracleLeafWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_zkoracle_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_with_pi_slice_expose(
        &desc2,
        &inner,
        public_inputs,
        config,
        0,
        ZKORACLE_CLAIM_LEN,
    )
    .map_err(|e| format!("zkoracle claim leaf expose-wrap failed: {e}"))
}

/// Read the exposed `ZKORACLE_CLAIM_LEN`-lane claim tuple off a leaf minted by
/// [`prove_zkoracle_leaf_with_claim`].
pub fn read_exposed_zkoracle_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; ZKORACLE_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < ZKORACLE_CLAIM_LEN {
        return None;
    }
    Some(core::array::from_fn(|i| claims[i]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::poseidon2::{hash_bytes, hash_many, single_perm_compress};
    use std::time::Instant;

    /// An Anthropic-messages-shaped JSON response body padded to EXACTLY `total`
    /// bytes (the `text` field carries the filler).
    fn anthropic_json_body(total: usize) -> Vec<u8> {
        let head = r#"{"id":"msg_zkoracle_demo","type":"message","role":"assistant","model":"claude-opus-4-8","content":[{"type":"text","text":""#;
        let tail =
            r#""}],"stop_reason":"end_turn","usage":{"input_tokens":128,"output_tokens":512}}"#;
        let pad = total
            .checked_sub(head.len() + tail.len())
            .expect("total below the JSON skeleton size");
        let filler: String = "the attested oracle response speaks plainly "
            .chars()
            .cycle()
            .take(pad)
            .collect();
        let body = format!("{head}{filler}{tail}");
        assert_eq!(body.len(), total);
        body.into_bytes()
    }

    /// KAT #1 — the head site: the chip's arity-4 absorb over `[MARK, n, 0, 0]` is
    /// BYTE-IDENTICAL to `hash_many` of the same 4 felts (both seed `st[0..4]` with
    /// the inputs and `st[4]` with 4 — `hash_many`'s tag is its input LENGTH, which
    /// for a 4-felt input equals the chip's arity tag). Pins the in-AIR head against
    /// its independent off-circuit twin.
    #[test]
    fn zkoracle_chip_head_absorb_matches_hash_many() {
        let ins = [
            BabyBear::new(ZKORACLE_DOMAIN_MARK),
            BabyBear::new(257),
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        assert_eq!(chip_absorb_all_lanes(4, &ins)[0], hash_many(&ins));
    }

    /// KAT #2 — the wide chain step: the chip's arity-11 absorb equals
    /// `single_perm_compress` over the same 11 felts (both seed `st[0..11]` with the
    /// inputs, capacity zero — the seed456 blend puts genuine `in4..in6` in lanes
    /// 4..6 for arity 11). All 8 carrier lanes, not just the digest.
    #[test]
    fn zkoracle_chip_wide_step_matches_single_perm_compress() {
        let ins: Vec<BabyBear> = (1u32..=11).map(|i| BabyBear::new(i * 313 + 7)).collect();
        assert_eq!(
            chip_absorb_all_lanes(CHIP_WIDE_ARITY, &ins),
            single_perm_compress(&ins)
        );
    }

    /// THE HONESTY TOOTH — the named divergence, pinned as a test so nobody quietly
    /// assumes the weld: `zkoracle_leaf_commit` is NOT `hash_bytes` (=
    /// `content_commitment`). Welding them is the module header's named follow-up.
    #[test]
    fn zkoracle_leaf_commit_is_not_hash_bytes() {
        let body = anthropic_json_body(256);
        let leaf = zkoracle_leaf_commit_bytes(&body).expect("commit over a demo body");
        let attestation = hash_bytes(&body);
        assert_ne!(
            leaf, attestation,
            "zkoracle_leaf_commit unexpectedly equals hash_bytes — if the weld landed, \
             REWRITE the module header and retire this divergence pin"
        );
    }

    /// Off-circuit binding: every single-limb flip moves the commit, and the SAME
    /// limb prefix under a different length (the truncation shape) commits
    /// differently — the head absorbs the limb count.
    #[test]
    fn zkoracle_leaf_commit_binds_every_limb_and_the_length() {
        let limbs: Vec<BabyBear> = (0u32..40).map(|i| BabyBear::new(1000 + 17 * i)).collect();
        let base = zkoracle_leaf_commit(&limbs).unwrap();
        for k in 0..limbs.len() {
            let mut m = limbs.clone();
            m[k] += BabyBear::ONE;
            assert_ne!(
                base,
                zkoracle_leaf_commit(&m).unwrap(),
                "limb {k} must be bound"
            );
        }
        // Truncation: drop the last limb — even though the final wide group would
        // zero-pad identically for a trailing-zero limb, the head's length absorb
        // separates the chains.
        let mut trunc = limbs.clone();
        trunc.pop();
        assert_ne!(base, zkoracle_leaf_commit(&trunc).unwrap());
        // The sharp case: a body whose last limb IS zero vs the body without it —
        // the wide-group padding makes the absorbs identical, so ONLY the head's
        // length binding separates them.
        let mut zero_tail = limbs.clone();
        zero_tail.push(BabyBear::ZERO);
        assert_ne!(
            zero_tail.len() % WIDE_K,
            1,
            "keep this case a mid-group zero-pad so it exercises the padding seam"
        );
        assert_ne!(
            zkoracle_leaf_commit(&zero_tail).unwrap(),
            zkoracle_leaf_commit(&limbs).unwrap(),
            "a zero-padded tail must not collide — the head length absorb is load-bearing"
        );
    }

    /// The descriptor lowers to the expected shape: `1 + ⌈n/3⌉` chip sites, 2 PIs,
    /// 2 First-row pins, the structural-length gate, and the documented width.
    #[test]
    fn zkoracle_descriptor_lowers() {
        for n in [1usize, 3, 4, 100, 256, ZKORACLE_MAX_BODY_LIMBS] {
            let desc = zkoracle_to_descriptor2(n).expect("descriptor builds");
            assert_eq!(desc.public_input_count, ZKORACLE_CLAIM_LEN);
            let sites = desc
                .constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
                .count();
            assert_eq!(sites, 1 + n.div_ceil(WIDE_K), "head + one site per 3 limbs");
            let pins = desc
                .constraints
                .iter()
                .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
                .count();
            assert_eq!(pins, 2, "the length pin + the commitment pin");
            assert_eq!(
                desc.trace_width,
                1 + n + (1 + n.div_ceil(WIDE_K)) * CHIP_OUT_LANES,
                "len col + n limb cols + one 8-lane carrier group per site"
            );
        }
        // The bounds are enforced.
        assert!(zkoracle_to_descriptor2(0).is_err());
        assert!(zkoracle_to_descriptor2(ZKORACLE_MAX_BODY_LIMBS + 1).is_err());
    }

    /// The host claim tuple matches the named composition.
    #[test]
    fn public_inputs_match_named_commitment() {
        let body = anthropic_json_body(300);
        let w = ZkOracleLeafWitness::from_body_bytes(&body).unwrap();
        let pis = zkoracle_leaf_public_inputs(&w);
        assert_eq!(pis.len(), ZKORACLE_CLAIM_LEN);
        assert_eq!(pis[ZKORACLE_LEAF_LEN_PI], BabyBear::new(75)); // 300 / 4
        assert_eq!(
            pis[ZKORACLE_LEAF_COMMIT_PI],
            zkoracle_leaf_commit_bytes(&body).unwrap()
        );
    }

    /// Prove + expose + check one body end-to-end; returns (prove wall-clock,
    /// serialized proof bytes).
    fn prove_and_check(body: &[u8]) -> (std::time::Duration, usize) {
        let w = ZkOracleLeafWitness::from_body_bytes(body).expect("witness packs");
        let pis = zkoracle_leaf_public_inputs(&w);
        let config = ir2_leaf_wrap_config();
        let t0 = Instant::now();
        let output = prove_zkoracle_leaf_with_claim(&w, &pis, &config)
            .expect("the honest zkoracle commitment must prove as a foldable claim leaf");
        let dt = t0.elapsed();
        let exposed = read_exposed_zkoracle_claim(&output).expect("the leaf exposes the claim");
        assert_eq!(
            exposed.as_slice(),
            pis.as_slice(),
            "exposed claim is the bound tuple"
        );
        assert_eq!(
            exposed[ZKORACLE_LEAF_COMMIT_PI],
            zkoracle_leaf_commit_bytes(body).unwrap(),
            "the exposed lane equals the off-circuit twin over the body"
        );
        let proof_bytes = postcard::to_allocvec(&output.0)
            .expect("leaf proof serializes")
            .len();
        (dt, proof_bytes)
    }

    /// THE POSITIVE POLE (~1 KiB): an honest Anthropic-messages-shaped body proves as
    /// a foldable recursion leaf and the exposed claim lanes equal `[n_limbs,
    /// zkoracle_leaf_commit(body)]`.
    #[test]
    #[ignore = "SLOW: real recursion leaf wrap (~seconds+); run with --ignored"]
    fn honest_zkoracle_1kib_proves_and_exposes_claim() {
        let body = anthropic_json_body(1024); // 256 limbs, 87 chip sites
        let (dt, bytes) = prove_and_check(&body);
        eprintln!("zkoracle leaf 1 KiB body: prove {dt:?}, proof {bytes} bytes");
    }

    /// THE POSITIVE POLE at the trace budget (~4 KiB = 1024 limbs, 343 chip sites).
    #[test]
    #[ignore = "SLOW: real recursion leaf wrap (~seconds+); run with --ignored"]
    fn honest_zkoracle_4kib_proves_and_exposes_claim() {
        let body = anthropic_json_body(4096); // 1024 limbs — the bound
        let (dt, bytes) = prove_and_check(&body);
        eprintln!("zkoracle leaf 4 KiB body: prove {dt:?}, proof {bytes} bytes");
    }

    /// THE LEAF-BINDING TOOTH: a forged commitment lane (body honest) is REFUSED at
    /// the leaf — the machinery's pre-flight replay / batch prover returns `Err` (the
    /// chip-recomputed carrier chain + the PI pin make it UNSAT); `catch_unwind` also
    /// tolerates a panicking assembly, matching the family's forged-pole convention.
    #[test]
    #[ignore = "SLOW: real prove path; run with --ignored"]
    fn forged_commit_lane_refused() {
        let body = anthropic_json_body(200);
        let w = ZkOracleLeafWitness::from_body_bytes(&body).unwrap();
        let mut pis = zkoracle_leaf_public_inputs(&w);
        pis[ZKORACLE_LEAF_COMMIT_PI] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_zkoracle_leaf(&w, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a FORGED commitment minted a foldable leaf — soundness OPEN"),
        }
    }

    /// THE LENGTH TOOTH: lying about the body length in the claim (commit lane
    /// honest) is REFUSED — the length pin + the structural-length gate disagree.
    /// Same refuse-shape as above (`Err` from the prove path).
    #[test]
    #[ignore = "SLOW: real prove path; run with --ignored"]
    fn lied_length_lane_refused() {
        let body = anthropic_json_body(200);
        let w = ZkOracleLeafWitness::from_body_bytes(&body).unwrap();
        let mut pis = zkoracle_leaf_public_inputs(&w);
        pis[ZKORACLE_LEAF_LEN_PI] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_zkoracle_leaf(&w, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a LIED length minted a foldable leaf — soundness OPEN"),
        }
    }

    /// THE BODY-TAMPER TOOTH: flip ONE witnessed body limb while the claim stays the
    /// original body's — the stale commitment no longer recomputes, REFUSED (`Err`).
    #[test]
    #[ignore = "SLOW: real prove path; run with --ignored"]
    fn tampered_body_limb_stale_claim_refused() {
        let body = anthropic_json_body(200);
        let honest = ZkOracleLeafWitness::from_body_bytes(&body).unwrap();
        let pis = zkoracle_leaf_public_inputs(&honest); // the HONEST body's claim
        let mut tampered = honest.clone();
        tampered.body_limbs[7] += BabyBear::ONE; // one flipped limb
        let config = ir2_leaf_wrap_config();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_zkoracle_leaf(&tampered, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => {
                panic!("a TAMPERED body proved under the stale claim — soundness OPEN")
            }
        }
    }
}
