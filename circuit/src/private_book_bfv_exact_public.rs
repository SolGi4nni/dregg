//! Fixed, public q0/N=8 BFV butterfly proof through DescriptorIR2 LogUp.
//!
//! This is deliberately a known-answer-test carrier, not a private transform
//! API.  The Lean-emitted descriptors below contain every schedule and tagged
//! read/write row as `exact_public_rows`; consequently all q0/N=8 butterfly
//! values are verifier-known relation constants.  A successful proof says that
//! the fixed public rows satisfy the Lean-authored radix equations and exact
//! multisets.  It does **not** hide a runtime input, bind a private BFV carrier,
//! or supply the terminal same-opening authority needed by fhEgg.
//!
//! The twelve logical rows are proved as three independent four-row batches,
//! one per radix-2 stage.  No row is padding and there is no unconstrained
//! selector: every main row performs one schedule lookup and four bus lookups.

use serde::{Deserialize, Serialize};

use crate::BabyBear;
use crate::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, TableSem,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use crate::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;
use crate::private_book_bfv_tables::{BFV_BUTTERFLY_TRACE_WIDTH, q0_n8_lean_rows};

/// Natural proof split: one power-of-two instance per q0/N=8 radix stage.
pub const BFV_Q0_N8_EXACT_PUBLIC_STAGE_COUNT: usize = 3;
/// Every stage has exactly four real butterfly rows.
pub const BFV_Q0_N8_EXACT_PUBLIC_ROWS_PER_STAGE: usize = 4;

const STAGE_JSON: [&str; BFV_Q0_N8_EXACT_PUBLIC_STAGE_COUNT] = [
    include_str!(
        "../descriptors/by-name/private-book-bfv-odd-ntt-butterfly-q0-n8-stage0-exact-public.json"
    ),
    include_str!(
        "../descriptors/by-name/private-book-bfv-odd-ntt-butterfly-q0-n8-stage1-exact-public.json"
    ),
    include_str!(
        "../descriptors/by-name/private-book-bfv-odd-ntt-butterfly-q0-n8-stage2-exact-public.json"
    ),
];

const STAGE_NAMES: [&str; BFV_Q0_N8_EXACT_PUBLIC_STAGE_COUNT] = [
    "private-book-bfv-odd-ntt-butterfly-q0-n8-stage0::exact-public-48-v1",
    "private-book-bfv-odd-ntt-butterfly-q0-n8-stage1::exact-public-48-v1",
    "private-book-bfv-odd-ntt-butterfly-q0-n8-stage2::exact-public-48-v1",
];

/// Three fixed-relation IR2 proofs.  Descriptors are intentionally absent from
/// the wire object: a verifier resolves the three checked-in Lean artifacts by
/// stage index and refuses any other relation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BfvQ0N8ExactPublicProof {
    stages: Vec<Ir2BatchProof<DreggStarkConfig>>,
}

impl BfvQ0N8ExactPublicProof {
    /// Number of stage proofs carried by this untrusted wire object.
    pub fn stage_count(&self) -> usize {
        self.stages.len()
    }
}

fn exact_public_rows_shape(
    table: &crate::descriptor_ir2::TableDef2,
) -> Result<(usize, usize), String> {
    let TableSem::ExactPublicRows { rows } = &table.sem else {
        return Err(format!(
            "table {} is not a Lean-emitted exact-public manifest",
            table.name
        ));
    };
    if rows.iter().any(|row| row.len() != table.arity) {
        return Err(format!("table {} contains a wrong-arity row", table.name));
    }
    Ok((rows.len(), table.arity))
}

/// Parse and outer-shape-check one fixed Lean-emitted relation.
pub fn bfv_q0_n8_exact_public_stage_descriptor(
    stage: usize,
) -> Result<EffectVmDescriptor2, String> {
    let json = STAGE_JSON
        .get(stage)
        .ok_or_else(|| format!("q0/N8 exact-public stage {stage} is outside 0..3"))?;
    let descriptor = parse_vm_descriptor2(json)?;
    if descriptor.name != STAGE_NAMES[stage]
        || descriptor.trace_width != BFV_BUTTERFLY_TRACE_WIDTH
        || descriptor.public_input_count != 0
        || descriptor.tables.len() != 2
    {
        return Err(format!(
            "q0/N8 exact-public stage {stage} outer shape drifted"
        ));
    }
    if exact_public_rows_shape(&descriptor.tables[0])? != (4, 17)
        || exact_public_rows_shape(&descriptor.tables[1])? != (16, 4)
    {
        return Err(format!(
            "q0/N8 exact-public stage {stage} manifest shape drifted"
        ));
    }
    Ok(descriptor)
}

/// Canonical typed relation identity of one fixed stage.  JSON formatting is
/// provenance only and never protocol identity.
pub fn bfv_q0_n8_exact_public_stage_fingerprint(stage: usize) -> Result<[u8; 32], String> {
    effect_vm_descriptor2_semantic_fingerprint(&bfv_q0_n8_exact_public_stage_descriptor(stage)?)
}

fn stage_rows(stage: usize) -> Result<Vec<Vec<BabyBear>>, String> {
    let rows = q0_n8_lean_rows();
    if rows.len() != BFV_Q0_N8_EXACT_PUBLIC_STAGE_COUNT * BFV_Q0_N8_EXACT_PUBLIC_ROWS_PER_STAGE {
        return Err(format!(
            "fixed q0/N8 witness has {} rows, expected exactly 12",
            rows.len()
        ));
    }
    let start = stage
        .checked_mul(BFV_Q0_N8_EXACT_PUBLIC_ROWS_PER_STAGE)
        .ok_or_else(|| "q0/N8 stage offset overflow".to_string())?;
    let end = start + BFV_Q0_N8_EXACT_PUBLIC_ROWS_PER_STAGE;
    let selected = rows
        .get(start..end)
        .ok_or_else(|| format!("q0/N8 stage {stage} is outside 0..3"))?;
    Ok(selected
        .iter()
        .map(|row| row.iter().copied().map(BabyBear::new).collect())
        .collect())
}

/// Prove the complete fixed q0/N=8 public KAT as three no-padding IR2 batches.
pub fn prove_bfv_q0_n8_exact_public() -> Result<BfvQ0N8ExactPublicProof, String> {
    let mut stages = Vec::with_capacity(BFV_Q0_N8_EXACT_PUBLIC_STAGE_COUNT);
    for stage in 0..BFV_Q0_N8_EXACT_PUBLIC_STAGE_COUNT {
        let descriptor = bfv_q0_n8_exact_public_stage_descriptor(stage)?;
        let rows = stage_rows(stage)?;
        stages.push(prove_vm_descriptor2(
            &descriptor,
            &rows,
            &[],
            &MemBoundaryWitness::default(),
            &[],
        )?);
    }
    let proof = BfvQ0N8ExactPublicProof { stages };
    // Producer-side self-check is diagnostic; consumers must call the public
    // verifier below and never treat construction as authority.
    verify_bfv_q0_n8_exact_public(&proof)?;
    Ok(proof)
}

/// Verify all three proofs against the fixed Lean relations.  The verifier
/// accepts no caller-supplied descriptor and no caller-supplied table contents.
pub fn verify_bfv_q0_n8_exact_public(proof: &BfvQ0N8ExactPublicProof) -> Result<(), String> {
    if proof.stages.len() != BFV_Q0_N8_EXACT_PUBLIC_STAGE_COUNT {
        return Err(format!(
            "q0/N8 exact-public bundle has {} stages, expected exactly 3",
            proof.stages.len()
        ));
    }
    for (stage, stage_proof) in proof.stages.iter().enumerate() {
        let descriptor = bfv_q0_n8_exact_public_stage_descriptor(stage)?;
        verify_vm_descriptor2(&descriptor, stage_proof, &[])
            .map_err(|error| format!("q0/N8 exact-public stage {stage}: {error}"))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_descriptors_have_distinct_typed_identity_and_exact_shapes() {
        let fingerprints = (0..BFV_Q0_N8_EXACT_PUBLIC_STAGE_COUNT)
            .map(|stage| bfv_q0_n8_exact_public_stage_fingerprint(stage).unwrap())
            .collect::<Vec<_>>();
        assert_ne!(fingerprints[0], fingerprints[1]);
        assert_ne!(fingerprints[1], fingerprints[2]);
        assert_ne!(fingerprints[0], fingerprints[2]);
    }

    #[test]
    fn three_stage_bundle_proves_and_verifies_without_padding() {
        let proof = prove_bfv_q0_n8_exact_public().expect("fixed public KAT proves");
        assert_eq!(proof.stage_count(), 3);
        verify_bfv_q0_n8_exact_public(&proof).expect("consumer verifies all fixed stages");
    }

    #[test]
    fn duplicate_omission_and_omitted_rows_refuse() {
        let descriptor = bfv_q0_n8_exact_public_stage_descriptor(0).unwrap();
        let honest = stage_rows(0).unwrap();

        let mut duplicate_omission = honest.clone();
        duplicate_omission[1] = duplicate_omission[0].clone();
        assert!(
            prove_vm_descriptor2(
                &descriptor,
                &duplicate_omission,
                &[],
                &MemBoundaryWitness::default(),
                &[],
            )
            .is_err(),
            "same-height duplicate+omission must fail the exact manifest"
        );

        let mut omitted = honest;
        omitted.remove(1);
        assert!(
            prove_vm_descriptor2(
                &descriptor,
                &omitted,
                &[],
                &MemBoundaryWitness::default(),
                &[],
            )
            .is_err(),
            "an omitted logical row must refuse, never become padding"
        );
    }

    #[test]
    fn manifest_and_stage_substitution_refuse_old_proofs() {
        let proof = prove_bfv_q0_n8_exact_public().expect("fixed public KAT proves");

        let mut changed = bfv_q0_n8_exact_public_stage_descriptor(0).unwrap();
        let TableSem::ExactPublicRows { rows } = &mut changed.tables[0].sem else {
            unreachable!()
        };
        rows[0][0] += 1;
        assert!(
            verify_vm_descriptor2(&changed, &proof.stages[0], &[]).is_err(),
            "one-cell manifest substitution must move the verified relation"
        );

        let mut swapped = proof.clone();
        swapped.stages.swap(0, 1);
        assert!(
            verify_bfv_q0_n8_exact_public(&swapped).is_err(),
            "a proof for one exact stage cannot authorize another stage"
        );
    }
}
