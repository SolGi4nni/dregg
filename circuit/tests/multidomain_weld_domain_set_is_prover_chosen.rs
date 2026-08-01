//! # The MULTI-DOMAIN umem weld's domain set is PROVER-CHOSEN, and its admission grounds it against
//! nothing. This file is the executable record of that, not a claim that it is fine.
//!
//! **RE-MINTED 2026-07-31** from `sdk/tests/umem_cohort_multidomain_staged_gauntlet.rs::
//! multidomain_domain_set_mismatch_fails_closed`, which was deleted with the staged umem-cohort
//! registries (`umem-cohort-multidomain-v1-staged-registry.tsv`). That test asserted a REAL property
//! of the cohort registry: the committed descriptor baked in a FIXED domain set `{heap(1),
//! nullifiers(3)}`, so a `{heap, caps}` leg handed to it FAILED CLOSED. One VK, one domain set.
//!
//! ⚑ **That property does not survive the move to the weld, and the honest thing is to say so rather
//! than delete the tooth.** `weld_umem_multidomain_into_wide_descriptor(wide, domains)` takes the
//! domain list from its CALLER and emits one guarded `umemOp` per entry, so there is no fixed set to
//! mismatch against — the descriptor is a function of what the prover asked for. And the admission
//! side does not close it either: `circuit-prove/src/ivc_turn_chain.rs::admit_welded_leg` grounds
//! only the SINGLE-domain wide weld (`-umem-wide-welded-staged`) against the DERIVED welded set
//! (`welded_wide_members` — the bare wide member under the Lean-emitted contract row); the
//! multi-domain suffix falls to the `leg.descriptor.clone()` arm and is verified against the AIR the
//! prover carried, authorized by a name suffix.
//!
//! So the two tests below pin what IS true today, at the descriptor level (fast — no proving):
//!
//!   1. `multidomain_weld_emits_whatever_domain_set_it_is_handed` — the same wide member welded at
//!      `{heap, nullifiers}` and at `{heap, caps}` yields two DIFFERENT descriptors that carry the
//!      SAME authorizing name suffix. The suffix does not distinguish them.
//!   2. `no_committed_registry_grounds_the_multidomain_weld` — the deployed wide registry carries no
//!      member with that suffix (and the derived welded set cannot: it appends the SINGLE-domain
//!      one), so a verifier has nothing to resolve against.
//!
//! **THE FALSIFIER / how this file dies:** when the multi-domain welded registry lands
//! (`EffectVmEmitUMemWeldWide`'s multi-domain twin), test 2 goes RED — a member WILL carry the
//! suffix — and that is the signal to replace this file with the mismatch refusal the cohort test
//! used to assert, now against the committed registry. Until then, deleting this file deletes the
//! only in-tree record that the domain set is unbound.

use dregg_circuit::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2};
use dregg_circuit::effect_vm_descriptors::{
    WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX,
    weld_umem_multidomain_into_wide_descriptor,
};

/// The domain codes (`dregg_turn::umem::UDomain`): heap 1, caps 2, nullifiers 3.
const HEAP: u32 = 1;
const CAPS: u32 = 2;
const NULLIFIERS: u32 = 3;

/// The wide member the NOTE/BRIDGE economic verbs weld onto.
fn wide_note_spend() -> dregg_circuit::descriptor_ir2::EffectVmDescriptor2 {
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some("noteSpendVmDescriptor2R24") {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("noteSpendVmDescriptor2R24 is a member of WIDE_REGISTRY_STAGED_TSV");
    parse_vm_descriptor2(json).expect("the committed wide noteSpend member parses")
}

fn declared_domains(d: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2) -> Vec<u32> {
    d.constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::UMemOp(spec) => Some(spec.domain),
            _ => None,
        })
        .collect()
}

/// The weld emits the domain set it is HANDED — two different sets over one wide member produce two
/// different AIRs behind one authorizing name.
#[test]
fn multidomain_weld_emits_whatever_domain_set_it_is_handed() {
    let wide = wide_note_spend();

    let honest = weld_umem_multidomain_into_wide_descriptor(&wide, &[HEAP, NULLIFIERS]);
    let foreign = weld_umem_multidomain_into_wide_descriptor(&wide, &[HEAP, CAPS]);

    assert_eq!(
        declared_domains(&honest),
        vec![HEAP, NULLIFIERS],
        "the weld declares exactly the domains it was handed"
    );
    assert_eq!(
        declared_domains(&foreign),
        vec![HEAP, CAPS],
        "…including a set no economic verb touches — nothing refuses it at weld time"
    );
    assert_ne!(
        honest.constraints, foreign.constraints,
        "the two welds are DIFFERENT AIRs (non-vacuity: the domain really is in the constraints)"
    );

    // …and they are authorized by the SAME token. This is the finding.
    assert!(
        honest.name.ends_with(WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX)
            && foreign.name.ends_with(WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX),
        "both welds carry the suffix `admit_welded_leg` accepts; the name does not distinguish the \
         domain set, so a verifier reading only the name cannot tell them apart"
    );
    assert_eq!(
        honest.name, foreign.name,
        "the names are BYTE-IDENTICAL — the domain set is not in the name at all"
    );
}

/// The deployed wide registry — the one every light-client verify resolves against — carries no
/// member with the multi-domain weld suffix, so a carried multi-domain welded descriptor has nothing
/// to be resolved against. (The SINGLE-domain suffix `-umem-wide-welded-staged` does have its
/// derived welded set, which is why `admit_welded_leg` grounds that one and only that one.)
/// ⚑ THE FALSIFIER: when the multi-domain welded set lands, this goes RED and the mismatch refusal
/// replaces it.
#[test]
fn no_committed_registry_grounds_the_multidomain_weld() {
    let grounded: Vec<&str> = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .filter(|l| !l.trim().is_empty())
        .filter_map(|l| {
            let mut it = l.splitn(3, '\t');
            let key = it.next()?;
            let name = it.next()?;
            name.ends_with(WIDE_UMEM_MULTIDOMAIN_WELD_SUFFIX)
                .then_some(key)
        })
        .collect();
    assert!(
        grounded.is_empty(),
        "the deployed wide registry now carries multi-domain welded members {grounded:?} — the \
         ungrounded-admission gap this file records is CLOSED. Replace this file with the domain-set \
         MISMATCH refusal (a `{{heap, caps}}` leg must not verify against a `{{heap, nullifiers}}` \
         committed member), the tooth `umem_cohort_multidomain_staged_gauntlet` used to carry."
    );
}
