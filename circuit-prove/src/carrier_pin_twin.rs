//! **THE CARRIER-OCTET PIN TWIN (regen-rider staging support).** The Rust twin of the Lean
//! STEP-3 descriptor transforms (`EffectVmEmitRotationV3.withAfterOctetPins` — commit
//! `556970558` — and the CarrierComposed / MembershipAuthRootEdge PI-exposure pieces): given
//! a DEPLOYED wide rotated descriptor (narrow PIs ++ 16 wide anchor PIs), INSERT a cohort of
//! claim pins at the narrow tail (ahead of the wide anchors), shifting the anchor pins up.
//!
//! ## Why this exists in `circuit-prove`
//!
//! The STEP-3 carrier-octet PI pins are COMMITTED in Lean (`factoryV3Carriers` swapped into
//! `v3Registry`; the sovereign/membership exposure named), but the EMITTED registry strings
//! (`WIDE_REGISTRY_STAGED_TSV` / `V3_STAGED_REGISTRY_TSV`) ride the BIG-BANG REGEN (owned by
//! the descriptor-emit lane). Until that regen lands, the deployed-path CARRIER FOLD TOOTHS
//! (`circuit-prove/tests/*_binding_deployed_tooth.rs`) need the PINNED descriptor shape to
//! exercise the fold arms in `prove_chain_core_rotated` end-to-end. This module builds that
//! shape FAITHFULLY from the deployed descriptor — the same additive transform the Lean emit
//! applies — so the teeth prove against the post-regen geometry today, and the regen merely
//! swaps the source of the descriptor from "twin transform" to "committed registry row".
//!
//! ## ⚑ THE SWITCH (v12 big-bang regen — sovereign + membership are NATIVE)
//!
//! The big-bang regen LANDED the sovereign + membership exposures into the committed
//! `WIDE_REGISTRY_STAGED_TSV`: `makeSovereignVmDescriptor2R24` is now
//! `CarrierComposed.makeSovereignV3DeployedWide` (teeth PIs 58..61 + the in-AIR KEY_COMMIT chip
//! gate) and `transferVmDescriptor2R24` is `CarrierComposed.transferV3MembershipWide` (claim PIs
//! 50..51, teeth columns past the carriers). Their tooths fetch the NATIVE rows directly —
//! `insert_tail_claim_pins` no longer stages them. The twin transform REMAINS for future
//! carrier staging (the bridge felt-domain mint-identity exposure is the named next rider).
//!
//! ## The transform (mirrors `withAfterOctetPins` exactly, lifted over the wide append)
//!
//! The Lean pipeline is `wideAppend (withAfterOctetPins g base)`: pins are appended to the
//! NARROW descriptor (PIs `g.piCount + k`), then the 16 wide anchors land after them. The
//! deployed emitted artifact at HEAD is `wideAppend g` (anchors directly after the narrow
//! PIs). [`insert_tail_claim_pins`] converts the latter into the former:
//!
//!   * every existing `PiBinding` with `pi_index >= insert_at` (the 16 wide anchors) shifts
//!     up by the pin count,
//!   * the claim pins are appended as `Base(PiBinding { row, col, pi_index: insert_at + k })`,
//!   * `public_input_count` bumps by the pin count.
//!
//! `PiBinding` is the ONLY PI-referencing constraint form (`Gate`/`Boundary` bodies are
//! column-space `LeanExpr`s; `Lookup`/`MemOp`/`MapOp`/`UMemOp`/`WindowGate` are column-space
//! too), so the shift is total. A descriptor carrying a `ProofBind` constraint (the custom
//! leg's recursion-argument row) is REFUSED — the custom carrier's claim slots (IR2 PI
//! 46..49) are already deployed and never ride this twin.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

/// One claim pin to insert: `trace[row][col] == PI[insert_at + k]`.
#[derive(Clone, Copy, Debug)]
pub struct TailClaimPin {
    /// The absolute trace column the pin binds (e.g. `AFTER_BASE + B_CHILD_VK_OCTET + k`).
    pub col: usize,
    /// The guarded boundary row (`Last` for AFTER-block octets, `First` for row-0 teeth).
    pub row: VmRow,
}

/// Insert `pins` as claim PIs at `insert_at` (the narrow PI tail), shifting every existing
/// `PiBinding` at `pi_index >= insert_at` (the wide anchor pins) up by `pins.len()`. Returns
/// the pinned twin descriptor; the caller splices the matching PI VALUES with
/// [`splice_pi_values`] and re-proves via `prove_vm_descriptor2_for_config`.
pub fn insert_tail_claim_pins(
    desc: &EffectVmDescriptor2,
    insert_at: usize,
    pins: &[TailClaimPin],
) -> Result<EffectVmDescriptor2, String> {
    if insert_at > desc.public_input_count {
        return Err(format!(
            "carrier pin twin: insert_at {insert_at} past descriptor PI count {}",
            desc.public_input_count
        ));
    }
    let shift = pins.len();
    let mut constraints = Vec::with_capacity(desc.constraints.len() + shift);
    for c in &desc.constraints {
        match c {
            VmConstraint2::ProofBind(_) => {
                return Err(
                    "carrier pin twin: descriptor carries a ProofBind constraint (the custom \
                     leg) — the twin transform does not support it (custom's claim slots are \
                     already deployed)"
                        .to_string(),
                );
            }
            VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
                if *pi_index >= insert_at =>
            {
                constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                    row: *row,
                    col: *col,
                    pi_index: pi_index + shift,
                }));
            }
            other => constraints.push(other.clone()),
        }
    }
    for (k, pin) in pins.iter().enumerate() {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: pin.row,
            col: pin.col,
            pi_index: insert_at + k,
        }));
    }
    Ok(EffectVmDescriptor2 {
        name: desc.name.clone(),
        trace_width: desc.trace_width,
        public_input_count: desc.public_input_count + shift,
        tables: desc.tables.clone(),
        constraints,
        hash_sites: desc.hash_sites.clone(),
        ranges: desc.ranges.clone(),
    })
}

/// Splice `values` into the PI vector at `insert_at` (the value twin of
/// [`insert_tail_claim_pins`] — the wide anchor values slide up past the inserted claims).
pub fn splice_pi_values(dpis: &[BabyBear], insert_at: usize, values: &[BabyBear]) -> Vec<BabyBear> {
    let mut out = Vec::with_capacity(dpis.len() + values.len());
    out.extend_from_slice(&dpis[..insert_at]);
    out.extend_from_slice(values);
    out.extend_from_slice(&dpis[insert_at..]);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pin(row: VmRow, col: usize, pi_index: usize) -> VmConstraint2 {
        VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
    }

    #[test]
    fn inserts_and_shifts_anchor_pins() {
        let desc = EffectVmDescriptor2 {
            name: "twin-test".into(),
            trace_width: 10,
            public_input_count: 5, // 3 narrow + 2 "anchors" at 3..5
            tables: vec![],
            constraints: vec![
                pin(VmRow::First, 0, 0),
                pin(VmRow::Last, 1, 3),
                pin(VmRow::Last, 2, 4),
            ],
            hash_sites: vec![],
            ranges: vec![],
        };
        let pins = [
            TailClaimPin {
                col: 7,
                row: VmRow::Last,
            },
            TailClaimPin {
                col: 8,
                row: VmRow::Last,
            },
        ];
        let twin = insert_tail_claim_pins(&desc, 3, &pins).expect("twin builds");
        assert_eq!(twin.public_input_count, 7);
        // anchors shifted 3→5, 4→6; claims at 3, 4.
        assert!(twin.constraints.contains(&pin(VmRow::Last, 1, 5)));
        assert!(twin.constraints.contains(&pin(VmRow::Last, 2, 6)));
        assert!(twin.constraints.contains(&pin(VmRow::Last, 7, 3)));
        assert!(twin.constraints.contains(&pin(VmRow::Last, 8, 4)));
        // the untouched narrow pin stays.
        assert!(twin.constraints.contains(&pin(VmRow::First, 0, 0)));

        let dpis: Vec<BabyBear> = (0..5).map(BabyBear::new).collect();
        let spliced = splice_pi_values(&dpis, 3, &[BabyBear::new(70), BabyBear::new(80)]);
        let want: Vec<BabyBear> = [0, 1, 2, 70, 80, 3, 4]
            .into_iter()
            .map(BabyBear::new)
            .collect();
        assert_eq!(spliced, want);
    }
}
