# Verified rotated layout: final architecture and flag-day procedure

Status: **BUILT.** ⚑ **NO LONGER BYTE-PRESERVING — flag day 2026-07-31, `rotatedNumPreLimbs`
178 -> 184.** See "The ninth-lane flag day" below. This was Goal A only; the narrow optimizer
deployment remains Goal B.

## The ninth-lane flag day (2026-07-31)

`p = 2013265921`, so `log2 p = 30.907` and **eight lanes carry 247.26 bits against a 32-byte field's
256**. No 8-lane encoding of 32 bytes is injective under any chunking — pigeonhole, before you read a
line of code. `fields[0..7]` are excluded from the byte-exact authority residue
(`cell/src/commitment.rs` — "bound by their own limbs"), so those lanes are the ONLY binding those
fields have, and the deficit reached `TurnReceipt::{pre,post}_state_hash`, the executor signature and
the receipt QC. Three successive repairs (an eight-way `fold_bytes32_to_bb` Horner fold, then a
`u32 % p` chunking, then a Poseidon2 image over an injective preimage) each moved the attacker's COST
and none reached injectivity; the last priced out at a **2^92.7 collision**, below the ~124-bit bar
this repo quotes elsewhere, which made the fields octet the weakest collision term in the rotated
commitment.

**The octet became a NONET.** `metatheory/Dregg2/Circuit/FieldLanes9.lean` is the authority:
`fieldToLanes9_injective` is an INJECTION with a total decoder (`lanes9ToField`) and a machine-checked
left inverse (`lanes9ToField_fieldToLanes9`), not a hash bound and not a birthday bound.
`nine_lanes_is_the_minimum` pins the counting argument as arithmetic: `P^8 < 2^256 <= P^9`.

Geometry: **184, and NOTHING SHIFTED.** Each `fields[slot]` keeps lane 0 on its welded v1 face limb
`4 + slot` and lanes 1..7 on the historical window `113 + 7*slot .. +6`; the NINTH lane of slot `j` is
the new column `176 + j`. The first two of those (176, 177) were the layout's only free pads; the
remaining six are the extent bump. `(184 - 4) % 3 = 0`, so `Legal.bodyAligned` survives — 186 is
bodyAligned-ILLEGAL and 187 costs four columns for nothing. The projection is
`RotatedLayout.fieldLaneCol`, with `fieldLaneCol_nodup` and `fieldLaneCol_occupied`; consumers must
read it and must NOT compute `113 + 8*slot`, because the nonet is deliberately non-contiguous.

Downstream: `B_SPAN` 239 -> 247, `2*B_SPAN` 478 -> 494, `APPENDIX_SPAN` 521 -> 537, chain carriers
59 -> 61, chip sites per block 60 -> 62, wide carriers 60 -> 62, `wideCarrierBlockSpan` 480 -> 496,
`wideAppendixSpan` 960 -> 992, `wideCommitCarrier` 59 -> 61, `fieldsCompletionOffs` 56 -> 64 columns,
`setFieldV3` completion PI count 53 -> 54.

**What refuses rather than reinterprets.** `circuit/src/effect_vm/trace_rotated.rs`'s
`const _: () = assert!(NUM_PRE_LIMBS == 178, ...)` block and
`circuit/src/exact_nullifier_aafi_rotated_trace.rs`'s width pins fail the BUILD, by design. Two
hand-mirrors that would have disagreed SILENTLY were de-mirrored in the same change:
`exact_nullifier_aafi_rotated_trace.rs` (`ROTATED_PRE_LIMBS` / `ROTATED_IROOT_OFFSET` /
`ROTATED_PAYLOAD_WIDTH` / `WIDE_CARRIERS`) and `circuit-prove/src/shielded_ring_clearing_air.rs`
(`ENDPOINT_NUM_PRE_LIMBS`, whose doc CLAIMED "the same `wireCommitR8` shape as the live wide cohort"
with nothing checking it) now PROJECT `layout_generated::NUM_PRE_LIMBS` and carry compile-time pins.

Every committed field value moves, so this is a **re-genesis**, a descriptor re-emit across the three
rotated registries, and a VK rotation.

## One source and its proof

`metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean` owns the rotated pre-iroot geometry. The current
source is `rotatedNumPreLimbs` plus the `rotated184 : RotatedLayout` data instance. In particular,
the ten faithful-8 groups—including non-contiguous `fields` and circuit-only `cells`—have concrete
coordinates only in `rotated184.groups`.

`Legal rotated184` proves, by `native_decide`, that:

- every named group has one lane-0 column and exactly seven completion columns;
- group names are unique and every `GroupName` is present;
- all occupied columns are disjoint and below `numPreLimbs`; and
- the post-head body is divisible into arity-3 fold groups.

Together with `rotated184_complete`, those obligations make the current 184 columns a complete
tiling of `0..183`: no overlap, no gap, no missing semantic group, and no partial fold chunk.

## How consumers derive

1. **Lean emit.** `EffectVmEmitRotationV3.layoutGroupCol` projects named lanes through
   `rotated184.groupCol`; all deployed `*GroupCol` definitions use that projection. The theorems in
   `RotatedLayoutBridge.lean` are now definitional equalities (`rfl`), retained as the public proof
   surface and byte-drift tripwire. The block extent and carrier counts derive from
   `rotatedNumPreLimbs`.
2. **Lean → Rust.** `EmitLayoutManifest.lean` emits `NUM_PRE_LIMBS`, the literal
   `ROTATED_GROUP_TABLE`, and generated semantic aliases such as `FIELDS_ROOT_GROUP`. The numeric
   table is emitted once; aliases index it rather than duplicating coordinates.
3. **Rust producers and AIR.** `cell/src/commitment.rs::compute_rotated_pre_limbs`, the independent
   live producer `turn/src/rotation_witness.rs::produce`, and
   `circuit/src/effect_vm/trace_rotated.rs` all consume the generated constants. There are no local
   named-group coordinate arrays or `*_group_col` formulas left. `cells` remains intentionally
   producer-zero: its generated completion columns 169..175 are filled only by the create-cell
   circuit path.

The scalar spine (`B_SPAN`, octet bases, and related deployed offsets) is still authored in Lean and
emitted by the same manifest. It is not an independent Rust layout. The Rust tiling unit test remains
as an artifact-integrity check over generated data, not as the legality source.

Current HEAD geometry: 184 pre-limbs, ten faithful-8 groups, block span 247, 134 rotated chip sites,
42 v1 PIs, 46 base rotated PIs, and 66 wide PIs.

## Geometry flag-day procedure

1. Edit `rotatedNumPreLimbs` and/or the `rotated184` data in `RotatedLayout.lean`. A group relocation
   is changed only there. Do not hand-edit generated Rust.
2. Close `rotated184_legal` and `rotated184_complete` with `native_decide`; an overlap, missing group,
   wrong group width, out-of-bounds column, or bad fold extent must fail here.
3. Build `RotatedLayoutBridge` and the narrow/wide refinement closure. The bridge should remain
   definitional; if it does not, the emit stopped deriving.
4. Run `scripts/emit-descriptors.sh`. A code-projection-only update may install without a regeneration
   acknowledgment only when descriptor bytes and fingerprint constants are identical. A real deployed
   geometry change will alter descriptor bytes and must remain blocked until a separately authorized
   federation re-key supplies `DREGG_VK_REGEN_ACK`.
5. Run the Rust layout tiling/disjointness tests and `scripts/check-descriptor-drift.sh`.

For the byte-preserving Goal-A refactor recorded here, step 4 took the generated-Rust-only branch:
one Lean-authored module changed, while descriptor bytes and fingerprint constants remained identical.

## Explicitly not done

Goal B is untouched: no narrow descriptor was deployed, no VK was regenerated, and the named
`effNarrow_rejects_wrong_facet` / narrow WIRE-wrapper residuals remain exactly that—named deployment
work, not proof holes in Goal A. Dead AIR columns such as `BUS_FACT` are also not byte-safe cleanup;
removing them belongs to a separately acknowledged descriptor change.
