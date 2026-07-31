//! **The fields nonet is INJECTIVE on values and UNCONSTRAINED on columns, and those are
//! different sentences.**
//!
//! ═══ WHAT `fieldToLanes9_injective` DOES AND DOES NOT SAY ════════════════════════════
//! `metatheory/Dregg2/Circuit/FieldLanes9.lean` proves `Function.Injective fieldToLanes9`:
//! two distinct 32-byte VALUES never share a lane vector. That quantifies over the
//! encoder's DOMAIN. **An adversarial prover never applies the encoder.** It writes nine
//! committed columns directly, and the deployed AIR has to independently force those
//! columns into the encoder's IMAGE. Witness-versus-constraint: injectivity is a fact
//! about honest inputs; admissibility is a fact about the constraint system.
//!
//! ═══ THE MEASUREMENT ═════════════════════════════════════════════════════════════════
//! Audited 2026-07-31 over all 186 members of the three emitted registries: every
//! member's `"ranges"` is `[]`, and the only `range`-semantics lookups anywhere in the
//! deployed set target the v1-state balance limbs (columns 76/77), the fee limb (89) and
//! the automatafl 15-bit teeth (188..201). **Not one range lookup lands on a rotated
//! block column, and none on a fields lane.** So `< 2^28` on the free lanes is a PRODUCER
//! invariant — which establishes nothing at all for the party relying on the proof.
//! `no_deployed_member_range_checks_any_rotated_fields_lane` below is that measurement,
//! read off the emitted TSVs rather than asserted from a constant.
//!
//! ═══ ⚑ AND WHY THE NAMED FIX IS NOT THE FIX ══════════════════════════════════════════
//! The residual note in `persist/src/lib.rs` priced the repair as *"7 × `< 2^28` lookups
//! per field"*. Those seven are NECESSARY and they are **NOT SUFFICIENT**, and the
//! counterexample is one lane wide — `the_off_image_exhibit_passes_all_seven_free_lane_range_checks`.
//!
//! The Lean now says exactly what IS sufficient. `Dregg2.Circuit.FieldLanes9.Canonical9`
//! has THREE legs and `canonical9_iff_in_image` proves the three are EXACTLY the image:
//!
//!   1. `FreeLanesRanged` — lanes 2..8 below `2^28`. Seven range lookups.
//!   2. `PinnedLanesField` — lanes 0/1 are BabyBear elements. Free; a column is one.
//!   3. `NoWrap` — `decLo`/`decHi`, the pinned lanes with the carry digit's discarded
//!      `mod p` quotient restored, stay below `2^32`. **This is not a range check on any
//!      lane.** It is a joint condition on lane 0, lane 1 and lane 8's top nibble, and it
//!      is the leg the exhibit below breaks while satisfying the other two.
//!
//! This file is the Rust twin of that section: the same predicate, the same exhibit, run
//! against the DEPLOYED `field_limbs9` / `field_from_lanes9` rather than the Lean model.

use dregg_circuit::descriptor_ir2::{
    CUSTOM_RANGE_WIDTHS, EffectVmDescriptor2, RANGE_W_TID_WIRE_BASE, TableSem, VmConstraint2,
};
use dregg_circuit::effect_vm::layout_generated::{B_SPAN, B_STATE_COMMIT, ROTATED_FIELD_LANE_COL};
use dregg_circuit::effect_vm::{field_from_lanes9, field_limbs9};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

/// The free lanes' radix. A free lane is `< 2^28 < p` and NEVER reduces — for an honest
/// witness. Nothing in the deployed AIR says so.
const CH: u64 = 1 << 28;
const TWO32: u64 = 1 << 32;
const P: u64 = BABYBEAR_P as u64;

// ════════════════════════════════════════════════════════════════════════════════════
// The Rust twin of `Dregg2.Circuit.FieldLanes9.Canonical9`
// ════════════════════════════════════════════════════════════════════════════════════

/// `decWord`'s 26 little-endian base-256 digits — the exact accumulation
/// [`field_from_lanes9`] performs, restated here so the predicate is readable beside the
/// decoder instead of hidden inside it.
fn dec_word_bytes(lanes: &[BabyBear; 9]) -> [u8; 26] {
    let mut w = [0u8; 26];
    for i in 0..7usize {
        let bits = 28 * i;
        let mut v = (lanes[2 + i].as_u32() as u64) << (bits % 8);
        let mut j = bits / 8;
        while v != 0 && j < w.len() {
            let s = w[j] as u64 + (v & 0xFF);
            w[j] = (s & 0xFF) as u8;
            v = (v >> 8) + (s >> 8);
            j += 1;
        }
    }
    w
}

/// Lean `decCarry` — base-256 digit 24 of `decWord`, the disambiguation digit read back.
fn dec_carry(lanes: &[BabyBear; 9]) -> u64 {
    dec_word_bytes(lanes)[24] as u64
}

/// Lean `decLo` — lane 0 with its `mod p` quotient restored, as an INTEGER (no `u32` wrap).
fn dec_lo(lanes: &[BabyBear; 9]) -> u64 {
    lanes[0].as_u32() as u64 + (dec_carry(lanes) % 4) * P
}

/// Lean `decHi`.
fn dec_hi(lanes: &[BabyBear; 9]) -> u64 {
    lanes[1].as_u32() as u64 + (dec_carry(lanes) / 4) * P
}

/// Leg 1 — Lean `FreeLanesRanged`. **This is what seven `< 2^28` range lookups buy.**
fn free_lanes_ranged(lanes: &[BabyBear; 9]) -> bool {
    lanes[2..].iter().all(|l| (l.as_u32() as u64) < CH)
}

/// Leg 2 — Lean `PinnedLanesField`. A committed column IS a BabyBear element, so this is
/// free in-AIR; it is stated so the three legs read the same here as in the Lean.
fn pinned_lanes_field(lanes: &[BabyBear; 9]) -> bool {
    (lanes[0].as_u32() as u64) < P && (lanes[1].as_u32() as u64) < P
}

/// Leg 3 — Lean `NoWrap`. **Not a range check on any lane.**
fn no_wrap(lanes: &[BabyBear; 9]) -> bool {
    dec_lo(lanes) < TWO32 && dec_hi(lanes) < TWO32
}

/// Lean `Canonical9` — proved (`canonical9_iff_in_image`) to be EXACTLY the encoder's image.
fn canonical9(lanes: &[BabyBear; 9]) -> bool {
    free_lanes_ranged(lanes) && pinned_lanes_field(lanes) && no_wrap(lanes)
}

fn lanes_of(v: [u32; 9]) -> [BabyBear; 9] {
    let mut out = [BabyBear::ZERO; 9];
    for (o, x) in out.iter_mut().zip(v.iter()) {
        *o = BabyBear::new(*x);
    }
    out
}

/// `field_from_u64` — the kernel's numeric field encoding, big-endian in bytes `24..32`.
fn from_u64(v: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[24..32].copy_from_slice(&v.to_be_bytes());
    b
}

// ════════════════════════════════════════════════════════════════════════════════════
// THE EXHIBIT
// ════════════════════════════════════════════════════════════════════════════════════

/// The honest value the exhibit collides with: `0x68000003`, below `p`, so its nonet is
/// `[v, 0, 0, 0, 0, 0, 0, 0, 0]` — lane 0 carries the raw value, every free lane empty.
const HONEST_VALUE: u64 = 1_744_830_467;

/// The off-image vector: `3 · 2^24` in lane 8 and nothing else. Its carry digit is `3`, so
/// the decoder restores `decLo = 0 + 3p = 6039797763`, which EXCEEDS `2^32`, wraps in the
/// `u32` view to exactly `HONEST_VALUE`, and the vector decodes byte-for-byte to the honest
/// value's 32 bytes. Lean `Dregg2.Circuit.FieldLanes9.forgedLanes`.
const FORGED: [u32; 9] = [0, 0, 0, 0, 0, 0, 0, 0, 3 << 24];

/// **COMPLETENESS POLE** (Lean `canonical_fieldToLanes9`). Every honest 32-byte value's
/// nonet satisfies all three legs, so an AIR that forces `Canonical9` refuses no honest
/// witness. Swept over structured and pseudorandom values, including both sides of the
/// `[p, 2^32)` window where lane 0 reduces and the carry digit is nonzero.
#[test]
fn every_honest_encoding_is_canonical() {
    let mut cases: Vec<[u8; 32]> = vec![
        [0u8; 32],
        [0xffu8; 32],
        from_u64(0),
        from_u64(1),
        from_u64(P - 1),
        from_u64(P),
        from_u64(2 * P - 1),
        from_u64(2 * P),
        from_u64(u32::MAX as u64),
        from_u64(u64::MAX),
    ];
    // Ascending bytes, and a deterministic LCG sweep — an encoder that scrambled would still
    // be caught by the round-trip assertion below, so this is not a "the vectors differ" test.
    let mut asc = [0u8; 32];
    for (i, b) in asc.iter_mut().enumerate() {
        *b = i as u8;
    }
    cases.push(asc);
    let mut seed: u64 = 0x2026_0731_dead_beef;
    for _ in 0..4096 {
        let mut b = [0u8; 32];
        for byte in b.iter_mut() {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            *byte = (seed >> 33) as u8;
        }
        cases.push(b);
    }

    let mut carries_seen = std::collections::BTreeSet::new();
    for b in &cases {
        let lanes = field_limbs9(b);
        assert!(
            canonical9(&lanes),
            "an HONEST encoding failed the AIR obligation — the gate would refuse a legal \
             witness.\n  value  : {b:02x?}\n  lanes  : {:?}\n  ranged : {}\n  field  : {}\n  \
             nowrap : {} (decLo={} decHi={})\n\nThis is the completeness pole of Lean's \
             `canonical_fieldToLanes9`. If it goes red the encoder and the predicate have \
             drifted apart; fix the predicate against the Lean, never by widening a leg.",
            lanes.map(|l| l.as_u32()),
            free_lanes_ranged(&lanes),
            pinned_lanes_field(&lanes),
            no_wrap(&lanes),
            dec_lo(&lanes),
            dec_hi(&lanes),
        );
        // ANTI-VACUITY: the VALUE comes back, so a predicate that accepted everything about a
        // scrambling encoder would still fail here.
        assert_eq!(field_from_lanes9(&lanes), *b, "the nonet must round-trip");
        carries_seen.insert(dec_carry(&lanes));
    }

    // The sweep must actually EXERCISE the carry digit, or the `NoWrap` leg is untested: a
    // corpus where every carry is 0 makes `decLo = lane 0 < p` trivially.
    assert!(
        carries_seen.len() >= 4 && carries_seen.iter().any(|c| *c >= 4),
        "the honest corpus never exercised the carry digit (seen: {carries_seen:?}) — the \
         `NoWrap` leg would be vacuous on it"
    );
}

/// **⚑ THE REFUTATION OF THE NAMED FIX.** `FORGED` satisfies legs 1 and 2 — every free lane
/// is below `2^28`, so all seven proposed range lookups accept it, and every lane is a
/// BabyBear element. It is NOT the honest vector. It decodes to the honest value anyway.
/// It fails ONLY `NoWrap`. So an AIR carrying just the seven lookups still admits it, and
/// "7 × `< 2^28` lookups per field" does not close this residual.
///
/// Lean twin: `free_lane_ranges_alone_do_not_force_the_image`.
#[test]
fn the_off_image_exhibit_passes_all_seven_free_lane_range_checks() {
    let forged = lanes_of(FORGED);
    let honest = field_limbs9(&from_u64(HONEST_VALUE));

    assert_eq!(
        honest.map(|l| l.as_u32()),
        [HONEST_VALUE as u32, 0, 0, 0, 0, 0, 0, 0, 0],
        "the honest nonet of a below-p numeric value is lane 0 alone"
    );

    // Leg 1 — ALL SEVEN proposed range lookups accept the forgery.
    for (i, lane) in forged[2..].iter().enumerate() {
        assert!(
            (lane.as_u32() as u64) < CH,
            "free lane {} of the forgery is {} ≥ 2^28 — the exhibit must pass every one of \
             the seven `< 2^28` lookups or it proves nothing about their sufficiency",
            i + 2,
            lane.as_u32()
        );
    }
    assert!(free_lanes_ranged(&forged) && pinned_lanes_field(&forged));

    // …and it is a DIFFERENT vector that decodes to the SAME 32 bytes.
    assert_ne!(
        forged.map(|l| l.as_u32()),
        honest.map(|l| l.as_u32()),
        "the exhibit must be a distinct lane vector"
    );
    assert_eq!(
        field_from_lanes9(&forged),
        from_u64(HONEST_VALUE),
        "the forged vector must decode to the honest value's bytes"
    );
    assert_eq!(
        field_from_lanes9(&forged),
        field_from_lanes9(&honest),
        "…which is exactly the honest vector's decode"
    );

    // The leg it breaks is `NoWrap`, and ONLY that one.
    assert_eq!(
        dec_carry(&forged),
        3,
        "the carry digit is lane 8's top nibble"
    );
    assert_eq!(
        dec_lo(&forged),
        3 * P,
        "decLo = 0 + 3p — above 2^32, which is the wrap"
    );
    assert!(dec_lo(&forged) >= TWO32, "decLo must exceed the u32 window");
    assert!(
        !no_wrap(&forged),
        "the exhibit must fail exactly the NoWrap leg"
    );
    assert!(
        !canonical9(&forged),
        "the full three-leg obligation MUST reject the exhibit — if this goes green the \
         predicate has been weakened and the gate it specifies would admit the forgery"
    );
}

/// **⚑ THE BITE.** The disagreement is not "two vectors decode alike" — it is that two
/// readers of the SAME committed columns, inside ONE accepted witness, answer differently.
///
/// Lane 0 is welded (`colEq (base + 4 + slot) (stateBase + FIELD_BASE + slot)`) to the v1
/// face column the kernel semantics reads: `gFieldWriteP1` against `param1`, `field_to_u64`,
/// and every escrow / discharge / vault weld. In the forged witness that column reads **0**.
/// The committed nonet decodes to **1744830467**. One proof, two answers to "what is
/// `fields[slot]`".
///
/// Lean twin: `the_welded_face_and_the_decode_disagree`.
#[test]
fn the_welded_face_and_the_decode_disagree_on_the_same_committed_columns() {
    let forged = lanes_of(FORGED);
    let honest = field_limbs9(&from_u64(HONEST_VALUE));

    let welded_face_reads = forged[0].as_u32() as u64;
    let decode_reads = u32::from_be_bytes(field_from_lanes9(&forged)[28..32].try_into().unwrap());

    assert_eq!(
        welded_face_reads, 0,
        "the forgery's welded v1 face column is zero"
    );
    assert_eq!(
        decode_reads, HONEST_VALUE as u32,
        "…while the nonet decodes to the value"
    );
    assert_ne!(
        welded_face_reads, decode_reads as u64,
        "\nTHE TWO IN-AIR READERS AGREE, SO THE EXHIBIT IS NO LONGER AN EXHIBIT.\n\
         If this went green because the codec changed, rebuild the exhibit against the new \
         codec — do not delete it. The property under test is that an off-image lane vector \
         can make the welded face and the decode disagree, and it is closed by forcing \
         `Canonical9` in the AIR, not by a codec that happens to make this pair agree.\n"
    );
    assert_eq!(
        honest[0].as_u32() as u64,
        decode_reads as u64,
        "on the HONEST vector the two readers agree — which is what makes the forgery's \
         disagreement a defect and not a property of the encoding"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════
// THE CENSUS — read off the emitted registries, not asserted from a constant
// ════════════════════════════════════════════════════════════════════════════════════

const REGISTRIES: [&str; 3] = [
    "descriptors/rotation-v3-staged-registry.tsv",
    "descriptors/rotation-wide-registry-staged.tsv",
    "descriptors/rotation-wide-umem-welded-registry-staged.tsv",
];

fn members() -> Vec<(String, EffectVmDescriptor2)> {
    let mut out = Vec::new();
    for path in REGISTRIES {
        let src = std::fs::read_to_string(path).unwrap_or_else(|e| {
            panic!(
                "cannot read {path}: {e}. This census reads the DEPLOYED descriptor bytes; if a \
                 registry moved, re-point it rather than dropping it — an unread census is the \
                 drift it exists to catch."
            )
        });
        for line in src.lines() {
            let mut cols = line.split('\t');
            let key = cols.next().unwrap_or_default().to_string();
            let _name = cols.next();
            let Some(json) = cols.next() else { continue };
            let d = parse_vm_descriptor2_or_panic(path, &key, json);
            out.push((format!("{path}::{key}"), d));
        }
    }
    assert!(!out.is_empty(), "the registry reader found no members");
    out
}

fn parse_vm_descriptor2_or_panic(path: &str, key: &str, json: &str) -> EffectVmDescriptor2 {
    dregg_circuit::descriptor_ir2::parse_vm_descriptor2(json)
        .unwrap_or_else(|e| panic!("{path}::{key}: descriptor bytes do not decode: {e}"))
}

/// Every column a `range`-semantics lookup targets in this member, with its declared width.
///
/// ⚑ **THE READER MUST CARRY THE WIDTH-TAGGED FALLBACK OR IT IS BLIND.** A range lookup does not
/// need a `tables` entry: `descriptor_ir2::MainLayout::build` recovers `bits` from the wire id
/// itself (`tid − RANGE_W_TID_WIRE_BASE`, the inverse of Lean's `rangeTidW`) whenever the width is
/// in [`CUSTOM_RANGE_WIDTHS`], and the deployed availability weld has always relied on exactly that.
/// The fields-canonicity emit rides the same path at widths 24 and 28. A `tables`-only reader
/// reports ZERO canonicity lookups and every census over it is vacuously "clean" — measured on
/// 2026-07-31, when the emit had landed and this file still read green.
fn range_checked_columns(d: &EffectVmDescriptor2) -> Vec<(usize, usize)> {
    d.constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Lookup(l) => {
                let bits = d
                    .tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
                    .or_else(|| {
                        l.table
                            .checked_sub(RANGE_W_TID_WIRE_BASE)
                            .filter(|bits| CUSTOM_RANGE_WIDTHS.contains(bits))
                    })?;
                match l.tuple.as_slice() {
                    [dregg_circuit::lean_descriptor_air::LeanExpr::Var(w)] => Some((*w, bits)),
                    _ => None,
                }
            }
            _ => None,
        })
        .collect()
}

/// The rotated BEFORE block's base, derived from the member's OWN constraint bytes: the
/// rotated pin quartet publishes `before_base + B_STATE_COMMIT` on the FIRST row and
/// `before_base + B_SPAN + B_STATE_COMMIT` on the LAST, so the base is the unique first-row
/// pin whose `+ B_SPAN` twin is also pinned. `None` for a member with no rotated block.
fn rotated_before_base(d: &EffectVmDescriptor2) -> Option<usize> {
    let last_cols: Vec<usize> = d
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::Last,
                col,
                ..
            }) => Some(*col),
            _ => None,
        })
        .collect();
    let mut found: Vec<usize> = d
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col,
                ..
            }) if *col >= B_STATE_COMMIT && last_cols.contains(&(*col + B_SPAN)) => {
                Some(*col - B_STATE_COMMIT)
            }
            _ => None,
        })
        .collect();
    found.sort_unstable();
    found.dedup();
    match found.as_slice() {
        [] => None,
        [b] => Some(*b),
        many => panic!("ambiguous rotated block base candidates {many:?}"),
    }
}

/// Every fields-lane column of both rotated blocks, for a member whose base is known.
fn rotated_fields_lane_columns(before_base: usize) -> Vec<usize> {
    let mut cols = Vec::new();
    for block in [before_base, before_base + B_SPAN] {
        for slot in ROTATED_FIELD_LANE_COL.iter() {
            for lane in slot.iter() {
                cols.push(block + lane);
            }
        }
    }
    cols
}

/// **THE MEASUREMENT, INVERTED — the emit LANDED (2026-07-31).**
///
/// This test used to assert the wound: *not one range lookup in any deployed member lands on a
/// fields-lane column of either rotated block.* Its own doc comment said to INVERT it rather than
/// delete it when `Dregg2.Circuit.Emit.FieldsCanonicity9Emit` landed, so that a landed fix would not
/// read as a red test and invite someone to delete the gate instead of the stale expectation. This
/// is that inversion, and the assertions are now the mirror of what they were:
///
///   * EVERY fields lane 2..8 of BOTH rotated blocks is range-checked at 28 bits — `2 × 8 × 7 = 112`
///     lane lookups per member. Lanes 0 and 1 are deliberately NOT range-checked: they are the
///     pinned kernel u64 pair, and `PinnedLanesField` is free (a committed column IS a BabyBear
///     element). A lookup on them would be noise, not canonicity.
///   * The `NoWrap` leg's own lookups are present too — `16 × (1 × 24-bit + 4 × 28-bit) = 80` more —
///     because seven `< 2^28` lookups per field are NECESSARY AND NOT SUFFICIENT
///     (`the_off_image_exhibit_passes_all_seven_free_lane_range_checks`, still green above). A
///     member carrying only the 112 would still admit the forgery.
///   * So the per-member floor is `112 + 80 = 192` canonicity lookups, and the old
///     `max_range_lookups < 16` ceiling becomes a FLOOR.
#[test]
fn every_deployed_member_range_checks_every_rotated_fields_lane() {
    let mut rotated_members = 0usize;
    let mut all_targets: std::collections::BTreeSet<(usize, usize)> = Default::default();
    let mut min_range_lookups = usize::MAX;
    let mut leanest = String::new();
    let all = members();
    let total_members = all.len();

    for (label, d) in all {
        for t in range_checked_columns(&d) {
            all_targets.insert(t);
        }
        let n = range_checked_columns(&d).len();
        if n < min_range_lookups {
            min_range_lookups = n;
            leanest = label.clone();
        }
        let Some(base) = rotated_before_base(&d) else {
            continue;
        };
        rotated_members += 1;

        // The FREE lanes (2..8) of both blocks must ALL be covered, at exactly 28 bits.
        let ranged: std::collections::BTreeMap<usize, usize> =
            range_checked_columns(&d).into_iter().collect();
        let mut missing: Vec<usize> = Vec::new();
        let mut wrong_width: Vec<(usize, usize)> = Vec::new();
        for block in [base, base + B_SPAN] {
            for slot in ROTATED_FIELD_LANE_COL.iter() {
                for lane in slot.iter().skip(2) {
                    match ranged.get(&(block + lane)) {
                        None => missing.push(block + lane),
                        Some(28) => {}
                        Some(bits) => wrong_width.push((block + lane, *bits)),
                    }
                }
            }
        }
        assert!(
            missing.is_empty(),
            "\n{label}: {} free fields-lane column(s) carry NO range lookup: {missing:?}\n\n\
             `Canonical9`'s first leg is not forced on those lanes, so the committed nonet is not \
             pinned into the encoder's image and `< 2^28` is back to being a producer invariant. \
             Re-emit against `FieldsCanonicity9Emit` — do NOT relax this assertion.\n",
            missing.len()
        );
        assert!(
            wrong_width.is_empty(),
            "\n{label}: fields-lane column(s) range-checked at the WRONG width: {wrong_width:?}\n\n\
             The free lanes are base-`2^28` digits. A wider lookup admits a non-digit; a narrower \
             one refuses honest values. Both are wrong.\n"
        );

        // …and lanes 0/1 are deliberately UNCHECKED (leg 2 is free in-AIR).
        for block in [base, base + B_SPAN] {
            for slot in ROTATED_FIELD_LANE_COL.iter() {
                for lane in slot.iter().take(2) {
                    assert!(
                        !ranged.contains_key(&(block + lane)),
                        "{label}: pinned lane column {} is range-checked — `PinnedLanesField` is \
                         free (a committed column is a BabyBear element); a lookup there is cost \
                         without content, and if it is NARROWER than `p` it REFUSES honest values",
                        block + lane
                    );
                }
            }
        }

        // The `NoWrap` leg's aux lookups: 16 at 24 bits, and 80 at 28 bits past the 112 lanes.
        let at24 = range_checked_columns(&d)
            .into_iter()
            .filter(|(_, b)| *b == 24)
            .count();
        let at28 = range_checked_columns(&d)
            .into_iter()
            .filter(|(_, b)| *b == 28)
            .count();
        assert_eq!(
            at24, 16,
            "\n{label}: {at24} 24-bit range lookups, expected 16 — one `r < 2^24` per (block, slot) \
             for the carry-digit split `L8 = (q0 + 4·q1)·2^24 + r`. Without it the split is \
             unforced and lane 8's top nibble is not the decoder's carry digit.\n"
        );
        assert_eq!(
            at28,
            112 + 64,
            "\n{label}: {at28} 28-bit range lookups, expected 176 = 112 free lanes + 64 `NoWrap` \
             selector columns (`v0, v0b, v1, v1b` per block-slot). Seven lookups per field are \
             NECESSARY AND NOT SUFFICIENT — see \
             `the_off_image_exhibit_passes_all_seven_free_lane_range_checks`.\n"
        );
    }

    assert!(
        rotated_members >= 60,
        "the census only recognised {rotated_members} rotated members of {total_members} — the \
         base derivation is failing and the exact measurement would be vacuously clean"
    );

    // THE COUNT, over every member including the compacted wide ones — now a FLOOR, not a ceiling.
    // `Canonical9` on eight fields in two blocks is 192 lookups per member at minimum.
    assert!(
        min_range_lookups >= 192,
        "\n{leanest} carries only {min_range_lookups} range lookups — below the 192 the \
         fields-canonicity weld puts on every rotated member (112 free lanes + 16 `r` + 64 \
         `v`/`vb`). Either a member escaped the emit or the reader lost the width-tagged fallback.\n"
    );

    // ANTI-VACUITY: the reader DOES find the range lookups that exist, including the ones that
    // predate this weld. A parser that silently matched nothing would report the same clean result.
    let cols: std::collections::BTreeSet<usize> = all_targets.iter().map(|(c, _)| *c).collect();
    assert!(
        cols.contains(&76) && cols.contains(&77),
        "the reader must still find the deployed balance-limb range teeth (columns 76/77)"
    );
    let widths: std::collections::BTreeSet<usize> = all_targets.iter().map(|(_, b)| *b).collect();
    assert!(
        widths.contains(&24) && widths.contains(&28),
        "the reader must find BOTH canonicity widths; it found {widths:?}"
    );
}

/// ANTI-VACUITY for the block-base derivation itself: it must land on the real rotated
/// geometry, not on some other pin pair that happens to sit `B_SPAN` apart.
#[test]
fn the_rotated_block_base_derivation_lands_on_the_real_geometry() {
    let all = members();
    let mut checked = 0usize;
    for (label, d) in &all {
        let Some(base) = rotated_before_base(d) else {
            continue;
        };
        checked += 1;
        // Both blocks must fit inside the declared trace.
        assert!(
            base + 2 * B_SPAN <= d.trace_width,
            "{label}: derived before_base {base} leaves no room for two {B_SPAN}-wide blocks \
             in a {}-column trace",
            d.trace_width
        );
        // The lane columns must be real columns, and the ninth lane of slot 7 is the last of
        // them — column `before_base + B_SPAN + 183`.
        let lanes = rotated_fields_lane_columns(base);
        assert_eq!(
            lanes.len(),
            2 * 8 * 9,
            "{label}: 2 blocks × 8 slots × 9 lanes"
        );
        assert_eq!(
            *lanes.iter().max().unwrap(),
            base + B_SPAN + 183,
            "{label}: the highest fields lane must be the AFTER block's slot-7 ninth lane"
        );
        assert!(
            lanes.iter().all(|c| *c < d.trace_width),
            "{label}: a fields lane column falls outside the declared trace width"
        );
    }
    // The two WIDE registries are E1/S2-compacted (dead columns deleted, survivors
    // renumbered), so their rotated blocks are not at `ROTATED_FIELD_LANE_COL` indices and
    // this derivation deliberately declines them. The 1-felt registry is the uncompacted
    // geometry and must be fully covered.
    assert!(
        checked >= 60,
        "only {checked} of {} members yielded a rotated base — the derivation is too narrow \
         and the exact census would be measuring almost nothing",
        all.len()
    );
}

/// ⚑ **RED-PROOF OF THE CENSUS, BY VARIANT, IN VALUE.** A census that reports "clean"
/// because its reader is broken is worse than no census. This plants a range lookup on a
/// real fields-lane column of a real deployed member — as an in-memory mutation of the
/// PARSED descriptor, so no file in the shared tree is ever touched — and requires the
/// detector to find exactly that column and no other.
///
/// The control matters as much as the mutation: the same member with NOTHING planted must
/// still report zero, or a detector that flagged everything would pass this too.
#[test]
fn the_census_reader_detects_a_planted_lane_range_lookup() {
    use dregg_circuit::descriptor_ir2::LookupSpec;
    use dregg_circuit::lean_descriptor_air::LeanExpr;

    let (label, mut d) = members()
        .into_iter()
        .find(|(_, d)| rotated_before_base(d).is_some())
        .expect("no member with a derivable rotated base");
    let base = rotated_before_base(&d).expect("checked");

    // The control: unmutated, the member covers exactly the 112 FREE lanes and NOT the pinned
    // pair. (Before the canonicity emit this leg read "no covered lane"; it is inverted with the
    // census above, and the property it guards — the reader is not blind — is unchanged.)
    let lanes: std::collections::BTreeSet<usize> =
        rotated_fields_lane_columns(base).into_iter().collect();
    let before: Vec<usize> = range_checked_columns(&d)
        .into_iter()
        .map(|(c, _)| c)
        .filter(|c| lanes.contains(c))
        .collect();
    assert_eq!(
        before.len(),
        112,
        "{label}: the control leg must see exactly the 112 free-lane lookups, found {}",
        before.len()
    );

    // The mutation: ONE lookup on a PINNED lane column (the AFTER block's slot-3 lane 0), which
    // the emit deliberately never range-checks — so a reader that missed it would be blind.
    let planted = base + B_SPAN + ROTATED_FIELD_LANE_COL[3][0];
    let range_tid = d
        .tables
        .iter()
        .find(|t| matches!(t.sem, TableSem::Range { .. }))
        .expect("the member declares a range table")
        .id;
    d.constraints.push(VmConstraint2::Lookup(LookupSpec {
        table: range_tid,
        tuple: vec![LeanExpr::Var(planted)],
    }));

    let after: Vec<usize> = range_checked_columns(&d)
        .into_iter()
        .map(|(c, _)| c)
        .filter(|c| lanes.contains(c) && !before.contains(c))
        .collect();
    assert_eq!(
        after,
        vec![planted],
        "\n{label}: the census reader did not report the PLANTED range lookup on fields-lane \
         column {planted}. The reader is blind, and every clean result it produces above is \
         meaningless. Fix the reader — do not relax the assertion.\n"
    );
}
