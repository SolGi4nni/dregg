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

// ════════════════════════════════════════════════════════════════════════════════════
// BOTH POLES, THROUGH THE DEPLOYED PROVER, IN ONE RUN
//
// Everything above this line is about the emitted BYTES: the encoder's image, the exhibit,
// and a census of which columns the committed constraints name. None of it runs a prover.
// The sentence the epoch actually needs is the pair
//
//   (a) an honest 32-byte field write PROVES and VERIFIES against the deployed member with
//       the canonicity constraints live — the COMPLETENESS pole; and
//   (b) the forged nonet is UNSAT against that SAME member — the SOUNDNESS pole,
//
// and (a) is the one a census cannot reach. A canonicity gate that refuses honest turns is
// worse than no gate, and "the columns are named by 192 lookups" is exactly as compatible
// with that outcome as with the right one.
//
// ⚑ THE WITNESS IS CHOSEN SO THE GADGET IS NOT VACUOUS ON IT. `2·v = q(q−1)·L` and
// `vb = v + q(q−1)` impose NOTHING when `q ∈ {0,1}` — the selector is dead and `v = vb = 0`
// whatever lane 0 holds. Only `q = 2` makes them bite, and it bites HARD: it forces
// `L < 2^28 − 2`, with no slack in either direction. Every pre-existing honest-large fixture
// in this tree (`setfield_value8_epoch_flip::honest_large_fixture` writes `1000` into
// `b[28..32]`) has `q0 = q1 = 0`, so a green under it says nothing at all about the `v` gates.
// The fixture below puts `0xFFFFFFFF` in BOTH pinned windows, which is `q0 = q1 = 2` — both
// selectors LIVE, both `vb` landing at `2^28 − 1`, one below the lookup bound.
// ════════════════════════════════════════════════════════════════════════════════════

/// The field slot the prove-throughs write (the deployed per-slot member is
/// `setFieldVmDescriptor2-{PROVE_SLOT}R24`).
const PROVE_SLOT: usize = 3;

/// **THE MAXIMAL HONEST 32-BYTE FIELD VALUE for this gadget.** `b[24..28] = b[28..32] =
/// 0xFFFFFFFF`, so BOTH pinned windows exceed `2p = 4026531842` and both quotients are `2` —
/// the only quotient at which the `v`/`vb` gates constrain anything. `b[21..24]` are nonzero so
/// the carry-digit remainder `r` is not the degenerate zero, and `b[0..21]` carry a pattern so
/// the seven free lanes are genuinely occupied.
fn maximal_carry_value() -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, x) in b[..21].iter_mut().enumerate() {
        *x = (0xA0 + i) as u8;
    }
    b[21] = 0x11;
    b[22] = 0x22;
    b[23] = 0x33;
    b[24..28].copy_from_slice(&0xFFFF_FFFFu32.to_be_bytes());
    b[28..32].copy_from_slice(&0xFFFF_FFFFu32.to_be_bytes());
    b
}

/// The seven aux values the deployed producer must have written for `(blk, slot)`, derived here
/// from the nonet ALONE — an independent transcription of
/// `Emit/FieldsCanonicity9Emit.gadgetBodies`, not a call into the producer's own fill. If the two
/// ever disagree, one of them is wrong and this says which columns.
fn expected_aux(lanes: &[BabyBear; 9]) -> [u64; 7] {
    let l0 = lanes[0].as_u32() as u64;
    let l1 = lanes[1].as_u32() as u64;
    let l8 = lanes[8].as_u32() as u64;
    let c = l8 >> 24;
    let (q0, q1) = (c % 4, c / 4);
    let (t0, t1) = (u64::from(q0 == 2), u64::from(q1 == 2));
    [
        l8 & 0x00ff_ffff,
        q0,
        q1,
        t0 * l0,
        t0 * l0 + 2 * t0,
        t1 * l1,
        t1 * l1 + 2 * t1,
    ]
}

/// The fixture's nonet really does drive the gadget's ONLY live arm. Cheap, no prover — so a
/// regression in the fixture is caught here rather than showing up as a mysteriously easy green
/// in the prove-through below.
#[test]
fn the_prove_through_fixture_drives_the_live_arm_of_the_gadget() {
    let lanes = field_limbs9(&maximal_carry_value());
    let aux = expected_aux(&lanes);
    assert_eq!(
        aux[1], 2,
        "q0 must be 2 — the only quotient the `v` gates bite at"
    );
    assert_eq!(aux[2], 2, "q1 must be 2");
    assert_ne!(
        aux[0], 0,
        "the carry remainder `r` must not be the degenerate zero"
    );
    // `v0 = L0` and `v0b = L0 + 2` must BOTH fit the 28-bit lookups — this is the tight fit the
    // Lean records as "no slack in either direction" (`L < 2^28 − 2 = 2^32 − 2p`).
    assert!(aux[3] < CH && aux[4] < CH, "v0/v0b must fit 2^28: {aux:?}");
    assert!(aux[5] < CH && aux[6] < CH, "v1/v1b must fit 2^28: {aux:?}");
    assert_eq!(
        aux[4],
        CH - 1,
        "the fixture is MAXIMAL: v0b is one below the bound, so a gadget off by one in either \
         direction refuses it"
    );
    assert!(
        canonical9(&lanes),
        "an honest encoding is canonical by construction"
    );
}

/// The deployed per-slot setField member, from the COMMITTED narrow registry.
fn deployed_setfield_member(slot: usize) -> EffectVmDescriptor2 {
    let key = format!("setFieldVmDescriptor2-{slot}R24");
    let json = dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() != Some(key.as_str()) {
                return None;
            }
            let _ = it.next();
            it.next()
        })
        .unwrap_or_else(|| panic!("{key} not in V3_STAGED_REGISTRY_TSV"));
    dregg_circuit::descriptor_ir2::parse_vm_descriptor2(json).expect("deployed member parses")
}

/// The honest narrow trace + PI vector for a `setField(PROVE_SLOT, value)` turn, built through the
/// LIVE producer.
///
/// ⚠ The v1 face value is `field_limbs9(&value)[0]` — the DEPLOYED projector, byte-identically what
/// `turn::executor::effect_vm_bridge::field_element_to_bb` and `sdk::cipherclerk`'s twin emit. The
/// older fixtures in this tree pass `fold_bytes32_to_bb` there instead, which makes the welded lane
/// 0 disagree with the nonet the cell encodes — harmless while the carry digit is 0 (the `v` gates
/// are dead), and exactly the incoherence the gadget is here to refuse once it is not.
fn honest_setfield_trace(value: [u8; 32]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    use dregg_cell::{Cell, Ledger};
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    };
    use dregg_circuit::effect_vm::{CellState, Effect};
    use dregg_turn::rotation_witness as rw;

    let balance: i64 = 50_000;
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let before_cell = Cell::with_balance(pk, [0u8; 32], balance);
    let mut after_cell = before_cell.clone();
    assert!(after_cell.state.set_field(PROVE_SLOT, value), "set_field");

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let z8 = dregg_circuit::heap_root::empty_heap_root_8();
    let rvk = dregg_turn::rotation_witness::empty_revoked_root_8();
    let rlog = vec![[3u8; 32]];
    let bridge = |w: &rw::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
    };
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &z8,
        &z8,
        &rvk,
        &rlog,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &z8,
        &z8,
        &rvk,
        &rlog,
        &Default::default(),
    );

    generate_rotated_effect_vm_trace(
        &CellState::new(balance as u64, 0),
        &[Effect::SetField {
            field_idx: PROVE_SLOT as u32,
            value: field_limbs9(&value)[0],
        }],
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
    )
    .expect("the live rotated producer must emit an honest setField trace")
}

fn proves_and_verifies(
    d: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
) -> Result<(), String> {
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
    };
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(d, trace, dpis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(d, &proof, dpis)
    })) {
        Ok(Ok(())) => Ok(()),
        Ok(Err(e)) => Err(format!("{e:?}")),
        Err(_) => Err("panicked".into()),
    }
}

/// Every column any row-local body or lookup of this constraint names.
fn constraint_columns(c: &VmConstraint2) -> Vec<usize> {
    fn walk(e: &dregg_circuit::lean_descriptor_air::LeanExpr, out: &mut Vec<usize>) {
        use dregg_circuit::lean_descriptor_air::LeanExpr as E;
        match e {
            E::Var(v) => out.push(*v),
            E::Const(_) => {}
            E::Add(a, b) | E::Mul(a, b) => {
                walk(a, out);
                walk(b, out);
            }
        }
    }
    let mut out = Vec::new();
    if let Some(body) = dregg_circuit::descriptor_ir2::row_local_body(c) {
        walk(&body, &mut out);
    }
    if let VmConstraint2::Lookup(l) = c {
        for t in &l.tuple {
            walk(t, &mut out);
        }
    }
    out
}

/// The 112 canonicity AUX columns of a member whose rotated appendix is based at `before_base`
/// (`Emit/FieldsCanonicity9Emit.auxColsAt`). NOT the lane columns — those are committed limbs.
fn canon9_aux_columns(before_base: usize) -> std::ops::Range<usize> {
    use dregg_circuit::effect_vm::layout_generated::{CANON9_REGION_OFF, CANON9_SPAN};
    before_base + CANON9_REGION_OFF..before_base + CANON9_REGION_OFF + CANON9_SPAN
}

/// ⚑ **BOTH POLES, ONE RUN, THROUGH `prove_vm_descriptor2` + `verify_vm_descriptor2` AGAINST THE
/// COMMITTED `setFieldVmDescriptor2-3R24` BYTES.**
///
/// 1. **COMPLETENESS.** An honest 32-byte field write whose nonet drives the gadget's only live arm
///    (`q0 = q1 = 2`, both `vb` one below the 28-bit bound) PROVES and VERIFIES. This is the claim a
///    census cannot make and the one a canonicity gate can most easily break.
/// 2. **THE AUX IS FILLED.** The seven producer columns per `(block, slot)` carry exactly the values
///    an independent transcription of `gadgetBodies` derives from the nonet — checked on BOTH blocks
///    and all sixteen slots, so a producer that filled only the written one would fail here.
/// 3. **THE AUX IS READ** (anti-vacuity, by variant). Zeroing ONLY the written slot's seven AFTER
///    aux columns — nothing else — makes the same member UNSAT. Without this leg a green (1) is
///    equally consistent with 112 columns nobody looks at.
/// 4. **SOUNDNESS.** The forged nonet (`FORGED`, lane 8 = `3·2^24`) is UNSAT at the prover, with the
///    rotated commitment RECOMPUTED and every moved PI re-read — so the refusal cannot be the stale
///    commitment or a stale pin.
/// 5. **THE CONTROL THAT MAKES (4) MEAN CANONICITY.** The identical forged trace and PI vector PROVE
///    against the same member with the 192 aux-reading constraints deleted in value — the 112
///    free-lane `< 2^28` lookups still present and still satisfied. That is
///    `free_lane_ranges_alone_do_not_force_the_image` at the prover instead of in the model.
#[test]
fn both_poles_through_the_deployed_prover() {
    use dregg_circuit::effect_vm::layout_generated::{CANON9_PER_SLOT, CANON9_REGION_OFF};
    use dregg_circuit::effect_vm::trace_rotated::{
        AFTER_BASE, BEFORE_BASE, V1_PI_COUNT, recompute_after_blocks_for_test,
    };

    let value = maximal_carry_value();
    let desc = deployed_setfield_member(PROVE_SLOT);
    let (mut trace, mut dpis) = honest_setfield_trace(value);
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "the live producer emits the committed member's PI shape"
    );

    // ── (2) THE AUX IS FILLED — both blocks, all sixteen slots, against an independent derivation.
    let aux_of = |t: &[Vec<BabyBear>], blk: usize, slot: usize| -> [u64; 7] {
        let a =
            BEFORE_BASE + CANON9_REGION_OFF + blk * (8 * CANON9_PER_SLOT) + slot * CANON9_PER_SLOT;
        core::array::from_fn(|k| t[0][a + k].as_u32() as u64)
    };
    let lanes_of_block = |t: &[Vec<BabyBear>], blk: usize, slot: usize| -> [BabyBear; 9] {
        let bb = if blk == 0 { BEFORE_BASE } else { AFTER_BASE };
        core::array::from_fn(|lane| t[0][bb + ROTATED_FIELD_LANE_COL[slot][lane]])
    };
    for blk in 0..2 {
        for slot in 0..8 {
            assert_eq!(
                aux_of(&trace, blk, slot),
                expected_aux(&lanes_of_block(&trace, blk, slot)),
                "\nthe producer's canonicity aux for (block {blk}, slot {slot}) is not the gadget's \
                 own derivation from that block's nonet. Fix the PRODUCER — a canonicity gate that \
                 refuses honest turns is worse than no gate, and relaxing the constraint to match a \
                 wrong fill would undo the epoch.\n"
            );
        }
    }
    // …and the written slot's AFTER aux is the LIVE arm (not sixteen copies of the dead one).
    let written = aux_of(&trace, 1, PROVE_SLOT);
    assert_eq!(
        (written[1], written[2]),
        (2, 2),
        "q0/q1 live on the written slot"
    );
    assert_eq!(
        aux_of(&trace, 0, PROVE_SLOT)[1],
        0,
        "the pre-state slot is empty, q0 = 0"
    );

    // ── (1) THE COMPLETENESS POLE.
    proves_and_verifies(&desc, &trace, &dpis).unwrap_or_else(|e| {
        panic!(
            "\n⚑ AN HONEST 32-BYTE FIELD WRITE IS UNSAT ON THE DEPLOYED MEMBER: {e}\n\n\
             This is the failure mode the fields-canonicity epoch must not have. Do NOT widen or \
             drop a canonicity constraint to make it pass — find the producer path that did not \
             fill its aux (`trace_rotated::fill_block` is the only writer of a nonet lane, and it \
             lays the aux itself) and fix it there.\n"
        )
    });
    eprintln!(
        "CANON9 COMPLETENESS: an honest 32-byte write at q0=q1=2 (v0b = 2^28 − 1, one below the \
         bound) PROVES + VERIFIES on the deployed setFieldVmDescriptor2-{PROVE_SLOT}R24."
    );

    // ── (3) THE AUX IS READ — zero the written slot's seven AFTER columns and nothing else.
    {
        let a =
            BEFORE_BASE + CANON9_REGION_OFF + 8 * CANON9_PER_SLOT + PROVE_SLOT * CANON9_PER_SLOT;
        let mut t = trace.clone();
        for row in t.iter_mut() {
            for k in 0..CANON9_PER_SLOT {
                row[a + k] = BabyBear::ZERO;
            }
        }
        assert!(
            proves_and_verifies(&desc, &t, &dpis).is_err(),
            "\nZEROING the written slot's seven canonicity aux columns left the member SATISFIABLE. \
             Those columns are then read by nothing, the 192 lookups the census counts are decoration, \
             and the completeness green above is vacuous.\n"
        );
    }

    // ── (4) THE SOUNDNESS POLE — the forged nonet, with every dependent value re-derived.
    let lane8_col = AFTER_BASE + ROTATED_FIELD_LANE_COL[PROVE_SLOT][8];
    for row in trace.iter_mut() {
        row[lane8_col] = BabyBear::new(FORGED[8]);
        // The forger's BEST aux: exactly what the producer's own derivation yields for this lane 8.
        // `c = 3` ⇒ `r = 0`, `q0 = 3`, `q1 = 0`, both selectors dead. Every range lookup passes and
        // the split gate `L8 = (q0 + 4·q1)·2^24 + r` is SATISFIED. What has no witness is
        // `q0(q0−1)(q0−2) = 0`, which is 6.
        let a =
            BEFORE_BASE + CANON9_REGION_OFF + 8 * CANON9_PER_SLOT + PROVE_SLOT * CANON9_PER_SLOT;
        let forged_lanes: [BabyBear; 9] =
            core::array::from_fn(|lane| row[AFTER_BASE + ROTATED_FIELD_LANE_COL[PROVE_SLOT][lane]]);
        let forged_aux = expected_aux(&forged_lanes);
        for (k, v) in forged_aux.iter().enumerate() {
            row[a + k] = BabyBear::new(*v as u32);
        }
    }
    // The rotated AFTER commitment absorbs lane 8, so re-chain it and re-read every PI it moved:
    // the rotated NEW commit and the written slot's ninth value8 pin. Without this the refusal
    // below would be the commitment's, not canonicity's.
    recompute_after_blocks_for_test(&mut trace);
    let last = trace.len() - 1;
    dpis[V1_PI_COUNT + 1] = trace[last][AFTER_BASE + B_STATE_COMMIT];
    for lane in 1..=8usize {
        dpis[46 + lane - 1] = trace[last][AFTER_BASE + ROTATED_FIELD_LANE_COL[PROVE_SLOT][lane]];
    }
    let forged_verdict = proves_and_verifies(&desc, &trace, &dpis);
    assert!(
        forged_verdict.is_err(),
        "\n⚑ THE FORGED NONET PROVED. Lane 8 = 3·2^24 makes the welded v1 face read {} while the \
         committed nonet decodes to {} — one accepted proof, two answers to \"what is fields[{}]\". \
         `canon9_rejects_the_forged_nonet` says this member has no witness; it just found one.\n",
        trace[last][AFTER_BASE + ROTATED_FIELD_LANE_COL[PROVE_SLOT][0]].as_u32(),
        HONEST_VALUE,
        PROVE_SLOT
    );
    eprintln!(
        "CANON9 SOUNDNESS: the forged nonet is UNSAT at the deployed prover ({forged_verdict:?})."
    );

    // ── (5) THE CONTROL — the same bytes prove once the 192 aux-reading constraints are gone.
    {
        let aux_cols = canon9_aux_columns(BEFORE_BASE);
        let mut stripped = desc.clone();
        let before = stripped.constraints.len();
        stripped
            .constraints
            .retain(|c| !constraint_columns(c).iter().any(|v| aux_cols.contains(v)));
        let removed = before - stripped.constraints.len();
        assert_eq!(
            removed,
            16 * (7 + 5),
            "the strip must remove exactly the 7 gates + 5 aux lookups per (block, slot) = 192; it \
             removed {removed}. The 112 free-lane `< 2^28` lookups name LANE columns, not aux \
             columns, and must SURVIVE — they are what the control keeps satisfied."
        );
        proves_and_verifies(&stripped, &trace, &dpis).unwrap_or_else(|e| {
            panic!(
                "\nthe forged trace is refused even WITHOUT the canonicity gadget ({e}), so leg (4) \
                 was measuring something else — a stale commitment, a stale pin, or a free-lane \
                 lookup. Re-derive whatever moved before reading (4) as a canonicity result.\n"
            )
        });
        eprintln!(
            "CANON9 CONTROL: with the {removed} aux-reading constraints deleted the IDENTICAL forged \
             trace PROVES — the 112 free-lane range lookups alone do not force the image, at the \
             prover and not only in the model."
        );
    }
}
