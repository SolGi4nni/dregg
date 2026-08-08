//! # The owner-key nonet's CANONICITY ENVELOPE, at the deployed prover.
//!
//! ## What this is about, said at the right resolution
//!
//! The 2026-08-01 key-nonet flag day gave the owner key a ninth lane (in-block pre-limb
//! `B_PUBKEY_NINTH_LANE = 186`) and taught both producers to write all nine base-`2^29` lanes. That
//! made `state_commit` **BIND** the nonet: the committed columns are entries of the list
//! `wireCommitR` folds, and `A` / `−A` separate on the key's own carrier.
//!
//! It did **not** make anything **REFUSE** a lane vector outside the encoder's image.
//! `Emit.KeyCanonicity9Emit.keyCanonical9At` was authored, proved and applied by NOTHING —
//! measured over the two committed registries on 2026-08-02: **10560** range lookups at 28 bits
//! (the fields nonet), **960** at 24 bits, and **ZERO** at 29 bits, which is the key nonet's lane
//! width and therefore the width nothing had ever emitted.
//!
//! ## The wound, in one addition
//!
//! `key_from_lanes9` is TOTAL: it reads any nine lanes modulo `2^256`. Lane 8's weight is
//! `(2^29)^8 = 2^232` and its honest range is `[0, 2^24)`, so
//!
//! ```text
//!     lane8  ↦  lane8 + 2^24        (still a legal BabyBear felt: 120 · 2^24 = p − 1)
//! ```
//!
//! adds exactly `2^256` to the recomposed value and therefore **decodes to the very same 32
//! bytes**. Every owner key thus has **120 distinct committed nonets** (121 when its top lane is
//! zero) — one canonical, the rest outside the image — and without this envelope the AIR refuses
//! none of them. Two readers of one accepted proof then disagree: `key_from_lanes9` says "the owner
//! is `A`", and `Faithful9::from_key_lanes9(A)` says "those are not `A`'s columns".
//!
//! ⚠ **Get the primitive right.** This is an INJECTIVITY question about a KEY, not a collision
//! bound about a hash node. The nine-lane encoder's image is exactly `2^256` and it is injective
//! with a machine-checked left inverse (`KeyLanes9.keyToLanes9_injective`); what was missing is the
//! in-AIR statement that the committed columns lie IN that image. `2^123.63` is the hash-node
//! figure and has no business in this file.
//!
//! ## The legs, and why each is here
//!
//! 1. **THE CENSUS** (`every_deployed_member_range_checks_the_owner_key_nonet`) — every rotated
//!    member of the committed registry carries, per block, eight `< 2^29` lookups on the octet
//!    `105..=112` and exactly ONE `< 2^24` lookup on limb 186. Read off the deployed bytes with
//!    the width-tagged wire-id fallback, without which the reader is blind (a `tables`-only reader
//!    reports zero and every census over it is vacuously clean). **This is the leg that is RED
//!    until the descriptor regen installs the re-emitted bytes**, and it is red on purpose: the
//!    Lean wiring is committed, the artifacts are not.
//! 2. **OLD ADMITS / NEW REJECTS** — one forged trace, two descriptors that differ by exactly the
//!    18 emitted lookups. The forged trace carries `lane8 + 2^24` in BOTH blocks (so the owner
//!    freeze, which welds all nine lanes BEFORE↔AFTER, is satisfied and cannot be what refuses),
//!    with the whole `wireCommitR` chain and every PI re-derived by the live producer from the
//!    mutated pre-limbs. It PROVES and VERIFIES without the envelope and is UNSAT with it.
//! 3. **THE NARROW LEG IS LOAD-BEARING** — widen lane 8's lookup from 24 to 29 "for uniformity"
//!    and the identical forged trace proves again. This is `keyCanon9_rejects_the_forged_nonet`'s
//!    content at the prover instead of in the model, and it is the anti-vacuity leg: the refusal
//!    in (2) is the narrow lookup and nothing else.
//! 4. **COMPLETENESS** — a 4100-key corpus is canonical, round-trips and is injective; a
//!    structured subset PROVES and VERIFIES with the envelope on. A canonicity gate that refuses
//!    honest turns is worse than no gate.
//!
//! ## Substrate
//!
//! Lean-authored AIR. Every constraint this file reasons about is emitted by
//! `Dregg2.Circuit.Emit.KeyCanonicity9Emit.keyCanonical9Wire` through
//! `metatheory/EmitRotationV3.lean`; nothing here writes a gate. What Rust does is build witnesses
//! and read verdicts. The theorems named below are about the LEAN object
//! (`keyCanon9Wire_determines_the_owner_key`, `keyCanon9Wire_rejects_the_forged_nonet`); these are
//! case tests against it, never a substitute for it.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    CUSTOM_RANGE_WIDTHS, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    RANGE_W_TID_WIRE_BASE, TableSem, VmConstraint2, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::layout_generated::{
    B_PUBKEY_NINTH_LANE, B_PUBKEY_OCTET, B_SPAN, KEY_LANE_BITS, KEY_TOP_BITS, NUM_PRE_LIMBS,
};
use dregg_circuit::effect_vm::trace_rotated::{
    BEFORE_BASE, RotatedBlockWitness, avail_pad_for_descriptor_name, empty_caveat_manifest,
    generate_rotated_effect_vm_trace,
};
use dregg_circuit::effect_vm::{CellState, Effect, PUBKEY_NONET_LANE_COL, key_from_lanes9};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_turn::rotation_witness as rw;

/// `2^24` — the top lane's honest ceiling, and the smallest step that maps a canonical nonet off
/// the image while leaving its decode byte-identical. Lean `KeyLanes9.KTOP` / `KEY_TOP_BITS`.
const KTOP: u32 = 1 << 24;

/// The wire table id a `bits`-wide range lookup rides. The inverse of Lean
/// `EffectVmEmitV2.rangeTidW`, as `descriptor_ir2::MainLayout::build` reads it.
fn range_tid(bits: usize) -> usize {
    RANGE_W_TID_WIRE_BASE + bits
}

// ════════════════════════════════════════════════════════════════════════════════════
// §1 — reading the deployed bytes
// ════════════════════════════════════════════════════════════════════════════════════

fn narrow_members() -> Vec<(String, EffectVmDescriptor2)> {
    let mut out = Vec::new();
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut cols = line.splitn(3, '\t');
        let key = cols.next().unwrap_or_default().to_string();
        let name = cols.next().unwrap_or_default().to_string();
        let Some(json) = cols.next() else { continue };
        let d = parse_vm_descriptor2(json)
            .unwrap_or_else(|e| panic!("{key}: deployed bytes do not decode: {e}"));
        assert_eq!(
            d.name, name,
            "{key}: TSV name column disagrees with the JSON"
        );
        out.push((key, d));
    }
    assert!(
        !out.is_empty(),
        "the narrow registry reader found no members"
    );
    out
}

/// Every `(column, bits)` a range-semantics lookup of this member targets.
///
/// ⚑ **THE WIDTH-TAGGED FALLBACK IS NOT OPTIONAL.** A range lookup needs no `tables` entry:
/// `MainLayout::build` recovers `bits` from the wire id (`tid − RANGE_W_TID_WIRE_BASE`) whenever
/// the width is in `CUSTOM_RANGE_WIDTHS`, and the availability weld, the fields canonicity and
/// this envelope all ride that path. A `tables`-only reader reports ZERO lookups here and reads
/// green over an empty envelope.
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
                    [LeanExpr::Var(w)] => Some((*w, bits)),
                    _ => None,
                }
            }
            _ => None,
        })
        .collect()
}

/// The v1-face width this member's rotated appendix rides at — the Rust twin of Lean
/// `FieldsCanonicity9Emit.faceWidthOfName`, which `keyCanonical9Wire` reads.
fn face_width(name: &str) -> usize {
    BEFORE_BASE + avail_pad_for_descriptor_name(name)
}

/// The nine owner-nonet columns of block `blk` at a member whose v1 face is `w` wide.
/// The Rust reading of Lean `KeyCanonicity9Emit.deployedKeyCanon9Cols`.
fn nonet_cols(w: usize, blk: usize) -> [usize; 9] {
    core::array::from_fn(|lane| w + blk * B_SPAN + PUBKEY_NONET_LANE_COL[lane])
}

/// The 18 lookups the envelope emits at face width `w`, in emission order — the Rust reading of
/// `keyCanon9ConstraintsAt (deployedKeyCanon9Cols w)`.
fn envelope_lookups(w: usize) -> Vec<VmConstraint2> {
    let mut out = Vec::new();
    for blk in 0..2 {
        let cols = nonet_cols(w, blk);
        for lane in cols.iter().take(8) {
            out.push(VmConstraint2::Lookup(LookupSpec {
                table: range_tid(KEY_LANE_BITS),
                tuple: vec![LeanExpr::Var(*lane)],
            }));
        }
        out.push(VmConstraint2::Lookup(LookupSpec {
            table: range_tid(KEY_TOP_BITS),
            tuple: vec![LeanExpr::Var(cols[8])],
        }));
    }
    assert_eq!(out.len(), 18);
    out
}

/// The two poles of the exhibit, from ONE deployed member: the member WITHOUT the envelope and the
/// member WITH it, differing by exactly the 18 emitted lookups and nothing else.
///
/// Whichever side the committed bytes are on, this yields the same pair — so the exhibit measures
/// the envelope both before and after the descriptor regen installs it, and cannot silently start
/// measuring something else. The census test is what pins which side the committed bytes are on.
fn the_two_poles(d: &EffectVmDescriptor2) -> (EffectVmDescriptor2, EffectVmDescriptor2) {
    let w = face_width(&d.name);
    let envelope = envelope_lookups(w);
    let present = d
        .constraints
        .iter()
        .filter(|c| envelope.contains(c))
        .count();
    assert!(
        present == 0 || present == 18,
        "{}: {present} of the 18 envelope lookups are present — a PARTIAL envelope is neither \
         pole, and the exhibit below would be measuring an object no emitter prints",
        d.name
    );
    let mut without = d.clone();
    without.constraints.retain(|c| !envelope.contains(c));
    let mut with = without.clone();
    with.constraints.extend(envelope);
    assert_eq!(with.constraints.len(), without.constraints.len() + 18);
    (without, with)
}

// ════════════════════════════════════════════════════════════════════════════════════
// §2 — the geometry, and the census
// ════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **THE GEOMETRY IS NOT A STRIDE.** Lane 8 lives at limb 186 while the octet ends at 112, so a
/// `base + 8` reconstruction would land on `contract_hash`'s territory. Pinned here because this
/// file computes columns.
#[test]
fn the_nonet_geometry_is_the_layouts_and_not_a_stride() {
    assert_eq!(PUBKEY_NONET_LANE_COL[0], B_PUBKEY_OCTET);
    assert_eq!(PUBKEY_NONET_LANE_COL[7], B_PUBKEY_OCTET + 7);
    assert_eq!(PUBKEY_NONET_LANE_COL[8], B_PUBKEY_NINTH_LANE);
    assert_ne!(
        PUBKEY_NONET_LANE_COL[8],
        B_PUBKEY_OCTET + 8,
        "the ninth lane is NOT adjacent to its octet — never stride it"
    );
    // ⚑ `B_PUBKEY_NINTH_LANE < NUM_PRE_LIMBS` (Lean `lane8_is_absorbed_iff`) is const-asserted in
    // `dregg_circuit::effect_vm::PUBKEY_NONET_LANE_COL`'s initializer — a build obligation, so this
    // file cannot even link against a layout where the envelope range-checks an unabsorbed felt.
    assert_eq!((KEY_LANE_BITS, KEY_TOP_BITS), (29, 24));
    assert_eq!(
        8 * KEY_LANE_BITS + KEY_TOP_BITS,
        256,
        "the two widths are the EXACT fit — a uniform 29 would leave 2^5 whole wraps of the byte \
         window available"
    );
    // Both widths must be realizable by the deployed IR-2 interpreter, or the emit lowers into a
    // table that does not exist and every member fails closed at parse time.
    assert!(CUSTOM_RANGE_WIDTHS.contains(&KEY_LANE_BITS));
    assert!(CUSTOM_RANGE_WIDTHS.contains(&KEY_TOP_BITS));
}

/// ⚑ **EVERY DEPLOYED MEMBER RANGE-CHECKS THE OWNER NONET, AT BOTH BLOCKS AND AT BOTH WIDTHS.**
///
/// This is the standing gate on the committed bytes. It read RED on 2026-08-02 — zero 29-bit
/// lookups in 10.2 MB of committed descriptor bytes — which is what "applied by NOTHING" means
/// measured rather than asserted, and it goes green when the re-emitted registry is installed.
#[test]
fn every_deployed_member_range_checks_the_owner_key_nonet() {
    let mut checked = 0usize;
    for (key, d) in narrow_members() {
        let w = face_width(&d.name);
        let ranges = range_checked_columns(&d);
        for blk in 0..2 {
            let cols = nonet_cols(w, blk);
            for (lane, col) in cols.iter().enumerate().take(8) {
                assert!(
                    ranges.contains(&(*col, KEY_LANE_BITS)),
                    "\n⚑ {key} ({}) block {blk} lane {lane}: column {col} carries NO `< 2^29` \
                     range lookup. The committed nonet is bound by `wireCommitR` and refused by \
                     nothing — a prover may publish lanes outside the encoder's image and the AIR \
                     does not object. Wire `KeyCanonicity9Emit.keyCanonical9Wire` into the emit \
                     driver and re-emit; do NOT relax this census.\n",
                    d.name
                );
            }
            assert!(
                ranges.contains(&(cols[8], KEY_TOP_BITS)),
                "\n⚑ {key} ({}) block {blk}: the NINTH lane at column {} carries no `< 2^24` \
                 lookup. This is the leg a uniform nine-lane check does not give: `[0,…,0,2^24]` \
                 passes `< 2^29` on every lane, recomposes to exactly 2^256 and decodes \
                 byte-for-byte to the all-zero key.\n",
                d.name,
                cols[8]
            );
            assert!(
                !ranges.contains(&(cols[8], KEY_LANE_BITS)),
                "\n⚑ {key}: the ninth lane ALSO carries a `< 2^29` lookup. If the narrow leg was \
                 widened \"for uniformity\", the encoding is re-opened — see \
                 `the_narrow_leg_alone_is_what_refuses_the_forgery`.\n"
            );
            checked += 1;
        }
    }
    assert!(
        checked >= 2 * 60,
        "the census covered only {checked} (member, block) pairs — a shrunken census passes \
         vacuously"
    );
    eprintln!("KEY-CANON9 CENSUS: {checked} (member, block) nonets range-checked at 8×29 + 1×24.");
}

/// The census reader must be able to report the ABSENCE it exists to detect, and the two-pole
/// split must remove exactly what it claims. Without this, a reader that always returns the empty
/// list would make the census above trivially satisfiable in the other direction.
#[test]
fn the_census_reader_and_the_pole_split_can_both_go_red() {
    let (_key, d) = narrow_members()
        .into_iter()
        .find(|(k, _)| k == "cellSealVmDescriptor2R24")
        .expect("cellSealVmDescriptor2R24 is a deployed member");
    let w = face_width(&d.name);
    let cols: Vec<usize> = (0..2).flat_map(|b| nonet_cols(w, b)).collect();
    let (without, with) = the_two_poles(&d);

    let seen = |m: &EffectVmDescriptor2| {
        range_checked_columns(m)
            .into_iter()
            .filter(|(c, _)| cols.contains(c))
            .count()
    };
    assert_eq!(
        seen(&with),
        18,
        "the WITH pole must show all 18 envelope lookups to this reader"
    );
    assert_eq!(
        seen(&without),
        0,
        "the WITHOUT pole must show none — if the reader still reports lookups after they were \
         removed, it is not reading what it claims to read"
    );
    // …and the two poles differ by NOTHING else.
    assert_eq!(with.trace_width, without.trace_width);
    assert_eq!(with.public_input_count, without.public_input_count);
    assert_eq!(with.tables, without.tables);
    assert_eq!(with.constraints.len(), without.constraints.len() + 18);
}

// ════════════════════════════════════════════════════════════════════════════════════
// §3 — THE EXHIBIT: one forged trace, two descriptors
// ════════════════════════════════════════════════════════════════════════════════════

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn cell_owned_by(pk: [u8; 32], balance: i64, nonce: u64) -> Cell {
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// The live rotated producer's trace + PI vector for a `cellSeal` turn on a cell owned by `pk`,
/// with `lane8_delta` ADDED to the owner nonet's ninth lane in **both** blocks.
///
/// ⚠ The delta goes on BOTH blocks deliberately. `OwnerFreezeWire` welds every owner nonet lane
/// BEFORE↔AFTER with a whole-domain `colEq`, so a one-sided mutation is refused by the FREEZE and
/// the verdict would be misattributed. Moving both keeps the freeze satisfied and leaves the
/// envelope as the only thing that can object.
///
/// The mutation is applied to `pre_limbs` BEFORE `RotatedBlockWitness::new`, so the trace generator
/// recomputes the entire `wireCommitR` absorption chain, `B_STATE_COMMIT` and every published PI
/// from the mutated limbs. The forged witness is therefore self-consistent: nothing stale is left
/// to refuse it.
fn rotated_cellseal_trace(pk: [u8; 32], lane8_delta: u32) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let balance: i64 = 50_000;
    let before_cell = cell_owned_by(pk, balance, 0);
    let mut after_cell = cell_owned_by(pk, balance, 1);
    after_cell.seal([9u8; 32], 0).expect("Live cell must seal");

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &rw::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let bridge = |w: &rw::RotationWitness| {
        let mut pre = w.pre_limbs.clone();
        assert_eq!(pre.len(), NUM_PRE_LIMBS);
        pre[B_PUBKEY_NINTH_LANE] += BabyBear::new(lane8_delta);
        RotatedBlockWitness::new(pre, w.iroot).expect("pre-iroot limbs")
    };

    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);

    generate_rotated_effect_vm_trace(
        &CellState::new(balance as u64, 0),
        &[Effect::CellSeal {
            target: [BabyBear::new(0); 8],
            reason_hash: [BabyBear::new(9); 8],
        }],
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
    )
    .expect("the live rotated producer must emit a cellSeal trace")
}

fn proves_and_verifies(
    d: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
) -> Result<(), String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(d, trace, dpis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(d, &proof, dpis)
    })) {
        Ok(Ok(())) => Ok(()),
        Ok(Err(e)) => Err(format!("{e:?}")),
        Err(_) => Err("the deployed prover panicked".into()),
    }
}

fn deployed_cellseal() -> EffectVmDescriptor2 {
    narrow_members()
        .into_iter()
        .find(|(k, _)| k == "cellSealVmDescriptor2R24")
        .expect("cellSealVmDescriptor2R24 is a deployed member")
        .1
}

/// ⚑⚑ **OLD ADMITS, NEW REJECTS — one forged nonet, through `prove_vm_descriptor2` +
/// `verify_vm_descriptor2` over the COMMITTED `cellSealVmDescriptor2R24` bytes.**
///
/// The forgery is the minimum one: `lane8 ↦ lane8 + 2^24`, both blocks. It is
/// * **outside the encoder's image** — `canonicalKey9_iff_in_image` is exactly `lane8 < 2^24`;
/// * **decodable to the honest key** — `key_from_lanes9` reads it modulo `2^256`, so an accepted
///   proof carrying it says the owner is the honest key while its committed columns are not that
///   key's columns;
/// * **self-consistent** — the producer re-folded `wireCommitR` and every PI over the mutated
///   limbs, so no stale commitment and no stale pin can be doing the refusing. Leg (b) is what
///   proves that: without the envelope the very same bytes are ACCEPTED.
#[test]
fn old_admits_new_rejects_at_the_deployed_prover() {
    // A key whose ninth lane is NON-ZERO, so `lane8 + 2^24` aliases a genuine key rather than zero.
    let mut pk = [0u8; 32];
    pk[0] = 7;
    pk[31] = 0x5A;

    let (without, with) = the_two_poles(&deployed_cellseal());
    let w = face_width(&with.name);

    let (honest_trace, honest_pis) = rotated_cellseal_trace(pk, 0);
    let (forged_trace, forged_pis) = rotated_cellseal_trace(pk, KTOP);
    let read_nonet = |t: &[Vec<BabyBear>], blk: usize| -> [BabyBear; 9] {
        let cols = nonet_cols(w, blk);
        core::array::from_fn(|lane| t[0][cols[lane]])
    };
    let honest_nonet = read_nonet(&honest_trace, 0);
    let forged_nonet = read_nonet(&forged_trace, 0);

    // ── the forgery is exactly what it claims to be.
    assert_eq!(
        key_from_lanes9(&honest_nonet),
        pk,
        "the honest nonet must decode to the cell's own public key — otherwise the columns this \
         exhibit reads are not the owner key's"
    );
    assert_eq!(
        forged_nonet[8].as_u32(),
        honest_nonet[8].as_u32() + KTOP,
        "the forgery is exactly one addition on lane 8"
    );
    assert!(
        honest_nonet[8].as_u32() < KTOP && forged_nonet[8].as_u32() >= KTOP,
        "the honest top lane must be IN the image ({} < 2^24) and the forged one OUT of it — \
         otherwise this exhibit is measuring nothing",
        honest_nonet[8].as_u32()
    );
    assert_eq!(
        key_from_lanes9(&forged_nonet),
        key_from_lanes9(&honest_nonet),
        "\n⚑ the two nonets must DECODE IDENTICALLY — that is the whole bite. If they differ, the \
         mutation changed the key rather than aliasing its representation.\n"
    );
    assert_eq!(
        read_nonet(&forged_trace, 1)[8],
        forged_nonet[8],
        "both blocks must carry the same forged lane or the OWNER FREEZE, not the envelope, is \
         what refuses leg (c)"
    );

    // ── (a) COMPLETENESS with the envelope on: the honest nonet proves and verifies.
    proves_and_verifies(&with, &honest_trace, &honest_pis).unwrap_or_else(|e| {
        panic!(
            "\n⚑ AN HONEST OWNER KEY IS UNSAT UNDER THE ENVELOPE: {e}\n\n\
             Do NOT widen or drop a canonicity lookup to make this pass. The producer\n\
             (`Faithful9::from_key_lanes9` over `PUBKEY_NONET_LANE_COL`) is the single writer of\n\
             a nonet lane; if its output is out of range, fix it THERE.\n"
        )
    });

    // ── (b) OLD ADMITS: without the envelope the out-of-image nonet is accepted.
    proves_and_verifies(&without, &forged_trace, &forged_pis).unwrap_or_else(|e| {
        panic!(
            "\nthe forged trace is refused even WITHOUT the envelope ({e}), so leg (c) below would \
             be measuring something else — a stale commitment, the owner freeze, or a PI. \
             Re-derive whatever moved before reading (c) as a canonicity result.\n"
        )
    });
    eprintln!(
        "KEY-CANON9 OLD ADMITS: lane8 = {} (≥ 2^24, outside the image) PROVES + VERIFIES on the \
         pre-envelope shape of {} — and decodes to the honest key byte-for-byte.",
        forged_nonet[8].as_u32(),
        with.name
    );

    // ── (c) NEW REJECTS: the same bytes are UNSAT once the envelope is on.
    let verdict = proves_and_verifies(&with, &forged_trace, &forged_pis);
    assert!(
        verdict.is_err(),
        "\n⚑ THE OUT-OF-IMAGE NONET PROVED UNDER THE ENVELOPE. lane 8 = {} is ≥ 2^24, so the \
         committed columns are not any key's nine-lane encoding — while `key_from_lanes9` reads \
         them as {:02x?}. `keyCanon9Wire_rejects_the_forged_nonet` says this member has no \
         witness; it just found one.\n",
        forged_nonet[8].as_u32(),
        key_from_lanes9(&forged_nonet)
    );
    eprintln!("KEY-CANON9 NEW REJECTS: the enveloped member is UNSAT ({verdict:?}).");
}

/// ⚑ **THE NARROW LEG IS NOT A CONSEQUENCE OF THE WIDE ONE — at the prover.**
///
/// Replace lane 8's `< 2^24` lookup with a `< 2^29` one (the "range-check the nine lanes"
/// simplification that has not done the arithmetic) and the identical forged trace proves again.
/// So the refusal above is that ONE lookup, and widening it re-opens the encoding.
#[test]
fn the_narrow_leg_alone_is_what_refuses_the_forgery() {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    pk[31] = 0x5A;

    let (_, with) = the_two_poles(&deployed_cellseal());
    let w = face_width(&with.name);
    let (forged_trace, forged_pis) = rotated_cellseal_trace(pk, KTOP);

    let lane8_cols = [nonet_cols(w, 0)[8], nonet_cols(w, 1)[8]];
    let mut uniform = with.clone();
    let mut widened = 0usize;
    for c in uniform.constraints.iter_mut() {
        if let VmConstraint2::Lookup(l) = c {
            let hits_lane8 =
                matches!(l.tuple.as_slice(), [LeanExpr::Var(v)] if lane8_cols.contains(v));
            if l.table == range_tid(KEY_TOP_BITS) && hits_lane8 {
                l.table = range_tid(KEY_LANE_BITS);
                widened += 1;
            }
        }
    }
    assert_eq!(
        widened, 2,
        "expected exactly the two ninth-lane narrow lookups (one per block), widened {widened}"
    );

    proves_and_verifies(&uniform, &forged_trace, &forged_pis).unwrap_or_else(|e| {
        panic!(
            "\nwith lane 8 checked at 29 bits instead of 24 the forged trace is STILL refused \
             ({e}). Then the refusal in `old_admits_new_rejects_at_the_deployed_prover` is not the \
             narrow leg, and that exhibit does not show what it claims.\n"
        )
    });
    eprintln!(
        "KEY-CANON9 NARROW LEG: widening lane 8's lookup 24 → 29 makes the SAME forged trace \
         prove — the second leg is load-bearing, not decoration."
    );
}

// ════════════════════════════════════════════════════════════════════════════════════
// §4 — COMPLETENESS over the key corpus
// ════════════════════════════════════════════════════════════════════════════════════

/// A structured, deterministic corpus: the extremes, every single source bit alone (the only way a
/// lane-boundary error is guaranteed to be seen), an Ed25519 `A` / `−A` pair, the top-lane boundary
/// patterns, and 3840 pseudorandom keys from a fixed-seed xorshift so the run replays exactly.
fn key_corpus() -> Vec<[u8; 32]> {
    use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
    use curve25519_dalek::scalar::Scalar;

    let a = ED25519_BASEPOINT_POINT * Scalar::from(0x5eed_1234_9abc_def0u64);
    let mut corpus: Vec<[u8; 32]> = vec![
        [0x00; 32],
        [0xFF; 32],
        a.compress().to_bytes(),
        (-a).compress().to_bytes(),
    ];
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut x = [0u8; 32];
            x[byte] = 1u8 << bit;
            corpus.push(x);
        }
    }
    // …and the region this envelope is actually about: keys whose bits 232..255 (the TOP lane, and
    // the Ed25519 x-sign) are all-ones / one-below / alternating.
    for pat in [0xFFu8, 0xFE, 0xAA, 0x55, 0x80] {
        let mut x = [0u8; 32];
        for b in x.iter_mut().skip(29) {
            *b = pat;
        }
        corpus.push(x);
    }
    let mut s: u64 = 0x243F_6A88_85A3_08D3;
    let mut next = move || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    for _ in 0..3840 {
        let mut x = [0u8; 32];
        for chunk in x.chunks_mut(8) {
            chunk.copy_from_slice(&next().to_le_bytes());
        }
        corpus.push(x);
    }
    corpus
}

/// ⚑ **EVERY HONEST KEY IS INSIDE THE EMITTED ENVELOPE.** The gate refuses nothing a producer can
/// emit: over the whole corpus all nine lanes satisfy the two legs the AIR now enforces, the
/// decoder recovers the bytes exactly, and the encoding is injective on the corpus.
///
/// ⚠ Stated as INJECTIVITY, which is what a key needs. The count assertion is what keeps a
/// collapsed corpus from passing this silently.
#[test]
fn the_key_corpus_is_inside_the_emitted_envelope() {
    let corpus = key_corpus();
    assert!(corpus.len() >= 4000, "corpus is {}", corpus.len());
    let mut top_lanes = std::collections::HashSet::new();
    for x in &corpus {
        let lanes = dregg_circuit::effect_vm::key_limbs9(x);
        for (i, l) in lanes.iter().enumerate().take(8) {
            assert!(
                l.as_u32() < (1u32 << KEY_LANE_BITS),
                "lane {i} = {} fails the emitted `< 2^29` lookup on key {x:02x?}",
                l.as_u32()
            );
        }
        assert!(
            lanes[8].as_u32() < KTOP,
            "the TOP lane = {} fails the emitted `< 2^24` lookup on key {x:02x?} — an honest key \
             the envelope refuses is the failure mode this epoch must not have",
            lanes[8].as_u32()
        );
        top_lanes.insert(lanes[8].as_u32());
        assert_eq!(key_from_lanes9(&lanes), *x, "round-trip failed on {x:02x?}");
    }
    let distinct: std::collections::HashSet<[u32; 9]> = corpus
        .iter()
        .map(|x| {
            let l = dregg_circuit::effect_vm::key_limbs9(x);
            core::array::from_fn(|i| l[i].as_u32())
        })
        .collect();
    let inputs: std::collections::HashSet<[u8; 32]> = corpus.iter().copied().collect();
    assert_eq!(
        distinct.len(),
        inputs.len(),
        "two distinct keys shared a nonet — the encoder is not injective"
    );
    assert!(
        top_lanes.len() > 1000,
        "the corpus exercised only {} distinct TOP lanes — a corpus whose lane 8 is nearly \
         constant cannot see a ninth-lane defect",
        top_lanes.len()
    );
    eprintln!(
        "KEY-CANON9 COMPLETENESS: {} keys ({} distinct, {} distinct top lanes) all canonical, all \
         round-tripping.",
        corpus.len(),
        distinct.len(),
        top_lanes.len()
    );
}

/// The corpus leg above is about the ENCODER. This one is about the AIR: a structured subset of the
/// same corpus PROVES and VERIFIES with the envelope on, including the two Ed25519 points whose
/// separation the ninth lane exists for.
#[test]
fn structured_honest_keys_prove_and_verify_under_the_envelope() {
    use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;
    use curve25519_dalek::scalar::Scalar;

    let a = ED25519_BASEPOINT_POINT * Scalar::from(0x5eed_1234_9abc_def0u64);
    let keys: Vec<[u8; 32]> = vec![
        [0x00; 32],
        [0xFF; 32],
        a.compress().to_bytes(),
        (-a).compress().to_bytes(),
    ];
    let (_, with) = the_two_poles(&deployed_cellseal());
    let w = face_width(&with.name);
    let mut seen_top_lanes = std::collections::HashSet::new();
    for pk in keys {
        let (trace, dpis) = rotated_cellseal_trace(pk, 0);
        let lane8 = trace[0][nonet_cols(w, 0)[8]].as_u32();
        seen_top_lanes.insert(lane8);
        proves_and_verifies(&with, &trace, &dpis).unwrap_or_else(|e| {
            panic!(
                "\n⚑ the honest key {pk:02x?} (top lane {lane8}) is UNSAT under the envelope: {e}\n"
            )
        });
    }
    assert!(
        seen_top_lanes.len() >= 3,
        "the honest subset exercised only {} distinct top-lane values — a subset whose lane 8 is \
         always the same value cannot see a ninth-lane defect",
        seen_top_lanes.len()
    );
    eprintln!(
        "KEY-CANON9 PROVE-THROUGH: {} distinct top-lane values, all PROVING + VERIFYING under the \
         envelope.",
        seen_top_lanes.len()
    );
}

/// ⚑ **HOW MANY ALIASES THE ENVELOPE CLOSES, counted rather than gestured at.** Lane 8 is a
/// BabyBear felt, so it ranges over `[0, p)`; the honest window is `[0, 2^24)`. Every value
/// `r + q·2^24` decodes to the same 32 bytes as `r`, so each key had that many committed
/// representations and the AIR distinguished none of them.
#[test]
fn the_envelope_closes_a_counted_set_of_aliases() {
    let p = u64::from(BABYBEAR_P);
    let ktop = u64::from(KTOP);
    assert_eq!(120 * ktop, p - 1, "120·2^24 is exactly p − 1");
    // r = 0: q ∈ {0 … 120}. r ≥ 1: one fewer.
    let for_zero_top = (0u64..).take_while(|q| q * ktop < p).count();
    let for_other_top = (0u64..).take_while(|q| q * ktop + 1 < p).count();
    assert_eq!(for_zero_top, 121);
    assert_eq!(for_other_top, 120);

    // …and the aliasing is real at the DEPLOYED decoder, not merely arithmetic.
    let lanes = dregg_circuit::effect_vm::key_limbs9(&[0x11u8; 32]);
    let honest = key_from_lanes9(&lanes);
    for q in 1..=3u32 {
        let mut aliased = lanes;
        aliased[8] = BabyBear::new(lanes[8].as_u32() + q * KTOP);
        assert_eq!(
            key_from_lanes9(&aliased),
            honest,
            "alias q={q} must decode to the same key"
        );
        assert_ne!(
            aliased[8], lanes[8],
            "alias q={q} must be a DIFFERENT column"
        );
    }
    eprintln!(
        "KEY-CANON9 ALIASES: every owner key had 120 committed nonets (121 at top lane 0); the \
         envelope leaves exactly one."
    );
}
