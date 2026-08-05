//! # RANK 3 — the per-effect COHORT descriptors migrated to umem-form `UMemOp` reconciliations.
//!
//! The rotation-flip plan (greenlit) makes the universal-memory prover the load-bearing
//! per-effect representation. Rank 1 landed the address/value CODEC ADAPTERS
//! (`metatheory/Dregg2/Crypto/UMemCodec.lean`, `f2ea3184` — `uaddrEnc = hash[domainTag d,
//! coll, key]`, the cap-leaf value codec); Rank 2 landed the EXECUTOR BRIDGE
//! (`turn/src/umem.rs`, `547dc5ee` — `record_kernel_boundary_agrees`, the projection ⟺
//! per-map-table-root anchor). THIS is Rank 3: each deployed cohort effect's state TOUCH is
//! emitted as a `UMemOp` read/write against the universal boundary table — the per-cell
//! `(domain, key) → value` cells the Rank-1 codecs address — instead of a per-map `MapOp`
//! reconciliation against a Merkle root.
//!
//! ## What this builds (IN ISOLATION — no registry / VK / deployed-prover change)
//!
//! For each faithful-class cohort effect (`set-field` · `set-heap` · `grant` · `attenuate`,
//! plus the scalar `transfer` balance touch), a real cell BEFORE → AFTER the effect is
//! projected into the ONE universal map (Rank-2's `project_record_kernel_state`), the state
//! TOUCHES are read off as the pre→post projection diff, and each touch becomes a `UMemOp`
//! row against the universal boundary table (the Rank-1 structured address codecs:
//! `heap_addr` for the heap/field planes, `slot_hash` for the caps plane). The umem-form
//! descriptor PROVES in isolation through the production `prove_vm_descriptor2_umem` and the
//! independent verifier accepts.
//!
//! ## The differential — AGREEMENT with the per-map form (riding Rank 2)
//!
//! "the umem-form's state-effect agrees with its per-map form" is anchored by Rank-2's
//! `record_kernel_boundary_agrees`: the per-domain boundary roots DERIVED from the
//! projection reproduce — value-for-value — the deployed per-map-table roots the cell
//! commits (`fields_root` · `heap_root` · `cap_root`). Asserting it holds at BOTH endpoints
//! (pre and post) ties the umem-form touch to the per-map form: the boundary's init image
//! folds to the committed PRE roots, the touch installs the post values, and the post image
//! folds to the committed POST roots. The umem reconciliation moves exactly what the per-map
//! `MapOp` reconciliation moves.
//!
//! ## The `absent` map-op → umem `none`-read (the nullifier-freshness win)
//!
//! A `MapKind::Absent` non-membership read (the bracketed-gap freshness leg) becomes ONE
//! umem `UMemOp::Read` returning `none` (present = 0) against a boundary cell that is absent
//! — Merkle-path-free, gap-opening-free (`UniversalMemory.nullifier_fresh_sound`). Covered
//! below by `nullifier_absent_none_read_*`.
//!
//! ## VK-RISK-FREE
//!
//! This is a pure ADDITIVE test exercising the deployed umem machinery
//! (`prove_vm_descriptor2_umem`); it touches no descriptor JSON, no registry entry, no VK,
//! and never arms `umem_witness_enabled`. The flag-day is Rank 4 (the owner's explicit go).

use std::collections::BTreeMap;

use dregg_cell::{AuthRequired, Cell, Permissions};
use dregg_circuit::cap_root::{fold_bytes32, slot_hash};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, MemKind, NULLIFIER_DOMAIN, UMemBoundaryWitness,
    UMemOpSpec, VmConstraint2, prove_vm_descriptor2_umem, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::heap_addr;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_turn::umem::{
    UKey, UProjection, UVal, project_record_kernel_state, record_kernel_boundary_agrees,
};

// ============================================================================
// The Rank-1-codec-shaped lowering: a structured `(domain, in-domain key)` and a value felt.
//
// The umem `(domain, key)` address is the literal PAIR — the domain is its own bus
// coordinate (`UMemOpSpec.domain`), so the in-domain key carries `hash[collection, key]`
// (the deployed `heap_addr` / `slot_hash` codecs; the cap leaf's `slot_hash` sort key). The
// multiset balance is label-invariant, so an injective structured encoding realizes exactly
// the memory-consistency statement; a collision would make the boundary fail its
// strict-increasing requirement (an in-build injectivity check).
// ============================================================================

/// Field-plane collection tag (the user-field map lives under one logical collection).
const FIELD_COLL: u32 = 0xF1E1;
/// Balance scalar tag (the economic register made a umem cell).
const BALANCE_COLL: u32 = 0xBA1A;
/// Nonce scalar tag.
const NONCE_COLL: u32 = 0x0CE0;

/// Fold a low `u64` into a key felt limb (the in-domain `key` argument of `heap_addr`).
fn key_limb(x: u64) -> BabyBear {
    BabyBear::new((x % (dregg_circuit::field::BABYBEAR_P as u64)) as u32)
}

/// The structured `(domain code, in-domain key felt)` of a projected address — Rank-1's
/// `uaddrEnc` shape with the domain split out as its own column.
fn ukey_addr(k: &UKey) -> (u32, BabyBear) {
    let domain = k.domain().code();
    let key = match k {
        UKey::Heap {
            collection, key, ..
        } => heap_addr(BabyBear::new(*collection), BabyBear::new(*key)),
        UKey::Field { slot, .. } => heap_addr(BabyBear::new(FIELD_COLL), key_limb(*slot)),
        UKey::Balance(_) => heap_addr(BabyBear::new(BALANCE_COLL), BabyBear::ZERO),
        UKey::Nonce(_) => heap_addr(BabyBear::new(NONCE_COLL), BabyBear::ZERO),
        UKey::CapSlot { slot, .. } => slot_hash(*slot),
        UKey::NoteNullifier(b) | UKey::BridgedNullifier(b) => fold_bytes32(b),
        // Any other projected address: a deterministic injective felt over its canonical
        // serialization (the planes above are the ones the cohort effects touch).
        other => fold_bytes(&serde_json::to_vec(other).expect("ukey serializes")),
    };
    (domain, key)
}

/// Horner fold of arbitrary canonical bytes into a value felt (the Rank-1 value-codec shape:
/// a field image of the value; `Bytes32` rides the deployed `fold_bytes32`).
fn fold_bytes(bytes: &[u8]) -> BabyBear {
    let mut acc = BabyBear::ONE; // nonzero seed so the empty value is distinct from absence
    let mul = BabyBear::new(0x1000_0193); // FNV-ish field multiplier
    for &b in bytes {
        acc = acc * mul + BabyBear::new(b as u32 + 1);
    }
    acc
}

/// The `(present, value)` felt pair of an optional cell — `none ↦ (0, 0)`, the canonical
/// absent encoding the umem grammar pins.
fn uval_felt(v: Option<&UVal>) -> (BabyBear, BabyBear) {
    match v {
        None => (BabyBear::ZERO, BabyBear::ZERO),
        Some(UVal::Bytes32(b)) | Some(UVal::UmemRef(b)) => (BabyBear::ONE, fold_bytes32(b)),
        Some(other) => (
            BabyBear::ONE,
            fold_bytes(&serde_json::to_vec(other).expect("uval serializes")),
        ),
    }
}

/// One state TOUCH: an address with its pre / post cell values (the pre→post projection diff).
struct Touch {
    key: UKey,
    prev: Option<UVal>,
    new: Option<UVal>,
}

/// The pre→post projection DIFF — every address whose value changed (insert / update /
/// delete). This is the effect's state touch set as the universal map sees it.
fn project_diff(pre: &UProjection, post: &UProjection) -> Vec<Touch> {
    let mut touches = Vec::new();
    let mut keys: Vec<&UKey> = pre.keys().chain(post.keys()).collect();
    keys.sort();
    keys.dedup();
    for k in keys {
        let a = pre.get(k);
        let b = post.get(k);
        if a != b {
            touches.push(Touch {
                key: k.clone(),
                prev: a.cloned(),
                new: b.cloned(),
            });
        }
    }
    touches
}

/// Build the umem-FORM descriptor + main rows + boundary for a set of touches: one
/// `UMemOp::Write` constraint per touched domain (guarded by its indicator column), one main
/// row per touch, and the boundary = the touched addresses with their PRE cell as the init
/// image. The exact shape `prove_vm_descriptor2_umem` consumes.
fn build_umem_form(
    name: &str,
    touches: &[Touch],
) -> (EffectVmDescriptor2, Vec<Vec<BabyBear>>, UMemBoundaryWitness) {
    // base cols: 0 key · 1 present · 2 value · 3 prev_present · 4 prev_value · 5 prev_serial.
    let mut domains: Vec<u32> = touches.iter().map(|t| t.key.domain().code()).collect();
    domains.sort();
    domains.dedup();
    let guard_col: BTreeMap<u32, usize> = domains
        .iter()
        .enumerate()
        .map(|(i, d)| (*d, 6 + i))
        .collect();
    let width = 6 + domains.len();

    let constraints: Vec<VmConstraint2> = domains
        .iter()
        .map(|d| {
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(guard_col[d]),
                domain: *d,
                key: LeanExpr::Var(0),
                present: LeanExpr::Var(1),
                value: LeanExpr::Var(2),
                prev_present: LeanExpr::Var(3),
                prev_value: LeanExpr::Var(4),
                prev_serial: LeanExpr::Var(5),
                kind: MemKind::Write,
            })
        })
        .collect();

    let desc = EffectVmDescriptor2 {
        name: name.to_string(),
        trace_width: width,
        public_input_count: 0,
        challenges: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    };

    // one main row per touch; prev cell = the PRE value (init boundary, serial 0).
    let mut rows: Vec<Vec<BabyBear>> = Vec::new();
    for t in touches {
        let (d, key) = ukey_addr(&t.key);
        let (present, value) = uval_felt(t.new.as_ref());
        let (prev_present, prev_value) = uval_felt(t.prev.as_ref());
        let mut row = vec![BabyBear::ZERO; width];
        row[0] = key;
        row[1] = present;
        row[2] = value;
        row[3] = prev_present;
        row[4] = prev_value;
        row[5] = BabyBear::ZERO; // each touched address opened once against init
        row[guard_col[&d]] = BabyBear::ONE;
        rows.push(row);
    }
    let height = rows.len().next_power_of_two().max(4);
    while rows.len() < height {
        rows.push(vec![BabyBear::ZERO; width]);
    }

    // boundary: touched addresses (strict-increasing by (domain, key)), pre values.
    let mut addrs: Vec<(u32, BabyBear, Option<BabyBear>)> = touches
        .iter()
        .map(|t| {
            let (d, k) = ukey_addr(&t.key);
            let (present, value) = uval_felt(t.prev.as_ref());
            let init = if present == BabyBear::ONE {
                Some(value)
            } else {
                None
            };
            (d, k, init)
        })
        .collect();
    addrs.sort_by_key(|(d, k, _)| (*d, k.as_u32()));
    let boundary = UMemBoundaryWitness {
        addrs: addrs.iter().map(|(d, k, _)| (*d, *k)).collect(),
        init_vals: addrs.iter().map(|(_, _, v)| *v).collect(),
    };

    (desc, rows, boundary)
}

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

fn make_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// THE COHORT DIFFERENTIAL: project a cell BEFORE → AFTER an effect, assert the per-map
/// agreement at BOTH endpoints (Rank-2 anchor — the umem-form's per-map form), build the
/// umem-form descriptor over the touch, prove + verify in isolation, and exercise the
/// forged-pre-state tooth. `expect_min_touches` lower-bounds the projection diff so a
/// no-op effect can't pass vacuously.
fn cohort_case(name: &str, pre: &Cell, post: &Cell, expect_min_touches: usize) {
    // The per-map agreement anchor (Rank 2): the projection reproduces the deployed
    // per-map-table roots, at both endpoints — the umem-form's per-map form.
    record_kernel_boundary_agrees(pre)
        .unwrap_or_else(|e| panic!("{name}: PRE projection must agree with per-map roots: {e}"));
    record_kernel_boundary_agrees(post)
        .unwrap_or_else(|e| panic!("{name}: POST projection must agree with per-map roots: {e}"));

    let proj_pre = project_record_kernel_state(pre);
    let proj_post = project_record_kernel_state(post);
    let touches = project_diff(&proj_pre, &proj_post);
    assert!(
        touches.len() >= expect_min_touches,
        "{name}: expected at least {expect_min_touches} touch(es), got {}",
        touches.len()
    );

    let (desc, rows, boundary) = build_umem_form(name, &touches);
    let proof = prove_vm_descriptor2_umem(
        &desc,
        &rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &boundary,
    )
    .unwrap_or_else(|e| panic!("{name}: umem-form descriptor must prove in isolation: {e}"));
    verify_vm_descriptor2(&desc, &proof, &[])
        .unwrap_or_else(|e| panic!("{name}: umem-form descriptor must independently verify: {e}"));

    // TOOTH (boundary_init_root_bound): forge the pinned INIT image — the committed
    // pre-state preimage the umem form binds against. Each op claims its prev cell against
    // serial 0 (the boundary); a tampered init declares a different value there than the op
    // claims, so the offline-memory multiset is inconsistent and refuses. (Only the init is
    // pinned — the final image is replayed from the ops — so this, not the installed value,
    // is the load-bearing anti-forge tooth.)
    let mut forged = boundary.clone();
    forged.init_vals[0] = match forged.init_vals[0] {
        Some(v) => Some(v + BabyBear::ONE), // an UPDATE touch: a different committed pre-value
        None => Some(BabyBear::ONE),        // an INSERT touch: claim a phantom pre-existing cell
    };
    let r = prove_vm_descriptor2_umem(
        &desc,
        &rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &forged,
    );
    assert!(
        r.is_err(),
        "{name}: a forged committed pre-state (init image) must refuse"
    );
}

// ============================================================================
// The cohort.
// ============================================================================

#[test]
fn cohort_set_field_umem_form() {
    // SET-FIELD on the committed user-field MAP (slot >= STATE_SLOTS) → one `Field`-plane
    // touch; the per-map form is the `fields_root` map-write.
    let pre = make_cell(11, 1000);
    let mut post = pre.clone();
    let mut v = [0u8; 32];
    v[..4].copy_from_slice(&424242u32.to_le_bytes());
    assert!(post.state.set_field_ext(20, v), "field-map write");
    cohort_case("set-field-umem", &pre, &post, 1);
}

#[test]
fn cohort_set_heap_umem_form() {
    // SET-HEAP on the committed `(collection, key) → value` heap → one `Heap`-plane touch;
    // the per-map form is the `heap_root` map-write.
    let pre = make_cell(12, 1000);
    let mut post = pre.clone();
    let mut v = [0u8; 32];
    v[..4].copy_from_slice(&555u32.to_le_bytes());
    assert!(post.state.set_heap(7, 3, v), "heap write");
    cohort_case("set-heap-umem", &pre, &post, 1);
}

#[test]
fn cohort_grant_umem_form() {
    // GRANT a capability → one `CapSlot`-plane INSERT (prev absent → present); the per-map
    // form is the `cap_root` sorted-insert.
    let pre = make_cell(13, 1000);
    let target = make_cell(14, 10).id();
    let mut post = pre.clone();
    post.capabilities
        .grant(target, AuthRequired::Either)
        .expect("grant");
    cohort_case("grant-umem", &pre, &post, 1);
}

#[test]
fn cohort_attenuate_umem_form() {
    // ATTENUATE an existing capability in place → one `CapSlot`-plane UPDATE (rights
    // narrowed); the per-map form is the `cap_root` value-update (no tombstone).
    let mut pre = make_cell(15, 1000);
    let target = make_cell(16, 10).id();
    let slot = pre
        .capabilities
        .grant(target, AuthRequired::Either)
        .expect("grant");
    let mut post = pre.clone();
    post.capabilities
        .attenuate_in_place(slot, AuthRequired::Signature, None, None)
        .expect("attenuate narrows");
    cohort_case("attenuate-umem", &pre, &post, 1);
}

#[test]
fn cohort_transfer_balance_umem_form() {
    // TRANSFER's economic touch is the scalar `Balance` register (NOT a per-map plane); its
    // umem form is a Heap-domain scalar write. The per-map roots (fields/heap/cap) are
    // UNCHANGED, so the Rank-2 agreement holds as the unchanged-plane invariant and the
    // balance touch proves in isolation all the same.
    let pre = make_cell(17, 1000);
    let mut post = pre.clone();
    post.state.set_balance(993); // debit 7
    cohort_case("transfer-balance-umem", &pre, &post, 1);
}

// ============================================================================
// The `absent` map-op → umem `none`-read (the nullifier-freshness win).
// ============================================================================

/// Build the single-row nullifier freshness descriptor: one `UMemOp::Read` of a
/// nullifier-domain address, claiming the cell (present, value). Width 7 (6 base + 1 guard).
fn nullifier_read_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "nullifier-fresh-umem".to_string(),
        trace_width: 7,
        public_input_count: 0,
        challenges: 0,
        tables: vec![],
        constraints: vec![VmConstraint2::UMemOp(UMemOpSpec {
            guard: LeanExpr::Var(6),
            domain: NULLIFIER_DOMAIN,
            key: LeanExpr::Var(0),
            present: LeanExpr::Var(1),
            value: LeanExpr::Var(2),
            prev_present: LeanExpr::Var(3),
            prev_value: LeanExpr::Var(4),
            prev_serial: LeanExpr::Var(5),
            kind: MemKind::Read,
        })],
        hash_sites: vec![],
        ranges: vec![],
    }
}

fn nullifier_key() -> BabyBear {
    fold_bytes32(&[0x9Au8; 32])
}

#[test]
fn nullifier_absent_none_read_proves_freshness() {
    // The `absent` non-membership read as ONE umem `none`-read: the boundary cell is absent,
    // the read returns (present 0, value 0) — Merkle-path-free freshness
    // (`UniversalMemory.nullifier_fresh_sound`).
    let desc = nullifier_read_desc();
    let mut row = vec![BabyBear::ZERO; 7];
    row[0] = nullifier_key();
    // present/value/prev all zero = a none-read; guard on.
    row[6] = BabyBear::ONE;
    let mut rows = vec![row];
    while rows.len() < 4 {
        rows.push(vec![BabyBear::ZERO; 7]);
    }
    let boundary = UMemBoundaryWitness {
        addrs: vec![(NULLIFIER_DOMAIN, nullifier_key())],
        init_vals: vec![None], // the nullifier is ABSENT (fresh)
    };
    let proof = prove_vm_descriptor2_umem(
        &desc,
        &rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &boundary,
    )
    .expect("an absent-cell none-read proves freshness");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("the freshness none-read verifies");
}

#[test]
fn nullifier_absent_none_read_claimed_spent_refuses() {
    // TOOTH: the same read claims the nullifier is PRESENT (already-spent) against the absent
    // boundary cell — the multiset balance cannot cancel, so it refuses. (A genuine
    // double-spend is exactly this lie.)
    let desc = nullifier_read_desc();
    let mut row = vec![BabyBear::ZERO; 7];
    row[0] = nullifier_key();
    row[1] = BabyBear::ONE; // present (claims spent)
    row[2] = BabyBear::ONE; // value
    row[3] = BabyBear::ONE; // prev present (read returns its claim)
    row[4] = BabyBear::ONE; // prev value
    row[6] = BabyBear::ONE;
    let mut rows = vec![row];
    while rows.len() < 4 {
        rows.push(vec![BabyBear::ZERO; 7]);
    }
    let boundary = UMemBoundaryWitness {
        addrs: vec![(NULLIFIER_DOMAIN, nullifier_key())],
        init_vals: vec![None], // absent — the read's present claim contradicts it
    };
    let r = prove_vm_descriptor2_umem(
        &desc,
        &rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &boundary,
    );
    assert!(
        r.is_err(),
        "a none-read claiming the absent cell is present must refuse"
    );
}
