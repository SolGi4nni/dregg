//! The verified-allocator teeth: the Legal obligation bites NON-VACUOUSLY (a
//! conflicting / out-of-bounds layout FAILS to construct), and the allocator refuses an
//! over-capacity or malformed schema.

use dregg_schema::{
    Archetype, Assignment, CheckedLayout, Layout, LayoutError, LegalError, RegisterWidth,
    STATE_SLOTS, Schema, Slot, allocate, allocate_checked, descent_schema,
};

#[test]
fn descent_allocates_to_a_legal_disjoint_layout() {
    let schema = descent_schema();
    let layout = allocate(&schema).expect("descent allocates");
    // The allocator's output passes the Legal check (disjoint + in-bounds).
    layout.legal().expect("allocated layout is Legal");

    // Deterministic register order, collection spilled to the heap.
    let checked = CheckedLayout::new(layout).expect("checked");
    assert_eq!(checked.resolve("hp"), Some(Slot::Register(0)));
    assert_eq!(checked.resolve("floor"), Some(Slot::Register(1)));
    assert_eq!(checked.resolve("gold"), Some(Slot::Register(2)));
    assert_eq!(checked.resolve("owner"), Some(Slot::Register(3)));
    assert_eq!(checked.resolve("shield"), Some(Slot::Register(4)));
    assert_eq!(
        checked.resolve("items"),
        Some(Slot::Heap(STATE_SLOTS as u64))
    );
}

#[test]
fn conflicting_declaration_fails_to_construct() {
    // A hand-built layout where two components write the SAME register column — the
    // disjointness (Nodup) obligation must refuse it. This is the non-vacuity witness:
    // the Legal check is load-bearing, not always-true.
    let bad = Layout {
        assignments: vec![
            Assignment {
                component: "hp".into(),
                archetype: Archetype::Stat { min: 0, max: 20 },
                slot: Slot::Register(3),
            },
            Assignment {
                component: "gold".into(),
                archetype: Archetype::Resource,
                slot: Slot::Register(3), // <-- collides with hp
            },
        ],
        num_registers: RegisterWidth::CELL,
    };
    match CheckedLayout::new(bad) {
        Err(LegalError::Overlap { column, .. }) => assert_eq!(column, 3),
        other => panic!("expected Overlap, got {other:?}"),
    }
}

#[test]
fn out_of_bounds_register_fails_to_construct() {
    let bad = Layout {
        assignments: vec![Assignment {
            component: "hp".into(),
            archetype: Archetype::Stat { min: 0, max: 20 },
            slot: Slot::Register(STATE_SLOTS + 4), // beyond the register file
        }],
        num_registers: RegisterWidth::CELL,
    };
    // The slot is outside the CELL's register file, so the physical bound is the
    // diagnosis (checked first), not the declared-width one.
    assert!(matches!(
        CheckedLayout::new(bad),
        Err(LegalError::RegisterExceedsCell { .. })
    ));
}

#[test]
fn heap_key_aliasing_registers_fails_to_construct() {
    let bad = Layout {
        assignments: vec![Assignment {
            component: "items".into(),
            archetype: Archetype::Collection,
            slot: Slot::Heap(5), // < STATE_SLOTS: aliases the register file
        }],
        num_registers: RegisterWidth::CELL,
    };
    assert!(matches!(
        CheckedLayout::new(bad),
        Err(LegalError::HeapAliasesRegisters { .. })
    ));
}

#[test]
fn over_capacity_schema_fails_to_allocate() {
    // 17 register-bound stats: one more than the 16-slot register file. The
    // register-bound archetypes do NOT spill to the heap, so this is a real allocation
    // failure (not a silent overflow).
    let mut schema = Schema::new("too-big");
    for i in 0..(STATE_SLOTS as usize + 1) {
        schema = schema.stat(format!("s{i}"), 0, 100);
    }
    match allocate(&schema) {
        Err(LayoutError::OutOfRegisters { needed, available }) => {
            assert_eq!(needed, STATE_SLOTS as usize + 1);
            assert_eq!(available, STATE_SLOTS);
        }
        other => panic!("expected OutOfRegisters, got {other:?}"),
    }
}

#[test]
fn many_collections_spill_to_the_heap() {
    // Collections are heap-placed, so a schema with many of them allocates fine (they
    // do not consume the register file).
    let mut schema = Schema::new("hoarder").stat("hp", 0, 20);
    for i in 0..40 {
        schema = schema.collection(format!("bag{i}"));
    }
    let layout = allocate(&schema).expect("collections spill to heap");
    layout.legal().expect("legal");
    let checked = CheckedLayout::new(layout).unwrap();
    assert_eq!(checked.resolve("hp"), Some(Slot::Register(0)));
    assert_eq!(
        checked.resolve("bag0"),
        Some(Slot::Heap(STATE_SLOTS as u64))
    );
    assert_eq!(
        checked.resolve("bag39"),
        Some(Slot::Heap(STATE_SLOTS as u64 + 39))
    );
}

#[test]
fn malformed_invariant_reference_fails_to_allocate() {
    // References an undeclared field.
    let schema = Schema::new("bad-inv")
        .stat("hp", 0, 20)
        .invariant("shield", "nope", 0);
    assert!(matches!(
        allocate(&schema),
        Err(LayoutError::UnknownInvariantTarget { .. })
    ));

    // References a heap (collection) field — FieldLteOther indexes registers only.
    let schema2 = Schema::new("bad-inv2")
        .collection("bag")
        .invariant("shield", "bag", 0);
    assert!(matches!(
        allocate(&schema2),
        Err(LayoutError::InvariantTargetNotRegister { .. })
    ));
}

#[test]
fn duplicate_component_fails_to_allocate() {
    let schema = Schema::new("dup").stat("hp", 0, 20).resource("hp");
    assert!(matches!(
        allocate(&schema),
        Err(LayoutError::DuplicateComponent { .. })
    ));
}

/// **The wound, and the wall.** `Layout::num_registers` was a bare `u8` and `legal()`
/// checked register slots against *that field only*, never against `STATE_SLOTS`. So this
/// EXACT code compiled, passed the Legal gate, and produced a `CheckedLayout` — in a cell
/// that has 16 registers:
///
/// ```text
/// let over_wide = Layout {
///     assignments: vec![Assignment {
///         component: "hp".into(),
///         archetype: Archetype::Stat { min: 0, max: 20 },
///         slot: Slot::Register(17),
///     }],
///     num_registers: 18,
/// };
/// assert!(CheckedLayout::new(over_wide).is_ok()); // <-- IT WAS Ok
/// ```
///
/// It can no longer be WRITTEN: `num_registers` is a [`RegisterWidth`], so the literal
/// `18` is a type error (`expected RegisterWidth, found integer`) and there is no
/// constructor that reaches 18. This is the runtime twin of that compile error — the
/// widening the wall refuses, and the narrowings it still allows.
#[test]
fn an_over_wide_register_width_is_unconstructable() {
    // The wound's own number: 18 registers in a 16-register cell.
    assert_eq!(RegisterWidth::narrowed(18), None);
    // Every width past the cell's, refused — including the off-by-one.
    assert_eq!(RegisterWidth::narrowed(STATE_SLOTS + 1), None);
    assert_eq!(RegisterWidth::narrowed(u8::MAX), None);

    // NARROWING is safe (a strictly stricter bound), so it is allowed: the good pole.
    let full = RegisterWidth::narrowed(STATE_SLOTS).expect("the cell's own width narrows");
    assert_eq!(full.get(), STATE_SLOTS);
    assert_eq!(full, RegisterWidth::CELL);
    let four = RegisterWidth::narrowed(4).expect("4 <= STATE_SLOTS");
    assert_eq!(four.get(), 4);
    assert_eq!(RegisterWidth::narrowed(0).map(RegisterWidth::get), Some(0));

    // And the width the allocator actually declares is the cell's, not a wider guess.
    let checked = allocate_checked(&descent_schema()).expect("descent allocates + checks");
    assert_eq!(checked.num_registers(), RegisterWidth::CELL);
    assert_eq!(checked.num_registers().get(), STATE_SLOTS);
}

#[test]
fn a_register_slot_outside_the_cell_is_refused_at_the_full_declared_width() {
    // The wound's slot (17) at a width the type accepts (the cell's real 16). The type
    // wall cannot see this one — the SLOT is over-wide, not the width — so `legal()` must,
    // and it names both bounds.
    let bad = Layout {
        assignments: vec![Assignment {
            component: "hp".into(),
            archetype: Archetype::Stat { min: 0, max: 20 },
            slot: Slot::Register(17),
        }],
        num_registers: RegisterWidth::CELL,
    };
    match bad.legal() {
        Err(LegalError::RegisterExceedsCell {
            component,
            slot,
            declared_width,
            cell_width,
        }) => {
            assert_eq!(component, "hp");
            assert_eq!(slot, 17);
            assert_eq!(declared_width, STATE_SLOTS);
            assert_eq!(cell_width, STATE_SLOTS);
        }
        other => panic!("expected RegisterExceedsCell, got {other:?}"),
    }
    // The message names the cell's width, so a reader is not left guessing the bound.
    let rendered = bad.legal().unwrap_err().to_string();
    assert!(
        rendered.contains(&format!("STATE_SLOTS = {STATE_SLOTS}")),
        "message must name STATE_SLOTS: {rendered}"
    );
    // The good pole: the last register the cell actually has is in bounds.
    let ok = Layout {
        assignments: vec![Assignment {
            component: "hp".into(),
            archetype: Archetype::Stat { min: 0, max: 20 },
            slot: Slot::Register(STATE_SLOTS - 1),
        }],
        num_registers: RegisterWidth::CELL,
    };
    ok.legal().expect("the cell's last register is legal");
    assert!(CheckedLayout::new(ok).is_ok());
}

#[test]
fn a_narrowed_width_refuses_a_slot_the_cell_has_but_the_layout_did_not_declare() {
    let narrow = RegisterWidth::narrowed(4).expect("4 <= STATE_SLOTS");
    // Slot 7 IS a register the cell has (7 < 16) but this layout declared only 4 — the
    // declared-width bound is the tighter one, and it is the diagnosis.
    let bad = Layout {
        assignments: vec![Assignment {
            component: "hp".into(),
            archetype: Archetype::Stat { min: 0, max: 20 },
            slot: Slot::Register(7),
        }],
        num_registers: narrow,
    };
    match CheckedLayout::new(bad) {
        Err(LegalError::RegisterOutOfBounds {
            slot,
            declared_width,
            cell_width,
            ..
        }) => {
            assert_eq!(slot, 7);
            // BOTH widths are named, and here they differ — that is the whole point.
            assert_eq!(declared_width, 4);
            assert_eq!(cell_width, STATE_SLOTS);
            assert_ne!(declared_width, cell_width);
        }
        other => panic!("expected RegisterOutOfBounds, got {other:?}"),
    }
    // The good pole: a slot inside the narrowed width passes.
    let ok = Layout {
        assignments: vec![Assignment {
            component: "hp".into(),
            archetype: Archetype::Stat { min: 0, max: 20 },
            slot: Slot::Register(3),
        }],
        num_registers: narrow,
    };
    assert!(CheckedLayout::new(ok).is_ok());
}

#[test]
fn a_narrowed_width_does_not_open_the_heap_below_the_cell_register_file() {
    // The heap bound is the CELL's register width, not the declared one. Heap key 5 is
    // `>= 4` (the declared width) yet still aliases register 5 in the real cell — before
    // `legal()` checked STATE_SLOTS independently, this layout was Legal.
    let narrow = RegisterWidth::narrowed(4).expect("4 <= STATE_SLOTS");
    let bad = Layout {
        assignments: vec![Assignment {
            component: "items".into(),
            archetype: Archetype::Collection,
            slot: Slot::Heap(5),
        }],
        num_registers: narrow,
    };
    match CheckedLayout::new(bad) {
        Err(LegalError::HeapAliasesRegisters {
            key,
            declared_width,
            cell_width,
            ..
        }) => {
            assert_eq!(key, 5);
            assert_eq!(declared_width, 4);
            assert_eq!(cell_width, STATE_SLOTS);
        }
        other => panic!("expected HeapAliasesRegisters, got {other:?}"),
    }
    // The good pole: the first key past the cell's register file is a legal heap key.
    let ok = Layout {
        assignments: vec![Assignment {
            component: "items".into(),
            archetype: Archetype::Collection,
            slot: Slot::Heap(STATE_SLOTS as u64),
        }],
        num_registers: narrow,
    };
    assert!(CheckedLayout::new(ok).is_ok());
}

#[test]
fn allocate_checked_on_the_real_schema_still_resolves_every_component() {
    // The honest pole for the whole wall: the one-step trusted path still succeeds on a
    // real schema and resolves the same slots as before.
    let checked = allocate_checked(&descent_schema()).expect("descent allocates + checks");
    assert_eq!(checked.resolve("hp"), Some(Slot::Register(0)));
    assert_eq!(checked.resolve("floor"), Some(Slot::Register(1)));
    assert_eq!(checked.resolve("gold"), Some(Slot::Register(2)));
    assert_eq!(checked.resolve("owner"), Some(Slot::Register(3)));
    assert_eq!(checked.resolve("shield"), Some(Slot::Register(4)));
    assert_eq!(
        checked.resolve("items"),
        Some(Slot::Heap(STATE_SLOTS as u64))
    );
    assert_eq!(checked.resolve("nope"), None);
    assert_eq!(checked.assignments().len(), 6);
}
