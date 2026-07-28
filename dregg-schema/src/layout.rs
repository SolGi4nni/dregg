//! # The verified allocator (translation-validation style).
//!
//! An UNTRUSTED allocator ([`allocate`]) assigns each component a [`Slot`]; a CHECKED
//! obligation ([`Layout::legal`], surfaced through [`CheckedLayout::new`]) verifies the
//! output before anything downstream may read it. This mirrors the LANDED
//! `metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean` discipline:
//!
//! * `RotatedLayout` there ≈ [`Layout`] here — the layout as data.
//! * `RotatedLayout.occupied` ≈ [`Layout::occupied`] — every column an instance uses.
//! * `structure Legal { disjoint : occupied.Nodup; inBounds : ∀ c ∈ occupied, c < n }`
//!   ≈ [`Layout::legal`]'s Nodup + in-bounds check.
//! * `theorem rotated178_legal : Legal rotated178 := by native_decide` (an ill-aligned
//!   layout is UNCONSTRUCTABLE) ≈ [`CheckedLayout`]: the only way to obtain one is to
//!   pass the Legal check, so an overlapping / out-of-bounds layout is a CONSTRUCTION
//!   ERROR, not a runtime panic.
//!
//! The Rust check is the imported PATTERN; the deeper Lean-PROVEN `Legal` obligation
//! over this allocator is the named follow-up (docs/GAME-STRATEGY.md Phase 2).

use crate::schema::{Archetype, Placement, Schema};

/// The number of fixed register slots a cell carries. Register keys are `0..STATE_SLOTS`;
/// heap keys are `>= STATE_SLOTS`. This IS `dregg_cell::state::STATE_SLOTS` (re-exported
/// by spween-dregg, which no longer keeps a literal of its own), narrowed to the `u8` a
/// slot index is carried in.
pub const STATE_SLOTS: u8 = spween_dregg::STATE_SLOTS as u8;

/// The `usize -> u8` narrowing directly above must never TRUNCATE. A cell register file
/// wider than 255 would wrap to a tiny width and hand every bounds check below a bound
/// that is not the cell's — the same class of silent-width wound [`RegisterWidth`] exists
/// to close. Compile error, not a runtime surprise.
const _: () = assert!(
    spween_dregg::STATE_SLOTS <= u8::MAX as usize,
    "STATE_SLOTS does not fit in a u8: dregg-schema's `as u8` narrowing would truncate"
);

/// **The register-width TYPE WALL** — a layout's declared register-space width, which
/// cannot exceed the cell's real register file.
///
/// The wound this closes, measured 2026-07-27: [`Layout::num_registers`] was a bare `u8`
/// and [`Layout::legal`] validated register slots against *that field*, never against
/// [`STATE_SLOTS`]. So a hand-built layout that DECLARED 18 registers and placed a
/// component at `Slot::Register(17)` sailed through the Legal gate and became a
/// [`CheckedLayout`] — the value the rest of the crate treats as "checked" — even though a
/// cell has 16 registers. The *value* check existed and the *type* permitted the bad
/// value.
///
/// This is `dregg_circuit::faithful8::Faithful8`'s discipline applied to a width: the
/// inner `u8` is private, and the only safe constructors produce a width `<= STATE_SLOTS`.
///
/// **NARROWING is safe; WIDENING is the wound.** A layout may declare FEWER registers than
/// the cell has — that is a strictly stricter in-bounds check, and [`Layout::legal`] still
/// checks the real cell bound independently — but it may never declare more. There is
/// deliberately NO `from_over_wide_DANGER` escape hatch: nothing in the tree needs one,
/// and a wall with an unused escape hatch is a convention.
///
/// The tripwire — the exact layout that used to pass, now refused by the compiler:
///
/// ```compile_fail
/// use dregg_schema::{Archetype, Assignment, Layout, Slot};
/// let over_wide = Layout {
///     assignments: vec![Assignment {
///         component: "hp".into(),
///         archetype: Archetype::Stat { min: 0, max: 20 },
///         slot: Slot::Register(17),
///     }],
///     num_registers: 18, // `expected RegisterWidth, found integer` — the wall
/// };
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegisterWidth(u8);

impl RegisterWidth {
    /// The cell's REAL register width ([`STATE_SLOTS`]) — what every [`allocate`] output
    /// declares.
    pub const CELL: Self = Self(STATE_SLOTS);

    /// The checked NARROWING constructor: `Some(w)` iff `n <= STATE_SLOTS`, `None`
    /// otherwise. The only way to name a width other than [`CELL`](Self::CELL), and it
    /// cannot name an over-wide one.
    pub const fn narrowed(n: u8) -> Option<Self> {
        if n <= STATE_SLOTS {
            Some(Self(n))
        } else {
            None
        }
    }

    /// The width as a number. Reading out is unrestricted — the wall polices
    /// construction, not inspection.
    pub const fn get(self) -> u8 {
        self.0
    }
}

/// Where a component's field is placed in the cell — a fixed register or a heap key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    /// Register slot `index` (`< STATE_SLOTS`).
    Register(u8),
    /// Heap key `key` (`>= STATE_SLOTS`) in the cell's `fields_map`.
    Heap(u64),
}

impl Slot {
    /// The single occupied "column" this slot uses — the domain element for the
    /// disjointness obligation. Register `r` occupies column `r` (`0..STATE_SLOTS`);
    /// heap key `k` occupies column `k` (`>= STATE_SLOTS`). The two spaces cannot alias
    /// (registers `< STATE_SLOTS <=` heap keys), so a single `u64` column space is a
    /// faithful disjointness domain.
    pub fn column(&self) -> u64 {
        match self {
            Slot::Register(r) => *r as u64,
            Slot::Heap(k) => *k,
        }
    }
}

/// One component's placement: its name, archetype, and assigned slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assignment {
    pub component: String,
    pub archetype: Archetype,
    pub slot: Slot,
}

/// A raw (untrusted) layout — the allocator's output, before the Legal check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub assignments: Vec<Assignment>,
    /// The register-space width this layout DECLARES. A [`RegisterWidth`], never a bare
    /// `u8`: an over-wide declaration (`18` registers in a 16-register cell) is a compile
    /// error, not a value [`legal`](Layout::legal) has to catch. A register slot is
    /// in-bounds iff `< num_registers` AND `< STATE_SLOTS`; a heap key iff
    /// `>= STATE_SLOTS`.
    pub num_registers: RegisterWidth,
}

/// Why a [`Layout`] is not [`Legal`](Layout::legal) — the disjointness / in-bounds
/// violations `CheckedLayout::new` refuses to construct past.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LegalError {
    /// Two components write the same column — the `disjoint : occupied.Nodup`
    /// obligation. THE invariant that was a comment in the 14-file emit.
    Overlap { column: u64, a: String, b: String },
    /// A register slot is `>= STATE_SLOTS` — it is not a register THE CELL HAS, whatever
    /// width this layout declared. The bound checked FIRST, because it is the physical
    /// fact; [`RegisterWidth`] makes the declared width `<= STATE_SLOTS`, so this fires
    /// exactly when the slot index itself is out of the cell.
    RegisterExceedsCell {
        component: String,
        slot: u8,
        declared_width: u8,
        cell_width: u8,
    },
    /// A register slot is inside the cell's register file but `>= num_registers` — out of
    /// the (possibly narrower) width this layout declared.
    RegisterOutOfBounds {
        component: String,
        slot: u8,
        declared_width: u8,
        cell_width: u8,
    },
    /// A "heap" key is `< STATE_SLOTS` (or `< num_registers`) — it aliases the register
    /// file. A heap key must be `>= STATE_SLOTS`, the cell's real register width, not
    /// merely `>=` whatever this layout declared.
    HeapAliasesRegisters {
        component: String,
        key: u64,
        declared_width: u8,
        cell_width: u8,
    },
}

impl core::fmt::Display for LegalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LegalError::Overlap { column, a, b } => write!(
                f,
                "layout is not disjoint: `{a}` and `{b}` both write column {column}"
            ),
            LegalError::RegisterExceedsCell {
                component,
                slot,
                declared_width,
                cell_width,
            } => write!(
                f,
                "`{component}` register slot {slot} is not a register this cell has \
                 (STATE_SLOTS = {cell_width}; this layout declared {declared_width})"
            ),
            LegalError::RegisterOutOfBounds {
                component,
                slot,
                declared_width,
                cell_width,
            } => write!(
                f,
                "`{component}` register slot {slot} is out of bounds \
                 (declared num_registers = {declared_width}, cell STATE_SLOTS = {cell_width})"
            ),
            LegalError::HeapAliasesRegisters {
                component,
                key,
                declared_width,
                cell_width,
            } => write!(
                f,
                "`{component}` heap key {key} aliases the register file \
                 (must be >= STATE_SLOTS = {cell_width}; this layout declared {declared_width})"
            ),
        }
    }
}

impl std::error::Error for LegalError {}

impl Layout {
    /// Every column this layout occupies — the domain of the disjointness obligation
    /// (`RotatedLayout.occupied`).
    pub fn occupied(&self) -> Vec<u64> {
        self.assignments.iter().map(|a| a.slot.column()).collect()
    }

    /// **THE LEGALITY OBLIGATION** — decidable, mirroring `RotatedLayout`'s
    /// `Legal { disjoint, inBounds }`:
    ///
    /// * `disjoint` — `occupied` has no duplicate column (Nodup);
    /// * `inBounds` — every register slot is `< STATE_SLOTS` **and** `< num_registers`;
    ///   every heap key is `>= STATE_SLOTS` (and `>= num_registers`).
    ///
    /// **Both bounds, independently — belt and braces.** [`RegisterWidth`] already pins
    /// the declared width `<= STATE_SLOTS`, so checking the declared width alone would be
    /// sufficient *today*; checking the cell's real width too is what keeps this honest if
    /// a future field-width change ever breaches the type wall. The wall stops the bad
    /// value; the check stops the bad *bound*. (Before both existed, a layout declaring
    /// 18 registers legalized `Slot::Register(17)` in a 16-register cell.)
    ///
    /// [`CheckedLayout::new`] runs this; an illegal layout cannot become a
    /// `CheckedLayout`, so nothing downstream ever reads an ill-aligned layout.
    pub fn legal(&self) -> Result<(), LegalError> {
        // disjoint : occupied.Nodup
        for i in 0..self.assignments.len() {
            for j in (i + 1)..self.assignments.len() {
                let ci = self.assignments[i].slot.column();
                let cj = self.assignments[j].slot.column();
                if ci == cj {
                    return Err(LegalError::Overlap {
                        column: ci,
                        a: self.assignments[i].component.clone(),
                        b: self.assignments[j].component.clone(),
                    });
                }
            }
        }
        // inBounds, against TWO bounds checked independently:
        //   (1) STATE_SLOTS — the cell's REAL register width, the physical fact;
        //   (2) self.num_registers — the width this layout declared, which `RegisterWidth`
        //       pins `<= STATE_SLOTS`, so it is the tighter of the two.
        let declared = self.num_registers.get();
        for a in &self.assignments {
            match a.slot {
                Slot::Register(r) => {
                    if r >= STATE_SLOTS {
                        return Err(LegalError::RegisterExceedsCell {
                            component: a.component.clone(),
                            slot: r,
                            declared_width: declared,
                            cell_width: STATE_SLOTS,
                        });
                    }
                    if r >= declared {
                        return Err(LegalError::RegisterOutOfBounds {
                            component: a.component.clone(),
                            slot: r,
                            declared_width: declared,
                            cell_width: STATE_SLOTS,
                        });
                    }
                }
                Slot::Heap(k) => {
                    if k < STATE_SLOTS as u64 || k < declared as u64 {
                        return Err(LegalError::HeapAliasesRegisters {
                            component: a.component.clone(),
                            key: k,
                            declared_width: declared,
                            cell_width: STATE_SLOTS,
                        });
                    }
                }
            }
        }
        Ok(())
    }
}

/// A layout that has PASSED the Legal check — the ONLY kind [`crate::emit`] and
/// [`crate::game`] read from. Constructing one is the sole gate; an illegal layout is a
/// construction error, exactly as an ill-aligned `RotatedLayout` is unconstructable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedLayout {
    layout: Layout,
}

impl CheckedLayout {
    /// The one gate: verify [`Layout::legal`], then wrap. Fails (never panics) on an
    /// overlapping / out-of-bounds layout.
    pub fn new(layout: Layout) -> Result<Self, LegalError> {
        layout.legal()?;
        Ok(CheckedLayout { layout })
    }

    /// The checked assignments.
    pub fn assignments(&self) -> &[Assignment] {
        &self.layout.assignments
    }

    /// The declared register-space width. The one honest accessor: it hands back the
    /// [`RegisterWidth`], so a caller that wants the number says `.num_registers().get()`
    /// and never re-widens it on the way out.
    pub fn num_registers(&self) -> RegisterWidth {
        self.layout.num_registers
    }

    /// Resolve a component name to its slot.
    pub fn resolve(&self, component: &str) -> Option<Slot> {
        self.layout
            .assignments
            .iter()
            .find(|a| a.component == component)
            .map(|a| a.slot)
    }
}

/// Why the allocator could not produce a layout at all (before the Legal check).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayoutError {
    /// More register-placed components than the register file holds — a real
    /// allocation failure (the register-bound archetypes do not spill to the heap).
    OutOfRegisters { needed: usize, available: u8 },
    /// An `Invariant` names an `other` component that is not declared.
    UnknownInvariantTarget { component: String, other: String },
    /// An `Invariant` names an `other` component that is not register-placed
    /// (`FieldLteOther` indexes registers, so the referenced field must be a register).
    InvariantTargetNotRegister { component: String, other: String },
    /// Two components share a name — resolution would be ambiguous.
    DuplicateComponent { name: String },
}

impl core::fmt::Display for LayoutError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LayoutError::OutOfRegisters { needed, available } => write!(
                f,
                "schema needs {needed} register slots but the cell has {available}"
            ),
            LayoutError::UnknownInvariantTarget { component, other } => write!(
                f,
                "invariant `{component}` references undeclared field `{other}`"
            ),
            LayoutError::InvariantTargetNotRegister { component, other } => write!(
                f,
                "invariant `{component}` references non-register field `{other}` (FieldLteOther indexes registers)"
            ),
            LayoutError::DuplicateComponent { name } => {
                write!(f, "component `{name}` is declared more than once")
            }
        }
    }
}

impl std::error::Error for LayoutError {}

/// **The (untrusted) allocator.** Assign register slots `0, 1, 2, …` in declaration
/// order to register-placed components and heap keys `STATE_SLOTS, …` to collections.
/// Fails on register exhaustion or a malformed invariant reference. The OUTPUT is then
/// handed to [`CheckedLayout::new`] (translation validation: untrusted search, checked
/// output).
pub fn allocate(schema: &Schema) -> Result<Layout, LayoutError> {
    // No duplicate names (resolution must be unambiguous).
    for (i, c) in schema.components.iter().enumerate() {
        if schema.components[..i].iter().any(|d| d.name == c.name) {
            return Err(LayoutError::DuplicateComponent {
                name: c.name.clone(),
            });
        }
    }

    // Total register demand (register-placed archetypes do not spill to the heap).
    let register_total = schema
        .components
        .iter()
        .filter(|c| c.archetype.placement() == Placement::Register)
        .count();
    if register_total > STATE_SLOTS as usize {
        return Err(LayoutError::OutOfRegisters {
            needed: register_total,
            available: STATE_SLOTS,
        });
    }

    let mut assignments = Vec::with_capacity(schema.components.len());
    let mut next_reg: u8 = 0;
    let mut next_heap: u64 = STATE_SLOTS as u64;

    for c in &schema.components {
        let slot = match c.archetype.placement() {
            Placement::Register => {
                let s = Slot::Register(next_reg);
                next_reg += 1;
                s
            }
            Placement::Heap => {
                let s = Slot::Heap(next_heap);
                next_heap += 1;
                s
            }
        };
        assignments.push(Assignment {
            component: c.name.clone(),
            archetype: c.archetype.clone(),
            slot,
        });
    }

    // Validate invariant references now that every placement is known.
    for a in &assignments {
        if let Archetype::Invariant { other, .. } = &a.archetype {
            match assignments.iter().find(|b| &b.component == other) {
                None => {
                    return Err(LayoutError::UnknownInvariantTarget {
                        component: a.component.clone(),
                        other: other.clone(),
                    });
                }
                Some(b) if !matches!(b.slot, Slot::Register(_)) => {
                    return Err(LayoutError::InvariantTargetNotRegister {
                        component: a.component.clone(),
                        other: other.clone(),
                    });
                }
                Some(_) => {}
            }
        }
    }

    Ok(Layout {
        assignments,
        num_registers: RegisterWidth::CELL,
    })
}

/// Allocate + Legal-check in one step: the trusted path from a [`Schema`] to a
/// [`CheckedLayout`].
pub fn allocate_checked(schema: &Schema) -> Result<CheckedLayout, LayoutError> {
    let layout = allocate(schema)?;
    // The allocator produces disjoint, in-bounds layouts by construction; the Legal
    // check re-validates its output (translation validation). A Legal failure here is
    // an allocator bug, surfaced as a construction error rather than trusted away.
    CheckedLayout::new(layout).map_err(|e| {
        // Fold a Legal failure into an allocation failure for the one-step path.
        match e {
            LegalError::Overlap { a, .. } => LayoutError::DuplicateComponent { name: a },
            LegalError::RegisterExceedsCell { .. } | LegalError::RegisterOutOfBounds { .. } => {
                LayoutError::OutOfRegisters {
                    needed: schema.components.len(),
                    available: STATE_SLOTS,
                }
            }
            LegalError::HeapAliasesRegisters { component, .. } => {
                LayoutError::DuplicateComponent { name: component }
            }
        }
    })
}
