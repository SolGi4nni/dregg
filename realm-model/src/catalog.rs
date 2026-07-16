//! §9.2 — the RULESET CATALOG: local configuration becomes shared law.
//!
//! > Today VK registration is HOST CONFIG (per-executor CustomEffectRegistry).
//! > The catalog makes a realm's ACTIVE ruleset roots COMMITTED LAW — the
//! > ruleset_root is IN the turn/receipt, not inferred from server build.
//!
//! `cell/src/custom_effect.rs` registers a verifier in ONE executor instance;
//! two hosts can be configured with different accepted sets (the doc's §9.2
//! warning). This catalog moves the admitted-roots set into COMMITTED CELL STATE
//! owned by the realm: which `ruleset_root` a turn may cite is read from the
//! realm's catalog cell, not from whatever the serving binary happened to
//! register. A turn citing an unlisted root is REFUSED; a listed one admitted.
//!
//! ## Cell-backed, non-vacuous
//!
//! Membership lives in the catalog cell's extended field map: each admitted root
//! `R` is stored under a key derived from `R`, with the STORED VALUE being `R`
//! itself. Admission of a cited root `C` checks `get(key(C)) == Some(C)` — this
//! confirms both that `C` is listed AND that the listing is genuinely `C` (not a
//! key collision). Unlisting writes zero, so `get(key(C)) != C` → refused. That
//! is the canary the driven test exercises.

use crate::RulesetRoot;
use dregg_cell::CellId;
use dregg_cell::state::FieldElement;

/// The extended-field key a ruleset root is listed under. High bit forces the
/// key `>= STATE_SLOTS` so it lands in the committed `fields_map` (not one of the
/// 16 fixed slots the realm/instance bookkeeping uses).
pub(crate) fn catalog_key(root: &RulesetRoot) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&root[..8]);
    0x8000_0000_0000_0000u64 | u64::from_le_bytes(b)
}

/// The value stored for a listed root: the full root bytes (so admission is a
/// full-32-byte equality, not an 8-byte-key coincidence). Unlisting writes the
/// zero field element, which no real root equals.
pub(crate) fn listed_value(root: &RulesetRoot) -> FieldElement {
    *root
}

/// The committed active-ruleset-root set of a realm. First-class: a realm's law
/// is an OBJECT with cell-backed state, not a property of the running binary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RulesetCatalog {
    /// The catalog cell handle (a sibling of the realm cell).
    pub cell: CellId,
    /// The realm this catalog governs.
    pub realm: CellId,
}
