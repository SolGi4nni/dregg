//! **The NT/Pharo chrome kit** — the reusable widget infrastructure of the deos
//! desktop, factored out so every surface (windows, menus, dialogs, the property
//! sheet) draws from ONE palette and ONE set of bevel/face primitives.
//!
//! This is the "reusable components" layer: the NT 3D-bevel look, the property-row
//! and section helpers, and the small render/format utilities are all here, so a
//! new window-type or dialog composes them rather than re-deriving the chrome.

use gpui::{FontWeight, IntoElement, ParentElement, Pixels, Styled, div, px};

use dregg_types::CellId;

// ── The NT palette ──────────────────────────────────────────────────────────────
// Deliberately sterile / technical: a 3D-beveled gray chrome over a teal void, the
// way an NT workstation reads. Dense, not calm; detailed, not minimal.
pub const NT_DESKTOP_BG: u32 = 0x0a3a4a; // the classic teal void
pub const NT_FACE: u32 = 0xc0c0c0; // button-face gray
pub const NT_FACE_DARK: u32 = 0x9a9a9a;
pub const NT_HILIGHT: u32 = 0xffffff; // top-left bevel
pub const NT_SHADOW: u32 = 0x404040; // bottom-right bevel
pub const NT_TEXT: u32 = 0x101010;
pub const NT_TITLE_ACTIVE: u32 = 0x000080; // navy active title bar
pub const NT_TITLE_TEXT: u32 = 0xffffff;
pub const NT_ICON_LABEL: u32 = 0xf0f0f0;
pub const NT_SELECT: u32 = 0x000080;
pub const NT_MENU_HILIGHT: u32 = 0x000080;
pub const NT_DIM: u32 = 0x707070; // a disabled / unheld affordance

// ── Geometry constants ────────────────────────────────────────────────────────────
pub const ICON_W: f32 = 92.0;
pub const ICON_H: f32 = 76.0;
pub const WIN_MIN_W: f32 = 280.0;
pub const WIN_MIN_H: f32 = 180.0;
pub const MENUBAR_H: f32 = 26.0;

/// The state slot a document-editor edit bumps via a real `SetField` turn — so
/// each edit advances the cell's chronicle (height + receipt) in the same breath
/// it commits the patch. Picked high (slot 14) to stay clear of the demo cells'
/// balance/model slots.
pub const DOC_REV_SLOT: usize = 14;

// ── Document prose in the committed cell heap ───────────────────────────────────────
// A document's prose is stored as field elements in the cell's `fields_map` (the
// unbounded `BTreeMap<u64, FieldElement>` committed via `fields_root`), addressed by
// **ext keys >= STATE_SLOTS(16)** so a `SetField` turn writes them through
// `set_field_ext` (`cell/src/state.rs`) — the prose is on-ledger, receipted, and
// replays from the committed state, not a sidecar.
//
// Namespace (per cell — one document per cell): a base far above the 16 fixed slots
// and far below the reserved refusal-audit ext key (`2^32`). `DOC_TEXT_BASE + 0`
// holds the byte LENGTH (LE u64 in the low 8 bytes); `DOC_TEXT_BASE + 1 + i` holds
// chunk `i` (up to [`DOC_CHUNK_BYTES`] raw UTF-8 bytes, stored verbatim — the
// `fields_map` keeps the 32 bytes byte-exact and `fields_root` binds all 32 via
// `fold_bytes32`).
pub const DOC_TEXT_BASE: u64 = 1_000_000;
/// Bytes of prose packed into one `FieldElement` (the full 32-byte value is stored
/// verbatim and committed, so all 32 carry payload).
pub const DOC_CHUNK_BYTES: usize = 32;
/// A sane ceiling on document chunks written/scanned per edit (keeps a malformed or
/// runaway document from unbounded heap writes; ~32 KiB of prose).
pub const DOC_MAX_CHUNKS: u64 = 1024;

// ── Id rendering ──────────────────────────────────────────────────────────────────

/// The full hex id of a cell (a stable layout/persistence key, and the inspector's
/// identity row). [`CellId`] carries the raw bytes; this is the canonical render.
pub fn id_hex(cell: &CellId) -> String {
    cell.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

/// A short legible id (first 4 bytes) — the icon caption / window-title id.
pub fn id_short(cell: &CellId) -> String {
    cell.as_bytes()[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// `Pixels` → `f32` (the field is private; the `From` impl is the supported route).
pub fn pxf(p: Pixels) -> f32 {
    f32::from(p)
}

// ── The bevel/face primitives (reusable NT widgets) ───────────────────────────────

/// An NT 3D bevel (raised) — a light face with a 2px top-left highlight border (the
/// raised-button look). Generic over any [`Styled`] element so it composes onto a
/// plain `div()` or an `.id()`'d `Stateful<Div>`.
pub fn bevel_raised<E: Styled>(d: E) -> E {
    d.border_t_2()
        .border_l_2()
        .border_color(gpui::rgb(NT_HILIGHT))
        .bg(gpui::rgb(NT_FACE))
}

/// A bold navy section heading inside a window/dialog body (the dense field-group
/// divider).
pub fn face_section(title: &str) -> impl IntoElement {
    div()
        .mt_1()
        .text_size(px(10.0))
        .font_weight(FontWeight::BOLD)
        .text_color(gpui::rgb(0x000080))
        .child(format!("── {title} "))
}

/// A `key: value` property row (the dense inspector/property line).
pub fn face_row(key: &str, value: &str) -> impl IntoElement {
    div()
        .flex()
        .flex_row()
        .text_size(px(11.0))
        .child(
            div()
                .w(px(96.0))
                .text_color(gpui::rgb(0x505050))
                .child(format!("{key}:")),
        )
        .child(div().flex_1().child(value.to_string()))
}

// ── Numeric formatting (NT-dense numerics) ────────────────────────────────────────

/// Format a signed balance with a unicode minus and thousands grouping.
pub fn fmt_balance(b: i64) -> String {
    if b < 0 {
        format!("−{}", group(-b as u64))
    } else {
        group(b as u64)
    }
}

/// Group an integer with thousands separators.
pub fn group(n: u64) -> String {
    let s = n.to_string();
    let mut out = String::new();
    let bytes = s.as_bytes();
    let len = bytes.len();
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 && (len - i) % 3 == 0 {
            out.push(',');
        }
        out.push(*b as char);
    }
    out
}
