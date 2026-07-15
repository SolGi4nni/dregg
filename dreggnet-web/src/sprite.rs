//! # `sprite` — the deterministic generative art surface for the web catalog.
//!
//! The catalog's items and assets rendered as **byte-identical vector SVG**, not text. A
//! [`dreggnet_asset::AssetId`] (a blake3 content address) is turned into a composed SVG sprite by
//! [`dreggnet_sprite`]'s pure, deterministic renderer (gear / card), so the SAME asset ⇒ the SAME
//! bytes — the art is itself re-derivable and verifiable, riding the house's byte-identical-replay
//! norm.
//!
//! Two things this module gives the web surface:
//! - **an art endpoint** — `GET /sprite/{kind}/{ref}` returns `image/svg+xml`: the deterministic
//!   sprite for an asset reference (`kind` ∈ `gear`/`card`; `ref` a 64-hex asset address, or any
//!   label — a non-address ref is hashed into a stable [`AssetId`], so a friendly name still yields
//!   a fixed sprite). This is what an `<img src>` / a `ViewNode::Tile` points at.
//! - **a Tile painter** — [`tile_html`] renders a deos [`ViewNode::Tile`] whose `handle` names an
//!   asset (`sprite:{kind}:{ref}` / `asset:{kind}:{ref}`, or a bare hex) as the inline SVG sprite in
//!   a framed cell, instead of the text placeholder the gpui-free renderers fall back to. The
//!   catalog walker ([`crate::catalog_node`]) calls this, so any offering that emits a
//!   sprite-handled `Tile` now shows real art.
//!
//! Plus a **gallery** ([`gallery_page`]) — a grid of deterministically-addressed gear + card
//! sprites, the growable proof that the art is wired end to end (each cell is a live SVG, and a
//! reload re-derives byte-identical sprites).
//!
//! ## Honest scope
//! REAL here: the deterministic `AssetId → SVG` art served over HTTP, the `Tile{handle}` → sprite
//! paint, and the gallery. NAMED, not built here: the `dreggnet-surfaces` inventory / trade / craft
//! surfaces still render their items as a text table because their `render` emits `Pill`/`Text`
//! rows that do NOT carry the note's `AssetId` into the view tree — painting THOSE items as sprites
//! needs the surface crate to emit a `Tile{handle}` carrying the asset address (a shared-crate
//! change, out of this crate's scope). This module renders the sprite for any Tile that DOES carry
//! an asset handle, so it is wired and forward-compatible.

use axum::{
    Router,
    extract::Path,
    http::header,
    response::{Html, IntoResponse},
    routing::get,
};

use dreggnet_asset::AssetId;
use dreggnet_sprite::{render, render_gear};

/// Re-exported so callers (and this crate's tests) name the sprite kind through the web surface
/// without a direct `dreggnet-sprite` dependency.
pub use dreggnet_sprite::AssetKind;

use crate::{document, esc};

/// Parse a sprite `kind` path/handle segment into an [`AssetKind`]. `gear` / `blade` / `weapon` →
/// [`AssetKind::Gear`]; `card` / `sigil` / `emblem` → [`AssetKind::Card`]; anything else → `None`.
pub fn parse_kind(s: &str) -> Option<AssetKind> {
    match s.trim().to_ascii_lowercase().as_str() {
        "gear" | "blade" | "weapon" => Some(AssetKind::Gear),
        "card" | "sigil" | "emblem" => Some(AssetKind::Card),
        _ => None,
    }
}

/// **Resolve an asset reference to a stable [`AssetId`].** A 64-hex string is decoded verbatim
/// (a real content address). Anything else (a friendly label, a short hex) is domain-separated and
/// hashed into a fixed 32-byte address — so a non-address ref still maps deterministically to ONE
/// asset (and thus ONE sprite), never failing. The whole map is a pure function of `reference`.
pub fn asset_ref(reference: &str) -> AssetId {
    let r = reference.trim();
    if r.len() == 64 {
        if let Some(bytes) = decode_hex32(r) {
            return AssetId(bytes);
        }
    }
    // Not a 32-byte address — derive a stable one from the label (domain-separated so it never
    // collides with a raw content address' derivation).
    AssetId(blake3::derive_key(
        "dreggnet-web sprite asset-ref v1",
        r.as_bytes(),
    ))
}

/// Decode exactly 64 lowercase/uppercase hex chars into 32 bytes; `None` on any non-hex or a
/// wrong length.
fn decode_hex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    let bytes = s.as_bytes();
    for i in 0..32 {
        let hi = hex_val(bytes[2 * i])?;
        let lo = hex_val(bytes[2 * i + 1])?;
        out[i] = (hi << 4) | lo;
    }
    Some(out)
}

fn hex_val(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

/// **Render the deterministic SVG for a `(kind, reference)`** — the pure art function the endpoint
/// and the gallery share. Byte-identical for the same inputs.
pub fn svg_for(kind: AssetKind, reference: &str) -> String {
    render(kind, &asset_ref(reference))
}

/// **Paint a deos [`ViewNode::Tile`] whose `handle` names an asset as the inline SVG sprite.**
/// Recognised handle shapes: `sprite:{kind}:{ref}`, `asset:{kind}:{ref}` (explicit kind), or a bare
/// asset ref (a 64-hex address / a label — defaulting to a card). Returns the framed-cell HTML, or
/// `None` if the handle names no asset (the caller then falls back to the text placeholder). `w`/`h`
/// bound the rendered box (the sprite scales to fit; the intrinsic SVG viewBox is preserved).
pub fn tile_html(handle: &str, w: u32, h: u32) -> Option<String> {
    let (kind, reference) = parse_handle(handle)?;
    let svg = svg_for(kind, reference);
    let w = w.clamp(32, 512);
    let h = h.clamp(32, 512);
    Some(format!(
        "<div class=\"sprite-tile\" style=\"width:{w}px;height:{h}px\" \
         title=\"{title}\">{svg}</div>",
        w = w,
        h = h,
        title = esc(handle),
        svg = svg,
    ))
}

/// Parse a `Tile` handle into `(kind, reference)`. `sprite:gear:<ref>` / `asset:card:<ref>` give an
/// explicit kind; a bare `<ref>` (no recognised scheme) defaults to a card sprite. `None` only for
/// an empty handle.
fn parse_handle(handle: &str) -> Option<(AssetKind, &str)> {
    let h = handle.trim();
    if h.is_empty() {
        return None;
    }
    // `sprite:{kind}:{ref}` or `asset:{kind}:{ref}`.
    for scheme in ["sprite:", "asset:"] {
        if let Some(rest) = h.strip_prefix(scheme) {
            if let Some((k, r)) = rest.split_once(':') {
                if let Some(kind) = parse_kind(k) {
                    if !r.is_empty() {
                        return Some((kind, r));
                    }
                }
            }
        }
    }
    // A bare reference — default to a card sprite (the emblem the catalog uses for a note).
    Some((AssetKind::Card, h))
}

/// **The sprite router** — stateless (the art is a pure function of the path):
/// - `GET /sprite/{kind}/{reference}` — the deterministic SVG (`image/svg+xml`);
/// - `GET /gallery` — the sprite gallery page.
///
/// Merged into the demo app beside the catalog + descent surfaces.
pub fn sprite_router() -> Router {
    Router::new()
        .route("/sprite/{kind}/{reference}", get(get_sprite))
        .route("/gallery", get(get_gallery))
}

/// `GET /sprite/{kind}/{reference}` — serve the asset's deterministic SVG sprite as
/// `image/svg+xml`. An unknown `kind` 404s; every `reference` resolves (a non-address is hashed).
async fn get_sprite(Path((kind, reference)): Path<(String, String)>) -> impl IntoResponse {
    match parse_kind(&kind) {
        Some(k) => {
            let svg = svg_for(k, &reference);
            (
                [(header::CONTENT_TYPE, "image/svg+xml; charset=utf-8")],
                svg,
            )
                .into_response()
        }
        None => (
            axum::http::StatusCode::NOT_FOUND,
            [(header::CONTENT_TYPE, "text/plain; charset=utf-8")],
            format!("unknown sprite kind {kind:?} (expected gear|card)"),
        )
            .into_response(),
    }
}

/// `GET /gallery` — the deterministic art gallery: a grid of gear + card sprites at fixed
/// addresses. Each cell is a live inline SVG; a reload re-derives byte-identical art.
async fn get_gallery() -> Html<String> {
    Html(gallery_page())
}

/// The fixed, deterministic gallery roster — friendly asset labels, rendered as gear or card. The
/// labels are stable, so the gallery is byte-reproducible.
const GALLERY_GEAR: &[&str] = &[
    "warden-blade",
    "hoard-key",
    "corridor-lantern",
    "gate-hammer",
    "keep-cleaver",
    "dregg-edge",
];
const GALLERY_CARDS: &[&str] = &[
    "council-sigil",
    "market-seal",
    "descent-emblem",
    "tug-charm",
    "automatafl-crest",
    "federation-mark",
];

/// **Render the sprite gallery page** — a grid of the deterministic gear + card sprites, each a live
/// SVG with its asset address shown (the short content-address the art is a pure function of).
pub fn gallery_page() -> String {
    let mut cells = String::new();
    for label in GALLERY_GEAR {
        cells.push_str(&gallery_cell(AssetKind::Gear, label));
    }
    for label in GALLERY_CARDS {
        cells.push_str(&gallery_cell(AssetKind::Card, label));
    }
    let body = format!(
        "<main class=\"catalog\"><div class=\"page-head\">\
         <p class=\"eyebrow\">Deterministic art</p>\
         <h1>Every sprite is a function of its address.</h1>\
         <p class=\"deck\">Every asset is a blake3 content address, and its sprite is a pure, \
         byte-identical function of that address (<code>dreggnet-sprite</code>). Same asset ⇒ same \
         art — reload and re-derive the identical SVG. The catalog paints an item's \
         <code>Tile</code> node with this same renderer.</p></div>\
         <div class=\"sprite-grid\">{cells}</div></main>",
    );
    document("DreggNet Cloud — sprite gallery", "gallery", &body)
}

/// One gallery cell — the sprite plus its kind + short asset address.
fn gallery_cell(kind: AssetKind, label: &str) -> String {
    let asset = asset_ref(label);
    let svg = render_kind(kind, &asset);
    let addr = short_addr(&asset);
    let kind_name = match kind {
        AssetKind::Gear => "gear",
        AssetKind::Card => "card",
    };
    format!(
        "<figure class=\"sprite-cell\"><div class=\"sprite-art\">{svg}</div>\
         <figcaption>{label} <span class=\"pill tag-accent\">{kind_name}</span><br>\
         <code>{addr}</code></figcaption></figure>",
        svg = svg,
        label = esc(label),
        kind_name = kind_name,
        addr = esc(&addr),
    )
}

/// Render an already-resolved [`AssetId`] as the given kind (gear uses [`render_gear`] to keep the
/// dependency surface small; the [`render`] dispatcher covers both).
fn render_kind(kind: AssetKind, asset: &AssetId) -> String {
    match kind {
        AssetKind::Gear => render_gear(asset),
        AssetKind::Card => render(AssetKind::Card, asset),
    }
}

/// A short hex of an asset address (first 6 bytes) for display.
fn short_addr(asset: &AssetId) -> String {
    let b = asset.bytes();
    let mut s = String::with_capacity(12);
    for byte in &b[..6] {
        s.push_str(&format!("{byte:02x}"));
    }
    s.push('…');
    s
}
