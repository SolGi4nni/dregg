//! THE LIVE IMAGE VIEWER — a Smalltalk/Pharo-style object browser of REAL deos
//! cells, painted into the framebuffer. This is NOT a slideshow: the left rail
//! lists the ACTUAL cells in the image (`image_data::IMAGE`, a frozen snapshot of
//! real `dregg_cell::Cell`s — real ids, balances, c-lists, fields, proofs), and
//! the main pane inspects the FOCUSED cell. ENTER drills INTO the focused cell's
//! four substances (VALUE / STATE / AUTHORITY / EVIDENCE); ESC backs out.
//!
//! The soul (houyhnhnm computing + AOL-1999 wonder, FUSED): the environment IS
//! its own live inspector. A newcomer clicks around with delight; an adept reads
//! real cell internals. The "about deos" cell is the welcome, woven in as the
//! first inspectable object — not a separate tutorial.
//!
//! The polish (palette, cards, chips, substance tiles) is inherited from the
//! deos-tutorial PD's screens; here it serves ONE live cell among many you
//! navigate.

use crate::fb::{rgb, Canvas, HEIGHT, WIDTH};
use crate::image_data::{ImageCell, BALANCE_SUM, IMAGE, N_CELLS};

// ───────────────────────────── the deos palette ─────────────────────────────
const INK_TOP: (u8, u8, u8) = (6, 16, 26);
const INK_BOT: (u8, u8, u8) = (3, 8, 16);
const CARD_HI: (u8, u8, u8) = (18, 34, 46);
const CARD_LO: (u8, u8, u8) = (9, 17, 26);
const RAIL_BG: (u8, u8, u8) = (8, 18, 28);
const RAIL_SEL: (u8, u8, u8) = (16, 40, 50);
const TEAL: u32 = rgb(64, 224, 208);
const TEAL_DIM: u32 = rgb(40, 130, 130);
const CYAN: u32 = rgb(120, 230, 240);
const WHITE: u32 = rgb(232, 246, 248);
const GREY: u32 = rgb(150, 178, 188);
const DIM: u32 = rgb(96, 124, 136);
const AMBER: u32 = rgb(255, 196, 92);
const GREEN: u32 = rgb(96, 230, 140);
const RED: u32 = rgb(232, 96, 96);
const MAGENTA: u32 = rgb(212, 130, 230);
const GOLD: u32 = rgb(240, 214, 120);

// Layout geometry.
const RAIL_W: u32 = 232;
const TOP_H: u32 = 40;
const BAR_H: u32 = 36;

/// Which substance we are drilled into (the inner carousel). `None` = the cell
/// overview (the list view's main pane); `Some(0..3)` = a full-pane substance.
pub type Substance = Option<usize>;

pub const N_SUBSTANCES: usize = 4;
const SUBSTANCE_NAME: [&str; N_SUBSTANCES] = ["VALUE", "STATE", "AUTHORITY", "EVIDENCE"];
const SUBSTANCE_ACCENT: [u32; N_SUBSTANCES] = [AMBER, CYAN, TEAL, GREEN];
const SUBSTANCE_GLYPH: [&str; N_SUBSTANCES] = ["the ledger", "16 fields + nonce", "the c-list", "vk + proof"];

/// The viewer's full state: which cell is focused, and whether we are drilled
/// into one of its substances.
#[derive(Clone, Copy)]
pub struct ViewState {
    /// Index into [`IMAGE`] of the focused cell.
    pub focus: usize,
    /// `None` = browsing the rail (overview pane); `Some(i)` = inspecting
    /// substance `i` of the focused cell full-pane.
    pub drill: Substance,
}

impl ViewState {
    pub const fn new() -> Self {
        ViewState { focus: 0, drill: None }
    }

    pub fn n_cells(&self) -> usize {
        N_CELLS
    }
}

/// Paint the whole frame for the current state.
pub fn draw(c: &mut Canvas, st: &ViewState) {
    c.vgradient(INK_TOP, INK_BOT);
    starfield(c, st.focus);
    top_chrome(c, st);
    let cell = &IMAGE[st.focus];
    match st.drill {
        None => {
            rail(c, st);
            overview_pane(c, cell);
        }
        Some(i) => {
            // In a drill-in the rail collapses to a slim spine; the substance
            // gets the full main pane.
            rail(c, st);
            substance_pane(c, cell, i);
        }
    }
    bottom_bar(c, st, cell);
}

// A faint deterministic starfield — depth without noise, seeded by focus so
// each cell's backdrop feels subtly distinct but calm.
fn starfield(c: &mut Canvas, seed: usize) {
    let mut s: u32 = 0x9E37_79B9 ^ (seed as u32).wrapping_mul(0x85EB_CA77).wrapping_add(1);
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        s
    };
    for _ in 0..70 {
        let x = next() % WIDTH;
        let y = TOP_H + next() % (HEIGHT - TOP_H - BAR_H);
        let b = 16 + (next() % 22) as u8;
        c.put(x, y, rgb(b / 2, b, b));
    }
}

// ───────────────────────────── top chrome ───────────────────────────────────
fn top_chrome(c: &mut Canvas, st: &ViewState) {
    c.rect(0, 0, WIDTH, TOP_H, rgb(7, 16, 24));
    c.rect(0, 0, WIDTH, 2, TEAL_DIM);
    c.text("deos", 24, 12, 2, 1, TEAL);
    c.text("image", 24 + 92, 14, 1, 1, DIM);
    c.text("live cell browser", 24 + 92 + 56, 14, 1, 1, rgb(70, 100, 110));

    // a breadcrumb on the right: which cell, and (if drilled) which substance.
    let cell = &IMAGE[st.focus];
    let mut buf = [0u8; 8];
    let counter = fmt_two(&mut buf, st.focus as u32 + 1, N_CELLS as u32);
    let mut x = WIDTH - 24;
    // draw right-to-left-ish: compute width and place
    let crumb = cell.key;
    let cw = Canvas::text_w(crumb, 1, 1);
    let nw = Canvas::text_w(counter, 1, 1);
    x = x - cw;
    c.text(crumb, x, 14, 1, 1, CYAN);
    x = x - 12 - nw;
    c.text(counter, x, 14, 1, 1, DIM);
    if let Some(i) = st.drill {
        let sname = SUBSTANCE_NAME[i];
        let sw = Canvas::text_w(sname, 1, 1);
        x = x - 14 - sw;
        c.text(sname, x, 14, 1, 1, SUBSTANCE_ACCENT[i]);
        let sep = "drill";
        let pw = Canvas::text_w(sep, 1, 1);
        x = x - 10 - pw;
        c.text(sep, x, 14, 1, 1, rgb(70, 100, 110));
    }
}

// ───────────────────────────── the cell rail ────────────────────────────────
// The left rail: one row per REAL cell in the image. The focused row is
// highlighted with an accent spine. This is the "image" — the actual objects.
fn rail(c: &mut Canvas, st: &ViewState) {
    let y0 = TOP_H;
    let h = HEIGHT - TOP_H - BAR_H;
    c.rect(0, y0, RAIL_W, h, rgb(RAIL_BG.0, RAIL_BG.1, RAIL_BG.2));
    c.rect(RAIL_W, y0, 2, h, rgb(20, 44, 52));

    c.text("THE IMAGE", 18, y0 + 12, 1, 1, TEAL);
    let mut nbuf = [0u8; 16];
    let label = fmt_n_cells(&mut nbuf, N_CELLS as u32);
    c.text(label, 18, y0 + 28, 1, 0, DIM);

    let row_h = 60u32;
    let list_y = y0 + 48;
    for (i, cell) in IMAGE.iter().enumerate() {
        let ry = list_y + i as u32 * row_h;
        if ry + row_h > y0 + h {
            break;
        }
        let focused = i == st.focus;
        if focused {
            c.vgradient_rect(0, ry, RAIL_W, row_h - 6, RAIL_SEL, RAIL_BG);
            c.rect(0, ry, 4, row_h - 6, accent_for(cell)); // accent spine
            c.rect(RAIL_W - 2, ry, 2, row_h - 6, accent_for(cell));
        }
        // the index marker
        let mut ib = [0u8; 4];
        let idx = fmt_u32(&mut ib, i as u32 + 1);
        c.text(idx, 16, ry + 8, 1, 0, if focused { TEAL } else { DIM });

        // the title + a lifecycle dot
        let tcol = if focused { WHITE } else { GREY };
        c.text(cell.title, 34, ry + 8, 1, 0, tcol);
        // lifecycle chip color
        let lc = life_color(cell.life_tag);
        c.rect(RAIL_W - 22, ry + 9, 8, 8, lc);

        // a compact one-line stat: balance or "content"
        let stat_col = if focused { CYAN } else { DIM };
        let mut sb = [0u8; 24];
        let stat = rail_stat(&mut sb, cell);
        c.text(stat, 34, ry + 26, 1, 0, stat_col);

        // a thin divider under each row
        c.rect(12, ry + row_h - 8, RAIL_W - 24, 1, rgb(18, 36, 44));
    }
}

fn rail_stat<'a>(buf: &'a mut [u8; 24], cell: &ImageCell) -> &'a str {
    // "1000 cv" for value cells, or the field count for content cells.
    if cell.balance != 0 || cell.is_well {
        let mut w = Writer::new(buf);
        if cell.is_well {
            w.str("well ");
        }
        w.i64(cell.balance);
        w.str(" cv");
        w.finish()
    } else {
        let mut w = Writer::new(buf);
        w.u32(cell.fields_used);
        w.str(" fields");
        w.finish()
    }
}

// ───────────────────────── the overview (focused cell) ──────────────────────
// The main pane for the list view: the focused cell's identity + a 2x2 grid of
// its four substances (compact), with a "press ENTER to inspect" hint. This is
// the deos-tutorial "a cell" screen, now LIVE — it is one cell among many.
fn overview_pane(c: &mut Canvas, cell: &ImageCell) {
    let px = RAIL_W + 28;
    let pw = WIDTH - px - 24;
    let py = TOP_H + 18;

    // header: title + mode + lifecycle chips
    c.text(cell.title, px, py, 3, 1, WHITE);
    let mut hx = px;
    let hy = py + 42;
    hx = chip(c, hx, hy, cell.mode, MAGENTA, rgb(24, 14, 28)) + 8;
    let _ = chip(c, hx, hy, cell.life_tag, life_color(cell.life_tag), rgb(10, 24, 18));

    c.text(cell.blurb, px, hy + 26, 1, 1, GREY);

    // identity block
    let idy = hy + 52;
    c.text("id", px, idy, 1, 1, DIM);
    c.text(cell.id_hex, px + 40, idy, 1, 1, CYAN);
    c.text("blake3(pk || token)", px + 40 + Canvas::text_w(cell.id_hex, 1, 1) + 16, idy, 1, 0, rgb(70, 100, 110));
    c.text("pk", px, idy + 18, 1, 1, DIM);
    c.text(cell.pk_hex, px + 40, idy + 18, 1, 1, GREY);

    // a divider
    c.rect(px, idy + 42, pw, 1, rgb(28, 48, 56));
    c.text("the four substances", px, idy + 50, 1, 1, TEAL);

    // 2x2 substance tiles (compact). Each shows the substance's headline value.
    let gy = idy + 74;
    let gx = px;
    let tile_w = (pw - 24) / 2;
    let tile_h = 84;
    let mut vb = [0u8; 32];
    let mut sb = [0u8; 32];
    let mut ab = [0u8; 32];

    sub_tile(c, gx, gy, tile_w, tile_h, 0, value_line(&mut vb, cell));
    sub_tile(c, gx + tile_w + 24, gy, tile_w, tile_h, 1, state_line(&mut sb, cell));
    sub_tile(c, gx, gy + tile_h + 16, tile_w, tile_h, 2, auth_line(&mut ab, cell));
    sub_tile(
        c,
        gx + tile_w + 24,
        gy + tile_h + 16,
        tile_w,
        tile_h,
        3,
        if cell.proved_state { "proved: true" } else if cell.vk_hash != "none" { "vk set" } else { "no vk" },
    );

    // the drill-in hint, set apart.
    let hint_y = gy + 2 * (tile_h) + 16 + 18;
    c.rect(px, hint_y, 6, 18, TEAL);
    c.text("press ENTER to walk this cell's substances", px + 16, hint_y + 3, 1, 1, CYAN);
}

fn sub_tile(c: &mut Canvas, x: u32, y: u32, w: u32, h: u32, idx: usize, value: &str) {
    let accent = SUBSTANCE_ACCENT[idx];
    c.vgradient_rect(x, y, w, h, CARD_LO, (6, 12, 18));
    c.frame(x, y, w, h, 1, accent);
    c.rect(x, y, 4, h, accent);
    c.text(SUBSTANCE_NAME[idx], x + 16, y + 12, 1, 2, accent);
    c.text(SUBSTANCE_GLYPH[idx], x + 16, y + 34, 1, 0, DIM);
    c.text(value, x + 16, y + 56, 1, 0, WHITE);
}

fn value_line<'a>(buf: &'a mut [u8; 32], cell: &ImageCell) -> &'a str {
    let mut w = Writer::new(buf);
    if cell.is_well {
        w.str("well ");
    }
    w.i64(cell.balance);
    w.str(" computrons");
    w.finish()
}

fn state_line<'a>(buf: &'a mut [u8; 32], cell: &ImageCell) -> &'a str {
    let mut w = Writer::new(buf);
    w.u32(cell.fields_used);
    w.str("/16 fields  n=");
    w.u64(cell.nonce);
    w.finish()
}

fn auth_line<'a>(buf: &'a mut [u8; 32], cell: &ImageCell) -> &'a str {
    let mut w = Writer::new(buf);
    w.usize(cell.caps.len());
    w.str(" caps held");
    w.finish()
}

// ─────────────────────── the substance drill-in (full pane) ─────────────────
// A single substance, full main-pane, rendered richly. ENTER pages to the next
// substance; ESC backs to the overview. This is the object-browser drill-down.
fn substance_pane(c: &mut Canvas, cell: &ImageCell, idx: usize) {
    let px = RAIL_W + 28;
    let pw = WIDTH - px - 24;
    let py = TOP_H + 18;
    let accent = SUBSTANCE_ACCENT[idx];

    // breadcrumb: cell title > SUBSTANCE
    c.text(cell.title, px, py, 1, 1, GREY);
    let bx = px + Canvas::text_w(cell.title, 1, 1) + 8;
    c.text(">", bx, py, 1, 1, DIM);
    c.text(SUBSTANCE_NAME[idx], bx + 18, py, 2, 1, accent);

    // a substance progress strip (which of the 4 we're on)
    let dots_x = WIDTH - 24 - (N_SUBSTANCES as u32) * 18;
    for i in 0..N_SUBSTANCES {
        let dx = dots_x + i as u32 * 18;
        let col = if i == idx { SUBSTANCE_ACCENT[i] } else { rgb(36, 56, 64) };
        c.rect(dx, py + 8, 11, 5, col);
    }

    let body_y = py + 48;
    match idx {
        0 => value_detail(c, cell, px, pw, body_y),
        1 => state_detail(c, cell, px, pw, body_y),
        2 => authority_detail(c, cell, px, pw, body_y),
        _ => evidence_detail(c, cell, px, pw, body_y),
    }
}

// VALUE: the signed ledger balance, with the conservation framing.
fn value_detail(c: &mut Canvas, cell: &ImageCell, px: u32, pw: u32, y: u32) {
    card(c, px, y, pw, 132);
    c.text("balance : i64 (signed)", px + 24, y + 18, 1, 1, DIM);

    // the big number
    let mut nb = [0u8; 32];
    let n = {
        let mut w = Writer::new(&mut nb);
        w.i64(cell.balance);
        w.finish()
    };
    let col = if cell.balance < 0 { RED } else if cell.balance > 0 { AMBER } else { GREY };
    c.text(n, px + 24, y + 42, 4, 1, col);
    c.text("computrons", px + 24, y + 96, 1, 1, DIM);

    if cell.is_well {
        let _ = chip(c, px + pw - 180, y + 44, "ISSUER WELL", RED, rgb(28, 12, 12));
        c.text("carries -supply", px + pw - 180, y + 70, 1, 0, rgb(200, 130, 130));
    } else {
        let _ = chip(c, px + pw - 150, y + 44, "ORDINARY", GREEN, rgb(10, 26, 18));
        c.text("kept >= 0 by verb", px + pw - 156, y + 70, 1, 0, GREEN);
    }

    // the conservation fact (real, computed over the whole image)
    let cy = y + 150;
    c.rect(px, cy, 6, 46, TEAL);
    c.text("conservation", px + 18, cy, 1, 1, TEAL);
    let mut sb = [0u8; 40];
    let line = {
        let mut w = Writer::new(&mut sb);
        w.str("across all ");
        w.usize(N_CELLS);
        w.str(" cells, balances sum to ");
        w.i64(BALANCE_SUM);
        w.finish()
    };
    c.text(line, px + 18, cy + 20, 1, 1, WHITE);
    c.text("issuer wells carry -supply, so a closed image conserves to zero.", px + 18, cy + 36, 1, 0, GREY);
}

// STATE: the 16 fields + nonce, rendered as a real table.
fn state_detail(c: &mut Canvas, cell: &ImageCell, px: u32, pw: u32, y: u32) {
    // header row (kept short so it fits the pane even for a full-16 cell)
    let mut hb = [0u8; 40];
    let head = {
        let mut w = Writer::new(&mut hb);
        w.str("fields[16] + nonce  -  ");
        w.u32(cell.fields_used);
        w.str(" set, nonce ");
        w.u64(cell.nonce);
        w.finish()
    };
    c.text(head, px, y, 1, 0, CYAN);

    // column titles
    let ty = y + 24;
    c.text("slot", px, ty, 1, 0, DIM);
    c.text("meaning", px + 48, ty, 1, 0, DIM);
    c.text("vis", px + 240, ty, 1, 0, DIM);
    c.text("value", px + 312, ty, 1, 0, DIM);
    c.rect(px, ty + 14, pw, 1, rgb(28, 48, 56));

    // rows
    let mut ry = ty + 22;
    let row_h = 20u32;
    let mut shown = 0;
    for f in cell.fields.iter() {
        if ry + row_h > HEIGHT - BAR_H - 56 {
            break;
        }
        // zebra
        if shown % 2 == 1 {
            c.rect(px, ry - 2, pw, row_h, rgb(10, 20, 30));
        }
        let mut sb = [0u8; 4];
        c.text(fmt_u32(&mut sb, f.slot), px, ry, 1, 0, TEAL);
        c.text(f.note, px + 48, ry, 1, 0, GREY);
        let vcol = match f.kind {
            "committed" => MAGENTA,
            "disclosable" => GOLD,
            _ => WHITE,
        };
        // visibility marker
        let vis = match f.kind {
            "committed" => "hid",
            "disclosable" => "zk",
            _ => "pub",
        };
        c.text(vis, px + 240, ry, 1, 0, if f.kind == "public" { DIM } else { vcol });
        // value (clipped to the pane)
        let v = clip(f.value, ((pw - 312) / 8) as usize);
        c.text(v, px + 312, ry, 1, 0, vcol);
        ry += row_h;
        shown += 1;
    }

    // footnote (clipped to the pane width so nothing bleeds past the edge)
    let fy = HEIGHT - BAR_H - 44;
    let fmax = (pw / 8) as usize;
    c.rect(px, fy, 6, 30, CYAN);
    c.text(clip("a committed field shows only its hash; plaintext stays private.", fmax), px + 16, fy + 2, 1, 0, GREY);
    c.text(clip("a proof setting all 16 fields flips proved_state (see EVIDENCE).", fmax), px + 16, fy + 16, 1, 0, DIM);
}

// AUTHORITY: the c-list (caps held) + the permission gate table.
fn authority_detail(c: &mut Canvas, cell: &ImageCell, px: u32, pw: u32, y: u32) {
    // left: the c-list (what this cell can reach — the web of cells)
    let half = (pw - 24) / 2;
    c.text("c-list (held capabilities)", px, y, 1, 1, TEAL);
    c.text("what this cell can reach", px, y + 16, 1, 0, DIM);

    let mut ry = y + 38;
    if cell.caps.is_empty() {
        c.vgradient_rect(px, ry, half, 60, CARD_LO, (6, 12, 18));
        c.frame(px, ry, half, 60, 1, rgb(40, 60, 68));
        c.text("(holds no caps)", px + 16, ry + 14, 1, 0, DIM);
        c.text("a leaf of the web -", px + 16, ry + 34, 1, 0, rgb(70, 100, 110));
        c.text("only connectivity begets", px + 16, ry + 46, 1, 0, rgb(70, 100, 110));
    } else {
        for cap in cell.caps.iter() {
            let ch = 64u32;
            c.vgradient_rect(px, ry, half, ch - 8, CARD_HI, CARD_LO);
            c.frame(px, ry, half, ch - 8, 1, TEAL_DIM);
            c.rect(px, ry, 4, ch - 8, TEAL);
            // slot + auth chip
            let mut sb = [0u8; 8];
            let mut w = Writer::new(&mut sb);
            w.str("slot ");
            w.u32(cap.slot);
            let slot = w.finish();
            c.text(slot, px + 14, ry + 8, 1, 0, CYAN);
            let _ = chip(c, px + half - 96, ry + 6, cap.auth, auth_color(cap.auth), rgb(8, 24, 28));
            // the note (-> which named cell)
            c.text(cap.note, px + 14, ry + 26, 1, 0, WHITE);
            // the target id (the real edge), clipped to the card's inner width
            // so it never bleeds into the permission-gates column.
            let id_max = ((half - 28) / 8) as usize;
            c.text(clip(cap.target, id_max), px + 14, ry + 42, 1, 0, rgb(90, 130, 140));
            ry += ch;
            if ry + 64 > HEIGHT - BAR_H - 16 {
                break;
            }
        }
    }

    // right: the permission gate table (permissions ∧ c-list = AUTHORITY)
    let rx = px + half + 24;
    c.text("permission gates", rx, y, 1, 1, TEAL);
    c.text("what auth each action needs", rx, y + 16, 1, 0, DIM);
    let mut py2 = y + 38;
    for kv in cell.perms.iter() {
        c.text(kv.k, rx, py2, 1, 0, GREY);
        let col = auth_color(kv.v);
        let vw = Canvas::text_w(kv.v, 1, 0);
        c.text(kv.v, rx + half - vw, py2, 1, 0, col);
        // gate bar
        c.rect(rx, py2 + 13, half, 1, rgb(20, 40, 48));
        py2 += 22;
    }
    let fy = py2 + 8;
    let amax = (half / 8) as usize;
    c.text(clip("AUTHORITY = permissions ^ c-list", amax), rx, fy, 1, 0, TEAL);
    c.text(clip("to hold a cap is to prove it", amax), rx, fy + 14, 1, 0, DIM);
}

// EVIDENCE: the verification key + proved_state + the state commitment.
fn evidence_detail(c: &mut Canvas, cell: &ImageCell, px: u32, pw: u32, y: u32) {
    // proved_state, prominent
    card(c, px, y, pw, 92);
    c.text("proved_state", px + 24, y + 16, 1, 1, DIM);
    if cell.proved_state {
        c.text("true", px + 24, y + 36, 3, 1, GREEN);
        c.text("all 16 fields were last set by a single verified proof.", px + 24, y + 74, 1, 0, GREY);
        let _ = chip(c, px + pw - 150, y + 30, "PROVEN", GREEN, rgb(10, 26, 18));
    } else {
        c.text("false", px + 24, y + 36, 3, 1, GREY);
        c.text("not all fields are proof-set (ordinary signed writes).", px + 24, y + 74, 1, 0, DIM);
    }

    // the verification key
    let vy = y + 108;
    c.text("verification key (vk_v2)", px, vy, 1, 1, GREEN);
    if cell.vk_hash != "none" {
        card(c, px, vy + 18, pw, 76);
        let vx = px + 104; // value column, clear of the longest label ("program")
        c.text("hash", px + 20, vy + 32, 1, 1, DIM);
        c.text(cell.vk_hash, vx, vy + 32, 1, 0, CYAN);
        c.text("program", px + 20, vy + 52, 1, 1, DIM);
        c.text(clip(cell.vk_program, ((pw - 124) / 8) as usize), vx, vy + 52, 1, 0, WHITE);
        c.text(clip("blake3_keyed(\"dregg-vk-v2\", air | verifier | proving-system)", (pw / 8) as usize), px + 20, vy + 70, 1, 0, rgb(70, 100, 110));
    } else {
        c.vgradient_rect(px, vy + 18, pw, 44, CARD_LO, (6, 12, 18));
        c.frame(px, vy + 18, pw, 44, 1, rgb(40, 60, 68));
        c.text("(no verification key set)", px + 20, vy + 32, 1, 0, DIM);
        c.text("this cell authorizes by signature, not by proof.", px + 20, vy + 46, 1, 0, rgb(70, 100, 110));
    }

    // the state commitment (the carrier that binds the whole cell)
    let cy = vy + 110;
    c.rect(px, cy, 6, 46, GREEN);
    c.text("state commitment", px + 18, cy, 1, 1, GREEN);
    c.text(cell.commitment, px + 18, cy + 18, 1, 1, CYAN);
    c.text("one 32-byte hash binding value, fields, c-list, vk, lifecycle.", px + 18, cy + 36, 1, 0, GREY);
}

// ───────────────────────────── bottom bar ───────────────────────────────────
fn bottom_bar(c: &mut Canvas, st: &ViewState, cell: &ImageCell) {
    let by = HEIGHT - BAR_H;
    c.rect(0, by, WIDTH, BAR_H, rgb(7, 14, 22));
    c.rect(0, by, WIDTH, 2, TEAL_DIM);

    let mut x = 24;
    match st.drill {
        None => {
            x = c.text("UP/DOWN", x, by + 11, 1, 1, TEAL);
            x = c.text(" walk cells", x, by + 11, 1, 1, GREY) + 16;
            x = c.text("ENTER", x, by + 11, 1, 1, TEAL);
            let _ = c.text(" inspect substances", x, by + 11, 1, 1, GREY);
        }
        Some(_) => {
            x = c.text("ENTER", x, by + 11, 1, 1, TEAL);
            x = c.text(" next substance", x, by + 11, 1, 1, GREY) + 16;
            x = c.text("ESC", x, by + 11, 1, 1, TEAL);
            let _ = c.text(" back to the image", x, by + 11, 1, 1, GREY);
        }
    }

    // right: "cell N/M · {key}" — the live cell, NOT a slide.
    let mut buf = [0u8; 24];
    let label = {
        let mut w = Writer::new(&mut buf);
        w.str("cell ");
        w.u32(st.focus as u32 + 1);
        w.str("/");
        w.u32(N_CELLS as u32);
        w.finish()
    };
    let lw = Canvas::text_w(label, 1, 1);
    let kw = Canvas::text_w(cell.key, 1, 1);
    let total = lw + 12 + kw;
    let rx = WIDTH - 24 - total;
    c.text(label, rx, by + 11, 1, 1, DIM);
    c.text(cell.key, rx + lw + 12, by + 11, 1, 1, CYAN);
}

// ───────────────────────────── small helpers ────────────────────────────────
fn accent_for(cell: &ImageCell) -> u32 {
    if cell.is_well {
        RED
    } else if cell.balance > 0 {
        AMBER
    } else {
        TEAL
    }
}

fn life_color(tag: &str) -> u32 {
    match tag {
        "LIVE" => GREEN,
        "SEALED" => AMBER,
        "DESTROYED" => RED,
        "ARCHIVED" => CYAN,
        "MIGRATED" => MAGENTA,
        _ => GREY,
    }
}

fn auth_color(a: &str) -> u32 {
    match a {
        "none" => GREEN,
        "signature" => TEAL,
        "proof" => CYAN,
        "either" => AMBER,
        "impossible" => RED,
        _ => MAGENTA,
    }
}

// A centered card panel with a teal border + a subtle vertical gradient.
fn card(c: &mut Canvas, x: u32, y: u32, w: u32, h: u32) {
    c.vgradient_rect(x, y, w, h, CARD_HI, CARD_LO);
    c.frame(x, y, w, h, 2, TEAL_DIM);
}

// A small "chip"/tag with a filled background and a label. Returns x past it.
fn chip(c: &mut Canvas, x: u32, y: u32, text: &str, fg: u32, bg: u32) -> u32 {
    let tw = Canvas::text_w(text, 1, 0);
    let w = tw + 16;
    c.rect(x, y, w, 18, bg);
    c.frame(x, y, w, 18, 1, fg);
    c.text(text, x + 8, y + 5, 1, 0, fg);
    x + w
}

/// Clip a string to `max` glyphs, replacing the tail with ".." if it overflows.
fn clip(s: &str, max: usize) -> &str {
    if max == 0 {
        return "";
    }
    if s.len() <= max {
        s
    } else {
        // safe byte slice (ASCII content)
        &s[..max.min(s.len())]
    }
}

// ── tiny no_std integer/string formatting into a fixed buffer ───────────────
// (no alloc on the draw path; the rendered numbers are small.)
struct Writer<'a> {
    buf: &'a mut [u8],
    len: usize,
}

impl<'a> Writer<'a> {
    fn new(buf: &'a mut [u8]) -> Self {
        Writer { buf, len: 0 }
    }
    fn push(&mut self, b: u8) {
        if self.len < self.buf.len() {
            self.buf[self.len] = b;
            self.len += 1;
        }
    }
    fn str(&mut self, s: &str) -> &mut Self {
        for &b in s.as_bytes() {
            self.push(b);
        }
        self
    }
    fn u64(&mut self, mut v: u64) -> &mut Self {
        let mut tmp = [0u8; 20];
        let mut i = tmp.len();
        if v == 0 {
            self.push(b'0');
            return self;
        }
        while v > 0 {
            i -= 1;
            tmp[i] = b'0' + (v % 10) as u8;
            v /= 10;
        }
        for &b in &tmp[i..] {
            self.push(b);
        }
        self
    }
    fn u32(&mut self, v: u32) -> &mut Self {
        self.u64(v as u64)
    }
    fn usize(&mut self, v: usize) -> &mut Self {
        self.u64(v as u64)
    }
    fn i64(&mut self, v: i64) -> &mut Self {
        if v < 0 {
            self.push(b'-');
            self.u64((v as i128).unsigned_abs() as u64)
        } else {
            self.u64(v as u64)
        }
    }
    fn finish(self) -> &'a str {
        // SAFETY: we only ever push ASCII bytes.
        core::str::from_utf8(&self.buf[..self.len]).unwrap_or("")
    }
}

fn fmt_u32(buf: &mut [u8; 4], v: u32) -> &str {
    let mut w = Writer::new(buf);
    w.u32(v);
    w.finish()
}

fn fmt_two<'a>(buf: &'a mut [u8; 8], a: u32, b: u32) -> &'a str {
    let mut w = Writer::new(buf);
    w.u32(a);
    w.str("/");
    w.u32(b);
    w.finish()
}

fn fmt_n_cells(buf: &mut [u8; 16], n: u32) -> &str {
    let mut w = Writer::new(buf);
    w.u32(n);
    w.str(" real cells");
    w.finish()
}
