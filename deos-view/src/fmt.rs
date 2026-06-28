//! **Renderer-independent display formatting** for bound values — the consumer-delight
//! layer that turns a raw opaque integer (a 20-digit decimal key/hash) into something
//! SHORT and FRIENDLY, identically across every renderer (native gpui / web HTML /
//! discord embed).
//!
//! A `bind` (and any bound text) carries a [`BindFmt`] chosen by the card author through
//! `props.fmt` (`"id"|"key"|"hash"|"hex"|"amount"|"raw"`). The default ([`BindFmt::Raw`])
//! keeps the plain decimal — a counter stays `count: 1`. But an IDENTITY slot tagged
//! `fmt:"id"` paints a deterministic emoji-avatar handle (`🦊 swift-fox`); a HASH slot
//! tagged `fmt:"hash"` paints a truncated hex (`0x8bf3…a3d8`); a balance tagged
//! `fmt:"amount"` paints grouped digits (`1,234,567`). This is what kills the dev-y feel
//! without re-authoring each card — the card sets one prop, the rendering layer does the
//! rest, the SAME way in all three renderers.
//!
//! The derivation is PURE + DETERMINISTIC (a stable hash → handle map), so the same value
//! always paints the same handle, and the [web JS mirror](fmt_js) produces byte-identical
//! output for the live in-tab re-read (no drift between the server bake and the browser
//! repaint — the avatar wordlists below are the single source both consume).

/// How a bound value renders to display text. Chosen per-`bind` by the card author via
/// `props.fmt`; [`BindFmt::Raw`] (the default) keeps the plain decimal so existing
/// integer binds are unchanged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BindFmt {
    /// The plain decimal (`12345`) — the default; a counter/quantity stays as-is.
    #[default]
    Raw,
    /// A truncated hex digest (`0x8bf3…a3d8`) — for a hash / opaque digest.
    Hex,
    /// A deterministic emoji-avatar handle (`🦊 swift-fox`) — for an identity / key / id.
    Id,
    /// Grouped decimal digits (`1,234,567`) — for a human amount / balance.
    Amount,
}

impl BindFmt {
    /// Lift the `props.fmt` string into a [`BindFmt`]. Unknown / absent → [`BindFmt::Raw`]
    /// (the safe default: a plain integer). `"id"`/`"key"` → the avatar handle; `"hash"`/
    /// `"hex"` → the short hex; `"amount"` → grouped digits.
    pub fn from_prop(s: Option<&str>) -> Self {
        match s.unwrap_or("") {
            "id" | "key" => BindFmt::Id,
            "hash" | "hex" => BindFmt::Hex,
            "amount" => BindFmt::Amount,
            _ => BindFmt::Raw,
        }
    }

    /// The canonical `props.fmt` string (round-trips [`BindFmt::from_prop`] modulo the
    /// `key`/`hash` aliases). Carried as `data-fmt` so the web JS mirror picks the path.
    pub fn as_str(self) -> &'static str {
        match self {
            BindFmt::Raw => "raw",
            BindFmt::Hex => "hex",
            BindFmt::Id => "id",
            BindFmt::Amount => "amount",
        }
    }
}

/// Format a bound `value` for display under `fmt`. The one entry every renderer calls so
/// the native, web (first paint) and discord projections paint the IDENTICAL string.
pub fn format_value(value: u64, fmt: BindFmt) -> String {
    match fmt {
        BindFmt::Raw => value.to_string(),
        BindFmt::Hex => short_hex(value),
        BindFmt::Id => handle_for(value),
        BindFmt::Amount => group_amount(value),
    }
}

/// A truncated hex digest of `value` — `0x{first4}…{last4}` when long, else `0x{hex}`.
/// E.g. `10083942588892332568 → 0x8bf3…a3d8`. Mirrors [`fmt_js`]'s `deosShortHex`.
pub fn short_hex(value: u64) -> String {
    let h = format!("{value:x}");
    if h.len() > 8 {
        format!("0x{}…{}", &h[..4], &h[h.len() - 4..])
    } else {
        format!("0x{h}")
    }
}

/// Group a decimal `value`'s digits in threes (`1234567 → 1,234,567`). Mirrors [`fmt_js`]'s
/// `deosGroupAmount`.
pub fn group_amount(value: u64) -> String {
    let s = value.to_string();
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut out = String::with_capacity(len + len / 3);
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 && (len - i) % 3 == 0 {
            out.push(',');
        }
        out.push(*b as char);
    }
    out
}

// ── The avatar wordlists — the SINGLE source of the stable hash→handle map. Both the Rust
//    [`handle_for`] and the web [`fmt_js`] mirror index into THESE, so the server bake and
//    the browser live re-read produce the identical handle (no drift). 16 each → a clean
//    4-bit slice; 16·16·16 = 4096 distinct friendly handles. ─────────────────────────────
/// The avatar emoji palette (friendly fauna), indexed by the low nibble of the mix.
pub const AVATAR_EMOJI: [&str; 16] = [
    "🦊", "🐢", "🦉", "🐙", "🦋", "🐝", "🐬", "🦁", "🐼", "🦅", "🦄", "🐳", "🦖", "🦜", "🦦", "🦩",
];
/// The avatar adjective list, indexed by mix bits 8..12.
pub const AVATAR_ADJ: [&str; 16] = [
    "swift", "brave", "calm", "bright", "lucky", "noble", "quiet", "merry", "bold", "gentle",
    "clever", "sunny", "cozy", "keen", "jolly", "wise",
];
/// The avatar noun list, indexed by mix bits 16..20.
pub const AVATAR_NOUN: [&str; 16] = [
    "fox", "owl", "wren", "lynx", "moth", "hare", "finch", "otter", "crane", "vole", "newt", "koi",
    "dove", "elk", "mole", "swan",
];

/// A splitmix64 finalizer — decorrelates sequential ids so `slot N` and `slot N+1` get
/// visually-distinct handles. Pure, wrapping; mirrored exactly by [`fmt_js`]'s `deosMix`.
fn mix(value: u64) -> u64 {
    let mut z = value.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// A deterministic emoji-avatar handle for an opaque `value` (`🦊 swift-fox`) — a stable,
/// human-memorable stand-in for a 20-digit key/id. Same value → same handle, forever.
pub fn handle_for(value: u64) -> String {
    let m = mix(value);
    let e = AVATAR_EMOJI[(m & 15) as usize];
    let a = AVATAR_ADJ[((m >> 8) & 15) as usize];
    let n = AVATAR_NOUN[((m >> 16) & 15) as usize];
    format!("{e} {a}-{n}")
}

/// The **web JS mirror** of this module — emitted into a live card document so the in-tab
/// re-read (`card.read(slot)`) formats a bound value the SAME way the server bake did.
/// Built FROM the shared wordlists above, so it can never drift from [`handle_for`]. It
/// defines `deosFmt(value, fmt)` (+ helpers) used by the web renderer's repaint wire.
pub fn fmt_js() -> String {
    let arr = |xs: &[&str]| -> String {
        xs.iter()
            .map(|s| format!("\"{s}\""))
            .collect::<Vec<_>>()
            .join(",")
    };
    format!(
        "\nconst DEOS_AVATAR_EMOJI=[{emoji}];\n\
const DEOS_AVATAR_ADJ=[{adj}];\n\
const DEOS_AVATAR_NOUN=[{noun}];\n\
const DEOS_U64=0xFFFFFFFFFFFFFFFFn;\n\
function deosMix(v){{\n\
  var z=(BigInt(v)+0x9E3779B97F4A7C15n)&DEOS_U64;\n\
  z=((z^(z>>30n))*0xBF58476D1CE4E5B9n)&DEOS_U64;\n\
  z=((z^(z>>27n))*0x94D049BB133111EBn)&DEOS_U64;\n\
  z=(z^(z>>31n))&DEOS_U64;\n\
  return z;\n\
}}\n\
function deosHandle(v){{\n\
  var m=deosMix(v);\n\
  return DEOS_AVATAR_EMOJI[Number(m&15n)]+' '+DEOS_AVATAR_ADJ[Number((m>>8n)&15n)]+'-'+DEOS_AVATAR_NOUN[Number((m>>16n)&15n)];\n\
}}\n\
function deosShortHex(v){{\n\
  var h=(BigInt(v)&DEOS_U64).toString(16);\n\
  return h.length>8 ? '0x'+h.slice(0,4)+'\\u2026'+h.slice(-4) : '0x'+h;\n\
}}\n\
function deosGroupAmount(v){{\n\
  var s=(BigInt(v)&DEOS_U64).toString(); var out=''; var n=s.length;\n\
  for(var i=0;i<n;i++){{ if(i>0&&(n-i)%3===0) out+=','; out+=s[i]; }} return out;\n\
}}\n\
function deosFmt(v,fmt){{\n\
  switch(fmt){{\n\
    case 'id': case 'key': return deosHandle(v);\n\
    case 'hash': case 'hex': return deosShortHex(v);\n\
    case 'amount': return deosGroupAmount(v);\n\
    default: return (BigInt(v)&DEOS_U64).toString();\n\
  }}\n\
}}\n",
        emoji = arr(&AVATAR_EMOJI),
        adj = arr(&AVATAR_ADJ),
        noun = arr(&AVATAR_NOUN),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_is_the_plain_decimal_default() {
        assert_eq!(format_value(0, BindFmt::Raw), "0");
        assert_eq!(format_value(12345, BindFmt::Raw), "12345");
        assert_eq!(BindFmt::from_prop(None), BindFmt::Raw);
        assert_eq!(BindFmt::from_prop(Some("nonsense")), BindFmt::Raw);
    }

    #[test]
    fn the_dev_y_20_digit_key_becomes_short() {
        // The exact value from the dev-y screenshot: `seller key · 10083942588892332568`.
        let v: u64 = 10083942588892332568;
        let hex = format_value(v, BindFmt::Hex);
        // `0x` + 4 + `…` + 4 = 11 chars (the `…` is one glyph / 3 UTF-8 bytes).
        assert!(
            hex.starts_with("0x") && hex.contains('…') && hex.chars().count() == 11,
            "short hex: {hex}"
        );
        let handle = format_value(v, BindFmt::Id);
        // Friendly, short, deterministic, and NOT a wall of digits.
        assert!(
            !handle.chars().any(|c| c.is_ascii_digit()),
            "the handle has no raw digits: {handle}"
        );
        assert!(handle.contains('-'), "adjective-noun handle: {handle}");
        assert_eq!(handle_for(v), handle, "the handle is stable for the value");
    }

    #[test]
    fn from_prop_maps_every_documented_alias() {
        assert_eq!(BindFmt::from_prop(Some("id")), BindFmt::Id);
        assert_eq!(BindFmt::from_prop(Some("key")), BindFmt::Id);
        assert_eq!(BindFmt::from_prop(Some("hash")), BindFmt::Hex);
        assert_eq!(BindFmt::from_prop(Some("hex")), BindFmt::Hex);
        assert_eq!(BindFmt::from_prop(Some("amount")), BindFmt::Amount);
        assert_eq!(BindFmt::from_prop(Some("raw")), BindFmt::Raw);
    }

    #[test]
    fn amount_groups_digits() {
        assert_eq!(group_amount(1), "1");
        assert_eq!(group_amount(1234), "1,234");
        assert_eq!(group_amount(1234567), "1,234,567");
    }

    #[test]
    fn short_hex_matches_the_documented_shape() {
        assert_eq!(short_hex(0), "0x0");
        assert_eq!(short_hex(0xff), "0xff");
        // A long value elides the middle.
        let h = short_hex(0x8bf3aabbccdda3d8);
        assert_eq!(h, "0x8bf3…a3d8");
    }

    #[test]
    fn the_js_mirror_carries_the_same_wordlists() {
        // The single-source guarantee: the JS mirror is built FROM the shared lists, so the
        // browser live re-read can't drift from the Rust bake.
        let js = fmt_js();
        for e in AVATAR_EMOJI {
            assert!(js.contains(e), "the JS mirror carries emoji {e}");
        }
        assert!(js.contains("swift") && js.contains("fox"));
        assert!(js.contains("function deosFmt"));
    }
}
