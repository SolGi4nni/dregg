//! # THE URI GRAMMAR — one grammar, mirrored, never a second one.
//!
//! `extension/src/port.ts` pins the canonical grammar (DREGG-QUIET-UPGRADE.md §1 + §9's
//! closing note). This module is a FAITHFUL Rust mirror of exactly three regexes there —
//! not a re-derivation:
//!
//! ```text
//! CANONICAL_RE  = /^dregg:\/\/([a-z0-9]+)\/([^?#\s]+)(?:[?#].*)?$/i
//! MIRROR_RE     = /^https?:\/\/<host>\/d\/([a-z0-9]+)\/([^?#\s]+)(?:[?#].*)?$/i
//! VALID_ADDR_RE = /^b3_[0-9a-f]{6,}$/i
//! ```
//!
//! [`canonical_uri`] is the same key function `port.ts` exports: BOTH uri forms map to
//! the one `dregg://<kind>/<addr>` string. A drift here is a security bug (the extension
//! and the mirror would disagree about what a link names), so the mirror never invents a
//! second parser — and [`parse_dregg_uri`] accepts an UNKNOWN kind exactly like `port.ts`
//! does (`[a-z0-9]+`); the *routing* layer is what refuses an unregistered kind (§4:
//! unknown kind ⇒ a clean 404, never a guess).
//!
//! ## THE MIRROR PATH SHAPE (this crate's one deliberate choice)
//!
//! Served form: **`https://dregg.gg/<kind>/<addr-or-prefix>`**, with
//! `/d/<kind>/<addr>` accepted as an ALIAS (that is the form §1 documents and the form
//! `extension/src/detect.ts` currently writes into fallback anchors, so already-published
//! links keep working forever).
//!
//! Why drop `/d/`: X truncates *displayed* link text. Every character of path prefix is a
//! character of content address that does not survive the elision, and `/d/` carries zero
//! information — the kind segment already namespaces the space. `dregg.gg/poll/7f2a9c4d`
//! is 23 characters; `dregg.net/d/poll/b3_7f2a9c4d` is 28. Why KEEP the kind segment: it
//! is what selects the renderer and what makes "unknown kind ⇒ clean 404" possible without
//! searching every namespace and guessing, and it keeps one grammar shared with `port.ts`,
//! which is kind-first.
//!
//! Why the `b3_` tag is OPTIONAL in the path but MANDATORY in the canonical string: on the
//! wire the server already knows its own addressing, so three characters of tag are three
//! characters of address budget spent on nothing; but the canonical `dregg://` string a
//! reader copies must never lose its algorithm tag, because that string travels.

/// The content-address tag `port.ts`'s `VALID_ADDR_RE` requires: `b3_` (blake3).
pub const ADDR_TAG: &str = "b3_";

/// `port.ts`'s `VALID_ADDR_RE` floor: `b3_[0-9a-f]{6,}`. A canonical uri shorter than
/// this is malformed *for the extension too*, so the mirror refuses it identically.
pub const MIN_ADDR_HEX: usize = 6;

/// A full blake3 digest in hex. An addr token of exactly this length is a FULL address;
/// anything shorter is a PREFIX to be disambiguated against the store.
pub const FULL_ADDR_HEX: usize = 64;

/// The git-style short-prefix floor for the *mirror path* (§2 of this lane's brief).
/// Deliberately stricter than [`MIN_ADDR_HEX`]: a 6-hex prefix is 24 bits, which is a
/// coin flip over a corpus of any size, and a mirror link is the thing a stranger clicks.
/// 8 hex = 32 bits, the same floor git uses for its short SHAs.
pub const MIN_PREFIX_HEX: usize = 8;

/// The KIND REGISTRY — the kinds this mirror will render, and the ONLY ones.
///
/// Each is a kind that already has a resolver in `extension/src/port.ts` and an element in
/// `extension/src/elements/`. A kind not on this list is a clean 404 (brief §4): the mirror
/// never guesses a renderer for a name it does not know.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    /// `dregg://poll/…` — `<dregg-poll>`, `PollEngine` (`port.ts`).
    Poll,
    /// `dregg://doc/…` — `<dregg-doc>`, `DocEngine`; holds a conflict as BOTH alternatives.
    Doc,
    /// `dregg://doctext/…` — the collaborative-text engine (`port.ts` `defaultResolveDocText`).
    DocText,
    /// `dregg://story/…` — `<dregg-story>`, the story engine.
    Story,
    /// `dregg://descent/…` — `<dregg-descent>`, the descent engine (epoch-pinned day).
    Descent,
}

impl Kind {
    /// Every registered kind, in canonical order.
    pub const ALL: &'static [Kind] = &[
        Kind::Poll,
        Kind::Doc,
        Kind::DocText,
        Kind::Story,
        Kind::Descent,
    ];

    /// Parse a kind token (lower-cased by the caller's grammar). `None` ⇒ unregistered,
    /// which the router turns into a 404 — never a guessed renderer.
    pub fn parse(s: &str) -> Option<Kind> {
        Some(match s {
            "poll" => Kind::Poll,
            "doc" => Kind::Doc,
            "doctext" => Kind::DocText,
            "story" => Kind::Story,
            "descent" => Kind::Descent,
            _ => return None,
        })
    }

    /// The canonical token, as it appears in `dregg://<kind>/…`.
    pub const fn as_str(self) -> &'static str {
        match self {
            Kind::Poll => "poll",
            Kind::Doc => "doc",
            Kind::DocText => "doctext",
            Kind::Story => "story",
            Kind::Descent => "descent",
        }
    }

    /// A one-line human description, for the index page's kind list.
    pub const fn describe(self) -> &'static str {
        match self {
            Kind::Poll => "a collective choice: options, a live tally, a quorum",
            Kind::Doc => "a verifiable document; a conflict is held as BOTH alternatives",
            Kind::DocText => "a collaboratively edited text",
            Kind::Story => "a branching story",
            Kind::Descent => "a descent run, pinned to a committed epoch",
        }
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A parsed dregg-thing: the kind token exactly as `port.ts` yields it (lower-cased,
/// NOT yet checked against the registry) and the raw addr token (NOT yet validated).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DreggRef {
    /// The kind token (`[a-z0-9]+`, lower-cased). May be unregistered.
    pub kind: String,
    /// The addr token as it appeared, e.g. `b3_7f2a…`. May be malformed.
    pub addr: String,
}

/// Parse a canonical `dregg://<kind>/<addr>[?q]` uri. The mirror of `CANONICAL_RE`.
///
/// Query/fragment are HINTS ONLY (§1) and are discarded here — never parsed, never
/// rendered, never trusted.
pub fn parse_canonical(uri: &str) -> Option<DreggRef> {
    let s = uri.trim();
    let rest = strip_prefix_ci(s, "dregg://")?;
    split_kind_addr(rest)
}

/// Parse a mirror `http(s)://<host>/[d/]<kind>/<addr>[?q]` url. The mirror of `MIRROR_RE`,
/// widened by exactly one thing: the `/d/` segment is optional (see the module doc).
///
/// HOST-AGNOSTIC on purpose. The mirror must accept its own links back whatever the host
/// header says — `dregg.gg`, the legacy `dregg.net`, a tailnet name, `localhost:8791`
/// during a smoke test. The host is *not* a trust input: the content address is.
pub fn parse_mirror_url(url: &str) -> Option<DreggRef> {
    let s = url.trim();
    let rest = strip_prefix_ci(s, "https://").or_else(|| strip_prefix_ci(s, "http://"))?;
    // Drop the authority; everything from the first `/` is the path.
    let (_authority, path) = rest.split_once('/')?;
    parse_mirror_path(&format!("/{path}"))
}

/// Parse a mirror request PATH: `/<kind>/<addr>` or the `/d/<kind>/<addr>` alias.
/// A trailing slash is tolerated; a query string must already be split off (the
/// `http-serve` [`WebRequest`](http_serve::WebRequest) does that).
pub fn parse_mirror_path(path: &str) -> Option<DreggRef> {
    let p = path.trim();
    let p = p.strip_prefix('/')?;
    let p = p.strip_suffix('/').unwrap_or(p);
    // The `/d/` alias — §1's documented mirror form, the one `detect.ts` writes today.
    let p = p.strip_prefix("d/").unwrap_or(p);
    split_kind_addr(p)
}

/// Parse EITHER uri form to `{kind, addr}` — the same contract as `port.ts`'s
/// `parseDreggUri`, so a string the extension upgrades is a string the mirror serves.
pub fn parse_dregg_uri(uri: &str) -> Option<DreggRef> {
    parse_canonical(uri).or_else(|| parse_mirror_url(uri))
}

/// The canonical key for a dregg-thing — `port.ts`'s `canonicalUri`. BOTH uri forms map
/// to this one string; it is what a reader copies out of the mirror page, and what the
/// extension keys its cache on.
pub fn canonical_uri(kind: &str, addr_hex: &str) -> String {
    format!("dregg://{kind}/{ADDR_TAG}{addr_hex}")
}

/// The mirror url this service serves a resolved object at — always the FULL address, so
/// the link a reader copies out of the page is never the ambiguous short one.
pub fn mirror_url(origin: &str, kind: &str, addr_hex: &str) -> String {
    format!("https://{origin}/{kind}/{ADDR_TAG}{addr_hex}")
}

/// How an addr token in a mirror path resolves against the addressing scheme, BEFORE the
/// store is consulted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddrToken {
    /// A complete 64-hex blake3 digest. Canonical; no disambiguation needed.
    Full(String),
    /// An unambiguous-*looking* short prefix (>= [`MIN_PREFIX_HEX`], < 64 hex). The STORE
    /// decides whether it actually is unambiguous.
    Prefix(String),
}

/// Why an addr token was refused. Each is a fail-closed 4xx with an honest explanation —
/// never a blank page and never an optimistic default (brief §5).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddrError {
    /// Not hex, or the `b3_` tag was present but malformed.
    Malformed,
    /// Shorter than [`MIN_PREFIX_HEX`] — too weak to be a link a stranger clicks.
    TooShort {
        /// The number of hex characters supplied.
        got: usize,
        /// The floor ([`MIN_PREFIX_HEX`]).
        need: usize,
    },
    /// Longer than a blake3 digest — not an address at all.
    TooLong,
}

/// Classify a mirror-path addr token. Accepts `b3_<hex>` and bare `<hex>` (see the module
/// doc on why the tag is optional here and mandatory in the canonical string).
pub fn classify_addr(token: &str) -> Result<AddrToken, AddrError> {
    let t = token.trim();
    let hex = match strip_prefix_ci(t, ADDR_TAG) {
        Some(rest) => rest,
        None => t,
    };
    if hex.is_empty() || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(AddrError::Malformed);
    }
    let hex = hex.to_ascii_lowercase();
    match hex.len() {
        FULL_ADDR_HEX => Ok(AddrToken::Full(hex)),
        n if n > FULL_ADDR_HEX => Err(AddrError::TooLong),
        n if n < MIN_PREFIX_HEX => Err(AddrError::TooShort {
            got: n,
            need: MIN_PREFIX_HEX,
        }),
        _ => Ok(AddrToken::Prefix(hex)),
    }
}

/// `VALID_ADDR_RE` — `port.ts`'s strict canonical-addr gate, verbatim. Used when the
/// mirror is handed a *canonical* string (which must carry the tag), not a path token.
pub fn is_valid_canonical_addr(token: &str) -> bool {
    match strip_prefix_ci(token, ADDR_TAG) {
        Some(hex) => {
            hex.len() >= MIN_ADDR_HEX
                && hex.len() <= FULL_ADDR_HEX
                && hex.chars().all(|c| c.is_ascii_hexdigit())
        }
        None => false,
    }
}

// ── the two shared primitives the regex mirror is built from ─────────────────

/// `[a-z0-9]+ '/' [^?#\s]+` with the query/fragment tail discarded — the shared body of
/// `CANONICAL_RE` and `MIRROR_RE`.
fn split_kind_addr(rest: &str) -> Option<DreggRef> {
    // `(?:[?#].*)?$` — the hint tail. Cut it before anything else.
    let rest = rest
        .split(['?', '#'])
        .next()
        .filter(|s| !s.is_empty())
        .map(str::trim)?;
    if rest.chars().any(char::is_whitespace) {
        return None; // `[^?#\s]+`
    }
    let (kind, addr) = rest.split_once('/')?;
    if kind.is_empty() || addr.is_empty() {
        return None;
    }
    if !kind.chars().all(|c| c.is_ascii_alphanumeric()) {
        return None; // `([a-z0-9]+)` under /i
    }
    Some(DreggRef {
        kind: kind.to_ascii_lowercase(),
        addr: addr.to_string(),
    })
}

/// ASCII-case-insensitive `strip_prefix` (the regexes are all `/i`).
fn strip_prefix_ci<'a>(s: &'a str, prefix: &str) -> Option<&'a str> {
    if s.len() >= prefix.len() && s[..prefix.len()].eq_ignore_ascii_case(prefix) {
        Some(&s[prefix.len()..])
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_and_mirror_forms_map_to_one_key() {
        let a = parse_dregg_uri("dregg://poll/b3_7f2a9c4d").unwrap();
        let b = parse_dregg_uri("https://dregg.gg/poll/b3_7f2a9c4d").unwrap();
        let c = parse_dregg_uri("https://dregg.net/d/poll/b3_7f2a9c4d").unwrap();
        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(canonical_uri(&a.kind, "7f2a9c4d"), "dregg://poll/b3_7f2a9c4d");
    }

    #[test]
    fn query_and_fragment_are_hints_only_and_are_discarded() {
        let r = parse_dregg_uri("dregg://poll/b3_7f2a9c4d?label=Vote%20now#x").unwrap();
        assert_eq!(r.addr, "b3_7f2a9c4d");
    }

    #[test]
    fn unregistered_kind_parses_but_does_not_resolve_to_a_kind() {
        // `port.ts` parses any `[a-z0-9]+`; the REGISTRY is what refuses.
        let r = parse_dregg_uri("dregg://wombat/b3_7f2a9c4d").unwrap();
        assert_eq!(r.kind, "wombat");
        assert_eq!(Kind::parse(&r.kind), None);
    }

    #[test]
    fn addr_token_classification_is_fail_closed() {
        assert_eq!(
            classify_addr("b3_7f2a9c4d"),
            Ok(AddrToken::Prefix("7f2a9c4d".into()))
        );
        assert_eq!(
            classify_addr("7F2A9C4D"),
            Ok(AddrToken::Prefix("7f2a9c4d".into()))
        );
        assert_eq!(
            classify_addr("7f2a"),
            Err(AddrError::TooShort { got: 4, need: 8 })
        );
        assert_eq!(classify_addr("zzzzzzzz"), Err(AddrError::Malformed));
        assert_eq!(classify_addr(&"a".repeat(65)), Err(AddrError::TooLong));
        assert!(matches!(
            classify_addr(&"a".repeat(64)),
            Ok(AddrToken::Full(_))
        ));
    }

    #[test]
    fn mirror_path_accepts_the_short_form_and_the_spec_alias() {
        let short = parse_mirror_path("/poll/7f2a9c4d").unwrap();
        let alias = parse_mirror_path("/d/poll/7f2a9c4d").unwrap();
        assert_eq!(short, alias);
        assert_eq!(short.kind, "poll");
    }

    #[test]
    fn strict_canonical_addr_gate_matches_port_ts() {
        assert!(is_valid_canonical_addr("b3_abcdef"));
        assert!(!is_valid_canonical_addr("abcdef")); // tag is MANDATORY in canonical form
        assert!(!is_valid_canonical_addr("b3_abcd")); // < 6 hex
        assert!(!is_valid_canonical_addr("b3_zzzzzz"));
    }
}
