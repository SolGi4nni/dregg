//! **The ONE affordance-transport codec** — the single encode/decode for a
//! [`ViewNode::Button`](crate::tree::ViewNode)'s `{turn, arg}` affordance as it rides back to the
//! executor over whatever channel a surface backend uses.
//!
//! Every backend carries the SAME `{turn, arg}` payload on actuation; they differed only in the
//! byte shape of the channel that carries it (Discord's component custom-id, Telegram's
//! `callback_data`, a web `data-turn`/form field). This canonicalizes that shape into one
//! transport-parameterized codec so the four ad-hoc encodings become one function with a
//! [`AffordanceTransport`] argument. The Discord `deosturn:<turn>:<arg>` shape is the general
//! case; Telegram/web are the un-prefixed `<turn>:<arg>` variant of the same codec.
//!
//! Round-trips for every transport: `parse_affordance_id(&affordance_id(turn, arg, t), t) ==
//! Some((turn, arg))`.

/// The channel a surface backend carries an affordance `{turn, arg}` back on. Selects the byte
/// shape of the encoded id; the payload is identical across all of them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AffordanceTransport {
    /// A Discord message-component **custom-id** — prefixed `deosturn:<turn>:<arg>` so a bot's
    /// component handler can tell one of ours from any other component id (a non-`deosturn:` id
    /// decodes to `None`, i.e. "not ours, ignore").
    Discord,
    /// A Telegram inline-keyboard button's **`callback_data`** — the un-prefixed `<turn>:<arg>`
    /// (Telegram caps `callback_data` at 64 bytes; the prefix is dead weight there, and the
    /// keyboard is only ever our own). Decoded by splitting on the LAST separator.
    Telegram,
    /// A web control's affordance payload — the un-prefixed `<turn>:<arg>` (the same shape the
    /// `data-turn`/`data-arg` attributes carry as a pair). Identical codec to [`Self::Telegram`].
    Web,
    /// A WeChat Official-Account affordance — the **numbered/positional** channel.
    ///
    /// WeChat OA forbids arbitrary per-message buttons: the affordances ride as a `1.`-indexed
    /// NUMBERED REPLY LIST in the message text and the user replies with the **number** (the reply
    /// arrives as an ordinary inbound text message). So this transport is a PAIR:
    ///
    /// * the **positional** half — [`wechat_reply_index`] takes a user's reply (`"2"`, `"2."`,
    ///   `"2 trade blows"`) to the 1-based POSITION in the presented list; the position is resolved
    ///   against that list ([`crate::wechat::WeChatMessage::resolve`]), because a bare number cannot
    ///   name a `{turn, arg}` by itself.
    /// * the **id** half — the `#<turn>:<arg>` id each numbered option carries (and a Mini-Program
    ///   card's button posts back verbatim). MARKED with `#` for the same reason Discord's id is
    ///   marked `deosturn:`, and a sharper one: WeChat's inbound channel is FREE USER TEXT (any prose
    ///   arrives on it), so an unmarked `<turn>:<arg>` shape would let a user's chat line be mistaken
    ///   for an affordance the surface minted. An unmarked id decodes to `None` — "not ours, ignore".
    WeChat,
}

/// The Discord custom-id prefix carrying a [`ViewNode::Button`](crate::tree::ViewNode)'s affordance
/// through Discord's component-id channel — the Discord analogue of the web renderer's `data-turn`.
pub const TURN_PREFIX: &str = "deosturn";

/// The `<turn>:<arg>` separator (the un-prefixed transports split on it; Discord uses it too, after
/// its prefix).
const SEP: char = ':';

/// The **number-sign mark** on a WeChat affordance id (`#<turn>:<arg>`) — the WeChat analogue of
/// Discord's `deosturn:` prefix. WeChat's inbound channel is free user text, so an id MUST be
/// distinguishable from ordinary prose; an unmarked string is never one of ours.
pub const WECHAT_MARK: char = '#';

/// Encode an affordance `{turn, arg}` into the id `transport` carries it on. The inverse of
/// [`parse_affordance_id`] for the same `transport`.
///
/// - [`AffordanceTransport::Discord`] → `deosturn:<turn>:<arg>` (prefixed).
/// - [`AffordanceTransport::Telegram`] / [`AffordanceTransport::Web`] → `<turn>:<arg>` (un-prefixed).
/// - [`AffordanceTransport::WeChat`] → `#<turn>:<arg>` (number-sign marked — the id half of the
///   numbered channel; the option's 1-based POSITION is the other half, see [`wechat_reply_index`]).
pub fn affordance_id(turn: &str, arg: i64, transport: AffordanceTransport) -> String {
    match transport {
        AffordanceTransport::Discord => format!("{TURN_PREFIX}{SEP}{turn}{SEP}{arg}"),
        AffordanceTransport::Telegram | AffordanceTransport::Web => format!("{turn}{SEP}{arg}"),
        AffordanceTransport::WeChat => format!("{WECHAT_MARK}{turn}{SEP}{arg}"),
    }
}

/// Decode an id minted by [`affordance_id`] for the same `transport` back into `(turn, arg)`.
/// `None` if the id is not one of ours for that transport (Discord: missing/`!= deosturn` prefix;
/// WeChat: missing the `#` mark — i.e. ordinary user prose, or a bare reply NUMBER, which is a
/// POSITION and not an id) or is malformed (no separator / a non-integer arg) — a press the surface
/// never minted.
///
/// Discord splits after the prefix (`splitn(3, ':')`); the un-prefixed transports and WeChat (after
/// its mark) split on the LAST separator (`rsplit_once`), so a `turn` may in principle contain
/// earlier separators.
pub fn parse_affordance_id(id: &str, transport: AffordanceTransport) -> Option<(String, i64)> {
    match transport {
        AffordanceTransport::Discord => {
            let mut it = id.splitn(3, SEP);
            if it.next()? != TURN_PREFIX {
                return None;
            }
            let turn = it.next()?.to_string();
            let arg = it.next()?.parse().ok()?;
            Some((turn, arg))
        }
        AffordanceTransport::Telegram | AffordanceTransport::Web => {
            let (turn, arg) = id.rsplit_once(SEP)?;
            Some((turn.to_string(), arg.parse().ok()?))
        }
        AffordanceTransport::WeChat => {
            let body = id.strip_prefix(WECHAT_MARK)?;
            let (turn, arg) = body.rsplit_once(SEP)?;
            Some((turn.to_string(), arg.parse().ok()?))
        }
    }
}

// ── THE TEXT-BEARING AFFORDANCE (additive) ──────────────────────────────────────────────────
// A `{turn, arg}` affordance names an *index* move; a **text-shaped** one (a document edit's
// prose, a hosted-Hermes prompt) needs a *string* alongside it. These two functions carry that
// optional text through the SAME transport-parameterised codec — WITHOUT disturbing the text-free
// wire: `affordance_id_with_text(t, a, None, tr)` is byte-for-byte `affordance_id(t, a, tr)`, and
// `parse_affordance_id_with_text` on a text-free id reproduces `parse_affordance_id` exactly. So
// every existing encoded affordance is unaffected; only a text-bearing one grows a trailing
// segment.

/// The **reserved separator** that introduces a text-bearing affordance's encoded text segment.
/// A text-FREE id never contains it — the `{turn, arg}` formatters ([`affordance_id`]) never emit
/// it, and it is an ASCII control character no affordance verb uses — so
/// [`parse_affordance_id_with_text`] on a text-free id splits off no text and falls through to the
/// unchanged [`parse_affordance_id`]. The text segment itself is HEX (its alphabet is `[0-9a-f]`,
/// which excludes this char), so the LAST occurrence is always the real delimiter.
const TEXT_SEP: char = '\u{1f}';

/// Hex-encode a string's UTF-8 bytes into `[0-9a-f]*` — the text segment's on-wire form. Hex is
/// dependency-free and its alphabet excludes [`TEXT_SEP`] and every base-id character (`:`, `#`,
/// the prefix, digits/`-`), so the encoded text is unambiguous to split back off.
fn hex_encode(s: &str) -> String {
    let mut out = String::with_capacity(s.len() * 2);
    for b in s.as_bytes() {
        out.push(char::from_digit((b >> 4) as u32, 16).expect("nibble is 0..16"));
        out.push(char::from_digit((b & 0x0f) as u32, 16).expect("nibble is 0..16"));
    }
    out
}

/// The inverse of [`hex_encode`]: `[0-9a-f]*` → the original string. `None` for an odd length, a
/// non-hex digit, or bytes that are not valid UTF-8 (a malformed / non-ours text segment).
fn hex_decode(h: &str) -> Option<String> {
    let bytes = h.as_bytes();
    if bytes.len() % 2 != 0 {
        return None;
    }
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        let hi = (pair[0] as char).to_digit(16)?;
        let lo = (pair[1] as char).to_digit(16)?;
        out.push(((hi << 4) | lo) as u8);
    }
    String::from_utf8(out).ok()
}

/// Encode an affordance `{turn, arg}` **plus an optional free-text payload** into the id
/// `transport` carries it on. The text-free path is byte-identical to [`affordance_id`]:
///
/// - `text == None` → exactly `affordance_id(turn, arg, transport)` (no trailing segment).
/// - `text == Some(t)` → that same base id, then [`TEXT_SEP`], then the hex of `t`.
///
/// The inverse of [`parse_affordance_id_with_text`] for the same `transport`.
pub fn affordance_id_with_text(
    turn: &str,
    arg: i64,
    text: Option<&str>,
    transport: AffordanceTransport,
) -> String {
    let base = affordance_id(turn, arg, transport);
    match text {
        None => base,
        Some(t) => format!("{base}{TEXT_SEP}{}", hex_encode(t)),
    }
}

/// Decode an id minted by [`affordance_id_with_text`] for the same `transport` back into
/// `(turn, arg, Option<text>)`. A text-free id (no [`TEXT_SEP`]) yields `text = None` and decodes
/// exactly as [`parse_affordance_id`] — so this is a strict superset of the plain decoder, safe to
/// point at any affordance id. `None` for an id that is not one of ours for that transport, or
/// whose text segment is malformed (odd-length / non-hex / non-UTF-8).
///
/// The text segment is hex (no [`TEXT_SEP`] in its alphabet), so the split takes the LAST
/// [`TEXT_SEP`]: everything after it is the text, everything before is the base id (which is then
/// parsed by the unchanged [`parse_affordance_id`]).
pub fn parse_affordance_id_with_text(
    id: &str,
    transport: AffordanceTransport,
) -> Option<(String, i64, Option<String>)> {
    match id.rsplit_once(TEXT_SEP) {
        Some((base, hex)) => {
            let text = hex_decode(hex)?;
            let (turn, arg) = parse_affordance_id(base, transport)?;
            Some((turn, arg, Some(text)))
        }
        None => {
            let (turn, arg) = parse_affordance_id(id, transport)?;
            Some((turn, arg, None))
        }
    }
}

/// **The POSITIONAL half of the WeChat codec** — a reply's text → the **1-based index** of the
/// affordance it names in the presented numbered list. Takes the leading run of ASCII digits (so
/// `"2"`, `"2."` and `"2 trade blows"` all resolve to `2`), so a user can reply with just the
/// number. `None` if the reply has no leading digit, or names index `0` (there is no 0th affordance —
/// the list is 1-based).
///
/// A position is NOT an affordance id: it names a SLOT in the list the surface last presented, so it
/// is resolved against that list ([`crate::wechat::WeChatMessage::resolve`]), which then yields the
/// `{turn, arg}` (whose id is the `#<turn>:<arg>` the option carries). This mirrors the live OA loop
/// (`dreggnet_wechat::api::parse_reply_index`) exactly.
pub fn wechat_reply_index(reply: &str) -> Option<usize> {
    let digits: String = reply
        .trim()
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    let n: usize = digits.parse().ok()?;
    if n == 0 {
        None
    } else {
        Some(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL: [AffordanceTransport; 4] = [
        AffordanceTransport::Discord,
        AffordanceTransport::Telegram,
        AffordanceTransport::Web,
        AffordanceTransport::WeChat,
    ];

    /// The one codec round-trips `encode → decode` for EVERY transport (the move-#1 property).
    #[test]
    fn round_trips_every_transport() {
        for t in ALL {
            for (turn, arg) in [
                ("inc", 7i64),
                ("choose", 0),
                ("bump", -1),
                ("trade_blows", 999),
            ] {
                let id = affordance_id(turn, arg, t);
                assert_eq!(
                    parse_affordance_id(&id, t),
                    Some((turn.to_string(), arg)),
                    "{t:?} round-trips {turn}/{arg} via {id}"
                );
            }
        }
    }

    /// A **text-bearing** affordance round-trips turn + arg + text through EVERY transport, and
    /// the text-free path stays byte-identical to the plain codec (the additive-non-breaking
    /// tooth). The text deliberately carries `:`, the WeChat `#`, unicode, and an empty case — the
    /// hex segment carries them all opaquely, never confused with the `{turn, arg}` shape.
    #[test]
    fn text_bearing_round_trips_and_text_free_is_byte_identical() {
        let texts = [
            "the dragon's hoard glittered",
            "a:b:c with #marks and 世界 :)",
            "",
            "deosturn:looks:like:an:id",
        ];
        for t in ALL {
            // TEXT-FREE is byte-identical to the plain encoder AND decoder (the invariant).
            for (turn, arg) in [("insert", 3i64), ("prompt", 0), ("choose", -1)] {
                assert_eq!(
                    affordance_id_with_text(turn, arg, None, t),
                    affordance_id(turn, arg, t),
                    "{t:?} text-free encode is byte-identical",
                );
                let plain = affordance_id(turn, arg, t);
                assert_eq!(
                    parse_affordance_id_with_text(&plain, t),
                    Some((turn.to_string(), arg, None)),
                    "{t:?} a plain id decodes with text: None",
                );
                // The plain decoder still sees the plain id unchanged (no regression).
                assert_eq!(
                    parse_affordance_id(&plain, t),
                    Some((turn.to_string(), arg)),
                );
            }
            // TEXT-BEARING carries turn + arg + text losslessly.
            for text in texts {
                let id = affordance_id_with_text("insert", 7, Some(text), t);
                assert_eq!(
                    parse_affordance_id_with_text(&id, t),
                    Some(("insert".to_string(), 7, Some(text.to_string()))),
                    "{t:?} carries {text:?} losslessly beside turn+arg",
                );
            }
        }
    }

    /// The Discord transport is prefixed; the un-prefixed transports are not (the shapes the four
    /// old encodings used).
    #[test]
    fn transport_byte_shapes() {
        assert_eq!(
            affordance_id("inc", 7, AffordanceTransport::Discord),
            "deosturn:inc:7"
        );
        assert_eq!(
            affordance_id("inc", 7, AffordanceTransport::Telegram),
            "inc:7"
        );
        assert_eq!(affordance_id("inc", 7, AffordanceTransport::Web), "inc:7");
        assert_eq!(
            affordance_id("inc", 7, AffordanceTransport::WeChat),
            "#inc:7"
        );
    }

    /// WeChat's inbound channel is FREE USER TEXT — so an UNMARKED string is never one of ours
    /// (a user typing `vote:1` in chat has not fired an affordance), and a BARE NUMBER is a
    /// POSITION in the presented list, not an id (it cannot name a `{turn, arg}` by itself).
    #[test]
    fn wechat_id_is_marked_and_a_bare_number_is_not_an_id() {
        // Unmarked prose that happens to have the un-prefixed shape: NOT ours.
        assert_eq!(
            parse_affordance_id("vote:1", AffordanceTransport::WeChat),
            None
        );
        // The user's numbered reply: a POSITION, not an id.
        assert_eq!(parse_affordance_id("2", AffordanceTransport::WeChat), None);
        // The marked id the numbered option carries: ours.
        assert_eq!(
            parse_affordance_id("#vote:1", AffordanceTransport::WeChat),
            Some(("vote".to_string(), 1))
        );
        // Malformed (marked but no arg) → None.
        assert_eq!(
            parse_affordance_id("#vote", AffordanceTransport::WeChat),
            None
        );
    }

    /// The POSITIONAL half: a reply's leading digits → the 1-based index of the numbered option
    /// (`"2"`, `"2."`, `"2 trade blows"` all resolve to 2); no leading digit / index 0 → `None`.
    /// The round-trip over the presented list is `wechat_reply_index(&format!("{n}. {label}")) == n`.
    #[test]
    fn wechat_reply_index_takes_the_leading_number() {
        assert_eq!(wechat_reply_index("2"), Some(2));
        assert_eq!(wechat_reply_index("2."), Some(2));
        assert_eq!(wechat_reply_index(" 2 trade blows "), Some(2));
        assert_eq!(wechat_reply_index("10. flee"), Some(10));
        assert_eq!(wechat_reply_index("0"), None, "the list is 1-based");
        assert_eq!(
            wechat_reply_index("hello"),
            None,
            "ordinary prose is not a pick"
        );
        assert_eq!(wechat_reply_index(""), None);
        // The presented line round-trips to its own position.
        for (n, label) in [(1usize, "Vote"), (2, "Pass"), (11, "Flee")] {
            assert_eq!(wechat_reply_index(&format!("{n}. {label}")), Some(n));
        }
    }

    /// A Discord id lacking the `deosturn:` prefix is "not ours" → `None` (the bot's component
    /// handler ignores foreign component ids).
    #[test]
    fn discord_rejects_a_foreign_id() {
        assert_eq!(
            parse_affordance_id("deos:abcd:approve", AffordanceTransport::Discord),
            None
        );
        assert_eq!(
            parse_affordance_id("other:thing", AffordanceTransport::Discord),
            None
        );
    }

    /// The un-prefixed transports split on the LAST separator (an arg stays unambiguous even if a
    /// turn contained an earlier one).
    #[test]
    fn unprefixed_splits_on_last_separator() {
        assert_eq!(
            parse_affordance_id("a:b:3", AffordanceTransport::Telegram),
            Some(("a:b".to_string(), 3))
        );
        assert_eq!(parse_affordance_id("noarg", AffordanceTransport::Web), None);
    }
}
