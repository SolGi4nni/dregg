//! Explorer reference building — the `DREGG_EXPLORER_BASE` pattern, shared.
//!
//! One rule for every surface: with `DREGG_EXPLORER_BASE` configured (e.g.
//! `https://explorer.dregg.net`, trailing slash tolerated) a reference links into
//! `{base}/explorer/{kind}/{id}`; with no base configured it renders as plain
//! copyable code — NEVER a dead link. `cards.rs` established the pattern (the old
//! hardcoded `devnet.dregg.fg-goose.online` no longer routes anywhere); this module
//! is its shared home for the hand-rolled embeds.
//!
//! The no-base fallbacks always carry the FULL id: a truncated hash whose only
//! escape is a link is a dead end when the link is absent — the advertised
//! verify-a-receipt workflow must complete by copy-paste alone.

/// The explorer base URL — `DREGG_EXPLORER_BASE`, trimmed, trailing slash dropped.
/// `None` (the default) means: render plain copyable text, never a dead link.
pub fn explorer_base() -> Option<String> {
    std::env::var("DREGG_EXPLORER_BASE")
        .ok()
        .map(|s| s.trim().trim_end_matches('/').to_string())
        .filter(|s| !s.is_empty())
}

/// The full explorer URL for `kind`/`id`, when a base is configured.
pub fn explorer_url(kind: &str, id: &str) -> Option<String> {
    explorer_base().map(|b| url_with_base(&b, kind, id))
}

/// A `[label](url)` markdown link when a base is configured; the full id as a
/// copyable code span otherwise.
pub fn view_link(kind: &str, id: &str, label: &str) -> String {
    view_link_with_base(explorer_base().as_deref(), kind, id, label)
}

/// A shortened `` [`id...`](url) `` code-span link when a base is configured; the
/// FULL id as a plain code span otherwise (copy-paste must still work).
pub fn short_ref(kind: &str, id: &str, short_len: usize) -> String {
    short_ref_with_base(explorer_base().as_deref(), kind, id, short_len)
}

/// A receipt/reference field value: the explorer link (when configured) PLUS the
/// full id in a copyable code block — the block is the always-works escape hatch.
pub fn receipt_field(kind: &str, id: &str, label: &str) -> String {
    receipt_field_with_base(explorer_base().as_deref(), kind, id, label)
}

// ─── pure cores (base explicit — what the tests drive; env reads stay above) ──

fn url_with_base(base: &str, kind: &str, id: &str) -> String {
    format!("{base}/explorer/{kind}/{id}")
}

fn view_link_with_base(base: Option<&str>, kind: &str, id: &str, label: &str) -> String {
    match base {
        Some(b) => format!("[{label}]({})", url_with_base(b, kind, id)),
        None => format!("`{id}`"),
    }
}

/// [`short_ref`]'s pure core, base explicit — for callers (and tests) that thread
/// the base themselves (e.g. `cards.rs`' card builders).
pub(crate) fn short_ref_with_base(
    base: Option<&str>,
    kind: &str,
    id: &str,
    short_len: usize,
) -> String {
    match base {
        Some(b) => {
            let short = if id.len() > short_len {
                &id[..short_len]
            } else {
                id
            };
            format!("[`{short}...`]({})", url_with_base(b, kind, id))
        }
        None => format!("`{id}`"),
    }
}

fn receipt_field_with_base(base: Option<&str>, kind: &str, id: &str, label: &str) -> String {
    match base {
        Some(b) => format!("[{label}]({})\n```\n{id}\n```", url_with_base(b, kind, id)),
        None => format!("```\n{id}\n```"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const HASH: &str = "abcdef0123456789abcdef0123456789";

    #[test]
    fn with_base_links_and_never_mentions_fg_goose() {
        let base = Some("https://explorer.dregg.net");
        for s in [
            view_link_with_base(base, "turn", HASH, "View"),
            short_ref_with_base(base, "tx", HASH, 12),
            receipt_field_with_base(base, "turn", HASH, "view on explorer"),
        ] {
            assert!(s.contains("https://explorer.dregg.net/explorer/"), "{s}");
            assert!(s.contains(HASH), "full id must ride in the URL: {s}");
            assert!(!s.contains("fg-goose"), "{s}");
        }
    }

    #[test]
    fn without_base_no_link_and_full_id_is_copyable() {
        for s in [
            view_link_with_base(None, "turn", HASH, "View"),
            short_ref_with_base(None, "tx", HASH, 12),
            receipt_field_with_base(None, "turn", HASH, "view on explorer"),
        ] {
            assert!(!s.contains("]("), "must not be a (dead) link: {s}");
            assert!(s.contains(HASH), "FULL id must survive with no base: {s}");
        }
    }

    #[test]
    fn receipt_field_always_has_a_copyable_code_block() {
        assert!(
            receipt_field_with_base(Some("https://x.example"), "turn", HASH, "v")
                .contains(&format!("```\n{HASH}\n```"))
        );
        assert!(
            receipt_field_with_base(None, "turn", HASH, "v").contains(&format!("```\n{HASH}\n```"))
        );
    }

    #[test]
    fn short_ref_truncates_display_only() {
        let s = short_ref_with_base(Some("https://x.example"), "tx", HASH, 12);
        assert!(s.contains("[`abcdef012345...`]"), "{s}");
        assert!(s.ends_with(&format!("/explorer/tx/{HASH})")), "{s}");
    }
}
