//! # THE PAGE — the mirror's chrome around `deos-view`'s card.
//!
//! Division of labour, deliberately: **`deos-view` renders the object**
//! ([`deos_view::web::render_html`] over the object's own view-tree, styled by
//! [`deos_view::web::portal_css`]), so the mirror paints the SAME surface every other glass
//! paints and no card markup is authored by hand here. **This module renders only the
//! chrome** — the trust block, the upgrade path, the gate disclosure, the ladder, and the
//! error pages.
//!
//! ## THE AFFORDANCES ARE INERT, NATIVELY
//!
//! `render_html` emits real `<button data-turn=…>` controls, because they are real
//! affordances of the object. On this surface there is no executor to fire them at, so the
//! card is wrapped in a `<fieldset disabled>`: the browser itself disables every descendant
//! control, with no script and no DOM surgery. The mirror deliberately does NOT ship
//! `deos-view`'s in-tab affordance wire — a live-looking button over a missing executor is
//! a lie in a different costume, and the page says so out loud
//! ([`crate::trust::INERT_NOTE`]).

use deos_view::tree::ViewNode;

use crate::object::{GateOutcome, VerifyReport};
use crate::trust;
use crate::uri::{self, Kind};

/// Everything the page needs about the serving deployment.
#[derive(Debug, Clone)]
pub struct PageConfig {
    /// The public origin this mirror is reached at, e.g. `dregg.gg`. Substituted into
    /// §5's badge and named in the trust block — the reader is told who they are trusting
    /// BY NAME.
    pub origin: String,
    /// Where a reader gets the extension (the tier-`extension` upgrade path).
    pub extension_url: String,
}

impl Default for PageConfig {
    fn default() -> PageConfig {
        PageConfig {
            origin: "dregg.gg".into(),
            extension_url: "https://dregg.gg/extension".into(),
        }
    }
}

/// Reduce whatever an operator wrote to the bare HOST the pages need.
///
/// `origin` is not cosmetics: it is printed as the party the reader is trusting
/// ("dregg.gg checked this object. You did not.") and it is the authority of every mirror
/// URL the page emits. So a deployment that sets `https://dregg.gg/` — which reads as the
/// obviously-correct value, and is exactly what `deploy/edge/compose/docker-compose.yml`
/// wrote — must not produce `✓ verified by https://dregg.gg/ (trust the origin)` and links
/// of the form `https://https://dregg.gg//poll/…`. Both forms normalize here rather than
/// making the operator guess which one this crate wanted.
pub fn normalize_origin(origin: &str) -> String {
    // Lower-case FIRST (a host is case-insensitive), so the scheme strip below is not
    // defeated by an operator who wrote `HTTPS://`.
    let s = origin.trim().to_ascii_lowercase();
    let s = s
        .strip_prefix("https://")
        .or_else(|| s.strip_prefix("http://"))
        .unwrap_or(&s);
    // Keep any `host:port` (a local smoke test is reached at `localhost:8791`), drop a
    // path/query the operator may have pasted along.
    s.split(['/', '?', '#'])
        .next()
        .unwrap_or(s)
        .trim()
        .to_string()
}

/// Render the resolved-object page: the object's own view-tree, under the tier-`server`
/// label and the upgrade path.
pub fn object_page(
    cfg: &PageConfig,
    kind: Kind,
    addr_hex: &str,
    title: &str,
    note: Option<&str>,
    tree: &ViewNode,
    binds: &[u64],
    report: &VerifyReport,
) -> String {
    let canonical = trust::canonical_for(kind.as_str(), addr_hex);
    let card = deos_view::web::render_html(tree, binds);
    let note_html = note
        .map(|n| format!("<p class=\"mirror-note\">{}</p>", esc(n)))
        .unwrap_or_default();

    let body = format!(
        "<header class=\"mirror-head\">\
           <div class=\"{badge_class}\">{badge}</div>\
           <h1>{title}</h1>\
           <p class=\"mirror-kindline\">a dregg <code>{kind}</code> · \
             <span class=\"mirror-addr\">{short}</span></p>\
         </header>\
         {trust_block}\
         {note}\
         <p class=\"mirror-inert-note\">{inert}</p>\
         <fieldset class=\"mirror-inert\" disabled>\
           <legend>the object</legend>\
           <div class=\"deos-card\">{card}</div>\
         </fieldset>\
         {upgrade}\
         {gates}\
         {ladder}",
        badge_class = trust::BADGE_CLASS,
        badge = esc(&trust::tier_badge(&cfg.origin)),
        title = esc(title),
        kind = kind,
        short = esc(&short_addr(addr_hex)),
        trust_block = trust_block(cfg),
        note = note_html,
        inert = trust::INERT_NOTE,
        card = card,
        upgrade = upgrade_block(cfg, &canonical, kind, addr_hex),
        gates = gate_block(report),
        ladder = ladder_block(),
    );
    document(&format!("{title} — dregg mirror"), trust::TIER, &body)
}

/// Render a fail-closed page. NEVER renders the object; shows the tier-`none` badge, the
/// honest reason, and (when there is one) the canonical reference so the reader can still
/// take the reference somewhere that can serve it.
pub fn error_page(
    cfg: &PageConfig,
    status_headline: &str,
    reason_html: &str,
    canonical: Option<&str>,
    detail: Option<&str>,
) -> String {
    let canonical_block = canonical
        .map(|c| {
            format!(
                "<section class=\"mirror-block\">\
                   <h2>The reference</h2>\
                   <p>This is what the link named. It is a reference, not a promise that \
                      anything answers it.</p>\
                   {copy}\
                 </section>",
                copy = copy_field("canonical reference", c)
            )
        })
        .unwrap_or_default();
    let detail_block = detail
        .map(|d| format!("<pre class=\"mirror-detail\">{}</pre>", esc(d)))
        .unwrap_or_default();

    let body = format!(
        "<header class=\"mirror-head\">\
           <div class=\"tier-badge tier-none\">{badge}</div>\
           <h1>{headline}</h1>\
         </header>\
         <section class=\"mirror-block mirror-refusal\">\
           <h2>Why you are seeing this</h2>\
           <p>{reason}</p>\
           {detail}\
           <p class=\"mirror-failclosed\">This mirror fails closed: when a reference does \
              not resolve, or the bytes served for it do not hash to the address in the \
              link, it shows you this instead of a guess. There is no partial render and \
              no optimistic default.</p>\
         </section>\
         {canonical_block}\
         {upgrade_min}\
         {ladder}",
        badge = esc(trust::TIER_NONE_BADGE),
        headline = esc(status_headline),
        reason = reason_html,
        detail = detail_block,
        canonical_block = canonical_block,
        upgrade_min = minimal_upgrade_block(cfg),
        ladder = ladder_block(),
    );
    document(&format!("{status_headline} — dregg mirror"), "none", &body)
}

/// The index page: what this service is, and the kinds it will render.
pub fn index_page(cfg: &PageConfig, counts: &[(Kind, usize)]) -> String {
    let rows: String = counts
        .iter()
        .map(|(k, n)| {
            format!(
                "<tr><td><code>{k}</code></td><td>{d}</td><td class=\"num\">{n}</td></tr>",
                k = k,
                d = esc(k.describe()),
                n = n
            )
        })
        .collect();

    let body = format!(
        "<header class=\"mirror-head\">\
           <div class=\"{badge_class}\">{badge}</div>\
           <h1>dregg mirror</h1>\
           <p class=\"mirror-kindline\">the no-extension view of a <code>dregg://</code> object</p>\
         </header>\
         <section class=\"mirror-block\">\
           <h2>What this is</h2>\
           <p>A <code>dregg://</code> object is content-addressed: the address in the link \
              <em>is</em> the hash of the object, so no platform carrying the link can forge \
              what it points at. Someone posted such a reference and you clicked it without \
              the extension installed, so this server resolved it and rendered it for you.</p>\
           <p>That makes this the weakest rung of the ladder. The rendering is real; the \
              <em>trust</em> is in {origin}, not in anything you checked. Every object page \
              here says so, prints the checks it ran, and hands you the canonical reference \
              so you can go check it yourself.</p>\
         </section>\
         <section class=\"mirror-block\">\
           <h2>Link shape</h2>\
           <p><code>https://{origin}/&lt;kind&gt;/&lt;address&gt;</code> — and a short \
              address works, git-style. <code>https://{origin}/poll/7f2a9c4d</code> resolves \
              as long as that prefix is unambiguous, which is what lets the whole reference \
              survive being truncated in a post. An ambiguous prefix is refused, never \
              guessed. <code>/d/&lt;kind&gt;/&lt;address&gt;</code> also works — that is the \
              form the original spec published.</p>\
         </section>\
         <section class=\"mirror-block\">\
           <h2>Kinds this mirror renders</h2>\
           <table class=\"mirror-table\"><thead><tr><th>kind</th><th>what it is</th>\
             <th class=\"num\">held</th></tr></thead><tbody>{rows}</tbody></table>\
           <p class=\"mirror-fine\">A kind not on this list is a 404. This mirror does not \
              guess a renderer for a name it does not know.</p>\
         </section>\
         {upgrade_min}\
         {ladder}",
        badge_class = trust::BADGE_CLASS,
        badge = esc(&trust::tier_badge(&cfg.origin)),
        origin = esc(&cfg.origin),
        rows = rows,
        upgrade_min = minimal_upgrade_block(cfg),
        ladder = ladder_block(),
    );
    document("dregg mirror", trust::TIER, &body)
}

// ── the blocks ───────────────────────────────────────────────────────────────

fn trust_block(cfg: &PageConfig) -> String {
    format!(
        "<section class=\"mirror-block mirror-trust\">\
           <h2>{heading}</h2>\
           <p>{body}</p>\
         </section>",
        heading = esc(trust::WHO_CHECKED_HEADING),
        body = trust::who_checked_body(&esc(&cfg.origin)),
    )
}

fn upgrade_block(cfg: &PageConfig, canonical: &str, kind: Kind, addr_hex: &str) -> String {
    format!(
        "<section class=\"mirror-block mirror-upgrade\">\
           <h2>{heading}</h2>\
           <p>{body}</p>\
           {copy}\
           <p class=\"mirror-fine\">Full mirror link (unambiguous, never a prefix): \
              <code>{full}</code></p>\
           <p><a class=\"mirror-cta\" href=\"{ext}\" rel=\"noopener\">Get the extension</a></p>\
         </section>",
        heading = esc(trust::UPGRADE_HEADING),
        body = trust::UPGRADE_BODY,
        copy = copy_field("canonical reference", canonical),
        full = esc(&uri::mirror_url(&cfg.origin, kind.as_str(), addr_hex)),
        ext = esc(&cfg.extension_url),
    )
}

fn minimal_upgrade_block(cfg: &PageConfig) -> String {
    format!(
        "<section class=\"mirror-block mirror-upgrade\">\
           <h2>{heading}</h2>\
           <p>{body}</p>\
           <p><a class=\"mirror-cta\" href=\"{ext}\" rel=\"noopener\">Get the extension</a></p>\
         </section>",
        heading = esc(trust::UPGRADE_HEADING),
        body = trust::UPGRADE_BODY,
        ext = esc(&cfg.extension_url),
    )
}

/// The gate disclosure — what the origin says it checked, gate by gate, including the
/// gates it SKIPPED and why. A skip is printed as loudly as a pass; that is the whole
/// point of printing the ladder instead of collapsing it into one badge.
fn gate_block(report: &VerifyReport) -> String {
    let rows: String = report
        .gates
        .iter()
        .map(|(g, o)| {
            let (cls, mark, detail) = match o {
                GateOutcome::Passed(d) => ("gate-pass", "checked", d.as_str()),
                GateOutcome::Skipped(d) => ("gate-skip", "NOT CHECKED", d.as_str()),
                GateOutcome::Failed(d) => ("gate-fail", "REFUSED", d.as_str()),
            };
            format!(
                "<tr class=\"{cls}\"><td class=\"gate-mark\">{mark}</td>\
                 <td>{label}</td><td class=\"gate-detail\"><code>{detail}</code></td></tr>",
                cls = cls,
                mark = mark,
                label = esc(g.label()),
                detail = esc(detail)
            )
        })
        .collect();
    let caption = if report.attested() {
        "The origin ran the full ladder — content address, serve-receipt, stream root, \
         quorum. You are reading its report of that, not the result of your own check."
    } else {
        "The origin ran the content-address gate. The federation attestation gates did NOT \
         run — this object carried no attestation, and a gate that did not run is shown as \
         not checked rather than quietly folded into a pass."
    };
    format!(
        "<section class=\"mirror-block mirror-gates\">\
           <h2>What the origin checked</h2>\
           <p>{caption}</p>\
           <table class=\"mirror-table gate-table\"><tbody>{rows}</tbody></table>\
         </section>",
        caption = caption,
        rows = rows
    )
}

fn ladder_block() -> String {
    let rows: String = trust::LADDER
        .iter()
        .map(|r| {
            let here = r.person_has.contains("YOU ARE HERE");
            format!(
                "<tr class=\"{cls}\"><td><code>{tier}</code></td><td>{has}</td>\
                 <td>{sees}</td><td class=\"ladder-badge\">{badge}</td></tr>",
                cls = if here { "ladder-here" } else { "" },
                tier = esc(r.tier),
                has = esc(r.person_has),
                sees = esc(r.sees),
                badge = esc(r.badge),
            )
        })
        .collect();
    format!(
        "<section class=\"mirror-block mirror-ladder\">\
           <h2>Where this page sits</h2>\
           <table class=\"mirror-table\"><thead><tr><th>tier</th><th>you have</th>\
             <th>you see</th><th>the badge says</th></tr></thead><tbody>{rows}</tbody></table>\
         </section>",
        rows = rows
    )
}

/// A read-only field a reader copies out of. No script: `readonly` + `onfocus`-free, the
/// browser's own select-all-on-click is enough and a copy button would need JS this page
/// deliberately does not ship.
fn copy_field(label: &str, value: &str) -> String {
    format!(
        "<label class=\"mirror-copy\"><span>{label}</span>\
         <input type=\"text\" readonly value=\"{value}\" \
           onclick=\"this.select()\" spellcheck=\"false\"></label>",
        label = esc(label),
        value = esc(value)
    )
}

/// The document shell. `data-trust` mirrors the element's reflected `trust=` attribute
/// (§5) so the tier is machine-readable on this surface too, not merely painted.
fn document(title: &str, tier: &str, body: &str) -> String {
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<meta name=\"referrer\" content=\"strict-origin-when-cross-origin\">\n\
<title>{title}</title>\n\
<style>{card_css}{mirror_css}</style>\n\
</head>\n\
<body>\n\
<main class=\"mirror\" data-trust=\"{tier}\">{body}</main>\n\
</body>\n\
</html>\n",
        title = esc(title),
        card_css = deos_view::web::portal_css(),
        mirror_css = MIRROR_CSS,
        tier = esc(tier),
        body = body,
    )
}

/// HTML-escape text content and attribute values.
pub fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

/// A display form of a full address: the first 12 hex, which is what a short link would
/// carry, followed by the tail so the full value is still on the page.
fn short_addr(addr_hex: &str) -> String {
    if addr_hex.len() <= 20 {
        return format!("{}{addr_hex}", uri::ADDR_TAG);
    }
    format!(
        "{}{}…{}",
        uri::ADDR_TAG,
        &addr_hex[..12],
        &addr_hex[addr_hex.len() - 4..]
    )
}

/// The mirror's own chrome styling. Rides ON TOP of `deos_view::web::portal_css` (the card
/// palette), so the object looks like it does everywhere else and only the chrome is ours.
///
/// The tier colours are load-bearing, not decoration: `--tier-server` is amber and
/// `tier-extension`'s green is never applied to this page's own badge. A person who has
/// learned "green = my agent checked it" must not be taught otherwise here.
const MIRROR_CSS: &str = "
:root{--tier-server:#f2c94c;--tier-server-ink:#2a2005;--tier-none:#f8737f;--tier-ext:#48d597;}
body{display:block;padding:0;}
.mirror{max-width:44rem;margin:0 auto;padding:2rem 1.15rem 4rem;display:flex;flex-direction:column;gap:1.05rem;}
.mirror-head{display:flex;flex-direction:column;gap:.5rem;}
.mirror h1{margin:0;font-size:1.55rem;line-height:1.25;letter-spacing:-.01em;}
.mirror h2{margin:0 0 .45rem;font-size:.74rem;letter-spacing:.09em;text-transform:uppercase;color:var(--head);}
.mirror p{margin:0 0 .6rem;}
.mirror p:last-child{margin-bottom:0;}
.mirror code{font-family:ui-monospace,Menlo,monospace;font-size:.86em;color:var(--fg);word-break:break-all;}
.tier-badge{align-self:flex-start;display:inline-block;padding:.3rem .7rem;border-radius:999px;font-size:.76rem;font-weight:800;letter-spacing:.02em;border:1px solid transparent;}
.tier-badge.tier-server{background:var(--tier-server);color:var(--tier-server-ink);border-color:#c9a12f;}
.tier-badge.tier-none{background:var(--tier-none);color:#26070a;border-color:#c9525c;}
.tier-badge.tier-cipherclerk{background:none;color:var(--tier-ext);border-color:var(--tier-ext);padding:.05rem .45rem;font-size:.78em;}
.mirror-kindline{color:var(--muted);font-size:.9rem;}
.mirror-addr{font-family:ui-monospace,Menlo,monospace;}
.mirror-block{border:1px solid var(--border);border-radius:11px;padding:.85rem 1rem;background:var(--panel);}
.mirror-trust{border-color:#7a6320;background:rgba(242,201,76,.07);}
.mirror-refusal{border-color:#8d3a41;background:rgba(248,115,127,.07);}
.mirror-note{color:var(--muted);font-style:italic;}
.mirror-inert-note{color:var(--muted);font-size:.87rem;}
.mirror-inert{border:1px dashed var(--border);border-radius:12px;padding:.2rem .55rem .75rem;margin:0;min-width:0;}
.mirror-inert legend{color:var(--muted);font-size:.68rem;letter-spacing:.1em;text-transform:uppercase;padding:0 .4rem;}
.mirror-inert .deos-card{max-width:none;}
.mirror-inert .deos-button,.mirror-inert button{opacity:.5;cursor:not-allowed;filter:grayscale(.5);}
.mirror-copy{display:flex;flex-direction:column;gap:.25rem;margin:.55rem 0;}
.mirror-copy span{font-size:.7rem;letter-spacing:.08em;text-transform:uppercase;color:var(--muted);}
.mirror-copy input{width:100%;padding:.5rem .65rem;border:1px solid var(--border);border-radius:8px;background:#0a1224;color:var(--fg);font-family:ui-monospace,Menlo,monospace;font-size:.85rem;}
.mirror-cta{display:inline-block;margin-top:.35rem;padding:.42rem .9rem;border-radius:8px;background:var(--accent);color:var(--accent-ink);font-weight:800;text-decoration:none;font-size:.88rem;}
.mirror-fine{color:var(--muted);font-size:.82rem;}
.mirror-failclosed{color:var(--muted);font-size:.85rem;}
.mirror-detail{margin:.4rem 0;padding:.5rem .65rem;border:1px solid var(--border);border-radius:8px;background:#0a1224;color:var(--muted);font-size:.8rem;overflow-x:auto;white-space:pre-wrap;word-break:break-all;}
.mirror-table{width:100%;border-collapse:collapse;font-size:.85rem;display:block;overflow-x:auto;}
.mirror-table th{text-align:left;font-size:.68rem;letter-spacing:.08em;text-transform:uppercase;color:var(--muted);font-weight:700;padding:.3rem .5rem;border-bottom:1px solid var(--border);}
.mirror-table td{padding:.4rem .5rem;border-bottom:1px solid rgba(255,255,255,.05);vertical-align:top;}
.mirror-table td.num{text-align:right;font-variant-numeric:tabular-nums;}
.ladder-here{background:rgba(242,201,76,.1);}
.ladder-here td{font-weight:700;}
.ladder-badge{color:var(--muted);}
.gate-table td.gate-mark{font-size:.68rem;letter-spacing:.07em;font-weight:800;white-space:nowrap;}
.gate-pass td.gate-mark{color:var(--good);}
.gate-skip td.gate-mark{color:var(--warn);}
.gate-fail td.gate-mark{color:var(--bad);}
.gate-detail code{color:var(--muted);font-size:.78rem;}
@media (max-width:34rem){.mirror{padding:1.2rem .8rem 3rem;}.mirror h1{font-size:1.3rem;}}
";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_addr_keeps_both_ends() {
        let a = "0123456789abcdef".repeat(4);
        let s = short_addr(&a);
        assert!(s.starts_with("b3_012345678"));
        assert!(s.ends_with("cdef"));
    }

    #[test]
    fn an_origin_written_as_a_url_still_names_a_host() {
        for written in [
            "dregg.gg",
            "https://dregg.gg",
            "http://dregg.gg/",
            " HTTPS://Dregg.GG/ ",
        ] {
            assert_eq!(normalize_origin(written), "dregg.gg", "{written:?}");
        }
        // A host:port survives — a local smoke test is reached at one.
        assert_eq!(normalize_origin("http://localhost:8791"), "localhost:8791");
    }

    #[test]
    fn escaping_closes_the_attribute_and_the_tag() {
        let e = esc("\"><script>x</script>");
        assert!(!e.contains('<'));
        assert!(!e.contains('"'));
    }
}
