//! # The LIVE reactive transclusion — Ted Nelson's "live quote", made runnable.
//!
//! `Dregg2.Deos.Transclusion` PROVES the four Xanadu properties and
//! `starbridge-web-surface`'s [`TranscludedField`] REALIZES them over the real
//! `dregg://` attested fetch. This module is the **runnable demo** the proof+types
//! were missing: a Leptos surface with TWO cells and a **live quote** between them.
//!
//! ## The two cells + the live quote
//!
//! - a **SOURCE cell** — a `constitution` cell carrying a `threshold` field (the
//!   quorum a proposal must clear). It is a genuine `dregg://constitution` origin in
//!   a real [`WebOfCells`]: its threshold is committed content (the bytes the serve
//!   ships), attested by a 3-of-3 quorum — a real finalized read source.
//! - a **TRANSCLUDING surface** — a `council` page that **transcludes** the
//!   constitution's `threshold` as a LIVE quote via the REAL
//!   [`TranscludedField::include`] (the verified cross-cell finalized read). The
//!   quote renders the value + its **provenance** (`transcluded from
//!   dregg://constitution @ height H, receipt …`) + its **backlinks** (`N surfaces
//!   quote me`, the witness-graph rendered the other way).
//!
//! ## THE PAYOFF — the live update (the unbreakable + LIVE Nelson link)
//!
//! When a turn fires on the SOURCE (the constitution is **amended** —
//! [`WebOfCells::amend`], a genuine state advance: re-commit the threshold into the
//! same origin cell, bump its nonce, advance the attested height), the transcluded
//! quote **UPDATES reactively**: the Leptos quote [`Memo`] re-resolves
//! [`TranscludedField::include`] against the advanced source and reports the NEW
//! committed/finalized value at a NEW provenance height — **not** a frozen copy. The
//! `dregg://` ref is UNCHANGED (same content-addressed cell), exactly Nelson's
//! unbreakable link: the citation still resolves, now to the source's new value.
//!
//! ## The anti-forge tooth, made visible
//!
//! A FORGED quote (a tampered [`AttestedResource`] whose bytes no longer match the
//! committed `content_hash`) fails [`AttestedResource::verify`] — so it does NOT
//! render as a verified quote ([`LiveQuote::try_resolve`] returns the precise
//! [`TransclusionError`], and the view shows a refusal, never the forged bytes). No
//! opened provenance ⇒ no quote (`transclusion_forge_refused`).
//!
//! ## Honest scope (a proof+types is not a demo; this is the demo)
//!
//! - **Runnable + proven (no browser):** the SSR render of the council page (the
//!   value, the live quote, the provenance line, the backlinks) AND the reactive
//!   sequence — render (quote shows V) → amend the source → re-render (quote shows
//!   V', the provenance height advanced). That sequence ([`live_quote_sequence`]) IS
//!   the demo's proof, exercised by the tests and printed by `cargo run`.
//! - **Needs a browser to fully appreciate:** the in-page hydrated live update (the
//!   amend button press re-rendering the quote without a reload). The reactive graph
//!   ([`CouncilTransclusionView`]) is the same `RwSignal`/`Memo` graph a hydrate
//!   build ships; the SSR sequence proves its behaviour headlessly.
//! - **Named follow-on (the deos seam):** in-browser WASM hydration of THIS surface.
//!   The `dregg://` fetch + attestation verify sit atop native crypto
//!   (`blake3`/the attested-root stack the executor shares), so — exactly as the
//!   council vote's executor — the resolve runs server-side and the island POSTs.
//!   The reactive shell hydrates; the quote-resolve is a server-fn (the same
//!   will/law split `server.rs` documents).

use leptos::prelude::*;

use dregg_types::CellId;
#[cfg(test)]
use starbridge_web_surface::transclusion::Backlinks;
use starbridge_web_surface::transclusion::{TranscludedField, TransclusionError};
use starbridge_web_surface::web_of_cells::{AttestedResource, DreggUri, WebOfCells};

/// The constitution cell's committed-URL (the trusted-path chrome the source binds —
/// drawn from the ledger, never the page). The `dregg://constitution` the council
/// quotes.
pub const CONSTITUTION_URL: &str = "dregg://constitution";
/// The seed byte that addresses the constitution origin cell in the web-of-cells.
pub const CONSTITUTION_SEED: u8 = 0xC0;

// ════════════════════════════════════════════════════════════════════════════
// THE SOURCE CELL — a constitution carrying a `threshold`, as a real dregg://
// origin in a real WebOfCells. Publishing commits the value; amending advances it.
// ════════════════════════════════════════════════════════════════════════════

/// The constitution SOURCE: a real [`WebOfCells`] holding the `dregg://constitution`
/// origin cell whose committed content IS the `threshold` value.
///
/// The threshold is encoded as its decimal-string bytes (e.g. `3` → `b"3"`), so the
/// **quoted bytes are exactly the value** — the council's live quote displays the
/// source's committed content, not a re-derived copy. [`Self::amend_threshold`] is
/// the source's turn: a genuine state advance (re-commit + nonce bump + height
/// advance), after which a re-resolved transclusion sees the NEW value.
pub struct Constitution {
    web: WebOfCells,
    uri: DreggUri,
}

impl Constitution {
    /// Found the constitution with an initial `threshold`, published + attested
    /// (3-of-3 quorum) into a fresh web-of-cells — a real finalized read source.
    pub fn found(threshold: u64) -> Self {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(
            CONSTITUTION_SEED,
            &encode_threshold(threshold),
            CONSTITUTION_URL,
        );
        Constitution { web, uri }
    }

    /// The `dregg://constitution` reference the council transcludes (the immutable,
    /// content-addressed origin — the link that does not break across amendments).
    pub fn uri(&self) -> &DreggUri {
        &self.uri
    }

    /// The constitution cell id (the source cell — what backlinks key on).
    pub fn cell(&self) -> CellId {
        self.uri.cell
    }

    /// Borrow the underlying web-of-cells (so a transclusion can `include` against it).
    pub fn web(&self) -> &WebOfCells {
        &self.web
    }

    /// **Amend the constitution's `threshold`** — the SOURCE's turn (the "fire a turn
    /// on the source" half of the live quote). A genuine state advance through
    /// [`WebOfCells::amend`]: re-commit the new threshold into the SAME origin cell,
    /// bump its nonce (a distinct serve-receipt leaf), advance the attested height.
    /// Returns the advanced federation height — the new provenance height the live
    /// quote will report. The `dregg://` ref is UNCHANGED (the unbreakable link).
    pub fn amend_threshold(&mut self, new_threshold: u64) -> u64 {
        self.web
            .amend(&self.uri, &encode_threshold(new_threshold))
            .expect("the constitution was founded, so it can be amended")
    }
}

/// Encode a `threshold` as the committed content bytes — its decimal string, so the
/// quoted bytes ARE the human-readable value.
fn encode_threshold(threshold: u64) -> Vec<u8> {
    threshold.to_string().into_bytes()
}

/// Decode the committed content bytes back to a `threshold` (the quoted value the
/// council reads out of the live quote). Fail-closed: non-numeric content yields
/// `None` (a malformed source is not silently shown as a number).
fn decode_threshold(bytes: &[u8]) -> Option<u64> {
    std::str::from_utf8(bytes).ok()?.trim().parse::<u64>().ok()
}

// ════════════════════════════════════════════════════════════════════════════
// THE LIVE QUOTE — the council's transclusion of the constitution's threshold,
// resolved through the REAL TranscludedField. The value + provenance + backlinks.
// ════════════════════════════════════════════════════════════════════════════

/// A resolved **live quote** — the council's view of the constitution's `threshold`,
/// obtained through the REAL [`TranscludedField::include`] (the verified cross-cell
/// finalized read). It carries the verified field, the decoded threshold value, and
/// the provenance height the quote was resolved at.
///
/// This is the runtime form of `Dregg2.Deos.Transclusion`'s `Transclusion.value` +
/// `Transclusion.provenance`: the displayed value IS the source's committed value
/// (content-addressed, recomputable), dated by the cited receipt + height.
#[derive(Clone, Debug)]
pub struct LiveQuote {
    /// The verified transcluded field (the `dregg://` finalized read result).
    pub field: TranscludedField,
    /// The decoded `threshold` the constitution committed — the quoted value.
    pub threshold: u64,
    /// The federation height the quote was resolved at (the provenance height —
    /// advances when the source is amended; the freshness the badge dates).
    pub height: u64,
}

impl LiveQuote {
    /// **Resolve the live quote** — perform the REAL `dregg://` finalized read against
    /// the constitution and decode the quoted threshold. Returns the precise
    /// [`TransclusionError`] on a refused/forged/absent source (no opened provenance ⇒
    /// no quote). `height` is the source's current attested height (the provenance
    /// height the quote is dated at).
    pub fn try_resolve(
        web: &WebOfCells,
        source: &DreggUri,
        height: u64,
    ) -> Result<LiveQuote, TransclusionError> {
        // THE REAL VERIFIED CROSS-CELL READ — the displayed bytes ARE the source's
        // committed bytes, the provenance verified (content→commitment→receipt→
        // receipt-stream-root→quorum). A forged/absent source is refused HERE.
        let field = TranscludedField::include(web, source)?;
        let threshold = decode_threshold(field.quoted_bytes())
            // a verified-but-malformed source is not a faithful numeric quote.
            .ok_or(TransclusionError::NotFinalized)?;
        Ok(LiveQuote {
            field,
            threshold,
            height,
        })
    }

    /// The **provenance line** the council renders under the quote — the honest, dated
    /// citation: the source ref, the resolved height, and a short receipt prefix. This
    /// is what makes the quote recomputable by a verifier and datable by tooling (a
    /// stale quote is *visible*, never a silent live read).
    pub fn provenance_line(&self) -> String {
        let p = self.field.cite();
        let r = p.receipt_hash;
        format!(
            "transcluded from {} @ height {} · receipt {:02x}{:02x}{:02x}{:02x}… · {}",
            p.source.to_uri_string(),
            self.height,
            r[0],
            r[1],
            r[2],
            r[3],
            if p.finalized {
                "finalized"
            } else {
                "UNATTESTED"
            },
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// THE REACTIVE RUNTIME — the source threshold is a signal; the quote is a Memo that
// re-resolves the REAL include when the source advances. THIS is the live update.
// ════════════════════════════════════════════════════════════════════════════

/// **`CouncilTransclusionView`** — the council page rendering the constitution's
/// `threshold` as a LIVE quote (the reactive transclusion, in the Leptos runtime).
///
/// The reactive shape (the htmx-on-crack live quote):
///   * the constitution + its threshold live in a thread-local [`StoredValue`] (the
///     `WebOfCells` holds a real ledger and is `!Send`; the SSR render is
///     single-threaded per request, so thread-local storage is its right home — the
///     SAME pattern `CounterCell` uses for the gate's closures);
///   * a `source_height` [`RwSignal`] is the reactive trigger — the amend handler
///     bumps it after advancing the source, so every dependent recomputes;
///   * the **quote [`Memo`]** re-resolves the REAL [`TranscludedField::include`]
///     whenever `source_height` changes — so the displayed value, the provenance
///     line, and the badge all reflect the source's CURRENT committed value. This is
///     the live quote: a `Memo` over the verified read, not a frozen copy.
///
/// The "amend constitution" button advances the source (a genuine state advance) and
/// bumps `source_height` → the quote Memo re-resolves → the view shows the NEW
/// threshold at the NEW provenance height. In a hydrate build the amend is a
/// server-fn POST (the resolve runs server-side atop native crypto — the deos seam);
/// here the body runs inline so the SSR render + tests exercise the REAL read.
#[component]
pub fn CouncilTransclusionView(
    /// The initial constitution threshold the council starts quoting.
    initial_threshold: u64,
    /// How many sibling surfaces also quote the constitution (the backlink count the
    /// witness-graph reports — `N surfaces quote me`).
    backlink_count: usize,
) -> impl IntoView {
    // The SOURCE constitution (a real web-of-cells) lives thread-local — it is `!Send`
    // (holds a real ledger), and an SSR request is single-threaded.
    let constitution = StoredValue::new_local(Constitution::found(initial_threshold));

    // The reactive TRIGGER: the source's current attested height. The amend handler
    // bumps it; every dependent Memo recomputes. Seeded to the founded height (1: a
    // single publish advanced the federation height once).
    let source_height = RwSignal::new(1u64);

    // THE LIVE QUOTE MEMO — re-resolves the REAL `TranscludedField::include` whenever
    // `source_height` changes. THIS is the live quote: the displayed value tracks the
    // source's committed value, reactively, through the verified read.
    let quote = Memo::new(move |_| {
        let h = source_height.get();
        constitution.with_value(|c| {
            LiveQuote::try_resolve(c.web(), c.uri(), h)
                .map(|q| (q.threshold, q.provenance_line()))
                .map_err(|e| format!("{e:?}"))
        })
    });

    // Derived readouts for the view (each recomputes when `quote` does).
    let threshold_text = Memo::new(move |_| match quote.get() {
        Ok((t, _)) => format!("{t}"),
        Err(_) => "—".to_string(),
    });
    let provenance_text = Memo::new(move |_| match quote.get() {
        Ok((_, line)) => line,
        // The anti-forge / refusal path made visible: a refused quote shows its
        // precise reason here, never the (would-be) forged bytes.
        Err(reason) => format!("quote refused: {reason}"),
    });

    // The AMEND handler — the SOURCE's turn. Advance the constitution's threshold (a
    // genuine state advance through the real `WebOfCells::amend`) and bump
    // `source_height` so the quote Memo re-resolves to the NEW value. The new
    // threshold is the current + 2 (a visible jump, e.g. 3 → 5 → 7).
    let on_amend = move || {
        // `try_update_value` returns the closure's value (the advanced height) — the
        // mutation runs on the thread-local store the SSR request owns.
        let advanced = constitution.try_update_value(|c| {
            let cur = LiveQuote::try_resolve(c.web(), c.uri(), 0)
                .map(|q| q.threshold)
                .unwrap_or(0);
            c.amend_threshold(cur + 2)
        });
        // Bump the reactive trigger to the source's NEW attested height — the quote
        // Memo re-resolves the verified read and the view reflects the new value.
        if let Some(h) = advanced {
            source_height.set(h);
        }
    };

    view! {
        <section class="deos-council-transclusion">
            <header class="trusted-path">
                <span class="origin">"council page · quoting "{CONSTITUTION_URL}</span>
            </header>
            // THE LIVE QUOTE — the constitution's threshold, transcluded.
            <div class="live-quote">
                <p class="quote-value">
                    "constitution threshold (live quote): "
                    <strong>{move || threshold_text.get()}</strong>
                </p>
                // The provenance line — the honest, dated citation (advances on amend).
                <p class="provenance">{move || provenance_text.get()}</p>
                // The backlinks — the two-way link, rendered as "who quotes me".
                <p class="backlinks">
                    {move || format!("{} surface(s) quote this constitution", backlink_count)}
                </p>
            </div>
            // THE PAYOFF BUTTON — amend the source; the quote updates reactively.
            <button class="amend" on:click=move |_| on_amend()>
                "amend constitution (advance threshold)"
            </button>
        </section>
    }
}

/// **`render_council_with_live_quote`** — render the council-with-live-quote surface
/// to an HTML string at a given source `height`, showing the quote's value +
/// provenance + backlinks. The per-viewer / SSR render path (the runtime form the
/// browser would hydrate).
///
/// `web` + `source` are the live constitution (so the quote resolves the CURRENT
/// committed value); `height` is the source's current attested height (dated into the
/// provenance line); `backlink_count` is the witness-graph in-degree.
pub fn render_council_with_live_quote(
    web: &WebOfCells,
    source: &DreggUri,
    height: u64,
    backlink_count: usize,
) -> String {
    // Resolve the live quote through the REAL verified read.
    let resolved = LiveQuote::try_resolve(web, source, height);

    // A fresh reactive Owner roots the per-request signal arena (as the council SSR
    // render does) — even a static render allocates reactive nodes.
    let owner = Owner::new();
    owner.with(move || {
        let body = match &resolved {
            Ok(q) => {
                let value = format!("{}", q.threshold);
                let prov = q.provenance_line();
                view! {
                    <div class="live-quote">
                        <p class="quote-value">
                            "constitution threshold (live quote): " <strong>{value}</strong>
                        </p>
                        <p class="provenance">{prov}</p>
                        <p class="backlinks">
                            {format!("{backlink_count} surface(s) quote this constitution")}
                        </p>
                    </div>
                }
                .into_any()
            }
            Err(e) => {
                // The refusal path made visible — the anti-forge tooth in the render:
                // a forged/absent source shows its reason, NEVER the would-be bytes.
                let reason = format!("quote refused: {e:?}");
                view! { <div class="live-quote refused"><p class="provenance">{reason}</p></div> }
                    .into_any()
            }
        };
        let view = view! {
            <section class="deos-council-transclusion">
                <header class="trusted-path">
                    <span class="origin">"council page · quoting "{CONSTITUTION_URL}</span>
                </header>
                {body}
            </section>
        };
        view.to_html()
    })
}

// ════════════════════════════════════════════════════════════════════════════
// THE LIVE-UPDATE SEQUENCE — the demo's PROOF: render (quote V) → amend the source →
// re-render (quote V', provenance height advanced, NOT stale V). The binary and the
// tests both drive this, so the runnable demo and the proof are the SAME path.
// ════════════════════════════════════════════════════════════════════════════

/// One step of the live-quote sequence — the council surface rendered at a moment,
/// carrying the value the quote showed + the provenance height it was dated at.
#[derive(Clone, Debug)]
pub struct QuoteStep {
    /// A human label for the step (e.g. `"founded"`, `"after amend #1"`).
    pub label: String,
    /// The threshold value the live quote displayed.
    pub threshold: u64,
    /// The provenance height the quote was dated at.
    pub height: u64,
    /// The full provenance line (the dated citation).
    pub provenance: String,
    /// The rendered council surface HTML (what the viewer's island shows).
    pub html: String,
}

/// **`live_quote_sequence`** — drive the live reactive transclusion end to end and
/// return the steps (the demo's proof). Founds a constitution at `start_threshold`,
/// resolves+renders the council's live quote (step 0), then AMENDS the source
/// `amendments` times, re-resolving+re-rendering after each — proving the quote
/// tracks the source REACTIVELY: each step's `threshold` is the source's NEW committed
/// value and its `height` advances, never the stale prior value.
///
/// This is exactly what [`CouncilTransclusionView`]'s quote `Memo` recomputes when its
/// `source_height` trigger is bumped — the headless form of the in-browser live
/// update. `backlink_count` is the witness-graph in-degree rendered in each step.
pub fn live_quote_sequence(
    start_threshold: u64,
    amendments: usize,
    backlink_count: usize,
) -> Vec<QuoteStep> {
    let mut constitution = Constitution::found(start_threshold);
    let mut steps = Vec::with_capacity(amendments + 1);

    // STEP 0 — the founded value, freshly quoted.
    let founded_height = 1; // one publish advanced the attested height once.
    steps.push(render_step(
        &constitution,
        "founded",
        founded_height,
        backlink_count,
    ));

    // EACH AMENDMENT — the source's turn; the quote re-resolves to the NEW value at
    // the NEW height (the live update).
    let mut threshold = start_threshold;
    for i in 0..amendments {
        threshold += 2; // a visible jump (e.g. 3 → 5 → 7).
        let new_height = constitution.amend_threshold(threshold);
        let label = format!("after amend #{}", i + 1);
        steps.push(render_step(
            &constitution,
            &label,
            new_height,
            backlink_count,
        ));
    }

    steps
}

/// Resolve + render one sequence step against the live constitution.
fn render_step(
    constitution: &Constitution,
    label: &str,
    height: u64,
    backlink_count: usize,
) -> QuoteStep {
    let q = LiveQuote::try_resolve(constitution.web(), constitution.uri(), height)
        .expect("the founded/amended constitution resolves a faithful quote");
    let html = render_council_with_live_quote(
        constitution.web(),
        constitution.uri(),
        height,
        backlink_count,
    );
    QuoteStep {
        label: label.to_string(),
        threshold: q.threshold,
        height: q.height,
        provenance: q.provenance_line(),
        html,
    }
}

/// **`forge_a_quote`** — build a deliberately FORGED transclusion (a genuine attested
/// resource whose bytes were tampered after attestation) and return the verification
/// error it fails with. This is the anti-forge tooth made concrete for the demo: a
/// forged quote's `content_hash` no longer matches its bytes, so
/// [`AttestedResource::verify`] REFUSES it — it can never render as a verified quote
/// (`transclusion_forge_refused`: no opened provenance ⇒ no quote). Returns the
/// genuine bytes the forger wanted to display alongside the refusal, so the demo can
/// show "the forger tried to show X; the chain refused".
pub fn forge_a_quote(genuine_threshold: u64, forged_threshold: u64) -> (Vec<u8>, String) {
    let mut web = WebOfCells::new(3);
    let uri = web.publish(
        0xF0,
        &encode_threshold(genuine_threshold),
        "dregg://forged-source",
    );
    // Fetch a GENUINE attested resource, then tamper its bytes to claim a different
    // threshold — the forge.
    let (mut resource, _chrome): (AttestedResource, _) = web.fetch(&uri).expect("genuine fetch");
    let forged_bytes = encode_threshold(forged_threshold);
    resource.content_bytes = forged_bytes.clone();
    // The verification chain catches it: the tampered bytes no longer hash to the
    // committed content_hash.
    let refusal = match resource.verify() {
        Ok(()) => "ERROR: a forged quote must NOT verify".to_string(),
        Err(e) => format!("{e:?}"),
    };
    (forged_bytes, refusal)
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── (1) THE LIVE QUOTE SHOWS THE SOURCE'S VALUE + PROVENANCE + BACKLINKS. ──

    #[test]
    fn live_quote_shows_source_value_and_provenance_and_backlinks() {
        let constitution = Constitution::found(3);
        let q = LiveQuote::try_resolve(constitution.web(), constitution.uri(), 1)
            .expect("the founded constitution resolves a faithful quote");

        // The quote IS the source's committed value (the verified cross-cell read).
        assert_eq!(
            q.threshold, 3,
            "the live quote shows the source's committed threshold"
        );
        // The provenance line dates it: the source ref + height + receipt + finalized.
        let line = q.provenance_line();
        assert!(
            line.contains("dregg://"),
            "provenance cites the source: {line}"
        );
        assert!(
            line.contains("height 1"),
            "provenance dates the height: {line}"
        );
        assert!(
            line.contains("finalized"),
            "a quorum-attested source is finalized: {line}"
        );

        // The SSR render carries the value, the provenance, and the backlink count.
        let html = render_council_with_live_quote(constitution.web(), constitution.uri(), 1, 4);
        assert!(html.contains("constitution threshold (live quote): "));
        assert!(
            html.contains("<strong>3</strong>"),
            "the quote renders the value: {html}"
        );
        assert!(
            html.contains("transcluded from dregg://"),
            "the provenance line renders"
        );
        assert!(html.contains("4 surface(s) quote"), "the backlinks render");
    }

    // ── (2) THE PAYOFF: THE LIVE UPDATE. quote shows V → amend → quote shows V'
    //        (reactively, NOT stale V); the provenance height advances. ──

    #[test]
    fn quote_updates_reactively_when_source_is_amended() {
        let mut constitution = Constitution::found(3);

        // Before: the quote shows V = 3 at height 1.
        let before =
            LiveQuote::try_resolve(constitution.web(), constitution.uri(), 1).expect("resolves");
        assert_eq!(before.threshold, 3);

        // FIRE A TURN ON THE SOURCE: amend the constitution to threshold 5.
        let h2 = constitution.amend_threshold(5);
        assert!(h2 > 1, "the amend advances the attested height: {h2}");

        // After: re-resolving the SAME dregg:// ref shows V' = 5 (the NEW committed
        // value), NOT the stale 3 — the live quote tracked the source reactively.
        let after = LiveQuote::try_resolve(constitution.web(), constitution.uri(), h2)
            .expect("the amended source still resolves (the unbreakable link)");
        assert_eq!(
            after.threshold, 5,
            "the live quote shows the AMENDED value, not stale"
        );
        assert_eq!(after.height, h2, "the provenance height advanced");
        assert_ne!(
            after.field.cite().receipt_hash,
            before.field.cite().receipt_hash,
            "the cited receipt advanced (a distinct serve-receipt leaf)"
        );

        // A second amend → V'' = 7, height advances again. The link never rots.
        let h3 = constitution.amend_threshold(7);
        let third =
            LiveQuote::try_resolve(constitution.web(), constitution.uri(), h3).expect("resolves");
        assert_eq!(third.threshold, 7);
        assert!(h3 > h2);
    }

    // ── (2b) THE SAME PAYOFF, THROUGH THE RENDER (what the viewer's island shows). ──

    #[test]
    fn rendered_quote_reflects_the_amended_value_not_the_stale_one() {
        let steps = live_quote_sequence(3, 2, 4);
        assert_eq!(steps.len(), 3, "founded + 2 amendments");

        // Step 0: the founded value 3.
        assert_eq!(steps[0].threshold, 3);
        assert!(steps[0].html.contains("<strong>3</strong>"));
        // Step 1: amended to 5 — the render shows 5, NOT the stale 3.
        assert_eq!(steps[1].threshold, 5);
        assert!(
            steps[1].html.contains("<strong>5</strong>"),
            "render shows amended 5"
        );
        assert!(
            !steps[1].html.contains("<strong>3</strong>"),
            "render is NOT stale 3"
        );
        // Step 2: amended to 7.
        assert_eq!(steps[2].threshold, 7);
        assert!(steps[2].html.contains("<strong>7</strong>"));

        // The provenance HEIGHT advances strictly across the live updates (the quote
        // dates each read; supersession is visible, never a silent live read).
        assert!(
            steps[0].height < steps[1].height && steps[1].height < steps[2].height,
            "provenance heights advance: {} < {} < {}",
            steps[0].height,
            steps[1].height,
            steps[2].height
        );
    }

    // ── (3) THE ANTI-FORGE TOOTH: a forged quote does NOT render as verified. ──

    #[test]
    fn forged_quote_is_refused_and_does_not_render() {
        // A forger takes a genuine attested resource (threshold 3) and tampers its
        // bytes to claim threshold 999. The verification chain catches it.
        let (forged_bytes, refusal) = forge_a_quote(3, 999);
        assert_eq!(forged_bytes, b"999", "the forger wanted to display 999");
        assert!(
            refusal.contains("ContentHashMismatch"),
            "the forge is refused on the content-hash tooth: {refusal}"
        );

        // And an ABSENT source (a dregg:// ref to a cell that was never published)
        // resolves to NO live quote — refused at the fetch, never a blank-but-trusted
        // quote.
        let constitution = Constitution::found(3);
        let absent = DreggUri::new({
            let mut b = [0u8; 32];
            b[0] = 0xAB;
            CellId::from_bytes(b)
        });
        let r = LiveQuote::try_resolve(constitution.web(), &absent, 1);
        assert!(
            matches!(r, Err(TransclusionError::Fetch(_))),
            "an absent source has no live quote (refused at fetch), got {r:?}"
        );

        // The render of an absent/forged source shows the REFUSAL, never bytes.
        let html = render_council_with_live_quote(constitution.web(), &absent, 1, 0);
        assert!(
            html.contains("quote refused"),
            "a refused source renders its refusal: {html}"
        );
        assert!(
            !html.contains("<strong>"),
            "and NEVER renders a value for it"
        );
    }

    // ── (4) THE UNBREAKABLE LINK: the dregg:// ref is unchanged across amendments. ──

    #[test]
    fn dregg_ref_is_unchanged_across_amendments_the_unbreakable_link() {
        let mut constitution = Constitution::found(3);
        let ref_before = constitution.uri().clone();
        constitution.amend_threshold(5);
        constitution.amend_threshold(7);
        // The citation still denotes the SAME content-addressed origin cell — Nelson's
        // link that does not break, even as the source advances.
        assert_eq!(
            &ref_before,
            constitution.uri(),
            "the dregg:// ref is unchanged across amendments (the unbreakable link)"
        );
        // …and it still resolves, now to the latest value.
        let q =
            LiveQuote::try_resolve(constitution.web(), constitution.uri(), 3).expect("resolves");
        assert_eq!(q.threshold, 7);
    }

    // ── (5) THE BACKLINKS — the two-way link rendered as "who quotes me". ──

    #[test]
    fn backlinks_count_the_surfaces_that_quote_the_constitution() {
        let constitution = Constitution::found(3);
        let quote =
            TranscludedField::include(constitution.web(), constitution.uri()).expect("resolves");

        // Three council surfaces transclude the same constitution.
        let mut links = Backlinks::new();
        for obs in 1u8..=3 {
            let mut b = [0u8; 32];
            b[0] = 0xB0 | obs;
            links.observe(CellId::from_bytes(b), &quote);
        }
        assert_eq!(
            links.backlink_count(constitution.cell()),
            3,
            "the witness-graph reports 3 surfaces quote the constitution"
        );
        // each backlink cites the receipt it observed at (a verifiable fact).
        assert!(links
            .observers_of(constitution.cell())
            .iter()
            .all(|o| o.receipt_hash == quote.provenance.receipt_hash));
    }

    // ── SSR sanity: the reactive component renders the live quote on the native
    //    (gate-linkable) target, reflecting the verified read. ──

    #[test]
    fn ssr_council_transclusion_view_renders_the_live_quote() {
        let owner = Owner::new();
        let html = owner.with(|| {
            view! { <CouncilTransclusionView initial_threshold=3 backlink_count=4 /> }.to_html()
        });
        // The component rendered the live quote with the founded value + the amend
        // button (the payoff the browser would press).
        assert!(html.contains("deos-council-transclusion"));
        assert!(html.contains("constitution threshold (live quote): "));
        assert!(
            html.contains("<strong>3</strong>"),
            "the founded value renders: {html}"
        );
        assert!(
            html.contains("amend constitution"),
            "the payoff button renders"
        );
        assert!(html.contains("surface(s) quote"), "the backlinks render");
    }
}
