//! `deos_leptos` EEL / PARALLEL-SOURCE-VIEW demo — Ted Nelson's parallel source view,
//! made runnable.
//!
//! Run: `cargo run --bin parallel_source_view` (native, the side that links the real
//! `dregg://` attested fetch + the verified document resolve).
//!
//! It builds a multi-span **dreggverse document** (`deos_web_cells::DreggverseDocument`)
//! — an EDL of the author's OWN prose interleaved with three **transcluded spans** of
//! real source cells (a `preamble`, a `threshold`, and a sealed `annex`) — and renders
//! the **EEL**: the document in one column and, BESIDE each transcluded span, its SOURCE
//! cell with the quoted byte range **highlighted** and a working **jump-to-source**
//! anchor (`#eel-src-N`). Then it shows:
//!
//!   * **the darkened-span case** — a WEAKER viewer (who lacks authority over the annex)
//!     sees the annex span DARKENED: *"you may not read this, but here is what it
//!     cites"* — its citation preserved, its bytes withheld (never forged);
//!   * **the live update** — AMENDING the threshold source (a genuine state advance) and
//!     re-rendering: the highlighted range in the source column tracks the source's NEW
//!     committed value, the provenance height advances, every other span untouched (the
//!     unbreakable Nelson link, in the parallel view).
//!
//! That sequence ([`eel_sequence`]) is exactly what the Leptos
//! [`ParallelSourceView`] component's view `Memo` recomputes when its `source_height`
//! trigger is bumped — the headless form of the in-browser live update, in the EEL.

use deos_leptos::parallel_source_view::eel_sequence;

fn main() {
    println!(
        "== deos EEL / PARALLEL-SOURCE-VIEW — Ted Nelson's parallel source view, on the \
         verified substrate ==\n"
    );
    println!(
        "A multi-span `DreggverseDocument` (the author's OWN prose interleaved with three\n\
         transcluded spans of real `dregg://` source cells) is rendered as the EEL: the\n\
         document in one column and, BESIDE each transcluded span, its SOURCE cell with the\n\
         quoted byte range highlighted (<mark>) and a working jump-to-source anchor\n\
         (#eel-src-N). A weaker viewer sees the sealed annex DARKENED (citation preserved,\n\
         bytes withheld); amending a source makes the highlighted range track it LIVE.\n"
    );

    // Build the worked scenario and amend the threshold source twice (→ "4 of 5" →
    // "5 of 5"), rendering the parallel source view after each.
    let steps = eel_sequence(2);

    for (i, step) in steps.iter().enumerate() {
        println!("─── step {i}: {} ───", step.label);
        println!(
            "  threshold source (the highlighted quote) : {}",
            step.threshold_text
        );
        println!("  provenance height                        : {}", step.height);
        println!(
            "  weaker-viewer darkened spans             : {} (citation preserved, bytes withheld)",
            step.darkened
        );
        println!();
        // The FULL-authority parallel source view (the author's own view — nothing
        // darkened): the document column beside the source column, the quoted ranges
        // highlit, the jump anchors present.
        println!("  ── FULL AUTHORITY (author's view) ──");
        println!("{}\n", step.full_html);
        // The WEAKER-viewer parallel source view: the sealed annex DARKENED — its
        // citation shown, its bytes withheld. The other two quotes still render.
        println!("  ── WEAKER VIEWER (sealed annex darkened) ──");
        println!("{}\n", step.weaker_html);
    }

    // The reactive payoff, stated plainly from the sequence.
    let first = steps.first().expect("a founded step");
    let last = steps.last().expect("an amended step");
    println!(
        "THE LIVE UPDATE (in the parallel view): the highlighted threshold quote showed\n\
         \"{}\" (height {}), and after the amendments the SAME `dregg://threshold` ref —\n\
         the unbreakable link — re-resolved so the source column's highlight now shows\n\
         \"{}\" (height {}). NOT a frozen copy: the quoted range tracked the source\n\
         reactively, and every OTHER span (including the darkened annex) was untouched.\n",
        first.threshold_text, first.height, last.threshold_text, last.height
    );

    println!(
        "THE DARKENED SPAN (citation preserved): the weaker viewer — who lacks authority\n\
         over the sealed annex — never saw the annex's source bytes. The annex span\n\
         DARKENED through the REAL membrane meet, but its CITATION survived in the source\n\
         column: \"you may not read this, but here is what it cites\". The jump-to-source\n\
         anchor still navigates to what the span cites; only the bytes are withheld\n\
         (never the source value the viewer lacks, never a forgery)."
    );

    println!(
        "\nWhat you'd see in a BROWSER: a two-pane widget — the document on the left, the\n\
         cited source cells on the right; clicking a quote scrolls the source pane to its\n\
         highlighted range; pressing \"amend source\" advances the threshold and the\n\
         highlight updates IN PLACE. (The pixel pane geometry + the click-routed scroll\n\
         are the servo-render follow-on lane — this demo ships the semantic two columns,\n\
         the highlight, the working #eel-src-N anchor, and the darkened-citation case;\n\
         the resolve runs server-side atop native crypto — the deos will/law seam.)"
    );
}
