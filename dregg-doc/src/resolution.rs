//! The conflict-view editing MODEL — a rendered conflict made *resolvable from the
//! surface*, each alternative carrying a ONE-CLICK resolving patch.
//!
//! [`crate::content`] surfaces a fork as a first-class [`ConflictRegion`]; the
//! [`crate::literate`] surface RENDERS that region to a legible `<<< … >>>` block
//! and PARSES it back. But the literate surface is *passive*: a reader sees the
//! conflict, yet authoring a resolution still meant reaching past the surface to
//! hand-thread raw [`AtomId`]s into [`crate::resolve_keep`] / [`crate::resolve_connect`].
//! This module closes that seam: given the live [`Rendered`] content it enumerates,
//! per conflict, the exact set of resolution *gestures* a reader can take, each
//! pre-built into a ready [`Patch`]. The conflict-view becomes an EDITOR — "two
//! people wrote this differently; here's both; click to keep one, order them, or
//! settle the field" — and every click is a single, content-addressed patch (which
//! on the substrate is a cap-gated turn leaving a receipt).
//!
//! The four gestures, one per resolution shape the algebra already admits:
//!
//! - [`Resolution::Keep`] — keep ONE prose alternative, tombstone the others
//!   (`resolve_keep`). One choice per alternative.
//! - [`Resolution::Order`] — keep BOTH (all) prose alternatives, in the offered
//!   order (`resolve_connect`). One choice per ordering offered.
//! - [`Resolution::ChooseField`] — settle a single-valued field clash to one of the
//!   clashing values (`resolve_field`, superseding). One choice per clashing value.
//!
//! Each [`ResolutionChoice`] is *legible* (a `label` a reader can read off the
//! conflict block) and *ready* (a [`Patch`] a caller commits). Resolution is itself
//! a patch authored by the resolver, so it leaves a receipt and is revertible
//! (§3.5) — the conflict view is a real moldable editor, not a read-only readout.
//!
//! ## The two load-bearing both-polarity facts (tested)
//!
//! - **A genuine conflict yields ready resolutions (the TRUE bite).** A merged
//!   document carrying a real antichain (or field clash) produces a non-empty set
//!   of [`ResolutionChoice`]s, and *applying any one of them collapses that
//!   conflict* — the merge is never a failure; resolution is always a click away.
//! - **A clean document offers nothing to resolve (the FALSE bite).** A conflict-
//!   free document produces an EMPTY resolution set — the editor does not fabricate
//!   a choice where there is no conflict (no laundered vacuity).

use crate::atom::{AtomId, Author};
use crate::content::{ConflictRegion, Rendered};
use crate::graph::DocGraph;
use crate::patch::Patch;
use crate::regime::Regime;
use crate::resolve::{resolve_connect_by, resolve_field, resolve_keep_in};

/// Which resolution gesture a [`ResolutionChoice`] performs — the click's meaning,
/// kept alongside the ready patch so a surface can group/label the options and a
/// test can assert the shape.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Resolution {
    /// Keep one prose alternative (`keep`), tombstoning every other head
    /// (`drop`). The antichain collapses to the single kept walk.
    Keep {
        /// The fork-point atom kept alive.
        keep: AtomId,
        /// The fork-point atoms tombstoned.
        drop: Vec<AtomId>,
    },
    /// Keep BOTH (all) prose alternatives, chaining the heads in `order`
    /// (`order[0]` before `order[1]` …). Nothing is lost; the antichain becomes a
    /// chain.
    Order {
        /// The fork-point atoms in the chosen reading order.
        order: Vec<AtomId>,
    },
    /// Settle a single-valued field clash to one canonical `value` (superseding
    /// all concurrent assignments). The conservation/authority regime resolution.
    ChooseField {
        /// The clashing field's name.
        field: String,
        /// The value to settle on.
        value: String,
    },
}

/// One offered resolution: a legible label (what the reader reads off the conflict
/// block), the gesture it performs, and the ready [`Patch`] a click commits.
///
/// The patch is authored by the resolver passed to [`resolutions_for`]; on the
/// substrate committing it is a cap-gated turn (only a region-edit cap holder may
/// resolve), leaving a receipt — so the resolution is witnessed and revertible.
#[derive(Clone, Debug)]
pub struct ResolutionChoice {
    /// A reader-legible description of the gesture (e.g. *keep alice's "Cats."* or
    /// *order: alice's then bob's* or *title := "On Cats"*).
    pub label: String,
    /// The structured gesture (for grouping / assertion).
    pub resolution: Resolution,
    /// The ready resolving patch — a click commits exactly this.
    pub patch: Patch,
}

impl ResolutionChoice {
    /// True iff this choice keeps every alternative (an [`Resolution::Order`]) — the
    /// "lose nothing" resolution, vs. a [`Resolution::Keep`] that drops the rest.
    pub fn keeps_all(&self) -> bool {
        matches!(self.resolution, Resolution::Order { .. })
    }
}

/// Enumerate the resolution choices a reader can take on ONE conflict region,
/// each pre-built into a ready patch authored by `resolver`.
///
/// For a [`Regime::Prose`] antichain with heads `h₀ … hₙ`:
/// - one [`Resolution::Keep`] per head (keep that head, drop the rest), and
/// - one [`Resolution::Order`] in the region's canonical (sorted) head order
///   (keep all, in reading order). *(A second, reversed ordering is offered for
///   a two-way fork so "swap the order" is a one-click option too.)*
///
/// For a [`Regime::Field`] clash on field `f` with values `v₀ … vₙ`:
/// - one [`Resolution::ChooseField`] per distinct clashing value.
///
/// The labels read the alternatives' attributed text/author straight off the
/// region, so the offered options are exactly what the conflict block shows.
pub fn resolutions_for(
    g: &DocGraph,
    region: &ConflictRegion,
    resolver: Author,
) -> Vec<ResolutionChoice> {
    match region.regime {
        Regime::Prose => prose_resolutions(g, region, resolver),
        Regime::Field => field_resolutions(region, resolver),
    }
}

/// All resolution choices across every conflict in a rendered document, in
/// document order, grouped by region. A clean document yields an empty vec — the
/// editor never fabricates a choice where there is no conflict (the FALSE bite).
pub fn resolutions(g: &DocGraph, rendered: &Rendered, resolver: Author) -> Vec<RegionResolutions> {
    rendered
        .conflicts()
        .map(|region| RegionResolutions {
            regime: region.regime,
            field: region.field.clone(),
            choices: resolutions_for(g, region, resolver),
        })
        .collect()
}

/// The resolution choices offered for one conflict region (its regime/field plus
/// the per-gesture choices), as surfaced by [`resolutions`].
#[derive(Clone, Debug)]
pub struct RegionResolutions {
    /// The region's regime (is it a real, consensus-needing clash?).
    pub regime: Regime,
    /// The clashing field name for a [`Regime::Field`] region; `None` for prose.
    pub field: Option<String>,
    /// The offered resolution choices (keep-each / order / choose-each-value).
    pub choices: Vec<ResolutionChoice>,
}

/// The prose-antichain resolution menu: keep-each-head + order-all (+ the reversed
/// order for a two-way fork).
fn prose_resolutions(
    g: &DocGraph,
    region: &ConflictRegion,
    resolver: Author,
) -> Vec<ResolutionChoice> {
    let heads = region.heads();
    let mut out = Vec::new();

    // One KEEP per alternative — keep this head, tombstone every OTHER branch
    // *whole* (head + its exclusively-owned tail) via the graph-aware
    // `resolve_keep_in`, so a dropped multi-atom branch cannot leak its tail.
    for (i, alt) in region.alternatives.iter().enumerate() {
        let keep = alt.head;
        let drop: Vec<AtomId> = heads.iter().copied().filter(|&h| h != keep).collect();
        out.push(ResolutionChoice {
            label: format!(
                "keep {}'s {}",
                author_name(alt.provenance.author),
                quote(&alt.text)
            ),
            resolution: Resolution::Keep {
                keep,
                drop: drop.clone(),
            },
            patch: resolve_keep_in(g, resolver, keep, &drop),
        });
        let _ = i;
    }

    // ORDER all (keep both, in the region's canonical reading order).
    if heads.len() >= 2 {
        out.push(order_choice(region, &heads, resolver, "order"));
        // For a clean two-way fork, also offer the reversed order (the "swap"
        // one-click). More-than-two folds keep just the canonical order to avoid
        // an explosion; finer ordering is a manual `resolve_connect`.
        if heads.len() == 2 {
            let rev: Vec<AtomId> = heads.iter().rev().copied().collect();
            let mut rev_region = region.clone();
            rev_region.alternatives.reverse();
            out.push(order_choice(&rev_region, &rev, resolver, "order (swapped)"));
        }
    }

    out
}

/// Build one ORDER choice over `order` (the heads in reading order), labelled from
/// the region's alternatives in that same order.
fn order_choice(
    region: &ConflictRegion,
    order: &[AtomId],
    resolver: Author,
    verb: &str,
) -> ResolutionChoice {
    let names: Vec<String> = region
        .alternatives
        .iter()
        .map(|a| format!("{}'s", author_name(a.provenance.author)))
        .collect();
    ResolutionChoice {
        label: format!("{verb}: {} (keep both)", names.join(" then ")),
        resolution: Resolution::Order {
            order: order.to_vec(),
        },
        patch: resolve_connect_by(resolver, order),
    }
}

/// The field-clash resolution menu: one CHOOSE per distinct clashing value.
fn field_resolutions(region: &ConflictRegion, resolver: Author) -> Vec<ResolutionChoice> {
    let Some(field) = region.field.clone() else {
        return Vec::new();
    };
    let mut seen: Vec<String> = Vec::new();
    let mut out = Vec::new();
    for alt in &region.alternatives {
        if seen.iter().any(|v| v == &alt.text) {
            continue; // one choice per distinct value
        }
        seen.push(alt.text.clone());
        out.push(ResolutionChoice {
            label: format!(
                "settle {field} := {} ({}'s)",
                quote(&alt.text),
                author_name(alt.provenance.author)
            ),
            resolution: Resolution::ChooseField {
                field: field.clone(),
                value: alt.text.clone(),
            },
            patch: resolve_field(resolver, &field, &alt.text),
        });
    }
    out
}

/// A short author display name (mirrors the editor's mapping; kept local so the
/// headless core has no UI dependency).
fn author_name(a: Author) -> String {
    match a.0 {
        0 => "system".to_string(),
        1 => "alice".to_string(),
        2 => "bob".to_string(),
        other => format!("author {other:x}"),
    }
}

/// Quote an alternative's text for a label, trimming a trailing newline (the
/// line-atom terminator) so the label reads as one phrase.
fn quote(text: &str) -> String {
    let t = text.strip_suffix('\n').unwrap_or(text);
    format!("“{t}”")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::content::content;
    use crate::literate::author_graph;
    use crate::merge::merge;
    use crate::patch::{Op, Patch};

    // ── REGRESSION: keep drops a MULTI-ATOM branch WHOLE (no tail leak) ──────────
    //
    // The corruption: the old head-only `resolve_keep_by` tombstoned only the
    // dropped branch's HEAD. For a multi-atom dropped branch the tail atoms stayed
    // alive and were reachable *through* the head tombstone, so (1) the dropped
    // content leaked back into the render and (2) the orphaned tail re-formed a
    // fresh antichain — the keep resolution did NOT collapse the conflict. This
    // test pins both polarities: the kept branch survives whole; the dropped
    // branch (head AND tail) is gone; and the conflict is genuinely collapsed.

    /// Build a two-way conflict where BOTH branches are two atoms long, off a
    /// shared base. Returns `(merged, a_head, b_head)`.
    fn two_multiatom_branches() -> (crate::DocGraph, AtomId, AtomId) {
        let mut h = crate::History::new();
        let (base, op0) = Patch::add(1, "shared\n", AtomId::ROOT);
        h.commit(Patch::by(Author(0), [op0]));
        let g = h.replay();
        let (a1, opa1) = Patch::add(2, "a1\n", base);
        let (_a2, opa2) = Patch::add(3, "a2\n", a1);
        let a = Patch::by(Author(1), [opa1, opa2]).apply_to(&g);
        let (b1, opb1) = Patch::add(4, "b1\n", base);
        let (_b2, opb2) = Patch::add(5, "b2\n", b1);
        let b = Patch::by(Author(2), [opb1, opb2]).apply_to(&g);
        (merge(&a, &b), a1, b1)
    }

    #[test]
    fn keep_drops_a_multiatom_branch_whole_and_collapses_the_conflict() {
        let (merged, a1, _b1) = two_multiatom_branches();
        let rendered = content(&merged);
        assert!(rendered.has_conflict(), "two multi-atom branches conflict");

        let region = rendered.conflicts().next().unwrap();
        let choices = resolutions_for(&merged, region, Author(1));
        let keep_a = choices
            .iter()
            .find(|c| matches!(&c.resolution, Resolution::Keep { keep, .. } if *keep == a1))
            .expect("a keep-A choice");

        let resolved = keep_a.patch.apply_to(&merged);
        let after = content(&resolved);
        let text = after.to_marked_string();

        // FALSE bite: the dropped branch is gone WHOLE — neither its head nor its
        // tail leaks (the old bug left "b2" alive and orphaned).
        assert!(!text.contains("b1"), "dropped head gone: {text:?}");
        assert!(
            !text.contains("b2"),
            "dropped TAIL gone too (no leak): {text:?}"
        );
        // TRUE bite: the kept branch survives whole, and the conflict is collapsed.
        assert!(text.contains("a1\na2"), "kept branch whole: {text:?}");
        assert!(
            !after.has_conflict(),
            "the keep genuinely collapses it: {text:?}"
        );
    }

    #[test]
    fn keep_in_spares_a_shared_rejoin_tail() {
        // Two branches that REJOIN at a shared tail atom: keeping one must NOT
        // tombstone the rejoin atom (it belongs to the kept reading too).
        let mut h = crate::History::new();
        let (base, op0) = Patch::add(1, "shared\n", AtomId::ROOT);
        h.commit(Patch::by(Author(0), [op0]));
        let g = h.replay();
        // tail atom both branches will point at (a rejoin).
        let (tail, opt) = Patch::add(9, "tail\n", AtomId::ROOT);
        // branch A: base -> a1 -> tail
        let (a1, opa1) = Patch::add(2, "a1\n", base);
        let a = Patch::by(
            Author(1),
            [opt.clone(), opa1, Op::Connect { from: a1, to: tail }],
        )
        .apply_to(&g);
        // branch B: base -> b1 -> tail
        let (b1, opb1) = Patch::add(4, "b1\n", base);
        let b = Patch::by(Author(2), [opt, opb1, Op::Connect { from: b1, to: tail }]).apply_to(&g);
        let merged = merge(&a, &b);

        let patch = crate::resolve_keep_in(&merged, Author(1), a1, &[b1]);
        let resolved = patch.apply_to(&merged);
        let text = content(&resolved).to_marked_string();
        assert!(text.contains("a1"), "kept branch present: {text:?}");
        assert!(!text.contains("b1"), "dropped branch gone: {text:?}");
        assert!(
            text.contains("tail"),
            "the SHARED rejoin atom survives: {text:?}"
        );
    }

    // ── TRUE bite: a genuine conflict yields ready resolutions that collapse it ──

    /// A two-way prose antichain offers keep-each (2) + order + order-swapped (2)
    /// = 4 choices, and EACH choice's patch collapses the conflict.
    #[test]
    fn a_prose_conflict_offers_resolutions_each_of_which_collapses_it() {
        // Two authors append a distinct line after a shared base => an antichain.
        let mut h = crate::History::new();
        let (base, op0) = Patch::add(1, "shared\n", AtomId::ROOT);
        h.commit(Patch::by(Author(0), [op0]));
        let g = h.replay();

        let (_a, opa) = Patch::add(2, "alpha\n", base);
        let (_b, opb) = Patch::add(3, "beta\n", base);
        let a = Patch::by(Author(1), [opa]).apply_to(&g);
        let b = Patch::by(Author(2), [opb]).apply_to(&g);
        let merged = merge(&a, &b);
        assert!(content(&merged).has_conflict(), "the two forks conflict");

        let region = content(&merged);
        let region = region.conflicts().next().unwrap();
        let choices = resolutions_for(&merged, region, Author(1));
        // keep alpha, keep beta, order, order-swapped.
        assert_eq!(choices.len(), 4, "two keeps + two orders: {choices:?}");
        assert_eq!(
            choices
                .iter()
                .filter(|c| matches!(c.resolution, Resolution::Keep { .. }))
                .count(),
            2
        );
        assert_eq!(
            choices.iter().filter(|c| c.keeps_all()).count(),
            2,
            "both order choices keep all alternatives"
        );

        // EACH choice's patch, applied, collapses the conflict.
        for c in &choices {
            let resolved = c.patch.apply_to(&merged);
            assert!(
                !content(&resolved).has_conflict(),
                "the choice {:?} collapses the conflict",
                c.label
            );
        }

        // The labels read the attributed text/author off the block.
        assert!(choices.iter().any(|c| c.label.contains("alpha")));
        assert!(choices.iter().any(|c| c.label.contains("beta")));
        assert!(choices.iter().any(|c| c.label.contains("keep both")));
    }

    /// A KEEP drops the other alternative; an ORDER keeps both — the rendered
    /// content after each is exactly the chosen reading.
    #[test]
    fn keep_drops_the_other_order_keeps_both() {
        let mut h = crate::History::new();
        let (base, op0) = Patch::add(1, "x\n", AtomId::ROOT);
        h.commit(Patch::by(Author(0), [op0]));
        let g = h.replay();
        let (_a, opa) = Patch::add(2, "alpha\n", base);
        let (_b, opb) = Patch::add(3, "beta\n", base);
        let a = Patch::by(Author(1), [opa]).apply_to(&g);
        let b = Patch::by(Author(2), [opb]).apply_to(&g);
        let merged = merge(&a, &b);

        let rendered = content(&merged);
        let region = rendered.conflicts().next().unwrap();
        let choices = resolutions_for(&merged, region, Author(1));

        let keep = choices
            .iter()
            .find(|c| matches!(&c.resolution, Resolution::Keep { .. }))
            .unwrap();
        let kept = keep.patch.apply_to(&merged);
        let kept_text = content(&kept).to_marked_string();
        // exactly one of the two survives (the other tombstoned).
        assert!(
            kept_text.contains("alpha\n") ^ kept_text.contains("beta\n"),
            "keep drops exactly one: {kept_text:?}"
        );

        let order = choices.iter().find(|c| c.keeps_all()).unwrap();
        let ordered = order.patch.apply_to(&merged);
        let otext = content(&ordered).to_marked_string();
        assert!(
            otext.contains("alpha\n") && otext.contains("beta\n"),
            "order keeps both: {otext:?}"
        );
    }

    /// A field clash offers one CHOOSE per distinct value; each settles the clash.
    #[test]
    fn a_field_conflict_offers_one_choose_per_value_each_settling_it() {
        let a = author_graph(Author(1), "---\ntitle: On Cats\n---\nbody\n");
        let b = author_graph(Author(2), "---\ntitle: On Dogs\n---\nbody\n");
        let merged = merge(&a, &b);
        let rendered = content(&merged);
        let region = rendered.field_conflicts().next().expect("a field clash");

        let choices = resolutions_for(&merged, region, Author(1));
        assert_eq!(
            choices.len(),
            2,
            "one choose per distinct value: {choices:?}"
        );
        for c in &choices {
            assert!(matches!(c.resolution, Resolution::ChooseField { .. }));
            let settled = c.patch.apply_to(&merged);
            assert!(
                !content(&settled).field_conflicts().next().is_some(),
                "the field clash is settled by {:?}",
                c.label
            );
        }
        assert!(choices.iter().any(|c| c.label.contains("On Cats")));
        assert!(choices.iter().any(|c| c.label.contains("On Dogs")));
    }

    /// The whole-document menu groups choices per region, in document order.
    #[test]
    fn resolutions_groups_choices_per_region() {
        // A prose antichain AND a field clash in one merged document.
        let a = author_graph(Author(1), "---\ntitle: Cats\n---\nshared\nalpha\n");
        let b = author_graph(Author(2), "---\ntitle: Dogs\n---\nshared\nbeta\n");
        let merged = merge(&a, &b);
        let rendered = content(&merged);

        let menu = resolutions(&merged, &rendered, Author(1));
        assert!(
            menu.len() >= 2,
            "at least a prose and a field region: {menu:?}"
        );
        assert!(menu.iter().any(|r| r.regime == Regime::Prose));
        let field = menu.iter().find(|r| r.regime == Regime::Field).unwrap();
        assert!(
            field.regime.needs_consensus(),
            "the field region is the real clash"
        );
        assert!(!field.choices.is_empty());
    }

    // ── FALSE bite: a clean document offers NOTHING (no laundered vacuity) ──

    #[test]
    fn a_clean_document_offers_no_resolutions() {
        let mut h = crate::History::new();
        let (a1, op1) = Patch::add(1, "hello ", AtomId::ROOT);
        h.commit(Patch::by(Author(1), [op1]));
        let (_a2, op2) = Patch::add(2, "world", a1);
        h.commit(Patch::by(Author(1), [op2]));
        let g = h.replay();
        let rendered = content(&g);
        assert!(!rendered.has_conflict());

        let menu = resolutions(&g, &rendered, Author(1));
        assert!(
            menu.is_empty(),
            "no conflict => no resolutions to fabricate"
        );
    }

    /// The resolution patch is authored by the resolver (it leaves a receipt under
    /// that author on the substrate).
    #[test]
    fn the_resolution_patch_is_authored_by_the_resolver() {
        let a = author_graph(Author(1), "---\ntitle: A\n---\nbody\n");
        let b = author_graph(Author(2), "---\ntitle: B\n---\nbody\n");
        let merged = merge(&a, &b);
        let rendered = content(&merged);
        let region = rendered.field_conflicts().next().unwrap();
        let choices = resolutions_for(&merged, region, Author(7));
        assert!(choices.iter().all(|c| c.patch.author == Author(7)));
    }
}
