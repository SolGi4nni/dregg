//! The hypermedia + tooling panels: proofs, web-of-cells, what-links-here, powerbox, the ⌘K palette overlay, buffer/terminal/editor panes.

use super::*;

impl Cockpit {
    /// THE PROOFS panel — the proof-attach + STARK verification-status board.
    /// Each committed turn's verification tier (verified-by-construction /
    /// executor-signed / STARK-attached) + the honest route to the next tier.
    /// See [`starbridge_v2::proofs`].
    pub(crate) fn proofs_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let board = starbridge_v2::proofs::ProofBoard::build(&w, 16);
        let mut col = div()
            .id("cockpit-scroll-body-16")
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title("PROOFS · attach + STARK verification status").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
            "{} verified-by-construction · {} signed · {} STARK-attached",
            board.by_construction, board.signed, board.stark_attached
        )));
        if board.is_empty() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .px_2()
                    .mt_1()
                    .child("(no committed turns yet)"),
            );
        }
        for e in &board.entries {
            let tier_color = match e.tier {
                starbridge_v2::proofs::VerificationTier::StarkAttached => theme::good(),
                starbridge_v2::proofs::VerificationTier::ExecutorSigned => theme::accent(),
                starbridge_v2::proofs::VerificationTier::VerifiedByConstruction => theme::text(),
            };
            col = col.child(
                div()
                    .flex()
                    .flex_col()
                    .px_2()
                    .py_0p5()
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::text())
                                    .child(format!("h{} · {}", e.height, e.receipt_short)),
                            )
                            .child(div().text_xs().text_color(tier_color).child(e.tier.label())),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(e.summary()),
                    ),
            );
            if let Some(route) = e.upgrade_route() {
                col = col.child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .px_3()
                        .child(format!("→ next: {route}")),
                );
            }
        }
        col
    }

    /// THE WEB-OF-CELLS BROWSER panel — the cockpit as a native browser of the
    /// `dregg://` docuverse. It browses the live image's cells AS the web of
    /// cells: each cell is a `dregg://` page (the real [`starbridge_web_surface`]
    /// attested fetch + ledger-drawn origin chrome), an opened cell shows its
    /// per-viewer affordance surface (the real `AffordanceSurface::project_for`
    /// progressive attenuation) + its derived rehydration liveness-type + a
    /// transcluded field, and FIRING an affordance runs through THIS crate's
    /// embedded executor (the seam the web crate could only model, closed). The
    /// transclusion row carries the SEMI-REINTERACTIVE "⚡ make interactive" button:
    /// it runs the real
    /// [`WebCellsBrowser::upgrade_transclusion_via_powerbox`](starbridge_v2::web_cells::WebCellsBrowser::upgrade_transclusion_via_powerbox)
    /// so the
    /// user confers an ATTENUATED affordance cap reaching the transcluded SOURCE into
    /// the HOST document (a read-only quote becomes act-on-able via a powerbox grant —
    /// held-authority + non-amplification enforced by the real powerbox + executor),
    /// after which the host may fire exactly the granted affordance on the source and
    /// no wider. The model is built gpui-free in [`starbridge_v2::web_cells`] (so it is
    /// `cargo test`-able); this maps it onto gpui. See [`starbridge_v2::web_cells`].
    pub(crate) fn web_of_cells_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let viewer = self.anchors[2]; // the "user" principal the cockpit browses as
        let rights = self.web_cells_viewer_rights.clone();
        let browser = {
            let w = self.world.borrow();
            starbridge_v2::web_cells::WebCellsBrowser::build(
                &w,
                viewer,
                rights.clone(),
                self.web_cells_opened,
            )
        };
        let is_root = matches!(rights, dregg_cell::AuthRequired::None);

        let mut col = div()
            .id("cockpit-scroll-body-17")
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col
            .child(section_title("WEB-OF-CELLS · browse the dregg:// docuverse natively").mb_1());
        // The viewer + tier header, with the "view as root/editor" toggle that
        // reveals/hides the attenuated affordances (the property, made tangible).
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(pill(
                    format!("viewer {}", reflect::short_hex(&viewer.0)),
                    theme::accent(),
                ))
                .child(pill(
                    format!("holds {}", browser.viewer_tier),
                    theme::good(),
                ))
                .child(
                    Button::new("web-cells-tier-toggle")
                        .label(if is_root {
                            "view as EDITOR (attenuate)"
                        } else {
                            "view as ROOT (reveal all)"
                        })
                        .primary()
                        .xsmall()
                        .on_click(cx.listener(|this, _ev: &ClickEvent, _w, cx| {
                            this.web_cells_viewer_rights = match this.web_cells_viewer_rights {
                                dregg_cell::AuthRequired::None => dregg_cell::AuthRequired::Either,
                                _ => dregg_cell::AuthRequired::None,
                            };
                            // The conferred tier of a ⚡ upgrade is the viewer's
                            // tier; changing it invalidates a prior grant — drop
                            // the upgrade so re-pressing ⚡ confers the new tier.
                            this.web_cells_upgraded = None;
                            this.web_cells_transclusion_outcome = None;
                            cx.notify();
                        })),
                ),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "A dregg:// link is a CAPABILITY into a cell; fetching it is a verified, \
             attested cross-cell read. The origin chrome is drawn from the LEDGER, never \
             the page. You see exactly the affordances your caps authorize.",
        ));

        // The web-of-cells fire outcome banner (a REAL executor verdict).
        if let Some(banner) = &self.web_cells_outcome {
            let good = banner.starts_with("committed");
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .text_xs()
                    .text_color(if good { theme::good() } else { theme::warn() })
                    .child(banner.clone()),
            );
        }

        // ── THE ADDRESSABLE CELLS (the dregg:// rows; clicking opens one) ──
        col = col.child(
            section_title(format!(
                "addressable cells · {} dregg:// pages",
                browser.cells.len()
            ))
            .mt_2()
            .mb_1(),
        );
        for row in &browser.cells {
            let opened = browser.opened == Some(row.cell);
            let cell = row.cell;
            let att_color = if row.attested {
                theme::good()
            } else {
                theme::bad()
            };
            col =
                col.child(
                    div()
                        .id(SharedString::from(format!(
                            "web-cell-{}",
                            reflect::short_hex(&cell.0)
                        )))
                        .flex()
                        .flex_col()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(if opened {
                            theme::panel_hi()
                        } else {
                            theme::panel()
                        })
                        .border_1()
                        .border_color(if opened {
                            theme::accent()
                        } else {
                            theme::border()
                        })
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::panel_hi()))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev, _w, cx| {
                                this.web_cells_opened = Some(cell);
                                this.web_cells_outcome = None;
                                // Opening a different cell changes the transclusion
                                // (a new host/source); drop any stale powerbox upgrade
                                // so the ⚡ interactive state never mismatches the row.
                                this.web_cells_upgraded = None;
                                this.web_cells_transclusion_outcome = None;
                                cx.notify();
                            }),
                        )
                        .child(
                            div()
                                .flex()
                                .justify_between()
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(theme::text())
                                        .child(row.chrome_badge.clone()),
                                )
                                .child(div().text_xs().text_color(att_color).child(
                                    if row.attested {
                                        "✓ attested"
                                    } else {
                                        "⚠ unattested"
                                    },
                                )),
                        )
                        .child(
                            div()
                                .text_xs()
                                .text_color(theme::muted())
                                .child(row.preview.clone()),
                        ),
                );
        }

        // ── THE OPENED CELL'S AFFORDANCE SURFACE (per-viewer projection) ──
        if let Some(opened) = browser.opened {
            col = col.child(
                section_title(format!(
                    "opened dregg://{} · affordance surface",
                    reflect::short_hex(&opened.0)
                ))
                .mt_2()
                .mb_1(),
            );
            col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
                "you see {} of {} declared affordances — the rest are ATTENUATED away by your caps (progressive enhancement → progressive attenuation)",
                browser.affordances.len(),
                browser.affordances_declared,
            )));
            for aff in &browser.affordances {
                let name = aff.name.clone();
                let opened_cell = opened;
                let viewer_id = viewer;
                let viewer_rights = rights.clone();
                col = col.child(
                    div()
                        .flex()
                        .items_center()
                        .justify_between()
                        .px_2()
                        .py_0p5()
                        .child(
                            div().flex().flex_col().child(
                                div()
                                    .text_xs()
                                    .text_color(theme::text())
                                    .child(format!("{} → {}", aff.name, aff.effect)),
                            ).child(
                                div()
                                    .text_xs()
                                    .text_color(theme::muted())
                                    .child(format!("requires {}", aff.required)),
                            ),
                        )
                        .child(
                            // THE FIRE BUTTON — fires the affordance through the
                            // REAL embedded executor (the closed seam).
                            Button::new(SharedString::from(format!("web-fire-{name}")))
                                .label("▶ fire")
                                .success()
                                .xsmall()
                                .on_click(
                                    cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                                        let banner = {
                                            let mut w = this.world.borrow_mut();
                                            match starbridge_v2::web_cells::WebCellsBrowser::fire_affordance(
                                                &mut w,
                                                opened_cell,
                                                viewer_id,
                                                viewer_rights.clone(),
                                                &name,
                                            ) {
                                                Ok(o) if o.is_committed() => {
                                                    format!("committed: fired '{name}' → real verified turn")
                                                }
                                                Ok(starbridge_v2::affordance::FireOutcome::Refused { reason, .. }) => {
                                                    format!("refused by executor: '{name}' — {reason}")
                                                }
                                                Ok(_) => format!("committed: fired '{name}'"),
                                                Err(e) => format!("refused in-band (anti-ghost): '{name}' — {e}"),
                                            }
                                        };
                                        this.web_cells_outcome = Some(banner);
                                        this.refresh_cells();
                                        cx.notify();
                                    }),
                                ),
                        ),
                );
            }

            // The rehydration liveness-type (DERIVED from the attested fetch).
            col = col.child(div().mt_1().px_2().child(pill(
                format!("rehydration: {}", browser.rehydration_badge),
                theme::accent(),
            )));

            // ── THE TED-NELSON TRANSCLUSION (one transcluded field + provenance) ──
            if let Some(t) = &browser.transclusion {
                col = col.child(
                    section_title("transclusion · a field included from another cell")
                        .mt_2()
                        .mb_1(),
                );
                col = col.child(
                    div()
                        .flex()
                        .items_center()
                        .justify_between()
                        .gap_1()
                        .child(div().text_xs().text_color(theme::text()).child(format!(
                            "this cell transcludes field {} from dregg://{}",
                            t.transcluded_field,
                            reflect::short_hex(&t.source.0),
                        )))
                        // ▶ FOLLOW the forward link: OPEN the transcluded SOURCE cell's
                        // live attested page in the browser — the transclusion BROWSES
                        // to where it quotes from (Engelbart/Nelson's link you can click).
                        // The quote stays a verified READ; this just navigates to the
                        // source's own `dregg://` affordance surface.
                        .child(
                            Button::new(SharedString::from(format!(
                                "transclusion-open-source-{}",
                                reflect::short_hex(&t.source.0)
                            )))
                            .label("▶ open source")
                            .ghost()
                            .xsmall()
                            .on_click({
                                let source = t.source;
                                cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                                    this.open_cell_in_browser(source, cx);
                                })
                            }),
                        ),
                );
                col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
                    "provenance receipt {} · source finalized={} (the inclusion is CHECKABLE, not trusted)",
                    t.provenance_receipt, t.source_finalized,
                )));

                // ── SEMI-REINTERACTIVE UPGRADE (the ⚡ "make interactive" button) ──
                //
                // A plain transclusion is a READ-ONLY quote — the free verified
                // observation (a quote is a read, not a key). Pressing ⚡ runs a REAL
                // `Powerbox::grant` (via `upgrade_transclusion_via_powerbox`) so the
                // user confers an ATTENUATED affordance cap reaching the SOURCE into
                // the HOST document's c-list — the host can then FIRE one of the
                // source's affordances, attenuated to what the user holds, and no
                // wider. The conferred tier is the viewer's current tier (the
                // "view as ROOT/EDITOR" toggle), so the attenuation is the user's own
                // authority. The `view` affordance (the Signature-tier default) is the
                // one made act-on-able. Held-authority + non-amplification are enforced
                // by the real powerbox + executor — a denial leaves the quote read-only.
                let upgraded_here = self.web_cells_upgraded.as_ref().filter(|u| {
                    u.read.host == t.host && u.read.source == t.source && u.interactive
                });
                match upgraded_here {
                    // INTERACTIVE: the powerbox granted — show the conferred state +
                    // a button that fires the granted affordance on the SOURCE through
                    // the real embedded executor (and refuses any wider affordance).
                    Some(upgraded) => {
                        let fire_name = upgraded
                            .granted_affordance
                            .clone()
                            .unwrap_or_else(|| "view".to_string());
                        col = col.child(
                            div()
                                .mt_1()
                                .px_2()
                                .py_0p5()
                                .rounded_md()
                                .bg(theme::panel_hi())
                                .text_xs()
                                .text_color(theme::good())
                                .child(upgraded.affordance_note()),
                        );
                        let fire_name_btn = fire_name.clone();
                        col = col.child(
                            div().mt_1().child(
                            Button::new("web-transclusion-fire")
                                .label(format!("▶ fire `{fire_name}` on the source"))
                                .success()
                                .xsmall()
                                .on_click(
                                    cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                                        let banner = match this.web_cells_upgraded.clone() {
                                            Some(up) => {
                                                let mut w = this.world.borrow_mut();
                                                match starbridge_v2::web_cells::WebCellsBrowser::fire_transcluded_affordance(
                                                    &mut w,
                                                    &up,
                                                    &fire_name_btn,
                                                ) {
                                                    Ok(o) if o.is_committed() => format!(
                                                        "committed: fired `{fire_name_btn}` on the transcluded source → real verified turn"
                                                    ),
                                                    Ok(starbridge_v2::affordance::FireOutcome::Refused { reason, .. }) => format!(
                                                        "refused by executor: `{fire_name_btn}` — {reason}"
                                                    ),
                                                    Ok(_) => format!("committed: fired `{fire_name_btn}`"),
                                                    Err(e) => format!(
                                                        "refused in-band (anti-ghost): `{fire_name_btn}` — {e}"
                                                    ),
                                                }
                                            }
                                            None => "no upgraded transclusion to fire".to_string(),
                                        };
                                        this.web_cells_transclusion_outcome = Some(banner);
                                        this.refresh_cells();
                                        cx.notify();
                                    }),
                                ),
                            ),
                        );
                    }
                    // READ-ONLY: offer the ⚡ upgrade. Pressing it runs the real
                    // powerbox grant through THIS crate's embedded executor.
                    None => {
                        col = col.child(div().text_xs().text_color(theme::muted()).child(
                            "READ-ONLY: this verified quote is free. Make it act-on-able with a \
                             powerbox-granted, attenuated affordance cap (a real grant turn).",
                        ));
                        let host = t.host;
                        let source = t.source;
                        let field = t.transcluded_field.clone();
                        let receipt = t.provenance_receipt.clone();
                        let finalized = t.source_finalized;
                        let confer = rights.clone();
                        col = col.child(
                            div().mt_1().child(
                            Button::new("web-transclusion-make-interactive")
                                .label("⚡ make interactive (powerbox-grant a source affordance)")
                                .primary()
                                .xsmall()
                                .on_click(
                                    cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                                        // Reconstruct the read-only quote for the
                                        // currently-shown transclusion + UPGRADE it via
                                        // the POWERBOX: confer the viewer's tier over the
                                        // source so the host may fire `view`, attenuated.
                                        let read = starbridge_v2::web_cells::Transclusion {
                                            host,
                                            source,
                                            transcluded_field: field.clone(),
                                            provenance_receipt: receipt.clone(),
                                            source_finalized: finalized,
                                        };
                                        let principal = this.anchors[2]; // the cockpit user (granter)
                                        let banner = {
                                            let mut w = this.world.borrow_mut();
                                            match starbridge_v2::web_cells::WebCellsBrowser::upgrade_transclusion_via_powerbox(
                                                &mut w,
                                                read,
                                                principal,
                                                "view",
                                                confer.clone(),
                                            ) {
                                                Ok(upgraded) => {
                                                    let note = upgraded.affordance_note();
                                                    this.web_cells_upgraded = Some(upgraded);
                                                    format!("upgraded via powerbox: {note}")
                                                }
                                                Err((still_read_only, reason)) => {
                                                    this.web_cells_upgraded = Some(still_read_only);
                                                    format!("powerbox refused the upgrade: {reason}")
                                                }
                                            }
                                        };
                                        this.web_cells_transclusion_outcome = Some(banner);
                                        this.refresh_cells();
                                        cx.notify();
                                    }),
                                ),
                            ),
                        );
                    }
                }

                // The transclusion-upgrade / transcluded-fire outcome banner (a REAL
                // powerbox grant-turn verdict, or the in-band read-only/over-wide refusal).
                if let Some(banner) = &self.web_cells_transclusion_outcome {
                    let good = banner.starts_with("upgraded") || banner.starts_with("committed");
                    col = col.child(
                        div()
                            .mt_1()
                            .px_2()
                            .py_0p5()
                            .rounded_md()
                            .bg(theme::panel_hi())
                            .text_xs()
                            .text_color(if good { theme::good() } else { theme::warn() })
                            .child(banner.clone()),
                    );
                }
            }
        }

        // ── THE DREGGVERSE DOCUMENT (Nelson's EDL made honest — the rich span
        //    model welded in from `deos-web-cells`) ──
        //
        // Where the transclusion above is ONE whole-field quote, this is a MULTI-SPAN
        // document: OWN content interleaved with byte-RANGE quotes of peer cells,
        // resolved PER-VIEWER through the REAL membrane. A span the viewer's projected
        // fetch-allowlist cannot reach renders DARKENED — its provenance survives (the
        // citation), its bytes withheld (never forged). The model is built gpui-free in
        // `starbridge_v2::web_cells` (so the composed text + the darkened span + the
        // surviving provenance are `cargo test`-proven); this maps it onto gpui.
        if let Some(doc) = &browser.document {
            col = col.child(section_title(doc.title.clone()).mt_2().mb_1());

            // The per-viewer summary pills: the document's shape + how much of it THIS
            // viewer can read (a darkened span ⇒ "not fully readable for you").
            col = col.child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .child(pill(format!("{} spans", doc.span_count), theme::accent()))
                    .child(pill(
                        format!("{} verified quotes", doc.quote_count),
                        theme::good(),
                    ))
                    .child(pill(
                        if doc.darkened_count == 0 {
                            "fully readable".to_string()
                        } else {
                            format!("{} darkened (per-viewer)", doc.darkened_count)
                        },
                        if doc.full {
                            theme::good()
                        } else {
                            theme::warn()
                        },
                    )),
            );

            // The composed text THIS viewer sees (OWN + reachable quotes; a darkened
            // span contributes nothing — the honest per-viewer render).
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(theme::text())
                    .child(format!("\u{201C}{}\u{201D}", doc.composed_text)),
            );

            // The EDL, span by span — OWN content, a verified quote (with its cited
            // byte range + provenance), or a DARKENED span (citation kept, bytes
            // withheld). Each row is styled by kind so the docuverse skeleton is
            // visible: the reader sees WHICH spans exist + where they are quoted from,
            // even the one they cannot read.
            for span in &doc.spans {
                let row = match span.kind {
                    starbridge_v2::web_cells::DocumentSpanKind::Own => div()
                        .text_xs()
                        .text_color(theme::text())
                        .child(format!("own · \u{201C}{}\u{201D}", span.text)),
                    starbridge_v2::web_cells::DocumentSpanKind::Quote => div()
                        .text_xs()
                        .text_color(theme::good())
                        .child(format!(
                            "quote {} · \u{201C}{}\u{201D} · from {} · commitment {} · receipt {}",
                            span.range.as_deref().unwrap_or("?"),
                            span.text,
                            span.source.as_deref().unwrap_or("?"),
                            span.content_commitment.as_deref().unwrap_or("?"),
                            span.provenance_receipt.as_deref().unwrap_or("?"),
                        )),
                    starbridge_v2::web_cells::DocumentSpanKind::Darkened => div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(format!(
                            "darkened {} · [you lack authority to read this span] · cites {} · commitment {} · receipt {}",
                            span.range.as_deref().unwrap_or("?"),
                            span.source.as_deref().unwrap_or("?"),
                            span.content_commitment.as_deref().unwrap_or("?"),
                            span.provenance_receipt.as_deref().unwrap_or("?"),
                        )),
                };
                col = col.child(row.mt_0p5().px_2());
            }

            // The per-viewer authority note — WHY some spans darken (the real membrane
            // fetch-allowlist meet, never a forgery).
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(doc.viewer_note.clone()),
            );
        }

        // ── THE SERVO LAYER ──
        // With feature `servo` ON and a rendered tile present, paint the REAL
        // cap-gated SWGL frame of the opened cell's attested `dregg://` page —
        // the first real rendered `dregg://` CONTENT in the tab. Otherwise
        // (feature-off, or the cap refused the page so no frame) fall back to the
        // servo_layer_note() placeholder that NAMES the next layer.
        #[cfg(feature = "servo")]
        let servo_tile: Option<gpui::AnyElement> = browser.rendered_tile.as_ref().map(|frame| {
            div()
                .mt_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(theme::good())
                .bg(theme::panel())
                .child(div().text_xs().text_color(theme::good()).child(
                    "SERVO: real cap-gated SWGL render of the opened cell's attested dregg:// page",
                ))
                .child(
                    gpui::img(rgba_frame_to_image(frame))
                        .w(gpui::px(frame.width as f32))
                        .h(gpui::px(frame.height as f32)),
                )
                .into_any_element()
        });
        #[cfg(not(feature = "servo"))]
        let servo_tile: Option<gpui::AnyElement> = None;

        col = col.child(servo_tile.unwrap_or_else(|| {
            div()
                .mt_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(theme::border())
                .bg(theme::panel())
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(browser.servo_layer_note()),
                )
                .into_any_element()
        }));
        col
    }

    /// THE WHAT-LINKS-HERE panel — Ted Nelson's two-way link, navigable.
    ///
    /// For the focused cell it renders the REAL [`Backlinks`] witness-graph (who
    /// transcludes ME), navigated by the genuine
    /// [`DreggverseMap`](starbridge_v2::dreggverse_map::DreggverseMap) and PROJECTED
    /// through the focused agent's [`Membrane`] via
    /// [`DreggverseMap::project_for`](starbridge_v2::dreggverse_map::DreggverseMap::project_for):
    /// a backlink whose link lineage the viewer's held authority cannot admit (the
    /// REAL `is_attenuation` lattice) is OMITTED — the link fog-of-war. Each visible
    /// backlink carries its cited receipt + content commitment (a verifiable fact) and
    /// is CLICKABLE to navigate INTO the observing cell (whose own what-links-here then
    /// renders — recursive docuverse navigation). The cockpit owns the render +
    /// click-to-navigate; the verified per-viewer graph is the vendored map's. The
    /// model is built gpui-free in [`starbridge_v2::links_here`] (so it is `cargo
    /// test`-able); this maps it onto gpui.
    ///
    /// The viewer authority is the panel's own held-authority lens
    /// (`links_here_viewer_rights`, None ⇄ Signature): the focus's backlinks are gated
    /// behind a `Proof` link lineage, so a `None` (root) viewer projects it and SEES
    /// them while an INCOMPARABLE `Signature` viewer is FOGGED — flipping the toggle
    /// reveals/fogs the gated backlink, the membrane made navigational. The focused
    /// cell defaults to the cockpit's own `user` principal.
    pub(crate) fn links_here_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let focus = self.links_here_focus.unwrap_or(self.anchors[2]); // the cockpit `user`
        let rights = self.links_here_viewer_rights.clone();
        let depth = self.links_here_depth;
        let panel = {
            let w = self.world.borrow();
            starbridge_v2::links_here::LinksHerePanel::build(&w, focus, rights.clone(), depth)
        };
        let is_root = matches!(rights, dregg_cell::AuthRequired::None);

        let mut col = div()
            .id("cockpit-scroll-body-18")
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col
            .child(section_title("WHAT-LINKS-HERE · Ted Nelson's two-way link, navigable").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The forward link points OUT (a cell transcludes another). This is the link the \
             OTHER way — who transcludes ME — the REAL Backlinks witness-graph, navigated by \
             DreggverseMap and PROJECTED through your membrane. Each backlink carries its cited \
             receipt + content commitment (a verifiable fact). Click a backlink to navigate into \
             the observing cell.",
        ));

        // ── THE FOCUS + VIEWER HEADER (with the held-authority + depth toggles) ──
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(pill(
                    format!("focus {}", reflect::short_hex(&focus.0)),
                    theme::accent(),
                ))
                .child(pill(format!("holds {}", panel.viewer_tier), theme::good()))
                .child(pill(format!("depth {}", panel.depth), theme::accent()))
                // The held-authority toggle (None ⇄ Signature): the viewer's authority
                // decides the link fog-of-war. At ROOT (None) the Proof-gated backlinks
                // are visible; dropping to the INCOMPARABLE Signature tier FOGS them
                // (the membrane refuses the lineage) — the property made tangible.
                .child(
                    Button::new("links-here-tier-toggle")
                        .label(if is_root {
                            "view as SIGNATURE (fog the gated links)"
                        } else {
                            "view as ROOT (reveal all)"
                        })
                        .primary()
                        .xsmall()
                        .on_click(cx.listener(|this, _ev: &ClickEvent, _w, cx| {
                            this.links_here_viewer_rights = match this.links_here_viewer_rights {
                                dregg_cell::AuthRequired::None => {
                                    dregg_cell::AuthRequired::Signature
                                }
                                _ => dregg_cell::AuthRequired::None,
                            };
                            cx.notify();
                        })),
                )
                // The depth toggle (1 ⇄ 2 ⇄ 3): how many hops of backlinks-of-backlinks
                // the transitive walk reaches. The walk is cycle-safe + depth-bounded.
                .child(
                    Button::new("links-here-depth-toggle")
                        .label("cycle depth")
                        .primary()
                        .xsmall()
                        .on_click(cx.listener(|this, _ev: &ClickEvent, _w, cx| {
                            // 1 → 2 → 3 → 1 (a small, finite, demonstrable range).
                            this.links_here_depth = match this.links_here_depth {
                                0 | 1 => 2,
                                2 => 3,
                                _ => 1,
                            };
                            cx.notify();
                        })),
                ),
        );

        // The focus address + a "navigate to user (home focus)" affordance so the
        // operator can always return to the principal's docuverse after drilling in.
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .mt_1()
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::text())
                        .child(format!("asking: who links to {} ?", panel.focus_uri)),
                )
                .child(
                    Button::new("links-here-refocus-user")
                        .label("↺ focus the user principal")
                        .ghost()
                        .xsmall()
                        .on_click(cx.listener(|this, _ev: &ClickEvent, _w, cx| {
                            this.links_here_focus = None; // None = the user anchor
                            cx.notify();
                        })),
                ),
        );

        // ── THE VISIBLE-OF-TOTAL READOUT (the fog made legible) ──
        let fogged = panel.fogged_count();
        col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
            "you see {} of {} backlink(s) within {} hop(s) — {} fogged by your caps · {} navigable node(s)",
            panel.backlinks.len(),
            panel.total_link_count,
            panel.depth,
            fogged,
            panel.visible_nodes,
        )));
        if panel.has_gated_links && fogged > 0 {
            col = col.child(div().text_xs().text_color(theme::warn()).child(
                "some backlinks are GATED behind a link lineage your held authority cannot project \
                 — the membrane omits them (try 'view as ROOT'). This is the link fog-of-war: two \
                 viewers navigate DIFFERENT maps of the same docuverse.",
            ));
        }

        // ── THE BACKLINK ROWS (each clickable to navigate INTO the observer) ──
        if panel.is_empty() {
            col = col.child(
                div()
                    .mt_2()
                    .px_2()
                    .py_1()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(
                        "no backlinks visible to you — nobody you are cleared to see transcludes \
                         this cell (an honest empty readout, never a dangling guess).",
                    ),
            );
        } else {
            col = col.child(
                section_title(format!(
                    "backlinks · {} two-way link(s) you can see",
                    panel.backlinks.len()
                ))
                .mt_2()
                .mb_1(),
            );
        }
        for b in &panel.backlinks {
            let observer = b.observer;
            col = col.child(
                div()
                    .id(SharedString::from(format!(
                        "links-here-{}",
                        reflect::short_hex(&observer.0)
                    )))
                    .flex()
                    .flex_col()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(theme::border())
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::panel_hi()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            // NAVIGATE INTO the observing cell — render ITS own
                            // what-links-here (recursive docuverse navigation).
                            this.links_here_focus = Some(observer);
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .items_center()
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::accent())
                                    .child(format!("← {}", b.observer_uri)),
                            )
                            .child(
                                div()
                                    .flex()
                                    .items_center()
                                    .gap_1()
                                    .child(
                                        div()
                                            .text_xs()
                                            .text_color(theme::muted())
                                            .child(format!("hop {}", b.hops)),
                                    )
                                    // ▶ OPEN the cited (observing) cell's LIVE attested
                                    // page in the web-of-cells browser — the backlink
                                    // BROWSES, not just refocuses. Clicking takes you to
                                    // the cell's `dregg://` affordance surface + its
                                    // transcluded content (the real attested read).
                                    .child(
                                        Button::new(SharedString::from(format!(
                                            "links-open-{}",
                                            reflect::short_hex(&observer.0)
                                        )))
                                        .label("▶ open")
                                        .ghost()
                                        .xsmall()
                                        .on_click(cx.listener(
                                            move |this, _ev: &ClickEvent, _w, cx| {
                                                // Swallow the row's own refocus: this is
                                                // the BROWSE action (open the live page),
                                                // not the recursive-refocus action.
                                                this.open_cell_in_browser(observer, cx);
                                            },
                                        )),
                                    ),
                            ),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(format!(
                        "transcludes dregg://{} · receipt {} · commitment {}",
                        reflect::short_hex(&b.source.0),
                        b.receipt_hash,
                        b.content_hash,
                    ))),
            );
        }

        // ── THE SEEDED-GRAPH NOTE (named honestly in the panel) ──
        col = col.child(
            div()
                .mt_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(theme::border())
                .bg(theme::panel())
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(panel.seeded_note()),
                ),
        );
        col
    }

    /// THE POWERBOX panel (CapDesk) — the trusted designation flow, rendered.
    ///
    /// The cockpit `user` principal is the GRANTING identity; a confined demo
    /// app-cell (`powerbox_app`) is the requester. The panel presents the powerbox
    /// over the live world: the app's request, then the picker of GRANTABLE targets
    /// (every cell the USER actually holds a cap reaching — `mint_needs_held_factory`
    /// made visible). Designating a target MINTS a fresh attenuated cap into the
    /// app's c-list via a REAL [`Powerbox::grant`] turn through the embedded executor
    /// — the conferral is `≤` the user's held authority (the powerbox refuses to
    /// amplify; the executor is the backstop). The panel content is exactly the
    /// powerbox model's [`Powerbox::all_text`], so the gpui-free `cargo test` proves
    /// the rendered tree without a GPU.
    pub(crate) fn powerbox_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        use starbridge_v2::powerbox::{CapabilityRequest, Powerbox};

        let principal = self.anchors[2]; // the cockpit's own `user` identity — the granter
        let app = self.powerbox_app.unwrap_or(principal); // the confined requester (a demo app-as-cell)
        let confer = self.powerbox_confer_rights.clone();

        // The app's standing request (it holds no authority; it can only ask). If `app`
        // was LAUNCHED at runtime (via the app-launcher), use ITS OWN recorded request
        // (the real `CapabilityRequest` the launched confined app raised) — so the panel
        // routes the genuine launched-app request through the existing powerbox; the
        // boot-seeded demo app falls back to the standing demo request.
        let request = self
            .launched_apps
            .iter()
            .find(|a| a.app_cell == app)
            .map(|a| a.request.clone())
            .unwrap_or_else(|| {
                CapabilityRequest::new(
                    app,
                    "this app needs to reach one peer/resource — designate exactly one",
                    dregg_cell::AuthRequired::None,
                )
            });
        let pb = {
            let w = self.world.borrow();
            Powerbox::present(&w, principal, &request)
        };
        let launched_count = self.launched_apps.len();

        let mut col = div()
            .id("cockpit-scroll-body-19")
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(
            section_title("POWERBOX · CapDesk — designate a held cap into a confined app").mb_1(),
        );
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(pill(
                    format!("you (granter) {}", reflect::short_hex(&principal.0)),
                    theme::accent(),
                ))
                .child(pill(
                    format!("app (requester) {}", reflect::short_hex(&app.0)),
                    theme::good(),
                ))
                // The confer-tier toggle: the rights the next designation confers. The
                // grant is ≤ the user's held authority; the powerbox refuses to amplify
                // past the held ceiling, so a wider tier than the user holds is refused.
                .child(
                    Button::new("powerbox-tier-toggle")
                        .label(format!("confer: {confer:?} (cycle)"))
                        .primary()
                        .xsmall()
                        .on_click(cx.listener(|this, _ev: &ClickEvent, _w, cx| {
                            // Cycle Signature → Either → None → Signature: from the
                            // narrowest (a strong attenuation) up through the wider
                            // tiers (still gated by the held ceiling + the executor).
                            this.powerbox_confer_rights = match this.powerbox_confer_rights {
                                dregg_cell::AuthRequired::Signature => {
                                    dregg_cell::AuthRequired::Either
                                }
                                dregg_cell::AuthRequired::Either => dregg_cell::AuthRequired::None,
                                _ => dregg_cell::AuthRequired::Signature,
                            };
                            cx.notify();
                        })),
                )
                // THE RUNTIME APP-LAUNCHER button — birth a fresh confined app (no
                // ambient authority) and route ITS request through this powerbox. The
                // powerbox's missing first half: spawn the confined requester on demand.
                .child(
                    Button::new("powerbox-launch-app")
                        .label("+ launch confined app")
                        .success()
                        .xsmall()
                        .on_click(cx.listener(|this, _ev: &ClickEvent, _w, cx| {
                            // Births a fresh confined app-cell + routes its request
                            // through the existing powerbox (sets it as powerbox_app).
                            this.run_launch_confined_app(cx);
                        })),
                ),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The app holds NO ambient authority — it can only ASK. The powerbox (this \
             trusted UI, NOT the app) can grant ONLY from YOUR own held caps: you can't \
             grant what you don't hold (mint_needs_held_factory). Designating a target \
             MINTS a fresh ATTENUATED cap into the app via a real verified grant turn. \
             Press '+ launch confined app' to SPAWN a new confined app at runtime (it \
             holds nothing — it requests through this powerbox).",
        ));
        // The runtime-launched apps roster (each a fresh confined app birthed on demand).
        if launched_count > 0 {
            col = col.child(div().text_xs().text_color(theme::accent()).child(format!(
                "{launched_count} confined app(s) launched at runtime · now mediating: {}",
                reflect::short_hex(&app.0)
            )));
        }
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .italic()
                .child(format!("reason: {}", pb.reason)),
        );

        // The last designation outcome banner (a REAL grant-turn verdict).
        if let Some(banner) = &self.powerbox_outcome {
            let good = banner.starts_with("granted");
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .text_xs()
                    .text_color(if good { theme::good() } else { theme::warn() })
                    .child(banner.clone()),
            );
        }

        // ── THE PICKER: every target the USER holds (the only things designable) ──
        col = col.child(
            section_title(format!(
                "designate a target you hold · {} grantable (you can't grant what you don't hold)",
                pb.grantable.len()
            ))
            .mt_2()
            .mb_1(),
        );
        if pb.grantable.is_empty() {
            col = col.child(div().text_xs().text_color(theme::warn()).child(
                "(you hold no grantable targets — the powerbox can confer nothing, by construction)",
            ));
        }
        for g in &pb.grantable {
            let target = g.target;
            let held = g.held_rights.clone();
            let confer_now = confer.clone();
            col = col.child(
                div()
                    .id(SharedString::from(format!(
                        "powerbox-target-{}",
                        reflect::short_hex(&target.0)
                    )))
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(theme::border())
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::panel_hi()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            // THE DESIGNATION: mint a fresh attenuated cap into the app
                            // via a REAL grant turn through the embedded executor.
                            let outcome = {
                                let mut w = this.world.borrow_mut();
                                Powerbox::grant(
                                    &mut w,
                                    this.anchors[2],
                                    this.powerbox_app.unwrap_or(this.anchors[2]),
                                    target,
                                    this.powerbox_confer_rights.clone(),
                                )
                            };
                            this.powerbox_outcome = Some(match outcome {
                                starbridge_v2::powerbox::PowerboxOutcome::Granted {
                                    conferred,
                                    receipt,
                                } => format!(
                                    "granted: app {} now holds {:?} reaching {} (slot {}) — receipt {}",
                                    reflect::short_hex(&conferred.app_cell.0),
                                    conferred.conferred_rights,
                                    reflect::short_hex(&conferred.target.0),
                                    conferred.slot,
                                    reflect::short_hex(&receipt.receipt_hash())
                                ),
                                starbridge_v2::powerbox::PowerboxOutcome::Denied { reason } => {
                                    format!("denied: {reason}")
                                }
                            });
                            this.refresh_cells();
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::text())
                            .child(format!("{}  (you hold {:?})", g.label, held)),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(format!("→ grant {confer_now:?}")),
                    ),
            );
        }

        col
    }

    /// THE ⌘K COMMAND PALETTE overlay — a centered, fuzzy-filtered list over
    /// EVERY action. Rendered on top of the cockpit when open. The query +
    /// selection live in `self.palette`; keystrokes are handled in [`on_key`];
    /// a click on a row also dispatches it.
    pub(crate) fn palette_overlay(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let results = self.palette.results();
        let selected = self.palette.selected();
        let query = self.palette.query().to_string();

        // A full-screen scrim that closes the palette on a click-out.
        let scrim = div()
            .id("palette-scrim")
            .absolute()
            .top_0()
            .left_0()
            .size_full()
            .bg(gpui::rgba(0x00000088))
            .flex()
            .flex_col()
            .items_center()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, _ev, _w, cx| {
                    this.palette.close();
                    cx.notify();
                }),
            );

        // The palette card. It is a FIXED-height flex column (not merely
        // `max_h`): the result `uniform_list` below grows into the leftover
        // space via `flex_1`, and a virtualizing list needs a DEFINITE parent
        // height to compute how many rows are visible. With only a `max_h` the
        // column shrank to its content (header + footer) and the list resolved
        // to a 0-height box — it virtualized to zero rows (the empty-palette
        // regression). A concrete `h` gives the flex child a real main-size.
        let mut card = div()
            .id("palette-card")
            .mt(px(120.))
            .w(px(560.))
            .h(px(440.))
            .flex()
            .flex_col()
            .rounded_md()
            .border_1()
            .border_color(theme::accent())
            .bg(theme::panel())
            // Swallow clicks on the card so they don't reach the scrim's close.
            .on_mouse_down(MouseButton::Left, |_ev, _w, cx| cx.stop_propagation());

        // The query line.
        card = card.child(
            div()
                .flex()
                .justify_between()
                .px_3()
                .py_2()
                .border_b_1()
                .border_color(theme::border())
                .child(div().text_color(theme::text()).child(if query.is_empty() {
                    "⌘K  type to search every action…".to_string()
                } else {
                    format!("⌘K  {query}▌")
                }))
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(format!("{} match", results.len())),
                ),
        );

        // The results list. EVERY matched command is reachable: the rows live
        // in a `uniform_list` that virtualizes + scrolls (mouse-wheel AND ↑/↓),
        // not a fixed `.take(12)` slice that silently drops the rest. The
        // selected row is scrolled into view by `on_key` via `palette_scroll`.
        if results.is_empty() {
            card = card.child(
                div()
                    .p_1()
                    .child(
                        div()
                            .px_2()
                            .py_1()
                            .text_xs()
                            .text_color(theme::muted())
                            .child("(no matching action — Esc to close)"),
                    ),
            );
        } else {
            // Each row needs to know the command id it dispatches; clone the
            // ids into the closure so the virtualizing list can build rows on
            // demand as it scrolls.
            let ids: Vec<CommandId> = results.iter().map(|h| h.command.id).collect();
            let titles: Vec<&'static str> = results.iter().map(|h| h.command.title).collect();
            let categories: Vec<Category> = results.iter().map(|h| h.command.category).collect();
            let row_count = results.len();

            let list = uniform_list(
                "palette-results",
                row_count,
                cx.processor(move |this, range: std::ops::Range<usize>, _w, cx| {
                    let mut rows = Vec::with_capacity(range.end - range.start);
                    for i in range {
                        let active = i == selected;
                        let (badge, bcolor) = category_badge(categories[i]);
                        let id = ids[i];
                        let title = titles[i];
                        rows.push(
                            div()
                                .id(SharedString::from(format!("palette-row-{i}")))
                                .flex()
                                .justify_between()
                                .items_center()
                                .px_2()
                                .py_1()
                                .mx_1()
                                .rounded_md()
                                .bg(if active {
                                    theme::panel_hi()
                                } else {
                                    theme::panel()
                                })
                                .cursor_pointer()
                                .hover(|s| s.bg(theme::border()))
                                .on_mouse_down(
                                    MouseButton::Left,
                                    cx.listener(move |this, _ev, _w, cx| {
                                        this.palette.close();
                                        this.dispatch(id, cx);
                                        cx.notify();
                                    }),
                                )
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(if active {
                                            theme::accent()
                                        } else {
                                            theme::text()
                                        })
                                        .child(format!(
                                            "{} {}",
                                            if active { "▸" } else { " " },
                                            title
                                        )),
                                )
                                .child(pill(badge, bcolor))
                                .into_any_element(),
                        );
                    }
                    let _ = this;
                    rows
                }),
            )
            .track_scroll(&self.palette_scroll)
            // Take the leftover height between the query line and the footer.
            // `flex_1` + `min_h_0` gives the list a DEFINITE resolved height
            // inside the fixed-height card (the parent flex column), which the
            // virtualizing `uniform_list` needs to compute its visible row
            // window — without it the list is 0-height and renders no rows.
            .flex_1()
            .min_h_0()
            .py_1();
            card = card.child(list);
        }

        // Footer hint.
        card = card.child(
            div()
                .px_3()
                .py_1()
                .border_t_1()
                .border_color(theme::border())
                .text_xs()
                .text_color(theme::muted())
                .child("↑↓ select · ⏎ run · esc close"),
        );

        scrim.child(card)
    }

    /// THE A1 EDITOR/BUFFER panel — a text buffer as a cap-confined Surface cell.
    /// Maps `buffer::BufferView` (gpui-free) onto gpui: the buffer header (its
    /// backing cell, revision, read-only/dirty badges, digests), the cap-gated
    /// action row (type · commit · the read-only-write REFUSE teaching moment),
    /// and the buffer body (the editable text, with line numbers). You watch the
    /// authenticated digest advance through a verified turn — not a self-report.
    pub(crate) fn buffer_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let v = BufferView::build(&self.editor_buffer, &w, Some(&self.editor_buffer_cap));
        drop(w);

        let mut col = div()
            .id("cockpit-scroll-body-20")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col
            .child(section_title("EDITOR · a text buffer as a cap-confined Surface cell").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The buffer is backed by a REAL cell: its content DIGEST rides the cell's state, and \
             its REVISION is the cell's nonce. Editing the text is free (in-memory); COMMITTING is \
             a CAP-GATED verified turn (a SetField writing the digest). A read-only buffer holds an \
             ATTENUATED cap — a write to it REFUSES (no-amplification at the editor).",
        ));

        // The buffer header: backing cell, state, badges, digests.
        let backed_color = if v.backed {
            theme::good()
        } else {
            theme::bad()
        };
        let rw_badge = if v.read_only {
            ("read-only", theme::warn())
        } else {
            ("writable", theme::good())
        };
        let clean_badge = if v.clean {
            ("clean", theme::good())
        } else {
            ("DIRTY (unsaved)", theme::warn())
        };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(v.name.clone(), theme::accent()))
                .child(pill(format!("cell {}", v.backing_short), theme::text()))
                .child(pill(
                    if v.backed { "live" } else { "UNBACKED" }.to_string(),
                    backed_color,
                ))
                .child(pill(rw_badge.0, rw_badge.1))
                .child(pill(clean_badge.0, clean_badge.1))
                .child(pill(format!("rev {}", v.revision), theme::muted())),
        );
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child("doc digest"),
                )
                .child(pill(v.doc_digest_short.clone(), theme::accent()))
                .when(v.stored_digest_short.is_some(), |d| {
                    d.child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child("committed"),
                    )
                    .child(pill(v.stored_digest_short.clone().unwrap(), theme::good()))
                }),
        );

        // The cap-gated action row.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .mt_1()
                .child(shell_button(
                    cx,
                    "type a line",
                    theme::accent(),
                    Cockpit::buffer_type_demo,
                ))
                .child(shell_button(
                    cx,
                    "commit (cap-gated turn)",
                    theme::good(),
                    Cockpit::buffer_commit,
                ))
                .child(shell_button(
                    cx,
                    "⚠ read-only write (REFUSE)",
                    theme::warn(),
                    Cockpit::buffer_readonly_write_demo,
                )),
        );

        // The buffer body: the editable text with line numbers.
        col = col.child(section_title("buffer (the surface content)").mt_2());
        let mut body = div()
            .flex()
            .flex_col()
            .gap_0p5()
            .p_2()
            .rounded_md()
            .bg(theme::panel());
        for (i, line) in v.lines.iter().enumerate() {
            body = body.child(
                div()
                    .flex()
                    .gap_2()
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .w(px(28.))
                            .child(format!("{:>3}", i + 1)),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::text())
                            .font_family("Menlo")
                            .child(line.clone()),
                    ),
            );
        }
        col = col.child(body);
        col = col.child(
            div().text_xs().text_color(theme::muted()).mt_1().child(format!(
                "cursor @ byte {} · {} line(s) — the digest above is what a COMMIT would bind into the cell",
                v.cursor,
                v.lines.len()
            )),
        );
        col
    }

    /// THE A1 TERMINAL panel — a command surface as a cap-confined Surface cell
    /// (the home of the ADOS tool-call seam). Maps `terminal::TerminalView`
    /// (gpui-free) onto gpui: the terminal header (its backing cell + its
    /// MANDATE — the targets it may reach), the cap-gated action row (an
    /// in-mandate command COMMITS; an out-of-mandate one REFUSES), and the output
    /// body (each command + its REAL receipt, or its REFUSAL — never faked).
    pub(crate) fn terminal_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let v = TerminalView::build(&self.terminal, &w);
        drop(w);

        let mut col = div()
            .id("cockpit-scroll-body-21")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(
            section_title("TERMINAL · a command surface as a cap-confined Surface cell").mb_1(),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "A command is a CAP-GATED action: the terminal-cell holds the cap for what it may run / \
             touch, and the output is its receipt. This is WHERE THE ADOS TOOL-CALL SEAM LIVES — an \
             agent's Bash routed through the terminal-cell's cap. A command whose target is within \
             the cell's mandate COMMITS (its receipt is the output); one outside it REFUSES.",
        ));

        // The terminal header: backing cell + the mandate (reachable targets).
        let backed_color = if v.backed {
            theme::good()
        } else {
            theme::bad()
        };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(v.name.clone(), theme::accent()))
                .child(pill(format!("cell {}", v.backing_short), theme::text()))
                .child(pill(
                    if v.backed { "live" } else { "UNBACKED" }.to_string(),
                    backed_color,
                ))
                .child(pill(
                    format!("{} committed", v.committed_count),
                    theme::good(),
                )),
        );
        col = col.child(section_title("mandate — the targets this terminal may reach").mt_1());
        let mut mandate = div().flex().flex_wrap().gap_1().items_center();
        for t in &v.reachable_short {
            mandate = mandate.child(pill(format!("→ {t}"), theme::accent()));
        }
        col = col.child(mandate);

        // The cap-gated action row.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .mt_1()
                .child(shell_button(
                    cx,
                    "run in-mandate (COMMITS)",
                    theme::good(),
                    Cockpit::terminal_run_in_mandate,
                ))
                .child(shell_button(
                    cx,
                    "⚠ run out-of-mandate (REFUSE)",
                    theme::warn(),
                    Cockpit::terminal_run_out_of_mandate,
                )),
        );

        // The output body: commands + receipts / refusals (oldest-first).
        col = col.child(section_title("output (commands + receipts — the surface content)").mt_2());
        if v.lines.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "no commands yet — run one above; an in-mandate target COMMITS, an out-of-mandate one REFUSES.",
            ));
        } else {
            let mut body = div().flex().flex_col().gap_0p5();
            for l in &v.lines {
                let (mark, mark_color) = if l.committed {
                    ("$", theme::good())
                } else {
                    ("✗", theme::bad())
                };
                body = body.child(
                    div()
                        .flex()
                        .flex_col()
                        .gap_0p5()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(mark_color).child(mark))
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(theme::text())
                                        .font_family("Menlo")
                                        .child(l.command.clone()),
                                )
                                .when(l.committed, |d| {
                                    d.child(pill(format!("{} ⚙", l.computrons), theme::muted()))
                                })
                                .when(l.receipt_short().is_some(), |d| {
                                    d.child(pill(l.receipt_short().unwrap(), theme::good()))
                                }),
                        )
                        .child(
                            div()
                                .text_xs()
                                .text_color(if l.committed {
                                    theme::muted()
                                } else {
                                    theme::bad()
                                })
                                .font_family("Menlo")
                                .child(l.result.clone()),
                        ),
                );
            }
            col = col.child(body);
        }
        col
    }

    /// THE LIVE EDITOR panel — `edit::render_panel` is gpui-free text; the
    /// cockpit presents it line-by-line.
    pub(crate) fn editor_panel(&self) -> impl IntoElement {
        let text = edit::render_panel(&self.editor);
        let mut col = div()
            .id("cockpit-scroll-body-22")
            .flex()
            .flex_col()
            .p_3()
            .size_full()
            .overflow_y_scroll();
        col = col.child(section_title("LIVE EDITOR · author · validate · deploy").mb_1());
        for line in text.lines() {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::text())
                    .font_family("Menlo")
                    .child(line.to_string()),
            );
        }
        col
    }
}
