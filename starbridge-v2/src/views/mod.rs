//! The cockpit's shared gpui primitives — palette + small render helpers.
//!
//! The comprehensive master-interface views live in [`crate::cockpit`]
//! (rendering the EMBEDDED `World` directly). This module keeps only the
//! palette/pill/section-title primitives the cockpit consumes.

use gpui::{div, Hsla, IntoElement, ParentElement, Styled};

/// The shell's palette (a dark ocap console) — **THE ONLY PLACE THESE HEXES ARE
/// WRITTEN.**
///
/// Every cockpit-family surface reads from here: `dock::theme` re-exports it,
/// and `guest` · `showcase` · `self_hosting` · `unified_boot` · `replay` · the
/// two bake views in `main.rs` all `use crate::views::theme`. Enforced by
/// [`one_palette_gate`] below, which scans `starbridge-v2/src` and fails naming
/// any other file that types one of these literals.
///
/// NOT the deos-desktop palette. The NT/Pharo workbench
/// (`deos_desktop::chrome`) is a DIFFERENT surface on purpose — teal void,
/// button-face gray, dark-on-light — and its `NT_*` constants are its own single
/// source of truth. The two must not be merged.
///
/// `gpui::rgb` is not `const` in this gpui rev, so these are functions
/// returning `Hsla` (the type `bg`/`text_color`/`border_color` all accept via
/// `Into<Hsla>` / `Into<Background>`).
pub mod theme {
    use gpui::{rgb, rgba, Hsla};
    pub fn bg() -> Hsla {
        rgb(0x0e1116).into()
    }
    pub fn panel() -> Hsla {
        rgb(0x161b22).into()
    }
    pub fn panel_hi() -> Hsla {
        rgb(0x1f2630).into()
    }
    pub fn border() -> Hsla {
        rgb(0x2b3340).into()
    }
    pub fn text() -> Hsla {
        rgb(0xd7dee8).into()
    }
    pub fn muted() -> Hsla {
        rgb(0x7d8794).into()
    }
    pub fn accent() -> Hsla {
        rgb(0x6cb6ff).into()
    }
    pub fn good() -> Hsla {
        rgb(0x57d977).into()
    }
    pub fn warn() -> Hsla {
        rgb(0xe3b341).into()
    }
    pub fn bad() -> Hsla {
        rgb(0xe5534b).into()
    }

    /// [`bg`] at 53% alpha — the scrim a modal/overlay lays over the surface it
    /// dims (`guest`'s command sheet). Derived from `bg`'s own hex so a palette
    /// change carries the scrim with it.
    pub fn scrim() -> Hsla {
        rgba(0x0e111688).into()
    }

    /// ⚠ **MEASURED DRIFT, PRESERVED — a THIRD green, not a synonym for
    /// [`good`].** `unified_boot`'s hand-transcribed palette had its `good()` at
    /// `0x5bd18b` while every sibling copy had `0x57d977`: rgb(91,209,139) vs
    /// rgb(87,217,119), so Δ = (+4, −8, +20) — visibly mintier, ~20/255 more
    /// blue. Nobody chose that; it is a transcription that diverged and then got
    /// read as "the same palette" for as long as both copies existed.
    ///
    /// Folding it onto [`good`] would move a rendered pixel, which the
    /// de-duplication pass that found it was not allowed to do — so it is kept
    /// bit-exact and named HERE, where the two greens sit three lines apart and
    /// the choice between them is a colour decision someone can actually make.
    /// Collapsing it to [`good`] is a one-line change once that decision exists.
    pub fn good_mint() -> Hsla {
        rgb(0x5bd18b).into()
    }

    /// The **capability-facet** family — the five colours a surface tags an
    /// affordance with by which authority it exercises (ok/value/auth/avail/
    /// know). A semantic axis over the base palette, not a second palette:
    /// [`facet::avail`] IS [`accent`], by call rather than by re-typing it.
    pub mod facet {
        use super::{accent, Hsla};
        use gpui::rgb;

        /// ⚠ **DRIFT, PRESERVED — a SECOND-order variant of [`super::good`]:**
        /// `0x57d97f` vs `0x57d977`, one hex digit, rgb(87,217,127) against
        /// rgb(87,217,119) — Δ = (0, 0, +8), invisible on a screen and exactly
        /// the shape of a mis-typed transcription. It appeared identically in
        /// `guest` and `showcase`, so it is a copied typo, not two mistakes.
        /// Kept bit-exact for the same reason [`super::good_mint`] is.
        pub fn ok() -> Hsla {
            rgb(0x57d97f).into()
        }
        pub fn value() -> Hsla {
            rgb(0xf2c14e).into()
        }
        pub fn auth() -> Hsla {
            rgb(0xff8b6b).into()
        }
        /// Deliberately the base [`super::accent`] — the availability facet and
        /// the shell accent are ONE blue, said once.
        pub fn avail() -> Hsla {
            accent()
        }
        pub fn know() -> Hsla {
            rgb(0xc792ea).into()
        }
    }
}

/// A small section header used across the rail and panels. Returns a `Div` so
/// callers can keep styling it (`.mb_1()` etc.).
pub fn section_title(text: impl Into<String>) -> gpui::Div {
    div()
        .text_xs()
        .text_color(theme::muted())
        .child(text.into())
}

/// A status pill — colored by ok/warn/bad.
pub fn pill(text: impl Into<String>, color: Hsla) -> impl IntoElement {
    div()
        .px_2()
        .py_0p5()
        .rounded_md()
        .bg(theme::panel_hi())
        .text_xs()
        .text_color(color)
        .child(text.into())
}

/// **ONE PALETTE — the gate.**
///
/// The GitHub-dark hexes above were hand-transcribed into eight places (seven
/// `mod theme`/`mod palette` blocks plus two inline `let` runs in `main.rs`), and
/// three of them had already drifted to a *different* green while every reviewer
/// read them as "the same palette". This test walks the crate's own source and
/// asserts each palette literal occurs in exactly ONE file — this one.
///
/// It fails on a *new* transcription as well as a re-introduced old one: a
/// contributor who types `rgb(0x161b22)` anywhere else in `starbridge-v2/src`
/// gets a red test naming their file, whether or not the value they typed agrees
/// with ours today.
///
/// Gated the same way every copy it scans is (`any(gpui-ui, gpui-web)`), so the
/// cfg the gate runs under is exactly the cfg the palette exists under — there is
/// no configuration in which a copy compiles and this test does not.
#[cfg(test)]
mod one_palette_gate {
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};

    /// Every hex the palette owns — the ten canonical values, the three DRIFTED
    /// greens preserved verbatim beside them, and the capability-facet family.
    /// Listed as `&str` so the gate scans for the *source text*, which is the
    /// thing that gets copied.
    const PALETTE_HEXES: &[&str] = &[
        // the ten canonical GitHub-dark values
        "0x0e1116", "0x161b22", "0x1f2630", "0x2b3340", "0xd7dee8", "0x7d8794", "0x6cb6ff",
        "0x57d977", "0xe3b341", "0xe5534b", // the measured drift, kept beside its sibling
        "0x5bd18b", "0x57d97f", // the capability-facet family
        "0xf2c14e", "0xff8b6b", "0xc792ea",
    ];

    /// The one file allowed to hold them, relative to `starbridge-v2/`.
    const CANONICAL: &str = "src/views/mod.rs";

    fn src_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src")
    }

    fn rust_sources(dir: &Path, out: &mut Vec<PathBuf>) {
        let entries = std::fs::read_dir(dir)
            .unwrap_or_else(|e| panic!("the gate must be able to read {}: {e}", dir.display()));
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                rust_sources(&path, out);
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push(path);
            }
        }
    }

    #[test]
    fn the_palette_literals_live_in_exactly_one_file() {
        let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let mut sources = Vec::new();
        rust_sources(&src_dir(), &mut sources);
        assert!(
            sources.len() > 50,
            "the gate scanned only {} files — it is not looking at the real tree",
            sources.len()
        );

        let mut offenders: BTreeSet<String> = BTreeSet::new();
        for path in &sources {
            let rel = path
                .strip_prefix(&manifest)
                .unwrap_or(path)
                .to_string_lossy()
                .replace('\\', "/");
            if rel == CANONICAL {
                continue;
            }
            let body = std::fs::read_to_string(path).unwrap_or_default();
            let lower = body.to_ascii_lowercase();
            for hex in PALETTE_HEXES {
                if lower.contains(hex) {
                    offenders.insert(format!("{rel} holds {hex}"));
                }
            }
        }

        assert!(
            offenders.is_empty(),
            "the palette is transcribed outside {CANONICAL} in {} place(s) — read them from \
             `crate::views::theme` instead of re-typing the hex:\n  {}",
            offenders.len(),
            offenders.into_iter().collect::<Vec<_>>().join("\n  ")
        );
    }

    /// **The drift is three greens, and they must STAY three.**
    ///
    /// The fold that made this the one palette had to keep two hand-transcribed
    /// greens bit-exact, because collapsing them would have moved a rendered
    /// pixel. That leaves `good` · `good_mint` · `facet::ok` sitting near each
    /// other, two of them looking like typos — which is exactly the shape a
    /// future tidy-up deletes without measuring anything.
    ///
    /// This is not a pin against its own definition: it asserts a RELATION
    /// between three separately-authored values, so it goes red the moment one
    /// is aliased to another. When someone decides the greens should be one
    /// green, they delete this test on purpose and say so in the commit.
    #[test]
    fn the_three_greens_stay_three_until_someone_chooses() {
        use crate::views::theme::{accent, facet, good, good_mint};
        assert_ne!(
            good(),
            good_mint(),
            "good_mint is `unified_boot`'s DRIFTED green (rgb 91,209,139 vs \
             87,217,119) kept bit-exact by the de-duplication pass — aliasing it \
             to good() changes what the unified-boot bake paints"
        );
        assert_ne!(
            good(),
            facet::ok(),
            "facet::ok is the capability-facet green, one hex digit off good() \
             (rgb 87,217,127 vs 87,217,119) — a copied transcription typo, kept \
             bit-exact for the same reason"
        );
        assert_ne!(
            good_mint(),
            facet::ok(),
            "the two drifts are distinct drifts"
        );
        assert_eq!(
            facet::avail(),
            accent(),
            "the availability facet IS the shell accent, by call and not by a \
             sixth transcription — if these ever differ, someone re-typed it"
        );
    }

    /// The gate above is only worth its runtime if the canonical file actually
    /// holds the values — otherwise "exactly one file" could be satisfied by
    /// ZERO. Pins the ten canonical hexes present at the canonical path.
    #[test]
    fn the_canonical_file_is_the_one_that_holds_them() {
        let canonical = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(CANONICAL);
        let body = std::fs::read_to_string(&canonical)
            .unwrap_or_else(|e| panic!("{} must be readable: {e}", canonical.display()))
            .to_ascii_lowercase();
        for hex in PALETTE_HEXES {
            assert!(
                body.contains(hex),
                "{CANONICAL} must hold {hex} — the gate is vacuous if the canonical home is empty"
            );
        }
    }
}
