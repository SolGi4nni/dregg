//! **The graphideOS SystemUI cap-chrome — the deos cockpit AS the android system UI.**
//!
//! `GRAPHIDEOS.md §1` (the SystemUI row) + `§2` stage 4: in graphideOS, *SystemUI*
//! (status bar, quick-settings shade, the permission surface) is not a privileged
//! Android process — it is **the deos cockpit chrome**, and the phone's permission UI
//! IS the deos cap surface. Stage 4's *model* half (the lit/dim cap-badge set + the
//! receipted hand-over) is already real in [`android_cell::permgate`]; this module is
//! the **chrome** half: it dresses a confined android-cell's live cap-badge set as the
//! two SystemUI surfaces a phone user actually sees —
//!
//! 1. **the status bar** — the always-visible compact strip ([`SystemUiCapChrome::status_bar`]):
//!    `🛡 held/total caps` plus the lit glyphs of what the running app holds RIGHT NOW.
//!    The authority is on the app's face, never buried.
//! 2. **the quick-settings shade** — the pull-down ([`SystemUiCapChrome::quick_settings`]):
//!    the WHOLE permission roster, each badge lit (●, held) or dim (○, not held), with the
//!    never-hidden [`android_cell::BadgeReason`] beside it. This is the "no hidden Settings
//!    tree" property `GRAPHIDEOS.md §1` names: you do not dig through a toggle forest, you
//!    pull down the shade and SEE every authority the app does and does not hold.
//! 3. **the hand-over sheet** — the powerbox ceremony ([`SystemUiCapChrome::grant_sheet`] +
//!    [`SystemUiCapChrome::hand_over`]): the dangerous, declared-but-dim caps render as the
//!    grant rows; tapping one is a **receipted hand-over turn**, NOT a modal dialog. The
//!    hand-over routes straight through [`android_cell::PermWorld::grant`], which mints a
//!    genuine [`Effect::GrantCapability`] from the device principal to the android-cell and
//!    commits it through the verified `TurnExecutor`, so the permission cap LANDS in the
//!    app's real c-list with a kernel `TurnReceipt` and the badge flips to lit because the
//!    cell GENUINELY holds the cap. There is no parallel grant path; the executor is the
//!    authority. This is the cockpit's [`crate::powerbox`] ceremony, in the android
//!    permission idiom.
//!
//! [`Effect::GrantCapability`]: android_cell may name it via `dregg_turn`
//!
//! # Reuse, not reinvention
//!
//! This is presentation/app layer over machinery this workspace already PROVES: the
//! cap-badge derivation + the powerbox `mint_needs_held_factory` teeth ([`android_cell::permgate`]),
//! and the verified `Effect::GrantCapability` executor (the SAME one [`crate::powerbox`]
//! commits through). No new kernel effect, no new authority. The chrome is a pure
//! projection: a status bar and a shade are just two renderings of one
//! [`android_cell::CapBadgeSet`], and a hand-over is one already-verified turn.
//!
//! # gpui-free, `cargo test`-able (the established pattern)
//!
//! Like [`crate::powerbox`] and [`crate::deos_desktop::android_window`], this is the
//! pure flow + render-text model: it computes exactly the rows the cockpit chrome
//! paints ([`SystemUiCapChrome::all_text`]) and drives the real hand-over, with NO gpui.
//! The `cargo test` below asserts the chrome renders an app's held caps and that a
//! hand-over flips a dim badge lit via a REAL kernel grant — that proves the surface
//! without a GPU, exactly as the powerbox flow test does.
//!
//! ## The cockpit-chrome gpui wire (the one named seam, for the `native-full` body)
//!
//! The gpui arm is ~30 lines of glue over this module's pure rows, mirroring
//! [`crate::cockpit`]'s `powerbox_panel`:
//! - **status bar:** a thin top strip — `div().flex().child(chrome.status_bar().summary)`
//!   then one `pill(badge.glyph_label(), if lit {good} else {muted})` per held badge.
//! - **quick-settings shade:** a pull-down column — one row per `chrome.quick_settings()`
//!   line (`● LOCATION — held by hand-over` / `○ CAMERA — not declared …`).
//! - **hand-over sheet:** one button per `chrome.grant_sheet()` row whose
//!   `.on_click` calls `chrome.hand_over(row.permission)` (the real `Effect::GrantCapability`)
//!   then `cx.notify()` so the badge repaints lit. A revoke row mirrors it.
//!   That body is the collision-free `native-full` follow-up; THIS module is the
//!   load-bearing logic + the bake (`src/bin/systemui_cap_bake.rs`).

use android_cell::{
    AndroidManifest, AndroidPermission, BadgeReason, BadgeState, CapBadge, CapBadgeSet,
    KernelGrantOutcome, PermWorld, ProtectionLevel,
};

/// **The status bar — the always-visible compact cap strip.** The phone's top edge:
/// a `🛡 held/total` summary plus the lit glyphs of the authorities the running app
/// holds right now. The user reads the app's standing authority at a glance, never
/// having to go looking (the anti-"hidden in Settings" property, in its most compact form).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatusBar {
    /// `🛡 N/M caps` — held over total recognised.
    pub summary: String,
    /// The lit authorities, as short glyph-labels (`● NET`, `● LOCATION`), in roster order.
    pub held: Vec<String>,
    /// How many recognised authorities are dim (not held) — the rest of the roster.
    pub dim_count: usize,
}

impl StatusBar {
    /// The whole status bar as one line (the compact render + the test/bake surface).
    pub fn line(&self) -> String {
        if self.held.is_empty() {
            format!("{} · (no caps held)", self.summary)
        } else {
            format!("{} · {}", self.summary, self.held.join("  "))
        }
    }
}

/// **One row in the hand-over sheet — a dangerous, declared-but-dim cap the user can
/// hand over.** Exactly the powerbox's grantable surface, in the android idiom: only a
/// permission the manifest declared but the app does not yet hold appears (a `Normal`
/// install-held cap is already lit and needs no sheet; an undeclared one is un-grantable
/// — no ambient escalation). Tapping it drives [`SystemUiCapChrome::hand_over`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrantSheetRow {
    /// The permission this row would hand over.
    pub permission: AndroidPermission,
    /// The short glyph-label the sheet renders (`○ CAMERA`).
    pub label: String,
    /// The faithful AOSP protection level (always `Dangerous`/`Signature` here).
    pub level: ProtectionLevel,
    /// The human prompt the sheet shows ("hand over CAMERA — the app declared it but
    /// does not hold it; this mints a real cap into the app's c-list").
    pub prompt: String,
}

/// **THE SYSTEMUI CAP-CHROME for one running android-cell.** Wraps a live
/// [`android_cell::PermWorld`] (a real ledger + the verified `TurnExecutor`) and the app's
/// human label, and renders the three SystemUI surfaces over it: the status bar, the
/// quick-settings shade, and the hand-over sheet. Holds NO ambient authority — every
/// hand-over is the principal's own held device-authority, conferred through the real
/// executor (the powerbox tooth, as the backstop).
pub struct SystemUiCapChrome {
    /// The real kernel permission world — the live c-list the badges read + the executor
    /// the hand-over commits through.
    world: PermWorld,
    /// The app's human label, shown in the chrome (e.g. "Maps · com.example.maps").
    app_label: String,
}

impl SystemUiCapChrome {
    /// Wrap an existing [`PermWorld`] as the SystemUI chrome for an app labelled `app_label`.
    pub fn new(app_label: impl Into<String>, world: PermWorld) -> Self {
        SystemUiCapChrome {
            world,
            app_label: app_label.into(),
        }
    }

    /// **Install a confined android-cell and dress it as SystemUI chrome in one act.**
    /// Births the android-cell (empty c-list, confined) + the device principal (holding
    /// `principal_holds`) into a fresh real ledger via [`PermWorld::install`], and wraps it.
    /// `package` is the manifest package id; `permissions` is the declared `<uses-permission>`
    /// set (what is even grantable); `principal_holds` is the device authority the system
    /// principal can confer (you cannot hand over what you do not hold).
    pub fn install(
        app_label: impl Into<String>,
        package: &str,
        app_seed: u8,
        principal_seed: u8,
        permissions: impl IntoIterator<Item = AndroidPermission>,
        principal_holds: impl IntoIterator<Item = AndroidPermission>,
    ) -> Self {
        let manifest = AndroidManifest::new(package, permissions);
        let world = PermWorld::install(app_seed, principal_seed, manifest, principal_holds);
        SystemUiCapChrome::new(app_label, world)
    }

    /// The app's human label.
    pub fn app_label(&self) -> &str {
        &self.app_label
    }

    /// The live cap-badge set read from the android-cell's REAL c-list (the source of
    /// both SystemUI renders).
    pub fn badges(&self) -> CapBadgeSet {
        self.world.badges()
    }

    /// **RENDER THE STATUS BAR** — the compact always-visible cap strip.
    pub fn status_bar(&self) -> StatusBar {
        let set = self.badges();
        let total = set.badges.len();
        let held: Vec<String> = set.held().map(glyph_label).collect();
        let held_n = held.len();
        StatusBar {
            summary: format!("🛡 {held_n}/{total} caps"),
            held,
            dim_count: total.saturating_sub(held_n),
        }
    }

    /// **RENDER THE QUICK-SETTINGS SHADE** — the WHOLE roster, each badge lit/dim with
    /// its never-hidden reason. One line per recognised permission (`● LOCATION — held by
    /// hand-over` / `○ CAMERA — not declared (un-grantable, no ambient escalation)`). This
    /// is the "no hidden Settings tree": every authority, shown, the only question lit vs dim.
    pub fn quick_settings(&self) -> Vec<String> {
        self.badges()
            .badges
            .iter()
            .map(|b| format!("{} — {}", glyph_label(b), reason_text(b.reason)))
            .collect()
    }

    /// **THE HAND-OVER SHEET** — the dangerous, declared-but-dim caps the user can hand
    /// over (the powerbox's grantable rows, in the android idiom). A `Normal` install-held
    /// cap is already lit (no sheet row); an undeclared one is un-grantable (no row).
    pub fn grant_sheet(&self) -> Vec<GrantSheetRow> {
        self.badges()
            .badges
            .iter()
            .filter(|b| b.reason == BadgeReason::DeclaredNotGranted)
            .map(|b| GrantSheetRow {
                permission: b.permission.clone(),
                label: glyph_label(b),
                level: b.level,
                prompt: format!(
                    "hand over {} — the app declared it but does not hold it; this mints a real \
                     cap into the app's c-list (a receipted turn, not a dialog)",
                    perm_short(&b.permission)
                ),
            })
            .collect()
    }

    /// **TAP A SHEET ROW → HAND OVER THE CAP (the dialog, reforged).** Drive the REAL
    /// kernel hand-over: [`PermWorld::grant`] builds a genuine `Effect::GrantCapability`
    /// from the device principal to the android-cell and commits it through the verified
    /// executor. On commit the cap lands in the app's c-list and its badge flips lit; the
    /// executor's `mint_needs_held_factory` / no-amplification gates are the backstop.
    /// Returns the kernel outcome (carrying the `TurnReceipt` on success).
    pub fn hand_over(&mut self, permission: AndroidPermission) -> KernelGrantOutcome {
        self.world.grant(permission)
    }

    /// A one-line banner for a hand-over outcome — the verdict the chrome shows after a tap.
    pub fn outcome_line(outcome: &KernelGrantOutcome) -> String {
        match outcome {
            KernelGrantOutcome::Granted {
                permission, slot, ..
            } => format!(
                "✔ {} HANDED OVER — a real cap landed in the app's c-list at slot {slot} (the badge lights; no dialog)",
                perm_short(permission)
            ),
            KernelGrantOutcome::AlreadyHeldAtInstall { permission } => format!(
                "● {} already held at install (a normal permission) — no hand-over needed",
                perm_short(permission)
            ),
            KernelGrantOutcome::RefusedNotDeclared { permission } => format!(
                "✖ {} REFUSED — the app never declared it; there is no cap to hold (no ambient escalation)",
                perm_short(permission)
            ),
            KernelGrantOutcome::RefusedByKernel { permission, reason } => format!(
                "✖ {} REFUSED by the executor — the device principal cannot back it ({reason})",
                perm_short(permission)
            ),
        }
    }

    /// **EVERY LINE OF CHROME, FLATTENED** — the status bar, the quick-settings shade, and
    /// the hand-over sheet, as the cockpit paints them. The bake/test surface (the gpui body
    /// maps these onto a top strip + a shade + a sheet of buttons).
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(format!("── SystemUI · {} ──", self.app_label));
        out.push(format!("[status bar] {}", self.status_bar().line()));
        out.push(
            "[quick settings — pull down the shade; every authority shown, lit ● or dim ○]".into(),
        );
        for line in self.quick_settings() {
            out.push(format!("  {line}"));
        }
        let sheet = self.grant_sheet();
        if sheet.is_empty() {
            out.push("[hand-over sheet] (nothing to hand over — no declared-but-dim cap)".into());
        } else {
            out.push(format!(
                "[hand-over sheet — {} cap(s) the device principal can hand over, each a receipted turn]",
                sheet.len()
            ));
            for row in sheet {
                out.push(format!("  {} · {}", row.label, row.prompt));
            }
        }
        out
    }
}

/// A badge's compact glyph-label for the chrome (`● NET`, `○ CAMERA`): the lit/dim glyph
/// plus the short authority name.
fn glyph_label(b: &CapBadge) -> String {
    format!("{} {}", b.state.glyph(), perm_short(&b.permission))
}

/// The short, human authority name the chrome shows (`INTERNET` → `NET`, the last dotted
/// segment otherwise) — the status bar wants a glance-readable token, not the FQ string.
fn perm_short(p: &AndroidPermission) -> String {
    match p {
        AndroidPermission::Internet => "NET".to_string(),
        AndroidPermission::AccessFineLocation => "LOCATION".to_string(),
        AndroidPermission::Camera => "CAMERA".to_string(),
        AndroidPermission::RecordAudio => "MIC".to_string(),
        AndroidPermission::ReadContacts => "CONTACTS".to_string(),
        AndroidPermission::ReadExternalStorage => "READ-STORAGE".to_string(),
        AndroidPermission::WriteExternalStorage => "WRITE-STORAGE".to_string(),
        AndroidPermission::Other(_) => {
            let name = p.android_name();
            name.rsplit('.').next().unwrap_or(&name).to_string()
        }
    }
}

/// The never-hidden audit reason text the quick-settings shade shows beside each badge.
fn reason_text(reason: BadgeReason) -> &'static str {
    match reason {
        BadgeReason::HeldAtInstall => "held at install (a normal permission)",
        BadgeReason::HeldByGrant => "held by hand-over (a receipted cap transfer)",
        BadgeReason::DeclaredNotGranted => "declared, awaiting hand-over (tap to grant)",
        BadgeReason::NotDeclared => "not declared (un-grantable, no ambient escalation)",
    }
}

/// Is a badge lit (held)? — re-exported convenience for the gpui body's color pick.
pub fn badge_is_lit(state: BadgeState) -> bool {
    state.is_lit()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A maps app declaring INTERNET (normal) + ACCESS_FINE_LOCATION + CAMERA (dangerous),
    /// whose device principal holds the location authority but NOT the camera authority.
    fn maps_chrome() -> SystemUiCapChrome {
        SystemUiCapChrome::install(
            "Maps · com.example.maps",
            "com.example.maps",
            0x51,
            0x01,
            [
                AndroidPermission::Internet,
                AndroidPermission::AccessFineLocation,
                AndroidPermission::Camera,
            ],
            // The principal can back LOCATION, but holds NO camera authority.
            [AndroidPermission::AccessFineLocation],
        )
    }

    /// **THE STATUS BAR renders the app's held caps at a glance.** INTERNET is lit at
    /// install; the dangerous caps are dim until handed over — so a fresh maps app shows
    /// exactly one held cap (NET) and the rest dim.
    #[test]
    fn status_bar_shows_held_caps_at_a_glance() {
        let chrome = maps_chrome();
        let bar = chrome.status_bar();
        // Exactly INTERNET is held at install; nothing dangerous is held yet.
        assert!(bar.held.iter().any(|h| h.contains("NET")), "NET is lit");
        assert!(
            !bar.held.iter().any(|h| h.contains("LOCATION")),
            "LOCATION dim until hand-over"
        );
        assert!(bar.dim_count >= 2, "the dangerous caps are dim");
        assert!(
            bar.line().contains("🛡"),
            "the cap strip carries the shield glyph"
        );
    }

    /// **THE QUICK-SETTINGS SHADE shows the WHOLE roster lit/dim — nothing hidden.** Every
    /// recognised permission appears with its never-hidden reason; a declared dim cap and an
    /// undeclared dim cap are both visible (and distinguishable by reason).
    #[test]
    fn quick_settings_shows_the_whole_roster_with_reasons() {
        let chrome = maps_chrome();
        let lines = chrome.quick_settings();
        // The full standard roster is shown (nothing hidden behind a toggle tree).
        assert_eq!(lines.len(), AndroidPermission::all_standard().len());
        // INTERNET → lit, held at install.
        assert!(lines
            .iter()
            .any(|l| l.contains("● NET") && l.contains("held at install")));
        // LOCATION → dim, declared-awaiting-hand-over (a grantable cap).
        assert!(lines
            .iter()
            .any(|l| l.contains("○ LOCATION") && l.contains("awaiting hand-over")));
        // MIC → dim, NOT declared (un-grantable, no ambient escalation).
        assert!(lines
            .iter()
            .any(|l| l.contains("○ MIC") && l.contains("no ambient escalation")));
    }

    /// **THE HAND-OVER SHEET lists exactly the declared-but-dim dangerous caps.** The maps
    /// app declared LOCATION + CAMERA (both dangerous, both dim) — so both are grantable
    /// rows; INTERNET (lit at install) and the undeclared caps are NOT in the sheet.
    #[test]
    fn grant_sheet_lists_the_declared_dim_dangerous_caps() {
        let chrome = maps_chrome();
        let sheet = chrome.grant_sheet();
        let perms: Vec<_> = sheet.iter().map(|r| r.permission.clone()).collect();
        assert!(perms.contains(&AndroidPermission::AccessFineLocation));
        assert!(perms.contains(&AndroidPermission::Camera));
        assert!(
            !perms.contains(&AndroidPermission::Internet),
            "install-held is not a sheet row"
        );
        assert!(
            !perms.contains(&AndroidPermission::RecordAudio),
            "undeclared is not a sheet row"
        );
        assert!(sheet.iter().all(|r| r.level == ProtectionLevel::Dangerous));
    }

    /// **THE KEYSTONE: tapping a sheet row hands over the cap via a REAL kernel grant — the
    /// badge flips lit because the cell GENUINELY holds the cap.** A hand-over of LOCATION
    /// (which the principal can back) commits a real `Effect::GrantCapability` turn; the
    /// status bar then shows LOCATION lit and the quick-settings reason becomes "held by
    /// hand-over". This is the phone's permission UI being the deos cap surface.
    #[test]
    fn handing_over_a_cap_flips_the_badge_lit_via_a_real_kernel_grant() {
        let mut chrome = maps_chrome();
        // Before: LOCATION is a dim grant-sheet row, not in the status bar.
        assert!(!chrome
            .status_bar()
            .held
            .iter()
            .any(|h| h.contains("LOCATION")));

        let outcome = chrome.hand_over(AndroidPermission::AccessFineLocation);
        assert!(
            outcome.granted(),
            "the held, declared dangerous cap hands over"
        );
        assert!(
            outcome.receipt().is_some(),
            "a committed hand-over carries a kernel TurnReceipt"
        );
        assert!(SystemUiCapChrome::outcome_line(&outcome).contains("HANDED OVER"));

        // After: the status bar now shows LOCATION lit, and the shade reason is "held by hand-over".
        assert!(
            chrome
                .status_bar()
                .held
                .iter()
                .any(|h| h.contains("● LOCATION")),
            "the status bar lights the handed-over cap"
        );
        assert!(
            chrome
                .quick_settings()
                .iter()
                .any(|l| l.contains("● LOCATION") && l.contains("held by hand-over")),
            "the shade reason flips to held-by-hand-over"
        );
        // …and LOCATION is no longer a grant-sheet row (it is held now).
        assert!(
            !chrome
                .grant_sheet()
                .iter()
                .any(|r| r.permission == AndroidPermission::AccessFineLocation),
            "a held cap leaves the hand-over sheet"
        );
    }

    /// **THE POWERBOX TOOTH AT THE REAL KERNEL: handing over a cap the device principal
    /// cannot back is refused by the executor itself — the cap never lands, no ambient
    /// escalation.** The maps principal holds NO camera authority, so a CAMERA hand-over is
    /// `RefusedByKernel` and the badge stays dim.
    #[test]
    fn handing_over_a_cap_the_principal_cannot_back_is_refused_by_the_executor() {
        let mut chrome = maps_chrome();
        let outcome = chrome.hand_over(AndroidPermission::Camera);
        assert!(
            outcome.refused_by_kernel(),
            "the executor refuses a grant the principal cannot back"
        );
        assert!(
            outcome.receipt().is_none(),
            "a refused hand-over runs no committed turn"
        );
        assert!(SystemUiCapChrome::outcome_line(&outcome).contains("REFUSED"));
        // CAMERA stays dim (still a grant-sheet row, still not in the status bar).
        assert!(!chrome
            .status_bar()
            .held
            .iter()
            .any(|h| h.contains("CAMERA")));
        assert!(
            chrome
                .grant_sheet()
                .iter()
                .any(|r| r.permission == AndroidPermission::Camera),
            "a refused cap stays a dim sheet row"
        );
    }

    /// The whole chrome flattens to real text (the bake surface): the status bar, the full
    /// shade, and the hand-over sheet are all present and coherent.
    #[test]
    fn all_text_renders_the_full_chrome() {
        let chrome = maps_chrome();
        let text = chrome.all_text();
        assert!(text.iter().any(|l| l.contains("SystemUI · Maps")));
        assert!(text.iter().any(|l| l.contains("[status bar]")));
        assert!(text.iter().any(|l| l.contains("quick settings")));
        assert!(text.iter().any(|l| l.contains("[hand-over sheet")));
        // The sheet names the two declared dim dangerous caps.
        assert!(text.iter().any(|l| l.contains("○ LOCATION")));
        assert!(text.iter().any(|l| l.contains("○ CAMERA")));
    }
}
