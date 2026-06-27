//! **Cap-gate the PERMISSION.** The confined Android app's runtime-permission model reforged
//! from an ambient "allow X to access Y?" dialog into a **visible cap-badge set** plus a
//! **receipted hand-over turn** — `GRAPHIDEOS.md §1` (the permission-model row) made real, in
//! the same shape as the proven [`crate::intentgate`] / [`crate::contentgate`] /
//! [`crate::organgate`] gates and the cockpit's [`powerbox`](../../starbridge-v2/src/powerbox.rs)
//! grant ceremony.
//!
//! # What Android does (the ambient mechanism deos replaces)
//!
//! Stock Android's runtime-permission model: an app declares `<uses-permission>` in its
//! manifest, then — for a *dangerous* permission — calls `requestPermissions(…)`, which raises
//! a system **dialog** ("Allow Maps to access this device's location?"). The user taps Allow /
//! Deny; the framework records a per-UID grant; the app later calls `checkSelfPermission`. A
//! *normal* permission (e.g. `INTERNET`) is granted **automatically at install**, no dialog. The
//! held set is **hidden in Settings** — a user inspecting an app sees a tree of toggles, not the
//! authority on the app's face. This is ambient: the grant is a UID-scoped flag, the dialog is a
//! modal interruption, and the standing authority is invisible until you go looking.
//!
//! # What graphideOS does (the cap-badge reforge)
//!
//! `GRAPHIDEOS.md §1`: *"**visible capabilities** — no dialogs; a cell's held caps render as
//! cap-badges on its card (lit = held, dim = ungranted, never hidden); a grant is a hand-over
//! sheet, itself a turn."* This module is that, in the same shape as the sibling gates:
//!
//! 1. **Authority is a visible badge set, never hidden in Settings.** [`PermBox::badges`]
//!    renders the WHOLE permission roster as a [`CapBadgeSet`]: each [`CapBadge`] is
//!    [`BadgeState::Lit`] (held) or [`BadgeState::Dim`] (not held), with a [`BadgeReason`]
//!    naming *why* — never hidden, never a toggle tree. The card shows its authority on its face.
//! 2. **An ungranted cap is simply absent — no ambient escalation.** A permission the app's
//!    manifest never declared has NO cap template ([`crate::appfactory`]), so it can never be
//!    held: its badge is [`BadgeReason::NotDeclared`] (dim, forever), and a hand-over of it is
//!    [`PermDecision::RefusedNotDeclared`]. Faithful to AOSP: you cannot grant a runtime
//!    permission the app did not declare.
//! 3. **A normal permission lights at install; a dangerous one waits for the hand-over.**
//!    Faithful AOSP protection levels ([`AndroidPermission::protection_level`]): a `Normal`
//!    permission (`INTERNET`) is held the moment the cell is minted ([`BadgeReason::HeldAtInstall`]);
//!    a `Dangerous`/`Signature` permission is declared-but-dim ([`BadgeReason::DeclaredNotGranted`])
//!    until the ceremony lights it ([`BadgeReason::HeldByGrant`]).
//! 4. **The grant is a receipted hand-over turn — the dialog, reforged.** [`PermBox::grant`]
//!    replaces `requestPermissions`'s modal dialog with a **powerbox-style hand-over**: a
//!    granting principal (the user/system, holding the device authority) confers the permission
//!    to the app-cell, and — exactly the powerbox's `mint_needs_held_factory` tooth — **it can
//!    only hand over an authority it actually holds** ([`PermDecision::RefusedNotHeldByGranter`]).
//!    Every decision leaves a content-addressed [`PermReceipt`], so the app's authority changes
//!    are auditable end to end exactly like the intent / content / service receipts. A
//!    [`PermBox::revoke`] (the Settings-revoke reforge) dims a runtime-granted badge again,
//!    receipted.
//!
//! # Two surfaces: the pure badge model, and the real kernel grant
//!
//! 1. [`PermBox`] is the **pure, device-free badge model**: the faithful projection of an app's
//!    held permissions + the receipted hand-over decision ([`PermReceipt`]), testable on any node.
//!    Its [`grant`](PermBox::grant) records a content-addressed *witness* — it does not, by
//!    itself, land a cap in any ledger. It is the cockpit's badge-preview surface.
//! 2. [`PermWorld`] is the **real kernel hand-over**: it owns a live [`dregg_cell::Ledger`] +
//!    the verified [`dregg_turn::executor::TurnExecutor`] (the SAME executor the cockpit's
//!    powerbox commits through — `World` is a thin wrapper over `dregg_sdk::embed::DreggEngine`,
//!    which wraps exactly this `TurnExecutor`). Its [`grant`](PermWorld::grant) of a *dangerous*
//!    permission mints a genuine [`Effect::GrantCapability`] from the granting principal to the
//!    android-cell and commits it through the executor, so **the permission cap actually lands in
//!    the android-cell's capability c-list with a kernel [`TurnReceipt`]** and the badge flips
//!    [`BadgeState::Lit`] because the cell *genuinely holds the cap*. The executor is the
//!    authority: it re-checks `mint_needs_held_factory` (the principal must hold the organ cap —
//!    `RefusedByKernel` / `CapabilityNotHeld`) and no-amplification, exactly the powerbox's teeth.
//!
//! # The android-cell ↔ cockpit-`World` boundary (named, not papered over)
//!
//! The cockpit's [`World`] is a `starbridge-v2` type that sits ABOVE this crate (it pulls gpui,
//! the SDK, persistence, …). So `android-cell` does NOT — and need not — depend on it: that would
//! invert the layering. The authority `World::commit_turn` ultimately runs is
//! `dregg_turn::TurnExecutor::execute` over a `dregg_cell::Ledger`; [`PermWorld`] depends on that
//! kernel directly. So the grant is a *real* verified turn through the same gate the powerbox
//! uses — the cockpit, when it drives an android-cell, hands its `World`'s ledger semantics to
//! this path; a future cockpit binding can lift [`PermWorld::grant`] onto its own `World` without
//! a new effect (the effect IS [`Effect::GrantCapability`], reused verbatim).
//!
//! # The in-runtime `checkSelfPermission` interposition (now real)
//!
//! `GRAPHIDEOS.md §1`/`§4`: the permission model becomes *visible capabilities*, and a cell's own
//! runtime permission checks read THIS badge set, not AOSP's per-UID framework grant table.
//! [`PermBox::check_self_permission`] / [`PermWorld::check_self_permission`] are that: a confined
//! app's `Context.checkSelfPermission` is routed through [`PermBox::holds`] / [`PermWorld::holds`]
//! (the SAME predicate the cap-badge renders) and answers [`PermissionCheck::Granted`]
//! (`PERMISSION_GRANTED`, 0) iff the cell holds the cap-badge, [`PermissionCheck::Denied`]
//! (`PERMISSION_DENIED`, -1) **in-runtime** otherwise — a permission whose cap the cell does not
//! hold genuinely denies the app's own check; no ambient framework grant overrides the cap model.
//! Each check leaves a [`PermCheckReceipt`], so the app's authority *reads* are auditable exactly
//! like its authority *changes* (the [`PermReceipt`]). Over [`PermWorld`] the verdict reads the
//! cell's GENUINE c-list in the live ledger, so a dangerous permission checks granted iff a real
//! [`Effect::GrantCapability`] turn actually landed its organ cap.
//!
//! # The remaining depth (honest) — the binder leg that routes the GUEST's check
//!
//! What is NOT yet claimed is the **device-kernel binder interposition**: making a *foreign,
//! unmodified APK's* in-process `checkSelfPermission` call (a `libbinder` transaction the
//! framework wires to `system_server`'s `PermissionManagerService` / `AppOpsService`, ultimately
//! `ActivityManagerService.checkPermission` over the per-UID runtime-permission state in
//! `packages.xml`) return THIS cap-derived verdict instead. That is the same per-service binder-shim
//! work `GRAPHIDEOS.md §4`/`§7.5` names (a Soong module forwarding the `IPermissionManager` /
//! `checkPermission` binder transaction into this gate, on a Linux build node / a live device) — it
//! is beyond this macOS host's model layer. What IS real today, on any node, with no device: the
//! check-routing over [`PermBox::holds`]/[`PermWorld::holds`] (a held cap grants, a dim cap denies,
//! receipted), the protection-level-faithful badge derivation, the declared / held-by-granter teeth,
//! the receipted hand-over + revoke, AND a real kernel cap-grant that lands in the cell's c-list
//! with a verified `TurnReceipt`. The in-circuit constructor proof that a given android-cell was
//! minted by its descriptor remains the sibling gates' shared not-yet-claimed depth.
//!
//! [`World`]: ../../starbridge-v2/src/world.rs
//! [`Effect::GrantCapability`]: dregg_turn::action::Effect
//! [`TurnReceipt`]: dregg_turn::turn::TurnReceipt

use std::collections::BTreeSet;

use dregg_firmament::CellId;

use crate::appfactory::{AndroidManifest, AndroidPermission, ProtectionLevel};

/// Whether a permission's cap-badge is **lit** (the authority is held) or **dim** (not held) —
/// the visible-capabilities core: `GRAPHIDEOS.md §1`'s "lit = held, dim = ungranted, never
/// hidden". There is no third "hidden" state: every recognised permission is always *shown*,
/// the only question is lit vs dim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BadgeState {
    /// The app holds this authority — the badge is lit.
    Lit,
    /// The app does not hold this authority — the badge is dim (never hidden).
    Dim,
}

impl BadgeState {
    /// The glyph the cockpit renders (a lit ● vs a dim ○) — the one-glance authority read.
    pub fn glyph(&self) -> char {
        match self {
            BadgeState::Lit => '●',
            BadgeState::Dim => '○',
        }
    }

    pub fn is_lit(&self) -> bool {
        matches!(self, BadgeState::Lit)
    }
}

/// **Why a badge is lit or dim** — the faithful audit reason, never hidden. This is the
/// load-bearing distinction the AOSP Settings tree obscures: a dim badge can be *declared but
/// not yet granted* (a pending hand-over) or *never declared* (un-grantable, no ambient
/// escalation), and a lit badge can be *held at install* (a normal permission) or *handed over*
/// (a dangerous permission's receipted grant).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BadgeReason {
    /// Lit: a `Normal` permission auto-granted at install (declaring it sufficed; no dialog).
    HeldAtInstall,
    /// Lit: a `Dangerous`/`Signature` permission lit by a receipted hand-over ([`PermBox::grant`]).
    HeldByGrant,
    /// Dim: declared in the manifest but NOT yet handed over — a pending grant (the badge the
    /// user can light via the ceremony).
    DeclaredNotGranted,
    /// Dim: NOT declared in the manifest — there is no cap template for it, so it can never be
    /// held. The no-ambient-escalation property, made visible (forever dim).
    NotDeclared,
}

impl BadgeReason {
    /// The badge state this reason implies (lit for the two held reasons, dim otherwise).
    pub fn state(&self) -> BadgeState {
        match self {
            BadgeReason::HeldAtInstall | BadgeReason::HeldByGrant => BadgeState::Lit,
            BadgeReason::DeclaredNotGranted | BadgeReason::NotDeclared => BadgeState::Dim,
        }
    }

    fn label(&self) -> &'static str {
        match self {
            BadgeReason::HeldAtInstall => "held at install (normal permission)",
            BadgeReason::HeldByGrant => "held by hand-over",
            BadgeReason::DeclaredNotGranted => "declared, awaiting hand-over",
            BadgeReason::NotDeclared => "not declared (un-grantable, no ambient escalation)",
        }
    }
}

/// **One cap-badge — a permission shown on the android-cell's card, lit or dim.** The visible
/// unit `GRAPHIDEOS.md §1` describes; the cockpit renders a row of these on the app's card. It
/// carries the permission, its faithful AOSP [`ProtectionLevel`], the [`BadgeState`], and the
/// [`BadgeReason`] (the never-hidden "why").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapBadge {
    /// The permission this badge represents.
    pub permission: AndroidPermission,
    /// The faithful AOSP protection level (normal → install, dangerous/signature → hand-over).
    pub level: ProtectionLevel,
    /// Lit (held) or dim (not held).
    pub state: BadgeState,
    /// Why — the never-hidden audit reason.
    pub reason: BadgeReason,
}

impl CapBadge {
    /// A one-line status for the cockpit/audit: the glyph, the AOSP permission name, and why.
    pub fn status_line(&self) -> String {
        format!(
            "{} {} — {}",
            self.state.glyph(),
            self.permission.android_name(),
            self.reason.label()
        )
    }
}

/// **The cap-badge set rendered on an android-cell's card** — the WHOLE permission roster, each
/// lit or dim, never a hidden toggle tree. `GRAPHIDEOS.md §1`'s visible capabilities, made a
/// value. The roster is the standard permissions ([`AndroidPermission::all_standard`]) unioned
/// with any custom permissions the app declared, so a declared `Other(_)` permission is shown
/// too (and a never-declared standard permission is shown dim — the authority the app does NOT
/// hold is as visible as the authority it does).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapBadgeSet {
    /// The android-cell whose authority this badge set renders.
    pub cell: CellId,
    /// The badges, one per recognised permission, sorted by permission (a stable render order).
    pub badges: Vec<CapBadge>,
}

impl CapBadgeSet {
    /// The lit badges — the authorities the app actually holds.
    pub fn held(&self) -> impl Iterator<Item = &CapBadge> {
        self.badges.iter().filter(|b| b.state.is_lit())
    }

    /// The dim badges — the authorities the app does NOT hold (declared-pending or undeclared).
    pub fn unheld(&self) -> impl Iterator<Item = &CapBadge> {
        self.badges.iter().filter(|b| !b.state.is_lit())
    }

    /// Every badge line, flattened — the cockpit row text + the test assertion surface.
    pub fn all_text(&self) -> Vec<String> {
        self.badges.iter().map(CapBadge::status_line).collect()
    }
}

/// The outcomes a permission hand-over (or revoke) can reach — the permission-side analogue of
/// [`crate::organgate::ServiceDecision`], faithful to AOSP's runtime-permission model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PermDecision {
    /// The hand-over committed: a `Dangerous`/`Signature` permission the granter held was
    /// conferred to the app-cell, lighting its badge. The receipted replacement for the dialog.
    Granted {
        permission: AndroidPermission,
        app_cell: CellId,
    },
    /// A runtime-granted permission was revoked (the Settings-revoke reforge): the badge dims.
    Revoked {
        permission: AndroidPermission,
        app_cell: CellId,
    },
    /// A no-op hand-over: a `Normal` permission is ALREADY held at install (auto-granted) — no
    /// ceremony is needed, the badge is already lit.
    AlreadyHeldAtInstall { permission: AndroidPermission },
    /// REFUSED: the app's manifest never declared this permission — there is no cap template, so
    /// it can never be held (no ambient escalation; AOSP refuses to grant an undeclared
    /// permission too).
    RefusedNotDeclared { permission: AndroidPermission },
    /// REFUSED: the granting principal does not hold this authority to confer it — the
    /// powerbox's `mint_needs_held_factory`: you cannot hand over what you do not hold.
    RefusedNotHeldByGranter { permission: AndroidPermission },
    /// A no-op revoke: the permission was not runtime-granted (it was install-held or already
    /// dim), so there is nothing to revoke (a `Normal` permission cannot be runtime-revoked).
    NothingToRevoke { permission: AndroidPermission },
}

impl PermDecision {
    pub fn granted(&self) -> bool {
        matches!(self, PermDecision::Granted { .. })
    }
    pub fn revoked(&self) -> bool {
        matches!(self, PermDecision::Revoked { .. })
    }
    pub fn refused_not_declared(&self) -> bool {
        matches!(self, PermDecision::RefusedNotDeclared { .. })
    }
    pub fn refused_not_held_by_granter(&self) -> bool {
        matches!(self, PermDecision::RefusedNotHeldByGranter { .. })
    }
    pub fn already_held_at_install(&self) -> bool {
        matches!(self, PermDecision::AlreadyHeldAtInstall { .. })
    }

    fn tag(&self) -> &'static str {
        match self {
            PermDecision::Granted { .. } => "granted",
            PermDecision::Revoked { .. } => "revoked",
            PermDecision::AlreadyHeldAtInstall { .. } => "already-held-at-install",
            PermDecision::RefusedNotDeclared { .. } => "refused-not-declared",
            PermDecision::RefusedNotHeldByGranter { .. } => "refused-not-held-by-granter",
            PermDecision::NothingToRevoke { .. } => "nothing-to-revoke",
        }
    }

    fn permission(&self) -> &AndroidPermission {
        match self {
            PermDecision::Granted { permission, .. }
            | PermDecision::Revoked { permission, .. }
            | PermDecision::AlreadyHeldAtInstall { permission }
            | PermDecision::RefusedNotDeclared { permission }
            | PermDecision::RefusedNotHeldByGranter { permission }
            | PermDecision::NothingToRevoke { permission } => permission,
        }
    }
}

/// **The receipt left by a permission hand-over (or revoke).** Every decision produces one, so
/// the android-cell's authority changes are auditable end to end exactly like the intent /
/// content / service receipts — the receipted cap transfer that replaces AOSP's silent per-UID
/// grant flag. Content-addressed:
/// `decision_digest = blake3(principal ‖ app_cell ‖ permission ‖ outcome)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PermReceipt {
    /// The granting principal (the user/system that held the device authority).
    pub principal: CellId,
    /// The android-cell the hand-over targeted (the grantee).
    pub app_cell: CellId,
    /// The decision reached.
    pub decision: PermDecision,
    /// `blake3(…)[..32]` — the content-addressed witness a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl PermReceipt {
    fn digest(principal: CellId, app_cell: CellId, decision: &PermDecision) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"graphideos-perm-handover-v1");
        h.update(principal.as_bytes());
        h.update(app_cell.as_bytes());
        h.update(decision.permission().android_name().as_bytes());
        h.update(b"\x00");
        h.update(decision.tag().as_bytes());
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which outcome, named exactly.
    pub fn status_line(&self) -> String {
        let perm = self.decision.permission().android_name();
        match &self.decision {
            PermDecision::Granted { .. } => format!(
                "android-perm: ✔ {perm} HANDED OVER to the app as a receipted cap transfer — the badge lights (no runtime dialog)"
            ),
            PermDecision::Revoked { .. } => format!(
                "android-perm: ↩ {perm} REVOKED — the runtime grant is withdrawn, the badge dims (the Settings-revoke reforge)"
            ),
            PermDecision::AlreadyHeldAtInstall { .. } => format!(
                "android-perm: ● {perm} already held at install (a normal permission) — no hand-over needed"
            ),
            PermDecision::RefusedNotDeclared { .. } => format!(
                "android-perm: ✖ {perm} REFUSED — the app never declared it; there is no cap to hold (no ambient escalation)"
            ),
            PermDecision::RefusedNotHeldByGranter { .. } => format!(
                "android-perm: ✖ {perm} REFUSED — the granting principal does not hold this authority (you cannot hand over what you do not hold)"
            ),
            PermDecision::NothingToRevoke { .. } => {
                format!("android-perm: ◦ {perm} not runtime-granted — nothing to revoke")
            }
        }
    }
}

// ── THE IN-RUNTIME `checkSelfPermission` INTERPOSITION ───────────────────────

/// **The result of a confined app's OWN permission check** — what
/// `Context.checkSelfPermission` / `Context.checkPermission` / `PermissionChecker`
/// return. In stock Android these are the two `PackageManager` int constants the app
/// branches on; here the verdict is decided by the deos **cap-badge set**, not AOSP's
/// per-UID framework grant table: the app sees the cap model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PermissionCheck {
    /// `PackageManager.PERMISSION_GRANTED` (`== 0`) — the cell GENUINELY holds the
    /// authority (a lit cap-badge): the check returns granted in-runtime.
    Granted,
    /// `PackageManager.PERMISSION_DENIED` (`== -1`) — the cell does NOT hold the
    /// authority (a dim cap-badge): the check returns denied in-runtime, no ambient
    /// framework grant can override it.
    Denied,
}

impl PermissionCheck {
    /// **The exact AOSP int the framework returns** — `PERMISSION_GRANTED == 0`,
    /// `PERMISSION_DENIED == -1`. The confined app's `checkSelfPermission` call reads
    /// this value verbatim, so it cannot tell a deos cap-derived verdict from a
    /// framework one (the interposition is transparent at the call site).
    pub fn aosp_code(&self) -> i32 {
        match self {
            PermissionCheck::Granted => 0,
            PermissionCheck::Denied => -1,
        }
    }

    /// The `PackageManager` constant name (the symbol the app's `if (… == GRANTED)`
    /// compares against) — the audit label.
    pub fn constant_name(&self) -> &'static str {
        match self {
            PermissionCheck::Granted => "PERMISSION_GRANTED",
            PermissionCheck::Denied => "PERMISSION_DENIED",
        }
    }

    pub fn granted(&self) -> bool {
        matches!(self, PermissionCheck::Granted)
    }
    pub fn denied(&self) -> bool {
        matches!(self, PermissionCheck::Denied)
    }

    fn tag(&self) -> &'static str {
        match self {
            PermissionCheck::Granted => "granted",
            PermissionCheck::Denied => "denied",
        }
    }
}

/// **The receipt left by an in-runtime `checkSelfPermission` interposition.** Every
/// permission check a confined app issues leaves one, so the app's authority *reads*
/// (not just its authority *changes*, the [`PermReceipt`]) are auditable end to end —
/// the deos answer to AOSP's silent, unlogged `checkSelfPermission` consultation of the
/// per-UID grant table. The verdict + the never-hidden [`BadgeReason`] (the same "why"
/// the cap-badge renders) are bound. Content-addressed:
/// `decision_digest = blake3(app_cell ‖ permission ‖ verdict)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PermCheckReceipt {
    /// The android-cell that asked (the confined app checking its OWN permission).
    pub app_cell: CellId,
    /// The permission the app checked.
    pub permission: AndroidPermission,
    /// The verdict — granted iff the cell holds the cap-badge, denied otherwise.
    pub result: PermissionCheck,
    /// The never-hidden audit reason — the SAME [`BadgeReason`] the cell's cap-badge
    /// renders, so the check verdict and the visible badge can never disagree.
    pub reason: BadgeReason,
    /// `blake3(…)[..32]` — the content-addressed witness a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl PermCheckReceipt {
    fn digest(
        app_cell: CellId,
        permission: &AndroidPermission,
        result: PermissionCheck,
    ) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"graphideos-perm-check-v1");
        h.update(app_cell.as_bytes());
        h.update(permission.android_name().as_bytes());
        h.update(b"\x00");
        h.update(result.tag().as_bytes());
        *h.finalize().as_bytes()
    }

    /// The AOSP int the confined app's `checkSelfPermission` call site reads (`0` / `-1`).
    pub fn aosp_code(&self) -> i32 {
        self.result.aosp_code()
    }

    /// A one-line audit truth for the cockpit status line — the verdict, named exactly.
    pub fn status_line(&self) -> String {
        let perm = self.permission.android_name();
        match self.result {
            PermissionCheck::Granted => format!(
                "android-perm-check: ✔ {perm} checkSelfPermission → PERMISSION_GRANTED (0) — the cell holds the cap-badge ({})",
                self.reason.label()
            ),
            PermissionCheck::Denied => format!(
                "android-perm-check: ✖ {perm} checkSelfPermission → PERMISSION_DENIED (-1) in-runtime — the cell holds no cap-badge ({}); no ambient framework grant overrides the cap model",
                self.reason.label()
            ),
        }
    }
}

/// **THE PERMISSION HAND-OVER SURFACE for one android-cell** — the trusted, powerbox-style
/// surface that renders the app's cap-badges AND mediates a receipted hand-over (the deos form
/// of the runtime-permission dialog). Holds the app's manifest (the declared set — what is even
/// grantable), the granting principal + the authorities it holds (the powerbox's "you can only
/// grant what you hold"), and the set of permissions runtime-granted so far. Holds NO ambient
/// authority: a hand-over the principal cannot back is refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PermBox {
    /// The android-cell this surface speaks for (the grantee).
    app_cell: CellId,
    /// The app's manifest — the declared permissions are the ONLY grantable ones.
    manifest: AndroidManifest,
    /// The granting principal (the user/system identity the hand-over grants FROM).
    principal: CellId,
    /// The authorities the principal actually holds and can confer (the powerbox ceiling: a
    /// hand-over of a permission not in here is `RefusedNotHeldByGranter`).
    principal_holds: BTreeSet<AndroidPermission>,
    /// The `Dangerous`/`Signature` permissions runtime-granted so far (the handed-over set). A
    /// `Normal` permission is never in here — it is held at install, not via the ceremony.
    granted: BTreeSet<AndroidPermission>,
}

impl PermBox {
    /// Build a permission hand-over surface for `app_cell` (born from `manifest`), granting from
    /// `principal` which holds `principal_holds`. No permission is runtime-granted yet — the
    /// dangerous badges start dim, the normal badges start lit (held at install).
    pub fn new(
        app_cell: CellId,
        manifest: AndroidManifest,
        principal: CellId,
        principal_holds: impl IntoIterator<Item = AndroidPermission>,
    ) -> Self {
        PermBox {
            app_cell,
            manifest,
            principal,
            principal_holds: principal_holds.into_iter().collect(),
            granted: BTreeSet::new(),
        }
    }

    /// The android-cell this surface speaks for.
    pub fn app_cell(&self) -> CellId {
        self.app_cell
    }

    /// Is this permission's badge currently LIT (the app holds the authority)? A `Normal`
    /// declared permission is always lit (held at install); a `Dangerous`/`Signature` declared
    /// permission is lit iff it was handed over; an undeclared permission is never lit.
    pub fn holds(&self, permission: &AndroidPermission) -> bool {
        self.manifest.declares(permission)
            && (permission.protection_level().held_at_install()
                || self.granted.contains(permission))
    }

    /// The [`BadgeReason`] for one permission — the faithful lit/dim "why".
    fn reason_for(&self, permission: &AndroidPermission) -> BadgeReason {
        if !self.manifest.declares(permission) {
            BadgeReason::NotDeclared
        } else if permission.protection_level().held_at_install() {
            BadgeReason::HeldAtInstall
        } else if self.granted.contains(permission) {
            BadgeReason::HeldByGrant
        } else {
            BadgeReason::DeclaredNotGranted
        }
    }

    fn badge_for(&self, permission: &AndroidPermission) -> CapBadge {
        let reason = self.reason_for(permission);
        CapBadge {
            permission: permission.clone(),
            level: permission.protection_level(),
            state: reason.state(),
            reason,
        }
    }

    /// **RENDER THE CAP-BADGE SET** — the WHOLE roster (standard permissions ∪ the app's
    /// declared custom permissions), each lit or dim. The visible-capabilities surface
    /// `GRAPHIDEOS.md §1` describes; the cockpit renders these as a row on the app's card.
    pub fn badges(&self) -> CapBadgeSet {
        let mut roster: BTreeSet<AndroidPermission> =
            AndroidPermission::all_standard().into_iter().collect();
        roster.extend(self.manifest.uses_permissions.iter().cloned());
        let badges = roster.iter().map(|p| self.badge_for(p)).collect();
        CapBadgeSet {
            cell: self.app_cell,
            badges,
        }
    }

    /// **THE IN-RUNTIME `checkSelfPermission` INTERPOSITION — route the confined app's OWN
    /// permission check through the cap-badge set.** `GRAPHIDEOS.md §1`/`§4`: the permission
    /// model becomes *visible capabilities*, and a cell's runtime permission checks read THIS
    /// badge set, not AOSP's per-UID framework grant table.
    ///
    /// When the confined app calls `Context.checkSelfPermission(perm)` (or `checkPermission` /
    /// `PermissionChecker.checkSelfPermission`), the runtime interposes the call and answers from
    /// [`PermBox::holds`] — the SAME predicate the cap-badge renders:
    ///
    /// - the cell holds the cap-badge (a `Normal` install-held permission, or a `Dangerous`/
    ///   `Signature` one a hand-over lit) ⟹ [`PermissionCheck::Granted`] (`PERMISSION_GRANTED`, 0);
    /// - the cell holds NO cap-badge (declared-but-dim, or never declared) ⟹
    ///   [`PermissionCheck::Denied`] (`PERMISSION_DENIED`, -1) **in-runtime** — a permission whose
    ///   cap the cell does not hold genuinely denies the app's own check; no ambient framework grant
    ///   can override the cap model.
    ///
    /// The verdict carries the never-hidden [`BadgeReason`] (the visible "why") and leaves a
    /// [`PermCheckReceipt`], so the app's authority *reads* are auditable exactly like its
    /// authority *changes*.
    pub fn check_self_permission(&self, permission: &AndroidPermission) -> PermCheckReceipt {
        let result = if self.holds(permission) {
            PermissionCheck::Granted
        } else {
            PermissionCheck::Denied
        };
        let reason = self.reason_for(permission);
        let decision_digest = PermCheckReceipt::digest(self.app_cell, permission, result);
        PermCheckReceipt {
            app_cell: self.app_cell,
            permission: permission.clone(),
            result,
            reason,
            decision_digest,
        }
    }

    /// **THE HAND-OVER CEREMONY — grant `permission` to the app (the dialog, reforged).** The
    /// receipted cap transfer that replaces `requestPermissions`'s modal dialog. Faithful AOSP
    /// + powerbox teeth, fail-closed:
    ///
    /// 1. **Declared, or absent** — the manifest must declare `permission`; otherwise there is
    ///    no cap template ([`crate::appfactory`]) and it can never be held:
    ///    [`PermDecision::RefusedNotDeclared`] (no ambient escalation).
    /// 2. **Normal is already held** — a `Normal` permission was auto-granted at install; the
    ///    hand-over is a no-op [`PermDecision::AlreadyHeldAtInstall`] (the badge is already lit).
    /// 3. **The granter must hold it** — for a `Dangerous`/`Signature` permission, the principal
    ///    must hold the authority to confer it; otherwise [`PermDecision::RefusedNotHeldByGranter`]
    ///    (the powerbox's `mint_needs_held_factory`: you cannot hand over what you do not hold).
    ///
    /// On success the permission joins the runtime-granted set (its badge lights), and the
    /// decision leaves a [`PermReceipt`].
    pub fn grant(&mut self, permission: AndroidPermission) -> PermReceipt {
        let decision = if !self.manifest.declares(&permission) {
            PermDecision::RefusedNotDeclared { permission }
        } else if permission.protection_level().held_at_install() {
            PermDecision::AlreadyHeldAtInstall { permission }
        } else if !self.principal_holds.contains(&permission) {
            PermDecision::RefusedNotHeldByGranter { permission }
        } else {
            self.granted.insert(permission.clone());
            PermDecision::Granted {
                permission,
                app_cell: self.app_cell,
            }
        };
        self.receipt(decision)
    }

    /// **REVOKE a runtime-granted permission (the Settings-revoke reforge).** Withdraw a
    /// previously handed-over `Dangerous`/`Signature` permission — the badge dims again,
    /// receipted. A permission that was not runtime-granted (a `Normal` install-held one, or one
    /// already dim) is [`PermDecision::NothingToRevoke`]: AOSP cannot runtime-revoke a normal
    /// permission either.
    pub fn revoke(&mut self, permission: AndroidPermission) -> PermReceipt {
        let decision = if self.granted.remove(&permission) {
            PermDecision::Revoked {
                permission,
                app_cell: self.app_cell,
            }
        } else {
            PermDecision::NothingToRevoke { permission }
        };
        self.receipt(decision)
    }

    fn receipt(&self, decision: PermDecision) -> PermReceipt {
        let decision_digest = PermReceipt::digest(self.principal, self.app_cell, &decision);
        PermReceipt {
            principal: self.principal,
            app_cell: self.app_cell,
            decision,
            decision_digest,
        }
    }
}

// ── THE REAL KERNEL HAND-OVER ────────────────────────────────────────────────

use dregg_cell::AuthRequired;
use dregg_cell::{CapabilityRef, Cell, Ledger, Permissions};
use dregg_turn::action::{Action, Authorization, DelegationMode, Effect};
use dregg_turn::executor::{ComputronCosts, TurnExecutor};
use dregg_turn::forest::CallForest;
use dregg_turn::turn::{Turn, TurnReceipt, TurnResult};

/// **The outcome of a real kernel permission hand-over** ([`PermWorld::grant`]) — the
/// permission-side analogue of the cockpit powerbox's `PowerboxOutcome`, faithful to AOSP and
/// carrying the executor's OWN [`TurnReceipt`] when a grant truly committed.
#[derive(Clone, Debug)]
pub enum KernelGrantOutcome {
    /// A genuine [`Effect::GrantCapability`] turn COMMITTED: the permission cap landed in the
    /// android-cell's real c-list at `slot`, its badge is genuinely [`BadgeState::Lit`], and the
    /// executor's own [`TurnReceipt`] witnesses the transition (the dialog, reforged into a
    /// verified turn — not just a content-addressed witness).
    Granted {
        permission: AndroidPermission,
        app_cell: CellId,
        /// The c-list slot the executor minted the cap into (assigned by the grantee's c-list).
        slot: u32,
        /// Boxed: `TurnReceipt` dwarfs the other variants (large_enum_variant).
        receipt: Box<TurnReceipt>,
    },
    /// A no-op: a `Normal` permission is already held at install (auto-granted) — no turn runs.
    AlreadyHeldAtInstall { permission: AndroidPermission },
    /// REFUSED before any turn: the app's manifest never declared this permission, so there is no
    /// cap template and it can never be held (no ambient escalation).
    RefusedNotDeclared { permission: AndroidPermission },
    /// REFUSED by the REAL executor: the granting principal holds no cap reaching the permission's
    /// organ (the kernel's `mint_needs_held_factory` / `CapabilityNotHeld`), or another
    /// no-amplification gate fired. Carries the kernel's own reason — the authority is the
    /// executor, never us.
    RefusedByKernel {
        permission: AndroidPermission,
        reason: String,
    },
}

impl KernelGrantOutcome {
    /// Did a real `GrantCapability` turn commit (the cap genuinely landed)?
    pub fn granted(&self) -> bool {
        matches!(self, KernelGrantOutcome::Granted { .. })
    }
    /// The executor's verified receipt, if a grant committed.
    pub fn receipt(&self) -> Option<&TurnReceipt> {
        match self {
            KernelGrantOutcome::Granted { receipt, .. } => Some(receipt.as_ref()),
            _ => None,
        }
    }
    /// Was the hand-over refused by the kernel (not held / amplifying)?
    pub fn refused_by_kernel(&self) -> bool {
        matches!(self, KernelGrantOutcome::RefusedByKernel { .. })
    }
    /// Was the hand-over refused because the permission was never declared?
    pub fn refused_not_declared(&self) -> bool {
        matches!(self, KernelGrantOutcome::RefusedNotDeclared { .. })
    }
}

/// **THE REAL KERNEL PERMISSION HAND-OVER — the powerbox path, for an android-cell.**
///
/// Where [`PermBox`] is the pure, device-free badge model (its [`grant`](PermBox::grant) leaves a
/// content-addressed witness), `PermWorld` owns a live [`Ledger`] + the verified [`TurnExecutor`]
/// — the SAME executor the cockpit's powerbox commits through — and its [`grant`](Self::grant) of
/// a dangerous permission mints a genuine [`Effect::GrantCapability`] so the permission cap lands
/// in the android-cell's real c-list with a kernel [`TurnReceipt`]. The cap-badge then flips
/// [`BadgeState::Lit`] because the cell GENUINELY holds the cap (the badge reads the live c-list,
/// not an internal set). Holds NO ambient authority: the executor refuses a grant the principal
/// cannot back (`mint_needs_held_factory`), exactly the powerbox tooth, as the real backstop.
pub struct PermWorld {
    ledger: Ledger,
    executor: TurnExecutor,
    /// The granting principal (the device/system identity that holds device authority).
    principal: CellId,
    /// The android-cell the hand-over targets (the grantee, confined: born with an empty c-list).
    app_cell: CellId,
    /// The app's manifest — the declared permissions are the ONLY grantable ones.
    manifest: AndroidManifest,
}

impl PermWorld {
    /// **Install the android-cell into a fresh real ledger + verified executor.** The android-cell
    /// (`app_seed`) is born CONFINED — an empty c-list, no ambient authority (the ocap floor). The
    /// granting principal (`principal_seed`) is born holding device authority over each *dangerous*
    /// permission in `principal_holds` (a real c-list cap reaching that permission's organ — the
    /// powerbox's "you can only grant what you hold"). A `Normal` permission needs no organ cap (it
    /// is held at install), so it is skipped. `app_seed` and `principal_seed` must differ.
    pub fn install(
        app_seed: u8,
        principal_seed: u8,
        manifest: AndroidManifest,
        principal_holds: impl IntoIterator<Item = AndroidPermission>,
    ) -> Self {
        let mut ledger = Ledger::new();

        // The android-cell: open, EMPTY c-list — a confined app-as-cell.
        let app = open_cell(app_seed, 0);
        let app_cell = app.id();
        ledger
            .insert_cell(app)
            .expect("fresh android-cell ledger slot");

        // The granting principal: holds a real cap reaching each organ for the dangerous
        // permissions it can confer (the device authority — what makes a hand-over backable).
        let mut principal_cell = open_cell(principal_seed, 0);
        for perm in principal_holds {
            if perm.protection_level().held_at_install() {
                continue; // a Normal permission is held at install — no organ cap to confer.
            }
            let target = perm.grant_target(app_cell);
            principal_cell
                .capabilities
                .grant(target, perm.cap_template().max_permissions)
                .expect("fresh principal c-list slot for the device organ");
        }
        let principal = principal_cell.id();
        ledger
            .insert_cell(principal_cell)
            .expect("fresh principal ledger slot");

        // Metering-free: the permission hand-over is a single-custody system act (the device's
        // package-manager principal), not a fee-bearing economic turn, so the grant turn carries
        // no fee. The cells' `Permissions` + the executor's authority/no-amplification gates still
        // decide every grant — `ComputronCosts::zero()` removes only the fee budget, never a gate.
        let executor = TurnExecutor::new(ComputronCosts::zero());
        PermWorld {
            ledger,
            executor,
            principal,
            app_cell,
            manifest,
        }
    }

    /// The android-cell this surface speaks for (the grantee).
    pub fn app_cell(&self) -> CellId {
        self.app_cell
    }

    /// The granting principal.
    pub fn principal(&self) -> CellId {
        self.principal
    }

    /// The live ledger — the real cap c-lists a verifier inspects.
    pub fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    /// **Does the android-cell GENUINELY hold this permission now** — reading its REAL c-list in
    /// the live ledger (not an internal flag set)? A `Normal` declared permission is held at
    /// install; a dangerous one is held iff a real grant turn landed its organ cap; an undeclared
    /// permission is never held.
    pub fn holds(&self, permission: &AndroidPermission) -> bool {
        if !self.manifest.declares(permission) {
            return false;
        }
        if permission.protection_level().held_at_install() {
            return true;
        }
        let target = permission.grant_target(self.app_cell);
        self.ledger
            .get(&self.app_cell)
            .map(|c| c.capabilities.has_access(&target))
            .unwrap_or(false)
    }

    fn reason_for(&self, permission: &AndroidPermission) -> BadgeReason {
        if !self.manifest.declares(permission) {
            BadgeReason::NotDeclared
        } else if permission.protection_level().held_at_install() {
            BadgeReason::HeldAtInstall
        } else if self.holds(permission) {
            BadgeReason::HeldByGrant
        } else {
            BadgeReason::DeclaredNotGranted
        }
    }

    fn badge_for(&self, permission: &AndroidPermission) -> CapBadge {
        let reason = self.reason_for(permission);
        CapBadge {
            permission: permission.clone(),
            level: permission.protection_level(),
            state: reason.state(),
            reason,
        }
    }

    /// **RENDER THE CAP-BADGE SET from the live ledger** — the WHOLE roster (standard permissions
    /// ∪ the app's declared custom permissions), each lit or dim by what the cell GENUINELY holds.
    pub fn badges(&self) -> CapBadgeSet {
        let mut roster: BTreeSet<AndroidPermission> =
            AndroidPermission::all_standard().into_iter().collect();
        roster.extend(self.manifest.uses_permissions.iter().cloned());
        let badges = roster.iter().map(|p| self.badge_for(p)).collect();
        CapBadgeSet {
            cell: self.app_cell,
            badges,
        }
    }

    /// **THE IN-RUNTIME `checkSelfPermission` INTERPOSITION, over the REAL c-list.** The confined
    /// app's own permission check, answered from [`PermWorld::holds`] — which reads the
    /// android-cell's GENUINE capability c-list in the live ledger, not an internal flag set. So a
    /// dangerous permission's `checkSelfPermission` returns [`PermissionCheck::Granted`] iff a real
    /// [`Effect::GrantCapability`] turn actually landed its organ cap (the cap-badge is lit because
    /// the cell holds the cap); a permission whose cap never landed genuinely denies in-runtime
    /// ([`PermissionCheck::Denied`], `PERMISSION_DENIED`, -1). The verdict carries the never-hidden
    /// [`BadgeReason`] and leaves a [`PermCheckReceipt`].
    pub fn check_self_permission(&self, permission: &AndroidPermission) -> PermCheckReceipt {
        let result = if self.holds(permission) {
            PermissionCheck::Granted
        } else {
            PermissionCheck::Denied
        };
        let reason = self.reason_for(permission);
        let decision_digest = PermCheckReceipt::digest(self.app_cell, permission, result);
        PermCheckReceipt {
            app_cell: self.app_cell,
            permission: permission.clone(),
            result,
            reason,
            decision_digest,
        }
    }

    /// **THE REAL HAND-OVER CEREMONY — grant `permission` to the android-cell via a verified turn.**
    /// Faithful AOSP, fail-closed, with the REAL executor as the authority:
    ///
    /// 1. **Declared, or absent** — the manifest must declare `permission`; otherwise there is no
    ///    cap template, so no turn runs ([`KernelGrantOutcome::RefusedNotDeclared`]).
    /// 2. **Normal is already held** — a `Normal` permission was auto-granted at install; the
    ///    hand-over is a no-op ([`KernelGrantOutcome::AlreadyHeldAtInstall`]).
    /// 3. **THE REAL MINT** — for a `Dangerous`/`Signature` permission, build a genuine
    ///    [`Effect::GrantCapability`] from the principal to the android-cell, reaching the
    ///    permission's organ at the cap template's ceiling, and commit it through the
    ///    [`TurnExecutor`]. The executor re-checks `mint_needs_held_factory` (the principal must
    ///    hold the organ cap) + no-amplification; a refusal surfaces as
    ///    [`KernelGrantOutcome::RefusedByKernel`] with the kernel's own reason. On commit the cap
    ///    lands in the android-cell's c-list, its badge flips [`BadgeState::Lit`], and the
    ///    executor's [`TurnReceipt`] is returned.
    pub fn grant(&mut self, permission: AndroidPermission) -> KernelGrantOutcome {
        if !self.manifest.declares(&permission) {
            return KernelGrantOutcome::RefusedNotDeclared { permission };
        }
        if permission.protection_level().held_at_install() {
            return KernelGrantOutcome::AlreadyHeldAtInstall { permission };
        }

        let target = permission.grant_target(self.app_cell);
        let rights = permission.cap_template().max_permissions;

        // THE REAL TURN: a genuine Effect::GrantCapability, committed through the verified
        // executor. The cap's `slot` field is advisory — the grantee's c-list (`grant_ref`)
        // assigns the real slot. We thread the principal's receipt-chain head + nonce exactly as
        // the cockpit's `World::commit_turn` does, so this is a well-formed verified turn.
        let nonce = self
            .ledger
            .get(&self.principal)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        let effect = Effect::GrantCapability {
            from: self.principal,
            to: self.app_cell,
            cap: CapabilityRef {
                target,
                slot: 0,
                permissions: rights,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: None,
            },
        };
        let mut turn = bare_turn(self.principal, nonce, vec![effect]);
        turn.previous_receipt_hash = self.executor.get_last_receipt_hash(&self.principal);

        match self.executor.execute(&turn, &mut self.ledger) {
            TurnResult::Committed { receipt, .. } => {
                self.executor
                    .set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
                let slot = self
                    .ledger
                    .get(&self.app_cell)
                    .and_then(|c| {
                        c.capabilities
                            .iter()
                            .find(|cr| cr.target == target)
                            .map(|cr| cr.slot)
                    })
                    .unwrap_or(0);
                KernelGrantOutcome::Granted {
                    permission,
                    app_cell: self.app_cell,
                    slot,
                    receipt: Box::new(receipt),
                }
            }
            TurnResult::Rejected { reason, .. } => KernelGrantOutcome::RefusedByKernel {
                permission,
                reason: format!("{reason:?}"),
            },
            other => KernelGrantOutcome::RefusedByKernel {
                permission,
                reason: format!("the executor did not commit the grant: {other:?}"),
            },
        }
    }
}

/// A deterministic open cell from a one-byte seed (the genesis fixture shape `make_open_cell`
/// uses): `pk[0]=seed`, `pk[31]=seed*37`, fully-open permissions, an empty c-list.
fn open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

/// A bare `Unchecked` single-action turn carrying `effects` (the executor-test template shape the
/// cockpit's `World::turn` also builds — honest for a single-custody surface: the cells'
/// `Permissions` + the executor's whole-turn guarantees still gate every effect).
fn bare_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;

    /// A maps app declaring INTERNET (normal) + ACCESS_FINE_LOCATION (dangerous), and a granting
    /// principal that holds the location authority. Returns `(permbox, app, principal)`.
    fn maps_permbox() -> (PermBox, CellId, CellId) {
        let app = cell_seed(0x51);
        let principal = cell_seed(0x01);
        let manifest = AndroidManifest::new(
            "com.example.maps",
            [
                AndroidPermission::Internet,
                AndroidPermission::AccessFineLocation,
            ],
        );
        let pb = PermBox::new(
            app,
            manifest,
            principal,
            [AndroidPermission::AccessFineLocation],
        );
        (pb, app, principal)
    }

    /// **THE VISIBLE-CAPABILITIES TEST: a normal declared permission lights at install; a
    /// dangerous declared one is dim (pending); an undeclared one is dim forever — never
    /// hidden.**
    #[test]
    fn badges_render_lit_dim_with_faithful_reasons() {
        let (pb, app, _principal) = maps_permbox();
        let set = pb.badges();
        assert_eq!(set.cell, app);

        let badge = |p: &AndroidPermission| {
            set.badges
                .iter()
                .find(|b| &b.permission == p)
                .unwrap_or_else(|| panic!("badge for {} is in the roster", p.android_name()))
        };

        // INTERNET (normal, declared) → lit, held at install.
        let net = badge(&AndroidPermission::Internet);
        assert_eq!(net.state, BadgeState::Lit);
        assert_eq!(net.reason, BadgeReason::HeldAtInstall);

        // ACCESS_FINE_LOCATION (dangerous, declared, not yet granted) → dim, pending.
        let loc = badge(&AndroidPermission::AccessFineLocation);
        assert_eq!(loc.state, BadgeState::Dim);
        assert_eq!(loc.reason, BadgeReason::DeclaredNotGranted);

        // CAMERA (dangerous, NOT declared) → dim, un-grantable (no ambient escalation).
        let cam = badge(&AndroidPermission::Camera);
        assert_eq!(cam.state, BadgeState::Dim);
        assert_eq!(cam.reason, BadgeReason::NotDeclared);

        // The whole standard roster is shown (nothing hidden).
        assert_eq!(set.badges.len(), AndroidPermission::all_standard().len());
        assert!(set.all_text().iter().any(|l| l.contains("INTERNET")));
    }

    /// **THE HAND-OVER TEST: granting a declared dangerous permission the principal holds lights
    /// the badge and leaves a receipt — the dialog, reforged into a receipted cap transfer.**
    #[test]
    fn hand_over_lights_a_dangerous_badge_and_receipts() {
        let (mut pb, app, principal) = maps_permbox();
        assert!(
            !pb.holds(&AndroidPermission::AccessFineLocation),
            "dim before"
        );

        let receipt = pb.grant(AndroidPermission::AccessFineLocation);
        assert!(receipt.decision.granted());
        assert_eq!(receipt.principal, principal);
        assert_eq!(receipt.app_cell, app);
        assert!(receipt.status_line().contains("HANDED OVER"));
        assert_eq!(
            receipt.decision_digest,
            PermReceipt::digest(principal, app, &receipt.decision)
        );

        // The badge is now LIT, by hand-over.
        assert!(pb.holds(&AndroidPermission::AccessFineLocation));
        let loc = pb
            .badges()
            .badges
            .into_iter()
            .find(|b| b.permission == AndroidPermission::AccessFineLocation)
            .unwrap();
        assert_eq!(loc.state, BadgeState::Lit);
        assert_eq!(loc.reason, BadgeReason::HeldByGrant);
    }

    /// **THE NO-AMBIENT-ESCALATION TEST: a hand-over of a permission the app never declared is
    /// refused — there is no cap to hold (faithful AOSP: cannot grant an undeclared permission).**
    #[test]
    fn hand_over_of_an_undeclared_permission_is_refused() {
        let (mut pb, _app, _principal) = maps_permbox();
        // The maps app never declared CAMERA.
        let receipt = pb.grant(AndroidPermission::Camera);
        assert!(receipt.decision.refused_not_declared());
        assert!(!pb.holds(&AndroidPermission::Camera));
        assert!(receipt.status_line().contains("no ambient escalation"));
    }

    /// **THE POWERBOX TOOTH: a hand-over of a declared dangerous permission the GRANTER does not
    /// hold is refused — you cannot hand over what you do not hold (mint_needs_held_factory).**
    #[test]
    fn hand_over_the_granter_cannot_back_is_refused() {
        let app = cell_seed(0x52);
        let principal = cell_seed(0x01);
        // The app declares CAMERA, but the principal holds NO camera authority.
        let manifest = AndroidManifest::new("com.example.cam", [AndroidPermission::Camera]);
        let mut pb = PermBox::new(app, manifest, principal, []); // principal holds nothing

        let receipt = pb.grant(AndroidPermission::Camera);
        assert!(receipt.decision.refused_not_held_by_granter());
        assert!(!pb.holds(&AndroidPermission::Camera));
        assert!(receipt
            .status_line()
            .contains("cannot hand over what you do not hold"));
    }

    /// A normal permission is already held at install — the hand-over is a no-op (no dialog ever
    /// existed for a normal permission in AOSP either).
    #[test]
    fn hand_over_of_a_normal_permission_is_a_no_op() {
        let (mut pb, _app, _principal) = maps_permbox();
        assert!(pb.holds(&AndroidPermission::Internet), "lit at install");
        let receipt = pb.grant(AndroidPermission::Internet);
        assert!(receipt.decision.already_held_at_install());
        // Still lit, and NOT in the runtime-granted set (it is install-held).
        assert!(pb.holds(&AndroidPermission::Internet));
        assert!(!pb.granted.contains(&AndroidPermission::Internet));
    }

    /// **REVOKE (the Settings-revoke reforge): a runtime-granted badge dims again, receipted; a
    /// normal install-held permission cannot be runtime-revoked (nothing to revoke).**
    #[test]
    fn revoke_dims_a_runtime_grant_but_not_an_install_grant() {
        let (mut pb, _app, _principal) = maps_permbox();
        pb.grant(AndroidPermission::AccessFineLocation);
        assert!(pb.holds(&AndroidPermission::AccessFineLocation));

        // Revoke the runtime grant → dim again, receipted.
        let r = pb.revoke(AndroidPermission::AccessFineLocation);
        assert!(r.decision.revoked());
        assert!(!pb.holds(&AndroidPermission::AccessFineLocation));
        assert!(r.status_line().contains("REVOKED"));

        // A normal install-held permission has nothing to runtime-revoke.
        let r2 = pb.revoke(AndroidPermission::Internet);
        assert!(matches!(r2.decision, PermDecision::NothingToRevoke { .. }));
        assert!(pb.holds(&AndroidPermission::Internet), "still install-held");
    }

    /// A declared custom (`Other`) permission appears in the roster and fails closed to
    /// dangerous (declared-but-dim until an explicit hand-over).
    #[test]
    fn a_declared_custom_permission_is_shown_and_fails_closed() {
        let app = cell_seed(0x53);
        let principal = cell_seed(0x01);
        let custom = AndroidPermission::Other("com.example.SPECIAL".into());
        let manifest = AndroidManifest::new("com.example.app", [custom.clone()]);
        let pb = PermBox::new(app, manifest, principal, [custom.clone()]);

        let badge = pb
            .badges()
            .badges
            .into_iter()
            .find(|b| b.permission == custom)
            .expect("the declared custom permission is shown in the roster");
        assert_eq!(
            badge.level,
            ProtectionLevel::Dangerous,
            "custom fails closed"
        );
        assert_eq!(badge.state, BadgeState::Dim, "dim until handed over");
        assert_eq!(badge.reason, BadgeReason::DeclaredNotGranted);
    }

    /// **THE checkSelfPermission INTERPOSITION TEST: the confined app's OWN permission check
    /// reads the cap-badge set — a held cap → PERMISSION_GRANTED (0), a dim cap → PERMISSION_DENIED
    /// (-1) in-runtime — and leaves a receipt. A permission whose cap the cell does not hold
    /// genuinely denies the app's own check (not AOSP's framework grant table).**
    #[test]
    fn check_self_permission_routes_through_the_cap_badge_set() {
        let (mut pb, app, _principal) = maps_permbox();

        // A NORMAL declared permission (INTERNET) is held at install → GRANTED in-runtime.
        let net = pb.check_self_permission(&AndroidPermission::Internet);
        assert!(net.result.granted());
        assert_eq!(net.aosp_code(), 0, "PERMISSION_GRANTED == 0");
        assert_eq!(net.result.constant_name(), "PERMISSION_GRANTED");
        assert_eq!(net.app_cell, app);
        assert_eq!(net.reason, BadgeReason::HeldAtInstall);
        assert!(net.status_line().contains("PERMISSION_GRANTED"));
        assert_eq!(
            net.decision_digest,
            PermCheckReceipt::digest(app, &AndroidPermission::Internet, net.result)
        );

        // A DANGEROUS declared-but-not-granted permission (ACCESS_FINE_LOCATION): the cap is dim,
        // so the app's OWN check is DENIED in-runtime — the load-bearing claim.
        let loc_dim = pb.check_self_permission(&AndroidPermission::AccessFineLocation);
        assert!(
            loc_dim.result.denied(),
            "a dim cap denies the app's own check"
        );
        assert_eq!(loc_dim.aosp_code(), -1, "PERMISSION_DENIED == -1");
        assert_eq!(loc_dim.reason, BadgeReason::DeclaredNotGranted);
        assert!(loc_dim.status_line().contains("PERMISSION_DENIED"));

        // An UNDECLARED permission (CAMERA) → DENIED, never declared (no ambient escalation).
        let cam = pb.check_self_permission(&AndroidPermission::Camera);
        assert!(cam.result.denied());
        assert_eq!(cam.reason, BadgeReason::NotDeclared);

        // After a receipted hand-over lights the badge, the SAME check now returns GRANTED —
        // the check verdict and the visible cap-badge can never disagree.
        pb.grant(AndroidPermission::AccessFineLocation);
        let loc_lit = pb.check_self_permission(&AndroidPermission::AccessFineLocation);
        assert!(
            loc_lit.result.granted(),
            "the granted cap now grants the check"
        );
        assert_eq!(loc_lit.reason, BadgeReason::HeldByGrant);
        assert_ne!(
            loc_dim.decision_digest, loc_lit.decision_digest,
            "the verdict is bound into the digest (denied ≠ granted)"
        );
    }

    // ── THE REAL KERNEL HAND-OVER tests (PermWorld) ──────────────────────────

    /// Build a `PermWorld` for a maps app declaring INTERNET (normal) +
    /// ACCESS_FINE_LOCATION (dangerous), whose principal holds the location device authority.
    fn maps_permworld() -> PermWorld {
        let manifest = AndroidManifest::new(
            "com.example.maps",
            [
                AndroidPermission::Internet,
                AndroidPermission::AccessFineLocation,
            ],
        );
        PermWorld::install(
            0x51,
            0x01,
            manifest,
            [AndroidPermission::AccessFineLocation],
        )
    }

    /// **THE REAL-CAP-LANDING TEST: `PermWorld::grant` of a dangerous permission commits a REAL
    /// `GrantCapability` turn, the cap lands in the android-cell's c-list, and the badge is Lit
    /// because the cell GENUINELY holds it — not just a content-addressed witness.**
    #[test]
    fn kernel_grant_lands_a_real_cap_in_the_cells_clist_and_lights_the_badge() {
        let mut pw = maps_permworld();
        let app = pw.app_cell();
        let organ = AndroidPermission::AccessFineLocation.grant_target(app);

        // Before: the dangerous badge is dim (declared, awaiting hand-over) and the cell's REAL
        // c-list does NOT reach the location organ.
        assert!(!pw.holds(&AndroidPermission::AccessFineLocation));
        assert!(
            !pw.ledger()
                .get(&app)
                .unwrap()
                .capabilities
                .has_access(&organ),
            "precondition: the android-cell does NOT reach the location organ before the grant"
        );
        let loc_before = pw
            .badges()
            .badges
            .into_iter()
            .find(|b| b.permission == AndroidPermission::AccessFineLocation)
            .unwrap();
        assert_eq!(loc_before.state, BadgeState::Dim);
        assert_eq!(loc_before.reason, BadgeReason::DeclaredNotGranted);

        // THE REAL MINT: a genuine GrantCapability turn through the verified executor.
        let outcome = pw.grant(AndroidPermission::AccessFineLocation);
        assert!(
            outcome.granted(),
            "the held, declared dangerous grant commits"
        );
        let receipt = outcome
            .receipt()
            .expect("a committed grant carries a kernel TurnReceipt");
        assert_eq!(
            receipt.agent,
            pw.principal(),
            "the turn was the principal's"
        );
        assert!(receipt.action_count >= 1, "a real verified turn landed");

        // After: the cap GENUINELY lives in the android-cell's real c-list, reaching the organ
        // at the template ceiling (Signature), and the badge is now Lit BY GRANT.
        assert!(pw.holds(&AndroidPermission::AccessFineLocation));
        let granted = pw
            .ledger()
            .get(&app)
            .unwrap()
            .capabilities
            .iter()
            .find(|cr| cr.target == organ)
            .expect("the granted organ cap is in the android-cell's c-list");
        assert_eq!(
            granted.permissions,
            AuthRequired::Signature,
            "the cap carries the template ceiling, never wider (no amplification)"
        );
        let loc_after = pw
            .badges()
            .badges
            .into_iter()
            .find(|b| b.permission == AndroidPermission::AccessFineLocation)
            .unwrap();
        assert_eq!(loc_after.state, BadgeState::Lit, "the badge flips Lit");
        assert_eq!(loc_after.reason, BadgeReason::HeldByGrant);
    }

    /// **THE NO-AMBIENT-ESCALATION TEST (kernel): an UNDECLARED permission still refuses — no cap
    /// template, no turn, the cell never reaches its organ.**
    #[test]
    fn kernel_grant_of_an_undeclared_permission_still_refuses() {
        let mut pw = maps_permworld();
        // The maps app never declared CAMERA.
        let outcome = pw.grant(AndroidPermission::Camera);
        assert!(outcome.refused_not_declared());
        assert!(
            outcome.receipt().is_none(),
            "a refused hand-over runs no turn"
        );
        assert!(!pw.holds(&AndroidPermission::Camera));
        let cam_organ = AndroidPermission::Camera.grant_target(pw.app_cell());
        assert!(
            !pw.ledger()
                .get(&pw.app_cell())
                .unwrap()
                .capabilities
                .has_access(&cam_organ),
            "the android-cell never reaches the camera organ"
        );
    }

    /// **THE POWERBOX TOOTH AT THE REAL KERNEL: a declared dangerous permission the PRINCIPAL does
    /// not hold is refused by the executor itself (`mint_needs_held_factory` / CapabilityNotHeld) —
    /// the real backstop, not our pre-check. The cap never lands.**
    #[test]
    fn kernel_grant_the_principal_cannot_back_is_refused_by_the_executor() {
        // The app declares CAMERA, but the principal holds NO camera authority.
        let manifest = AndroidManifest::new("com.example.cam", [AndroidPermission::Camera]);
        let mut pw = PermWorld::install(0x52, 0x02, manifest, []); // principal holds nothing
        let app = pw.app_cell();

        let outcome = pw.grant(AndroidPermission::Camera);
        assert!(
            outcome.refused_by_kernel(),
            "the executor refuses a grant the principal cannot back"
        );
        match &outcome {
            KernelGrantOutcome::RefusedByKernel { reason, .. } => assert!(
                reason.contains("CapabilityNotHeld") || reason.contains("Delegation"),
                "the kernel reason cites the held-authority requirement, got: {reason}"
            ),
            other => panic!("expected a kernel refusal, got {other:?}"),
        }
        assert!(!pw.holds(&AndroidPermission::Camera));
        let organ = AndroidPermission::Camera.grant_target(app);
        assert!(
            !pw.ledger()
                .get(&app)
                .unwrap()
                .capabilities
                .has_access(&organ),
            "the cap never landed"
        );
    }

    /// A `Normal` permission is already held at install — the kernel hand-over is a no-op, no turn.
    #[test]
    fn kernel_grant_of_a_normal_permission_is_a_no_op() {
        let mut pw = maps_permworld();
        assert!(pw.holds(&AndroidPermission::Internet), "lit at install");
        let outcome = pw.grant(AndroidPermission::Internet);
        assert!(matches!(
            outcome,
            KernelGrantOutcome::AlreadyHeldAtInstall { .. }
        ));
        assert!(
            outcome.receipt().is_none(),
            "no turn for an install-held permission"
        );
        assert!(pw.holds(&AndroidPermission::Internet));
    }

    /// **THE checkSelfPermission INTERPOSITION OVER THE REAL c-list: the app's own check reads the
    /// android-cell's GENUINE capability c-list — a dangerous permission denies in-runtime
    /// (PERMISSION_DENIED, -1) until a real GrantCapability turn lands its organ cap, then the SAME
    /// check grants (PERMISSION_GRANTED, 0). A receipt is left.**
    #[test]
    fn kernel_check_self_permission_reads_the_live_clist() {
        let mut pw = maps_permworld();
        let app = pw.app_cell();

        // INTERNET (normal, install-held) → GRANTED from the live ledger.
        let net = pw.check_self_permission(&AndroidPermission::Internet);
        assert!(net.result.granted());
        assert_eq!(net.aosp_code(), 0);
        assert_eq!(net.app_cell, app);

        // ACCESS_FINE_LOCATION before the grant: the real c-list does NOT reach the organ, so the
        // app's own check is DENIED in-runtime.
        let loc_before = pw.check_self_permission(&AndroidPermission::AccessFineLocation);
        assert!(
            loc_before.result.denied(),
            "no organ cap in the c-list → the app's checkSelfPermission denies"
        );
        assert_eq!(loc_before.aosp_code(), -1);
        assert_eq!(loc_before.reason, BadgeReason::DeclaredNotGranted);
        assert_eq!(
            loc_before.decision_digest,
            PermCheckReceipt::digest(
                app,
                &AndroidPermission::AccessFineLocation,
                loc_before.result
            )
        );

        // The REAL hand-over lands the organ cap in the cell's c-list.
        assert!(pw.grant(AndroidPermission::AccessFineLocation).granted());

        // Now the SAME check reads the live c-list and GRANTS — the cap genuinely landed.
        let loc_after = pw.check_self_permission(&AndroidPermission::AccessFineLocation);
        assert!(
            loc_after.result.granted(),
            "the landed cap grants the in-runtime check"
        );
        assert_eq!(loc_after.reason, BadgeReason::HeldByGrant);

        // An UNDECLARED permission denies (no cap template, never reaches the c-list).
        let cam = pw.check_self_permission(&AndroidPermission::Camera);
        assert!(cam.result.denied());
        assert_eq!(cam.reason, BadgeReason::NotDeclared);
    }
}
