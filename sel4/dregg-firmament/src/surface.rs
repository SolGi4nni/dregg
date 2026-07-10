//! The SURFACE backing — a window IS a dregg cell's surface capability.
//!
//! `docs/DREGG-DESKTOP-OS.md` casts the dregg-native desktop as **the firmament
//! made visual**: a window is a `Capability{ target: Surface(cell), rights }` on
//! the SAME `(target, rights)` handle that today resolves [`crate::Target::Local`]
//! (an seL4 syscall) and [`crate::Target::Distributed`] (a real executor turn).
//! A surface is not a new kind of authority — it is a dregg **cell** whose state
//! is rendered as glass. Holding a window means holding a cap over that cell;
//! attenuating the window (read-only mirror, input-disabled view, a clipped
//! sub-region) is attenuating the cap; delegating the window to another app is
//! delegating the cap; revoking it is revoking the cap. All through the SAME
//! gate as every other firmament cap.
//!
//! Concretely this backing is the [`crate::DistributedBacking`] machinery aimed
//! at a cell that backs a surface: it holds a real [`dregg_cell::Ledger`] and a
//! real [`dregg_turn::TurnExecutor`], and
//!
//! - [`SurfaceBacking::invoke`] resolves a surface cap by reading the surface
//!   cell out of the real ledger and checking `requested ⊆ held` via the REAL
//!   [`dregg_cell::is_attenuation`] (e.g. an app asking to *draw* into a surface
//!   it only holds a read-only mirror of is refused — the same direction the
//!   kernel's cap-rights check enforces locally).
//! - [`SurfaceBacking::delegate`] runs a GENUINE `Effect::GrantCapability` turn
//!   through [`dregg_turn::TurnExecutor::execute`], so handing a window to
//!   another cell gates on `granted ⊆ held` enforced by the real executor. A
//!   WIDENING surface grant (handing out *more* rights over the glass than you
//!   hold — e.g. promoting a read-only mirror to a writable surface) is rejected
//!   by the executor with `DelegationDenied`. There is no separate "surface
//!   authority" to reinvent; the compositor multiplexes capabilities, it does
//!   not mint authority.
//!
//! The payoff this makes load-bearing: "a window = a cell's surface capability"
//! is REAL, validated by a turn against the deployed executor, with zero new
//! trust surface and zero drivers — exactly the bridge the local and
//! distributed backings already proved, reused for the glass.

use std::collections::HashMap;

use dregg_cell::{AuthRequired, CapabilityRef, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Turn, TurnExecutor,
    TurnResult,
};

use crate::{Backing, Bounds, Resolution, ResolveError, Rights};

/// The surface backing: a real dregg ledger + executor, where each cell backs a
/// rendered surface (a window). `n` is the number of machines the surfaces are
/// spread across; `n = 1` is the firmament's collapsed limit — the compositor
/// and the apps share one box, so a surface revoke is immediate (the glass goes
/// dark the instant the syscall returns) and a present is synchronous.
pub struct SurfaceBacking {
    ledger: Ledger,
    executor: TurnExecutor,
    /// The distance parameter for THIS surface fabric (how spread the surface
    /// cells are). `n = 1` = compositor + apps co-located; `n > 1` = a surface
    /// whose backing cell lives on another machine (a remote window).
    pub n: u32,
}

impl SurfaceBacking {
    /// A fresh single-machine (`n = 1`) surface fabric with an empty ledger.
    pub fn new() -> Self {
        SurfaceBacking {
            ledger: Ledger::new(),
            executor: TurnExecutor::new(ComputronCosts::zero()),
            n: 1,
        }
    }

    /// Set the distance parameter (the number of machines the surfaces span).
    /// `n = 1` keeps the strong local bounds (immediate dark-on-revoke,
    /// synchronous present); `n > 1` relaxes them (a remote window over the
    /// wire — the same reach-out the distributed backing models).
    pub fn with_distance(mut self, n: u32) -> Self {
        self.n = n;
        self
    }

    /// Seed a SURFACE cell into the real ledger with permissive permissions,
    /// returning its [`CellId`]. This is the cell whose state is rendered as a
    /// window; the deterministic key derivation mirrors the protocol-test
    /// generators so surfaces are addressable by seed.
    pub fn seed_surface(&mut self, seed: u8) -> CellId {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(7);
        let mut cell = Cell::with_balance(pk, [0u8; 32], 10_000);
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
        let id = cell.id();
        self.ledger.insert_cell(cell).expect("seed surface cell");
        id
    }

    /// Grant `holder` an ORIGINAL capability over the `surface` cell with
    /// `rights` — the compositor minting a window handle into an app's c-list
    /// (the powerbox handing an app a surface). The compositor multiplexes
    /// capabilities; it does not invent authority — so this is the SAME
    /// original-grant shape as [`crate::DistributedBacking::install`].
    pub fn install(&mut self, holder: CellId, surface: CellId, rights: Rights) {
        let cell = self.ledger.get_mut(&holder).expect("holder cell exists");
        // Replace any auto-granted cap to `surface` with one at exactly `rights`.
        if let Some(slot) = cell.capabilities.lookup_by_target(&surface).map(|c| c.slot) {
            cell.capabilities.revoke(slot);
        }
        cell.capabilities.grant(surface, rights);
    }

    /// Resolve (invoke) a holder's capability over a `surface` with `rights` —
    /// e.g. presenting/drawing into the window.
    ///
    /// Models a turn that resolves the surface cap against real cell-state: the
    /// held cap must exist and cover the requested `rights` (`requested ⊆ held`,
    /// the REAL [`dregg_cell::is_attenuation`]). An app holding only a
    /// read-only mirror that asks for a wider authority than it holds is refused
    /// — the same cap-rights direction the kernel enforces for a local frame.
    /// Returns a [`Resolution`] with the `n`-parametrized bounds (collapsing to
    /// strong-local at `n = 1`).
    pub fn invoke(
        &self,
        holder: CellId,
        surface: CellId,
        rights: &Rights,
    ) -> Result<Resolution, ResolveError> {
        let cell = self
            .ledger
            .get(&holder)
            .ok_or(ResolveError::TargetNotFound)?;
        let held = cell
            .capabilities
            .lookup_by_target(&surface)
            .ok_or(ResolveError::TargetNotFound)?;
        if !dregg_cell::is_attenuation(&held.permissions, rights) {
            return Err(ResolveError::Unauthorized(format!(
                "dregg surface cap-authority check: requested {:?} exceeds held {:?} over surface",
                rights, held.permissions
            )));
        }
        Ok(Resolution {
            backing: Backing::DistributedTurn,
            bounds: Bounds::distributed(self.n),
            note: format!(
                "turn resolved surface cap (held {:?}, n={})",
                held.permissions, self.n
            ),
        })
    }

    /// `recKDelegateAtten` for a SURFACE — handing a window to another cell,
    /// run as a GENUINE turn through the real executor.
    ///
    /// `granter` issues `Effect::GrantCapability(surface, narrower)` to
    /// `recipient` (e.g. sharing a clipped read-only view of a window with
    /// another app). The REAL executor enforces `granted ⊆ held`: it commits
    /// iff the surface grant is attenuating, and rejects with `DelegationDenied`
    /// otherwise. A WIDENING surface grant — handing out more authority over the
    /// glass than you hold — is refused by the executor, byte-for-byte the
    /// deployed semantics. Returns `Ok(())` on a committed (attenuating) grant;
    /// `Err(BackingRejected)` if the executor refused.
    pub fn delegate(
        &mut self,
        granter: CellId,
        recipient: CellId,
        surface: CellId,
        narrower: Rights,
    ) -> Result<(), ResolveError> {
        // Chain the shared window handle onto the granter's HELD surface cap: the
        // executor's grant arm (`grant_ref`) folds this `provenance` in as the
        // installed cap's PARENT, so revoking the granter's window cap transitively
        // dims every clipped view it handed out (the seL4 MDB subtree teardown).
        // Fall back to a mint-rooted parent only if no held surface cap exists (the
        // executor's attenuation gate then rejects the widening grant).
        let parent_provenance = self
            .ledger
            .get(&granter)
            .and_then(|c| c.capabilities.lookup_by_target(&surface))
            .map(|held| held.provenance)
            .unwrap_or_else(dregg_cell::derivation::mint_provenance);
        let cap = CapabilityRef {
            target: surface,
            slot: 0, // rewritten by the executor on grant
            permissions: narrower,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
            provenance: parent_provenance,
        };
        self.run_grant_turn(
            granter,
            Effect::GrantCapability {
                from: granter,
                to: recipient,
                cap,
            },
            "surface grant",
        )
    }

    /// Build + execute a one-effect turn from `agent` through the REAL executor,
    /// correctly chained into the deployed receipt chain.
    ///
    /// The executor enforces a per-agent receipt chain (`ReceiptChainMismatch`):
    /// the FIRST turn from an agent carries `previous_receipt_hash: None`, and
    /// each SUBSEQUENT turn must carry the prior receipt's hash. A window manager
    /// issues MANY surface turns (present / embed / grant-input / revoke in one
    /// session), so the verbs MUST chain — we read the executor's tracked last
    /// hash ([`TurnExecutor::get_last_receipt_hash`]) and the cell's fresh nonce
    /// (the executor bumps it on each commit) so consecutive verbs from the same
    /// agent are accepted, not rejected as a replay. Returns `Ok(())` on a
    /// committed turn; `Err(BackingRejected)` if the executor refused (a widening
    /// grant/embed, missing connectivity, denied consent — byte-for-byte the
    /// deployed semantics).
    fn run_grant_turn(
        &mut self,
        agent: CellId,
        effect: Effect,
        what: &str,
    ) -> Result<(), ResolveError> {
        let nonce = self.ledger.get(&agent).expect("agent exists").state.nonce();
        // Chain into the real receipt chain: None for the agent's first turn, the
        // prior receipt's hash thereafter (the executor tracks it per-agent).
        let previous_receipt_hash = self.executor.get_last_receipt_hash(&agent);
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Default::default(),
            effects: vec![effect],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        let turn = Turn {
            agent,
            nonce,
            call_forest: forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let result = self.executor.execute(&turn, &mut self.ledger);
        match result {
            r if r.is_committed() => Ok(()),
            TurnResult::Rejected { reason, .. } => Err(ResolveError::BackingRejected(format!(
                "executor refused {}: {:?}",
                what, reason
            ))),
            other => Err(ResolveError::BackingRejected(format!(
                "unexpected: {:?}",
                other
            ))),
        }
    }

    // ── THE FIVE CAP-CONFINED SURFACE VERBS (`docs/DREGG-DESKTOP-OS.md §5`) ──
    //
    // `create-surface` / `present` / `embed` / `grant-input` / `revoke`. Every
    // one routes through the SAME real executor + the SAME `is_attenuation`
    // (`granted ⊆ held`) gate as every other dregg cap — the compositor
    // multiplexes capabilities, it never mints authority. `embed` is authorized
    // by the REAL `Effect::Introduce` discipline (connectivity + holds-target +
    // non-amplifying + consent — the four premises `apply_introduce` checks in
    // `turn/src/executor/apply.rs`), so a surface-tree edge is exactly dregg's
    // three-party introduction, NOT a parallel handshake.

    /// **CREATE-SURFACE** — birth a new surface cell and hand `owner` the window.
    ///
    /// `docs/DREGG-DESKTOP-OS.md §5`: "authorized by a surface-factory cap; the
    /// factory CONTRACT bounds what surface/input rights the cell may ever hold."
    /// This is the powerbox handing an app a fresh window: it seeds the surface
    /// cell (the View — its state is what the compositor renders) and grants
    /// `owner` an ORIGINAL cap over it at `rights` (the Viewport the parent
    /// holds). The compositor multiplexes caps; it does not invent authority, so
    /// the grant is the same original-grant shape every backing uses. Returns the
    /// new surface's [`CellId`] (its ViewRef — already unforgeable,
    /// content-addressed).
    pub fn create_surface(&mut self, owner: CellId, seed: u8, rights: Rights) -> CellId {
        let surface = self.seed_surface(seed);
        self.install(owner, surface, rights);
        surface
    }

    /// **PRESENT** — `holder` draws into its `surface` (paints a frame).
    ///
    /// `docs/DREGG-DESKTOP-OS.md §5`: "requires a write-cap on the surface." A
    /// present is a turn that resolves the surface cap against real cell-state
    /// requiring DRAW authority (`required ⊆ held`, the REAL
    /// [`dregg_cell::is_attenuation`]): an app holding only a read-only mirror is
    /// refused exactly as the kernel refuses a write on a read-only frame. The
    /// caller passes the authority the draw requires (`required`); at `n = 1` the
    /// present is synchronous (the pixel lands the instant it returns). Returns a
    /// [`Resolution`] carrying the `n`-parametrized bounds.
    ///
    /// (The compositor-PD's SCENE gate — T1 non-overlap / T2 label-binding / T3
    /// focus — is enforced separately in [`crate::compositor_pd`]; THIS verb is
    /// the cap-authority half: does the presenter even hold draw-rights over the
    /// surface? Both must pass for a frame to composite.)
    pub fn present(
        &self,
        holder: CellId,
        surface: CellId,
        required: &Rights,
    ) -> Result<Resolution, ResolveError> {
        // PRESENT is exactly an invoke that requires draw authority over the
        // surface cap — the read-only-mirror refusal falls out of the real
        // `is_attenuation` direction with no special-casing.
        self.invoke(holder, surface, required)
    }

    /// **EMBED** — make a surface-tree edge from `recipient` to a `child_surface`,
    /// authorized by the REAL three-party introduction.
    ///
    /// `docs/DREGG-DESKTOP-OS.md §5`: "a surface-tree edge authorized ONLY by
    /// `Spec.Authority.Introduce` — Fuchsia's non-clonable token handshake IS
    /// dregg's introduce; the surface tree is decoupled from the cell-ownership
    /// tree." This runs a GENUINE [`Effect::Introduce`] turn through the real
    /// executor, so the edge is gated by the FOUR premises `apply_introduce`
    /// checks (`turn/src/executor/apply.rs`):
    ///
    /// 1. **connectivity** — the `introducer` (the parent window manager) holds a
    ///    cap to the `recipient` (`has_access`);
    /// 2. **holds-target** — the `introducer` holds a cap over the
    ///    `child_surface`;
    /// 3. **non-amplification** — the embedded `rights` are `⊆` the introducer's
    ///    own over the child (`is_attenuation`); a WIDENING embed is REJECTED;
    /// 4. **consent** — the `child_surface` cell allows delegation
    ///    (`delegate != Impossible`).
    ///
    /// On success the `recipient` gains an (expiry-stamped) Viewport cap over the
    /// child surface — the compositor can now composite the child inside the
    /// parent's frame. Returns `Ok(())` on a committed embed; `Err(BackingRejected)`
    /// if the executor refused (missing connectivity, a widening grant, or denied
    /// consent) — byte-for-byte the deployed introduction semantics.
    pub fn embed(
        &mut self,
        introducer: CellId,
        recipient: CellId,
        child_surface: CellId,
        rights: Rights,
    ) -> Result<(), ResolveError> {
        self.run_grant_turn(
            introducer,
            Effect::Introduce {
                introducer,
                recipient,
                target: child_surface,
                permissions: rights,
            },
            "surface embed (Introduce)",
        )
    }

    /// **GRANT-INPUT** — hand `recipient` a (narrowed) input-receive facet over a
    /// `surface`, run as a GENUINE grant turn.
    ///
    /// `docs/DREGG-DESKTOP-OS.md §5`: "the explicit attenuable cap Wayland leaves
    /// as an ungoverned 'privileged client' bit — in dregg a global screenshot
    /// cap simply does NOT exist unless minted." Focus IS a capability: the
    /// compositor grants a short-lived input-receive cap to exactly one surface;
    /// this verb is that grant, run through the real executor's `granted ⊆ held`
    /// gate (the SAME `Effect::GrantCapability` as [`Self::delegate`]). A WIDENING
    /// input grant — handing out more authority over the surface than you hold —
    /// is REJECTED by the executor (`DelegationDenied`). Returns `Ok(())` on a
    /// committed (attenuating) grant; `Err(BackingRejected)` otherwise.
    ///
    /// (`grant_input` is `delegate` named for the input facet; they share the
    /// real grant path so input-routing rides the identical attenuation law as
    /// every surface delegation — only the caller's INTENT differs.)
    pub fn grant_input(
        &mut self,
        granter: CellId,
        recipient: CellId,
        surface: CellId,
        narrower: Rights,
    ) -> Result<(), ResolveError> {
        self.delegate(granter, recipient, surface, narrower)
    }

    /// **REVOKE** — drop `holder`'s cap over the `surface`; the glass goes dark.
    ///
    /// `docs/DREGG-DESKTOP-OS.md §5`: "drops the surface cap; n=1 immediate via
    /// seL4_CNode_Revoke." At `n = 1` (compositor + apps on one box) this is
    /// SYNCHRONOUS — the surface cap is dead the instant `revoke` returns, with
    /// no in-flight window (a subsequent [`Self::present`] / [`Self::invoke`]
    /// finds nothing held and is refused, so the window cannot paint even one
    /// more frame). This is the surface analog of the local
    /// [`crate::LocalBacking::revoke`]'s synchronous-transitive removal; here it
    /// removes the holder's surface cap from real cell-state. Returns `true` iff
    /// a live surface cap was removed.
    ///
    /// At `n > 1` (a remote window) revocation is the group-key epoch lift
    /// (eventual — the [`crate::Bounds::distributed`] relax); this `n = 1` path
    /// is the collapsed limit where the dark-on-revoke is immediate.
    pub fn revoke(&mut self, holder: CellId, surface: CellId) -> bool {
        let cell = match self.ledger.get_mut(&holder) {
            Some(c) => c,
            None => return false,
        };
        match cell.capabilities.lookup_by_target(&surface).map(|c| c.slot) {
            Some(slot) => cell.capabilities.revoke(slot),
            None => false,
        }
    }

    /// Does `recipient` hold a cap over the `surface`? (Used to confirm a
    /// window-share landed — the surface analog of
    /// [`crate::DistributedBacking::holds_cap`].)
    pub fn holds_cap(&self, recipient: CellId, surface: CellId) -> bool {
        self.ledger
            .get(&recipient)
            .map(|c| c.capabilities.lookup_by_target(&surface).is_some())
            .unwrap_or(false)
    }

    /// The rights `recipient` holds over the `surface`, if any.
    pub fn rights_held(&self, recipient: CellId, surface: CellId) -> Option<Rights> {
        self.ledger.get(&recipient).and_then(|c| {
            c.capabilities
                .lookup_by_target(&surface)
                .map(|r| r.permissions.clone())
        })
    }
}

impl Default for SurfaceBacking {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_executor_enforces_attenuation_on_surface_share() {
        let mut fab = SurfaceBacking::new();
        let app = fab.seed_surface(0);
        let other = fab.seed_surface(1);
        let window = fab.seed_surface(2);

        // The app holds a writable (Either) surface cap over the window.
        fab.install(app, window, AuthRequired::Either);

        // Sharing a NARROWER view (Either -> Signature, a read-only-mirror-shaped
        // narrowing) COMMITS through the real executor.
        assert!(fab
            .delegate(app, other, window, AuthRequired::Signature)
            .is_ok());
        assert!(fab.holds_cap(other, window));
        assert_eq!(
            fab.rights_held(other, window),
            Some(AuthRequired::Signature)
        );
    }

    #[test]
    fn real_executor_rejects_widening_surface_share() {
        let mut fab = SurfaceBacking::new();
        let app = fab.seed_surface(0);
        let other = fab.seed_surface(1);
        let window = fab.seed_surface(2);

        // The app holds only a read-only mirror (Signature) of the window.
        fab.install(app, window, AuthRequired::Signature);

        // Handing out a WIDER surface authority (Signature -> None, promoting a
        // read-only mirror to a fully-authorized surface) is REJECTED by the
        // real executor (DelegationDenied), and the other app gets nothing.
        let r = fab.delegate(app, other, window, AuthRequired::None);
        assert!(r.is_err());
        assert!(!fab.holds_cap(other, window));
    }

    // ── THE FIVE VERBS (create-surface / present / embed / grant-input / revoke)

    #[test]
    fn create_surface_hands_the_owner_a_window_cap() {
        // CREATE-SURFACE: the powerbox births a surface cell and grants the owner
        // a window cap over it — the owner now holds the Viewport.
        let mut fab = SurfaceBacking::new();
        let app = fab.seed_surface(0);
        let window = fab.create_surface(app, 9, AuthRequired::None);
        assert!(
            fab.holds_cap(app, window),
            "owner must hold the new window cap"
        );
        assert_eq!(fab.rights_held(app, window), Some(AuthRequired::None));
    }

    #[test]
    fn present_requires_draw_rights_read_only_mirror_refused() {
        // PRESENT: drawing into a surface requires draw authority; an app holding
        // only a read-only mirror (a NARROWER authority than the draw requires)
        // is refused by the real `is_attenuation` direction.
        let mut fab = SurfaceBacking::new();
        let app = fab.seed_surface(0);
        let window = fab.seed_surface(2);

        // Holds a writable (Either) cap: a present requiring Either succeeds, and
        // requiring a narrower Signature (⊆ Either) also succeeds.
        fab.install(app, window, AuthRequired::Either);
        assert!(fab.present(app, window, &AuthRequired::Either).is_ok());
        assert!(fab.present(app, window, &AuthRequired::Signature).is_ok());

        // Holds only a read-only mirror (Signature): a present requiring the
        // BROADER None authority exceeds the held cap — REFUSED (the read-only
        // mirror cannot draw).
        let mirror = fab.seed_surface(3);
        fab.install(app, mirror, AuthRequired::Signature);
        assert!(
            fab.present(app, mirror, &AuthRequired::None).is_err(),
            "a read-only mirror must NOT be able to draw"
        );

        // PRESENT carries the n=1 strong bounds (synchronous — the pixel lands at
        // once).
        let res = fab.present(app, window, &AuthRequired::Either).unwrap();
        assert_eq!(res.bounds, Bounds::LOCAL);
    }

    #[test]
    fn embed_via_real_introduce_commits_then_widening_rejected() {
        // EMBED: a surface-tree edge authorized by the REAL three-party
        // introduction. The window-manager (introducer) embeds a child surface
        // into a recipient app, gated by the four `apply_introduce` premises.
        let mut fab = SurfaceBacking::new();
        let wm = fab.seed_surface(0); // the window-manager (introducer)
        let app = fab.seed_surface(1); // the recipient (the framed app)
        let child = fab.seed_surface(2); // the child surface to embed

        // Premise 1 (connectivity): the wm holds a cap to the recipient app.
        fab.install(wm, app, AuthRequired::None);
        // Premise 2 (holds-target): the wm holds a writable cap over the child.
        fab.install(wm, child, AuthRequired::Either);

        // A NARROWING embed (Either -> Signature, a read-only child view) COMMITS
        // through the real Introduce — the recipient gains the Viewport.
        assert!(
            fab.embed(wm, app, child, AuthRequired::Signature).is_ok(),
            "an attenuating embed must commit via the real Introduce"
        );
        assert!(
            fab.holds_cap(app, child),
            "the recipient must hold the embedded child cap"
        );
        assert_eq!(fab.rights_held(app, child), Some(AuthRequired::Signature));

        // A WIDENING embed (the wm holds only Signature over child2, tries to
        // embed None) is REJECTED by the executor (Introduction amplification
        // denied) — premise 3 fires.
        let child2 = fab.seed_surface(3);
        let app2 = fab.seed_surface(4);
        fab.install(wm, app2, AuthRequired::None); // connectivity to app2
        fab.install(wm, child2, AuthRequired::Signature); // wm holds only Signature
        let r = fab.embed(wm, app2, child2, AuthRequired::None);
        assert!(
            r.is_err(),
            "a widening embed must be REJECTED by the real Introduce"
        );
        assert!(
            !fab.holds_cap(app2, child2),
            "the recipient gets nothing on a refused embed"
        );
    }

    #[test]
    fn embed_without_connectivity_is_refused() {
        // EMBED premise 1 (connectivity): an introducer with NO cap to the
        // recipient cannot embed — `apply_introduce` refuses ("introducer has no
        // capability to recipient").
        let mut fab = SurfaceBacking::new();
        let wm = fab.seed_surface(0);
        let stranger = fab.seed_surface(1);
        let child = fab.seed_surface(2);

        // The wm holds the child but has NO cap to the stranger.
        fab.install(wm, child, AuthRequired::Either);
        let r = fab.embed(wm, stranger, child, AuthRequired::Signature);
        assert!(
            r.is_err(),
            "no connectivity to the recipient ⇒ embed refused"
        );
        assert!(!fab.holds_cap(stranger, child));
    }

    #[test]
    fn grant_input_attenuates_and_rejects_widening() {
        // GRANT-INPUT: focus is a capability; granting an input-receive facet
        // rides the SAME `granted ⊆ held` gate. A narrowing grant commits; a
        // widening one is rejected.
        let mut fab = SurfaceBacking::new();
        let compositor = fab.seed_surface(0);
        let focused = fab.seed_surface(1);
        let surface = fab.seed_surface(2);

        // The compositor holds a writable (Either) cap over the surface.
        fab.install(compositor, surface, AuthRequired::Either);

        // Granting a narrowed input facet (Either -> Signature) COMMITS.
        assert!(
            fab.grant_input(compositor, focused, surface, AuthRequired::Signature)
                .is_ok(),
            "an attenuating input grant must commit"
        );
        assert!(fab.holds_cap(focused, surface));

        // A WIDENING input grant (the compositor holds only Signature over a
        // second surface, tries to grant None) is REJECTED.
        let surface2 = fab.seed_surface(3);
        let other = fab.seed_surface(4);
        fab.install(compositor, surface2, AuthRequired::Signature);
        let r = fab.grant_input(compositor, other, surface2, AuthRequired::None);
        assert!(r.is_err(), "a widening input grant must be REJECTED");
        assert!(!fab.holds_cap(other, surface2));
    }

    #[test]
    fn revoke_darkens_the_glass_synchronously_at_n1() {
        // REVOKE: dropping the surface cap is synchronous at n=1 — the window
        // goes dark the instant revoke returns, and a subsequent present finds
        // nothing held (the window cannot paint even one more frame).
        let mut fab = SurfaceBacking::new();
        let app = fab.seed_surface(0);
        let window = fab.create_surface(app, 9, AuthRequired::Either);

        // Before revoke: the app can present.
        assert!(fab.present(app, window, &AuthRequired::Either).is_ok());

        // Revoke the window cap — returns having ALREADY removed it (synchronous).
        assert!(
            fab.revoke(app, window),
            "revoke removes the live surface cap"
        );
        assert!(
            !fab.holds_cap(app, window),
            "the cap is dead the instant revoke returns"
        );

        // After revoke: the present is refused — the glass is dark, no in-flight
        // frame (the n=1 immediacy: TargetNotFound, the cap is simply gone).
        assert!(
            fab.present(app, window, &AuthRequired::Either).is_err(),
            "a revoked window cannot paint even one more frame at n=1"
        );

        // Revoking an absent cap is a no-op false.
        assert!(
            !fab.revoke(app, window),
            "revoking an already-dead cap is a no-op"
        );
    }
}
