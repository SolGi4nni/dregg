//! The WEB SURFACE — a browser window IS a dregg cell's surface capability.
//!
//! This is the in-tab realization of `sel4/dregg-firmament/src/surface.rs`'s
//! `Target::Surface{cell}` arm (`docs/design-frontiers/WEB-FORWARD.md §2`, the
//! N10 slice of `docs/FRONTIER-ROADMAP.md`). The native `SurfaceBacking` holds
//! its own [`Ledger`] + [`TurnExecutor`]; here we MIRROR its verb shapes onto
//! the EXISTING [`DreggRuntime`] ledger + executor, so a browser surface rides
//! the SAME real `dregg-cell`/`dregg-turn` world the ~80 existing bindings drive
//! — never a parallel surface model.
//!
//! The discipline, byte-for-byte the firmament's:
//!
//! - **`open_surface`** — register a holder's view over a cell that backs a
//!   surface (a window). A surface is not a new kind of authority — it is a
//!   dregg cell whose state the compositor renders as glass. "Opening" a cell as
//!   a surface returns its live identity (the T2 badge) and seeds the owner an
//!   original surface cap, exactly the powerbox shape
//!   [`SurfaceBacking::create_surface`] / `install` uses.
//! - **`present`** — resolve the surface cap against real cell-state requiring
//!   the draw authority (`requested ⊆ held`, the REAL [`dregg_cell::is_attenuation`]).
//!   A read-only mirror that asks for a wider authority than it holds is refused,
//!   the same direction the kernel refuses a write on a read-only frame.
//! - **`share_surface`** — hand a window to another cell as a GENUINE
//!   `Effect::GrantCapability` turn through the real executor, so it gates on
//!   `granted ⊆ held`. A WIDENING surface share is rejected by the executor with
//!   `DelegationDenied` — the no-amplification law firing at the pixel layer.
//! - **`revoke_surface`** — drop the holder's surface cap; at n=1 (the local tab)
//!   the glass goes dark the instant it returns (a subsequent `present` finds
//!   nothing held).
//! - **`surface_identity`** — the anti-spoof T2 badge: `(owningCellId, lifecycle,
//!   sourceStateRoot)` read FROM THE LIVE LEDGER, never the page's
//!   self-description. A label ≠ owner is impossible because the badge is a
//!   function of the cell's real state, not a `<div>` the page drew.
//!
//! The compositor multiplexes capabilities; it does not mint authority. There is
//! no separate "surface authority" reinvented here — the share is the real
//! `GrantCapability` path and the gate is the real `is_attenuation` lattice.

use serde::Serialize;

use dregg_cell::{AuthRequired, CapabilityRef, CellId, CellLifecycle};
use dregg_turn::builder::ActionBuilder;
use dregg_turn::{Effect, TurnBuilder, TurnResult};

use crate::runtime::DreggRuntime;

/// The live identity of a surface — the T2 label-binding, read from the ledger.
///
/// Every field is a FUNCTION of the surface cell's real state in the live
/// ledger, NOT the page's self-description. The compositor draws the badge from
/// this; a window cannot masquerade as another cell because `owning_cell_id` and
/// `source_state_root` are the authenticated state-root binding, not chrome the
/// page rendered. (`WEB-FORWARD.md §2` T2 LABEL-BINDING.)
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct SurfaceIdentity {
    /// The cell that backs this surface (its ViewRef — unforgeable,
    /// content-addressed). Hex32.
    pub owning_cell_id: String,
    /// The cell's canonical lifecycle, read live: `live` / `sealed` / `migrated`
    /// / `destroyed` / `archived`. A sealed backing cell reads its lifecycle
    /// honestly (the compositor can dim a non-live pane).
    pub lifecycle: String,
    /// The cell's current canonical state commitment (`Cell::state_commitment()`,
    /// the BLAKE3-v* root) — the `sourceStateRoot` the remote-surface
    /// self-attestation checks against a light-client-attested root
    /// (`WEB-FORWARD.md §6`). Hex32.
    pub source_state_root: String,
    /// The cell's balance, read live (informational chrome — the genuine value,
    /// not a page claim). Signed (THE EPOCH §5 i64 value model).
    pub balance: i64,
    /// Whether the backing cell currently accepts effects (false for sealed /
    /// destroyed / migrated). Drawn live so a dimmed pane is honest.
    pub accepts_effects: bool,
}

/// The outcome of a surface op that gates on the cap lattice / the real executor.
///
/// Mirrors the `Resolution` / `ResolveError` split of `surface.rs`, flattened for
/// JS. `ok` is the headline; on a refusal `reason` carries the executor's own
/// reason string (e.g. `DelegationDenied`) so the `⚠ over-share` banner can
/// TEACH what was violated.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct SurfaceOutcome {
    /// Did the op succeed (cap covered the request / the grant committed)?
    pub ok: bool,
    /// A short reason. On success: what the backing did. On refusal: the
    /// executor's / cap-check's own reason (the teaching string).
    pub reason: String,
    /// The n-parametrized bound: is revocation immediate (n=1, the local tab)?
    /// Always true in the tab — surfaced so the demo can show the n=1 collapse.
    pub revocation_immediate: bool,
    /// Is the commit synchronous (n=1)? Always true in the tab.
    pub commit_synchronous: bool,
}

impl SurfaceOutcome {
    fn committed(reason: impl Into<String>) -> Self {
        SurfaceOutcome {
            ok: true,
            reason: reason.into(),
            revocation_immediate: true,
            commit_synchronous: true,
        }
    }
    fn refused(reason: impl Into<String>) -> Self {
        SurfaceOutcome {
            ok: false,
            reason: reason.into(),
            revocation_immediate: true,
            commit_synchronous: true,
        }
    }
}

/// Map an [`AuthRequired`] name from a JS string. The web surface speaks the
/// REAL dregg rights lattice (`WEB-FORWARD.md`: `Rights = AuthRequired`), not a
/// parallel "read/write" enum — so the over-share refusal is the genuine
/// `granted ⊆ held` direction. `none` is the widest (a fully-authorized
/// surface); `signature` models a read-only mirror (narrower); `impossible` is
/// the locked floor.
fn parse_rights(s: &str) -> Result<AuthRequired, String> {
    match s.to_ascii_lowercase().as_str() {
        "none" => Ok(AuthRequired::None),
        "signature" | "sig" | "read-only" | "readonly" | "mirror" => Ok(AuthRequired::Signature),
        "proof" => Ok(AuthRequired::Proof),
        "either" | "writable" | "write" => Ok(AuthRequired::Either),
        "impossible" | "locked" => Ok(AuthRequired::Impossible),
        other => Err(format!(
            "unknown surface rights '{other}' (use one of: none, signature/read-only, \
             proof, either/writable, impossible)"
        )),
    }
}

fn lifecycle_label(l: &CellLifecycle) -> &'static str {
    match l {
        CellLifecycle::Live => "live",
        CellLifecycle::Sealed { .. } => "sealed",
        CellLifecycle::Migrated { .. } => "migrated",
        CellLifecycle::Destroyed { .. } => "destroyed",
        CellLifecycle::Archived { .. } => "archived",
    }
}

fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for b in bytes {
        out.push(char::from_digit((b >> 4) as u32, 16).unwrap());
        out.push(char::from_digit((b & 0x0f) as u32, 16).unwrap());
    }
    out
}

impl DreggRuntime {
    /// **OPEN-SURFACE** — open the `owner` agent's OWN cell as a surface (a
    /// window) and return its live identity (the T2 badge source).
    ///
    /// In the firmament model a surface IS a cell; an agent's cell is already a
    /// real cell in the live ledger, so "opening it as a surface" means: confirm
    /// the cell exists, ensure the owner holds an ORIGINAL self-cap over it at
    /// `rights` (the Viewport the compositor renders), and read off the live
    /// identity. This is the powerbox handing the owner a window handle, the same
    /// `install`/`create_surface` shape as `surface.rs` — over the EXISTING
    /// ledger, not a parallel one.
    ///
    /// Returns the [`SurfaceIdentity`] (owning cell id / lifecycle / state root /
    /// balance) drawn from the live cell — so the JS compositor draws the badge
    /// from the ledger, never the page.
    pub fn open_surface(
        &mut self,
        owner_agent_idx: usize,
        rights: &str,
    ) -> Result<SurfaceIdentity, String> {
        let rights = parse_rights(rights)?;
        let owner_cell = self
            .agents
            .get(owner_agent_idx)
            .ok_or_else(|| format!("no agent at index {owner_agent_idx}"))?
            .cell_id;

        // The surface cell must exist in the live ledger.
        if self.ledger.get(&owner_cell).is_none() {
            return Err(format!(
                "surface cell {} not in ledger (agent not materialized?)",
                hex32(&owner_cell.0)
            ));
        }

        // Ensure the owner holds an ORIGINAL surface cap over its own cell at
        // exactly `rights` — the Viewport. The compositor multiplexes caps; it
        // does not invent authority, so this is the same original-grant shape
        // every firmament backing uses. (Replace any pre-existing self-cap so
        // re-opening at a different width is deterministic.)
        let cell = self
            .ledger
            .get_mut(&owner_cell)
            .ok_or_else(|| "surface cell vanished".to_string())?;
        if let Some(slot) = cell.capabilities.lookup_by_target(&owner_cell).map(|c| c.slot) {
            cell.capabilities.revoke(slot);
        }
        cell.capabilities.grant(owner_cell, rights);

        self.surface_identity_for(&owner_cell)
    }

    /// **PRESENT** — does `holder` hold draw authority over the `surface` cell?
    ///
    /// A present resolves the surface cap against real cell-state requiring the
    /// `required` authority (`required ⊆ held`, the REAL
    /// [`dregg_cell::is_attenuation`]). An app holding only a read-only mirror is
    /// refused exactly as the kernel refuses a write on a read-only frame — the
    /// refusal falls out of the real attenuation direction with no special-casing.
    /// At n=1 (the local tab) a present is synchronous (the pixel lands at once).
    ///
    /// `holder_agent_idx` is the presenting agent; `surface_owner_agent_idx`
    /// names the surface (its backing cell). For the owner presenting into its
    /// own window the two are equal.
    pub fn present_surface(
        &self,
        holder_agent_idx: usize,
        surface_owner_agent_idx: usize,
        required: &str,
    ) -> Result<SurfaceOutcome, String> {
        let required = parse_rights(required)?;
        let holder_cell = self
            .agents
            .get(holder_agent_idx)
            .ok_or_else(|| format!("no holder agent at index {holder_agent_idx}"))?
            .cell_id;
        let surface_cell = self
            .agents
            .get(surface_owner_agent_idx)
            .ok_or_else(|| format!("no surface-owner agent at index {surface_owner_agent_idx}"))?
            .cell_id;

        let cell = match self.ledger.get(&holder_cell) {
            Some(c) => c,
            None => return Ok(SurfaceOutcome::refused("holder cell not in ledger")),
        };
        let held = match cell.capabilities.lookup_by_target(&surface_cell) {
            Some(h) => h,
            None => {
                return Ok(SurfaceOutcome::refused(
                    "holder has no surface cap over this window (revoked or never granted) \
                     — the glass is dark",
                ));
            }
        };
        // `required ⊆ held`: the read-only-mirror refusal IS the real
        // `is_attenuation` direction.
        if dregg_cell::is_attenuation(&held.permissions, &required) {
            Ok(SurfaceOutcome::committed(format!(
                "present authorized: holder draw-cap {:?} covers required {:?}",
                held.permissions, required
            )))
        } else {
            Ok(SurfaceOutcome::refused(format!(
                "present refused: required {:?} exceeds held {:?} over surface \
                 (a read-only mirror cannot draw)",
                required, held.permissions
            )))
        }
    }

    /// **SHARE-SURFACE** — hand a window from `from` to `to` as a GENUINE
    /// `Effect::GrantCapability` turn through the real executor.
    ///
    /// `from` issues `GrantCapability(surface, narrower)` to `to` (e.g. sharing a
    /// clipped read-only view of a window with another agent). The REAL executor
    /// enforces `granted ⊆ held`: it commits iff the surface grant is attenuating,
    /// and rejects with `DelegationDenied` otherwise. A WIDENING surface share —
    /// handing out more authority over the glass than you hold — is refused by the
    /// executor, byte-for-byte the deployed semantics, and the `⚠ over-share`
    /// banner fires at the pixel layer.
    ///
    /// `surface_owner_agent_idx` names the surface (its backing cell). Returns the
    /// [`SurfaceOutcome`]; on refusal `reason` carries the executor's reason (the
    /// teaching string).
    pub fn share_surface(
        &mut self,
        from_agent_idx: usize,
        to_agent_idx: usize,
        surface_owner_agent_idx: usize,
        narrower: &str,
    ) -> Result<SurfaceOutcome, String> {
        let narrower = parse_rights(narrower)?;
        let from_cell = self
            .agents
            .get(from_agent_idx)
            .ok_or_else(|| format!("no granter agent at index {from_agent_idx}"))?
            .cell_id;
        let to_cell = self
            .agents
            .get(to_agent_idx)
            .ok_or_else(|| format!("no recipient agent at index {to_agent_idx}"))?
            .cell_id;
        let surface_cell = self
            .agents
            .get(surface_owner_agent_idx)
            .ok_or_else(|| format!("no surface-owner agent at index {surface_owner_agent_idx}"))?
            .cell_id;

        let nonce = self
            .ledger
            .get(&from_cell)
            .map(|c| c.state.nonce())
            .ok_or_else(|| "granter cell not in ledger".to_string())?;

        // The grant turn: `from` grants `to` a (narrowed) cap over the surface
        // cell. `slot` is rewritten by the executor on grant; the executor's
        // GrantCapability arm enforces `granted ⊆ held` against `from`'s own cap.
        let cap = CapabilityRef {
            target: surface_cell,
            slot: 0,
            permissions: narrower.clone(),
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        let action = ActionBuilder::new_unchecked_for_tests(from_cell, "share-surface", from_cell)
            .effect(Effect::GrantCapability {
                from: from_cell,
                to: to_cell,
                cap,
            })
            .build();
        // The DreggRuntime executor charges real computrons (it runs on
        // `ComputronCosts::default_costs()`); a GrantCapability costs `effect_base`
        // (~100). The fee IS the per-turn computron budget, so it must cover the
        // grant — a 0 fee yields a 0 budget and the executor refuses with "budget
        // exceeded" before the attenuation check ever fires. SURFACE_SHARE_FEE
        // gives comfortable headroom (the granter pays it from its own balance on
        // a COMMITTED grant; a refused widening share fails in `apply` before
        // finalize, so the recipient/granter is not charged for a denied share).
        const SURFACE_SHARE_FEE: u64 = 2000;
        let mut builder = TurnBuilder::new(from_cell, nonce);
        builder.set_fee(SURFACE_SHARE_FEE);
        builder.add_action(action);
        let mut turn = builder.build();
        if turn.previous_receipt_hash.is_none() {
            if let Some(prev) = self.executor.get_last_receipt_hash(&from_cell) {
                turn.previous_receipt_hash = Some(prev);
            }
        }
        // Sign with the granter's real cipherclerk — the same canonical signing
        // path every wasm turn uses (no hand-rolled crypto).
        let federation_id = self.executor.local_federation_id;
        let cclerk = &self.agents[from_agent_idx].cclerk;
        crate::runtime::sign_call_forest(&mut turn, cclerk, &federation_id);

        match self.executor.execute(&turn, &mut self.ledger) {
            TurnResult::Committed { .. } => Ok(SurfaceOutcome::committed(format!(
                "surface share committed: {:?} cap over window granted to recipient \
                 (attenuating — granted ⊆ held)",
                narrower
            ))),
            TurnResult::Rejected { reason, .. } => {
                // Carry the executor's GENUINE reason. A DelegationDenied is the
                // no-amplification tooth (the ⚠ over-share teaching moment); any
                // other refusal (e.g. insufficient fee balance) is reported as
                // itself — we do NOT launder every refusal as "no-amplification".
                let r = format!("{reason}");
                let rl = r.to_lowercase();
                let is_non_amp = rl.contains("delegation denied") || rl.contains("attenuat");
                let msg = if is_non_amp {
                    format!(
                        "executor refused surface share: {r} — a WIDENING share over the glass \
                         is no-amplification denied (granted ⊄ held)"
                    )
                } else {
                    format!("executor refused surface share: {r}")
                };
                Ok(SurfaceOutcome::refused(msg))
            }
            other => Ok(SurfaceOutcome::refused(format!(
                "surface share did not commit: {other:?}"
            ))),
        }
    }

    /// **REVOKE-SURFACE** — drop `holder`'s cap over the `surface`; the glass goes
    /// dark. At n=1 (the local tab) this is SYNCHRONOUS — the surface cap is dead
    /// the instant it returns, and a subsequent [`Self::present_surface`] finds
    /// nothing held (the window cannot paint even one more frame). Returns `true`
    /// iff a live surface cap was removed.
    pub fn revoke_surface(
        &mut self,
        holder_agent_idx: usize,
        surface_owner_agent_idx: usize,
    ) -> Result<bool, String> {
        let holder_cell = self
            .agents
            .get(holder_agent_idx)
            .ok_or_else(|| format!("no holder agent at index {holder_agent_idx}"))?
            .cell_id;
        let surface_cell = self
            .agents
            .get(surface_owner_agent_idx)
            .ok_or_else(|| format!("no surface-owner agent at index {surface_owner_agent_idx}"))?
            .cell_id;
        let cell = match self.ledger.get_mut(&holder_cell) {
            Some(c) => c,
            None => return Ok(false),
        };
        match cell.capabilities.lookup_by_target(&surface_cell).map(|c| c.slot) {
            Some(slot) => Ok(cell.capabilities.revoke(slot)),
            None => Ok(false),
        }
    }

    /// **SURFACE-IDENTITY** — the anti-spoof T2 badge for the surface backed by
    /// `surface_owner_agent_idx`'s cell, read FROM THE LIVE LEDGER.
    ///
    /// `(owningCellId, lifecycle, sourceStateRoot)` are each a function of the
    /// cell's real state, never the page's self-description. This is the badge the
    /// compositor draws; a window cannot masquerade as another cell because these
    /// are the authenticated bindings, not chrome.
    pub fn surface_identity(
        &self,
        surface_owner_agent_idx: usize,
    ) -> Result<SurfaceIdentity, String> {
        let surface_cell = self
            .agents
            .get(surface_owner_agent_idx)
            .ok_or_else(|| format!("no surface-owner agent at index {surface_owner_agent_idx}"))?
            .cell_id;
        self.surface_identity_for(&surface_cell)
    }

    /// Does `holder` hold a surface cap over `surface`? (Used by the compositor to
    /// decide whether to paint a recipient's pane — the surface analog of
    /// `SurfaceBacking::holds_cap`.)
    pub fn surface_holds_cap(
        &self,
        holder_agent_idx: usize,
        surface_owner_agent_idx: usize,
    ) -> Result<bool, String> {
        let holder_cell = self
            .agents
            .get(holder_agent_idx)
            .ok_or_else(|| format!("no holder agent at index {holder_agent_idx}"))?
            .cell_id;
        let surface_cell = self
            .agents
            .get(surface_owner_agent_idx)
            .ok_or_else(|| format!("no surface-owner agent at index {surface_owner_agent_idx}"))?
            .cell_id;
        Ok(self
            .ledger
            .get(&holder_cell)
            .map(|c| c.capabilities.lookup_by_target(&surface_cell).is_some())
            .unwrap_or(false))
    }

    /// The rights a holder holds over a surface, as a string, if any. (The
    /// compositor uses this to render the pane's CAN/CAN'T chrome.)
    pub fn surface_rights_held(
        &self,
        holder_agent_idx: usize,
        surface_owner_agent_idx: usize,
    ) -> Result<Option<String>, String> {
        let holder_cell = self
            .agents
            .get(holder_agent_idx)
            .ok_or_else(|| format!("no holder agent at index {holder_agent_idx}"))?
            .cell_id;
        let surface_cell = self
            .agents
            .get(surface_owner_agent_idx)
            .ok_or_else(|| format!("no surface-owner agent at index {surface_owner_agent_idx}"))?
            .cell_id;
        Ok(self.ledger.get(&holder_cell).and_then(|c| {
            c.capabilities
                .lookup_by_target(&surface_cell)
                .map(|r| format!("{:?}", r.permissions))
        }))
    }

    /// Internal: build a [`SurfaceIdentity`] from a cell id by reading the live
    /// ledger. The single source of truth for the T2 badge.
    fn surface_identity_for(&self, surface_cell: &CellId) -> Result<SurfaceIdentity, String> {
        let cell = self
            .ledger
            .get(surface_cell)
            .ok_or_else(|| format!("surface cell {} not in ledger", hex32(&surface_cell.0)))?;
        Ok(SurfaceIdentity {
            owning_cell_id: hex32(&cell.id().0),
            lifecycle: lifecycle_label(&cell.lifecycle).to_string(),
            source_state_root: hex32(&cell.state_commitment()),
            balance: cell.state.balance(),
            accepts_effects: cell.lifecycle.accepts_effects(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rt_with_two_agents() -> DreggRuntime {
        let mut rt = DreggRuntime::new();
        // idx 0 = genesis (alice), idx 1 = bob, minted from genesis. Alice must
        // hold enough to cover the GENESIS_MINT_FEE (2000) debited when bob's
        // cell is minted via Effect::CreateCellFromFactory, plus her own balance
        // and the share fee. Bob is funded too so that when HE attempts an
        // onward share, the refusal is the GENUINE attenuation refusal
        // (DelegationDenied) — not a fee-balance failure that would precede it
        // (the executor checks fee coverage before applying effects). This keeps
        // the no-amplification teeth honest rather than passing on any refusal.
        rt.create_agent("alice", 20_000);
        rt.create_agent("bob", 5_000);
        rt
    }

    #[test]
    fn open_surface_returns_live_identity_from_ledger() {
        let mut rt = rt_with_two_agents();
        let id = rt.open_surface(0, "either").expect("alice opens her cell as a surface");
        // The badge is drawn from the live cell, not a page claim. Alice started
        // at 20_000, paid the 2_000 mint fee for bob AND transferred 5_000 to
        // fund bob → 13_000 live.
        assert_eq!(id.lifecycle, "live");
        assert!(id.accepts_effects);
        assert_eq!(id.balance, 13_000);
        assert_eq!(id.owning_cell_id.len(), 64);
        assert_eq!(id.source_state_root.len(), 64);
        // The owner now holds a draw cap, so a present at the held width succeeds.
        let pres = rt.present_surface(0, 0, "either").unwrap();
        assert!(pres.ok, "owner can present into its own window");
    }

    #[test]
    fn read_only_mirror_cannot_present_wider() {
        let mut rt = rt_with_two_agents();
        // Open alice's window read-only (a mirror).
        rt.open_surface(0, "signature").expect("open read-only");
        // Presenting at the held Signature width succeeds...
        assert!(rt.present_surface(0, 0, "signature").unwrap().ok);
        // ...but presenting at the WIDER None authority exceeds the held mirror
        // — refused by the real is_attenuation direction.
        let wide = rt.present_surface(0, 0, "none").unwrap();
        assert!(!wide.ok, "a read-only mirror must NOT be able to draw wider");
        assert!(wide.reason.contains("exceeds held"));
    }

    #[test]
    fn share_read_only_commits_then_onward_widening_refuses() {
        let mut rt = rt_with_two_agents();
        // Alice opens her cell as a WRITABLE surface (None = widest).
        rt.open_surface(0, "none").expect("alice opens writable");
        // Alice shares a READ-ONLY (Signature) view with Bob — attenuating,
        // commits through the real executor.
        let share = rt.share_surface(0, 1, 0, "signature").unwrap();
        assert!(share.ok, "an attenuating read-only share must commit: {}", share.reason);
        assert!(rt.surface_holds_cap(1, 0).unwrap(), "bob holds the shared surface cap");
        assert_eq!(rt.surface_rights_held(1, 0).unwrap().as_deref(), Some("Signature"));

        // Bob can present read-only (he holds Signature)...
        assert!(rt.present_surface(1, 0, "signature").unwrap().ok);
        // ...but Bob tries to share it ONWARD as WRITABLE (None ⊋ Signature) —
        // the executor REJECTS with DelegationDenied (the ⚠ over-share moment).
        // Bob is funded (see the fixture), so this is the GENUINE attenuation
        // refusal, not a fee-balance failure — the message carries the real
        // executor reason, so we assert on the no-amplification tooth itself.
        let onward = rt.share_surface(1, 0, 0, "none").unwrap();
        assert!(!onward.ok, "a widening onward share must be REFUSED");
        assert!(
            onward.reason.contains("no-amplification denied")
                && onward.reason.to_lowercase().contains("delegation denied"),
            "the refusal must be the GENUINE DelegationDenied (no-amplification), \
             not a laundered/other reason: {}",
            onward.reason
        );
    }

    #[test]
    fn revoke_darkens_the_glass_synchronously() {
        let mut rt = rt_with_two_agents();
        rt.open_surface(0, "none").unwrap();
        rt.share_surface(0, 1, 0, "signature").unwrap();
        assert!(rt.surface_holds_cap(1, 0).unwrap());
        // Before revoke: bob can present.
        assert!(rt.present_surface(1, 0, "signature").unwrap().ok);
        // Revoke bob's pane — synchronous at n=1.
        assert!(rt.revoke_surface(1, 0).unwrap(), "revoke removes the live cap");
        assert!(!rt.surface_holds_cap(1, 0).unwrap(), "cap dead the instant revoke returns");
        // After revoke: present is refused — the glass is dark this frame.
        let after = rt.present_surface(1, 0, "signature").unwrap();
        assert!(!after.ok, "a revoked window cannot paint even one more frame at n=1");
        // Revoking an already-dead cap is a no-op false.
        assert!(!rt.revoke_surface(1, 0).unwrap());
    }

    #[test]
    fn surface_identity_is_drawn_from_the_live_ledger() {
        let mut rt = rt_with_two_agents();
        // No open needed — surface_identity reads the cell directly.
        let id = rt.surface_identity(1).expect("bob's cell identity");
        assert_eq!(id.lifecycle, "live");
        assert_eq!(id.owning_cell_id.len(), 64);
        // The state root is the cell's real commitment — distinct cells differ.
        let alice_id = rt.surface_identity(0).unwrap();
        assert_ne!(
            id.source_state_root, alice_id.source_state_root,
            "distinct cells have distinct source state roots (the T2 binding)"
        );
        assert_ne!(id.owning_cell_id, alice_id.owning_cell_id);
    }
}
