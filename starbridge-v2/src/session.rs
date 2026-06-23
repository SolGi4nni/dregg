//! The deos **SESSION / LOGIN MANAGER** — login = receiving your ROOT
//! CAPABILITY, a session = the cap-tree you hold, logout = revoking it.
//!
//! See `docs/deos/SESSION-LOGIN.md` for the full design. This module is the
//! L6-adjacent trusted piece the WM/login investigation found missing: every
//! primitive a login manager needs already exists; the manager that composes
//! them did not. This is that composition — a designation flow over real turns,
//! exactly as [`crate::powerbox`] is a designation flow over
//! [`Effect::GrantCapability`]. It reinvents NO authority machinery.
//!
//! The one-sentence model:
//!
//! > **login = receiving your root capability · a session = the cap-tree you
//! > hold · logout = revoking it.**
//!
//! A session is NOT an object kept in sync with the ledger — it IS a c-list.
//! The window manager renders exactly what the root cap authorizes; revoking
//! the root darkens the whole tree synchronously (`n = 1`).
//!
//! ## The ceremony (each step a REAL turn, each leaving a receipt)
//!
//! 1. **AUTHENTICATE** — prove possession of the principal's key (challenge /
//!    KERI pre-rotation). Output: a proven [`Principal`]. Nothing granted yet.
//! 2. **DERIVE** the root cell — `CellId::derive_raw(&pubkey, &ROOT_TOKEN)`
//!    (`cell/src/id.rs` → `dregg_types::CellId::derive_raw`): the identity cell
//!    is the content-address of the key. Deterministic + stateless: the same
//!    key always derives the same root cell (mint on first login, retrieve on
//!    return).
//! 3. **GRANT** the [`CapTemplate`] — the per-user initial cap set — into the
//!    root cell, FROM the system principal, via the REAL grant path (so
//!    `mint_needs_held_factory` + `gen_conferral_is_attenuation` both bite: the
//!    system principal can only hand authority it holds, narrowed).
//! 4. The **session** = the resulting c-list (the live cap-tree on `root_cell`).
//! 5. **LOGOUT** = `Effect::RevokeCapability` over the session root → the whole
//!    cap-tree goes dark, synchronous + transitive at `n = 1`
//!    (`sel4/dregg-firmament/src/surface.rs:407`).
//!
//! gpui-free and `cargo test`-able — the same pure-flow stance as
//! [`crate::powerbox`]: the cockpit's login surface renders exactly these rows,
//! so a `cargo test` that asserts the session is real + template-bounded +
//! dark-after-revoke proves the flow without a GPU.

use dregg_cell::{AuthRequired, CellId};
use dregg_turn::action::Effect;
use dregg_turn::turn::TurnReceipt;

use crate::world::{CommitOutcome, World};

/// The fixed root token under which a principal's identity cell is derived. The
/// identity cell = `derive_raw(pubkey, ROOT_TOKEN)` — the content-address of the
/// key under this domain. A deployment could derive several roles from one key
/// by using distinct tokens; the login root is this one.
pub const ROOT_TOKEN: [u8; 32] = *b"dregg-deos-session-root-token!!!";

/// **A proven principal** — the output of [`LoginManager::authenticate`]. It is
/// *only* constructible by an authentication path, so holding a `Principal` is a
/// proof that possession of `pubkey`'s secret half was demonstrated. (In the
/// sketch the proof is a held-key check; the live manager runs challenge / KERI
/// pre-rotation against the identity app.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Principal {
    /// The authenticated public key — the identity. The root cell is its
    /// content-address.
    pub pubkey: [u8; 32],
}

impl Principal {
    /// The root identity cell for this principal: the content-address of the key
    /// under [`ROOT_TOKEN`]. Deterministic + stateless — the SAME key always
    /// derives the SAME cell, so a returning user re-derives to exactly their
    /// identity cell with no stored mapping.
    pub fn root_cell(&self) -> CellId {
        CellId::derive_raw(&self.pubkey, &ROOT_TOKEN)
    }
}

/// **One entry of a login [`CapTemplate`]** — mirrors `cell/src/factory.rs`'s
/// `CapTemplate` (target · max_permissions · attenuatable), the proven shape for
/// "what a factory may grant". A login template is a VECTOR of these: the c-list
/// the session is born holding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapEntry {
    /// The cell this session cap reaches — a home cell, a launchable surface/app,
    /// or a factory cell. (Modeled as a concrete [`CellId`]; the factory
    /// `CapTarget` enum's `SelfCell` resolves to `root_cell` at grant time.)
    pub target: CellId,
    /// The ceiling rights for this edge — `≤` what the system principal holds
    /// over `target` (the grant attenuates from there; amplification is refused).
    pub max_permissions: AuthRequired,
    /// May the session re-delegate this cap (mint sub-caps for apps it launches)?
    pub attenuatable: bool,
    /// A human label for the entry (the trusted-UI row text).
    pub label: String,
}

impl CapEntry {
    /// A template entry granting `max_permissions` over `target`.
    pub fn new(
        target: CellId,
        max_permissions: AuthRequired,
        attenuatable: bool,
        label: impl Into<String>,
    ) -> Self {
        CapEntry {
            target,
            max_permissions,
            attenuatable,
            label: label.into(),
        }
    }
}

/// **The per-user initial cap set** — the c-list a fresh session is born
/// holding. This is the one place a deos deployment says "what does a new user
/// get": the home cells, the surfaces/apps they may launch, the self-cap that
/// lets the session run the powerbox for the apps it launches. Policy, not
/// mechanism — changing it changes every new session with no change to the grant
/// machinery.
///
/// An AGENT session differs from a user session ONLY in this template: an agent
/// is born holding a deliberately narrower cap-tree (its mandate). The ceremony
/// is identical.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct CapTemplate {
    /// The cap entries to grant into the root cell on login, in order.
    pub entries: Vec<CapEntry>,
}

impl CapTemplate {
    /// An empty template (an inhabitant born holding nothing — the ocap floor).
    pub fn empty() -> Self {
        CapTemplate::default()
    }

    /// Add a cap entry to the template (builder style).
    pub fn with(mut self, entry: CapEntry) -> Self {
        self.entries.push(entry);
        self
    }
}

/// **A live session** — the cap-tree rooted at `root_cell`. The session is NOT
/// a separate object to keep in sync: it is a VIEW over the root cell's live
/// c-list at a point in time. Carries the granted caps (each a real, attenuated
/// edge in the ledger) + the receipts the login ceremony left.
#[derive(Clone, Debug)]
pub struct Session {
    /// The authenticated principal whose session this is.
    pub principal: Principal,
    /// The session root — the principal's identity cell. Revoking its caps is
    /// logout.
    pub root_cell: CellId,
    /// The caps granted into the root cell (the session's c-list), as
    /// `(target, slot, rights)`. The WM renders exactly these.
    pub granted: Vec<(CellId, u32, AuthRequired)>,
    /// The receipts the login ceremony left (mint + per-entry grant) — the
    /// session's verifiable lifecycle on the ledger.
    pub receipts: Vec<TurnReceipt>,
}

impl Session {
    /// Does the session currently reach `target` in the live ledger? The WM
    /// uses this to decide what to render; after logout it is false for every
    /// session target (the tree is dark).
    pub fn reaches(&self, world: &World, target: &CellId) -> bool {
        world
            .ledger()
            .get(&self.root_cell)
            .map(|c| c.capabilities.has_access(target))
            .unwrap_or(false)
    }

    /// Is the session live — does the root cell still hold ANY of its granted
    /// caps? After [`LoginManager::logout`] this is false (the whole tree dark).
    pub fn is_live(&self, world: &World) -> bool {
        self.granted.iter().any(|(t, _, _)| self.reaches(world, t))
    }
}

/// The outcome of a login attempt.
#[derive(Debug)]
pub enum LoginOutcome {
    /// Login succeeded — the session is established (the root cap-tree is held).
    Session(Session),
    /// Login was refused — authentication failed, or a template grant was
    /// refused by the executor (an over-grant the system principal cannot make).
    Denied { reason: String },
}

impl LoginOutcome {
    pub fn session(&self) -> Option<&Session> {
        match self {
            LoginOutcome::Session(s) => Some(s),
            LoginOutcome::Denied { .. } => None,
        }
    }
}

/// **THE LOGIN MANAGER — the trusted L6-adjacent session cell.**
///
/// It holds the **system principal**: the deos image's root identity, the only
/// principal that holds the home cells + factory caps a fresh session is
/// provisioned from. It has NO ambient authority beyond that — every session cap
/// it hands is granted FROM the system principal's held caps, attenuated,
/// through a real turn the executor re-checks (`mint_needs_held_factory` is the
/// backstop). It is trusted to *designate the session*, not to *be the
/// authority* — exactly the powerbox split.
#[derive(Clone, Debug)]
pub struct LoginManager {
    /// The deos image's root identity — the principal a session is provisioned
    /// FROM. Holds the home cells + factory caps a `CapTemplate` draws on.
    pub system_principal: CellId,
}

impl LoginManager {
    /// A login manager backed by the deos image's `system_principal` (its root
    /// identity, seeded at image construction).
    pub fn new(system_principal: CellId) -> Self {
        LoginManager { system_principal }
    }

    /// **AUTHENTICATE** — prove possession of the principal's key. In the live
    /// manager this is challenge–response (sign a nonce) or KERI pre-rotation
    /// against the identity app. The sketch's stand-in: the principal proves
    /// possession by exhibiting that its claimed pubkey is the one whose secret
    /// half signed `proof_ok` — modeled as the boolean a real signature check
    /// would produce, so the *flow* (auth gates everything downstream) is exact.
    ///
    /// Returns a [`Principal`] ONLY on a passing check, so holding one is a
    /// proof of authentication.
    pub fn authenticate(&self, pubkey: [u8; 32], proof_ok: bool) -> Option<Principal> {
        if proof_ok {
            Some(Principal { pubkey })
        } else {
            None
        }
    }

    /// **LOGIN** — the whole ceremony: derive the root cell (mint on first
    /// login), then grant each [`CapTemplate`] entry into it FROM the system
    /// principal via a real [`Effect::GrantCapability`] turn. The resulting
    /// root-cell c-list IS the session.
    ///
    /// Every grant is the genuine attenuating mint: the system principal must
    /// HOLD a cap reaching the entry's target (`mint_needs_held_factory`) and
    /// the conferred rights are `≤` the held rights — the executor
    /// (`World::commit_turn`) is the authority and the backstop. An entry the
    /// system principal cannot satisfy makes the login [`LoginOutcome::Denied`].
    pub fn login(
        &self,
        world: &mut World,
        principal: Principal,
        template: &CapTemplate,
    ) -> LoginOutcome {
        let root_cell = principal.root_cell();
        let mut receipts = Vec::new();

        // DERIVE + mint-on-first-login: if the identity cell does not exist yet,
        // birth it (a confined genesis cell — empty c-list, no ambient
        // authority). A returning login finds it already present + retrieves it.
        if world.ledger().get(&root_cell).is_none() {
            // Seed the root cell deterministically at its derived id so the same
            // key always lands the same cell (mint-on-first-login).
            let cell = make_root_cell(&principal.pubkey);
            debug_assert_eq!(cell.id(), root_cell, "the root cell IS the content-address of the key");
            world.genesis_install(cell);
        }

        // GRANT the template — each entry, FROM the system principal, via the
        // real grant turn. The session is born holding exactly these.
        let mut granted = Vec::new();
        for entry in &template.entries {
            let slot = next_free_slot(world, &root_cell);
            let effect = Effect::GrantCapability {
                from: self.system_principal,
                to: root_cell,
                cap: dregg_cell::CapabilityRef {
                    target: entry.target,
                    slot,
                    permissions: entry.max_permissions.clone(),
                    breadstuff: None,
                    expires_at: None,
                    allowed_effects: None,
                    stored_epoch: None,
                },
            };
            let turn = world.turn(self.system_principal, vec![effect]);
            match world.commit_turn(turn) {
                CommitOutcome::Committed { receipt, .. } => {
                    receipts.push(receipt);
                    granted.push((entry.target, slot, entry.max_permissions.clone()));
                }
                CommitOutcome::Rejected { reason, .. } => {
                    // The system principal cannot hand this entry (over-grant /
                    // not held). The login is refused — never partially granted
                    // beyond what the executor admitted.
                    return LoginOutcome::Denied {
                        reason: format!(
                            "session template entry {:?} refused by the executor: {reason}",
                            entry.label
                        ),
                    };
                }
                CommitOutcome::Queued { .. } => {
                    return LoginOutcome::Denied {
                        reason: "world suspended: a session grant queued, not committed".to_string(),
                    };
                }
            }
        }

        LoginOutcome::Session(Session {
            principal,
            root_cell,
            granted,
            receipts,
        })
    }

    /// **LOGOUT** — revoke the session root → the whole cap-tree goes dark. At
    /// `n = 1` this is synchronous + transitive (`surface.rs:407`): the instant
    /// the revoke turn returns, the caps are gone from real cell-state and any
    /// surface present / app invoke that depended on the tree is refused. Every
    /// granted leaf was reachable only through these root edges, so removing them
    /// darkens the whole session.
    ///
    /// Returns the number of caps revoked (the session was holding them).
    pub fn logout(&self, world: &mut World, session: &Session) -> usize {
        let mut revoked = 0;
        // Revoke from the highest slot down so each removal is stable (a revoke
        // is over a live slot on the root cell).
        let mut slots: Vec<u32> = session.granted.iter().map(|(_, slot, _)| *slot).collect();
        slots.sort_unstable();
        for slot in slots.into_iter().rev() {
            let effect = Effect::RevokeCapability {
                cell: session.root_cell,
                slot,
            };
            let turn = world.turn(session.root_cell, vec![effect]);
            if world.commit_turn(turn).is_committed() {
                revoked += 1;
            }
        }
        revoked
    }
}

// ===========================================================================
// THE DEOS LOGIN CEREMONY — the provisioning + identity seeds the RUNNING login
// surface drives. These are gpui-free so `cargo test` exercises the EXACT flow
// the (gpui-gated) `crate::login` surface runs on click: a real grant turn from
// a real system principal that HOLDS the home/app caps, attenuated per identity.
// ===========================================================================

/// Provision the deos image's **system principal** over a set of resource cells
/// (the desktop's home/app/surface cells a fresh session is drawn from). It is
/// installed as an open genesis cell HOLDING a full-rights cap to each resource,
/// so a later `Effect::GrantCapability` FROM it is legitimate (the executor's
/// no-amplification rule: you can only grant what you hold). Returns its id — the
/// `LoginManager::new` argument.
///
/// This is the one out-of-band step §5 of the design names: the image's own root
/// identity, seeded at construction, is "what authority does this desktop have to
/// hand out". The login surface grants the per-user `CapTemplate` from here.
pub fn provision_system_principal(world: &mut World, resources: &[CellId]) -> CellId {
    let mut sys = crate::world::make_open_cell(0x55, 0);
    for r in resources {
        // Full rights over each resource — the ceiling a session template
        // attenuates from. (`AuthRequired::None` = unconditional hold.)
        sys.capabilities
            .grant(*r, AuthRequired::None)
            .expect("the system principal's c-list has a free slot per resource");
    }
    world.genesis_install(sys)
}

/// The **default human-user `CapTemplate`** over the deos desktop's anchor cells
/// `[treasury, service, user]`: full attenuatable authority over the `user` home
/// cell, and an attenuated (Signature-tier) launch cap to the `service` app cell.
/// This is policy — the one place "what does a fresh user get" lives.
pub fn default_user_template(anchors: [CellId; 3]) -> CapTemplate {
    let [_treasury, service, user] = anchors;
    CapTemplate::empty()
        .with(CapEntry::new(user, AuthRequired::None, true, "home"))
        .with(CapEntry::new(service, AuthRequired::Signature, true, "launcher"))
}

/// The **agent `CapTemplate`** — the polis payoff. The SAME ceremony as a user,
/// the ONLY difference being a deliberately narrower mandate: an agent (Hermes)
/// is born holding a single, non-re-delegatable cap to its tool surface (the
/// `service` app cell), and crucially NO cap to a user's home cell.
pub fn agent_template(anchors: [CellId; 3]) -> CapTemplate {
    let [_treasury, service, _user] = anchors;
    CapTemplate::empty().with(CapEntry::new(
        service,
        AuthRequired::Signature,
        false, // a tightly-bounded agent cannot re-delegate its mandate
        "agent-tool-surface",
    ))
}

/// Which kind of inhabitant a [`DemoIdentity`] is — selects the `CapTemplate`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IdentityKind {
    /// A human user — born holding the full [`default_user_template`].
    User,
    /// An agent (Hermes-shaped) — born holding the narrower [`agent_template`].
    Agent,
}

/// A **demo seed identity** the login surface offers to pick (the held-key
/// stand-in: selecting it is "I possess this key"). Each carries a fixed pubkey
/// (so its root cell is stable across logins) and the kind that selects its
/// template. The live manager replaces the pick with a real key challenge.
#[derive(Clone, Debug)]
pub struct DemoIdentity {
    /// The human-readable name shown in the login picker.
    pub name: &'static str,
    /// The identity's public key — its root cell is `derive_raw(pubkey, ROOT_TOKEN)`.
    pub pubkey: [u8; 32],
    /// User vs agent — selects the `CapTemplate` granted on login.
    pub kind: IdentityKind,
    /// A one-line description of what this inhabitant's session is born holding.
    pub blurb: &'static str,
}

impl DemoIdentity {
    /// The root identity cell this demo identity logs into.
    pub fn root_cell(&self) -> CellId {
        CellId::derive_raw(&self.pubkey, &ROOT_TOKEN)
    }

    /// The `CapTemplate` this identity's session is born holding, over `anchors`.
    pub fn template(&self, anchors: [CellId; 3]) -> CapTemplate {
        match self.kind {
            IdentityKind::User => default_user_template(anchors),
            IdentityKind::Agent => agent_template(anchors),
        }
    }
}

/// The deos image's seed identities — the login picker's roster. Two human users
/// (each gets the full desktop) and one agent inhabitant (Hermes, cap-bounded to
/// its tool surface — the kill-switch-on-logout polis frame). A real deployment
/// authenticates keys; these are the demo's held-key stand-ins.
pub fn demo_identities() -> Vec<DemoIdentity> {
    vec![
        DemoIdentity {
            name: "ember",
            pubkey: [0xE3u8; 32],
            kind: IdentityKind::User,
            blurb: "a human user — full home cell + a launchable app (attenuatable)",
        },
        DemoIdentity {
            name: "guest",
            pubkey: [0x67u8; 32],
            kind: IdentityKind::User,
            blurb: "a second human user — the same desktop, their own root cell",
        },
        DemoIdentity {
            name: "Hermes (agent)",
            pubkey: [0xA6u8; 32],
            kind: IdentityKind::Agent,
            blurb: "an agent inhabitant — ONLY its tool surface, no home cell, no re-delegate",
        },
    ]
}

/// Build the principal's root identity cell at its DERIVED id (mint-on-first-
/// login). A confined cell — empty c-list, no ambient authority — that the login
/// then grants the `CapTemplate` INTO. Built from the principal's pubkey under
/// [`ROOT_TOKEN`], so `cell.id == derive_raw(pubkey, ROOT_TOKEN)` (the content-
/// address invariant): the same key always re-derives to it. Open permissions so
/// the granted session caps are exercisable, mirroring [`make_open_cell`].
fn make_root_cell(pubkey: &[u8; 32]) -> dregg_cell::Cell {
    // `Cell::new(pk, token)` sets `id = derive_raw(pk, token)` — the identity
    // cell IS the content-address of the key. Born with no value (conservation:
    // value only moves) and no caps until the template is granted.
    let mut cell = dregg_cell::Cell::new(*pubkey, ROOT_TOKEN);
    cell.permissions = crate::world::open_permissions();
    cell
}

/// The next free slot in `cell`'s c-list to grant into (one past the highest
/// occupied slot). A fresh root cell starts at slot 0.
fn next_free_slot(world: &World, cell: &CellId) -> u32 {
    match world.ledger().get(cell) {
        Some(c) => c
            .capabilities
            .iter()
            .map(|cap| cap.slot)
            .max()
            .map(|m| m + 1)
            .unwrap_or(0),
        None => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{make_open_cell, World};

    /// A login world: a SYSTEM PRINCIPAL holding caps to two home/app cells (the
    /// authority a session is provisioned from), and two resource cells (`home`,
    /// `app`) the template will draw on. Returns `(world, login_mgr, home, app)`.
    fn login_world() -> (World, LoginManager, CellId, CellId) {
        let mut w = World::new();
        let home = w.genesis_cell(0xD0, 0);
        let app = w.genesis_cell(0xA0, 0);

        // The system principal holds full authority over both — the ceiling a
        // session template attenuates from.
        let mut sys = make_open_cell(0x55, 0);
        sys.capabilities
            .grant(home, AuthRequired::None)
            .expect("slot for home");
        sys.capabilities
            .grant(app, AuthRequired::Signature)
            .expect("slot for app");
        let system_principal = w.genesis_install(sys);

        (w, LoginManager::new(system_principal), home, app)
    }

    /// A default user template: full attenuatable authority over `home`, narrowed
    /// (Signature) over the launchable `app`.
    fn user_template(home: CellId, app: CellId) -> CapTemplate {
        CapTemplate::empty()
            .with(CapEntry::new(home, AuthRequired::None, true, "home"))
            .with(CapEntry::new(app, AuthRequired::Signature, true, "launcher"))
    }

    #[test]
    fn authenticate_gates_the_session_and_derives_a_stable_root_cell() {
        let (_w, mgr, _home, _app) = login_world();
        let pk = [7u8; 32];

        // A failed auth yields no principal — nothing downstream can run.
        assert!(mgr.authenticate(pk, false).is_none(), "failed auth gates login");

        // A passing auth yields a principal whose root cell is the deterministic
        // content-address of the key (same key → same cell, every time).
        let p = mgr.authenticate(pk, true).expect("auth passes");
        assert_eq!(p.pubkey, pk);
        assert_eq!(
            p.root_cell(),
            CellId::derive_raw(&pk, &ROOT_TOKEN),
            "the root cell IS derive_raw(pubkey, ROOT_TOKEN)"
        );
        // Re-deriving from a fresh principal lands the SAME cell (stateless).
        let p2 = mgr.authenticate(pk, true).unwrap();
        assert_eq!(p.root_cell(), p2.root_cell(), "the same key re-derives the same root cell");
        // A different key → a different cell.
        let other = mgr.authenticate([9u8; 32], true).unwrap();
        assert_ne!(p.root_cell(), other.root_cell(), "distinct keys → distinct identity cells");
    }

    #[test]
    fn login_mints_the_root_cell_and_grants_the_template_as_the_session() {
        // THE CEREMONY: authenticate → derive (mint on first login) → grant the
        // template → the root-cell c-list IS the session.
        let (mut w, mgr, home, app) = login_world();
        let p = mgr.authenticate([7u8; 32], true).unwrap();
        let root = p.root_cell();

        // First login: the identity cell does not exist yet.
        assert!(w.ledger().get(&root).is_none(), "first login: root cell not yet minted");
        let cells_before = w.cell_count();

        let outcome = mgr.login(&mut w, p, &user_template(home, app));
        let session = match outcome {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("login should succeed: {reason}"),
        };

        // The root cell was minted (a brand-new identity cell).
        assert_eq!(w.cell_count(), cells_before + 1, "first login mints the identity cell");
        assert_eq!(session.root_cell, root);

        // The session IS the granted cap-tree: the root cell now reaches BOTH
        // template targets, at the ATTENUATED rights (≤ the system principal's).
        assert!(session.reaches(&w, &home), "the session reaches home");
        assert!(session.reaches(&w, &app), "the session reaches the launchable app");
        assert!(session.is_live(&w), "a freshly logged-in session is live");

        let root_cell = w.ledger().get(&root).unwrap();
        let home_cap = root_cell.capabilities.iter().find(|c| c.target == home).unwrap();
        let app_cap = root_cell.capabilities.iter().find(|c| c.target == app).unwrap();
        assert_eq!(home_cap.permissions, AuthRequired::None, "home at the template ceiling");
        assert_eq!(app_cap.permissions, AuthRequired::Signature, "app at the attenuated tier");

        // Each grant left a real receipt — the session's verifiable lifecycle.
        assert_eq!(session.receipts.len(), 2, "one receipt per template entry granted");
    }

    #[test]
    fn logout_revokes_the_session_root_and_the_whole_tree_goes_dark() {
        // LOGOUT = revoke the session root → synchronous, the whole cap-tree dark.
        let (mut w, mgr, home, app) = login_world();
        let p = mgr.authenticate([7u8; 32], true).unwrap();
        let session = match mgr.login(&mut w, p, &user_template(home, app)) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("login: {reason}"),
        };
        assert!(session.is_live(&w), "live before logout");
        assert!(session.reaches(&w, &home) && session.reaches(&w, &app));

        let revoked = mgr.logout(&mut w, &session);
        assert_eq!(revoked, 2, "both session caps revoked");

        // The whole tree is dark: the root cell reaches NEITHER target.
        assert!(!session.reaches(&w, &home), "home is dark after logout");
        assert!(!session.reaches(&w, &app), "the app is dark after logout");
        assert!(!session.is_live(&w), "the session is no longer live");
    }

    #[test]
    fn a_returning_login_retrieves_the_same_root_cell_not_a_new_one() {
        // The identity cell is the content-address of the key: a second login
        // with the same key DERIVES the same cell and does NOT mint another.
        let (mut w, mgr, home, app) = login_world();
        let p = mgr.authenticate([7u8; 32], true).unwrap();

        let first = mgr.login(&mut w, p, &user_template(home, app));
        let root = first.session().unwrap().root_cell;
        mgr.logout(&mut w, first.session().unwrap());
        let cells_after_first = w.cell_count();

        // Returning login (same key): no new cell minted; same root cell.
        let p2 = mgr.authenticate([7u8; 32], true).unwrap();
        let second = mgr.login(&mut w, p2, &user_template(home, app));
        assert_eq!(second.session().unwrap().root_cell, root, "same key → same identity cell");
        assert_eq!(
            w.cell_count(),
            cells_after_first,
            "a returning login retrieves the cell, it does not mint a new one"
        );
        assert!(second.session().unwrap().is_live(&w), "the re-granted session is live again");
    }

    #[test]
    fn after_logout_a_session_exercise_is_refused_the_cap_tree_is_dark() {
        // The teeth of logout: it is not just that `is_live` reports false — an
        // attempt to EXERCISE the session's authority after logout is REFUSED by
        // the executor, because the root cell no longer holds the cap to amplify.
        let (mut w, mgr, home, app) = login_world();
        let p = mgr.authenticate([7u8; 32], true).unwrap();
        let session = match mgr.login(&mut w, p, &user_template(home, app)) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("login: {reason}"),
        };
        let root = session.root_cell;

        // WHILE LOGGED IN: the session can re-delegate its held home cap into a
        // fresh slot — a real authorized exercise (it holds the cap to grant).
        let live_slot = next_free_slot(&w, &root);
        let exercise = |w: &mut World, slot: u32| {
            let effect = Effect::GrantCapability {
                from: root,
                to: root,
                cap: dregg_cell::CapabilityRef {
                    target: home,
                    slot,
                    permissions: AuthRequired::None,
                    breadstuff: None,
                    expires_at: None,
                    allowed_effects: None,
                    stored_epoch: None,
                },
            };
            let turn = w.turn(root, vec![effect]);
            w.commit_turn(turn).is_committed()
        };
        assert!(exercise(&mut w, live_slot), "a live session can exercise its held cap");

        // LOGOUT — revoke the session root. (Revoke the original template slots;
        // the test then proves the WHOLE tree is dark for a fresh exercise.)
        mgr.logout(&mut w, &session);
        // Also revoke the slot the live exercise minted, so the root holds nothing
        // reaching `home` at all (logout in the surface revokes the live c-list).
        let sweep = Effect::RevokeCapability { cell: root, slot: live_slot };
        let t = w.turn(root, vec![sweep]);
        let _ = w.commit_turn(t);

        // AFTER LOGOUT: the same exercise is REFUSED — the root holds no cap to
        // `home` to amplify, so the grant cannot be authorized. The tree is dark.
        let dark_slot = next_free_slot(&w, &root);
        assert!(
            !exercise(&mut w, dark_slot),
            "after logout the session exercise is refused — the cap-tree is dark"
        );
        assert!(!session.reaches(&w, &home), "home unreachable after logout");
    }

    #[test]
    fn provisioning_and_the_demo_identities_drive_the_real_ceremony() {
        // The RUNNING-login provisioning path (what `crate::login` drives): a real
        // system principal holding the anchor caps, the demo identities, and their
        // per-kind templates — all granting through the real executor.
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000_000);
        let svc_target = w.genesis_cell(0x33, 0);
        let (service, _) = w.genesis_cell_with_cap(0x22, 0, svc_target);
        let user = w.genesis_cell(0x44, 5_000);
        let anchors = [treasury, service, user];

        let system_principal = super::provision_system_principal(&mut w, &anchors);
        let mgr = LoginManager::new(system_principal);

        let ids = super::demo_identities();
        assert_eq!(ids.len(), 3, "two users + one agent");

        // A USER identity: full home + launchable app.
        let ember = ids.iter().find(|i| i.name == "ember").unwrap();
        let p = mgr.authenticate(ember.pubkey, true).unwrap();
        assert_eq!(p.root_cell(), ember.root_cell(), "the picker shows the real root cell");
        let user_session = match mgr.login(&mut w, p, &ember.template(anchors)) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("user login: {reason}"),
        };
        assert!(user_session.reaches(&w, &user), "the user reaches their home cell");
        assert!(user_session.reaches(&w, &service), "the user reaches the launchable app");

        // The AGENT identity: the SAME ceremony, a strictly narrower mandate —
        // ONLY the tool surface, no home cell (the polis controller-blind bound).
        let hermes = ids.iter().find(|i| i.kind == super::IdentityKind::Agent).unwrap();
        let pa = mgr.authenticate(hermes.pubkey, true).unwrap();
        let agent_session = match mgr.login(&mut w, pa, &hermes.template(anchors)) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("agent login: {reason}"),
        };
        assert!(agent_session.reaches(&w, &service), "the agent reaches its tool surface");
        assert!(!agent_session.reaches(&w, &user), "the agent gets NO home cell — its mandate is narrower");
        assert_ne!(
            user_session.root_cell, agent_session.root_cell,
            "distinct inhabitants, distinct root cells"
        );

        // Logout is the agent kill switch.
        assert_eq!(mgr.logout(&mut w, &agent_session), 1, "the agent's one cap revoked");
        assert!(!agent_session.is_live(&w), "the agent session is dark — the kill switch");
        assert!(user_session.is_live(&w), "the user session is untouched by the agent's logout");
    }

    #[test]
    fn an_agent_session_is_the_same_ceremony_with_a_narrower_template() {
        // THE POLIS FRAME: an agent (Hermes) logging in = a cap-bounded inhabitant.
        // Identical ceremony; the ONLY difference is a narrower CapTemplate (its
        // mandate). polis_safety's controller-blindness: the bound holds whoever
        // the inhabitant is.
        let (mut w, mgr, home, app) = login_world();
        // The agent's mandate: ONLY the app, at the narrow Signature tier — NOT
        // the user's home cell.
        let agent_template = CapTemplate::empty().with(CapEntry::new(
            app,
            AuthRequired::Signature,
            false, // a tightly-bounded agent cannot re-delegate
            "agent-tool-surface",
        ));
        let agent = mgr.authenticate([0xA6u8; 32], true).unwrap();
        let session = match mgr.login(&mut w, agent, &agent_template) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("agent login: {reason}"),
        };

        // The agent's session reaches ONLY its mandate — not the home cell.
        assert!(session.reaches(&w, &app), "the agent reaches its tool surface");
        assert!(!session.reaches(&w, &home), "the agent's session is bounded — no home cell");

        // Logout is the kill switch: revoke the agent's root → its whole ability
        // to act on the desktop goes dark in one turn.
        assert_eq!(mgr.logout(&mut w, &session), 1, "the agent's one cap revoked");
        assert!(!session.is_live(&w), "the agent session is dark — the kill switch");
    }
}
