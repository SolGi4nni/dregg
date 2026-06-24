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
use dregg_sdk::cipherclerk::AgentCipherclerk;
use dregg_turn::action::Effect;
use dregg_turn::turn::TurnReceipt;

use crate::world::{CommitOutcome, World};

/// The domain string under which a logged-in identity derives its DEFAULT value
/// cell from its clerk — `clerk.cell_id("default")` =
/// `derive_raw(pubkey, blake3("default"))`. This is the cell the cockpit's
/// client-signed turns operate over by default.
pub const DEFAULT_CELL_DOMAIN: &str = "default";

/// Expand a per-identity dev label into a deterministic 64-byte seed for an
/// [`AgentCipherclerk`]. Two independent BLAKE3 `derive_key` outputs (distinct
/// context strings) concatenated → the full 64-byte SDK seed. Fixed + per-label,
/// so the SAME label always reconstructs the SAME clerk (and thus the same
/// pubkey / root cell) across launches. A DEV seed — honest convenience, NOT
/// production key custody.
fn dev_seed(label: &str) -> [u8; 64] {
    let lo = blake3::derive_key("deos-dev-identity-v1", label.as_bytes());
    let hi = blake3::derive_key("deos-dev-identity-v1-hi", label.as_bytes());
    let mut seed = [0u8; 64];
    seed[..32].copy_from_slice(&lo);
    seed[32..].copy_from_slice(&hi);
    seed
}

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
    /// The logged-in identity's 64-byte DEV signing seed, if known. The cockpit
    /// rebuilds the identity's [`AgentCipherclerk`] from this to CLIENT-SIGN turns
    /// (see [`Session::user_clerk`]). `None` for a session reconstructed from a
    /// durable record (which carries only the public identity, not the seed) — such
    /// a session can render + revoke but cannot client-sign until re-derived. A
    /// dev seed, NOT production key custody.
    pub signing_seed: Option<[u8; 64]>,
}

impl Session {
    /// Rebuild the logged-in identity's signing clerk to CLIENT-SIGN turns, if this
    /// session carries the dev seed. `AgentCipherclerk` is NOT `Clone`, so it is
    /// rebuilt from the stored seed on demand (cheap + deterministic). Returns
    /// `None` for a session restored from a durable record (no seed carried).
    pub fn user_clerk(&self) -> Option<AgentCipherclerk> {
        self.signing_seed.map(AgentCipherclerk::from_seed)
    }

    /// The logged-in identity's DEFAULT value cell — `clerk.cell_id("default")` =
    /// `derive_raw(pubkey, blake3("default"))` — if the signing seed is carried.
    /// The cell the cockpit's client-signed turns operate over by default.
    pub fn user_default_cell(&self) -> Option<CellId> {
        self.user_clerk().map(|c| c.cell_id(DEFAULT_CELL_DOMAIN))
    }

    /// Attach the logged-in identity's DEV signing seed to this session so the
    /// cockpit can client-sign turns. The grant ceremony only knows the proven
    /// principal (a pubkey); the caller that holds the picked [`DemoIdentity`]
    /// threads the seed in here (builder style). A dev seed, NOT production custody.
    pub fn with_signing_seed(mut self, seed: [u8; 64]) -> Self {
        self.signing_seed = Some(seed);
        self
    }

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
            debug_assert_eq!(
                cell.id(),
                root_cell,
                "the root cell IS the content-address of the key"
            );
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
                        reason: "world suspended: a session grant queued, not committed"
                            .to_string(),
                    };
                }
            }
        }

        LoginOutcome::Session(Session {
            principal,
            root_cell,
            granted,
            receipts,
            // The ceremony knows only the proven principal (a pubkey), not the
            // secret seed. The signing seed is attached by the caller that holds
            // the picked `DemoIdentity` (see `Session::with_signing_seed` /
            // `login.rs::login_as`).
            signing_seed: None,
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
// SESSION RESUME — Houyhnhnm orthogonal persistence: a logged-in session is
// DURABLE. Login persists a SESSION RECORD (the principal + the granted c-list
// snapshot) into the per-user image's redb store; a relaunch RESTORES it without
// re-running the full grant ceremony. Logout overwrites the record with a REVOKED
// marker — so a revoked session must NOT silently resume.
// (`docs/deos/SESSION-LOGIN.md`; the persistence spine is `crate::persistence`.)
// ===========================================================================

/// **The durable SESSION RECORD** — the snapshot login writes into the per-user
/// image's redb store so a relaunch can RESTORE the session without re-running the
/// grant ceremony. It is the session's identity (principal + root cell) + its
/// c-list snapshot (`granted`), plus a `revoked` flag logout sets.
///
/// Serialized with postcard (the same codec the durable commit log + genesis
/// table use). It is NOT the authority — the authority is the live cap-tree on the
/// root cell in the recovered ledger. The record is the lookup that says "this
/// image belongs to principal P, whose session held these caps"; resume
/// CROSS-CHECKS it against the live ledger (a revoked-or-dark tree does not
/// resume), so a tampered record cannot manufacture authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SessionRecord {
    /// The authenticated principal's public key (the identity; the root cell is
    /// its content-address under [`ROOT_TOKEN`]).
    pub pubkey: [u8; 32],
    /// The session root — the principal's identity cell.
    pub root_cell: CellId,
    /// The c-list snapshot the login ceremony left (`(target, slot, rights)`).
    pub granted: Vec<(CellId, u32, AuthRequired)>,
    /// `true` once LOGOUT revoked the session — a revoked record does NOT resume.
    pub revoked: bool,
}

impl SessionRecord {
    /// Capture the durable record for a freshly-established (live) session.
    pub fn of(session: &Session) -> Self {
        SessionRecord {
            pubkey: session.principal.pubkey,
            root_cell: session.root_cell,
            granted: session.granted.clone(),
            revoked: false,
        }
    }

    /// Encode to the opaque blob stored in the image (postcard).
    pub fn encode(&self) -> Vec<u8> {
        // A hand-rolled, dependency-free postcard-equivalent is avoided: the codec
        // must round-trip exactly, so use the workspace `postcard` the rest of the
        // persistence spine uses.
        postcard::to_stdvec(&Encodable::from(self)).unwrap_or_default()
    }

    /// Decode from the opaque blob (returns `None` on a corrupt/empty record —
    /// fail-closed: a record that does not decode does NOT resume).
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        postcard::from_bytes::<Encodable>(bytes)
            .ok()
            .map(Into::into)
    }

    /// Reconstruct the in-RAM [`Session`] this record describes (no receipts —
    /// they are durable in the image's commit log, not carried in the record).
    pub fn to_session(&self) -> Session {
        Session {
            principal: Principal {
                pubkey: self.pubkey,
            },
            root_cell: self.root_cell,
            granted: self.granted.clone(),
            receipts: Vec::new(),
            // The durable record carries only the PUBLIC identity (pubkey), never
            // the secret seed — so a resumed session cannot client-sign until the
            // caller re-attaches the seed from the picked identity. Fail-closed: a
            // tampered record cannot manufacture a signing key.
            signing_seed: None,
        }
    }
}

/// The on-disk shape of a [`SessionRecord`] — a plain serde struct over the
/// already-`Serialize` field types (`AuthRequired`/`CellId` derive it), so the
/// record codec is exactly the workspace postcard the rest of persistence uses.
#[derive(serde::Serialize, serde::Deserialize)]
struct Encodable {
    pubkey: [u8; 32],
    root_cell: CellId,
    granted: Vec<(CellId, u32, AuthRequired)>,
    revoked: bool,
}

impl From<&SessionRecord> for Encodable {
    fn from(r: &SessionRecord) -> Self {
        Encodable {
            pubkey: r.pubkey,
            root_cell: r.root_cell,
            granted: r.granted.clone(),
            revoked: r.revoked,
        }
    }
}

impl From<Encodable> for SessionRecord {
    fn from(e: Encodable) -> Self {
        SessionRecord {
            pubkey: e.pubkey,
            root_cell: e.root_cell,
            granted: e.granted,
            revoked: e.revoked,
        }
    }
}

// SESSION RESUME is a NATIVE desktop feature — the durable per-user image lives in
// redb (`dregg-persist`, native-only). The browser/wasm image is always ephemeral
// (no `World::session_blob`/`put_session_blob`), so the resumable surface is gated
// off wasm; the plain `login`/`logout` ceremony above is unconditional.
#[cfg(not(target_arch = "wasm32"))]
impl LoginManager {
    /// **LOGIN, RESUMABLE** — the SESSION-RESUME ceremony over a DURABLE image.
    ///
    /// The Houyhnhnm property, made operable: a logged-in session survives a
    /// relaunch. This wraps [`LoginManager::login`] / resume with the per-user
    /// image's durable session record:
    ///
    /// 1. If the image carries a LIVE (non-revoked) session record for this
    ///    principal whose cap-tree is STILL reachable in the recovered ledger →
    ///    RESUME it: reconstruct the [`Session`] from the record, run NO grant
    ///    ceremony (the caps are already durably in the ledger). This is the
    ///    second-login / relaunch path.
    /// 2. Otherwise (fresh image, a record for a different principal, a revoked
    ///    record, or a dark tree) → run the full [`LoginManager::login`] ceremony,
    ///    then PERSIST the resulting session record. This is the first login.
    ///
    /// A REVOKED record never resumes (`revoked == true` ⟹ re-run the ceremony,
    /// which re-grants a fresh live tree) — the load-bearing security property:
    /// logout darkened the tree, and a relaunch must not silently bring it back
    /// without a fresh authenticated grant.
    pub fn login_resumable(
        &self,
        world: &mut World,
        principal: Principal,
        template: &CapTemplate,
    ) -> LoginOutcome {
        let root_cell = principal.root_cell();

        // RESUME path: a durable session record present, for THIS principal, NOT
        // revoked, whose granted tree is still live in the recovered ledger.
        if let Some(record) = world.session_blob().and_then(|b| SessionRecord::decode(&b)) {
            if record.pubkey == principal.pubkey && record.root_cell == root_cell && !record.revoked
            {
                let session = record.to_session();
                // Cross-check against the live ledger: the resume is only legitimate
                // if the cap-tree the record describes is STILL held. A dark tree
                // (e.g. an out-of-band revoke) falls through to a fresh ceremony.
                if session.is_live(world) {
                    return LoginOutcome::Session(session);
                }
            }
        }

        // FIRST-LOGIN (or revoked / dark / foreign record) path: run the real grant
        // ceremony (the mint + per-entry grant turns dual-write into the durable
        // image, so the cap-tree itself SURVIVES a reopen — recovery re-executes
        // them), then persist the session RECORD so the NEXT launch resumes it.
        // Persistence is the default for a logged-in durable session — no save button.
        match self.login(world, principal, template) {
            LoginOutcome::Session(session) => {
                world.put_session_blob(&SessionRecord::of(&session).encode());
                LoginOutcome::Session(session)
            }
            denied => denied,
        }
    }

    /// **LOGOUT, DURABLE** — revoke the session root (the cap-tree goes dark) AND
    /// write a REVOKED session record into the durable image, so a relaunch does
    /// NOT silently resume the revoked session ([`LoginManager::login_resumable`]
    /// skips a revoked record). Returns the number of caps revoked.
    pub fn logout_durable(&self, world: &mut World, session: &Session) -> usize {
        // The revoke turns dual-write durably (the darkened cap-tree survives a
        // reopen — recovery re-executes the revokes), AND the durable session record
        // is stamped REVOKED so `login_resumable` will not resume it on a relaunch.
        let revoked = self.logout(world, session);
        let mut record = SessionRecord::of(session);
        record.revoked = true;
        world.put_session_blob(&record.encode());
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

// ===========================================================================
// THE PER-USER DURABLE SESSION WORLD — the boot wire for SESSION RESUME.
// ===========================================================================

/// The fixed genesis seeds the per-user session world provisions its anchor cells
/// at. They are CONSTANT (not random) so the anchor ids are DETERMINISTIC across
/// launches — the same content-addressed `[treasury, service, user]` ids every
/// time — which is what lets a relaunch recover the SAME anchors from the durable
/// store and reconstruct the SAME session cap-tree.
const ANCHOR_SEEDS: [u8; 3] = [0x11, 0x22, 0x33];

/// The deos image ROOT directory — where per-user session images live. Honors
/// `$DREGG_DEOS_DIR` (the deployment / test override), else `$XDG_DATA_HOME/deos`,
/// else `$HOME/.local/share/deos`, else the OS temp dir. Created on first use.
#[cfg(not(target_arch = "wasm32"))]
pub fn session_base_dir() -> std::path::PathBuf {
    if let Ok(dir) = std::env::var("DREGG_DEOS_DIR") {
        return std::path::PathBuf::from(dir);
    }
    if let Ok(xdg) = std::env::var("XDG_DATA_HOME") {
        return std::path::PathBuf::from(xdg).join("deos");
    }
    if let Ok(home) = std::env::var("HOME") {
        return std::path::PathBuf::from(home).join(".local/share/deos");
    }
    std::env::temp_dir().join("deos")
}

/// The durable image FILE for `principal` under the deos image root `base_dir`:
/// `base_dir/deos-session-<root-cell-hex>.redb`, keyed by the principal's root
/// cell id (its content-address). Each inhabitant gets their OWN sovereign image
/// — distinct keys → distinct files → independent resume, never crossed.
#[cfg(not(target_arch = "wasm32"))]
pub fn session_world_path(base_dir: &std::path::Path, principal: &Principal) -> std::path::PathBuf {
    let hex: String = principal
        .root_cell()
        .as_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    base_dir.join(format!("deos-session-{hex}.redb"))
}

/// **Open (or create) a principal's DURABLE per-user session world**, provisioning
/// its desktop anchors + system principal on first launch and recovering them on a
/// relaunch — the boot half of SESSION RESUME.
///
/// On a FRESH image (first ever launch for this principal) it installs the three
/// deterministic anchor cells `[treasury, service, user]` + an issuer well + the
/// **system principal** holding full caps over the anchors, all via the genesis
/// path (which the durable image MIRRORS, so they survive a reopen). On a RELAUNCH
/// it [`World::open`]s the image — the anchors, system principal and any committed
/// turns recover to exactly where they were closed (the Houyhnhnm property) — and
/// the deterministic seeds re-derive the SAME anchor ids, so the recovered
/// `LoginManager` + anchors line up with the durable cap-tree.
///
/// Returns the opened world, the `[treasury, service, user]` anchors, the
/// [`LoginManager`] over the (recovered or freshly-provisioned) system principal,
/// and `fresh` = whether this launch provisioned a brand-new image (so the caller
/// knows whether to run the demo seed turns — only on a fresh image).
#[cfg(not(target_arch = "wasm32"))]
pub fn open_session_world(
    base_dir: &std::path::Path,
    principal: &Principal,
    costs: dregg_turn::ComputronCosts,
) -> Result<(World, [CellId; 3], LoginManager, bool), crate::persistence::OpenError> {
    let path = session_world_path(base_dir, principal);
    let _ = std::fs::create_dir_all(base_dir);
    // RECOVER, NEVER STRAND: a torn/divergent durable image (a crash mid-write,
    // a poisoned cell) is truncated to its last root-consistent ordinal and
    // reopened at the last-good state, rather than refused — the owner can ALWAYS
    // log in. Only a wholly-unsalvageable image errs here, which login surfaces as
    // the explicit "start fresh?" choice (see `start_fresh_session_world`).
    let (mut world, recovered) = World::open_recovering(&path, costs)?;
    if recovered > 0 {
        eprintln!(
            "[starbridge-v2] open_session_world: recovered a divergent per-user image by \
             truncating {recovered} torn turn(s) to the last consistent state (login proceeds)"
        );
    }

    // The deterministic anchor ids — content-addresses of the fixed seeds, the
    // SAME on a fresh provision and on a recovered image.
    let [s_treasury, s_service, s_user] = ANCHOR_SEEDS;
    let anchors = [
        anchor_id(s_treasury),
        anchor_id(s_service),
        anchor_id(s_user),
    ];

    // FRESH iff the recovered image has no anchor cells yet (an empty store opens
    // to a genesis-empty World). On a relaunch every cell (anchors + the
    // cap-carrying system principal + the session's granted root cell) is RECOVERED
    // from the durable image — the Houyhnhnm property: exactly where it was closed.
    let fresh = world.ledger().get(&anchors[0]).is_none();
    if fresh {
        // FIRST LAUNCH: provision the desktop anchors (value cells) + the system
        // principal (the cap-holder a session is granted FROM) via the genesis path
        // — all durably mirrored, so a relaunch recovers them rather than
        // re-provisioning. Their ids are content-addresses of the fixed seeds, so a
        // recovered image lines up with the deterministic `anchors` /
        // `system_principal` here.
        world.genesis_install(crate::world::make_open_cell(s_treasury, 1_000_000));
        world.genesis_install(crate::world::make_open_cell(s_service, 0));
        world.genesis_install(crate::world::make_open_cell(s_user, 5_000));
        let system_principal = provision_system_principal(&mut world, &anchors);
        debug_assert_eq!(system_principal, anchor_id(SYSTEM_PRINCIPAL_SEED));
        Ok((world, anchors, LoginManager::new(system_principal), true))
    } else {
        // RELAUNCH: the system principal is already in the recovered ledger at the
        // content-address of its fixed seed — do NOT re-provision (that would land a
        // duplicate). Re-derive its id deterministically.
        let system_principal = anchor_id(SYSTEM_PRINCIPAL_SEED);
        debug_assert!(
            world.ledger().get(&system_principal).is_some(),
            "the system principal must be recovered from the durable image on relaunch"
        );
        Ok((world, anchors, LoginManager::new(system_principal), false))
    }
}

/// **Start a FRESH per-user session world**, quarantining an unsalvageable
/// durable image — the last-resort branch of "recover, never strand".
///
/// [`open_session_world`] already RECOVERS a torn image (truncates the divergent
/// tail to the last consistent state). This is for the rarer case where recovery
/// itself is impossible (NO commit-log prefix reconstructs to its claim — e.g. a
/// corrupt checkpoint, a damaged store file): the owner chooses to start over.
/// The corrupt image is RENAMED aside (`<path>.corrupt-<nanos>`) rather than
/// deleted (the prior session is preserved for forensics / manual salvage), then
/// a brand-new image is provisioned at the canonical path. The owner is thus
/// ALWAYS able to log in — recovered when possible, fresh when not.
///
/// Returns the same tuple as [`open_session_world`] (`fresh == true` always).
#[cfg(not(target_arch = "wasm32"))]
pub fn start_fresh_session_world(
    base_dir: &std::path::Path,
    principal: &Principal,
    costs: dregg_turn::ComputronCosts,
) -> Result<(World, [CellId; 3], LoginManager, bool), crate::persistence::OpenError> {
    let path = session_world_path(base_dir, principal);
    // Quarantine the unsalvageable image aside (keep it for forensics), so the
    // canonical path is free for a fresh provision. A missing file is fine (the
    // image may never have existed); a rename failure is non-fatal — the fresh
    // open below will overwrite/append, and the recovery has already truncated.
    if path.exists() {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let aside = path.with_extension(format!("redb.corrupt-{nanos}"));
        if let Err(e) = std::fs::rename(&path, &aside) {
            eprintln!(
                "[starbridge-v2] start_fresh_session_world: could not quarantine the corrupt \
                 image ({e}) — proceeding to provision a fresh one over it"
            );
        } else {
            eprintln!(
                "[starbridge-v2] start_fresh_session_world: the prior durable image was \
                 unsalvageable; quarantined it aside at {} and provisioned a fresh session",
                aside.display()
            );
        }
    }
    // A fresh open of the (now absent) canonical path provisions a brand-new image.
    open_session_world(base_dir, principal, costs)
}

/// The fixed seed the per-user session world's system principal is provisioned at
/// (matches [`provision_system_principal`]'s `make_open_cell(0x55, 0)`), so its id
/// re-derives deterministically on a relaunch.
const SYSTEM_PRINCIPAL_SEED: u8 = 0x55;

/// The deterministic [`CellId`] a genesis anchor seeded at `seed` lands at — the
/// content-address `make_open_cell(seed, _)` computes (balance does not enter the
/// id). Used to re-derive the anchor / system-principal ids on a relaunch without
/// re-installing them.
fn anchor_id(seed: u8) -> CellId {
    crate::world::make_open_cell(seed, 0).id()
}

/// The **default human-user `CapTemplate`** over the deos desktop's anchor cells
/// `[treasury, service, user]`: full attenuatable authority over the `user` home
/// cell, and an attenuated (Signature-tier) launch cap to the `service` app cell.
/// This is policy — the one place "what does a fresh user get" lives.
pub fn default_user_template(anchors: [CellId; 3]) -> CapTemplate {
    let [_treasury, service, user] = anchors;
    CapTemplate::empty()
        .with(CapEntry::new(user, AuthRequired::None, true, "home"))
        .with(CapEntry::new(
            service,
            AuthRequired::Signature,
            true,
            "launcher",
        ))
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
/// stand-in: selecting it is "I possess this key"). Each is backed by a REAL
/// Ed25519 key reconstructable from `dev_seed`: `pubkey` is the actual public key
/// of `AgentCipherclerk::from_seed(dev_seed)`, so the identity can CLIENT-SIGN
/// turns (it is not a fabricated stand-in pubkey). The `kind` selects its
/// template. The live manager replaces the pick with a real key challenge; the
/// dev seed is honest convenience, NOT production key custody.
///
/// NOTE: because each pubkey is now the REAL key (not the old fabricated
/// `[0xE3;32]`/`[0x67;32]`/`[0xA6;32]` bytes), every identity's derived
/// `root_cell` (= `derive_raw(pubkey, ROOT_TOKEN)`) is DIFFERENT from before. Any
/// session image persisted under the old fabricated pubkeys will NOT resume — a
/// fresh per-user image is expected on first login with the real keys.
#[derive(Clone, Debug)]
pub struct DemoIdentity {
    /// The human-readable name shown in the login picker.
    pub name: &'static str,
    /// The identity's public key — the REAL Ed25519 public key of the clerk
    /// rebuilt from `dev_seed`. Its root cell is `derive_raw(pubkey, ROOT_TOKEN)`.
    pub pubkey: [u8; 32],
    /// The deterministic 64-byte DEV seed backing this identity's signing key.
    /// `AgentCipherclerk::from_seed(dev_seed)` rebuilds the exact clerk whose
    /// public key is `pubkey`. A dev convenience (NOT production key custody) —
    /// honest because the resulting key really is the identity's signing key.
    pub dev_seed: [u8; 64],
    /// User vs agent — selects the `CapTemplate` granted on login.
    pub kind: IdentityKind,
    /// A one-line description of what this inhabitant's session is born holding.
    pub blurb: &'static str,
}

impl DemoIdentity {
    /// Construct a demo identity from a fixed dev `label`: derive the 64-byte dev
    /// seed, rebuild the clerk, and take its REAL public key as the identity's
    /// pubkey. The same label always reconstructs the same key (and root cell).
    fn from_label(
        name: &'static str,
        label: &str,
        kind: IdentityKind,
        blurb: &'static str,
    ) -> Self {
        let dev_seed = dev_seed(label);
        let pubkey = AgentCipherclerk::from_seed(dev_seed).public_key().0;
        DemoIdentity {
            name,
            pubkey,
            dev_seed,
            kind,
            blurb,
        }
    }

    /// The root identity cell this demo identity logs into.
    pub fn root_cell(&self) -> CellId {
        CellId::derive_raw(&self.pubkey, &ROOT_TOKEN)
    }

    /// Rebuild this identity's REAL signing clerk from its dev seed. The cockpit
    /// uses this to CLIENT-SIGN turns as the logged-in identity. `AgentCipherclerk`
    /// is NOT `Clone`, so we rebuild from the seed on demand (cheap + deterministic).
    pub fn clerk(&self) -> AgentCipherclerk {
        AgentCipherclerk::from_seed(self.dev_seed)
    }

    /// This identity's DEFAULT value cell — `clerk.cell_id("default")` =
    /// `derive_raw(pubkey, blake3("default"))`. The cell the cockpit's client-signed
    /// turns operate over by default. Stateless: the same key always derives it.
    pub fn user_default_cell(&self) -> CellId {
        self.clerk().cell_id(DEFAULT_CELL_DOMAIN)
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
/// its tool surface — the kill-switch-on-logout polis frame). Each is backed by a
/// REAL Ed25519 key reconstructable from a fixed per-identity dev seed (so the
/// cockpit can client-sign as them); a real deployment authenticates live keys.
pub fn demo_identities() -> Vec<DemoIdentity> {
    vec![
        DemoIdentity::from_label(
            "ember",
            "ember",
            IdentityKind::User,
            "a human user — full home cell + a launchable app (attenuatable)",
        ),
        DemoIdentity::from_label(
            "guest",
            "guest",
            IdentityKind::User,
            "a second human user — the same desktop, their own root cell",
        ),
        DemoIdentity::from_label(
            "Hermes (agent)",
            "hermes",
            IdentityKind::Agent,
            "an agent inhabitant — ONLY its tool surface, no home cell, no re-delegate",
        ),
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
            .with(CapEntry::new(
                app,
                AuthRequired::Signature,
                true,
                "launcher",
            ))
    }

    #[test]
    fn authenticate_gates_the_session_and_derives_a_stable_root_cell() {
        let (_w, mgr, _home, _app) = login_world();
        let pk = [7u8; 32];

        // A failed auth yields no principal — nothing downstream can run.
        assert!(
            mgr.authenticate(pk, false).is_none(),
            "failed auth gates login"
        );

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
        assert_eq!(
            p.root_cell(),
            p2.root_cell(),
            "the same key re-derives the same root cell"
        );
        // A different key → a different cell.
        let other = mgr.authenticate([9u8; 32], true).unwrap();
        assert_ne!(
            p.root_cell(),
            other.root_cell(),
            "distinct keys → distinct identity cells"
        );
    }

    #[test]
    fn login_mints_the_root_cell_and_grants_the_template_as_the_session() {
        // THE CEREMONY: authenticate → derive (mint on first login) → grant the
        // template → the root-cell c-list IS the session.
        let (mut w, mgr, home, app) = login_world();
        let p = mgr.authenticate([7u8; 32], true).unwrap();
        let root = p.root_cell();

        // First login: the identity cell does not exist yet.
        assert!(
            w.ledger().get(&root).is_none(),
            "first login: root cell not yet minted"
        );
        let cells_before = w.cell_count();

        let outcome = mgr.login(&mut w, p, &user_template(home, app));
        let session = match outcome {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("login should succeed: {reason}"),
        };

        // The root cell was minted (a brand-new identity cell).
        assert_eq!(
            w.cell_count(),
            cells_before + 1,
            "first login mints the identity cell"
        );
        assert_eq!(session.root_cell, root);

        // The session IS the granted cap-tree: the root cell now reaches BOTH
        // template targets, at the ATTENUATED rights (≤ the system principal's).
        assert!(session.reaches(&w, &home), "the session reaches home");
        assert!(
            session.reaches(&w, &app),
            "the session reaches the launchable app"
        );
        assert!(session.is_live(&w), "a freshly logged-in session is live");

        let root_cell = w.ledger().get(&root).unwrap();
        let home_cap = root_cell
            .capabilities
            .iter()
            .find(|c| c.target == home)
            .unwrap();
        let app_cap = root_cell
            .capabilities
            .iter()
            .find(|c| c.target == app)
            .unwrap();
        assert_eq!(
            home_cap.permissions,
            AuthRequired::None,
            "home at the template ceiling"
        );
        assert_eq!(
            app_cap.permissions,
            AuthRequired::Signature,
            "app at the attenuated tier"
        );

        // Each grant left a real receipt — the session's verifiable lifecycle.
        assert_eq!(
            session.receipts.len(),
            2,
            "one receipt per template entry granted"
        );
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
        assert_eq!(
            second.session().unwrap().root_cell,
            root,
            "same key → same identity cell"
        );
        assert_eq!(
            w.cell_count(),
            cells_after_first,
            "a returning login retrieves the cell, it does not mint a new one"
        );
        assert!(
            second.session().unwrap().is_live(&w),
            "the re-granted session is live again"
        );
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
        assert!(
            exercise(&mut w, live_slot),
            "a live session can exercise its held cap"
        );

        // LOGOUT — revoke the session root. (Revoke the original template slots;
        // the test then proves the WHOLE tree is dark for a fresh exercise.)
        mgr.logout(&mut w, &session);
        // Also revoke the slot the live exercise minted, so the root holds nothing
        // reaching `home` at all (logout in the surface revokes the live c-list).
        let sweep = Effect::RevokeCapability {
            cell: root,
            slot: live_slot,
        };
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
        assert_eq!(
            p.root_cell(),
            ember.root_cell(),
            "the picker shows the real root cell"
        );
        let user_session = match mgr.login(&mut w, p, &ember.template(anchors)) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("user login: {reason}"),
        };
        assert!(
            user_session.reaches(&w, &user),
            "the user reaches their home cell"
        );
        assert!(
            user_session.reaches(&w, &service),
            "the user reaches the launchable app"
        );

        // The AGENT identity: the SAME ceremony, a strictly narrower mandate —
        // ONLY the tool surface, no home cell (the polis controller-blind bound).
        let hermes = ids
            .iter()
            .find(|i| i.kind == super::IdentityKind::Agent)
            .unwrap();
        let pa = mgr.authenticate(hermes.pubkey, true).unwrap();
        let agent_session = match mgr.login(&mut w, pa, &hermes.template(anchors)) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("agent login: {reason}"),
        };
        assert!(
            agent_session.reaches(&w, &service),
            "the agent reaches its tool surface"
        );
        assert!(
            !agent_session.reaches(&w, &user),
            "the agent gets NO home cell — its mandate is narrower"
        );
        assert_ne!(
            user_session.root_cell, agent_session.root_cell,
            "distinct inhabitants, distinct root cells"
        );

        // Logout is the agent kill switch.
        assert_eq!(
            mgr.logout(&mut w, &agent_session),
            1,
            "the agent's one cap revoked"
        );
        assert!(
            !agent_session.is_live(&w),
            "the agent session is dark — the kill switch"
        );
        assert!(
            user_session.is_live(&w),
            "the user session is untouched by the agent's logout"
        );
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
        assert!(
            session.reaches(&w, &app),
            "the agent reaches its tool surface"
        );
        assert!(
            !session.reaches(&w, &home),
            "the agent's session is bounded — no home cell"
        );

        // Logout is the kill switch: revoke the agent's root → its whole ability
        // to act on the desktop goes dark in one turn.
        assert_eq!(
            mgr.logout(&mut w, &session),
            1,
            "the agent's one cap revoked"
        );
        assert!(
            !session.is_live(&w),
            "the agent session is dark — the kill switch"
        );
    }

    // =======================================================================
    // SESSION RESUME — the Houyhnhnm property, tested (durable per-user image).
    // =======================================================================

    use dregg_turn::ComputronCosts;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};

    static RESUME_COUNTER: AtomicU64 = AtomicU64::new(0);
    const RTS: i64 = 1_700_000_000;

    /// A unique throwaway base DIR for a per-user session image (cleaned up).
    fn scratch_dir() -> PathBuf {
        let n = RESUME_COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        std::env::temp_dir().join(format!("sbv2-session-{pid}-{nanos}-{n}"))
    }

    /// Open a per-user durable session world deterministically at a pinned clock
    /// (so the recovered receipts re-derive bit-identically across reopens). Mirrors
    /// `open_session_world` exactly but pins the test timestamp.
    fn open_resume(
        dir: &std::path::Path,
        principal: &Principal,
    ) -> (World, [CellId; 3], LoginManager, bool) {
        let path = session_world_path(dir, principal);
        let _ = std::fs::create_dir_all(dir);
        let mut world = World::open_with_timestamp(&path, ComputronCosts::zero(), RTS)
            .expect("open per-user session image");
        let [st, ss, su] = ANCHOR_SEEDS;
        let anchors = [anchor_id(st), anchor_id(ss), anchor_id(su)];
        let fresh = world.ledger().get(&anchors[0]).is_none();
        let system_principal = if fresh {
            world.genesis_install(make_open_cell(st, 1_000_000));
            world.genesis_install(make_open_cell(ss, 0));
            world.genesis_install(make_open_cell(su, 5_000));
            provision_system_principal(&mut world, &anchors)
        } else {
            // The system principal is recovered from the durable image on relaunch.
            anchor_id(SYSTEM_PRINCIPAL_SEED)
        };
        (world, anchors, LoginManager::new(system_principal), fresh)
    }

    #[test]
    fn the_session_record_round_trips_through_postcard() {
        let (mut w, mgr, home, app) = login_world();
        let p = mgr.authenticate([7u8; 32], true).unwrap();
        let session = mgr
            .login(&mut w, p, &user_template(home, app))
            .session()
            .unwrap()
            .clone();
        let record = SessionRecord::of(&session);
        let decoded = SessionRecord::decode(&record.encode()).expect("record decodes");
        assert_eq!(
            decoded, record,
            "the session record round-trips byte-exactly"
        );
        assert!(
            !decoded.revoked,
            "a fresh login record is live, not revoked"
        );
        // The reconstructed session has the same root + c-list (receipts are durable
        // in the commit log, not carried in the record).
        let rebuilt = decoded.to_session();
        assert_eq!(rebuilt.root_cell, session.root_cell);
        assert_eq!(rebuilt.granted, session.granted);
    }

    #[test]
    fn a_logged_in_session_dual_writes_and_resumes_after_a_reopen() {
        // (b) THE HOUYHNHNM PROPERTY: a logged-in session's turns dual-write to the
        // durable image, and a RELAUNCH resumes the EXACT image — the cell graph +
        // balances + the SESSION CAP-TREE itself — without re-running the grant
        // ceremony. (Not a fresh demo.)
        let dir = scratch_dir();
        let p = Principal {
            pubkey: [0xE3u8; 32],
        };

        let (root, treasury_after, user_after, granted_len) = {
            let (mut w, anchors, mgr, fresh) = open_resume(&dir, &p);
            assert!(fresh, "first launch provisions a fresh image");
            assert!(w.is_durable(), "the per-user session world is durable");
            let template = default_user_template(anchors);

            // FIRST LOGIN: runs the ceremony (the mint + 2 grant turns dual-write
            // durably) + persists the session record.
            let session = match mgr.login_resumable(&mut w, p, &template) {
                LoginOutcome::Session(s) => s,
                LoginOutcome::Denied { reason } => panic!("first login: {reason}"),
            };
            assert!(session.is_live(&w), "the session is live after first login");
            assert_eq!(
                session.receipts.len(),
                2,
                "first login ran the 2-entry grant ceremony"
            );

            // A SESSION VALUE TURN: treasury → user, a real committed turn dual-written.
            let [treasury, _service, user] = anchors;
            let nonce = w
                .ledger()
                .get(&treasury)
                .map(|c| c.state.nonce())
                .unwrap_or(0);
            let t = crate::world::bare_turn(
                treasury,
                nonce,
                vec![crate::world::transfer(treasury, user, 1234)],
            );
            assert!(
                w.commit_turn(t).is_committed(),
                "the session value turn commits + dual-writes"
            );
            w.checkpoint_now();
            (
                session.root_cell,
                w.ledger().get(&treasury).unwrap().state.balance(),
                w.ledger().get(&user).unwrap().state.balance(),
                session.granted.len(),
            )
            // w dropped → the redb image persists, the handle releases.
        };

        // RELAUNCH: reopen the SAME per-user image — the WHOLE image resumes, the
        // cap-tree included, and `login_resumable` RESUMES (no re-grant ceremony).
        {
            let (mut w, anchors, mgr, fresh) = open_resume(&dir, &p);
            assert!(
                !fresh,
                "the relaunch recovers the existing image (not fresh)"
            );
            let [treasury, _service, user] = anchors;

            // The VALUE substrate resumed exactly (the Houyhnhnm property).
            assert_eq!(
                w.ledger().get(&treasury).unwrap().state.balance(),
                treasury_after,
                "the treasury balance resumed exactly"
            );
            assert_eq!(
                w.ledger().get(&user).unwrap().state.balance(),
                user_after,
                "the user balance resumed exactly"
            );

            // The CAP-TREE resumed too: the granted root cell still reaches its
            // template targets in the RECOVERED ledger, BEFORE any re-login.
            let recovered_root = w.ledger().get(&root).expect("the root cell resumed");
            assert!(
                anchors[1..]
                    .iter()
                    .all(|t| recovered_root.capabilities.has_access(t)),
                "the session cap-tree resumed from the durable image"
            );

            // RESUME: a re-login finds the live record + live tree and RESUMES it —
            // no grant ceremony re-ran (no new receipts).
            let template = default_user_template(anchors);
            let resumed = match mgr.login_resumable(&mut w, p, &template) {
                LoginOutcome::Session(s) => s,
                LoginOutcome::Denied { reason } => panic!("resume login: {reason}"),
            };
            assert!(
                resumed.receipts.is_empty(),
                "a RESUMED session ran NO grant ceremony"
            );
            assert_eq!(
                resumed.root_cell, root,
                "the resumed session is the same root"
            );
            assert_eq!(
                resumed.granted.len(),
                granted_len,
                "the same c-list resumed"
            );
            assert!(resumed.is_live(&w), "the resumed session is live");
        }

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn logout_then_relaunch_does_not_resume_a_revoked_session() {
        // (c) THE SECURITY PROPERTY: after a DURABLE logout, a relaunch must NOT
        // silently resume the revoked session — the cap-tree stays dark (the revokes
        // are durable) AND the durable record carries REVOKED, so `login_resumable`
        // re-runs the ceremony (a fresh authenticated grant) rather than resuming.
        let dir = scratch_dir();
        let p = Principal {
            pubkey: [0x67u8; 32],
        };

        // FIRST LOGIN then DURABLE LOGOUT.
        {
            let (mut w, anchors, mgr, _fresh) = open_resume(&dir, &p);
            let template = default_user_template(anchors);
            let session = match mgr.login_resumable(&mut w, p, &template) {
                LoginOutcome::Session(s) => s,
                LoginOutcome::Denied { reason } => panic!("login: {reason}"),
            };
            assert!(session.is_live(&w), "live after login");
            let revoked = mgr.logout_durable(&mut w, &session);
            assert_eq!(revoked, 2, "logout revoked both session caps");
            assert!(!session.is_live(&w), "the cap-tree is dark after logout");
            let rec =
                SessionRecord::decode(&w.session_blob().expect("a record was written")).unwrap();
            assert!(rec.revoked, "the durable session record is marked revoked");
            w.checkpoint_now();
        }

        // RELAUNCH: the revoked cap-tree stays dark across the reopen, and the
        // revoked record does NOT silently resume.
        {
            let (mut w, anchors, mgr, _fresh) = open_resume(&dir, &p);
            let rec = SessionRecord::decode(&w.session_blob().unwrap()).unwrap();
            assert!(
                rec.revoked,
                "the revoked record persisted across the reopen"
            );
            // The recovered cap-tree is dark (the durable revokes resumed too).
            let dark = rec.to_session();
            assert!(
                !dark.is_live(&w),
                "the revoked session does NOT silently resume — the tree is dark on reopen"
            );

            // A fresh, explicit login re-runs the ceremony (not a resume) — the
            // authenticated way back in — and writes a fresh LIVE record.
            let template = default_user_template(anchors);
            let session = match mgr.login_resumable(&mut w, p, &template) {
                LoginOutcome::Session(s) => s,
                LoginOutcome::Denied { reason } => panic!("re-login: {reason}"),
            };
            assert_eq!(
                session.receipts.len(),
                2,
                "the re-login re-ran the grant ceremony (not a resume)"
            );
            assert!(
                session.is_live(&w),
                "the freshly re-granted session is live again"
            );
            let rec2 = SessionRecord::decode(&w.session_blob().unwrap()).unwrap();
            assert!(!rec2.revoked, "the re-login wrote a fresh LIVE record");
        }

        let _ = std::fs::remove_dir_all(&dir);
    }
}
