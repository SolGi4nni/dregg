//! Node-hosted, restart-durable REALM substrate.
//!
//! This is the graduation of `realm-model/` (the §9.4/§9.5/§9.2 MUD substrate:
//! persistent REALM vs child INSTANCE, canonical IDENTITY the surfaces derive
//! from, and the committed RULESET CATALOG) from a disconnected standalone crate
//! into the running node. `docs/audit/DEEP-world-substrate.md` recorded it as
//! REAL-as-a-model but with CONNECTEDNESS = NONE (zero reverse deps, its own empty
//! `[workspace]`); `docs/design/MUD-SUBSTRATE.md:163-198` named the wiring and
//! `:365-389` named the one load-bearing dependency it lacked — a node-served,
//! **restart-durable receipt/turn chain**. That dependency is now BUILT (the
//! keystone: `persist`'s `RECEIPT_CHAIN` + `node`'s
//! `install_receipt_chain_durability`, driven by
//! `receipt_chain_and_mmr_head_survive_node_restart`). This module rides the same
//! durable-append discipline for the realm substrate.
//!
//! ## What is genuinely wired here
//!
//! * The node HOSTS a real [`realm_model::RealmWorld`] (its own cell-backed
//!   ledger). Every realm/instance turn the node admits routes through
//!   realm-model's actual gate ([`RealmWorld::admit`] /
//!   [`RealmWorld::settle_instance`]) — the catalog check, the identity
//!   resolution, and the scope membrane are realm-model's, not ad-hoc JavaScript
//!   in a `mud_gm.js` host program.
//! * Every ADMITTED operation is appended to the durable `REALM_LOG` (persist), a
//!   dense, gap-checked, hash-linked log (the exact density discipline the
//!   `RECEIPT_CHAIN` keystone uses). A REFUSED turn (e.g. an unlisted
//!   `ruleset_root`) mutates nothing and is NOT logged.
//! * On boot, [`NodeRealms::restore`] replays the durable log through a fresh
//!   `RealmWorld`, reconstructing the identical realm/instance/identity/catalog
//!   state AND the identical receipt-chain head — a realm created through the node
//!   survives a node restart.
//!
//! ## The HTTP ingress (`/realm*`)
//!
//! [`routes`] mounts the realm substrate on the node's HTTP surface (the
//! ORGANS service pattern — `storage_service` / `trustline_service` /
//! `channels_service` / `equivocation_court_service` / `dkg_service`), inside
//! the node's PROTECTED router, so a client can create/list realms, list law,
//! open/play/settle instances, drive identity succession + guardian recovery,
//! and read the durable realm state over the wire. Every write route goes
//! through the SAME [`NodeRealms`] gate as the in-process path — realm-model's
//! catalog check, identity resolution, and scope membrane — and lands in the
//! SAME durable `REALM_LOG`. A refused HTTP request (e.g. an uncatalogued
//! `ruleset_root`) mutates nothing and persists nothing.
//!
//! ## Honest residual (named, not laundered)
//!
//! * The catalog gate here is realm-model's `RealmWorld::admit`, which the node
//!   calls as the deployed admission point for realm turns. It is NOT yet inside
//!   the kernel executor's `proof_verify.rs` path, and `ruleset_root` is NOT yet a
//!   first-class field of `dregg_turn::Turn` (MUD-SUBSTRATE.md wiring items 1-2;
//!   the design for that kernel-perimeter change is
//!   `docs/design/DESIGN-realm-kernel-perimeter.md`). So a realm turn admitted
//!   over `/realm/*` is a node-hosted, durable, gate-routed admission — NOT the
//!   signed, fee-estimated, proof-carrying `Turn` that `/turns/submit` drives.
//! * **Identity minting through this ingress is NON-CUSTODIAL by default.** The
//!   holder generates the birth hybrid key (ed25519 + ML-DSA-65) OFF node and
//!   `POST /realm/identity/mint` carries only its PUBLIC halves (`birth_ed_pk` +
//!   `birth_ml_pk`); the node computes the commitment
//!   ([`realm_model::identity::commit_hybrid`]) and derives the identity cell-id
//!   from it — NO seed material crosses the API or into the durable `REALM_LOG`
//!   (the `MintIdentityPubkey` op carries only the public keys, re-derived on boot
//!   replay). A non-custodial identity is referenced by its PUBLIC cell-id handle,
//!   so bind / guardians / rotate / recover carry `identity` (the id hex) rather
//!   than a seed. This matches succession's existing posture: the hybrid
//!   signatures arrive ON THE WIRE and the node only verifies them through
//!   realm-model's gate — the node never holds key material.
//! * ⚠ A **CUSTODIAL** mint is RETAINED for a server-custodial use only: supplying
//!   `principal_seed` makes realm-model derive the birth key from it
//!   ([`realm_model::identity::hybrid_seed`]), handing the node the seed material
//!   (never echoed or logged; behind the bearer gate). The two are mutually
//!   exclusive on the route, and the non-custodial public-key path is preferred.
//! * The realm write path takes the realm lock, not the node's executor lock:
//!   these turns do not consume fees, do not enter the block/receipt pipeline,
//!   and are not visible to `/api/receipts`. The realm receipt chain is its own
//!   ordered history (see [`NodeRealms::receipt_head`]).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use axum::extract::{Path as AxumPath, State};
use axum::http::StatusCode;
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};

use dregg_cell::CellId;
use dregg_persist::PersistentStore;
use dregg_turn::action::Effect;

use realm_model::identity::{HybridSig, Surface, SurfaceRef};
use realm_model::instance::InstanceStatus;
use realm_model::realm::Membrane;
use realm_model::{
    CanonicalIdentity, Instance, Realm, RealmReceipt, RealmTurn, RealmWorld, Refused, RulesetRoot,
    pack_u64,
};

use crate::state::NodeState;

/// An error from a node realm operation: a gate REFUSAL (realm-model's semantics,
/// e.g. an unlisted `ruleset_root`), an unknown node-side handle (a caller named a
/// realm/identity the node never created), or a durable-store failure.
#[derive(Debug)]
pub enum RealmError {
    /// realm-model's admission gate refused the turn (the deployed refusal —
    /// `RulesetNotInCatalog`, `OutsideInstanceScope`, `InstanceFinalized`, ...).
    Refused(Refused),
    /// A node-side handle (realm name / identity principal-seed) is unknown.
    UnknownHandle(String),
    /// A durable realm-log encode/append failure (fail-closed: the caller must not
    /// treat an unpersisted realm mutation as durable).
    Store(String),
    /// A malformed request (bad hex, wrong signature length, unknown surface).
    /// Nothing is applied and nothing is persisted.
    BadRequest(String),
}

impl std::fmt::Display for RealmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RealmError::Refused(r) => write!(f, "realm turn refused: {r:?}"),
            RealmError::UnknownHandle(h) => write!(f, "unknown realm handle: {h}"),
            RealmError::Store(s) => write!(f, "realm store error: {s}"),
            RealmError::BadRequest(s) => write!(f, "bad realm request: {s}"),
        }
    }
}

impl std::error::Error for RealmError {}

/// A serde mirror of [`Surface`] (the model's enum has no serde derive; the wire
/// form is stable across the durable log).
fn surface_to_u8(s: Surface) -> u8 {
    match s {
        Surface::Discord => 0,
        Surface::Web => 1,
        Surface::Telegram => 2,
        Surface::WeChat => 3,
        Surface::Native => 4,
        Surface::Other => 5,
    }
}

fn u8_to_surface(v: u8) -> Surface {
    match v {
        0 => Surface::Discord,
        1 => Surface::Web,
        2 => Surface::Telegram,
        3 => Surface::WeChat,
        4 => Surface::Native,
        _ => Surface::Other,
    }
}

/// Serializable mirror of [`SurfaceRef`] for the durable log.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct SurfaceRefWire {
    surface: u8,
    local: String,
}

impl From<&SurfaceRef> for SurfaceRefWire {
    fn from(s: &SurfaceRef) -> Self {
        SurfaceRefWire {
            surface: surface_to_u8(s.surface),
            local: s.local.clone(),
        }
    }
}

impl From<SurfaceRefWire> for SurfaceRef {
    fn from(w: SurfaceRefWire) -> Self {
        SurfaceRef::new(u8_to_surface(w.surface), w.local)
    }
}

/// A serde mirror of [`HybridSig`] (ed25519 ∧ ML-DSA-65 over one canonical
/// succession message). The signature arrives ON THE WIRE and is stored verbatim
/// in the durable log, so boot replay RE-VERIFIES it through realm-model's gate —
/// a succession is never durable-but-unchecked. `ed_sig` is a `Vec<u8>` because
/// serde has no impl for `[u8; 64]`; it must be exactly 64 bytes.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HybridSigWire {
    /// ed25519 public key of the signer (32 bytes).
    pub ed_pk: [u8; 32],
    /// Serialized ML-DSA-65 public key of the signer.
    pub ml_pk: Vec<u8>,
    /// ed25519 signature (exactly 64 bytes).
    pub ed_sig: Vec<u8>,
    /// ML-DSA-65 signature.
    pub ml_sig: Vec<u8>,
}

impl HybridSigWire {
    /// Wire → model. Fails closed on a malformed ed25519 signature length (an
    /// invalid signature would fail verification anyway; this refuses earlier and
    /// with a better message).
    fn to_sig(&self) -> Result<HybridSig, RealmError> {
        let ed_sig: [u8; 64] = self.ed_sig.as_slice().try_into().map_err(|_| {
            RealmError::BadRequest(format!(
                "ed25519 signature must be 64 bytes, got {}",
                self.ed_sig.len()
            ))
        })?;
        Ok(HybridSig {
            ed_pk: self.ed_pk,
            ml_pk: self.ml_pk.clone(),
            ed_sig,
            ml_sig: self.ml_sig.clone(),
        })
    }
}

impl From<&HybridSig> for HybridSigWire {
    fn from(s: &HybridSig) -> Self {
        HybridSigWire {
            ed_pk: s.ed_pk,
            ml_pk: s.ml_pk.clone(),
            ed_sig: s.ed_sig.to_vec(),
            ml_sig: s.ml_sig.clone(),
        }
    }
}

/// One durable realm operation — the replay unit. Only ADMITTED operations are
/// logged; replaying the dense log through a fresh [`RealmWorld`] reconstructs the
/// identical state. Every field is stable-serializable (32-byte ids, the wire
/// surface, and `dregg_turn::action::Effect`, which already derives serde).
#[derive(Clone, Debug, Serialize, Deserialize)]
enum RealmOp {
    MintIdentity {
        label: String,
        principal_seed: String,
    },
    BindSurface {
        principal_seed: String,
        actor: SurfaceRefWire,
    },
    CreateRealm {
        name: String,
        /// The committed [`Membrane`] discriminant (`Membrane::as_u64`).
        membrane: u8,
    },
    ListRuleset {
        realm_name: String,
        root: [u8; 32],
    },
    UnlistRuleset {
        realm_name: String,
        root: [u8; 32],
    },
    OpenInstance {
        realm_name: String,
        seed: String,
    },
    Admit {
        actor: SurfaceRefWire,
        instance: [u8; 32],
        ruleset_root: [u8; 32],
        effects: Vec<Effect>,
    },
    Settle {
        actor: SurfaceRefWire,
        instance: [u8; 32],
        ruleset_root: [u8; 32],
    },
    // ── succession / guardian recovery (§9.5) ────────────────────────────────
    // NOTE: these variants are APPENDED. postcard tags enum variants by index,
    // so appending keeps every previously-written log entry decodable.
    RegisterGuardians {
        principal_seed: String,
        /// Guardian key COMMITMENTS (`realm_model::identity::commit_hybrid`).
        guardians: Vec<[u8; 32]>,
        threshold: u32,
    },
    Rotate {
        principal_seed: String,
        new_key_commit: [u8; 32],
        /// Hybrid signature BY THE CURRENT KEY — re-verified on replay.
        sig: HybridSigWire,
    },
    Recover {
        principal_seed: String,
        new_key_commit: [u8; 32],
        /// K-of-N guardian co-signs — re-verified on replay.
        guardian_sigs: Vec<HybridSigWire>,
    },
    // ── NON-CUSTODIAL identity (the default) ─────────────────────────────────
    // The holder generates the birth hybrid key OFF node; only PUBLIC key
    // material crosses. Succession then references the identity by its durable
    // CELL-ID (there is no node-known seed). APPENDED — postcard tags variants by
    // index, so every previously-written log entry stays decodable.
    /// Mint from the holder's birth hybrid PUBLIC key. NO seed material — the
    /// node computes the commitment and derives the cell-id from it. Re-derived
    /// deterministically on replay from the same public keys.
    MintIdentityPubkey {
        label: String,
        /// ed25519 public key of the birth key (32 bytes).
        ed_pk: [u8; 32],
        /// Serialized ML-DSA-65 public key of the birth key.
        ml_pk: Vec<u8>,
    },
    /// Bind a surface onto an identity named by its durable cell-id (the public
    /// handle a non-custodial identity is referenced by).
    BindSurfaceToId {
        identity: [u8; 32],
        actor: SurfaceRefWire,
    },
    /// Register a guardian set on an identity named by its cell-id.
    RegisterGuardiansById {
        identity: [u8; 32],
        guardians: Vec<[u8; 32]>,
        threshold: u32,
    },
    /// Rotate an identity named by its cell-id — hybrid signature by the current
    /// key, re-verified on replay.
    RotateById {
        identity: [u8; 32],
        new_key_commit: [u8; 32],
        sig: HybridSigWire,
    },
    /// Recover an identity named by its cell-id — K-of-N guardian co-signs,
    /// re-verified on replay.
    RecoverById {
        identity: [u8; 32],
        new_key_commit: [u8; 32],
        guardian_sigs: Vec<HybridSigWire>,
    },
}

/// The node's durable realm subsystem: a real `RealmWorld` plus the durable
/// `REALM_LOG` it is projected from, and the node-side handle maps that name
/// realms/identities for the ingress.
pub struct NodeRealms {
    world: RealmWorld,
    store: Arc<PersistentStore>,
    /// Dense index of the next durable log entry (== durable log length).
    next_index: u64,
    /// principal-seed -> the canonical identity minted from it. ONLY populated for
    /// CUSTODIAL mints (the node held the seed); a non-custodial identity has no
    /// entry here (the node never saw a seed).
    identities: HashMap<String, CanonicalIdentity>,
    /// identity cell-id -> the canonical identity. The PUBLIC handle, populated
    /// for BOTH mint paths — the reference a non-custodial identity (and its
    /// succession) uses, since there is no node-known seed to key it by.
    identities_by_id: HashMap<CellId, CanonicalIdentity>,
    /// realm name -> the realm.
    realms: HashMap<String, Realm>,
    /// realm name -> the roots the durable log LISTED and did not unlist. A
    /// node-side INDEX for the read routes only — the AUTHORITY is the catalog
    /// cell, so every reported root is re-checked against
    /// [`RealmWorld::is_listed`] before it is served.
    listed: HashMap<String, BTreeSet<RulesetRoot>>,
    /// instance id -> (realm name, seed). The reverse handle the instance read
    /// routes need; rebuilt by replay exactly like the rest.
    instances: BTreeMap<CellId, (String, String)>,
}

impl NodeRealms {
    /// Reconstruct the realm subsystem from the durable `REALM_LOG` (the boot
    /// RESTORE, mirroring `install_receipt_chain_durability`). Replays the complete
    /// dense log through a fresh `RealmWorld`; a gap, undecodable entry, or an op
    /// that refuses on replay fails node construction (fail-closed — none may be
    /// laundered into a shorter accepted realm history).
    pub fn restore(store: Arc<PersistentStore>) -> Result<Self, String> {
        let mut this = NodeRealms {
            world: RealmWorld::new(),
            store: Arc::clone(&store),
            next_index: 0,
            identities: HashMap::new(),
            identities_by_id: HashMap::new(),
            realms: HashMap::new(),
            listed: HashMap::new(),
            instances: BTreeMap::new(),
        };
        let log = store
            .load_realm_log()
            .map_err(|e| format!("failed to load durable realm log: {e}"))?;
        let persisted = log.len();
        for (i, bytes) in log.iter().enumerate() {
            let op: RealmOp = postcard::from_bytes(bytes)
                .map_err(|e| format!("invalid durable realm op at log index {i}: {e}"))?;
            this.apply(&op).map_err(|e| {
                format!("durable realm op at log index {i} refused on replay (integrity): {e}")
            })?;
        }
        this.next_index = persisted as u64;
        if persisted > 0 {
            tracing::info!(
                replayed = persisted,
                "restored durable realm substrate on boot (realm/instance/identity + \
                 receipt-chain head survive the restart)"
            );
        } else {
            tracing::debug!("no durable realm log to restore (fresh node)");
        }
        Ok(this)
    }

    /// Apply one op to the in-memory world + handle maps. DETERMINISTIC and shared
    /// by both the live path and boot replay, so replaying the log reproduces the
    /// identical state (including the realm receipt-chain head).
    fn apply(&mut self, op: &RealmOp) -> Result<(), RealmError> {
        match op {
            RealmOp::MintIdentity {
                label,
                principal_seed,
            } => {
                let id = self
                    .world
                    .mint_identity(label, principal_seed)
                    .map_err(RealmError::Refused)?;
                self.identities.insert(principal_seed.clone(), id.clone());
                self.identities_by_id.insert(id.id, id);
            }
            RealmOp::BindSurface {
                principal_seed,
                actor,
            } => {
                let identity = self
                    .identities
                    .get(principal_seed)
                    .cloned()
                    .ok_or_else(|| {
                        RealmError::UnknownHandle(format!("identity {principal_seed}"))
                    })?;
                self.world
                    .bind_surface(&identity, actor.clone().into())
                    .map_err(RealmError::Refused)?;
            }
            RealmOp::CreateRealm { name, membrane } => {
                let realm = self
                    .world
                    .create_realm_with_membrane(name, Membrane::from_u64(*membrane as u64))
                    .map_err(RealmError::Refused)?;
                self.realms.insert(name.clone(), realm);
            }
            RealmOp::ListRuleset { realm_name, root } => {
                let realm_id = self.realm_id(realm_name)?;
                self.world
                    .list_ruleset(&realm_id, *root)
                    .map_err(RealmError::Refused)?;
                self.listed
                    .entry(realm_name.clone())
                    .or_default()
                    .insert(*root);
            }
            RealmOp::UnlistRuleset { realm_name, root } => {
                let realm_id = self.realm_id(realm_name)?;
                self.world
                    .unlist_ruleset(&realm_id, *root)
                    .map_err(RealmError::Refused)?;
                if let Some(set) = self.listed.get_mut(realm_name) {
                    set.remove(root);
                }
            }
            RealmOp::OpenInstance { realm_name, seed } => {
                let realm_id = self.realm_id(realm_name)?;
                let inst = self
                    .world
                    .open_instance(&realm_id, seed)
                    .map_err(RealmError::Refused)?;
                self.instances
                    .insert(inst.id, (realm_name.clone(), seed.clone()));
            }
            RealmOp::Admit {
                actor,
                instance,
                ruleset_root,
                effects,
            } => {
                self.world
                    .admit(RealmTurn {
                        actor: actor.clone().into(),
                        instance: CellId::from_bytes(*instance),
                        ruleset_root: *ruleset_root,
                        effects: effects.clone(),
                    })
                    .map_err(RealmError::Refused)?;
            }
            RealmOp::Settle {
                actor,
                instance,
                ruleset_root,
            } => {
                self.world
                    .settle_instance(
                        actor.clone().into(),
                        CellId::from_bytes(*instance),
                        *ruleset_root,
                    )
                    .map_err(RealmError::Refused)?;
            }
            RealmOp::RegisterGuardians {
                principal_seed,
                guardians,
                threshold,
            } => {
                let id = self.identity_id(principal_seed)?;
                self.world
                    .register_guardians(&id, guardians, *threshold)
                    .map_err(RealmError::Refused)?;
            }
            RealmOp::Rotate {
                principal_seed,
                new_key_commit,
                sig,
            } => {
                let id = self.identity_id(principal_seed)?;
                let sig = sig.to_sig()?;
                self.world
                    .rotate_identity(&id, *new_key_commit, &sig)
                    .map_err(RealmError::Refused)?;
            }
            RealmOp::Recover {
                principal_seed,
                new_key_commit,
                guardian_sigs,
            } => {
                let id = self.identity_id(principal_seed)?;
                let sigs = guardian_sigs
                    .iter()
                    .map(|s| s.to_sig())
                    .collect::<Result<Vec<_>, _>>()?;
                self.world
                    .recover_identity(&id, *new_key_commit, &sigs)
                    .map_err(RealmError::Refused)?;
            }
            // ── non-custodial (by public key / by cell-id) ───────────────────
            RealmOp::MintIdentityPubkey {
                label,
                ed_pk,
                ml_pk,
            } => {
                let id = self
                    .world
                    .mint_identity_from_pubkey(label, ed_pk, ml_pk)
                    .map_err(RealmError::Refused)?;
                // NO seed handle — the node never saw one. Public cell-id handle only.
                self.identities_by_id.insert(id.id, id);
            }
            RealmOp::BindSurfaceToId { identity, actor } => {
                let id = CellId::from_bytes(*identity);
                let canonical = self.id_identity(&id)?;
                self.world
                    .bind_surface(&canonical, actor.clone().into())
                    .map_err(RealmError::Refused)?;
            }
            RealmOp::RegisterGuardiansById {
                identity,
                guardians,
                threshold,
            } => {
                let id = CellId::from_bytes(*identity);
                self.world
                    .register_guardians(&id, guardians, *threshold)
                    .map_err(RealmError::Refused)?;
            }
            RealmOp::RotateById {
                identity,
                new_key_commit,
                sig,
            } => {
                let id = CellId::from_bytes(*identity);
                let sig = sig.to_sig()?;
                self.world
                    .rotate_identity(&id, *new_key_commit, &sig)
                    .map_err(RealmError::Refused)?;
            }
            RealmOp::RecoverById {
                identity,
                new_key_commit,
                guardian_sigs,
            } => {
                let id = CellId::from_bytes(*identity);
                let sigs = guardian_sigs
                    .iter()
                    .map(|s| s.to_sig())
                    .collect::<Result<Vec<_>, _>>()?;
                self.world
                    .recover_identity(&id, *new_key_commit, &sigs)
                    .map_err(RealmError::Refused)?;
            }
        }
        Ok(())
    }

    /// Apply then durably append an op. Refused ops (nothing mutated) are NOT
    /// persisted — the durable log is a log of ADMITTED operations only. A store
    /// failure after a successful apply is fail-closed (the caller learns the
    /// mutation is not durable; a restart replays only the durable prefix).
    fn commit(&mut self, op: RealmOp) -> Result<(), RealmError> {
        self.apply(&op)?;
        let bytes = postcard::to_stdvec(&op)
            .map_err(|e| RealmError::Store(format!("encode realm op: {e}")))?;
        self.store
            .append_realm_log_entry(self.next_index, &bytes)
            .map_err(|e| {
                RealmError::Store(format!(
                    "persist realm op at index {}: {e}",
                    self.next_index
                ))
            })?;
        self.next_index += 1;
        Ok(())
    }

    fn realm_id(&self, name: &str) -> Result<CellId, RealmError> {
        self.realms
            .get(name)
            .map(|r| r.id)
            .ok_or_else(|| RealmError::UnknownHandle(format!("realm {name}")))
    }

    /// The canonical identity cell minted from `principal_seed` (the CUSTODIAL
    /// node-side handle). The seed itself is NEVER echoed back to a caller.
    fn identity_id(&self, principal_seed: &str) -> Result<CellId, RealmError> {
        self.identities
            .get(principal_seed)
            .map(|i| i.id)
            .ok_or_else(|| RealmError::UnknownHandle("identity (unminted principal)".to_string()))
    }

    /// The canonical identity named by its durable cell-id (the PUBLIC handle a
    /// non-custodial identity is referenced by). Works for custodial identities
    /// too — both mint paths register the id handle.
    fn id_identity(&self, identity: &CellId) -> Result<CanonicalIdentity, RealmError> {
        self.identities_by_id.get(identity).cloned().ok_or_else(|| {
            RealmError::UnknownHandle(format!(
                "identity {} (unminted)",
                hex32(identity.as_bytes())
            ))
        })
    }

    // ── the node ingress: durable, gate-routed realm operations ────────────────

    /// Mint a canonical identity (durable). Returns the identity.
    pub fn mint_identity(
        &mut self,
        label: &str,
        principal_seed: &str,
    ) -> Result<CanonicalIdentity, RealmError> {
        self.commit(RealmOp::MintIdentity {
            label: label.to_string(),
            principal_seed: principal_seed.to_string(),
        })?;
        Ok(self
            .identities
            .get(principal_seed)
            .cloned()
            .expect("identity present after successful mint"))
    }

    /// Mint a canonical identity NON-CUSTODIALLY — the DEFAULT (durable). The
    /// holder generated the birth hybrid key OFF node and hands over only its
    /// PUBLIC halves (`ed_pk` + `ml_pk`); NO seed material crosses into the node or
    /// the durable log. The node computes the commitment, derives the identity
    /// cell-id from it, and the durable `MintIdentityPubkey` op re-derives the
    /// identical identity on boot replay from the same public keys. Returns the
    /// identity — its cell-id hex is the PUBLIC handle succession then references.
    pub fn mint_identity_from_pubkey(
        &mut self,
        label: &str,
        ed_pk: &[u8; 32],
        ml_pk: &[u8],
    ) -> Result<CanonicalIdentity, RealmError> {
        self.commit(RealmOp::MintIdentityPubkey {
            label: label.to_string(),
            ed_pk: *ed_pk,
            ml_pk: ml_pk.to_vec(),
        })?;
        // The id is deterministic from the public commitment; fetch the registered
        // identity by re-deriving nothing — it is the last one inserted by id.
        let commit = realm_model::identity::commit_hybrid(ed_pk, ml_pk);
        self.identities_by_id
            .values()
            .find(|i| i.birth_key_commit == commit)
            .cloned()
            .ok_or_else(|| RealmError::UnknownHandle("identity absent after mint".to_string()))
    }

    /// Bind a surface ref onto an identity named by its durable cell-id — the
    /// non-custodial handle (durable). No seed is involved.
    pub fn bind_surface_to_id(
        &mut self,
        identity: CellId,
        actor: &SurfaceRef,
    ) -> Result<(), RealmError> {
        let _ = self.id_identity(&identity)?; // NOT_FOUND before writing anything
        self.commit(RealmOp::BindSurfaceToId {
            identity: *identity.as_bytes(),
            actor: actor.into(),
        })
    }

    /// Register a guardian set on an identity named by its cell-id (durable).
    pub fn register_guardians_by_id(
        &mut self,
        identity: CellId,
        guardians: &[[u8; 32]],
        threshold: u32,
    ) -> Result<(), RealmError> {
        let _ = self.id_identity(&identity)?;
        self.commit(RealmOp::RegisterGuardiansById {
            identity: *identity.as_bytes(),
            guardians: guardians.to_vec(),
            threshold,
        })
    }

    /// Rotate an identity named by its cell-id (durable). The node does NOT sign —
    /// the holder's hybrid signature arrives on the wire and realm-model's gate
    /// verifies signer-commitment == committed current key before the key advances.
    pub fn rotate_identity_by_id(
        &mut self,
        identity: CellId,
        new_key_commit: [u8; 32],
        sig: &HybridSig,
    ) -> Result<u64, RealmError> {
        let _ = self.id_identity(&identity)?;
        self.commit(RealmOp::RotateById {
            identity: *identity.as_bytes(),
            new_key_commit,
            sig: sig.into(),
        })?;
        Ok(self.world.identity_epoch(&identity))
    }

    /// Recover an identity named by its cell-id through its guardian quorum
    /// (durable). Below threshold the gate refuses and nothing is logged.
    pub fn recover_identity_by_id(
        &mut self,
        identity: CellId,
        new_key_commit: [u8; 32],
        guardian_sigs: &[HybridSig],
    ) -> Result<u64, RealmError> {
        let _ = self.id_identity(&identity)?;
        self.commit(RealmOp::RecoverById {
            identity: *identity.as_bytes(),
            new_key_commit,
            guardian_sigs: guardian_sigs.iter().map(HybridSigWire::from).collect(),
        })?;
        Ok(self.world.identity_epoch(&identity))
    }

    /// Bind a surface ref onto the identity minted from `principal_seed` (durable).
    pub fn bind_surface(
        &mut self,
        principal_seed: &str,
        actor: &SurfaceRef,
    ) -> Result<(), RealmError> {
        self.commit(RealmOp::BindSurface {
            principal_seed: principal_seed.to_string(),
            actor: actor.into(),
        })
    }

    /// Create a realm with the given membrane (durable). Returns the realm.
    pub fn create_realm(&mut self, name: &str, membrane: Membrane) -> Result<Realm, RealmError> {
        self.commit(RealmOp::CreateRealm {
            name: name.to_string(),
            membrane: membrane.as_u64() as u8,
        })?;
        Ok(self
            .realms
            .get(name)
            .cloned()
            .expect("realm present after successful create"))
    }

    /// List a ruleset root as committed law for a realm (durable).
    pub fn list_ruleset(&mut self, realm_name: &str, root: RulesetRoot) -> Result<(), RealmError> {
        self.commit(RealmOp::ListRuleset {
            realm_name: realm_name.to_string(),
            root,
        })
    }

    /// Unlist a ruleset root (durable) — deprecation; future turns citing it are
    /// refused.
    pub fn unlist_ruleset(
        &mut self,
        realm_name: &str,
        root: RulesetRoot,
    ) -> Result<(), RealmError> {
        self.commit(RealmOp::UnlistRuleset {
            realm_name: realm_name.to_string(),
            root,
        })
    }

    /// Open a child instance of a realm (durable). Returns the instance.
    pub fn open_instance(&mut self, realm_name: &str, seed: &str) -> Result<Instance, RealmError> {
        let realm_id = self.realm_id(realm_name)?;
        self.commit(RealmOp::OpenInstance {
            realm_name: realm_name.to_string(),
            seed: seed.to_string(),
        })?;
        // The instance id is deterministic from (realm_id, seed) — the exact seed
        // `RealmWorld::open_instance` derives — and the authoritative instance now
        // lives in the world. Reconstruct the caller-facing handle from public
        // reads (its pinned parent value is committed on the cell).
        let inst_id = realm_model::derive_cell_id(&format!(
            "realm-instance:{}:{seed}",
            hex32(realm_id.as_bytes())
        ));
        Ok(Instance {
            id: inst_id,
            realm: realm_id,
            seed: seed.to_string(),
            parent_pin: self.world.instance_parent_pin(&inst_id),
        })
    }

    /// Admit a realm turn THROUGH realm-model's gate (durable on success). A
    /// refusal (e.g. an unlisted `ruleset_root`) mutates nothing and is not logged.
    pub fn admit_turn(
        &mut self,
        actor: &SurfaceRef,
        instance: CellId,
        ruleset_root: RulesetRoot,
        effects: Vec<Effect>,
    ) -> Result<RealmReceipt, RealmError> {
        self.commit(RealmOp::Admit {
            actor: actor.into(),
            instance: *instance.as_bytes(),
            ruleset_root,
            effects,
        })?;
        Ok(self
            .world
            .receipts()
            .last()
            .cloned()
            .expect("receipt present after admitted turn"))
    }

    /// Convenience: play a single scoped `SetField` inside an instance (durable).
    pub fn play(
        &mut self,
        actor: &SurfaceRef,
        instance: CellId,
        ruleset_root: RulesetRoot,
        index: usize,
        value: u64,
    ) -> Result<RealmReceipt, RealmError> {
        self.admit_turn(
            actor,
            instance,
            ruleset_root,
            vec![Effect::SetField {
                cell: instance,
                index: index as u64,
                value: pack_u64(value),
            }],
        )
    }

    /// Settle an instance's certified result back into its realm (durable).
    pub fn settle(
        &mut self,
        actor: &SurfaceRef,
        instance: CellId,
        ruleset_root: RulesetRoot,
    ) -> Result<RealmReceipt, RealmError> {
        self.commit(RealmOp::Settle {
            actor: actor.into(),
            instance: *instance.as_bytes(),
            ruleset_root,
        })?;
        Ok(self
            .world
            .receipts()
            .last()
            .cloned()
            .expect("receipt present after settle"))
    }

    // ── §9.5 succession + guardian recovery (durable) ─────────────────────────

    /// Register (or replace) an identity's K-of-N guardian recovery set
    /// (durable). `guardians` are guardian key COMMITMENTS
    /// ([`realm_model::identity::commit_hybrid`]).
    pub fn register_guardians(
        &mut self,
        principal_seed: &str,
        guardians: &[[u8; 32]],
        threshold: u32,
    ) -> Result<(), RealmError> {
        // Refuse an unknown principal BEFORE writing anything to the log.
        let _ = self.identity_id(principal_seed)?;
        self.commit(RealmOp::RegisterGuardians {
            principal_seed: principal_seed.to_string(),
            guardians: guardians.to_vec(),
            threshold,
        })
    }

    /// ROTATE an identity's key: a succession hybrid-signed BY THE CURRENT KEY
    /// (durable on success). The node does not sign — the signature arrives from
    /// the holder and realm-model's gate checks signer-commitment == committed
    /// current key before the key advances. A refusal
    /// ([`Refused::WrongSuccessionKey`] / [`Refused::BadSuccessionSignature`])
    /// mutates nothing and is not logged.
    pub fn rotate_identity(
        &mut self,
        principal_seed: &str,
        new_key_commit: [u8; 32],
        sig: &HybridSig,
    ) -> Result<u64, RealmError> {
        let id = self.identity_id(principal_seed)?;
        self.commit(RealmOp::Rotate {
            principal_seed: principal_seed.to_string(),
            new_key_commit,
            sig: sig.into(),
        })?;
        Ok(self.world.identity_epoch(&id))
    }

    /// RECOVER a locked-out identity through its guardian quorum (durable on
    /// success). Below threshold the gate refuses
    /// ([`Refused::BelowGuardianThreshold`]) and nothing is logged.
    pub fn recover_identity(
        &mut self,
        principal_seed: &str,
        new_key_commit: [u8; 32],
        guardian_sigs: &[HybridSig],
    ) -> Result<u64, RealmError> {
        let id = self.identity_id(principal_seed)?;
        self.commit(RealmOp::Recover {
            principal_seed: principal_seed.to_string(),
            new_key_commit,
            guardian_sigs: guardian_sigs.iter().map(HybridSigWire::from).collect(),
        })?;
        Ok(self.world.identity_epoch(&id))
    }

    // ── read-only projections (for the ingress + the restart canary) ───────────

    /// Read-only access to the hosted world (surface resolution, catalog reads,
    /// realm/instance state).
    pub fn world(&self) -> &RealmWorld {
        &self.world
    }

    /// The head of the realm receipt chain (`None` before the first admitted turn).
    /// This is the value that survives a restart — the durable-realm canary.
    pub fn receipt_head(&self) -> Option<[u8; 32]> {
        self.world.receipts().last().map(|r| r.receipt_hash)
    }

    /// The number of admitted realm turns on the chain.
    pub fn receipt_count(&self) -> usize {
        self.world.receipts().len()
    }

    /// The durable realm-log length (== `receipt`-producing + setup ops persisted).
    pub fn durable_log_len(&self) -> u64 {
        self.next_index
    }

    /// Look up a realm's id by name (the node-side handle).
    pub fn realm_by_name(&self, name: &str) -> Option<Realm> {
        self.realms.get(name).cloned()
    }

    /// Every realm name the durable log created, sorted (the list ingress).
    pub fn realm_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.realms.keys().cloned().collect();
        names.sort();
        names
    }

    /// The realm's currently-listed ruleset roots. The node-side index supplies
    /// the CANDIDATES; every one is re-checked against the catalog CELL
    /// ([`RealmWorld::is_listed`]) before it is served, so the answer is
    /// cell-authoritative, not an index that can drift.
    pub fn listed_rulesets(&self, realm_name: &str) -> Vec<RulesetRoot> {
        let Some(realm) = self.realms.get(realm_name) else {
            return Vec::new();
        };
        self.listed
            .get(realm_name)
            .map(|set| {
                set.iter()
                    .copied()
                    .filter(|r| self.world.is_listed(&realm.id, r))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The (realm name, seed) an instance was opened under, if the node created
    /// it. `None` for an id this node never opened.
    pub fn instance_handle(&self, instance: &CellId) -> Option<(String, String)> {
        self.instances.get(instance).cloned()
    }

    /// Every instance this node opened under `realm_name`, in id order.
    pub fn instances_of(&self, realm_name: &str) -> Vec<(CellId, String)> {
        self.instances
            .iter()
            .filter(|(_, (rn, _))| rn == realm_name)
            .map(|(id, (_, seed))| (*id, seed.clone()))
            .collect()
    }

    /// The canonical identity minted from `principal_seed`, if this node minted
    /// it CUSTODIALLY. The seed is a node-side handle only and is never returned.
    pub fn identity_by_seed(&self, principal_seed: &str) -> Option<CanonicalIdentity> {
        self.identities.get(principal_seed).cloned()
    }

    /// The canonical identity named by its durable cell-id (the PUBLIC handle) —
    /// present for identities minted through EITHER path.
    pub fn identity_by_id(&self, identity: &CellId) -> Option<CanonicalIdentity> {
        self.identities_by_id.get(identity).cloned()
    }
}

fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

// =============================================================================
// THE HTTP INGRESS — `/realm*`
//
// The ORGANS service pattern (storage / trustline / channels / court / dkg):
// one `routes()` Router mounted inside the node's PROTECTED router in `api.rs`.
// Every write route drives the SAME `NodeRealms` gate the in-process path uses,
// so the catalog check / identity resolution / scope membrane and the durable
// `REALM_LOG` are shared — an HTTP caller gets no weaker (and no stronger) gate
// than the node's own code.
// =============================================================================

/// Every way a `/realm*` request can be refused. A refusal mutates nothing and
/// persists nothing (realm-model's refusals are total; the durable log only ever
/// receives an ADMITTED op).
#[derive(Debug)]
pub struct RealmRefusal(RealmError);

impl From<RealmError> for RealmRefusal {
    fn from(e: RealmError) -> Self {
        RealmRefusal(e)
    }
}

impl RealmRefusal {
    fn bad_request(detail: impl Into<String>) -> Self {
        RealmRefusal(RealmError::BadRequest(detail.into()))
    }

    fn not_found(detail: impl Into<String>) -> Self {
        RealmRefusal(RealmError::UnknownHandle(detail.into()))
    }

    fn status(&self) -> StatusCode {
        match &self.0 {
            // A gate refusal is a genuine CONFLICT with committed state
            // (uncatalogued law, a finalized instance, a membrane violation, a
            // wrong succession key) — the request was well-formed and REFUSED.
            RealmError::Refused(_) => StatusCode::CONFLICT,
            RealmError::UnknownHandle(_) => StatusCode::NOT_FOUND,
            RealmError::BadRequest(_) => StatusCode::BAD_REQUEST,
            RealmError::Store(_) => StatusCode::INTERNAL_SERVER_ERROR,
        }
    }

    /// A stable machine-readable reason. The catalog refusal
    /// (`ruleset-not-in-catalog`) is the deployed §9.2 tooth an ingress client
    /// keys on.
    fn reason(&self) -> &'static str {
        match &self.0 {
            RealmError::Refused(r) => match r {
                Refused::UnknownActor(_) => "unknown-actor",
                Refused::UnknownInstance(_) => "unknown-instance",
                Refused::InstanceFinalized(_) => "instance-finalized",
                Refused::RulesetNotInCatalog { .. } => "ruleset-not-in-catalog",
                Refused::OutsideInstanceScope { .. } => "outside-instance-scope",
                Refused::UnsupportedEffect => "unsupported-effect",
                Refused::Ledger(_) => "ledger-error",
                Refused::UnknownIdentity(_) => "unknown-identity",
                Refused::IdentityExists(_) => "identity-exists",
                Refused::WrongSuccessionKey { .. } => "wrong-succession-key",
                Refused::BadSuccessionSignature { .. } => "bad-succession-signature",
                Refused::BelowGuardianThreshold { .. } => "below-guardian-threshold",
                Refused::SettleConflict { .. } => "settle-conflict",
            },
            RealmError::UnknownHandle(_) => "unknown-handle",
            RealmError::BadRequest(_) => "bad-request",
            RealmError::Store(_) => "store-error",
        }
    }
}

impl IntoResponse for RealmRefusal {
    fn into_response(self) -> Response {
        let body = serde_json::json!({
            "error": self.0.to_string(),
            "reason": self.reason(),
        });
        (self.status(), Json(body)).into_response()
    }
}

/// The realm route surface. Mounted inside the node's PROTECTED router (bearer
/// gate) in `api.rs` — the same posture as the other ORGANS services. Read
/// routes are gated too: opening them publicly is ember's call, and fail-closed
/// is the conservative default.
pub fn routes() -> Router<NodeState> {
    Router::new()
        // realm lifecycle
        .route("/realm/create", post(post_create_realm))
        .route("/realm/list", get(get_realm_list))
        .route("/realm/status", get(get_realm_status))
        .route("/realm/read/{name}", get(get_realm_read))
        // committed law (§9.2)
        .route("/realm/ruleset/list", post(post_ruleset_list))
        .route("/realm/ruleset/unlist", post(post_ruleset_unlist))
        // instances (§9.4)
        .route("/realm/instance/open", post(post_instance_open))
        .route("/realm/instance/play", post(post_instance_play))
        .route("/realm/instance/turn", post(post_instance_turn))
        .route("/realm/instance/settle", post(post_instance_settle))
        .route("/realm/instance/read/{id}", get(get_instance_read))
        // canonical identity + succession (§9.5)
        .route("/realm/identity/mint", post(post_identity_mint))
        .route("/realm/identity/bind", post(post_identity_bind))
        .route("/realm/identity/resolve", get(get_identity_resolve))
        .route("/realm/identity/guardians", post(post_identity_guardians))
        .route("/realm/identity/rotate", post(post_identity_rotate))
        .route("/realm/identity/recover", post(post_identity_recover))
}

// ── wire helpers ─────────────────────────────────────────────────────────────

fn parse_hex32(label: &str, s: &str) -> Result<[u8; 32], RealmRefusal> {
    crate::trustline_service::hex_decode_32(s)
        .ok_or_else(|| RealmRefusal::bad_request(format!("{label} must be 32 bytes of hex: {s}")))
}

/// How a succession/bind request names its identity: the PUBLIC cell-id handle
/// (`identity`, the non-custodial default) OR the custodial `principal_seed`. A
/// non-custodially minted identity has no seed, so it is referenced by id.
enum IdRef {
    Id(CellId),
    Seed(String),
}

fn parse_id_ref(
    identity: &Option<String>,
    principal_seed: &Option<String>,
) -> Result<IdRef, RealmRefusal> {
    match (identity, principal_seed) {
        (Some(hex), None) => Ok(IdRef::Id(CellId::from_bytes(parse_hex32("identity", hex)?))),
        (None, Some(seed)) => Ok(IdRef::Seed(seed.clone())),
        (Some(_), Some(_)) => Err(RealmRefusal::bad_request(
            "specify EITHER identity (public, non-custodial) OR principal_seed (custodial), not both",
        )),
        (None, None) => Err(RealmRefusal::bad_request(
            "an identity handle is required: identity (public, non-custodial) or principal_seed (custodial)",
        )),
    }
}

fn parse_surface(s: &str) -> Result<Surface, RealmRefusal> {
    match s.to_ascii_lowercase().as_str() {
        "discord" => Ok(Surface::Discord),
        "web" => Ok(Surface::Web),
        "telegram" => Ok(Surface::Telegram),
        "wechat" => Ok(Surface::WeChat),
        "native" => Ok(Surface::Native),
        "other" => Ok(Surface::Other),
        other => Err(RealmRefusal::bad_request(format!(
            "unknown surface {other:?} (discord|web|telegram|wechat|native|other)"
        ))),
    }
}

fn surface_name(s: Surface) -> &'static str {
    match s {
        Surface::Discord => "discord",
        Surface::Web => "web",
        Surface::Telegram => "telegram",
        Surface::WeChat => "wechat",
        Surface::Native => "native",
        Surface::Other => "other",
    }
}

fn parse_membrane(s: &str) -> Result<Membrane, RealmRefusal> {
    match s.to_ascii_lowercase().as_str() {
        "pin-at-birth" | "pinatbirth" | "pin" => Ok(Membrane::PinAtBirth),
        "moving-parent" | "movingparent" | "moving" => Ok(Membrane::MovingParent),
        other => Err(RealmRefusal::bad_request(format!(
            "unknown membrane {other:?} (pin-at-birth|moving-parent)"
        ))),
    }
}

fn membrane_name(m: Membrane) -> &'static str {
    match m {
        Membrane::PinAtBirth => "pin-at-birth",
        Membrane::MovingParent => "moving-parent",
    }
}

fn status_name(s: InstanceStatus) -> &'static str {
    match s {
        InstanceStatus::Open => "open",
        InstanceStatus::Finalized => "finalized",
    }
}

/// The actor half every in-instance write carries: a per-surface ref the gate
/// RESOLVES to a canonical identity (§9.5 — the surface is derived, never
/// primary). An unbound surface is refused (`unknown-actor`).
#[derive(Deserialize)]
struct ActorSpec {
    /// `discord` | `web` | `telegram` | `wechat` | `native` | `other`.
    surface: String,
    /// The surface-local id (a Discord handle, a web session id, ...).
    local: String,
}

impl ActorSpec {
    fn to_ref(&self) -> Result<SurfaceRef, RealmRefusal> {
        Ok(SurfaceRef::new(parse_surface(&self.surface)?, &self.local))
    }
}

/// The receipt of an admitted realm turn, on the wire.
#[derive(Serialize)]
struct ReceiptWire {
    /// The RESOLVED canonical identity that acted (not the surface id).
    actor_identity: String,
    instance: String,
    realm: String,
    /// The law the turn cited, COMMITTED into the receipt (§9.2).
    ruleset_root: String,
    effects_hash: String,
    previous_receipt_hash: Option<String>,
    receipt_hash: String,
    /// The durable `REALM_LOG` length after this op — the caller's proof that
    /// the admission was persisted, not just applied.
    durable_log_len: u64,
}

impl ReceiptWire {
    fn new(r: &RealmReceipt, durable_log_len: u64) -> Self {
        ReceiptWire {
            actor_identity: hex32(r.actor_identity.as_bytes()),
            instance: hex32(r.instance.as_bytes()),
            realm: hex32(r.realm.as_bytes()),
            ruleset_root: hex32(&r.ruleset_root),
            effects_hash: hex32(&r.effects_hash),
            previous_receipt_hash: r.previous_receipt_hash.as_ref().map(hex32),
            receipt_hash: hex32(&r.receipt_hash),
            durable_log_len,
        }
    }
}

// ── realm lifecycle ──────────────────────────────────────────────────────────

#[derive(Deserialize)]
struct CreateRealmRequest {
    /// The realm's stable name (the node-side handle).
    name: String,
    /// `pin-at-birth` (default, deterministic) | `moving-parent` (live).
    #[serde(default)]
    membrane: Option<String>,
}

#[derive(Serialize)]
struct RealmWire {
    name: String,
    realm: String,
    catalog: String,
    membrane: &'static str,
    hoard: u64,
    epoch: u64,
    /// Roots the catalog CELL currently admits (§9.2 committed law).
    listed_rulesets: Vec<String>,
    instances: Vec<InstanceSummaryWire>,
}

#[derive(Serialize)]
struct InstanceSummaryWire {
    instance: String,
    seed: String,
    status: &'static str,
    result: u64,
    parent_pin: u64,
    /// What the instance SEES of its parent under this realm's membrane —
    /// the birth pin under `pin-at-birth`, the live head under `moving-parent`.
    visible_parent: u64,
}

fn realm_wire(r: &NodeRealms, name: &str) -> Option<RealmWire> {
    let realm = r.realm_by_name(name)?;
    let instances = r
        .instances_of(name)
        .into_iter()
        .map(|(id, seed)| InstanceSummaryWire {
            instance: hex32(id.as_bytes()),
            seed,
            status: status_name(r.world().instance_status(&id)),
            result: r.world().instance_result(&id),
            parent_pin: r.world().instance_parent_pin(&id),
            visible_parent: r.world().visible_parent(&id),
        })
        .collect();
    Some(RealmWire {
        name: name.to_string(),
        realm: hex32(realm.id.as_bytes()),
        catalog: hex32(realm.catalog.as_bytes()),
        // Read the membrane off the CELL, not the handle struct's mirror.
        membrane: membrane_name(r.world().membrane_of(&realm.id)),
        hoard: r.world().realm_hoard(&realm.id),
        epoch: r.world().realm_epoch(&realm.id),
        listed_rulesets: r.listed_rulesets(name).iter().map(hex32).collect(),
        instances,
    })
}

/// `POST /realm/create` — create a persistent realm (durable) with its committed
/// per-realm membrane.
async fn post_create_realm(
    State(state): State<NodeState>,
    Json(req): Json<CreateRealmRequest>,
) -> Result<Json<RealmWire>, RealmRefusal> {
    let membrane = match req.membrane.as_deref() {
        None => Membrane::PinAtBirth,
        Some(m) => parse_membrane(m)?,
    };
    let realms = state.realms();
    let mut r = realms.write().await;
    r.create_realm(&req.name, membrane)?;
    tracing::info!(
        realm = %req.name,
        membrane = membrane_name(membrane),
        "realm created through the HTTP ingress (durable REALM_LOG)"
    );
    Ok(Json(
        realm_wire(&r, &req.name).expect("realm present after successful create"),
    ))
}

/// `GET /realm/list` — every realm the durable log holds, with live cell state.
async fn get_realm_list(State(state): State<NodeState>) -> Json<Vec<RealmWire>> {
    let realms = state.realms();
    let r = realms.read().await;
    Json(
        r.realm_names()
            .iter()
            .filter_map(|n| realm_wire(&r, n))
            .collect(),
    )
}

/// `GET /realm/read/{name}` — one realm's durable state.
async fn get_realm_read(
    State(state): State<NodeState>,
    AxumPath(name): AxumPath<String>,
) -> Result<Json<RealmWire>, RealmRefusal> {
    let realms = state.realms();
    let r = realms.read().await;
    realm_wire(&r, &name)
        .map(Json)
        .ok_or_else(|| RealmRefusal::not_found(format!("realm {name}")))
}

#[derive(Serialize)]
struct RealmStatusWire {
    realms: usize,
    instances: usize,
    identities: usize,
    /// Admitted realm turns on the substrate's own receipt chain.
    receipt_count: usize,
    /// The head of that chain — the value that survives a node restart.
    receipt_head: Option<String>,
    /// The node's view of the durable log length.
    durable_log_len: u64,
    /// The STORE's view of the same length. A mismatch means the in-memory
    /// substrate and the durable log disagree — loud, never silent.
    durable_log_len_store: u64,
    durable_log_agrees: bool,
}

/// `GET /realm/status` — the substrate's durable position.
async fn get_realm_status(State(state): State<NodeState>) -> Json<RealmStatusWire> {
    // Lock order: realms THEN inner (the order the in-process canary uses).
    let realms = state.realms();
    let r = realms.read().await;
    let store_len = {
        let s = state.read().await;
        s.store.realm_log_len().unwrap_or_default()
    };
    let node_len = r.durable_log_len();
    Json(RealmStatusWire {
        realms: r.realm_names().len(),
        instances: r.instances.len(),
        identities: r.identities.len(),
        receipt_count: r.receipt_count(),
        receipt_head: r.receipt_head().as_ref().map(hex32),
        durable_log_len: node_len,
        durable_log_len_store: store_len,
        durable_log_agrees: node_len == store_len,
    })
}

// ── committed law (§9.2) ─────────────────────────────────────────────────────

#[derive(Deserialize)]
struct RulesetRequest {
    /// Realm name.
    realm: String,
    /// The 32-byte ruleset root, hex.
    ruleset_root: String,
}

#[derive(Serialize)]
struct RulesetResponse {
    realm: String,
    ruleset_root: String,
    /// Read back off the catalog CELL after the write (the authority).
    listed: bool,
    durable_log_len: u64,
}

/// `POST /realm/ruleset/list` — admit a ruleset root as this realm's law
/// (durable). A turn may then cite it; an unlisted root is refused.
async fn post_ruleset_list(
    State(state): State<NodeState>,
    Json(req): Json<RulesetRequest>,
) -> Result<Json<RulesetResponse>, RealmRefusal> {
    let root = parse_hex32("ruleset_root", &req.ruleset_root)?;
    let realms = state.realms();
    let mut r = realms.write().await;
    r.list_ruleset(&req.realm, root)?;
    let realm_id = r
        .realm_by_name(&req.realm)
        .ok_or_else(|| RealmRefusal::not_found(format!("realm {}", req.realm)))?
        .id;
    Ok(Json(RulesetResponse {
        realm: req.realm.clone(),
        ruleset_root: hex32(&root),
        listed: r.world().is_listed(&realm_id, &root),
        durable_log_len: r.durable_log_len(),
    }))
}

/// `POST /realm/ruleset/unlist` — deprecate a root (durable). The canary
/// property: the SAME turn that was admitted is refused afterwards, because the
/// gate reads live committed catalog state.
async fn post_ruleset_unlist(
    State(state): State<NodeState>,
    Json(req): Json<RulesetRequest>,
) -> Result<Json<RulesetResponse>, RealmRefusal> {
    let root = parse_hex32("ruleset_root", &req.ruleset_root)?;
    let realms = state.realms();
    let mut r = realms.write().await;
    r.unlist_ruleset(&req.realm, root)?;
    let realm_id = r
        .realm_by_name(&req.realm)
        .ok_or_else(|| RealmRefusal::not_found(format!("realm {}", req.realm)))?
        .id;
    Ok(Json(RulesetResponse {
        realm: req.realm.clone(),
        ruleset_root: hex32(&root),
        listed: r.world().is_listed(&realm_id, &root),
        durable_log_len: r.durable_log_len(),
    }))
}

// ── instances (§9.4) ─────────────────────────────────────────────────────────

#[derive(Deserialize)]
struct OpenInstanceRequest {
    /// Realm name.
    realm: String,
    /// The immutable seed that scopes the instance (a day seed, a match seed).
    seed: String,
}

#[derive(Serialize)]
struct InstanceWire {
    instance: String,
    realm: String,
    realm_name: Option<String>,
    seed: String,
    status: &'static str,
    result: u64,
    /// The realm value PINNED at birth (the membrane snapshot).
    parent_pin: u64,
    /// What the instance sees of its parent NOW under the realm's membrane.
    visible_parent: u64,
    membrane: &'static str,
    durable_log_len: u64,
}

fn instance_wire(r: &NodeRealms, id: CellId) -> Option<InstanceWire> {
    let (realm_name, seed) = r.instance_handle(&id)?;
    let realm = r.realm_by_name(&realm_name)?;
    Some(InstanceWire {
        instance: hex32(id.as_bytes()),
        realm: hex32(realm.id.as_bytes()),
        realm_name: Some(realm_name),
        seed,
        status: status_name(r.world().instance_status(&id)),
        result: r.world().instance_result(&id),
        parent_pin: r.world().instance_parent_pin(&id),
        visible_parent: r.world().visible_parent(&id),
        membrane: membrane_name(r.world().membrane_of(&realm.id)),
        durable_log_len: r.durable_log_len(),
    })
}

/// `POST /realm/instance/open` — open a scoped child instance (durable). Pins
/// the parent per the realm's committed membrane.
async fn post_instance_open(
    State(state): State<NodeState>,
    Json(req): Json<OpenInstanceRequest>,
) -> Result<Json<InstanceWire>, RealmRefusal> {
    let realms = state.realms();
    let mut r = realms.write().await;
    let inst = r.open_instance(&req.realm, &req.seed)?;
    Ok(Json(
        instance_wire(&r, inst.id).expect("instance present after successful open"),
    ))
}

/// `GET /realm/instance/read/{id}` — one instance's scoped state.
async fn get_instance_read(
    State(state): State<NodeState>,
    AxumPath(id): AxumPath<String>,
) -> Result<Json<InstanceWire>, RealmRefusal> {
    let id = CellId::from_bytes(parse_hex32("instance", &id)?);
    let realms = state.realms();
    let r = realms.read().await;
    instance_wire(&r, id)
        .map(Json)
        .ok_or_else(|| RealmRefusal::not_found(format!("instance {}", hex32(id.as_bytes()))))
}

#[derive(Deserialize)]
struct PlayRequest {
    /// Instance cell id, hex.
    instance: String,
    /// The law this turn cites — gated against the realm's catalog.
    ruleset_root: String,
    #[serde(flatten)]
    actor: ActorSpec,
    /// Which instance field to set.
    index: u64,
    /// The u64 value to pack into it.
    value: u64,
}

/// `POST /realm/instance/play` — the convenience single-`SetField` turn, admitted
/// THROUGH realm-model's gate (durable on success). An uncatalogued
/// `ruleset_root` is refused (`ruleset-not-in-catalog`) and persists nothing.
async fn post_instance_play(
    State(state): State<NodeState>,
    Json(req): Json<PlayRequest>,
) -> Result<Json<ReceiptWire>, RealmRefusal> {
    let instance = CellId::from_bytes(parse_hex32("instance", &req.instance)?);
    let root = parse_hex32("ruleset_root", &req.ruleset_root)?;
    let actor = req.actor.to_ref()?;
    let realms = state.realms();
    let mut r = realms.write().await;
    let receipt = r.play(&actor, instance, root, req.index as usize, req.value)?;
    let len = r.durable_log_len();
    Ok(Json(ReceiptWire::new(&receipt, len)))
}

#[derive(Deserialize)]
struct TurnRequest {
    /// Instance cell id, hex.
    instance: String,
    /// The law this turn cites.
    ruleset_root: String,
    #[serde(flatten)]
    actor: ActorSpec,
    /// The typed effects (realm-model interprets `Effect::SetField`; anything
    /// else is refused `unsupported-effect`). Effects that reach outside the
    /// instance are refused `outside-instance-scope` (the membrane).
    effects: Vec<Effect>,
}

/// `POST /realm/instance/turn` — the general gate-routed admission: an arbitrary
/// effect vector inside an instance. Same gate, same durable log.
async fn post_instance_turn(
    State(state): State<NodeState>,
    Json(req): Json<TurnRequest>,
) -> Result<Json<ReceiptWire>, RealmRefusal> {
    let instance = CellId::from_bytes(parse_hex32("instance", &req.instance)?);
    let root = parse_hex32("ruleset_root", &req.ruleset_root)?;
    let actor = req.actor.to_ref()?;
    let realms = state.realms();
    let mut r = realms.write().await;
    let receipt = r.admit_turn(&actor, instance, root, req.effects)?;
    let len = r.durable_log_len();
    Ok(Json(ReceiptWire::new(&receipt, len)))
}

#[derive(Deserialize)]
struct SettleRequest {
    /// Instance cell id, hex.
    instance: String,
    /// The law the settle cites.
    ruleset_root: String,
    #[serde(flatten)]
    actor: ActorSpec,
}

#[derive(Serialize)]
struct SettleResponse {
    receipt: ReceiptWire,
    /// The realm AFTER the settle crossed the membrane.
    realm: RealmWire,
}

/// `POST /realm/instance/settle` — cross the membrane: the instance's certified
/// RESULT advances the realm's durable hoard/epoch and the instance finalizes
/// (durable). Only this path may write the realm cell.
async fn post_instance_settle(
    State(state): State<NodeState>,
    Json(req): Json<SettleRequest>,
) -> Result<Json<SettleResponse>, RealmRefusal> {
    let instance = CellId::from_bytes(parse_hex32("instance", &req.instance)?);
    let root = parse_hex32("ruleset_root", &req.ruleset_root)?;
    let actor = req.actor.to_ref()?;
    let realms = state.realms();
    let mut r = realms.write().await;
    let realm_name = r
        .instance_handle(&instance)
        .map(|(n, _)| n)
        .ok_or_else(|| {
            RealmRefusal::not_found(format!("instance {}", hex32(instance.as_bytes())))
        })?;
    let receipt = r.settle(&actor, instance, root)?;
    let len = r.durable_log_len();
    Ok(Json(SettleResponse {
        receipt: ReceiptWire::new(&receipt, len),
        realm: realm_wire(&r, &realm_name).expect("realm present after settle"),
    }))
}

// ── canonical identity + succession (§9.5) ───────────────────────────────────

#[derive(Deserialize)]
struct MintIdentityRequest {
    /// A human-meaningful label for the principal (NOT a surface id).
    label: String,
    /// NON-CUSTODIAL (the DEFAULT): the holder's birth hybrid PUBLIC key — the
    /// ed25519 half (32 bytes hex) and the ML-DSA-65 half (hex). The holder
    /// generated the key OFF node and keeps the seed; only these public bytes
    /// cross. When present, the mint is non-custodial and no seed is involved.
    birth_ed_pk: Option<String>,
    birth_ml_pk: Option<String>,
    /// ⚠ CUSTODIAL (retained, server-custodial use only): realm-model derives the
    /// identity's hybrid-PQ BIRTH KEY from this seed, so supplying it HANDS THE
    /// NODE key material. The node never echoes or logs it, but the non-custodial
    /// `birth_ed_pk`/`birth_ml_pk` path is preferred. Mutually exclusive with the
    /// public-key fields.
    principal_seed: Option<String>,
}

#[derive(Serialize)]
struct IdentityWire {
    /// The durable canonical principal — STABLE across surface rebindings and
    /// key rotation/recovery.
    identity: String,
    label: String,
    /// ed25519 public key of the BIRTH key (informational).
    principal_pk: String,
    /// The genesis anchor of the succession chain.
    birth_key_commit: String,
    /// The commitment to the CURRENT key, read off the identity cell.
    current_key_commit: Option<String>,
    /// Succession epoch (1 at genesis, +1 per rotation/recovery).
    epoch: u64,
    /// The endpoint a resolver reaches by walking the succession chain from
    /// genesis. Equals `current_key_commit` on a sound chain.
    followed_key_commit: Option<String>,
    durable_log_len: u64,
}

fn identity_wire(r: &NodeRealms, id: &CanonicalIdentity) -> IdentityWire {
    IdentityWire {
        identity: hex32(id.id.as_bytes()),
        label: id.label.clone(),
        principal_pk: hex32(&id.principal_pk),
        birth_key_commit: hex32(&id.birth_key_commit),
        current_key_commit: r.world().current_key_commit(&id.id).as_ref().map(hex32),
        epoch: r.world().identity_epoch(&id.id),
        followed_key_commit: r.world().follow_chain(&id.id).as_ref().map(hex32),
        durable_log_len: r.durable_log_len(),
    }
}

/// `POST /realm/identity/mint` — mint a canonical identity (durable). It exists
/// FIRST; surfaces bind ONTO it (§9.5 — there is deliberately no
/// identity-from-surface constructor).
///
/// NON-CUSTODIAL by DEFAULT: supply the holder's birth hybrid PUBLIC key
/// (`birth_ed_pk` + `birth_ml_pk`) — the holder keeps the seed off-node and only
/// public bytes cross. The retained `principal_seed` path is CUSTODIAL
/// (server-custodial use only) and mutually exclusive with the public-key fields.
async fn post_identity_mint(
    State(state): State<NodeState>,
    Json(req): Json<MintIdentityRequest>,
) -> Result<Json<IdentityWire>, RealmRefusal> {
    let realms = state.realms();
    let mut r = realms.write().await;
    let id = match (&req.birth_ed_pk, &req.birth_ml_pk, &req.principal_seed) {
        // NON-CUSTODIAL (default): only the public birth key crosses.
        (Some(ed_hex), Some(ml_hex), None) => {
            let ed_pk = parse_hex32("birth_ed_pk", ed_hex)?;
            let ml_pk = hex_bytes("birth_ml_pk", ml_hex)?;
            let id = r.mint_identity_from_pubkey(&req.label, &ed_pk, &ml_pk)?;
            tracing::info!(
                label = %req.label,
                "canonical identity minted NON-CUSTODIALLY through the HTTP ingress (public key only)"
            );
            id
        }
        // CUSTODIAL (retained): the node derives the birth key from the seed.
        (None, None, Some(seed)) => {
            let id = r.mint_identity(&req.label, seed)?;
            // The label is safe to log; `principal_seed` is KEY MATERIAL and is not.
            tracing::info!(
                label = %req.label,
                "canonical identity minted CUSTODIALLY through the HTTP ingress"
            );
            id
        }
        (Some(_), None, _) | (None, Some(_), _) => {
            return Err(RealmRefusal::bad_request(
                "non-custodial mint needs BOTH birth_ed_pk and birth_ml_pk",
            ));
        }
        (Some(_), Some(_), Some(_)) => {
            return Err(RealmRefusal::bad_request(
                "specify EITHER the non-custodial birth public key OR a custodial principal_seed, not both",
            ));
        }
        (None, None, None) => {
            return Err(RealmRefusal::bad_request(
                "mint needs the non-custodial birth_ed_pk + birth_ml_pk (preferred) or a custodial principal_seed",
            ));
        }
    };
    Ok(Json(identity_wire(&r, &id)))
}

#[derive(Deserialize)]
struct BindSurfaceRequest {
    /// The PUBLIC handle of an already-minted identity: its cell-id hex (the
    /// non-custodial default). Mutually exclusive with `principal_seed`.
    identity: Option<String>,
    /// The CUSTODIAL node-side handle of an already-minted identity.
    principal_seed: Option<String>,
    #[serde(flatten)]
    actor: ActorSpec,
}

#[derive(Serialize)]
struct BindResponse {
    identity: IdentityWire,
    surface: &'static str,
    local: String,
}

/// `POST /realm/identity/bind` — bind a surface ref onto an existing canonical
/// identity (durable). The binding cell's state IS the canonical id, so
/// resolution is cell-backed.
async fn post_identity_bind(
    State(state): State<NodeState>,
    Json(req): Json<BindSurfaceRequest>,
) -> Result<Json<BindResponse>, RealmRefusal> {
    let actor = req.actor.to_ref()?;
    let idref = parse_id_ref(&req.identity, &req.principal_seed)?;
    let realms = state.realms();
    let mut r = realms.write().await;
    let id = match idref {
        IdRef::Id(cell) => {
            r.bind_surface_to_id(cell, &actor)?;
            r.identity_by_id(&cell)
        }
        IdRef::Seed(seed) => {
            r.bind_surface(&seed, &actor)?;
            r.identity_by_seed(&seed)
        }
    }
    .ok_or_else(|| RealmRefusal::not_found("identity (unminted)"))?;
    Ok(Json(BindResponse {
        identity: identity_wire(&r, &id),
        surface: surface_name(actor.surface),
        local: actor.local.clone(),
    }))
}

#[derive(Deserialize)]
struct ResolveQuery {
    surface: String,
    local: String,
}

/// `GET /realm/identity/resolve?surface=..&local=..` — the §9.5 resolution a
/// per-surface host should perform: surface ref → durable canonical identity. An
/// unbound surface is NOT an identity (404).
async fn get_identity_resolve(
    State(state): State<NodeState>,
    axum::extract::Query(q): axum::extract::Query<ResolveQuery>,
) -> Result<Json<IdentityWire>, RealmRefusal> {
    let actor = SurfaceRef::new(parse_surface(&q.surface)?, &q.local);
    let realms = state.realms();
    let r = realms.read().await;
    let id = r
        .world()
        .resolve_surface(&actor)
        .ok_or_else(|| RealmRefusal::not_found("surface is not bound to any canonical identity"))?;
    Ok(Json(identity_wire(&r, &id)))
}

#[derive(Deserialize)]
struct GuardiansRequest {
    /// PUBLIC cell-id handle (non-custodial default). Mutually exclusive with
    /// `principal_seed`.
    identity: Option<String>,
    /// CUSTODIAL handle.
    principal_seed: Option<String>,
    /// Guardian key COMMITMENTS (hex, 32 bytes each).
    guardians: Vec<String>,
    /// The K-of-N co-sign floor.
    threshold: u32,
}

#[derive(Serialize)]
struct GuardiansResponse {
    identity: String,
    guardians: usize,
    threshold: u32,
    durable_log_len: u64,
}

/// `POST /realm/identity/guardians` — register the K-of-N guardian recovery set
/// (durable). WHO may amend it in production is a named decision-for-ember.
async fn post_identity_guardians(
    State(state): State<NodeState>,
    Json(req): Json<GuardiansRequest>,
) -> Result<Json<GuardiansResponse>, RealmRefusal> {
    let guardians = req
        .guardians
        .iter()
        .map(|g| parse_hex32("guardian commitment", g))
        .collect::<Result<Vec<_>, _>>()?;
    let idref = parse_id_ref(&req.identity, &req.principal_seed)?;
    let realms = state.realms();
    let mut r = realms.write().await;
    let id = match idref {
        IdRef::Id(cell) => {
            r.register_guardians_by_id(cell, &guardians, req.threshold)?;
            r.identity_by_id(&cell)
        }
        IdRef::Seed(seed) => {
            r.register_guardians(&seed, &guardians, req.threshold)?;
            r.identity_by_seed(&seed)
        }
    }
    .ok_or_else(|| RealmRefusal::not_found("identity (unminted)"))?;
    Ok(Json(GuardiansResponse {
        identity: hex32(id.id.as_bytes()),
        guardians: guardians.len(),
        threshold: req.threshold,
        durable_log_len: r.durable_log_len(),
    }))
}

/// A hybrid signature on the wire (hex halves). The NODE NEVER SIGNS a
/// succession — the holder (or a guardian) does, and realm-model's gate verifies.
#[derive(Deserialize)]
struct SigSpec {
    ed_pk: String,
    ml_pk: String,
    ed_sig: String,
    ml_sig: String,
}

fn hex_bytes(label: &str, s: &str) -> Result<Vec<u8>, RealmRefusal> {
    if !s.is_ascii() || !s.len().is_multiple_of(2) {
        return Err(RealmRefusal::bad_request(format!("{label} must be hex")));
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect::<Option<Vec<u8>>>()
        .ok_or_else(|| RealmRefusal::bad_request(format!("{label} must be hex")))
}

impl SigSpec {
    fn to_sig(&self) -> Result<HybridSig, RealmRefusal> {
        let ed_sig: [u8; 64] = hex_bytes("ed_sig", &self.ed_sig)?
            .as_slice()
            .try_into()
            .map_err(|_| RealmRefusal::bad_request("ed_sig must be 64 bytes"))?;
        Ok(HybridSig {
            ed_pk: parse_hex32("ed_pk", &self.ed_pk)?,
            ml_pk: hex_bytes("ml_pk", &self.ml_pk)?,
            ed_sig,
            ml_sig: hex_bytes("ml_sig", &self.ml_sig)?,
        })
    }
}

#[derive(Deserialize)]
struct RotateRequest {
    /// PUBLIC cell-id handle (non-custodial default). Mutually exclusive with
    /// `principal_seed`.
    identity: Option<String>,
    /// CUSTODIAL handle.
    principal_seed: Option<String>,
    /// The successor key's commitment, hex.
    new_key_commit: String,
    /// The hybrid signature BY THE CURRENT KEY over the canonical succession
    /// message (`realm_model::identity::succession_message`, kind `SelfSigned`).
    sig: SigSpec,
}

/// `POST /realm/identity/rotate` — advance the identity's committed current key
/// (durable). The id does NOT change, so every surface binding still resolves to
/// the same canonical identity across the rotation. A non-current signer is
/// refused `wrong-succession-key`.
async fn post_identity_rotate(
    State(state): State<NodeState>,
    Json(req): Json<RotateRequest>,
) -> Result<Json<IdentityWire>, RealmRefusal> {
    let new_commit = parse_hex32("new_key_commit", &req.new_key_commit)?;
    let sig = req.sig.to_sig()?;
    let idref = parse_id_ref(&req.identity, &req.principal_seed)?;
    let realms = state.realms();
    let mut r = realms.write().await;
    let id = match idref {
        IdRef::Id(cell) => {
            r.rotate_identity_by_id(cell, new_commit, &sig)?;
            r.identity_by_id(&cell)
        }
        IdRef::Seed(seed) => {
            r.rotate_identity(&seed, new_commit, &sig)?;
            r.identity_by_seed(&seed)
        }
    }
    .ok_or_else(|| RealmRefusal::not_found("identity (unminted)"))?;
    Ok(Json(identity_wire(&r, &id)))
}

#[derive(Deserialize)]
struct RecoverRequest {
    /// PUBLIC cell-id handle (non-custodial default). Mutually exclusive with
    /// `principal_seed`.
    identity: Option<String>,
    /// CUSTODIAL handle.
    principal_seed: Option<String>,
    new_key_commit: String,
    /// Guardian co-signs over the canonical recovery message (kind
    /// `GuardianRecovery`). DISTINCT registered guardians are counted.
    guardian_sigs: Vec<SigSpec>,
}

/// `POST /realm/identity/recover` — a K-of-N guardian quorum succeeds a
/// locked-out identity (durable). Below threshold is refused
/// `below-guardian-threshold` and persists nothing.
async fn post_identity_recover(
    State(state): State<NodeState>,
    Json(req): Json<RecoverRequest>,
) -> Result<Json<IdentityWire>, RealmRefusal> {
    let new_commit = parse_hex32("new_key_commit", &req.new_key_commit)?;
    let sigs = req
        .guardian_sigs
        .iter()
        .map(|s| s.to_sig())
        .collect::<Result<Vec<_>, _>>()?;
    let idref = parse_id_ref(&req.identity, &req.principal_seed)?;
    let realms = state.realms();
    let mut r = realms.write().await;
    let id = match idref {
        IdRef::Id(cell) => {
            r.recover_identity_by_id(cell, new_commit, &sigs)?;
            r.identity_by_id(&cell)
        }
        IdRef::Seed(seed) => {
            r.recover_identity(&seed, new_commit, &sigs)?;
            r.identity_by_seed(&seed)
        }
    }
    .ok_or_else(|| RealmRefusal::not_found("identity (unminted)"))?;
    Ok(Json(identity_wire(&r, &id)))
}

// =============================================================================
// Tests — the realm substrate DRIVEN THROUGH THE REAL ROUTER
//
// These are the ingress twin of `state.rs`'s in-process canary
// (`realm_created_through_node_survives_restart_and_refuses_false_catalog`):
// the same properties, but every operation goes over the HTTP surface.
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use http_body_util::BodyExt;
    use realm_model::identity::{HybridKey, SuccessionKind, succession_message};
    use tower::ServiceExt;

    async fn post_json(
        state: &NodeState,
        uri: &str,
        body: serde_json::Value,
    ) -> (StatusCode, serde_json::Value) {
        let app = routes().with_state(state.clone());
        let resp = app
            .oneshot(
                Request::builder()
                    .uri(uri)
                    .method("POST")
                    .header("content-type", "application/json")
                    .body(Body::from(body.to_string()))
                    .unwrap(),
            )
            .await
            .unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let json = serde_json::from_slice(&bytes).unwrap_or(serde_json::json!({}));
        (status, json)
    }

    async fn get_json(state: &NodeState, uri: &str) -> (StatusCode, serde_json::Value) {
        let app = routes().with_state(state.clone());
        let resp = app
            .oneshot(Request::builder().uri(uri).body(Body::empty()).unwrap())
            .await
            .unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let json = serde_json::from_slice(&bytes).unwrap_or(serde_json::json!({}));
        (status, json)
    }

    async fn realm_status(state: &NodeState) -> serde_json::Value {
        let (status, json) = get_json(state, "/realm/status").await;
        assert_eq!(status, StatusCode::OK, "status: {json}");
        json
    }

    /// ⚑ THE INGRESS CANARY. A realm built ENTIRELY through the HTTP routes —
    /// identity mint, surface bind, realm create, ruleset list, instance open,
    /// play, settle — survives a real node restart on the durable `REALM_LOG`;
    /// and a turn citing an UNCATALOGUED `ruleset_root` is REFUSED over HTTP
    /// (`ruleset-not-in-catalog`) while persisting NOTHING, before AND after the
    /// restart.
    #[tokio::test]
    async fn realm_through_http_ingress_survives_restart_and_refuses_uncatalogued_ruleset() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let key_bytes = [37u8; 32];
        let law = hex32(blake3::hash(b"http-descent-v1").as_bytes());
        let rogue = hex32(blake3::hash(b"http-rogue-v1").as_bytes());
        let actor = serde_json::json!({ "surface": "discord", "local": "pip-4242" });

        let pre_head;
        let pre_log_len;
        let identity_id;
        let instance_b;
        {
            let state = crate::state::NodeState::with_cclerk(tmp.path(), vec![], key_bytes)
                .expect("create node state");

            // ── §9.5: the canonical identity exists FIRST; the surface binds ONTO it.
            let (st, minted) = post_json(
                &state,
                "/realm/identity/mint",
                serde_json::json!({ "label": "player-one", "principal_seed": "http-seed-p1" }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "mint: {minted}");
            identity_id = minted["identity"].as_str().unwrap().to_string();
            assert_eq!(minted["epoch"], 1, "genesis succession epoch");
            assert_eq!(
                minted["current_key_commit"], minted["birth_key_commit"],
                "at genesis the current key IS the birth key"
            );

            let (st, bound) = post_json(
                &state,
                "/realm/identity/bind",
                serde_json::json!({
                    "principal_seed": "http-seed-p1",
                    "surface": "discord",
                    "local": "pip-4242",
                }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "bind: {bound}");
            assert_eq!(bound["identity"]["identity"], identity_id);

            // ── §9.4: the persistent realm + §9.2 its committed law.
            let (st, realm) = post_json(
                &state,
                "/realm/create",
                serde_json::json!({ "name": "http-burrow", "membrane": "pin-at-birth" }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "create: {realm}");
            assert_eq!(realm["membrane"], "pin-at-birth");
            assert_eq!(realm["hoard"], 0);

            let (st, listed) = post_json(
                &state,
                "/realm/ruleset/list",
                serde_json::json!({ "realm": "http-burrow", "ruleset_root": law }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "list ruleset: {listed}");
            assert_eq!(listed["listed"], true, "read back off the catalog CELL");

            // ── open, play, settle — the whole instance lifecycle over HTTP.
            let (st, inst_a) = post_json(
                &state,
                "/realm/instance/open",
                serde_json::json!({ "realm": "http-burrow", "seed": "day-1" }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "open a: {inst_a}");
            assert_eq!(inst_a["parent_pin"], 0, "instance A pins parent hoard 0");
            assert_eq!(inst_a["status"], "open");
            let inst_a_id = inst_a["instance"].as_str().unwrap().to_string();

            let mut play = actor.clone();
            play["instance"] = serde_json::json!(inst_a_id);
            play["ruleset_root"] = serde_json::json!(law);
            play["index"] = serde_json::json!(realm_model::instance::field::RESULT as u64);
            play["value"] = serde_json::json!(40u64);
            let (st, receipt) = post_json(&state, "/realm/instance/play", play).await;
            assert_eq!(st, StatusCode::OK, "play: {receipt}");
            assert_eq!(
                receipt["actor_identity"], identity_id,
                "the receipt is attributed to the RESOLVED canonical identity, not the surface"
            );
            assert_eq!(
                receipt["ruleset_root"], law,
                "the cited law is COMMITTED into the receipt"
            );

            let mut settle = actor.clone();
            settle["instance"] = serde_json::json!(inst_a_id);
            settle["ruleset_root"] = serde_json::json!(law);
            let (st, settled) = post_json(&state, "/realm/instance/settle", settle).await;
            assert_eq!(st, StatusCode::OK, "settle: {settled}");
            assert_eq!(settled["realm"]["hoard"], 40, "the realm accrued 40");
            assert_eq!(settled["realm"]["epoch"], 1);

            // ── THE DEPLOYED REFUSAL, over HTTP: an unlisted ruleset_root.
            let (st, inst_b) = post_json(
                &state,
                "/realm/instance/open",
                serde_json::json!({ "realm": "http-burrow", "seed": "day-2" }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "open b: {inst_b}");
            instance_b = inst_b["instance"].as_str().unwrap().to_string();

            let before = realm_status(&state).await;
            let len_before = before["durable_log_len"].as_u64().unwrap();
            assert_eq!(
                before["durable_log_len_store"].as_u64().unwrap(),
                len_before,
                "the node and the store agree on the durable log length"
            );

            let mut bad = actor.clone();
            bad["instance"] = serde_json::json!(instance_b);
            bad["ruleset_root"] = serde_json::json!(rogue);
            bad["index"] = serde_json::json!(realm_model::instance::field::RESULT as u64);
            bad["value"] = serde_json::json!(1u64);
            let (st, refusal) = post_json(&state, "/realm/instance/play", bad).await;
            assert_eq!(
                st,
                StatusCode::CONFLICT,
                "an uncatalogued ruleset_root is REFUSED over HTTP: {refusal}"
            );
            assert_eq!(
                refusal["reason"], "ruleset-not-in-catalog",
                "the §9.2 gate refusal reaches the wire verbatim: {refusal}"
            );

            let after = realm_status(&state).await;
            assert_eq!(
                after["durable_log_len"].as_u64().unwrap(),
                len_before,
                "a REFUSED HTTP realm turn persists NOTHING"
            );
            assert_eq!(
                after["durable_log_len_store"].as_u64().unwrap(),
                len_before,
                "the durable REALM_LOG did not grow on the refused HTTP turn"
            );
            assert!(after["durable_log_agrees"].as_bool().unwrap());

            pre_head = after["receipt_head"].as_str().unwrap().to_string();
            pre_log_len = len_before;
        }

        // ── RESTART ── reopen the SAME data dir; drive the reads over HTTP.
        let restored = crate::state::NodeState::with_cclerk(tmp.path(), vec![], key_bytes)
            .expect("restore node state");

        let status = realm_status(&restored).await;
        assert_eq!(
            status["receipt_head"].as_str().unwrap(),
            pre_head,
            "the realm receipt-chain head created over HTTP survives the node restart"
        );
        assert_eq!(status["durable_log_len"].as_u64().unwrap(), pre_log_len);
        assert!(status["durable_log_agrees"].as_bool().unwrap());

        let (st, realm) = get_json(&restored, "/realm/read/http-burrow").await;
        assert_eq!(st, StatusCode::OK, "read realm after restart: {realm}");
        assert_eq!(
            realm["hoard"], 40,
            "the persistent realm's durable hoard survived the restart"
        );
        assert_eq!(realm["epoch"], 1);
        assert_eq!(
            realm["listed_rulesets"],
            serde_json::json!([law]),
            "the committed law survived; the rogue root is not law"
        );
        assert_eq!(
            realm["instances"].as_array().unwrap().len(),
            2,
            "both instances reloaded from the durable log"
        );

        let (st, list) = get_json(&restored, "/realm/list").await;
        assert_eq!(st, StatusCode::OK, "list: {list}");
        assert_eq!(list.as_array().unwrap().len(), 1);

        // The canonical identity still resolves FROM ITS SURFACE across the reboot.
        let (st, resolved) = get_json(
            &restored,
            "/realm/identity/resolve?surface=discord&local=pip-4242",
        )
        .await;
        assert_eq!(st, StatusCode::OK, "resolve after restart: {resolved}");
        assert_eq!(resolved["identity"], identity_id);
        assert_eq!(resolved["label"], "player-one");

        // An unbound surface is NOT an identity.
        let (st, _) = get_json(
            &restored,
            "/realm/identity/resolve?surface=discord&local=nobody",
        )
        .await;
        assert_eq!(
            st,
            StatusCode::NOT_FOUND,
            "an unbound surface resolves to nothing"
        );

        // And the rogue root is STILL refused after the restart (the gate reads
        // live committed catalog state, reconstructed from the durable log).
        let mut bad = actor.clone();
        bad["instance"] = serde_json::json!(instance_b);
        bad["ruleset_root"] = serde_json::json!(rogue);
        bad["index"] = serde_json::json!(realm_model::instance::field::RESULT as u64);
        bad["value"] = serde_json::json!(1u64);
        let (st, refusal) = post_json(&restored, "/realm/instance/play", bad).await;
        assert_eq!(
            st,
            StatusCode::CONFLICT,
            "still refused after restart: {refusal}"
        );
        assert_eq!(refusal["reason"], "ruleset-not-in-catalog");
        let after = realm_status(&restored).await;
        assert_eq!(after["durable_log_len"].as_u64().unwrap(), pre_log_len);
    }

    /// The §9.2 CANARY over HTTP: unlisting a previously-listed root makes the
    /// SAME turn that was admitted be REFUSED — proving the gate reads live
    /// committed catalog state, not a compile-time set or a boot-time snapshot.
    #[tokio::test]
    async fn unlisting_law_over_http_refuses_the_same_turn_that_was_admitted() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = crate::state::NodeState::with_cclerk(tmp.path(), vec![], [39u8; 32])
            .expect("node state");
        let law = hex32(blake3::hash(b"http-unlist-law").as_bytes());
        let actor = serde_json::json!({ "surface": "web", "local": "sess-9" });

        post_json(
            &state,
            "/realm/identity/mint",
            serde_json::json!({ "label": "p", "principal_seed": "unlist-seed" }),
        )
        .await;
        post_json(
            &state,
            "/realm/identity/bind",
            serde_json::json!({ "principal_seed": "unlist-seed", "surface": "web", "local": "sess-9" }),
        )
        .await;
        post_json(
            &state,
            "/realm/create",
            serde_json::json!({ "name": "canary-realm" }),
        )
        .await;
        post_json(
            &state,
            "/realm/ruleset/list",
            serde_json::json!({ "realm": "canary-realm", "ruleset_root": law }),
        )
        .await;
        let (_, inst) = post_json(
            &state,
            "/realm/instance/open",
            serde_json::json!({ "realm": "canary-realm", "seed": "s" }),
        )
        .await;
        let inst_id = inst["instance"].as_str().unwrap().to_string();

        let mut play = actor.clone();
        play["instance"] = serde_json::json!(inst_id);
        play["ruleset_root"] = serde_json::json!(law);
        play["index"] = serde_json::json!(realm_model::instance::field::RESULT as u64);
        play["value"] = serde_json::json!(7u64);
        let (st, ok) = post_json(&state, "/realm/instance/play", play.clone()).await;
        assert_eq!(st, StatusCode::OK, "listed law admits the turn: {ok}");

        let (st, unlisted) = post_json(
            &state,
            "/realm/ruleset/unlist",
            serde_json::json!({ "realm": "canary-realm", "ruleset_root": law }),
        )
        .await;
        assert_eq!(st, StatusCode::OK, "unlist: {unlisted}");
        assert_eq!(unlisted["listed"], false);

        let before = realm_status(&state).await["durable_log_len"]
            .as_u64()
            .unwrap();
        let (st, refusal) = post_json(&state, "/realm/instance/play", play).await;
        assert_eq!(
            st,
            StatusCode::CONFLICT,
            "the SAME turn is now refused (live committed law): {refusal}"
        );
        assert_eq!(refusal["reason"], "ruleset-not-in-catalog");
        assert_eq!(
            realm_status(&state).await["durable_log_len"]
                .as_u64()
                .unwrap(),
            before,
            "the refused turn persisted nothing"
        );

        let (_, realm) = get_json(&state, "/realm/read/canary-realm").await;
        assert_eq!(
            realm["listed_rulesets"],
            serde_json::json!([]),
            "the unlisted root is gone from the served catalog"
        );
    }

    /// ⚑ SUCCESSION IS IN THE DURABLE LOG. Hybrid-PQ rotation and K-of-N
    /// guardian recovery driven over HTTP, then RELOADED across a restart: the
    /// identity's durable id is unchanged, its surface still resolves, and the
    /// COMMITTED CURRENT KEY is the recovered one. The refusals (a non-current
    /// signer, a sub-threshold quorum) persist nothing.
    #[tokio::test]
    async fn identity_succession_and_guardian_recovery_over_http_survive_restart() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let key_bytes = [41u8; 32];
        let seed = "succession-seed-p1";

        let birth = HybridKey::from_principal_seed(seed);
        let v2 = HybridKey::from_principal_seed("succession-seed-p1-v2");
        let v3 = HybridKey::from_principal_seed("succession-seed-p1-v3");
        let guardians: Vec<HybridKey> = ["g-alpha", "g-beta", "g-gamma"]
            .iter()
            .map(|s| HybridKey::from_principal_seed(s))
            .collect();
        let stranger = HybridKey::from_principal_seed("a-total-stranger");

        fn sig_json(k: &HybridKey, msg: &[u8]) -> serde_json::Value {
            let s = k.sign(msg).expect("hybrid sign");
            serde_json::json!({
                "ed_pk": hex32(&s.ed_pk),
                "ml_pk": s.ml_pk.iter().map(|b| format!("{b:02x}")).collect::<String>(),
                "ed_sig": s.ed_sig.iter().map(|b| format!("{b:02x}")).collect::<String>(),
                "ml_sig": s.ml_sig.iter().map(|b| format!("{b:02x}")).collect::<String>(),
            })
        }

        let identity_hex;
        let identity_cell;
        {
            let state = crate::state::NodeState::with_cclerk(tmp.path(), vec![], key_bytes)
                .expect("node state");
            let (st, minted) = post_json(
                &state,
                "/realm/identity/mint",
                serde_json::json!({ "label": "succeeding-one", "principal_seed": seed }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "mint: {minted}");
            identity_hex = minted["identity"].as_str().unwrap().to_string();
            identity_cell = CellId::from_bytes(
                crate::trustline_service::hex_decode_32(&identity_hex).expect("id hex"),
            );
            post_json(
                &state,
                "/realm/identity/bind",
                serde_json::json!({
                    "principal_seed": seed, "surface": "telegram", "local": "tg-77",
                }),
            )
            .await;

            // ── guardians (durable).
            let (st, g) = post_json(
                &state,
                "/realm/identity/guardians",
                serde_json::json!({
                    "principal_seed": seed,
                    "guardians": guardians
                        .iter()
                        .map(|k| hex32(&k.commitment()))
                        .collect::<Vec<_>>(),
                    "threshold": 2,
                }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "guardians: {g}");
            assert_eq!(g["guardians"], 3);
            assert_eq!(g["threshold"], 2);

            // ── the STOLEN-IDENTITY refusal: a non-current signer cannot succeed.
            let msg_v2 = succession_message(
                &identity_cell,
                1,
                &birth.commitment(),
                &v2.commitment(),
                SuccessionKind::SelfSigned,
            );
            let before = realm_status(&state).await["durable_log_len"]
                .as_u64()
                .unwrap();
            let (st, refusal) = post_json(
                &state,
                "/realm/identity/rotate",
                serde_json::json!({
                    "principal_seed": seed,
                    "new_key_commit": hex32(&v2.commitment()),
                    "sig": sig_json(&stranger, &msg_v2),
                }),
            )
            .await;
            assert_eq!(st, StatusCode::CONFLICT, "stranger rotate: {refusal}");
            assert_eq!(refusal["reason"], "wrong-succession-key");
            assert_eq!(
                realm_status(&state).await["durable_log_len"]
                    .as_u64()
                    .unwrap(),
                before,
                "a refused succession persists NOTHING"
            );

            // ── the real rotation, signed by the CURRENT key.
            let (st, rotated) = post_json(
                &state,
                "/realm/identity/rotate",
                serde_json::json!({
                    "principal_seed": seed,
                    "new_key_commit": hex32(&v2.commitment()),
                    "sig": sig_json(&birth, &msg_v2),
                }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "rotate: {rotated}");
            assert_eq!(rotated["epoch"], 2, "the succession epoch advanced");
            assert_eq!(
                rotated["identity"], identity_hex,
                "the durable id is UNCHANGED"
            );
            assert_eq!(rotated["current_key_commit"], hex32(&v2.commitment()));
            assert_eq!(
                rotated["followed_key_commit"], rotated["current_key_commit"],
                "following the chain from genesis reaches the current key"
            );

            // ── guardian recovery: below threshold is refused, 2-of-3 lands.
            let msg_v3 = succession_message(
                &identity_cell,
                2,
                &v2.commitment(),
                &v3.commitment(),
                SuccessionKind::GuardianRecovery,
            );
            let before = realm_status(&state).await["durable_log_len"]
                .as_u64()
                .unwrap();
            let (st, refusal) = post_json(
                &state,
                "/realm/identity/recover",
                serde_json::json!({
                    "principal_seed": seed,
                    "new_key_commit": hex32(&v3.commitment()),
                    "guardian_sigs": [sig_json(&guardians[0], &msg_v3)],
                }),
            )
            .await;
            assert_eq!(st, StatusCode::CONFLICT, "1-of-3 recovery: {refusal}");
            assert_eq!(refusal["reason"], "below-guardian-threshold");
            assert_eq!(
                realm_status(&state).await["durable_log_len"]
                    .as_u64()
                    .unwrap(),
                before,
                "a sub-threshold recovery persists NOTHING"
            );

            let (st, recovered) = post_json(
                &state,
                "/realm/identity/recover",
                serde_json::json!({
                    "principal_seed": seed,
                    "new_key_commit": hex32(&v3.commitment()),
                    "guardian_sigs": [
                        sig_json(&guardians[0], &msg_v3),
                        sig_json(&guardians[1], &msg_v3),
                    ],
                }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "2-of-3 recovery: {recovered}");
            assert_eq!(recovered["epoch"], 3);
            assert_eq!(recovered["current_key_commit"], hex32(&v3.commitment()));
        }

        // ── RESTART ── the succession log replays (each signature RE-VERIFIED).
        let restored = crate::state::NodeState::with_cclerk(tmp.path(), vec![], key_bytes)
            .expect("restore node state");
        let (st, resolved) = get_json(
            &restored,
            "/realm/identity/resolve?surface=telegram&local=tg-77",
        )
        .await;
        assert_eq!(st, StatusCode::OK, "resolve after restart: {resolved}");
        assert_eq!(
            resolved["identity"], identity_hex,
            "the durable principal outlived TWO key changes and a restart"
        );
        assert_eq!(resolved["epoch"], 3, "the succession epoch reloaded");
        assert_eq!(
            resolved["current_key_commit"],
            hex32(&v3.commitment()),
            "the RECOVERED key is the committed current key after the restart"
        );
        assert_eq!(
            resolved["followed_key_commit"], resolved["current_key_commit"],
            "the reloaded succession chain still resolves to the current key"
        );
    }

    /// ⚑ THE NON-CUSTODIAL MINT CANARY. A realm identity minted through the HTTP
    /// ingress where the node receives ONLY the holder's birth hybrid PUBLIC key —
    /// no seed material crosses the API OR into the durable `REALM_LOG` (asserted:
    /// the mint op is the seedless `MintIdentityPubkey` variant, and the holder's
    /// 32-byte seed material appears in NO log entry). The identity resolves + binds
    /// a surface (by its PUBLIC cell-id handle), survives a node restart on the
    /// durable log, and succession + guardian recovery STILL work on it — both
    /// before the restart AND on the reloaded identity.
    #[tokio::test]
    async fn non_custodial_mint_over_http_seed_never_crosses_survives_restart_and_succeeds() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let key_bytes = [43u8; 32];

        // The HOLDER's secret is generated OFF NODE and NEVER sent. Only the birth
        // hybrid PUBLIC key crosses. `seed_material` is the 32-byte key material the
        // node must never see in any durable log entry.
        let holder_secret = "HOLDER-ONLY-SECRET-noncustodial";
        let birth = HybridKey::from_principal_seed(holder_secret);
        let seed_material = realm_model::identity::hybrid_seed(holder_secret);

        let v2 = HybridKey::from_principal_seed("HOLDER-ONLY-SECRET-noncustodial-v2");
        let v3 = HybridKey::from_principal_seed("HOLDER-ONLY-SECRET-noncustodial-v3");
        let v4 = HybridKey::from_principal_seed("HOLDER-ONLY-SECRET-noncustodial-v4");
        let guardians: Vec<HybridKey> = ["ncg-a", "ncg-b", "ncg-c"]
            .iter()
            .map(|s| HybridKey::from_principal_seed(s))
            .collect();
        let stranger = HybridKey::from_principal_seed("a-total-stranger-nc");

        fn ml_hex(b: &[u8]) -> String {
            b.iter().map(|x| format!("{x:02x}")).collect()
        }
        fn sig_json(k: &HybridKey, msg: &[u8]) -> serde_json::Value {
            let s = k.sign(msg).expect("hybrid sign");
            serde_json::json!({
                "ed_pk": hex32(&s.ed_pk),
                "ml_pk": ml_hex(&s.ml_pk),
                "ed_sig": ml_hex(s.ed_sig.as_slice()),
                "ml_sig": ml_hex(&s.ml_sig),
            })
        }
        // Assert the holder's seed material appears in NO durable log entry.
        async fn assert_seed_absent(state: &NodeState, seed_material: &[u8; 32], when: &str) {
            let log = {
                let s = state.read().await;
                s.store.load_realm_log().expect("load durable realm log")
            };
            for (i, entry) in log.iter().enumerate() {
                assert!(
                    !entry.windows(32).any(|w| w == seed_material),
                    "durable realm log entry {i} contains the holder's seed material ({when})"
                );
            }
        }

        let identity_hex;
        let identity_cell;
        {
            let state = crate::state::NodeState::with_cclerk(tmp.path(), vec![], key_bytes)
                .expect("node state");

            // ── NON-CUSTODIAL MINT: the request carries ONLY the birth PUBLIC key.
            //    There is no `principal_seed` field — the node never sees a seed.
            let (st, minted) = post_json(
                &state,
                "/realm/identity/mint",
                serde_json::json!({
                    "label": "holder-one",
                    "birth_ed_pk": hex32(&birth.ed_pk()),
                    "birth_ml_pk": ml_hex(birth.ml_pk()),
                }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "non-custodial mint: {minted}");
            identity_hex = minted["identity"].as_str().unwrap().to_string();
            identity_cell = CellId::from_bytes(
                crate::trustline_service::hex_decode_32(&identity_hex).expect("id hex"),
            );
            assert_eq!(minted["epoch"], 1, "genesis succession epoch");
            assert_eq!(
                minted["current_key_commit"], minted["birth_key_commit"],
                "at genesis the current key IS the holder's birth key"
            );
            assert_eq!(
                minted["principal_pk"],
                hex32(&birth.ed_pk()),
                "principal_pk is the HOLDER's real ed25519 pubkey (the node did not derive it)"
            );
            assert_eq!(
                minted["current_key_commit"],
                hex32(&birth.commitment()),
                "KEY_COMMIT binds commit_hybrid over the holder's PUBLIC keys"
            );

            // ── THE SEED NEVER CROSSED: the sole durable op is the SEEDLESS
            //    `MintIdentityPubkey` variant, and no log entry holds the seed.
            let log = {
                let s = state.read().await;
                s.store.load_realm_log().expect("load durable realm log")
            };
            assert_eq!(log.len(), 1, "one durable op: the non-custodial mint");
            let op: RealmOp = postcard::from_bytes(&log[0]).expect("decode the mint op");
            assert!(
                matches!(op, RealmOp::MintIdentityPubkey { .. }),
                "the durable mint op is the non-custodial (structurally seedless) variant, not MintIdentity"
            );
            assert_seed_absent(&state, &seed_material, "after mint").await;

            // ── the identity BINDS a surface by its PUBLIC cell-id handle (no seed).
            let (st, bound) = post_json(
                &state,
                "/realm/identity/bind",
                serde_json::json!({
                    "identity": identity_hex,
                    "surface": "web",
                    "local": "holder-sess-1",
                }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "bind by public id: {bound}");
            assert_eq!(bound["identity"]["identity"], identity_hex);

            // ── it RESOLVES from its surface to the same canonical id.
            let (st, resolved) = get_json(
                &state,
                "/realm/identity/resolve?surface=web&local=holder-sess-1",
            )
            .await;
            assert_eq!(st, StatusCode::OK, "resolve: {resolved}");
            assert_eq!(resolved["identity"], identity_hex);
            assert_eq!(resolved["label"], "holder-one");

            // ── guardians (durable), for the recovery below.
            let (st, g) = post_json(
                &state,
                "/realm/identity/guardians",
                serde_json::json!({
                    "identity": identity_hex,
                    "guardians": guardians
                        .iter()
                        .map(|k| hex32(&k.commitment()))
                        .collect::<Vec<_>>(),
                    "threshold": 2,
                }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "guardians by id: {g}");
            assert_eq!(g["guardians"], 3);

            // ── SUCCESSION WORKS on the non-custodial identity. Stranger refused.
            let msg_v2 = succession_message(
                &identity_cell,
                1,
                &birth.commitment(),
                &v2.commitment(),
                SuccessionKind::SelfSigned,
            );
            let before = realm_status(&state).await["durable_log_len"]
                .as_u64()
                .unwrap();
            let (st, refusal) = post_json(
                &state,
                "/realm/identity/rotate",
                serde_json::json!({
                    "identity": identity_hex,
                    "new_key_commit": hex32(&v2.commitment()),
                    "sig": sig_json(&stranger, &msg_v2),
                }),
            )
            .await;
            assert_eq!(
                st,
                StatusCode::CONFLICT,
                "stranger rotate refused: {refusal}"
            );
            assert_eq!(refusal["reason"], "wrong-succession-key");
            assert_eq!(
                realm_status(&state).await["durable_log_len"]
                    .as_u64()
                    .unwrap(),
                before,
                "a refused succession persists NOTHING"
            );

            // The real rotation, signed by the holder's CURRENT (birth) key.
            let (st, rotated) = post_json(
                &state,
                "/realm/identity/rotate",
                serde_json::json!({
                    "identity": identity_hex,
                    "new_key_commit": hex32(&v2.commitment()),
                    "sig": sig_json(&birth, &msg_v2),
                }),
            )
            .await;
            assert_eq!(
                st,
                StatusCode::OK,
                "rotate by holder's birth key: {rotated}"
            );
            assert_eq!(rotated["epoch"], 2);
            assert_eq!(
                rotated["identity"], identity_hex,
                "the durable id is UNCHANGED"
            );
            assert_eq!(rotated["current_key_commit"], hex32(&v2.commitment()));

            // Guardian recovery: 2-of-3 succeeds over the id handle.
            let msg_v3 = succession_message(
                &identity_cell,
                2,
                &v2.commitment(),
                &v3.commitment(),
                SuccessionKind::GuardianRecovery,
            );
            let (st, recovered) = post_json(
                &state,
                "/realm/identity/recover",
                serde_json::json!({
                    "identity": identity_hex,
                    "new_key_commit": hex32(&v3.commitment()),
                    "guardian_sigs": [
                        sig_json(&guardians[0], &msg_v3),
                        sig_json(&guardians[1], &msg_v3),
                    ],
                }),
            )
            .await;
            assert_eq!(st, StatusCode::OK, "2-of-3 recovery: {recovered}");
            assert_eq!(recovered["epoch"], 3);
            assert_eq!(recovered["current_key_commit"], hex32(&v3.commitment()));

            // STILL no seed material anywhere in the durable log after succession.
            assert_seed_absent(&state, &seed_material, "after succession").await;
        }

        // ── RESTART ── the non-custodial mint + succession replay from the log.
        let restored = crate::state::NodeState::with_cclerk(tmp.path(), vec![], key_bytes)
            .expect("restore node state");
        assert_seed_absent(&restored, &seed_material, "after restart").await;

        // The identity resolves from its surface across the reboot, same durable id.
        let (st, resolved) = get_json(
            &restored,
            "/realm/identity/resolve?surface=web&local=holder-sess-1",
        )
        .await;
        assert_eq!(st, StatusCode::OK, "resolve after restart: {resolved}");
        assert_eq!(
            resolved["identity"], identity_hex,
            "the non-custodial durable principal outlived TWO key changes + a restart"
        );
        assert_eq!(resolved["epoch"], 3, "the succession epoch reloaded");
        assert_eq!(resolved["current_key_commit"], hex32(&v3.commitment()));
        assert_eq!(
            resolved["followed_key_commit"],
            resolved["current_key_commit"]
        );

        // ── succession STILL works on the RELOADED non-custodial identity.
        let msg_v4 = succession_message(
            &identity_cell,
            3,
            &v3.commitment(),
            &v4.commitment(),
            SuccessionKind::SelfSigned,
        );
        let (st, rotated4) = post_json(
            &restored,
            "/realm/identity/rotate",
            serde_json::json!({
                "identity": identity_hex,
                "new_key_commit": hex32(&v4.commitment()),
                "sig": sig_json(&v3, &msg_v4),
            }),
        )
        .await;
        assert_eq!(
            st,
            StatusCode::OK,
            "rotate after restart on the reloaded non-custodial identity: {rotated4}"
        );
        assert_eq!(rotated4["epoch"], 4);
        assert_eq!(rotated4["current_key_commit"], hex32(&v4.commitment()));
        assert_seed_absent(&restored, &seed_material, "after post-restart rotation").await;
    }
}
