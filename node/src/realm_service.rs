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
//! ## Honest residual (named, not laundered)
//!
//! The catalog gate here is realm-model's `RealmWorld::admit`, which the node
//! calls as the deployed admission point for realm turns. It is NOT yet inside the
//! kernel executor's `proof_verify.rs` path, and `ruleset_root` is NOT yet a
//! first-class field of `dregg_turn::Turn` (MUD-SUBSTRATE.md wiring items 1-2).
//! Those are additive kernel changes on the signed-turn perimeter and are left as
//! named residual — the node's realm admission genuinely routes through
//! realm-model's gate and is durable, but a realm turn is not yet the same signed,
//! fee-estimated, proof-carrying `Turn` the HTTP `/turns/submit` ingress drives.

use std::collections::HashMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use dregg_cell::CellId;
use dregg_persist::PersistentStore;
use dregg_turn::action::Effect;

use realm_model::identity::{Surface, SurfaceRef};
use realm_model::realm::Membrane;
use realm_model::{
    CanonicalIdentity, Instance, Realm, RealmReceipt, RealmTurn, RealmWorld, Refused, RulesetRoot,
    pack_u64,
};

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
}

impl std::fmt::Display for RealmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RealmError::Refused(r) => write!(f, "realm turn refused: {r:?}"),
            RealmError::UnknownHandle(h) => write!(f, "unknown realm handle: {h}"),
            RealmError::Store(s) => write!(f, "realm store error: {s}"),
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
}

/// The node's durable realm subsystem: a real `RealmWorld` plus the durable
/// `REALM_LOG` it is projected from, and the node-side handle maps that name
/// realms/identities for the ingress.
pub struct NodeRealms {
    world: RealmWorld,
    store: Arc<PersistentStore>,
    /// Dense index of the next durable log entry (== durable log length).
    next_index: u64,
    /// principal-seed -> the canonical identity minted from it.
    identities: HashMap<String, CanonicalIdentity>,
    /// realm name -> the realm.
    realms: HashMap<String, Realm>,
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
            realms: HashMap::new(),
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
                self.identities.insert(principal_seed.clone(), id);
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
            }
            RealmOp::UnlistRuleset { realm_name, root } => {
                let realm_id = self.realm_id(realm_name)?;
                self.world
                    .unlist_ruleset(&realm_id, *root)
                    .map_err(RealmError::Refused)?;
            }
            RealmOp::OpenInstance { realm_name, seed } => {
                let realm_id = self.realm_id(realm_name)?;
                self.world
                    .open_instance(&realm_id, seed)
                    .map_err(RealmError::Refused)?;
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
}

fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}
