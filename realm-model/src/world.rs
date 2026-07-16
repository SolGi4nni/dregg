//! `RealmWorld` — the one coherent model that ties realm/instance/identity/catalog
//! together, backed by a real [`dregg_cell::Ledger`].
//!
//! This is where the three §9 decisions MEET (they are interdependent, which is
//! why they are one crate): [`RealmWorld::admit`] resolves the actor's surface to
//! a canonical IDENTITY (§9.5), locates the INSTANCE's parent REALM (§9.4), and
//! gates the cited `ruleset_root` against that realm's CATALOG (§9.2) before any
//! effect touches the ledger. Refuse any leg and the turn commits nothing.
//!
//! ## The admission gate models "committed law"
//!
//! In production this gate is NOT a standalone function — it belongs inside the
//! executor's proof-verify path (`turn/src/executor/proof_verify.rs`, where a
//! proof-carrying turn already fails closed on an unregistered VK). This crate
//! models the SEMANTICS the executor must enforce: the admitted-roots set is
//! committed realm state, and the `ruleset_root` is a first-class field of the
//! turn/receipt (see [`RealmReceipt::ruleset_root`]), not inferred from the
//! serving binary. The design doc names the exact wiring.

use std::collections::HashMap;

use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger};
use dregg_turn::action::Effect;

use crate::catalog::{RulesetCatalog, catalog_key, listed_value};
use crate::identity::{CanonicalIdentity, SurfaceRef};
use crate::instance::{Instance, InstanceStatus, field as ifield};
use crate::realm::{Realm, field as rfield};
use crate::{
    RulesetRoot, default_token_id, derive_cell_id, derive_pubkey, open_permissions, pack_u64,
    unpack_u64,
};

/// A turn addressed to the realm substrate: an actor (on some surface) exercises
/// a cited body of law (`ruleset_root`) inside an instance, via typed effects.
///
/// The `ruleset_root` is a FIRST-CLASS field here — the §9.2 property that the
/// law is IN the turn, not inferred. The `actor` is a [`SurfaceRef`] (the
/// per-surface id) that the gate resolves to a canonical identity (§9.5).
#[derive(Clone, Debug)]
pub struct RealmTurn {
    /// Who acts, as seen on their surface (Discord user, web session, ...).
    pub actor: SurfaceRef,
    /// Which instance this turn acts inside.
    pub instance: CellId,
    /// The body of law the turn cites — gated against the realm catalog.
    pub ruleset_root: RulesetRoot,
    /// The typed effects (this model interprets [`Effect::SetField`]).
    pub effects: Vec<Effect>,
}

/// The receipt of an admitted realm turn. Chain-linked by
/// `previous_receipt_hash` — the substrate's own ordered history. What makes
/// realm PERSISTENCE real is a durable, node-served version of THIS chain; see
/// the design doc's "honest scope" (the node cannot yet serve it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealmReceipt {
    /// The resolved canonical identity that acted (NOT the surface id).
    pub actor_identity: CellId,
    /// The instance the turn acted in.
    pub instance: CellId,
    /// The parent realm.
    pub realm: CellId,
    /// The law the turn cited (committed into the receipt — §9.2).
    pub ruleset_root: RulesetRoot,
    /// Hash of the effects the turn admitted.
    pub effects_hash: [u8; 32],
    /// The prior receipt in this world's chain (None for the first).
    pub previous_receipt_hash: Option<[u8; 32]>,
    /// This receipt's hash (binds all of the above + the predecessor).
    pub receipt_hash: [u8; 32],
}

/// Why a turn was refused. Every variant leaves the ledger UNCHANGED.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refused {
    /// The actor's surface ref resolves to no canonical identity (§9.5 gate).
    UnknownActor(SurfaceRef),
    /// The cited instance is not known to this world.
    UnknownInstance(CellId),
    /// The instance is finalized; no further turns may act in it.
    InstanceFinalized(CellId),
    /// The cited `ruleset_root` is NOT in the realm's catalog (§9.2 gate) —
    /// "committed law": an unlisted root is refused.
    RulesetNotInCatalog {
        realm: CellId,
        ruleset_root: RulesetRoot,
    },
    /// An effect targets a cell outside the instance's scope (the membrane —
    /// an ordinary in-instance turn may not reach the durable realm cell; only
    /// the finalize/settle path crosses back).
    OutsideInstanceScope { effect_cell: CellId },
    /// An effect this model does not interpret (only `SetField` is supported).
    UnsupportedEffect,
    /// A ledger-level failure applying an admitted effect.
    Ledger(String),
}

/// The living world: realms, their instances, canonical identities, catalogs —
/// all cell-backed on one [`Ledger`], plus the ordered receipt chain.
pub struct RealmWorld {
    ledger: Ledger,
    identities: HashMap<CellId, CanonicalIdentity>,
    realms: HashMap<CellId, Realm>,
    realms_by_name: HashMap<String, CellId>,
    instances: HashMap<CellId, Instance>,
    receipts: Vec<RealmReceipt>,
    last_receipt_hash: Option<[u8; 32]>,
}

impl Default for RealmWorld {
    fn default() -> Self {
        Self::new()
    }
}

impl RealmWorld {
    pub fn new() -> Self {
        RealmWorld {
            ledger: Ledger::new(),
            identities: HashMap::new(),
            realms: HashMap::new(),
            realms_by_name: HashMap::new(),
            instances: HashMap::new(),
            receipts: Vec::new(),
            last_receipt_hash: None,
        }
    }

    /// Read-only access to the underlying ledger (for asserting cell-backed state).
    pub fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    /// The world's ordered receipt chain.
    pub fn receipts(&self) -> &[RealmReceipt] {
        &self.receipts
    }

    // ── cell plumbing ────────────────────────────────────────────────────────

    /// Mint a fresh, open cell at the deterministic id of `seed`.
    fn spawn_cell(&mut self, seed: &str) -> Result<CellId, Refused> {
        let pk = derive_pubkey(seed);
        let mut cell = Cell::with_balance(pk, default_token_id(), 0);
        cell.permissions = open_permissions();
        let id = cell.id();
        if self.ledger.get(&id).is_none() {
            self.ledger
                .insert_cell(cell)
                .map_err(|e| Refused::Ledger(format!("{e:?}")))?;
        }
        Ok(id)
    }

    fn write_field(
        &mut self,
        cell: &CellId,
        index: usize,
        value: FieldElement,
    ) -> Result<(), Refused> {
        self.ledger
            .update_with(cell, |c| {
                c.state.set_field(index, value);
            })
            .map_err(|e| Refused::Ledger(format!("{e:?}")))
    }

    fn read_field_u64(&self, cell: &CellId, index: usize) -> u64 {
        self.ledger
            .get(cell)
            .and_then(|c| c.state.get_field(index).map(unpack_u64))
            .unwrap_or(0)
    }

    fn read_field_bytes(&self, cell: &CellId, index: usize) -> Option<FieldElement> {
        self.ledger
            .get(cell)
            .and_then(|c| c.state.get_field(index).copied())
    }

    // ── §9.5 IDENTITY ─────────────────────────────────────────────────────────

    /// Mint a canonical identity from a principal seed. It exists FIRST and
    /// independently of any surface — surfaces bind onto it, never mint it.
    pub fn mint_identity(
        &mut self,
        label: &str,
        principal_seed: &str,
    ) -> Result<CanonicalIdentity, Refused> {
        let seed = format!("realm-identity:{principal_seed}");
        let id = self.spawn_cell(&seed)?;
        // Stamp a version marker (rotation epoch = 1) — the durable identity record.
        self.write_field(&id, 0, pack_u64(1))?;
        let identity = CanonicalIdentity {
            id,
            principal_pk: derive_pubkey(&seed),
            label: label.to_string(),
        };
        self.identities.insert(id, identity.clone());
        Ok(identity)
    }

    /// Bind a surface ref onto an EXISTING canonical identity. The binding is a
    /// real cell whose entire state is the canonical id it points at — so the
    /// surface DERIVES from the identity (§9.5), never the reverse. Re-binding a
    /// surface to a new identity is a NAMED decision-for-ember (account recovery)
    /// — see the design doc.
    pub fn bind_surface(
        &mut self,
        identity: &CanonicalIdentity,
        surface: SurfaceRef,
    ) -> Result<(), Refused> {
        let seed = surface.binding_seed();
        let bind_cell = self.spawn_cell(&seed)?;
        // The binding cell's field 0 IS the canonical id — resolution reads it.
        let id_bytes: FieldElement = *identity.id.as_bytes();
        self.write_field(&bind_cell, 0, id_bytes)?;
        Ok(())
    }

    /// Resolve a surface ref to its canonical identity by reading the binding
    /// cell's committed state. Returns `None` if the surface is unbound. This is
    /// the object `dreggnet-offerings`' per-surface viewer should resolve to.
    pub fn resolve_surface(&self, surface: &SurfaceRef) -> Option<CanonicalIdentity> {
        let seed = surface.binding_seed();
        let bind_cell = derive_cell_id(&seed);
        let id_bytes = self.read_field_bytes(&bind_cell, 0)?;
        if id_bytes == [0u8; 32] {
            return None;
        }
        let canonical = CellId::from_bytes(id_bytes);
        self.identities.get(&canonical).cloned()
    }

    // ── §9.4 REALM + INSTANCE ─────────────────────────────────────────────────

    /// Create a persistent realm (a durable cell) plus its ruleset catalog cell.
    pub fn create_realm(&mut self, name: &str) -> Result<Realm, Refused> {
        let realm_seed = format!("realm:{name}");
        let realm_id = self.spawn_cell(&realm_seed)?;
        self.write_field(&realm_id, rfield::EPOCH, pack_u64(0))?;
        self.write_field(&realm_id, rfield::HOARD, pack_u64(0))?;

        let catalog_seed = format!("realm-catalog:{name}");
        let catalog_id = self.spawn_cell(&catalog_seed)?;

        let realm = Realm {
            id: realm_id,
            name: name.to_string(),
            catalog: catalog_id,
        };
        self.realms.insert(realm_id, realm.clone());
        self.realms_by_name.insert(name.to_string(), realm_id);
        Ok(realm)
    }

    /// The realm's catalog handle.
    pub fn catalog_of(&self, realm: &CellId) -> Option<RulesetCatalog> {
        self.realms.get(realm).map(|r| RulesetCatalog {
            cell: r.catalog,
            realm: *realm,
        })
    }

    /// Open a child instance of a realm. PINS the realm's current durable value
    /// at birth (the §9.4 "child pins a parent root at birth" choice). The
    /// instance's scratch state resets with the instance (a fresh cell).
    pub fn open_instance(&mut self, realm: &CellId, seed: &str) -> Result<Instance, Refused> {
        let realm = *realm;
        if !self.realms.contains_key(&realm) {
            return Err(Refused::UnknownInstance(realm));
        }
        // Pin the parent realm value NOW.
        let parent_pin = self.read_field_u64(&realm, rfield::HOARD);

        let inst_seed = format!("realm-instance:{}:{seed}", hex(&realm));
        let inst_id = self.spawn_cell(&inst_seed)?;
        self.write_field(&inst_id, ifield::STATUS, pack_u64(0))?;
        self.write_field(&inst_id, ifield::RESULT, pack_u64(0))?;
        self.write_field(&inst_id, ifield::PARENT_PIN, pack_u64(parent_pin))?;

        let instance = Instance {
            id: inst_id,
            realm,
            seed: seed.to_string(),
            parent_pin,
        };
        self.instances.insert(inst_id, instance.clone());
        Ok(instance)
    }

    /// Current durable hoard value of a realm (what persists across instances).
    pub fn realm_hoard(&self, realm: &CellId) -> u64 {
        self.read_field_u64(realm, rfield::HOARD)
    }

    /// How many instances have settled back into a realm.
    pub fn realm_epoch(&self, realm: &CellId) -> u64 {
        self.read_field_u64(realm, rfield::EPOCH)
    }

    /// An instance's certified result (its scratch RESULT field).
    pub fn instance_result(&self, instance: &CellId) -> u64 {
        self.read_field_u64(instance, ifield::RESULT)
    }

    /// An instance's pinned parent value (what it saw of its realm at birth).
    pub fn instance_parent_pin(&self, instance: &CellId) -> u64 {
        self.read_field_u64(instance, ifield::PARENT_PIN)
    }

    /// An instance's status.
    pub fn instance_status(&self, instance: &CellId) -> InstanceStatus {
        if self.read_field_u64(instance, ifield::STATUS) == 1 {
            InstanceStatus::Finalized
        } else {
            InstanceStatus::Open
        }
    }

    // ── §9.2 CATALOG (committed law) ──────────────────────────────────────────

    /// LIST a ruleset root as active law for a realm (governance appends a root).
    pub fn list_ruleset(&mut self, realm: &CellId, root: RulesetRoot) -> Result<(), Refused> {
        let catalog = self
            .realms
            .get(realm)
            .map(|r| r.catalog)
            .ok_or(Refused::UnknownInstance(*realm))?;
        let key = catalog_key(&root);
        let value = listed_value(&root);
        self.ledger
            .update_with(&catalog, |c| {
                c.state.set_field_ext(key, value);
            })
            .map_err(|e| Refused::Ledger(format!("{e:?}")))
    }

    /// UNLIST a ruleset root (deprecation) — writes zero, so it no longer equals
    /// any real root. Historical receipts that cited it are untouched (they hold
    /// the root); only FUTURE turns citing it are refused. The driven canary.
    pub fn unlist_ruleset(&mut self, realm: &CellId, root: RulesetRoot) -> Result<(), Refused> {
        let catalog = self
            .realms
            .get(realm)
            .map(|r| r.catalog)
            .ok_or(Refused::UnknownInstance(*realm))?;
        let key = catalog_key(&root);
        self.ledger
            .update_with(&catalog, |c| {
                c.state.set_field_ext(key, [0u8; 32]);
            })
            .map_err(|e| Refused::Ledger(format!("{e:?}")))
    }

    /// Is `root` committed active law for this realm? Reads the catalog cell:
    /// the stored value must EQUAL the cited root (not merely a key hit).
    pub fn is_listed(&self, realm: &CellId, root: &RulesetRoot) -> bool {
        let Some(catalog) = self.realms.get(realm).map(|r| r.catalog) else {
            return false;
        };
        let key = catalog_key(root);
        self.ledger
            .get(&catalog)
            .and_then(|c| c.state.get_field_ext(key))
            .map(|v| &v == root)
            .unwrap_or(false)
    }

    // ── the admission gate (where the three decisions meet) ───────────────────

    /// Admit a realm turn: resolve identity (§9.5), locate parent realm (§9.4),
    /// gate the cited `ruleset_root` against the realm catalog (§9.2), enforce
    /// the instance-scope membrane, then apply the effects and chain a receipt.
    /// Any refusal leaves the ledger unchanged.
    pub fn admit(&mut self, turn: RealmTurn) -> Result<RealmReceipt, Refused> {
        self.admit_inner(turn, /*allow_realm_target=*/ false)
    }

    fn admit_inner(
        &mut self,
        turn: RealmTurn,
        allow_realm_target: bool,
    ) -> Result<RealmReceipt, Refused> {
        // (1) §9.5 — resolve the actor's surface to a canonical identity.
        let identity = self
            .resolve_surface(&turn.actor)
            .ok_or_else(|| Refused::UnknownActor(turn.actor.clone()))?;

        // (2) §9.4 — locate the instance and its parent realm.
        let instance = self
            .instances
            .get(&turn.instance)
            .cloned()
            .ok_or(Refused::UnknownInstance(turn.instance))?;
        if self.instance_status(&instance.id) == InstanceStatus::Finalized {
            return Err(Refused::InstanceFinalized(instance.id));
        }
        let realm = instance.realm;

        // (3) §9.2 — gate the cited ruleset_root against the realm catalog.
        if !self.is_listed(&realm, &turn.ruleset_root) {
            return Err(Refused::RulesetNotInCatalog {
                realm,
                ruleset_root: turn.ruleset_root,
            });
        }

        // (4) validate ALL effects (type + scope) BEFORE mutating anything.
        let mut writes: Vec<(CellId, usize, FieldElement)> = Vec::with_capacity(turn.effects.len());
        for effect in &turn.effects {
            match effect {
                Effect::SetField { cell, index, value } => {
                    let in_scope = *cell == instance.id || (allow_realm_target && *cell == realm);
                    if !in_scope {
                        return Err(Refused::OutsideInstanceScope { effect_cell: *cell });
                    }
                    writes.push((*cell, *index, *value));
                }
                _ => return Err(Refused::UnsupportedEffect),
            }
        }

        // (5) apply — the turn is admitted.
        for (cell, index, value) in &writes {
            self.write_field(cell, *index, *value)?;
        }

        // (6) chain the receipt.
        let effects_hash = hash_effects(&writes);
        let previous = self.last_receipt_hash;
        let receipt_hash = hash_receipt(
            &identity.id,
            &instance.id,
            &realm,
            &turn.ruleset_root,
            &effects_hash,
            previous.as_ref(),
        );
        let receipt = RealmReceipt {
            actor_identity: identity.id,
            instance: instance.id,
            realm,
            ruleset_root: turn.ruleset_root,
            effects_hash,
            previous_receipt_hash: previous,
            receipt_hash,
        };
        self.last_receipt_hash = Some(receipt_hash);
        self.receipts.push(receipt.clone());
        Ok(receipt)
    }

    /// Play a single scoped effect inside an instance (convenience over
    /// [`RealmWorld::admit`]) — writes the instance's own scratch field.
    pub fn play(
        &mut self,
        actor: SurfaceRef,
        instance: CellId,
        ruleset_root: RulesetRoot,
        index: usize,
        value: u64,
    ) -> Result<RealmReceipt, Refused> {
        self.admit(RealmTurn {
            actor,
            instance,
            ruleset_root,
            effects: vec![Effect::SetField {
                cell: instance,
                index,
                value: pack_u64(value),
            }],
        })
    }

    /// SETTLE an instance's certified result back into its persistent realm
    /// (§9.4 "how certified outputs return"). Finalizes the instance, then
    /// crosses the membrane to advance the realm's durable hoard + epoch — itself
    /// a catalog-gated, identity-attributed admitted turn. After this, the
    /// instance is closed; a NEW instance opened on the realm pins the new value.
    pub fn settle_instance(
        &mut self,
        actor: SurfaceRef,
        instance: CellId,
        ruleset_root: RulesetRoot,
    ) -> Result<RealmReceipt, Refused> {
        let inst = self
            .instances
            .get(&instance)
            .cloned()
            .ok_or(Refused::UnknownInstance(instance))?;
        if self.instance_status(&instance) == InstanceStatus::Finalized {
            return Err(Refused::InstanceFinalized(instance));
        }
        let realm = inst.realm;
        let result = self.read_field_u64(&instance, ifield::RESULT);
        let new_hoard = self.realm_hoard(&realm).saturating_add(result);
        let new_epoch = self.realm_epoch(&realm).saturating_add(1);

        // Cross the membrane: this admitted turn targets the REALM cell (only the
        // settle path may). Still gated by identity + catalog.
        let receipt = self.admit_inner(
            RealmTurn {
                actor,
                instance,
                ruleset_root,
                effects: vec![
                    Effect::SetField {
                        cell: realm,
                        index: rfield::HOARD,
                        value: pack_u64(new_hoard),
                    },
                    Effect::SetField {
                        cell: realm,
                        index: rfield::EPOCH,
                        value: pack_u64(new_epoch),
                    },
                ],
            },
            /*allow_realm_target=*/ true,
        )?;

        // Finalize the instance (its scratch is now spent). Status lives on the
        // ledger; the `Instance` struct mirrors only seed/realm/pin.
        self.write_field(&instance, ifield::STATUS, pack_u64(1))?;
        Ok(receipt)
    }
}

fn hex(id: &CellId) -> String {
    let mut s = String::with_capacity(64);
    for b in id.as_bytes() {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn hash_effects(writes: &[(CellId, usize, FieldElement)]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"realm-effects-v1");
    for (cell, index, value) in writes {
        h.update(cell.as_bytes());
        h.update(&(*index as u64).to_le_bytes());
        h.update(value);
    }
    *h.finalize().as_bytes()
}

fn hash_receipt(
    actor: &CellId,
    instance: &CellId,
    realm: &CellId,
    ruleset_root: &RulesetRoot,
    effects_hash: &[u8; 32],
    previous: Option<&[u8; 32]>,
) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"realm-receipt-v1");
    h.update(actor.as_bytes());
    h.update(instance.as_bytes());
    h.update(realm.as_bytes());
    h.update(ruleset_root);
    h.update(effects_hash);
    h.update(previous.unwrap_or(&[0u8; 32]));
    *h.finalize().as_bytes()
}
