//! Name resolution + lowering: a [`Deployment`] → a `dregg_turn::CallForest`.
//!
//! The lowering is a single pass that (1) resolves the symbolic names to
//! content-addresses / `CellId`s, (2) builds the exact core types the executor
//! already gates — `FactoryDescriptor`, `FactoryCreationParams`, `Effect` —
//! and (3) emits an ordered effect list (deploy → birth → fund → grant)
//! grouped into one root action per emitted turn, in dependency order (a cell
//! is born before it is granted from). The output forest is precisely what
//! `dregg-userspace-verify::analyze` consumes.

use std::collections::BTreeMap;

use dregg_cell::CapabilityRef;
use dregg_cell::factory::{
    CapGrant, CapTarget, CapTemplate, FactoryCreationParams, FactoryDescriptor,
};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::StateConstraint;
use dregg_cell::state::FieldElement;
use dregg_cell::CellMode;
use dregg_turn::action::{Action, DelegationMode, Effect};
use dregg_turn::{CallForest, CallTree};
use dregg_types::{CellId, FederationId};

use crate::schema::*;

/// Lowering / resolution errors, each naming the offending row.
#[derive(Debug, thiserror::Error, PartialEq)]
pub enum LowerError {
    #[error("cell `{cell}` references factory `{factory}`, which is not declared in any [[factory]]")]
    UnknownFactory { cell: String, factory: String },
    #[error("{site} references name `{name}`, which is not a declared cell and is not a 64-hex CellId")]
    UnknownName { site: String, name: String },
    #[error("duplicate factory ref `{0}` (each [[factory]].ref must be unique)")]
    DuplicateFactory(String),
    #[error("duplicate cell name `{0}` (each [[cell]].name must be unique)")]
    DuplicateCell(String),
    #[error("bad hex in {site}: `{value}` ({reason})")]
    BadHex {
        site: String,
        value: String,
        reason: String,
    },
    #[error("unknown {field} `{value}` in {site} (expected one of: {expected})")]
    UnknownEnum {
        site: String,
        field: String,
        value: String,
        expected: String,
    },
    #[error("state_constraint kind `{kind}` (slot {slot}) requires a `value =` (in {site})")]
    MissingConstraintValue {
        site: String,
        kind: String,
        slot: u8,
    },
    #[error(transparent)]
    Facet(#[from] crate::facet::FacetParseError),
    #[error(
        "grant[{index}] sets BOTH `facet = \"{facet}\"` and `allowed_effects = {allowed_effects}`, \
         and they DISAGREE (facet ⇒ {facet_mask}). Set only one, or make them equal."
    )]
    FacetConflict {
        index: usize,
        facet: String,
        facet_mask: u32,
        allowed_effects: u32,
    },
}

/// The lowered deployment: the forest the checker consumes, plus the resolved
/// content-addresses so a caller can submit / audit by name.
#[derive(Clone, Debug)]
pub struct Lowered {
    /// The federation this deployment binds to.
    pub federation_id: FederationId,
    /// The ordered turn forest (one root per effect-group, dependency-ordered:
    /// births, then funds, then grants). This is the
    /// `dregg-userspace-verify`-checkable artifact.
    pub forest: CallForest,
    /// Resolved factory content-addresses (`ref` -> `factory_vk` / descriptor
    /// hash).
    pub factory_vks: BTreeMap<String, [u8; 32]>,
    /// Resolved cell ids (`name` -> `CellId`).
    pub cell_ids: BTreeMap<String, CellId>,
}

impl Lowered {
    /// Reverse-resolve a `CellId` back to the spec NAME that minted it (for
    /// diagnostics that want to say `operator`, not `a1b2c3…`). Falls back to
    /// `None` for a raw-hex id that never had a name.
    pub fn name_of_cell(&self, id: &CellId) -> Option<&str> {
        self.cell_ids
            .iter()
            .find(|(_, v)| *v == id)
            .map(|(k, _)| k.as_str())
    }

    /// A short, human label for a `CellId`: its spec name if known, else an
    /// 8-hex prefix of the id (so a finding always names *something* legible).
    pub fn label_cell(&self, id: &CellId) -> String {
        match self.name_of_cell(id) {
            Some(n) => n.to_string(),
            None => {
                let h: String = id.0.iter().take(4).map(|b| format!("{b:02x}")).collect();
                format!("0x{h}…")
            }
        }
    }
}

// ─── hex helpers ─────────────────────────────────────────────────────────────

fn parse_hex32(site: &str, s: &str) -> Result<[u8; 32], LowerError> {
    // Accept an optional `b3:` / `0x` / `vk:` / `ed:` / `tok:` prefix; the
    // surface uses these as friendly tags, the bytes are what matter.
    let cleaned = s
        .trim()
        .trim_start_matches("b3:")
        .trim_start_matches("0x")
        .trim_start_matches("vk:")
        .trim_start_matches("ed:")
        .trim_start_matches("tok:");
    let bytes = decode_hex(cleaned).map_err(|reason| LowerError::BadHex {
        site: site.to_string(),
        value: s.to_string(),
        reason,
    })?;
    if bytes.len() != 32 {
        return Err(LowerError::BadHex {
            site: site.to_string(),
            value: s.to_string(),
            reason: format!("expected 32 bytes (64 hex chars), got {}", bytes.len()),
        });
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&bytes);
    Ok(out)
}

fn decode_hex(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("odd number of hex digits".to_string());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    let bytes = s.as_bytes();
    for pair in bytes.chunks(2) {
        let hi = hex_nibble(pair[0])?;
        let lo = hex_nibble(pair[1])?;
        out.push((hi << 4) | lo);
    }
    Ok(out)
}

fn hex_nibble(c: u8) -> Result<u8, String> {
    match c {
        b'0'..=b'9' => Ok(c - b'0'),
        b'a'..=b'f' => Ok(c - b'a' + 10),
        b'A'..=b'F' => Ok(c - b'A' + 10),
        other => Err(format!("`{}` is not a hex digit", other as char)),
    }
}

/// A stable 32-byte derivation from a symbolic name (used to give cells /
/// factories / owners deterministic ids when the deployment does not pin a
/// concrete content-address). Re-running the same DreggDL yields the same ids.
fn derive32(domain: &str, name: &str) -> [u8; 32] {
    blake3::derive_key(domain, name.as_bytes())
}

// ─── enum surface parsing ────────────────────────────────────────────────────

fn parse_mode(site: &str, s: &str) -> Result<CellMode, LowerError> {
    match s.trim().to_ascii_lowercase().as_str() {
        "hosted" => Ok(CellMode::Hosted),
        "sovereign" => Ok(CellMode::Sovereign),
        other => Err(LowerError::UnknownEnum {
            site: site.to_string(),
            field: "mode".to_string(),
            value: other.to_string(),
            expected: "hosted | sovereign".to_string(),
        }),
    }
}

fn parse_auth(site: &str, s: &str) -> Result<AuthRequired, LowerError> {
    match s.trim().to_ascii_lowercase().as_str() {
        "none" => Ok(AuthRequired::None),
        "signature" | "sig" => Ok(AuthRequired::Signature),
        "proof" => Ok(AuthRequired::Proof),
        "either" => Ok(AuthRequired::Either),
        "impossible" => Ok(AuthRequired::Impossible),
        other => Err(LowerError::UnknownEnum {
            site: site.to_string(),
            field: "permissions".to_string(),
            value: other.to_string(),
            expected: "none | signature | proof | either | impossible".to_string(),
        }),
    }
}

/// Resolve a `[[grant]]`'s effect facet to the `allowed_effects` mask the
/// `CapabilityRef` carries, reconciling the friendly `facet` surface with the
/// raw `allowed_effects` field:
///   * neither set ⇒ `None` (unrestricted, top);
///   * only `allowed_effects` ⇒ that raw mask;
///   * only `facet` ⇒ the parsed facet (`"all"` ⇒ `None`);
///   * BOTH set ⇒ they must AGREE (else [`LowerError::FacetConflict`]); `facet`
///     is the canonical surface, the raw field is the round-trip echo.
fn resolve_grant_facet(i: usize, grant: &Grant) -> Result<Option<u32>, LowerError> {
    let site = format!("grant[{i}].facet");
    match (&grant.facet, grant.allowed_effects) {
        (None, ae) => Ok(ae),
        (Some(f), None) => Ok(crate::facet::facet_to_allowed_effects(&site, f)?),
        (Some(f), Some(ae)) => {
            let from_facet = crate::facet::facet_to_allowed_effects(&site, f)?;
            // Compare as the resolved Option<mask>; `"all"`⇒None must match a
            // raw `allowed_effects` only if that raw is also the top reading.
            // We treat the raw field's intent literally: they agree iff equal.
            if from_facet == Some(ae) || (from_facet.is_none() && ae == dregg_cell::EFFECT_ALL) {
                Ok(from_facet)
            } else {
                Err(LowerError::FacetConflict {
                    index: i,
                    facet: f.clone(),
                    facet_mask: from_facet.unwrap_or(dregg_cell::EFFECT_ALL),
                    allowed_effects: ae,
                })
            }
        }
    }
}

/// Lift a big-endian u64 into a 32-byte field element (last 8 bytes), matching
/// the `StateConstraint` / executor field encoding.
fn u64_to_field(v: u64) -> FieldElement {
    let mut f = [0u8; 32];
    f[24..].copy_from_slice(&v.to_be_bytes());
    f
}

fn parse_state_constraint(
    site: &str,
    row: &StateConstraintRow,
) -> Result<StateConstraint, LowerError> {
    let need_value = || -> Result<FieldElement, LowerError> {
        row.value
            .map(u64_to_field)
            .ok_or_else(|| LowerError::MissingConstraintValue {
                site: site.to_string(),
                kind: row.kind.clone(),
                slot: row.slot,
            })
    };
    let c = match row.kind.trim().to_ascii_lowercase().as_str() {
        "write_once" | "writeonce" => StateConstraint::WriteOnce { index: row.slot },
        "immutable" => StateConstraint::Immutable { index: row.slot },
        "monotonic" => StateConstraint::Monotonic { index: row.slot },
        "strict_monotonic" | "strictmonotonic" => {
            StateConstraint::StrictMonotonic { index: row.slot }
        }
        "field_equals" | "fieldequals" => StateConstraint::FieldEquals {
            index: row.slot,
            value: need_value()?,
        },
        "field_gte" | "fieldgte" => StateConstraint::FieldGte {
            index: row.slot,
            value: need_value()?,
        },
        "field_lte" | "fieldlte" => StateConstraint::FieldLte {
            index: row.slot,
            value: need_value()?,
        },
        other => {
            return Err(LowerError::UnknownEnum {
                site: site.to_string(),
                field: "state_constraint.kind".to_string(),
                value: other.to_string(),
                expected: "write_once | immutable | monotonic | strict_monotonic | \
                           field_equals | field_gte | field_lte"
                    .to_string(),
            });
        }
    };
    Ok(c)
}

// ─── the lowering pass ───────────────────────────────────────────────────────

impl Lowered {
    /// Lower a parsed [`Deployment`] to the checkable forest.
    pub fn from_deployment(dep: &Deployment) -> Result<Lowered, LowerError> {
        // (0) federation id.
        let federation_id = resolve_federation(&dep.federation)?;

        // (1) factories: build each descriptor, take its hash as factory_vk.
        let mut factory_vks: BTreeMap<String, [u8; 32]> = BTreeMap::new();
        let mut factory_descs: BTreeMap<String, FactoryDescriptor> = BTreeMap::new();
        for f in &dep.factories {
            if factory_vks.contains_key(&f.r#ref) {
                return Err(LowerError::DuplicateFactory(f.r#ref.clone()));
            }
            let desc = build_descriptor(f)?;
            // The ON-CHAIN factory VK the born cell's `CreateCellFromFactory`
            // effect names: when the spec PINS `factory_vk` (binding to a real,
            // published factory like an app's `*_FACTORY_VK`), that pinned value
            // IS the identity — so the deploy instantiates that exact factory.
            // Absent a pin, the self-contained descriptor hash is the identity.
            let vk = match &f.factory_vk {
                Some(s) => parse_hex32(&format!("factory `{}`.factory_vk", f.r#ref), s)?,
                None => desc.hash(),
            };
            factory_vks.insert(f.r#ref.clone(), vk);
            factory_descs.insert(f.r#ref.clone(), desc);
        }

        // (2) cells: assign each a deterministic CellId by name.
        let mut cell_ids: BTreeMap<String, CellId> = BTreeMap::new();
        for c in &dep.cells {
            if cell_ids.contains_key(&c.name) {
                return Err(LowerError::DuplicateCell(c.name.clone()));
            }
            cell_ids.insert(c.name.clone(), CellId(derive32("dregg-deploy-cell-v1", &c.name)));
        }

        // The name resolver closes over cells (and accepts raw 64-hex ids).
        let resolve_cell = |site: &str, name: &str| -> Result<CellId, LowerError> {
            if let Some(id) = cell_ids.get(name) {
                return Ok(*id);
            }
            // Fall back to a literal 64-hex CellId.
            if let Ok(bytes) = parse_hex32(site, name) {
                return Ok(CellId(bytes));
            }
            Err(LowerError::UnknownName {
                site: site.to_string(),
                name: name.to_string(),
            })
        };

        let mut roots: Vec<CallTree> = Vec::new();

        // (3) births: one CreateCellFromFactory per [[cell]], dependency-first.
        for c in &dep.cells {
            let factory_vk = *factory_vks.get(&c.factory).ok_or_else(|| {
                LowerError::UnknownFactory {
                    cell: c.name.clone(),
                    factory: c.factory.clone(),
                }
            })?;
            let desc = &factory_descs[&c.factory];
            let cell_id = cell_ids[&c.name];

            let mode = match &c.mode {
                Some(m) => parse_mode(&format!("cell `{}`.mode", c.name), m)?,
                None => desc.default_mode.clone(),
            };
            let owner_pubkey = match &c.owner_pubkey {
                Some(s) => parse_hex32(&format!("cell `{}`.owner_pubkey", c.name), s)?,
                None => derive32("dregg-deploy-owner-v1", &c.name),
            };
            let token_id = match &c.token_id {
                Some(s) => parse_hex32(&format!("cell `{}`.token_id", c.name), s)?,
                None => [0u8; 32],
            };
            let program_vk = match &c.program_vk {
                Some(s) => Some(parse_hex32(&format!("cell `{}`.program_vk", c.name), s)?),
                None => desc.child_program_vk,
            };
            let initial_fields: Vec<(u32, u64)> =
                c.initial_fields.iter().map(|fr| (fr.slot, fr.value)).collect();

            let params = FactoryCreationParams {
                mode,
                program_vk,
                initial_fields,
                // Birth-time caps are out of v0 scope: the authority graph is
                // declared in [[grant]] (the audit-bearing CapDL surface).
                initial_caps: Vec::new(),
                owner_pubkey,
            };

            let effect = Effect::CreateCellFromFactory {
                factory_vk,
                owner_pubkey,
                token_id,
                params,
            };
            roots.push(CallTree::new(action_on(cell_id, "deploy.create_cell", vec![effect])));
        }

        // (4) funds: one Transfer per [[fund]].
        for (i, fund) in dep.funds.iter().enumerate() {
            let from = resolve_cell(&format!("fund[{i}].from"), &fund.from)?;
            let to = resolve_cell(&format!("fund[{i}].to"), &fund.to)?;
            let effect = Effect::Transfer {
                from,
                to,
                amount: fund.amount,
            };
            roots.push(CallTree::new(action_on(from, "deploy.fund", vec![effect])));
        }

        // (5) grants: one GrantCapability per [[grant]] — the authority graph.
        //
        // Build a DELEGATION FOREST, not a flat list: grant G2 nests under
        // grant G1 when `G2.from == G1.to` (the recipient re-delegates the cap
        // it was just handed). This makes the declared cap graph a real tree
        // that `dregg-userspace-verify::check_no_amplification` walks
        // parent→child — so a re-delegation that AMPLIFIES (grants wider than
        // it was handed) is caught as an in-forest amplification. Top-level
        // grants (whose `from` is not the recipient of any earlier grant) are
        // roots.
        struct GrantNode {
            tree: CallTree,
            to: CellId,
        }
        let mut grant_nodes: Vec<GrantNode> = Vec::new();
        for (i, grant) in dep.grants.iter().enumerate() {
            let from = resolve_cell(&format!("grant[{i}].from"), &grant.from)?;
            let to = resolve_cell(&format!("grant[{i}].to"), &grant.to)?;
            let target = match &grant.target {
                Some(t) if t.eq_ignore_ascii_case("self") => from,
                Some(t) => resolve_cell(&format!("grant[{i}].target"), t)?,
                None => from,
            };
            let permissions = parse_auth(&format!("grant[{i}].permissions"), &grant.permissions)?;
            let expires_at = match grant.expires_at {
                Some(0) | None => None,
                Some(h) => Some(h),
            };
            let allowed_effects = resolve_grant_facet(i, grant)?;
            let cap = CapabilityRef {
                target,
                slot: grant.slot,
                permissions,
                breadstuff: None,
                expires_at,
                allowed_effects,
                stored_epoch: None,
            };
            let effect = Effect::GrantCapability { from, to, cap };
            grant_nodes.push(GrantNode {
                tree: CallTree::new(action_on(from, "deploy.grant", vec![effect])),
                to,
            });
        }

        // Splice each grant under the FIRST earlier grant whose recipient is
        // this grant's grantor (so the re-delegation chain is parent→child).
        // We build the tree by repeatedly attaching the deepest-first; using
        // indices to avoid borrow issues, then assembling bottom-up.
        let grantor_of: Vec<CellId> = dep
            .grants
            .iter()
            .enumerate()
            .map(|(i, g)| resolve_cell(&format!("grant[{i}].from"), &g.from))
            .collect::<Result<_, _>>()?;
        // parent[i] = index of the grant node `i` nests under, or None (root).
        let mut parent: Vec<Option<usize>> = vec![None; grant_nodes.len()];
        for i in 0..grant_nodes.len() {
            // Find an earlier grant j whose recipient == grantor of i.
            for j in 0..i {
                if grant_nodes[j].to == grantor_of[i] {
                    parent[i] = Some(j);
                    break;
                }
            }
        }
        // Assemble: process in reverse so children are folded into parents.
        // Move trees out, attach child trees to parents, collect roots.
        let mut trees: Vec<Option<CallTree>> = grant_nodes.into_iter().map(|g| Some(g.tree)).collect();
        for i in (0..trees.len()).rev() {
            if let Some(p) = parent[i] {
                let child = trees[i].take().expect("each grant tree taken once");
                trees[p]
                    .as_mut()
                    .expect("parent precedes child, not yet taken")
                    .children
                    .push(child);
            }
        }
        for t in trees.into_iter().flatten() {
            roots.push(t);
        }

        let mut forest = CallForest {
            roots,
            forest_hash: [0u8; 32],
        };
        forest.forest_hash = forest.compute_hash();

        Ok(Lowered {
            federation_id,
            forest,
            factory_vks,
            cell_ids,
        })
    }
}

/// Build an `Action` carrying `effects` on `target`.
///
/// The lowering emits a `Signature` placeholder authorization (a zero
/// signature), NOT `Authorization::Unchecked`. The static audit is about the
/// declared *authority layout* (conservation + non-amplification + structural
/// shape); the *actual signature bytes* are dynamic — the SDK re-signs each
/// lowered turn with the real key at submit time, and the executor verifies
/// them. Using `Signature` here keeps the well-formedness check meaningful (it
/// would correctly flag a genuine `Unchecked` auth-bypass) without making every
/// valid deployment fail it on the placeholder.
fn action_on(target: CellId, method: &str, effects: Vec<Effect>) -> Action {
    Action {
        target,
        method: dregg_turn::action::symbol(method),
        args: Vec::new(),
        authorization: dregg_turn::action::Authorization::Signature([0u8; 32], [0u8; 32]),
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: Vec::new(),
    }
}

fn resolve_federation(fed: &Federation) -> Result<FederationId, LowerError> {
    let id = fed.id.trim();
    if id.is_empty() || id.eq_ignore_ascii_case("auto") {
        return Ok(FederationId([0u8; 32]));
    }
    Ok(FederationId(parse_hex32("federation.id", id)?))
}

fn build_descriptor(f: &Factory) -> Result<FactoryDescriptor, LowerError> {
    let factory_vk = match &f.factory_vk {
        Some(s) => parse_hex32(&format!("factory `{}`.factory_vk", f.r#ref), s)?,
        None => derive32("dregg-deploy-factory-vk-v1", &f.r#ref),
    };
    let child_program_vk = match &f.child_program_vk {
        Some(s) => Some(parse_hex32(
            &format!("factory `{}`.child_program_vk", f.r#ref),
            s,
        )?),
        None => None,
    };
    let default_mode = parse_mode(&format!("factory `{}`.default_mode", f.r#ref), &f.default_mode)?;

    let mut state_constraints = Vec::new();
    for sc in &f.state_constraints {
        state_constraints.push(parse_state_constraint(
            &format!("factory `{}`.state_constraint", f.r#ref),
            sc,
        )?);
    }

    let mut allowed_cap_templates = Vec::new();
    for t in &f.allowed_cap_templates {
        let max_permissions = parse_auth(
            &format!("factory `{}`.allowed_cap_template.permissions", f.r#ref),
            &t.permissions,
        )?;
        let target = parse_cap_target(&format!("factory `{}`.allowed_cap_template.target", f.r#ref), &t.target)?;
        allowed_cap_templates.push(CapTemplate {
            target,
            max_permissions,
            attenuatable: t.attenuatable,
        });
    }

    Ok(FactoryDescriptor {
        factory_vk,
        child_program_vk,
        child_vk_strategy: None,
        allowed_cap_templates,
        field_constraints: Vec::new(),
        state_constraints,
        default_mode,
        creation_budget: f.creation_budget,
    })
}

fn parse_cap_target(site: &str, s: &str) -> Result<CapTarget, LowerError> {
    match s.trim().to_ascii_lowercase().as_str() {
        "self" | "selfcell" => Ok(CapTarget::SelfCell),
        "any" => Ok(CapTarget::Any),
        _ => {
            // A specific 64-hex CellId.
            let bytes = parse_hex32(site, s)?;
            Ok(CapTarget::Specific(CellId(bytes)))
        }
    }
}

/// Build a `CapGrant` form (used when a caller wants the birth-time cap surface
/// rather than an in-band `[[grant]]`). Exposed for completeness / the SDK
/// binding; `from_deployment` keeps birth caps empty by design.
pub fn cap_grant(target: CapTarget, permissions: AuthRequired, attenuatable: bool) -> CapGrant {
    CapGrant {
        target,
        max_permissions: permissions,
        attenuatable,
    }
}
