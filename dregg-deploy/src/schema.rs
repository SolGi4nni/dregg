//! The DreggDL surface schema — the serde structs the TOML/JSON text parses
//! into.
//!
//! These are a friendly, *named* skin over the existing serialized core
//! types. A `[[factory]]` row is a `FactoryDescriptor` in surface form; a
//! `[[cell]]` row is a `CreateCellFromFactory` instantiation; a `[[grant]]`
//! row is one `Effect::GrantCapability` edge of the authority graph; a
//! `[[fund]]` row is one `Effect::Transfer`. Names — not raw content-addresses
//! — are the ergonomic layer: the resolver ([`crate::resolve`]) turns
//! `factory = "escrow"` / `to = "operator"` into the content-addresses and
//! `CellId`s the lowering needs.

use serde::{Deserialize, Serialize};

/// A whole DreggDL deployment: a federation topology, a set of factory
/// constructor-contracts, the cells born from them, the funding transfers, and
/// the capability-grant edges of the authority graph.
///
/// This is the canonical serde form; the TOML/JSON text is a surface for it.
/// Parse with [`crate::parse_toml`] / [`crate::parse_json`].
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Deployment {
    /// The topology anchor: which federation this deployment binds to.
    pub federation: Federation,
    /// Factory constructor-contracts, keyed by `ref`.
    #[serde(default, rename = "factory")]
    pub factories: Vec<Factory>,
    /// Cells to birth (one `CreateCellFromFactory` each), keyed by `name`.
    #[serde(default, rename = "cell")]
    pub cells: Vec<Cell>,
    /// Funding transfers (one `Effect::Transfer` each).
    #[serde(default, rename = "fund")]
    pub funds: Vec<Fund>,
    /// Capability-grant edges of the authority graph (one
    /// `Effect::GrantCapability` each). Reading all of these off the file
    /// *is* reading the whole dregg cap graph of the deployment — the CapDL
    /// property.
    #[serde(default, rename = "grant")]
    pub grants: Vec<Grant>,
}

/// `[federation]` — the topology anchor. v0 is single-federation.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Federation {
    /// The `FederationId` as 64-char hex of `[u8; 32]`, or `"auto"`/empty to
    /// leave it to the node/SDK at signing time (all-zeros placeholder for the
    /// static lowering). Names like `b3:1f0a…` are accepted with the `b3:`
    /// prefix stripped.
    #[serde(default)]
    pub id: String,
    /// The ingress endpoint (informational for the static lowering; the SDK
    /// uses it at submit time). `"in-process"` for the Rust in-process path.
    #[serde(default)]
    pub node: String,
}

/// `[[factory]]` — a `FactoryDescriptor` in surface form, referenced by `ref`,
/// identified on-chain by its content-address (the descriptor `.hash()`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Factory {
    /// The symbolic name a `[[cell]].factory` resolves to.
    pub r#ref: String,
    /// `CellMode` of cells this factory produces: `"hosted"` | `"sovereign"`.
    #[serde(default = "default_mode")]
    pub default_mode: String,
    /// The factory's on-chain VK (32-byte hex) — the identity the born cell's
    /// `CreateCellFromFactory` effect names. Set this to a REAL app's published
    /// factory VK (e.g. `starbridge-escrow-market`'s `ESCROW_FACTORY_VK`) to make
    /// the deployment instantiate that exact factory; the `b3:`/`0x`/`vk:`/`tok:`
    /// tags are accepted and stripped. When ABSENT, the lowering derives a
    /// self-contained VK from the descriptor (a deployment that stands alone
    /// without a published circuit). Either way the spec is checkable end-to-end;
    /// pinning it is what binds the deploy to the real on-chain factory.
    #[serde(default)]
    pub factory_vk: Option<String>,
    /// The program VK installed on children (32-byte hex), or absent.
    #[serde(default)]
    pub child_program_vk: Option<String>,
    /// Max cells this factory may create per epoch (`creation_budget`).
    #[serde(default)]
    pub creation_budget: Option<u64>,
    /// The perpetual slot caveats (`StateConstraint`) baked into children.
    #[serde(default, rename = "state_constraint")]
    pub state_constraints: Vec<StateConstraintRow>,
    /// The most this factory may grant (`CapTemplate`s).
    #[serde(default, rename = "allowed_cap_template")]
    pub allowed_cap_templates: Vec<CapTemplateRow>,
}

fn default_mode() -> String {
    "hosted".to_string()
}

/// `[[factory.state_constraint]]` — one perpetual slot caveat. `kind` selects
/// the `StateConstraint` variant; `slot` (and `value` where the variant needs
/// it) parameterize it. Supported `kind`s:
/// `write_once` · `immutable` · `monotonic` · `strict_monotonic` ·
/// `field_equals` (needs `value`) · `field_gte` (needs `value`) ·
/// `field_lte` (needs `value`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct StateConstraintRow {
    pub kind: String,
    pub slot: u8,
    /// The bound/target value for `field_equals` / `field_gte` / `field_lte`
    /// (interpreted as a big-endian u64 in the last 8 bytes of the field).
    #[serde(default)]
    pub value: Option<u64>,
}

/// `[[factory.allowed_cap_template]]` — one `CapTemplate`: the most this
/// factory may grant. `permissions` is an `AuthRequired` name; `target` is
/// `"self"` | `"any"` | a 64-hex `CellId`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CapTemplateRow {
    #[serde(default = "default_perms")]
    pub permissions: String,
    #[serde(default = "default_target")]
    pub target: String,
    #[serde(default)]
    pub attenuatable: bool,
}

fn default_perms() -> String {
    "signature".to_string()
}
fn default_target() -> String {
    "self".to_string()
}

/// `[[cell]]` — a `CreateCellFromFactory` instantiation. `factory` resolves to
/// a `[[factory]].ref`; `name` is the symbolic id `[[grant]]`/`[[fund]]` rows
/// reference.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Cell {
    /// The symbolic name grants/funds resolve to.
    pub name: String,
    /// Which factory births this cell (`-> factory.ref`).
    pub factory: String,
    /// Owner public key (32-byte hex). Defaults to a hash of `name`.
    #[serde(default)]
    pub owner_pubkey: Option<String>,
    /// Token domain (32-byte hex). Defaults to all-zeros (native domain).
    #[serde(default)]
    pub token_id: Option<String>,
    /// `CellMode`: `"hosted"` | `"sovereign"`. Defaults to the factory's mode.
    #[serde(default)]
    pub mode: Option<String>,
    /// The program VK installed on this cell (32-byte hex). Defaults to the
    /// factory's `child_program_vk`.
    #[serde(default)]
    pub program_vk: Option<String>,
    /// Initial field values at birth.
    #[serde(default)]
    pub initial_fields: Vec<FieldRow>,
}

/// `{ slot = N, value = V }` — one initial field assignment.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FieldRow {
    pub slot: u32,
    pub value: u64,
}

/// `[[fund]]` — one `Effect::Transfer` of `amount` computrons `from -> to`.
/// `from`/`to` are cell names (or 64-hex `CellId`s).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Fund {
    pub from: String,
    pub to: String,
    pub amount: u64,
}

/// `[[grant]]` — one `Effect::GrantCapability` edge: cell `from` grants `to` a
/// capability reaching `target` with `permissions`. Names resolve to `CellId`s.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Grant {
    /// The granting cell (name or 64-hex id).
    pub from: String,
    /// The recipient cell (name or 64-hex id).
    pub to: String,
    /// `AuthRequired` name the granted cap requires.
    #[serde(default = "default_perms")]
    pub permissions: String,
    /// The cell the capability reaches. Defaults to `from` (a self-grant /
    /// adopt). Name, 64-hex id, or `"self"` (= `from`).
    #[serde(default)]
    pub target: Option<String>,
    /// Optional expiry height (`0`/absent = no expiry).
    #[serde(default)]
    pub expires_at: Option<u64>,
    /// c-list slot the granted cap occupies (default 0).
    #[serde(default)]
    pub slot: u32,
    /// The capability's effect FACET, restricting which effect KINDS this cap
    /// permits — the human-friendly surface for the `allowed_effects` mask.
    /// Accepts, in order of preference:
    ///
    /// * a named facet — `"read-only"` · `"transfer-only"` · `"state-writer"` ·
    ///   `"admin"` · `"delegator"` · `"all"` (alias `"unrestricted"`);
    /// * a `|`/`+`/`,`-joined list of effect-kind names — `"transfer|emit_event"`,
    ///   `"set_field+emit_event"`, etc. (the `dregg_cell::facet::EFFECT_*` kinds:
    ///   `transfer`, `set_field`, `emit_event`, `grant_capability`,
    ///   `revoke_capability`, `create_cell`, `set_permissions`,
    ///   `set_verification_key`, … — see [`crate::facet::EFFECT_KIND_NAMES`]);
    /// * a raw mask — decimal `"6"` or hex `"0x6"`.
    ///
    /// A subset facet is the attenuation `dregg-userspace-verify` checks along
    /// delegation edges. `None`/absent = unrestricted (top). When BOTH `facet`
    /// and `allowed_effects` are given, `facet` is the canonical surface — but the
    /// lowering errors if they DISAGREE, so the surface is unambiguous.
    #[serde(default)]
    pub facet: Option<String>,
    /// The raw facet mask (the low-level form of [`Grant::facet`]).
    /// `None`/absent = unrestricted. Prefer `facet` for readability; this stays
    /// for round-trip stability and machine-generated specs.
    #[serde(default)]
    pub allowed_effects: Option<u32>,
}
