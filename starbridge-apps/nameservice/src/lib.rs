//! # starbridge-nameservice
//!
//! Greenfield rebuild of the nameservice as a **starbridge-app**: a thin
//! library of `FactoryDescriptor`s plus turn-builder helpers that compose
//! dregg-native primitives only. No `Effect::RegisterName`, no
//! `Authorization::Unchecked`, no `[0u8; 64]` placeholder signatures, no
//! reaching past the framework into `dregg_turn::builder::*`.
//!
//! Companion docs:
//! - `../../../STARBRIDGE-APPS-PLAN.md` §3.1 ("nameservice — recommended
//!   first build") — the per-app design sketch this crate implements.
//! - `../../../SLOT-CAVEATS-DESIGN.md` — the design lane (Lane G) for
//!   slot-level caveats; the `register_name` flow below has a TODO on
//!   the `WriteOnce` constraint that lives there.
//! - `../../../APPS-AS-USERSPACE-AUDIT.md` §1.3 — the userspace audit
//!   that motivated rebuilding nameservice as dregg-native.
//!
//! ## What this crate exports
//!
//! 1. [`name_factory_descriptor`] — the `FactoryDescriptor` for
//!    per-name sovereign cells (rent + ownership state machine). Bakes
//!    in the write-once name-hash slot, the monotone-increasing expiry
//!    slot, the owner-authorization caveats, and a per-epoch creation
//!    budget to rate-limit Sybil registration.
//!
//! 2. [`FACTORY_DESCRIPTORS`] — a slice of all factory descriptors this
//!    starbridge-app contributes. The wasm runtime preloads these at
//!    startup so `window.dregg.createFromFactory(factory_vk, ..)` can
//!    resolve string VKs into real descriptors. (Today the slice has
//!    one entry; the dispute-resolution factory and the registry
//!    factory follow once Tier-2 paired escrow lands — see
//!    `STARBRIDGE-APPS-PLAN.md` §3.1 "Real version".)
//!
//! 3. [`build_register_action`] — turn-builder helper that takes an
//!    [`AppCipherclerk`] and produces a real signed
//!    [`Action`] recording a name registration via
//!    `Effect::SetField` + `Effect::EmitEvent`. No new Effect variant
//!    is introduced.
//!
//! 4. [`build_renew_action`] — increments the registry cell's
//!    `EXPIRY_SLOT` by the configured rent-extension epoch length and
//!    emits a `name-renewed` event. The baked-in `Monotonic(EXPIRY_SLOT)`
//!    caveat enforces the expiry only moves forward; the exact-increment
//!    `FieldDelta` caveat (Tier-1 #1) is not yet baked in.
//!
//! 5. [`build_transfer_action`] — the CURRENT owner re-points the
//!    owner-hash slot and stages the incoming owner's raw key; the
//!    handoff completes with [`build_accept_transfer_action`] (the
//!    incoming owner rotates the authority register to the staged key).
//!    The cell program's [`owner_authorization_constraints`] refuse
//!    both halves from anyone but the respective authorized signer.
//!    Capability handoff (`Effect::GrantCapability` /
//!    `Effect::RevokeCapability`) is the responsibility of the
//!    capability-broker turn that issues *with* this one — kept
//!    separate so this helper stays pure-state.
//!
//! ## The userspace stance
//!
//! "Register a name" is *userspace policy*, not a dregg primitive. The
//! ledger only needs to see:
//!
//! 1. **A name binding** — `SetField(NAME_HASH_SLOT, name_hash)` —
//!    anchoring the registration in cell state.
//! 2. **An owner binding** — `SetField(OWNER_HASH_SLOT, owner_hash)`.
//! 3. **An expiry binding** — `SetField(EXPIRY_SLOT, expiry_height)`.
//! 4. **An event for off-chain indexers** —
//!    `EmitEvent("name-registered", [name_hash, owner_hash])`.
//!
//! If we needed *cell-program-enforced uniqueness* ("the slot at
//! index `NAME_HASH_SLOT` may only be set if its prior value is
//! zero"), that's a **cell program caveat** (`WriteOnce`), not a new
//! `Effect` variant — see the TODO on [`build_register_action`].
//!
//! ## Compatibility with the in-browser DreggRuntime + extension cclerk
//!
//! `build_register_action` returns an [`Action`] carrying a real
//! `Authorization::Signature(..)` produced by the cclerk. That action
//! is what `cclerk::signTurn(turnSpec)` (the extension API
//! surface — see `../../../extension/src/page.ts`) expects to wrap in
//! a `Turn` for submission. The in-browser `DreggRuntime`
//! (`../../../wasm/src/runtime.rs`) executes the resulting turn
//! against the same `dregg_turn::TurnExecutor` code-path that native
//! CLIs use.

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, AuthorizedSet, CapTarget, CapTemplate, CellAffordance,
    CellId, CellMode, CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect,
    EmbeddedExecutor, Event, FactoryDescriptor, FieldElement, FireExecuteError, GatedAffordance,
    InputRef, InspectorDescriptor, StarbridgeAppContext, StateConstraint, TurnReceipt,
    WitnessedPredicate, WitnessedPredicateKind, canonical_program_vk, field_from_bytes,
    field_from_u64, hex_encode_32, symbol,
};

/// The nameservice as a SERVICE CELL on the `invoke()` front door (the
/// cells-as-service-objects face): a `register`/`release`/`resolve` registry
/// whose `name → cell` map lives on the per-cell umem-heap, driven through
/// [`dregg_app_framework::invoke`] (no `Effect::Invoke`). The
/// [`FactoryDescriptor`] federation surface in THIS module is unchanged; see
/// [`service`] for the second worked citizen after `starbridge-kvstore`.
pub mod service;

/// The deos-view CARD: the app's UI as a renderer-independent `deos.ui.*`
/// view-tree (pure `serde_json`, no `deos-view` dep). The button `turn` names ARE
/// the [`service`] method vocabulary — one card, three renderers, one registry.
pub mod card;

// =============================================================================
// State schema (per-registry-cell field-slot layout)
// =============================================================================

/// State field slot at which a registered name's hash is anchored.
///
/// Slot indices are 0..16 (per [`dregg_cell::STATE_SLOTS`]); `nonce` and
/// `balance` are *not* in `fields[]` (they live on separate `CellState`
/// accessors), so all 16 slots are addressable. The constants here pin a
/// stable schema so:
///
/// - The factory descriptor's `FieldConstraint::NonZero { field_index:
///   NAME_HASH_SLOT as u32 }` constraint is meaningful.
/// - The wasm-side inspector (`shared/inspectors/name.js`) can index
///   into the cell's state at the same slot.
pub const NAME_HASH_SLOT: usize = 2;

/// State field slot at which the registered name's owner-hash is anchored.
pub const OWNER_HASH_SLOT: usize = 3;

/// State field slot at which the rent expiry block height is recorded.
pub const EXPIRY_SLOT: usize = 4;

/// State field slot at which the name's revocation marker is recorded.
///
/// Zero = active. Non-zero = revoked (the non-zero value is the
/// `field_from_bytes(b"revoked:" || name_hash)` tombstone so the
/// revocation is bound to the name being revoked and replays do not
/// move a different name's tombstone here).
///
/// Carries `StateConstraint::WriteOnce` so revocation is one-way: once
/// set, the slot cannot be cleared or rewritten to a different tombstone.
/// This closes the "owner re-uses a revoked name's cell" gap.
pub const REVOKED_SLOT: usize = 5;

/// State field slot at which the name's resolve target is recorded.
///
/// Free-form 32 bytes; conventionally the BLAKE3 hash of a
/// `dregg://cell/...` URI that the name resolves to. The owner may
/// update this slot at will to point the name at different targets
/// (changing your website's cell, redirecting to a new owner's
/// document, etc.); no `Monotonic` or `WriteOnce` constraint applies.
pub const RESOLVE_TARGET_SLOT: usize = 6;

/// State field slot holding the **raw Ed25519 public key of the current
/// owner** — THE authority register the owner-authorization caveats bind
/// the turn sender against.
///
/// [`OWNER_HASH_SLOT`] stays the blake3 *image* of the owner key (the
/// display/index form off-chain consumers already read); `OWNER_PK_SLOT`
/// carries the raw 32-byte key so `StateConstraint::SenderInSlot` (which
/// compares `ctx.sender`, the raw signer pubkey, against a slot value)
/// can enforce **sender == current owner** on every owner-mutating
/// transition. See [`owner_authorization_constraints`] for the caveat
/// set and the soundness argument.
pub const OWNER_PK_SLOT: usize = 7;

/// State field slot staging the **incoming owner's raw public key**
/// during an ownership handoff (the propose half of propose→accept).
///
/// Written only by the *current* owner (the caveats refuse any other
/// signer). The authority register [`OWNER_PK_SLOT`] may then rotate
/// **only to this staged key, in a turn signed by that key** (the accept
/// half) — ownership moves exactly where the current owner pointed it,
/// never anywhere else. See [`owner_authorization_constraints`].
pub const PENDING_OWNER_PK_SLOT: usize = 8;

// =============================================================================
// Rent / factory configuration
// =============================================================================

/// Default rent-extension window (in blocks) baked into the name factory.
///
/// One year ≈ 31_536_000 seconds; at a notional 6-second block time
/// that's ~5_256_000 blocks. Chosen so a single `renew` extends a
/// name's expiry by one "year" of clock time.
pub const DEFAULT_RENT_EPOCH_BLOCKS: u64 = 5_256_000;

/// Creation budget per epoch baked into the name factory.
///
/// Rate-limits Sybil registration: at most 10_000 names may be
/// created per epoch from this factory.
pub const DEFAULT_CREATION_BUDGET: u64 = 10_000;

/// The factory VK we publish for the name factory.
///
/// In a real deployment this is the BLAKE3 hash of the
/// `NAMESERVICE_NAME_PROGRAM_VK` cell-program VK. We bake a stable
/// placeholder here so the descriptor hash is reproducible across
/// builds; the eventual real-program VK replacement is a single
/// constant change.
pub const NAME_FACTORY_VK: [u8; 32] = *b"starbridge-nameservice-factory!!";

/// The child cell-program installed on per-name cells.
///
/// Per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1: every cell produced by
/// [`name_factory_descriptor`] carries this `CellProgram` (or, more
/// precisely, the AIR that enforces it post-recursion). The VK
/// returned by [`name_child_program_vk`] is the canonical hash of
/// this program's postcard encoding; any validator with the program
/// can re-derive the VK and re-execute against witness data.
///
/// The constraint set:
/// - `WriteOnce(NAME_HASH_SLOT)` — names cannot be re-bound.
/// - `Monotonic(EXPIRY_SLOT)`     — rent extensions only push forward.
/// - `WriteOnce(REVOKED_SLOT)`    — revocations are one-way.
/// - [`owner_authorization_constraints`] — owner-mutating writes are
///   refused unless the turn's **sender is the current owner** (and
///   authority rotation is a staged, accepted handoff).
///
/// Lifted as an `Always`-guarded `CellProgram::Cases` so future
/// operation-scoped cases can be added without restructuring.
pub fn name_cell_program() -> CellProgram {
    let mut constraints = vec![
        StateConstraint::WriteOnce {
            index: NAME_HASH_SLOT as u8,
        },
        StateConstraint::Monotonic {
            index: EXPIRY_SLOT as u8,
        },
        StateConstraint::WriteOnce {
            index: REVOKED_SLOT as u8,
        },
    ];
    constraints.extend(owner_authorization_constraints());
    CellProgram::always(constraints)
}

/// **The owner-authorization caveats** — the cell-program teeth that make an
/// unauthorized owner-change a REAL refusal at the constraint layer (not
/// just at the signature/cap layers above it).
///
/// The problem these close: the slot caveats used to be silent about *who*
/// may write [`OWNER_HASH_SLOT`], so an impostor's `SetField(OWNER_HASH_SLOT, ..)`
/// passed `CellProgram::evaluate` (the executor's per-cell program check).
///
/// The mechanism. Every sender-reading atom in the constraint language
/// (`SenderInSlot`, `SenderAuthorized{PublicRoot}`) binds the **post-state**
/// slot value — read alone on the mutated slot, that is the *seizure* pole
/// ("the slot moved to whoever signed"). The sound form is the conjunction
/// of single-level disjunctions
///
/// ```text
/// (WriteOnce(s) ∨ SenderInSlot(auth)) ∧ (WriteOnce(s) ∨ Immutable(auth))
/// ```
///
/// which distributes to `WriteOnce(s) ∨ (SenderInSlot(auth) ∧ Immutable(auth))`:
/// past the first write, slot `s` may move only in a turn whose sender equals
/// the post-state authority register — and the register is frozen in that same
/// turn, so post-state == pre-state == **the CURRENT owner**. `ctx.sender` is
/// the raw signer pubkey the executor binds from the verified turn parent, so
/// the authority register ([`OWNER_PK_SLOT`]) holds the owner's *raw* key
/// (while [`OWNER_HASH_SLOT`] keeps the blake3 image for display/indexing).
///
/// The full set (F1–F7, all `SimpleStateConstraint`s under single-level
/// `AnyOf` — no new kernel atoms):
///
/// - **F1/F2 (the owner-field gate):** `OWNER_HASH_SLOT` moves only on its
///   first write (registration, from zero) or by the current owner.
/// - **F3/F4/F5 (accepted handoff):** `OWNER_PK_SLOT` rotates only in a turn
///   *signed by the incoming key* (F3: sender == new value), *to the staged
///   key* (F4: sender == staged value ⇒ new == staged), with the staging
///   register frozen (F5) — so the staged value is the one the current owner
///   authorized, and an atomic stage-and-seize turn is refused.
/// - **F6 (owner-only staging):** `PENDING_OWNER_PK_SLOT` moves only by the
///   current owner (with F5 forcing the authority register immutable in any
///   staging turn past its first write).
/// - **F7 (no ownerless names):** any state with a bound owner image carries
///   a non-zero authority register — a registration that "forgets" the
///   authority register (leaving it seizable via first-write) is refused.
///
/// Together: **register** stays permissionless-first-write; **renew /
/// revoke / set-target** are untouched (no owner slot moves); **transfer**
/// is the owner-signed re-point + stage ([`build_transfer_action`]) followed
/// by the incoming owner's acceptance ([`build_accept_transfer_action`]).
/// An impostor can neither move the owner image, nor stage, nor rotate the
/// authority register — each path fails one of F1–F7 (fail-closed: a
/// missing sender context refuses too).
pub fn owner_authorization_constraints() -> Vec<StateConstraint> {
    use dregg_cell::program::SimpleStateConstraint as S;
    let oh = OWNER_HASH_SLOT as u8;
    let opk = OWNER_PK_SLOT as u8;
    let pend = PENDING_OWNER_PK_SLOT as u8;
    vec![
        // F1 — owner-image writes are owner-authorized.
        StateConstraint::AnyOf {
            variants: vec![S::WriteOnce { index: oh }, S::SenderInSlot { index: opk }],
        },
        // F2 — ...with the authority register frozen in the same turn
        // (so F1's post-state read IS the current owner).
        StateConstraint::AnyOf {
            variants: vec![S::WriteOnce { index: oh }, S::Immutable { index: opk }],
        },
        // F3 — authority rotation is signed by the incoming key.
        StateConstraint::AnyOf {
            variants: vec![S::WriteOnce { index: opk }, S::SenderInSlot { index: opk }],
        },
        // F4 — the incoming key must be the STAGED key.
        StateConstraint::AnyOf {
            variants: vec![S::WriteOnce { index: opk }, S::SenderInSlot { index: pend }],
        },
        // F5 — the staging register is frozen during rotation (the staged
        // value is the pre-state, owner-authorized one; also refuses an
        // atomic stage-and-seize turn).
        StateConstraint::AnyOf {
            variants: vec![S::WriteOnce { index: opk }, S::Immutable { index: pend }],
        },
        // F6 — staging is owner-authorized.
        StateConstraint::AnyOf {
            variants: vec![S::Immutable { index: pend }, S::SenderInSlot { index: opk }],
        },
        // F7 — an owned name always carries a non-zero authority register
        // (closes the "register the image, leave the authority register
        // zero/seizable-by-first-write" gap).
        StateConstraint::AnyOf {
            variants: vec![
                S::FieldEquals {
                    index: oh,
                    value: [0u8; 32],
                },
                S::Not(Box::new(S::FieldEquals {
                    index: opk,
                    value: [0u8; 32],
                })),
            ],
        },
    ]
}

/// The child cell program VK installed on per-name cells.
///
/// Computed canonically per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1:
/// `canonical_program_vk(&name_cell_program())`. This makes the VK a
/// re-execution recipe — any validator with [`name_cell_program`] in
/// scope can confirm the VK binds to a program they can execute
/// against witness data.
///
/// Previously a byte-string placeholder
/// (`*b"starbridge-nameservice-childprog"`); the canonical version
/// makes the substrate honest pre-recursion.
pub fn name_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&name_cell_program())
}

// =============================================================================
// FactoryDescriptors (the constructor transparency)
// =============================================================================

/// Build the `FactoryDescriptor` for the per-name sovereign-cell factory.
///
/// Pins the constructor contract anyone can audit by hashing the
/// descriptor:
///
/// - `child_program_vk = name_child_program_vk()` — the rent +
///   ownership state machine.
/// - `default_mode = Sovereign` — names live as their own cells, not
///   inside a host.
/// - `creation_budget = DEFAULT_CREATION_BUDGET` (rate-limits Sybil
///   registration to 10_000 per epoch).
/// - `allowed_cap_templates = [owner_cap]` — the factory may grant a
///   single attenuatable, signature-authorized capability to the
///   creator (the owner cap). Renewal, transfer, sub-delegation are
///   all derived from the owner cap via attenuation
///   (`Caveat::ResourcePrefix`, etc.); the factory itself does not
///   mint those separately.
/// - `field_constraints` (creation-time): every created name cell *must*
///   initialize its `NAME_HASH_SLOT` and `EXPIRY_SLOT` to non-zero
///   values. These run once at constructor invocation.
/// - `state_constraints` (perpetual / Lane G slot caveats):
///   - `StateConstraint::WriteOnce { index: NAME_HASH_SLOT }` — the
///     name-hash slot may only be written from `FIELD_ZERO`. After the
///     first registration the slot is frozen for the cell's lifetime.
///     This closes `APPS-USERSPACE-GAPS.md` Gap 1 ("name-hash slot may
///     only be written once") — the gap that the
///     `SLOT-CAVEATS-DESIGN.md` TODO above pointed at.
///   - `StateConstraint::Monotonic { index: EXPIRY_SLOT }` — rent
///     extensions may only push the expiry *forward*; an attacker
///     cannot shorten a rental they've already sold by writing a
///     smaller expiry value.
pub fn name_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: NAME_FACTORY_VK,
        child_program_vk: Some(name_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(name_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // No creation-time `field_constraints`: a freshly-minted name cell is
        // born empty (all slots zero) and its FIRST `register_name` turn writes
        // the real `NAME_HASH` + `EXPIRY` under the perpetual caveats below.
        // (`FieldConstraint::NonZero` validated against `params.initial_fields`,
        // which a factory birth cannot carry the real 32-byte hash through — it
        // forced the seed path to mint a `1` placeholder. Mirror
        // privacy-voting/bounty-board: drop the birth NonZero, let `WriteOnce`
        // admit the first write from zero.)
        field_constraints: vec![],
        state_constraints: {
            let mut cs = vec![
                StateConstraint::WriteOnce {
                    index: NAME_HASH_SLOT as u8,
                },
                StateConstraint::Monotonic {
                    index: EXPIRY_SLOT as u8,
                },
                StateConstraint::WriteOnce {
                    index: REVOKED_SLOT as u8,
                },
            ];
            // Owner authorization (see `owner_authorization_constraints`):
            // an owner-mutating write is refused unless the sender IS the
            // current owner; authority rotation is a staged, accepted
            // handoff. Appended after the three legacy caveats so existing
            // error-shape consumers (WriteOnce/Monotonic matchers) see the
            // same first-violation ordering.
            cs.extend(owner_authorization_constraints());
            cs
        },
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// The full slice of factory descriptors this starbridge-app contributes.
///
/// Today: one entry (the name factory). Future:
/// - A `dispute_factory` for the paired-escrow dispute flow (blocked
///   on Tier-2 #6, paired escrow).
/// - A `registry_factory` for the federation-attested reverse-index
///   `CommittedMap<TargetUri, NameId>` cell (blocked on Tier-2 #10,
///   `CommittedMap<K, V>`).
///
/// Returned as a `Vec` (not `&'static [..]`) because
/// `FactoryDescriptor` carries non-`const`-constructible
/// `Vec<CapTemplate>` / `Vec<FieldConstraint>` fields. Hosts call
/// this once at startup and stash the result.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![name_factory_descriptor()]
}

// =============================================================================
// Turn-builders (signed actions consuming only generic Effects)
// =============================================================================

/// Build the on-ledger [`Action`] that records a name registration.
///
/// The action carries five effects:
///
/// 1. `SetField(cell=registry_cell, index=NAME_HASH_SLOT, value=name_hash)`
///    — anchors the name binding in the cell's state.
/// 2. `SetField(cell=registry_cell, index=OWNER_HASH_SLOT, value=owner_hash)`
///    — anchors the owner image (`blake3(owner)`).
/// 3. `SetField(cell=registry_cell, index=OWNER_PK_SLOT, value=owner)`
///    — anchors the raw owner key as THE authority register the
///    owner-authorization caveats bind the turn sender against (see
///    [`owner_authorization_constraints`]).
/// 4. `SetField(cell=registry_cell, index=EXPIRY_SLOT, value=expiry_height)`
///    — anchors the rent expiry. The on-cell `FieldDelta` constraint
///    (when Tier-1 #1 lands) enforces subsequent `renew_name` turns
///    increment exactly by `DEFAULT_RENT_EPOCH_BLOCKS`.
/// 5. `EmitEvent(cell=registry_cell, topic="name-registered",
///    data=[name_hash, owner_hash, expiry])` — surfaces the
///    registration for off-chain indexers.
///
/// The action is signed by the framework's [`AppCipherclerk`]; the
/// signature binds to the cipherclerk's `federation_id`.
///
/// # Slot-caveat enforcement
///
/// The "name-hash slot may only be written once" guarantee is now
/// enforced by [`name_factory_descriptor`]'s
/// `StateConstraint::WriteOnce { index: NAME_HASH_SLOT }` — every name
/// cell carries this caveat on its `CellProgram`, and the executor
/// rejects any subsequent `SetField(NAME_HASH_SLOT, ..)` that would
/// overwrite a non-zero slot. Likewise,
/// `StateConstraint::Monotonic { index: EXPIRY_SLOT }` prevents
/// expiry decreases. See `SLOT-CAVEATS-DESIGN.md` and
/// `SLOT-CAVEATS-EVALUATION.md` for the Lane G design that landed
/// these.
pub fn build_register_action(
    cipherclerk: &AppCipherclerk,
    registry_cell: CellId,
    name: &str,
    owner: [u8; 32],
    expiry_height: u64,
) -> Action {
    let name_hash = field_from_bytes(name.as_bytes());
    let owner_hash = field_from_bytes(&owner);
    let expiry_field = field_from_u64(expiry_height);

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: NAME_HASH_SLOT,
            value: name_hash,
        },
        Effect::SetField {
            cell: registry_cell,
            index: OWNER_HASH_SLOT,
            value: owner_hash,
        },
        // The authority register: the raw owner pubkey the
        // owner-authorization caveats bind the turn sender against.
        // Written atomically with the owner image — a registration that
        // omitted it would be refused by the caveats' "no ownerless
        // names" tooth (see `owner_authorization_constraints`).
        Effect::SetField {
            cell: registry_cell,
            index: OWNER_PK_SLOT,
            value: owner,
        },
        Effect::SetField {
            cell: registry_cell,
            index: EXPIRY_SLOT,
            value: expiry_field,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(
                symbol("name-registered"),
                vec![name_hash, owner_hash, expiry_field],
            ),
        },
    ];

    cipherclerk.make_action(registry_cell, "register_name", effects)
}

/// Build the on-ledger [`Action`] that extends a name's rent.
///
/// Emits a `name-renewed` event and updates the `EXPIRY_SLOT` to
/// `new_expiry_height = old_expiry + rent_epoch_blocks`. The caller is
/// responsible for reading the prior expiry off the cell state and
/// supplying the correct `new_expiry_height` — when the
/// `FieldDelta(EXPIRY_SLOT, +rent_epoch_blocks)` constraint (Tier 1 #1)
/// lands on the cell program, an off-by-one will be rejected at
/// execution time.
pub fn build_renew_action(
    cipherclerk: &AppCipherclerk,
    registry_cell: CellId,
    name: &str,
    new_expiry_height: u64,
) -> Action {
    let name_hash = field_from_bytes(name.as_bytes());
    let new_expiry_field = field_from_u64(new_expiry_height);

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: EXPIRY_SLOT,
            value: new_expiry_field,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(symbol("name-renewed"), vec![name_hash, new_expiry_field]),
        },
    ];

    cipherclerk.make_action(registry_cell, "renew_name", effects)
}

/// Build the on-ledger [`Action`] that records a name-owner transfer —
/// **the propose half, signed by the CURRENT owner**.
///
/// Updates `OWNER_HASH_SLOT` (the owner image), stages the incoming
/// owner's raw key in [`PENDING_OWNER_PK_SLOT`], and emits
/// `name-transferred` with the old/new owner hashes. The cell program's
/// owner-authorization caveats ([`owner_authorization_constraints`])
/// admit this action **only when the executor-verified sender is the
/// current owner** (the key in [`OWNER_PK_SLOT`]); an impostor's
/// transfer is refused at the constraint layer.
///
/// The handoff completes when the incoming owner fires
/// [`build_accept_transfer_action`], rotating the authority register
/// [`OWNER_PK_SLOT`] to the staged key. Until acceptance, authority
/// remains with the proposing owner (who may freely re-stage).
///
/// Capability handoff (`Effect::GrantCapability` to the new owner /
/// `Effect::RevokeCapability` from the old owner) is intentionally
/// *not* part of this action — capability brokerage is the
/// responsibility of the issuer turn that pairs with this one,
/// because the broker's identity is typically distinct from the
/// owner's. Composing them at the call-site (rather than
/// hard-coding the pair here) keeps the helper pure-state.
pub fn build_transfer_action(
    cipherclerk: &AppCipherclerk,
    registry_cell: CellId,
    name: &str,
    old_owner: [u8; 32],
    new_owner: [u8; 32],
) -> Action {
    let name_hash = field_from_bytes(name.as_bytes());
    let old_hash = field_from_bytes(&old_owner);
    let new_hash = field_from_bytes(&new_owner);

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: OWNER_HASH_SLOT,
            value: new_hash,
        },
        // Stage the incoming owner's raw key — the accept half
        // (`build_accept_transfer_action`) may rotate the authority
        // register ONLY to this owner-authorized value.
        Effect::SetField {
            cell: registry_cell,
            index: PENDING_OWNER_PK_SLOT,
            value: new_owner,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(
                symbol("name-transferred"),
                vec![name_hash, old_hash, new_hash],
            ),
        },
    ];

    cipherclerk.make_action(registry_cell, "transfer_name", effects)
}

/// Build the on-ledger [`Action`] that **completes** a name-owner
/// transfer — the accept half, signed by the INCOMING owner.
///
/// Rotates the authority register [`OWNER_PK_SLOT`] to `new_owner` and
/// emits `name-transfer-accepted`. The owner-authorization caveats
/// ([`owner_authorization_constraints`]) admit this **only** when:
///
/// - the turn's sender is `new_owner` itself (the rotation is signed by
///   the incoming key), AND
/// - `new_owner` equals the key staged in [`PENDING_OWNER_PK_SLOT`] by
///   the *current* owner's [`build_transfer_action`].
///
/// So the authority register moves exactly where the current owner
/// pointed it, and only with the incoming owner's own signature —
/// neither the current owner alone (no acceptance) nor an impostor
/// (not staged) can rotate it.
pub fn build_accept_transfer_action(
    cipherclerk: &AppCipherclerk,
    registry_cell: CellId,
    name: &str,
    new_owner: [u8; 32],
) -> Action {
    let name_hash = field_from_bytes(name.as_bytes());
    let new_hash = field_from_bytes(&new_owner);

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: OWNER_PK_SLOT,
            value: new_owner,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(symbol("name-transfer-accepted"), vec![name_hash, new_hash]),
        },
    ];

    cipherclerk.make_action(registry_cell, "accept_transfer_name", effects)
}

/// Build the on-ledger [`Action`] that revokes a name.
///
/// Sets the [`REVOKED_SLOT`] to a tombstone value that binds the
/// revocation to this specific name (so a replay can't move a tombstone
/// from one cell to another to "revoke" a different name), and emits a
/// `name-revoked` event for off-chain indexers.
///
/// # Slot-caveat enforcement
///
/// The [`name_factory_descriptor`]'s
/// `StateConstraint::WriteOnce { index: REVOKED_SLOT }` makes revocation
/// one-way: once the slot transitions from `FIELD_ZERO` to a tombstone,
/// the executor rejects any subsequent write. A revoked name cannot be
/// "un-revoked" by the owner, nor moved to a different tombstone.
pub fn build_revoke_action(
    cipherclerk: &AppCipherclerk,
    registry_cell: CellId,
    name: &str,
) -> Action {
    let name_hash = field_from_bytes(name.as_bytes());
    let tombstone = revoked_tombstone(name);

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: REVOKED_SLOT,
            value: tombstone,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(symbol("name-revoked"), vec![name_hash, tombstone]),
        },
    ];

    cipherclerk.make_action(registry_cell, "revoke_name", effects)
}

/// Build the on-ledger [`Action`] that re-points a name's resolve target.
///
/// Updates [`RESOLVE_TARGET_SLOT`] to a new 32-byte target (conventionally
/// `field_from_bytes(target_uri.as_bytes())` where `target_uri` is the
/// `dregg://cell/<id>` URI the name should resolve to) and emits a
/// `name-target-set` event.
///
/// The resolve-target slot carries no `Monotonic` or `WriteOnce`
/// constraint (a name's owner may freely re-point the name at any
/// target). The `WriteOnce { index: NAME_HASH_SLOT }` invariant means
/// the binding `name -> cell` is permanent, but the binding
/// `cell -> target` is mutable — exactly the semantics a hierarchical
/// nameservice wants.
pub fn build_set_target_action(
    cipherclerk: &AppCipherclerk,
    registry_cell: CellId,
    name: &str,
    target: FieldElement,
) -> Action {
    let name_hash = field_from_bytes(name.as_bytes());

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: RESOLVE_TARGET_SLOT,
            value: target,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(symbol("name-target-set"), vec![name_hash, target]),
        },
    ];

    cipherclerk.make_action(registry_cell, "set_name_target", effects)
}

/// Compute the canonical revocation tombstone for a name.
///
/// Public so off-chain indexers / cross-app code can reproduce it.
/// The tombstone is `field_from_bytes(b"dregg-nameservice-revoked:" || name_bytes)`,
/// which is content-addressed to the name being revoked. This means:
///
/// - A replay attacker cannot move one name's tombstone into another
///   cell's REVOKED_SLOT to "revoke" a different name; the value would
///   not match `revoked_tombstone(other_name)`.
/// - The same name always produces the same tombstone, so verifiers
///   can confirm "this slot value is the canonical tombstone for
///   *this* name".
pub fn revoked_tombstone(name: &str) -> FieldElement {
    let mut input = Vec::with_capacity(b"dregg-nameservice-revoked:".len() + name.len());
    input.extend_from_slice(b"dregg-nameservice-revoked:");
    input.extend_from_slice(name.as_bytes());
    field_from_bytes(&input)
}

/// Convenience: hash a name string to its canonical 32-byte field.
///
/// Public for off-chain indexers + cross-app code that wants to
/// reproduce the value the executor sees in `NAME_HASH_SLOT`.
pub fn name_hash(name: &str) -> FieldElement {
    field_from_bytes(name.as_bytes())
}

/// Convenience: encode a u64 as the canonical big-endian-padded
/// [`FieldElement`] used by the nameservice's `EXPIRY_SLOT`.
pub fn expiry_field(expiry_height: u64) -> FieldElement {
    field_from_u64(expiry_height)
}

/// Convenience: hash a target URI string to a [`FieldElement`] suitable
/// for [`RESOLVE_TARGET_SLOT`]. Public so callers can prepare the
/// target value the same way the inspector chain expects.
pub fn resolve_target(uri: &str) -> FieldElement {
    field_from_bytes(uri.as_bytes())
}

// =============================================================================
// The deos-native surface — the NAME as a composed `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: nameservice is THE web-of-cells
// keystone. Re-expressed as a composed [`DeosApp`] ([`name_app`] below) and mounted by
// `register(ctx)` (see [`register_deos`]): the framework wires per-viewer projection,
// the generated `<dregg-affordance-surface>` component, the manifest, the rehydratable
// frustum-snapshot — and, the headline here, **web-of-cells publish: each NAME cell is
// a real `dregg://` sturdyref**. That sturdyref is reacquirable across a federation
// membrane, so [`RESOLVE_TARGET_SLOT`] can point a name at a LIVE, reacquirable cell ref
// instead of an opaque `blake3(uri)` digest — the name directory becomes a web OF cells.
//
// **The seam is closed** — a TWO-TEMPO fire (mirror supply-chain-provenance /
// subscription). The three owner-only state-mutating operations (`renew`, `revoke`,
// `set_target`) are [`GatedAffordance`]s carrying a live-state PRECONDITION; the FULL
// name program ([`name_cell_program`] = `WriteOnce(NAME_HASH)` · `Monotonic(EXPIRY)` ·
// `WriteOnce(REVOKED)`) is INSTALLED on the seeded name cell ([`seed_name`]) and
// RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_renew`] / [`fire_revoke`] / [`fire_set_target`] then submit the FULL turn
//      derived from the cell's LIVE state, and the executor RE-ENFORCES the name program
//      — so a REWOUND expiry (`renew` that rolls the rent backward, `Monotonic(EXPIRY)`),
//      an UN-REVOKE (`REVOKED` 1 -> 0, `WriteOnce(REVOKED)`), and a name REBIND
//      (`WriteOnce(NAME_HASH)`) are all REAL executor refusals in the SUBMISSION path —
//      the half the floor's `program.evaluate`-only tests never exercised through a real
//      signed turn (see `tests/deos_seam.rs`).
//
// The htmx tooth: after a `revoke`, the name is dead — `renew` and `set_target` carry the
// `REVOKED == 0` precondition, so they go DARK the instant the tombstone lands.

/// The nameservice rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the roles
/// the floor crate's cap-graph enforces:
///
///   - a RESOLVER (the public / any peer) holds [`AuthRequired::Signature`] — the narrow
///     read tier: it can `resolve` (read [`RESOLVE_TARGET_SLOT`] and reacquire the cell the
///     name points at) and nothing else;
///   - the OWNER holds [`AuthRequired::None`]/root — it can `transfer` (re-key the owner),
///     `renew` (extend the rent), `revoke` (tombstone the name), and `set_target` (re-point
///     the name) on top of resolving.
///
/// So `Signature ⊂ None` IS the resolver ⊂ owner ladder — a two-tier name authority.
pub const RESOLVER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The owner rights tier (root — transfer/renew/revoke/set_target + resolve). See [`RESOLVER_RIGHTS`].
pub const OWNER_RIGHTS: AuthRequired = AuthRequired::None;

/// **The owner-lifecycle method names on a NAME cell** — the deos affordance
/// vocabulary [`name_app`] exposes and the `fire_*` helpers route. Held as shared
/// constants so an affordance's name, its `fire_*` lookup, and the deos-view
/// CARD's button `turn` payload (`src/card.rs`) can never drift apart.
///
/// `register` / `resolve` are the registry-FACE method symbols of the same
/// registry primitive — see [`service::METHOD_REGISTER`] / [`service::METHOD_RESOLVE`]
/// (the `resolve` affordance below IS [`service::METHOD_RESOLVE`]).
pub const METHOD_RENEW: &str = "renew";
/// The OWNER tombstones the name — the one-way `WriteOnce(REVOKED)` op. See [`METHOD_RENEW`].
pub const METHOD_REVOKE: &str = "revoke";
/// The OWNER re-keys [`OWNER_HASH_SLOT`] (a cap-graph re-key). See [`METHOD_RENEW`].
pub const METHOD_TRANSFER: &str = "transfer";
/// The OWNER re-points [`RESOLVE_TARGET_SLOT`] at another reacquirable cell. See [`METHOD_RENEW`].
pub const METHOD_SET_TARGET: &str = "set_target";

/// The **life-of-cell name invariants** the executor re-enforces on every touching turn —
/// exactly [`name_cell_program`] (`WriteOnce(NAME_HASH)` · `Monotonic(EXPIRY)` ·
/// `WriteOnce(REVOKED)`), the same program the factory installs on every born name cell
/// (the one `tests/factory_birth.rs` proves bites on the executor). Installed by
/// [`seed_name`] so the gated fires re-enforce it.
pub fn name_invariants_program() -> CellProgram {
    name_cell_program()
}

/// The **not-revoked precondition** — the name must be ACTIVE (`REVOKED == 0`). A real
/// [`CellProgram`] read against the cell's current state, so an owner-op button is LIT on a
/// live name and goes DARK the instant the name is revoked (the htmx tooth). This gates
/// "may `renew` / `revoke` / `set_target` fire now"; the one-way [`WriteOnce(REVOKED)`]
/// (a re-revoke / un-revoke) is the installed [`name_invariants_program`] the executor
/// re-enforces on the produced transition.
pub fn not_revoked_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: REVOKED_SLOT as u8,
        value: field_from_u64(0),
    }])
}

/// **The nameservice NAME as a composed [`DeosApp`]** — the whole interaction surface, on
/// the deos bones. The name cell is the agent's OWN cell (`cipherclerk.cell_id()`) so fires
/// execute against the seeded embedded ledger.
///
/// Five operations on the NAME cell, on the resolver ⊂ owner rights ladder:
///
///   - `resolve` — a cap-only affordance (a RESOLVER reads the target): `Signature`, an
///     `EmitEvent` reading [`RESOLVE_TARGET_SLOT`]. The published web-of-cells sturdyref is
///     reacquired at THIS tier;
///   - `transfer` — a cap-only affordance (the OWNER re-keys [`OWNER_HASH_SLOT`]):
///     `None`/root, a real `SetField` on the owner slot (an owner re-key is a cap-graph
///     event, not a gated state-machine step — so it is cap-only);
///   - `renew` — a [`GatedAffordance`] (the OWNER extends the rent): `None`/root, the
///     not-revoked PRECONDITION; the real fire ([`fire_renew`]) submits a turn that advances
///     [`EXPIRY_SLOT`] off the LIVE expiry, re-enforced by the executor's `Monotonic(EXPIRY)`;
///   - `revoke` — a [`GatedAffordance`] (the OWNER tombstones the name): `None`/root, the
///     not-revoked PRECONDITION; the real fire ([`fire_revoke`]) sets [`REVOKED_SLOT`] -> 1,
///     re-enforced by the executor's one-way `WriteOnce(REVOKED)`;
///   - `set_target` — a [`GatedAffordance`] (the OWNER re-points the name): `None`/root, the
///     not-revoked PRECONDITION; the real fire ([`fire_set_target`]) sets [`RESOLVE_TARGET_SLOT`].
///
/// The name cell is published into the web-of-cells at the resolver tier (a peer on another
/// federation reacquires the name — and through its `resolve`, the cell the name points at)
/// and is discoverable under `names`.
///
/// Seed the cell's program + genesis state with [`seed_name`] so the gated fires have a live
/// state and the executor re-enforces the invariants.
pub fn name_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let cell = cipherclerk.cell_id();

    // `resolve` — a RESOLVER reads the target. Cap-only; an `EmitEvent` reading
    // RESOLVE_TARGET_SLOT. This is the affordance the published web-of-cells sturdyref
    // exposes at the resolver tier — a peer reacquires the name AND follows it to the cell
    // the target points at.
    let resolve = CellAffordance::new(
        service::METHOD_RESOLVE,
        RESOLVER_RIGHTS,
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("name-resolved"),
                vec![field_from_u64(RESOLVE_TARGET_SLOT as u64)],
            ),
        },
    );
    // `transfer` — the OWNER re-keys the owner slot. Cap-only (a cap-graph re-key, no gated
    // state-machine step), carrying the real `SetField` on OWNER_HASH_SLOT.
    let transfer = CellAffordance::new(
        METHOD_TRANSFER,
        OWNER_RIGHTS,
        Effect::SetField {
            cell,
            index: OWNER_HASH_SLOT,
            value: signer_owner_hash(cipherclerk),
        },
    );
    // `renew` — the OWNER extends the rent. The GatedAffordance carries the DECISIVE effect
    // (the EXPIRY advance) as its surface representative AND the not-revoked PRECONDITION — so
    // the button is dark on a revoked name and lit on a live one (the htmx tooth), and the
    // cap∧state gate decides its verdict in-band. The actual fire ([`fire_renew`]) submits a
    // turn that advances EXPIRY off the LIVE expiry, which the executor re-enforces
    // `Monotonic(EXPIRY)` on — so a REWOUND expiry is REFUSED.
    let renew = GatedAffordance::new(
        CellAffordance::new(
            METHOD_RENEW,
            OWNER_RIGHTS,
            Effect::SetField {
                cell,
                index: EXPIRY_SLOT,
                value: field_from_u64(DEFAULT_RENT_EPOCH_BLOCKS),
            },
        ),
        not_revoked_precondition(),
    );
    // `revoke` — the OWNER tombstones the name. The decisive effect sets REVOKED -> 1; gated
    // on the not-revoked precondition (a live name). The executor re-enforces the one-way
    // `WriteOnce(REVOKED)` (a re-revoke / un-revoke is a real refusal).
    let revoke = GatedAffordance::new(
        CellAffordance::new(
            METHOD_REVOKE,
            OWNER_RIGHTS,
            Effect::SetField {
                cell,
                index: REVOKED_SLOT,
                value: field_from_u64(1),
            },
        ),
        not_revoked_precondition(),
    );
    // `set_target` — the OWNER re-points the name. The decisive effect writes
    // RESOLVE_TARGET_SLOT; gated on the not-revoked precondition. (RESOLVE_TARGET carries no
    // slot caveat, so the executor admits any re-point on a live name; once revoked, the
    // precondition darkens it.)
    let set_target = GatedAffordance::new(
        CellAffordance::new(
            METHOD_SET_TARGET,
            OWNER_RIGHTS,
            Effect::SetField {
                cell,
                index: RESOLVE_TARGET_SLOT,
                value: resolve_target("dregg://cell/placeholder"),
            },
        ),
        not_revoked_precondition(),
    );

    DeosApp::builder("nameservice", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["names".into()])
        .cell(
            DeosCell::new(cell, "name")
                .affordance(resolve)
                .affordance(transfer)
                .gated(renew)
                .gated(revoke)
                .gated(set_target)
                .publish(RESOLVER_RIGHTS),
        )
        .build()
}

/// The signer's **owner-hash** — `field_from_bytes(public_key)`, the same shape
/// [`build_transfer_action`] writes into [`OWNER_HASH_SLOT`] (the field image of an owner's
/// pubkey). The `transfer` affordance's effect-template carries the APP signer as a surface
/// representative.
pub fn signer_owner_hash(cipherclerk: &AppCipherclerk) -> FieldElement {
    field_from_bytes(&cipherclerk.public_key().0)
}

/// **Seed the NAME cell** so the gated fires have live state + the caveats bite: install the
/// full [`name_invariants_program`] on the seeded name cell (so the executor re-enforces it
/// on every touching turn), then bind the genesis state directly into the embedded ledger —
/// `NAME_HASH` + `OWNER_HASH` (`WriteOnce`, frozen after), `EXPIRY = initial_expiry`, and
/// `REVOKED = 0` (active).
///
/// After seeding, the name is registered + active with `EXPIRY = initial_expiry` — a real
/// `(old, new)` baseline against which `renew` advances the expiry, `revoke` tombstones, and
/// `set_target` re-points. Returns the seeded `NAME_HASH` digest.
pub fn seed_name(
    executor: &EmbeddedExecutor,
    name: &str,
    owner: [u8; 32],
    initial_expiry: u64,
) -> FieldElement {
    let cell = executor.cell_id();
    executor.install_program(cell, name_invariants_program());
    let nh = field_from_bytes(name.as_bytes());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state.set_field(NAME_HASH_SLOT, nh);
            c.state.set_field(OWNER_HASH_SLOT, field_from_bytes(&owner));
            // The authority register: the raw owner key the
            // owner-authorization caveats bind the turn sender against.
            c.state.set_field(OWNER_PK_SLOT, owner);
            c.state
                .set_field(EXPIRY_SLOT, field_from_u64(initial_expiry));
            c.state.set_field(REVOKED_SLOT, field_from_u64(0));
        }
    });
    nh
}

/// **Fire `renew`** — the deos cap∧state PRECONDITION gate (cap ⊇ root AND the name is
/// active), then a turn that advances [`EXPIRY_SLOT`] off the cell's LIVE expiry (by
/// [`DEFAULT_RENT_EPOCH_BLOCKS`]). The two-tempo bridge: the gated affordance decides the
/// button in-band (nothing submitted on a precondition miss); on passing, the executor's
/// re-enforcement of `Monotonic(EXPIRY)` is the SECOND, verified gate — a REWOUND expiry is
/// a real refusal. Because the new expiry is read from live state, the renew advances each
/// time (the state-parameterized fire). Use [`seed_name`] first.
pub fn fire_renew(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let name_cell = cell.cell();
    cell.fire_gated_through_executor_with(METHOD_RENEW, held, cipherclerk, executor, |state| {
        // The new expiry advances the LIVE expiry by one rent epoch (Monotonic(EXPIRY) holds).
        let live_expiry = field_to_u64(&state.fields[EXPIRY_SLOT]);
        let new_expiry = live_expiry + DEFAULT_RENT_EPOCH_BLOCKS;
        vec![
            Effect::SetField {
                cell: name_cell,
                index: EXPIRY_SLOT,
                value: field_from_u64(new_expiry),
            },
            Effect::EmitEvent {
                cell: name_cell,
                event: Event::new(symbol("name-renewed"), vec![field_from_u64(new_expiry)]),
            },
        ]
    })
}

/// **Fire `revoke`** — the deos cap∧state PRECONDITION gate (cap ⊇ root AND the name is
/// active), then a turn that sets [`REVOKED_SLOT`] -> 1 (a tombstone). The executor
/// re-enforces the one-way `WriteOnce(REVOKED)` — once set, the slot is frozen, so a second
/// revoke / an un-revoke is a real refusal. Use [`seed_name`] first.
pub fn fire_revoke(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let name_cell = cell.cell();
    cell.fire_gated_through_executor_with(METHOD_REVOKE, held, cipherclerk, executor, |_state| {
        vec![
            Effect::SetField {
                cell: name_cell,
                index: REVOKED_SLOT,
                value: field_from_u64(1),
            },
            Effect::EmitEvent {
                cell: name_cell,
                event: Event::new(symbol("name-revoked"), vec![field_from_u64(1)]),
            },
        ]
    })
}

/// **Fire `set_target`** — the deos cap∧state PRECONDITION gate (cap ⊇ root AND the name is
/// active), then a turn that re-points [`RESOLVE_TARGET_SLOT`] at `target`. The web-of-cells
/// payoff: after [`DeosApp::publish_all`] mints the name cell's `dregg://` sturdyref, an
/// owner points the name at ANOTHER reacquirable cell ref via this fire — the name directory
/// is a web OF cells. Use [`seed_name`] first.
pub fn fire_set_target(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    target: FieldElement,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let name_cell = cell.cell();
    cell.fire_gated_through_executor_with(
        METHOD_SET_TARGET,
        held,
        cipherclerk,
        executor,
        move |_state| {
            vec![
                Effect::SetField {
                    cell: name_cell,
                    index: RESOLVE_TARGET_SLOT,
                    value: target,
                },
                Effect::EmitEvent {
                    cell: name_cell,
                    event: Event::new(symbol("name-target-set"), vec![target]),
                },
            ]
        },
    )
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the `EXPIRY` counter the name cell stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Register the nameservice starbridge-app on a [`StarbridgeAppContext`].
///
/// Concrete `register(ctx)` hook a host calls at startup to bind this
/// app's factory descriptors and inspector surfaces into the shared
/// context. After this call:
///
/// - `ctx.factory_registry().get(&NAME_FACTORY_VK)` returns the
///   [`name_factory_descriptor`]. The in-browser DreggRuntime can
///   resolve `window.dregg.createFromFactory(NAME_FACTORY_VK, ..)`
///   against the host's HTTP descriptor service backed by this
///   registry.
/// - `ctx.inspector_registry().get("name")` returns the
///   [`InspectorDescriptor`] pointing the Studio at
///   `/starbridge-apps/nameservice/inspectors.js` for any
///   `<dregg-name uri="..."/>` mount.
/// - `ctx.inspector_registry().get("name-registry")` returns the
///   parent-list inspector (the registry-cell view that links
///   into individual name cells).
///
/// Returns the registered `factory_vk` so the host can log or
/// surface it.
///
/// ## Typical host wiring
///
/// ```ignore
/// use dregg_app_framework::{
///     AgentCipherclerk, AppServer, AppConfig, AppCipherclerk, EmbeddedExecutor,
///     StarbridgeAppContext,
/// };
///
/// #[tokio::main]
/// async fn main() {
///     let federation_id = [42u8; 32];
///     let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), federation_id);
///     let executor = EmbeddedExecutor::new(&cipherclerk, "default");
///     let ctx = StarbridgeAppContext::new(cipherclerk.clone(), executor.clone());
///
///     // Each starbridge-app contributes its factories + inspectors.
///     starbridge_nameservice::register(&ctx);
///     // starbridge_identity::register(&ctx);
///     // ...
///
///     AppServer::new(AppConfig::from_env())
///         .service_name("starbridge-host")
///         .with_health()
///         .with_cors()
///         .with_cipherclerk(cipherclerk)
///         .with_embedded_executor(executor)
///         .with_starbridge(ctx)
///         .serve()
///         .await
///         .unwrap();
/// }
/// ```
///
/// Per-handler use: extract `axum::Extension<StarbridgeAppContext>`
/// and reach `ctx.cipherclerk()`, `ctx.executor()`, or
/// `ctx.factory_registry()` uniformly across all starbridge-apps
/// mounted on the same host.
/// The canonical web-constants module for this app — a single source of truth
/// for the slot indices, factory-vk, and event topics.
///
/// Every value here is read from this crate's `pub const`s (slot indices,
/// factory-vk) and `symbol(..)` topic strings, so any consumer cannot drift from
/// the executor's slot layout / event vocabulary. The `web_constants_slots_match_pub_consts`
/// test (`tests/constants_js_drift.rs`) pins it to the `pub const`s. (The legacy
/// `pages/` web bundle has been retired in favour of the deos-view CARD,
/// `src/card.rs`.)
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("nameservice")
        .slot("NAME_HASH_SLOT", NAME_HASH_SLOT as u64)
        .slot("OWNER_HASH_SLOT", OWNER_HASH_SLOT as u64)
        .slot("EXPIRY_SLOT", EXPIRY_SLOT as u64)
        .slot("REVOKED_SLOT", REVOKED_SLOT as u64)
        .slot("RESOLVE_TARGET_SLOT", RESOLVE_TARGET_SLOT as u64)
        .slot("OWNER_PK_SLOT", OWNER_PK_SLOT as u64)
        .slot("PENDING_OWNER_PK_SLOT", PENDING_OWNER_PK_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&NAME_FACTORY_VK))
        .string(
            "REVOKED_TOMBSTONE_PREFIX",
            // The exact prefix `revoked_tombstone` hashes (see src/lib.rs).
            "dregg-nameservice-revoked:",
        )
        .topic("REGISTERED", "name-registered")
        .topic("RENEWED", "name-renewed")
        .topic("TRANSFERRED", "name-transferred")
        .topic("REVOKED", "name-revoked")
        .topic("TARGET_SET", "name-target-set")
}

pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    // 1. Register the name factory descriptor. The returned vk is
    // `NAME_FACTORY_VK`; downstream code looks descriptors up by it.
    let factory_vk = ctx.register_factory(name_factory_descriptor());

    // 2. Register the per-name inspector. The descriptor points the
    // Studio runtime at this app's `inspectors.js` module under the
    // `<dregg-name uri="..."/>` webcomponent name. The shape matches
    // `site/_includes/studio/inspectors.js`'s registration grammar.
    ctx.register_inspector(InspectorDescriptor {
        kind: "name".into(),
        descriptor: serde_json::json!({
            "component": "dregg-name",
            "module": "/starbridge-apps/nameservice/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["name_hash", "owner_hash", "expiry", "revoked", "target"],
            "slot_layout": {
                "name_hash":   NAME_HASH_SLOT,
                "owner_hash":  OWNER_HASH_SLOT,
                "expiry":      EXPIRY_SLOT,
                "revoked":     REVOKED_SLOT,
                "target":      RESOLVE_TARGET_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&name_child_program_vk()),
        }),
    });

    // 3. Register the registry-list inspector (the parent view that
    // links to each name cell). Apps with no parent view can skip
    // this; for nameservice it is the "browse all registered names"
    // surface.
    ctx.register_inspector_with("name-registry", || {
        serde_json::json!({
            "component": "dregg-name-registry",
            "module": "/starbridge-apps/nameservice/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "child_inspector": "name",
        })
    });

    // 4. Register the register-form inspector — the mutation surface
    // that wraps `window.dregg.signTurn` with the nameservice's
    // `register_name` / `renew_name` / `transfer_name` / `revoke_name`
    // / `set_name_target` preset builders. The Studio renders this as
    // a side-pane editor when the user is looking at a registry cell
    // and wants to author a turn against it.
    ctx.register_inspector_with("name-register-form", || {
        serde_json::json!({
            "component": "dregg-name-register-form",
            "module": "/starbridge-apps/nameservice/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "builders_module": "/starbridge-apps/nameservice/turn-builders.js",
            "methods": [
                "register_name",
                "renew_name",
                "transfer_name",
                "revoke_name",
                "set_name_target",
            ],
        })
    });

    // 5. Mount the deos-native composition surface (the `DeosApp`) on the SAME context —
    // nameservice is THE web-of-cells keystone (each name cell is a `dregg://` sturdyref).
    // The factory + inspectors are where SOUNDNESS lives (a rebind / expiry-rewind /
    // un-revoke is a real executor refusal on the born cell); the deos surface is the
    // composition skin (per-viewer projection, the cap∧state gated fires, the `dregg://`
    // publish, the rehydratable snapshot, the manifest).
    register_deos(ctx);

    factory_vk
}

/// **Mount the deos-native surface** ([`name_app`]) on a shared context: build the composed
/// [`DeosApp`] from the context's cipherclerk + executor, seed the name cell's program +
/// genesis state (so the gated fires bite), and fold the app into the context's affordance
/// registry ([`DeosApp::register`]). Returns the live [`DeosApp`] (so a host can also
/// [`DeosApp::mount`] its axum router / [`DeosApp::publish_all`] into the web-of-cells — the
/// nameservice keystone: each name cell is exported as a real `dregg://` sturdyref).
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = name_app(ctx.cipherclerk(), ctx.executor());
    // Seed the name cell so the gated `renew` / `revoke` / `set_target` fires have a live
    // `(old, new)` and the full name program (installed here) is re-enforced by the executor
    // on every touching turn. A registered, active name at a real initial expiry.
    seed_name(
        ctx.executor(),
        "deos.dregg",
        ctx.cipherclerk().public_key().0,
        DEFAULT_RENT_EPOCH_BLOCKS,
    );
    app.register(ctx);
    app
}

// =============================================================================
// Cross-app composition: identity-attested registration tier
// =============================================================================
//
// Some federations want a *gated* registration tier: only callers who
// present a verifiable credential of a pinned schema, issued by a known
// identity-issuer cell, may register names. The substrate primitive that
// enables this is `AuthorizedSet::CredentialSet` (cell/src/program.rs);
// the userspace integration is the helper triple below — a tier
// constraint, a registration action that carries the credential proof
// in `witness_blobs`, and a deterministic predicate identifier the
// executor's `WitnessedPredicateRegistry` dispatches against.
//
// The composition is data-only: nameservice does not import the
// identity crate's credential internals. Callers wire the two by
// passing in the issuer cell and a schema commitment (computed via
// `starbridge_identity::schema_commitment`); the resulting constraint
// and predicate agree on the same 32-byte commitment by construction
// (see `AuthorizedSet::credential_set_commitment`).

/// Build the `StateConstraint` clause an identity-attested tier of the
/// nameservice imposes on registration turns.
///
/// Drop this into a `CellProgram::Cases` operation case for
/// `register_name` (or a tier-specific method symbol) when the tier
/// only admits callers who can present a credential of
/// `credential_schema_id` issued by `issuer_cell`. The accompanying
/// `Action` is built with [`build_register_with_credential_action`],
/// which carries the `Presentation` proof bytes in
/// `witness_blobs[proof_witness_index]`.
///
/// The constraint's `AuthorizedSet::CredentialSet { issuer_cell,
/// credential_schema_id }` resolves on the executor side to
/// `blake3_derive_key("dregg-credential-set-v1") || issuer_cell ||
/// credential_schema_id` (per
/// [`AuthorizedSet::credential_set_commitment`]); the matching
/// witness predicate this crate emits names the same commitment so
/// dispatch is deterministic.
pub fn identity_attested_tier_constraint(
    issuer_cell: CellId,
    credential_schema_id: [u8; 32],
) -> StateConstraint {
    StateConstraint::SenderAuthorized {
        set: AuthorizedSet::CredentialSet {
            issuer_cell: *issuer_cell.as_bytes(),
            credential_schema_id,
        },
    }
}

/// Build the witness-predicate shape an `Action` carries to discharge
/// an [`identity_attested_tier_constraint`].
///
/// The returned predicate's `commitment` agrees with the constraint's
/// `AuthorizedSet::CredentialSet` resolution, and `input_ref` is
/// [`InputRef::Sender`] so the executor binds the sender pubkey to
/// the credential's holder commitment via the registered
/// `WitnessedPredicateKind::BlindedSet` verifier.
pub fn identity_attested_witness_predicate(
    issuer_cell: CellId,
    credential_schema_id: [u8; 32],
    proof_witness_index: usize,
) -> WitnessedPredicate {
    WitnessedPredicate {
        kind: WitnessedPredicateKind::BlindedSet,
        commitment: AuthorizedSet::credential_set_commitment(
            issuer_cell.as_bytes(),
            &credential_schema_id,
        ),
        input_ref: InputRef::Sender,
        proof_witness_index,
    }
}

/// Build the `Action` recording a credential-gated name registration.
///
/// Behaves like [`build_register_action`] (same five-effect shape: name
/// hash, owner hash, owner authority register, expiry, event) but
/// additionally:
///
/// 1. Attaches `credential_presentation_proof_bytes` as
///    `witness_blobs[0]` (kind `ProofBytes`). The bytes are typically
///    the postcard-serialized `dregg_credentials::Presentation` whose
///    `WitnessedPredicateKind::BlindedSet` verifier accepts against
///    the issuer cell's revocation root + schema commitment.
/// 2. Emits an additional `name-registered-attested` event whose data
///    fields [name_hash, owner_hash, issuer_cell, schema_commitment]
///    pin the credential attestation in the receipt chain.
/// 3. Tags the action's method as `register_name_attested` so the
///    cell-program's `MethodIs`-guarded credential-gated case fires
///    rather than the unattested `register_name` case.
///
/// The companion cell-program case for `register_name_attested` should
/// install [`identity_attested_tier_constraint`] in its constraints
/// (so the executor rejects callers without a matching credential
/// proof).
pub fn build_register_with_credential_action(
    cipherclerk: &AppCipherclerk,
    registry_cell: CellId,
    name: &str,
    owner: [u8; 32],
    expiry_height: u64,
    issuer_cell: CellId,
    credential_schema_id: [u8; 32],
    credential_presentation_proof_bytes: Vec<u8>,
) -> Action {
    let name_hash_val = field_from_bytes(name.as_bytes());
    let owner_hash = field_from_bytes(&owner);
    let expiry_field = field_from_u64(expiry_height);
    let issuer_field = *issuer_cell.as_bytes();

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: NAME_HASH_SLOT,
            value: name_hash_val,
        },
        Effect::SetField {
            cell: registry_cell,
            index: OWNER_HASH_SLOT,
            value: owner_hash,
        },
        // The authority register — mirrors `build_register_action`; the
        // owner-authorization caveats refuse a registration that binds an
        // owner image without its raw-key authority register.
        Effect::SetField {
            cell: registry_cell,
            index: OWNER_PK_SLOT,
            value: owner,
        },
        Effect::SetField {
            cell: registry_cell,
            index: EXPIRY_SLOT,
            value: expiry_field,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(
                symbol("name-registered-attested"),
                vec![
                    name_hash_val,
                    owner_hash,
                    issuer_field,
                    credential_schema_id,
                ],
            ),
        },
    ];

    let mut action = cipherclerk.make_action(registry_cell, "register_name_attested", effects);
    action.witness_blobs = vec![dregg_turn::action::WitnessBlob::proof(
        credential_presentation_proof_bytes,
    )];
    action
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([1u8; 32])
    }

    #[test]
    fn factory_descriptor_is_stable() {
        // The descriptor hash is the constructor-transparency
        // identity. Two builds must produce the same hash.
        let h1 = name_factory_descriptor().hash();
        let h2 = name_factory_descriptor().hash();
        assert_eq!(h1, h2, "descriptor hash must be deterministic");
    }

    #[test]
    fn factory_descriptor_pins_program_vk() {
        let d = name_factory_descriptor();
        assert_eq!(d.child_program_vk, Some(name_child_program_vk()));
        assert_eq!(d.factory_vk, NAME_FACTORY_VK);
        assert_eq!(d.default_mode, CellMode::Sovereign);
        assert_eq!(d.creation_budget, Some(DEFAULT_CREATION_BUDGET));
    }

    #[test]
    fn name_child_program_vk_is_canonical_recipe() {
        // Per VK-AS-RE-EXECUTION-RECIPE.md §2.1, the child program VK is
        // the canonical hash of the program. A validator with both in
        // hand must be able to confirm the binding.
        let expected = dregg_app_framework::canonical_program_vk(&name_cell_program());
        assert_eq!(
            name_child_program_vk(),
            expected,
            "name_child_program_vk must equal canonical_program_vk(&name_cell_program())"
        );
        // The descriptor's child_program_vk binds to the canonical program.
        let d = name_factory_descriptor();
        let program = name_cell_program();
        let canonical = dregg_app_framework::canonical_program_vk(&program);
        assert_eq!(d.child_program_vk, Some(canonical));
    }

    #[test]
    fn name_child_program_vk_is_not_placeholder_bytes() {
        // The pre-recipe placeholder was `*b"starbridge-nameservice-childprg"`.
        // The canonical VK MUST differ — otherwise we did not migrate.
        // Pad the 31-byte historical sentinel with a trailing NUL to fit
        // the 32-byte VK slot.
        let old_placeholder: [u8; 32] = *b"starbridge-nameservice-childprg\0";
        assert_ne!(
            name_child_program_vk(),
            old_placeholder,
            "canonical VK must differ from the pre-recipe placeholder"
        );
    }

    #[test]
    fn name_child_program_vk_is_v2_layered_hash() {
        // VK v2 (VK-AS-RE-EXECUTION-RECIPE.md §v2): the app-framework
        // `canonical_program_vk` wrapper commits to four components,
        // not just program bytes. The resulting hash must be distinct
        // from the v1 program-bytes-only hash.
        let program = name_cell_program();
        let v2 = name_child_program_vk();
        let v1 = dregg_app_framework::canonical_program_bytes_hash(&program);
        assert_ne!(
            v2, v1,
            "v2 layered hash must differ from v1 program-bytes-only hash"
        );
    }

    #[test]
    fn factory_descriptor_validates_against_canonical_program() {
        // VK v2: app-framework wrapper validates against the layered
        // canonical hash (program bytes + Effect VM AIR + verifier +
        // Plonky3 proving system).
        let d = name_factory_descriptor();
        let program = name_cell_program();
        dregg_app_framework::validate_child_vk_canonical(&d, &program)
            .expect("descriptor's child_program_vk must bind to name_cell_program() under v2");
    }

    #[test]
    fn name_cell_program_carries_expected_caveats() {
        // Sanity: the program text actually contains the three slot caveats
        // the factory advertises in `state_constraints`.
        let p = name_cell_program();
        let constraints = match p {
            CellProgram::Cases(cases) => cases
                .into_iter()
                .flat_map(|c| c.constraints)
                .collect::<Vec<_>>(),
            other => panic!("expected CellProgram::Cases, got {other:?}"),
        };
        assert_eq!(
            constraints.len(),
            3 + owner_authorization_constraints().len()
        );
        assert!(constraints.iter().any(|c| matches!(
            c,
            StateConstraint::WriteOnce { index } if *index == NAME_HASH_SLOT as u8
        )));
        assert!(constraints.iter().any(|c| matches!(
            c,
            StateConstraint::Monotonic { index } if *index == EXPIRY_SLOT as u8
        )));
        assert!(constraints.iter().any(|c| matches!(
            c,
            StateConstraint::WriteOnce { index } if *index == REVOKED_SLOT as u8
        )));
        // The owner-authorization gate rides the same program.
        for oc in owner_authorization_constraints() {
            assert!(
                constraints.contains(&oc),
                "name_cell_program must carry the owner-authorization caveat {oc:?}"
            );
        }
    }

    #[test]
    fn factory_descriptor_has_no_birth_field_constraints() {
        // A factory-born name cell mints empty (all slots zero). Creation-time
        // `field_constraints` validate against `params.initial_fields`, which a
        // birth cannot carry the real 32-byte name hash through — so we carry
        // NONE (mirroring privacy-voting/bounty-board). The NAME_HASH/EXPIRY
        // gating lives in the perpetual `state_constraints` (WriteOnce/Monotonic),
        // which admit the first write from zero and bite thereafter. See
        // `factory_descriptor_bakes_slot_caveats`.
        let d = name_factory_descriptor();
        assert!(
            d.field_constraints.is_empty(),
            "name factory must carry NO creation-time field_constraints (birth-incompatible); \
             the NAME_HASH/EXPIRY gating is the perpetual WriteOnce/Monotonic state_constraints"
        );
    }

    #[test]
    fn factory_descriptor_bakes_slot_caveats() {
        // Lane G slot caveats are baked into the descriptor's
        // `state_constraints` — every produced cell inherits them.
        let d = name_factory_descriptor();
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::WriteOnce { index } if *index == NAME_HASH_SLOT as u8
            )),
            "name factory must install WriteOnce on NAME_HASH_SLOT"
        );
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::Monotonic { index } if *index == EXPIRY_SLOT as u8
            )),
            "name factory must install Monotonic on EXPIRY_SLOT"
        );
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::WriteOnce { index } if *index == REVOKED_SLOT as u8
            )),
            "name factory must install WriteOnce on REVOKED_SLOT (revocations are one-way)"
        );
        // The owner-authorization gate is baked into the descriptor too —
        // the born cell's `Predicate(state_constraints)` program refuses an
        // impostor's owner-slot write.
        for oc in owner_authorization_constraints() {
            assert!(
                d.state_constraints.contains(&oc),
                "factory descriptor must bake the owner-authorization caveat {oc:?}"
            );
        }
        // Pin the exact set so additions are caught in review.
        assert_eq!(
            d.state_constraints.len(),
            3 + owner_authorization_constraints().len()
        );
    }

    #[test]
    fn factory_descriptor_does_not_constrain_resolve_target_slot() {
        // RESOLVE_TARGET_SLOT is intentionally unconstrained so the
        // owner can repoint the name freely. If a future change adds
        // a constraint here, the rationale belongs in the factory
        // descriptor doc-comment and this test should be updated to
        // match.
        let d = name_factory_descriptor();
        let target_index = RESOLVE_TARGET_SLOT as u8;
        for c in &d.state_constraints {
            let constrained_index = match c {
                StateConstraint::WriteOnce { index }
                | StateConstraint::Immutable { index }
                | StateConstraint::Monotonic { index }
                | StateConstraint::StrictMonotonic { index } => Some(*index),
                _ => None,
            };
            if constrained_index == Some(target_index) {
                panic!("RESOLVE_TARGET_SLOT must remain unconstrained, found {c:?}");
            }
        }
    }

    // ── Slot-caveat enforcement (positive + negative). ───────────────────
    //
    // These exercise the `StateConstraint` evaluator directly against the
    // descriptor's slot caveats. They are the executor-side regression for
    // the Lane G migration: a legal registration succeeds; a second
    // registration on the same cell is rejected with `WriteOnceViolation`
    // and an expiry decrement is rejected with `MonotonicViolation`.

    fn build_name_program() -> dregg_cell::CellProgram {
        dregg_cell::CellProgram::Predicate(name_factory_descriptor().state_constraints.clone())
    }

    fn empty_state() -> dregg_cell::state::CellState {
        dregg_cell::state::CellState::new(0)
    }

    fn state_with(name_hash: FieldElement, expiry: u64) -> dregg_cell::state::CellState {
        let mut s = empty_state();
        s.fields[NAME_HASH_SLOT] = name_hash;
        s.fields[EXPIRY_SLOT] = field_from_u64(expiry);
        s
    }

    #[test]
    fn slot_caveats_legal_registration_succeeds() {
        // Initial registration: old slot is FIELD_ZERO (fresh cell), new
        // slot is `blake3("alice.dregg")`. WriteOnce permits this because
        // the prior value is zero; Monotonic permits any expiry on init.
        let program = build_name_program();
        let old = empty_state();
        let new = state_with(field_from_bytes(b"alice.dregg"), 1_000);
        let result = program.evaluate(&new, Some(&old), None);
        assert!(
            result.is_ok(),
            "legal registration must succeed: {result:?}"
        );
    }

    #[test]
    fn slot_caveats_reregister_taken_name_is_write_once_violation() {
        let program = build_name_program();
        let alice_hash = field_from_bytes(b"alice.dregg");
        let bob_hash = field_from_bytes(b"bob.dregg");
        let mut old = state_with(alice_hash, 1_000);
        old.set_nonce(1); // not a fresh cell
        // Attempt: overwrite NAME_HASH_SLOT with a different value.
        let new = state_with(bob_hash, 1_000);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("re-registration must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } => assert_eq!(index, NAME_HASH_SLOT as u8),
            other => panic!("expected WriteOnce violation, got: {other:?}"),
        }
    }

    #[test]
    fn slot_caveats_expiry_decrease_is_monotonic_violation() {
        let program = build_name_program();
        let alice_hash = field_from_bytes(b"alice.dregg");
        let mut old = state_with(alice_hash, 5_000);
        old.set_nonce(1);
        // Attempt: shorten expiry from 5000 → 4000.
        let new = state_with(alice_hash, 4_000);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("expiry decrement must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::Monotonic { index },
                ..
            } => assert_eq!(index, EXPIRY_SLOT as u8),
            other => panic!("expected Monotonic violation, got: {other:?}"),
        }
    }

    #[test]
    fn slot_caveats_legal_renewal_succeeds() {
        // Renewal extends expiry — Monotonic permits new >= old.
        let program = build_name_program();
        let alice_hash = field_from_bytes(b"alice.dregg");
        let mut old = state_with(alice_hash, 5_000);
        old.set_nonce(1);
        let new = state_with(alice_hash, 10_000);
        let result = program.evaluate(&new, Some(&old), None);
        assert!(result.is_ok(), "legal renewal must succeed: {result:?}");
    }

    #[test]
    fn factory_descriptors_includes_name_factory() {
        let all = factory_descriptors();
        assert_eq!(all.len(), 1, "expected exactly one descriptor today");
        assert_eq!(all[0].factory_vk, NAME_FACTORY_VK);
    }

    #[test]
    fn register_action_writes_three_slots_and_emits_event() {
        let cipherclerk = test_cipherclerk();
        let action =
            build_register_action(&cipherclerk, test_cell(), "alice.dregg", [3u8; 32], 1_000);

        assert_eq!(action.effects.len(), 5);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == NAME_HASH_SLOT
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == OWNER_HASH_SLOT
        ));
        // The authority register rides the registration atomically (the
        // owner-authorization caveats refuse an image without it).
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, value, .. }
                if *index == OWNER_PK_SLOT && *value == [3u8; 32]
        ));
        assert!(matches!(
            &action.effects[3],
            Effect::SetField { index, .. } if *index == EXPIRY_SLOT
        ));
        assert!(matches!(&action.effects[4], Effect::EmitEvent { .. }));
    }

    #[test]
    fn register_action_carries_real_signature() {
        // The whole point of the userspace stance: actions carry a real
        // framework-issued signature, not a `[0u8; 64]` placeholder.
        let cipherclerk = test_cipherclerk();
        let action =
            build_register_action(&cipherclerk, test_cell(), "alice.dregg", [3u8; 32], 1_000);
        match action.authorization {
            Authorization::Signature(a, b) => {
                assert!(
                    a != [0u8; 32] || b != [0u8; 32],
                    "signature must be non-zero (no [0u8; 64] placeholders!)"
                );
            }
            other => panic!("expected Signature variant, got {other:?}"),
        }
    }

    #[test]
    fn different_names_produce_different_name_hashes() {
        let cipherclerk = test_cipherclerk();
        let pick = |action: &Action| match &action.effects[0] {
            Effect::SetField { value, .. } => *value,
            _ => panic!("first effect is not SetField"),
        };
        let a = build_register_action(&cipherclerk, test_cell(), "alice.dregg", [3u8; 32], 1_000);
        let b = build_register_action(&cipherclerk, test_cell(), "bob.dregg", [3u8; 32], 1_000);
        assert_ne!(pick(&a), pick(&b));
    }

    #[test]
    fn renew_action_updates_expiry_slot_and_emits_event() {
        let cipherclerk = test_cipherclerk();
        let action = build_renew_action(&cipherclerk, test_cell(), "alice.dregg", 2_000);
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, EXPIRY_SLOT);
                assert_eq!(*value, field_from_u64(2_000));
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    #[test]
    fn transfer_action_updates_owner_slot_and_emits_event() {
        let cipherclerk = test_cipherclerk();
        let old = [3u8; 32];
        let new = [4u8; 32];
        let action = build_transfer_action(&cipherclerk, test_cell(), "alice.dregg", old, new);
        assert_eq!(action.effects.len(), 3);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, OWNER_HASH_SLOT);
                assert_eq!(*value, field_from_bytes(&new));
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        // The propose half stages the incoming owner's raw key for the
        // accept half to rotate the authority register to.
        match &action.effects[1] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, PENDING_OWNER_PK_SLOT);
                assert_eq!(*value, new);
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        assert!(matches!(&action.effects[2], Effect::EmitEvent { .. }));
    }

    #[test]
    fn accept_transfer_action_rotates_authority_register_and_emits_event() {
        let cipherclerk = test_cipherclerk();
        let new = [4u8; 32];
        let action = build_accept_transfer_action(&cipherclerk, test_cell(), "alice.dregg", new);
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, OWNER_PK_SLOT);
                assert_eq!(*value, new);
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    // ── StarbridgeAppContext mount integration. ──────────────────────────

    #[test]
    fn register_installs_name_factory_descriptor() {
        let ctx = test_context();
        assert_eq!(ctx.factory_registry().len(), 0);
        let vk = register(&ctx);
        assert_eq!(vk, NAME_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        let got = ctx
            .factory_registry()
            .get(&NAME_FACTORY_VK)
            .expect("factory descriptor registered");
        assert_eq!(got.factory_vk, NAME_FACTORY_VK);
        assert_eq!(got.child_program_vk, Some(name_child_program_vk()));
        assert_eq!(got.default_mode, CellMode::Sovereign);
    }

    #[test]
    fn register_installs_inspector_descriptors() {
        let ctx = test_context();
        register(&ctx);
        let name_insp = ctx
            .inspector_registry()
            .get("name")
            .expect("name inspector registered");
        assert_eq!(name_insp.descriptor["component"], "dregg-name");
        assert_eq!(
            name_insp.descriptor["module"],
            "/starbridge-apps/nameservice/inspectors.js"
        );
        let registry_insp = ctx
            .inspector_registry()
            .get("name-registry")
            .expect("name-registry inspector registered");
        assert_eq!(registry_insp.descriptor["component"], "dregg-name-registry");
        assert_eq!(registry_insp.descriptor["child_inspector"], "name");

        // The register-form inspector binds the JS turn-builders module.
        let form_insp = ctx
            .inspector_registry()
            .get("name-register-form")
            .expect("name-register-form inspector registered");
        assert_eq!(
            form_insp.descriptor["component"],
            "dregg-name-register-form"
        );
        assert_eq!(
            form_insp.descriptor["builders_module"],
            "/starbridge-apps/nameservice/turn-builders.js"
        );
        let methods = form_insp.descriptor["methods"]
            .as_array()
            .expect("methods array present");
        let methods: Vec<&str> = methods.iter().filter_map(|m| m.as_str()).collect();
        for required in [
            "register_name",
            "renew_name",
            "transfer_name",
            "revoke_name",
            "set_name_target",
        ] {
            assert!(
                methods.contains(&required),
                "register-form inspector must list method `{required}` but methods were {methods:?}"
            );
        }
    }

    #[test]
    fn name_inspector_descriptor_carries_slot_layout() {
        let ctx = test_context();
        register(&ctx);
        let name_insp = ctx.inspector_registry().get("name").unwrap();
        let layout = &name_insp.descriptor["slot_layout"];
        assert_eq!(layout["name_hash"], NAME_HASH_SLOT);
        assert_eq!(layout["owner_hash"], OWNER_HASH_SLOT);
        assert_eq!(layout["expiry"], EXPIRY_SLOT);
        assert_eq!(layout["revoked"], REVOKED_SLOT);
        assert_eq!(layout["target"], RESOLVE_TARGET_SLOT);
    }

    #[test]
    fn register_is_idempotent_on_factory() {
        // Calling register twice with the same ctx should not panic
        // and should not duplicate the factory entry (constructor
        // transparency: one descriptor per factory_vk).
        let ctx = test_context();
        register(&ctx);
        register(&ctx);
        assert_eq!(ctx.factory_registry().len(), 1);
    }

    #[test]
    fn register_inspector_descriptor_contains_factory_vk_hex() {
        // Inspectors need the factory VK to mount the
        // constructor-transparency view. Confirm the JSON carries it
        // as a hex string.
        let ctx = test_context();
        register(&ctx);
        let name_insp = ctx.inspector_registry().get("name").unwrap();
        let hex = name_insp.descriptor["factory_vk_hex"]
            .as_str()
            .expect("factory_vk_hex must be a string");
        assert_eq!(hex.len(), 64);
        assert_eq!(hex, hex_encode_32(&NAME_FACTORY_VK));
    }

    #[test]
    fn revoke_action_writes_revoked_slot_and_emits_event() {
        let cipherclerk = test_cipherclerk();
        let action = build_revoke_action(&cipherclerk, test_cell(), "alice.dregg");
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, REVOKED_SLOT);
                assert_eq!(*value, revoked_tombstone("alice.dregg"));
                assert_ne!(*value, [0u8; 32], "tombstone must be non-zero");
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    #[test]
    fn revoke_action_tombstone_is_name_bound() {
        // Two different names produce two different tombstones — defeats
        // "move tombstone from cell A to cell B to revoke a different name".
        let t1 = revoked_tombstone("alice.dregg");
        let t2 = revoked_tombstone("bob.dregg");
        assert_ne!(t1, t2);
        // Same name = same tombstone (replay-safe verifier).
        let t1_again = revoked_tombstone("alice.dregg");
        assert_eq!(t1, t1_again);
    }

    #[test]
    fn set_target_action_writes_resolve_slot_and_emits_event() {
        let cipherclerk = test_cipherclerk();
        let target = resolve_target("dregg://cell/abc123");
        let action = build_set_target_action(&cipherclerk, test_cell(), "alice.dregg", target);
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, RESOLVE_TARGET_SLOT);
                assert_eq!(*value, target);
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    #[test]
    fn name_hash_is_blake3_of_name_bytes() {
        // Public helper must match the value the executor sees in
        // NAME_HASH_SLOT.
        let direct = field_from_bytes(b"alice.dregg");
        let helper = name_hash("alice.dregg");
        assert_eq!(direct, helper);
    }

    #[test]
    fn expiry_field_helper_matches_internal_encoding() {
        let direct = field_from_u64(5_000);
        let helper = expiry_field(5_000);
        assert_eq!(direct, helper);
        // Sanity: low byte ends up at position 31 (big-endian).
        assert_eq!(helper[31], (5_000u64 & 0xff) as u8);
    }

    // ── Slot-caveat: double-revoke rejected by WriteOnce. ────────────────

    #[test]
    fn slot_caveats_double_revoke_is_write_once_violation() {
        let program = build_name_program();
        let alice_hash = field_from_bytes(b"alice.dregg");
        let mut old = state_with(alice_hash, 5_000);
        old.set_nonce(1);
        old.fields[REVOKED_SLOT] = revoked_tombstone("alice.dregg");
        // Attempt: overwrite the tombstone (e.g., with zero, to "un-revoke",
        // or with a different tombstone).
        let mut new = state_with(alice_hash, 5_000);
        new.fields[REVOKED_SLOT] = revoked_tombstone("alice.dregg-different");
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("double revoke must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } => assert_eq!(index, REVOKED_SLOT as u8),
            other => panic!("expected WriteOnce on REVOKED_SLOT, got: {other:?}"),
        }
    }

    #[test]
    fn slot_caveats_un_revoke_clearing_to_zero_is_write_once_violation() {
        let program = build_name_program();
        let alice_hash = field_from_bytes(b"alice.dregg");
        let mut old = state_with(alice_hash, 5_000);
        old.set_nonce(1);
        old.fields[REVOKED_SLOT] = revoked_tombstone("alice.dregg");
        // Attempt: clear the tombstone back to FIELD_ZERO.
        let new = state_with(alice_hash, 5_000); // REVOKED_SLOT == FIELD_ZERO
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("un-revocation must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } => assert_eq!(index, REVOKED_SLOT as u8),
            other => panic!("expected WriteOnce on REVOKED_SLOT, got: {other:?}"),
        }
    }

    #[test]
    fn slot_caveats_legal_initial_revocation_succeeds() {
        // First revocation on an active name: REVOKED_SLOT transitions
        // FIELD_ZERO → tombstone. WriteOnce permits.
        let program = build_name_program();
        let alice_hash = field_from_bytes(b"alice.dregg");
        let mut old = state_with(alice_hash, 5_000);
        old.set_nonce(1);
        let mut new = state_with(alice_hash, 5_000);
        new.fields[REVOKED_SLOT] = revoked_tombstone("alice.dregg");
        let result = program.evaluate(&new, Some(&old), None);
        assert!(
            result.is_ok(),
            "legal initial revocation must succeed: {result:?}"
        );
    }

    #[test]
    fn slot_caveats_target_repointing_is_unconstrained() {
        // RESOLVE_TARGET_SLOT carries no slot caveats — the owner may
        // freely set, change, and re-clear the slot.
        let program = build_name_program();
        let alice_hash = field_from_bytes(b"alice.dregg");
        let mut old = state_with(alice_hash, 5_000);
        old.set_nonce(1);
        old.fields[RESOLVE_TARGET_SLOT] = resolve_target("dregg://cell/first");
        let mut new = state_with(alice_hash, 5_000);
        new.fields[RESOLVE_TARGET_SLOT] = resolve_target("dregg://cell/second");
        let result = program.evaluate(&new, Some(&old), None);
        assert!(
            result.is_ok(),
            "freely changing the resolve target must succeed: {result:?}"
        );
    }

    // ── Cross-app composition: identity-attested registration ───────────

    #[test]
    fn identity_attested_tier_constraint_matches_predicate_commitment() {
        // The constraint and predicate MUST agree on the 32-byte
        // commitment, otherwise the executor cannot dispatch.
        let issuer = CellId::from_bytes([42u8; 32]);
        let schema_id = field_from_bytes(b"verified-developer-v1");
        let constraint = identity_attested_tier_constraint(issuer, schema_id);
        let predicate = identity_attested_witness_predicate(issuer, schema_id, 0);

        let constraint_commit = match constraint {
            StateConstraint::SenderAuthorized {
                set:
                    AuthorizedSet::CredentialSet {
                        issuer_cell,
                        credential_schema_id,
                    },
            } => AuthorizedSet::credential_set_commitment(&issuer_cell, &credential_schema_id),
            other => panic!("expected CredentialSet, got {other:?}"),
        };
        assert_eq!(predicate.commitment, constraint_commit);
        assert_eq!(predicate.kind, WitnessedPredicateKind::BlindedSet);
        assert_eq!(predicate.input_ref, InputRef::Sender);
    }

    #[test]
    fn build_register_with_credential_attaches_proof_witness_blob() {
        let cipherclerk = test_cipherclerk();
        let issuer = CellId::from_bytes([42u8; 32]);
        let schema_id = field_from_bytes(b"verified-developer-v1");
        let presentation_bytes = b"presentation-proof-stub".to_vec();
        let action = build_register_with_credential_action(
            &cipherclerk,
            test_cell(),
            "bob.dev",
            [3u8; 32],
            1_000,
            issuer,
            schema_id,
            presentation_bytes.clone(),
        );

        assert_eq!(action.method, symbol("register_name_attested"));
        assert_eq!(action.effects.len(), 5);
        // The SetFields parallel build_register_action (incl. the
        // authority register).
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == NAME_HASH_SLOT
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, .. } if *index == OWNER_PK_SLOT
        ));
        // Last effect is the attested event with issuer + schema fields.
        match &action.effects[4] {
            Effect::EmitEvent { event, .. } => {
                assert_eq!(event.topic, symbol("name-registered-attested"));
                assert_eq!(event.data.len(), 4);
                assert_eq!(event.data[2], *issuer.as_bytes());
                assert_eq!(event.data[3], schema_id);
            }
            other => panic!("expected EmitEvent, got {other:?}"),
        }
        // Witness blob present and kind ProofBytes.
        assert_eq!(action.witness_blobs.len(), 1);
        assert_eq!(action.witness_blobs[0].bytes, presentation_bytes);
        assert_eq!(
            action.witness_blobs[0].kind,
            dregg_turn::action::WitnessKind::ProofBytes
        );
    }

    #[test]
    fn identity_attested_tier_distinguishes_issuers_and_schemas() {
        // Different issuer cells or different schemas must produce
        // different constraint commitments so the executor can route
        // proofs to the correct registered verifier instance.
        let issuer_a = CellId::from_bytes([1u8; 32]);
        let issuer_b = CellId::from_bytes([2u8; 32]);
        let schema_a = field_from_bytes(b"verified-developer-v1");
        let schema_b = field_from_bytes(b"verified-developer-v2");
        let c1 = match identity_attested_tier_constraint(issuer_a, schema_a) {
            StateConstraint::SenderAuthorized {
                set:
                    AuthorizedSet::CredentialSet {
                        issuer_cell,
                        credential_schema_id,
                    },
            } => AuthorizedSet::credential_set_commitment(&issuer_cell, &credential_schema_id),
            _ => panic!(),
        };
        let c2 = match identity_attested_tier_constraint(issuer_b, schema_a) {
            StateConstraint::SenderAuthorized {
                set:
                    AuthorizedSet::CredentialSet {
                        issuer_cell,
                        credential_schema_id,
                    },
            } => AuthorizedSet::credential_set_commitment(&issuer_cell, &credential_schema_id),
            _ => panic!(),
        };
        let c3 = match identity_attested_tier_constraint(issuer_a, schema_b) {
            StateConstraint::SenderAuthorized {
                set:
                    AuthorizedSet::CredentialSet {
                        issuer_cell,
                        credential_schema_id,
                    },
            } => AuthorizedSet::credential_set_commitment(&issuer_cell, &credential_schema_id),
            _ => panic!(),
        };
        assert_ne!(c1, c2);
        assert_ne!(c1, c3);
        assert_ne!(c2, c3);
    }

    #[test]
    fn cipherclerk_identity_binds_into_signature() {
        // Two different cipherclerks sign the same logical action with
        // different signatures — confirms the cipherclerk's identity is
        // actually bound in.
        let cc1 = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let cc2 = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let cell = test_cell();
        let a1 = build_register_action(&cc1, cell, "alice", [3u8; 32], 1_000);
        let a2 = build_register_action(&cc2, cell, "alice", [3u8; 32], 1_000);
        let (Authorization::Signature(r1, _), Authorization::Signature(r2, _)) =
            (&a1.authorization, &a2.authorization)
        else {
            panic!("expected Signature variants");
        };
        assert_ne!(
            r1, r2,
            "different cipherclerks must produce different signatures"
        );
    }
}
