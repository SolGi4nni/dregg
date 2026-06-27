//! # starbridge-subscription
//!
//! Greenfield rebuild of the **storage-layer** of `apps/subscription/`
//! as a starbridge-app, and the **first concrete proof-of-pattern for
//! `STORAGE-AS-CELL-PROGRAMS.md`**.
//!
//! The original `apps/subscription/` used
//! `dregg_storage::inbox::CapInbox` as an operator-process data
//! structure with HTTP shims around it (`app-framework::inbox_endpoint`).
//! Per `STORAGE-AS-CELL-PROGRAMS.md` §1 that arrangement has five
//! distinct failure modes, the headline one being **the executor
//! never sees the queue's `SenderAuthorized` / `MonotonicSequence` /
//! `WriteOnce` constraints** — those are evaluated by a parallel
//! storage-side enforcement loop that produces no `TurnReceipt` and
//! cannot be audited against the cell-program substrate.
//!
//! This crate inverts that arrangement: a subscription cell *is* a
//! `CapInbox`-shaped cell-program. Its slot layout, slot caveats,
//! per-method operation-scoping, and capability surface live in a
//! [`subscription_factory_descriptor`] that anyone can audit by
//! hashing. The executor enforces the constraints on every turn.
//! Publish, consume, and the two grant operations are
//! [`AppCipherclerk`]-signed [`Action`]s composed only of existing
//! `Effect::SetField` and `Effect::EmitEvent` variants. No new Effect
//! is introduced; no storage-side enforcement loop survives.
//!
//! ## Companion docs
//!
//! - `STORAGE-AS-CELL-PROGRAMS.md` §3.1 — the CapInbox reference design
//!   (slot layout, declared `StateConstraint`s, factory descriptor,
//!   app-side `Effect` composition, observability, what-it-replaces).
//! - `STARBRIDGE-APPS-PLAN.md` §3.8 — subscription's place in the
//!   starbridge-app order. (The plan framed subscription as a
//!   *delegated-debit* shape; this crate is the *queue* shape that
//!   was the subscription app's real load-bearing primitive. The
//!   debit shape can layer on top in a follow-on crate.)
//! - `SLOT-CAVEATS-DESIGN.md` — the slot-caveat vocabulary the
//!   factory descriptor draws from.
//! - `SLOT-CAVEATS-EVALUATION.md` — the 21-variant lifted enum +
//!   operation-scoped `CellProgram::Cases(_)` shape used below.
//! - `starbridge-apps/nameservice/src/lib.rs` — the pattern anchor.
//!   This crate mirrors its structure.
//!
//! ## What this crate exports
//!
//! 1. [`subscription_factory_descriptor`] — the `FactoryDescriptor`
//!    pinning the constructor contract: slot layout, immutable
//!    capacity + owner, monotonic head/tail, opaque root commitments, plus the
//!    operation-scoped state constraints via [`subscription_program`].
//! 2. [`subscription_program`] — the `CellProgram::Cases(_)` value
//!    that the descriptor bakes in. Exported separately so tests can
//!    directly drive `program.evaluate_with_meta(..)` against
//!    hand-rolled `(old_state, new_state, meta)` triples.
//! 3. [`factory_descriptors`] — the slice of all factory descriptors
//!    this starbridge-app contributes. Today: just one.
//! 4. Turn-builders (signed actions composed of generic Effects):
//!    - [`build_publish_action`] — publisher writes a payload hash
//!      and advances head.
//!    - [`build_consume_action`] — consumer advances tail and emits
//!      a dequeue event.
//!    - [`build_grant_publisher_action`] — owner adds a publisher key.
//!    - [`build_grant_consumer_action`] — owner adds a consumer key.
//! 5. [`register`] — `StarbridgeAppContext` mount hook that wires the
//!    factory + inspector descriptors into a shared host context.
//!
//! ## The slot layout
//!
//! `STATE_SLOTS = 16`. The 16 slots are:
//!
//! | Slot | Name | Caveat | Purpose |
//! |---:|---|---|---|
//! | 0 | `seq_head` | `MonotonicSequence` (publish-scoped) | Next sequence number a publisher will write. Advanced exactly +1 per publish. Bookmark for consumers. |
//! | 1 | `seq_tail` | `MonotonicSequence` (consume-scoped) | Next sequence number a consumer will read. Advanced exactly +1 per consume. Invariant: `tail <= head`. |
//! | 2 | `capacity` | `Immutable` | Max in-flight messages. Set at creation; never changes. |
//! | 3 | `authorized_publishers_root` | per-method non-zero | Merkle root over the set of authorized publisher pubkeys. |
//! | 4 | `authorized_consumers_root` | per-method non-zero | Merkle root over authorized consumers. |
//! | 5 | `owner_pk_hash` | `Immutable` | Hash of the subscription owner's pubkey. Only the owner may grant publishers/consumers. |
//! | 6 | `message_root` | per-method non-zero | Poseidon2/BLAKE3 root over the (seq, payload_hash) tuples published into the queue. |
//! | 7 | `latest_payload_hash` | per-method | The hash of the most recently published payload. On publish: written. On consume: unchanged. Inspectors read it as the head-of-queue summary. |
//!
//! ### Why a `message_root` and not 16 dedicated `message_slot[i]` slots?
//!
//! The spec in `STORAGE-AS-CELL-PROGRAMS.md` §3.1 talks about per-message
//! `WriteOnce` slots as an *idealized* surface. The cell substrate has
//! `STATE_SLOTS = 16` total (`dregg_cell::state::STATE_SLOTS`), which is
//! not enough to host an unbounded message ring. The actual data path
//! is the same one `MerkleQueue::root` uses today in `dregg_storage`:
//! a root commitment in slot 6, with the per-message tuples stored
//! out-of-band (in an off-cell content store keyed by the root). The
//! `WriteOnce` semantic at the *individual-message* level is enforced
//! by the root: once an `(i, payload_hash)` pair has been folded into
//! the root, the root commits to that payload at position `i`, and
//! any subsequent attempt to write a different payload at the same
//! index would have to produce the same root (and so would be
//! rejected by the consumer's Merkle membership check). The slot-level
//! caveat only prevents zero-clears because roots are opaque
//! commitments, not ordered counters; the per-message `WriteOnce`
//! semantic is structural.
//!
//! For deployments that want a tiny, slot-resident message ring (no
//! off-cell content store), the message_root slot can be replaced by
//! a fixed set of `WriteOnce { index: k }` constraints over slots
//! 6..N. That variant is a follow-on; the root-commitment shape is
//! the canonical pattern.
//!
//! ## Operation-scoping
//!
//! Per `SLOT-CAVEATS-EVALUATION.md` §7.1, the `CellProgram::Cases(_)`
//! shape (Cav-Codex Block 4) lets us scope constraints to specific
//! operations. The four operations on a subscription cell each get
//! their own case, guarded on the action's method symbol:
//!
//! - `publish` — head advances by exactly 1 (`MonotonicSequence`),
//!   tail must be unchanged (`Immutable { index: 1 }`),
//!   the message_root must change and be non-zero,
//!   sender must be in `authorized_publishers_root`
//!   (`SenderAuthorized { set: PublicRoot { set_root_index: 3 } }`),
//!   roots-of-membership stay frozen on publish.
//! - `consume` — tail advances by exactly 1 (`MonotonicSequence`),
//!   head must be unchanged (`Immutable { index: 0 }`),
//!   sender must be in `authorized_consumers_root`
//!   (`SenderAuthorized { set: PublicRoot { set_root_index: 4 } }`),
//!   message_root + latest_payload_hash stay frozen, membership
//!   roots frozen.
//! - `grant_publisher` — `authorized_publishers_root` changes
//!   and is non-zero; head, tail, capacity, owner, msg
//!   root, latest payload, and the consumers root all immutable.
//!   The owner authorization is enforced by the per-cell capability
//!   layer (action sender is the owner of the cell).
//! - `grant_consumer` — symmetric to `grant_publisher` over slot 4.
//!
//! Plus an `Always`-guarded base case carrying the *invariants* that
//! hold across every transition: capacity and owner immutable. These
//! invariants AND with whatever per-method case fires.
//!
//! Per Cav-Codex Block 4, if **no** case matches a transition the
//! program default-denies. That is: an action with an unrecognized
//! method symbol is rejected outright. The four operations above are
//! the *only* legal transitions.
//!
//! ## Dependency on the caveat-correctness lane
//!
//! `STORAGE-AS-CELL-PROGRAMS.md` notes the operation-scoped case
//! shape is exactly what the caveat-correctness lane is adding. If
//! that lane has not landed at the executor / AIR level by the time
//! this crate ships, the descriptor and turn-builders still produce
//! correct Actions and Effects — what gates on the in-flight lane is
//! the *executor-side* rejection of off-pattern transitions
//! (`evaluate_with_meta` against the `MethodIs` guard). The unit
//! tests in this crate and the adversarial tests in `tests/program.rs`
//! drive `evaluate_with_meta` directly so they exercise the
//! operation-scoped semantics regardless of the executor's wiring
//! state. See the README for the dependency note.

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, AuthorizedSet, CapTarget, CapTemplate, CellAffordance,
    CellId, CellMode, CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect,
    EmbeddedExecutor, Event, FactoryDescriptor, FieldElement, FireError, FireExecuteError,
    GatedAffordance, InspectorDescriptor, StarbridgeAppContext, StateConstraint, TransitionCase,
    TransitionGuard, TurnReceipt, canonical_program_vk, field_from_u64, hex_encode_32, symbol,
};
use dregg_cell::program::SimpleStateConstraint;

pub use dregg_app_framework::field_from_bytes;

// =============================================================================
// The four-axis (+ reactor) template
// =============================================================================
//
// This crate is the 4-axis starbridge-app template, plus the FIRST `Reactor`
// (AX5) exemplar:
//
//   - AX1 (factory): [`subscription_factory_descriptor`] + [`subscription_program`]
//     — the AIR-bound, operation-scoped cell program pinned by the child VK.
//   - AX2 (deos): [`subscription_deos_app`] / [`register_deos`] / [`seed_feed`] /
//     [`fire_publish`] / [`fire_consume`] — the composed `DeosApp` surface.
//   - AX3 (service): [`service`] — the queue as a typed `InterfaceDescriptor` on the
//     `invoke()` front door.
//   - AX4 (card): [`card`] — the UI as a renderer-independent `deos.ui.*` view-tree.
//   - AX5 (reactor): [`reactor`] — the auto-draining consumer as a `Reactor`, the
//     reactive twin of `invoke()`.
//
// AX2/AX3/AX5 all install/assume the SAME shared runtime program
// ([`feed_invariants_program`], the flat invariants); the full operation-scoped
// [`subscription_program`] `Cases` is the AIR-bound AX1 program.

pub mod card;
pub mod obligation;
pub mod reactor;
pub mod service;

pub use obligation::{BillingError, BillingPlan, Subscription, SubscriptionStatus};

// =============================================================================
// Slot layout
// =============================================================================

/// Slot 0 — `seq_head`. Producer cursor. Advanced exactly +1 per `publish`.
pub const SEQ_HEAD_SLOT: u8 = 0;
/// Slot 1 — `seq_tail`. Consumer cursor. Advanced exactly +1 per `consume`.
pub const SEQ_TAIL_SLOT: u8 = 1;
/// Slot 2 — `capacity`. Immutable upper bound on in-flight messages.
pub const CAPACITY_SLOT: u8 = 2;
/// Slot 3 — `authorized_publishers_root`. Merkle root of allowed publisher pubkeys.
pub const PUBLISHERS_ROOT_SLOT: u8 = 3;
/// Slot 4 — `authorized_consumers_root`. Merkle root of allowed consumer pubkeys.
pub const CONSUMERS_ROOT_SLOT: u8 = 4;
/// Slot 5 — `owner_pk_hash`. Immutable owner identity.
pub const OWNER_PK_HASH_SLOT: u8 = 5;
/// Slot 6 — `message_root`. Root over published (seq, payload_hash) tuples.
pub const MESSAGE_ROOT_SLOT: u8 = 6;
/// Slot 7 — `latest_payload_hash`. The most recently published payload hash.
pub const LATEST_PAYLOAD_SLOT: u8 = 7;

/// **Record-layer Stage 0 (`_RECORD-LAYER-UPGRADE.md` §E).** Subscription is the
/// 16/16-full app — slots 0..15 are all assigned above, so it has historically had
/// to fold *unbounded* message state into the slot-6 `message_root` workaround
/// by hand. The committed user-field MAP (`CellState::fields_root` /
/// `fields_map`) frees it: keys `>= STATE_SLOTS` (16) live in the map, committed
/// by `fields_root`, with a membership read-back.
///
/// This is the FIRST overflow field on the map: a per-subscription
/// `subscriber_count` that the 16-slot cell had no room for. It demonstrates the
/// end-to-end path (write → root update → committed read-back) on the app the
/// 16-cap actually blocked. Reserved low keys are `0..15`; this is the first
/// user-map key.
pub const SUBSCRIBER_COUNT_KEY: u64 = 16;

fn u64_field(value: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    out
}

// =============================================================================
// Factory configuration
// =============================================================================

/// Default per-epoch creation budget. Rate-limits Sybil creation of
/// subscription cells from this factory.
pub const DEFAULT_CREATION_BUDGET: u64 = 1_000;

/// The factory VK we publish for the subscription factory.
///
/// Like the nameservice factory, this is a stable placeholder for the
/// BLAKE3 hash of the subscription cell-program VK. Replacing it with
/// the real VK is a single constant change once the cell-program AIR
/// for `subscription_program` is authored.
pub const SUBSCRIPTION_FACTORY_VK: [u8; 32] = *b"starbridge-subscription-factory!";

/// The child cell-program VK installed on per-subscription cells.
///
/// Per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1: computed canonically as
/// `canonical_program_vk(&subscription_program())`. A validator with
/// [`subscription_program`] in scope can re-derive the VK and
/// re-execute the program against witness data.
///
/// Previously a byte-string placeholder
/// (`*b"starbridge-subscription-childprg"`); the canonical version
/// makes the substrate honest pre-recursion.
pub fn subscription_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&subscription_program())
}

/// Method symbol for `publish`.
pub fn publish_method_symbol() -> [u8; 32] {
    symbol("publish")
}
/// Method symbol for `consume`.
pub fn consume_method_symbol() -> [u8; 32] {
    symbol("consume")
}
/// Method symbol for `grant_publisher`.
pub fn grant_publisher_method_symbol() -> [u8; 32] {
    symbol("grant_publisher")
}
/// Method symbol for `grant_consumer`.
pub fn grant_consumer_method_symbol() -> [u8; 32] {
    symbol("grant_consumer")
}

fn slot_changed(index: u8) -> StateConstraint {
    StateConstraint::AnyOf {
        variants: vec![SimpleStateConstraint::Not(Box::new(
            SimpleStateConstraint::Immutable { index },
        ))],
    }
}

// =============================================================================
// CellProgram: operation-scoped Cases
// =============================================================================

/// Build the `CellProgram` enforcing the subscription cell's
/// lifetime invariants and per-operation transitions.
///
/// Per the design notes in the crate docs: this is a
/// `CellProgram::Cases(_)` with five cases — one `Always`-guarded
/// invariants case plus four `MethodIs`-guarded operation cases.
/// Cases default-deny when no case matches (per Cav-Codex Block 4),
/// so any action whose method symbol is not one of the four legal
/// operations is rejected outright.
pub fn subscription_program() -> CellProgram {
    CellProgram::Cases(vec![
        // ────────────────────────────────────────────────────────────────
        // Invariants: every transition, regardless of operation.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                // `WriteOnce` (not `Immutable`): a factory-born subscription is
                // empty, so capacity + owner are bound once by the first turn
                // and frozen thereafter — the birth-compatible form of "set at
                // creation, never changes".
                StateConstraint::WriteOnce {
                    index: CAPACITY_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: OWNER_PK_HASH_SLOT,
                },
                StateConstraint::FieldLteField {
                    left_index: SEQ_TAIL_SLOT,
                    right_index: SEQ_HEAD_SLOT,
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // publish: head advances by +1; tail, capacity, owner, roots stay
        // unchanged; message_root changes and is non-zero; sender must be
        // a member of authorized_publishers_root.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("publish"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: SEQ_HEAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_TAIL_SLOT,
                },
                StateConstraint::Immutable {
                    index: PUBLISHERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: CONSUMERS_ROOT_SLOT,
                },
                slot_changed(MESSAGE_ROOT_SLOT),
                StateConstraint::FieldGte {
                    index: MESSAGE_ROOT_SLOT,
                    value: u64_field(1),
                },
                // The latest_payload slot is overwritten per publish; the
                // per-message WriteOnce semantic is structurally enforced
                // by the message_root commitment (see crate docs).
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: PUBLISHERS_ROOT_SLOT,
                    },
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // consume: tail advances by +1; head, message_root, latest_payload,
        // capacity, owner, roots stay unchanged; sender must be a member
        // of authorized_consumers_root.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("consume"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: SEQ_TAIL_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_HEAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: MESSAGE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: LATEST_PAYLOAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: PUBLISHERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: CONSUMERS_ROOT_SLOT,
                },
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: CONSUMERS_ROOT_SLOT,
                    },
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // grant_publisher: publishers_root changes; everything else frozen.
        // Owner authorization rides on the per-cell capability layer.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("grant_publisher"),
            },
            constraints: vec![
                slot_changed(PUBLISHERS_ROOT_SLOT),
                StateConstraint::FieldGte {
                    index: PUBLISHERS_ROOT_SLOT,
                    value: u64_field(1),
                },
                StateConstraint::Immutable {
                    index: SEQ_HEAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_TAIL_SLOT,
                },
                StateConstraint::Immutable {
                    index: CONSUMERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: MESSAGE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: LATEST_PAYLOAD_SLOT,
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // grant_consumer: symmetric to grant_publisher over consumers_root.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("grant_consumer"),
            },
            constraints: vec![
                slot_changed(CONSUMERS_ROOT_SLOT),
                StateConstraint::FieldGte {
                    index: CONSUMERS_ROOT_SLOT,
                    value: u64_field(1),
                },
                StateConstraint::Immutable {
                    index: SEQ_HEAD_SLOT,
                },
                StateConstraint::Immutable {
                    index: SEQ_TAIL_SLOT,
                },
                StateConstraint::Immutable {
                    index: PUBLISHERS_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: MESSAGE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: LATEST_PAYLOAD_SLOT,
                },
            ],
        },
    ])
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the `FactoryDescriptor` for per-subscription sovereign cells.
///
/// The descriptor pins the constructor-transparency contract anyone
/// can audit by hashing:
///
/// - `child_program_vk = subscription_child_program_vk()` — the
///   operation-scoped cell-program (`subscription_program`).
/// - `default_mode = Hosted` — subscription queues are naturally
///   federation-hosted (the federation sees cleartext events for
///   producers and consumers; the payload bodies themselves live in
///   the off-cell content store). Sovereign cells with private
///   payload bodies are a follow-on factory.
/// - `creation_budget = DEFAULT_CREATION_BUDGET` (Sybil cap).
/// - `allowed_cap_templates` = a `[owner, publisher, consumer]` triple:
///   the factory may issue an owner cap (full control over grants)
///   plus an attenuatable publisher cap and an attenuatable consumer
///   cap. Sub-delegation rides on `Caveat::ResourcePrefix`.
/// - `field_constraints` (creation-time): head, tail initialize to
///   zero; capacity within a sane range; owner_pk_hash non-zero.
/// - `state_constraints` (perpetual / Lane G slot caveats): the
///   `Immutable` invariants flattened from
///   [`subscription_program`]'s `Always` case plus the cell-wide
///   `Monotonic` invariants for head and tail. Opaque hash roots are
///   constrained by operation-scoped cases. The full operation-scoped shape is bound
///   by `child_program_vk` (which is the VK of an AIR that enforces
///   [`subscription_program`]).
///
/// The split between `state_constraints` (descriptor) and
/// `subscription_program` (cell-program) is intentional. The
/// descriptor's field is `Vec<StateConstraint>` — a flat list, no
/// `Cases` shape — because the descriptor is hashed for constructor
/// transparency before the cell-program AIR exists. The flat list
/// commits to the *invariants*; the AIR commits to the full
/// operation-scoped shape.
pub fn subscription_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: SUBSCRIPTION_FACTORY_VK,
        child_program_vk: Some(subscription_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(
            Some(subscription_child_program_vk()),
        )),
        allowed_cap_templates: vec![
            // Owner cap — full control over publisher/consumer grants.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
            // Publisher cap — may publish.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
            // Consumer cap — may consume.
            CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            },
        ],
        // No creation-time `field_constraints`: a freshly-minted subscription
        // cell is born empty (head == tail == 0 already, capacity/owner zero)
        // and its first `configure` turn writes `CAPACITY` + `OWNER_PK_HASH`
        // (`WriteOnce`, frozen after) before any publish/consume. The birth
        // `Range`/`NonZero` validated against `params.initial_fields`, forcing
        // the seed path to mint placeholders; an owner placeholder is a real
        // soundness hazard (a null/`1`-owned subscription). Mirror
        // privacy-voting/bounty-board: drop the birth constraints, bind the
        // capacity and owner with the first turn under `WriteOnce`.
        field_constraints: vec![],
        state_constraints: vec![
            // Lifetime invariants — flattened from the `Always` case.
            // The full operation-scoped shape is in `subscription_program`.
            // `WriteOnce` (not `Immutable`): a born cell is empty, so capacity
            // and owner are bound by the FIRST turn from zero, then frozen.
            StateConstraint::WriteOnce {
                index: CAPACITY_SLOT,
            },
            StateConstraint::WriteOnce {
                index: OWNER_PK_HASH_SLOT,
            },
            StateConstraint::FieldLteField {
                left_index: SEQ_TAIL_SLOT,
                right_index: SEQ_HEAD_SLOT,
            },
            // Cursors grow monotonically across the cell's lifetime.
            // Opaque hash roots are constrained by operation-scoped cases.
            StateConstraint::Monotonic {
                index: SEQ_HEAD_SLOT,
            },
            StateConstraint::Monotonic {
                index: SEQ_TAIL_SLOT,
            },
        ],
        default_mode: CellMode::Hosted,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// The full slice of factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![subscription_factory_descriptor()]
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the on-ledger [`Action`] that records a `publish`.
///
/// The action carries three `SetField` effects (head advances,
/// message_root changes, latest_payload slot updated) plus an
/// `EmitEvent("subscription-published", ...)` for off-chain
/// indexers. The cipherclerk's `make_action` produces a real
/// `Authorization::Signature(..)`; the executor checks the
/// `publish`-case constraints against the (old, new) state pair
/// and the action's sender on every turn.
///
/// # Parameters
///
/// - `cipherclerk` — the [`AppCipherclerk`] signing the publish (must hold a
///   publisher cap or have its public key under
///   `authorized_publishers_root`).
/// - `subscription_cell` — the target subscription cell.
/// - `new_head` — the new value of slot 0 (`old_head + 1`). The
///   caller computes this from the cell's current state.
/// - `new_message_root` — the new value of slot 6 (the root after
///   folding `(new_head, payload_hash)` into the prior root).
/// - `payload_hash` — the hash of the payload being published. Stored
///   verbatim in slot 7 as `latest_payload_hash`; also published in
///   the event payload for indexers.
pub fn build_publish_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_head: FieldElement,
    new_message_root: FieldElement,
    payload_hash: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: subscription_cell,
            index: SEQ_HEAD_SLOT as usize,
            value: new_head,
        },
        Effect::SetField {
            cell: subscription_cell,
            index: MESSAGE_ROOT_SLOT as usize,
            value: new_message_root,
        },
        Effect::SetField {
            cell: subscription_cell,
            index: LATEST_PAYLOAD_SLOT as usize,
            value: payload_hash,
        },
        Effect::EmitEvent {
            cell: subscription_cell,
            event: Event::new(
                symbol("subscription-published"),
                vec![new_head, new_message_root, payload_hash],
            ),
        },
    ];

    cipherclerk.make_action(subscription_cell, "publish", effects)
}

/// Build the on-ledger [`Action`] that records a `consume`.
///
/// The action carries one `SetField` (tail advances) plus an
/// `EmitEvent("subscription-consumed", ...)`. The consumer fetches
/// the payload body out-of-band by Merkle-proving inclusion against
/// slot 6's `message_root`; the on-cell state only commits to the
/// cursor and the root.
///
/// # Parameters
///
/// - `cipherclerk` — the [`AppCipherclerk`] signing the consume (must hold a
///   consumer cap or have its public key under
///   `authorized_consumers_root`).
/// - `subscription_cell` — the target subscription cell.
/// - `new_tail` — the new value of slot 1 (`old_tail + 1`). The
///   caller computes this from the cell's current state.
/// - `consumed_payload_hash` — the payload hash that was just
///   consumed. Surfaced in the event for off-chain indexers; not
///   written to state (per the `consume` case's `Immutable` set on
///   slot 7).
pub fn build_consume_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_tail: FieldElement,
    consumed_payload_hash: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: subscription_cell,
            index: SEQ_TAIL_SLOT as usize,
            value: new_tail,
        },
        Effect::EmitEvent {
            cell: subscription_cell,
            event: Event::new(
                symbol("subscription-consumed"),
                vec![new_tail, consumed_payload_hash],
            ),
        },
    ];

    cipherclerk.make_action(subscription_cell, "consume", effects)
}

/// Build the on-ledger [`Action`] that adds a new publisher to the
/// authorized-publishers set.
///
/// The action carries one `SetField` (the publishers_root changes
/// to a new root that includes `new_publisher_pk`) plus an
/// `EmitEvent("subscription-publisher-granted", ...)` for indexers.
/// Per the `grant_publisher` case, every other slot stays frozen on
/// this turn.
///
/// # Parameters
///
/// - `cipherclerk` — the [`AppCipherclerk`] signing the grant. Must be the
///   owner of the subscription cell (the `owner_pk_hash` slot's
///   preimage); the per-cell capability layer enforces this.
/// - `subscription_cell` — the target subscription cell.
/// - `new_publishers_root` — the new Merkle root over the publishers
///   set after adding `new_publisher_pk`. The caller computes this
///   from the prior root + the new pubkey.
/// - `new_publisher_pk` — the pubkey being added (for the event).
pub fn build_grant_publisher_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_publishers_root: FieldElement,
    new_publisher_pk: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: subscription_cell,
            index: PUBLISHERS_ROOT_SLOT as usize,
            value: new_publishers_root,
        },
        Effect::EmitEvent {
            cell: subscription_cell,
            event: Event::new(
                symbol("subscription-publisher-granted"),
                vec![new_publishers_root, new_publisher_pk],
            ),
        },
    ];

    cipherclerk.make_action(subscription_cell, "grant_publisher", effects)
}

/// Build the on-ledger [`Action`] that adds a new consumer to the
/// authorized-consumers set.
///
/// Symmetric to [`build_grant_publisher_action`].
pub fn build_grant_consumer_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_consumers_root: FieldElement,
    new_consumer_pk: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: subscription_cell,
            index: CONSUMERS_ROOT_SLOT as usize,
            value: new_consumers_root,
        },
        Effect::EmitEvent {
            cell: subscription_cell,
            event: Event::new(
                symbol("subscription-consumer-granted"),
                vec![new_consumers_root, new_consumer_pk],
            ),
        },
    ];

    cipherclerk.make_action(subscription_cell, "grant_consumer", effects)
}

// =============================================================================
// Record-layer Stage 0: the committed user-field MAP (the unbounded-fields win)
// =============================================================================

/// Write the `subscriber_count` overflow field (user-map key 16) into a
/// subscription cell's committed field-map, recomputing `fields_root`.
///
/// `_RECORD-LAYER-UPGRADE.md` §E.3: subscription is 8/8-full, so this field has
/// nowhere to live in the fixed `fields[0..7]`. The committed map carries it for
/// keys `>= STATE_SLOTS`. After the write, `fields_root` commits the value, and
/// [`read_subscriber_count`] proves the read-back is committed.
pub fn write_subscriber_count(state: &mut dregg_cell::CellState, count: u64) -> bool {
    let mut value = [0u8; 32];
    value[24..32].copy_from_slice(&count.to_be_bytes());
    state.set_field_ext(SUBSCRIBER_COUNT_KEY, value)
}

/// Read the `subscriber_count` overflow field back **with a membership proof**:
/// returns `Some(count)` iff the value is genuinely committed by the cell's
/// `fields_root` (`CellState::fields_root_membership`), else `None`. This is the
/// end-to-end demonstration that the map field round-trips through the committed
/// root, not just an off-cell side store.
pub fn read_subscriber_count(state: &dregg_cell::CellState) -> Option<u64> {
    let value = state.fields_root_membership(SUBSCRIBER_COUNT_KEY)?;
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&value[24..32]);
    Some(u64::from_be_bytes(bytes))
}

// =============================================================================
// Cross-app composition: bounty-state notifications
// =============================================================================
//
// A subscription cell is a generic publish/consume queue, but the
// canonical cross-app load it carries in the cross-app-e2e composition
// story is **bounty-state notifications**: when a bounty's state
// transitions (posted → claimed → fulfilled → settled), the bounty's
// posting cell wants to notify subscribers (the original poster, the
// claimant, watchers) without leaking the bounty body cleartext.
//
// The integration is data-only: the bounty app computes a canonical
// `bounty_state_payload_hash` over the (bounty_id, prior_state,
// new_state, actor_pk_hash) tuple and publishes it via
// [`build_publish_action`]. Subscribers consume the event stream and
// resolve the payload body out-of-band from a content store keyed by
// the published hash.

/// Canonical bounty lifecycle states. Used to seed the state-change
/// payload hash so each transition is uniquely identifiable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BountyState {
    /// Bounty has been posted; no claimant yet.
    Posted,
    /// A worker has claimed the bounty; fulfillment pending.
    Claimed,
    /// A fulfillment proof has been submitted; pending dispute window.
    Fulfilled,
    /// Settlement has occurred — bounty paid (or refunded on dispute).
    Settled,
    /// Bounty was canceled before fulfillment.
    Canceled,
}

impl BountyState {
    /// Single-byte canonical tag for the state. Used inside the payload
    /// hash and surfaced as a 32-byte event datum so off-chain indexers
    /// can filter by state without parsing the full payload.
    pub fn tag(self) -> u8 {
        match self {
            BountyState::Posted => 1,
            BountyState::Claimed => 2,
            BountyState::Fulfilled => 3,
            BountyState::Settled => 4,
            BountyState::Canceled => 5,
        }
    }

    /// Encode the state tag as a 32-byte `FieldElement` (zero-padded
    /// LSB-style). Suitable as a fact term in event data.
    pub fn tag_field(self) -> FieldElement {
        let mut out = [0u8; 32];
        out[31] = self.tag();
        out
    }
}

/// Compute the canonical payload hash for a bounty-state transition.
///
/// `blake3_derive_key("dregg-bounty-state-v1") || bounty_id ||
/// prior_state.tag() || new_state.tag() || actor_pk_hash`. Distinct
/// (bounty_id, prior, new, actor) tuples produce distinct payload
/// hashes — replay-safe at the commitment level. The matching
/// fulfillment / settlement payloads carry the same shape so the
/// receipt chain composes deterministically.
///
/// Returns a 32-byte `FieldElement` ready to feed into
/// [`build_publish_action`]'s `payload_hash` argument.
pub fn bounty_state_payload_hash(
    bounty_id: &[u8; 32],
    prior_state: BountyState,
    new_state: BountyState,
    actor_pk_hash: &[u8; 32],
) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-bounty-state-v1");
    hasher.update(bounty_id);
    hasher.update(&[prior_state.tag()]);
    hasher.update(&[new_state.tag()]);
    hasher.update(actor_pk_hash);
    *hasher.finalize().as_bytes()
}

/// Convenience: build a `publish` action that notifies a subscription
/// cell of a bounty state change.
///
/// Wraps [`build_publish_action`] with [`bounty_state_payload_hash`] so
/// callers compose the cross-app pipeline in one call. The caller still
/// supplies `new_head` (the advanced cursor) and `new_message_root`
/// (the advanced root) — these are queue invariants the executor's
/// `publish`-case constraints enforce regardless of payload contents.
pub fn build_bounty_state_publish_action(
    cipherclerk: &AppCipherclerk,
    subscription_cell: CellId,
    new_head: FieldElement,
    new_message_root: FieldElement,
    bounty_id: &[u8; 32],
    prior_state: BountyState,
    new_state: BountyState,
    actor_pk_hash: &[u8; 32],
) -> Action {
    let payload_hash = bounty_state_payload_hash(bounty_id, prior_state, new_state, actor_pk_hash);
    build_publish_action(
        cipherclerk,
        subscription_cell,
        new_head,
        new_message_root,
        payload_hash,
    )
}

// =============================================================================
// The deos-native surface — the FEED as a composed `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (Tier-1 #2): subscription's deos
// re-expression was the MOST complete of the leading cohort, but MISLOCATED — it
// lived in `app-framework/tests/reexpress_subscription.rs` (the framework tree). This
// PROMOTES it into the crate: the four pub/sub operations are ONE [`DeosApp`]
// ([`subscription_deos_app`] below); the framework wires the rest — per-viewer
// projection, web-of-cells publish (the FEED cell IS a `dregg://` sturdyref),
// per-viewer rehydration, the generated `<dregg-affordance-surface>` component, and
// the manifest — none of which the old bones had. `register(ctx)` now mounts it (see
// [`register_deos`]).
//
// **The seam is closed** — a TWO-TEMPO fire (mirror supply-chain-provenance). The two
// state-advancing operations (`publish`, `consume`) are [`GatedAffordance`]s carrying a
// live-state PRECONDITION; the FULL queue invariants (the descriptor's
// `state_constraints`: `Monotonic` head/tail, `WriteOnce` capacity/owner,
// `FieldLteField(tail <= head)`) are INSTALLED on the seeded feed cell ([`seed_feed`])
// and RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_publish`] / [`fire_consume`] then submit the FULL multi-effect
//      publish/consume turn ([`publish_effects`] / [`consume_effects`]), and the
//      executor RE-ENFORCES the installed invariants — so a REWOUND delivery cursor (a
//      `publish` whose head is rolled back to forge re-delivery room, `Monotonic(SEQ_HEAD)`)
//      and an OVER-DELIVER (a `consume` whose tail passes the head, `FieldLteField(tail <=
//      head)`) are REAL executor refusals in the SUBMISSION path — the half the floor's
//      `evaluate_with_meta`-only tests never exercised through a real signed turn (see
//      `tests/deos_seam.rs`). (The flat invariants carry `Monotonic` (`>=`), so a no-advance
//      head stays put; the per-op `MonotonicSequence(+1)` exact-advance lives in the full
//      [`subscription_program`] `Cases`, bound by the child program VK.)
//
// Recurring delivery as gated affordances: each `publish` is a billing/delivery event
// that advances the producer cursor (`Monotonic(SEQ_HEAD)`, never rewound); each `consume`
// draws delivered items forward under `tail <= head` — a consumer can never over-draw the
// feed (the executor refuses).

/// The pub/sub rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the roles the
/// floor crate's cap-graph enforces:
///
///   - a CONSUMER holds [`AuthRequired::Signature`] — the narrow reader tier: it can
///     `consume` (draw a delivered item forward) and `view_feed`, nothing else;
///   - a PUBLISHER holds [`AuthRequired::Either`] — it can `publish` (a recurring
///     delivery) AND consume AND view;
///   - the OWNER holds [`AuthRequired::None`]/root — it can `grant_publisher` /
///     `grant_consumer` (admit members) on top of everything a publisher can do.
///
/// So `Signature ⊂ Either ⊂ None` IS the consumer ⊂ publisher ⊂ owner ladder.
pub const CONSUMER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The publisher rights tier (sig-or-proof — publish + consume + view). See [`CONSUMER_RIGHTS`].
pub const PUBLISHER_RIGHTS: AuthRequired = AuthRequired::Either;
/// The owner rights tier (root — grant publishers/consumers + all). See [`CONSUMER_RIGHTS`].
pub const OWNER_RIGHTS: AuthRequired = AuthRequired::None;

/// The **life-of-cell queue invariants** the executor re-enforces on every touching
/// turn — exactly the descriptor's `state_constraints` (`WriteOnce` capacity/owner,
/// `FieldLteField(tail <= head)`, `Monotonic` head/tail). This is the FLAT predicate a
/// factory-born feed cell carries FOR LIFE (the same one `tests/factory_birth.rs`
/// proves bites on the executor); the full operation-scoped [`subscription_program`]
/// `Cases` shape is bound by the child program VK. Installed by [`seed_feed`] so the
/// gated fires re-enforce it.
pub fn feed_invariants_program() -> CellProgram {
    CellProgram::Predicate(subscription_factory_descriptor().state_constraints)
}

/// The `publish` **live-state precondition** — the feed must be CONFIGURED (capacity
/// bound, `CAPACITY >= 1`). A real [`CellProgram`] read against the cell's current
/// state, so a publish button is DARK on an unconfigured feed and LIT once configured
/// (the htmx tooth). This gates "may `publish` fire now"; the delivery INVARIANT
/// (`Monotonic(SEQ_HEAD)`, head strictly advances) is the installed
/// [`feed_invariants_program`] the executor re-enforces on the produced transition.
pub fn configured_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: CAPACITY_SLOT,
        value: field_from_u64(1),
    }])
}

/// The `consume` **live-state precondition** — the feed must have an UNDRAINED item
/// (`SEQ_HEAD > SEQ_TAIL`, i.e. `tail < head`). So the `consume` button is DARK on a
/// drained feed (tail caught up to head) and LIT when a delivery is pending (the htmx
/// tooth). The executor's installed `FieldLteField(tail <= head)` is the second guard
/// (an over-draw past the head is a real refusal).
pub fn pending_precondition() -> CellProgram {
    // `tail < head` ≡ `tail <= head - 1` ≡ `FieldLteOther { tail, head, delta: -1 }`.
    CellProgram::Predicate(vec![StateConstraint::FieldLteOther {
        index: SEQ_TAIL_SLOT,
        other: SEQ_HEAD_SLOT,
        delta: -1,
    }])
}

/// **The subscription FEED as a composed [`DeosApp`]** — the whole interaction surface,
/// on the deos bones. The feed cell is the agent's OWN cell (`cipherclerk.cell_id()`)
/// so fires execute against the seeded embedded ledger.
///
/// Four operations on the FEED cell, on the consumer ⊂ publisher ⊂ owner rights ladder:
///
///   - `view_feed` — a cap-only affordance (a CONSUMER reads the head-of-queue):
///     `Signature`, an `EmitEvent`;
///   - `consume` — a [`GatedAffordance`] (a CONSUMER draws an item forward):
///     `Signature`, a live-state PRECONDITION (a delivery is pending); the real fire
///     ([`fire_consume`]) submits the FULL consume turn, re-enforced by the executor's
///     installed invariants (`MonotonicSequence(SEQ_TAIL)` under `tail <= head`);
///   - `publish` — a [`GatedAffordance`] (a PUBLISHER delivers): `Either`, a live-state
///     PRECONDITION (the feed is configured); the real fire ([`fire_publish`]) submits
///     the FULL publish turn, re-enforced by the executor (`Monotonic(SEQ_HEAD)`);
///   - `grant_publisher` / `grant_consumer` — cap-only affordances carrying the real
///     root-advancing `Effect::SetField` (the owner admits a member): `None`/root.
///
/// The feed cell is published into the web-of-cells at the consumer tier (a peer on
/// another federation reacquires the feed across the membrane) and is discoverable under
/// `pubsub` / `feed`.
///
/// Seed the cell's program + configured state with [`seed_feed`] so the gated fires have
/// a live state and the executor re-enforces the invariants.
pub fn subscription_deos_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let feed = cipherclerk.cell_id();

    // `publish` — a PUBLISHER delivers (recurring). The GatedAffordance carries the
    // DECISIVE effect (the producer-cursor advance) as its surface representative AND a
    // live-state PRECONDITION ([`configured_precondition`]: the feed is configured) — so
    // the button is dark before configure and lit after, and the cap∧state gate decides
    // its verdict in-band. The actual fire ([`fire_publish`]) submits the FULL publish
    // turn ([`publish_effects`]: head + message_root + latest_payload + event), which the
    // executor re-enforces the installed invariants on — so `Monotonic(SEQ_HEAD)` BITES:
    // a non-advancing (stale) delivery is REFUSED.
    let publish = GatedAffordance::new(
        CellAffordance::new(
            "publish",
            PUBLISHER_RIGHTS,
            Effect::SetField {
                cell: feed,
                index: SEQ_HEAD_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        configured_precondition(),
    );
    // `consume` — a CONSUMER draws a delivered item forward. The decisive effect advances
    // the consumer cursor; gated on the PENDING precondition ([`pending_precondition`]:
    // `tail < head`, an item is undrained). The executor re-enforces the installed
    // invariants (so `FieldLteField(tail <= head)` bites — an over-draw past the head is
    // refused).
    let consume = GatedAffordance::new(
        CellAffordance::new(
            "consume",
            CONSUMER_RIGHTS,
            Effect::SetField {
                cell: feed,
                index: SEQ_TAIL_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        pending_precondition(),
    );
    // `grant_publisher` / `grant_consumer` — the owner admits a member. A real
    // root-advancing `Effect::SetField`, cap-only (the membership half — no cursor move).
    let grant_publisher = CellAffordance::new(
        "grant_publisher",
        OWNER_RIGHTS,
        Effect::SetField {
            cell: feed,
            index: PUBLISHERS_ROOT_SLOT as usize,
            value: field_from_u64(1),
        },
    );
    let grant_consumer = CellAffordance::new(
        "grant_consumer",
        OWNER_RIGHTS,
        Effect::SetField {
            cell: feed,
            index: CONSUMERS_ROOT_SLOT as usize,
            value: field_from_u64(1),
        },
    );
    // `view_feed` — a consumer reads the head-of-queue. Cap-only.
    let view = CellAffordance::new(
        "view_feed",
        CONSUMER_RIGHTS,
        Effect::EmitEvent {
            cell: feed,
            event: Event::new(symbol("feed-read"), vec![]),
        },
    );

    DeosApp::builder("subscription", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["pubsub".into(), "feed".into()])
        .cell(
            DeosCell::new(feed, "feed")
                .affordance(view)
                .gated(publish)
                .gated(consume)
                .affordance(grant_publisher)
                .affordance(grant_consumer)
                .publish(CONSUMER_RIGHTS),
        )
        .build()
}

/// **Seed the FEED cell** so the gated fires have live state + the invariants bite:
/// install the queue invariants ([`feed_invariants_program`]) on the seeded feed cell
/// (so the executor re-enforces them on every touching turn), then configure the genesis
/// state directly into the embedded ledger — bind `CAPACITY` and `OWNER_PK_HASH`
/// (`WriteOnce`, frozen after) and seed one pending delivery (`SEQ_HEAD = 1`,
/// `SEQ_TAIL = 0`) so a real `(old, new)` baseline exists against which `publish`
/// advances the head and `consume` draws the tail.
///
/// After seeding, the feed is configured with one undrained item — a real baseline.
/// Returns the seeded `SEQ_HEAD` value.
pub fn seed_feed(executor: &EmbeddedExecutor, capacity: u64, owner: &str) -> u64 {
    let feed = executor.cell_id();
    executor.install_program(feed, feed_invariants_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&feed) {
            cell.state
                .set_field(CAPACITY_SLOT as usize, field_from_u64(capacity));
            cell.state.set_field(
                OWNER_PK_HASH_SLOT as usize,
                field_from_bytes(owner.as_bytes()),
            );
            // one pending delivery: head at 1, tail at 0 (tail < head).
            cell.state
                .set_field(SEQ_HEAD_SLOT as usize, field_from_u64(1));
            cell.state
                .set_field(SEQ_TAIL_SLOT as usize, field_from_u64(0));
        }
    });
    1
}

/// **`publish` effects** — the multi-effect delivery body: advance the producer cursor
/// `SEQ_HEAD` to `new_head` (`Monotonic` — strictly forward), fold the new message into
/// `MESSAGE_ROOT`, write `LATEST_PAYLOAD`, and emit `subscription-published`. This is the
/// ONE coherent transition the installed invariants admit (head advances, tail/capacity/
/// owner unchanged, `tail <= head` preserved). The deos `publish` gated affordance is the
/// cap∧state PRECONDITION face; THIS is the turn [`fire_publish`] submits.
pub fn publish_effects(
    feed: CellId,
    new_head: u64,
    new_message_root: FieldElement,
    payload_hash: FieldElement,
) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: feed,
            index: SEQ_HEAD_SLOT as usize,
            value: field_from_u64(new_head),
        },
        Effect::SetField {
            cell: feed,
            index: MESSAGE_ROOT_SLOT as usize,
            value: new_message_root,
        },
        Effect::SetField {
            cell: feed,
            index: LATEST_PAYLOAD_SLOT as usize,
            value: payload_hash,
        },
        Effect::EmitEvent {
            cell: feed,
            event: Event::new(
                symbol("subscription-published"),
                vec![field_from_u64(new_head), new_message_root, payload_hash],
            ),
        },
    ]
}

/// **`consume` effects** — the multi-effect draw body: advance the consumer cursor
/// `SEQ_TAIL` to `new_tail` and emit `subscription-consumed`. The installed
/// `FieldLteField(tail <= head)` re-enforces that the draw never passes the head (no
/// over-deliver). THIS is the turn [`fire_consume`] submits.
pub fn consume_effects(feed: CellId, new_tail: u64, consumed_payload: FieldElement) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: feed,
            index: SEQ_TAIL_SLOT as usize,
            value: field_from_u64(new_tail),
        },
        Effect::EmitEvent {
            cell: feed,
            event: Event::new(
                symbol("subscription-consumed"),
                vec![field_from_u64(new_tail), consumed_payload],
            ),
        },
    ]
}

/// **Fire `publish`** — the deos cap∧state PRECONDITION gate (anti-ghost, in-band), then
/// the FULL multi-effect delivery turn the executor re-enforces the queue invariants on.
/// The two-tempo bridge: the gated affordance decides the button's verdict (cap ⊇ Either
/// AND the feed is configured) WITHOUT touching the executor; on both passing, the
/// complete cursor-advancing turn ([`publish_effects`]) is submitted, and the executor's
/// re-enforcement of [`feed_invariants_program`] is the SECOND, verified gate
/// (`Monotonic(SEQ_HEAD)` bites — a REWOUND delivery cursor is REFUSED). Anti-ghost both
/// ways: a precondition miss never submits; an invariant violation is a real executor refusal.
///
/// The cursor is read from the cell's live state (current `SEQ_HEAD` ⇒ the next head),
/// so the caller threads nothing. Use [`seed_feed`] first.
pub fn fire_publish(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let feed = cell.cell();
    // Tooth 1+2: the deos cap∧state PRECONDITION gate, in-band, nothing submitted on a miss.
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "publish")
    {
        let ga = cell
            .gated_surface()
            .get("publish")
            .expect("publish is a gated affordance");
        let state = executor.cell_state(feed).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "publish".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(feed, held, &state, &state).unwrap_err(),
        ));
    }
    // The cursor, read from live state: the next head strictly advances the current one.
    let state = executor.cell_state(feed).expect("checked above");
    let head = field_to_u64(&state.fields[SEQ_HEAD_SLOT as usize]);
    let new_head = head + 1;
    // The delivered message folds the new head into the prior root (a real commitment move).
    let prev_root = state.fields[MESSAGE_ROOT_SLOT as usize];
    let payload = field_from_bytes(&new_head.to_be_bytes());
    let new_root = fold_message_root(&prev_root, new_head, &payload);
    // Submit the FULL multi-effect delivery turn — the executor re-enforces the invariants.
    let action = cipherclerk.make_action(
        feed,
        "publish",
        publish_effects(feed, new_head, new_root, payload),
    );
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// **Fire `consume`** — the deos cap∧state PRECONDITION gate (cap ⊇ Signature AND a
/// delivery is pending, `tail < head`), then the FULL consume turn ([`consume_effects`]).
/// Like [`fire_publish`], the gated affordance decides the button in-band and the
/// executor's re-enforcement (`FieldLteField(tail <= head)`, the draw never passes the
/// head) is the verified second gate. Use [`seed_feed`] first.
pub fn fire_consume(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let feed = cell.cell();
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "consume")
    {
        let ga = cell
            .gated_surface()
            .get("consume")
            .expect("consume is a gated affordance");
        let state = executor.cell_state(feed).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "consume".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(feed, held, &state, &state).unwrap_err(),
        ));
    }
    let state = executor.cell_state(feed).expect("checked above");
    let tail = field_to_u64(&state.fields[SEQ_TAIL_SLOT as usize]);
    let new_tail = tail + 1;
    let consumed = state.fields[LATEST_PAYLOAD_SLOT as usize];
    let action =
        cipherclerk.make_action(feed, "consume", consume_effects(feed, new_tail, consumed));
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// Fold a delivered `(seq, payload)` into the running `MESSAGE_ROOT` commitment —
/// `blake3(prev ‖ seq ‖ payload)`. Deterministic and collision-resistant; the
/// production face of the queue's per-message commitment (a different payload at the
/// same seq produces a different root, so the consumer's membership check detects it).
pub fn fold_message_root(prev: &FieldElement, seq: u64, payload: &FieldElement) -> FieldElement {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-subscription-msg\x01");
    h.update(prev);
    h.update(&seq.to_be_bytes());
    h.update(payload);
    *h.finalize().as_bytes()
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// `field_from_u64` for the head/tail cursors the feed stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// **Mount the deos-native surface** ([`subscription_deos_app`]) on a shared context:
/// build the composed [`DeosApp`] from the context's cipherclerk + executor, seed the
/// feed cell's program + configured state (so the gated fires bite), and fold the app
/// into the context's affordance registry ([`DeosApp::register`]). Returns the live
/// [`DeosApp`] (so a host can also [`DeosApp::mount`] its axum router /
/// [`DeosApp::publish_all`] into the web-of-cells). This is the PROMOTION the census
/// Tier-1 #2 asks for: the deos surface now ships from `src/`, not from a side-proof in
/// `app-framework/tests/`.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = subscription_deos_app(ctx.cipherclerk(), ctx.executor());
    // Seed the feed cell so the gated `publish` / `consume` fires have a live `(old, new)`
    // and the queue invariants (installed here) are re-enforced by the executor on every
    // touching turn.
    seed_feed(ctx.executor(), 16, "owner");
    app.register(ctx);
    app
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// The canonical web-constants module — the single Rust source of truth for the
/// slot layout + the four subscription event topics + the factory-vk hex. A host
/// renders it into JS/JSON for its web surface; the legacy `pages/` static surface
/// it once backed has been retired in favour of the deos card (AX4, [`card`]).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("subscription")
        .slot("SEQ_HEAD_SLOT", SEQ_HEAD_SLOT as u64)
        .slot("SEQ_TAIL_SLOT", SEQ_TAIL_SLOT as u64)
        .slot("CAPACITY_SLOT", CAPACITY_SLOT as u64)
        .slot("PUBLISHERS_ROOT_SLOT", PUBLISHERS_ROOT_SLOT as u64)
        .slot("CONSUMERS_ROOT_SLOT", CONSUMERS_ROOT_SLOT as u64)
        .slot("OWNER_PK_HASH_SLOT", OWNER_PK_HASH_SLOT as u64)
        .slot("MESSAGE_ROOT_SLOT", MESSAGE_ROOT_SLOT as u64)
        .slot("LATEST_PAYLOAD_SLOT", LATEST_PAYLOAD_SLOT as u64)
        // Record-layer Stage 0: first user-map key (>= STATE_SLOTS).
        .slot("SUBSCRIBER_COUNT_KEY", SUBSCRIBER_COUNT_KEY)
        .string("FACTORY_VK_HEX", hex_encode_32(&SUBSCRIPTION_FACTORY_VK))
        .topic("PUBLISHED", "subscription-published")
        .topic("CONSUMED", "subscription-consumed")
        .topic("PUBLISHER_GRANTED", "subscription-publisher-granted")
        .topic("CONSUMER_GRANTED", "subscription-consumer-granted")
}

/// Register this starbridge-app on a [`StarbridgeAppContext`].
///
/// Wires the subscription factory descriptor and the
/// `<dregg-subscription>` family of inspector descriptors into the
/// shared host registry. Returns the registered `factory_vk` so the
/// host can log it.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(subscription_factory_descriptor());

    // Per-subscription inspector — the head-of-queue summary mount.
    ctx.register_inspector(InspectorDescriptor {
        kind: "subscription".into(),
        descriptor: serde_json::json!({
            "component": "dregg-subscription",
            "module": "/starbridge-apps/subscription/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": [
                "seq_head", "seq_tail", "capacity",
                "publishers_root", "consumers_root", "message_root",
                "latest_payload_hash",
            ],
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&subscription_child_program_vk()),
        }),
    });

    // Publisher's compose-and-publish form. Distinct kind so the
    // Studio can mount a different React component.
    ctx.register_inspector_with("subscription-publish-form", || {
        serde_json::json!({
            "component": "dregg-subscription-publish-form",
            "module": "/starbridge-apps/subscription/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "factory_vk_hex": hex_encode_32(&SUBSCRIPTION_FACTORY_VK),
        })
    });

    // Consumer's live feed view (the head-of-queue stream).
    ctx.register_inspector_with("subscription-feed", || {
        serde_json::json!({
            "component": "dregg-subscription-feed",
            "module": "/starbridge-apps/subscription/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "factory_vk_hex": hex_encode_32(&SUBSCRIPTION_FACTORY_VK),
        })
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context —
    // the census Tier-1 #2 promotion: the deos surface now ships from `src/`, not from a
    // side-proof in `app-framework/tests/`. The factory + inspectors are where SOUNDNESS
    // lives (a stale delivery / over-draw is a real executor refusal on the born cell);
    // the deos surface is the composition skin (per-viewer projection, the cap∧state
    // gated fires, the `dregg://` publish, the rehydratable snapshot, the manifest).
    register_deos(ctx);

    factory_vk
}

// =============================================================================
// Tests — adversarial transition tests live in tests/program.rs
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
        CellId::from_bytes([7u8; 32])
    }

    fn u64_field(value: u64) -> FieldElement {
        let mut out = [0u8; 32];
        out[24..32].copy_from_slice(&value.to_be_bytes());
        out
    }

    fn blake3_field(bytes: &[u8]) -> FieldElement {
        *blake3::hash(bytes).as_bytes()
    }

    // ─── Record-layer Stage 0: committed user-field MAP (end-to-end) ─────

    /// The 16/16-full subscription cell gains an unbounded overflow field
    /// (`subscriber_count`, user-map key 16) via the committed `fields_root`.
    /// END-TO-END: write -> root update -> committed membership read-back.
    #[test]
    fn subscriber_count_overflow_field_roundtrips_through_fields_root() {
        let mut state = dregg_cell::CellState::new(0);
        // Empty map => fixed empty-map constant (legacy backward-compat).
        assert_eq!(state.fields_root, dregg_cell::empty_fields_root());
        assert_eq!(read_subscriber_count(&state), None, "absent before write");

        // Write the overflow field (key 16) — the 16 fixed slots are untouched.
        assert!(write_subscriber_count(&mut state, 1234));
        assert_ne!(
            state.fields_root,
            dregg_cell::empty_fields_root(),
            "the committed root must move once the map carries a value"
        );

        // Committed read-back: the value is genuinely committed by fields_root.
        assert_eq!(
            read_subscriber_count(&state),
            Some(1234),
            "membership read-back must return the committed value"
        );

        // The fixed slots 0..15 are all still zero — the map did not steal a slot.
        for i in 0..dregg_cell::STATE_SLOTS {
            assert_eq!(*state.get_field(i).unwrap(), [0u8; 32]);
        }
    }

    /// ANTI-VACUITY (negative witness): a tampered committed root rejects the
    /// read-back — the membership proof is load-bearing, not a `:= 0` stub.
    #[test]
    fn subscriber_count_membership_rejects_tampered_root() {
        let mut state = dregg_cell::CellState::new(0);
        write_subscriber_count(&mut state, 1234);
        assert_eq!(read_subscriber_count(&state), Some(1234));

        // Tamper the stored root so it no longer matches the map's digest.
        state.fields_root = [0xAAu8; 32];
        assert_eq!(
            read_subscriber_count(&state),
            None,
            "a root that does not commit the map must reject the read-back"
        );
    }

    // ─── FactoryDescriptor tests ────────────────────────────────────────

    #[test]
    fn factory_descriptor_is_stable() {
        let h1 = subscription_factory_descriptor().hash();
        let h2 = subscription_factory_descriptor().hash();
        assert_eq!(h1, h2, "descriptor hash must be deterministic");
    }

    #[test]
    fn factory_descriptor_pins_program_vk() {
        let d = subscription_factory_descriptor();
        assert_eq!(d.factory_vk, SUBSCRIPTION_FACTORY_VK);
        assert_eq!(d.child_program_vk, Some(subscription_child_program_vk()));
        assert_eq!(d.default_mode, CellMode::Hosted);
        assert_eq!(d.creation_budget, Some(DEFAULT_CREATION_BUDGET));
    }

    #[test]
    fn subscription_child_program_vk_is_canonical_recipe() {
        // Per VK-AS-RE-EXECUTION-RECIPE.md §2.1: validators with
        // `subscription_program()` in scope re-derive the VK and re-execute.
        let expected = dregg_app_framework::canonical_program_vk(&subscription_program());
        assert_eq!(
            subscription_child_program_vk(),
            expected,
            "subscription_child_program_vk must equal canonical_program_vk(&subscription_program())"
        );
    }

    #[test]
    fn subscription_child_program_vk_is_not_placeholder_bytes() {
        let old_placeholder: [u8; 32] = *b"starbridge-subscription-childprg";
        assert_ne!(
            subscription_child_program_vk(),
            old_placeholder,
            "canonical VK must differ from the pre-recipe placeholder"
        );
    }

    #[test]
    fn subscription_child_program_vk_is_v2_layered_hash() {
        // VK v2 (VK-AS-RE-EXECUTION-RECIPE.md §v2): the layered hash
        // must differ from the v1 program-bytes-only hash.
        let program = subscription_program();
        let v2 = subscription_child_program_vk();
        let v1 = dregg_app_framework::canonical_program_bytes_hash(&program);
        assert_ne!(
            v2, v1,
            "v2 layered hash must differ from v1 program-bytes-only hash"
        );
    }

    #[test]
    fn factory_descriptor_validates_against_canonical_program() {
        // VK v2: the app-framework wrapper validates against the
        // *layered* canonical hash (program bytes + Effect VM AIR +
        // verifier + Plonky3 proving system).
        let d = subscription_factory_descriptor();
        let program = subscription_program();
        dregg_app_framework::validate_child_vk_canonical(&d, &program)
            .expect("descriptor's child_program_vk must bind to subscription_program() under v2");
    }

    #[test]
    fn factory_descriptor_bakes_invariant_write_once() {
        // `WriteOnce` (not `Immutable`): a factory-born subscription is empty, so
        // capacity + owner are bound ONCE by the first `configure` turn (from zero)
        // and frozen thereafter — the birth-compatible form of "set at creation,
        // never changes".
        let d = subscription_factory_descriptor();
        assert!(
            d.state_constraints.iter().any(
                |c| matches!(c, StateConstraint::WriteOnce { index } if *index == CAPACITY_SLOT)
            ),
            "factory must install WriteOnce on CAPACITY_SLOT (bound once, frozen after)"
        );
        assert!(
            d.state_constraints
                .iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == OWNER_PK_HASH_SLOT)),
            "factory must install WriteOnce on OWNER_PK_HASH_SLOT (bound once, frozen after)"
        );
    }

    #[test]
    fn factory_descriptor_bakes_monotonic_invariants() {
        let d = subscription_factory_descriptor();
        for slot in [SEQ_HEAD_SLOT, SEQ_TAIL_SLOT] {
            assert!(
                d.state_constraints
                    .iter()
                    .any(|c| matches!(c, StateConstraint::Monotonic { index } if *index == slot)),
                "factory must install Monotonic on slot {slot}"
            );
        }
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::FieldLteField { left_index, right_index }
                    if *left_index == SEQ_TAIL_SLOT && *right_index == SEQ_HEAD_SLOT
            )),
            "factory must install tail <= head invariant"
        );
    }

    #[test]
    fn factory_descriptor_has_no_birth_field_constraints() {
        // A factory-born subscription cell mints empty: head == tail == 0 ALREADY
        // (a born cell is all-zero), capacity/owner zero until the first `configure`
        // turn binds them under `WriteOnce`. Creation-time `field_constraints`
        // (the old head==tail==0 `Equality`, capacity `Range`, owner `NonZero`)
        // forced the seed path to mint placeholders — an owner placeholder is a
        // real soundness hazard. We carry NONE (mirroring privacy-voting/
        // bounty-board); the head/tail invariant is the perpetual `FieldLteField`
        // `state_constraints`, which already hold at the all-zero birth state.
        let d = subscription_factory_descriptor();
        assert!(
            d.field_constraints.is_empty(),
            "subscription factory must carry NO creation-time field_constraints; \
             head==tail==0 already holds at birth and capacity/owner are bound by \
             the first configure turn under WriteOnce"
        );
    }

    #[test]
    fn factory_descriptors_slice_contains_subscription() {
        let all = factory_descriptors();
        assert_eq!(all.len(), 1);
        assert_eq!(all[0].factory_vk, SUBSCRIPTION_FACTORY_VK);
    }

    // ─── Turn-builder shape tests ───────────────────────────────────────

    #[test]
    fn publish_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let new_head = u64_field(1);
        let new_root = blake3_field(b"root-after-1");
        let payload = blake3_field(b"payload");
        let action = build_publish_action(&cipherclerk, cell, new_head, new_root, payload);

        assert_eq!(action.target, cell);
        assert_eq!(action.method, symbol("publish"));
        assert_eq!(action.effects.len(), 4, "publish has 3 SetField + 1 Event");
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == SEQ_HEAD_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == MESSAGE_ROOT_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, .. } if *index == LATEST_PAYLOAD_SLOT as usize
        ));
        assert!(matches!(&action.effects[3], Effect::EmitEvent { .. }));
    }

    #[test]
    fn consume_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let action =
            build_consume_action(&cipherclerk, cell, u64_field(1), blake3_field(b"payload"));

        assert_eq!(action.method, symbol("consume"));
        assert_eq!(action.effects.len(), 2);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == SEQ_TAIL_SLOT as usize
        ));
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    #[test]
    fn grant_publisher_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let new_root = blake3_field(b"publishers-root-v1");
        let action = build_grant_publisher_action(&cipherclerk, cell, new_root, [9u8; 32]);

        assert_eq!(action.method, symbol("grant_publisher"));
        assert_eq!(action.effects.len(), 2);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. }
            if *index == PUBLISHERS_ROOT_SLOT as usize && *value == new_root
        ));
    }

    #[test]
    fn grant_consumer_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let new_root = blake3_field(b"consumers-root-v1");
        let action = build_grant_consumer_action(&cipherclerk, cell, new_root, [11u8; 32]);

        assert_eq!(action.method, symbol("grant_consumer"));
        assert_eq!(action.effects.len(), 2);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. }
            if *index == CONSUMERS_ROOT_SLOT as usize && *value == new_root
        ));
    }

    #[test]
    fn actions_carry_real_signatures() {
        // No `[0u8; 64]` placeholders anywhere.
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let actions = [
            build_publish_action(
                &cipherclerk,
                cell,
                u64_field(1),
                blake3_field(b"r"),
                blake3_field(b"p"),
            ),
            build_consume_action(&cipherclerk, cell, u64_field(1), blake3_field(b"p")),
            build_grant_publisher_action(&cipherclerk, cell, blake3_field(b"r"), [9u8; 32]),
            build_grant_consumer_action(&cipherclerk, cell, blake3_field(b"r"), [11u8; 32]),
        ];
        for a in &actions {
            match &a.authorization {
                Authorization::Signature(r, s) => {
                    assert!(
                        *r != [0u8; 32] || *s != [0u8; 32],
                        "signature must be non-zero (no [0u8; 64] placeholders!)"
                    );
                }
                other => panic!("expected Signature variant, got {other:?}"),
            }
        }
    }

    #[test]
    fn different_cipherclerks_produce_different_signatures() {
        let cc1 = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let cc2 = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let cell = test_cell();
        let payload = blake3_field(b"payload");
        let a1 = build_publish_action(&cc1, cell, u64_field(1), blake3_field(b"r"), payload);
        let a2 = build_publish_action(&cc2, cell, u64_field(1), blake3_field(b"r"), payload);
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

    // ─── CellProgram: structural shape ──────────────────────────────────

    #[test]
    fn program_is_cases_with_five_branches() {
        match subscription_program() {
            CellProgram::Cases(cases) => {
                assert_eq!(cases.len(), 5, "expected one Always + four MethodIs cases");
            }
            other => panic!("expected CellProgram::Cases, got {other:?}"),
        }
    }

    #[test]
    fn program_covers_all_four_methods() {
        let cases = match subscription_program() {
            CellProgram::Cases(c) => c,
            _ => panic!("expected Cases"),
        };
        let mut seen_publish = false;
        let mut seen_consume = false;
        let mut seen_grant_pub = false;
        let mut seen_grant_con = false;
        for case in &cases {
            if let TransitionGuard::MethodIs { method } = &case.guard {
                if *method == symbol("publish") {
                    seen_publish = true;
                }
                if *method == symbol("consume") {
                    seen_consume = true;
                }
                if *method == symbol("grant_publisher") {
                    seen_grant_pub = true;
                }
                if *method == symbol("grant_consumer") {
                    seen_grant_con = true;
                }
            }
        }
        assert!(seen_publish, "publish case missing");
        assert!(seen_consume, "consume case missing");
        assert!(seen_grant_pub, "grant_publisher case missing");
        assert!(seen_grant_con, "grant_consumer case missing");
    }

    #[test]
    fn publish_case_advances_head_only() {
        let cases = match subscription_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let publish_case = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("publish")))
            .expect("publish case present");
        assert!(
            publish_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::MonotonicSequence { seq_index } if *seq_index == SEQ_HEAD_SLOT
            )),
            "publish must MonotonicSequence head"
        );
        assert!(
            publish_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::Immutable { index } if *index == SEQ_TAIL_SLOT
            )),
            "publish must lock tail Immutable (no tail advance)"
        );
    }

    #[test]
    fn consume_case_advances_tail_only() {
        let cases = match subscription_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let consume_case = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("consume")))
            .expect("consume case present");
        assert!(
            consume_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::MonotonicSequence { seq_index } if *seq_index == SEQ_TAIL_SLOT
            )),
            "consume must MonotonicSequence tail"
        );
        assert!(
            consume_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::Immutable { index } if *index == SEQ_HEAD_SLOT
            )),
            "consume must lock head Immutable (no head advance)"
        );
    }

    // ─── StarbridgeAppContext registration ──────────────────────────────

    #[test]
    fn register_installs_subscription_factory() {
        let ctx = test_context();
        assert_eq!(ctx.factory_registry().len(), 0);
        let vk = register(&ctx);
        assert_eq!(vk, SUBSCRIPTION_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        let got = ctx
            .factory_registry()
            .get(&SUBSCRIPTION_FACTORY_VK)
            .expect("subscription factory registered");
        assert_eq!(got.factory_vk, SUBSCRIPTION_FACTORY_VK);
        assert_eq!(got.child_program_vk, Some(subscription_child_program_vk()));
        assert_eq!(got.default_mode, CellMode::Hosted);
    }

    #[test]
    fn register_installs_three_inspectors() {
        let ctx = test_context();
        register(&ctx);
        for kind in [
            "subscription",
            "subscription-publish-form",
            "subscription-feed",
        ] {
            assert!(
                ctx.inspector_registry().get(kind).is_some(),
                "missing inspector kind: {kind}"
            );
        }
    }

    #[test]
    fn register_is_idempotent_on_factory() {
        let ctx = test_context();
        register(&ctx);
        register(&ctx);
        assert_eq!(ctx.factory_registry().len(), 1);
    }

    // ── Cross-app composition: bounty-state notifications ───────────────

    #[test]
    fn bounty_state_payload_hash_is_deterministic() {
        let id = [9u8; 32];
        let actor = [11u8; 32];
        let a = bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &actor);
        let b = bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &actor);
        assert_eq!(a, b);
    }

    #[test]
    fn bounty_state_payload_hash_distinguishes_transitions() {
        let id = [9u8; 32];
        let actor = [11u8; 32];
        let claim =
            bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &actor);
        let fulfill =
            bounty_state_payload_hash(&id, BountyState::Claimed, BountyState::Fulfilled, &actor);
        let settle =
            bounty_state_payload_hash(&id, BountyState::Fulfilled, BountyState::Settled, &actor);
        assert_ne!(claim, fulfill);
        assert_ne!(fulfill, settle);
        assert_ne!(claim, settle);
    }

    #[test]
    fn bounty_state_payload_hash_distinguishes_actors() {
        let id = [9u8; 32];
        let a1 =
            bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &[1u8; 32]);
        let a2 =
            bounty_state_payload_hash(&id, BountyState::Posted, BountyState::Claimed, &[2u8; 32]);
        assert_ne!(a1, a2);
    }

    #[test]
    fn bounty_state_payload_hash_distinguishes_bounties() {
        let actor = [11u8; 32];
        let h1 = bounty_state_payload_hash(
            &[1u8; 32],
            BountyState::Posted,
            BountyState::Claimed,
            &actor,
        );
        let h2 = bounty_state_payload_hash(
            &[2u8; 32],
            BountyState::Posted,
            BountyState::Claimed,
            &actor,
        );
        assert_ne!(h1, h2);
    }

    #[test]
    fn build_bounty_state_publish_action_emits_bounty_payload_hash() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let bounty_id = blake3_field(b"CVE-2025-1234");
        let actor_hash = blake3_field(b"dan-pk");
        let new_head = u64_field(1);
        let new_root = blake3_field(b"queue-root-1");

        let action = build_bounty_state_publish_action(
            &cipherclerk,
            cell,
            new_head,
            new_root,
            &bounty_id,
            BountyState::Claimed,
            BountyState::Fulfilled,
            &actor_hash,
        );

        assert_eq!(action.method, symbol("publish"));
        // Payload-bearing SetField is the third effect (LATEST_PAYLOAD_SLOT).
        match &action.effects[2] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, LATEST_PAYLOAD_SLOT as usize);
                assert_eq!(
                    *value,
                    bounty_state_payload_hash(
                        &bounty_id,
                        BountyState::Claimed,
                        BountyState::Fulfilled,
                        &actor_hash
                    )
                );
            }
            other => panic!("expected SetField on LATEST_PAYLOAD_SLOT, got {other:?}"),
        }
    }

    #[test]
    fn bounty_state_tag_field_distinguishes_states() {
        let states = [
            BountyState::Posted,
            BountyState::Claimed,
            BountyState::Fulfilled,
            BountyState::Settled,
            BountyState::Canceled,
        ];
        for i in 0..states.len() {
            for j in (i + 1)..states.len() {
                assert_ne!(states[i].tag_field(), states[j].tag_field());
            }
        }
    }
}
