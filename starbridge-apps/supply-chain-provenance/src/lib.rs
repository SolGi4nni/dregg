//! # starbridge-supply-chain-provenance
//!
//! **Verifiable supply-chain provenance** — an ITEM is a cell, a CUSTODY HANDOFF
//! is a cap-attenuated transfer, and SINGLE-CUSTODIANSHIP is a CONSERVATION law:
//! custody is conserved across handoffs, with EXACTLY ONE custodian at any time
//! (no double-custody, no replay), and the PROVENANCE is a tamper-evident receipt
//! chain a third party can re-derive and PROVE. All of it runs through the REAL
//! verified executor; a FORGED handoff (a party claiming custody it does not hold)
//! is REFUSED.
//!
//! This is the executable surface of two verified Lean developments, **composed
//! from existing slot-caveat atoms only** (no new Lean module):
//!
//! | Lean keystone                                            | What this crate enforces |
//! |---------------------------------------------------------|--------------------------|
//! | `AgentOrchestrationBudget.anyOf[immutable batonF, senderInField batonF]` | **actor-bound custody handoff**: the `CUSTODIAN` register may change only in a turn SIGNED BY the incoming holder (`stolen_baton_rejected`) |
//! | `AgentOrchestrationBudget.strictMono epochF`            | **no replay**: every handoff strictly advances the provenance epoch |
//! | `AgentProvenanceGated.prov_entry_writeonce`             | each custody-receipt link slot is `WriteOnce` — a committed link is frozen forever (tamper-evidence) |
//! | `AgentProvenanceGated.prov_head_cannot_rewind`          | the provenance `HEAD` is `Monotonic` — the chain is append-only (no truncate-then-fork) |
//! | `AgentProvenanceGated.prov_chain_links` / [`verify_chain`] | the receipt chain re-derives link-for-link from the published events — PROVE the full custody chain |
//! | `AgentOrchestration.derive_no_amplify`                  | the custody cap is handed forward NARROWED, never widened (no amplification) |
//!
//! ## The item cell (the provenance substrate)
//!
//! **The ITEM — a factory-born sovereign cell.** Its installed [`CellProgram`] IS
//! the custody policy, re-checked by the verified executor on EVERY turn that
//! touches it:
//!
//!   * [`CUSTODIAN_SLOT`] — the **current** custodian's identity scalar (the
//!     single-custodianship register). Guarded by `AnyOf[Immutable, SenderInSlot]`
//!     — the **actor-bound baton**: the custodian may change ONLY in a turn signed
//!     by the *incoming* holder (the Lean `anyOf[immutable, senderInField]`
//!     keystone). A turn that flips the custodian to a party that did not sign is
//!     REFUSED.
//!   * [`EPOCH_SLOT`] — the provenance epoch (the handoff counter). `StrictMonotonic`
//!     — every handoff strictly advances it; a replayed handoff (same / stale epoch)
//!     is REFUSED (the Lean `strictMono epochF`).
//!   * [`HEAD_SLOT`] — the provenance cursor (next link index). `Monotonic` — the
//!     custody chain is append-only (no re-order, no rewind, no truncate-then-fork).
//!   * [`TIP_SLOT`] — the latest committed custody-link digest (the chain tip a
//!     verifier reads first to walk the chain).
//!   * `LINK_BASE + i` — the i-th custody-receipt link digest. `WriteOnce` — a
//!     committed link is frozen forever (tamper-evidence).
//!
//! ## Custody is a capability (the cap-graph half of single-custodianship)
//!
//! A handoff is a **cap-attenuated transfer**: the incoming custodian gains the
//! item's custody capability and the prior custodian no longer holds it — EXACTLY
//! ONE custodian holds the cap at a time. This is the ocap half of
//! single-custodianship, enforced by the executor's c-list authorization gate: a
//! turn touching the item requires a capability reaching it, so a party that does
//! NOT hold the custody cap cannot hand the item off at all
//! ([`build_forged_handoff_action`] is REFUSED by the authorization gate). The
//! cap is handed forward NARROWED, never widened (the Lean `derive_no_amplify`).
//!
//! ## The provenance chain (PROVE the custody chain)
//!
//! Each handoff appends a custody-receipt link `link_i = blake3(prev ‖ event_i)`
//! where `event_i` binds (from_custodian, to_custodian, epoch). Because each link
//! folds the previous one, the chain binds the ENTIRE committed custody history;
//! because each link slot is `WriteOnce`, a committed link is frozen. A third
//! party PROVES the item's full custody chain by re-derivation: recompute the
//! honest chain from the published events and check it matches the committed
//! digests link-for-link ([`verify_chain`]). A tampered, forged, reordered, or
//! dropped handoff breaks the re-derivation — the provenance is verifiable by
//! re-execution, not by trust.
//!
//! ## Single-custodianship as conservation
//!
//! The beautiful invariant: across any honest custody chain, custody is conserved
//! — there is always EXACTLY ONE custodian (the latest `to`), and the chain of
//! `(from -> to)` handoffs is a connected path with no fork and no gap. The
//! `from` of handoff `i+1` is the `to` of handoff `i` ([`custody_chain_is_connected`]).
//! Mint creates the sole custodian; each handoff moves the sole custodianship
//! forward; nothing mints a second custodian or burns the custodian. The
//! conservation is witnessed three ways: the `WriteOnce`/`Monotonic` chain
//! (tamper-evidence + append-only), the `StrictMonotonic` epoch (no replay), and
//! the cap-graph (exactly one cap holder).
//!
//! ## Pre-submission assurance (`dregg-userspace-verify`)
//!
//! Before a handoff forest is submitted, it is linted by the userspace `analyze()`
//! toolkit — conservation (no value conjured), non-amplification (no in-forest
//! grant exceeds a delegated cap — a custodian re-granting WIDER custody than it
//! holds is caught), and well-formedness — so a stranger can pre-flight the
//! custody plan and SEE it pass (or see a malformed plan's findings) before
//! spending gas. See `tests/userspace_verify.rs`.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CapabilityRef, CellAffordance,
    CellId, CellMode, CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect,
    EmbeddedExecutor, Event, FactoryDescriptor, FieldElement, FireError, FireExecuteError,
    GatedAffordance, InspectorDescriptor, StarbridgeAppContext, StateConstraint, TurnReceipt,
    canonical_program_vk, field_from_u64, hex_encode_32, symbol,
};
use dregg_cell::program::SimpleStateConstraint;
use dregg_cell::state::STATE_SLOTS;

pub use dregg_app_framework::field_from_bytes;

// =============================================================================
// Slot layout (the ITEM cell) — the custody register + the provenance chain.
// =============================================================================

/// Slot 0 — `CUSTODIAN`. The **current** custodian's identity scalar (the
/// single-custodianship register). Guarded by `AnyOf[Immutable, SenderInSlot]` —
/// the actor-bound baton: it may change ONLY in a turn signed by the incoming
/// holder. Mirrors the Lean `batonF` under
/// `anyOf[immutable batonF, senderInField batonF]`.
pub const CUSTODIAN_SLOT: u8 = 0;

/// Slot 1 — `EPOCH`. The provenance epoch (the handoff counter). `StrictMonotonic`
/// — every handoff strictly advances it (no replay). Mirrors the Lean `epochF`.
pub const EPOCH_SLOT: u8 = 1;

/// Slot 2 — `HEAD`. The provenance cursor: the index of the NEXT custody-receipt
/// link to be written. `Monotonic` — the chain is append-only. Mirrors
/// `AgentProvenanceGated.HEAD`.
pub const HEAD_SLOT: u8 = 2;

/// Slot 3 — `TIP`. The latest committed custody-link digest (the chain tip a
/// verifier reads first). Mirrors `AgentProvenanceGated.TIP`.
pub const TIP_SLOT: u8 = 3;

/// The first custody-receipt link slot. Link `i` lives at `LINK_BASE + i`, each
/// carrying a `WriteOnce` caveat — a committed link is frozen forever
/// (tamper-evidence). Mirrors `AgentProvenanceGated.ENTRY_BASE`.
pub const LINK_BASE: u8 = 4;

/// How many custody-receipt link slots fit in a single item cell. A dregg cell
/// carries exactly [`STATE_SLOTS`] field slots; after reserving CUSTODIAN / EPOCH
/// / HEAD / TIP, the links occupy `LINK_BASE..STATE_SLOTS`. A provenance chain
/// longer than this per-cell capacity chains ACROSS item cells (the filled cell's
/// `TIP` is the genesis predecessor of the next cell's first link), so
/// [`verify_chain`] continues seamlessly across the boundary.
pub const LINK_CAPACITY: usize = STATE_SLOTS - LINK_BASE as usize;

/// The slot index of the i-th custody-receipt link.
pub fn link_slot(i: usize) -> usize {
    LINK_BASE as usize + i
}

// =============================================================================
// The custody POLICY (the slot-caveat predicate installed on every item cell).
// =============================================================================

/// The supply-chain custody POLICY as a flat conjunction of slot caveats — THIS is
/// the exact predicate the executor installs as the factory-born item's
/// `CellProgram` and re-checks on EVERY turn that touches the item. Each clause is
/// a primitive of the custody invariant; each refusal is a theorem on the Lean
/// side and a real executor refusal here:
///
///   * **actor-bound handoff** (`AnyOf[Immutable(CUSTODIAN), SenderInSlot(CUSTODIAN)]`):
///     the `CUSTODIAN` register may change ONLY in a turn SIGNED BY the incoming
///     holder. Either the custodian is unchanged (`Immutable` holds — a non-handoff
///     turn is open) OR the turn's sender IS the (new) recorded custodian
///     (`SenderInSlot`). A flip to a party that did not sign is REFUSED. This is
///     the Lean `anyOf[immutable batonF, senderInField batonF]` keystone
///     (`stolen_baton_rejected`).
///   * **no replay** (`StrictMonotonic(EPOCH)`): every touching handoff strictly
///     advances the provenance epoch; a replayed (same / stale epoch) handoff is
///     REFUSED. The Lean `strictMono epochF`. (The item is minted at epoch 1 so the
///     mint turn itself strictly advances 0 -> 1; handoffs then go 1 -> 2 -> 3 -> ….)
///   * **append-only chain** (`Monotonic(HEAD)`): the provenance cursor only grows;
///     a rewind (truncate-then-fork) is REFUSED. The Lean `prov_head_cannot_rewind`.
///   * **frozen links** (`WriteOnce(LINK_BASE + i)`): each committed custody-receipt
///     link is frozen forever; an overwrite is REFUSED (tamper-evidence). The Lean
///     `prov_entry_writeonce`.
pub fn custody_constraints() -> Vec<StateConstraint> {
    let mut cs = Vec::with_capacity(3 + LINK_CAPACITY);
    // actor-bound custody handoff — the custodian flips only in a turn signed by
    // the incoming holder (the verified baton keystone).
    cs.push(StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable {
                index: CUSTODIAN_SLOT,
            },
            SimpleStateConstraint::SenderInSlot {
                index: CUSTODIAN_SLOT,
            },
        ],
    });
    // no replay — every handoff strictly advances the provenance epoch.
    cs.push(StateConstraint::StrictMonotonic { index: EPOCH_SLOT });
    // append-only chain — the provenance cursor only grows.
    cs.push(StateConstraint::Monotonic { index: HEAD_SLOT });
    // frozen links — each committed custody-receipt link is write-once.
    for i in 0..LINK_CAPACITY {
        cs.push(StateConstraint::WriteOnce {
            index: link_slot(i) as u8,
        });
    }
    cs
}

/// The ITEM program — `custody_constraints` as a `CellProgram::Predicate`,
/// identical to what the factory installs on the born cell (so the program VK
/// names the exact installed predicate byte-for-byte).
pub fn item_program() -> CellProgram {
    CellProgram::Predicate(custody_constraints())
}

/// Canonical child program VK for the supply-chain item cell.
pub fn item_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&item_program())
}

// =============================================================================
// The custody-receipt LINK HASH (the provenance hash chain).
// =============================================================================

/// The genesis predecessor digest (no custody link before the mint).
pub const GENESIS_PREV: FieldElement = [0u8; 32];

/// Hash a party identity string to its identity scalar (the custodian register
/// stores `CUSTODIAN` as this scalar — the field image of a custodian's pubkey).
pub fn identity_field(party: &str) -> FieldElement {
    field_from_bytes(party.as_bytes())
}

/// **The custody EVENT digest** — `custody_event(from, to, epoch)` is the
/// canonical 32-byte digest of a single handoff: it binds the OUTGOING custodian,
/// the INCOMING custodian, and the provenance epoch. This is the payload each
/// receipt link commits to. Deterministic (a third party recomputes it exactly);
/// collision-resistant (a forged event hashing elsewhere is detectable).
pub fn custody_event(from: &FieldElement, to: &FieldElement, epoch: u64) -> FieldElement {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-custody-event\x01");
    h.update(from);
    h.update(to);
    h.update(&epoch.to_be_bytes());
    *h.finalize().as_bytes()
}

/// **The custody link hash** — `link_hash(prev, event)` is the digest stored at a
/// receipt link slot: `blake3(prev ‖ event)`, binding the new handoff event to the
/// ENTIRE committed prefix (since `prev` is itself the previous link). The
/// production (real-blake3) face of the Lean executable Horner shadow `linkHash`.
pub fn link_hash(prev: &FieldElement, event: &FieldElement) -> FieldElement {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-custody-link\x01");
    h.update(prev);
    h.update(event);
    *h.finalize().as_bytes()
}

/// A single handoff event in a custody history: `from` handed the item to `to` at
/// provenance epoch `epoch`. The mint is modelled as a handoff from
/// [`GENESIS_PREV`]'s identity (the zero scalar — "no prior custodian") to the
/// first custodian at epoch 1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Handoff {
    /// The outgoing custodian's identity scalar (the zero scalar for the mint).
    pub from: FieldElement,
    /// The incoming custodian's identity scalar.
    pub to: FieldElement,
    /// The provenance epoch this handoff advances to (mint = 1, then 2, 3, …).
    pub epoch: u64,
}

impl Handoff {
    /// The canonical custody event digest for this handoff.
    pub fn event(&self) -> FieldElement {
        custody_event(&self.from, &self.to, self.epoch)
    }
}

/// `custody_chain_digests(handoffs)` — the honest custody-link digest sequence for
/// a custody history: each link folds the PREVIOUS link's digest with the next
/// handoff event, starting from [`GENESIS_PREV`]. This is exactly what an honest
/// custody chain commits to `LINK_BASE + i`, and exactly what [`verify_chain`]
/// recomputes.
pub fn custody_chain_digests(handoffs: &[Handoff]) -> Vec<FieldElement> {
    let mut out = Vec::with_capacity(handoffs.len());
    let mut prev = GENESIS_PREV;
    for h in handoffs {
        let link = link_hash(&prev, &h.event());
        out.push(link);
        prev = link;
    }
    out
}

/// **`verify_chain`** — the third-party VERIFIER ("PROVE this item's full custody
/// chain"). Given the published handoff events and the link digests read off the
/// committed item cell, re-derive the honest chain from scratch and check they
/// match link-for-link. Returns `true` IFF every committed link equals
/// `link_hash(previous committed link, handoff_i.event())`, i.e. the chain is
/// EXACTLY the honest custody history. A tampered, reordered, forged, or dropped
/// handoff makes this `false` — the provenance is verifiable by re-execution.
pub fn verify_chain(handoffs: &[Handoff], committed: &[FieldElement]) -> bool {
    committed == custody_chain_digests(handoffs).as_slice()
}

/// **`custody_chain_is_connected`** — the single-custodianship CONSERVATION check
/// on a custody history: the `from` of every handoff equals the `to` of the
/// previous handoff (and the first handoff's `from` is the genesis zero scalar).
/// This is the structural witness that custody is CONSERVED — there is no fork (a
/// second custodian appearing from nowhere) and no gap (a handoff whose outgoing
/// holder is not the prior incoming holder). Returns `true` IFF the chain is a
/// single connected custody path.
pub fn custody_chain_is_connected(handoffs: &[Handoff]) -> bool {
    let mut expected_from = GENESIS_PREV; // the mint's `from` is "no prior custodian"
    for h in handoffs {
        if h.from != expected_from {
            return false;
        }
        // ...and the epoch must strictly advance (no replay), starting at 1.
        expected_from = h.to;
    }
    // epochs must be 1, 2, 3, … (strictly monotone from the mint at 1).
    handoffs
        .iter()
        .enumerate()
        .all(|(i, h)| h.epoch == (i as u64) + 1)
}

// =============================================================================
// Factory configuration (the supply-chain item factory).
// =============================================================================

/// The factory VK we publish for the supply-chain item factory.
pub const ITEM_FACTORY_VK: [u8; 32] = *b"starbridge-supplychain-item-fact";

/// Default per-epoch creation budget for the item factory.
pub const DEFAULT_CREATION_BUDGET: u64 = 1_000_000;

/// Build the [`FactoryDescriptor`] for supply-chain ITEM cells.
///
/// A factory-born item is born EMPTY; the `mint_item` turn binds the first
/// `CUSTODIAN`, advances `EPOCH` to 1, and appends the genesis custody link before
/// any handoff. The custody policy (actor-bound register + strict-mono epoch +
/// append-only/write-once chain) is installed at birth FOR LIFE (mirror
/// agent-provenance / swarm-orchestration: born empty, bound by the first turn,
/// frozen).
pub fn item_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: ITEM_FACTORY_VK,
        child_program_vk: Some(item_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(item_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            // The item's custody cap is an attenuatable SelfCell cap — the ocap
            // handle a custodian holds. A handoff narrows it onward to the next
            // custodian (no amplification; the Lean `derive_no_amplify`).
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // Born empty: the `mint_item` turn binds CUSTODIAN + EPOCH + the genesis
        // link from zero under the installed caveats.
        field_constraints: vec![],
        // The life-of-cell custody policy, installed at birth as the born cell's
        // `CellProgram::Predicate` and re-checked by the executor on every touching
        // turn. This is EXACTLY `custody_constraints()` (and `item_program()`'s
        // predicate), so the advertised program VK names the installed predicate
        // byte-for-byte.
        state_constraints: custody_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![item_factory_descriptor()]
}

// =============================================================================
// Turn builders — MINT / HANDOFF / (the forged-handoff adversary).
// =============================================================================

/// **MINT effects** (by-identity) — the multi-effect body of a mint turn binding
/// `first_custodian`'s identity scalar into `CUSTODIAN`, advancing `EPOCH` 0 -> 1
/// (satisfying `StrictMonotonic(EPOCH)`), appending the genesis custody link `link_0`,
/// advancing `HEAD` 0 -> 1, pointing `TIP` at the genesis link, and emitting
/// `item-minted`. The CONCEPTUAL mint (the chain commits the `first_custodian`
/// identity); [`build_mint_action`] signs it. For the EXECUTABLE mint through the real
/// executor, use [`mint_effects_signed`] — the actor-bound `SenderInSlot(CUSTODIAN)`
/// caveat requires the on-cell `CUSTODIAN` to equal the SIGNER's identity (a pubkey),
/// so an executed mint binds the signer, not a name-hash.
pub fn mint_effects(item: CellId, first_custodian: &str) -> Vec<Effect> {
    mint_effects_for(item, identity_field(first_custodian))
}

/// **MINT effects** (signed) — the EXECUTABLE mint: bind the SIGNER's own identity
/// scalar ([`signer_identity`]) into `CUSTODIAN`. The minter (the first custodian)
/// signs the genesis turn and writes its OWN identity into the baton, so the
/// actor-bound `AnyOf[Immutable, SenderInSlot]` caveat ADMITS (`SenderInSlot` holds:
/// sender == the written `CUSTODIAN`) — the inception of the actor-bound register. This
/// is the turn [`fire_mint`] submits; the genesis chain link commits the signer as the
/// first custodian.
pub fn mint_effects_signed(cipherclerk: &AppCipherclerk, item: CellId) -> Vec<Effect> {
    mint_effects_for(item, signer_identity(cipherclerk))
}

/// The shared mint-effects body for a `first` custodian identity scalar (the on-cell
/// `CUSTODIAN` value AND the genesis chain event's incoming custodian).
fn mint_effects_for(item: CellId, first: FieldElement) -> Vec<Effect> {
    let event = custody_event(&GENESIS_PREV, &first, 1);
    let link = link_hash(&GENESIS_PREV, &event);
    vec![
        Effect::SetField {
            cell: item,
            index: CUSTODIAN_SLOT as usize,
            value: first,
        },
        // mint at epoch 1 — the mint turn itself strictly advances 0 -> 1 (so the
        // `StrictMonotonic(EPOCH)` no-replay caveat holds on the very first touch);
        // handoffs then go 1 -> 2 -> 3 -> ….
        Effect::SetField {
            cell: item,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(1),
        },
        // append the genesis custody link.
        Effect::SetField {
            cell: item,
            index: link_slot(0),
            value: link,
        },
        // advance the provenance cursor 0 -> 1.
        Effect::SetField {
            cell: item,
            index: HEAD_SLOT as usize,
            value: field_from_u64(1),
        },
        // point the chain tip at the genesis link.
        Effect::SetField {
            cell: item,
            index: TIP_SLOT as usize,
            value: link,
        },
        Effect::EmitEvent {
            cell: item,
            event: Event::new(symbol("item-minted"), vec![first, link]),
        },
    ]
}

/// **MINT** — the manufacturer mints the item by binding the FIRST custodian into
/// `CUSTODIAN`, advancing `EPOCH` to 1 (so the mint turn itself satisfies
/// `StrictMonotonic(EPOCH)`, 0 -> 1), appending the genesis custody link
/// `link_0 = link_hash(GENESIS_PREV, event(genesis -> first, 1))`, advancing
/// `HEAD` to 1, and pointing `TIP` at the genesis link.
///
/// The mint is the actor-bound register's INCEPTION: the manufacturer (the first
/// custodian) signs the turn, and the written `CUSTODIAN` equals the signer, so
/// `SenderInSlot(CUSTODIAN)` holds (the `Immutable` disjunct's inception path also
/// admits the first write from zero). After the mint there is EXACTLY ONE
/// custodian — the manufacturer. Signs [`mint_effects`].
pub fn build_mint_action(
    cipherclerk: &AppCipherclerk,
    item: CellId,
    first_custodian: &str,
) -> Action {
    cipherclerk.make_action(item, "mint_item", mint_effects(item, first_custodian))
}

/// **HANDOFF** — the incoming custodian accepts custody. It rewrites `CUSTODIAN`
/// to the incoming holder (the actor-bound register: the turn is signed by the
/// incoming holder, so `SenderInSlot(CUSTODIAN)` holds on the new value),
/// strictly advances `EPOCH` (no-replay), appends the custody-receipt link
/// `link_i = link_hash(prev, event(from -> to, new_epoch))`, advances `HEAD`, and
/// points `TIP` at the new link.
///
/// The executor admits this IFF the signer holds the item's custody cap (the
/// cap-graph half — the prior custodian handed it forward), the custodian flip is
/// signed by the incoming holder (the actor-bound caveat), the epoch strictly
/// advances, and the link slot is fresh. After the handoff there is again EXACTLY
/// ONE custodian — the incoming holder.
///
/// `from` is the outgoing custodian's identity (the current register value); `to`
/// is the incoming custodian's identity (the signer); `prev` is the digest
/// committed at link `i-1`; `new_epoch` is the strictly-greater epoch; `i` is the
/// link index (the current `HEAD`).
#[allow(clippy::too_many_arguments)]
pub fn build_handoff_action(
    cipherclerk: &AppCipherclerk,
    item: CellId,
    from: &str,
    to: &str,
    prev: &FieldElement,
    new_epoch: u64,
    i: usize,
) -> Action {
    cipherclerk.make_action(
        item,
        "handoff_custody",
        handoff_effects(item, from, to, prev, new_epoch, i),
    )
}

/// **HANDOFF effects** — the multi-effect body of a handoff turn: advance `CUSTODIAN`
/// to the incoming holder (the actor-bound register), strictly advance `EPOCH`
/// (no-replay), append the custody-receipt link at `link_slot(i)` (`WriteOnce`),
/// advance `HEAD` (append-only), point `TIP` at the new link, and emit
/// `custody-handoff`. The CONCEPTUAL handoff (by-identity, the chain commits the `to`
/// label); [`build_handoff_action`] signs it. The EXECUTABLE handoff the deos
/// `accept_custody` affordance submits is [`accept_custody_effects`] — it binds the
/// SIGNER's identity into `CUSTODIAN` (so the actor-bound `SenderInSlot` admits), and
/// [`fire_accept_custody`] is the cap∧state-gated path that submits it.
#[allow(clippy::too_many_arguments)]
pub fn handoff_effects(
    item: CellId,
    from: &str,
    to: &str,
    prev: &FieldElement,
    new_epoch: u64,
    i: usize,
) -> Vec<Effect> {
    let from_id = identity_field(from);
    let to_id = identity_field(to);
    let event = custody_event(&from_id, &to_id, new_epoch);
    let link = link_hash(prev, &event);
    vec![
        // the custody register advances to the incoming holder (actor-bound).
        Effect::SetField {
            cell: item,
            index: CUSTODIAN_SLOT as usize,
            value: to_id,
        },
        // the provenance epoch strictly advances (no replay).
        Effect::SetField {
            cell: item,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        // append the custody-receipt link.
        Effect::SetField {
            cell: item,
            index: link_slot(i),
            value: link,
        },
        // advance the provenance cursor.
        Effect::SetField {
            cell: item,
            index: HEAD_SLOT as usize,
            value: field_from_u64((i + 1) as u64),
        },
        // point the chain tip at the new link.
        Effect::SetField {
            cell: item,
            index: TIP_SLOT as usize,
            value: link,
        },
        Effect::EmitEvent {
            cell: item,
            event: Event::new(
                symbol("custody-handoff"),
                vec![from_id, to_id, field_from_u64(new_epoch), link],
            ),
        },
    ]
}

/// **FORGED HANDOFF (the adversary)** — a party claims custody it does not hold.
/// This builds the SAME shape as an honest handoff (flipping `CUSTODIAN` to a new
/// holder and advancing the chain) but with the forger as the new holder while the
/// turn is NOT signed by that holder. Two real teeth REFUSE it:
///
///   * the **cap-graph** tooth: if the forger holds no custody cap reaching the
///     item, the executor's authorization gate rejects the turn before any caveat
///     runs (the ocap half of single-custodianship);
///   * the **actor-bound** tooth: if the custodian flips to a party that did NOT
///     sign the turn, `AnyOf[Immutable, SenderInSlot]` rejects (the held register
///     can only move to the signer — the Lean `stolen_baton_rejected`).
///
/// `claimed_to` is the custodian the forger tries to install; `forger_signs` is
/// the (different) identity actually signing — when these differ, the actor-bound
/// caveat bites. The capability gate bites independently whenever the signer holds
/// no custody cap over the item.
pub fn build_forged_handoff_action(
    cipherclerk: &AppCipherclerk,
    item: CellId,
    claimed_from: &str,
    claimed_to: &str,
    prev: &FieldElement,
    new_epoch: u64,
    i: usize,
) -> Action {
    // Identical shape to an honest handoff — only the (missing) authority differs.
    build_handoff_action(
        cipherclerk,
        item,
        claimed_from,
        claimed_to,
        prev,
        new_epoch,
        i,
    )
}

// =============================================================================
// The deos-native surface — the ITEM as a composed `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md` (Tier-1 #1, the reference port): the
// supply-chain ITEM, re-expressed as a composed deos app and PROMOTED into `src/`
// (it lived in `tests/reexpress_deos_app.rs`). The same operations are ONE
// [`DeosApp`] (`item_app` below); the framework wires the rest — per-viewer
// projection, web-of-cells publish (the ITEM cell IS a `dregg://` sturdyref), the
// rehydratable frustum-snapshot, the generated `<dregg-affordance-surface>`
// component, and the manifest — none of which the old bones had.
//
// **The seam is closed** — a TWO-TEMPO fire. The two state-mutating operations
// (`accept_custody`, `mint_item`) are [`GatedAffordance`]s carrying a live-state
// PRECONDITION ([`minted_precondition`] / [`premint_precondition`]); the FULL custody
// program ([`item_program`] = [`custody_constraints`]) is INSTALLED on the seeded item
// cell ([`seed_item`]) and RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_accept_custody`] / [`fire_mint`] then submit the FULL multi-effect
//      handoff/mint turn ([`accept_custody_effects`] / [`mint_effects_signed`]), and the
//      executor RE-ENFORCES the full custody program — so the actor-bound
//      `AnyOf[Immutable, SenderInSlot]` (the baton accepts only the SIGNER), the
//      `StrictMonotonic(epoch)` (a stale/replayed handoff), the `WriteOnce(links)` (a
//      link overwrite), and the `Monotonic(head)` (a rewind) are all REAL executor
//      refusals in the SUBMISSION path — the half the floor's `program.evaluate`-only
//      tests never exercised through a real signed turn (see `tests/deos_seam.rs`).
//
// Both gates are the genuine ones (`is_attenuation` + `CellProgram::evaluate`). The
// executable handoff/mint binds the SIGNER's identity into `CUSTODIAN` (so
// `SenderInSlot` admits — the incoming holder takes the baton for itself).
// `grant_custody` carries the REAL [`Effect::GrantCapability`] (the `derive_no_amplify`
// cap handoff) as a cap-only affordance.

/// The supply-chain rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the
/// roles the floor crate's cap-graph enforces (one custody-cap holder at a time):
///
///   - a VERIFIER (the public / a regulator) holds [`AuthRequired::Signature`] — the
///     narrow read tier: it can `view_provenance` (read + re-derive the custody
///     chain) and nothing else;
///   - a CUSTODIAN (a warehouse / carrier currently holding the item) holds
///     [`AuthRequired::Either`] — it can `accept_custody` (a handoff) AND view;
///   - the MANUFACTURER / OWNER holds [`AuthRequired::None`]/root — it can `mint_item`
///     and `grant_custody` (hand the item's custody cap FORWARD, narrowed) on top of
///     everything a custodian can do.
///
/// So `Signature ⊂ Either ⊂ None` IS the verifier ⊂ custodian ⊂ manufacturer ladder.
pub const VERIFIER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The custodian rights tier (sig-or-proof — accept custody + view). See [`VERIFIER_RIGHTS`].
pub const CUSTODIAN_RIGHTS: AuthRequired = AuthRequired::Either;
/// The manufacturer/owner rights tier (root — mint, grant the custody cap, +all). See [`VERIFIER_RIGHTS`].
pub const MANUFACTURER_RIGHTS: AuthRequired = AuthRequired::None;

/// The permissions an item's custody capability carries (a `SelfCell` cap a
/// custodian holds; handed forward NARROWED, never widened — the Lean
/// `derive_no_amplify`). Matches the factory's `allowed_cap_templates` ceiling.
pub const CUSTODY_CAP_PERMISSIONS: AuthRequired = AuthRequired::Signature;

/// **`grant_custody` effect** — the manufacturer's real cap handoff: an
/// [`Effect::GrantCapability`] of the item's custody cap to the next custodian, at
/// the SAME (`Signature`) permissions — narrowed, never widened (the Lean
/// `derive_no_amplify`). This is the deos affordance's effect-template for
/// `grant_custody`, NOT a scaffold stand-in.
pub fn grant_custody_effect(item: CellId, next_custodian: CellId) -> Effect {
    Effect::GrantCapability {
        from: item,
        to: next_custodian,
        cap: CapabilityRef {
            target: item,
            slot: CUSTODIAN_SLOT as u32,
            permissions: CUSTODY_CAP_PERMISSIONS,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// **The supply-chain ITEM as a composed [`DeosApp`]** — the whole interaction
/// surface, on the deos bones. The item cell is the agent's OWN cell
/// (`cipherclerk.cell_id()`) so fires execute against the seeded embedded ledger.
///
/// Four operations on the ITEM cell, on the verifier ⊂ custodian ⊂ manufacturer
/// rights ladder:
///
///   - `view_provenance` — a cap-only affordance (a VERIFIER reads + re-derives the
///     chain): `Signature`, an `EmitEvent`;
///   - `accept_custody` — a [`GatedAffordance`] (a CUSTODIAN advances the baton):
///     `Either`, a live-state PRECONDITION (the item is minted); the real fire
///     ([`fire_accept_custody`]) submits the FULL handoff, re-enforced by the executor's
///     installed custody program (the actor-bound + strict-mono + write-once + monotonic
///     caveats BITE on the produced transition);
///   - `mint_item` — a [`GatedAffordance`] (the MANUFACTURER inaugurates the sole
///     custodian): `None`/root, a live-state PRECONDITION (the item is NOT yet minted);
///     the real fire ([`fire_mint`]) submits the FULL mint, re-enforced by the executor;
///   - `grant_custody` — a cap-only affordance carrying the REAL
///     [`Effect::GrantCapability`] (the `derive_no_amplify` cap handoff): `None`/root.
///
/// The item cell is published into the web-of-cells at the verifier tier (a regulator
/// on another federation reacquires the item's provenance across the membrane) and is
/// discoverable under `supply-chain` / `provenance`.
///
/// Seed the cell's program + genesis state with [`seed_item`] (or fire `mint_item`) so
/// the gated fires have a live state and the executor re-enforces the caveats.
pub fn item_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let item = cipherclerk.cell_id();
    // The signer's identity scalar — the 32-byte public key the executor reads as a
    // turn's `sender` (`Authorization::Signature(pk, _)`). The `accept_custody` fire
    // writes the FIRING signer's identity into the `CUSTODIAN` baton (see
    // [`accept_custody_effects`]), so the actor-bound `AnyOf[Immutable, SenderInSlot]`
    // caveat admits (`SenderInSlot` holds: the incoming holder takes the baton FOR
    // ITSELF) — and REFUSES any turn that writes a custodian OTHER than the signer (the
    // anti-impersonation baton keystone). The affordance's effect-template carries the
    // APP signer as a surface representative; the actual fire rebinds to the firer.
    let signer = signer_identity(cipherclerk);

    // `accept_custody` — a CUSTODIAN advances the baton to ITSELF (the incoming holder
    // signs and takes custody). The GatedAffordance carries the DECISIVE effect (the
    // `CUSTODIAN` register write) as its surface representative AND a live-state
    // PRECONDITION ([`minted_precondition`]: the item is minted) — so the button is dark
    // before the mint and lit after (the htmx tooth) and the cap∧state gate decides its
    // verdict in-band. The actual fire ([`fire_accept_custody`]) submits the FULL
    // multi-effect handoff ([`accept_custody_effects`]: register + epoch + WriteOnce link
    // + head + tip), which the executor re-enforces the FULL custody program on — so the
    // actor-bound `AnyOf[Immutable, SenderInSlot]` caveat BITES: a flip to a non-signer
    // is REFUSED.
    let accept = GatedAffordance::new(
        CellAffordance::new(
            "accept_custody",
            CUSTODIAN_RIGHTS,
            Effect::SetField {
                cell: item,
                index: CUSTODIAN_SLOT as usize,
                value: signer,
            },
        ),
        minted_precondition(),
    );
    // `mint_item` — the MANUFACTURER inaugurates the sole custodian. The decisive
    // effect advances `EPOCH` 0 -> 1 (the genesis custodian/link/head/tip are the full
    // `mint_effects` turn); gated on the PRE-MINT precondition ([`premint_precondition`]:
    // the item is not yet minted, `EPOCH == 0`). The executor re-enforces the installed
    // custody program (so `StrictMonotonic(EPOCH)` bites — a second mint is refused).
    let mint = GatedAffordance::new(
        CellAffordance::new(
            "mint_item",
            MANUFACTURER_RIGHTS,
            Effect::SetField {
                cell: item,
                index: EPOCH_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        premint_precondition(),
    );
    // `grant_custody` — the manufacturer hands the custody cap forward NARROWED. A
    // real `Effect::GrantCapability`, cap-only (the cap-graph half — no state mutation).
    let grant = CellAffordance::new(
        "grant_custody",
        MANUFACTURER_RIGHTS,
        grant_custody_effect(item, CellId::from_bytes([0xAA; 32])),
    );
    // `view_provenance` — a verifier reads + re-derives. Cap-only.
    let view = CellAffordance::new(
        "view_provenance",
        VERIFIER_RIGHTS,
        Effect::EmitEvent {
            cell: item,
            event: Event::new(symbol("provenance-read"), vec![]),
        },
    );

    DeosApp::builder(
        "supply-chain-provenance",
        cipherclerk.clone(),
        executor.clone(),
    )
    .discoverable(vec!["supply-chain".into(), "provenance".into()])
    .cell(
        DeosCell::new(item, "item")
            .affordance(view)
            .gated(accept)
            .gated(mint)
            .affordance(grant)
            .publish(VERIFIER_RIGHTS),
    )
    .build()
}

/// The signer's **identity scalar** — the 32-byte public key the executor reads as a
/// turn's `sender` (from `Authorization::Signature(pk, _)`). This is what
/// `SenderInSlot(CUSTODIAN)` compares the baton against, so an `accept_custody` fire
/// writes THIS into `CUSTODIAN` and the actor-bound caveat admits the signer's own
/// handoff (the incoming holder IS the signer).
pub fn signer_identity(cipherclerk: &AppCipherclerk) -> FieldElement {
    cipherclerk.public_key().0
}

/// The `accept_custody` **live-state precondition** — the item must be MINTED
/// (`EPOCH >= 1`). A real [`CellProgram`] read against the cell's current state (the
/// `(state, state)` precondition read), so a handoff button is DARK before the mint
/// and LIT after it (the htmx tooth). This gates "may `accept_custody` fire now"; the
/// custody INVARIANT (the actor-bound register etc.) is the installed [`item_program`]
/// the executor re-enforces on the produced transition.
pub fn minted_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: EPOCH_SLOT,
        value: field_from_u64(1),
    }])
}

/// The `mint_item` **live-state precondition** — the item must NOT yet be minted
/// (`EPOCH == 0`). So the `mint_item` button is LIT only on a fresh item and goes DARK
/// the instant it is minted (the htmx tooth). The executor's installed
/// `StrictMonotonic(EPOCH)` is the second guard (a re-mint is a real refusal).
pub fn premint_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: EPOCH_SLOT,
        value: field_from_u64(0),
    }])
}

/// **Seed the ITEM cell** so the gated fires have live state + the caveats bite:
/// install the full custody [`item_program`] on the seeded item cell (so the executor
/// re-enforces it on every touching turn), then mint the genesis state (bind the
/// first custodian, advance `EPOCH` to 1, append the genesis link, advance `HEAD`,
/// point `TIP`) directly into the embedded ledger.
///
/// After seeding, the item is at epoch 1 with `first_custodian` holding the baton — a
/// real `(old, new)` baseline against which `accept_custody` advances. Returns the
/// genesis link digest (the chain tip) so a caller can walk the chain.
pub fn seed_item(executor: &EmbeddedExecutor, first_custodian: &str) -> FieldElement {
    let item = executor.cell_id();
    executor.install_program(item, item_program());
    let first = identity_field(first_custodian);
    let event = custody_event(&GENESIS_PREV, &first, 1);
    let link = link_hash(&GENESIS_PREV, &event);
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&item) {
            cell.state.set_field(CUSTODIAN_SLOT as usize, first);
            cell.state.set_field(EPOCH_SLOT as usize, field_from_u64(1));
            cell.state.set_field(link_slot(0), link);
            cell.state.set_field(HEAD_SLOT as usize, field_from_u64(1));
            cell.state.set_field(TIP_SLOT as usize, link);
        }
    });
    link
}

/// **`accept_custody` effects** — the signer-aware multi-effect handoff body: write
/// `CUSTODIAN := the signer's own identity` (so the actor-bound `SenderInSlot` admits —
/// the incoming holder takes the baton FOR ITSELF), strictly advance `EPOCH`
/// (no-replay), append the custody-receipt link (`WriteOnce`), advance `HEAD`, and
/// point `TIP`. This is the ONE coherent transition the full custody program admits —
/// every clause holds together: `AnyOf[Immutable, SenderInSlot]` (the signer takes the
/// baton), `StrictMonotonic(EPOCH)`, `WriteOnce(link)`, `Monotonic(HEAD)`. The deos
/// `accept_custody` gated affordance is the cap∧state PRECONDITION face; THIS is the
/// turn [`fire_accept_custody`] submits.
pub fn accept_custody_effects(
    cipherclerk: &AppCipherclerk,
    item: CellId,
    from: &FieldElement,
    prev: &FieldElement,
    new_epoch: u64,
    i: usize,
) -> Vec<Effect> {
    let to = signer_identity(cipherclerk); // the incoming holder IS the signer
    let event = custody_event(from, &to, new_epoch);
    let link = link_hash(prev, &event);
    vec![
        Effect::SetField {
            cell: item,
            index: CUSTODIAN_SLOT as usize,
            value: to,
        },
        Effect::SetField {
            cell: item,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        Effect::SetField {
            cell: item,
            index: link_slot(i),
            value: link,
        },
        Effect::SetField {
            cell: item,
            index: HEAD_SLOT as usize,
            value: field_from_u64((i + 1) as u64),
        },
        Effect::SetField {
            cell: item,
            index: TIP_SLOT as usize,
            value: link,
        },
        Effect::EmitEvent {
            cell: item,
            event: Event::new(
                symbol("custody-handoff"),
                vec![*from, to, field_from_u64(new_epoch), link],
            ),
        },
    ]
}

/// **Fire `accept_custody`** — the deos cap∧state PRECONDITION gate (anti-ghost,
/// in-band), then the FULL multi-effect handoff turn the executor re-enforces the
/// custody program on. The two-tempo bridge: the gated affordance decides the button's
/// verdict (cap ⊇ Either AND the item is minted) WITHOUT touching the executor; on both
/// passing, the complete chain-advancing turn ([`accept_custody_effects`]) is submitted,
/// and the executor's re-enforcement of [`item_program`] is the SECOND, verified gate
/// (the actor-bound + strict-mono + write-once + monotonic caveats all bite on the
/// produced transition). Anti-ghost both ways: a precondition miss never submits; a
/// program violation is a real executor refusal.
///
/// The chain is read from the cell's live state (current `EPOCH` ⇒ the next epoch,
/// current `HEAD` ⇒ the next link index, current `TIP` ⇒ the link predecessor), so the
/// caller threads nothing. Use [`seed_item`] first.
pub fn fire_accept_custody(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let item = cell.cell();
    // Tooth 1+2: the deos cap∧state PRECONDITION gate, in-band, nothing submitted on a
    // miss. (The cap-gate AND the live-state precondition the gated affordance carries.)
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "accept_custody")
    {
        // Distinguish the cap miss from the state miss for a precise refusal.
        let ga = cell
            .gated_surface()
            .get("accept_custody")
            .expect("accept_custody is a gated affordance");
        let state = executor.cell_state(item).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "accept_custody".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(item, held, &state, &state).unwrap_err(),
        ));
    }
    // The chain cursor, read from live state.
    let state = executor.cell_state(item).expect("checked above");
    let epoch = field_to_u64(&state.fields[EPOCH_SLOT as usize]);
    let head = field_to_u64(&state.fields[HEAD_SLOT as usize]) as usize;
    let prev = state.fields[TIP_SLOT as usize];
    let from = state.fields[CUSTODIAN_SLOT as usize];
    // Submit the FULL multi-effect handoff turn — the executor re-enforces the program.
    let effects = accept_custody_effects(cipherclerk, item, &from, &prev, epoch + 1, head);
    let action = cipherclerk.make_action(item, "accept_custody", effects);
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// **Fire `mint_item`** — the deos cap∧state PRECONDITION gate (cap ⊇ root AND the item
/// is NOT yet minted), then the FULL multi-effect mint turn ([`mint_effects`]). Like
/// [`fire_accept_custody`], the gated affordance decides the button in-band and the
/// executor's program re-enforcement (`StrictMonotonic(EPOCH)` 0 -> 1) is the verified
/// second gate. Install the program first (the executor re-enforces it); do NOT seed
/// the genesis state (mint is what binds it).
pub fn fire_mint(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let item = cell.cell();
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "mint_item")
    {
        let ga = cell
            .gated_surface()
            .get("mint_item")
            .expect("mint_item is gated");
        let state = executor.cell_state(item).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "mint_item".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(item, held, &state, &state).unwrap_err(),
        ));
    }
    // The EXECUTABLE mint binds the SIGNER's identity into CUSTODIAN (so the actor-bound
    // caveat admits the inception — the minter signs and takes the baton).
    let action = cipherclerk.make_action(item, "mint_item", mint_effects_signed(cipherclerk, item));
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the epoch/head counters the custody chain stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// StarbridgeAppContext mount.
// =============================================================================

/// The canonical web-constants module (slot layout + event topics + factory-vk hex).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("supply-chain-provenance")
        .slot("CUSTODIAN_SLOT", CUSTODIAN_SLOT as u64)
        .slot("EPOCH_SLOT", EPOCH_SLOT as u64)
        .slot("HEAD_SLOT", HEAD_SLOT as u64)
        .slot("TIP_SLOT", TIP_SLOT as u64)
        .slot("LINK_BASE", LINK_BASE as u64)
        .slot("LINK_CAPACITY", LINK_CAPACITY as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&ITEM_FACTORY_VK))
        .topic("MINTED", "item-minted")
        .topic("HANDOFF", "custody-handoff")
}

/// **Register the supply-chain-provenance starbridge-app** on a shared context —
/// the FLOOR (the executor-truth layer: the factory descriptor whose
/// `state_constraints` ARE the custody policy, installed on every born item cell) AND
/// the deos-native composition surface (the [`DeosApp`], folded into the context's
/// affordance registry — so the same `register(ctx)` mounts BOTH).
///
/// The factory + inspector are where SOUNDNESS lives (a forged handoff is a real
/// executor refusal on the born cell). The deos surface is the composition skin:
/// per-viewer projection, the cap∧state gated fires, the `dregg://` publish, the
/// rehydratable snapshot, the generated component, the manifest. [`register_deos`]
/// folds the surface; this returns the factory VK (the floor's identity) as before so
/// the floor's callers are unchanged.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(item_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "supply-chain-item".into(),
        descriptor: serde_json::json!({
            "component": "dregg-supply-chain-item",
            "module": "/starbridge-apps/supply-chain-provenance/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["custodian", "epoch", "head", "tip", "links"],
            "slot_layout": {
                "custodian": CUSTODIAN_SLOT,
                "epoch": EPOCH_SLOT,
                "head": HEAD_SLOT,
                "tip": TIP_SLOT,
                "link_base": LINK_BASE,
                "capacity": LINK_CAPACITY,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&item_child_program_vk()),
            "methods": ["mint_item", "handoff_custody"],
        }),
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context.
    register_deos(ctx);

    factory_vk
}

/// **Mount the deos-native surface** ([`item_app`]) on a shared context: build the
/// composed [`DeosApp`] from the context's cipherclerk + executor, seed the item
/// cell's program + genesis state (so the gated fires bite), and fold the app into the
/// context's affordance registry ([`DeosApp::register`]). Returns the live [`DeosApp`]
/// (so a host can also [`DeosApp::mount`] its axum router / [`DeosApp::publish_all`]
/// into the web-of-cells). This is the PROMOTION the census Tier-1 #1 asks for: the
/// deos surface now ships from `src/`, not from a side-proof in `tests/`.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = item_app(ctx.cipherclerk(), ctx.executor());
    // Seed the item cell so the gated `accept_custody` / `mint_item` fires have a live
    // `(old, new)` and the full custody program (installed here) is re-enforced by the
    // executor on every touching turn.
    seed_item(ctx.executor(), "manufacturer");
    app.register(ctx);
    app
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x5cu8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_item() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    // ── the custody policy is the verified slot-caveat shape ─────────────────

    #[test]
    fn item_program_has_the_custody_clauses() {
        let CellProgram::Predicate(ks) = item_program() else {
            panic!("item program must be a flat Predicate");
        };
        assert_eq!(
            ks,
            custody_constraints(),
            "the program IS custody_constraints"
        );
        // the actor-bound custody register: AnyOf[Immutable, SenderInSlot] on CUSTODIAN.
        assert!(
            ks.iter().any(|k| matches!(
                k,
                StateConstraint::AnyOf { variants }
                    if variants.contains(&SimpleStateConstraint::Immutable { index: CUSTODIAN_SLOT })
                        && variants.contains(&SimpleStateConstraint::SenderInSlot { index: CUSTODIAN_SLOT })
            )),
            "the actor-bound handoff caveat AnyOf[Immutable(CUSTODIAN), SenderInSlot(CUSTODIAN)] must be a clause"
        );
        // no replay + append-only chain.
        assert!(ks.iter().any(
            |k| matches!(k, StateConstraint::StrictMonotonic { index } if *index == EPOCH_SLOT)
        ));
        assert!(
            ks.iter()
                .any(|k| matches!(k, StateConstraint::Monotonic { index } if *index == HEAD_SLOT))
        );
        // every link slot is write-once (tamper-evidence).
        for i in 0..LINK_CAPACITY {
            let idx = link_slot(i) as u8;
            assert!(
                ks.iter()
                    .any(|k| matches!(k, StateConstraint::WriteOnce { index } if *index == idx)),
                "expected WriteOnce on link slot {idx}"
            );
        }
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        assert_eq!(
            item_child_program_vk(),
            canonical_program_vk(&item_program())
        );
        assert_eq!(
            item_factory_descriptor().child_program_vk,
            Some(item_child_program_vk())
        );
    }

    #[test]
    fn descriptor_is_deterministic() {
        assert_eq!(
            item_factory_descriptor().hash(),
            item_factory_descriptor().hash()
        );
    }

    // ── the provenance hash chain + verifier ─────────────────────────────────

    /// Build a connected honest custody history mint(M) -> A -> B -> C.
    fn demo_history() -> Vec<Handoff> {
        let m = identity_field("manufacturer");
        let a = identity_field("warehouse-a");
        let b = identity_field("carrier-b");
        let c = identity_field("retailer-c");
        vec![
            Handoff {
                from: GENESIS_PREV,
                to: m,
                epoch: 1,
            }, // mint
            Handoff {
                from: m,
                to: a,
                epoch: 2,
            },
            Handoff {
                from: a,
                to: b,
                epoch: 3,
            },
            Handoff {
                from: b,
                to: c,
                epoch: 4,
            },
        ]
    }

    #[test]
    fn honest_custody_chain_verifies_and_is_connected() {
        let h = demo_history();
        let committed = custody_chain_digests(&h);
        assert!(
            verify_chain(&h, &committed),
            "the honest custody chain must verify"
        );
        assert!(
            custody_chain_is_connected(&h),
            "the honest custody chain is connected (conserved)"
        );
    }

    #[test]
    fn chain_is_actually_linked() {
        let h = demo_history();
        let d = custody_chain_digests(&h);
        assert_eq!(d[0], link_hash(&GENESIS_PREV, &h[0].event()));
        assert_eq!(d[1], link_hash(&d[0], &h[1].event()));
        // the second link genuinely depends on the first (tamper the first ⇒ second differs).
        let mut tampered = d[0];
        tampered[0] ^= 0xff;
        assert_ne!(link_hash(&tampered, &h[1].event()), d[1]);
    }

    #[test]
    fn tampered_handoff_breaks_verification() {
        let h = demo_history();
        let mut committed = custody_chain_digests(&h);
        committed[2] = custody_event(&identity_field("x"), &identity_field("y"), 99);
        assert!(
            !verify_chain(&h, &committed),
            "a tampered middle link must break verification"
        );
    }

    #[test]
    fn dropped_handoff_breaks_verification() {
        let h = demo_history();
        let mut committed = custody_chain_digests(&h);
        committed.pop();
        assert!(
            !verify_chain(&h, &committed),
            "a dropped tail handoff must break verification"
        );
    }

    #[test]
    fn reordered_handoffs_break_verification() {
        let h = demo_history();
        let mut swapped = h.clone();
        swapped.swap(1, 2);
        let honest = custody_chain_digests(&h);
        assert!(
            !verify_chain(&swapped, &honest),
            "reordered handoffs must break verification"
        );
    }

    // ── single-custodianship as conservation (the connected-chain witness) ───

    #[test]
    fn a_forked_chain_is_not_connected() {
        // A second custodian appears from nowhere: handoff 2's `from` is NOT the
        // prior `to` — custody was not conserved (a fork).
        let m = identity_field("manufacturer");
        let a = identity_field("warehouse-a");
        let rogue = identity_field("rogue");
        let b = identity_field("carrier-b");
        let forked = vec![
            Handoff {
                from: GENESIS_PREV,
                to: m,
                epoch: 1,
            },
            Handoff {
                from: m,
                to: a,
                epoch: 2,
            },
            // rogue hands off as if it held custody — but `a` held it, not rogue.
            Handoff {
                from: rogue,
                to: b,
                epoch: 3,
            },
        ];
        assert!(
            !custody_chain_is_connected(&forked),
            "a chain where a non-holder hands off is not connected — custody is not conserved"
        );
    }

    #[test]
    fn a_replayed_epoch_is_not_connected() {
        // Two handoffs at the same epoch — the no-replay law is violated.
        let m = identity_field("manufacturer");
        let a = identity_field("warehouse-a");
        let b = identity_field("carrier-b");
        let replayed = vec![
            Handoff {
                from: GENESIS_PREV,
                to: m,
                epoch: 1,
            },
            Handoff {
                from: m,
                to: a,
                epoch: 2,
            },
            Handoff {
                from: a,
                to: b,
                epoch: 2,
            }, // replayed epoch
        ];
        assert!(
            !custody_chain_is_connected(&replayed),
            "a replayed epoch breaks the strictly-monotone provenance — not conserved"
        );
    }

    // ── the turn builders carry real effects + a real signature ──────────────

    #[test]
    fn mint_action_pins_custodian_epoch_and_genesis_link() {
        let cclerk = test_cipherclerk();
        let action = build_mint_action(&cclerk, test_item(), "manufacturer");
        // custodian, epoch(=1), link_0, head(=1), tip, + event.
        assert_eq!(action.effects.len(), 6);
        let first = identity_field("manufacturer");
        let event = custody_event(&GENESIS_PREV, &first, 1);
        let link = link_hash(&GENESIS_PREV, &event);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. } if *index == CUSTODIAN_SLOT as usize && *value == first
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. } if *index == EPOCH_SLOT as usize && *value == field_from_u64(1)
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, value, .. } if *index == link_slot(0) && *value == link
        ));
    }

    #[test]
    fn handoff_action_advances_register_epoch_and_link() {
        let cclerk = test_cipherclerk();
        let action = build_handoff_action(
            &cclerk,
            test_item(),
            "manufacturer",
            "warehouse-a",
            &GENESIS_PREV,
            2,
            1,
        );
        assert_eq!(action.effects.len(), 6);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. } if *index == CUSTODIAN_SLOT as usize && *value == identity_field("warehouse-a")
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. } if *index == EPOCH_SLOT as usize && *value == field_from_u64(2)
        ));
    }

    #[test]
    fn handoff_action_carries_a_real_signature() {
        let cclerk = test_cipherclerk();
        let action = build_handoff_action(&cclerk, test_item(), "a", "b", &GENESIS_PREV, 2, 1);
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    // ── slot-caveat evaluation (executor-side regression) ─────────────────────

    fn empty() -> dregg_cell::state::CellState {
        dregg_cell::state::CellState::new(0)
    }

    #[test]
    fn link_overwrite_is_write_once_violation() {
        // A committed custody link; a turn tries to overwrite it → WriteOnce rejects.
        // (The turn otherwise advances the epoch like a real handoff, so the
        // earlier no-replay caveat is satisfied and the WriteOnce tooth is the one
        // that bites — isolating the constraint under test.)
        let program = item_program();
        let mut old = empty();
        old.fields[link_slot(0)] = link_hash(
            &GENESIS_PREV,
            &custody_event(&GENESIS_PREV, &identity_field("m"), 1),
        );
        old.fields[HEAD_SLOT as usize] = field_from_u64(1);
        old.fields[EPOCH_SLOT as usize] = field_from_u64(1);
        old.set_nonce(1);
        let mut new = old.clone();
        new.fields[EPOCH_SLOT as usize] = field_from_u64(2); // a real handoff advances the epoch
        new.fields[link_slot(0)] = identity_field("forged-rewrite");
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("overwriting a committed custody link must be rejected");
        assert!(
            matches!(err, dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index }, ..
            } if index == link_slot(0) as u8),
            "expected WriteOnce violation on the link slot, got {err:?}"
        );
    }

    #[test]
    fn epoch_replay_is_strict_monotonic_violation() {
        // EPOCH at 2; a replayed handoff writes 2 again → StrictMonotonic rejects.
        let program = item_program();
        let mut old = empty();
        old.fields[EPOCH_SLOT as usize] = field_from_u64(2);
        old.set_nonce(2);
        let mut new = old.clone();
        new.fields[EPOCH_SLOT as usize] = field_from_u64(2); // not strictly greater
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("a replayed (non-advancing) epoch must be rejected");
        assert!(
            matches!(err, dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::StrictMonotonic { index }, ..
            } if index == EPOCH_SLOT),
            "expected StrictMonotonic violation on EPOCH, got {err:?}"
        );
    }

    #[test]
    fn head_rewind_is_monotonic_violation() {
        // A real handoff advances the epoch; here it also REWINDS the provenance
        // cursor → Monotonic(HEAD) rejects. (The turn advances the epoch like a
        // real handoff, so the earlier StrictMonotonic(EPOCH) no-replay caveat —
        // checked first — is satisfied and the Monotonic(HEAD) tooth is the one
        // that bites, isolating the constraint under test.)
        let program = item_program();
        let mut old = empty();
        old.fields[HEAD_SLOT as usize] = field_from_u64(3);
        old.fields[EPOCH_SLOT as usize] = field_from_u64(1);
        old.set_nonce(3);
        let mut new = old.clone();
        new.fields[EPOCH_SLOT as usize] = field_from_u64(2); // a real handoff advances the epoch
        new.fields[HEAD_SLOT as usize] = field_from_u64(2); // rewind
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("rewinding the provenance cursor must be rejected");
        assert!(
            matches!(err, dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::Monotonic { index }, ..
            } if index == HEAD_SLOT),
            "expected Monotonic violation on HEAD, got {err:?}"
        );
    }

    #[test]
    fn register_installs_factory_and_inspector() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, ITEM_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("supply-chain-item").is_some());
    }
}
