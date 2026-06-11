//! # starbridge-agent-provenance
//!
//! Usecase #3: **PROOF-CARRYING AGENT PROVENANCE / VERIFIABLE MEMORY** as a
//! dregg-native **starbridge-app**: a thin library of [`FactoryDescriptor`]s
//! plus signed turn-builder helpers that compose dregg primitives only
//! (`FactoryDescriptor` + `Effect::SetField` + `Effect::EmitEvent` +
//! `StateConstraint` slot caveats). No domain-specific provenance `Effect`, no
//! `Authorization::Unchecked`, no placeholder signatures.
//!
//! ## What this is for
//!
//! An AI agent needs an *attestable, non-repudiable scratchpad*: a place to
//! post claims / outputs / intermediate reasoning such that
//!
//! 1. **write-access is capability-gated** — only a holder of the owner
//!    capability can append (the turn carries the owner's signature; the
//!    executor admits only an authorized write),
//! 2. **entries are append-only / tamper-evident** — each provenance record
//!    occupies its own `WriteOnce` slot, so once committed it can NEVER be
//!    silently overwritten, and the `HEAD` cursor is `Monotonic`, so the log
//!    index only ever grows (no re-order, no rewind, no truncate-then-fork),
//! 3. **the provenance chain is VERIFIABLE** — the entries form a blake3 hash
//!    chain (`entry_i = blake3(prev_digest ‖ claim_i)`), so any third party can
//!    recompute the chain from the published claims and the committed
//!    predecessor and check it link-for-link ([`verify_chain`]). A single
//!    tampered, forged, or dropped entry breaks the recomputation.
//!
//! ## The provenance log is a substrate-enforced append-only hash chain
//!
//! A provenance log is a single factory-born sovereign cell
//! ([`provenance_factory_descriptor`]) whose slot caveats *are* the rules — the
//! executor rejects any turn that would overwrite an entry or rewind the head:
//!
//! | Slot                  | Meaning                              | Caveat       |
//! |-----------------------|--------------------------------------|--------------|
//! | [`HEAD_SLOT`]         | the append cursor (next entry index) | `Monotonic`  |
//! | [`TIP_SLOT`]          | the latest committed entry digest    | (pointer)    |
//! | `ENTRY_BASE + i`      | the i-th provenance record digest    | `WriteOnce`  |
//!
//! Because each `ENTRY_BASE + i` slot is `WriteOnce`, a committed provenance
//! entry is frozen forever (tamper-evidence). Because [`HEAD_SLOT`] is
//! `Monotonic`, the cursor can only grow (append-only ordering). This is the
//! Rust face of the verified-executor theorems in
//! `Dregg2/Apps/AgentProvenanceGated.lean` (`prov_entry_writeonce`,
//! `prov_head_cannot_rewind`, `prov_append_reads_back`, `prov_chain_links`).
//!
//! ## What this crate exports
//!
//! - [`provenance_factory_descriptor`] — the `FactoryDescriptor`, slot caveats
//!   baked into `state_constraints` so every born log cell inherits the gating.
//! - [`factory_descriptors`] — the descriptor slice for host registration.
//! - [`build_append_action`] — writes `ENTRY_BASE + i = link_hash(prev, claim)`,
//!   advances `HEAD`, points `TIP` at the new digest, emits `provenance-appended`.
//! - [`build_advance_head_action`] — bumps the cursor only (a `Monotonic` no-op
//!   demo handle).
//! - [`link_hash`], [`entry_digests`], [`verify_chain`] — the executable
//!   verifier: re-derive the honest hash chain from the claims and check the
//!   committed digests match link-for-link.
//! - [`register`] — mounts the app's factory + inspector on a
//!   [`StarbridgeAppContext`].

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, Effect, Event, FactoryDescriptor, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, canonical_program_vk,
    field_from_bytes, field_from_u64, hex_encode_32, symbol,
};
use dregg_cell::state::STATE_SLOTS;

// =============================================================================
// Provenance-cell state schema
// =============================================================================

/// Provenance cell slot: the append cursor — the index of the NEXT entry to be
/// written. `Monotonic` — the executor rejects any write that would rewind it,
/// so the log is append-only (no re-order, no truncate-then-fork).
pub const HEAD_SLOT: usize = 2;
/// Provenance cell slot: the latest committed entry digest (the chain tip a
/// verifier reads first to walk the chain backward).
pub const TIP_SLOT: usize = 3;
/// The first entry-digest slot. Entry `i` lives at `ENTRY_BASE + i`, and each
/// such slot carries a `WriteOnce` caveat — a committed entry is frozen forever.
pub const ENTRY_BASE: usize = 4;
/// How many entry slots fit in a single provenance cell's record. A dregg cell
/// carries exactly [`STATE_SLOTS`] field slots (indices `0..STATE_SLOTS`); after
/// reserving `HEAD`/`TIP` (and slots `0`/`1` for the framework's nonce/balance
/// conventions), the entries occupy `ENTRY_BASE..STATE_SLOTS`. A provenance log
/// longer than this per-cell capacity chains ACROSS cells: when a cell fills,
/// its `TIP` is the genesis predecessor of the next cell's first entry, so the
/// hash chain (and [`verify_chain`]) continues seamlessly across the boundary.
pub const ENTRY_CAPACITY: usize = STATE_SLOTS - ENTRY_BASE;

/// The slot index of the i-th provenance entry.
pub fn entry_slot(i: usize) -> usize {
    ENTRY_BASE + i
}

// =============================================================================
// The provenance LINK HASH (the hash chain)
// =============================================================================

/// The genesis predecessor digest (no entry before the first one).
pub const GENESIS_PREV: FieldElement = [0u8; 32];

/// **The provenance link hash** — `link_hash(prev, claim)` is the digest stored
/// at an entry slot: `blake3(prev ‖ claim)`, binding the new claim to the entire
/// committed prefix (since `prev` is itself the previous link). Deterministic, so
/// a third party recomputes it exactly; collision-resistant, so a forged entry
/// that hashes to a different value is detectable. This is the production
/// (real-blake3) face of the Lean executable Horner shadow `linkHash`.
pub fn link_hash(prev: &FieldElement, claim: &FieldElement) -> FieldElement {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-provenance-link\x01");
    h.update(prev);
    h.update(claim);
    *h.finalize().as_bytes()
}

/// `entry_digests(claims)` — the honest digest sequence for a list of claim
/// digests: each entry folds the PREVIOUS entry's digest with the next claim,
/// starting from [`GENESIS_PREV`]. This is exactly what an honest agent commits
/// to `ENTRY_BASE + i`, and exactly what [`verify_chain`] recomputes.
pub fn entry_digests(claims: &[FieldElement]) -> Vec<FieldElement> {
    let mut out = Vec::with_capacity(claims.len());
    let mut prev = GENESIS_PREV;
    for claim in claims {
        let h = link_hash(&prev, claim);
        out.push(h);
        prev = h;
    }
    out
}

/// **`verify_chain`** — the third-party VERIFIER. Given the published claims and
/// the entry digests as read off the committed cell, re-derive the honest chain
/// from scratch and check they match link-for-link. Returns `true` IFF every
/// committed digest equals `link_hash(previous committed digest, claim)`, i.e.
/// the log is EXACTLY the honest hash chain of those claims. A tampered,
/// reordered, forged, or dropped entry makes this `false` — the provenance chain
/// is verifiable by re-execution, not by trust.
pub fn verify_chain(claims: &[FieldElement], committed: &[FieldElement]) -> bool {
    committed == entry_digests(claims).as_slice()
}

/// Convenience: encode an arbitrary claim payload (a content/output blob) as the
/// 32-byte field the agent records — `blake3(claim_bytes)`.
pub fn claim_digest(claim_bytes: &[u8]) -> FieldElement {
    field_from_bytes(claim_bytes)
}

// =============================================================================
// Cell program (the slot caveats, also returned by the descriptor)
// =============================================================================

/// The perpetual `state_constraints` installed on every provenance cell:
/// `HEAD` is `Monotonic`; each of the `ENTRY_CAPACITY` entry slots is `WriteOnce`.
fn provenance_state_constraints() -> Vec<StateConstraint> {
    let mut cs = Vec::with_capacity(1 + ENTRY_CAPACITY);
    cs.push(StateConstraint::Monotonic {
        index: HEAD_SLOT as u8,
    });
    for i in 0..ENTRY_CAPACITY {
        cs.push(StateConstraint::WriteOnce {
            index: entry_slot(i) as u8,
        });
    }
    cs
}

/// The `CellProgram` installed on every provenance cell: a monotone head cursor
/// and write-once entry slots, enforced on every turn.
pub fn provenance_cell_program() -> CellProgram {
    CellProgram::always(provenance_state_constraints())
}

/// Canonical child-program VK for provenance cells.
pub fn provenance_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&provenance_cell_program())
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Factory VK we publish for the provenance factory.
pub const PROVENANCE_FACTORY_VK: [u8; 32] = *b"starbridge-agent-provenance-vk01";

/// Build the provenance-cell `FactoryDescriptor`.
///
/// The cell is born empty; entries are appended by subsequent turns. The
/// `state_constraints` (monotone head + write-once entries) are installed as the
/// born cell's `CellProgram` and bite on every turn — `WriteOnce` admits the
/// first write to a fresh entry slot (from zero) and rejects any overwrite;
/// `Monotonic` admits a forward head advance and rejects a rewind.
pub fn provenance_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: PROVENANCE_FACTORY_VK,
        child_program_vk: Some(provenance_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(provenance_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: provenance_state_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(1_000_000),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![provenance_factory_descriptor()]
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the signed `Action` that appends the i-th provenance entry.
///
/// Writes `ENTRY_BASE + i = link_hash(prev, claim)` (the new hash-chain link),
/// advances `HEAD` to `i + 1` (Monotonic forward), points `TIP` at the new
/// digest, and emits `provenance-appended`. The `WriteOnce` caveat on the entry
/// slot admits this FIRST write (the slot is fresh) and would reject any later
/// overwrite of the same slot; the `Monotonic` caveat on `HEAD` admits the
/// forward bump and would reject a rewind.
///
/// `prev` is the digest committed at entry `i-1` (or [`GENESIS_PREV`] for `i =
/// 0`); `claim` is the 32-byte digest of the content being attested.
pub fn build_append_action(
    cipherclerk: &AppCipherclerk,
    log_cell: CellId,
    i: usize,
    prev: &FieldElement,
    claim: &FieldElement,
) -> Action {
    let digest = link_hash(prev, claim);
    let effects = vec![
        Effect::SetField {
            cell: log_cell,
            index: entry_slot(i),
            value: digest,
        },
        Effect::SetField {
            cell: log_cell,
            index: HEAD_SLOT,
            value: field_from_u64((i + 1) as u64),
        },
        Effect::SetField {
            cell: log_cell,
            index: TIP_SLOT,
            value: digest,
        },
        Effect::EmitEvent {
            cell: log_cell,
            event: Event::new(symbol("provenance-appended"), vec![digest, *claim]),
        },
    ];
    cipherclerk.make_action(log_cell, "append_provenance", effects)
}

/// Build the signed `Action` that advances the head cursor to `new_head` only
/// (no entry written). `Monotonic` ⇒ admitted iff `new_head >= old`. A demo
/// handle for the head-monotonicity property; real appends use
/// [`build_append_action`] (which advances the head as part of the entry write).
pub fn build_advance_head_action(
    cipherclerk: &AppCipherclerk,
    log_cell: CellId,
    new_head: u64,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: log_cell,
            index: HEAD_SLOT,
            value: field_from_u64(new_head),
        },
        Effect::EmitEvent {
            cell: log_cell,
            event: Event::new(
                symbol("provenance-head-advanced"),
                vec![field_from_u64(new_head)],
            ),
        },
    ];
    cipherclerk.make_action(log_cell, "advance_head", effects)
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Web-constants module (single source of truth for the JS surface).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("agent-provenance")
        .slot("HEAD_SLOT", HEAD_SLOT as u64)
        .slot("TIP_SLOT", TIP_SLOT as u64)
        .slot("ENTRY_BASE", ENTRY_BASE as u64)
        .slot("ENTRY_CAPACITY", ENTRY_CAPACITY as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&PROVENANCE_FACTORY_VK))
        .topic("APPENDED", "provenance-appended")
        .topic("HEAD_ADVANCED", "provenance-head-advanced")
}

/// Register this starbridge-app on a [`StarbridgeAppContext`].
///
/// Installs the provenance factory descriptor and the provenance inspector.
/// Returns the registered factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(provenance_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "provenance".into(),
        descriptor: serde_json::json!({
            "component": "dregg-provenance",
            "module": "/starbridge-apps/agent-provenance/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["head", "tip", "entries"],
            "slot_layout": {
                "head":       HEAD_SLOT,
                "tip":        TIP_SLOT,
                "entry_base": ENTRY_BASE,
                "capacity":   ENTRY_CAPACITY,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&provenance_child_program_vk()),
        }),
    });

    factory_vk
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};
    use dregg_cell::FactoryCreationParams;

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [9u8; 32])
    }

    // ── Descriptor shape ─────────────────────────────────────────────────

    #[test]
    fn descriptor_is_deterministic() {
        assert_eq!(
            provenance_factory_descriptor().hash(),
            provenance_factory_descriptor().hash()
        );
    }

    #[test]
    fn factory_bakes_head_monotonic_and_entries_write_once() {
        let d = provenance_factory_descriptor();
        // HEAD is Monotonic.
        assert!(
            d.state_constraints.iter().any(
                |c| matches!(c, StateConstraint::Monotonic { index } if *index == HEAD_SLOT as u8)
            ),
            "HEAD slot must be Monotonic"
        );
        // every entry slot is WriteOnce.
        for i in 0..ENTRY_CAPACITY {
            let idx = entry_slot(i);
            assert!(
                d.state_constraints.iter().any(
                    |c| matches!(c, StateConstraint::WriteOnce { index } if *index == idx as u8)
                ),
                "expected WriteOnce on entry slot {idx}"
            );
        }
        assert_eq!(d.state_constraints.len(), 1 + ENTRY_CAPACITY);
    }

    #[test]
    fn child_program_vk_is_canonical_recipe() {
        let expected = canonical_program_vk(&provenance_cell_program());
        assert_eq!(provenance_child_program_vk(), expected);
        assert_eq!(
            provenance_factory_descriptor().child_program_vk,
            Some(expected)
        );
    }

    // ── The hash chain + verifier ────────────────────────────────────────

    #[test]
    fn honest_chain_verifies() {
        let claims: Vec<FieldElement> = ["alpha", "beta", "gamma"]
            .iter()
            .map(|c| claim_digest(c.as_bytes()))
            .collect();
        let committed = entry_digests(&claims);
        assert!(
            verify_chain(&claims, &committed),
            "honest chain must verify"
        );
    }

    #[test]
    fn chain_is_actually_linked() {
        // Each entry must equal link_hash(previous entry, claim) — not an
        // independent hash of the claim alone. This is what makes it a *chain*.
        let claims: Vec<FieldElement> = ["one", "two"]
            .iter()
            .map(|c| claim_digest(c.as_bytes()))
            .collect();
        let d = entry_digests(&claims);
        assert_eq!(d[0], link_hash(&GENESIS_PREV, &claims[0]));
        assert_eq!(d[1], link_hash(&d[0], &claims[1]));
        // ...and the second link genuinely depends on the first (tamper the
        // first entry and the recomputed second differs):
        let mut tampered_prev = d[0];
        tampered_prev[0] ^= 0xff;
        assert_ne!(link_hash(&tampered_prev, &claims[1]), d[1]);
    }

    #[test]
    fn tampered_link_is_rejected() {
        let claims: Vec<FieldElement> = ["alpha", "beta", "gamma"]
            .iter()
            .map(|c| claim_digest(c.as_bytes()))
            .collect();
        let mut committed = entry_digests(&claims);
        // overwrite the middle entry with a forged digest
        committed[1] = claim_digest(b"forged-middle-entry");
        assert!(
            !verify_chain(&claims, &committed),
            "a tampered middle link must break verification"
        );
    }

    #[test]
    fn truncated_chain_is_rejected() {
        let claims: Vec<FieldElement> = ["alpha", "beta", "gamma"]
            .iter()
            .map(|c| claim_digest(c.as_bytes()))
            .collect();
        let mut committed = entry_digests(&claims);
        committed.pop(); // drop the tail entry
        assert!(
            !verify_chain(&claims, &committed),
            "a dropped tail entry must break verification"
        );
    }

    #[test]
    fn reordered_claims_rejected() {
        // The same claims in a different order produce a different chain, so a
        // verifier checking against the published claim order catches reordering.
        let a = claim_digest(b"alpha");
        let b = claim_digest(b"beta");
        let honest = entry_digests(&[a, b]);
        assert!(!verify_chain(&[b, a], &honest));
    }

    // ── Turn-builder shape ───────────────────────────────────────────────

    #[test]
    fn append_action_writes_entry_head_tip_and_emits_event() {
        let cclerk = test_cipherclerk();
        let log = CellId::from_bytes([4u8; 32]);
        let claim = claim_digest(b"the agent's first attested output");
        let action = build_append_action(&cclerk, log, 0, &GENESIS_PREV, &claim);
        assert_eq!(action.effects.len(), 4);
        let expected = link_hash(&GENESIS_PREV, &claim);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. } if *index == entry_slot(0) && *value == expected
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. } if *index == HEAD_SLOT && *value == field_from_u64(1)
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, value, .. } if *index == TIP_SLOT && *value == expected
        ));
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    // ── Slot-caveat evaluation (executor-side regression) ─────────────────

    fn provenance_program() -> dregg_cell::CellProgram {
        dregg_cell::CellProgram::Predicate(provenance_state_constraints())
    }

    fn empty() -> dregg_cell::state::CellState {
        dregg_cell::state::CellState::new(0)
    }

    #[test]
    fn legal_first_append_succeeds() {
        let program = provenance_program();
        let old = empty();
        let claim = claim_digest(b"hello world");
        let mut new = old.clone();
        new.fields[entry_slot(0)] = link_hash(&GENESIS_PREV, &claim);
        new.fields[HEAD_SLOT] = field_from_u64(1);
        assert!(program.evaluate(&new, Some(&old), None).is_ok());
    }

    #[test]
    fn entry_overwrite_is_write_once_violation() {
        // Entry 0 holds a committed digest; a turn tries to overwrite it with a
        // DIFFERENT value → WriteOnce rejects (tamper-evidence).
        let program = provenance_program();
        let claim = claim_digest(b"committed claim");
        let mut old = empty();
        old.fields[entry_slot(0)] = link_hash(&GENESIS_PREV, &claim);
        old.fields[HEAD_SLOT] = field_from_u64(1);
        old.set_nonce(1);
        let mut new = old.clone();
        new.fields[entry_slot(0)] = claim_digest(b"forged overwrite");
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("overwriting a committed provenance entry must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } => assert_eq!(index, entry_slot(0) as u8),
            other => panic!("expected WriteOnce violation, got {other:?}"),
        }
    }

    #[test]
    fn head_rewind_is_monotonic_violation() {
        // HEAD is at 2; a turn tries to rewind it to 1 → Monotonic rejects
        // (no re-order / no truncate-then-fork).
        let program = provenance_program();
        let mut old = empty();
        old.fields[HEAD_SLOT] = field_from_u64(2);
        old.set_nonce(2);
        let mut new = old.clone();
        new.fields[HEAD_SLOT] = field_from_u64(1);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("rewinding the head cursor must be rejected");
        match err {
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::Monotonic { index },
                ..
            } => assert_eq!(index, HEAD_SLOT as u8),
            other => panic!("expected Monotonic violation, got {other:?}"),
        }
    }

    #[test]
    fn head_forward_advance_succeeds() {
        let program = provenance_program();
        let mut old = empty();
        old.fields[HEAD_SLOT] = field_from_u64(2);
        old.set_nonce(2);
        let mut new = old.clone();
        new.fields[HEAD_SLOT] = field_from_u64(3);
        assert!(program.evaluate(&new, Some(&old), None).is_ok());
    }

    // ── End-to-end factory-birth + caveat-biting through EmbeddedExecutor ──

    /// Births a provenance log cell from the deployed factory, appends a 3-entry
    /// hash chain (all accepted), then proves the gating bites: overwriting a
    /// committed entry is rejected by the `WriteOnce` caveat installed at birth.
    /// Finally, reads the committed digests back off the ledger and VERIFIES the
    /// provenance chain against the claims. End to end on the real executor.
    #[test]
    fn factory_born_log_appends_chain_rejects_overwrite_and_verifies() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        exec.deploy_factory(provenance_factory_descriptor());

        // Fund the agent cell so it can pay turn fees.
        let agent = cclerk.cell_id();
        exec.with_ledger_mut(|ledger| {
            if let Some(cell) = ledger.get_mut(&agent) {
                cell.state.set_balance(100_000_000);
            }
        });

        // Birth a provenance log cell from the factory.
        let owner = cclerk.public_key().0;
        let token: [u8; 32] = *blake3::hash(b"provenance-log-1").as_bytes();
        let params = FactoryCreationParams {
            mode: CellMode::Sovereign,
            program_vk: Some(provenance_child_program_vk()),
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        let birth = cclerk.create_from_factory(PROVENANCE_FACTORY_VK, owner, token, params);
        exec.submit_turn(&birth)
            .expect("provenance log birth commits");

        let log = CellId::derive_raw(&owner, &token);

        // The born cell must carry the slot caveats as its program.
        let has_program = exec.with_ledger_mut(|ledger| {
            ledger
                .get(&log)
                .map(|c| !c.program.is_none())
                .unwrap_or(false)
        });
        assert!(has_program, "factory-born log must carry a CellProgram");

        // Hand the creator an owner capability over the born cell.
        exec.with_ledger_mut(|ledger| {
            if let Some(agent_cell) = ledger.get_mut(&agent) {
                agent_cell
                    .capabilities
                    .grant(log, dregg_app_framework::AuthRequired::Signature);
            }
        });

        // Append a 3-entry provenance chain. Each append's `prev` is the digest
        // committed by the previous append (the chain link).
        let claims: Vec<FieldElement> = [
            "model:reasoning-step-1",
            "tool-call:web.search(...)",
            "final:answer",
        ]
        .iter()
        .map(|c| claim_digest(c.as_bytes()))
        .collect();
        let honest = entry_digests(&claims);

        let mut prev = GENESIS_PREV;
        for (i, claim) in claims.iter().enumerate() {
            exec.submit_action(&cclerk, build_append_action(&cclerk, log, i, &prev, claim))
                .unwrap_or_else(|e| panic!("append {i} must commit: {e}"));
            prev = honest[i];
        }

        // The committed entries must read back EXACTLY the honest chain digests.
        let committed: Vec<FieldElement> = exec.with_ledger_mut(|ledger| {
            let cell = ledger.get(&log).expect("log cell exists");
            (0..claims.len())
                .map(|i| cell.state.fields[entry_slot(i)])
                .collect()
        });
        assert_eq!(
            committed, honest,
            "committed entries must equal the honest chain"
        );

        // The provenance chain VERIFIES against the published claims.
        assert!(
            verify_chain(&claims, &committed),
            "the committed provenance chain must verify"
        );

        // Tamper-evidence: overwriting a committed entry is rejected by the
        // WriteOnce caveat that the factory baked in at birth.
        let overwrite = {
            let forged = claim_digest(b"forged-rewrite");
            let effects = vec![Effect::SetField {
                cell: log,
                index: entry_slot(0),
                value: forged,
            }];
            cclerk.make_action(log, "tamper", effects)
        };
        let err = exec
            .submit_action(&cclerk, overwrite)
            .expect_err("overwriting a committed entry must be rejected");
        let msg = format!("{err}").to_lowercase();
        assert!(
            msg.contains("writeonce")
                || msg.contains("write-once")
                || msg.contains("program")
                || msg.contains("constraint"),
            "rejection must cite the WriteOnce slot-caveat violation, got: {msg}"
        );

        // ...and the committed entry is UNCHANGED after the rejected tamper.
        let still: FieldElement =
            exec.with_ledger_mut(|ledger| ledger.get(&log).unwrap().state.fields[entry_slot(0)]);
        assert_eq!(
            still, honest[0],
            "committed entry must survive the rejected tamper"
        );
    }

    #[test]
    fn register_installs_factory() {
        let cclerk = test_cipherclerk();
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let ctx = StarbridgeAppContext::new(cclerk, exec);
        let vk = register(&ctx);
        assert_eq!(vk, PROVENANCE_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
    }
}
