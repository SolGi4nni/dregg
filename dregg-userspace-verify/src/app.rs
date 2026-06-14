//! App-level static checks — the first *application* customers of the static
//! pre-submission toolkit.
//!
//! The four core checks in [`crate`] (conservation, non-amplification,
//! well-formedness, ring-balance) are *protocol-shaped*: they read a
//! [`CallForest`] knowing only the universal `Effect` grammar. But the apps
//! built on dregg are state-machine cells whose meaning lives one level up — in
//! *which slot means what*. The escrow market's conservation is
//! `RELEASED + REFUNDED == ESCROWED` over three specific slots; the provenance
//! log's integrity is a blake3 hash chain over the `ENTRY_BASE + i` slots; the
//! bounty board's safety is a strictly-monotone lifecycle on the `STATE` slot.
//!
//! Those properties are *the executor's own slot-caveat invariants*, restated
//! as static, artifact-only predicates so an app builder can catch a malformed
//! turn before paying gas — exactly as the four core checks do, but in the
//! app's vocabulary. Each app supplies a tiny [`SlotSchema`] (which slots carry
//! which meaning) and the check projects the forest's `SetField` writes through
//! it.
//!
//! These mirror, slot-for-slot, the *real* shipped apps:
//!
//!   * [`check_escrow_conservation`] ← `starbridge-apps/escrow-market`
//!     (`build_settle_action` + the `settle`-scoped `AffineEq
//!     { RELEASED + REFUNDED − ESCROWED = 0 }`). The FLASHWELL organ, statically.
//!   * [`verify_provenance_chain`] / [`check_provenance_chain_in_forest`] ←
//!     `starbridge-apps/agent-provenance` (`verify_chain`, `entry_digests`,
//!     `link_hash` — the blake3 hash chain `entry_i = blake3(prev ‖ claim_i)`).
//!   * [`check_bounty_lifecycle`] ← `starbridge-apps/bounty-board`
//!     (the `StrictMonotonic(STATE)` caveat: `OPEN→CLAIMED→SUBMITTED→PAID`,
//!     no rewind, no re-entry).
//!
//! ## The boundary (same honesty as the core checks)
//!
//! A forest is a *plan*: it carries the `SetField` writes the turn intends. The
//! app check decodes those writes and asserts the app invariant over them. What
//! it does NOT see is the *live cell's current state* — e.g. whether the
//! `ESCROWED` slot was already written by a prior turn (so this forest's
//! `released + refunded` must match *that* committed escrow, not one this forest
//! sets). When the forest itself writes every slot the invariant relates (the
//! common single-turn `settle`, or a full post→claim→submit→payout test
//! forest), the check is exact. When the invariant spans turns, pass the
//! prior-committed values explicitly (the `*_with_prior` entry points) — the
//! check then closes over the whole relation. With neither, the check reports
//! what it can decide and names the slot it could not resolve, never silently
//! passing an unknowable.

use std::collections::BTreeMap;

use dregg_turn::action::Effect;
use dregg_turn::{CallForest, CallTree};
use dregg_types::CellId;

use crate::{Finding, Locus, Verdict, walk};

/// Decode a 32-byte [`dregg_cell::state::FieldElement`] written by
/// `field_from_u64` (big-endian u64 in the trailing 8 bytes, leading 24 bytes
/// zero) back to its `u64`. Returns `None` if any leading byte is nonzero — that
/// field is a hash / identity digest, not a small integer, so reading it as an
/// amount would be a category error.
pub fn decode_u64_field(f: &[u8; 32]) -> Option<u64> {
    if f[..24].iter().any(|&b| b != 0) {
        return None;
    }
    let mut le = [0u8; 8];
    le.copy_from_slice(&f[24..32]);
    Some(u64::from_be_bytes(le))
}

// ─── escrow conservation (FLASHWELL, statically) ────────────────────────────

/// The three value slots the escrow conservation invariant relates, for a given
/// escrow cell. Defaults match `starbridge-apps/escrow-market`
/// (`ESCROWED_SLOT = 5`, `RELEASED_SLOT = 7`, `REFUNDED_SLOT = 8`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct EscrowSchema {
    /// The escrow cell the slots live on.
    pub cell: CellId,
    /// Slot holding the amount the buyer ESCROWED.
    pub escrowed_slot: usize,
    /// Slot holding the funds RELEASED to the seller at settlement.
    pub released_slot: usize,
    /// Slot holding the funds REFUNDED to the buyer at settlement.
    pub refunded_slot: usize,
}

impl EscrowSchema {
    /// The canonical escrow-market schema for an escrow `cell`
    /// (`escrow-market`: escrowed=5, released=7, refunded=8).
    pub fn escrow_market(cell: CellId) -> Self {
        EscrowSchema { cell, escrowed_slot: 5, released_slot: 7, refunded_slot: 8 }
    }
}

/// **Escrow conservation — `released + refunded == escrowed`, statically.**
///
/// This is the escrow market's FLASHWELL organ ( `build_settle_action`'s
/// settle-scoped `AffineEq { RELEASED + REFUNDED − ESCROWED = 0 }` ) restated as
/// a static, artifact-only predicate. It scans the forest for the last
/// `SetField` write to each of the escrow cell's `escrowed` / `released` /
/// `refunded` slots, decodes them as `u64`, and asserts the conservation
/// identity: a settlement splits the escrow with no mint and no burn.
///
/// `prior_escrowed` supplies the committed escrow amount when the forest under
/// analysis is the `settle` turn alone (which writes `released`/`refunded` but
/// not `escrowed` — that was bound by the earlier `fund` turn). Pass `None` when
/// the forest itself writes `escrowed` (a full lifecycle forest), in which case
/// the in-forest write is used.
///
/// THE BOUNDARY: this proves the *intended* split conserves the *escrowed*
/// amount it can resolve. It does not prove the seller/buyer actually receive
/// the funds (no `Transfer` is implied — escrow value lives in the cell's state
/// slots, paid out by the app's own settlement convention), nor that the escrow
/// was ≤ the listing ceiling (the TRUSTLINE invariant — a separate `FieldLteField`
/// the executor enforces; add a ceiling slot to check it here too).
pub fn check_escrow_conservation(
    forest: &CallForest,
    schema: &EscrowSchema,
    prior_escrowed: Option<u64>,
) -> Verdict {
    let writes = last_field_writes(forest, schema.cell);

    // Resolve each operand: prefer the in-forest write; fall back to the prior
    // committed value for `escrowed`; default the settlement legs to 0 (an
    // unwritten leg is genuinely zero — a one-sided settlement).
    let escrowed = resolve_amount(&writes, schema.escrowed_slot, prior_escrowed);
    let released = resolve_amount(&writes, schema.released_slot, Some(0));
    let refunded = resolve_amount(&writes, schema.refunded_slot, Some(0));

    let mut findings = Vec::new();

    // Surface a non-decodable write as its own finding (an amount slot carrying
    // a hash is a construction bug the executor's arithmetic would also reject).
    for (name, slot) in [
        ("escrowed", schema.escrowed_slot),
        ("released", schema.released_slot),
        ("refunded", schema.refunded_slot),
    ] {
        if let Some((path, raw)) = writes.get(&slot) {
            if decode_u64_field(raw).is_none() {
                findings.push(Finding {
                    guarantee: "escrow (conservation)".to_string(),
                    locus: Locus::node(path.clone()),
                    message: format!(
                        "escrow {name} slot {slot} is written with a non-integer field \
                         (leading bytes nonzero — looks like a hash, not an amount); \
                         the conservation arithmetic cannot net it"
                    ),
                });
            }
        }
    }

    match (escrowed, released, refunded) {
        (Some(e), Some(r), Some(rf)) => {
            // i128 to dodge wrap on the sum.
            let payout = r as i128 + rf as i128;
            if payout != e as i128 {
                let verb = if payout > e as i128 { "mints" } else { "burns" };
                findings.push(Finding {
                    guarantee: "escrow (conservation)".to_string(),
                    locus: Locus::node(vec![]).at_asset(format!("escrow:{}", short_cell(&schema.cell))),
                    message: format!(
                        "escrow settlement does not conserve: released ({r}) + refunded ({rf}) \
                         = {payout} ≠ escrowed ({e}) — the split {verb} value (the FLASHWELL \
                         AffineEq the executor enforces at settle would reject it). \
                         A conserving settlement needs released + refunded == escrowed."
                    ),
                });
            }
        }
        _ => {
            // Could not resolve escrowed (no in-forest write, no prior given) —
            // report it rather than vacuously pass.
            if escrowed.is_none() {
                findings.push(Finding {
                    guarantee: "escrow (conservation)".to_string(),
                    locus: Locus::node(vec![]).at_asset(format!("escrow:{}", short_cell(&schema.cell))),
                    message: format!(
                        "cannot check escrow conservation: the escrowed amount (slot {}) is \
                         neither written in this forest nor supplied as a prior-committed value. \
                         Pass the committed escrow via `prior_escrowed` when analyzing a settle \
                         turn in isolation.",
                        schema.escrowed_slot
                    ),
                });
            }
        }
    }

    Verdict::from_findings(findings)
}

// ─── bounty lifecycle monotonicity ──────────────────────────────────────────

/// The lifecycle schema for a monotone state-machine cell: the `STATE` slot and
/// the legal strictly-increasing code ladder. Defaults match
/// `starbridge-apps/bounty-board` (`STATE_SLOT = 4`; OPEN=1, CLAIMED=2,
/// SUBMITTED=3, PAID=4).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LifecycleSchema {
    /// The cell the lifecycle lives on.
    pub cell: CellId,
    /// The slot carrying the lifecycle state code (`StrictMonotonic`).
    pub state_slot: usize,
    /// The legal state codes, in strictly-increasing lifecycle order. A write to
    /// a code not in this set, or out of order, is flagged.
    pub ladder: Vec<u64>,
}

impl LifecycleSchema {
    /// The canonical bounty-board lifecycle for a bounty `cell`
    /// (`bounty-board`: state slot 4; OPEN=1→CLAIMED=2→SUBMITTED=3→PAID=4).
    pub fn bounty_board(cell: CellId) -> Self {
        LifecycleSchema { cell, state_slot: 4, ladder: vec![1, 2, 3, 4] }
    }

    /// The canonical escrow-market lifecycle for an escrow `cell`
    /// (`escrow-market`: state slot 9; LISTED=1→FUNDED=2→SHIPPED=3→SETTLED=4).
    pub fn escrow_market(cell: CellId) -> Self {
        LifecycleSchema { cell, state_slot: 9, ladder: vec![1, 2, 3, 4] }
    }
}

/// **Bounty-board lifecycle monotonicity — `OPEN→CLAIMED→SUBMITTED→PAID`,
/// statically.**
///
/// This is the bounty board's `StrictMonotonic(STATE)` caveat restated as a
/// static, artifact-only predicate. It walks the forest in execution order
/// (pre-order DFS — the order the executor applies the actions), collects every
/// `SetField` write to the lifecycle `state_slot`, and checks the sequence of
/// state codes:
///
///   * each code is a *known* ladder state (an unknown code is a default-deny
///     the executor would reject at `NoTransitionCaseMatched`),
///   * the sequence is *strictly increasing* (a forest that writes the same
///     state twice, or steps backward, violates `StrictMonotonic` — a
///     double-claim, a re-open of a paid bounty, a rewind),
///   * (with `prior_state`) the first in-forest write strictly exceeds the
///     already-committed state.
///
/// `prior_state` is the lifecycle code already committed on the live cell (the
/// state before this forest runs). Pass `None` for a from-genesis forest (e.g. a
/// test forest that posts the bounty itself, starting at OPEN).
///
/// THE BOUNDARY: this checks the *ordering* of the planned writes is legal. It
/// does NOT check the per-step *side conditions* (that `claim` also binds the
/// claimant hash, that `submit` binds the artifact) — those are `WriteOnce`
/// slot caveats; use [`check_writeonce_slots`] for the freeze half.
pub fn check_bounty_lifecycle(
    forest: &CallForest,
    schema: &LifecycleSchema,
    prior_state: Option<u64>,
) -> Verdict {
    let mut findings = Vec::new();
    let mut prev: Option<u64> = prior_state;

    for (path, code, raw) in ordered_field_writes(forest, schema.cell, schema.state_slot) {
        let Some(code) = code else {
            findings.push(Finding {
                guarantee: "bounty (lifecycle)".to_string(),
                locus: Locus::node(path.clone()),
                message: format!(
                    "lifecycle state slot {} written with a non-integer field {} \
                     (a state code must be a small integer)",
                    schema.state_slot,
                    hex_prefix(&raw)
                ),
            });
            continue;
        };

        // unknown code → default-deny territory
        if !schema.ladder.contains(&code) {
            findings.push(Finding {
                guarantee: "bounty (lifecycle)".to_string(),
                locus: Locus::node(path.clone()),
                message: format!(
                    "lifecycle write sets state {code}, which is not a legal ladder state \
                     {:?} — the cell program default-denies an unknown transition",
                    schema.ladder
                ),
            });
            // still fold it into prev so we don't double-report a later step
        }

        if let Some(p) = prev {
            if code <= p {
                findings.push(Finding {
                    guarantee: "bounty (lifecycle)".to_string(),
                    locus: Locus::node(path.clone()),
                    message: format!(
                        "lifecycle is not strictly monotone: state {code} does not exceed the \
                         previous state {p} (StrictMonotonic requires new > old). {}",
                        if code == p {
                            "Re-entering the same state is a double-claim / replay."
                        } else {
                            "Stepping backward re-opens a closed lifecycle."
                        }
                    ),
                });
            }
        }
        prev = Some(code);
    }

    Verdict::from_findings(findings)
}

// ─── agent-provenance hash-chain verification ───────────────────────────────

/// **`verify_provenance_chain`** — the third-party VERIFIER, byte-identical to
/// `starbridge-apps/agent-provenance::verify_chain`. Given the published claim
/// digests and the entry digests as read off the committed cell, re-derive the
/// honest blake3 hash chain (`entry_i = blake3("dregg-provenance-link\x01" ‖
/// prev ‖ claim_i)`, starting from the genesis predecessor `[0u8; 32]`) and
/// check they match link-for-link. Returns `true` IFF every committed digest
/// equals the honest link — a tampered, reordered, forged, or dropped entry
/// makes it `false`.
///
/// This is the *executable* verifier, kept in lock-step with the app so the
/// pre-submission toolkit and the on-chain log agree on the chain law.
pub fn verify_provenance_chain(claims: &[[u8; 32]], committed: &[[u8; 32]]) -> bool {
    committed == provenance_entry_digests(claims).as_slice()
}

/// The provenance link hash — `blake3("dregg-provenance-link\x01" ‖ prev ‖
/// claim)`. Mirrors `agent-provenance::link_hash`.
pub fn provenance_link_hash(prev: &[u8; 32], claim: &[u8; 32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-provenance-link\x01");
    h.update(prev);
    h.update(claim);
    *h.finalize().as_bytes()
}

/// The honest digest sequence for a list of claim digests — each entry folds the
/// PREVIOUS entry's digest with the next claim, from the genesis predecessor.
/// Mirrors `agent-provenance::entry_digests`.
pub fn provenance_entry_digests(claims: &[[u8; 32]]) -> Vec<[u8; 32]> {
    let mut out = Vec::with_capacity(claims.len());
    let mut prev = [0u8; 32];
    for claim in claims {
        let h = provenance_link_hash(&prev, claim);
        out.push(h);
        prev = h;
    }
    out
}

/// The provenance-log schema: where the entry digests live in the cell's slots.
/// Default `entry_base = 4` matches `agent-provenance::ENTRY_BASE`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ProvenanceSchema {
    /// The provenance-log cell.
    pub cell: CellId,
    /// The slot of the 0-th entry digest; entry `i` lives at `entry_base + i`.
    pub entry_base: usize,
}

impl ProvenanceSchema {
    /// The canonical agent-provenance schema for a log `cell` (`entry_base = 4`).
    pub fn agent_provenance(cell: CellId) -> Self {
        ProvenanceSchema { cell, entry_base: 4 }
    }
}

/// **Provenance-chain integrity over a forest.** Extracts the entry digests the
/// forest *commits* (the `SetField` writes to `entry_base + i`, ordered by `i`)
/// and checks they form exactly the honest blake3 hash chain of the supplied
/// `claims` — i.e. [`verify_provenance_chain`] against the in-forest digests.
///
/// `prior_committed` are the entry digests already on the live cell from earlier
/// turns; the forest's writes extend them. Pass `&[]` for a from-genesis forest
/// that appends the whole chain. The `claims` must cover
/// `prior_committed.len() + (entries this forest writes)` entries, in order.
///
/// THE BOUNDARY: this verifies the *digests the forest intends to commit* equal
/// the honest chain of the *claims you publish*. It cannot know the claim
/// preimages from the forest alone (the cell stores only digests) — you supply
/// them, exactly as a third-party auditor publishes the claims it is attesting.
pub fn check_provenance_chain_in_forest(
    forest: &CallForest,
    schema: &ProvenanceSchema,
    claims: &[[u8; 32]],
    prior_committed: &[[u8; 32]],
) -> Verdict {
    let mut findings = Vec::new();

    // Gather the in-forest entry writes by slot offset.
    let writes = last_field_writes(forest, schema.cell);
    let mut committed: Vec<[u8; 32]> = prior_committed.to_vec();
    // Append contiguous entries starting at prior_committed.len().
    let mut i = prior_committed.len();
    loop {
        let slot = schema.entry_base + i;
        match writes.get(&slot) {
            Some((_, raw)) => {
                committed.push(*raw);
                i += 1;
            }
            None => break,
        }
    }

    // A gap (an entry written past a hole) is itself a malformed log.
    let highest_written = writes
        .keys()
        .filter(|&&s| s >= schema.entry_base)
        .map(|&s| s - schema.entry_base)
        .max();
    if let Some(hi) = highest_written {
        let contiguous_top = committed.len(); // exclusive
        if hi + 1 > contiguous_top {
            findings.push(Finding {
                guarantee: "provenance (chain)".to_string(),
                locus: Locus::node(vec![]).at_asset(format!("prov:{}", short_cell(&schema.cell))),
                message: format!(
                    "provenance entries are not contiguous: an entry was written at index {hi} \
                     but the chain only fills contiguously up to index {} \
                     (a hole breaks the append-only hash chain)",
                    contiguous_top.saturating_sub(1)
                ),
            });
        }
    }

    if committed.len() != claims.len() {
        findings.push(Finding {
            guarantee: "provenance (chain)".to_string(),
            locus: Locus::node(vec![]).at_asset(format!("prov:{}", short_cell(&schema.cell))),
            message: format!(
                "provenance claim/digest count mismatch: {} committed entries (prior {} + \
                 in-forest {}) vs {} published claims — the verifier needs one claim per \
                 committed entry, in order",
                committed.len(),
                prior_committed.len(),
                committed.len() - prior_committed.len(),
                claims.len()
            ),
        });
        return Verdict::from_findings(findings);
    }

    if !verify_provenance_chain(claims, &committed) {
        // Locate the first divergent link for a precise message.
        let honest = provenance_entry_digests(claims);
        let first_bad = committed
            .iter()
            .zip(honest.iter())
            .position(|(c, h)| c != h);
        let where_ = first_bad.map(|i| i.to_string()).unwrap_or_else(|| "?".into());
        findings.push(Finding {
            guarantee: "provenance (chain)".to_string(),
            locus: Locus::node(vec![]).at_asset(format!("prov:{}", short_cell(&schema.cell))),
            message: format!(
                "provenance chain does not verify: committed entry {where_} is not \
                 link_hash(previous, claim[{where_}]). The committed log is not the honest \
                 blake3 hash chain of the published claims — a tampered, reordered, forged, \
                 or dropped entry."
            ),
        });
    }

    Verdict::from_findings(findings)
}

// ─── WriteOnce freeze (the write-once half shared by all three apps) ─────────

/// **WriteOnce freeze check.** Given the slots an app declares `WriteOnce` and
/// the values already committed on the live cell (`prior`), flags any forest
/// write that would *overwrite a different value* into an already-bound slot —
/// the executor's `WriteOnce` caveat (tamper-evidence: escrow delivery hash,
/// provenance entries, bounty title/reward/claimant/submission).
///
/// A write that re-states the SAME committed value is a harmless no-op (the
/// `WriteOnce` caveat admits idempotent rewrites); a write into a slot with NO
/// prior value is the legitimate first write. Only a *changing* overwrite is
/// flagged.
pub fn check_writeonce_slots(
    forest: &CallForest,
    cell: CellId,
    writeonce_slots: &[usize],
    prior: &BTreeMap<usize, [u8; 32]>,
) -> Verdict {
    let mut findings = Vec::new();
    let writes = last_field_writes(forest, cell);
    for &slot in writeonce_slots {
        if let (Some((path, new)), Some(old)) = (writes.get(&slot), prior.get(&slot)) {
            if new != old {
                findings.push(Finding {
                    guarantee: "app (write-once)".to_string(),
                    locus: Locus::node(path.clone()),
                    message: format!(
                        "write-once slot {slot} is overwritten with a different value \
                         ({} → {}); the WriteOnce caveat freezes a committed slot — this \
                         is a tamper the executor rejects",
                        hex_prefix(old),
                        hex_prefix(new)
                    ),
                });
            }
        }
    }
    Verdict::from_findings(findings)
}

// ─── shared forest projection helpers ───────────────────────────────────────

/// The last `SetField` write to each slot of `cell` in the forest (execution
/// order — a later write wins, as it does in the executor), with the node path
/// of that write.
fn last_field_writes(forest: &CallForest, cell: CellId) -> BTreeMap<usize, (Vec<usize>, [u8; 32])> {
    let mut out: BTreeMap<usize, (Vec<usize>, [u8; 32])> = BTreeMap::new();
    walk(forest, |path, node| {
        for eff in &node.action.effects {
            if let Effect::SetField { cell: c, index, value } = eff {
                if *c == cell {
                    out.insert(*index, (path.to_vec(), *value));
                }
            }
        }
    });
    out
}

/// Every `SetField` write to `(cell, slot)` in execution order, as
/// `(node_path, decoded_u64, raw_field)`.
fn ordered_field_writes(
    forest: &CallForest,
    cell: CellId,
    slot: usize,
) -> Vec<(Vec<usize>, Option<u64>, [u8; 32])> {
    let mut out = Vec::new();
    walk(forest, |path, node| {
        for eff in &node.action.effects {
            if let Effect::SetField { cell: c, index, value } = eff {
                if *c == cell && *index == slot {
                    out.push((path.to_vec(), decode_u64_field(value), *value));
                }
            }
        }
    });
    out
}

/// Resolve an amount slot: the in-forest decoded write, else the supplied
/// fallback (prior-committed value, or a default).
fn resolve_amount(
    writes: &BTreeMap<usize, (Vec<usize>, [u8; 32])>,
    slot: usize,
    fallback: Option<u64>,
) -> Option<u64> {
    match writes.get(&slot) {
        Some((_, raw)) => decode_u64_field(raw),
        None => fallback,
    }
}

fn short_cell(c: &CellId) -> String {
    let mut s = String::with_capacity(8);
    for byte in &c.0[..4] {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

fn hex_prefix(f: &[u8; 32]) -> String {
    let mut s = String::with_capacity(10);
    s.push_str("0x");
    for byte in &f[..4] {
        s.push_str(&format!("{byte:02x}"));
    }
    s.push('…');
    s
}
