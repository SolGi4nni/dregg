//! The LEAN-BACKED CONSTRAINT ORACLE — the deployed-node backend for `dregg_cell`'s
//! [`ConstraintOracle`](dregg_cell::program::ConstraintOracle) seam.
//!
//! Marshals a `StateConstraint` + its `(old, new)` `CellState` slice + the small typed context slice
//! into the wire the verified Lean `@[export] dregg_constraint_admits`
//! (`Dregg2.Exec.DeployedConstraint.admitsTop`) reads, calls it through `dregg-lean-ffi`, and maps the
//! verdict back to the deployed `ProgramError` variants. This is what makes the deployed node's
//! per-constraint admission decision (for the subset) COMPUTED BY the Lean source — the game-proof
//! LARP-audit collapse. `cell`/`turn` cannot link the archive (they compile to wasm32 + the SP1 zkVM
//! guest), so this backend lives in `dregg-exec-lean` (which DOES link it) and is installed at native
//! node startup, exactly like [`register_distributed_gates`](crate::distributed_gates).
//!
//! ## THE NAMED TRUSTED-RUST SLOT
//!
//! [`encode_constraint`] is an EXHAUSTIVE match with **no wildcard arm**. Every `StateConstraint`
//! variant is either encoded (Lean-evaluated) or listed by name in the `── TRUSTED RUST SLOT ──`
//! block with the reason it cannot be. Adding a variant to `StateConstraint` therefore FAILS THE
//! BUILD here until someone classifies it — a new security-critical arm cannot slide in silently as
//! "not my subset".
//!
//! ## The marshaller is NOT a free mirror
//!
//! The wire grammar is hand-authored on both sides (`parseConstraint` in Lean, `encode_constraint`
//! here). What keeps them honest is a BITING differential: `tests/constraint_oracle_differential.rs`
//! names EVERY `StateConstraint` variant (`VARIANT_NAMES`, count-pinned) and asserts, for EVERY
//! Lean-routed arm, both an ADMIT case and a REFUSE case agreeing with the Rust evaluator, PLUS a
//! ROUTING LEDGER (`LEAN_ROUTED`) equality so a silently-narrowed subset fails too. A drifted tag
//! makes the Lean parse fail closed (`"1"` = violated), which contradicts the arm's ADMIT case — so
//! any tag/arity divergence turns that test red. (The two executor-only sentinels have no admitting
//! input at all; for those the bite is the error-DISCRIMINANT comparison.)
//!
//! ## What crosses the wire, and what does NOT
//!
//! Rust marshals STATE (the 16+16 registers, the balance, the resolved heap cells) and a bounded
//! TYPED context slice; Lean decides. For the aggregate arms Rust does the KEY RESOLUTION only —
//! `read_collection`'s anchor truncation, `CollPred::eval`, and the council's `mOfNDistinct`
//! distinctness are all Lean-authored. Rust never re-states a predicate.

use dregg_cell::preconditions::EvalContext;
use dregg_cell::program::{
    CollPred, ConstraintOracle, ElemPredAtom, HeapAtom, ProgramError, SimpleStateConstraint,
    StateConstraint, TransitionMeta,
};
use dregg_cell::state::{CellState, FieldElement};

/// Hex-encode a 32-byte field element, big-endian (the Lean wire's field encoding).
fn hex32(f: &FieldElement) -> String {
    let mut s = String::with_capacity(64);
    for b in f.iter() {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ── ENCODING ENVELOPES ──────────────────────────────────────────────────────────────────────────
//
// These bound the WIRE, so one admission cannot become a megabyte of tokens. Outside them the
// marshaller DECLINES (`None`), and `dregg_cell`'s `undecided_subset_disposition` then REFUSES the
// constraint rather than handing a Lean-subset decision back to the Rust twin.
//
// ⚠ THEY ARE NO LONGER LOAD-BEARING FOR AGREEMENT, AND THE ARGUMENT THAT SAID THEY WERE WAS
// UNSOUND. This block used to read: "the deployed Rust computes the affine sums in `i128`; inside
// these envelopes the `i128` arithmetic cannot overflow, so the two agree EXACTLY. Outside them the
// marshaller DECLINES and the Rust evaluator runs — no silent disagreement, no wrapped-sum admit."
// The first half was true and the last clause was the exact opposite of what happened: outside the
// envelope the Rust evaluator ran and its `i128` accumulator WRAPPED, so a sum of `2^128` read as
// `0` and ADMITTED an `AffineLe { c: 0 }` that Lean refuses. Measured on wasm32 (the browser light
// client), where no oracle is installed and so no envelope stands in front of that accumulator at
// all. `dregg_cell::program::eval::AffineAcc` now accumulates EXACTLY over a signed 256-bit value
// on every target, so the Rust evaluator agrees with `DeployedConstraint.affineSum` for ALL inputs,
// in or out of envelope — and these constants are a wire budget, not a soundness argument.

/// Maximum affine terms marshalled. `1024 · 2^32 · 2^64 = 2^106`, comfortably inside the wire's
/// decimal-token budget.
const MAX_AFFINE_TERMS: usize = 1024;
/// Maximum absolute affine coefficient marshalled (see [`MAX_AFFINE_TERMS`]).
const MAX_AFFINE_COEFF: i64 = 1 << 32;
/// Maximum length of any marshalled list (allowlists, edge sets, transition tables, member sets).
/// Bounds the wire so a pathological program cannot turn one admission into a megabyte of tokens.
const MAX_LIST: usize = 4096;
/// Maximum number of RESOLVED heap / field-map cells marshalled for the aggregate arms. The
/// collection read is `fuel × stride` cells plus the anchor probe; beyond this the marshaller
/// DECLINES and the Rust evaluator runs (sound — no silent half-read).
const MAX_COLL_CELLS: u64 = 8192;

/// The number of RESOLVED cells the Lean side needs to reproduce `read_collection` /
/// `read_collection_fields` for a `(stride, fuel, anchor)` shape: the row-major `fuel × stride`
/// grid, PLUS the anchor probe of the last element.
///
/// ⚑ The deployed anchor probe reads key `i*stride + anchor` — NOT the element's `stride`-bounded
/// slice — so an `anchor >= stride` probes past the grid. `+ anchor + 1` covers that faithfully.
/// `None` = outside the marshalling envelope (the caller declines to Rust).
fn coll_cell_count(stride: u32, fuel: u32, anchor: u32) -> Option<u64> {
    let n = (fuel as u64)
        .checked_mul(stride as u64)?
        .checked_add(anchor as u64)?
        .checked_add(1)?;
    if n > MAX_COLL_CELLS { None } else { Some(n) }
}

/// Is this affine term list inside the `i128`-exact envelope?
fn affine_envelope_ok(terms: &[(i64, u8)]) -> bool {
    terms.len() <= MAX_AFFINE_TERMS
        && terms
            .iter()
            .all(|(k, _)| *k >= -MAX_AFFINE_COEFF && *k <= MAX_AFFINE_COEFF)
}

/// Encode an affine term run: `<n> (k slot)*n`.
fn encode_terms(tag: &str, terms: &[(i64, u8)], c: i64) -> Option<String> {
    if !affine_envelope_ok(terms) {
        return None;
    }
    let mut s = format!("{tag} {}", terms.len());
    for (k, idx) in terms {
        s.push(' ');
        s.push_str(&k.to_string());
        s.push(' ');
        s.push_str(&idx.to_string());
    }
    s.push(' ');
    s.push_str(&c.to_string());
    Some(s)
}

/// Encode a decimal-token list run: `<n> v*n`.
fn encode_u64_list(prefix: &str, xs: &[u64]) -> Option<String> {
    if xs.len() > MAX_LIST {
        return None;
    }
    let mut s = format!("{prefix} {}", xs.len());
    for v in xs {
        s.push(' ');
        s.push_str(&v.to_string());
    }
    Some(s)
}

/// Encode a `u8`-slot list run: `<n> v*n`.
fn encode_u8_list(prefix: &str, xs: &[u8]) -> Option<String> {
    if xs.len() > MAX_LIST {
        return None;
    }
    let mut s = format!("{prefix} {}", xs.len());
    for v in xs {
        s.push(' ');
        s.push_str(&v.to_string());
    }
    Some(s)
}

/// Encode the constraint tail token stream. `None` = OUTSIDE the Lean-evaluated subset (the named
/// trusted-Rust slot, or an input outside an encoding envelope), which the caller evaluates in Rust.
///
/// The token grammar MUST match `Dregg2.Exec.DeployedConstraint.parseConstraint` /
/// `parseHeapAtom` / `parseTop` — this is the load-bearing wire contract of the collapse, held by
/// the biting differential in `tests/constraint_oracle_differential.rs`.
///
/// ⚠ EXHAUSTIVE — no wildcard arm. A new `StateConstraint` variant breaks this build until it is
/// classified as Lean-evaluated or added to the named trusted-Rust slot below.
fn encode_constraint(c: &StateConstraint) -> Option<String> {
    Some(match c {
        // ══ (a) PURE — registers ═════════════════════════════════════════════════════════════════
        StateConstraint::FieldEquals { index, value } => format!("FE {index} {}", hex32(value)),
        StateConstraint::FieldGte { index, value } => format!("FG {index} {}", hex32(value)),
        StateConstraint::FieldLte { index, value } => format!("FL {index} {}", hex32(value)),
        StateConstraint::FieldLteField {
            left_index,
            right_index,
        } => format!("FLF {left_index} {right_index}"),
        StateConstraint::FieldLteOther {
            index,
            other,
            delta,
        } => format!("FLO {index} {other} {delta}"),
        StateConstraint::SumEquals { indices, value } => {
            encode_u8_list(&format!("SE {}", hex32(value)), indices)?
        }
        StateConstraint::Immutable { index } => format!("IM {index}"),
        StateConstraint::WriteOnce { index } => format!("WO {index}"),
        StateConstraint::Monotonic { index } => format!("MO {index}"),
        StateConstraint::StrictMonotonic { index } => format!("SM {index}"),
        StateConstraint::BoundedBy {
            index,
            witness_index,
        } => format!("BB {index} {witness_index}"),
        StateConstraint::FieldDelta { index, delta } => format!("FD {index} {}", hex32(delta)),
        StateConstraint::FieldDeltaInRange {
            index,
            min_delta,
            max_delta,
        } => format!("FDR {index} {} {}", hex32(min_delta), hex32(max_delta)),
        StateConstraint::SumEqualsAcross {
            input_fields,
            output_fields,
        } => {
            if input_fields.len() > MAX_LIST || output_fields.len() > MAX_LIST {
                return None;
            }
            let mut s = format!("SEA {}", input_fields.len());
            for i in input_fields {
                s.push(' ');
                s.push_str(&i.to_string());
            }
            s.push(' ');
            s.push_str(&output_fields.len().to_string());
            for o in output_fields {
                s.push(' ');
                s.push_str(&o.to_string());
            }
            s
        }
        StateConstraint::MonotonicSequence { seq_index } => format!("MSEQ {seq_index}"),
        StateConstraint::AllowedTransitions {
            slot_index,
            allowed,
        } => {
            if allowed.len() > MAX_LIST {
                return None;
            }
            let mut s = format!("AT {slot_index} {}", allowed.len());
            for (o, n) in allowed {
                s.push(' ');
                s.push_str(&hex32(o));
                s.push(' ');
                s.push_str(&hex32(n));
            }
            s
        }
        StateConstraint::SymEq { index, sym } => format!("SYE {index} {sym}"),
        StateConstraint::SymMemberOf { index, set } => {
            encode_u64_list(&format!("SYM {index}"), set)?
        }
        StateConstraint::DigEq { index, digest } => format!("DGE {index} {}", hex32(digest)),
        StateConstraint::DigFieldEq {
            left_index,
            right_index,
        } => format!("DGF {left_index} {right_index}"),
        StateConstraint::MemberOf { index, set } => encode_u64_list(&format!("MEM {index}"), set)?,
        StateConstraint::PrefixOf {
            seg_indices,
            prefix,
        } => {
            if seg_indices.len() > MAX_LIST || prefix.len() > MAX_LIST {
                return None;
            }
            let mut s = format!("PRE {}", seg_indices.len());
            for i in seg_indices {
                s.push(' ');
                s.push_str(&i.to_string());
            }
            s.push(' ');
            s.push_str(&prefix.len().to_string());
            for p in prefix {
                s.push(' ');
                s.push_str(&p.to_string());
            }
            s
        }
        StateConstraint::InRangeTwoSided { index, lo, hi } => format!("IR {index} {lo} {hi}"),
        StateConstraint::DeltaBounded { index, d } => format!("DB {index} {d}"),
        StateConstraint::AffineLe { terms, c } => encode_terms("ALE", terms, *c)?,
        StateConstraint::AffineEq { terms, c } => encode_terms("AEQ", terms, *c)?,
        StateConstraint::AffineDeltaLe { terms, c } => encode_terms("ADLE", terms, *c)?,
        StateConstraint::Reachable {
            from_index,
            to_label,
            edges,
        } => {
            if edges.len() > MAX_LIST {
                return None;
            }
            let mut s = format!("RCH {from_index} {to_label} {}", edges.len());
            for (a, b) in edges {
                s.push(' ');
                s.push_str(&a.to_string());
                s.push(' ');
                s.push_str(&b.to_string());
            }
            s
        }
        StateConstraint::SettleEscrow {
            leg_a_index,
            leg_b_index,
        } => format!("SETL {leg_a_index} {leg_b_index}"),
        StateConstraint::VaultDeposit {
            assets_slot,
            shares_slot,
        } => format!("VD {assets_slot} {shares_slot}"),
        StateConstraint::RateBound { counter_index, k } => format!("RB {counter_index} {k}"),
        StateConstraint::UntilEvent { flag_index } => format!("UE {flag_index}"),
        StateConstraint::SinceEvent { flag_index } => format!("SEV {flag_index}"),

        // ══ (a) PURE — the SIGNED sealed balance ═════════════════════════════════════════════════
        StateConstraint::BalanceGte { min } => format!("BGE {min}"),
        StateConstraint::BalanceLte { max } => format!("BLE {max}"),
        StateConstraint::BalanceDeltaLte { max } => format!("BDL {max}"),
        StateConstraint::BalanceDeltaGte { min } => format!("BDG {min}"),

        // ══ (a) PURE — heap ══════════════════════════════════════════════════════════════════════
        StateConstraint::HeapField { atom, .. } => encode_heap_atom(atom)?,
        StateConstraint::HeapFieldLteOther { delta, .. } => format!("HLO {delta}"),

        // ══ (b) CONTEXT — {block_height, sender, delegation_epoch} ═══════════════════════════════
        StateConstraint::FieldGteHeight { index, offset } => format!("FGH {index} {offset}"),
        StateConstraint::FieldLteHeight { index, offset } => format!("FLH {index} {offset}"),
        StateConstraint::TemporalGate {
            not_before,
            not_after,
        } => {
            let nb = match not_before {
                Some(x) => format!("1 {x}"),
                None => "0 0".to_string(),
            };
            let na = match not_after {
                Some(x) => format!("1 {x}"),
                None => "0 0".to_string(),
            };
            format!("TG {nb} {na}")
        }
        StateConstraint::CooledSince { staged_at, period } => format!("CS {staged_at} {period}"),
        StateConstraint::ChallengeWindow {
            challenge_index,
            staged_at,
            period,
        } => format!("CW {challenge_index} {staged_at} {period}"),
        StateConstraint::DischargeObligation {
            cursor_slot,
            due_slot,
            amount_slot,
            period,
            amount,
        } => format!("DO {cursor_slot} {due_slot} {amount_slot} {period} {amount}"),
        StateConstraint::SenderIs { pk } => format!("SIS {}", hex32(pk)),
        StateConstraint::SenderInSlot { index } => format!("SIL {index}"),
        StateConstraint::SenderMemberOf { members } => {
            if members.len() > MAX_LIST {
                return None;
            }
            let mut s = format!("SMO {}", members.len());
            for m in members {
                s.push(' ');
                s.push_str(&hex32(m));
            }
            s
        }
        StateConstraint::DelegationEpochEquals { index } => format!("DEE {index}"),

        // ══ (b) CONTEXT — the executor's per-(cell, sender, epoch) rate counters ═════════════════
        //
        // `ctx.sender_epoch_count` is the FOURTH marshalled context field. It is EXECUTOR-HELD
        // (`execute_tree::state_constraint_context_count`), never submitter-supplied, so putting it
        // on the wire does not widen the attack surface — it moves the COMPARISON into Lean while
        // the value stays the executor's. `epoch_duration` is NOT read by the deployed arms.
        StateConstraint::RateLimit { max_per_epoch, .. } => format!("RL {max_per_epoch}"),
        StateConstraint::RateLimitBySum {
            slot_index,
            max_sum_per_epoch,
            ..
        } => format!("RLS {slot_index} {max_sum_per_epoch}"),

        // ══ (a) PURE — the RESOLVED heap / field-map cell run ════════════════════════════════════
        //
        // Rust resolves the KEYS (the same job it already does for `HeapField`); the SEMANTICS —
        // the `readIndexed` anchor truncation, the element predicate, the aggregate, the council's
        // distinctness — are Lean's. See `resolve_cells`.
        StateConstraint::FieldsCountEquals {
            keys,
            value,
            count_index,
        } => {
            if keys.len() > MAX_LIST {
                return None;
            }
            format!("FCE {} {} {count_index}", keys.len(), hex32(value))
        }
        StateConstraint::CollectionAggregate {
            stride, fuel, pred, ..
        }
        | StateConstraint::FieldsCollectionAggregate {
            stride, fuel, pred, ..
        } => {
            // ONE Lean arm serves BOTH: after key resolution the two differ only in WHERE the
            // cells came from (the `(collection_id, key)` heap vs the `fields_map` tail), which is
            // Rust's resolution job, not a semantic difference.
            coll_cell_count(*stride, *fuel, pred.anchor_offset())?;
            format!("CAGG {stride} {fuel} {}", encode_coll_pred(pred)?)
        }

        // ══ (a) PURE — the EXECUTOR-ONLY SENTINELS (fail-closed by construction) ═════════════════
        //
        // Both deployed arms are total refusals the scalar evaluator CANNOT decide otherwise. Moving
        // them here makes the fail-closed refusal Lean-authored: the historic silent `Ok(())` that
        // let a cell DECLARE NFT-uniqueness while enforcing nothing cannot come back through a Rust
        // edit alone. The `cap_set_root_slot` / `peer_cell` payloads are re-attached by
        // `decode_verdict` FROM THE CONSTRAINT, so no `CellId` needs a wire encoding.
        StateConstraint::CapabilityUniqueness { cap_set_root_slot } => {
            format!("CAPU {cap_set_root_slot}")
        }
        StateConstraint::BoundDelta { .. } => "BDW".to_string(),

        // ══ THE BOOLEAN COMBINATORS (over Lean-evaluated simple branches) ════════════════════════
        StateConstraint::AnyOf { variants } => encode_branches("ANY", variants)?,
        StateConstraint::AllOf { variants } => encode_branches("ALL", variants)?,

        // ══ ── TRUSTED RUST SLOT ── (class (c): CRYPTO / WITNESS) ════════════════════════════════
        //
        // EXPLICITLY carved out, by name, with the reason. These ELEVEN arms stay in the hand-written
        // Rust evaluator (`cell/src/program/eval.rs`) and are therefore UNVERIFIED — this list IS the
        // honest statement of what the reality-gate does NOT yet cover. Every one of them needs a
        // hash recomputation, a proof/witness verifier, a DSL runtime, or peer-cell state: there is
        // no "pure but unported" arm left here. (`RateLimit` / `RateLimitBySum` / `CapabilityUniqueness`
        // / `BoundDelta` / the aggregates moved to the Lean-evaluated subset above.)
        //
        // ── crypto: hashes the evaluator computes itself ──
        StateConstraint::PreimageGate { .. }        // BLAKE3 / Poseidon2 over a revealed preimage
        | StateConstraint::KeyRotationGate { .. }   // pre-rotation digest + witness preimage
        | StateConstraint::ClearanceDominates { .. } // BLAKE3 clearance-graph root recomputation
        // ── witness/proof dispatch: a verifier registry, not a state predicate ──
        | StateConstraint::SenderAuthorized { .. }  // Merkle / blinded-set membership proof
        | StateConstraint::Renounced { .. }         // sorted-set NON-membership proof
        | StateConstraint::Witnessed { .. }         // generic witnessed-predicate registry dispatch
        | StateConstraint::TemporalPredicate { .. } // temporal-DSL circuit verification
        | StateConstraint::ObservedFieldEquals { .. } // cross-cell verified observation proof
        | StateConstraint::AnyOfBound { .. }        // disjunction WITH witnessed branches
        | StateConstraint::CountGe { .. }           // set-exhibit witness + BLAKE3 commitment
        | StateConstraint::Custom { .. }            // DSL runtime expression table
        => return None,
    })
}

/// Encode an `ElemPredAtom` token run (`Dregg2.Exec.DeployedConstraint.parseElemPred`).
fn encode_elem_pred(p: &ElemPredAtom) -> Option<String> {
    Some(match p {
        ElemPredAtom::FieldEquals { offset, value } => format!("EEQ {offset} {}", hex32(value)),
        ElemPredAtom::FieldGte { offset, value } => format!("EGE {offset} {}", hex32(value)),
        ElemPredAtom::FieldLte { offset, value } => format!("ELE {offset} {}", hex32(value)),
        ElemPredAtom::FieldInSet { offset, set } => encode_u64_list(&format!("EIN {offset}"), set)?,
    })
}

/// Encode a `CollPred` token run (`Dregg2.Exec.DeployedConstraint.parseCollPred`).
fn encode_coll_pred(q: &CollPred) -> Option<String> {
    Some(match q {
        CollPred::CountSatGe { m, p } => format!("PCNT {m} {}", encode_elem_pred(p)?),
        CollPred::SumOfLe { offset, bound } => format!("PSLE {offset} {bound}"),
        CollPred::SumOfGe { offset, bound } => format!("PSGE {offset} {bound}"),
        CollPred::AllMembers { p } => format!("PALL {}", encode_elem_pred(p)?),
        CollPred::ExistsMember { p } => format!("PEX {}", encode_elem_pred(p)?),
        CollPred::MOfNDistinct {
            m,
            key_offset,
            approved,
        } => format!("PMN {m} {key_offset} {}", encode_elem_pred(approved)?),
    })
}

/// Resolve the RESOLVED CELL RUN this constraint needs — the row-major `Option<FieldElement>`
/// vector the Lean aggregate arms read. Rust does the KEY RESOLUTION only; the truncation and the
/// aggregate live in `Dregg2.Exec.DeployedConstraint`.
///
/// `Some(vec![])` for every arm that reads no cells; `None` = outside the marshalling envelope
/// (the caller declines the whole constraint and the Rust evaluator runs).
fn resolve_cells(c: &StateConstraint, new_state: &CellState) -> Option<Vec<Option<FieldElement>>> {
    Some(match c {
        StateConstraint::FieldsCountEquals { keys, .. } => {
            if keys.len() > MAX_LIST {
                return None;
            }
            keys.iter().map(|k| new_state.get_field_ext(*k)).collect()
        }
        StateConstraint::CollectionAggregate {
            collection_id,
            stride,
            fuel,
            pred,
        } => {
            let n = coll_cell_count(*stride, *fuel, pred.anchor_offset())?;
            // `read_collection` reads `get_heap(collection_id, key as u32)`; a key past the u32
            // lane cannot be present (the deployed `u32::try_from(key).ok()`).
            (0..n)
                .map(|j| {
                    u32::try_from(j)
                        .ok()
                        .and_then(|k| new_state.get_heap(*collection_id, k))
                })
                .collect()
        }
        StateConstraint::FieldsCollectionAggregate {
            base,
            stride,
            fuel,
            pred,
        } => {
            let n = coll_cell_count(*stride, *fuel, pred.anchor_offset())?;
            // `read_collection_fields` reads `get_field_ext(base + j)`; decline rather than wrap.
            base.checked_add(n)?;
            (0..n).map(|j| new_state.get_field_ext(base + j)).collect()
        }
        _ => Vec::new(),
    })
}

/// Encode `AnyOf` / `AllOf` branches: `<TAG> n (N0|N1 <base-run>)*n`.
///
/// Each branch carries the PEELED `Not` parity (`N1` = negated) and the `Not`-free atom under it —
/// exactly the reduction `eval.rs::evaluate_simple_constraint` performs before `lift_simple`.
/// A branch whose atom is outside the Lean-evaluated subset declines the WHOLE combinator (the
/// caller then evaluates it in Rust), so a combinator never half-routes.
fn encode_branches(tag: &str, variants: &[SimpleStateConstraint]) -> Option<String> {
    if variants.len() > MAX_LIST {
        return None;
    }
    let mut s = format!("{tag} {}", variants.len());
    for v in variants {
        // Peel the negation chain to its parity + the `Not`-free atom (eval.rs:2691).
        let mut atom = v;
        let mut negated = false;
        while let SimpleStateConstraint::Not(inner) = atom {
            negated = !negated;
            atom = inner.as_ref();
        }
        let lifted = lift_simple(atom)?;
        // A HeapField branch would need a per-branch heap slot on the wire (the header carries one
        // key pair); decline rather than resolve the wrong key.
        if matches!(lifted, StateConstraint::HeapField { .. }) {
            return None;
        }
        let run = encode_constraint(&lifted)?;
        s.push(' ');
        s.push_str(if negated { "N1" } else { "N0" });
        s.push(' ');
        s.push_str(&run);
    }
    Some(s)
}

/// The marshaller's twin of `eval.rs::lift_simple`: a `Not`-free `SimpleStateConstraint` lifted into
/// the full enum so ONE encoder handles both surfaces. `None` for the variants the lift cannot serve
/// here (`Not`, which the caller has already peeled).
fn lift_simple(s: &SimpleStateConstraint) -> Option<StateConstraint> {
    Some(match s {
        SimpleStateConstraint::FieldEquals { index, value } => StateConstraint::FieldEquals {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::FieldGte { index, value } => StateConstraint::FieldGte {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::FieldLte { index, value } => StateConstraint::FieldLte {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::WriteOnce { index } => StateConstraint::WriteOnce { index: *index },
        SimpleStateConstraint::Immutable { index } => StateConstraint::Immutable { index: *index },
        SimpleStateConstraint::Monotonic { index } => StateConstraint::Monotonic { index: *index },
        SimpleStateConstraint::StrictMonotonic { index } => {
            StateConstraint::StrictMonotonic { index: *index }
        }
        SimpleStateConstraint::BoundedBy {
            index,
            witness_index,
        } => StateConstraint::BoundedBy {
            index: *index,
            witness_index: *witness_index,
        },
        SimpleStateConstraint::FieldGteHeight { index, offset } => {
            StateConstraint::FieldGteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::FieldLteHeight { index, offset } => {
            StateConstraint::FieldLteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::TemporalGate {
            not_before,
            not_after,
        } => StateConstraint::TemporalGate {
            not_before: *not_before,
            not_after: *not_after,
        },
        SimpleStateConstraint::SenderIs { pk } => StateConstraint::SenderIs { pk: *pk },
        SimpleStateConstraint::SenderInSlot { index } => {
            StateConstraint::SenderInSlot { index: *index }
        }
        SimpleStateConstraint::BalanceGte { min } => StateConstraint::BalanceGte { min: *min },
        SimpleStateConstraint::BalanceLte { max } => StateConstraint::BalanceLte { max: *max },
        SimpleStateConstraint::HeapField { key, atom } => StateConstraint::HeapField {
            key: *key,
            atom: atom.clone(),
        },
        SimpleStateConstraint::DelegationEpochEquals { index } => {
            StateConstraint::DelegationEpochEquals { index: *index }
        }
        SimpleStateConstraint::SenderMemberOf { members } => StateConstraint::SenderMemberOf {
            members: members.clone(),
        },
        SimpleStateConstraint::BalanceDeltaLte { max } => {
            StateConstraint::BalanceDeltaLte { max: *max }
        }
        SimpleStateConstraint::BalanceDeltaGte { min } => {
            StateConstraint::BalanceDeltaGte { min: *min }
        }
        // Trusted-Rust branches (crypto / witness) and the already-peeled `Not`: decline the whole
        // combinator rather than half-route it.
        SimpleStateConstraint::PreimageGate { .. }
        | SimpleStateConstraint::CountGe { .. }
        | SimpleStateConstraint::Not(_) => return None,
    })
}

fn encode_heap_atom(a: &HeapAtom) -> Option<String> {
    Some(match a {
        HeapAtom::Equals { value } => format!("HEQ {}", hex32(value)),
        HeapAtom::Gte { value } => format!("HGE {}", hex32(value)),
        HeapAtom::Lte { value } => format!("HLE {}", hex32(value)),
        HeapAtom::MemberOf { set } => encode_u64_list("HMEM", set)?,
        HeapAtom::InRangeTwoSided { lo, hi } => format!("HRANGE {lo} {hi}"),
        HeapAtom::Immutable => "HIM".to_string(),
        HeapAtom::WriteOnce => "HWO".to_string(),
        HeapAtom::Monotonic => "HMON".to_string(),
        HeapAtom::StrictMonotonic => "HSMON".to_string(),
        HeapAtom::DeltaBounded { d } => format!("HDB {d}"),
        HeapAtom::DeltaEquals { d } => format!("HDE {d}"),
        // ⚠ DECLINE, LOUDLY AND ON PURPOSE — the wire has no token for this atom yet.
        //
        // `HeapAtom::AllowedTransitions` is the deployed twin of the Lean-authored
        // `Dregg2.Games.Dungeon.Prog.HeapAtom.allowedTransitions` (the descent's per-relic custody
        // hop table). Lean's own lowering sends it to the NAME-keyed
        // `Dregg2.Exec.StateConstraint.allowedTransitions`, which the deployed wire narrows to a
        // REGISTER index: `Dregg2/Exec/DeployedConstraint.lean`'s `allowedTransitions (index : Nat)`
        // answers `.badIndex` for any `idx ≥ stateSlots`, and its heap vocabulary `DHeapAtom` has
        // eleven arms — exactly `cell::HeapAtom`'s previous eleven — and no transition table.
        //
        // So there is no encoding that the verified decider would read correctly, and inventing one
        // here would be a Rust-authored constraint wearing a Lean tag. `None` routes to
        // `ConstraintOracleUnavailable`, i.e. FAIL CLOSED on a native release build — the correct
        // disposition for a Lean-subset constraint the verified evaluator did not decide.
        //
        // What it costs, stated where it is paid: on a native RELEASE build the Descent's custody
        // teeth refuse. Debug (every test build in this repo) takes `eval.rs`'s guest-path evaluator
        // and plays. Closing it is a `DHeapAtom` arm + a `parseHeapAtom` token, in `metatheory/`.
        // `cell/tests/heap_allowed_transitions_lean_sourced.rs` measures the gap from the Rust side.
        HeapAtom::AllowedTransitions { .. } => return None,
    })
}

/// Emit an `Option<FieldElement>` as the wire's `present(0|1) value(hex)` pair.
fn opt_field(f: &Option<FieldElement>) -> String {
    match f {
        Some(x) => format!("1 {}", hex32(x)),
        None => "0 0".to_string(),
    }
}

/// Build the full admission wire, or `None` if the constraint is outside the Lean-evaluated subset.
///
/// Header (17 tokens), then 16 old registers, 16 new registers, the RESOLVED CELL RUN, then the
/// constraint:
///
/// ```text
/// oldPresent nonce  hoP hoV hnP hnV hxP hxV  oldBal newBal
/// ctxP height sndP sender epP epoch  epochCount
/// R0..R15  N0..N15  <ncells> (present value)*ncells  <TAG> args…
/// ```
///
/// — matches `Dregg2.Exec.DeployedConstraint.parse` / `parseHeader` / `parseCells`.
///
/// ⚑ CONTEXT MARSHALLING, FAIL-CLOSED. Exactly FOUR context fields cross the wire:
/// `block_height`, `sender`, `delegation_epoch`, `sender_epoch_count`. Each carries an explicit
/// presence bit (the count rides `ctxPresent` — it is a plain `u64` field of [`EvalContext`], not an
/// `Option`), and the Lean evaluator turns an absent one into the deployed `MissingContextField`
/// verdict — the same refusal `eval.rs` raises. Nothing else from `EvalContext` is marshalled
/// (`timestamp`, `current_epoch`, `revealed_preimage`): the arms that read those (`PreimageGate`) are
/// in the trusted-Rust slot and are declined above, so the wire never carries a HALF context that
/// could admit on a stale field.
fn build_wire(
    c: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    meta: &TransitionMeta,
) -> Option<String> {
    let ctok = encode_constraint(c)?;
    let cells = resolve_cells(c, new_state)?;

    // Heap old/new options — only the heap-keyed arms read them; everything else emits absent.
    // `HeapFieldLteOther` reads TWO POST-state keys, carried as (heapNew, heapOther).
    let (heap_old, heap_new, heap_other) = match c {
        StateConstraint::HeapField { key, .. } => (
            old_state.and_then(|s| s.get_field_ext(*key)),
            new_state.get_field_ext(*key),
            None,
        ),
        StateConstraint::HeapFieldLteOther { key, other_key, .. } => (
            None,
            new_state.get_field_ext(*key),
            new_state.get_field_ext(*other_key),
        ),
        _ => (None, None, None),
    };

    let (ctx_present, height) = match ctx {
        Some(c) => (1u8, c.block_height),
        None => (0u8, 0),
    };
    let sender = ctx.and_then(|c| c.sender);
    let (epoch_present, epoch) = match meta.delegation_epoch {
        Some(e) => (1u8, e),
        None => (0u8, 0),
    };

    let epoch_count = ctx.map(|c| c.sender_epoch_count).unwrap_or(0);

    let mut wire = format!(
        "{} {} {} {} {} {} {} {} {} {} {} {} {} {}",
        old_state.is_some() as u8,
        new_state.nonce(),
        opt_field(&heap_old),
        opt_field(&heap_new),
        opt_field(&heap_other),
        old_state.map(|s| s.balance()).unwrap_or(0),
        new_state.balance(),
        ctx_present,
        height,
        u8::from(sender.is_some()),
        sender.map(|s| hex32(&s)).unwrap_or_else(|| "0".to_string()),
        epoch_present,
        epoch,
        epoch_count,
    );
    // 16 old regs (zeros if old absent — the `oldPresent` flag tells Lean not to read them).
    for i in 0..16 {
        wire.push(' ');
        match old_state {
            Some(s) => wire.push_str(&hex32(&s.fields[i])),
            None => wire.push('0'),
        }
    }
    // 16 new regs.
    for i in 0..16 {
        wire.push(' ');
        wire.push_str(&hex32(&new_state.fields[i]));
    }
    // The RESOLVED cell run: `<n>` then n × `present(0|1) value(hex)`.
    wire.push(' ');
    wire.push_str(&cells.len().to_string());
    for cell in &cells {
        wire.push(' ');
        wire.push_str(&opt_field(cell));
    }
    wire.push(' ');
    wire.push_str(&ctok);
    Some(wire)
}

/// The `&'static str` behind each Lean `missingContext` code (`DeployedConstraint.ctx*`).
fn ctx_field_name(code: &str) -> Option<&'static str> {
    match code {
        "0" => Some("block_height"),
        "1" => Some("sender"),
        "2" => Some("delegation_epoch"),
        "3" => Some("sender_epoch_count"),
        _ => None,
    }
}

/// Parse the Lean verdict (`"0"`/`"1"`/`"2 <idx>"`/`"3 <idx>"`/`"4 <code>"`) into a deployed
/// `ProgramError`.
fn decode_verdict(out: &str, c: &StateConstraint) -> Option<Result<(), ProgramError>> {
    let mut it = out.split_whitespace();
    match it.next()? {
        "0" => Some(Ok(())),
        "1" => Some(Err(ProgramError::ConstraintViolated {
            constraint: c.clone(),
            description: "refused by the verified Lean deployed-constraint evaluator".to_string(),
        })),
        "2" => {
            let index: u8 = it.next()?.parse().ok()?;
            Some(Err(ProgramError::TransitionCheckRequiresOldState {
                constraint: c.clone(),
                index,
            }))
        }
        "3" => {
            let index: u8 = it.next()?.parse().ok()?;
            Some(Err(ProgramError::InvalidFieldIndex { index }))
        }
        "4" => {
            let field = ctx_field_name(it.next()?)?;
            Some(Err(ProgramError::MissingContextField { field }))
        }
        // The two EXECUTOR-ONLY sentinels. Their payloads are re-attached FROM THE CONSTRAINT (the
        // Lean verdict carries only the kind), so a `CellId` never needs a wire encoding. A verdict
        // that does not match the constraint's shape falls through to Rust rather than fabricating
        // a payload.
        "5" => match c {
            StateConstraint::CapabilityUniqueness { cap_set_root_slot } => {
                Some(Err(ProgramError::CapabilityUniquenessRequiresExecutor {
                    cap_set_root_slot: *cap_set_root_slot,
                }))
            }
            _ => None,
        },
        "6" => match c {
            StateConstraint::BoundDelta { peer_cell, .. } => {
                Some(Err(ProgramError::BoundDeltaNotWired {
                    peer_cell: *peer_cell,
                }))
            }
            _ => None,
        },
        // A malformed verdict (never expected from the linked, `#guard`-teethed evaluator) falls
        // through to the Rust guest-path evaluator — sound because it is differentially equal.
        _ => None,
    }
}

/// The deployed-node backend: routes the Lean-evaluated subset through the verified Lean evaluator.
pub struct LeanConstraintOracle;

impl ConstraintOracle for LeanConstraintOracle {
    fn admits(
        &self,
        constraint: &StateConstraint,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
        meta: &TransitionMeta,
    ) -> Option<Result<(), ProgramError>> {
        let wire = build_wire(constraint, new_state, old_state, ctx, meta)?;
        match dregg_lean_ffi::shadow_constraint_admits(&wire) {
            Ok(out) => decode_verdict(&out, constraint),
            // FFI unavailable/failed (not expected once installed) ⇒ fall through to Rust (sound:
            // the Rust guest-path evaluator is differentially equal on the subset).
            Err(_) => None,
        }
    }
}

/// Install the Lean-backed constraint oracle into `dregg_cell` (call once at native node startup,
/// only when the archive exports `dregg_constraint_admits`). After this, the deployed executor's
/// admission for the Lean-evaluated subset is computed by the PROVEN Lean `admitsTop`.
pub fn register_constraint_oracle() -> bool {
    if !dregg_lean_ffi::constraint_admits_available() {
        return false;
    }
    dregg_cell::program::install_constraint_oracle(Box::new(LeanConstraintOracle)).is_ok()
}
