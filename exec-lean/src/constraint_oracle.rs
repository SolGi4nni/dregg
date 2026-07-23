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
//! asserts, for EVERY encoded arm, both an ADMIT case and a REFUSE case agreeing with the Rust
//! evaluator. A drifted tag makes the Lean parse fail closed (`"1"` = violated), which contradicts
//! the arm's ADMIT case — so any tag/arity divergence turns that test red.

use dregg_cell::preconditions::EvalContext;
use dregg_cell::program::{
    ConstraintOracle, HeapAtom, ProgramError, SimpleStateConstraint, StateConstraint,
    TransitionMeta,
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
// The Lean evaluator computes over unbounded `Nat`/`Int`; the deployed Rust computes the affine
// sums in `i128`. Inside these envelopes the `i128` arithmetic cannot overflow, so the two agree
// EXACTLY. Outside them the marshaller DECLINES (returns `None`) and the Rust evaluator runs —
// no silent disagreement, no wrapped-sum admit.

/// Maximum affine terms marshalled. `1024 · 2^32 · 2^64 = 2^106 < i128::MAX`.
const MAX_AFFINE_TERMS: usize = 1024;
/// Maximum absolute affine coefficient marshalled (see [`MAX_AFFINE_TERMS`]).
const MAX_AFFINE_COEFF: i64 = 1 << 32;
/// Maximum length of any marshalled list (allowlists, edge sets, transition tables, member sets).
/// Bounds the wire so a pathological program cannot turn one admission into a megabyte of tokens.
const MAX_LIST: usize = 4096;

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

        // ══ THE BOOLEAN COMBINATORS (over Lean-evaluated simple branches) ════════════════════════
        StateConstraint::AnyOf { variants } => encode_branches("ANY", variants)?,
        StateConstraint::AllOf { variants } => encode_branches("ALL", variants)?,

        // ══ ── TRUSTED RUST SLOT ── (class (c)) ══════════════════════════════════════════════════
        //
        // EXPLICITLY carved out, by name, with the reason. Each stays in the hand-written Rust
        // evaluator (`cell/src/program/eval.rs`) and is therefore UNVERIFIED — this list IS the
        // honest statement of what the reality-gate does NOT yet cover.
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
        // ── executor-held state the evaluator cannot see ──
        | StateConstraint::RateLimit { .. }         // per-(cell,sender,epoch) executor counter
        | StateConstraint::RateLimitBySum { .. }    // per-(cell,slot,window) executor running sum
        | StateConstraint::CapabilityUniqueness { .. } // needs the real CapabilitySet, not slots
        | StateConstraint::BoundDelta { .. }        // needs PEER-cell state (γ.2 cross-cell loop)
        // ── heap SHAPES not yet on the wire (tractable; the next widening) ──
        | StateConstraint::FieldsCountEquals { .. } // N-key heap census
        | StateConstraint::CollectionAggregate { .. } // strided heap collection + CollPred
        | StateConstraint::FieldsCollectionAggregate { .. } // strided fields-map collection
        => return None,
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
/// Header (16 tokens), then 16 old registers, 16 new registers, then the constraint:
///
/// ```text
/// oldPresent nonce  hoP hoV hnP hnV hxP hxV  oldBal newBal  ctxP height sndP sender epP epoch
/// ```
///
/// — matches `Dregg2.Exec.DeployedConstraint.parse` / `parseHeader`.
///
/// ⚑ CONTEXT MARSHALLING, FAIL-CLOSED. Exactly three context fields cross the wire:
/// `block_height`, `sender`, `delegation_epoch`. Each carries an explicit presence bit, and the Lean
/// evaluator turns an absent one into the deployed `MissingContextField` verdict — the same refusal
/// `eval.rs` raises. Nothing else from `EvalContext` is marshalled (`timestamp`, `current_epoch`,
/// `sender_epoch_count`, `revealed_preimage`): the arms that read those are in the trusted-Rust slot
/// and are declined above, so the wire never carries a HALF context that could admit on a stale field.
fn build_wire(
    c: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    meta: &TransitionMeta,
) -> Option<String> {
    let ctok = encode_constraint(c)?;

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

    let mut wire = format!(
        "{} {} {} {} {} {} {} {} {} {} {} {} {}",
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
