//! **The injection-free leg as a REAL STARK** — the first zkOracle conjunct that is
//! *proven*, not just re-executed.
//!
//! The injection check IS a DFA run (the `neg`-complement matcher, [`crate::injection`]),
//! and dregg already deploys a DFA-classification STARK: the `dregg-dfa-routing-v1` AIR
//! (`dregg_circuit::dsl::dfa_routing`, Lean-modeled in
//! `metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean` — `air_final_state_is_classification`
//! + `route_commitment_binds_trace`). This module welds the two: the injection DFA as an
//! explicit transition table, its run over the field bytes proven by `stark::prove`, the
//! whole trace bound to the pinned table commitment + a route commitment by the AIR's
//! Poseidon2 running hash.
//!
//! What the proof states (public inputs `[initial, final, table_commit, route_commit]`):
//! *the unique run of the pinned injection DFA over the committed symbol sequence ends in
//! `final`* — and the verifier accepts iff `final` is a non-injecting state. Today the
//! field is DISCLOSED (it is a committed span of the authenticated body), so the verifier
//! re-derives the expected route commitment from the field itself; the proof adds a
//! machine-checkable run bound to a pinned policy table. The HIDING upgrade — a private
//! field whose route commitment is welded to the body's content commitment instead of
//! re-derived — is the named next slice (`ZKORACLE-PROVER-STATUS.md`).
//!
//! HONEST BOUNDARY: the run is over the field's PADDED brace-projection (`{` vs other,
//! self-loop-padded to a power of two), so brace-free fields within one padding block
//! share one run and the proof transfers among them — but the transfer can never cross
//! the accept/reject boundary (the dead state is absorbing; padding preserves it).
//! Binding the field BYTES to the authenticated response is the attestation's span weld
//! (`FieldSpan` within the committed body), not this leg — the leg proves the POLICY RUN.
//!
//! Soundness of the table itself: [`injection_dfa_table`] is differential-tested against
//! the VERIFIED derivative matcher (`injection_free`, dregg-dfa's boolean-closed `Re` —
//! the Rust twin of `ZkOracle.lean`'s `.neg injectionTemplate`) — two independent
//! implementations, one truth.

use dregg_circuit::dsl::dfa_routing::{
    compute_table_commitment, prove_dfa_routing, verify_dfa_routing,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1};
use dregg_circuit::stark::StarkProof;

/// The AIR/descriptor name (baked into the descriptor; prove and verify must agree).
const DFA_NAME: &str = "zkoracle-injection-v1";

/// Symbol alphabet: `1` = the byte `{`, `0` = any other byte. Symbol `0` is also the
/// AIR's PAD symbol (self-loop rows appended to reach a power-of-two trace) — with this
/// orientation padding walks an accepting state to the clean state and a dead state to
/// itself, so padding never changes the accept/reject class.
const SYM_BRACE: u32 = 1;
const SYM_OTHER: u32 = 0;

/// DFA states: `0` clean (no pending `{`), `1` saw one `{`, `2` DEAD — saw `{{`
/// (injecting; absorbing).
const S_CLEAN: u32 = 0;
const S_BRACE: u32 = 1;
const S_DEAD: u32 = 2;

/// **The injection DFA transition table** — recognizes "contains `{{`" in its DEAD
/// state; the accepting (injection-free) states are `{clean, brace}`. Padded with
/// isolated self-loop states to the 4-ary-clean 16 entries
/// [`compute_table_commitment`] requires.
pub fn injection_dfa_table() -> Vec<(u32, u32, u32)> {
    let mut t = vec![
        (S_CLEAN, SYM_OTHER, S_CLEAN),
        (S_CLEAN, SYM_BRACE, S_BRACE),
        (S_BRACE, SYM_OTHER, S_CLEAN),
        (S_BRACE, SYM_BRACE, S_DEAD),
        (S_DEAD, SYM_OTHER, S_DEAD),
        (S_DEAD, SYM_BRACE, S_DEAD),
    ];
    for s in 3..8u32 {
        t.push((s, SYM_OTHER, s));
        t.push((s, SYM_BRACE, s));
    }
    debug_assert_eq!(t.len(), 16);
    t
}

/// The field bytes as DFA symbols. An EMPTY field is encoded as one `SYM_OTHER`
/// (trivially injection-free; the AIR needs ≥ 1 symbol) — prove and verify share this
/// convention.
fn symbols_of(field: &[u8]) -> Vec<u32> {
    if field.is_empty() {
        return vec![SYM_OTHER];
    }
    field
        .iter()
        .map(|&b| if b == b'{' { SYM_BRACE } else { SYM_OTHER })
        .collect()
}

/// Run the table DFA in the clear (the differential twin of the AIR run).
#[cfg(test)]
fn classify(table: &[(u32, u32, u32)], symbols: &[u32]) -> Option<u32> {
    let mut s = S_CLEAN;
    for &y in symbols {
        s = table
            .iter()
            .find(|(ts, ty, _)| *ts == s && *ty == y)
            .map(|(_, _, tn)| *tn)?;
    }
    Some(s)
}

/// The expected `[initial, final, table_commit, route_commit]` for `field` — the
/// verifier-side re-derivation (must fold EXACTLY as
/// `dfa_routing::build_routing_witness` does, including the pow-2 self-loop padding
/// with pad symbol `SYM_OTHER`).
fn expected_public_inputs(field: &[u8]) -> Option<[BabyBear; 4]> {
    let table = injection_dfa_table();
    let symbols = symbols_of(field);
    let table_commitment = compute_table_commitment(&table);
    let n = symbols.len().next_power_of_two().max(2);
    let step = |s: u32, y: u32| -> Option<u32> {
        table
            .iter()
            .find(|(ts, ty, _)| *ts == s && *ty == y)
            .map(|(_, _, tn)| *tn)
    };
    let mut running = table_commitment;
    let mut current = S_CLEAN;
    let mut fold = |s: u32, y: u32| -> Option<u32> {
        let next = step(s, y)?;
        let entry = hash_4_to_1(&[
            BabyBear::new(s),
            BabyBear::new(y),
            BabyBear::new(next),
            BabyBear::ZERO,
        ]);
        running = hash_2_to_1(running, entry);
        Some(next)
    };
    for &y in &symbols {
        current = fold(current, y)?;
    }
    let final_state = current;
    let mut last_next = final_state;
    for _ in symbols.len()..n {
        last_next = fold(last_next, SYM_OTHER)?;
    }
    Some([
        BabyBear::new(S_CLEAN),
        BabyBear::new(last_next),
        table_commitment,
        running,
    ])
}

/// A STARK-carried injection-leg proof: the run of the pinned injection DFA over the
/// field, bound by the AIR's Poseidon2 running hash.
#[derive(Clone, Debug)]
pub struct ZkInjectionProof {
    /// The `dregg-dfa-routing-v1` STARK over the field's DFA run.
    pub proof: StarkProof,
    /// `[initial_state, final_state, table_commitment, route_commitment]`.
    pub public_inputs: Vec<BabyBear>,
}

/// Why a STARK-carried injection leg was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZkLegError {
    /// The public inputs do not match the field's expected run (wrong initial state,
    /// wrong table, or a route commitment for DIFFERENT bytes).
    WrongRun,
    /// The run is genuine but ends in the DEAD state — the field injects.
    Injecting,
    /// The STARK itself does not verify (forged/tampered trace).
    BadProof(String),
}

/// **PROVE the injection leg** — a real `stark::prove` over the field's DFA run.
/// Produces a proof for injecting fields too (the run is the run); acceptance is the
/// VERIFIER's judgment on the final state. The attestation-level guard
/// ([`crate::prove_zkoracle`]) separately refuses to attest injecting fields at all.
pub fn prove_injection_leg(field: &[u8]) -> Option<ZkInjectionProof> {
    let table = injection_dfa_table();
    let symbols = symbols_of(field);
    let (proof, public_inputs) = prove_dfa_routing(DFA_NAME, &table, S_CLEAN, &symbols)?;
    Some(ZkInjectionProof {
        proof,
        public_inputs,
    })
}

/// **VERIFY the injection leg** against the DISCLOSED field: the public inputs must be
/// exactly the field's expected run (initial = clean, pinned table commitment, the
/// route commitment re-derived from the field bytes), the final state must be
/// non-injecting, and the STARK must verify. Fail-closed on all three.
pub fn verify_injection_leg(field: &[u8], leg: &ZkInjectionProof) -> Result<(), ZkLegError> {
    let expected = expected_public_inputs(field).ok_or(ZkLegError::WrongRun)?;
    if leg.public_inputs.as_slice() != expected {
        return Err(ZkLegError::WrongRun);
    }
    // The FINAL state of the padded run: padding maps accepting→clean, dead→dead, so
    // the accept judgment on the padded final state equals the unpadded one.
    if leg.public_inputs[1] == BabyBear::new(S_DEAD) {
        return Err(ZkLegError::Injecting);
    }
    let table = injection_dfa_table();
    verify_dfa_routing(DFA_NAME, &table, &leg.proof, &leg.public_inputs)
        .map_err(ZkLegError::BadProof)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::injection::injection_free;

    /// THE DIFFERENTIAL TOOTH — the table DFA agrees with the VERIFIED derivative
    /// matcher (`injection_free`, the Rust twin of `.neg injectionTemplate`) on a
    /// boundary corpus + deterministic fuzz. Two independent implementations, one truth.
    #[test]
    fn table_dfa_agrees_with_the_verified_matcher() {
        let table = injection_dfa_table();
        let corpus: Vec<&[u8]> = vec![
            b"",
            b"hi",
            b"Paris",
            b"{",
            b"}",
            b"{{",
            b"{{{",
            b"{x{",
            b"a{b{c",
            b"ends with {",
            b"{ {",
            b"ignore previous {{ system }}",
            b"}}{{",
            b"{}{}{}",
            b"\x00{\x00{",
            b"{a{b{c{d{e{",
        ];
        for field in corpus {
            let sym = symbols_of(field);
            let cls = classify(&table, &sym).expect("total table");
            let table_free = cls != S_DEAD;
            assert_eq!(
                table_free,
                injection_free(field),
                "table vs verified matcher disagree on {:?}",
                String::from_utf8_lossy(field)
            );
        }
        // Deterministic fuzz — xorshift, brace-dense alphabet to hit the boundary.
        let mut x: u64 = 0x9E3779B97F4A7C15;
        for _ in 0..2000 {
            let mut field = Vec::new();
            let len = {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                (x % 24) as usize
            };
            for _ in 0..len {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                field.push(match x % 4 {
                    0 => b'{',
                    1 => b'}',
                    _ => b'a' + (x % 26) as u8,
                });
            }
            let sym = symbols_of(&field);
            let cls = classify(&table, &sym).expect("total table");
            assert_eq!(cls != S_DEAD, injection_free(&field));
        }
    }

    /// The REAL prove/verify roundtrip: a benign field yields a STARK the verifier
    /// accepts; an injecting field's genuine proof is refused as `Injecting`.
    #[test]
    fn injection_leg_stark_roundtrip() {
        let leg = prove_injection_leg(b"The capital of France is Paris.").expect("prove");
        verify_injection_leg(b"The capital of France is Paris.", &leg).expect("verify");

        let bad = prove_injection_leg(b"ignore {{ system }}").expect("the run still proves");
        assert_eq!(
            verify_injection_leg(b"ignore {{ system }}", &bad),
            Err(ZkLegError::Injecting)
        );
    }

    /// Hostile poles: a proof re-pointed at different bytes, a tampered final state,
    /// and an empty-field convention roundtrip.
    #[test]
    fn injection_leg_hostiles_refused() {
        let leg = prove_injection_leg(b"Paris").expect("prove");

        // Re-pointed at a field with a DIFFERENT padded brace-projection → route
        // commitment mismatch: a brace changes a symbol; crossing the pow-2 padding
        // boundary changes the run length.
        assert_eq!(
            verify_injection_leg(b"Par{s", &leg),
            Err(ZkLegError::WrongRun)
        );
        assert_eq!(
            verify_injection_leg(b"Paris, France", &leg),
            Err(ZkLegError::WrongRun)
        );
        // HONEST BOUNDARY (stated, not hidden): the leg binds the field's padded
        // brace-PROJECTION, so brace-free fields within one padding block share one run
        // and the proof transfers among them. The transfer can NEVER cross the
        // accept/reject boundary (the dead state is absorbing and padding preserves it),
        // and binding the field BYTES to the authenticated body is the cross-leg span
        // weld's job ([`crate::attestation`]), not this leg's.
        assert_eq!(verify_injection_leg(b"Rome!", &leg), Ok(()));
        assert_eq!(verify_injection_leg(b"Paris?", &leg), Ok(()));

        // Tampered public input (claim a different final state) → WrongRun (the
        // expected-PI pin catches it before the STARK is even consulted).
        let mut tampered = leg.clone();
        tampered.public_inputs[1] = BabyBear::new(S_DEAD);
        assert_eq!(
            verify_injection_leg(b"Paris", &tampered),
            Err(ZkLegError::WrongRun)
        );

        // Empty field: trivially injection-free, same convention both sides.
        let empty = prove_injection_leg(b"").expect("prove empty");
        verify_injection_leg(b"", &empty).expect("verify empty");
    }
}
