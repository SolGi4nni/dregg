//! marshal_conformance.rs — THE TRANSLATION-VALIDATION GATE (Klein CRITICAL-2, the Rust half).
//!
//! # What this anchors
//!
//! The Lean half of CRITICAL-2 (`metatheory/Dregg2/Exec/FFI/Refine.lean`) proves the
//! `@[export] dregg_exec_full_forest_auth` String→String body refines the gated model with the
//! wire codec (`parseWWire`/`encodeWWire`/`encodeWStatusOut`) INSIDE the proof, and
//! `Dregg2.Exec.CodecRoundtrip` proves `parseWWire ∘ encodeWWire = id`. So on the LEAN side the
//! codec is out of the TCB and `encodeWWire`/`encodeWStatusOut` are the PROVED reference encoders.
//!
//! The remaining TCB limb is the hand-written Rust marshaller (`marshal.rs`): `marshal_turn_hosted`
//! (the T8 encoder) and `unmarshal_result` (the T9 decoder). Until now it was upheld ONLY by a
//! round-trip differential (`marshal_roundtrip.rs`) that checks the Rust against ITSELF (encode then
//! feed the live parser), plus ONE hard-coded golden string. That is a weak stand-in for the real
//! obligation, which is *translation-validation*: that the Rust marshaller equals the LEAN codec
//! (`marshal_turn_hosted = encodeWWire ∘ lift`, `unmarshal_result = decode`).
//!
//! This harness closes that: it compares the Rust marshaller against a Lean-EMITTED GOLDEN CORPUS —
//! the proved `encodeWWire`/`encodeWStatusOut` applied to a shape-covering set of turns, captured
//! by `metatheory/EmitMarshalGolden.lean` and committed at `goldens/marshal-golden.txt`. For every
//! case it asserts:
//!
//!   * T8 ENCODE conformance: `marshal_turn_hosted(host, state, turn)` reproduces the Lean `IN`
//!     wire BYTE-FOR-BYTE (the Rust encoder's bytes == the proved Lean encoder's bytes);
//!   * T9 DECODE conformance: `unmarshal_result(out_wire)` decodes every Lean `OUT` wire to the
//!     expected `(committed, loglen, status)` (or the `MalformedWireSentinel` error for the empty
//!     sentinel) — the Rust decoder inverts the proved OUTPUT encoder;
//!   * NO DRIFT: the Rust corpus (`conformance_input_corpus`/`conformance_output_expectations`) and
//!     the Lean golden cover EXACTLY the same set of `<name>`s — a case present on one side only is
//!     a hard failure (so the two corpora cannot silently diverge).
//!
//! # Why this is a `#[test]`, not a bin
//!
//! Unlike `marshal_roundtrip.rs` (which calls the LIVE Lean kernel via FFI and so must be a bin that
//! one-time-inits the Lean runtime), this harness needs NO Lean runtime at run time: it compares the
//! Rust encoder's output against the COMMITTED Lean golden *string*. It therefore runs in plain
//! `cargo test -p dregg-lean-ffi` with no archive link — strictly cheaper and CI-friendlier.
//!
//! # Refreshing the golden
//!
//! The golden is regenerated from the verified Lean spec (NOT hand-edited):
//!   `cd metatheory && lake env lean --run EmitMarshalGolden.lean > ../dregg-lean-ffi/goldens/marshal-golden.txt`
//! If a wire-grammar change makes this test fail, regenerate the golden and re-run; a diff here means
//! the Rust marshaller and the proved Lean codec disagree on bytes (a real seam bug), OR the grammar
//! moved and the golden is stale.

#[path = "marshal.rs"]
mod marshal;

use marshal::*;

/// The Lean-emitted golden corpus (proved `encodeWWire`/`encodeWStatusOut` over the shape-covering
/// set), committed verbatim. Each line is `IN\t<name>\t<wire>` or `OUT\t<name>\t<wire>`.
const GOLDEN: &str = include_str!("../goldens/marshal-golden.txt");

/// Parse the golden into `(kind, name, wire)` triples (kind = "IN" | "OUT").
fn parse_golden() -> Vec<(String, String, String)> {
    GOLDEN
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let mut it = l.splitn(3, '\t');
            let kind = it.next().expect("golden line missing kind").to_string();
            let name = it.next().expect("golden line missing name").to_string();
            let wire = it.next().expect("golden line missing wire").to_string();
            (kind, name, wire)
        })
        .collect()
}

/// Index the golden `IN`/`OUT` lines by name (asserting no duplicate names within a kind).
fn golden_index(kind: &str) -> std::collections::BTreeMap<String, String> {
    let mut m = std::collections::BTreeMap::new();
    for (k, name, wire) in parse_golden() {
        if k == kind {
            assert!(
                m.insert(name.clone(), wire).is_none(),
                "duplicate golden {kind} name `{name}`"
            );
        }
    }
    assert!(
        !m.is_empty(),
        "golden has no `{kind}` lines — is goldens/marshal-golden.txt populated?"
    );
    m
}

/// Show the first byte where two strings differ (for a precise failure message).
fn first_diff(got: &str, want: &str) -> String {
    let (a, b) = (got.as_bytes(), want.as_bytes());
    let n = a.len().min(b.len());
    let at = (0..n).find(|&k| a[k] != b[k]).unwrap_or(n);
    let lo = at.saturating_sub(24);
    format!(
        "first diff at byte {at} (got len {}, want len {}):\n   got: …{}\n  want: …{}",
        a.len(),
        b.len(),
        &got[lo..(at + 24).min(got.len())],
        &want[lo..(at + 24).min(want.len())]
    )
}

// =============================================================================
// T8 ENCODE — every Rust `marshal_turn_hosted` output == the proved Lean `IN` wire.
// =============================================================================
#[test]
fn t8_encode_matches_lean_golden_byte_for_byte() {
    let golden = golden_index("IN");
    let corpus = conformance_input_corpus();

    // NO DRIFT: the Rust corpus names == the golden `IN` names (exactly).
    let rust_names: std::collections::BTreeSet<String> =
        corpus.iter().map(|(n, ..)| n.clone()).collect();
    let golden_names: std::collections::BTreeSet<String> = golden.keys().cloned().collect();
    assert_eq!(
        rust_names,
        golden_names,
        "Rust IN corpus and Lean golden cover different case names (drift!):\n  \
         in Rust only: {:?}\n  in golden only: {:?}",
        rust_names.difference(&golden_names).collect::<Vec<_>>(),
        golden_names.difference(&rust_names).collect::<Vec<_>>(),
    );

    let mut checked = 0usize;
    for (name, host, state, turn) in &corpus {
        let want = golden
            .get(name)
            .unwrap_or_else(|| panic!("no golden IN wire for `{name}`"));
        let got = marshal_turn_hosted(host, state, turn)
            .unwrap_or_else(|e| panic!("marshal_turn_hosted errored on `{name}`: {e}"));
        assert_eq!(
            &got,
            want,
            "T8 BYTE MISMATCH on `{name}` — the Rust marshaller diverges from the PROVED Lean \
             encodeWWire:\n  {}",
            first_diff(&got, want)
        );
        checked += 1;
    }
    assert_eq!(checked, golden.len(), "did not check every golden IN case");
    eprintln!(
        "T8 conformance: {checked} cases reproduce the proved Lean encodeWWire byte-for-byte \
         (12 auth variants + 30 action arms + deep forest + 11-field state + escaped values + \
         signed fields + populated host)."
    );
}

// =============================================================================
// T9 DECODE — every proved Lean `OUT` wire decodes to the expected struct.
// =============================================================================
#[test]
fn t9_decode_inverts_lean_output_encoder() {
    let golden = golden_index("OUT");
    let expectations = conformance_output_expectations();

    // NO DRIFT: the Rust output-expectation names == the golden `OUT` names.
    let rust_names: std::collections::BTreeSet<String> =
        expectations.iter().map(|e| e.name.to_string()).collect();
    let golden_names: std::collections::BTreeSet<String> = golden.keys().cloned().collect();
    assert_eq!(
        rust_names,
        golden_names,
        "Rust OUT expectations and Lean golden cover different names (drift!):\n  \
         in Rust only: {:?}\n  in golden only: {:?}",
        rust_names.difference(&golden_names).collect::<Vec<_>>(),
        golden_names.difference(&rust_names).collect::<Vec<_>>(),
    );

    for exp in &expectations {
        let wire = golden
            .get(exp.name)
            .unwrap_or_else(|| panic!("no golden OUT wire for `{}`", exp.name));
        match unmarshal_result(wire) {
            Ok(res) => {
                assert!(
                    !exp.is_sentinel,
                    "`{}`: expected the malformed-wire sentinel ERROR but decode succeeded",
                    exp.name
                );
                assert_eq!(
                    res.committed, exp.committed,
                    "`{}`: committed bit",
                    exp.name
                );
                assert_eq!(res.loglen, exp.loglen, "`{}`: loglen", exp.name);
                assert_eq!(res.status, exp.status, "`{}`: status code", exp.name);
            }
            Err(UnmarshalError::MalformedWireSentinel) => {
                assert!(
                    exp.is_sentinel,
                    "`{}`: unexpected MalformedWireSentinel (this is a real OUTPUT wire, not the sentinel)",
                    exp.name
                );
            }
            Err(e) => panic!("`{}`: unmarshal_result errored unexpectedly: {e}", exp.name),
        }
    }
    eprintln!(
        "T9 conformance: {} OUT wires (status 0/1/2 + the empty sentinel) decode to the expected \
         result — the Rust decoder inverts the proved Lean encodeWStatusOut.",
        expectations.len()
    );
}

// =============================================================================
// ROUND-TRIP CLOSURE — for the INPUT goldens, decoding via the OUTPUT grammar is a separate
// concern; here we additionally pin that the Rust T8 encoder is DETERMINISTIC and total over the
// whole corpus (no case errors), and that re-encoding is idempotent (catches accidental
// nondeterminism, e.g. hashmap iteration, that a single-golden check would miss).
// =============================================================================
#[test]
fn t8_encode_is_total_and_deterministic() {
    for (name, host, state, turn) in conformance_input_corpus() {
        let a = marshal_turn_hosted(&host, &state, &turn)
            .unwrap_or_else(|e| panic!("`{name}`: marshal errored: {e}"));
        let b = marshal_turn_hosted(&host, &state, &turn)
            .unwrap_or_else(|e| panic!("`{name}`: marshal errored (2nd): {e}"));
        assert_eq!(a, b, "`{name}`: marshal_turn_hosted is nondeterministic");
    }
}
