//! Runtime-ingestion gate for the additive, unregistered FNSP-v3 exact-nullifier descriptor.
//!
//! The artifact remains deliberately outside `circuit/descriptors/`: this test does not register
//! a selector, mint a verifier key, update provenance, or make the staged circuit deployable.  It
//! closes the narrower seam that mattered immediately after Lean emission: the exact checked-in
//! bytes decode through the production IR-v2 parser and retain their reviewed geometry and
//! content-addressed identity.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, parse_vm_descriptor2};

const STAGED_JSON: &[u8] = include_bytes!(
    "../staged-descriptors/fnsp-v3/faithful-note-spend-exact-aafi-fns3-rotated-wide-state.json"
);
const EXPECTED_NAME: &str = "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state";
/// ⚑ ROTATED 2026-07-31 with the staged artifact itself. The nine-lane flag day re-emitted the
/// registry copy of this member but not `circuit/staged-descriptors/fnsp-v3/`, so the two diverged
/// at `trace_width` 3804 vs 3760 and this fingerprint went stale by omission. The repair was to
/// re-run the emitter (`lake env lean --run metatheory/EmitExactNullifierAafiRotatedState.lean`)
/// and install its stdout verbatim — the freshly emitted bytes are byte-identical to the registry
/// copy, which is the property `descriptor_by_name`'s promotion tooth asserts.
const EXPECTED_SHA256: &str = "df654baea5a922badb8cd287fda6955d30a931b940f221b80fed284b3b7fbfc5";
const EXPECTED_TABLE_IDS: [usize; 5] = [0, 9, 1, 84, 85];
const EXPECTED_TRACE_WIDTH: usize = 3804;
const EXPECTED_PUBLIC_INPUT_COUNT: usize = 76;
const EXPECTED_CONSTRAINT_COUNT: usize = 1274;

/// The descriptor registry's fingerprint semantics are SHA-256 over the exact Lean-emitted JSON
/// bytes, without JSON normalization.  This is the same self-contained FIPS 180-4 implementation
/// used by `effect_vm_descriptors`' registered-fingerprint gate; keeping it dependency-free avoids
/// changing the circuit crate just to test a staged artifact.
fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a_2f98,
        0x7137_4491,
        0xb5c0_fbcf,
        0xe9b5_dba5,
        0x3956_c25b,
        0x59f1_11f1,
        0x923f_82a4,
        0xab1c_5ed5,
        0xd807_aa98,
        0x1283_5b01,
        0x2431_85be,
        0x550c_7dc3,
        0x72be_5d74,
        0x80de_b1fe,
        0x9bdc_06a7,
        0xc19b_f174,
        0xe49b_69c1,
        0xefbe_4786,
        0x0fc1_9dc6,
        0x240c_a1cc,
        0x2de9_2c6f,
        0x4a74_84aa,
        0x5cb0_a9dc,
        0x76f9_88da,
        0x983e_5152,
        0xa831_c66d,
        0xb003_27c8,
        0xbf59_7fc7,
        0xc6e0_0bf3,
        0xd5a7_9147,
        0x06ca_6351,
        0x1429_2967,
        0x27b7_0a85,
        0x2e1b_2138,
        0x4d2c_6dfc,
        0x5338_0d13,
        0x650a_7354,
        0x766a_0abb,
        0x81c2_c92e,
        0x9272_2c85,
        0xa2bf_e8a1,
        0xa81a_664b,
        0xc24b_8b70,
        0xc76c_51a3,
        0xd192_e819,
        0xd699_0624,
        0xf40e_3585,
        0x106a_a070,
        0x19a4_c116,
        0x1e37_6c08,
        0x2748_774c,
        0x34b0_bcb5,
        0x391c_0cb3,
        0x4ed8_aa4a,
        0x5b9c_ca4f,
        0x682e_6ff3,
        0x748f_82ee,
        0x78a5_636f,
        0x84c8_7814,
        0x8cc7_0208,
        0x90be_fffa,
        0xa450_6ceb,
        0xbef9_a3f7,
        0xc671_78f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09_e667,
        0xbb67_ae85,
        0x3c6e_f372,
        0xa54f_f53a,
        0x510e_527f,
        0x9b05_688c,
        0x1f83_d9ab,
        0x5be0_cd19,
    ];
    let mut msg = data.to_vec();
    let bit_len = (data.len() as u64) * 8;
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in msg.chunks_exact(64) {
        let mut w = [0_u32; 64];
        for (i, word) in w.iter_mut().take(16).enumerate() {
            *word = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
            (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
        for (&round_constant, &word) in K.iter().zip(&w) {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choose = (e & f) ^ ((!e) & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(choose)
                .wrapping_add(round_constant)
                .wrapping_add(word);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(majority);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (state, value) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *state = (*state).wrapping_add(value);
        }
    }

    h.into_iter()
        .flat_map(u32::to_be_bytes)
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// The staged-ingestion contract.  Parsing is delegated to the production IR-v2 parser; this
/// wrapper adds the content/geometry pins that a later registry entry would carry.
fn ingest_staged(bytes: &[u8]) -> Result<EffectVmDescriptor2, String> {
    let fingerprint = sha256_hex(bytes);
    if fingerprint != EXPECTED_SHA256 {
        return Err(format!(
            "staged descriptor fingerprint mismatch: {fingerprint} != {EXPECTED_SHA256}"
        ));
    }
    let json = std::str::from_utf8(bytes)
        .map_err(|error| format!("staged descriptor is not UTF-8: {error}"))?;
    let descriptor = parse_vm_descriptor2(json)?;
    if descriptor.name != EXPECTED_NAME {
        return Err(format!("unexpected descriptor name: {}", descriptor.name));
    }
    if descriptor.trace_width != EXPECTED_TRACE_WIDTH {
        return Err(format!(
            "unexpected trace width: {}",
            descriptor.trace_width
        ));
    }
    if descriptor.public_input_count != EXPECTED_PUBLIC_INPUT_COUNT {
        return Err(format!(
            "unexpected public-input count: {}",
            descriptor.public_input_count
        ));
    }
    if descriptor.constraints.len() != EXPECTED_CONSTRAINT_COUNT {
        return Err(format!(
            "unexpected constraint count: {}",
            descriptor.constraints.len()
        ));
    }
    let table_ids: Vec<_> = descriptor.tables.iter().map(|table| table.id).collect();
    if table_ids != EXPECTED_TABLE_IDS {
        return Err(format!("unexpected table IDs: {table_ids:?}"));
    }
    if !descriptor.hash_sites.is_empty() || !descriptor.ranges.is_empty() {
        return Err("graduated descriptor has non-empty legacy carriers".to_owned());
    }
    Ok(descriptor)
}

#[test]
fn exact_aafi_staged_bytes_ingest_through_production_ir2_parser() {
    // Non-vacuity: independently pin the SHA helper before trusting its descriptor result.
    assert_eq!(
        sha256_hex(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );

    let descriptor = ingest_staged(STAGED_JSON).expect("Lean-emitted staged descriptor ingests");
    assert_eq!(descriptor.name, EXPECTED_NAME);
    assert_eq!(descriptor.trace_width, EXPECTED_TRACE_WIDTH);
    assert_eq!(descriptor.public_input_count, EXPECTED_PUBLIC_INPUT_COUNT);
    assert_eq!(descriptor.constraints.len(), EXPECTED_CONSTRAINT_COUNT);
    assert_eq!(
        descriptor
            .tables
            .iter()
            .map(|table| table.id)
            .collect::<Vec<_>>(),
        EXPECTED_TABLE_IDS
    );
}

#[test]
fn exact_aafi_staged_ingestion_rejects_tamper_and_truncation() {
    let json = std::str::from_utf8(STAGED_JSON).expect("fixture is UTF-8");

    // A parseable one-byte semantic edit still loses the content-addressed descriptor identity.
    let name_tamper = json.replacen("exact-aafi", "exagt-aafi", 1);
    assert!(
        parse_vm_descriptor2(&name_tamper).is_ok(),
        "name edit remains valid IR-v2 syntax, making the fingerprint pin load-bearing"
    );
    let error = ingest_staged(name_tamper.as_bytes()).expect_err("fingerprint tamper must refuse");
    assert!(error.contains("fingerprint mismatch"), "{error}");

    // The production parser itself rejects a version tamper, independent of the outer pin.
    let ir_tamper = json.replacen("\"ir\":2", "\"ir\":3", 1);
    let error = parse_vm_descriptor2(&ir_tamper).expect_err("unknown IR version must refuse");
    assert!(
        error.contains("unsupported descriptor ir version 3"),
        "{error}"
    );

    // Truncated Lean emission is neither accepted by the parser nor by staged ingestion.
    let truncated = &STAGED_JSON[..STAGED_JSON.len() - 1];
    let truncated_json = std::str::from_utf8(truncated).expect("prefix remains UTF-8");
    assert!(parse_vm_descriptor2(truncated_json).is_err());
    assert!(ingest_staged(truncated).is_err());
}
