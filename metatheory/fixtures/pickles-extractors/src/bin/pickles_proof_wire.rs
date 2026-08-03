//! **PICKLES PROOF WIRE — the encoder, and the round-trip that judges it.**
//!
//! ## The gap this closes
//!
//! This tree could DECODE a Pickles proof (`bridge/src/mina_pickles.rs`, `MinaBinprot.lean`,
//! `main.rs`'s `binprot_read`) and could DERIVE a `VerificationKey` a Mina node parses
//! (`pickles-vk-derive`). It could not EMIT a proof object in either wire encoding. This binary
//! does, and it is judged the only way an encoder can honestly be judged: **on real bytes, by
//! byte identity.**
//!
//! ## ⚑ THERE ARE TWO WIRE ENCODINGS AND THEY ARE NOT THE SAME
//!
//! | encoding | what carries it | reader |
//! |---|---|---|
//! | **binprot** | a block's `protocolStateProof`, the p2p wire, a zkApp account update | openmina `binprot_read`, Mina's OCaml `bin_read_t` |
//! | **sexp** (base64'd) | o1js `Proof.toJSON().proof` / `Proof.fromJSON` | `Pickles.proofOfBase64`, i.e. Mina's OCaml sexp reader compiled into o1js |
//!
//! Measured, not assumed: `bridge/mina-zkapp/.fullchain/proof-5.json`'s `proof` field base64-decodes
//! to ASCII `((statement((proof_state((deferred_values((plonk((alpha((inner(8e9c…`. It is an
//! S-expression. It is NOT binprot. An encoder that emits only binprot cannot be handed to o1js,
//! and an encoder that emits only sexp cannot be put on the p2p wire. Both are emitted here.
//!
//! ## ⚑ openmina's own `SexpOf` CANNOT be used for the o1js half, and its round-trip is BROKEN
//!
//! `p2p-messages/src/v2/manual.rs:236-247` — `OfSexp for LimbVectorConstantHex64StableV1` REFUSES
//! any atom whose length is not exactly 16 (`if hex_str.len() != 16 { return Err(...) }`).
//! `manual.rs:262-269` — `SexpOf` for the same type EMITS `format!("0x{:016x}")`, eighteen chars.
//! So `openmina_sexp_of(x)` is not readable by `openmina_of_sexp`, and it does not match Mina,
//! whose own printer emits the bare 16 lowercase hex digits (verified against o1js's proof above:
//! `(beta(eaf9112db9f3d5b8 c65a17708076d06d))`). The sexp printer below is therefore written
//! HERE, against the observed OCaml grammar, not delegated.
//!
//! ## The grammar, pinned against o1js's own emitted proof
//!
//! * record  `((f1 v1)(f2 v2)…)`. ⚑ The separator is sexplib's `to_string_mach` rule, NOT
//!   "join with a space": a space appears only BETWEEN TWO BARE ATOMS. `(ft_eval1 0x1F18…)` has
//!   one; `(branch_data((proofs_verified N1)…`, `(domain_log2"\016")` and `((a)(b))` do not.
//!   See [`glue`] — joining lists with a space still PARSED and was caught only by re-printing.
//! * `BigInt`  `0x` + 64 UPPERCASE hex, BIG-endian  (`bigint.rs:192-205` agrees).
//! * `Hex64`   16 lowercase hex, NO prefix.
//! * `unit`  `()`;  `Option`  `()` for None, `(x)` for Some;  `bool`  `true`/`false`.
//! * `Proofs_verified`  `N0`/`N1`/`N2`;  `Domain_log2` is a CHAR, printed `"\016"` (3-digit decimal).
//! * list/array/vector  `(e1 e2 …)`;  tuple  `(a b)`.
//!
//! ## What it runs
//!
//! For every block fixture given (default: the whole `metatheory/fixtures/mina-blocks/` set plus
//! the 539508 control):
//!
//!   1. base64url → bytes → `PicklesProofProofsVerified2ReprStableV2::binprot_read`, ZERO trailing.
//!   2. `binprot_write` → **compare against the ORIGINAL bytes.** Byte-identical or the offset of
//!      the first difference. This is the encoder's verdict on real data.
//!   3. sexp-print → base64 → written out for `bridge/mina-zkapp/scripts/mina-proof-parse-gate.mjs`,
//!      which hands it to `Pickles.proofOfBase64` — Mina's own reader — and then RE-PRINTS the
//!      parsed object with Mina's own `proofToBase64` and compares. Parsing says well-formed;
//!      the re-print comparison says our printer IS Mina's printer, character for character.
//!   4. **A PROOF OBJECT WE BUILT**, not one we echoed: [`synthetic_proof`] assembles a
//!      `PicklesProofProofsVerified2ReprStableV2` from OUR OWN Pallas points (`g = k·G` for a
//!      counter `k`, so every point is on-curve and none is copied) and our own canonical field
//!      elements, then encodes it BOTH ways and reads it back. Nothing about it verifies — it is
//!      an object of the right SHAPE, which is the stated milestone.
//!
//! ## Scope
//!
//! A parseable proof is not a verifying proof. Nothing here claims the emitted object satisfies
//! any check beyond decoding; §REMAINDER in the report says what is between the two.
//!
//! RUN
//!   cargo run --release --manifest-path metatheory/fixtures/pickles-extractors/Cargo.toml \
//!       --bin pickles_proof_wire -- <out-dir> [fixture.json …]

use std::fmt::Write as _;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use base64::Engine as _;
use mina_curves::pasta::{Fp, Pallas};
use mina_p2p_messages::array::ArrayN16;
use mina_p2p_messages::bigint::BigInt;
use mina_p2p_messages::binprot::BinProtRead;
use mina_p2p_messages::list::List;
use mina_p2p_messages::pseq::PaddedSeq;
use mina_p2p_messages::v2::*;

// ⚑ The two encoders MOVED to `src/wire.rs` (unchanged) so `src/marshal.rs` can emit through the
// same ones these round-trips judge. This file is still where they are JUDGED.
use pickles_reality_gate_export::wire::{binprot_of_proof, sexp_of_proof};

// ───────────────────────────── the gate ─────────────────────────────

#[derive(serde::Deserialize)]
struct Fixture {
    #[serde(default)]
    state_hash: String,
    #[serde(default)]
    blockchain_length: String,
    protocol_state_proof_base64_urlsafe: String,
}

struct Verdict {
    path: String,
    height: String,
    state_hash: String,
    n_bytes: usize,
    trailing: usize,
    identical: bool,
    first_divergence: Option<usize>,
    sexp_len: usize,
    sexp_b64: String,
}

fn first_diff(a: &[u8], b: &[u8]) -> Option<usize> {
    for i in 0..a.len().min(b.len()) {
        if a[i] != b[i] {
            return Some(i);
        }
    }
    if a.len() == b.len() {
        None
    } else {
        Some(a.len().min(b.len()))
    }
}

fn roundtrip(path: &str) -> Verdict {
    let raw = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"));
    let fx: Fixture =
        serde_json::from_str(&raw).unwrap_or_else(|e| panic!("{path} does not parse: {e}"));
    let orig = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(fx.protocol_state_proof_base64_urlsafe.trim_end_matches('='))
        .expect("base64url");

    let mut slice = orig.as_slice();
    let proof = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut slice)
        .unwrap_or_else(|e| panic!("{path}: binprot_read failed: {e}"));
    let trailing = slice.len();

    let re = binprot_of_proof(&proof);
    let identical = re == orig;
    let first_divergence = if identical {
        None
    } else {
        first_diff(&orig, &re)
    };

    // ⚑ The re-encoded bytes must ALSO decode to the same value. Byte identity already implies
    // it here, but when it fails this is what tells us whether we lost information or only
    // re-spelled it.
    let mut s2 = re.as_slice();
    let reparsed = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut s2)
        .expect("our own binprot output decodes");
    assert_eq!(
        reparsed, proof,
        "{path}: our encoding decodes to a DIFFERENT proof"
    );

    let sexp = sexp_of_proof(&proof);
    let sexp_b64 = base64::engine::general_purpose::STANDARD.encode(sexp.as_bytes());

    Verdict {
        path: path.to_string(),
        height: fx.blockchain_length,
        state_hash: fx.state_hash,
        n_bytes: orig.len(),
        trailing,
        identical,
        first_divergence,
        sexp_len: sexp.len(),
        sexp_b64,
    }
}

// ─────────────────────── a proof object WE BUILT ───────────────────────

/// `k·G` on Pallas, as the wire's `(x, y)` pair. Every point in the synthetic proof comes from
/// here, so none is copied from a real proof and all are on-curve.
fn our_point(k: u64) -> (BigInt, BigInt) {
    let g = Pallas::generator();
    let p = (g * mina_curves::pasta::Fq::from(k)).into_affine();
    let (x, y) = p.xy().expect("k*G is not the identity");
    (
        BigInt::from_bytes(x.into_bigint().to_bytes_le().try_into().unwrap()),
        BigInt::from_bytes(y.into_bigint().to_bytes_le().try_into().unwrap()),
    )
}

fn our_fp(k: u64) -> BigInt {
    let v = Fp::from(k) * Fp::from(0x9E3779B97F4A7C15u64) + Fp::from(1u64);
    BigInt::from_bytes(v.into_bigint().to_bytes_le().try_into().unwrap())
}

fn our_hex64(k: u64) -> LimbVectorConstantHex64StableV1 {
    LimbVectorConstantHex64StableV1((k.wrapping_mul(0x9E3779B97F4A7C15) | 1).into())
}

fn our_challenge(
    k: u64,
) -> PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2AChallenge {
    PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2AChallenge {
        inner: PaddedSeq([our_hex64(k), our_hex64(k + 1)]),
    }
}

fn our_bp(k: u64) -> PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2A {
    PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2A {
        prechallenge: our_challenge(k),
    }
}

fn our_evalpair(k: u64) -> (ArrayN16<BigInt>, ArrayN16<BigInt>) {
    (vec![our_fp(k)].into(), vec![our_fp(k + 1)].into())
}

/// **A `Proofs_verified_2`-shaped proof object assembled here, from our own values.** Nothing in
/// it is copied from a real proof. It does not verify and is not claimed to; it exists so the
/// parse gate is answering "can dregg EMIT one", not "can dregg re-emit one it was handed".
fn synthetic_proof() -> PicklesProofProofsVerified2ReprStableV2 {
    let mut ctr = 1u64;
    let mut next = || {
        ctr += 1;
        ctr
    };

    let plonk = PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonk {
        alpha: our_challenge(next()),
        beta: PaddedSeq([our_hex64(next()), our_hex64(next())]),
        gamma: PaddedSeq([our_hex64(next()), our_hex64(next())]),
        zeta: our_challenge(next()),
        // Real Mina block wrap proofs carry NONE here; the o1js proof read in the header carries
        // Some. Emitting None exercises the `()` arm, which is the one a block uses.
        joint_combiner: None,
        feature_flags:
            PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkFeatureFlags {
                range_check0: false,
                range_check1: false,
                foreign_field_add: false,
                foreign_field_mul: false,
                xor: false,
                rot: false,
                lookup: false,
                runtime_tables: false,
            },
    };

    let deferred_values =
        PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValues {
            plonk,
            bulletproof_challenges: PaddedSeq(std::array::from_fn(|i| our_bp(100 + i as u64))),
            branch_data: CompositionTypesBranchDataStableV1 {
                proofs_verified: PicklesBaseProofsVerifiedStableV1::N2,
                domain_log2: CompositionTypesBranchDataDomainLog2StableV1(14u8.into()),
            },
        };

    let proof_state = PicklesProofProofsVerified2ReprStableV2StatementProofState {
        deferred_values,
        sponge_digest_before_evaluations: CompositionTypesDigestConstantStableV1(PaddedSeq(
            std::array::from_fn(|i| our_hex64(200 + i as u64)),
        )),
        messages_for_next_wrap_proof:
            PicklesProofProofsVerified2ReprStableV2MessagesForNextWrapProof {
                challenge_polynomial_commitment: our_point(7),
                old_bulletproof_challenges: PaddedSeq(std::array::from_fn(|j| {
                    PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2(
                        PaddedSeq(std::array::from_fn(|i| our_bp(300 + (j * 15 + i) as u64))),
                    )
                })),
            },
    };

    let messages_for_next_step_proof =
        PicklesProofProofsVerified2ReprStableV2MessagesForNextStepProof {
            app_state: (),
            challenge_polynomial_commitments: (0..2u64)
                .map(|i| our_point(11 + i))
                .collect::<Vec<_>>()
                .into_iter()
                .collect::<List<_>>(),
            old_bulletproof_challenges: (0..2u64)
                .map(|j| PaddedSeq(std::array::from_fn(|i| our_bp(400 + j * 16 + i as u64))))
                .collect::<Vec<_>>()
                .into_iter()
                .collect::<List<_>>(),
        };

    let prev_evals = PicklesProofProofsVerified2ReprStableV2PrevEvals {
        evals: PicklesProofProofsVerified2ReprStableV2PrevEvalsEvals {
            public_input: (our_fp(500), our_fp(501)),
            evals: PicklesProofProofsVerified2ReprStableV2PrevEvalsEvalsEvals {
                w: PaddedSeq(std::array::from_fn(|i| our_evalpair(600 + i as u64 * 2))),
                coefficients: PaddedSeq(std::array::from_fn(|i| our_evalpair(700 + i as u64 * 2))),
                z: our_evalpair(800),
                s: PaddedSeq(std::array::from_fn(|i| our_evalpair(810 + i as u64 * 2))),
                generic_selector: our_evalpair(830),
                poseidon_selector: our_evalpair(832),
                complete_add_selector: our_evalpair(834),
                mul_selector: our_evalpair(836),
                emul_selector: our_evalpair(838),
                endomul_scalar_selector: our_evalpair(840),
                range_check0_selector: None,
                range_check1_selector: None,
                foreign_field_add_selector: None,
                foreign_field_mul_selector: None,
                xor_selector: None,
                rot_selector: None,
                lookup_aggregation: None,
                lookup_table: None,
                lookup_sorted: PaddedSeq([None, None, None, None, None]),
                runtime_lookup_table: None,
                runtime_lookup_table_selector: None,
                xor_lookup_selector: None,
                lookup_gate_lookup_selector: None,
                range_check_lookup_selector: None,
                foreign_field_mul_lookup_selector: None,
            },
        },
        ft_eval1: our_fp(900),
    };

    let proof = PicklesWrapWireProofStableV1 {
        commitments: PicklesWrapWireProofCommitmentsStableV1 {
            w_comm: PaddedSeq(std::array::from_fn(|i| our_point(1000 + i as u64))),
            z_comm: our_point(1100),
            t_comm: PaddedSeq(std::array::from_fn(|i| our_point(1200 + i as u64))),
        },
        evaluations: PicklesWrapWireProofEvaluationsStableV1 {
            w: PaddedSeq(std::array::from_fn(|i| {
                (our_fp(1300 + i as u64 * 2), our_fp(1301 + i as u64 * 2))
            })),
            coefficients: PaddedSeq(std::array::from_fn(|i| {
                (our_fp(1400 + i as u64 * 2), our_fp(1401 + i as u64 * 2))
            })),
            z: (our_fp(1500), our_fp(1501)),
            s: PaddedSeq(std::array::from_fn(|i| {
                (our_fp(1510 + i as u64 * 2), our_fp(1511 + i as u64 * 2))
            })),
            generic_selector: (our_fp(1530), our_fp(1531)),
            poseidon_selector: (our_fp(1532), our_fp(1533)),
            complete_add_selector: (our_fp(1534), our_fp(1535)),
            mul_selector: (our_fp(1536), our_fp(1537)),
            emul_selector: (our_fp(1538), our_fp(1539)),
            endomul_scalar_selector: (our_fp(1540), our_fp(1541)),
        },
        ft_eval1: our_fp(1600),
        bulletproof: PicklesWrapWireProofStableV1Bulletproof {
            // ⚑ 15 rounds: the wrap IPA has log2(2^15) = 15 (l, r) pairs, which is what every
            // real block proof read below carries.
            lr: (0..15u64)
                .map(|i| (our_point(1700 + i * 2), our_point(1701 + i * 2)))
                .collect::<Vec<_>>()
                .into(),
            z_1: our_fp(1800),
            z_2: our_fp(1801),
            delta: our_point(1900),
            challenge_polynomial_commitment: our_point(1901),
        },
    };

    PicklesProofProofsVerified2ReprStableV2 {
        statement: PicklesProofProofsVerified2ReprStableV2Statement {
            proof_state,
            messages_for_next_step_proof,
        },
        prev_evals,
        proof,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let out_dir = args
        .first()
        .cloned()
        .unwrap_or_else(|| "/tmp/pickles-proof-wire".to_string());
    std::fs::create_dir_all(&out_dir).expect("out dir");

    let fixtures: Vec<String> = if args.len() > 1 {
        args[1..].to_vec()
    } else {
        let mut v = vec!["mina_devnet_block.json".to_string()];
        let dir = "../mina-blocks";
        if let Ok(rd) = std::fs::read_dir(dir) {
            let mut names: Vec<_> = rd
                .filter_map(|e| e.ok())
                .map(|e| e.path().to_string_lossy().to_string())
                .filter(|p| p.ends_with(".json"))
                .collect();
            names.sort();
            v.extend(names);
        }
        v
    };

    println!("== BINPROT ROUND-TRIP ON REAL BLOCK PROOFS ==");
    let mut verdicts = Vec::new();
    let mut all_identical = true;
    for f in &fixtures {
        let v = roundtrip(f);
        all_identical &= v.identical && v.trailing == 0;
        println!(
            "[roundtrip] {:<52} h={:<8} bytes={:<6} trailing={} byte_identical={} {}",
            v.path,
            v.height,
            v.n_bytes,
            v.trailing,
            v.identical,
            match v.first_divergence {
                None => String::new(),
                Some(o) => format!("FIRST_DIVERGENCE_AT={o}"),
            }
        );
        std::fs::write(
            format!("{out_dir}/{}.o1js-proof.json", sanitize(&v.path)),
            format!(
                "{{\n  \"publicInput\": [],\n  \"publicOutput\": [],\n  \"maxProofsVerified\": 2,\n  \"proof\": \"{}\"\n}}\n",
                v.sexp_b64
            ),
        )
        .expect("write o1js proof json");
        verdicts.push(v);
    }

    println!("\n== A PROOF OBJECT WE BUILT (nothing copied from a real proof) ==");
    let synth = synthetic_proof();
    let sb = binprot_of_proof(&synth);
    let mut s = sb.as_slice();
    let back = PicklesProofProofsVerified2ReprStableV2::binprot_read(&mut s)
        .expect("our synthetic proof decodes with openmina's reader");
    assert_eq!(
        back, synth,
        "synthetic proof does not survive its own encoding"
    );
    assert_eq!(s.len(), 0, "synthetic proof left trailing bytes");
    println!("[synthetic] binprot bytes = {} ; openmina binprot_read ACCEPTS and re-decodes EQUAL ; trailing = 0", sb.len());
    let synth_sexp = sexp_of_proof(&synth);
    let synth_b64 = base64::engine::general_purpose::STANDARD.encode(synth_sexp.as_bytes());
    println!("[synthetic] sexp bytes = {}", synth_sexp.len());
    std::fs::write(format!("{out_dir}/synthetic.binprot"), &sb).expect("write");
    std::fs::write(
        format!("{out_dir}/synthetic.o1js-proof.json"),
        format!(
            "{{\n  \"publicInput\": [],\n  \"publicOutput\": [],\n  \"maxProofsVerified\": 2,\n  \"proof\": \"{synth_b64}\"\n}}\n"
        ),
    )
    .expect("write");

    // A machine-readable summary for the gate script.
    let mut j = String::from("{\n  \"roundtrip\": [\n");
    for (i, v) in verdicts.iter().enumerate() {
        let _ = write!(
            j,
            "    {{\"fixture\": {:?}, \"height\": {:?}, \"state_hash\": {:?}, \"binprot_bytes\": {}, \"trailing\": {}, \"byte_identical\": {}, \"first_divergence\": {}, \"sexp_bytes\": {}}}{}\n",
            v.path,
            v.height,
            v.state_hash,
            v.n_bytes,
            v.trailing,
            v.identical,
            match v.first_divergence {
                None => "null".to_string(),
                Some(o) => o.to_string(),
            },
            v.sexp_len,
            if i + 1 == verdicts.len() { "" } else { "," }
        );
    }
    let _ = write!(
        j,
        "  ],\n  \"all_byte_identical\": {all_identical},\n  \"synthetic_binprot_bytes\": {},\n  \"synthetic_sexp_bytes\": {}\n}}\n",
        sb.len(),
        synth_sexp.len()
    );
    std::fs::write(format!("{out_dir}/summary.json"), j).expect("write summary");

    println!("\nwrote {out_dir}/*.o1js-proof.json and summary.json");
    if !all_identical {
        eprintln!("PROOF_WIRE_RESULT=RED (a real proof did not survive decode->encode)");
        std::process::exit(1);
    }
    println!("PROOF_WIRE_RESULT=GREEN");
}

fn sanitize(p: &str) -> String {
    std::path::Path::new(p)
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "fixture".into())
}
