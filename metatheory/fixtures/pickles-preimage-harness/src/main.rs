// PROVE + VERIFY the first Lean-authored kimchi circuit in this tree that is not a Pickles shape:
//
//     "I know x such that Poseidon.hash([x]) = c",  c the ONE PUBLIC INPUT.
//
// The circuit — gates, coefficients, copy-permutation variables, placement and witness — is authored
// in `Dregg2.Circuit.Emit.KimchiPreimageCircuit` and emitted by `EmitPreimageJson`. This harness
// reads that JSON, builds the pure-Rust kimchi objects, and runs the prover/verifier. House Law #1:
// the circuit is Lean-authored; `proof-systems` is the Rust prover.
//
// Two entry points over the same logic: `main()` is the driver (point it at `/tmp/pickles-preimage`
// to run the LIVE Lean emission); the `#[test]` fns are the committed gate, one property each.

use std::array;
use std::path::PathBuf;
use std::str::FromStr;
use std::time::Instant;

use ark_ff::{PrimeField, Zero};
use groupmap::GroupMap;
use mina_curves::pasta::{Fp, Fq, Vesta, VestaParameters};
use mina_poseidon::{
    constants::{PlonkSpongeConstantsKimchi, SpongeConstants},
    pasta::{fp_kimchi, FULL_ROUNDS},
    poseidon::{ArithmeticSponge, Sponge},
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::{commitment::CommitmentCurve, ipa::OpeningProof, ipa::SRS, SRS as _};
use serde::Deserialize;

use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        wires::{GateWires, Wire, COLUMNS},
    },
    proof::ProverProof,
    prover_index::{testing::new_index_for_test_with_lookups_and_custom_srs, ProverIndex},
    verifier::{batch_verify, Context},
};

type BaseSponge = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type Idx = ProverIndex<FULL_ROUNDS, Vesta, SRS<Vesta>>;

// ---- the Lean-emitted JSON shape ----

#[derive(Deserialize, Clone)]
struct GateJson {
    typ: u64,
    wires: Vec<[usize; 2]>,
    coeffs: Vec<String>,
}

#[derive(Deserialize, Clone)]
struct CircuitJson {
    name: String,
    public_input_size: usize,
    public_input: Vec<String>,
    num_rows: usize,
    gates: Vec<GateJson>,
    witness: Vec<Vec<String>>, // COLUMNS columns, each num_rows long
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures"))
}

/// Decimal (possibly negative, possibly 255-bit) string -> Fp, reduced. `i128` is NOT enough here:
/// the public input and every Poseidon round state are full field elements, so parsing must go
/// through the arbitrary-precision decimal reader and the sign handled separately.
fn parse_fp(s: &str) -> Fp {
    if let Some(rest) = s.strip_prefix('-') {
        -Fp::from_str(rest).expect("negative coefficient must be a decimal integer")
    } else {
        Fp::from_str(s).expect("coefficient/witness must be a decimal integer")
    }
}

fn gate_type_from_ordinal(o: u64) -> GateType {
    match o {
        0 => GateType::Zero,
        1 => GateType::Generic,
        2 => GateType::Poseidon,
        3 => GateType::CompleteAdd,
        4 => GateType::VarBaseMul,
        5 => GateType::EndoMul,
        6 => GateType::EndoMulScalar,
        _ => panic!("unsupported gate ordinal {o}"),
    }
}

fn load(dir: &std::path::Path, name: &str) -> CircuitJson {
    let path = dir.join(name);
    let raw =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_str(&raw).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

fn build_gates(c: &CircuitJson) -> Vec<CircuitGate<Fp>> {
    c.gates
        .iter()
        .map(|g| {
            assert_eq!(g.wires.len(), 7, "kimchi PERMUTS = 7 wires per gate");
            let wires: GateWires = array::from_fn(|i| Wire {
                row: g.wires[i][0],
                col: g.wires[i][1],
            });
            let coeffs: Vec<Fp> = g.coeffs.iter().map(|s| parse_fp(s)).collect();
            CircuitGate::new(gate_type_from_ordinal(g.typ), wires, coeffs)
        })
        .collect()
}

fn build_witness(c: &CircuitJson) -> [Vec<Fp>; COLUMNS] {
    assert_eq!(
        c.witness.len(),
        COLUMNS,
        "witness must have {COLUMNS} columns"
    );
    array::from_fn(|col| {
        let column = &c.witness[col];
        assert_eq!(
            column.len(),
            c.num_rows,
            "each witness column is num_rows long"
        );
        column.iter().map(|s| parse_fp(s)).collect()
    })
}

fn build_public(c: &CircuitJson) -> Vec<Fp> {
    assert_eq!(
        c.public_input.len(),
        c.public_input_size,
        "the emitted public vector must have public_input_size entries"
    );
    c.public_input.iter().map(|s| parse_fp(s)).collect()
}

/// ⚑ MINA'S OWN SRS CONSTRUCTION, not kimchi's serialized test SRS. `SRS::<Vesta>::create(n)` is the
/// deterministic Blake2b-to-curve generator Mina uses (`SRS::<Vesta>::create(1 << 16)` on the step
/// side), and it is index-deterministic, so this circuit's generators ARE a prefix of Mina's.
/// ⚠ The DOMAIN is this circuit's, not Mina's 2^16 — see the manifest header on what that costs.
fn index_for(c: &CircuitJson) -> Idx {
    index_with(c, /* gate preflight */ true)
}

/// `checks = false` disables kimchi's prover-side gate-satisfaction PREFLIGHT, so a refusal is by
/// the argument and not by a debug assert. Every tamper below is run with the preflight OFF.
fn index_with(c: &CircuitJson, checks: bool) -> Idx {
    let gates = build_gates(c);
    let mut index =
        new_index_for_test_with_lookups_and_custom_srs::<FULL_ROUNDS, Vesta, SRS<Vesta>, _>(
            gates,
            c.public_input_size,
            /* prev_challenges */ 0,
            vec![],
            None,
            /* disable_gates_checks */ !checks,
            /* override_srs_size */ None,
            |d1, size| {
                let srs = SRS::<Vesta>::create(size);
                srs.get_lagrange_basis(d1);
                srs
            },
            /* lazy_mode */ false,
        );
    index.compute_verifier_index_digest::<BaseSponge>();
    index
}

type Proof = ProverProof<Vesta, OpeningProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>;

/// Prove alone. Separated from `verify_at` so a refusal can be ATTRIBUTED: a prover-side refusal
/// (the permutation product failing to close) and a verifier-side refusal are different facts and
/// only the second is evidence about what a chain would accept.
fn prove(
    index: &Idx,
    group_map: &<Vesta as CommitmentCurve>::Map,
    witness: [Vec<Fp>; COLUMNS],
) -> Result<Proof, String> {
    ProverProof::create::<BaseSponge, ScalarSponge, _>(
        group_map,
        witness,
        &[],
        index,
        &mut rand::rngs::OsRng,
    )
    .map_err(|e| format!("prove rejected: {e:?}"))
}

/// Verify an existing proof at a public input the caller chooses. This is the half a chain runs.
fn verify_at(
    index: &Idx,
    group_map: &<Vesta as CommitmentCurve>::Map,
    proof: &Proof,
    public_input: &[Fp],
) -> Result<(), String> {
    let vk = index.verifier_index.as_ref().expect("verifier index");
    let ctx = Context {
        verifier_index: vk,
        proof,
        public_input,
    };
    batch_verify::<55, Vesta, BaseSponge, ScalarSponge, OpeningProof<Vesta, FULL_ROUNDS>>(
        group_map,
        &[ctx],
    )
    .map_err(|e| format!("verify rejected: {e:?}"))
}

/// Prove + verify one witness against a fixed index at a given public input. `Ok(())` iff the
/// verifier accepts.
fn prove_and_verify(
    index: &Idx,
    group_map: &<Vesta as CommitmentCurve>::Map,
    witness: [Vec<Fp>; COLUMNS],
    public_input: &[Fp],
) -> Result<(), String> {
    let proof = prove(index, group_map, witness)?;

    let vk = index.verifier_index.as_ref().expect("verifier index");
    let ctx = Context {
        verifier_index: vk,
        proof: &proof,
        public_input,
    };
    batch_verify::<55, Vesta, BaseSponge, ScalarSponge, OpeningProof<Vesta, FULL_ROUNDS>>(
        group_map,
        &[ctx],
    )
    .map_err(|e| format!("verify rejected: {e:?}"))?;
    Ok(())
}

/// ⚑ AN INDEPENDENT IMPLEMENTATION OF THE HASH THE CIRCUIT COMPUTES. `mina-poseidon`'s
/// `fp_kimchi::static_params()` + `poseidon_block_cipher` is the same code path mina-rust and the
/// o1js wasm bindings use. Absorbing one element into the zero sponge and permuting once IS
/// `Poseidon.hash([x])`; the Lean side computes it from `PastaPoseidon.Ref.permFrom`, which shares
/// no code with this.
fn mina_poseidon_hash_one(x: Fp) -> Fp {
    let params = fp_kimchi::static_params();
    let mut sponge = ArithmeticSponge::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>::new(params);
    assert!(
        sponge.state.iter().all(|s: &Fp| s.is_zero()),
        "the sponge starts at [0;3]"
    );
    assert_eq!(
        PlonkSpongeConstantsKimchi::SPONGE_WIDTH,
        3,
        "the width this circuit's 11 Poseidon rows are laid out for"
    );
    sponge.state[0] += x;
    sponge.poseidon_block_cipher();
    sponge.state[0]
}

/// The Lean-emitted secret: the free witness cell `(1,0)` — row 1, column 0.
fn secret_of(c: &CircuitJson) -> Fp {
    parse_fp(&c.witness[0][1])
}

/// The Lean-emitted permutation output: the `Zero` row's column 0 — row 12.
fn output_of(c: &CircuitJson) -> Fp {
    parse_fp(&c.witness[0][12])
}

/// The forgery both circuits are asked to accept: claim `c + 1` and move the PUBLIC-ROW witness
/// cell `(0,0)` with it, so the public-row generic gate `w₀ − c′ = 0` still holds. Everything else
/// — including the real permutation output at `(12,0)` — is untouched. The ONLY thing that can
/// refuse this is the copy-permutation wire `(0,0) ↔ (12,0)`.
fn forged(c: &CircuitJson) -> ([Vec<Fp>; COLUMNS], Vec<Fp>) {
    let mut w = build_witness(c);
    let mut p = build_public(c);
    let bumped = p[0] + Fp::from(1u64);
    p[0] = bumped;
    w[0][0] = bumped;
    (w, p)
}

/// ⚑ `Fq`, not `Fp`: the verifier-index digest is absorbed by the BASE-field sponge, so it is a
/// Vesta base-field element — the same field a Mina VK hash lives in on this side.
fn vk_digest(index: &Idx) -> Fq {
    index
        .verifier_index
        .as_ref()
        .expect("verifier index")
        .digest::<BaseSponge>()
}

fn main() {
    let dir = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(fixtures_dir);

    println!("== a LEAN-AUTHORED zkApp-shaped circuit -> pure-Rust prove + verify ==");
    println!("   fixtures dir: {}", dir.display());
    println!();

    let bound = load(&dir, "preimage.json");
    let control = load(&dir, "unbound.json");

    let x = secret_of(&bound);
    let c = build_public(&bound)[0];
    println!("-- the statement --");
    println!("   circuit          : {}", bound.name);
    println!(
        "   rows             : {} ({} public)",
        bound.num_rows, bound.public_input_size
    );
    println!("   secret x         : {}", x.into_bigint());
    println!("   public c         : {}", c.into_bigint());
    println!(
        "   mina-poseidon    : {}",
        mina_poseidon_hash_one(x).into_bigint()
    );
    println!(
        "   agree            : {}",
        if mina_poseidon_hash_one(x) == c {
            "YES"
        } else {
            "NO"
        }
    );
    println!("   output cell(12,0): {}", output_of(&bound).into_bigint());
    println!();

    let group_map = <Vesta as CommitmentCurve>::Map::setup();

    let t = Instant::now();
    let ib = index_for(&bound);
    let ic = index_for(&control);
    println!(
        "-- indices (Mina's SRS construction) built in {:?} --",
        t.elapsed()
    );
    println!(
        "   domain           : 2^{}",
        ib.cs.domain.d1.log_size_of_group
    );
    println!("   vk digest bound  : {}", vk_digest(&ib).into_bigint());
    println!("   vk digest control: {}", vk_digest(&ic).into_bigint());
    println!(
        "   the wire is in the key: {}",
        if vk_digest(&ib) != vk_digest(&ic) {
            "YES"
        } else {
            "NO"
        }
    );
    println!();

    let t = Instant::now();
    let ok = prove_and_verify(
        &ib,
        &group_map,
        build_witness(&bound),
        &build_public(&bound),
    );
    println!("-- honest witness --");
    println!("   {:?}   ({:?})", ok, t.elapsed());

    // ⚑ THE VERIFIER-SIDE POLARITY: an HONEST, valid proof, offered at a public input the circuit
    // did not compute. Nothing about the proof changes; only the claim does. This is the half a
    // chain runs, and the only one that measures what a chain would accept.
    let honest = prove(&ib, &group_map, build_witness(&bound)).expect("honest proof");
    let cplus = vec![build_public(&bound)[0] + Fp::from(1u64)];
    let wrongclaim = verify_at(&ib, &group_map, &honest, &cplus);
    println!("-- a VALID proof, offered at c+1 (VERIFIER side) --");
    println!("   {:?}", wrongclaim);

    // ⚠ The prover-side polarity. A forger who bumps the claim AND the public-row witness cell keeps
    // every GATE satisfied, so kimchi's gate preflight passes; the refusal below is the permutation
    // product failing to close. That is a PROVER refusal, not a verifier one — the gate-satisfaction
    // preflight is disabled here so it is the argument refusing and not an assert.
    let ibn = index_with(&bound, false);
    let (fw, fp_) = forged(&bound);
    let bad = prove_and_verify(&ibn, &group_map, fw, &fp_);
    println!("-- forged claim + moved public cell, BOUND circuit (PROVER side) --");
    println!("   {:?}", bad);

    let icn = index_with(&control, false);
    let (fw2, fp2) = forged(&control);
    let ctl = prove_and_verify(&icn, &group_map, fw2, &fp2);
    println!("-- the SAME forgery, CONTROL circuit (no binding wire) --");
    println!("   {:?}", ctl);

    println!();
    println!(
        "VERDICT: honest={} wrong_claim_rejected_by_VERIFIER={} forgery_rejected_by_PROVER={} \
control_accepts_forgery={} vk_moves={}",
        ok.is_ok(),
        wrongclaim.is_err(),
        bad.is_err(),
        ctl.is_ok(),
        vk_digest(&ib) != vk_digest(&ic)
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fx(name: &str) -> CircuitJson {
        load(&fixtures_dir(), name)
    }

    /// The shape the Lean header declares, read back off the emitted artifact.
    #[test]
    fn the_emitted_shape_is_the_declared_one() {
        let c = fx("preimage.json");
        assert_eq!(c.name, "poseidonPreimage");
        assert_eq!(
            c.public_input_size, 1,
            "ONE public word: the claimed digest"
        );
        assert_eq!(
            c.num_rows, 14,
            "1 public + 11 Poseidon + Zero + zero-assert"
        );
        assert_eq!(c.gates.len(), 14);
        assert_eq!(c.witness.len(), COLUMNS);
        // row 0 public generic, rows 1..=11 Poseidon, row 12 Zero, row 13 generic
        let typs: Vec<u64> = c.gates.iter().map(|g| g.typ).collect();
        assert_eq!(typs, vec![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1]);
        // the binding wire, read off the emitted gate list
        assert_eq!(c.gates[0].wires[0], [12, 0], "sigma(0,0) = the output cell");
        assert_eq!(
            c.gates[12].wires[0],
            [0, 0],
            "sigma(12,0) = the public cell"
        );
    }

    /// ⚑ CROSS-IMPLEMENTATION: the digest the Lean circuit publishes is the digest
    /// `mina-poseidon`'s own `fp_kimchi` permutation produces from the same secret.
    #[test]
    fn the_lean_digest_is_mina_poseidons() {
        let c = fx("preimage.json");
        let x = secret_of(&c);
        let claimed = build_public(&c)[0];
        assert_eq!(
            mina_poseidon_hash_one(x),
            claimed,
            "the public word must be mina-poseidon's Poseidon.hash([x])"
        );
        // …and the witness cell the copy-permutation binds to it carries the same value.
        assert_eq!(
            output_of(&c),
            claimed,
            "witness (12,0) is the claimed digest"
        );
        assert_ne!(x, claimed, "a fixed point would make this test vacuous");
    }

    /// The honest witness proves and `kimchi::verifier::batch_verify` ACCEPTS.
    #[test]
    fn the_honest_witness_proves_and_verifies() {
        let c = fx("preimage.json");
        let group_map = <Vesta as CommitmentCurve>::Map::setup();
        let index = index_for(&c);
        prove_and_verify(&index, &group_map, build_witness(&c), &build_public(&c))
            .expect("the honest preimage witness must verify");
    }

    /// ⚑ **THE VERIFIER REFUSES A CLAIM THE CIRCUIT DID NOT COMPUTE.** An honest, valid proof is
    /// offered at `c+1`. The proof is untouched — only the claim moves — so this is measured on the
    /// half a chain actually runs, `kimchi::verifier::batch_verify`.
    #[test]
    fn a_valid_proof_does_not_verify_against_a_different_claim() {
        let c = fx("preimage.json");
        let group_map = <Vesta as CommitmentCurve>::Map::setup();
        let index = index_for(&c);
        let proof = prove(&index, &group_map, build_witness(&c)).expect("honest proof");
        let real = build_public(&c);
        verify_at(&index, &group_map, &proof, &real).expect("the real claim must verify");
        let bumped = vec![real[0] + Fp::from(1u64)];
        assert!(
            verify_at(&index, &group_map, &proof, &bumped).is_err(),
            "the VERIFIER must refuse a digest this proof does not attest"
        );
    }

    /// ⚠ A FORGED CLAIM IS REFUSED BY THE PROVER, and the attribution matters. Bumping `c` and
    /// moving the public-row witness cell with it keeps every GATE satisfied — so with the gate
    /// preflight DISABLED, what refuses is the permutation product failing to close. That is a
    /// prover-side fact, not a verifier-side one; `the_control_without_the_wire_accepts_the_forgery`
    /// is what makes it evidence about the WIRE.
    #[test]
    fn a_forged_claim_cannot_close_the_permutation() {
        let c = fx("preimage.json");
        let group_map = <Vesta as CommitmentCurve>::Map::setup();
        let index = index_with(&c, /* preflight */ false);
        let (w, p) = forged(&c);
        let e = prove_and_verify(&index, &group_map, w, &p)
            .expect_err("claiming a digest the circuit did not compute must be REFUSED");
        assert!(
            e.contains("Permutation"),
            "the refusal must be the copy-permutation argument, not a gate check; got: {e}"
        );
    }

    /// ⚑ THE CONTROL ACCEPTS THE SAME FORGERY. Byte-identical gate types, coefficients and witness;
    /// the ONLY difference is that the output row exposes no copy variable. So the rejection above
    /// is attributable to the wire and to nothing else.
    #[test]
    fn the_control_without_the_wire_accepts_the_forgery() {
        let b = fx("preimage.json");
        let c = fx("unbound.json");
        // the control really is the same circuit but for the wire
        let tb: Vec<u64> = b.gates.iter().map(|g| g.typ).collect();
        let tc: Vec<u64> = c.gates.iter().map(|g| g.typ).collect();
        assert_eq!(tb, tc, "the control must carry the same gate types");
        let cb: Vec<&Vec<String>> = b.gates.iter().map(|g| &g.coeffs).collect();
        let cc: Vec<&Vec<String>> = c.gates.iter().map(|g| &g.coeffs).collect();
        assert_eq!(cb, cc, "the control must carry the same coefficients");
        assert_eq!(
            b.witness, c.witness,
            "the control must carry the same witness"
        );
        assert_eq!(
            c.gates[0].wires[0],
            [0, 0],
            "the control's public cell self-wires"
        );
        assert_eq!(
            c.gates[12].wires[0],
            [12, 0],
            "the control's output cell self-wires"
        );

        let group_map = <Vesta as CommitmentCurve>::Map::setup();
        let index = index_with(&c, /* preflight */ false);
        let (w, p) = forged(&c);
        prove_and_verify(&index, &group_map, w, &p)
            .expect("without the binding wire the same forgery must be ACCEPTED");
    }

    /// ⚑ THE WIRE IS IN THE KEY. The verifier-index digest — the value a deployed VK would be
    /// identified by — differs between the circuit and its control, so the copy permutation is not
    /// merely a prover-side convention.
    #[test]
    fn the_binding_wire_moves_the_verification_key() {
        let ib = index_for(&fx("preimage.json"));
        let ic = index_for(&fx("unbound.json"));
        assert_ne!(
            vk_digest(&ib),
            vk_digest(&ic),
            "a circuit and its unbound control must not share a verification key"
        );
    }
}
