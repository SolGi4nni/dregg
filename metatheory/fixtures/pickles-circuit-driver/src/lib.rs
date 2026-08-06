//! pickles-circuit-driver — **PROVE THIS LEAN CIRCUIT.** One driver, both curves.
//!
//! House Law #1: the CIRCUIT is Lean-authored. Nothing in this crate writes a constraint, chooses a
//! coefficient or fills a witness cell. It reads what `Dregg2.Circuit.Emit.KimchiCircuitJson`
//! emitted, builds the pure-Rust kimchi objects, and runs `proof-systems` 0.3.0.
//!
//! # ⚑ WHAT THE FOUR COPIES DISAGREED ABOUT
//!
//! `build_gates` / `build_witness` / `index_for` / `prove_and_verify` existed four times. They were
//! not four transcriptions of one thing — they were four different readers, and the differences
//! were live:
//!
//! * **The field parser.** `pickles-r4-harness` parsed every coefficient and witness cell through
//!   `i128`, so it PANICS on any value wider than 127 bits — it could not read a Poseidon round
//!   constant, let alone a wrap statement word. The other three used `F::from_str`.
//! * **…and `F::from_str` SILENTLY REDUCES.** Measured in `ark-ff` 0.5
//!   (`fields/models/fp/mod.rs:651-666`): it is `BigInt::from_str(s) % MODULUS`, with the modulus
//!   added back when negative. A value at or above the modulus does not error — it wraps. That is
//!   exactly the Fp-into-Fq hazard, and it is why [`parse_field`] REFUSES a non-canonical literal
//!   instead of calling `from_str` on it. (Signs are fine: `BigInt::from_str` reads them, and the
//!   `%`-then-add is the correct reduction. `pickles-preimage-harness` hand-rolled a sign branch
//!   around `from_str` that was doing nothing.)
//! * **The gate-ordinal table.** `pickles-poseidon-harness` accepted ordinals 0..=3 and panicked on
//!   the three curve gates; the rest accepted 0..=6. A harness whose table is short cannot even
//!   report that the emission grew a gate type — it dies on it.
//! * **The SRS.** Three harnesses take kimchi's serialized TEST srs; `pickles-preimage-harness`
//!   builds Mina's own deterministic `SRS::create`. These are DIFFERENT points and produce different
//!   verification keys, so the choice is carried as [`Srs`] data per call site rather than baked in
//!   — every harness keeps exactly the SRS it had.
//! * **The gate preflight.** `pickles-r4-harness` left kimchi's prover-side gate-satisfaction check
//!   ON, so its tampers are rejected by a debug assert rather than by the argument; the other three
//!   disable it so a refusal is the proof's. Carried as [`IndexOpts::gate_checks`].
//! * **The public input.** Two of the four had no `public_input` field in their `serde` shape at
//!   all, which is the same gap that made a lane write a fourth `renderCircuit` in Lean.
//!
//! # THE SHAPE THIS READS
//!
//! One `serde` shape for all four Lean field-sets. The three optional groups are `Option`, so a
//! consumer can tell "the key was absent" from "the key was there and empty" — the distinction the
//! Lean side carries deliberately (`KimchiCircuitJson.optField_some_nil_still_emits_the_key`).

use std::path::Path;
use std::str::FromStr;

use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use num_bigint::{BigInt, BigUint, Sign};
use serde::Deserialize;

use groupmap::GroupMap as _;
use kimchi::{
    circuits::{
        gate::{CircuitGate, GateType},
        wires::{GateWires, Wire, COLUMNS, PERMUTS},
    },
    curve::KimchiCurve,
    proof::ProverProof,
    prover_index::{testing::new_index_for_test_with_lookups_and_custom_srs, ProverIndex},
    verifier::{batch_verify, Context},
};
use mina_curves::named::NamedCurve;
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    pasta::FULL_ROUNDS,
    sponge::{DefaultFqSponge, DefaultFrSponge},
    FqSponge,
};
use poly_commitment::{
    commitment::CommitmentCurve, ipa::OpeningProof, ipa::SRS, precomputed_srs, SRS as _,
};

pub use kimchi;
pub use mina_poseidon::pasta::FULL_ROUNDS as ROUNDS;

// =================================================================================================
// §1 — the Lean-emitted shape
// =================================================================================================

/// One placed gate: the `typ` ordinal, the seven copy-permutation cells, the coefficients.
#[derive(Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct GateJson {
    pub typ: u64,
    pub wires: Vec<[usize; 2]>,
    pub coeffs: Vec<String>,
}

/// A Lean-emitted circuit. `public_input`, `probe_rows` and the slot census are `Option` because
/// the Lean renderer distinguishes an ABSENT key from a present-and-empty one, and so must this.
#[derive(Deserialize, Clone, Debug)]
pub struct CircuitJson {
    pub name: String,
    pub public_input_size: usize,
    #[serde(default)]
    pub public_input: Option<Vec<String>>,
    pub num_rows: usize,
    #[serde(default)]
    pub probe_rows: Option<Vec<usize>>,
    /// Which of Mina's forty wrap statement slots the emission DERIVES.
    #[serde(default)]
    pub derived_slots: Option<Vec<usize>>,
    /// …and which it declares unread. Emitted together or not at all.
    #[serde(default)]
    pub unread_slots: Option<Vec<usize>>,
    pub gates: Vec<GateJson>,
    /// `COLUMNS` columns, each `num_rows` long.
    pub witness: Vec<Vec<String>>,
}

impl CircuitJson {
    /// The public vector as the emission carried it. A `pubSize > 0` circuit that omits it is a
    /// refusal, not a default: the verifier is handed the vector separately
    /// (`kimchi/src/verifier.rs:816` rejects a length mismatch outright), so re-deriving it in Rust
    /// would be witness authoring.
    pub fn public_strings(&self) -> &[String] {
        match &self.public_input {
            Some(p) => p,
            None => {
                assert_eq!(
                    self.public_input_size, 0,
                    "{}: public_input_size {} but the emission carries NO public_input vector; \
                     a harness that filled one in would be authoring the witness",
                    self.name, self.public_input_size
                );
                &[]
            }
        }
    }

    /// The probe rows the Lean schedule emitted. Absent is not "none": a harness that aimed its
    /// tampers at a hand-copied constant would be testing its own guess.
    pub fn probes(&self) -> &[usize] {
        self.probe_rows.as_deref().unwrap_or(&[])
    }
}

/// Read one emitted circuit. Refuses an EMPTY file loudly: `include_str!`/`read_to_string` hand a
/// zero-byte fixture back as `""`, and a test run against nothing reports success.
pub fn load(path: &Path) -> CircuitJson {
    let raw =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    assert!(
        !raw.trim().is_empty(),
        "{} is EMPTY — a zero-byte fixture parses as nothing and proves nothing",
        path.display()
    );
    serde_json::from_str(&raw).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

pub fn load_in(dir: &Path, name: &str) -> CircuitJson {
    load(&dir.join(name))
}

// =================================================================================================
// §2 — ⚑ the field reader, and the refusal that is the whole point of it
// =================================================================================================

/// A decimal literal (optionally signed) as an element of `F` — **or a refusal.**
///
/// ⚠ This is NOT `F::from_str`. `ark-ff` 0.5 implements that as `BigInt::from_str(s) % MODULUS`
/// (`fields/models/fp/mod.rs:651-666`): a literal at or above the modulus is silently WRAPPED. The
/// Lean emissions carry Fp elements on the step side and Fq elements on the wrap side, the two
/// primes differ above bit 128, and nothing in the JSON says which — so `from_str` is the exact
/// place a wrap-side coefficient becomes a different, well-formed, step-side coefficient with no
/// error anywhere. Here a non-canonical literal is an ERROR.
///
/// This does not make the two fields distinguishable — a literal below both primes parses in both,
/// and no amount of reading the bytes will say which circuit it is. It makes the reduction that
/// would hide the mistake impossible, and leaves the declaration to the caller.
pub fn try_parse_field<F: PrimeField>(s: &str) -> Result<F, String> {
    let n = BigInt::from_str(s.trim()).map_err(|_| format!("{s:?} is not a decimal integer"))?;
    let modulus = BigUint::from_bytes_le(&F::MODULUS.to_bytes_le());
    let (sign, mag) = (n.sign(), n.magnitude().clone());
    if mag >= modulus {
        return Err(format!(
            "{s:?} is NOT canonical for this field (|value| >= modulus {modulus}). \
             Refusing rather than reducing: a coefficient authored over the OTHER pasta prime \
             would reduce into a perfectly well-formed element of this one and nothing downstream \
             could tell. Check which curve the emission was authored for."
        ));
    }
    let v = F::from_le_bytes_mod_order(&mag.to_bytes_le());
    Ok(if sign == Sign::Minus { -v } else { v })
}

/// [`try_parse_field`], panicking. The panic message names the refusal.
pub fn parse_field<F: PrimeField>(s: &str) -> F {
    try_parse_field(s).unwrap_or_else(|e| panic!("{e}"))
}

/// The seven gate types Mina uses. ⚠ NO catch-all that "defaults" to `Zero`: an ordinal this table
/// does not know is an emission this driver cannot read, and reading it as something else is worse
/// than stopping.
pub fn gate_type_from_ordinal(o: u64) -> GateType {
    match o {
        0 => GateType::Zero,
        1 => GateType::Generic,
        2 => GateType::Poseidon,
        3 => GateType::CompleteAdd,
        4 => GateType::VarBaseMul,
        5 => GateType::EndoMul,
        6 => GateType::EndoMulScalar,
        _ => panic!(
            "gate ordinal {o} is not one of the seven Mina gate types this driver reads \
             (Zero, Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, EndoMulScalar)"
        ),
    }
}

// =================================================================================================
// §3 — circuit -> kimchi objects
// =================================================================================================

pub fn build_gates<F: PrimeField>(c: &CircuitJson) -> Vec<CircuitGate<F>> {
    assert_eq!(
        c.gates.len(),
        c.num_rows,
        "{}: {} gates against num_rows {}",
        c.name,
        c.gates.len(),
        c.num_rows
    );
    c.gates
        .iter()
        .enumerate()
        .map(|(row, g)| {
            assert_eq!(
                g.wires.len(),
                PERMUTS,
                "{}: row {row} has {} wires, a kimchi row has {PERMUTS} permutable columns",
                c.name,
                g.wires.len()
            );
            let wires: GateWires = std::array::from_fn(|i| Wire {
                row: g.wires[i][0],
                col: g.wires[i][1],
            });
            let coeffs: Vec<F> = g.coeffs.iter().map(|s| parse_field(s)).collect();
            CircuitGate::new(gate_type_from_ordinal(g.typ), wires, coeffs)
        })
        .collect()
}

/// The witness as proof-systems wants it: `COLUMNS` columns, each `num_rows` long.
pub fn build_witness<F: PrimeField>(c: &CircuitJson) -> [Vec<F>; COLUMNS] {
    assert_eq!(
        c.witness.len(),
        COLUMNS,
        "{}: witness has {} columns, kimchi wants {COLUMNS}",
        c.name,
        c.witness.len()
    );
    std::array::from_fn(|col| {
        let column = &c.witness[col];
        assert_eq!(
            column.len(),
            c.num_rows,
            "{}: witness column {col} is {} long, num_rows is {}",
            c.name,
            column.len(),
            c.num_rows
        );
        column.iter().map(|s| parse_field(s)).collect()
    })
}

pub fn build_public<F: PrimeField>(c: &CircuitJson) -> Vec<F> {
    let p = c.public_strings();
    assert_eq!(
        p.len(),
        c.public_input_size,
        "{}: the emitted public vector has {} entries for public_input_size {}",
        c.name,
        p.len(),
        c.public_input_size
    );
    p.iter().map(|s| parse_field(s)).collect()
}

// =================================================================================================
// §4 — the lane: which curve a circuit is proved on
// =================================================================================================

/// A commitment curve plus its two sponges. ⚑ The step side is Vesta/Fp and the wrap side is
/// Pallas/Fq (`wrap_main_inputs.ml:4,6` sets `Me = Tock`), and a circuit authored for one proved on
/// the other is a different circuit, not a relabelling.
pub trait Lane {
    /// A name for messages. Not a discriminator: nothing in an emitted artifact says which curve it
    /// was authored for.
    const NAME: &'static str;
    type G: KimchiCurve<FULL_ROUNDS> + CommitmentCurve + NamedCurve;
}

pub type ScalarOf<L> = <<L as Lane>::G as AffineRepr>::ScalarField;
pub type BaseOf<L> = <<L as Lane>::G as AffineRepr>::BaseField;
pub type Idx<L> = ProverIndex<FULL_ROUNDS, <L as Lane>::G, SRS<<L as Lane>::G>>;
pub type Proof<L> =
    ProverProof<<L as Lane>::G, OpeningProof<<L as Lane>::G, FULL_ROUNDS>, FULL_ROUNDS>;
pub type Map<L> = <<L as Lane>::G as CommitmentCurve>::Map;

/// **The STEP side.** Vesta-committed, Fp-scalar.
pub struct Step;
impl Lane for Step {
    const NAME: &'static str = "vesta/Fp (step)";
    type G = mina_curves::pasta::Vesta;
}
pub type StepBaseSponge =
    DefaultFqSponge<mina_curves::pasta::VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
pub type StepScalarSponge =
    DefaultFrSponge<mina_curves::pasta::Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// **The WRAP side.** Pallas-committed, Fq-scalar.
pub struct Wrap;
impl Lane for Wrap {
    const NAME: &'static str = "pallas/Fq (wrap)";
    type G = mina_curves::pasta::Pallas;
}
pub type WrapBaseSponge =
    DefaultFqSponge<mina_curves::pasta::PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
pub type WrapScalarSponge =
    DefaultFrSponge<mina_curves::pasta::Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

// =================================================================================================
// §5 — the index
// =================================================================================================

/// Which SRS the index is built over. ⚑ These are DIFFERENT sets of points and produce different
/// verification keys, so it is carried per call site rather than chosen here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Srs {
    /// kimchi's serialized TEST srs for `log2 <= 16`, `SRS::create` above it — what
    /// `new_index_for_test_with_lookups` hands back.
    KimchiTest,
    /// **Mina's own** deterministic Blake2b-to-curve `SRS::create`
    /// (`poly-commitment/src/ipa.rs:353-380`), which is what openmina builds a zkApp verifier index
    /// with. Index-deterministic, so a small circuit's generators ARE a prefix of Mina's.
    Mina,
    /// Mina's, built in parallel. Same points; only the construction is threaded.
    MinaParallel,
}

/// How to build a prover index from a Lean-emitted gate list.
#[derive(Clone, Copy, Debug)]
pub struct IndexOpts {
    pub public: usize,
    pub prev_challenges: usize,
    /// `true` keeps kimchi's prover-side gate-satisfaction PREFLIGHT, which panics on a bad
    /// witness. `false` disables it, so a tamper is refused by the PROOF (a non-vanishing quotient,
    /// or the permutation product failing to close) and comes back as an `Err`. A binding claim
    /// wants `false`: a debug assert is not the argument.
    pub gate_checks: bool,
    pub srs: Srs,
    /// `max_poly_size` override. `None` = the circuit's own domain.
    pub max_poly_size: Option<usize>,
}

impl IndexOpts {
    /// The default the gate-fixture harnesses use: no previous challenges, kimchi's test SRS,
    /// preflight OFF so a refusal is the argument's.
    pub fn test(public: usize) -> Self {
        IndexOpts {
            public,
            prev_challenges: 0,
            gate_checks: false,
            srs: Srs::KimchiTest,
            max_poly_size: None,
        }
    }
    pub fn gate_checks(mut self, on: bool) -> Self {
        self.gate_checks = on;
        self
    }
    pub fn srs(mut self, srs: Srs) -> Self {
        self.srs = srs;
        self
    }
    pub fn prev_challenges(mut self, n: usize) -> Self {
        self.prev_challenges = n;
        self
    }
    pub fn max_poly_size(mut self, n: Option<usize>) -> Self {
        self.max_poly_size = n;
        self
    }
}

/// Build a `ProverIndex` (+ its verifier-index digest) from a Lean-emitted gate list.
pub fn index_from_gates<L: Lane, EFq>(gates: Vec<CircuitGate<ScalarOf<L>>>, o: IndexOpts) -> Idx<L>
where
    BaseOf<L>: PrimeField,
    Map<L>: Sync,
    EFq: Clone + FqSponge<BaseOf<L>, L::G, ScalarOf<L>, FULL_ROUNDS>,
{
    let mut index = new_index_for_test_with_lookups_and_custom_srs::<FULL_ROUNDS, L::G, SRS<L::G>, _>(
        gates,
        o.public,
        o.prev_challenges,
        vec![],
        None,
        /* disable_gates_checks */ !o.gate_checks,
        o.max_poly_size,
        |d1, size| {
            let srs = match o.srs {
                Srs::KimchiTest => {
                    if size.ilog2() <= precomputed_srs::SERIALIZED_SRS_SIZE {
                        precomputed_srs::get_srs_test::<L::G>()
                    } else {
                        SRS::<L::G>::create(size)
                    }
                }
                Srs::Mina => SRS::<L::G>::create(size),
                Srs::MinaParallel => SRS::<L::G>::create_parallel(size),
            };
            srs.get_lagrange_basis(d1);
            srs
        },
        /* lazy_mode */ false,
    );
    index.compute_verifier_index_digest::<EFq>();
    index
}

/// Build a `ProverIndex` straight from an emitted circuit.
pub fn index_for<L: Lane, EFq>(c: &CircuitJson, o: IndexOpts) -> Idx<L>
where
    BaseOf<L>: PrimeField,
    Map<L>: Sync,
    EFq: Clone + FqSponge<BaseOf<L>, L::G, ScalarOf<L>, FULL_ROUNDS>,
{
    index_from_gates::<L, EFq>(build_gates::<ScalarOf<L>>(c), o)
}

/// The verifier-index digest — the value a deployed VK would be identified by. ⚑ It is a BASE-field
/// element: the digest is absorbed by the base-field sponge.
pub fn vk_digest<L: Lane, EFq>(index: &Idx<L>) -> BaseOf<L>
where
    BaseOf<L>: PrimeField,
    EFq: Clone + FqSponge<BaseOf<L>, L::G, ScalarOf<L>, FULL_ROUNDS>,
{
    index
        .verifier_index
        .as_ref()
        .expect("verifier index")
        .digest::<EFq>()
}

// =================================================================================================
// §6 — prove / verify, kept SEPARATE
// =================================================================================================

/// Prove alone. ⚑ Separated from [`verify_at`] so a refusal can be ATTRIBUTED: a prover-side refusal
/// (the permutation product failing to close) and a verifier-side refusal are different facts, and
/// only the second is evidence about what a chain would accept.
pub fn prove<L: Lane, EFq, EFr>(
    index: &Idx<L>,
    group_map: &Map<L>,
    witness: [Vec<ScalarOf<L>>; COLUMNS],
) -> Result<Proof<L>, String>
where
    BaseOf<L>: PrimeField,
    EFq: Clone + FqSponge<BaseOf<L>, L::G, ScalarOf<L>, FULL_ROUNDS>,
    EFr: kimchi::plonk_sponge::FrSponge<ScalarOf<L>>
        + From<&'static mina_poseidon::poseidon::ArithmeticSpongeParams<ScalarOf<L>, FULL_ROUNDS>>,
{
    ProverProof::create::<EFq, EFr, _>(group_map, witness, &[], index, &mut rand::rngs::OsRng)
        .map_err(|e| format!("prove rejected: {e:?}"))
}

/// Verify an existing proof at a public input the caller chooses. **This is the half a chain runs.**
pub fn verify_at<L: Lane, EFq, EFr>(
    index: &Idx<L>,
    group_map: &Map<L>,
    proof: &Proof<L>,
    public_input: &[ScalarOf<L>],
) -> Result<(), String>
where
    BaseOf<L>: PrimeField,
    EFq: Clone + FqSponge<BaseOf<L>, L::G, ScalarOf<L>, FULL_ROUNDS>,
    EFr: kimchi::plonk_sponge::FrSponge<ScalarOf<L>>
        + From<&'static mina_poseidon::poseidon::ArithmeticSpongeParams<ScalarOf<L>, FULL_ROUNDS>>,
{
    let vk = index.verifier_index.as_ref().expect("verifier index");
    let ctx = Context {
        verifier_index: vk,
        proof,
        public_input,
    };
    batch_verify::<FULL_ROUNDS, L::G, EFq, EFr, OpeningProof<L::G, FULL_ROUNDS>>(group_map, &[ctx])
        .map_err(|e| format!("verify rejected: {e:?}"))
}

/// Prove + verify one witness against a fixed index at a given public input. `Ok(())` iff the
/// verifier accepts.
pub fn prove_and_verify<L: Lane, EFq, EFr>(
    index: &Idx<L>,
    group_map: &Map<L>,
    witness: [Vec<ScalarOf<L>>; COLUMNS],
    public_input: &[ScalarOf<L>],
) -> Result<(), String>
where
    BaseOf<L>: PrimeField,
    EFq: Clone + FqSponge<BaseOf<L>, L::G, ScalarOf<L>, FULL_ROUNDS>,
    EFr: kimchi::plonk_sponge::FrSponge<ScalarOf<L>>
        + From<&'static mina_poseidon::poseidon::ArithmeticSpongeParams<ScalarOf<L>, FULL_ROUNDS>>,
{
    let proof = prove::<L, EFq, EFr>(index, group_map, witness)?;
    verify_at::<L, EFq, EFr>(index, group_map, &proof, public_input)
}

/// The group map the prover and verifier share.
pub fn group_map<L: Lane>() -> Map<L> {
    <L::G as CommitmentCurve>::Map::setup()
}

// =================================================================================================
// §7 — the two lanes, spelled out so a harness names ONE type
// =================================================================================================

/// The step lane's four entry points, with both sponges already chosen.
pub mod step {
    use super::*;
    pub type F = mina_curves::pasta::Fp;
    pub type Index = Idx<Step>;
    pub type StepProof = Proof<Step>;
    pub type Map = super::Map<Step>;

    pub fn index_for(c: &CircuitJson, o: IndexOpts) -> Index {
        super::index_for::<Step, StepBaseSponge>(c, o)
    }
    pub fn index_from_gates(gates: Vec<CircuitGate<F>>, o: IndexOpts) -> Index {
        super::index_from_gates::<Step, StepBaseSponge>(gates, o)
    }
    pub fn vk_digest(index: &Index) -> mina_curves::pasta::Fq {
        super::vk_digest::<Step, StepBaseSponge>(index)
    }
    pub fn prove(index: &Index, gm: &Map, witness: [Vec<F>; COLUMNS]) -> Result<StepProof, String> {
        super::prove::<Step, StepBaseSponge, StepScalarSponge>(index, gm, witness)
    }
    pub fn verify_at(
        index: &Index,
        gm: &Map,
        proof: &StepProof,
        public_input: &[F],
    ) -> Result<(), String> {
        super::verify_at::<Step, StepBaseSponge, StepScalarSponge>(index, gm, proof, public_input)
    }
    pub fn prove_and_verify(
        index: &Index,
        gm: &Map,
        witness: [Vec<F>; COLUMNS],
        public_input: &[F],
    ) -> Result<(), String> {
        super::prove_and_verify::<Step, StepBaseSponge, StepScalarSponge>(
            index,
            gm,
            witness,
            public_input,
        )
    }
    pub fn group_map() -> Map {
        super::group_map::<Step>()
    }
    pub fn gates(c: &CircuitJson) -> Vec<CircuitGate<F>> {
        build_gates(c)
    }
    pub fn witness(c: &CircuitJson) -> [Vec<F>; COLUMNS] {
        build_witness(c)
    }
    pub fn public(c: &CircuitJson) -> Vec<F> {
        build_public(c)
    }
}

/// The wrap lane's four entry points. ⚑ `Fq`, not `Fp`: a step-side coefficient reduced mod the
/// other prime would parse here and mean something else — which is what [`try_parse_field`]'s
/// canonicality refusal is for.
pub mod wrap {
    use super::*;
    pub type F = mina_curves::pasta::Fq;
    pub type Index = Idx<Wrap>;
    pub type WrapProof = Proof<Wrap>;
    pub type Map = super::Map<Wrap>;

    pub fn index_for(c: &CircuitJson, o: IndexOpts) -> Index {
        super::index_for::<Wrap, WrapBaseSponge>(c, o)
    }
    pub fn index_from_gates(gates: Vec<CircuitGate<F>>, o: IndexOpts) -> Index {
        super::index_from_gates::<Wrap, WrapBaseSponge>(gates, o)
    }
    pub fn vk_digest(index: &Index) -> mina_curves::pasta::Fp {
        super::vk_digest::<Wrap, WrapBaseSponge>(index)
    }
    pub fn prove(index: &Index, gm: &Map, witness: [Vec<F>; COLUMNS]) -> Result<WrapProof, String> {
        super::prove::<Wrap, WrapBaseSponge, WrapScalarSponge>(index, gm, witness)
    }
    pub fn verify_at(
        index: &Index,
        gm: &Map,
        proof: &WrapProof,
        public_input: &[F],
    ) -> Result<(), String> {
        super::verify_at::<Wrap, WrapBaseSponge, WrapScalarSponge>(index, gm, proof, public_input)
    }
    pub fn prove_and_verify(
        index: &Index,
        gm: &Map,
        witness: [Vec<F>; COLUMNS],
        public_input: &[F],
    ) -> Result<(), String> {
        super::prove_and_verify::<Wrap, WrapBaseSponge, WrapScalarSponge>(
            index,
            gm,
            witness,
            public_input,
        )
    }
    pub fn group_map() -> Map {
        super::group_map::<Wrap>()
    }
    pub fn gates(c: &CircuitJson) -> Vec<CircuitGate<F>> {
        build_gates(c)
    }
    pub fn witness(c: &CircuitJson) -> [Vec<F>; COLUMNS] {
        build_witness(c)
    }
    pub fn public(c: &CircuitJson) -> Vec<F> {
        build_public(c)
    }
}

// =================================================================================================
// §8 — the driver's own tests. They are about the READER, not about any circuit.
// =================================================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use mina_curves::pasta::{Fp, Fq};

    /// ⚑ THE REFUSAL BITES, AND `from_str` DOES NOT. The Fq modulus is above the Fp one, so an Fq
    /// element in the window `[p, q)` is a wrap-side value that `Fp::from_str` accepts and reduces.
    /// Here it is an error.
    #[test]
    fn a_non_canonical_literal_is_refused_not_reduced() {
        let p: BigUint = BigUint::from_bytes_le(&<Fp as PrimeField>::MODULUS.to_bytes_le());
        let q: BigUint = BigUint::from_bytes_le(&<Fq as PrimeField>::MODULUS.to_bytes_le());
        assert!(p < q, "Fp's modulus is the smaller of the two pasta primes");
        // A value inside the window only Fq can hold canonically.
        let in_window = (&p + &q) / 2u32;
        let s = in_window.to_string();

        // ark-ff would take it silently…
        let reduced = Fp::from_str(&s).expect("ark-ff reduces rather than refusing");
        assert_ne!(
            reduced.into_bigint().to_bytes_le(),
            in_window.to_bytes_le(),
            "if this ever holds, ark-ff stopped reducing and this test lost its subject"
        );
        // …and this driver does not.
        assert!(
            try_parse_field::<Fp>(&s).is_err(),
            "a literal at or above Fp's modulus must be REFUSED, not wrapped"
        );
        // The same literal IS canonical for Fq, and parses.
        assert!(try_parse_field::<Fq>(&s).is_ok());
    }

    /// The modulus itself is out of range; the modulus minus one is not.
    #[test]
    fn the_boundary_is_the_modulus() {
        let p: BigUint = BigUint::from_bytes_le(&<Fp as PrimeField>::MODULUS.to_bytes_le());
        assert!(try_parse_field::<Fp>(&p.to_string()).is_err());
        assert!(try_parse_field::<Fp>(&(&p - 1u32).to_string()).is_ok());
        assert!(try_parse_field::<Fp>(&format!("-{}", &p - 1u32)).is_ok());
        assert!(try_parse_field::<Fp>(&format!("-{p}")).is_err());
    }

    /// ⚑ SIGNS. The Lean renderer emits signed decimals (`-35` is a real generic-gate coefficient),
    /// and a reader that dropped the sign would build a different circuit that still proves.
    #[test]
    fn a_negative_literal_is_the_additive_inverse() {
        assert_eq!(try_parse_field::<Fp>("-35").unwrap(), -Fp::from(35u64));
        assert_eq!(try_parse_field::<Fp>("0").unwrap(), Fp::from(0u64));
        assert_eq!(try_parse_field::<Fp>("-0").unwrap(), Fp::from(0u64));
    }

    /// ⚠ …and the `i128` reader `pickles-r4-harness` carried could not do this at all: the smallest
    /// Poseidon round constant in the emission is wider than 127 bits.
    #[test]
    fn a_wide_literal_round_trips() {
        let s = "7555220006856562833147743033256142154591945963958408607501861037584894828141";
        let v = try_parse_field::<Fp>(s).expect("a 253-bit canonical Fp element");
        assert_eq!(v.into_bigint().to_string(), s);
        assert!(s.parse::<i128>().is_err(), "i128 cannot hold this");
    }

    /// A garbage literal is an error, not a zero.
    #[test]
    fn a_non_numeric_literal_is_refused() {
        assert!(try_parse_field::<Fp>("").is_err());
        assert!(try_parse_field::<Fp>("0x10").is_err());
        assert!(try_parse_field::<Fp>("nope").is_err());
    }

    /// The gate table covers exactly the seven Mina types, and an eighth ordinal stops the run.
    #[test]
    fn the_gate_table_is_the_seven_mina_types() {
        for (o, t) in [
            (0, GateType::Zero),
            (1, GateType::Generic),
            (2, GateType::Poseidon),
            (3, GateType::CompleteAdd),
            (4, GateType::VarBaseMul),
            (5, GateType::EndoMul),
            (6, GateType::EndoMulScalar),
        ] {
            assert_eq!(gate_type_from_ordinal(o), t);
        }
        assert!(std::panic::catch_unwind(|| gate_type_from_ordinal(7)).is_err());
    }

    /// ⚑ ABSENT IS NOT EMPTY. The Lean side distinguishes `"public_input":[]` from no key at all,
    /// and this reader must carry that distinction rather than flattening it to `vec![]`.
    #[test]
    fn an_absent_public_input_is_not_an_empty_one() {
        let with: CircuitJson = serde_json::from_str(
            r#"{"name":"a","public_input_size":0,"public_input":[],"num_rows":0,
                "gates":[],"witness":[]}"#,
        )
        .unwrap();
        let without: CircuitJson = serde_json::from_str(
            r#"{"name":"a","public_input_size":0,"num_rows":0,"gates":[],"witness":[]}"#,
        )
        .unwrap();
        assert_eq!(with.public_input, Some(vec![]));
        assert_eq!(without.public_input, None);
    }

    /// The slot census parses as a pair when the wrap side emits it, and is absent otherwise.
    #[test]
    fn the_slot_census_is_read_off_the_emission() {
        let c: CircuitJson = serde_json::from_str(
            r#"{"name":"w","public_input_size":2,"public_input":["1","2"],
                "derived_slots":[0,1],"unread_slots":[7],"num_rows":0,"probe_rows":[3],
                "gates":[],"witness":[]}"#,
        )
        .unwrap();
        assert_eq!(c.derived_slots, Some(vec![0, 1]));
        assert_eq!(c.unread_slots, Some(vec![7]));
        assert_eq!(c.probes(), &[3]);
    }
}
