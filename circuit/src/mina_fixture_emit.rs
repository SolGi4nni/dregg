//! **The dregg-side fixture emitter for a Mina/o1js verifier — the ONE copy.**
//!
//! Mint a REAL dregg FRI-STARK proof of the Lean-authored `mina-fixture` AIR at
//! a REDUCED FRI geometry, verify it with dregg's OWN verifier, and emit every
//! field an o1js/Kimchi verifier needs, in CANONICAL form, as one line of JSON.
//!
//! ## ⚑ WHY THIS MODULE IS GENERIC — it is the point, not an extra
//!
//! There are TWO hash suites that must produce the SAME fixture schema:
//!
//! | | commitments hashed with | digest | binary |
//! |---|---|---|---|
//! | BabyBear | `Poseidon2BabyBear<16>` (`DreggStarkConfig`) | `[BabyBear; 8]` | `dregg-circuit`'s `mina_stark_fixture` |
//! | Pasta | Mina-Poseidon over Pasta `Fp` (`DreggMinaConfig`) | `[PastaFp; 1]` | `dregg-circuit-prove`'s `mina_pasta_stark_fixture` |
//!
//! A second, copy-pasted emitter for the Pasta suite would be an instance of
//! this repo's named failure class — *two shapes that agree today are two
//! shapes that will disagree later*. So the trace, the AIR, the tamper modes,
//! the domain constants, the constraint cross-check and the JSON layout have
//! **exactly one definition each, here**, and the two binaries are thin
//! instantiations of [`FixtureHashSuite`]. The only things a suite supplies are
//! the two things that genuinely differ: **how a digest is written** and **how
//! the verifier's transcript is replayed**.
//!
//! `dregg-circuit-prove` depends on `dregg-circuit`, never the reverse, so the
//! generic half and the BabyBear suite live here (Poseidon2-BabyBear is a
//! `dregg-circuit` dependency) and the Pasta suite lives downstream in
//! `dregg-circuit-prove::mina_pasta_fixture_suite` (there is no `p3-pasta`
//! here, deliberately: the verify floor takes no Pasta dependency).
//!
//! ## ⚑ The Rust verifier accepts BEFORE anything is written
//!
//! [`run`] calls `p3_uni_stark::verify` and aborts on failure, so a fixture that
//! reaches the o1js side is one dregg itself accepts. It ALSO proves the
//! negative: the `tamper` argument bends one field and the emitter REQUIRES its
//! own verifier to refuse — an emitter whose verifier cannot say no is not a
//! check.
//!
//! ## ⚑ Canonical, not Montgomery
//!
//! `MontyField31`'s `Serialize` writes the raw Montgomery limb, which is right
//! for p3↔p3 and WRONG for anyone reading the numbers as field elements. Every
//! BabyBear value here goes through `as_canonical_u32`; every Pasta value goes
//! through `as_canonical_biguint` and is written as a DECIMAL STRING, because a
//! 254-bit integer is not a JSON number.
//!
//! ## ⚑ WHAT THE AIR IS — AUTHORED IN LEAN
//!
//! The AIR is authored in `metatheory/Dregg2/Circuit/Emit/MinaFixtureEmit.lean`,
//! emitted to `circuit/descriptors/by-name/mina-fixture.json`, and INTERPRETED
//! here by [`Ir2UniAir`]. **This file constructs no constraint.** It did until
//! 2026-07-30, when `impl<AB: AirBuilder> Air<AB> for MinaFixtureAir` was a
//! hand-written Rust AIR, caught red by `law1_enforcement_gate` and recorded as
//! HORIZONLOG E4. Emitting it from Lean is the remedy that gate names.
//!
//! It is a 3-column, degree-3 AIR — NOT one of dregg's seven root tables. It is
//! here because the o1js side must evaluate `C_i` itself for the verifier to be
//! closed rather than PCS-only, and dregg's real AIRs are uncounted
//! (`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.14). It is chosen to exercise
//! every arm the protocol arithmetic has: **all three Lagrange selectors**, a
//! **next-row** reference (so `zeta` and `g*zeta` are both opened and the DEEP
//! quotient runs at two points), **public values** in the transcript AND in a
//! constraint, and a **degree-3** constraint so the quotient really splits into
//! more than one chunk.
//!
//! Trace, `n = 2^degree_bits` rows, columns `[a, b, c]`:
//!   * `b_i = a_i^3`
//!   * `c_0 = pis[0]`, `c_{i+1} = c_i + b_i`, `c_{n-1} = pis[1]`
//!
//! Both directions of that shape are PROVED against the emitted descriptor, not
//! asserted here: `mina_forces_cube` / `mina_forces_first_pi` /
//! `mina_forces_running_sum` / `mina_forces_last_pi` (a satisfying window has
//! this shape) and `mina_window_holds_of_shape` (this shape satisfies).
//!
//! ⚑ **The emission order is the folding order**, and it is the LEAN LIST's
//! order: `Ir2UniAir` walks `constraints` in list order precisely so the
//! descriptor — not a Rust traversal — is what
//! `bridge/mina-zkapp/src/DreggProofVerify.ts::minaFixtureConstraints` has to
//! agree with.

use std::fmt::Write as _;

use p3_air::BaseAir;
use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{
    CanObserve, CanSample, CanSampleBits, DuplexChallenger, FieldChallenger, GrindingChallenger,
};
use p3_commit::{BatchOpening, Mmcs, PolynomialSpace};
use p3_dft::Radix2DitParallel;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::extension::BinomialExtensionField;
use p3_field::{
    BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField, PrimeField32, TwoAdicField,
};
use p3_fri::{FriProof, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_symmetric::MerkleCap;
use p3_uni_stark::{
    Proof, StarkGenericConfig, prove, recompose_quotient_from_chunks, verify, verify_constraints,
};

use crate::descriptor_ir2::{Ir2UniAir, parse_vm_descriptor2};
use crate::plonky3_prover::{DreggStarkConfig, create_config_with_fri_full};

/// Trace/arithmetic field. **Unchanged by the hash swap** — only the commitment
/// hash moves between the two suites.
pub type F = BabyBear;
/// Challenge field: the degree-4 BabyBear extension every dregg config uses.
pub type EF = BinomialExtensionField<BabyBear, 4>;
/// Challenge extension degree, written out because the fixture carries it.
pub const EXT_DEGREE: usize = 4;
/// Both suites use the same DFT; it is not a hash-suite parameter.
pub type FixtureDft = Radix2DitParallel<F>;

/// The FRI proof object of a suite, spelled out so generic code can walk it.
pub type FixtureFriProof<S, const N: usize> = FriProof<
    EF,
    <S as FixtureHashSuite<N>>::ChallengeMmcs,
    F,
    Vec<BatchOpening<F, <S as FixtureHashSuite<N>>::ValMmcs>>,
>;

// ===========================================================================
// The AIR — DECODED, not authored.
// ===========================================================================

/// The Lean-authored descriptor, byte-pinned on the Lean side by
/// `MinaFixtureEmit.lean`'s `#guard emitVmJson2 minaFixtureDesc == "..."` and
/// re-derived from that module on every `scripts/check-descriptor-drift.sh` run
/// (it is routed in `metatheory/EmitByName.lean`). Three-sided closure:
/// Lean-emit ≡ this golden ≡ what `parse_vm_descriptor2` decodes below.
const FIXTURE_DESCRIPTOR_JSON: &str = include_str!("../descriptors/by-name/mina-fixture.json");

/// Decode the golden into the AIR the prover runs.
///
/// The shape assertions are the Rust half of the byte-pin: the Lean side
/// `#guard`s the same four numbers (`§2a`), so a descriptor swapped underneath
/// these binaries — a different width, a dropped constraint — stops them here
/// rather than minting a proof of a different AIR that the o1js twin would then
/// be checked against.
pub fn fixture_air() -> Ir2UniAir {
    let desc = parse_vm_descriptor2(FIXTURE_DESCRIPTOR_JSON)
        .expect("the byte-pinned mina-fixture descriptor must decode");
    assert_eq!(
        desc.name, "dregg-mina-stark-fixture-v1",
        "descriptor identity"
    );
    assert_eq!(desc.trace_width, 3, "descriptor trace width");
    assert_eq!(desc.public_input_count, 2, "descriptor public-input count");
    assert_eq!(desc.constraints.len(), 4, "descriptor constraint count");
    Ir2UniAir::new(desc).expect("the fixture descriptor is bus-free and single-table")
}

/// The honest trace and its two public values.
pub fn build_trace(degree_bits: usize, seed: u64) -> (RowMajorMatrix<F>, Vec<F>) {
    let n = 1usize << degree_bits;
    let mut a_vals = Vec::with_capacity(n);
    let mut x = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    for _ in 0..n {
        x = x
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        a_vals.push(F::from_u32(((x >> 33) as u32) % 1_000_003));
    }
    let mut values = Vec::with_capacity(n * 3);
    let c0 = F::from_u32(7);
    let mut c = c0;
    for i in 0..n {
        let a = a_vals[i];
        let b = a * a * a;
        values.push(a);
        values.push(b);
        values.push(c);
        c += b;
    }
    // `c` now holds `c_0 + sum_i b_i`; the LAST row's `c` is what C3 pins.
    let c_last = values[(n - 1) * 3 + 2];
    (RowMajorMatrix::new(values, 3), vec![c0, c_last])
}

// ===========================================================================
// Canonical encoders.
// ===========================================================================

/// Canonical `u32` of a BabyBear element — never the Montgomery limb.
pub fn f_u32(v: F) -> u32 {
    v.as_canonical_u32()
}
/// The four canonical BabyBear limbs of a challenge element.
pub fn ef_limbs(v: EF) -> Vec<u32> {
    v.as_basis_coefficients_slice()
        .iter()
        .map(|x| f_u32(*x))
        .collect()
}
/// A JSON array of already-rendered elements.
pub fn arr(vals: impl IntoIterator<Item = String>) -> String {
    let mut s = String::from("[");
    for (i, v) in vals.into_iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str(&v);
    }
    s.push(']');
    s
}
/// A JSON array of numbers.
pub fn nums(vals: impl IntoIterator<Item = u32>) -> String {
    arr(vals.into_iter().map(|v| v.to_string()))
}
/// One challenge element as `[c0,c1,c2,c3]`.
pub fn ef_json(v: EF) -> String {
    nums(ef_limbs(v))
}
/// A list of challenge elements.
pub fn ef_list(vs: &[EF]) -> String {
    arr(vs.iter().map(|v| ef_json(*v)))
}

// ===========================================================================
// The two things a hash suite actually changes.
// ===========================================================================

/// The transcript half of a hash suite: a recording replay of the challenger the
/// deployed verifier runs.
///
/// ⚑ **A transcript twin that agrees with its own reading proves nothing.** The
/// replay this drives is handed to p3's OWN `verify_constraints` over p3's OWN
/// `recompose_quotient_from_chunks` (see [`run`]); both are functions of the
/// sampled challenges, so an honest fixture is emitted only if the replay
/// reproduced the verifier's transcript exactly.
pub trait FixtureTranscript<const DIGEST_ELEMS: usize> {
    /// The field one commitment-digest word lives in.
    type Word;

    /// Absorb one base-field element.
    fn observe_f(&mut self, v: F);
    /// Absorb one commitment digest. ⚑ For a MultiField challenger this is NOT
    /// the same as absorbing the digest's base-field limbs — see the Pasta suite.
    fn observe_digest(&mut self, d: &[Self::Word; DIGEST_ELEMS]);
    /// Squeeze one challenge-field element.
    fn sample_ext(&mut self) -> EF;
    /// p3's `GrindingChallenger::check_witness`: `bits == 0` is a no-op that
    /// returns `true`; otherwise absorb `w` and require the next `bits` sampled
    /// bits to be zero.
    fn check_witness(&mut self, bits: usize, w: F) -> bool;
    /// Squeeze `bits` bits (the low bits of one sampled base element).
    fn sample_bits(&mut self, bits: usize) -> usize;
    /// The suite's own tail of the `"challenges"` object: the record of HOW the
    /// transcript got where it got, so the o1js side can be checked against the
    /// derivation and not only against its outputs. Rendered WITHOUT a leading
    /// comma and WITHOUT enclosing braces.
    fn record_json(&self) -> String;

    /// Absorb a slice of base elements.
    fn observe_slice(&mut self, vs: &[F]) {
        for v in vs {
            self.observe_f(*v);
        }
    }
    /// Absorb one challenge element as its base-field coefficients — exactly
    /// what `observe_algebra_slice` does.
    fn observe_ext(&mut self, v: EF) {
        let coeffs: Vec<F> = v.as_basis_coefficients_slice().to_vec();
        self.observe_slice(&coeffs);
    }
}

/// A hash suite: everything that changes when the commitment hash moves from
/// Poseidon2-over-BabyBear to Mina-Poseidon-over-Pasta.
///
/// `DIGEST_ELEMS` is a const parameter rather than an associated const because
/// the digest arrays `[Word; DIGEST_ELEMS]` appear in the MMCS types.
pub trait FixtureHashSuite<const DIGEST_ELEMS: usize>: Sized {
    /// One digest word.
    type Word: PrimeField;
    /// The base-field MMCS (trace + quotient commitments, input openings).
    type ValMmcs: Mmcs<
            F,
            Commitment = MerkleCap<F, [Self::Word; DIGEST_ELEMS]>,
            Proof = Vec<[Self::Word; DIGEST_ELEMS]>,
            Proof: Sync,
            Error: Sync,
        >;
    /// The challenge-field MMCS (FRI commit phase). Its commitment and proof are
    /// the base MMCS's, since it is an `ExtensionMmcs` over it.
    type ChallengeMmcs: Mmcs<
            EF,
            Commitment = MerkleCap<F, [Self::Word; DIGEST_ELEMS]>,
            Proof = Vec<[Self::Word; DIGEST_ELEMS]>,
        >;
    /// The config's Fiat–Shamir challenger.
    ///
    /// ⚑ It is an associated type of the SUITE rather than being read off
    /// `Config` because reading it off `Config` is a cycle rustc cannot close:
    /// `StarkGenericConfig::Challenger`'s own bound mentions `Val<Self>`, which
    /// projects through `Pcs::Domain`, which needs the challenger's bounds —
    /// `E0275: overflow evaluating the requirement`. Naming it here states those
    /// bounds ONCE, without going through `Config`.
    type Challenger: FieldChallenger<F>
        + CanObserve<MerkleCap<F, [Self::Word; DIGEST_ELEMS]>>
        + CanSample<EF>
        + GrindingChallenger<Witness = F>;
    /// The STARK config. Pinned to the SAME `TwoAdicFriPcs` shape for both
    /// suites: only the MMCS hash moves.
    type Config: StarkGenericConfig<
            Challenge = EF,
            Challenger = Self::Challenger,
            Pcs = TwoAdicFriPcs<F, FixtureDft, Self::ValMmcs, Self::ChallengeMmcs>,
        >;
    /// The recording replay of `Config::Challenger`.
    type Transcript: FixtureTranscript<DIGEST_ELEMS, Word = Self::Word>;

    /// The `"hash"` discriminant the o1js consumer dispatches on.
    const HASH_NAME: &'static str;
    /// ⚑ The NATIVE-HASH CANARY, as a per-suite bit floor a digest word of an
    /// honest proof must exceed.
    ///
    /// **Pasta: 31.** A Merkle root that fits in 31 bits means the Mina-Poseidon
    /// hash never reached the commitment — the same runtime canary
    /// `circuit-prove/tests/mina_terminal_tooth.rs` runs, and the reason it
    /// exists is that a hash swap which silently no-ops still type-checks.
    ///
    /// **BabyBear: 0, and the check is SKIPPED rather than run vacuously.**
    /// There the digest word field IS `Val`, so there is no foreign-field
    /// confusion to catch and a "check" would be a no-op wearing a check's name.
    const MIN_DIGEST_WORD_BITS: u64;

    /// Build the config at the fixture's reduced FRI geometry.
    /// `log_final_poly_len = 0`, `max_log_arity = 1`, `commit_pow_bits = 0` are
    /// fixed by the fixture (and asserted in the emitted `knobs`).
    fn config(log_blowup: usize, num_queries: usize, query_pow_bits: usize) -> Self::Config;
    /// A fresh recording transcript in the config's initial state.
    fn new_transcript() -> Self::Transcript;
    /// JSON for ONE digest. ⚑ Always an ARRAY of `DIGEST_ELEMS` elements, in
    /// both suites, so the consumer's shape code is shared: BabyBear writes
    /// eight numbers, Pasta writes ONE canonical decimal STRING (a 254-bit
    /// integer exceeds 2^53 and cannot be a JSON number).
    fn digest_json(d: &[Self::Word; DIGEST_ELEMS]) -> String;
}

/// A list of digests.
fn digests_json<S: FixtureHashSuite<N>, const N: usize>(ds: &[[S::Word; N]]) -> String {
    arr(ds.iter().map(S::digest_json))
}

// ===========================================================================
// The replay — p3's own transcript order, so the o1js derivation is KAT'd
// against the deployed state machine rather than against a re-reading of it.
// ===========================================================================

/// What one replay of the verifier's transcript recovers.
pub struct Replay {
    /// Whether `query_pow_witness` really grinds `query_pow_bits` zeros under
    /// THIS transcript. False is a legitimate outcome for a bent fixture.
    pub query_pow_ok: bool,
    pub alpha_stark: EF,
    pub zeta: EF,
    pub fri_alpha: EF,
    pub betas: Vec<EF>,
    pub query_indices: Vec<usize>,
}

/// Replay the verifier's Fiat–Shamir transcript over an emitted proof.
///
/// The order is `p3_uni_stark::verify` → `TwoAdicFriPcs::verify` →
/// `p3_fri::verifier::verify_fri`, and it is the ONLY place that order is
/// written down on the dregg side.
#[allow(clippy::too_many_arguments)]
fn replay<S: FixtureHashSuite<N>, const N: usize>(
    t: &mut S::Transcript,
    proof: &Proof<S::Config>,
    fri: &FixtureFriProof<S, N>,
    public_values: &[F],
    preprocessed_width: usize,
    base_degree_bits: usize,
    query_pow_bits: usize,
    log_global_max_height: usize,
    num_queries: usize,
) -> Replay {
    t.observe_f(F::from_usize(proof.degree_bits));
    t.observe_f(F::from_usize(base_degree_bits));
    t.observe_f(F::from_usize(preprocessed_width));
    for d in proof.commitments.trace.as_ref() {
        t.observe_digest(d);
    }
    t.observe_slice(public_values);
    let alpha_stark = t.sample_ext();
    for d in proof.commitments.quotient_chunks.as_ref() {
        t.observe_digest(d);
    }
    let zeta = t.sample_ext();

    // `two_adic_pcs::verify` observes every opened evaluation, in round order,
    // BEFORE `verify_fri` samples its own alpha (`two_adic_pcs.rs:686-692`).
    let ov = &proof.opened_values;
    for v in &ov.trace_local {
        t.observe_ext(*v);
    }
    if let Some(next) = &ov.trace_next {
        for v in next {
            t.observe_ext(*v);
        }
    }
    for chunk in &ov.quotient_chunks {
        for v in chunk {
            t.observe_ext(*v);
        }
    }

    let fri_alpha = t.sample_ext();
    let mut betas = Vec::new();
    for (commit, w) in fri
        .commit_phase_commits
        .iter()
        .zip(&fri.commit_pow_witnesses)
    {
        for d in commit.as_ref() {
            t.observe_digest(d);
        }
        assert!(t.check_witness(0, *w), "commit-phase PoW is 0 bits here");
        betas.push(t.sample_ext());
    }
    for coeff in &fri.final_poly {
        t.observe_ext(*coeff);
    }
    for qp in fri.query_proofs[0].commit_phase_openings.iter() {
        t.observe_f(F::from_usize(qp.log_arity as usize));
    }
    // ⚑ NOT AN ASSERT. A bent fixture is SUPPOSED to break something, and for a
    // bend upstream of the grind (an opened value, the final polynomial, the
    // witness itself) the thing it breaks IS this. Recording it keeps the
    // emitter able to describe a proof its own verifier refuses — which is the
    // fixture the o1js side needs in order to be shown refusing too.
    let query_pow_ok = t.check_witness(query_pow_bits, fri.query_pow_witness);
    let query_indices = (0..num_queries)
        .map(|_| t.sample_bits(log_global_max_height))
        .collect();

    Replay {
        query_pow_ok,
        alpha_stark,
        zeta,
        fri_alpha,
        betas,
        query_indices,
    }
}

// ===========================================================================
// Tamper modes.
// ===========================================================================

/// Every tamper mode this emitter knows, in the order the o1js side should run
/// them. Each arm targets a DIFFERENT layer, so a leg that runs all of them
/// cannot pass by catching one thing four times.
pub const TAMPER_MODES: [&str; 7] = [
    "opened",
    "quotient",
    "finalpoly",
    "sibling",
    "inputrow",
    "inputpath",
    "querypow",
];

/// Bend one field of an honest proof.
fn bend<S: FixtureHashSuite<N>, const N: usize>(
    p: &Proof<S::Config>,
    which: &str,
) -> Proof<S::Config> {
    let mut q = clone_proof::<S, N>(p);
    match which {
        // The claimed out-of-domain evaluation. Moves the AIR closing equality
        // AND every downstream challenge (it is absorbed before alpha).
        "opened" => q.opened_values.trace_local[0] += EF::ONE,
        // A quotient chunk: the AIR side only.
        "quotient" => q.opened_values.quotient_chunks[0][0] += EF::ONE,
        // The final polynomial the fold chain must land on.
        "finalpoly" => q.opening_proof.final_poly[0] += EF::ONE,
        // A commit-phase sibling: the fold chain's own input.
        "sibling" => {
            q.opening_proof.query_proofs[0].commit_phase_openings[0].sibling_values[0] += EF::ONE
        }
        // An input-phase opened row element: the Merkle opening AND the DEEP
        // quotient both depend on it.
        "inputrow" => q.opening_proof.query_proofs[0].input_proof[0].opened_values[0][0] += F::ONE,
        // A Merkle sibling on the input path: the opening only.
        "inputpath" => {
            q.opening_proof.query_proofs[0].input_proof[0].opening_proof[0][0] += S::Word::ONE
        }
        // The query PoW witness: the grind and every index after it.
        "querypow" => q.opening_proof.query_pow_witness += F::ONE,
        other => panic!("unknown tamper mode '{other}'"),
    }
    q
}

/// `Proof<SC>` is not `Clone`, and re-proving would give a different (equally
/// honest) object, so the bend has to start from a structural copy of THIS one.
fn clone_proof<S: FixtureHashSuite<N>, const N: usize>(p: &Proof<S::Config>) -> Proof<S::Config> {
    let bytes = postcard::to_allocvec(p).expect("postcard round-trip of the emitted proof");
    postcard::from_bytes(&bytes).expect("postcard round-trip of the emitted proof")
}

// ===========================================================================
// The whole run: prove, verify, (bend, require refusal), replay, cross-check,
// emit.
// ===========================================================================

/// The emitter's argument vector, in the order both binaries take it:
/// `<degree_bits> <log_blowup> <num_queries> <query_pow_bits> [seed] [tamper]`.
pub struct FixtureArgs {
    pub degree_bits: usize,
    pub log_blowup: usize,
    pub num_queries: usize,
    pub query_pow_bits: usize,
    pub seed: u64,
    pub tamper: String,
}

impl FixtureArgs {
    /// Parse `std::env::args()`. A malformed argument is a hard failure: a
    /// fixture emitted at a geometry nobody asked for is worse than none.
    pub fn from_env() -> Self {
        let args: Vec<String> = std::env::args().collect();
        Self {
            degree_bits: args.get(1).map_or(2, |s| s.parse().unwrap()),
            log_blowup: args.get(2).map_or(1, |s| s.parse().unwrap()),
            num_queries: args.get(3).map_or(1, |s| s.parse().unwrap()),
            query_pow_bits: args.get(4).map_or(16, |s| s.parse().unwrap()),
            seed: args.get(5).map_or(1, |s| s.parse().unwrap()),
            tamper: args.get(6).cloned().unwrap_or_else(|| String::from("none")),
        }
    }
}

/// Mint, verify, replay and print one fixture. Prints exactly one line of JSON
/// to stdout.
pub fn run<S: FixtureHashSuite<N>, const N: usize>(args: &FixtureArgs) {
    let config = S::config(args.log_blowup, args.num_queries, args.query_pow_bits);
    let air = fixture_air();
    let (matrix, pis) = build_trace(args.degree_bits, args.seed);

    let proof = prove(&config, &air, matrix, &pis);
    verify(&config, &air, &proof, &pis)
        .expect("dregg's OWN verifier must accept before anything is emitted");

    // ⚑ THE NATIVE-HASH CANARY. Runs on the HONEST proof, before any bend, so a
    // hash swap that silently no-opped is caught here rather than being read
    // back off the JSON as a Pasta commitment that is really a BabyBear one.
    assert_native_digests::<S, N>(&proof);

    // ⚑ THE EMITTER PROVES ITS OWN VERIFIER CAN SAY NO. A `tamper` mode that no
    // longer matches its target silently becomes a passing test, so the bend is
    // applied to the SAME structure that is emitted, and refusal is REQUIRED.
    if args.tamper != "none" {
        let bent = bend::<S, N>(&proof, &args.tamper);
        assert!(
            verify(&config, &air, &bent, &pis).is_err(),
            "the '{}' bend was ACCEPTED by dregg's verifier — the fault no longer reaches \
             anything, and any o1js leg built on it is vacuous",
            args.tamper
        );
        println!("{}", emit::<S, N>(&bent, &pis, args));
        return;
    }

    println!("{}", emit::<S, N>(&proof, &pis, args));
}

/// The suite's runtime canary that the commitments really were hashed in its
/// own field. See [`FixtureHashSuite::MIN_DIGEST_WORD_BITS`].
fn assert_native_digests<S: FixtureHashSuite<N>, const N: usize>(proof: &Proof<S::Config>) {
    if S::MIN_DIGEST_WORD_BITS == 0 {
        return;
    }
    for (what, cap) in [
        ("trace", proof.commitments.trace.as_ref()),
        ("quotient", proof.commitments.quotient_chunks.as_ref()),
    ] {
        assert!(!cap.is_empty(), "{what} commitment has no roots");
        for root in cap {
            for w in root.iter() {
                assert!(
                    w.as_canonical_biguint().bits() > S::MIN_DIGEST_WORD_BITS,
                    "{what} root word fits in {} bits — the commitment does not look native to \
                     {}; the hash swap did not reach the Merkle tree",
                    S::MIN_DIGEST_WORD_BITS,
                    S::HASH_NAME
                );
            }
        }
    }
}

/// Render one fixture. Hash-independent end to end except for
/// [`FixtureHashSuite::digest_json`] and the transcript record.
fn emit<S: FixtureHashSuite<N>, const N: usize>(
    proof: &Proof<S::Config>,
    pis: &[F],
    args: &FixtureArgs,
) -> String {
    let air = fixture_air();
    let degree_bits = args.degree_bits;
    let log_blowup = args.log_blowup;
    let num_queries = args.num_queries;
    let query_pow_bits = args.query_pow_bits;
    let tamper = args.tamper.as_str();

    // `TwoAdicFriPcs::natural_domain_for_degree` IS `TwoAdicMultiplicativeCoset::
    // new(ONE, log2(degree))` (`two_adic_pcs.rs:376-378`); taking it directly
    // sidesteps the `Pcs<_, Challenger>` inference without changing the object.
    let base_degree_bits = degree_bits; // is_zk = 0 for this PCS
    let trace_domain: TwoAdicMultiplicativeCoset<F> =
        TwoAdicMultiplicativeCoset::new(F::ONE, degree_bits).unwrap();

    let n_chunks = proof.opened_values.quotient_chunks.len();
    let log_num_chunks = n_chunks.trailing_zeros() as usize;
    let quotient_domain = trace_domain.create_disjoint_domain(1 << (degree_bits + log_num_chunks));
    let chunk_domains = quotient_domain.split_domains(n_chunks);

    let fri: &FixtureFriProof<S, N> = &proof.opening_proof;
    let layers = fri.commit_phase_commits.len();
    let log_global_max_height = layers + log_blowup; // log_final_poly_len = 0, arity 1

    let mut transcript = S::new_transcript();
    let rep = replay::<S, N>(
        &mut transcript,
        proof,
        fri,
        pis,
        0,
        base_degree_bits,
        query_pow_bits,
        log_global_max_height,
        num_queries,
    );

    // ⚑ THE REPLAY IS CHECKED AGAINST THE VERIFIER, NOT AGAINST ITSELF. A
    // transcript twin that agrees with its own reading proves nothing; this
    // hands the REPLAYED `zeta` and `alpha` to p3's OWN `verify_constraints`
    // over p3's OWN `recompose_quotient_from_chunks`. Both are functions of the
    // sampled challenges, so this passes only if the replay reproduced the
    // verifier's transcript exactly — and it is skipped for a bent fixture,
    // whose whole point is that some check must fail.
    if tamper == "none" {
        assert!(
            rep.query_pow_ok,
            "an HONEST fixture whose query PoW does not grind means the replay is not the \
             verifier's transcript"
        );
        let quotient = recompose_quotient_from_chunks::<S::Config>(
            &chunk_domains,
            &proof.opened_values.quotient_chunks,
            rep.zeta,
        );
        let zeros = vec![EF::ZERO; <Ir2UniAir as BaseAir<F>>::width(&air)];
        let next = proof
            .opened_values
            .trace_next
            .as_deref()
            .unwrap_or(zeros.as_slice());
        verify_constraints::<S::Config, Ir2UniAir, ()>(
            &air,
            &proof.opened_values.trace_local,
            next,
            None,
            None,
            &[],
            pis,
            trace_domain,
            rep.zeta,
            rep.alpha_stark,
            quotient,
        )
        .expect(
            "the replayed transcript does not reproduce the verifier's zeta/alpha — every \
             challenge this fixture carries would be a different protocol",
        );
    }

    // -- the domain constants the o1js side folds in for free -----------------
    // `selectors_at_point` on the natural trace domain: shift = 1.
    let subgroup_gen_inv = F::two_adic_generator(degree_bits).inverse();
    // `recompose_quotient_from_chunks`: `Z_{D_j}(first_point(D_i))^{-1}`.
    let mut lagrange = Vec::with_capacity(n_chunks);
    for di in &chunk_domains {
        let mut row = Vec::with_capacity(n_chunks);
        for dj in &chunk_domains {
            let v: F = dj.vanishing_poly_at_point(di.first_point());
            row.push(v);
        }
        lagrange.push(row);
    }
    // Invert off the diagonal; the diagonal entry is never read (j != i).
    let lagrange_inv: Vec<Vec<u32>> = lagrange
        .iter()
        .enumerate()
        .map(|(i, row)| {
            row.iter()
                .enumerate()
                .map(|(j, v)| if i == j { 1 } else { f_u32(v.inverse()) })
                .collect()
        })
        .collect();

    let mut o = String::new();
    o.push('{');
    // ⚑ `hash` + `digestElems` are what the o1js consumer DISPATCHES on: the two
    // suites emit the same schema at different digest shapes, and a consumer
    // that has to guess which one it is holding is a consumer that will
    // eventually guess wrong.
    write!(
        o,
        r#""kind":"dregg-uni-stark-fixture","hash":"{}","digestElems":{N},"tamper":"{tamper}","#,
        S::HASH_NAME
    )
    .unwrap();
    write!(
        o,
        r#""knobs":{{"logBlowup":{log_blowup},"logFinalPolyLen":0,"maxLogArity":1,"numQueries":{num_queries},"commitPowBits":0,"queryPowBits":{query_pow_bits},"extDegree":{EXT_DEGREE}}},"#
    )
    .unwrap();
    write!(
        o,
        r#""shape":{{"degreeBits":{},"baseDegreeBits":{base_degree_bits},"preprocessedWidth":0,"airWidth":{},"numPublicValues":{},"numQuotientChunks":{n_chunks},"logNumChunks":{log_num_chunks},"layers":{layers},"logGlobalMaxHeight":{log_global_max_height},"traceLdeLogHeight":{},"quotientLdeLogHeight":{},"hasTraceNext":{}}},"#,
        proof.degree_bits,
        <Ir2UniAir as BaseAir<F>>::width(&air),
        <Ir2UniAir as BaseAir<F>>::num_public_values(&air),
        degree_bits + log_blowup,
        chunk_domains[0].log_size() + log_blowup,
        proof.opened_values.trace_next.is_some(),
    )
    .unwrap();
    write!(
        o,
        r#""domain":{{"traceShiftInv":1,"traceLogSize":{degree_bits},"subgroupGenInv":{},"chunkLogSize":{},"chunkShiftInvs":{},"lagrangeConstInvs":{}}},"#,
        f_u32(subgroup_gen_inv),
        chunk_domains[0].log_size(),
        nums(chunk_domains.iter().map(|d| f_u32(d.shift().inverse()))),
        arr(lagrange_inv.iter().map(|r| nums(r.iter().copied()))),
    )
    .unwrap();
    write!(
        o,
        r#""publicValues":{},"#,
        nums(pis.iter().map(|v| f_u32(*v)))
    )
    .unwrap();

    // -- commitments ---------------------------------------------------------
    write!(
        o,
        r#""commitments":{{"trace":{},"quotient":{}}},"#,
        digests_json::<S, N>(proof.commitments.trace.as_ref()),
        digests_json::<S, N>(proof.commitments.quotient_chunks.as_ref()),
    )
    .unwrap();

    // -- opened values -------------------------------------------------------
    write!(
        o,
        r#""openedValues":{{"traceLocal":{},"traceNext":{},"quotientChunks":{}}},"#,
        ef_list(&proof.opened_values.trace_local),
        match &proof.opened_values.trace_next {
            Some(v) => ef_list(v),
            None => "null".to_string(),
        },
        arr(proof
            .opened_values
            .quotient_chunks
            .iter()
            .map(|c| ef_list(c))),
    )
    .unwrap();

    // -- the FRI proof -------------------------------------------------------
    write!(
        o,
        r#""fri":{{"commitPhaseCommits":{},"commitPowWitnesses":{},"finalPoly":{},"queryPowWitness":{},"#,
        arr(fri
            .commit_phase_commits
            .iter()
            .map(|c| digests_json::<S, N>(c.as_ref()))),
        nums(fri.commit_pow_witnesses.iter().map(|w| f_u32(*w))),
        ef_list(&fri.final_poly),
        f_u32(fri.query_pow_witness),
    )
    .unwrap();
    write!(
        o,
        r#""queryProofs":{}}},"#,
        arr(fri.query_proofs.iter().map(|qp| {
            let inputs = arr(qp.input_proof.iter().map(|b| {
                format!(
                    r#"{{"openedValues":{},"openingProof":{}}}"#,
                    arr(b
                        .opened_values
                        .iter()
                        .map(|m| nums(m.iter().map(|v| f_u32(*v))))),
                    digests_json::<S, N>(&b.opening_proof),
                )
            }));
            let steps = arr(qp.commit_phase_openings.iter().map(|s| {
                format!(
                    r#"{{"logArity":{},"siblingValues":{},"openingProof":{}}}"#,
                    s.log_arity,
                    ef_list(&s.sibling_values),
                    digests_json::<S, N>(&s.opening_proof),
                )
            }));
            format!(r#"{{"inputProof":{inputs},"commitPhaseOpenings":{steps}}}"#)
        })),
    )
    .unwrap();

    // -- what p3's OWN challenger produced -----------------------------------
    write!(
        o,
        r#""challenges":{{"queryPowOk":{},"alphaStark":{},"zeta":{},"friAlpha":{},"betas":{},"queryIndices":{},{}}}"#,
        rep.query_pow_ok,
        ef_json(rep.alpha_stark),
        ef_json(rep.zeta),
        ef_json(rep.fri_alpha),
        ef_list(&rep.betas),
        arr(rep.query_indices.iter().map(|i| i.to_string())),
        transcript.record_json(),
    )
    .unwrap();
    o.push('}');
    o
}

// ===========================================================================
// The BabyBear instantiation — `DreggStarkConfig`, Poseidon2-BabyBear-W16.
//
// It lives HERE and not in its binary because `dregg-circuit` is where
// Poseidon2-BabyBear lives; the Pasta suite CANNOT live here (there is no
// `p3-pasta` on the verify floor, deliberately) and is in
// `dregg-circuit-prove::mina_pasta_fixture_suite`.
// ===========================================================================

type BbPerm = Poseidon2BabyBear<16>;
type BbChallenger = DuplexChallenger<BabyBear, BbPerm, 16, 8>;

/// Digest words per commitment node under `PaddingFreeSponge<_, 16, 8, 8>`.
pub const BABYBEAR_DIGEST_ELEMS: usize = 8;

/// The BabyBear hash suite.
pub struct BabyBearSuite;

/// A `DuplexChallenger` that also records everything observed, so the fixture
/// can carry the absorbed sequence and the o1js side can be checked against the
/// TRANSCRIPT, not only against its outputs.
///
/// ⚑ A `DuplexChallenger` over `Val` absorbs a digest as its eight base-field
/// words, which is why one flat `"absorbed"` list is a complete description
/// here and is NOT for the Pasta suite.
pub struct BabyBearRecording {
    inner: BbChallenger,
    absorbed: Vec<F>,
}

impl FixtureTranscript<BABYBEAR_DIGEST_ELEMS> for BabyBearRecording {
    type Word = BabyBear;

    fn observe_f(&mut self, v: F) {
        self.absorbed.push(v);
        self.inner.observe(v);
    }
    fn observe_digest(&mut self, d: &[BabyBear; BABYBEAR_DIGEST_ELEMS]) {
        self.observe_slice(d);
    }
    fn sample_ext(&mut self) -> EF {
        self.inner.sample_algebra_element()
    }
    fn check_witness(&mut self, bits: usize, w: F) -> bool {
        if bits == 0 {
            return true;
        }
        self.observe_f(w);
        self.inner.sample_bits(bits) == 0
    }
    fn sample_bits(&mut self, bits: usize) -> usize {
        self.inner.sample_bits(bits)
    }
    fn record_json(&self) -> String {
        format!(
            r#""absorbed":{}"#,
            nums(self.absorbed.iter().map(|v| f_u32(*v)))
        )
    }
}

impl FixtureHashSuite<BABYBEAR_DIGEST_ELEMS> for BabyBearSuite {
    type Word = BabyBear;
    type ValMmcs = crate::plonky3_prover::FixtureValMmcs;
    type ChallengeMmcs = crate::plonky3_prover::FixtureChallengeMmcs;
    type Challenger = BbChallenger;
    type Config = DreggStarkConfig;
    type Transcript = BabyBearRecording;

    const HASH_NAME: &'static str = "poseidon2-babybear-w16";
    // See the trait doc: the digest word field IS `Val` here, so there is
    // nothing a bit floor could catch and the check is skipped, not faked.
    const MIN_DIGEST_WORD_BITS: u64 = 0;

    fn config(log_blowup: usize, num_queries: usize, query_pow_bits: usize) -> DreggStarkConfig {
        create_config_with_fri_full(
            log_blowup,
            /* log_final_poly_len */ 0,
            /* max_log_arity     */ 1,
            num_queries,
            /* commit_pow_bits   */ 0,
            query_pow_bits,
        )
    }

    fn new_transcript() -> BabyBearRecording {
        BabyBearRecording {
            inner: BbChallenger::new(default_babybear_poseidon2_16()),
            absorbed: Vec::new(),
        }
    }

    fn digest_json(d: &[BabyBear; BABYBEAR_DIGEST_ELEMS]) -> String {
        nums(d.iter().map(|x| f_u32(*x)))
    }
}
