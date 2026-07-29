//! **The dregg-side emitter for `DreggProofVerify`** — mint a REAL dregg
//! FRI-STARK proof at a REDUCED FRI geometry, verify it with dregg's OWN
//! verifier, and emit every field an o1js/Kimchi verifier needs, in CANONICAL
//! form.
//!
//! ```text
//!   cargo run -p dregg-circuit --release --bin mina_stark_fixture -- \
//!       <degree_bits> <log_blowup> <num_queries> <query_pow_bits> [seed] [tamper]
//! ```
//!
//! ## Why this exists
//!
//! Every Mina-side rung built so far (`bridge/mina-zkapp/src/*.ts`) is fed by
//! `mina-pasta-hash-probe`, which emits *pieces* of the protocol — a Merkle
//! opening, a fold chain, a transcript, a DEEP quotient — synthesised for the
//! measurement. None of them is a proof anything actually made. This emitter is
//! the other end: `p3_uni_stark::prove` under `DreggStarkConfig`, the SAME
//! `Poseidon2BabyBear<16>` permutation / `PaddingFreeSponge<.,16,8,8>` /
//! `TruncatedPermutation<.,2,8,16>` / `MerkleTreeMmcs` / `DuplexChallenger<.,16,8>`
//! / `BinomialExtensionField<BabyBear,4>` / `TwoAdicFriPcs` stack the deployed
//! root runs, with only the six FRI knobs turned down.
//!
//! ⚑ **The Rust verifier accepts BEFORE anything is written.** `emit` runs
//! `p3_uni_stark::verify` and aborts on failure, so a fixture that reaches the
//! o1js side is one dregg itself accepts. It ALSO proves the negative: the
//! `tamper` argument bends one field and the emitter REQUIRES its own verifier
//! to refuse — an emitter whose verifier cannot say no is not a check.
//!
//! ⚑ **Canonical, not Montgomery.** `MontyField31`'s `Serialize` writes the raw
//! Montgomery limb (`monty-31/src/monty_31.rs:167-172`), which is right for
//! p3↔p3 and WRONG for anyone reading the numbers as field elements. Every value
//! here goes through `as_canonical_u32`, the same discipline
//! `apex_shrink_gnark_export.rs` follows.
//!
//! ⚑ **It is a `src/bin` target, not an example, deliberately.** Cargo compiles
//! DEV-DEPENDENCIES for an example, and `dregg-circuit`'s dev-deps reach
//! `dregg-lean-ffi`, whose build script fails closed whenever the Lean tree is
//! mid-edit. This emitter needs nothing outside `[dependencies]`, and a gate leg
//! that goes red because an unrelated Lean module is being rewritten is a gate
//! nobody can read.
//!
//! ## What the AIR is, said plainly
//!
//! `MinaFixtureAir` is a 3-column, degree-3 AIR — NOT one of dregg's seven root
//! tables. It is here because the o1js side must evaluate `C_i` itself for the
//! verifier to be closed rather than PCS-only, and dregg's real AIRs are
//! uncounted (`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.14: `N` is the one
//! quantity nobody has taken). It is chosen to exercise every arm the protocol
//! arithmetic has: **all three Lagrange selectors**, a **next-row** reference (so
//! `zeta` and `g*zeta` are both opened and the DEEP quotient runs at two points),
//! **public values** in the transcript AND in a constraint, and a **degree-3**
//! constraint so the quotient really splits into more than one chunk and the
//! Lagrange recomposition is not a no-op.
//!
//! Trace, `n = 2^degree_bits` rows, columns `[a, b, c]`:
//!   * `b_i = a_i^3`
//!   * `c_0 = pis[0]`, `c_{i+1} = c_i + b_i`, `c_{n-1} = pis[1]`

use std::env;
use std::fmt::Write as _;

use dregg_circuit::plonky3_prover::{DreggStarkConfig, create_config_with_fri_full};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{CanObserve, CanSampleBits, DuplexChallenger, FieldChallenger};
use p3_commit::PolynomialSpace;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{Proof, prove, recompose_quotient_from_chunks, verify, verify_constraints};

type F = BabyBear;
type EF = BinomialExtensionField<BabyBear, 4>;
type Chal = DuplexChallenger<BabyBear, Poseidon2BabyBear<16>, 16, 8>;

const D: usize = 4;

// ===========================================================================
// The AIR.
// ===========================================================================

struct MinaFixtureAir;

impl<T: PrimeCharacteristicRing + Sync> BaseAir<T> for MinaFixtureAir {
    fn width(&self) -> usize {
        3
    }
    fn num_public_values(&self) -> usize {
        2
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(3)
    }
}

impl<AB: AirBuilder> Air<AB> for MinaFixtureAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: Vec<AB::Expr> = main.current_slice().iter().map(|v| (*v).into()).collect();
        let next: Vec<AB::Expr> = main.next_slice().iter().map(|v| (*v).into()).collect();
        let pis: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|v| (*v).into())
            .collect();

        // ⚑ THE EMISSION ORDER IS THE FOLDING ORDER. `VerifierConstraintFolder::
        // assert_zero` does `acc = acc * alpha + C` (`uni-stark/src/folder.rs`),
        // so the o1js twin must fold these four in exactly this sequence. A
        // permuted order is a different accumulator and a different proof.

        // C0 — degree 3, the constraint that forces `n_chunks > 1`.
        builder
            .assert_zero(local[1].clone() - local[0].clone() * local[0].clone() * local[0].clone());
        // C1 — is_first_row.
        builder
            .when_first_row()
            .assert_eq(local[2].clone(), pis[0].clone());
        // C2 — is_transition, and the only next-row reference.
        builder
            .when_transition()
            .assert_eq(next[2].clone(), local[2].clone() + local[1].clone());
        // C3 — is_last_row.
        builder
            .when_last_row()
            .assert_eq(local[2].clone(), pis[1].clone());
    }
}

/// The honest trace and its two public values.
fn build_trace(degree_bits: usize, seed: u64) -> (RowMajorMatrix<F>, Vec<F>) {
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

fn f_u32(v: F) -> u32 {
    v.as_canonical_u32()
}
fn ef_limbs(v: EF) -> Vec<u32> {
    v.as_basis_coefficients_slice()
        .iter()
        .map(|x| f_u32(*x))
        .collect()
}
fn arr(vals: impl IntoIterator<Item = String>) -> String {
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
fn nums(vals: impl IntoIterator<Item = u32>) -> String {
    arr(vals.into_iter().map(|v| v.to_string()))
}
fn ef_json(v: EF) -> String {
    nums(ef_limbs(v))
}
fn ef_list(vs: &[EF]) -> String {
    arr(vs.iter().map(|v| ef_json(*v)))
}
fn digest_json(d: &[F; 8]) -> String {
    nums(d.iter().map(|x| f_u32(*x)))
}
fn digests_json(ds: &[[F; 8]]) -> String {
    arr(ds.iter().map(digest_json))
}

// ===========================================================================
// The challenger REPLAY — p3's own transcript, so the o1js derivation is KAT'd
// against the deployed state machine rather than against a re-reading of it.
// ===========================================================================

struct Replay {
    /// Whether `query_pow_witness` really grinds `query_pow_bits` zeros under
    /// THIS transcript. False is a legitimate outcome for a bent fixture.
    query_pow_ok: bool,
    alpha_stark: EF,
    zeta: EF,
    fri_alpha: EF,
    betas: Vec<EF>,
    query_indices: Vec<usize>,
    /// The exact base-field sequence the challenger absorbed, in order — the
    /// o1js side rebuilds this and a mismatch anywhere is a mismatch here.
    absorbed: Vec<F>,
}

/// A `DuplexChallenger` that also records everything observed, so the fixture
/// can carry the absorbed sequence and the o1js side can be checked against the
/// TRANSCRIPT, not only against its outputs.
struct Recording {
    inner: Chal,
    absorbed: Vec<F>,
}
impl Recording {
    fn new() -> Self {
        Self {
            inner: Chal::new(default_babybear_poseidon2_16()),
            absorbed: Vec::new(),
        }
    }
    fn observe(&mut self, v: F) {
        self.absorbed.push(v);
        self.inner.observe(v);
    }
    fn observe_slice(&mut self, vs: &[F]) {
        for v in vs {
            self.observe(*v);
        }
    }
    fn observe_ext(&mut self, v: EF) {
        self.observe_slice(v.as_basis_coefficients_slice());
    }
    fn sample_ext(&mut self) -> EF {
        self.inner.sample_algebra_element()
    }
    fn check_witness(&mut self, bits: usize, w: F) -> bool {
        if bits == 0 {
            return true;
        }
        self.observe(w);
        self.inner.sample_bits(bits) == 0
    }
    fn sample_bits(&mut self, bits: usize) -> usize {
        self.inner.sample_bits(bits)
    }
}

#[allow(clippy::too_many_arguments)]
fn replay(
    proof: &Proof<DreggStarkConfig>,
    public_values: &[F],
    preprocessed_width: usize,
    base_degree_bits: usize,
    log_blowup: usize,
    query_pow_bits: usize,
    log_global_max_height: usize,
    num_queries: usize,
) -> Replay {
    let mut c = Recording::new();
    c.observe(F::from_usize(proof.degree_bits));
    c.observe(F::from_usize(base_degree_bits));
    c.observe(F::from_usize(preprocessed_width));
    for d in proof.commitments.trace.as_ref() {
        c.observe_slice(d);
    }
    c.observe_slice(public_values);
    let alpha_stark = c.sample_ext();
    for d in proof.commitments.quotient_chunks.as_ref() {
        c.observe_slice(d);
    }
    let zeta = c.sample_ext();

    // `two_adic_pcs::verify` observes every opened evaluation, in round order,
    // BEFORE `verify_fri` samples its own alpha (`two_adic_pcs.rs:780-788`).
    let ov = &proof.opened_values;
    for v in &ov.trace_local {
        c.observe_ext(*v);
    }
    if let Some(next) = &ov.trace_next {
        for v in next {
            c.observe_ext(*v);
        }
    }
    for chunk in &ov.quotient_chunks {
        for v in chunk {
            c.observe_ext(*v);
        }
    }

    let fri = &proof.opening_proof;
    let fri_alpha = c.sample_ext();
    let mut betas = Vec::new();
    for (commit, w) in fri
        .commit_phase_commits
        .iter()
        .zip(&fri.commit_pow_witnesses)
    {
        for d in commit.as_ref() {
            c.observe_slice(d);
        }
        assert!(c.check_witness(0, *w), "commit-phase PoW is 0 bits here");
        betas.push(c.sample_ext());
    }
    for coeff in &fri.final_poly {
        c.observe_ext(*coeff);
    }
    for qp in fri.query_proofs[0].commit_phase_openings.iter() {
        c.observe(F::from_usize(qp.log_arity as usize));
    }
    // ⚑ NOT AN ASSERT. A bent fixture is SUPPOSED to break something, and for a
    // bend upstream of the grind (an opened value, the final polynomial, the
    // witness itself) the thing it breaks IS this. Recording it keeps the
    // emitter able to describe a proof its own verifier refuses — which is the
    // fixture the o1js side needs in order to be shown refusing too.
    let query_pow_ok = c.check_witness(query_pow_bits, fri.query_pow_witness);
    let query_indices = (0..num_queries)
        .map(|_| c.sample_bits(log_global_max_height))
        .collect();

    let _ = log_blowup;
    Replay {
        query_pow_ok,
        alpha_stark,
        zeta,
        fri_alpha,
        betas,
        query_indices,
        absorbed: c.absorbed,
    }
}

// ===========================================================================
// main
// ===========================================================================

fn main() {
    let args: Vec<String> = env::args().collect();
    let degree_bits: usize = args.get(1).map_or(2, |s| s.parse().unwrap());
    let log_blowup: usize = args.get(2).map_or(1, |s| s.parse().unwrap());
    let num_queries: usize = args.get(3).map_or(1, |s| s.parse().unwrap());
    let query_pow_bits: usize = args.get(4).map_or(16, |s| s.parse().unwrap());
    let seed: u64 = args.get(5).map_or(1, |s| s.parse().unwrap());
    let tamper: &str = args.get(6).map(String::as_str).unwrap_or("none");

    let config = create_config_with_fri_full(
        log_blowup,
        /* log_final_poly_len */ 0,
        /* max_log_arity     */ 1,
        num_queries,
        /* commit_pow_bits   */ 0,
        query_pow_bits,
    );
    let air = MinaFixtureAir;
    let (matrix, pis) = build_trace(degree_bits, seed);

    let proof = prove(&config, &air, matrix, &pis);
    verify(&config, &air, &proof, &pis)
        .expect("dregg's OWN verifier must accept before anything is emitted");

    // ⚑ THE EMITTER PROVES ITS OWN VERIFIER CAN SAY NO. A `tamper` mode that no
    // longer matches its target silently becomes a passing test, so the bend is
    // applied to the SAME structure that is emitted, and refusal is REQUIRED.
    if tamper != "none" {
        let bent = bend(&proof, tamper);
        assert!(
            verify(&config, &air, &bent, &pis).is_err(),
            "the '{tamper}' bend was ACCEPTED by dregg's verifier — the fault no longer \
             reaches anything, and any o1js leg built on it is vacuous"
        );
        emit(
            &config,
            &bent,
            &pis,
            degree_bits,
            log_blowup,
            num_queries,
            query_pow_bits,
            tamper,
        );
        return;
    }

    emit(
        &config,
        &proof,
        &pis,
        degree_bits,
        log_blowup,
        num_queries,
        query_pow_bits,
        "none",
    );
}

/// Bend one field of an honest proof. Each arm targets a DIFFERENT layer, so a
/// leg that runs all of them cannot pass by catching one thing four times.
fn bend(p: &Proof<DreggStarkConfig>, which: &str) -> Proof<DreggStarkConfig> {
    let mut q = clone_proof(p);
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
        "inputpath" => q.opening_proof.query_proofs[0].input_proof[0].opening_proof[0][0] += F::ONE,
        // The query PoW witness: the grind and every index after it.
        "querypow" => q.opening_proof.query_pow_witness += F::ONE,
        other => panic!("unknown tamper mode '{other}'"),
    }
    q
}

/// `Proof<SC>` is not `Clone`, and re-proving would give a different (equally
/// honest) object, so the bend has to start from a structural copy of THIS one.
fn clone_proof(p: &Proof<DreggStarkConfig>) -> Proof<DreggStarkConfig> {
    let bytes = postcard::to_allocvec(p).expect("postcard round-trip of the emitted proof");
    postcard::from_bytes(&bytes).expect("postcard round-trip of the emitted proof")
}

#[allow(clippy::too_many_arguments)]
fn emit(
    _config: &DreggStarkConfig,
    proof: &Proof<DreggStarkConfig>,
    pis: &[F],
    degree_bits: usize,
    log_blowup: usize,
    num_queries: usize,
    query_pow_bits: usize,
    tamper: &str,
) {
    let air = MinaFixtureAir;
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

    let fri = &proof.opening_proof;
    let layers = fri.commit_phase_commits.len();
    let log_global_max_height = layers + log_blowup; // log_final_poly_len = 0, arity 1

    let rep = replay(
        proof,
        pis,
        0,
        base_degree_bits,
        log_blowup,
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
        let quotient = recompose_quotient_from_chunks::<DreggStarkConfig>(
            &chunk_domains,
            &proof.opened_values.quotient_chunks,
            rep.zeta,
        );
        let zeros = vec![EF::ZERO; <MinaFixtureAir as BaseAir<F>>::width(&air)];
        let next = proof
            .opened_values
            .trace_next
            .as_deref()
            .unwrap_or(zeros.as_slice());
        verify_constraints::<DreggStarkConfig, MinaFixtureAir, ()>(
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
    write!(
        o,
        r#""kind":"dregg-uni-stark-fixture","tamper":"{tamper}","#
    )
    .unwrap();
    write!(
        o,
        r#""knobs":{{"logBlowup":{log_blowup},"logFinalPolyLen":0,"maxLogArity":1,"numQueries":{num_queries},"commitPowBits":0,"queryPowBits":{query_pow_bits},"extDegree":{D}}},"#
    )
    .unwrap();
    write!(
        o,
        r#""shape":{{"degreeBits":{},"baseDegreeBits":{base_degree_bits},"preprocessedWidth":0,"airWidth":{},"numPublicValues":{},"numQuotientChunks":{n_chunks},"logNumChunks":{log_num_chunks},"layers":{layers},"logGlobalMaxHeight":{log_global_max_height},"traceLdeLogHeight":{},"quotientLdeLogHeight":{},"hasTraceNext":{}}},"#,
        proof.degree_bits,
        <MinaFixtureAir as BaseAir<F>>::width(&air),
        <MinaFixtureAir as BaseAir<F>>::num_public_values(&air),
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
        digests_json(proof.commitments.trace.as_ref()),
        digests_json(proof.commitments.quotient_chunks.as_ref()),
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
        arr(fri.commit_phase_commits.iter().map(|c| digests_json(c.as_ref()))),
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
                    digests_json(&b.opening_proof),
                )
            }));
            let steps = arr(qp.commit_phase_openings.iter().map(|s| {
                format!(
                    r#"{{"logArity":{},"siblingValues":{},"openingProof":{}}}"#,
                    s.log_arity,
                    ef_list(&s.sibling_values),
                    digests_json(&s.opening_proof),
                )
            }));
            format!(r#"{{"inputProof":{inputs},"commitPhaseOpenings":{steps}}}"#)
        })),
    )
    .unwrap();

    // -- what p3's OWN challenger produced -----------------------------------
    write!(
        o,
        r#""challenges":{{"queryPowOk":{},"alphaStark":{},"zeta":{},"friAlpha":{},"betas":{},"queryIndices":{},"absorbed":{}}}"#,
        rep.query_pow_ok,
        ef_json(rep.alpha_stark),
        ef_json(rep.zeta),
        ef_json(rep.fri_alpha),
        ef_list(&rep.betas),
        arr(rep.query_indices.iter().map(|i| i.to_string())),
        nums(rep.absorbed.iter().map(|v| f_u32(*v))),
    )
    .unwrap();
    o.push('}');
    println!("{o}");
}
