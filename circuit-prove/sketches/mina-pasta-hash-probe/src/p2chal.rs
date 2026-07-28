//! The DEPLOYED Fiat-Shamir transcript, as an EMITTER for the o1js side.
//!
//! WHY THIS EXISTS. `p2bb.rs` pins the hash and the fold; `FriQueryStep.ts`
//! walks a query. Neither says where the query INDEX or the fold challenge
//! `beta` came from. In the rung-2 circuit they are witnesses — which means a
//! prover picks its own queries, and a FRI walk over self-chosen indices proves
//! nothing at all. The object that closes that hole is the challenger, and it
//! is the one part of the verifier where a transcription is most likely to be
//! subtly wrong: `DuplexChallenger`'s output buffer is popped from the BACK, its
//! `observe` CLEARS pending output, `sample` re-duplexes when the input buffer
//! is non-empty, and `check_witness` at 0 bits does not observe at all. Every
//! one of those is a place a re-implementation drifts while every hash still
//! matches.
//!
//! So this module calls `p3_challenger::DuplexChallenger<BabyBear,
//! Poseidon2BabyBear<16>, 16, 8>` — the type `circuit-prove/src/
//! plonky3_recursion_impl.rs:138` instantiates — at the same `82cfad73` rev, and
//! emits its outputs on inputs the o1js side cannot have precomputed. Nothing
//! here re-implements a sponge.

use p3_challenger::{CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_field::extension::BinomialExtensionField;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_symmetric::Permutation;

use crate::p2bb::{perm, Perm, DIGEST_ELEMS, RATE, WIDTH};
use p3_baby_bear::BabyBear;

/// The deployed challenger — `plonky3_recursion_impl.rs:138`.
pub type Chal = p3_challenger::DuplexChallenger<BabyBear, Perm, WIDTH, RATE>;
/// The deployed challenge field — `RECURSION_EXT_DEGREE = 4`.
pub type Challenge = BinomialExtensionField<BabyBear, 4>;

// ---------------------------------------------------------------------------
// The deployed root's FRI knobs. Every one is re-derived in
// `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §1.2 from `ir2_leaf_wrap_config()`
// (`circuit-prove/src/ivc_turn_chain.rs:1242-1245,1315-1329`) and
// `plonky3_recursion_impl.rs:118-121`.
// ---------------------------------------------------------------------------

/// `IR2_INNER_LOG_BLOWUP` — `ivc_turn_chain.rs:1242`.
pub const LOG_BLOWUP: usize = 6;
/// `IR2_INNER_LOG_FINAL_POLY_LEN` — `ivc_turn_chain.rs:1243`.
pub const LOG_FINAL_POLY_LEN: usize = 0;
/// `IR2_INNER_COMMIT_POW_BITS` — `ivc_turn_chain.rs:1244`. ZERO, and
/// `check_witness` at 0 bits returns before observing, so the commit-phase PoW
/// touches the transcript not at all.
pub const COMMIT_POW_BITS: usize = 0;
/// `IR2_INNER_QUERY_POW_BITS` — `ivc_turn_chain.rs:1245`.
pub const QUERY_POW_BITS: usize = 16;
/// `INNER_FRI_MAX_LOG_ARITY` — `plonky3_recursion_impl.rs:118`. The root folds
/// by TWO; the "max_log_arity 3" in `ir2_leaf_wrap_config`'s doc-comment
/// describes the inner batch (a documented name collision).
pub const MAX_LOG_ARITY: usize = 1;
/// `INNER_FRI_NUM_QUERIES` — `plonky3_recursion_impl.rs:121`.
pub const NUM_QUERIES: usize = 19;
/// `log|D^0|` for the accumulator root shape: `WRAP_LOG_CEIL = 16` + blowup 6.
pub const LOG_GLOBAL_MAX_HEIGHT: usize = 22;
/// `(22 - 6) / 1`.
pub const LAYERS: usize = (LOG_GLOBAL_MAX_HEIGHT - LOG_BLOWUP - LOG_FINAL_POLY_LEN) / MAX_LOG_ARITY;
/// `TwoAdicFriFolding::extra_query_index_bits` — `fri/src/two_adic_pcs.rs:105`.
pub const EXTRA_QUERY_INDEX_BITS: usize = 0;

// ---------------------------------------------------------------------------
// A deterministic value source. The permutation itself is the PRG, so no extra
// dependency and no chance of the o1js side "happening" to hold the values: the
// seed comes from the caller and the expansion is the deployed hash.
// ---------------------------------------------------------------------------

pub(crate) struct Prg {
    state: [BabyBear; WIDTH],
    idx: usize,
    perm: Perm,
}

impl Prg {
    pub(crate) fn new(seed: u64) -> Self {
        let mut state = [BabyBear::ZERO; WIDTH];
        state[0] = BabyBear::from_u64(seed);
        state[1] = BabyBear::from_u64(0x5eed);
        let p = perm();
        Self {
            state,
            idx: WIDTH,
            perm: p,
        }
    }
    pub(crate) fn next(&mut self) -> BabyBear {
        if self.idx == WIDTH {
            self.perm.permute_mut(&mut self.state);
            self.idx = 0;
        }
        let v = self.state[self.idx];
        self.idx += 1;
        v
    }
    pub(crate) fn next_n(&mut self, n: usize) -> Vec<BabyBear> {
        (0..n).map(|_| self.next()).collect()
    }
    pub(crate) fn next_ext(&mut self) -> Challenge {
        let c: [BabyBear; 4] = core::array::from_fn(|_| self.next());
        Challenge::new(c)
    }
}

fn d(x: BabyBear) -> String {
    x.as_canonical_u32().to_string()
}
fn arr(v: &[BabyBear]) -> String {
    v.iter()
        .map(|x| format!("\"{}\"", d(*x)))
        .collect::<Vec<_>>()
        .join(",")
}
fn ext_limbs(e: Challenge) -> Vec<BabyBear> {
    use p3_field::BasedVectorSpace;
    e.as_basis_coefficients_slice().to_vec()
}
fn arr_ext(v: &[Challenge]) -> String {
    v.iter()
        .map(|e| format!("[{}]", arr(&ext_limbs(*e))))
        .collect::<Vec<_>>()
        .join(",")
}
fn arr_digests(v: &[[BabyBear; DIGEST_ELEMS]]) -> String {
    v.iter()
        .map(|g| format!("[{}]", arr(g)))
        .collect::<Vec<_>>()
        .join(",")
}

// ---------------------------------------------------------------------------
// `p2chal` — a low-level observe/sample TRACE.
// ---------------------------------------------------------------------------

/// `p2chal <seed> <op>...` where each op is one of
///
///   `o:<n>`  observe `n` fresh base elements
///   `s:<n>`  sample `n` base elements
///   `e:<n>`  sample `n` extension elements (4 base samples each)
///   `b:<k>`  sample a `k`-bit integer
///
/// and every input and output is emitted along with the sponge state after the
/// whole script. The o1js twin must reproduce all of it.
///
/// ⚑ The interesting ops are the ones that cross `DuplexChallenger`'s state
/// machine: `o:8` fills the rate exactly and duplexes; `o:3 s:1` duplexes on a
/// PARTIAL buffer (zero-fill is NOT what happens — the untouched lanes keep the
/// previous permutation's output); `s:9` drains one output buffer and forces a
/// second duplex with an EMPTY input buffer.
pub fn emit_p2_chal(args: &[String]) {
    let seed: u64 = args[0].parse().expect("seed");
    let mut prg = Prg::new(seed);
    let mut chal = Chal::new(perm());

    let mut ops_json: Vec<String> = Vec::new();
    for op in &args[1..] {
        let (kind, n) = op
            .split_once(':')
            .unwrap_or_else(|| panic!("bad op '{op}'"));
        let n: usize = n.parse().unwrap_or_else(|_| panic!("bad count in '{op}'"));
        match kind {
            "o" => {
                let vals = prg.next_n(n);
                for v in &vals {
                    chal.observe(*v);
                }
                ops_json.push(format!(
                    "{{\"op\":\"observe\",\"values\":[{}]}}",
                    arr(&vals)
                ));
            }
            "s" => {
                let out: Vec<BabyBear> = (0..n).map(|_| chal.sample()).collect();
                ops_json.push(format!("{{\"op\":\"sample\",\"values\":[{}]}}", arr(&out)));
            }
            "e" => {
                let out: Vec<Challenge> = (0..n).map(|_| chal.sample_algebra_element()).collect();
                ops_json.push(format!(
                    "{{\"op\":\"sampleExt\",\"values\":[{}]}}",
                    arr_ext(&out)
                ));
            }
            "b" => {
                let v = chal.sample_bits(n);
                ops_json.push(format!(
                    "{{\"op\":\"sampleBits\",\"bits\":{n},\"value\":{v}}}"
                ));
            }
            _ => panic!("unknown op kind '{kind}'"),
        }
    }

    println!("{{");
    println!(
        "  \"emitter\": \"mina-pasta-hash-probe p2chal (p3 DuplexChallenger<BabyBear, Poseidon2BabyBear<16>, 16, 8>)\","
    );
    println!("  \"width\": {WIDTH}, \"rate\": {RATE},");
    println!("  \"seed\": {seed},");
    println!("  \"ops\": [{}],", ops_json.join(","));
    println!("  \"finalSpongeState\": [{}],", arr(&chal.sponge_state));
    println!("  \"finalInputBuffer\": [{}],", arr(&chal.input_buffer));
    println!("  \"finalOutputBuffer\": [{}]", arr(&chal.output_buffer));
    println!("}}");
}

// ---------------------------------------------------------------------------
// `p2fritranscript` — the WHOLE deployed FRI transcript.
// ---------------------------------------------------------------------------

/// `p2fritranscript <seed> <preambleLen>` — run exactly the challenger schedule
/// `p3_fri::verifier::verify_fri` runs at the deployed knobs, and emit every
/// challenge it derives.
///
/// The schedule, read off `fri/src/verifier.rs:139-270` line for line:
///
///   1. `alpha = challenger.sample_algebra_element()`                    (:139)
///   2. per commit round: `observe(commit)`; `check_witness(commit_pow,   (:211-219)
///      w)` — a NO-OP at 0 bits, it returns before observing;
///      `beta_r = sample_algebra_element()`
///   3. `observe_algebra_slice(final_poly)`                              (:236)
///   4. `observe(Val::from_usize(log_arity))` per round                  (:249-251)
///   5. `check_witness(query_pow_bits, query_pow_witness)`               (:254)
///   6. per query: `index = sample_bits(log_global_max_height + extra)`  (:268)
///
/// `preambleLen` base elements are observed first, standing in for the
/// batch-STARK preamble the real verifier has already absorbed (degree bits,
/// trace commitments, public values, zeta). ⚑ That substitution is the honest
/// residual: this pins the FRI transcript GIVEN a starting state, and binding
/// the starting state to the STARK's own observes is a separate rung.
///
/// The query PoW witness is GROUND, not fabricated: `check_witness(16, w)`
/// really passes on the emitted value, so the o1js circuit checks a real one.
/// `layers` and `numQueries` may be overridden (args 3 and 4) so a
/// PROVABLE-SIZE instance of the same schedule is KAT'd by the same emitter
/// rather than by a hand-built witness. Every other knob — the PoW bits, the
/// index width, the arity — stays at the deployed value, so the shrunk instance
/// is the deployed protocol with fewer layers, not a different one.
pub fn emit_fri_transcript(args: &[String]) {
    let seed: u64 = args[0].parse().expect("seed");
    let preamble_len: usize = args[1].parse().expect("preambleLen");
    let layers: usize = args.get(2).map_or(LAYERS, |s| s.parse().expect("layers"));
    let num_queries: usize = args
        .get(3)
        .map_or(NUM_QUERIES, |s| s.parse().expect("numQueries"));
    let mut prg = Prg::new(seed);
    let mut chal = Chal::new(perm());

    // 0. the stand-in preamble.
    let preamble = prg.next_n(preamble_len);
    for v in &preamble {
        chal.observe(*v);
    }
    let state_at_fri_entry = chal.sponge_state;
    let buffered_at_fri_entry = chal.input_buffer.clone();

    // 1. alpha — the batch-combination challenge.
    let alpha: Challenge = chal.sample_algebra_element();

    // 2. the commit-phase rounds.
    let commits: Vec<[BabyBear; DIGEST_ELEMS]> = (0..layers)
        .map(|_| {
            let v = prg.next_n(DIGEST_ELEMS);
            core::array::from_fn(|i| v[i])
        })
        .collect();
    // `commit_pow_bits = 0`, so p3 grinds nothing: `grind` returns `F::ZERO`
    // immediately and `check_witness` returns true WITHOUT observing.
    let commit_pow_witnesses = vec![BabyBear::ZERO; layers];
    let mut betas: Vec<Challenge> = Vec::with_capacity(layers);
    for r in 0..layers {
        chal.observe(commits[r]);
        assert!(
            chal.check_witness(COMMIT_POW_BITS, commit_pow_witnesses[r]),
            "commit-phase PoW check failed at round {r}"
        );
        betas.push(chal.sample_algebra_element());
    }

    // 3. the final polynomial. `log_final_poly_len = 0` => exactly ONE
    //    coefficient, so the final check is a CONSTANT comparison.
    let final_poly_len = 1usize << LOG_FINAL_POLY_LEN;
    let final_poly: Vec<Challenge> = (0..final_poly_len).map(|_| prg.next_ext()).collect();
    chal.observe_algebra_slice(&final_poly);

    // 4. the variable-arity schedule, bound in before query grinding.
    let log_arities = vec![MAX_LOG_ARITY; layers];
    for &la in &log_arities {
        chal.observe(BabyBear::from_usize(la));
    }

    // 5. the query PoW. GROUND on a clone, then checked on the real challenger
    //    — `grind` itself asserts `check_witness`, so an emitted witness that
    //    did not pass could not get here.
    let query_pow_witness = chal.clone().grind(QUERY_POW_BITS);
    assert!(
        chal.check_witness(QUERY_POW_BITS, query_pow_witness),
        "the ground query PoW witness did not pass check_witness"
    );

    // 6. the query indices.
    let index_bits = LOG_GLOBAL_MAX_HEIGHT + EXTRA_QUERY_INDEX_BITS;
    let query_indices: Vec<usize> = (0..num_queries)
        .map(|_| chal.sample_bits(index_bits))
        .collect();

    println!("{{");
    println!(
        "  \"emitter\": \"mina-pasta-hash-probe p2fritranscript (p3 verify_fri challenger schedule, DuplexChallenger<BabyBear,Poseidon2BabyBear<16>,16,8>)\","
    );
    println!("  \"seed\": {seed},");
    println!("  \"width\": {WIDTH}, \"rate\": {RATE},");
    println!("  \"logBlowup\": {LOG_BLOWUP},");
    println!("  \"logFinalPolyLen\": {LOG_FINAL_POLY_LEN},");
    println!("  \"maxLogArity\": {MAX_LOG_ARITY},");
    println!("  \"layers\": {layers},");
    println!("  \"numQueries\": {num_queries},");
    println!("  \"deployedLayers\": {LAYERS},");
    println!("  \"deployedNumQueries\": {NUM_QUERIES},");
    println!("  \"commitPowBits\": {COMMIT_POW_BITS},");
    println!("  \"queryPowBits\": {QUERY_POW_BITS},");
    println!("  \"logGlobalMaxHeight\": {LOG_GLOBAL_MAX_HEIGHT},");
    println!("  \"extraQueryIndexBits\": {EXTRA_QUERY_INDEX_BITS},");
    println!("  \"indexBits\": {index_bits},");
    println!("  \"preamble\": [{}],", arr(&preamble));
    println!("  \"stateAtFriEntry\": [{}],", arr(&state_at_fri_entry));
    println!(
        "  \"bufferedAtFriEntry\": [{}],",
        arr(&buffered_at_fri_entry)
    );
    println!("  \"alpha\": [{}],", arr(&ext_limbs(alpha)));
    println!("  \"commits\": [{}],", arr_digests(&commits));
    println!("  \"betas\": [{}],", arr_ext(&betas));
    println!("  \"finalPoly\": [{}],", arr_ext(&final_poly));
    println!(
        "  \"logArities\": [{}],",
        log_arities
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );
    println!("  \"queryPowWitness\": \"{}\",", d(query_pow_witness));
    println!(
        "  \"queryIndices\": [{}],",
        query_indices
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );
    println!("  \"finalSpongeState\": [{}]", arr(&chal.sponge_state));
    println!("}}");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The deployed challenger's sponge is the deployed PERMUTATION: absorbing
    /// exactly `RATE` elements into a fresh challenger and sampling must give
    /// `perm(v || 0^8)`, read BACK TO FRONT. Both halves matter — the second is
    /// the one a transcription gets wrong, because `output_buffer.pop()` takes
    /// the LAST rate lane first.
    #[test]
    fn sample_is_the_permutation_read_backwards() {
        let mut chal = Chal::new(perm());
        let vals: Vec<BabyBear> = (0..RATE as u64).map(BabyBear::from_u64).collect();
        for v in &vals {
            chal.observe(*v);
        }
        let mut want = [BabyBear::ZERO; WIDTH];
        want[..RATE].copy_from_slice(&vals);
        perm().permute_mut(&mut want);

        let got: Vec<BabyBear> = (0..RATE).map(|_| chal.sample()).collect();
        let backwards: Vec<BabyBear> = want[..RATE].iter().rev().copied().collect();
        assert_eq!(
            got, backwards,
            "samples are not the rate read back-to-front"
        );
        // and NOT front-to-back — the discriminating polarity.
        assert_ne!(
            got,
            want[..RATE].to_vec(),
            "the rate is symmetric here, so this test cannot see the order"
        );
    }

    /// `observe` after a `sample` DISCARDS the rest of the output buffer, and a
    /// `sample` with a partially-filled input buffer duplexes with the untouched
    /// lanes carrying the PREVIOUS permutation's output — not zeros. A
    /// transcription that zero-fills the unabsorbed rate diverges here and
    /// nowhere else.
    #[test]
    fn partial_absorb_keeps_the_previous_state_and_observe_drops_output() {
        let mut a = Chal::new(perm());
        for i in 0..RATE as u64 {
            a.observe(BabyBear::from_u64(i));
        }
        let _first: BabyBear = a.sample(); // duplexed; 7 outputs left
        a.observe(BabyBear::from_u64(999)); // clears those 7
        let got: BabyBear = a.sample();

        // The reference: state after the first permutation, lane 0 overwritten
        // by 999, everything else UNTOUCHED, permuted again, last rate lane.
        let mut st = [BabyBear::ZERO; WIDTH];
        for i in 0..RATE {
            st[i] = BabyBear::from_u64(i as u64);
        }
        perm().permute_mut(&mut st);
        st[0] = BabyBear::from_u64(999);
        perm().permute_mut(&mut st);
        assert_eq!(got, st[RATE - 1], "partial-absorb duplexing diverges");

        // Discriminating: a zero-filled rate would give something else.
        let mut zf = [BabyBear::ZERO; WIDTH];
        for i in 0..RATE {
            zf[i] = BabyBear::from_u64(i as u64);
        }
        perm().permute_mut(&mut zf);
        zf[0] = BabyBear::from_u64(999);
        zf[1..RATE].fill(BabyBear::ZERO);
        perm().permute_mut(&mut zf);
        assert_ne!(
            got,
            zf[RATE - 1],
            "zero-filling the unabsorbed rate is indistinguishable here"
        );
    }

    /// `check_witness` at ZERO bits returns WITHOUT observing. The deployed
    /// commit-phase PoW is 0 bits, so every one of the 16 per-layer calls must
    /// leave the transcript byte-identical — if a circuit "checked" them by
    /// absorbing the witness, every beta after the first would be wrong.
    #[test]
    fn zero_bit_check_witness_does_not_touch_the_transcript() {
        let mut a = Chal::new(perm());
        let mut b = Chal::new(perm());
        for i in 0..5u64 {
            a.observe(BabyBear::from_u64(i));
            b.observe(BabyBear::from_u64(i));
        }
        assert!(a.check_witness(0, BabyBear::from_u64(12345)));
        let (x, y): (BabyBear, BabyBear) = (a.sample(), b.sample());
        assert_eq!(x, y, "a 0-bit check_witness perturbed the transcript");
        // Discriminating: at 1 bit it DOES observe, so the samples must differ.
        let mut c = Chal::new(perm());
        for i in 0..5u64 {
            c.observe(BabyBear::from_u64(i));
        }
        let _ = c.check_witness(1, BabyBear::from_u64(12345));
        let z: BabyBear = c.sample();
        assert_ne!(z, y, "a 1-bit check_witness left the transcript unchanged");
    }

    /// `sample_bits(k)` is the LOW `k` bits of the canonical representative of a
    /// sampled field element — not a re-hash, not the high bits.
    #[test]
    fn sample_bits_is_the_low_bits_of_a_sample() {
        let mut a = Chal::new(perm());
        let mut b = Chal::new(perm());
        for i in 0..11u64 {
            a.observe(BabyBear::from_u64(i));
            b.observe(BabyBear::from_u64(i));
        }
        let raw: BabyBear = b.sample();
        let got = a.sample_bits(22);
        assert_eq!(
            got,
            (raw.as_canonical_u32() as usize) & ((1 << 22) - 1),
            "sample_bits is not the low 22 bits of the sample"
        );
        assert!(got < (1 << 22));
    }

    /// A ground PoW witness passes and a perturbed one does not — at the
    /// DEPLOYED 16 bits. Without the second half "the circuit checks the PoW"
    /// is compatible with the check accepting everything.
    #[test]
    fn ground_query_pow_witness_passes_and_a_wrong_one_does_not() {
        let mut base = Chal::new(perm());
        for i in 0..13u64 {
            base.observe(BabyBear::from_u64(i * 7 + 1));
        }
        let w = base.clone().grind(QUERY_POW_BITS);
        assert!(base.clone().check_witness(QUERY_POW_BITS, w));
        assert!(
            !base
                .clone()
                .check_witness(QUERY_POW_BITS, w + BabyBear::ONE),
            "a perturbed witness passed a 16-bit PoW (chance 1/65536 by luck)"
        );
    }

    /// The layer count and the index width the emitter reports are the deployed
    /// ones, derived rather than typed: `(22 - 6 - 0)/1 = 16` and `22 + 0`.
    #[test]
    fn the_deployed_geometry_is_what_it_says() {
        assert_eq!(LAYERS, 16);
        assert_eq!(LOG_GLOBAL_MAX_HEIGHT + EXTRA_QUERY_INDEX_BITS, 22);
        assert_eq!(1usize << LOG_FINAL_POLY_LEN, 1, "final poly is a constant");
        assert_eq!(MAX_LOG_ARITY, 1, "the root folds by 2");
    }
}
