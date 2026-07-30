//! **The Pasta half of the ONE fixture emitter** — [`DreggMinaConfig`] as a
//! [`FixtureHashSuite`], so `mina_pasta_stark_fixture` emits the exact schema
//! `mina_stark_fixture` does, with Mina-Poseidon commitments.
//!
//! ## ⚑ SUBSTRATE (HOUSE LAW #1)
//!
//! **No AIR, no constraint, no gadget, no `air_accepts` here.** The AIR this
//! suite's binary proves is the Lean-authored `mina-fixture` descriptor, decoded
//! by `dregg_circuit::mina_fixture_emit::fixture_air`. This module is transcript
//! and commitment plumbing: which prime field the Merkle/Fiat–Shamir hash lives
//! in and how to write it down.
//!
//! ## What actually differs from the BabyBear suite
//!
//! Two things, and they are the two the trait asks for:
//!
//! 1. **A digest is ONE native Pasta element**, not eight BabyBear words. It is
//!    written as a canonical DECIMAL STRING — `2^254`-scale integers are not
//!    JSON numbers — inside an array of length one, so the consumer's shape code
//!    (`digest[i]`) is the same in both suites.
//! 2. **The challenger is `MultiField32Challenger<BabyBear, PastaFp, _, 3, 2>`**,
//!    which absorbs base-field scalars PACKED (8 per rate slot, radix `2^31`) and
//!    absorbs digests NATIVELY. A flat "absorbed BabyBear list" — what the
//!    BabyBear suite emits — cannot describe that, so this suite emits a
//!    chronological **event log** plus the inner `[PastaFp; 3]` sponge state
//!    **after every permutation**.
//!
//! ## ⚑ THE SPONGE STATES COME FROM A REPLICA, AND THE REPLICA IS CHECKED
//!
//! `MultiField32Challenger::inner` is PRIVATE, so `inner.sponge_state` cannot be
//! read without patching p3. [`SpongeReplica`] is therefore a faithful
//! reimplementation of that challenger over the public `MinaPoseidonPerm`.
//!
//! **An unchecked replica is worthless**, so [`MinaPastaRecording`] runs the
//! replica in LOCKSTEP with a real `MultiField32Challenger` on the actual proof
//! and, after EVERY transcript event, asserts:
//!
//! * every sampled output agrees (`sample_ext`, `sample_bits`, `check_witness`),
//!   and
//! * `CanFinalizeDigest::finalize` on a CLONE of each agrees — which is a direct
//!   window onto the real challenger's `inner.sponge_state[..RATE]` (finalize
//!   permutes once more and returns the rate lanes), i.e. the sponge states this
//!   module publishes are pinned against p3's own state, not merely against p3's
//!   outputs.
//!
//! A divergence anywhere panics before a fixture is printed.
//!
//! ⚑ **AND THE CHECK CAN GO RED.** A gate that cannot fail is not a gate, so
//! each of the three errors a re-implementer of this challenger is most likely
//! to make was injected into [`SpongeReplica`] alone and the suite re-run:
//!
//! | mutation | what went red |
//! |---|---|
//! | squeeze limbs `7 → 6` | `challenge 0 diverged` — the sampled-output leg |
//! | absorb radix `31 → 32` | `sponge diverged at partial batch` — the finalize/sponge leg |
//! | drop `sponge_state[RATE] += length_tag` | both that and [`tests::native_digest_absorb_is_not_the_scalar_path`] |
//!
//! Two independent legs, three plausible errors, all red — then reverted.

use dregg_circuit::mina_fixture_emit::{
    EF, F, FixtureHashSuite, FixtureTranscript, arr, ef_json, f_u32, nums,
};
use p3_challenger::{
    CanFinalizeDigest, CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger,
};
use p3_field::{
    BasedVectorSpace, PrimeCharacteristicRing, PrimeField, PrimeField32, absorb_radix_bits,
    max_absorb_injective_limbs, reduce_packed, split_pf_to_field_order_limbs,
    squeeze_field_order_num_limbs,
};
use p3_pasta::{MinaPoseidonPerm, PASTA_RATE, PASTA_WIDTH, PastaFp};
use p3_symmetric::{Hash, Permutation};

use crate::dregg_mina_config::{
    DreggMinaConfig, MINA_DIGEST_ELEMS, MinaChallengeMmcs, MinaChallenger, MinaValMmcs,
    create_mina_config_with_fri,
};

/// One Pasta element as a canonical decimal STRING.
///
/// ⚑ Not a JSON number: `p ≈ 2^254`, and JSON numbers are IEEE-754 doubles past
/// `2^53` in every consumer that matters here. Canonical, never Montgomery.
fn pasta_dec(x: PastaFp) -> String {
    format!("\"{}\"", x.as_canonical_biguint())
}

// ===========================================================================
// The replica: `MultiField32Challenger<BabyBear, PastaFp, MinaPoseidonPerm, 3, 2>`
// with a visible sponge.
// ===========================================================================

/// Number of BabyBear scalars packed into one Pasta rate slot (8 for this pair).
fn absorb_num_f_elms() -> usize {
    max_absorb_injective_limbs::<F, PastaFp>()
}
/// Base-`|BabyBear|` limbs taken from each squeezed Pasta rate cell (7 here).
fn squeeze_num_f_elms() -> usize {
    squeeze_field_order_num_limbs::<PastaFp, F>()
}

/// A byte-faithful reimplementation of p3's `MultiField32Challenger` for this
/// (`BabyBear`, `PastaFp`, `MinaPoseidonPerm`, `WIDTH = 3`, `RATE = 2`)
/// instantiation, with the inner duplex sponge exposed.
///
/// It exists ONLY because `MultiField32Challenger::inner` is private and the
/// per-permutation sponge state is the single most useful thing an in-circuit
/// o1js challenger can be differentially checked against. It is asserted equal
/// to the real one on every event — see the module doc.
#[derive(Clone)]
pub struct SpongeReplica {
    /// The inner `DuplexChallenger<PastaFp, _, 3, 2>` sponge state.
    sponge_state: [PastaFp; PASTA_WIDTH],
    /// p3's `inner.input_buffer`. The MultiField wrapper never pushes to it (it
    /// absorbs through `absorb_rate_padded_with_tag`, which clears it), so it is
    /// always empty here — kept so `duplexing` is the same function p3 runs.
    input_buffer: Vec<PastaFp>,
    /// p3's `inner.output_buffer`: the rate lanes after the last permutation.
    output_buffer: Vec<PastaFp>,
    /// Observed base-field scalars not yet packed and absorbed.
    f_buffer: Vec<F>,
    /// Base-field limbs split out of the last squeezed rate row. **Popped from
    /// the END** — the single most-missed detail of this challenger.
    f_squeeze_buffer: Vec<F>,
    /// The sponge state after EVERY permutation, in order.
    states: Vec<[PastaFp; PASTA_WIDTH]>,
}

impl SpongeReplica {
    fn new() -> Self {
        Self {
            sponge_state: [PastaFp::ZERO; PASTA_WIDTH],
            input_buffer: Vec::new(),
            output_buffer: Vec::new(),
            f_buffer: Vec::new(),
            f_squeeze_buffer: Vec::new(),
            states: Vec::new(),
        }
    }

    fn permute(&mut self) {
        MinaPoseidonPerm.permute_mut(&mut self.sponge_state);
        self.states.push(self.sponge_state);
    }

    /// `DuplexChallenger::absorb_rate_padded_with_tag`: overwrite the rate lanes,
    /// zero the unused ones, ADD the length tag into `sponge_state[RATE]`,
    /// permute, refill the output buffer.
    fn absorb_rate_padded_with_tag(&mut self, values: &[PastaFp], length_tag: u8) {
        assert!(values.len() <= PASTA_RATE);
        self.input_buffer.clear();
        self.output_buffer.clear();
        for (i, &v) in values.iter().enumerate() {
            self.sponge_state[i] = v;
        }
        self.sponge_state[values.len()..PASTA_RATE].fill(PastaFp::ZERO);
        self.sponge_state[PASTA_RATE] += PastaFp::from_u8(length_tag);
        self.permute();
        self.output_buffer
            .extend_from_slice(&self.sponge_state[..PASTA_RATE]);
    }

    /// `DuplexChallenger::duplexing`.
    fn duplexing(&mut self) {
        assert!(self.input_buffer.len() <= PASTA_RATE);
        for (i, val) in self.input_buffer.drain(..).enumerate() {
            self.sponge_state[i] = val;
        }
        self.permute();
        self.output_buffer.clear();
        self.output_buffer
            .extend_from_slice(&self.sponge_state[..PASTA_RATE]);
    }

    /// `MultiField32Challenger::flush_f_if_non_empty`.
    fn flush_f_if_non_empty(&mut self) {
        if self.f_buffer.is_empty() {
            return;
        }
        let n_in = self.f_buffer.len();
        let absorb_n = absorb_num_f_elms();
        assert!(n_in <= absorb_n * PASTA_RATE);
        let rb = absorb_radix_bits::<F>();
        let packed: Vec<PastaFp> = self
            .f_buffer
            .chunks(absorb_n)
            .map(|chunk| reduce_packed(chunk, rb))
            .collect();
        self.absorb_rate_padded_with_tag(&packed, n_in as u8);
        self.f_buffer.clear();
        self.f_squeeze_buffer.clear();
    }

    /// `MultiField32Challenger::refill_f_squeeze_from_inner`.
    fn refill_f_squeeze_from_inner(&mut self) {
        self.f_squeeze_buffer.clear();
        let squeeze_n = squeeze_num_f_elms();
        for &pf in &self.output_buffer {
            self.f_squeeze_buffer
                .extend(split_pf_to_field_order_limbs::<PastaFp, F>(pf, squeeze_n));
        }
        self.output_buffer.clear();
    }

    /// `CanObserve<F>::observe`.
    fn observe_f(&mut self, v: F) {
        self.output_buffer.clear();
        self.f_squeeze_buffer.clear();
        self.f_buffer.push(v);
        if self.f_buffer.len() == absorb_num_f_elms() * PASTA_RATE {
            self.flush_f_if_non_empty();
        }
    }

    /// `CanObserve<Hash<F, PF, N>>::observe` — flush pending scalars, then absorb
    /// the digest words NATIVELY in `RATE`-sized chunks with the chunk length as
    /// the tag. ⚑ This is NOT the same transcript as splitting the digest into
    /// base-field limbs and observing those (p3 has a test for exactly that).
    fn observe_digest_words(&mut self, words: &[PastaFp]) {
        self.output_buffer.clear();
        self.f_squeeze_buffer.clear();
        self.flush_f_if_non_empty();
        for chunk in words.chunks(PASTA_RATE) {
            self.absorb_rate_padded_with_tag(chunk, chunk.len() as u8);
            self.f_squeeze_buffer.clear();
        }
    }

    /// One base-field challenge — the body of `CanSample::sample`.
    fn sample_f(&mut self) -> F {
        self.flush_f_if_non_empty();
        if self.f_squeeze_buffer.is_empty() {
            if !self.input_buffer.is_empty() || self.output_buffer.is_empty() {
                self.duplexing();
            }
            self.refill_f_squeeze_from_inner();
        }
        self.f_squeeze_buffer
            .pop()
            .expect("output buffer should be non-empty")
    }

    fn sample_ext(&mut self) -> EF {
        EF::from_basis_coefficients_fn(|_| self.sample_f())
    }

    fn sample_bits(&mut self, bits: usize) -> usize {
        assert!(bits < (usize::BITS as usize));
        assert!((1 << bits) < F::ORDER_U32);
        let r: F = self.sample_f();
        (r.as_canonical_u32() as usize) & ((1 << bits) - 1)
    }

    fn check_witness(&mut self, bits: usize, w: F) -> bool {
        if bits == 0 {
            return true;
        }
        self.observe_f(w);
        self.sample_bits(bits) == 0
    }

    /// `CanFinalizeDigest::finalize` — the window the lockstep check uses.
    fn finalize(mut self) -> [PastaFp; PASTA_RATE] {
        let had_pending_f = !self.f_buffer.is_empty();
        self.flush_f_if_non_empty();
        if !had_pending_f {
            self.duplexing();
        }
        self.sponge_state[..PASTA_RATE].try_into().unwrap()
    }
}

// ===========================================================================
// The recording transcript: real challenger + replica, in lockstep.
// ===========================================================================

/// The Pasta suite's [`FixtureTranscript`]: p3's own
/// `MultiField32Challenger` (whose outputs the fixture carries) driven in
/// lockstep with a [`SpongeReplica`] (whose sponge states the fixture carries).
pub struct MinaPastaRecording {
    real: MinaChallenger,
    replica: SpongeReplica,
    events: Vec<String>,
}

impl MinaPastaRecording {
    fn new() -> Self {
        Self {
            real: MinaChallenger::new(MinaPoseidonPerm)
                .expect("BabyBear order < Pasta order, RATE < WIDTH"),
            replica: SpongeReplica::new(),
            events: Vec::new(),
        }
    }

    /// ⚑ THE CHECK THAT MAKES THE REPLICA WORTH PUBLISHING. `finalize` permutes
    /// once and returns `sponge_state[..RATE]`, so agreeing here is agreement on
    /// the REAL challenger's inner sponge — not just on its sampled outputs.
    fn assert_lockstep(&self, after: &str) {
        let real = self.real.clone().finalize();
        let replica = self.replica.clone().finalize();
        assert_eq!(
            real,
            replica,
            "the MultiField32 replica diverged from p3's own challenger after `{after}` \
             (event #{}) — the sponge states this fixture carries would describe a different \
             state machine",
            self.events.len()
        );
    }
}

impl FixtureTranscript<MINA_DIGEST_ELEMS> for MinaPastaRecording {
    type Word = PastaFp;

    fn observe_f(&mut self, v: F) {
        self.real.observe(v);
        self.replica.observe_f(v);
        self.events
            .push(format!(r#"{{"op":"observeF","v":{}}}"#, f_u32(v)));
        self.assert_lockstep("observeF");
    }

    fn observe_digest(&mut self, d: &[PastaFp; MINA_DIGEST_ELEMS]) {
        self.real
            .observe(Hash::<F, PastaFp, MINA_DIGEST_ELEMS>::from(*d));
        self.replica.observe_digest_words(d);
        self.events.push(format!(
            r#"{{"op":"observeDigest","w":{}}}"#,
            arr(d.iter().map(|w| pasta_dec(*w)))
        ));
        self.assert_lockstep("observeDigest");
    }

    fn sample_ext(&mut self) -> EF {
        let real: EF = self.real.sample_algebra_element();
        let replica = self.replica.sample_ext();
        assert_eq!(
            real, replica,
            "the MultiField32 replica sampled a different challenge element"
        );
        self.events
            .push(format!(r#"{{"op":"sampleExt","v":{}}}"#, ef_json(real)));
        self.assert_lockstep("sampleExt");
        real
    }

    fn check_witness(&mut self, bits: usize, w: F) -> bool {
        let real = self.real.check_witness(bits, w);
        let replica = self.replica.check_witness(bits, w);
        assert_eq!(
            real, replica,
            "the MultiField32 replica disagreed on a proof-of-work witness"
        );
        self.events.push(format!(
            r#"{{"op":"checkWitness","bits":{bits},"w":{}}}"#,
            f_u32(w)
        ));
        self.assert_lockstep("checkWitness");
        real
    }

    fn sample_bits(&mut self, bits: usize) -> usize {
        let real = self.real.sample_bits(bits);
        let replica = self.replica.sample_bits(bits);
        assert_eq!(
            real, replica,
            "the MultiField32 replica sampled different query bits"
        );
        self.events
            .push(format!(r#"{{"op":"sampleBits","bits":{bits},"v":{real}}}"#));
        self.assert_lockstep("sampleBits");
        real
    }

    fn record_json(&self) -> String {
        format!(
            r#""transcript":{},"spongeStates":{}"#,
            arr(self.events.iter().cloned()),
            arr(self
                .replica
                .states
                .iter()
                .map(|s| arr(s.iter().map(|x| pasta_dec(*x))))),
        )
    }
}

// ===========================================================================
// The suite.
// ===========================================================================

/// [`DreggMinaConfig`] as a fixture hash suite: Mina-Poseidon commitments over
/// Pasta `Fp`, single-element digests, `MultiField32Challenger` transcript.
pub struct MinaPastaSuite;

impl FixtureHashSuite<MINA_DIGEST_ELEMS> for MinaPastaSuite {
    type Word = PastaFp;
    type ValMmcs = MinaValMmcs;
    type ChallengeMmcs = MinaChallengeMmcs;
    type Challenger = MinaChallenger;
    type Config = DreggMinaConfig;
    type Transcript = MinaPastaRecording;

    const HASH_NAME: &'static str = "mina-poseidon-pasta";
    /// ⚑ 31: a Merkle root that fits in 31 bits is a root the Mina-Poseidon hash
    /// never touched. The same runtime canary `tests/mina_terminal_tooth.rs`
    /// runs, and it exists because a hash swap that silently no-ops still type-
    /// checks.
    const MIN_DIGEST_WORD_BITS: u64 = 31;

    fn config(log_blowup: usize, num_queries: usize, query_pow_bits: usize) -> DreggMinaConfig {
        create_mina_config_with_fri(
            log_blowup,
            /* log_final_poly_len */ 0,
            /* max_log_arity     */ 1,
            num_queries,
            /* commit_pow_bits   */ 0,
            query_pow_bits,
        )
    }

    fn new_transcript() -> MinaPastaRecording {
        MinaPastaRecording::new()
    }

    fn digest_json(d: &[PastaFp; MINA_DIGEST_ELEMS]) -> String {
        arr(d.iter().map(|w| pasta_dec(*w)))
    }
}

#[cfg(test)]
mod tests {
    use p3_field::integers::QuotientMap;

    use super::*;

    /// The three derived constants a re-implementer must get right. They are the
    /// ETH wrap's, which is a RESULT (Pasta and BN254 land on the same three),
    /// not a design choice.
    #[test]
    fn pasta_challenger_pack_split_constants() {
        assert_eq!(absorb_radix_bits::<F>(), 31);
        assert_eq!(absorb_num_f_elms(), 8);
        assert_eq!(squeeze_num_f_elms(), 7);
        assert_eq!(PASTA_WIDTH, 3);
        assert_eq!(PASTA_RATE, 2);
    }

    /// The replica against p3's OWN challenger over a transcript that exercises
    /// every arm: a partial scalar batch, a full 16-scalar auto-flush, a native
    /// digest absorb mid-batch, extension samples that cross a squeeze-buffer
    /// refill, and bit sampling.
    #[test]
    fn replica_tracks_p3_multifield_challenger() {
        let mut real =
            MinaChallenger::new(MinaPoseidonPerm).expect("challenger constants are valid");
        let mut rep = SpongeReplica::new();

        let check = |real: &MinaChallenger, rep: &SpongeReplica, at: &str| {
            assert_eq!(
                real.clone().finalize(),
                rep.clone().finalize(),
                "sponge diverged at {at}"
            );
        };

        // 3 scalars: a PARTIAL batch, nothing flushed yet.
        for i in 0..3u32 {
            real.observe(F::from_u32(i + 1));
            rep.observe_f(F::from_u32(i + 1));
        }
        check(&real, &rep, "partial batch");

        // A native digest absorb: flushes the partial batch, then absorbs the
        // Pasta word with tag 1.
        let d = [PastaFp::from_int(123456789u64)];
        real.observe(Hash::<F, PastaFp, 1>::from(d));
        rep.observe_digest_words(&d);
        check(&real, &rep, "native digest absorb");

        // Exactly 16 scalars: the auto-flush boundary (absorb_num_f_elms * RATE).
        for i in 0..16u32 {
            real.observe(F::from_u32(1_000 + i));
            rep.observe_f(F::from_u32(1_000 + i));
        }
        check(&real, &rep, "auto-flush boundary");

        // 8 extension samples = 32 base limbs > one 14-limb squeeze row, so the
        // refill path runs more than once.
        for k in 0..8 {
            let a: EF = real.sample_algebra_element();
            let b = rep.sample_ext();
            assert_eq!(a, b, "challenge {k} diverged");
            check(&real, &rep, "sample_ext");
        }

        // Bit sampling and a PoW check, both after fresh observations.
        real.observe(F::from_u32(7));
        rep.observe_f(F::from_u32(7));
        for bits in [1usize, 8, 22] {
            assert_eq!(real.sample_bits(bits), rep.sample_bits(bits));
            check(&real, &rep, "sample_bits");
        }
        for (bits, w) in [(0usize, F::ZERO), (4usize, F::from_u32(9))] {
            assert_eq!(real.check_witness(bits, w), rep.check_witness(bits, w));
            check(&real, &rep, "check_witness");
        }

        assert!(
            !rep.states.is_empty(),
            "the replica recorded no permutations — the sponge log would be empty"
        );
    }

    /// ⚑ REJECT polarity: the replica is not accidentally a permissive twin. A
    /// natively-absorbed digest and the same digest observed as packed base
    /// limbs are DIFFERENT transcripts, and both the real challenger and the
    /// replica must say so.
    #[test]
    fn native_digest_absorb_is_not_the_scalar_path() {
        let d = [PastaFp::from_int(987654321u64)];

        let mut a = SpongeReplica::new();
        a.observe_digest_words(&d);

        let mut b = SpongeReplica::new();
        for limb in split_pf_to_field_order_limbs::<PastaFp, F>(d[0], squeeze_num_f_elms()) {
            b.observe_f(limb);
        }

        assert_ne!(
            a.clone().finalize(),
            b.finalize(),
            "absorbing a digest natively and absorbing its base-field limbs produced the SAME \
             transcript — an o1js verifier could then be fed either"
        );

        let mut real = MinaChallenger::new(MinaPoseidonPerm).unwrap();
        real.observe(Hash::<F, PastaFp, 1>::from(d));
        assert_eq!(real.finalize(), a.finalize());
    }
}
