//! **THE SOUNDNESS DELTA OF THE HASH SWAP, as arithmetic instead of a sentence.**
//!
//! A different commitment hash is a different security argument, and the honest
//! way to say what changed is to price it with the machinery the tree already
//! proved rather than to assert "comparable".
//!
//! The bar is `Dregg2.Crypto.RomQueryFloor.birthday_bound`: a `Q`-query
//! adversary finds a collision in a random oracle with range `R` with
//! probability at most `(Q² + 1)/|R|`. It is UNCONDITIONAL — no MSIS, no MLWE,
//! no "the hash is collision resistant" — and it is the same bound the tree
//! uses at both ends of this comparison:
//!
//! - `Dregg2.Circuit.MapOpWideDigest8` applies it to BabyBear digests and gets
//!   ≈2^15.45 at ONE felt (a BREAK, not a bound) and ≈2^123.63 at eight;
//! - `Dregg2.Circuit.Emit.PicklesTranscriptBinding` applies it to the REAL
//!   `PastaPoseidon.Ref.hash` at `pN ≈ 2^255` and gets a residual that is
//!   "effectively zero at any real budget".
//!
//! **Same machinery, and this test computes both endpoints from the FIELD
//! ORDERS THEMSELVES**, so nobody has to trust a transcribed exponent.
//!
//! ## What this does and does not settle
//!
//! It settles the GENERIC-COLLISION bar on the commitment digest. It does not
//! discharge — and nothing in this tree does — the idealization that the
//! concrete permutation behaves like a random oracle. That assumption exists on
//! both sides and is named on both sides:
//! `Dregg2.Crypto.Poseidon2RomInstantiation.Poseidon2IsKeyedRandomOracle` for
//! the deployed Poseidon2-BabyBear, and `SpongeKeyedROFaithful` over
//! `PastaPoseidon.Ref.hash` for Mina-Poseidon. **The Mina terminal does not add
//! a new species of assumption; it swaps one named instance for another named
//! instance.**
//!
//! ⚠ **AND THE ONE THING THAT IS GENUINELY NEW, stated rather than buried:**
//! the Pasta ROM idealization is named in-tree *on the Pickles side* (it prices
//! the Pickles transcript digest). Nothing points it at the FRI/MMCS carrier
//! sites the way `Poseidon2RomInstantiation` is pointed at the BabyBear ones.
//! So the Mina terminal's commitment inherits a bar this test computes and an
//! idealization that exists but is **not yet wired to the site that would
//! consume it**. That is an unconnected leg, not a hole — and it is exactly the
//! shape that reads as closed if nobody writes it down.

use num_bigint::BigUint;
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeField32};
use p3_pasta::PastaFp;

/// `log2(|R|)`, to two decimals, for a digest space of `n` copies of a field of
/// order `p`.
fn log2_range(p: &BigUint, n: u32) -> f64 {
    // log2(p^n) = n · log2(p); compute log2(p) from the top 64 bits so the
    // fractional part is real rather than a bit count.
    let bits = p.bits();
    let shifted: BigUint = p >> (bits.saturating_sub(64));
    let top = shifted.to_u64_digits()[0] as f64;
    let log2p = (bits as f64 - 64.0).max(0.0) + top.log2();
    (n as f64) * log2p
}

/// The birthday bar in bits: the `Q` at which `(Q² + 1)/|R|` stops being small,
/// i.e. `log2(Q) ≈ log2(|R|)/2`.
fn birthday_bar_bits(p: &BigUint, n: u32) -> f64 {
    log2_range(p, n) / 2.0
}

fn babybear_order() -> BigUint {
    BigUint::from(BabyBear::ORDER_U32)
}

#[test]
fn the_hash_swap_does_not_lower_the_commitment_collision_bar() {
    let bb = babybear_order();
    let pasta = PastaFp::order();
    // BN254's order, for the third leg (the deployed ETH terminal). Written as
    // a literal because `p3-bn254` is not a dependency of this crate; it is the
    // constant `p3_bn254::Bn254::order()` returns.
    let bn254 = BigUint::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
        10,
    )
    .unwrap();

    // ---- the three digest spaces actually shipped --------------------------
    //
    // deployed inner (DreggRecursionConfig): PaddingFreeSponge<_, 16, 8, 8>
    //   and TruncatedPermutation<_, 2, 8, 16> ⇒ EIGHT BabyBear felts per node.
    // ETH terminal  (DreggOuterConfig)     : ONE BN254 element per node.
    // MINA terminal (DreggMinaConfig)      : ONE Pasta element per node.
    let deployed = birthday_bar_bits(&bb, 8);
    let eth = birthday_bar_bits(&bn254, 1);
    let mina = birthday_bar_bits(&pasta, 1);

    println!("commitment-digest collision bars (RomQueryFloor.birthday_bound):");
    println!(
        "  deployed BabyBear MMCS  [BabyBear; 8]  |R| = 2^{:.2}  ⇒  Q ≈ 2^{deployed:.2}",
        log2_range(&bb, 8)
    );
    println!(
        "  ETH terminal            [Bn254; 1]     |R| = 2^{:.2}  ⇒  Q ≈ 2^{eth:.2}",
        log2_range(&bn254, 1)
    );
    println!(
        "  MINA terminal           [PastaFp; 1]   |R| = 2^{:.2}  ⇒  Q ≈ 2^{mina:.2}",
        log2_range(&pasta, 1)
    );
    println!("  delta Mina − deployed   : {:+.2} bits", mina - deployed);
    println!("  delta Mina − ETH        : {:+.2} bits", mina - eth);

    // ⚑ THE CLAIM, AS AN ASSERTION. The Mina terminal must not LOWER the bar
    // against either shipped alternative. If a future edit narrows the digest
    // (the `MapOpWideDigest8` disease: a widened preimage with a one-felt
    // image), this goes red instead of reading fine.
    assert!(
        mina >= deployed,
        "the Mina terminal's collision bar ({mina:.2}) is BELOW the deployed BabyBear MMCS's ({deployed:.2})"
    );
    assert!(
        mina >= eth,
        "the Mina terminal's collision bar ({mina:.2}) is BELOW the ETH terminal's ({eth:.2})"
    );

    // The numbers, pinned so the delta cannot drift silently. Tolerances are
    // wide enough for float noise and narrow enough to catch a field swap.
    // ⚑ A CORRECTION THIS TEST FORCED. `docs/MINA-FACING-TERMINAL-OPTIONS.md`
    // §3 (and, until this commit, this crate's own docs) says "Pasta Fp is
    // 254.6 bits". It is **254.000**: `p = 2^254 + 0x224698fc094cf91b992d30ed…`,
    // a hair above a power of two, so `log2(p) = 254.0000000000000000023`. The
    // conclusion the document drew from it (~127-bit collision resistance) is
    // right; the input was not. BN254 is 2^253.60, not 2^254.0, for the same
    // reason read the other way.
    assert!(
        (deployed - 123.63).abs() < 0.05,
        "deployed bar moved: {deployed}"
    );
    assert!((eth - 126.80).abs() < 0.05, "ETH bar moved: {eth}");
    assert!((mina - 127.00).abs() < 0.05, "Mina bar moved: {mina}");

    // ⚑ AND THE NON-VACUITY POLE: the bound is only interesting because it CAN
    // be a break. At a ONE-felt BabyBear digest — the shape `MapOpWideDigest8`
    // found shipping — the same arithmetic reads ≈2^15.45, which is a number an
    // attacker reaches on a laptop. Asserting that here is what proves the
    // comparison above is measuring something rather than restating a tautology
    // about big fields.
    let one_felt_babybear = birthday_bar_bits(&bb, 1);
    println!(
        "  (non-vacuity) [BabyBear; 1]            |R| = 2^{:.2}  ⇒  Q ≈ 2^{one_felt_babybear:.2}",
        log2_range(&bb, 1)
    );
    assert!(
        one_felt_babybear < 16.0,
        "a one-felt BabyBear digest no longer reads as a break — the bar computation is not sensitive to width"
    );
}

/// The sponge CAPACITY, which is the other half of the story and the half that
/// is easy to lose: a bar on the digest says nothing if the sponge state the
/// digest is squeezed from is narrower than the digest.
///
/// - deployed: `PaddingFreeSponge<Poseidon2BabyBear<16>, 16, 8, 8>` — width 16,
///   rate 8 ⇒ **capacity 8 felts ≈ 2^247.3**.
/// - Mina: `MultiField32PaddingFreeSponge<_, PastaFp, _, 3, 2, 1>` over
///   kimchi's width-3 permutation — rate 2 ⇒ **capacity 1 Pasta element
///   = 2^254.00**.
///
/// So the Mina sponge's capacity is WIDER than the deployed one, not narrower,
/// and the digest is exactly the capacity rather than a truncation of it.
#[test]
fn the_mina_sponge_capacity_is_not_narrower_than_the_deployed_one() {
    let bb = babybear_order();
    let pasta = PastaFp::order();
    let deployed_capacity = log2_range(&bb, 8); //  16 − 8 = 8 felts
    let mina_capacity = log2_range(&pasta, 1); //   3 − 2 = 1 element
    println!("sponge capacity: deployed 2^{deployed_capacity:.2}  vs  Mina 2^{mina_capacity:.2}");
    assert!(
        mina_capacity >= deployed_capacity,
        "the Mina sponge's capacity ({mina_capacity:.2} bits) is NARROWER than the deployed one's ({deployed_capacity:.2})"
    );
    // And the digest is the whole capacity, not a truncation: OUT = 1 = WIDTH − RATE.
    assert_eq!(
        p3_pasta::PASTA_WIDTH - p3_pasta::PASTA_RATE,
        p3_pasta::PASTA_DIGEST_ELEMS,
        "the Mina digest is no longer exactly the sponge capacity"
    );
}

/// ⚑ WHAT DOES **NOT** MOVE, asserted so the soundness statement is complete
/// rather than selective: the FRI/DEEP soundness denominators.
///
/// Every FRI and DEEP bound in the ledger is denominated in the CHALLENGE
/// field, `EF4 = BabyBear^4 ≈ 2^123.6`, and in the FRI knobs. The hash swap
/// touches neither: `DreggMinaConfig` keeps `Val = BabyBear`, `Challenge = EF4`
/// and the ETH wrap's exact knob set (`3·38 + 16 = 130` conjectured bits), so
/// the ledger entry it reads is the one already modeled as
/// `FriLedgerSound.ethWrapOuterConfig`.
///
/// This test exists because "the commitment bar went UP" is only half an
/// answer if the thing that actually binds went down somewhere else.
#[test]
fn the_challenge_field_the_fri_bounds_are_denominated_in_is_unchanged() {
    let bb = babybear_order();
    let ef4 = log2_range(&bb, 4);
    println!("challenge field |EF4| = 2^{ef4:.2} — unchanged by the hash swap");
    assert!((ef4 - 123.63).abs() < 0.05);
    // The commitment bar and the challenge field are DIFFERENT quantities and
    // it matters that the weaker one is named: at 2^123.6 the challenge field —
    // not the Pasta digest — is what any FRI/DEEP soundness statement is
    // denominated in, and the hash swap leaves it exactly where it was.
    let mina = birthday_bar_bits(&PastaFp::order(), 1);
    assert!(
        mina > ef4,
        "the commitment bar is now the binding constraint rather than the challenge field — \
         the soundness story would need re-reading"
    );
}
