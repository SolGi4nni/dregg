//! # The Mina STATE-HASH seam, on the emitted bytes — `OWNHASH` stops being a free witness.
//!
//! ⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): every constraint under test is LEAN-AUTHORED and
//! LEAN-COMPILED (`Dregg2.Circuit.Emit.LightClientMinaLinkAir.minaLinkDesc` is
//! `EffectLower.lowerTiedAir` of the `EffectAir` source `minaLinkAir`). This file writes no AIR. It
//! reads two emitted descriptors and asserts they agree with each other and with Lean's literals.
//!
//! ## The claim, and what makes it checkable here
//!
//! `LightClientMinaLinkAir` used to say, in its own header: *"`OWNHASH` is a witnessed nonet … a
//! prover free to choose `OWNHASH` can fabricate a chain of any length."* The segment descriptor now
//! carries a `proof_bind` whose commitment is **six `Fp` elements at nine `Faithful9` lanes each**
//!
//!     salt("MinaProtoState")[0..2]  ‖  PARENT  ‖  BODYHASH  ‖  OWNHASH        = 54 lanes
//!
//! against a nine-lane program pin. Mina's own identity is
//! `state_hash = Poseidon_Fp(salt "MinaProtoState")[previous_state_hash ; state_body_hash]`
//! (`Bridge/MinaStateHashDerive.lean:31`, the daemon's `protocol_state.ml:45-55`) — **two field
//! elements at rate 2, one permutation** — and the pinned program is `dregg-pasta-fp-absorb::v1`,
//! which computes exactly `perm(state + [x₀, x₁, 0])` with the incoming state a PUBLIC INPUT.
//!
//! ## ⚑ Three things this file checks that nothing else could
//!
//! 1. **The program pin is the real program.** Lean cannot compute blake3, so `ABSORB_VK_LANES` is a
//!    transcription — and a transcription is only a gate if something recomputes it. The wraplink
//!    drift (`LightClientMinaAir:702-709`) is the measured reason: a head once pinned
//!    `[460719650, …]` while the served sub-proof fingerprinted to `[172082222, …]`, so **the bind
//!    named a program no descriptor in this tree has.**
//! 2. **The salt constants are the salt.** The 27 `.const` head lanes of the commitment are what
//!    make the bound sub-proof a *Mina* state hash rather than a generic two-input Poseidon. With a
//!    free incoming state the seam would be VACUOUS and not weakly so: `perm` is a permutation, so
//!    for any target `out` a prover picks `state := perm⁻¹(T) − [x₀,x₁,0]` and the sub-proof is
//!    honest. These lanes are recomposed and compared against **openmina's own regression
//!    constants**, not against the Lean file that emitted them.
//! 3. **The two descriptors' shapes agree.** The absorb descriptor's public inputs must actually
//!    have room for a salted state and a squeeze, or the seam names a program that cannot state the
//!    sentence.
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_statehash_seam_proves -- --nocapture`

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, ProofBindSpec, VmConstraint2, parse_vm_descriptor2,
};
use dregg_circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

const LINK_JSON: &str = include_str!("../descriptors/by-name/dregg-mina-lightclient-link-v1.json");
const ABSORB_JSON: &str = include_str!("../descriptors/by-name/pasta-fp-absorb.json");

const LINK_NAME: &str = "dregg-mina-lightclient-link::v1";
const ABSORB_NAME: &str = "dregg-pasta-fp-absorb::v1";

/// `LightClientMinaLinkAir.ABSORB_VK_LANES`, transcribed. Recomputed below.
const LEAN_ABSORB_VK_LANES: [i64; 9] = [
    446814635, 83884421, 374082988, 139195248, 519518863, 422740375, 389354132, 515631608, 9097818,
];

/// `LightClientMinaLinkAir.MINA_PROTO_STATE_SALT_LANES`, transcribed. Recomposed below against
/// openmina's regression constants.
const LEAN_SALT_LANES: [i64; 27] = [
    116766262, 149354484, 292986828, 413194933, 280149768, 225329418, 86819885, 115568088, 756181,
    484328300, 122810986, 211984088, 66952329, 462241909, 111193962, 66311195, 117199812, 1110329,
    340957929, 274801759, 113970126, 217898572, 2899587, 228371615, 197690145, 523247988, 2877414,
];

/// ⚑ **THE EXTERNAL ANCHOR — openmina's own `Random_oracle.salt "MinaProtoState"`.** These three
/// decimals are the regression constants at `poseidon/tests/test_hash_params.rs:28-51` in
/// o1-labs/openmina, which exist there for exactly this purpose. `Bridge/MinaStateHashDerive.lean`
/// pins the same three; comparing against them here rather than against that file is what keeps the
/// check from being a transcription of a transcription.
const OPENMINA_SALT_PROTO_STATE: [&str; 3] = [
    "5218970939948495870036503265499543025475317910763049867270287867667146978870",
    "7663210626148314949787033187186036425676070286961909238040356477815169631084",
    "19859188289320816036969227839574854326171440874550138016648548415357198703337",
];

/// The link descriptor's column layout (`LightClientMinaLinkAir` §1).
const PARENT_0: usize = 0;
const OWNHASH_0: usize = 9;
const BODYHASH_0: usize = 22;
const HASH_VK_0: usize = 31;
const LINK_WIDTH: usize = 40;

/// `PastaFieldSound.SK` — 32 eight-bit limbs an `Fp` element on the absorb side.
const SK: usize = 32;

fn link_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(LINK_JSON).expect("the segment descriptor parses")
}

fn absorb_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(ABSORB_JSON).expect("the absorb descriptor parses")
}

/// Nine base-`2^29` lanes of a 32-byte value, least-significant first (Lean `keyToLanes9`,
/// `Faithful9::from_key_lanes9`): `8·29 + 24 = 256` exactly, machine-checked injective.
fn key_lanes9(bytes: &[u8; 32]) -> [i64; 9] {
    let mut v = [0i64; 9];
    let mut acc: u128 = 0;
    let mut bits = 0usize;
    let mut out = 0usize;
    for b in bytes.iter() {
        acc |= u128::from(*b) << bits;
        bits += 8;
        while bits >= 29 && out < 8 {
            v[out] = (acc & ((1u128 << 29) - 1)) as i64;
            acc >>= 29;
            bits -= 29;
            out += 1;
        }
    }
    v[8] = acc as i64;
    v
}

/// Recompose nine base-`2^29` lanes into a DECIMAL string, by repeated multiply-add on the decimal
/// digits — so no bignum dependency and no chance to transcribe an intermediate wrong.
fn lanes9_to_decimal(lanes: &[i64]) -> String {
    // value = Σ lane_i · 2^(29 i), computed most-significant-first as ((l8·2^29 + l7)·2^29 + …).
    let mut digits: Vec<u32> = vec![0];
    let mul_add = |digits: &mut Vec<u32>, mul: u64, add: u64| {
        let mut carry = add;
        for d in digits.iter_mut().rev() {
            let cur = u64::from(*d) * mul + carry;
            *d = (cur % 10) as u32;
            carry = cur / 10;
        }
        while carry > 0 {
            digits.insert(0, (carry % 10) as u32);
            carry /= 10;
        }
    };
    for lane in lanes.iter().rev() {
        mul_add(&mut digits, 1 << 29, *lane as u64);
    }
    while digits.len() > 1 && digits[0] == 0 {
        digits.remove(0);
    }
    digits.iter().map(|d| char::from(b'0' + *d as u8)).collect()
}

fn the_seam(d: &EffectVmDescriptor2) -> &ProofBindSpec {
    let mut found = None;
    for c in &d.constraints {
        if let VmConstraint2::ProofBind(m) = c {
            assert!(found.is_none(), "exactly one seam (minaLink_proofBinds)");
            found = Some(m);
        }
    }
    found.expect("the segment descriptor declares a state-hash seam")
}

/// ⚑ **§1 — THE SEAM PINS THE REAL ABSORB PROGRAM.** Side A: the nine lanes Lean carries. Side B:
/// `effect_vm_descriptor2_semantic_fingerprint(pasta-fp-absorb.json)`, recomputed here from that
/// descriptor's own bytes. A drift means one descriptor was re-emitted and the other was not.
#[test]
fn the_seam_pins_the_real_absorb_program() {
    let absorb = absorb_desc();
    assert_eq!(absorb.name, ABSORB_NAME, "the sub-program's identity");
    let fp = effect_vm_descriptor2_semantic_fingerprint(&absorb).expect("representable");
    let lanes = key_lanes9(&fp);

    assert_eq!(
        lanes, LEAN_ABSORB_VK_LANES,
        "LightClientMinaLinkAir.ABSORB_VK_LANES must be the recomputed fingerprint of \
         {ABSORB_NAME}"
    );

    let link = link_desc();
    assert_eq!(link.name, LINK_NAME);
    let seam = the_seam(&link);
    assert_eq!(
        seam.vk_pin.as_deref(),
        Some(&lanes[..]),
        "the seam's vk_pin must be the nine lanes of the ABSORB fingerprint"
    );
    assert!(
        !seam.is_declarative(),
        "the seam must pin its program (ProofBind::is_declarative)"
    );
    seam.width_ok().expect("the seam clears both lane floors");

    println!(
        "\n§1 ⚑ THE SEAM PINS {ABSORB_NAME}\n  fingerprint lanes {lanes:?}\n  \
         recomputed from that descriptor's own canonical bytes, not transcribed."
    );
}

/// ⚑⚑ **§2 — THE SALT CONSTANTS ARE THE SALT.** The commitment's first 27 lanes are `.const`
/// literals; recomposed nine at a time they are `Random_oracle.salt "MinaProtoState"` as openmina
/// pins it. ⚠ Without this the seam binds a generic two-input Poseidon and is VACUOUS: `perm` is a
/// permutation, so a free incoming state lets a prover hit any output it likes.
#[test]
fn the_commitments_salt_head_is_minas_own_salt() {
    let link = link_desc();
    let seam = the_seam(&link);

    assert_eq!(
        seam.commit.len(),
        54,
        "six Fp elements at nine Faithful9 lanes each"
    );

    // The first 27 lanes are CONSTANTS, and they are the salt.
    let mut consts = Vec::with_capacity(27);
    for (i, e) in seam.commit.iter().take(27).enumerate() {
        match e {
            LeanExpr::Const(v) => consts.push(*v),
            other => panic!(
                "commit lane {i} is {other:?}, not a constant — a salt a prover can choose is not \
                 a salt"
            ),
        }
    }
    assert_eq!(
        consts.as_slice(),
        &LEAN_SALT_LANES[..],
        "the emitted salt head drifted from LightClientMinaLinkAir.MINA_PROTO_STATE_SALT_LANES"
    );

    for k in 0..3 {
        let got = lanes9_to_decimal(&consts[9 * k..9 * (k + 1)]);
        assert_eq!(
            got, OPENMINA_SALT_PROTO_STATE[k],
            "salt lane {k} recomposes to {got}, not to openmina's regression constant. The seam \
             would bind a Poseidon under a salt that is not Mina's."
        );
    }

    // ⚑ NON-VACUITY: a salt of zeros would make every assertion above pass for a FRESH sponge, and
    // a fresh sponge is `Poseidon.hash`, not `state_hash`.
    assert!(
        consts.iter().any(|v| *v != 0),
        "the salt head is the zero state — that is an UNSALTED sponge, i.e. a different function"
    );

    println!(
        "\n§2 ⚑⚑ THE SALT HEAD IS `Random_oracle.salt \"MinaProtoState\"`, 27/27 lanes,\n  \
         recomposed against openmina's own regression constants."
    );
}

/// ⚑ **§3 — THE COMMITMENT NAMES THE ROW'S THREE NONETS, IN ORDER, AS COLUMNS.** Lanes 27..53 are
/// `PARENT 0..8`, `BODYHASH 0..8`, `OWNHASH 0..8`. ⚠ The ORDER is load-bearing: the sub-program's
/// two absorbed slots are `(x₀, x₁) = (previous_state_hash, state_body_hash)` and its squeeze is the
/// output, so a transposed pair would bind `Poseidon(body, parent)` — a real hash of the wrong
/// preimage, and every gate would stay green.
#[test]
fn the_commitment_names_parent_then_body_then_own() {
    let link = link_desc();
    let seam = the_seam(&link);
    assert_eq!(link.trace_width, LINK_WIDTH, "the Lean layout");

    let want: Vec<usize> = (0..9)
        .map(|j| PARENT_0 + j)
        .chain((0..9).map(|j| BODYHASH_0 + j))
        .chain((0..9).map(|j| OWNHASH_0 + j))
        .collect();
    let got: Vec<usize> = seam.commit[27..]
        .iter()
        .map(|e| match e {
            LeanExpr::Var(c) => *c,
            other => panic!("commit lane is {other:?}, not a column read"),
        })
        .collect();
    assert_eq!(
        got, want,
        "the commitment must be PARENT ‖ BODYHASH ‖ OWNHASH, in the sub-program's own argument order"
    );

    let vk: Vec<usize> = seam
        .vk
        .iter()
        .map(|e| match e {
            LeanExpr::Var(c) => *c,
            other => panic!("vk lane is {other:?}, not a column read"),
        })
        .collect();
    assert_eq!(
        vk,
        (0..9).map(|i| HASH_VK_0 + i).collect::<Vec<usize>>(),
        "the attested program lanes are the nine HASH_VK columns"
    );

    // ⚑ The guard is UNCONDITIONAL. A column guard would let a prover switch the seam off, and the
    // natural choice (`IS_REAL`) switches it off exactly where the tip lives: the `.last` tip pin
    // reads the final row whether or not that row is real.
    assert_eq!(
        seam.guard,
        LeanExpr::Const(1),
        "the seam must fire on EVERY row; a guard column is an off switch"
    );

    println!("\n§3 ⚑ COMMITMENT = salt ‖ PARENT ‖ BODYHASH ‖ OWNHASH, guard = 1 (unconditional).");
}

/// ⚑ **§4 — THE SUB-PROGRAM CAN STATE THE SENTENCE.** The absorb descriptor exposes six 32-limb
/// register blocks as public inputs: three incoming sponge lanes, two absorbed values, one squeeze.
/// ⚠ This is what makes a SALTED sponge expressible without touching that descriptor — the incoming
/// state is a public input, not a constant. If it were a constant the seam's salt head would be
/// describing something the sub-program cannot vary, and the whole construction would be fiction.
#[test]
fn the_absorb_program_has_room_for_a_salted_state_and_a_squeeze() {
    let absorb = absorb_desc();
    assert_eq!(
        absorb.public_input_count,
        6 * SK,
        "six 32-limb blocks: state[0..2], x0, x1, squeeze"
    );

    // Every public input is bound to a trace cell by a pi_binding, and the three incoming state
    // blocks are bound on the FIRST row — which is what "the initial state is a public input" means.
    let mut first_row_slots = 0usize;
    let mut last_row_slots = 0usize;
    for c in &absorb.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding { row, .. }) = c {
            match row {
                VmRow::First => first_row_slots += 1,
                _ => last_row_slots += 1,
            }
        }
    }
    assert_eq!(
        first_row_slots + last_row_slots,
        6 * SK,
        "every public input is pinned to a trace cell"
    );
    assert!(
        first_row_slots >= 5 * SK,
        "the three incoming state blocks and the two absorbed values are FIRST-row pins; got \
         {first_row_slots} first-row slots. If the incoming state were not a public input, a salted \
         sponge would need a different descriptor and this seam would name the wrong program."
    );
    assert_eq!(
        last_row_slots, SK,
        "exactly one 32-limb block is read on the LAST row: the squeeze"
    );

    println!(
        "\n§4 ⚑ {ABSORB_NAME}: {} PIs = state(3) ‖ x0 ‖ x1 ‖ squeeze, {first_row_slots} pinned on \
         row 0 and {last_row_slots} on the last.\n  The incoming state is a PUBLIC INPUT, so a \
         salted sponge is the SAME descriptor with different public inputs.",
        absorb.public_input_count
    );
}

/// ⚑ **§5 — THE TWO PROGRAMS ARE DIFFERENT PROGRAMS.** A seam that pinned its own carrier's
/// fingerprint would be one bind wearing two names, and §1 would still pass.
#[test]
fn the_seam_does_not_pin_its_own_carrier() {
    let link = link_desc();
    let absorb = absorb_desc();
    assert_ne!(
        effect_vm_descriptor2_semantic_fingerprint(&link).expect("representable"),
        effect_vm_descriptor2_semantic_fingerprint(&absorb).expect("representable"),
        "the segment descriptor and its sub-program must be distinct objects"
    );
}
