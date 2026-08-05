//! ⚑⚑ **THE MINA LIGHT CLIENT'S CARRIER IS BOUND TO A SUB-PROOF THAT EXISTS — measured on the
//! emitted bytes of BOTH descriptors, from two independent sources.**
//!
//! # What this file gates
//!
//! `dregg-mina-lightclient-verify::v1` used to publish `PICKLES_OK`: a witnessed boolean column
//! forced `= 1`, with nothing in the circuit computing it. Since 2026-08-05 it publishes two things
//! instead — `PICKLES_WITNESSED` (the residue, still a bit, and named so) and `WRAP_FS_PROVED`,
//! whose `= 1` is the guard of **nine `proof_bind` constraints** pinning the row's attested program
//! lane by lane to the semantic fingerprint of `dregg-pasta-fq-chainlink::v1`.
//!
//! A pinned literal is only a gate if the two sides come from independent places
//! (`feedback-a-pin-against-its-own-definition-is-decoration`). Here they do:
//!
//! * side A — the nine `vk_pin` literals inside `dregg-mina-lightclient-verify-v1.json`, emitted by
//!   Lean from `LightClientMinaAir.CHAINLINK_VK_LANES`;
//! * side B — `effect_vm_descriptor2_semantic_fingerprint(pasta-fq-chainlink.json)`, recomputed here
//!   from the SIBLING descriptor's own canonical bytes.
//!
//! If the chainlink descriptor is re-emitted and the Mina one is not, side B moves and this goes RED.
//! That is the intended coupling: a light client must not keep accepting sub-proofs of a program
//! that changed shape.
//!
//! ⚑⚑ **AND THAT IS NOT HYPOTHETICAL — IT HAPPENED, AND THIS FILE WAS THE ONLY THING THAT NOTICED.**
//! `7a4b8ab00` wrote the (then-wraplink) fingerprint into Lean correctly. `75df624cf` re-emitted
//! `pasta-fq-wraplink.json` — its subject line is *"140 served descriptors were not the Lean
//! object"* — and moved its bytes; the Lean literal did not follow. From then until 2026-08-05 the
//! head descriptor pinned `[460719650, 491018495, …]` while the served sub-proof fingerprinted to
//! `[172082222, 381973190, …]`, so **the recursion bind named a program no descriptor in this tree
//! has.** This test was RED the whole time and nothing else was.
//!
//! ⚑ That is why the pin now has a SECOND reader that runs on a node:
//! `dregg_turn::executor::mina_head_verifier::check_subproof_program_pin` recomputes side B at
//! verify time and REFUSES the head on a mismatch. A gate only a test can go red on is a gate a
//! running node drifts past.
//!
//! ⚠ **SCOPE, said before the assertions.** Nothing here shows a Pickles proof is valid. What the
//! chainlink sub-proof establishes is one absorption of a phase-2 `fq_kimchi` transcript — see
//! `MinaPhase2Chain` and `LightClientMinaAir` §2b, plus the module docs of
//! `turn/src/executor/mina_head_verifier.rs`. This file gates the BINDING, not the cryptography.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, parse_vm_descriptor2};
use dregg_circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};

const LINK_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fq-chainlink.json");
/// The 46 chain links' public-input vectors, one line each — TRACKED. Link 45 is the sub-proof the
/// honest head names; the emit directory's per-link files are gitignored and must never be read.
const CHAINLINK_ALL_PIS: &str = include_str!("fixtures/pasta-fq-chainlink-pis.txt");
/// The number of links the phase-2 chain folds — one tracked PI line each.
const CHAINLINK_LINKS: usize = 46;
const MINA_LC_JSON: &str =
    include_str!("../descriptors/by-name/dregg-mina-lightclient-verify-v1.json");

/// The chainlink sub-proof's descriptor name, as the Mina AIR's docblock names it.
const CHAINLINK_NAME: &str = "dregg-pasta-fq-chainlink::v1";

/// Domain separation for the sub-proof public-input commitment the Mina row publishes. Changing
/// this string is a wire-format flag day for `MinaHeadProofWire`. ⚑ It moved with the descriptor on
/// 2026-08-05 (`wraplink-` → `chainlink-`), so a commitment minted for the seven-block program
/// cannot be re-read as one for the eight-block program.
pub const CHAINLINK_PI_COMMITMENT_CONTEXT: &str =
    "dregg.mina-lightclient.chainlink-subproof-pi-commitment.v1";

/// ⚑ The nine lanes `LightClientMinaAir.CHAINLINK_PI_LANES` transcribes. Lean cannot compute blake3,
/// so the literal there is a transcription — and a transcription is only a gate if something
/// recomputes it. This is that something.
const LEAN_CHAINLINK_PI_LANES: [u64; 9] = [
    76470648, 44150818, 361910605, 443692671, 242143308, 490185822, 240590146, 360276303, 4019771,
];

/// Column layout of `dregg-mina-lightclient-verify::v1` after the recursion rung.
const WRAP_FS_PROVED: usize = 30;
const SUB_VK_BASE: usize = 31;
const SUB_PI_BASE: usize = 40;
const STATE_LANES: usize = 9;

/// Nine base-`2^29` lanes of a 32-byte value, least-significant first (Lean `keyToLanes9`,
/// `Faithful9::from_key_lanes9`): `8·29 + 24 = 256` exactly, machine-checked injective.
pub fn key_lanes9(bytes: &[u8; 32]) -> [u64; 9] {
    let mut v = [0u64; 9];
    let mut acc: u128 = 0;
    let mut bits = 0usize;
    let mut out = 0usize;
    for b in bytes.iter() {
        acc |= (*b as u128) << bits;
        bits += 8;
        while bits >= 29 && out < 8 {
            v[out] = (acc & ((1u128 << 29) - 1)) as u64;
            acc >>= 29;
            bits -= 29;
            out += 1;
        }
    }
    v[8] = acc as u64;
    v
}

/// ⚑ **THE SUB-PROOF PUBLIC-INPUT COMMITMENT.** blake3 derive-key over the context above, absorbing
/// every public input as its canonical `u32` little-endian, in descriptor order. This is the value
/// the Mina row PI-binds at slots 20..28 and the consumer recomputes from the sub-proof it verifies.
pub fn chainlink_pi_commitment(pis: &[u32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(CHAINLINK_PI_COMMITMENT_CONTEXT);
    h.update(&(pis.len() as u64).to_le_bytes());
    for v in pis {
        h.update(&v.to_le_bytes());
    }
    *h.finalize().as_bytes()
}

/// Link 45's public inputs: the LAST line of the tracked 46-line aggregate.
fn link45_pis() -> Vec<u32> {
    let n = CHAINLINK_ALL_PIS.lines().count();
    assert_eq!(
        n, CHAINLINK_LINKS,
        "the tracked chain-link PI aggregate carries {n} lines; the fold is {CHAINLINK_LINKS} links"
    );
    parse_pis(
        CHAINLINK_ALL_PIS
            .lines()
            .nth(CHAINLINK_LINKS - 1)
            .expect("checked non-empty above"),
    )
}

fn parse_pis(text: &str) -> Vec<u32> {
    text.split_whitespace()
        .map(|t| t.parse::<u32>().expect("public input is a canonical u32"))
        .collect()
}

fn link_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(LINK_DESC_JSON).expect("chainlink descriptor parses")
}

fn mina_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(MINA_LC_JSON).expect("mina lightclient descriptor parses")
}

/// The `proof_bind` constraints of a descriptor, in emission order.
fn proof_binds(d: &EffectVmDescriptor2) -> Vec<&dregg_circuit::descriptor_ir2::ProofBindSpec> {
    d.constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::ProofBind(p) => Some(p),
            _ => None,
        })
        .collect()
}

/// ⚑ **THE PIN IS AGAINST AN INDEPENDENT SOURCE.** The nine `vk_pin` literals the Mina descriptor
/// carries ARE the nine `Faithful9` lanes of the chainlink descriptor's semantic fingerprint,
/// recomputed here from that descriptor's own canonical bytes.
#[test]
fn the_mina_carrier_pins_the_real_chainlink_program() {
    let link = link_desc();
    assert_eq!(
        link.name, CHAINLINK_NAME,
        "the sub-proof descriptor identity"
    );

    let fp = effect_vm_descriptor2_semantic_fingerprint(&link).expect("representable");
    let lanes = key_lanes9(&fp);

    let mina = mina_desc();
    let binds = proof_binds(&mina);
    // ⚑ 2026-08-05: ONE bind carrying nine LANES, where it was nine one-felt binds.
    assert_eq!(
        binds.len(),
        1,
        "the Mina light client declares one proof_bind, carrying every program lane"
    );
    let b = binds[0];
    assert_eq!(
        b.guard,
        LeanExpr::Var(WRAP_FS_PROVED),
        "the bind is guarded by WRAP_FS_PROVED"
    );
    assert_eq!(b.vk.len(), STATE_LANES, "nine attested program lanes");
    assert_eq!(
        b.commit.len(),
        STATE_LANES,
        "nine declared commitment lanes"
    );
    for i in 0..STATE_LANES {
        assert_eq!(
            b.vk[i],
            LeanExpr::Var(SUB_VK_BASE + i),
            "lane {i} attests program lane column {i}"
        );
        assert_eq!(
            b.commit[i],
            LeanExpr::Var(SUB_PI_BASE + i),
            "lane {i}'s declared commitment is the PI-BOUND lane, not a free column"
        );
    }
    assert_eq!(
        b.vk_pin.as_deref(),
        Some(&lanes.iter().map(|l| *l as i64).collect::<Vec<i64>>()[..]),
        "the vk_pin must be the nine lanes of the CHAINLINK fingerprint recomputed from \
         pasta-fq-chainlink.json — a drift here means one descriptor was re-emitted and the \
         other was not"
    );
    assert!(
        !b.is_declarative(),
        "the bind must not be the unpinned shape (ProofBind::is_declarative)"
    );
    // ⚑ AND IT IS NOT A PREFIX PIN: the declared program names every lane the seam attests.
    b.width_ok()
        .expect("the Mina seam must satisfy the lane discipline at admission");
}

/// ⚑ **NINE LANES, NOT ONE FELT — the number said out loud.** A single-felt program tie is worth
/// `2^31`. Nine `Faithful9` lanes cover 256 bits exactly and the lanes sit on nine DISTINCT columns,
/// so a forger must match all nine. This asserts the width structurally rather than in prose.
#[test]
fn the_program_pin_is_nine_distinct_lanes() {
    let mina = mina_desc();
    let binds = proof_binds(&mina);
    let mut cols: Vec<usize> = binds
        .iter()
        .flat_map(|b| b.vk.iter())
        .map(|e| match e {
            LeanExpr::Var(c) => *c,
            _ => panic!("a program lane must be a column"),
        })
        .collect();
    cols.sort_unstable();
    cols.dedup();
    assert_eq!(
        cols.len(),
        STATE_LANES,
        "nine DISTINCT program-lane columns"
    );

    let link = link_desc();
    let fp = effect_vm_descriptor2_semantic_fingerprint(&link).expect("representable");
    let lanes = key_lanes9(&fp);
    // The nine lanes reconstruct the 256-bit fingerprint exactly: 8 lanes < 2^29, top < 2^24.
    for (i, l) in lanes.iter().enumerate().take(8) {
        assert!(*l < (1 << 29), "lane {i} is a base-2^29 digit");
    }
    assert!(lanes[8] < (1 << 24), "the top lane is below 2^24");
    let mut recomposed = [0u8; 32];
    let mut acc: u128 = 0;
    let mut bits = 0usize;
    let mut out = 0usize;
    for l in lanes.iter() {
        acc |= (*l as u128) << bits;
        bits += 29;
        while bits >= 8 && out < 32 {
            recomposed[out] = (acc & 0xff) as u8;
            acc >>= 8;
            bits -= 8;
            out += 1;
        }
    }
    assert_eq!(
        recomposed, fp,
        "the nine lanes ARE the fingerprint, losslessly"
    );
}

/// ⚑ **THE COMMITMENT THE MINA ROW PUBLISHES IS THE SUB-PROOF'S OWN PUBLIC INPUTS.**
///
/// Printed as the Lean literal so `LightClientMinaAir.CHAINLINK_PI_LANES` is a transcription of a
/// computed value and not a number somebody chose — and asserted against the emitted descriptor's
/// PI arity so the two cannot drift in shape.
#[test]
fn the_published_commitment_covers_the_sub_proofs_public_inputs() {
    let link = link_desc();
    let pis = link45_pis();
    assert_eq!(
        pis.len(),
        link.public_input_count,
        "the fixture PI vector is the descriptor's declared arity"
    );
    assert_eq!(
        pis.len(),
        256,
        "eight 32-limb pin blocks: in(3) ++ out(3) ++ absorbed(2)"
    );

    let digest = chainlink_pi_commitment(&pis);
    let lanes = key_lanes9(&digest);
    assert_eq!(
        lanes, LEAN_CHAINLINK_PI_LANES,
        "LightClientMinaAir.CHAINLINK_PI_LANES is a TRANSCRIPTION of this digest; a mismatch means \
         the sub-proof's public inputs, the commitment context, or the Lean literal moved"
    );

    // The Mina descriptor PI-binds nine columns for it, at slots 20..28.
    let mina = mina_desc();
    // ⚑ 30, not 29: `adf5aa892` appended `PI_ANCHOR_H` at slot 29. This literal said 29 for hours
    // after that flip, which is the pin doing its job and nobody reading it.
    assert_eq!(
        mina.public_input_count, 30,
        "20 + nine commitment lanes + the published anchor height"
    );
    let pinned: Vec<(usize, usize)> = mina
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) => {
                Some((*col, *pi_index))
            }
            _ => None,
        })
        .collect();
    for i in 0..STATE_LANES {
        assert!(
            pinned.contains(&(SUB_PI_BASE + i, 20 + i)),
            "commitment lane {i} must be PI-bound at slot {}",
            20 + i
        );
    }
}
