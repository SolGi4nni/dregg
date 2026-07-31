//! # AUTHORIZATION INSIDE THE AIR — the refusal teeth, run by the DEPLOYED prover.
//!
//! **The AIR is Lean-authored.** Every constraint under test comes from
//! `metatheory/Dregg2/Circuit/Emit/TurnAuthLamportEmit.lean`, serialised by `EmitTurnAuthProbe.lean`
//! into `turn-auth-lamport-probe-nb1.json`. This file constructs NO constraints — it parses the
//! emitted bytes, lays a witness, and asks `prove_vm_descriptor2` (the deployed prover, which
//! self-verifies before returning) whether it accepts.
//!
//! ## What was measured before this existed
//!
//! The table census over the whole deployed registry is `{main, poseidon2_chip,
//! poseidon2_state16_chip, range, memory, map_ops, umemory, umem_boundary}` — **no curve table, no
//! signature table.** Every signature check is host-side ed25519 `verify_strict` in
//! `turn/src/executor/authorize.rs`. So a turn proof asserted a legal state transition and nothing
//! about who asked for it, and `transferCapOpenTB` published `actor` and `dst` to PI 47/48 from
//! columns that appear in exactly one constraint each — their own `pi_binding`.
//!
//! ⚑ **A refusal that only the executor performs is exactly the sin**: the host already checks
//! signatures; a light client has no executor. These teeth are therefore run against the AIR, and
//! the refusal that counts is the prover's/verifier's, not a host predicate's.
//!
//! ## The four measurements
//!
//! 1. **CONTROL** — the honest, correctly-signed witness PROVES.
//! 2. **WRONG KEY** — one signature felt moved: REFUSED.
//! 3. **UNSIGNED** — the whole signature block zeroed: REFUSED.
//! 4. **MOVED `dst`** — the turn's recipient column moved by one, everything else untouched
//!    (exactly the free-weld forgery): REFUSED.
//!
//! Cases 2-4 differ from the control ONLY in witness cells; the descriptor, the public inputs and
//! the trace shape are identical, so the refusal cannot come from a shape check.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, chip_absorb_all_lanes, parse_vm_descriptor2,
    prove_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{must_accept, must_refuse_or_unsat_panic};

/// The Lean-emitted descriptor bytes (`EmitTurnAuthProbe.lean`, `probeNb1`).
const PROBE_NB1: &str = include_str!("turn-auth-lamport-probe-nb1.json");

// ---- the column plan, mirroring `TurnAuthLamportEmit`'s generators exactly ----
const W: usize = 8; // felts per digest group (the deployed `CAP_W`)
const BASE: usize = 3; // the probe base: cols 0,1,2 = src, actor, dst
const NB: usize = 1; // blocks signed in this instance
const BLOCK_BITS: usize = 31;
const ELL: usize = BLOCK_BITS * NB; // signed message bits
const CHIP_RATE: usize = 16;

const SIG_B: usize = BASE;
const SIGH_B: usize = BASE + W * ELL;
const PK0_B: usize = BASE + 2 * W * ELL;
const PK1_B: usize = BASE + 3 * W * ELL;
const PAIR_B: usize = BASE + 4 * W * ELL;
const ACC_B: usize = BASE + 5 * W * ELL;
const M_B: usize = BASE + 6 * W * ELL;
const CT1_B: usize = M_B + ELL;
const CT2_B: usize = CT1_B + NB;
const CT_B: usize = CT1_B + 2 * NB;
const TD_B: usize = CT1_B + 3 * NB;
const ZPAD: usize = TD_B + W;
const WIDTH: usize = ZPAD + 1;

const COL_SRC: usize = 0;
const COL_ACTOR: usize = 1;
const COL_DST: usize = 2;

/// Absorb an input block at the `node8` arity 16 — the ONLY arities that seed every lane are
/// `{7, 11, 16}`, which is why the Lean generator pads every absorb to 16 (an arity-8 absorb drops
/// inputs 4, 5 and 6 outright).
fn absorb16(ins: &[BabyBear]) -> [BabyBear; W] {
    assert!(ins.len() <= CHIP_RATE);
    let mut buf = [BabyBear::new(0); CHIP_RATE];
    buf[..ins.len()].copy_from_slice(ins);
    chip_absorb_all_lanes(CHIP_RATE, &buf)
}

/// A deterministic stand-in for the owner's offline Lamport secret: the preimage for bit `k`,
/// value `b`. In deployment these are the owner's secrets and the prover never sees the unopened
/// half — here the test plays both roles so it can also build the forgeries.
fn secret(k: usize, b: bool) -> [BabyBear; W] {
    core::array::from_fn(|j| {
        BabyBear::new(
            (1 + 7919 * (k as u32) + 104_729 * (j as u32) + if b { 31 } else { 17 })
                % 2_013_265_921,
        )
    })
}

/// Build the honest witness row for a given turn identity.
fn honest_row(src: u32, actor: u32, dst: u32) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::new(0); WIDTH];
    row[COL_SRC] = BabyBear::new(src);
    row[COL_ACTOR] = BabyBear::new(actor);
    row[COL_DST] = BabyBear::new(dst);
    // `zpad` stays 0 — the gate pins it, and every absorb's tail is that column.

    // The TURN DIGEST: `permOut(src, actor, dst, 0…)`. THIS is the weld — actor and dst are
    // arguments of the hash whose bits the signature opens.
    let td = absorb16(&[row[COL_SRC], row[COL_ACTOR], row[COL_DST]]);
    for (q, v) in td.iter().enumerate() {
        row[TD_B + q] = *v;
    }

    // The signed message: the 31-bit decomposition of each signed digest felt, plus the in-AIR
    // BabyBear canonicality products.
    let mut bits = vec![false; ELL];
    for q in 0..NB {
        let v = td[q].as_u32();
        for i in 0..BLOCK_BITS {
            let b = (v >> i) & 1 == 1;
            bits[BLOCK_BITS * q + i] = b;
            row[M_B + BLOCK_BITS * q + i] = BabyBear::new(u32::from(b));
        }
        let bit = |i: usize| u32::from(bits[BLOCK_BITS * q + i]);
        let t1 = bit(30) * bit(29);
        let t2 = bit(28) * bit(27);
        row[CT1_B + q] = BabyBear::new(t1);
        row[CT2_B + q] = BabyBear::new(t2);
        row[CT_B + q] = BabyBear::new(t1 * t2);
    }

    // The Lamport public key, the revealed signature, and its hash.
    let mut pair = vec![[BabyBear::new(0); W]; ELL];
    for k in 0..ELL {
        let sk0 = secret(k, false);
        let sk1 = secret(k, true);
        let pk0 = absorb16(&sk0);
        let pk1 = absorb16(&sk1);
        let sig = if bits[k] { sk1 } else { sk0 };
        let sigh = absorb16(&sig);
        for j in 0..W {
            row[PK0_B + W * k + j] = pk0[j];
            row[PK1_B + W * k + j] = pk1[j];
            row[SIG_B + W * k + j] = sig[j];
            row[SIGH_B + W * k + j] = sigh[j];
        }
        let mut both = [BabyBear::new(0); CHIP_RATE];
        both[..W].copy_from_slice(&pk0);
        both[W..].copy_from_slice(&pk1);
        pair[k] = chip_absorb_all_lanes(CHIP_RATE, &both);
        for j in 0..W {
            row[PAIR_B + W * k + j] = pair[k][j];
        }
    }

    // The authority-root fold: acc[1] = H(pair[0] ‖ pair[1]); acc[k] = H(acc[k-1] ‖ pair[k]).
    let mut acc = vec![[BabyBear::new(0); W]; ELL];
    for k in 1..ELL {
        let left = if k == 1 { pair[0] } else { acc[k - 1] };
        let mut both = [BabyBear::new(0); CHIP_RATE];
        both[..W].copy_from_slice(&left);
        both[W..].copy_from_slice(&pair[k]);
        acc[k] = chip_absorb_all_lanes(CHIP_RATE, &both);
        for j in 0..W {
            row[ACC_B + W * k + j] = acc[k][j];
        }
    }
    row
}

/// The published authority root: the folded public key, which the light client anchors from the
/// owner's committed key. Without this pin the prover would choose the public key and the verify
/// would be a tautology.
fn authority_root(row: &[BabyBear]) -> Vec<BabyBear> {
    (0..W).map(|j| row[ACC_B + W * (ELL - 1) + j]).collect()
}

/// Four identical rows: the gates ride the non-last domain and the PI pins ride the first row, so
/// row 0 carries everything; the lookups are row-agnostic, so every row must carry valid absorbs.
fn trace_of(row: Vec<BabyBear>) -> Vec<Vec<BabyBear>> {
    vec![row.clone(), row.clone(), row.clone(), row]
}

fn probe_desc() -> EffectVmDescriptor2 {
    let d = parse_vm_descriptor2(PROBE_NB1).expect("the Lean-emitted auth descriptor parses");
    assert_eq!(
        d.trace_width, WIDTH,
        "the Rust witness layout must mirror the Lean generator's column plan"
    );
    assert_eq!(d.public_input_count, W, "the 8 authority-root PI slots");
    d
}

#[test]
fn turn_auth_in_air_control_honest_turn_proves() {
    let desc = probe_desc();
    let row = honest_row(11, 22, 33);
    let pis = authority_root(&row);
    must_accept("the honest, correctly-signed turn", || {
        prove_vm_descriptor2(
            &desc,
            &trace_of(row),
            &pis,
            &MemBoundaryWitness::default(),
            &[],
        )
    });
    eprintln!(
        "CONTROL GREEN: an honestly-signed turn PROVES against the Lean-authored in-AIR \
         authorization gadget ({} columns, {} signed bits).",
        WIDTH, ELL
    );
}

#[test]
fn turn_auth_in_air_wrong_key_refused() {
    let desc = probe_desc();
    let honest = honest_row(11, 22, 33);
    let pis = authority_root(&honest);

    // A prover who does NOT hold the owner's secret: one felt of the revealed preimage is wrong.
    // Everything else — the public key, the authority root, the message, the turn — is untouched.
    let mut forged = honest.clone();
    forged[SIG_B] = forged[SIG_B] + BabyBear::new(1);

    let r = must_refuse_or_unsat_panic("a turn signed with the wrong key", || {
        prove_vm_descriptor2(
            &desc,
            &trace_of(forged),
            &pis,
            &MemBoundaryWitness::default(),
            &[],
        )
    });
    eprintln!("WRONG-KEY REFUSED BY THE AIR: {}", r.reason());
}

#[test]
fn turn_auth_in_air_unsigned_refused() {
    let desc = probe_desc();
    let honest = honest_row(11, 22, 33);
    let pis = authority_root(&honest);

    // An UNSIGNED turn: no signature at all. The whole revealed-preimage block is zero, which is
    // also exactly what an un-updated producer would leave behind — and what the prover's
    // zero-extension of short rows would manufacture. It must not pass.
    let mut unsigned = honest.clone();
    for k in 0..ELL {
        for j in 0..W {
            unsigned[SIG_B + W * k + j] = BabyBear::new(0);
        }
    }

    let r = must_refuse_or_unsat_panic("an UNSIGNED turn (zeroed signature block)", || {
        prove_vm_descriptor2(
            &desc,
            &trace_of(unsigned),
            &pis,
            &MemBoundaryWitness::default(),
            &[],
        )
    });
    eprintln!("UNSIGNED REFUSED BY THE AIR: {}", r.reason());
}

#[test]
fn turn_auth_in_air_moved_dst_refused() {
    let desc = probe_desc();
    let honest = honest_row(11, 22, 33);
    let pis = authority_root(&honest);

    // ⚑ THE FREE-WELD FORGERY. `dst` is the column `transferCapOpenTB` publishes to PI 48 and that
    // no other constraint mentions. Here it is an argument of the turn-digest hash whose bits the
    // signature opens, so moving it — with a genuine signature for the ORIGINAL turn still in the
    // trace — must fail.
    let mut moved = honest.clone();
    moved[COL_DST] = moved[COL_DST] + BabyBear::new(1);

    let r = must_refuse_or_unsat_panic("a turn whose dst was moved after signing", || {
        prove_vm_descriptor2(
            &desc,
            &trace_of(moved),
            &pis,
            &MemBoundaryWitness::default(),
            &[],
        )
    });
    eprintln!("MOVED-DST REFUSED BY THE AIR: {}", r.reason());
}

#[test]
fn turn_auth_in_air_moved_actor_refused() {
    let desc = probe_desc();
    let honest = honest_row(11, 22, 33);
    let pis = authority_root(&honest);

    // The sibling free weld: `actor` (PI 47), likewise mentioned by exactly one constraint today.
    let mut moved = honest.clone();
    moved[COL_ACTOR] = moved[COL_ACTOR] + BabyBear::new(1);

    let r = must_refuse_or_unsat_panic("a turn whose actor was moved after signing", || {
        prove_vm_descriptor2(
            &desc,
            &trace_of(moved),
            &pis,
            &MemBoundaryWitness::default(),
            &[],
        )
    });
    eprintln!("MOVED-ACTOR REFUSED BY THE AIR: {}", r.reason());
}
