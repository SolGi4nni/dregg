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
/// The DEPLOYED instance (248 signed bits — every digest felt signed).
const PROBE_NB8: &str = include_str!("turn-auth-lamport-probe-nb8.json");

// ---- the column plan, mirroring `TurnAuthLamportEmit`'s generators exactly ----
const W: usize = 8; // felts per digest group (the deployed `CAP_W`)
const BASE: usize = 3; // the probe base: cols 0,1,2 = src, actor, dst
const BLOCK_BITS: usize = 31;
const CHIP_RATE: usize = 16;

const COL_SRC: usize = 0;
const COL_ACTOR: usize = 1;
const COL_DST: usize = 2;

/// The column plan at block count `nb`. `nb = 8` is the DEPLOYED instance: one 31-bit block per
/// felt of the chip's 8-felt squeeze, so every digest felt is signed and the signed message
/// determines the turn digest.
#[derive(Clone, Copy)]
struct Layout {
    nb: usize,
    ell: usize,
    sig_b: usize,
    sigh_b: usize,
    pk0_b: usize,
    pk1_b: usize,
    pair_b: usize,
    acc_b: usize,
    m_b: usize,
    ct1_b: usize,
    ct2_b: usize,
    ct_b: usize,
    td_b: usize,
    width: usize,
}

impl Layout {
    const fn new(nb: usize) -> Self {
        let ell = BLOCK_BITS * nb;
        let m_b = BASE + 6 * W * ell;
        let ct1_b = m_b + ell;
        let td_b = ct1_b + 3 * nb;
        Self {
            nb,
            ell,
            sig_b: BASE,
            sigh_b: BASE + W * ell,
            pk0_b: BASE + 2 * W * ell,
            pk1_b: BASE + 3 * W * ell,
            pair_b: BASE + 4 * W * ell,
            acc_b: BASE + 5 * W * ell,
            m_b,
            ct1_b,
            ct2_b: ct1_b + nb,
            ct_b: ct1_b + 2 * nb,
            td_b,
            width: td_b + W + 1, // + the zero-pinned arity-16 pad column
        }
    }
}

const L1: Layout = Layout::new(1);
/// ⚑ The DEPLOYED shape: 248 signed bits, every one of the chip's 8 digest felts covered.
const L8: Layout = Layout::new(8);

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
fn honest_row(l: Layout, src: u32, actor: u32, dst: u32) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::new(0); l.width];
    row[COL_SRC] = BabyBear::new(src);
    row[COL_ACTOR] = BabyBear::new(actor);
    row[COL_DST] = BabyBear::new(dst);
    // `zpad` stays 0 — the gate pins it, and every absorb's tail is that column.

    // The TURN DIGEST: `permOut(src, actor, dst, 0…)`. THIS is the weld — actor and dst are
    // arguments of the hash whose bits the signature opens.
    let td = absorb16(&[row[COL_SRC], row[COL_ACTOR], row[COL_DST]]);
    for (q, v) in td.iter().enumerate() {
        row[l.td_b + q] = *v;
    }

    // The signed message: the 31-bit decomposition of each signed digest felt, plus the in-AIR
    // BabyBear canonicality products.
    let mut bits = vec![false; l.ell];
    for q in 0..l.nb {
        let v = td[q].as_u32();
        for i in 0..BLOCK_BITS {
            let b = (v >> i) & 1 == 1;
            bits[BLOCK_BITS * q + i] = b;
            row[l.m_b + BLOCK_BITS * q + i] = BabyBear::new(u32::from(b));
        }
        let bit = |i: usize| u32::from(bits[BLOCK_BITS * q + i]);
        let t1 = bit(30) * bit(29);
        let t2 = bit(28) * bit(27);
        row[l.ct1_b + q] = BabyBear::new(t1);
        row[l.ct2_b + q] = BabyBear::new(t2);
        row[l.ct_b + q] = BabyBear::new(t1 * t2);
    }

    // The Lamport public key, the revealed signature, and its hash.
    let mut pair = vec![[BabyBear::new(0); W]; l.ell];
    for k in 0..l.ell {
        let sk0 = secret(k, false);
        let sk1 = secret(k, true);
        let pk0 = absorb16(&sk0);
        let pk1 = absorb16(&sk1);
        let sig = if bits[k] { sk1 } else { sk0 };
        let sigh = absorb16(&sig);
        for j in 0..W {
            row[l.pk0_b + W * k + j] = pk0[j];
            row[l.pk1_b + W * k + j] = pk1[j];
            row[l.sig_b + W * k + j] = sig[j];
            row[l.sigh_b + W * k + j] = sigh[j];
        }
        let mut both = [BabyBear::new(0); CHIP_RATE];
        both[..W].copy_from_slice(&pk0);
        both[W..].copy_from_slice(&pk1);
        pair[k] = chip_absorb_all_lanes(CHIP_RATE, &both);
        for j in 0..W {
            row[l.pair_b + W * k + j] = pair[k][j];
        }
    }

    // The authority-root fold: acc[1] = H(pair[0] ‖ pair[1]); acc[k] = H(acc[k-1] ‖ pair[k]).
    let mut acc = vec![[BabyBear::new(0); W]; l.ell];
    for k in 1..l.ell {
        let left = if k == 1 { pair[0] } else { acc[k - 1] };
        let mut both = [BabyBear::new(0); CHIP_RATE];
        both[..W].copy_from_slice(&left);
        both[W..].copy_from_slice(&pair[k]);
        acc[k] = chip_absorb_all_lanes(CHIP_RATE, &both);
        for j in 0..W {
            row[l.acc_b + W * k + j] = acc[k][j];
        }
    }
    row
}

/// The published authority root: the folded public key, which the light client anchors from the
/// owner's committed key. Without this pin the prover would choose the public key and the verify
/// would be a tautology.
fn authority_root(l: Layout, row: &[BabyBear]) -> Vec<BabyBear> {
    (0..W).map(|j| row[l.acc_b + W * (l.ell - 1) + j]).collect()
}

/// Four identical rows: the gates ride the non-last domain and the PI pins ride the first row, so
/// row 0 carries everything; the lookups are row-agnostic, so every row must carry valid absorbs.
fn trace_of(row: Vec<BabyBear>) -> Vec<Vec<BabyBear>> {
    vec![row.clone(), row.clone(), row.clone(), row]
}

fn probe_desc(l: Layout) -> EffectVmDescriptor2 {
    let json = if l.nb == 1 { PROBE_NB1 } else { PROBE_NB8 };
    let d = parse_vm_descriptor2(json).expect("the Lean-emitted auth descriptor parses");
    assert_eq!(
        d.trace_width, l.width,
        "the Rust witness layout must mirror the Lean generator's column plan"
    );
    assert_eq!(d.public_input_count, W, "the 8 authority-root PI slots");
    d
}

/// The four measurements at one block count.
fn run_teeth(l: Layout, tag: &str) {
    let desc = probe_desc(l);
    let honest = honest_row(l, 11, 22, 33);
    let pis = authority_root(l, &honest);

    // (1) CONTROL — the honest, correctly-signed turn PROVES.
    must_accept(
        &format!("[{tag}] the honest, correctly-signed turn"),
        || {
            prove_vm_descriptor2(
                &desc,
                &trace_of(honest.clone()),
                &pis,
                &MemBoundaryWitness::default(),
                &[],
            )
        },
    );
    eprintln!(
        "[{tag}] CONTROL GREEN: an honestly-signed turn PROVES against the Lean-authored in-AIR \
         authorization gadget ({} columns, {} signed bits).",
        l.width, l.ell
    );

    // Each negative differs from the control ONLY in witness cells: same descriptor, same public
    // inputs, same trace shape. A refusal therefore cannot be a shape check.
    let cases: Vec<(&str, Box<dyn Fn(&mut Vec<BabyBear>)>)> = vec![
        // (2) WRONG KEY — a prover who does not hold the owner's secret: one felt of the revealed
        // preimage is wrong. Public key, authority root, message and turn are untouched.
        (
            "a turn signed with the WRONG KEY",
            Box::new(move |r: &mut Vec<BabyBear>| r[l.sig_b] = r[l.sig_b] + BabyBear::new(1)),
        ),
        // (3) UNSIGNED — no signature at all. This is also exactly what an un-updated producer
        // leaves behind, and what the prover's zero-extension of short rows would manufacture.
        (
            "an UNSIGNED turn (zeroed signature block)",
            Box::new(move |r: &mut Vec<BabyBear>| {
                for k in 0..l.ell {
                    for j in 0..W {
                        r[l.sig_b + W * k + j] = BabyBear::new(0);
                    }
                }
            }),
        ),
        // (4) ⚑ THE FREE-WELD FORGERY. `dst` is the column `transferCapOpenTB` publishes to PI 48
        // and that no other constraint mentions today. Here it is an argument of the turn-digest
        // absorb whose output the signed bits recompose, so moving it with a genuine signature for
        // the ORIGINAL turn still in the trace must fail.
        (
            "a turn whose dst was MOVED after signing",
            Box::new(|r: &mut Vec<BabyBear>| r[COL_DST] = r[COL_DST] + BabyBear::new(1)),
        ),
        // (5) the sibling free weld: `actor` (PI 47), likewise mentioned by exactly one constraint.
        (
            "a turn whose actor was MOVED after signing",
            Box::new(|r: &mut Vec<BabyBear>| r[COL_ACTOR] = r[COL_ACTOR] + BabyBear::new(1)),
        ),
    ];

    for (what, bend) in cases {
        let mut forged = honest.clone();
        bend(&mut forged);
        assert_ne!(
            forged, honest,
            "[{tag}] {what}: the bend must change the witness"
        );
        let r = must_refuse_or_unsat_panic(&format!("[{tag}] {what}"), || {
            prove_vm_descriptor2(
                &desc,
                &trace_of(forged),
                &pis,
                &MemBoundaryWitness::default(),
                &[],
            )
        });
        eprintln!("[{tag}] REFUSED BY THE AIR — {what}: {}", r.reason());
    }
}

/// The fast instance: 31 signed bits. Same generator, same per-bit machinery.
#[test]
fn turn_auth_in_air_teeth_nb1() {
    run_teeth(L1, "nb=1");
}

/// ⚑ THE DEPLOYED INSTANCE: 248 signed bits, every one of the chip's 8 digest felts signed, so the
/// signed message DETERMINES the turn digest and the weld does not leak.
#[test]
fn turn_auth_in_air_teeth_nb8_deployed() {
    run_teeth(L8, "nb=8 DEPLOYED");
}
