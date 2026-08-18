//! # `air_interp_census` — the interpreted-AIR measurement harness
//!
//! Three instruments for `notes/air-interpreter.md` (zkml-research), all COUNT-arm or
//! byte-identity — no wall clock is reported here:
//!
//! * **§1 `bytes_sweep`** — proof-byte fingerprints for the IR-v2 transfer workload at
//!   `b = 3..8` (pow=0) plus the deployed `(6,19,pow16)` point, proved twice at `b=6` to
//!   establish determinism. This is the byte-identity BASELINE for the compiled-evaluator
//!   change: a compiled evaluator is a pure re-arrangement of how the same polynomial is
//!   evaluated, so the bytes must not move (the LDE-layout precedent).
//! * **§2 `invocation_census`** — how many times `Ir2Air::eval` actually runs per prove, per
//!   instance, per builder TYPE (symbolic / prover folder / verifier folder). Requires
//!   `--features eval-count`; refuses loudly (rather than printing zeros) without it.
//! * **§3 `static_node_census`** — the size of the boxed expression forest each of those
//!   invocations re-walks: nodes / adds / muls per instance, per constraint kind. Pure
//!   function of the deployed descriptors; total interpreted node-visits per prove is
//!   (§2 invocations) × (§3 nodes), exactly, because every invocation walks the full list.
//!
//! Run:
//! ```text
//! cargo test -p dregg-circuit --release --test air_interp_census -- --ignored --nocapture --test-threads=1
//! cargo test -p dregg-circuit --release --features eval-count --test air_interp_census -- --ignored --nocapture --test-threads=1
//! ```

use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::Field;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
    ir2_airs_and_common_for_config, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use dregg_circuit::table_air::TableExpr;

// ── the uninstrumented (deployed-shape) config, generic in the FRI knobs — the rig's
//    `clock_config` types, restated because integration tests are separate crates. ──
type Pack = <P3BabyBear as Field>::Packing;
type Ef = BinomialExtensionField<P3BabyBear, 4>;
type Perm = Poseidon2BabyBear<16>;
type PHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type PCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type PValMmcs = MerkleTreeMmcs<Pack, Pack, PHash, PCompress, 2, 8>;
type PChallengeMmcs = ExtensionMmcs<P3BabyBear, Ef, PValMmcs>;
type PPcs = TwoAdicFriPcs<P3BabyBear, Radix2DitParallel<P3BabyBear>, PValMmcs, PChallengeMmcs>;
type PChallenger = DuplexChallenger<P3BabyBear, Perm, 16, 8>;
type PlainConfig = StarkConfig<PPcs, Ef, PChallenger>;

fn plain_config(log_blowup: usize, num_queries: usize, pow_bits: usize) -> PlainConfig {
    let perm = default_babybear_poseidon2_16();
    let val_mmcs = PValMmcs::new(PHash::new(perm.clone()), PCompress::new(perm.clone()), 0);
    let fri = FriParameters {
        log_blowup,
        log_final_poly_len: 0,
        max_log_arity: 3,
        num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: pow_bits,
        mmcs: PChallengeMmcs::new(val_mmcs.clone()),
    };
    StarkConfig::new(
        TwoAdicFriPcs::new(Radix2DitParallel::default(), val_mmcs, fri),
        PChallenger::new(perm),
    )
}

struct Workload {
    desc: EffectVmDescriptor2,
    base_trace: Vec<Vec<BabyBear>>,
    pis: Vec<BabyBear>,
}

fn workload() -> Workload {
    let state = CellState::new(100_000, 0);
    let effs = vec![Effect::Transfer {
        amount: 50,
        direction: 1,
    }];
    let (base_trace, pis) = generate_effect_vm_trace(&state, &effs);
    let json = descriptor2_for_key("transferVmDescriptor2").expect("v2 transfer descriptor");
    let desc = parse_vm_descriptor2(json).expect("descriptor parses");
    let pis = pis[..desc.public_input_count].to_vec();
    Workload {
        desc,
        base_trace,
        pis,
    }
}

fn prove(w: &Workload, config: &PlainConfig) -> p3_batch_stark::BatchProof<PlainConfig> {
    prove_vm_descriptor2_for_config(
        &w.desc,
        &w.base_trace,
        &w.pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .expect("IR-v2 transfer proves")
}

fn fingerprint(proof: &p3_batch_stark::BatchProof<PlainConfig>) -> (usize, String, usize, String) {
    let json = serde_json::to_vec(proof).expect("serde_json");
    let rmp = rmp_serde::to_vec(proof).expect("rmp");
    (
        json.len(),
        blake3::hash(&json).to_hex().to_string(),
        rmp.len(),
        blake3::hash(&rmp).to_hex().to_string(),
    )
}

/// **§1** — byte fingerprints across the blowup sweep + the deployed point.
#[test]
#[ignore = "measurement harness — run explicitly with --ignored --nocapture"]
fn bytes_sweep() {
    let w = workload();
    println!("\n== §1 proof-byte fingerprints (transferVmDescriptor2, 1 Transfer) ==");
    println!(
        "{:>14}  {:>9}  {:<20}  {:>9}  {:<20}",
        "point", "json B", "blake3(json)[..20]", "rmp B", "blake3(rmp)[..20]"
    );
    for b in 3..=8usize {
        let c = plain_config(b, 19, 0);
        let (jl, jh, rl, rh) = fingerprint(&prove(&w, &c));
        println!(
            "{:>14}  {:>9}  {:<20}  {:>9}  {:<20}",
            format!("(lb {b}, q 19, p0)"),
            jl,
            &jh[..20],
            rl,
            &rh[..20]
        );
    }
    // Determinism: same point proved twice must agree byte-for-byte.
    let c6 = plain_config(6, 19, 0);
    let f1 = fingerprint(&prove(&w, &c6));
    let f2 = fingerprint(&prove(&w, &c6));
    assert_eq!(
        f1, f2,
        "the prover is not byte-deterministic at (6,19,p0) — byte-identity comparisons are void"
    );
    println!(
        "  determinism at (lb 6, q 19, p0): two proves agree ({} / {})",
        &f1.1[..20],
        &f1.3[..20]
    );
    // The deployed point (with grind — deterministic given the transcript).
    let cd = plain_config(6, 19, 16);
    let (jl, jh, rl, rh) = fingerprint(&prove(&w, &cd));
    println!(
        "{:>14}  {:>9}  {:<20}  {:>9}  {:<20}",
        "(6,19,pow16)",
        jl,
        &jh[..20],
        rl,
        &rh[..20]
    );
}

/// **§2** — `Ir2Air::eval` invocations per prove, per instance, per builder type.
#[test]
#[ignore = "measurement harness — needs --features eval-count"]
fn invocation_census() {
    #[cfg(not(feature = "eval-count"))]
    panic!(
        "invocation_census needs `--features eval-count` — without it the census is compiled out and every count would read as a false zero"
    );

    #[cfg(feature = "eval-count")]
    {
        let w = workload();
        let c = plain_config(6, 19, 0);
        dregg_circuit::eval_census::take(); // clear anything from other tests
        let proof = prove(&w, &c);
        let census = dregg_circuit::eval_census::take();
        println!(
            "\n== §2 Air::eval invocation census — one prove at (lb 6, q 19, pow 0), including its unconditional self-verify =="
        );
        let mut total = 0u64;
        for ((inst, builder), n) in &census {
            println!("  {n:>7}  {inst:<28}  {builder}");
            total += n;
        }
        println!("  {total:>7}  TOTAL");
        assert!(total > 0, "a prove ran but recorded no eval invocations");
        // Geometry cross-check: heights per instance from the proof itself.
        let (airs, _tpis, _common) =
            ir2_airs_and_common_for_config(&w.desc, &proof, &w.pis, &c).expect("airs rebuild");
        println!(
            "\n  instances: {} — degree_bits {:?}",
            airs.len(),
            proof.degree_bits
        );
    }
}

// ── §3: static node census over the boxed expression forest ──

#[derive(Default, Clone, Copy)]
struct N {
    nodes: u64,
    adds: u64,
    muls: u64,
    depth: u64,
}
impl N {
    fn merge2(a: N, b: N, is_add: bool) -> N {
        N {
            nodes: a.nodes + b.nodes + 1,
            adds: a.adds + b.adds + u64::from(is_add),
            muls: a.muls + b.muls + u64::from(!is_add),
            depth: 1 + a.depth.max(b.depth),
        }
    }
    fn leaf() -> N {
        N {
            nodes: 1,
            adds: 0,
            muls: 0,
            depth: 1,
        }
    }
    fn add(&mut self, o: N) {
        self.nodes += o.nodes;
        self.adds += o.adds;
        self.muls += o.muls;
        self.depth = self.depth.max(o.depth);
    }
}

fn n_lean(e: &LeanExpr) -> N {
    match e {
        LeanExpr::Var(_) | LeanExpr::Const(_) => N::leaf(),
        LeanExpr::Add(a, b) => N::merge2(n_lean(a), n_lean(b), true),
        LeanExpr::Mul(a, b) => N::merge2(n_lean(a), n_lean(b), false),
    }
}
fn n_window(e: &dregg_circuit::descriptor_ir2::WindowExpr) -> N {
    use dregg_circuit::descriptor_ir2::WindowExpr as W;
    match e {
        W::Loc(_) | W::Nxt(_) | W::Const(_) => N::leaf(),
        W::Add(a, b) => N::merge2(n_window(a), n_window(b), true),
        W::Mul(a, b) => N::merge2(n_window(a), n_window(b), false),
    }
}
fn n_chal(e: &dregg_circuit::descriptor_ir2::ChalExpr) -> N {
    use dregg_circuit::descriptor_ir2::ChalExpr as C;
    match e {
        C::Loc(_) | C::Nxt(_) | C::Const(_) | C::Chal(_) => N::leaf(),
        C::Add(a, b) => N::merge2(n_chal(a), n_chal(b), true),
        C::Mul(a, b) => N::merge2(n_chal(a), n_chal(b), false),
    }
}
fn n_table(e: &TableExpr) -> N {
    match e {
        TableExpr::Loc(_)
        | TableExpr::Nxt(_)
        | TableExpr::Const(_)
        | TableExpr::Shr(_)
        | TableExpr::Prep(_) => N::leaf(),
        TableExpr::Add(a, b) => N::merge2(n_table(a), n_table(b), true),
        TableExpr::Mul(a, b) => N::merge2(n_table(a), n_table(b), false),
    }
}

/// **§3** — the forest each invocation re-walks, by instance and constraint kind.
#[test]
#[ignore = "measurement harness"]
fn static_node_census() {
    let w = workload();
    let c = plain_config(6, 19, 0);
    let proof = prove(&w, &c);
    let (airs, _tpis, _common) =
        ir2_airs_and_common_for_config(&w.desc, &proof, &w.pis, &c).expect("airs rebuild");

    println!("\n== §3 static node census — what ONE Air::eval invocation walks ==");
    println!("  (total interpreted node-visits per prove = these × the §2 invocation counts)\n");

    // Main instance: by constraint kind.
    let mut by_kind: std::collections::BTreeMap<&'static str, (u64, N)> = Default::default();
    let mut bump = |k: &'static str, n: N| {
        let e = by_kind.entry(k).or_insert((0, N::default()));
        e.0 += 1;
        e.1.add(n);
    };
    for k in &w.desc.constraints {
        match k {
            VmConstraint2::Base(VmConstraint::Gate(b)) => bump("base.gate", n_lean(b)),
            VmConstraint2::Base(VmConstraint::Boundary { body, .. }) => {
                bump("base.boundary", n_lean(body))
            }
            VmConstraint2::Base(VmConstraint::Transition { .. }) => {
                bump("base.transition", N::default())
            }
            VmConstraint2::Base(VmConstraint::PiBinding { .. }) => {
                bump("base.pi_binding", N::default())
            }
            VmConstraint2::WindowGate(g) => bump("window_gate", n_window(&g.body)),
            VmConstraint2::ChalGate(g) => bump("chal_gate", n_chal(&g.body)),
            VmConstraint2::Lookup(l) => {
                let mut n = N::default();
                for e in &l.tuple {
                    n.add(n_lean(e));
                }
                bump("lookup.tuple", n);
            }
            VmConstraint2::MemOp(m) => {
                let mut n = N::default();
                for e in [&m.guard, &m.addr, &m.value, &m.prev_value, &m.prev_serial] {
                    n.add(n_lean(e));
                }
                bump("mem_op", n);
            }
            VmConstraint2::MapOp(m) => {
                let mut n = N::default();
                for e in m
                    .root
                    .iter()
                    .chain(m.new_root.iter())
                    .chain([&m.guard, &m.key, &m.value])
                {
                    n.add(n_lean(e));
                }
                bump("map_op", n);
            }
            VmConstraint2::UMemOp(m) => {
                let mut n = N::default();
                for e in [
                    &m.guard,
                    &m.key,
                    &m.present,
                    &m.value,
                    &m.prev_present,
                    &m.prev_value,
                    &m.prev_serial,
                ] {
                    n.add(n_lean(e));
                }
                bump("umem_op", n);
            }
            VmConstraint2::ProofBind(p) => {
                let mut n = n_lean(&p.guard);
                for e in p.vk.iter().chain(p.commit.iter()) {
                    n.add(n_lean(e));
                }
                bump("proof_bind", n);
            }
        }
    }
    println!("  main ({} constraints):", w.desc.constraints.len());
    println!(
        "    {:<16} {:>6} {:>9} {:>8} {:>8} {:>6}",
        "kind", "count", "nodes", "adds", "muls", "depth"
    );
    let mut main_total = N::default();
    for (k, (cnt, n)) in &by_kind {
        println!(
            "    {:<16} {:>6} {:>9} {:>8} {:>8} {:>6}",
            k, cnt, n.nodes, n.adds, n.muls, n.depth
        );
        main_total.add(*n);
    }
    println!(
        "    {:<16} {:>6} {:>9} {:>8} {:>8} {:>6}",
        "TOTAL",
        w.desc.constraints.len(),
        main_total.nodes,
        main_total.adds,
        main_total.muls,
        main_total.depth
    );

    // Table instances.
    println!("\n  tables:");
    println!(
        "    {:<34} {:>7} {:>9} {:>8} {:>8} {:>6}",
        "instance (defs/gates/interactions)", "exprs", "nodes", "adds", "muls", "depth"
    );
    for a in &airs {
        let Some(t) = a.lean_table_air() else {
            continue;
        };
        let mut n = N::default();
        let mut exprs = 0u64;
        for d in &t.defs {
            n.add(n_table(d));
            exprs += 1;
        }
        for g in &t.gates {
            n.add(n_table(&g.body));
            exprs += 1;
        }
        for it in &t.interactions {
            n.add(n_table(&it.mult));
            exprs += 1;
            for e in &it.tuple {
                n.add(n_table(e));
                exprs += 1;
            }
        }
        println!(
            "    {:<34} {:>7} {:>9} {:>8} {:>8} {:>6}",
            format!(
                "{} ({}/{}/{})",
                t.name,
                t.defs.len(),
                t.gates.len(),
                t.interactions.len()
            ),
            exprs,
            n.nodes,
            n.adds,
            n.muls,
            n.depth
        );
    }
}
