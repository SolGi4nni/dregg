use std::time::Instant;
#[test]
fn bench_descriptor_by_name_parse() {
    let names = [
        "dfa-routing-toggle-2state::poseidon2-v1",
        "note-spend-leaf::dregg-note-spending-dsl-v3",
        "dregg-membership-adjacency::poseidon2-v1",
        "dregg-delegate::v2",
        "dregg-accumulator-nonrev-emit-v2",
    ];
    for name in names {
        let _ = dregg_circuit::descriptor_by_name::descriptor_by_name(name);
        let n = 2000u32;
        let t = Instant::now();
        for _ in 0..n {
            std::hint::black_box(dregg_circuit::descriptor_by_name::descriptor_by_name(
                std::hint::black_box(name),
            ));
        }
        let per_us = t.elapsed().as_secs_f64() * 1e6 / n as f64;
        eprintln!("DISPATCH {name}: {per_us:.2} µs/call",);
    }
}
