//! TEMP benchmark (run with `--ignored --nocapture`); not committed.
use dregg_cell::{Cell, Ledger, LedgerDelta};
use std::collections::HashMap;
use std::time::Instant;

fn pk(n: u64) -> [u8; 32] {
    let mut a = [0u8; 32];
    a[..8].copy_from_slice(&n.to_le_bytes());
    a
}
fn tok(n: u64) -> [u8; 32] {
    let mut a = [0u8; 32];
    a[24..].copy_from_slice(&n.to_le_bytes());
    a
}

#[test]
#[ignore = "BENCH with NO assertion: builds 2k- and 20k-cell ledgers and prints the whole-map-clone \
            vs apply_delta ratio. It cannot go red, so un-ignoring it would cost CI time and add zero \
            coverage. The apply_delta correctness teeth live in cell/src/ledger.rs."]
fn bench_apply_delta_single_transfer() {
    for &n in &[2000usize, 20000usize] {
        let mut ledger = Ledger::new();
        let mut ids = Vec::new();
        for i in 0..n as u64 {
            let id = ledger
                .insert_cell(Cell::with_balance(pk(i), tok(i), 1_000_000))
                .unwrap();
            ids.push(id);
        }

        // Cost the OLD code paid on EVERY apply_delta: deep-clone the whole map.
        let mut raw: HashMap<_, Cell> = HashMap::new();
        for id in &ids {
            raw.insert(*id, ledger.get(id).cloned().unwrap());
        }
        let t = Instant::now();
        let iters = 200;
        for _ in 0..iters {
            let c = raw.clone();
            std::hint::black_box(&c);
        }
        let clone_us = t.elapsed().as_secs_f64() * 1e6 / iters as f64;

        // NEW apply_delta: a single 1-computron transfer between two cells.
        let (a, b) = (ids[0], ids[1]);
        let t = Instant::now();
        let iters = 200;
        for _ in 0..iters {
            let mut d = LedgerDelta::new();
            d.computron_transfers.push((a, b, 1));
            ledger.apply_delta(&d).unwrap();
            // move it back to keep balances valid across iters
            let mut d2 = LedgerDelta::new();
            d2.computron_transfers.push((b, a, 1));
            ledger.apply_delta(&d2).unwrap();
        }
        let apply_us = t.elapsed().as_secs_f64() * 1e6 / (iters as f64 * 2.0);

        eprintln!(
            "N={n:>6}  old-per-apply whole-map clone = {clone_us:>9.2} us   |   new apply_delta(single transfer) = {apply_us:>7.3} us   => ~{:.0}x",
            clone_us / apply_us.max(1e-9)
        );
    }
}
