//! The runnable entry point: compose all five crates into one playthrough.
//!
//! `cargo run -p interactive-fiction-demo`

fn main() {
    match interactive_fiction_demo::run() {
        Ok(summary) => {
            eprintln!(
                "\n[ok] {} branches crowd-certified · {}-turn un-retconnable chain · {} attested DM turns · injection-refused={} · federation-approved={}",
                summary.rounds,
                summary.chain_len,
                summary.dm_receipts,
                summary.injection_refused,
                summary.federation_approved
            );
        }
        Err(e) => {
            eprintln!("[fail] {e}");
            std::process::exit(1);
        }
    }
}
