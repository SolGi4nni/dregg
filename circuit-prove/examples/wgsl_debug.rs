//! `wgsl_debug` — the RADV compute-pipeline crash bisector. A DEBUG TOOL, not a gate.
//!
//! These two subcommands used to be `#[test] fn dump_hash_wgsl` and `#[test] fn
//! compile_wgsl_from_env` inside `gpu_backend.rs`'s test module. They were honestly labelled
//! DIAGNOSTIC in a comment — but being `#[test]`s they RAN on every CI run and reported `ok`
//! while asserting nothing: `dump_hash_wgsl` had zero assertions and wrote `/tmp/hash.wgsl`
//! unconditionally on every runner; `compile_wgsl_from_env` early-returned because `WGSL_FILE` is
//! unset in CI, so it never executed its body at all. A test that cannot fail is not a test — it
//! inflates the count and buys nothing. As an example binary the tool is unchanged in power and
//! runs exactly when a human asks for it.
//!
//! ## Why it exists
//!
//! Mesa's RADV driver has SIGSEGV'd inside `create_compute_pipeline` on the generated hash-engine
//! shader. Rebuilding the Rust crate to tweak one WGSL line is far too slow to bisect with, so:
//! dump the real generated source, edit the FILE, and re-compile just that file until the crash
//! moves. The dumped text is the exact source the prover compiles — not a reconstruction.
//!
//! ## Usage
//!
//! ```text
//! # 1. dump the generated hash-engine WGSL (default: ./hash.wgsl — an explicit path, NOT /tmp)
//! cargo run -p dregg-circuit-prove --example wgsl_debug -- dump [PATH]
//!
//! # 2. edit PATH, then re-compile it on the real adapter until the SIGSEGV moves
//! cargo run -p dregg-circuit-prove --example wgsl_debug -- compile PATH [ENTRY]   # ENTRY default: leaf_main
//! ```
//!
//! A SIGSEGV *is* the expected reproduction; `OK compiled` means the shader survived.

#[cfg(target_arch = "wasm32")]
fn main() {
    eprintln!("wgsl_debug is native-only (the shared blocking GPU init does not exist on wasm32).");
    std::process::exit(2);
}

#[cfg(not(target_arch = "wasm32"))]
fn main() -> std::process::ExitCode {
    use dregg_circuit_prove::gpu_backend::wgsl_debug;

    let args: Vec<String> = std::env::args().skip(1).collect();
    let usage = "usage:\n  wgsl_debug dump [PATH]            # write the generated hash-engine WGSL (default ./hash.wgsl)\n  wgsl_debug compile FILE [ENTRY]   # create a compute pipeline for ENTRY (default leaf_main)";

    match args.first().map(String::as_str) {
        Some("dump") => {
            // An EXPLICIT default in the cwd. The old `#[test]` wrote `/tmp/hash.wgsl` on every CI
            // run, unasked; a tool a human invokes writes where the human is standing.
            let path = args.get(1).cloned().unwrap_or_else(|| "hash.wgsl".into());
            match std::fs::write(&path, wgsl_debug::hash_shader_source_at_deployed_wg()) {
                Ok(()) => {
                    eprintln!("wrote {path}");
                    std::process::ExitCode::SUCCESS
                }
                Err(e) => {
                    eprintln!("error: could not write {path}: {e}");
                    std::process::ExitCode::FAILURE
                }
            }
        }
        Some("compile") => {
            let Some(file) = args.get(1) else {
                eprintln!("error: `compile` needs a WGSL FILE\n\n{usage}");
                return std::process::ExitCode::FAILURE;
            };
            let entry = args.get(2).cloned().unwrap_or_else(|| "leaf_main".into());
            let src = match std::fs::read_to_string(file) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("error: could not read {file}: {e}");
                    return std::process::ExitCode::FAILURE;
                }
            };
            eprintln!("compiling {file} entry={entry} ...");
            match wgsl_debug::compile_probe(&src, &entry) {
                Ok(layout) => {
                    eprintln!("OK compiled entry={entry}: {layout}");
                    std::process::ExitCode::SUCCESS
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    std::process::ExitCode::FAILURE
                }
            }
        }
        _ => {
            eprintln!("{usage}");
            std::process::ExitCode::FAILURE
        }
    }
}
