//! `dregg-uverify` — lint a constructed turn forest before you spend gas.
//!
//! Reads a JSON-serialized `dregg_turn::CallForest` (the artifact the SDK
//! builders emit) from a file argument or stdin, runs the static assurance
//! checks, and reports a verdict. Exit code is `0` on Pass, `1` on any
//! finding (so it composes into CI / pre-submit hooks).
//!
//! ```text
//!   dregg-uverify [FILE]            analyze FILE (or stdin if omitted)
//!   dregg-uverify --ring [FILE]     also run the ring-balance check
//!   dregg-uverify --json [FILE]     emit the Assurance as JSON
//!   dregg-uverify --boundary        print the static/dynamic boundary and exit
//! ```

use std::io::Read;
use std::process::ExitCode;

use dregg_turn::CallForest;
use dregg_userspace_verify::{analyze, boundary};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();

    if args.iter().any(|a| a == "--boundary") {
        print!("{}", boundary::report());
        return ExitCode::SUCCESS;
    }
    if args.iter().any(|a| a == "-h" || a == "--help") {
        eprintln!(
            "dregg-uverify — lint a constructed turn forest before you spend gas\n\n\
             USAGE:\n  \
               dregg-uverify [FILE]            analyze FILE (or stdin)\n  \
               dregg-uverify --ring [FILE]     also run the ring-balance check\n  \
               dregg-uverify --json [FILE]     emit the Assurance as JSON\n  \
               dregg-uverify --boundary        print the static/dynamic boundary\n\n\
             INPUT: a JSON-serialized dregg_turn::CallForest.\n\
             EXIT: 0 = Pass, 1 = findings, 2 = input error."
        );
        return ExitCode::SUCCESS;
    }

    let as_ring = args.iter().any(|a| a == "--ring");
    let as_json = args.iter().any(|a| a == "--json");
    let file = args.iter().find(|a| !a.starts_with("--"));

    let input = match read_input(file.map(String::as_str)) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error reading input: {e}");
            return ExitCode::from(2);
        }
    };

    let forest: CallForest = match serde_json::from_str(&input) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("error: input is not a JSON CallForest: {e}");
            return ExitCode::from(2);
        }
    };

    let assurance = analyze(&forest, as_ring);

    if as_json {
        match serde_json::to_string_pretty(&assurance) {
            Ok(j) => println!("{j}"),
            Err(e) => {
                eprintln!("error serializing verdict: {e}");
                return ExitCode::from(2);
            }
        }
    } else {
        print_human(&assurance);
    }

    if assurance.pass() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

fn read_input(file: Option<&str>) -> std::io::Result<String> {
    match file {
        Some(path) => std::fs::read_to_string(path),
        None => {
            let mut s = String::new();
            std::io::stdin().read_to_string(&mut s)?;
            Ok(s)
        }
    }
}

fn print_human(a: &dregg_userspace_verify::Assurance) {
    let line = |name: &str, v: &dregg_userspace_verify::Verdict| {
        if v.is_pass() {
            println!("  [PASS] {name}");
        } else {
            println!("  [FAIL] {name}");
            for f in v.findings() {
                println!("         @ {}  —  {}", f.locus, f.message);
            }
        }
    };
    println!("dregg-uverify assurance:");
    line("B  conservation     ", &a.conservation);
    line("A  no-amplification ", &a.no_amplification);
    line("   well-formedness  ", &a.wellformed);
    line("   ring balance     ", &a.ring_balance);
    println!();
    if a.pass() {
        println!(
            "VERDICT: PASS (static). Well-shaped and self-conserving. NOTE: a Pass is \
             necessary, not sufficient — the executor still checks holding, balances, \
             credentials, freshness. Run with --boundary for the full line."
        );
    } else {
        println!(
            "VERDICT: FAIL — fix the findings above before submitting (you'd pay gas to be rejected)."
        );
    }
}
