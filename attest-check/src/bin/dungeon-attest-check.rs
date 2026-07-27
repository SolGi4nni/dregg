//! **`dungeon-attest-check` — check the attestation `/dungeon attestation` handed you.**
//!
//! The Discord panel attaches two files per attested turn: a raw Intel TDX quote (`.bin`) and a
//! JSON sidecar. Before this program the sidecar NAMED four checks and performed none of them,
//! which is a manual to a verifier rather than a verifier. This runs them.
//!
//! It is a program you run, not a bot command you ask, on purpose. A slash command would grade
//! the bot's artifact using the bot; the artifact exists so that is not necessary. Everything
//! here reads bytes you already hold, and it touches the network only if you ask it to.
//!
//! ```text
//! cargo run -p dregg-attest-check --bin dungeon-attest-check -- \
//!     --quote dungeon-attestation-<id>.tdx-quote.bin \
//!     --record dungeon-attestation-<id>.json \
//!     --measurements chutes_measurements.json \
//!     --collateral collateral.json
//! ```
//!
//! `--measurements` should be a copy of the Chutes registry you pinned yourself. The sidecar
//! names where the live one lives; a registry fetched at check time is whatever answered, so this
//! program takes a FILE and reports check 3 as NOT RUN rather than quietly fetching one.
//!
//! `--collateral` is the Intel-signed DCAP `QuoteCollateralV3` for this quote's platform. It is
//! the input to the only check that decides whether the quote is genuine. Built with
//! `--features collateral-fetch`, `--pccs <url>` fetches it instead.
//!
//! Exit status: `0` every check ran and passed. `1` a check FAILED. `2` bad usage or unreadable
//! input. `3` nothing failed but something did not run, so a script cannot read an offline run as
//! a full pass from the exit code alone.

use std::process::ExitCode;

use dregg_attest_check::{verify_record, NarrationAttestationRecord, NOT_ESTABLISHED};

const USAGE: &str = "\
dungeon-attest-check — check one archived dungeon narration attestation.

  --quote        <path>   the raw TDX quote (the .bin attachment)              [required]
  --record       <path>   the JSON sidecar beside it                           [required]
  --measurements <path>   a PINNED copy of the Chutes measurements registry    [check 3]
  --collateral   <path>   Intel-signed DCAP QuoteCollateralV3 JSON             [check 6]
  --pccs         <url>    fetch collateral instead (needs --features collateral-fetch)
  --accept-tcb   <list>   comma-separated accepted TCB statuses (default: UpToDate)
  --json                  print the checks as JSON instead of prose
  --help

Exit: 0 all checks ran and passed · 1 a check FAILED · 2 usage/IO · 3 a check did not run.";

struct Args {
    quote: Option<String>,
    record: Option<String>,
    measurements: Option<String>,
    collateral: Option<String>,
    pccs: Option<String>,
    accept_tcb: Vec<String>,
    json: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut args = Args {
        quote: None,
        record: None,
        measurements: None,
        collateral: None,
        pccs: None,
        accept_tcb: Vec::new(),
        json: false,
    };
    let mut it = std::env::args().skip(1);
    while let Some(flag) = it.next() {
        let mut value = || it.next().ok_or_else(|| format!("{flag} needs a value"));
        match flag.as_str() {
            "--quote" => args.quote = Some(value()?),
            "--record" | "--sidecar" => args.record = Some(value()?),
            "--measurements" | "--registry" => args.measurements = Some(value()?),
            "--collateral" => args.collateral = Some(value()?),
            "--pccs" => args.pccs = Some(value()?),
            "--accept-tcb" => {
                args.accept_tcb = value()?
                    .split(',')
                    .map(str::trim)
                    .filter(|s| !s.is_empty())
                    .map(str::to_string)
                    .collect();
            }
            "--json" => args.json = true,
            "--help" | "-h" => return Err(String::new()),
            other => return Err(format!("unknown argument {other}")),
        }
    }
    Ok(args)
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => ExitCode::from(code as u8),
        Err(message) => {
            if !message.is_empty() {
                eprintln!("{message}\n");
            }
            eprintln!("{USAGE}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<i32, String> {
    let args = parse_args()?;
    let quote_path = args.quote.ok_or("--quote is required")?;
    let record_path = args.record.ok_or("--record is required")?;

    let quote = std::fs::read(&quote_path).map_err(|e| format!("read {quote_path}: {e}"))?;
    let record_text =
        std::fs::read_to_string(&record_path).map_err(|e| format!("read {record_path}: {e}"))?;
    let record: NarrationAttestationRecord = serde_json::from_str(&record_text)
        .map_err(|e| format!("the sidecar {record_path} did not parse: {e}"))?;

    let registry = match args.measurements.as_ref() {
        Some(path) => Some(std::fs::read_to_string(path).map_err(|e| format!("read {path}: {e}"))?),
        None => None,
    };

    // Collateral from a file, or (only with the feature) fetched for THIS quote from a PCCS.
    let collateral = match (args.collateral.as_ref(), args.pccs.as_ref()) {
        (Some(path), _) => {
            Some(std::fs::read_to_string(path).map_err(|e| format!("read {path}: {e}"))?)
        }
        (None, Some(url)) => Some(fetch_collateral(&quote, url)?),
        (None, None) => None,
    };

    let verification = verify_record(
        &quote,
        &record,
        registry.as_deref(),
        collateral.as_deref(),
        &args.accept_tcb,
    );

    if args.json {
        println!("{}", render_json(&record, &verification));
    } else {
        println!("dungeon narration attestation");
        println!("  record   {record_path}");
        println!("  quote    {quote_path} ({} bytes)", quote.len());
        println!("  receipt  {}", record.receipt_hex);
        println!("  model    {}", record.model);
        println!();
        print!("{}", verification.render());
    }
    Ok(verification.exit_code())
}

#[cfg(feature = "collateral-fetch")]
fn fetch_collateral(quote: &[u8], url: &str) -> Result<String, String> {
    let collateral = dregg_tee_verify::tdx::fetch_collateral_blocking(quote, url)?;
    serde_json::to_string(&collateral).map_err(|e| format!("serialize fetched collateral: {e}"))
}

#[cfg(not(feature = "collateral-fetch"))]
fn fetch_collateral(_quote: &[u8], _url: &str) -> Result<String, String> {
    Err(
        "--pccs needs `--features collateral-fetch`. Without it this program makes no network \
         request at all; pass --collateral <file> instead."
            .to_string(),
    )
}

/// The machine-readable form. `not_established` rides along so a consumer that only reads JSON
/// still gets the ceiling.
fn render_json(
    record: &NarrationAttestationRecord,
    verification: &dregg_attest_check::Verification,
) -> String {
    let checks: Vec<serde_json::Value> = verification
        .checks
        .iter()
        .map(|c| {
            serde_json::json!({
                "number": c.number,
                "name": c.name,
                "state": c.state.label(),
                "detail": c.detail,
            })
        })
        .collect();
    serde_json::to_string_pretty(&serde_json::json!({
        "receipt_hex": record.receipt_hex,
        "quote_sha256_hex": record.quote_sha256_hex,
        "checks": checks,
        "verdict": verification.verdict_line(),
        "exit_code": verification.exit_code(),
        "not_established": NOT_ESTABLISHED,
    }))
    .unwrap_or_else(|_| "{}".to_string())
}
