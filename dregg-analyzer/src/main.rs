//! `dregg-analyze` — the forensic/observability CLI.
//!
//! ```text
//! dregg-analyze blocklace <capture-file>   # DAG: causal order, equivocation, finality, quorum
//! dregg-analyze receipts  <capture-file>   # strand: chain integrity, conservation disclosure
//! dregg-analyze wal       <capture-file>   # commit log: replay/recovery + crash overlay
//! dregg-analyze network   <capture-file>   # gossip: peer behavior + eclipse risk
//! dregg-analyze forest    <capture-file>   # turn forest: conservation/non-amplification (attested)
//! dregg-analyze auto      <capture-file>   # dispatch on the file's own `source` tag
//! ```
//!
//! Captures are JSON (`.json`) or postcard (any other extension / `--postcard`).
//! `--json` emits the structured [`AnalysisReport`] as JSON; otherwise a
//! human-readable report is printed. Exit code is non-zero iff the capture is
//! anomalous (a `Critical` finding).

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use dregg_analyzer::findings::{Attestation, Severity};
use dregg_analyzer::{AnalysisReport, Capture, TraceAnalyzer};
use dregg_analyzer::{blocklace, forest, network, receipts, wal};

#[derive(Parser)]
#[command(
    name = "dregg-analyze",
    about = "Forensic/observability analysis of captured dregg traces — attesting every \
             checkable claim against the real dregg verifiers."
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
    /// Emit the structured report as JSON instead of human-readable text.
    #[arg(long, global = true)]
    json: bool,
    /// Force postcard decoding (default: by extension — `.json` ⇒ JSON, else postcard).
    #[arg(long, global = true)]
    postcard: bool,
}

#[derive(Subcommand)]
enum Command {
    /// Analyze a blocklace-DAG capture.
    Blocklace { file: PathBuf },
    /// Analyze a receipt-strand capture.
    Receipts { file: PathBuf },
    /// Analyze a persist/WAL commit-log capture.
    Wal { file: PathBuf },
    /// Analyze a network/gossip capture.
    Network { file: PathBuf },
    /// Analyze a captured turn forest (conservation/non-amplification, attested).
    Forest { file: PathBuf },
    /// Auto-detect the source from the capture file's own `source` tag.
    Auto { file: PathBuf },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let report = match run(&cli) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };

    if cli.json {
        match serde_json::to_string_pretty(&report) {
            Ok(s) => println!("{s}"),
            Err(e) => {
                eprintln!("error serializing report: {e}");
                return ExitCode::FAILURE;
            }
        }
    } else {
        print_human(&report);
    }

    if report.is_clean() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn run(cli: &Cli) -> Result<AnalysisReport, String> {
    let (file, is_auto): (&PathBuf, bool) = match &cli.command {
        Command::Blocklace { file }
        | Command::Receipts { file }
        | Command::Wal { file }
        | Command::Network { file }
        | Command::Forest { file } => (file, false),
        Command::Auto { file } => (file, true),
    };

    let bytes = std::fs::read(file).map_err(|e| format!("reading {}: {e}", file.display()))?;
    let use_postcard = cli.postcard || file.extension().map(|e| e != "json").unwrap_or(true);

    if is_auto {
        let capture: Capture = decode(&bytes, use_postcard)?;
        return Ok(TraceAnalyzer::analyze(&capture));
    }

    Ok(match &cli.command {
        Command::Blocklace { .. } => {
            let c: blocklace::BlocklaceCapture = decode(&bytes, use_postcard)?;
            blocklace::analyze(&c)
        }
        Command::Receipts { .. } => {
            let c: receipts::ReceiptStrandCapture = decode(&bytes, use_postcard)?;
            receipts::analyze(&c)
        }
        Command::Wal { .. } => {
            let c: wal::WalCapture = decode(&bytes, use_postcard)?;
            wal::analyze(&c)
        }
        Command::Network { .. } => {
            let c: network::NetworkCapture = decode(&bytes, use_postcard)?;
            network::analyze(&c)
        }
        Command::Forest { .. } => {
            let c: forest::ForestCapture = decode(&bytes, use_postcard)?;
            forest::analyze(&c)
        }
        Command::Auto { .. } => unreachable!("handled above"),
    })
}

fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8], use_postcard: bool) -> Result<T, String> {
    if use_postcard {
        postcard::from_bytes(bytes).map_err(|e| format!("postcard decode: {e}"))
    } else {
        serde_json::from_slice(bytes).map_err(|e| format!("json decode: {e}"))
    }
}

fn print_human(report: &AnalysisReport) {
    println!("═══ dregg trace analysis: {} ═══", report.source);
    if !report.summary.is_empty() {
        println!("\nSummary:");
        for (k, v) in &report.summary {
            println!("  {k:<28} {v}");
        }
    }
    println!("\nFindings ({}):", report.findings.len());
    for f in &report.findings {
        let sev = match f.severity {
            Severity::Info => "INFO",
            Severity::Notice => "NOTICE",
            Severity::Critical => "CRITICAL",
        };
        let att = match &f.attestation {
            Attestation::Verified { by } => format!("[VERIFIED by {by}]"),
            Attestation::Observed => "[observed]".to_string(),
        };
        println!("  {sev:<8} {} {att}", f.code);
        println!("           {}", f.message);
    }
    println!("\n{}", report.verdict_line());
}
