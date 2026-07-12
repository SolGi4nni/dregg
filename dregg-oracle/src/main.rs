//! **dregg-oracle** — CLI for *trustless web facts you can reuse*.
//!
//! ```text
//! dregg-oracle prove  --endpoint coinbase --asset BTC-USD           --out proof.json
//! dregg-oracle prove  --endpoint github   --repo octocat/hello-world --sha 6dcb09b… --out proof.json
//! dregg-oracle verify proof.json
//! ```
//!
//! `prove` runs the real-host zkOracle proof and writes a PORTABLE `proof.json`.
//! `verify` re-runs the genuine verifier fail-closed and prints the attested fact —
//! anyone can run it, trusting no one but the pinned transport anchors.

use std::path::PathBuf;

use anyhow::{bail, Context, Result};
use clap::{Parser, Subcommand, ValueEnum};

use dregg_oracle::{prove, verify_envelope, Endpoint, ProofEnvelope};

#[derive(Parser)]
#[command(
    name = "dregg-oracle",
    version,
    about = "Trustless web facts you can reuse — portable, independently-verifiable proofs that a real HTTPS endpoint returned a value (authentic ∧ well-formed ∧ injection-free, STARK-bound)."
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Produce a portable proof that a real HTTPS endpoint returned a value.
    Prove {
        /// Which public web fact to prove.
        #[arg(long, value_enum)]
        endpoint: EndpointArg,
        /// Coinbase: the asset pair, e.g. `BTC-USD` (a bare `BTC` is read as `BTC-USD`).
        #[arg(long)]
        asset: Option<String>,
        /// GitHub: the repository as `owner/name`.
        #[arg(long)]
        repo: Option<String>,
        /// GitHub: the commit sha.
        #[arg(long)]
        sha: Option<String>,
        /// url: the full https URL, e.g. https://api.coincap.io/v2/assets/bitcoin
        #[arg(long)]
        url: Option<String>,
        /// url: dotted path to the field to report, e.g. data.priceUsd
        #[arg(long)]
        field: Option<String>,
        /// npm/wikipedia: the package name or page title for a preset endpoint.
        #[arg(long)]
        name: Option<String>,
        /// Where to write the portable proof.
        #[arg(long, default_value = "proof.json")]
        out: PathBuf,
    },
    /// Verify a portable proof, fail-closed, and print the attested fact.
    Verify {
        /// The `proof.json` to verify.
        proof: PathBuf,
    },
}

#[derive(Clone, ValueEnum)]
enum EndpointArg {
    Coinbase,
    Github,
    Url,
    /// npm registry: prove the latest published version of a package.
    Npm,
    /// Wikipedia REST summary: prove a field of a page summary.
    Wikipedia,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Prove {
            endpoint,
            asset,
            repo,
            sha,
            url,
            field,
            name,
            out,
        } => run_prove(endpoint, asset, repo, sha, url, field, name, out),
        Cmd::Verify { proof } => run_verify(proof),
    }
}

fn run_prove(
    endpoint: EndpointArg,
    asset: Option<String>,
    repo: Option<String>,
    sha: Option<String>,
    url: Option<String>,
    field: Option<String>,
    name: Option<String>,
    out: PathBuf,
) -> Result<()> {
    let endpoint = match endpoint {
        EndpointArg::Coinbase => {
            let asset = asset.context("--asset is required for --endpoint coinbase")?;
            // Convenience: a bare base (`BTC`) is quoted in USD.
            let asset = if asset.contains('-') {
                asset
            } else {
                format!("{asset}-USD")
            };
            Endpoint::Coinbase { asset }
        }
        EndpointArg::Github => {
            let repo = repo.context("--repo owner/name is required for --endpoint github")?;
            let (owner, name) = repo
                .split_once('/')
                .context("--repo must be owner/name (e.g. octocat/hello-world)")?;
            let sha = sha.context("--sha is required for --endpoint github")?;
            Endpoint::Github {
                owner: owner.to_string(),
                repo: name.to_string(),
                sha,
            }
        }
        EndpointArg::Url => {
            let url = url.context("--url is required for --endpoint url")?;
            let field = field.context(
                "--field (dotted path, e.g. data.priceUsd) is required for --endpoint url",
            )?;
            let rest = url
                .strip_prefix("https://")
                .context("--url must start with https://")?;
            let (host, path) = match rest.split_once('/') {
                Some((h, p)) => (h.to_string(), format!("/{p}")),
                None => (rest.to_string(), "/".to_string()),
            };
            Endpoint::Url { host, path, field }
        }
        EndpointArg::Npm => {
            let name = name.context("--name <package> is required for --endpoint npm")?;
            // registry.npmjs.org/<pkg>/latest is a plain public JSON GET; the
            // preset just wires up the existing Url path with a default field.
            let field = field.unwrap_or_else(|| "version".to_string());
            Endpoint::Url {
                host: "registry.npmjs.org".to_string(),
                path: format!("/{name}/latest"),
                field,
            }
        }
        EndpointArg::Wikipedia => {
            let name = name.context("--name <title> is required for --endpoint wikipedia")?;
            // REST v1 page-summary is a plain public JSON GET.
            let field = field.unwrap_or_else(|| "title".to_string());
            Endpoint::Url {
                host: "en.wikipedia.org".to_string(),
                path: format!("/api/rest_v1/page/summary/{name}"),
                field,
            }
        }
    };

    eprintln!(
        "proving {} against {} …",
        endpoint.label(),
        endpoint.server_name()
    );
    let env = prove(&endpoint)?;
    let json = env.to_json()?;
    std::fs::write(&out, json.as_bytes())
        .with_context(|| format!("writing proof to {}", out.display()))?;
    eprintln!("wrote portable proof → {}", out.display());
    Ok(())
}

fn run_verify(proof: PathBuf) -> Result<()> {
    let json = std::fs::read_to_string(&proof)
        .with_context(|| format!("reading proof from {}", proof.display()))?;
    let env = ProofEnvelope::from_json(&json)?;

    match verify_envelope(&env) {
        Ok(att) => {
            println!("PASS  {}", att.value);
            println!("  endpoint     {}", att.endpoint);
            println!("  server pinned {}", att.server_pinned);
            println!("  carrier      {}", att.carrier);
            println!("  session time {} (unix)", att.time);
            println!("  legs passed  {}", att.legs.len());
            for leg in &att.legs {
                println!("    \u{2713} {:<14} {}", leg.name, leg.detail);
            }
            println!("  tool         {}", env.tool);
            println!("  note         {}", att.trust_note);
            Ok(())
        }
        Err(e) => {
            // Fail-closed: a refused proof is a hard error, named leg and all.
            println!("FAIL  {} — {e:#}", env.endpoint.label());
            bail!("proof did not verify");
        }
    }
}
