//! `dregg-auth` — the 60-second CLI for scoped, offline-verifiable agent tokens.
//!
//!   dregg-auth init                       generate + store a root key
//!   dregg-auth pubkey                     print the root public key (publishable)
//!   dregg-auth grant <agent> \
//!       --tools read,pr-create \
//!       --until friday                    emit a scoped token (printed to stdout)
//!   dregg-auth verify <token> --tool pr-create [--at WHEN] [--pubkey HEX]
//!                                         exit 0 (allow) / 1 (deny) + a reason
//!   dregg-auth attenuate <token> --tools read [--until +1d] [--pubkey HEX]
//!                                         emit a narrowed token (never amplifies)
//!   dregg-auth gate <token> --tool <name> [--args k=v,...] [--pubkey HEX]
//!                                         middleware profile: decide + a receipt
//!   dregg-auth explain <token> [--pubkey HEX]
//!                                         print the grant's terms, block by block
//!
//! Every command rides the **proven** credential core (`dregg_auth::policy`):
//! the token a `grant` issues IS a machine-checked credential (the `dga1_…`
//! form), the decision a `verify`/`gate` makes IS `Credential::verify`. L1 is
//! standalone: no node, no wallet, no network. `verify` needs only a public
//! key (defaults to the local root's, or pass `--pubkey`).
//!
//! `--until` / `--at` accept an absolute clock (unix seconds), a relative
//! offset (`+7d`, `+24h`, `+90m`, `+2w`), or a friendly **named day**
//! (`friday`, `tomorrow`, `eod`, `eow`) — resolved against the wall clock at
//! the moment of issue.

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};

use dregg_auth::policy::{Call, Grant, Policy, Verifier};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        usage();
        return ExitCode::FAILURE;
    }
    let cmd = args[0].as_str();
    let rest = &args[1..];

    let result = match cmd {
        "init" => cmd_init(),
        "pubkey" => cmd_pubkey(),
        "grant" => cmd_grant(rest),
        "verify" => return cmd_verify(rest),
        "attenuate" => cmd_attenuate(rest),
        "gate" => return cmd_gate(rest),
        "explain" => cmd_explain(rest),
        "help" | "-h" | "--help" => {
            usage();
            Ok(())
        }
        other => Err(CliError::Usage(format!("unknown command `{other}`"))),
    };

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("dregg-auth: {e}");
            ExitCode::FAILURE
        }
    }
}

// =============================================================================
// Commands
// =============================================================================

fn cmd_init() -> Result<(), CliError> {
    let path = key_path();
    if path.exists() {
        return Err(CliError::Other(format!(
            "root key already exists at {} (refusing to overwrite)",
            path.display()
        )));
    }
    let polis = Policy::generate();
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).map_err(|e| CliError::Io(e.to_string()))?;
    }
    std::fs::write(&path, polis.secret_hex()).map_err(|e| CliError::Io(e.to_string()))?;
    restrict_permissions(&path);
    println!("root key written to {}", path.display());
    println!("public key (publish this):");
    println!("{}", polis.public_key_hex());
    Ok(())
}

fn cmd_pubkey() -> Result<(), CliError> {
    let polis = load_policy()?;
    println!("{}", polis.public_key_hex());
    Ok(())
}

fn cmd_grant(args: &[String]) -> Result<(), CliError> {
    let (positional, flags) = parse(args);
    let subject = positional
        .first()
        .ok_or_else(|| CliError::Usage("grant requires an <agent>".into()))?;

    let tools = flag_list(&flags, "tools");
    if tools.is_empty() {
        return Err(CliError::Usage(
            "grant requires --tools tool1,tool2 (an unscoped agent token is the thing we prevent)"
                .into(),
        ));
    }

    let mut grant = Grant::to(subject).tools(tools);
    if let Some(until) = flags.get("until") {
        grant = grant.until(parse_when(until)?);
    }

    let polis = load_policy()?;
    let token = polis.issue(grant).map_err(CliError::Policy)?;
    println!("{}", token.encode());
    Ok(())
}

fn cmd_verify(args: &[String]) -> ExitCode {
    match do_verify(args) {
        Ok(verdict) => {
            // Human reason to stderr; exit code carries allow/deny for scripts.
            eprintln!("{}", verdict.reason());
            if verdict.admitted() {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        Err(e) => {
            eprintln!("dregg-auth: {e}");
            ExitCode::FAILURE
        }
    }
}

fn do_verify(args: &[String]) -> Result<dregg_auth::policy::Verdict, CliError> {
    let (positional, flags) = parse(args);
    let token = positional
        .first()
        .ok_or_else(|| CliError::Usage("verify requires a <token>".into()))?;
    let tool = flags
        .get("tool")
        .ok_or_else(|| CliError::Usage("verify requires --tool <name>".into()))?;

    let pubkey = pubkey_or_local(&flags)?;
    let mut call = Call::tool(tool);
    // Default to "now" so a token without an explicit --at is checked against
    // the wall clock; pass --at WHEN for a deterministic offline check.
    call = call.at(match flags.get("at") {
        Some(at) => parse_when(at)?,
        None => now_secs(),
    });
    for pair in flag_list(&flags, "args") {
        if let Some((k, v)) = pair.split_once('=') {
            call = call.arg(k, v);
        }
    }

    let gate = Verifier::new(pubkey);
    Ok(gate.admit(token, &call))
}

fn cmd_attenuate(args: &[String]) -> Result<(), CliError> {
    let (positional, flags) = parse(args);
    let encoded = positional
        .first()
        .ok_or_else(|| CliError::Usage("attenuate requires a <token>".into()))?;

    // The proven narrowing rides the GrantToken; reconstruct it from the wire
    // (structural validation — narrowing does not need a verifier key, the
    // bearer-tail discipline keeps it sound, and the result re-verifies under
    // the original root). --pubkey is accepted but unused here.
    let _ = &flags;
    let token = dregg_auth::policy::GrantToken::decode(encoded)
        .map_err(|e| CliError::Other(format!("cannot parse token: {e}")))?;

    let tools = flag_list(&flags, "tools");
    let tools_opt: Option<&[String]> = if tools.is_empty() { None } else { Some(&tools) };
    let until_opt = match flags.get("until") {
        Some(u) => Some(parse_when(u)?),
        None => None,
    };
    let narrowed = Grant::attenuate_token(token, tools_opt, until_opt).map_err(CliError::Policy)?;
    println!("{}", narrowed.encode());
    Ok(())
}

/// `gate` — the middleware profile: verify a call and print the audit receipt.
fn cmd_gate(args: &[String]) -> ExitCode {
    match do_gate(args) {
        Ok((line, admitted)) => {
            println!("{line}");
            if admitted {
                ExitCode::SUCCESS
            } else {
                ExitCode::FAILURE
            }
        }
        Err(e) => {
            eprintln!("dregg-auth: {e}");
            ExitCode::FAILURE
        }
    }
}

fn do_gate(args: &[String]) -> Result<(String, bool), CliError> {
    let (positional, flags) = parse(args);
    let encoded = positional
        .first()
        .ok_or_else(|| CliError::Usage("gate requires a <token>".into()))?;
    let tool = flags
        .get("tool")
        .ok_or_else(|| CliError::Usage("gate requires --tool <name>".into()))?;
    let pubkey = pubkey_or_local(&flags)?;

    let mut call = Call::tool(tool);
    call = call.at(match flags.get("at") {
        Some(at) => parse_when(at)?,
        None => now_secs(),
    });
    for pair in flag_list(&flags, "args") {
        if let Some((k, v)) = pair.split_once('=') {
            call = call.arg(k, v);
        }
    }

    let gate = Verifier::new(pubkey);
    let verdict = gate.admit(encoded, &call);
    let line = if flags.contains_key("json") {
        verdict.receipt.json()
    } else {
        verdict.receipt.line()
    };
    Ok((line, verdict.admitted()))
}

/// `explain` — print the grant's terms, block by block (the cold-reader audit).
fn cmd_explain(args: &[String]) -> Result<(), CliError> {
    let (positional, flags) = parse(args);
    let encoded = positional
        .first()
        .ok_or_else(|| CliError::Usage("explain requires a <token>".into()))?;
    // explain reads structure only — no key needed; but recover the subject for
    // the header if the token carries one.
    let token = dregg_auth::policy::GrantToken::decode(encoded)
        .map_err(|e| CliError::Other(format!("cannot parse token: {e}")))?;
    let _ = &flags; // explain ignores --pubkey; structural read only.
    println!("{}", token.explain());
    Ok(())
}

// =============================================================================
// Key storage
// =============================================================================

fn key_path() -> PathBuf {
    if let Ok(explicit) = std::env::var("DREGG_AUTH_KEY") {
        return PathBuf::from(explicit);
    }
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
    PathBuf::from(home).join(".dregg-auth").join("root.key")
}

fn load_policy() -> Result<Policy, CliError> {
    let path = key_path();
    let hex = std::fs::read_to_string(&path).map_err(|_| {
        CliError::Other(format!(
            "no root key at {} — run `dregg-auth init` first",
            path.display()
        ))
    })?;
    Policy::from_secret_hex(&hex).map_err(CliError::Policy)
}

/// The verifier public key: `--pubkey HEX` if given, else the local root's.
fn pubkey_or_local(flags: &HashMap<String, String>) -> Result<String, CliError> {
    match flags.get("pubkey") {
        Some(pk) => Ok(pk.clone()),
        None => Ok(load_policy()?.public_key_hex()),
    }
}

#[cfg(unix)]
fn restrict_permissions(path: &std::path::Path) {
    use std::os::unix::fs::PermissionsExt;
    let _ = std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600));
}
#[cfg(not(unix))]
fn restrict_permissions(_path: &std::path::Path) {}

// =============================================================================
// Tiny arg parsing + time helpers (no clap, no chrono — keep the surface tight)
// =============================================================================

/// Split args into positionals and `--key value` / `--key=value` flags.
/// `--flag` with no value becomes `("flag", "true")`.
fn parse(args: &[String]) -> (Vec<String>, HashMap<String, String>) {
    let mut positional = Vec::new();
    let mut flags = HashMap::new();
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        if let Some(key) = a.strip_prefix("--") {
            if let Some((k, v)) = key.split_once('=') {
                flags.insert(k.to_string(), v.to_string());
            } else if i + 1 < args.len() && !args[i + 1].starts_with("--") {
                flags.insert(key.to_string(), args[i + 1].clone());
                i += 1;
            } else {
                flags.insert(key.to_string(), "true".to_string());
            }
        } else {
            positional.push(a.clone());
        }
        i += 1;
    }
    (positional, flags)
}

fn flag_list(flags: &HashMap<String, String>, key: &str) -> Vec<String> {
    flags
        .get(key)
        .map(|s| {
            s.split(',')
                .map(|t| t.trim().to_string())
                .filter(|t| !t.is_empty())
                .collect()
        })
        .unwrap_or_default()
}

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

const DAY: u64 = 86_400;

/// Parse a `--until` / `--at` value into an absolute clock (unix seconds):
///
/// * an absolute unix timestamp (`1900000000`);
/// * a relative offset `+<n><unit>` where unit ∈ s/m/h/d/w (`+7d`, `+90m`);
/// * a friendly **named day**, resolved against the wall clock at issue:
///   `today`/`eod` (end of today), `tomorrow`, `eow` (end of this week, Sun),
///   or a weekday name (`mon`…`sun` / `monday`…`sunday`, the *next* such day,
///   end-of-day). The product's headline `--until friday` lands here.
fn parse_when(s: &str) -> Result<u64, CliError> {
    let s = s.trim();
    // Relative offset.
    if let Some(rel) = s.strip_prefix('+') {
        let (num, unit) =
            rel.split_at(rel.find(|c: char| !c.is_ascii_digit()).unwrap_or(rel.len()));
        let n: u64 = num
            .parse()
            .map_err(|_| CliError::Usage(format!("bad duration `{s}` (want e.g. +7d)")))?;
        let secs = match unit {
            "s" | "" => n,
            "m" => n * 60,
            "h" => n * 3600,
            "d" => n * DAY,
            "w" => n * 7 * DAY,
            other => {
                return Err(CliError::Usage(format!(
                    "unknown duration unit `{other}` (use s/m/h/d/w)"
                )));
            }
        };
        return Ok(now_secs() + secs);
    }
    // Named day.
    if let Some(at) = parse_named_day(s) {
        return Ok(at);
    }
    // Absolute timestamp.
    s.parse::<u64>().map_err(|_| {
        CliError::Usage(format!(
            "`{s}` is not a unix timestamp, a +<n><unit> offset, or a day name (friday, tomorrow, eod, eow)"
        ))
    })
}

/// End-of-day (23:59:59 UTC) of the day `days_ahead` from today, as unix secs.
fn end_of_day_in(days_ahead: u64) -> u64 {
    let now = now_secs();
    let start_of_today = now - (now % DAY);
    start_of_today + (days_ahead + 1) * DAY - 1
}

/// Resolve a friendly day name to an end-of-day unix timestamp, or `None` if it
/// is not a recognized day name. Weekday names resolve to the *next* such day
/// (today counts if it matches), end of that day.
fn parse_named_day(s: &str) -> Option<u64> {
    let lower = s.to_ascii_lowercase();
    match lower.as_str() {
        "today" | "eod" => return Some(end_of_day_in(0)),
        "tomorrow" => return Some(end_of_day_in(1)),
        "eow" => {
            // End of week = upcoming Sunday (inclusive of today if Sunday).
            let dow = day_of_week(now_secs()); // 0=Thu epoch-based; map below
            let days_to_sun = (6 + 7 - dow) % 7; // Sunday index 6 in our Mon..Sun
            return Some(end_of_day_in(days_to_sun as u64));
        }
        _ => {}
    }
    let target = weekday_index(&lower)?;
    let dow = day_of_week(now_secs());
    let days_ahead = (target + 7 - dow) % 7; // 0 if today matches
    Some(end_of_day_in(days_ahead as u64))
}

/// Day-of-week with Monday=0 … Sunday=6. (Unix epoch 1970-01-01 was a
/// Thursday, index 3.)
fn day_of_week(unix_secs: u64) -> u32 {
    let days = unix_secs / DAY;
    ((days + 3) % 7) as u32
}

/// Map a weekday name (full or 3-letter) to Monday=0 … Sunday=6.
fn weekday_index(name: &str) -> Option<u32> {
    Some(match name {
        "mon" | "monday" => 0,
        "tue" | "tues" | "tuesday" => 1,
        "wed" | "weds" | "wednesday" => 2,
        "thu" | "thur" | "thurs" | "thursday" => 3,
        "fri" | "friday" => 4,
        "sat" | "saturday" => 5,
        "sun" | "sunday" => 6,
        _ => return None,
    })
}

// =============================================================================
// Errors + usage
// =============================================================================

enum CliError {
    Usage(String),
    Io(String),
    Other(String),
    Policy(dregg_auth::policy::PolicyError),
}

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliError::Usage(s) => write!(f, "{s}\n\n(run `dregg-auth help`)"),
            CliError::Io(s) => write!(f, "io error: {s}"),
            CliError::Other(s) => write!(f, "{s}"),
            CliError::Policy(e) => write!(f, "{e}"),
        }
    }
}

fn usage() {
    eprintln!(
        r#"dregg-auth — scoped, offline-verifiable agent permissions (proven core)

  init                                 generate + store a root key (~/.dregg-auth/root.key)
  pubkey                               print the root public key (publish this)
  grant <agent> --tools a,b \
        [--until friday]               emit a scoped token (printed to stdout)
  verify <token> --tool <name> \
        [--at WHEN] [--pubkey HEX]     exit 0=allow / 1=deny, reason on stderr
  attenuate <token> --tools a \
        [--until +1d] [--pubkey HEX]   emit a narrowed token (never amplifies)
  gate <token> --tool <name> \
        [--args k=v,...] [--json]      middleware profile: decide + print a receipt
  explain <token>                      print the grant's terms, block by block

WHEN = a unix timestamp, a +<n><unit> offset (+7d/+24h/+90m/+2w), or a day name
(friday, tomorrow, eod, eow). The token a `grant` issues is a machine-checked
credential; verification is OFFLINE — it needs only a public key. No node, no
wallet, no blockchain."#
    );
}
