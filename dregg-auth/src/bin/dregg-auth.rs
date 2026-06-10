//! `dregg-auth` — the 60-second CLI for scoped, offline-verifiable agent tokens.
//!
//!   dregg-auth init                       generate + store a root key
//!   dregg-auth pubkey                     print the root public key (publishable)
//!   dregg-auth grant <subject> \
//!       --tools read,pr-create \
//!       --until +7d [--rate 30/h]         emit a scoped token
//!   dregg-auth verify <token> --tool pr-create [--args ...] [--pubkey HEX]
//!                                         exit 0 (allow) / 1 (deny) + a reason
//!   dregg-auth attenuate <token> --tools read [--until +1d]
//!                                         emit a narrowed token
//!
//! L1 is standalone: no node, no wallet, no network. `verify` needs only a
//! public key (defaults to the local root's, or pass `--pubkey`).

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};

use dregg_auth::{AuthError, Grant, Rate, Request, Token, mcp, verify_offline};

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
        "gate" => cmd_gate(rest),
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
    let root = dregg_auth::Root::generate();
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).map_err(|e| CliError::Io(e.to_string()))?;
    }
    std::fs::write(&path, root.private_key_hex()).map_err(|e| CliError::Io(e.to_string()))?;
    restrict_permissions(&path);
    println!("root key written to {}", path.display());
    println!("public key (publish this):");
    println!("{}", root.public_key_hex());
    Ok(())
}

fn cmd_pubkey() -> Result<(), CliError> {
    let root = load_root()?;
    println!("{}", root.public_key_hex());
    Ok(())
}

fn cmd_grant(args: &[String]) -> Result<(), CliError> {
    let (positional, flags) = parse(args);
    let subject = positional
        .first()
        .ok_or_else(|| CliError::Usage("grant requires a <subject>".into()))?;

    let tools = flag_list(&flags, "tools");
    if tools.is_empty() {
        return Err(CliError::Usage(
            "grant requires --tools tool1,tool2 (an unscoped agent token is the thing we prevent)"
                .into(),
        ));
    }

    let mut grant = Grant::new(subject).tools(tools);
    if let Some(until) = flags.get("until") {
        grant = grant.until(parse_until(until)?);
    }
    if let Some(rate) = flags.get("rate") {
        grant = grant.rate(Rate::parse(rate)?);
    }
    if let Some(actions) = flags.get("actions") {
        grant = grant.with_actions(actions);
    }

    let root = load_root()?;
    let token = root.issue(&grant)?;
    println!("{}", token.encode()?);
    Ok(())
}

fn cmd_verify(args: &[String]) -> ExitCode {
    match do_verify(args) {
        Ok(decision) => {
            // Human reason to stderr; exit code carries allow/deny for scripts.
            eprintln!("{}", decision.reason());
            if decision.allowed() {
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

fn do_verify(args: &[String]) -> Result<dregg_auth::Decision, CliError> {
    let (positional, flags) = parse(args);
    let token = positional
        .first()
        .ok_or_else(|| CliError::Usage("verify requires a <token>".into()))?;
    let tool = flags
        .get("tool")
        .ok_or_else(|| CliError::Usage("verify requires --tool <name>".into()))?;

    let pubkey = match flags.get("pubkey") {
        Some(pk) => pk.clone(),
        None => load_root()?.public_key_hex(),
    };

    let mut request = Request::tool(tool);
    if let Some(action) = flags.get("action") {
        request = request.action(action);
    }
    if let Some(now) = flags.get("at") {
        request = request.at(parse_until(now)?);
    }
    let arglist = flag_list(&flags, "args");
    if !arglist.is_empty() {
        request = request.with_args(arglist);
    }

    Ok(verify_offline(token, &pubkey, &request))
}

fn cmd_attenuate(args: &[String]) -> Result<(), CliError> {
    let (positional, flags) = parse(args);
    let encoded = positional
        .first()
        .ok_or_else(|| CliError::Usage("attenuate requires a <token>".into()))?;

    let pubkey = match flags.get("pubkey") {
        Some(pk) => pk.clone(),
        None => load_root()?.public_key_hex(),
    };
    let token = Token::parse(encoded, &pubkey)?;

    // The narrowing grant: subject is irrelevant for attenuation (it only
    // tightens tools/expiry), so use a placeholder subject.
    let mut narrow = Grant::new("_");
    let tools = flag_list(&flags, "tools");
    if !tools.is_empty() {
        narrow = narrow.tools(tools);
    }
    if let Some(until) = flags.get("until") {
        narrow = narrow.until(parse_until(until)?);
    }

    let narrowed = token.attenuate(&narrow)?;
    println!("{}", narrowed.encode()?);
    Ok(())
}

/// `gate` — demo the MCP gateway profile: verify a call and print the receipt.
fn cmd_gate(args: &[String]) -> Result<(), CliError> {
    let (positional, flags) = parse(args);
    let encoded = positional
        .first()
        .ok_or_else(|| CliError::Usage("gate requires a <token>".into()))?;
    let tool = flags
        .get("tool")
        .ok_or_else(|| CliError::Usage("gate requires --tool <name>".into()))?;
    let pubkey = match flags.get("pubkey") {
        Some(pk) => pk.clone(),
        None => load_root()?.public_key_hex(),
    };

    let mut call = mcp::ToolCall::new(tool);
    for pair in flag_list(&flags, "args") {
        if let Some((k, v)) = pair.split_once('=') {
            call = call.arg(k, v);
        }
    }
    if let Some(at) = flags.get("at") {
        call = call.at(parse_until(at)?);
    }

    let gate = mcp::OfflineGate::new(pubkey);
    use mcp::ToolGate;
    let gated = gate.admit(encoded, &call);
    println!("{}", gated.receipt.line());
    if gated.admitted() {
        Ok(())
    } else {
        Err(CliError::Denied)
    }
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

fn load_root() -> Result<dregg_auth::Root, CliError> {
    let path = key_path();
    let hex = std::fs::read_to_string(&path).map_err(|_| {
        CliError::Other(format!(
            "no root key at {} — run `dregg-auth init` first",
            path.display()
        ))
    })?;
    Ok(dregg_auth::Root::from_private_hex(&hex)?)
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

/// Parse an `--until` value: an absolute unix timestamp, or a relative offset
/// `+<n><unit>` where unit is s/m/h/d (e.g. `+7d`, `+24h`, `+90m`).
fn parse_until(s: &str) -> Result<i64, CliError> {
    let s = s.trim();
    if let Some(rel) = s.strip_prefix('+') {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let (num, unit) = rel.split_at(
            rel.find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rel.len()),
        );
        let n: i64 = num
            .parse()
            .map_err(|_| CliError::Usage(format!("bad duration `{s}` (want e.g. +7d)")))?;
        let secs = match unit {
            "s" | "" => n,
            "m" => n * 60,
            "h" => n * 3600,
            "d" => n * 86400,
            "w" => n * 604800,
            other => {
                return Err(CliError::Usage(format!(
                    "unknown duration unit `{other}` (use s/m/h/d/w)"
                )));
            }
        };
        return Ok(now + secs);
    }
    s.parse::<i64>()
        .map_err(|_| CliError::Usage(format!("`{s}` is not a unix timestamp or +<n><unit> offset")))
}

// =============================================================================
// Errors + usage
// =============================================================================

enum CliError {
    Usage(String),
    Io(String),
    Other(String),
    Auth(AuthError),
    Denied,
}

impl From<AuthError> for CliError {
    fn from(e: AuthError) -> Self {
        CliError::Auth(e)
    }
}

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliError::Usage(s) => write!(f, "{s}\n\n(run `dregg-auth help`)"),
            CliError::Io(s) => write!(f, "io error: {s}"),
            CliError::Other(s) => write!(f, "{s}"),
            CliError::Auth(e) => write!(f, "{e}"),
            CliError::Denied => write!(f, "denied"),
        }
    }
}

fn usage() {
    eprintln!(
        r#"dregg-auth — scoped, offline-verifiable agent permissions

  init                                 generate + store a root key (~/.dregg-auth/root.key)
  pubkey                               print the root public key (publish this)
  grant <subject> --tools a,b \
        [--until +7d] [--rate 30/h]    emit a scoped token (printed to stdout)
  verify <token> --tool <name> \
        [--args k=v,...] [--pubkey HEX]  exit 0=allow / 1=deny, reason on stderr
  attenuate <token> --tools a \
        [--until +1d] [--pubkey HEX]   emit a narrowed token (never amplifies)
  gate <token> --tool <name> \
        [--args k=v,...]               MCP gateway profile: decide + print a receipt

The guarantee: prove your agent cannot exceed the grant. Verification is OFFLINE
— it needs only a public key. No node, no wallet, no blockchain."#
    );
}
