//! Named identity profiles: `dregg id create / list / use`.
//!
//! Identity step 1 (`docs/REFINEMENT-DESIGN.md` Decision 2): an identity is a
//! *name you chose*, not a hex key you pasted. Profiles live where the
//! cipherclerk keeps keys, in the exact store the SDK reads
//! (`sdk/src/profiles.rs` — keep the two in lockstep):
//!
//! ```text
//! $DREGG_HOME/profiles/<name>.json   (else ~/.dregg/profiles/) — mode 0600
//! $DREGG_HOME/profiles/ACTIVE        — the persistent default (a name)
//! ```
//!
//! The active profile resolves as `DREGG_PROFILE` (env override) → `ACTIVE`
//! file → none, and both the SDK (`AgentCipherclerk::from_active_profile`)
//! and this CLI pick it up automatically.
//!
//! Key derivation matches the SDK's [`AgentCipherclerk::from_seed`] exactly:
//! `blake3::derive_key("dregg/0", seed)` → Ed25519 signing key. The golden
//! vector test at the bottom of this file is mirrored in
//! `sdk/src/profiles.rs`; if either side changes derivation, both tests fail.

use std::io::Write;
use std::path::PathBuf;

use clap::Subcommand;
use serde::{Deserialize, Serialize};
use zeroize::Zeroizing;

use crate::config::Config;
use crate::output::{Context, abbrev_hex};

/// Environment variable that overrides the persistent active profile.
pub const PROFILE_ENV: &str = "DREGG_PROFILE";

/// The derivation path the SDK uses for the primary identity key.
const DERIVATION_PATH: &str = "dregg/0";

#[derive(Subcommand)]
pub enum IdCommand {
    /// Create a named identity profile (fresh Ed25519 key).
    Create {
        /// Profile name: 1-64 chars of [a-z0-9-_].
        name: String,
    },

    /// List identity profiles (the active one is marked).
    List,

    /// Set the persistent default profile (DREGG_PROFILE env overrides it).
    Use {
        /// Profile name to make the default.
        name: String,
    },
}

pub async fn run(
    cmd: IdCommand,
    cfg: &Config,
    ctx: &Context,
) -> Result<(), Box<dyn std::error::Error>> {
    match cmd {
        IdCommand::Create { name } => create(cfg, ctx, &name),
        IdCommand::List => list(cfg, ctx),
        IdCommand::Use { name } => use_profile(cfg, ctx, &name),
    }
}

// ─── the store (format-compatible with sdk/src/profiles.rs) ───

/// The on-disk profile record (version 1) — the SDK's `ProfileFile` shape.
#[derive(Serialize, Deserialize)]
struct ProfileFile {
    version: u32,
    name: String,
    /// 64-byte master seed, hex — KEY MATERIAL.
    seed_hex: String,
    /// Ed25519 public key derived from the seed, hex (display/audit).
    public_key_hex: String,
    /// Unix seconds at creation.
    created_at: i64,
}

/// `$DREGG_HOME/profiles` if set, else `~/.dregg/profiles` (next to
/// `config.toml`).
fn profiles_dir() -> PathBuf {
    if let Some(home) = std::env::var_os("DREGG_HOME") {
        return PathBuf::from(home).join("profiles");
    }
    let base = dirs::home_dir().unwrap_or_else(|| PathBuf::from("."));
    base.join(".dregg").join("profiles")
}

fn profile_path(name: &str) -> PathBuf {
    profiles_dir().join(format!("{name}.json"))
}

fn active_path() -> PathBuf {
    profiles_dir().join("ACTIVE")
}

fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 64
        && name
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-' || c == '_')
}

/// The active profile name: `DREGG_PROFILE` env override → `ACTIVE` file.
fn active_name() -> Option<String> {
    if let Ok(name) = std::env::var(PROFILE_ENV) {
        let name = name.trim().to_string();
        if !name.is_empty() {
            return Some(name);
        }
    }
    let contents = std::fs::read_to_string(active_path()).ok()?;
    let name = contents.trim().to_string();
    (!name.is_empty()).then_some(name)
}

fn write_private(path: &PathBuf, bytes: &[u8]) -> std::io::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let mut opts = std::fs::OpenOptions::new();
    opts.write(true).create(true).truncate(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.mode(0o600);
    }
    let mut f = opts.open(path)?;
    f.write_all(bytes)?;
    Ok(())
}

/// The SDK's key derivation, replicated byte-for-byte
/// (`sdk/src/mnemonic.rs::derive_keypair` at path `dregg/0`): the BLAKE3 KDF
/// output is the Ed25519 seed.
fn derive_public_key(seed: &[u8; 64]) -> [u8; 32] {
    let derived = Zeroizing::new(blake3::derive_key(DERIVATION_PATH, seed));
    let signing = ed25519_dalek::SigningKey::from_bytes(&derived);
    signing.verifying_key().to_bytes()
}

// ─── the verbs ───

fn create(cfg: &Config, ctx: &Context, name: &str) -> Result<(), Box<dyn std::error::Error>> {
    if !valid_name(name) {
        return Err(format!("invalid profile name {name:?}: use 1-64 chars of [a-z0-9-_]").into());
    }
    let path = profile_path(name);
    if path.exists() {
        return Err(format!("profile {name:?} already exists ({})", path.display()).into());
    }

    let mut seed = Zeroizing::new([0u8; 64]);
    getrandom::fill(seed.as_mut())
        .map_err(|e| format!("OS randomness unavailable for key generation: {e}"))?;
    let public_key_hex = hex::encode(derive_public_key(&seed));
    let created_at = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    let record = ProfileFile {
        version: 1,
        name: name.to_string(),
        seed_hex: hex::encode(seed.as_ref()),
        public_key_hex: public_key_hex.clone(),
        created_at,
    };
    write_private(&path, &serde_json::to_vec_pretty(&record)?)?;

    if cfg.is_json() {
        ctx.json_stdout(&serde_json::json!({
            "created": name,
            "public_key": public_key_hex,
            "path": path.display().to_string(),
            "active": active_name().as_deref() == Some(name),
        }));
        return Ok(());
    }
    ctx.success(&format!("Created identity profile '{name}'"));
    ctx.kv("Public key", &public_key_hex);
    ctx.kv_dim("Key file", &format!("{} (mode 0600)", path.display()));
    if active_name().as_deref() != Some(name) {
        ctx.info(&format!(
            "  Make it the default with `dregg id use {name}` (or export {PROFILE_ENV}={name})."
        ));
    }
    Ok(())
}

fn list(cfg: &Config, ctx: &Context) -> Result<(), Box<dyn std::error::Error>> {
    let dir = profiles_dir();
    let active = active_name();
    let env_override = std::env::var(PROFILE_ENV).ok().filter(|v| !v.trim().is_empty());

    let mut profiles: Vec<ProfileFile> = Vec::new();
    match std::fs::read_dir(&dir) {
        Ok(entries) => {
            for entry in entries {
                let path = entry?.path();
                if path.extension().and_then(|e| e.to_str()) != Some("json") {
                    continue;
                }
                let contents = std::fs::read_to_string(&path)?;
                match serde_json::from_str::<ProfileFile>(&contents) {
                    Ok(p) => profiles.push(p),
                    Err(e) => {
                        // Surface a broken profile rather than hiding it.
                        profiles.push(ProfileFile {
                            version: 0,
                            name: path
                                .file_stem()
                                .and_then(|s| s.to_str())
                                .unwrap_or("?")
                                .to_string(),
                            seed_hex: String::new(),
                            public_key_hex: format!("<malformed: {e}>"),
                            created_at: 0,
                        });
                    }
                }
            }
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(e.into()),
    }
    profiles.sort_by(|a, b| a.name.cmp(&b.name));

    if cfg.is_json() {
        let rows: Vec<serde_json::Value> = profiles
            .iter()
            .map(|p| {
                serde_json::json!({
                    "name": p.name,
                    "public_key": p.public_key_hex,
                    "created_at": p.created_at,
                    "active": active.as_deref() == Some(p.name.as_str()),
                })
            })
            .collect();
        ctx.json_stdout(&serde_json::json!({
            "profiles": rows,
            "active": active,
            "env_override": env_override,
            "store": dir.display().to_string(),
        }));
        return Ok(());
    }

    ctx.header("Identity Profiles");
    if profiles.is_empty() {
        ctx.info(&format!(
            "No profiles yet ({}). Create one with `dregg id create <name>`.",
            dir.display()
        ));
        return Ok(());
    }
    let rows: Vec<Vec<String>> = profiles
        .iter()
        .map(|p| {
            vec![
                if active.as_deref() == Some(p.name.as_str()) {
                    format!("* {}", p.name)
                } else {
                    format!("  {}", p.name)
                },
                abbrev_hex(&p.public_key_hex, 12, 6),
            ]
        })
        .collect();
    ctx.table(&["Name", "Public key"], &rows);
    match (&env_override, &active) {
        (Some(name), _) => ctx.info(&format!("  * active via {PROFILE_ENV}={name} (env override)")),
        (None, Some(name)) => ctx.kv_dim("Active", &format!("{name} (persistent default)")),
        (None, None) => ctx.info("  No active profile. Set one with `dregg id use <name>`."),
    }
    Ok(())
}

fn use_profile(cfg: &Config, ctx: &Context, name: &str) -> Result<(), Box<dyn std::error::Error>> {
    if !valid_name(name) {
        return Err(format!("invalid profile name {name:?}: use 1-64 chars of [a-z0-9-_]").into());
    }
    if !profile_path(name).exists() {
        return Err(format!(
            "profile {name:?} not found — `dregg id list` shows what exists; \
             `dregg id create {name}` makes it"
        )
        .into());
    }
    write_private(&active_path(), name.as_bytes())?;

    if cfg.is_json() {
        ctx.json_stdout(&serde_json::json!({ "active": name }));
        return Ok(());
    }
    ctx.success(&format!("Active profile is now '{name}'"));
    if let Ok(env) = std::env::var(PROFILE_ENV) {
        if !env.trim().is_empty() && env.trim() != name {
            ctx.warn(&format!(
                "{PROFILE_ENV}={} is set and overrides this default in this shell.",
                env.trim()
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The CLI's replicated derivation matches the SDK's
    /// `AgentCipherclerk::from_seed` byte-for-byte. The same golden vector is
    /// asserted in `sdk/src/profiles.rs`; if either side drifts, both fail.
    #[test]
    fn derivation_matches_sdk_golden_vector() {
        let mut seed = [0u8; 64];
        for (i, b) in seed.iter_mut().enumerate() {
            *b = i as u8;
        }
        assert_eq!(
            hex::encode(derive_public_key(&seed)),
            "335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a",
            "CLI key derivation diverged from the SDK profile store"
        );
    }

    #[test]
    fn profile_record_shape_is_sdk_compatible() {
        // The exact field set sdk/src/profiles.rs reads (version-1 record).
        let json = r#"{ "version": 1, "name": "ember",
            "seed_hex": "00", "public_key_hex": "aa", "created_at": 5 }"#;
        let p: ProfileFile = serde_json::from_str(json).unwrap();
        assert_eq!(p.version, 1);
        assert_eq!(p.name, "ember");
        assert_eq!(p.created_at, 5);
    }

    #[test]
    fn names_are_validated() {
        assert!(valid_name("ember"));
        assert!(valid_name("node-2_test"));
        assert!(!valid_name(""));
        assert!(!valid_name("No Caps"));
        assert!(!valid_name("../evil"));
    }
}
