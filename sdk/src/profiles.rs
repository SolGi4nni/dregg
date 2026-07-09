//! # Named local identity profiles (identity step 1).
//!
//! `dregg id create <name>` / `dregg id list` / `dregg id use <name>` — the
//! cipherclerk gains named local profiles so an identity is a *name you
//! chose*, not a hex key you pasted. This is stage 1 of the identity design
//! (`docs/REFINEMENT-DESIGN.md` Decision 2); the identity-council factory
//! and petname-DB ties are later stages.
//!
//! ## Store layout (shared with `dregg-cli`)
//!
//! Profiles live where dregg keeps its local state, next to the CLI config:
//!
//! ```text
//! ~/.dregg/profiles/<name>.json   — one profile per file (mode 0600)
//! ~/.dregg/profiles/ACTIVE        — the persistent default (a profile name)
//! ```
//!
//! A profile file is version-tagged JSON:
//!
//! ```json
//! { "version": 1, "name": "ember", "seed_hex": "…128 hex chars…",
//!   "public_key_hex": "…64 hex chars…", "created_at": 1765432100 }
//! ```
//!
//! `seed_hex` is the 64-byte master seed [`AgentCipherclerk::from_seed`]
//! derives the Ed25519 identity from — **key material**, protected only by
//! file permissions (the same custody level as a node's `node.key`).
//!
//! ## Resolution order
//!
//! The active profile is `DREGG_PROFILE` (env override) if set, else the
//! `ACTIVE` file, else none. [`load_active`] is what the SDK and CLI call
//! to pick the identity up automatically.

#![cfg(not(target_arch = "wasm32"))]

use std::io::Write;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};
use zeroize::Zeroizing;

use crate::cipherclerk::AgentCipherclerk;

/// Environment variable that overrides the persistent active profile.
pub const PROFILE_ENV: &str = "DREGG_PROFILE";

/// The on-disk profile record (version 1).
#[derive(Clone, Serialize, Deserialize)]
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

/// A profile's public face (no key material).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProfileInfo {
    /// The chosen name.
    pub name: String,
    /// Hex Ed25519 public key.
    pub public_key_hex: String,
    /// Unix seconds at creation.
    pub created_at: i64,
    /// Whether this is the currently-active profile.
    pub active: bool,
}

/// Profile-store errors.
#[derive(Debug, thiserror::Error)]
pub enum ProfileError {
    #[error("invalid profile name {0:?}: use 1-64 chars of [a-z0-9-_]")]
    InvalidName(String),
    #[error("profile {0:?} already exists")]
    AlreadyExists(String),
    #[error("profile {0:?} not found")]
    NotFound(String),
    #[error("profile store io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("profile file for {name:?} is malformed: {reason}")]
    Malformed { name: String, reason: String },
}

/// Where the profile store lives: `$DREGG_HOME/profiles` if `DREGG_HOME` is
/// set, else `~/.dregg/profiles` (next to the CLI's `config.toml`).
pub fn profiles_dir() -> PathBuf {
    if let Some(home) = std::env::var_os("DREGG_HOME") {
        return PathBuf::from(home).join("profiles");
    }
    let base = std::env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));
    base.join(".dregg").join("profiles")
}

fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 64
        && name
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-' || c == '_')
}

fn profile_path(name: &str) -> PathBuf {
    profiles_dir().join(format!("{name}.json"))
}

fn active_path() -> PathBuf {
    profiles_dir().join("ACTIVE")
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

fn read_profile(name: &str) -> Result<ProfileFile, ProfileError> {
    let path = profile_path(name);
    if !path.exists() {
        return Err(ProfileError::NotFound(name.to_string()));
    }
    let contents = std::fs::read_to_string(&path)?;
    serde_json::from_str(&contents).map_err(|e| ProfileError::Malformed {
        name: name.to_string(),
        reason: e.to_string(),
    })
}

fn seed_from(profile: &ProfileFile) -> Result<Zeroizing<[u8; 64]>, ProfileError> {
    let bytes = hex::decode(&profile.seed_hex).map_err(|e| ProfileError::Malformed {
        name: profile.name.clone(),
        reason: format!("seed_hex: {e}"),
    })?;
    let arr: [u8; 64] = bytes
        .as_slice()
        .try_into()
        .map_err(|_| ProfileError::Malformed {
            name: profile.name.clone(),
            reason: format!("seed_hex is {} bytes, expected 64", bytes.len()),
        })?;
    Ok(Zeroizing::new(arr))
}

/// Create a named profile with a fresh random 64-byte seed. Fails if the
/// name is taken. Returns its public face; the cipherclerk is available via
/// [`load`]. Does NOT change the active profile (call [`set_active`]).
pub fn create(name: &str) -> Result<ProfileInfo, ProfileError> {
    if !valid_name(name) {
        return Err(ProfileError::InvalidName(name.to_string()));
    }
    let path = profile_path(name);
    if path.exists() {
        return Err(ProfileError::AlreadyExists(name.to_string()));
    }
    let mut seed = Zeroizing::new([0u8; 64]);
    getrandom::fill(seed.as_mut()).expect("OS randomness must be available for key generation");
    let clerk = AgentCipherclerk::from_seed(*seed);
    let public_key_hex = hex::encode(clerk.public_key().0);
    let created_at = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    let record = ProfileFile {
        version: 1,
        name: name.to_string(),
        seed_hex: hex::encode(&seed[..]),
        public_key_hex: public_key_hex.clone(),
        created_at,
    };
    let json = serde_json::to_vec_pretty(&record).expect("profile record serializes");
    write_private(&path, &json)?;
    let active = active_name().as_deref() == Some(name);
    Ok(ProfileInfo {
        name: name.to_string(),
        public_key_hex,
        created_at,
        active,
    })
}

/// List all profiles (sorted by name), marking the active one.
pub fn list() -> Result<Vec<ProfileInfo>, ProfileError> {
    let dir = profiles_dir();
    let active = active_name();
    let mut out = Vec::new();
    let entries = match std::fs::read_dir(&dir) {
        Ok(e) => e,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(out),
        Err(e) => return Err(e.into()),
    };
    for entry in entries {
        let entry = entry?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let Some(name) = path.file_stem().and_then(|s| s.to_str()).map(String::from) else {
            continue;
        };
        match read_profile(&name) {
            Ok(p) => out.push(ProfileInfo {
                active: active.as_deref() == Some(name.as_str()),
                name: p.name,
                public_key_hex: p.public_key_hex,
                created_at: p.created_at,
            }),
            // A malformed file is listed by name so the user can see and fix
            // it — silently hiding a broken profile would be worse.
            Err(ProfileError::Malformed { name, reason }) => out.push(ProfileInfo {
                name,
                public_key_hex: format!("<malformed: {reason}>"),
                created_at: 0,
                active: false,
            }),
            Err(e) => return Err(e),
        }
    }
    out.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(out)
}

/// Set the persistent default profile (`dregg id use <name>`). The profile
/// must exist.
pub fn set_active(name: &str) -> Result<(), ProfileError> {
    if !valid_name(name) {
        return Err(ProfileError::InvalidName(name.to_string()));
    }
    if !profile_path(name).exists() {
        return Err(ProfileError::NotFound(name.to_string()));
    }
    write_private(&active_path(), name.as_bytes())?;
    Ok(())
}

/// The active profile name: `DREGG_PROFILE` env override first, then the
/// persistent `ACTIVE` file.
pub fn active_name() -> Option<String> {
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

/// Load a named profile's identity.
pub fn load(name: &str) -> Result<AgentCipherclerk, ProfileError> {
    let record = read_profile(name)?;
    let seed = seed_from(&record)?;
    Ok(AgentCipherclerk::from_seed(*seed))
}

/// Load the active profile's identity, if any is configured
/// (`DREGG_PROFILE` override → `ACTIVE` file → `Ok(None)`).
///
/// This is the automatic pickup point: SDK consumers (and the CLI) call
/// this to act as the named identity without any key plumbing.
pub fn load_active() -> Result<Option<AgentCipherclerk>, ProfileError> {
    match active_name() {
        Some(name) => load(&name).map(Some),
        None => Ok(None),
    }
}

impl AgentCipherclerk {
    /// Construct from the active named profile (see [`crate::profiles`]).
    /// `Ok(None)` when no profile is configured.
    pub fn from_active_profile() -> Result<Option<Self>, ProfileError> {
        load_active()
    }

    /// Construct from a named profile in the local store.
    pub fn from_profile(name: &str) -> Result<Self, ProfileError> {
        load(name)
    }
}

impl crate::runtime::AgentRuntime {
    /// Open a runtime as the active named profile — the automatic pickup
    /// (`DREGG_PROFILE` override → the persistent `dregg id use` default).
    /// `Ok(None)` when no profile is configured.
    pub fn from_active_profile(domain: &str) -> Result<Option<Self>, ProfileError> {
        Ok(load_active()?.map(|clerk| Self::new_simple(clerk, domain)))
    }

    /// Open a runtime as a named profile from the local store.
    pub fn from_profile(name: &str, domain: &str) -> Result<Self, ProfileError> {
        Ok(Self::new_simple(load(name)?, domain))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Mutex, OnceLock};

    /// Serialize env mutation across tests (they share DREGG_HOME).
    fn env_lock() -> std::sync::MutexGuard<'static, ()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
            .lock()
            .unwrap_or_else(|e| e.into_inner())
    }

    fn with_temp_store<R>(f: impl FnOnce() -> R) -> R {
        let _guard = env_lock();
        let dir =
            std::env::temp_dir().join(format!("dregg-profile-test-{}-{}", std::process::id(), {
                let mut b = [0u8; 8];
                getrandom::fill(&mut b).unwrap();
                hex::encode(b)
            }));
        // SAFETY: guarded by env_lock; tests in this module are the only
        // mutators of DREGG_HOME / DREGG_PROFILE in this crate.
        unsafe {
            std::env::set_var("DREGG_HOME", &dir);
            std::env::remove_var(PROFILE_ENV);
        }
        let r = f();
        unsafe {
            std::env::remove_var("DREGG_HOME");
        }
        let _ = std::fs::remove_dir_all(&dir);
        r
    }

    #[test]
    fn create_list_use_load_roundtrip() {
        with_temp_store(|| {
            assert!(list().unwrap().is_empty());
            let info = create("ember").unwrap();
            assert_eq!(info.name, "ember");
            assert!(!info.active, "no active profile yet");

            // Duplicate name refused.
            assert!(matches!(
                create("ember"),
                Err(ProfileError::AlreadyExists(_))
            ));

            create("walnut").unwrap();
            set_active("walnut").unwrap();
            let listing = list().unwrap();
            assert_eq!(listing.len(), 2);
            assert!(listing.iter().any(|p| p.name == "walnut" && p.active));
            assert!(listing.iter().any(|p| p.name == "ember" && !p.active));

            // The loaded identity's key matches the recorded public key.
            let clerk = load("walnut").unwrap();
            let pk = hex::encode(clerk.public_key().0);
            let rec = listing.iter().find(|p| p.name == "walnut").unwrap();
            assert_eq!(pk, rec.public_key_hex);

            // load_active resolves the persistent default…
            let active = load_active().unwrap().expect("active set");
            assert_eq!(hex::encode(active.public_key().0), pk);

            // …and DREGG_PROFILE overrides it.
            unsafe {
                std::env::set_var(PROFILE_ENV, "ember");
            }
            let overridden = load_active().unwrap().expect("env override");
            let ember_pk = hex::encode(load("ember").unwrap().public_key().0);
            assert_eq!(hex::encode(overridden.public_key().0), ember_pk);
            unsafe {
                std::env::remove_var(PROFILE_ENV);
            }
        });
    }

    /// The golden derivation vector mirrored in `cli/src/commands/id.rs`:
    /// the CLI replicates `from_seed`'s derivation (it deliberately does not
    /// link the SDK), so a profile created by `dregg id create` must load to
    /// this exact key here. If either side drifts, both tests fail.
    #[test]
    fn derivation_matches_cli_golden_vector() {
        let mut seed = [0u8; 64];
        for (i, b) in seed.iter_mut().enumerate() {
            *b = i as u8;
        }
        let clerk = AgentCipherclerk::from_seed(seed);
        assert_eq!(
            hex::encode(clerk.public_key().0),
            "335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a",
            "SDK key derivation diverged from the CLI profile store"
        );
    }

    #[test]
    fn names_are_validated_and_loads_are_deterministic() {
        with_temp_store(|| {
            assert!(matches!(create(""), Err(ProfileError::InvalidName(_))));
            assert!(matches!(
                create("No Caps"),
                Err(ProfileError::InvalidName(_))
            ));
            assert!(matches!(
                create("../evil"),
                Err(ProfileError::InvalidName(_))
            ));
            assert!(matches!(
                set_active("ghost"),
                Err(ProfileError::NotFound(_))
            ));

            create("stable").unwrap();
            let a = load("stable").unwrap().public_key();
            let b = load("stable").unwrap().public_key();
            assert_eq!(a, b, "profile load is deterministic (same seed, same key)");
        });
    }

    #[cfg(unix)]
    #[test]
    fn profile_files_are_private() {
        use std::os::unix::fs::PermissionsExt;
        with_temp_store(|| {
            create("secretive").unwrap();
            let meta = std::fs::metadata(profile_path("secretive")).unwrap();
            assert_eq!(
                meta.permissions().mode() & 0o777,
                0o600,
                "profile key material must be 0600"
            );
        });
    }
}
