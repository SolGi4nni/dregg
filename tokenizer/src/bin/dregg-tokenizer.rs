//! dregg-tokenizer — key custody daemon for sealed secrets.
//!
//! Listens on a Unix domain socket and serves Seal/Unseal/Rotate operations.
//! The private key never leaves this process.
//!
//! Usage:
//!   dregg-tokenizer [--socket <path>] [--key-store <path>]

use std::path::PathBuf;

use dregg_tokenizer::service::{KeyRing, ServiceConfig, TokenizerService};

fn parse_args() -> ServiceConfig {
    let mut config = ServiceConfig::default();
    let args: Vec<String> = std::env::args().collect();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--socket" | "-s" => {
                i += 1;
                if i < args.len() {
                    config.socket_path = PathBuf::from(&args[i]);
                }
            }
            "--key-store" | "-k" => {
                i += 1;
                if i < args.len() {
                    config.key_store_path = PathBuf::from(&args[i]);
                }
            }
            "--help" | "-h" => {
                eprintln!("dregg-tokenizer — key custody daemon");
                eprintln!();
                eprintln!("Usage: dregg-tokenizer [OPTIONS]");
                eprintln!();
                eprintln!("Options:");
                eprintln!(
                    "  -s, --socket <PATH>     Unix socket path (default: /tmp/dregg-tokenizer.sock)"
                );
                eprintln!(
                    "  -k, --key-store <PATH>  Key store file path (default: ~/.dregg/tokenizer-keys)"
                );
                eprintln!("  -h, --help              Show this help");
                std::process::exit(0);
            }
            other => {
                eprintln!("unknown argument: {}", other);
                std::process::exit(1);
            }
        }
        i += 1;
    }
    config
}

/// Load or generate the key ring from disk.
///
/// The key store is a simple binary file:
///   [4-byte LE key count][32-byte key 1][32-byte key 2]...
fn load_or_generate_keyring(path: &std::path::Path) -> KeyRing {
    if let Ok(data) = std::fs::read(path) {
        if data.len() >= 4 {
            let count = u32::from_le_bytes(data[0..4].try_into().unwrap()) as usize;
            let expected_len = 4 + count * 32;
            if data.len() == expected_len && count > 0 {
                let mut keys = Vec::with_capacity(count);
                for i in 0..count {
                    let offset = 4 + i * 32;
                    let mut key = [0u8; 32];
                    key.copy_from_slice(&data[offset..offset + 32]);
                    keys.push(key);
                }
                eprintln!(
                    "[tokenizer] loaded {} key(s) from {}",
                    count,
                    path.display()
                );
                return KeyRing::from_stored_keys(keys);
            }
        }
        eprintln!(
            "[tokenizer] key store at {} is corrupt, generating new key",
            path.display()
        );
    } else {
        eprintln!(
            "[tokenizer] no key store at {}, generating new key",
            path.display()
        );
    }

    let ring = KeyRing::generate();
    save_keyring(path, &ring);
    ring
}

/// Persist the key ring to disk.
fn save_keyring(path: &std::path::Path, _ring: &KeyRing) {
    // We can't extract raw bytes from KeyRing directly, but we'll re-serialize
    // at startup from the config. For the initial generation, we note that the
    // ring was just generated. A full implementation would serialize via the
    // secrets crate; for now we create the placeholder.
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    // Note: In a production implementation, this would use dregg-secrets to
    // encrypt the key material at rest. For the initial daemon scaffolding,
    // we acknowledge this TODO.
    eprintln!(
        "[tokenizer] key store persistence at {} (placeholder — use dregg-secrets in production)",
        path.display()
    );
}

#[tokio::main]
async fn main() {
    let config = parse_args();

    eprintln!("[tokenizer] dregg-tokenizer starting");
    eprintln!("[tokenizer] socket: {}", config.socket_path.display());
    eprintln!("[tokenizer] key store: {}", config.key_store_path.display());

    let keyring = load_or_generate_keyring(&config.key_store_path);
    let service = TokenizerService::new(config, keyring);

    // Handle Ctrl+C gracefully.
    let service_ref = &service;
    tokio::select! {
      result = service_ref.serve() => {
        if let Err(e) = result {
          eprintln!("[tokenizer] fatal error: {}", e);
          std::process::exit(1);
        }
      }
      _ = tokio::signal::ctrl_c() => {
        eprintln!("[tokenizer] received SIGINT, shutting down");
        service_ref.shutdown();
      }
    }
}
