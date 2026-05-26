# secrets

Pluggable secret storage with AES-256-GCM encrypted file backend and OS keychain
integration. Provides a unified `SecretStore` trait so the rest of the auth stack
can store and retrieve secrets without caring about the underlying backend.

## Overview

Secrets (OAuth client credentials, API keys, signing keys) need to be stored
securely at rest. This crate provides two backends behind a common trait:

- **EncryptedFileStore**: AES-256-GCM encrypted files in `~/.dregg/secrets/`.
  Portable across all platforms. Files are created with 0600 permissions on Unix.
- **KeychainStore** (feature `keychain`): Delegates to the OS credential manager
  via the `keyring` crate (macOS Keychain, Windows Credential Manager, Linux
  Secret Service / D-Bus).

Use `CompositeStore` to try the keychain first and fall back to encrypted files.

## Key Types

| Type | Description |
|------|-------------|
| `SecretStore` | Trait: `put`, `get`, `delete`, `exists`, `list` |
| `EncryptedFileStore` | AES-256-GCM file backend at a given directory |
| `KeychainStore` | OS keychain backend (behind `keychain` feature) |
| `CompositeStore` | Tries multiple backends in order (write to all, read first match) |
| `SecretId` | Namespaced key identifier (e.g., `oauth/github:client_secret`) |
| `SecretValue` | Zeroize-on-drop byte buffer with `as_bytes()` / `as_str()` accessors |
| `SecretMetadata` | ID, timestamps, user-defined labels |

## Features

| Feature | Default | Description |
|---------|---------|-------------|
| `keychain` | yes | Enables OS keychain backend via `keyring` crate |

## Usage

```rust
use dregg_secrets::{EncryptedFileStore, SecretId, SecretStore};
use std::path::PathBuf;

// Create an encrypted file store with a 256-bit master key
let master_key: [u8; 32] = /* derive or load your master key */;
let store = EncryptedFileStore::new(
    PathBuf::from("/home/user/.dregg/secrets"),
    master_key,
)?;

// Store a secret
let id = SecretId::new("oauth", "github:client_secret");
store.put(&id, b"ghp_xxxxxxxxxxxx")?;

// Retrieve it
if let Some(value) = store.get(&id)? {
    let secret_str = value.as_str().unwrap();
    // Use the secret...
    // SecretValue is automatically zeroized when dropped
}

// List all secrets in a namespace
let entries = store.list("oauth")?;
for meta in &entries {
    println!("{} (updated: {})", meta.id, meta.updated_at);
}

// Delete
store.delete(&id)?;
```

### Composite Store

```rust
use dregg_secrets::{CompositeStore, EncryptedFileStore, KeychainStore};

let composite = CompositeStore::new(vec![
    Box::new(KeychainStore::new()),
    Box::new(EncryptedFileStore::new(path, key)?),
]);

// Writes go to ALL backends; reads return the first match
composite.put(&id, b"secret")?;
```

## Security Model

- AES-256-GCM with unique random nonces per encryption operation
- `SecretValue` implements `ZeroizeOnDrop` -- memory is cleared when the value
  goes out of scope
- Files are created with restrictive permissions (0600 on Unix)
- Debug output redacts secret contents (`SecretValue([REDACTED, N bytes])`)

## Architecture

This crate is used by the auth service to persist OAuth credentials and other
secrets. The `AuthService` holds an `Arc<dyn SecretStore>` and exposes secret
operations over Cap'n Proto RPC (methods 30-33).

```
secrets (this crate)
  -> auth (AuthService holds Arc<dyn SecretStore>)
    -> sidecar (IPC daemon)
    -> tokenizer (proxy reads sealed secrets)
```

## Tests

7 tests covering put/get/delete round-trips, existence checks, listing, and
overwrite behavior.

```sh
cargo test -p secrets
```
