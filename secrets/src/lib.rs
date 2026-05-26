//! Dregg Secret Store
//!
//! Pluggable secret storage with two backends:
//!
//! - **Encrypted file store**: AES-256-GCM encrypted files in `~/.dregg/secrets/`.
//!   Portable, works everywhere. 0600 permissions on Unix.
//!
//! - **OS keychain** (feature `keychain`): Uses the platform credential manager
//!   via the `keyring` crate (macOS Keychain, Windows Credential Manager,
//!   Linux Secret Service).
//!
//! Both implement the [`SecretStore`] trait. Use [`CompositeStore`] to
//! try keychain first and fall back to encrypted files.

pub mod encrypted;
pub mod error;
#[cfg(feature = "keychain")]
pub mod keychain;
pub mod store;

// Re-export primary types.
pub use encrypted::EncryptedFileStore;
pub use error::SecretStoreError;
#[cfg(feature = "keychain")]
pub use keychain::KeychainStore;
pub use store::{CompositeStore, SecretId, SecretMetadata, SecretStore, SecretValue};
