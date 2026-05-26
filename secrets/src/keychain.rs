//! OS keychain secret store backend.
//!
//! Uses the `keyring` crate for cross-platform credential storage:
//! - **macOS**: Keychain Services
//! - **Windows**: Credential Manager
//! - **Linux**: Secret Service (D-Bus, e.g., GNOME Keyring, KWallet)

#[cfg(feature = "keychain")]
use crate::error::SecretStoreError;
#[cfg(feature = "keychain")]
use crate::store::{SecretId, SecretMetadata, SecretStore, SecretValue};
#[cfg(feature = "keychain")]
use base64::Engine;

/// OS keychain secret store.
///
/// Secrets are stored as entries in the OS credential manager with
/// service name `dev.dregg.secrets.<namespace>` and username as the key.
#[cfg(feature = "keychain")]
pub struct KeychainStore {
    service_prefix: String,
}

#[cfg(feature = "keychain")]
impl KeychainStore {
    /// Create a new keychain store with the default service prefix.
    pub fn new() -> Self {
        Self {
            service_prefix: "dev.dregg.secrets".into(),
        }
    }

    /// Create with a custom service prefix.
    pub fn with_prefix(prefix: impl Into<String>) -> Self {
        Self {
            service_prefix: prefix.into(),
        }
    }

    /// Build the keyring service name for a given namespace.
    fn service_name(&self, namespace: &str) -> String {
        format!("{}.{}", self.service_prefix, namespace)
    }

    /// Get a keyring entry for a secret.
    fn entry(&self, id: &SecretId) -> Result<keyring::Entry, SecretStoreError> {
        keyring::Entry::new(&self.service_name(&id.namespace), &id.key)
            .map_err(|e| SecretStoreError::Keychain(e.to_string()))
    }
}

#[cfg(feature = "keychain")]
impl Default for KeychainStore {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "keychain")]
impl SecretStore for KeychainStore {
    fn put(&self, id: &SecretId, value: &[u8]) -> Result<(), SecretStoreError> {
        let entry = self.entry(id)?;
        // keyring stores bytes as base64 string
        let encoded = base64::engine::general_purpose::STANDARD.encode(value);
        entry
            .set_password(&encoded)
            .map_err(|e| SecretStoreError::Keychain(e.to_string()))
    }

    fn get(&self, id: &SecretId) -> Result<Option<SecretValue>, SecretStoreError> {
        let entry = self.entry(id)?;
        match entry.get_password() {
            Ok(encoded) => {
                use base64::Engine;
                let decoded = base64::engine::general_purpose::STANDARD
                    .decode(&encoded)
                    .map_err(|e| SecretStoreError::Crypto(e.to_string()))?;
                Ok(Some(SecretValue::new(decoded)))
            }
            Err(keyring::Error::NoEntry) => Ok(None),
            Err(e) => Err(SecretStoreError::Keychain(e.to_string())),
        }
    }

    fn delete(&self, id: &SecretId) -> Result<bool, SecretStoreError> {
        let entry = self.entry(id)?;
        match entry.delete_credential() {
            Ok(()) => Ok(true),
            Err(keyring::Error::NoEntry) => Ok(false),
            Err(e) => Err(SecretStoreError::Keychain(e.to_string())),
        }
    }

    fn exists(&self, id: &SecretId) -> Result<bool, SecretStoreError> {
        let entry = self.entry(id)?;
        match entry.get_password() {
            Ok(_) => Ok(true),
            Err(keyring::Error::NoEntry) => Ok(false),
            Err(e) => Err(SecretStoreError::Keychain(e.to_string())),
        }
    }

    /// List secrets in a namespace.
    ///
    /// Returns an empty list. OS keychain APIs (Keychain Services on macOS,
    /// Credential Manager on Windows, Secret Service on Linux) do not expose
    /// a portable enumeration interface. The `keyring` crate does not support
    /// listing credentials across any platform.
    ///
    /// When used inside a [`CompositeStore`](crate::store::CompositeStore), the
    /// encrypted file backend provides listing capability. If the keychain
    /// store is used standalone, callers must maintain their own index of
    /// stored secret IDs.
    fn list(&self, _namespace: &str) -> Result<Vec<SecretMetadata>, SecretStoreError> {
        Ok(Vec::new())
    }
}
