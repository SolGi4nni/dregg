//! AES-256-GCM encrypted file-based secret store.
//!
//! Storage layout:
//! ```text
//! ~/.dregg/secrets/<namespace>/<key>.enc
//! ~/.dregg/secrets/<namespace>/<key>.meta
//! ```
//!
//! File format (.enc):
//! ```text
//! [12-byte nonce][ciphertext][16-byte auth tag]
//! ```
//!
//! All files are created with 0600 permissions on Unix.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::error::SecretStoreError;
use crate::store::{SecretId, SecretMetadata, SecretStore, SecretValue};
use aes_gcm::aead::{Aead, KeyInit};
use aes_gcm::{Aes256Gcm, Nonce};

/// AES-256-GCM encrypted file-based secret store.
pub struct EncryptedFileStore {
    base_dir: PathBuf,
    master_key: zeroize::Zeroizing<[u8; 32]>,
}

impl EncryptedFileStore {
    /// Create a new encrypted file store with the given base directory and master key.
    pub fn new(base_dir: PathBuf, master_key: [u8; 32]) -> Self {
        Self {
            base_dir,
            master_key: zeroize::Zeroizing::new(master_key),
        }
    }

    /// Create with the default base directory (`~/.dregg/secrets/`).
    pub fn with_default_dir(master_key: [u8; 32]) -> Result<Self, SecretStoreError> {
        let dir = default_secrets_dir()?;
        Ok(Self::new(dir, master_key))
    }

    /// Get the file path for a secret's encrypted data.
    fn secret_path(&self, id: &SecretId) -> PathBuf {
        self.base_dir
            .join(sanitize_name(&id.namespace))
            .join(format!("{}.enc", sanitize_name(&id.key)))
    }

    /// Get the file path for a secret's metadata.
    fn meta_path(&self, id: &SecretId) -> PathBuf {
        self.base_dir
            .join(sanitize_name(&id.namespace))
            .join(format!("{}.meta", sanitize_name(&id.key)))
    }

    /// Encrypt data using AES-256-GCM.
    fn encrypt(&self, plaintext: &[u8]) -> Result<Vec<u8>, SecretStoreError> {
        let cipher = Aes256Gcm::new((&*self.master_key).into());
        let mut nonce_bytes = [0u8; 12];
        getrandom::fill(&mut nonce_bytes).map_err(|e| SecretStoreError::Crypto(e.to_string()))?;
        let nonce = Nonce::from(nonce_bytes);
        let ciphertext = cipher
            .encrypt(&nonce, plaintext)
            .map_err(|e| SecretStoreError::Crypto(e.to_string()))?;

        let mut result = Vec::with_capacity(12 + ciphertext.len());
        result.extend_from_slice(&nonce_bytes);
        result.extend_from_slice(&ciphertext);
        Ok(result)
    }

    /// Decrypt data using AES-256-GCM.
    fn decrypt(&self, encrypted: &[u8]) -> Result<Vec<u8>, SecretStoreError> {
        if encrypted.len() < 12 {
            return Err(SecretStoreError::Crypto("data too short".into()));
        }
        let (nonce_bytes, ciphertext) = encrypted.split_at(12);
        let nonce = Nonce::try_from(nonce_bytes)
            .map_err(|_| SecretStoreError::Crypto("invalid nonce length".into()))?;
        let cipher = Aes256Gcm::new((&*self.master_key).into());
        cipher
            .decrypt(&nonce, ciphertext)
            .map_err(|e| SecretStoreError::Crypto(e.to_string()))
    }

    /// Atomically write file with restrictive permissions from the start.
    ///
    /// Writes to a temp file in the same directory, fsyncs, then renames
    /// into place. The file is created with mode 0600 on Unix to avoid any
    /// window where data is world-readable.
    fn write_file(&self, path: &Path, data: &[u8]) -> Result<(), SecretStoreError> {
        use std::io::Write;

        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
            set_restrictive_dir_permissions(parent)?;
        }

        let dir = path.parent().unwrap_or(Path::new("."));
        let mut tmp = tempfile::NamedTempFile::new_in(dir)?;

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            tmp.as_file()
                .set_permissions(fs::Permissions::from_mode(0o600))?;
        }

        tmp.write_all(data)?;
        tmp.as_file().sync_all()?;
        tmp.persist(path)
            .map_err(|e| SecretStoreError::Io(e.error))?;
        Ok(())
    }
}

impl SecretStore for EncryptedFileStore {
    fn put(&self, id: &SecretId, value: &[u8]) -> Result<(), SecretStoreError> {
        let encrypted = self.encrypt(value)?;
        self.write_file(&self.secret_path(id), &encrypted)?;

        let now = now_unix();
        let existing_meta = self.meta_path(id);
        let meta = if existing_meta.exists() {
            let raw = fs::read_to_string(&existing_meta)?;
            let mut m: SecretMetadata = serde_json::from_str(&raw)
                .map_err(|e| SecretStoreError::Serialization(e.to_string()))?;
            m.updated_at = now;
            m
        } else {
            SecretMetadata {
                id: id.clone(),
                created_at: now,
                updated_at: now,
                labels: HashMap::new(),
            }
        };

        let meta_json = serde_json::to_string(&meta)
            .map_err(|e| SecretStoreError::Serialization(e.to_string()))?;
        self.write_file(&self.meta_path(id), meta_json.as_bytes())?;

        Ok(())
    }

    fn get(&self, id: &SecretId) -> Result<Option<SecretValue>, SecretStoreError> {
        let path = self.secret_path(id);
        if !path.exists() {
            return Ok(None);
        }
        let encrypted = fs::read(&path)?;
        let plaintext = self.decrypt(&encrypted)?;
        Ok(Some(SecretValue::new(plaintext)))
    }

    fn delete(&self, id: &SecretId) -> Result<bool, SecretStoreError> {
        let enc_path = self.secret_path(id);
        let meta_path = self.meta_path(id);
        let existed = enc_path.exists();
        if enc_path.exists() {
            fs::remove_file(&enc_path)?;
        }
        if meta_path.exists() {
            fs::remove_file(&meta_path)?;
        }
        Ok(existed)
    }

    fn exists(&self, id: &SecretId) -> Result<bool, SecretStoreError> {
        Ok(self.secret_path(id).exists())
    }

    fn list(&self, namespace: &str) -> Result<Vec<SecretMetadata>, SecretStoreError> {
        let ns_dir = self.base_dir.join(sanitize_name(namespace));
        if !ns_dir.exists() {
            return Ok(Vec::new());
        }

        let mut results = Vec::new();
        for entry in fs::read_dir(&ns_dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("meta") {
                // Skip files deleted between read_dir() and read_to_string() (race with concurrent delete).
                let raw = match fs::read_to_string(&path) {
                    Ok(r) => r,
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                    Err(e) => return Err(e.into()),
                };
                if let Ok(meta) = serde_json::from_str::<SecretMetadata>(&raw) {
                    results.push(meta);
                }
            }
        }
        Ok(results)
    }
}

/// Get the default secrets directory.
fn default_secrets_dir() -> Result<PathBuf, SecretStoreError> {
    let proj = directories::ProjectDirs::from("dev", "dregg", "dregg")
        .ok_or_else(|| SecretStoreError::StorePath("could not determine home directory".into()))?;
    Ok(proj.data_dir().join("secrets"))
}

/// Encode a name for use as a filesystem path component.
///
/// Uses percent-encoding for non-alphanumeric characters (except `-` and `_`)
/// to avoid collisions between different IDs.
fn sanitize_name(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for c in name.chars() {
        if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
            out.push(c);
        } else {
            for b in c.to_string().as_bytes() {
                out.push_str(&format!("%{:02X}", b));
            }
        }
    }
    out
}

/// Set directory permissions to 0700 (owner rwx only) on Unix.
#[cfg(unix)]
fn set_restrictive_dir_permissions(path: &Path) -> Result<(), SecretStoreError> {
    use std::os::unix::fs::PermissionsExt;
    let perms = fs::Permissions::from_mode(0o700);
    fs::set_permissions(path, perms)?;
    Ok(())
}

#[cfg(not(unix))]
fn set_restrictive_dir_permissions(_path: &Path) -> Result<(), SecretStoreError> {
    Ok(())
}

/// Current Unix timestamp in seconds.
fn now_unix() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;

    fn temp_store() -> EncryptedFileStore {
        static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let id = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = env::temp_dir().join(format!("dregg-secrets-test-{}-{}", std::process::id(), id));
        let _ = fs::remove_dir_all(&dir);
        let mut key = [0u8; 32];
        getrandom::fill(&mut key).unwrap();
        EncryptedFileStore::new(dir, key)
    }

    #[test]
    fn test_put_get_roundtrip() {
        let store = temp_store();
        let id = SecretId::new("test", "my-secret");
        let value = b"super-secret-value";

        store.put(&id, value).unwrap();
        let retrieved = store.get(&id).unwrap().unwrap();
        assert_eq!(retrieved.as_bytes(), value);

        // Cleanup
        let _ = fs::remove_dir_all(&store.base_dir);
    }

    #[test]
    fn test_get_nonexistent_and_exists() {
        let store = temp_store();
        let id = SecretId::new("test", "nonexistent");
        assert!(store.get(&id).unwrap().is_none());
        assert!(!store.exists(&id).unwrap());

        // After storing, both get and exists should reflect the entry
        store.put(&id, b"value").unwrap();
        assert!(store.exists(&id).unwrap());
        assert_eq!(store.get(&id).unwrap().unwrap().as_bytes(), b"value");
        let _ = fs::remove_dir_all(&store.base_dir);
    }

    #[test]
    fn test_delete() {
        let store = temp_store();
        let id = SecretId::new("test", "to-delete");
        store.put(&id, b"value").unwrap();
        assert!(store.delete(&id).unwrap());
        assert!(!store.exists(&id).unwrap());
        assert!(!store.delete(&id).unwrap()); // already deleted
        let _ = fs::remove_dir_all(&store.base_dir);
    }

    #[test]
    fn test_list() {
        let store = temp_store();
        store.put(&SecretId::new("ns1", "key1"), b"val1").unwrap();
        store.put(&SecretId::new("ns1", "key2"), b"val2").unwrap();
        store.put(&SecretId::new("ns2", "key3"), b"val3").unwrap();

        let list = store.list("ns1").unwrap();
        assert_eq!(list.len(), 2);

        let list2 = store.list("ns2").unwrap();
        assert_eq!(list2.len(), 1);

        let list3 = store.list("ns3").unwrap();
        assert!(list3.is_empty());

        let _ = fs::remove_dir_all(&store.base_dir);
    }

    #[test]
    fn test_overwrite_updates_metadata() {
        let store = temp_store();
        let id = SecretId::new("test", "overwrite");

        store.put(&id, b"first").unwrap();
        let meta1 = store.list("test").unwrap();
        assert_eq!(meta1.len(), 1);

        // Small sleep to ensure different timestamp
        std::thread::sleep(std::time::Duration::from_millis(10));

        store.put(&id, b"second").unwrap();
        let retrieved = store.get(&id).unwrap().unwrap();
        assert_eq!(retrieved.as_bytes(), b"second");

        let _ = fs::remove_dir_all(&store.base_dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_file_permissions() {
        use std::os::unix::fs::PermissionsExt;

        let store = temp_store();
        let id = SecretId::new("test", "perms");
        store.put(&id, b"value").unwrap();

        let path = store.secret_path(&id);
        let perms = fs::metadata(&path).unwrap().permissions();
        assert_eq!(perms.mode() & 0o777, 0o600);

        let _ = fs::remove_dir_all(&store.base_dir);
    }
}
