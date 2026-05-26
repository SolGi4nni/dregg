//! Atomic JSON file persistence for dregg app state.
//!
//! Provides [`JsonPersistence`], a simple helper that serializes state to a JSON
//! file using an atomic write-then-rename strategy. This prevents corruption from
//! partial writes on crash.
//!
//! # Usage
//!
//! ```ignore
//! use dregg_app_framework::persistence::JsonPersistence;
//!
//! #[derive(serde::Serialize, serde::Deserialize)]
//! struct MyState { counter: u64 }
//!
//! let persist = JsonPersistence::new("/tmp/my-app/state.json");
//! persist.initialize().unwrap();
//!
//! // Save state atomically
//! persist.save(&MyState { counter: 42 }).unwrap();
//!
//! // Load state on startup
//! let loaded: Option<MyState> = persist.load().unwrap();
//! ```

use serde::{Deserialize, Serialize};
use std::io;
use std::path::{Path, PathBuf};

// =============================================================================
// JsonPersistence
// =============================================================================

/// Atomic JSON file persistence.
///
/// Writes go to a temporary `.tmp` sibling file, then are renamed into place
/// (atomic on POSIX). Reads deserialize from the target path.
#[derive(Clone, Debug)]
pub struct JsonPersistence {
    /// The target file path for the state.
    path: PathBuf,
}

impl JsonPersistence {
    /// Create a new persistence helper for the given file path.
    ///
    /// Does NOT create directories or files -- call [`Self::initialize`] to ensure
    /// the parent directory exists and is writable.
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Self { path: path.into() }
    }

    /// Create from an optional path. Returns `None` if the path is `None`
    /// (persistence disabled).
    pub fn from_optional(path: Option<impl Into<PathBuf>>) -> Option<Self> {
        path.map(|p| Self::new(p))
    }

    /// Ensure the parent directory exists and is writable.
    ///
    /// Call this at startup before any save/load operations.
    pub fn initialize(&self) -> Result<(), io::Error> {
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        // Test writability by touching the tmp file.
        let tmp = self.tmp_path();
        std::fs::write(&tmp, b"dregg-persistence-init")?;
        std::fs::remove_file(&tmp)?;
        Ok(())
    }

    /// Save state atomically: serialize to JSON, write to .tmp file, rename into place.
    pub fn save<T: Serialize>(&self, state: &T) -> Result<(), PersistError> {
        let json = serde_json::to_string_pretty(state)
            .map_err(|e| PersistError::Serialize(e.to_string()))?;
        let tmp = self.tmp_path();
        std::fs::write(&tmp, json.as_bytes()).map_err(PersistError::Io)?;
        std::fs::rename(&tmp, &self.path).map_err(PersistError::Io)?;
        Ok(())
    }

    /// Load state from the file. Returns `Ok(None)` if the file does not exist.
    pub fn load<T: for<'de> Deserialize<'de>>(&self) -> Result<Option<T>, PersistError> {
        match std::fs::read_to_string(&self.path) {
            Ok(contents) => {
                let value = serde_json::from_str(&contents)
                    .map_err(|e| PersistError::Deserialize(e.to_string()))?;
                Ok(Some(value))
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(PersistError::Io(e)),
        }
    }

    /// Check whether the state file exists on disk.
    pub fn exists(&self) -> bool {
        self.path.exists()
    }

    /// Return the path to the state file.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Compute the temporary file path (sibling with `.tmp` extension).
    fn tmp_path(&self) -> PathBuf {
        let mut tmp = self.path.clone();
        let name = tmp
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .into_owned();
        tmp.set_file_name(format!("{name}.tmp"));
        tmp
    }
}

// =============================================================================
// Error type
// =============================================================================

/// Errors from persistence operations.
#[derive(Debug)]
pub enum PersistError {
    /// Filesystem I/O error.
    Io(io::Error),
    /// Serialization failed.
    Serialize(String),
    /// Deserialization failed (corrupt or incompatible state file).
    Deserialize(String),
}

impl std::fmt::Display for PersistError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "persistence I/O error: {e}"),
            Self::Serialize(e) => write!(f, "serialization error: {e}"),
            Self::Deserialize(e) => write!(f, "deserialization error: {e}"),
        }
    }
}

impl std::error::Error for PersistError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<io::Error> for PersistError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

// =============================================================================
// Auto-persist wrapper (save on every mutation)
// =============================================================================

/// A wrapper that auto-persists state to disk after every mutable access.
///
/// Useful for apps that want "save on every write" semantics without manually
/// calling `persist.save()` after each mutation.
///
/// # Usage
///
/// ```ignore
/// use dregg_app_framework::persistence::{AutoPersist, JsonPersistence};
///
/// let persist = JsonPersistence::new("/tmp/state.json");
/// let mut ap = AutoPersist::new(MyState::default(), persist);
///
/// // Mutate and auto-save:
/// ap.mutate(|state| state.counter += 1).unwrap();
/// ```
pub struct AutoPersist<T: Serialize + for<'de> Deserialize<'de>> {
    state: T,
    persistence: JsonPersistence,
}

impl<T: Serialize + for<'de> Deserialize<'de>> AutoPersist<T> {
    /// Create a new auto-persist wrapper.
    pub fn new(state: T, persistence: JsonPersistence) -> Self {
        Self { state, persistence }
    }

    /// Load from disk (or use default) and create an auto-persist wrapper.
    pub fn load_or(default: T, persistence: JsonPersistence) -> Result<Self, PersistError> {
        let state = persistence.load::<T>()?.unwrap_or(default);
        Ok(Self { state, persistence })
    }

    /// Read-only access to the state.
    pub fn get(&self) -> &T {
        &self.state
    }

    /// Mutate the state and persist to disk.
    pub fn mutate(&mut self, f: impl FnOnce(&mut T)) -> Result<(), PersistError> {
        f(&mut self.state);
        self.persistence.save(&self.state)
    }

    /// Force a save without mutation (e.g. after bulk operations).
    pub fn flush(&self) -> Result<(), PersistError> {
        self.persistence.save(&self.state)
    }

    /// Get the underlying persistence handle.
    pub fn persistence(&self) -> &JsonPersistence {
        &self.persistence
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    struct TestState {
        counter: u64,
        name: String,
    }

    #[test]
    fn save_and_load_roundtrip() {
        let dir = std::env::temp_dir().join("dregg-persist-test-roundtrip");
        let _ = std::fs::remove_dir_all(&dir);
        let path = dir.join("state.json");

        let persist = JsonPersistence::new(&path);
        persist.initialize().unwrap();

        let state = TestState {
            counter: 42,
            name: "hello".into(),
        };
        persist.save(&state).unwrap();

        let loaded: Option<TestState> = persist.load().unwrap();
        assert_eq!(loaded, Some(state));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn load_missing_returns_none() {
        let path = std::env::temp_dir().join("dregg-persist-test-missing/state.json");
        let persist = JsonPersistence::new(&path);
        let loaded: Result<Option<TestState>, _> = persist.load();
        assert!(loaded.unwrap().is_none());
    }

    #[test]
    fn auto_persist_mutate_saves() {
        let dir = std::env::temp_dir().join("dregg-persist-test-auto");
        let _ = std::fs::remove_dir_all(&dir);
        let path = dir.join("state.json");

        let persist = JsonPersistence::new(&path);
        persist.initialize().unwrap();

        let mut ap = AutoPersist::new(
            TestState {
                counter: 0,
                name: "start".into(),
            },
            persist.clone(),
        );

        ap.mutate(|s| s.counter = 99).unwrap();

        // Reload from disk to verify it was saved.
        let loaded: TestState = persist.load().unwrap().unwrap();
        assert_eq!(loaded.counter, 99);

        let _ = std::fs::remove_dir_all(&dir);
    }
}
