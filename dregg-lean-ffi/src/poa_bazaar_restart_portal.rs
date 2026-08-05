//! Exact-byte durability substrate for Path of Angels' Lean-owned Bazaar state.
//!
//! This module deliberately does not know the shape of `BazaarGame.StateKey`.
//! The only admissible payload is a bounded, non-empty canonical state image
//! emitted by Lean.  Persistence compares the complete image byte-for-byte;
//! it never substitutes a digest, reconstructs a partial Rust state, or runs a
//! second copy of the Bazaar transition semantics.
//!
//! The wire formats are fixed and versioned.  A stored head is checksummed for
//! crash/corruption detection, and a successful compare-and-swap is durable
//! before it is reported: write + file `sync_all`, atomic rename, then parent
//! directory `sync_all`.  A process crash while holding the create-new lock
//! leaves a fail-closed lock file for operator recovery rather than risking a
//! second writer.
//!
//! This is the native engine behind the future
//! `dregg_poa_bazaar_perform_cas` and durable-load portals.  The dependent Lean
//! ABI still needs a Lean-owned `StateKey` byte codec and thin glue; do not call
//! this file alone an implementation of either extern.

use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

const REQUEST_MAGIC: &[u8; 8] = b"POACASR1";
const HEAD_MAGIC: &[u8; 8] = b"POAHEAD1";
const WIRE_VERSION: u16 = 1;
const REQUEST_CHECKSUM_DOMAIN: &str = "dregg.poa-bazaar.cas-request.v1";
const HEAD_CHECKSUM_DOMAIN: &str = "dregg.poa-bazaar.durable-head.v1";
const HEAD_FILE: &str = "bazaar-head-v1.bin";
const LOCK_FILE: &str = "bazaar-head-v1.lock";
const TEMP_PREFIX: &str = ".bazaar-head-v1.tmp";

/// A generous hard ceiling against hostile or corrupt allocation lengths.
/// It is a wire bound, not a claim about the current semantic state size.
pub const MAX_CANONICAL_STATE_BYTES: usize = 16 * 1024 * 1024;
const MAX_REQUEST_WIRE_BYTES: usize = 8 + 2 + 1 + 4 + 4 + MAX_CANONICAL_STATE_BYTES * 2 + 32;

/// Opaque bytes reserved for a complete Lean-emitted `StateKey` image.
///
/// This type does not infer canonicality from byte content. Its constructor is
/// crate-visible so only the eventual Lean bridge (and this crate's tests) can
/// assert that provenance; downstream callers cannot bless arbitrary bytes.
#[derive(Clone, PartialEq, Eq)]
pub struct CanonicalStateBytes(Vec<u8>);

impl CanonicalStateBytes {
    fn new_checked(bytes: Vec<u8>) -> Result<Self, BazaarRestartError> {
        validate_state_len(bytes.len())?;
        Ok(Self(bytes))
    }

    #[cfg(test)]
    pub(crate) fn new(bytes: Vec<u8>) -> Result<Self, BazaarRestartError> {
        Self::new_checked(bytes)
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.0
    }
}

impl fmt::Debug for CanonicalStateBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CanonicalStateBytes")
            .field("len", &self.0.len())
            .field("digest", &blake3::hash(&self.0).to_hex().as_str())
            .finish()
    }
}

/// Exact request produced from Lean's dependent `RuntimeCasRequest`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BazaarCasRequest {
    expected: Option<CanonicalStateBytes>,
    replacement: CanonicalStateBytes,
}

impl BazaarCasRequest {
    fn new_checked(
        expected: Option<CanonicalStateBytes>,
        replacement: CanonicalStateBytes,
    ) -> Self {
        Self {
            expected,
            replacement,
        }
    }

    #[cfg(test)]
    pub(crate) fn new(
        expected: Option<CanonicalStateBytes>,
        replacement: CanonicalStateBytes,
    ) -> Self {
        Self::new_checked(expected, replacement)
    }

    pub fn expected(&self) -> Option<&CanonicalStateBytes> {
        self.expected.as_ref()
    }

    pub fn replacement(&self) -> &CanonicalStateBytes {
        &self.replacement
    }

    fn encode_wire_bytes(&self) -> Vec<u8> {
        let expected_len = self.expected.as_ref().map_or(0, |value| value.0.len());
        let mut out =
            Vec::with_capacity(8 + 2 + 1 + 4 + 4 + expected_len + self.replacement.0.len() + 32);
        out.extend_from_slice(REQUEST_MAGIC);
        out.extend_from_slice(&WIRE_VERSION.to_be_bytes());
        out.push(u8::from(self.expected.is_some()));
        out.extend_from_slice(&(expected_len as u32).to_be_bytes());
        out.extend_from_slice(&(self.replacement.0.len() as u32).to_be_bytes());
        if let Some(expected) = &self.expected {
            out.extend_from_slice(&expected.0);
        }
        out.extend_from_slice(&self.replacement.0);
        append_checksum(&mut out, REQUEST_CHECKSUM_DOMAIN);
        out
    }

    #[cfg(test)]
    pub(crate) fn to_wire_bytes(&self) -> Vec<u8> {
        self.encode_wire_bytes()
    }

    fn decode_wire_bytes(bytes: &[u8]) -> Result<Self, BazaarRestartError> {
        if bytes.len() > MAX_REQUEST_WIRE_BYTES {
            return Err(BazaarRestartError::InvalidWire("request exceeds maximum"));
        }
        let body = checked_body(bytes, REQUEST_CHECKSUM_DOMAIN)?;
        let mut cursor = 0usize;
        if take::<8>(body, &mut cursor)? != *REQUEST_MAGIC {
            return Err(BazaarRestartError::InvalidWire("request magic"));
        }
        if u16::from_be_bytes(take::<2>(body, &mut cursor)?) != WIRE_VERSION {
            return Err(BazaarRestartError::InvalidWire("request version"));
        }
        let expected_present = match take::<1>(body, &mut cursor)?[0] {
            0 => false,
            1 => true,
            _ => return Err(BazaarRestartError::InvalidWire("request option tag")),
        };
        let expected_len = decode_len(body, &mut cursor)?;
        let replacement_len = decode_len(body, &mut cursor)?;
        if expected_present != (expected_len != 0) {
            return Err(BazaarRestartError::InvalidWire(
                "request expected tag/length mismatch",
            ));
        }
        if expected_present {
            validate_state_len(expected_len)?;
        }
        validate_state_len(replacement_len)?;
        let expected = if expected_present {
            Some(CanonicalStateBytes(take_vec(
                body,
                &mut cursor,
                expected_len,
            )?))
        } else {
            None
        };
        let replacement = CanonicalStateBytes(take_vec(body, &mut cursor, replacement_len)?);
        if cursor != body.len() {
            return Err(BazaarRestartError::InvalidWire("request trailing bytes"));
        }
        Ok(Self {
            expected,
            replacement,
        })
    }

    #[cfg(test)]
    pub(crate) fn from_wire_bytes(bytes: &[u8]) -> Result<Self, BazaarRestartError> {
        Self::decode_wire_bytes(bytes)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BazaarCasOutcome {
    Applied {
        previous: Option<CanonicalStateBytes>,
        current: CanonicalStateBytes,
    },
    Stale {
        observed: Option<CanonicalStateBytes>,
    },
}

#[derive(Debug)]
pub enum BazaarRestartError {
    InvalidWire(&'static str),
    Busy,
    UnsafePath(&'static str),
    Io(io::Error),
}

impl fmt::Display for BazaarRestartError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidWire(reason) => write!(f, "invalid Bazaar restart wire: {reason}"),
            Self::Busy => write!(f, "Bazaar head is locked by another writer or recovery"),
            Self::UnsafePath(reason) => write!(f, "unsafe Bazaar store path: {reason}"),
            Self::Io(error) => write!(f, "Bazaar restart I/O error: {error}"),
        }
    }
}

impl std::error::Error for BazaarRestartError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            _ => None,
        }
    }
}

impl From<io::Error> for BazaarRestartError {
    fn from(value: io::Error) -> Self {
        Self::Io(value)
    }
}

/// One deployment's exact canonical Bazaar head.
#[derive(Clone, Debug)]
pub struct DurableBazaarHeadStore {
    root: PathBuf,
}

impl DurableBazaarHeadStore {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, BazaarRestartError> {
        let root = root.as_ref();
        match fs::symlink_metadata(root) {
            Ok(metadata) => {
                if metadata.file_type().is_symlink() {
                    return Err(BazaarRestartError::UnsafePath("root is a symlink"));
                }
                if !metadata.is_dir() {
                    return Err(BazaarRestartError::UnsafePath("root is not a directory"));
                }
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                fs::create_dir_all(root)?;
                let metadata = fs::symlink_metadata(root)?;
                if metadata.file_type().is_symlink() || !metadata.is_dir() {
                    return Err(BazaarRestartError::UnsafePath(
                        "created root is not a real directory",
                    ));
                }
            }
            Err(error) => return Err(error.into()),
        }
        Ok(Self {
            root: root.to_path_buf(),
        })
    }

    pub fn load(&self) -> Result<Option<CanonicalStateBytes>, BazaarRestartError> {
        let path = self.root.join(HEAD_FILE);
        let file = match open_regular_nofollow(&path) {
            Ok(file) => file,
            Err(BazaarRestartError::Io(error)) if error.kind() == io::ErrorKind::NotFound => {
                return Ok(None);
            }
            Err(error) => return Err(error),
        };
        let maximum = 8 + 2 + 4 + MAX_CANONICAL_STATE_BYTES + 32;
        let mut bytes = Vec::new();
        file.take((maximum + 1) as u64).read_to_end(&mut bytes)?;
        if bytes.len() > maximum {
            return Err(BazaarRestartError::InvalidWire("head exceeds maximum"));
        }
        decode_head(&bytes).map(Some)
    }

    /// Compare the complete expected canonical image and durably install the
    /// complete replacement. `expected = None` succeeds only at genesis.
    pub fn compare_and_swap(
        &self,
        request: &BazaarCasRequest,
    ) -> Result<BazaarCasOutcome, BazaarRestartError> {
        let lock = WriterLock::acquire(&self.root)?;
        let observed = self.load()?;
        if observed.as_ref() != request.expected.as_ref() {
            return Ok(BazaarCasOutcome::Stale { observed });
        }

        let bytes = encode_head(&request.replacement);
        let temp = self.root.join(format!(
            "{TEMP_PREFIX}.{}.{}",
            std::process::id(),
            unique_nonce()
        ));
        let write_result = (|| -> Result<(), BazaarRestartError> {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temp)?;
            file.write_all(&bytes)?;
            file.sync_all()?;
            fs::rename(&temp, self.root.join(HEAD_FILE))?;
            File::open(&self.root)?.sync_all()?;
            Ok(())
        })();
        if write_result.is_err() {
            let _ = fs::remove_file(&temp);
        }
        write_result?;
        drop(lock);

        Ok(BazaarCasOutcome::Applied {
            previous: observed,
            current: request.replacement.clone(),
        })
    }
}

struct WriterLock {
    path: PathBuf,
    _file: File,
}

impl WriterLock {
    fn acquire(root: &Path) -> Result<Self, BazaarRestartError> {
        let path = root.join(LOCK_FILE);
        let mut file = match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                return Err(BazaarRestartError::Busy);
            }
            Err(error) => return Err(error.into()),
        };
        file.write_all(format!("{}\n", std::process::id()).as_bytes())?;
        file.sync_all()?;
        File::open(root)?.sync_all()?;
        Ok(Self { path, _file: file })
    }
}

impl Drop for WriterLock {
    fn drop(&mut self) {
        if fs::remove_file(&self.path).is_ok() {
            if let Some(root) = self.path.parent() {
                let _ = File::open(root).and_then(|directory| directory.sync_all());
            }
        }
    }
}

fn encode_head(state: &CanonicalStateBytes) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + 2 + 4 + state.0.len() + 32);
    out.extend_from_slice(HEAD_MAGIC);
    out.extend_from_slice(&WIRE_VERSION.to_be_bytes());
    out.extend_from_slice(&(state.0.len() as u32).to_be_bytes());
    out.extend_from_slice(&state.0);
    append_checksum(&mut out, HEAD_CHECKSUM_DOMAIN);
    out
}

fn decode_head(bytes: &[u8]) -> Result<CanonicalStateBytes, BazaarRestartError> {
    let body = checked_body(bytes, HEAD_CHECKSUM_DOMAIN)?;
    let mut cursor = 0usize;
    if take::<8>(body, &mut cursor)? != *HEAD_MAGIC {
        return Err(BazaarRestartError::InvalidWire("head magic"));
    }
    if u16::from_be_bytes(take::<2>(body, &mut cursor)?) != WIRE_VERSION {
        return Err(BazaarRestartError::InvalidWire("head version"));
    }
    let len = decode_len(body, &mut cursor)?;
    validate_state_len(len)?;
    let state = CanonicalStateBytes(take_vec(body, &mut cursor, len)?);
    if cursor != body.len() {
        return Err(BazaarRestartError::InvalidWire("head trailing bytes"));
    }
    Ok(state)
}

fn validate_state_len(len: usize) -> Result<(), BazaarRestartError> {
    if len == 0 {
        Err(BazaarRestartError::InvalidWire("empty canonical state"))
    } else if len > MAX_CANONICAL_STATE_BYTES {
        Err(BazaarRestartError::InvalidWire(
            "canonical state exceeds maximum",
        ))
    } else {
        Ok(())
    }
}

fn append_checksum(bytes: &mut Vec<u8>, domain: &str) {
    let digest = blake3::derive_key(domain, bytes);
    bytes.extend_from_slice(&digest);
}

fn checked_body<'a>(bytes: &'a [u8], domain: &str) -> Result<&'a [u8], BazaarRestartError> {
    if bytes.len() < 32 {
        return Err(BazaarRestartError::InvalidWire("truncated checksum"));
    }
    let (body, checksum) = bytes.split_at(bytes.len() - 32);
    if blake3::derive_key(domain, body).as_slice() != checksum {
        return Err(BazaarRestartError::InvalidWire("checksum"));
    }
    Ok(body)
}

fn decode_len(bytes: &[u8], cursor: &mut usize) -> Result<usize, BazaarRestartError> {
    Ok(u32::from_be_bytes(take::<4>(bytes, cursor)?) as usize)
}

fn take<const N: usize>(bytes: &[u8], cursor: &mut usize) -> Result<[u8; N], BazaarRestartError> {
    let end = cursor
        .checked_add(N)
        .filter(|end| *end <= bytes.len())
        .ok_or(BazaarRestartError::InvalidWire("truncated field"))?;
    let value = bytes[*cursor..end]
        .try_into()
        .map_err(|_| BazaarRestartError::InvalidWire("field width"))?;
    *cursor = end;
    Ok(value)
}

fn take_vec(bytes: &[u8], cursor: &mut usize, len: usize) -> Result<Vec<u8>, BazaarRestartError> {
    let end = cursor
        .checked_add(len)
        .filter(|end| *end <= bytes.len())
        .ok_or(BazaarRestartError::InvalidWire("truncated payload"))?;
    let value = bytes[*cursor..end].to_vec();
    *cursor = end;
    Ok(value)
}

#[cfg(unix)]
fn open_regular_nofollow(path: &Path) -> Result<File, BazaarRestartError> {
    use std::os::unix::fs::OpenOptionsExt;

    match fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_symlink() => {
            return Err(BazaarRestartError::UnsafePath("head is a symlink"));
        }
        Ok(metadata) if !metadata.is_file() => {
            return Err(BazaarRestartError::UnsafePath("head is not a regular file"));
        }
        Ok(_) => {}
        Err(error) => return Err(error.into()),
    }

    #[cfg(any(target_os = "linux", target_os = "android"))]
    const O_NOFOLLOW: i32 = 0x20_000;
    #[cfg(any(
        target_os = "macos",
        target_os = "ios",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd"
    ))]
    const O_NOFOLLOW: i32 = 0x100;
    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd"
    )))]
    const O_NOFOLLOW: i32 = 0;
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(O_NOFOLLOW)
        .open(path)?;
    if !file.metadata()?.is_file() {
        return Err(BazaarRestartError::UnsafePath("head is not a regular file"));
    }
    Ok(file)
}

#[cfg(not(unix))]
fn open_regular_nofollow(path: &Path) -> Result<File, BazaarRestartError> {
    let metadata = fs::symlink_metadata(path)?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(BazaarRestartError::UnsafePath("head is not a regular file"));
    }
    Ok(File::open(path)?)
}

fn unique_nonce() -> u64 {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    NEXT.fetch_add(1, Ordering::Relaxed)
}
