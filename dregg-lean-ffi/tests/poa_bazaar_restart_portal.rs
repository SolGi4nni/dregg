#[path = "../src/poa_bazaar_restart_portal.rs"]
mod portal;

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Barrier};

use dregg_lean_ffi::poa_bazaar_restart_portal::DurableBazaarHeadStore as RegisteredDurableBazaarHeadStore;
use portal::{
    BazaarCasOutcome, BazaarCasRequest, BazaarRestartError, CanonicalStateBytes,
    DurableBazaarHeadStore, MAX_CANONICAL_STATE_BYTES,
};

const REQUEST_CHECKSUM_DOMAIN: &str = "dregg.poa-bazaar.cas-request.v1";
const HEAD_CHECKSUM_DOMAIN: &str = "dregg.poa-bazaar.durable-head.v1";

struct ScratchDir(PathBuf);

impl ScratchDir {
    fn new(label: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "dregg-poa-bazaar-{label}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).expect("create isolated Bazaar test directory");
        Self(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn state(bytes: &[u8]) -> CanonicalStateBytes {
    CanonicalStateBytes::new(bytes.to_vec()).expect("bounded non-empty state")
}

fn reseal_request(mut bytes: Vec<u8>) -> Vec<u8> {
    bytes.truncate(bytes.len() - 32);
    let checksum = blake3::derive_key(REQUEST_CHECKSUM_DOMAIN, &bytes);
    bytes.extend_from_slice(&checksum);
    bytes
}

fn reseal_head(mut bytes: Vec<u8>) -> Vec<u8> {
    bytes.truncate(bytes.len() - 32);
    let checksum = blake3::derive_key(HEAD_CHECKSUM_DOMAIN, &bytes);
    bytes.extend_from_slice(&checksum);
    bytes
}

#[test]
fn production_restart_portal_is_registered_and_opens_an_empty_store() {
    let scratch = ScratchDir::new("registered-module");
    let store = RegisteredDurableBazaarHeadStore::open(scratch.path()).unwrap();
    assert_eq!(store.load().unwrap(), None);
}

#[test]
fn fixed_request_codec_roundtrips_genesis_and_successor_exactly() {
    let genesis = BazaarCasRequest::new(None, state(b"lean-state-v1:genesis"));
    let genesis_wire = genesis.to_wire_bytes();
    assert_eq!(
        BazaarCasRequest::from_wire_bytes(&genesis_wire).unwrap(),
        genesis
    );
    assert_eq!(genesis_wire, genesis.to_wire_bytes());

    let successor = BazaarCasRequest::new(
        Some(state(b"lean-state-v1:genesis")),
        state(b"lean-state-v1:revision-2\0with-full-tail"),
    );
    let successor_wire = successor.to_wire_bytes();
    assert_eq!(
        BazaarCasRequest::from_wire_bytes(&successor_wire).unwrap(),
        successor
    );
    assert_eq!(successor_wire, successor.to_wire_bytes());
}

#[test]
fn request_decoder_refuses_checksum_version_option_length_trailing_and_bounds_lies() {
    let request = BazaarCasRequest::new(Some(state(b"before")), state(b"after"));
    let original = request.to_wire_bytes();

    let mut bad_checksum = original.clone();
    bad_checksum[18] ^= 1;
    assert!(matches!(
        BazaarCasRequest::from_wire_bytes(&bad_checksum),
        Err(BazaarRestartError::InvalidWire("checksum"))
    ));

    let mut bad_version = original.clone();
    bad_version[9] = 2;
    assert!(matches!(
        BazaarCasRequest::from_wire_bytes(&reseal_request(bad_version)),
        Err(BazaarRestartError::InvalidWire("request version"))
    ));

    let genesis = BazaarCasRequest::new(None, state(b"after")).to_wire_bytes();
    let mut bad_option = genesis;
    bad_option[10] = 1;
    assert!(matches!(
        BazaarCasRequest::from_wire_bytes(&reseal_request(bad_option)),
        Err(BazaarRestartError::InvalidWire(
            "request expected tag/length mismatch"
        ))
    ));

    let mut trailing = original.clone();
    trailing.truncate(trailing.len() - 32);
    trailing.push(0x99);
    let checksum = blake3::derive_key(REQUEST_CHECKSUM_DOMAIN, &trailing);
    trailing.extend_from_slice(&checksum);
    assert!(matches!(
        BazaarCasRequest::from_wire_bytes(&trailing),
        Err(BazaarRestartError::InvalidWire("request trailing bytes"))
    ));

    let mut oversized = original;
    // replacement length begins after magic/version/tag/expected-length.
    oversized[15..19].copy_from_slice(&((MAX_CANONICAL_STATE_BYTES as u32) + 1).to_be_bytes());
    assert!(matches!(
        BazaarCasRequest::from_wire_bytes(&reseal_request(oversized)),
        Err(BazaarRestartError::InvalidWire(
            "canonical state exceeds maximum"
        ))
    ));

    assert!(BazaarCasRequest::from_wire_bytes(b"tiny").is_err());
    assert!(CanonicalStateBytes::new(Vec::new()).is_err());
}

#[test]
fn exact_cas_has_one_genesis_and_refuses_forks_without_mutating_the_head() {
    let scratch = ScratchDir::new("cas");
    let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
    assert_eq!(store.load().unwrap(), None);

    let first = state(b"complete-lean-state:revision=1;inventory=A");
    let applied = store
        .compare_and_swap(&BazaarCasRequest::new(None, first.clone()))
        .unwrap();
    assert_eq!(
        applied,
        BazaarCasOutcome::Applied {
            previous: None,
            current: first.clone()
        }
    );

    let competing_genesis = state(b"complete-lean-state:revision=1;inventory=MALLORY");
    assert_eq!(
        store
            .compare_and_swap(&BazaarCasRequest::new(None, competing_genesis))
            .unwrap(),
        BazaarCasOutcome::Stale {
            observed: Some(first.clone())
        }
    );
    assert_eq!(store.load().unwrap(), Some(first.clone()));

    let wrong_predecessor = state(b"complete-lean-state:revision=1;inventory=B");
    let replacement = state(b"complete-lean-state:revision=2;inventory=C");
    assert_eq!(
        store
            .compare_and_swap(&BazaarCasRequest::new(Some(wrong_predecessor), replacement))
            .unwrap(),
        BazaarCasOutcome::Stale {
            observed: Some(first.clone())
        }
    );
    assert_eq!(store.load().unwrap(), Some(first));
}

#[test]
fn concurrent_genesis_attempts_can_never_both_apply() {
    let scratch = ScratchDir::new("concurrent-cas");
    let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
    let barrier = Arc::new(Barrier::new(3));
    let mut workers = Vec::new();
    for candidate in [b"lean-state:genesis:A".as_slice(), b"lean-state:genesis:B"] {
        let worker_store = store.clone();
        let worker_barrier = barrier.clone();
        let candidate = state(candidate);
        workers.push(std::thread::spawn(move || {
            worker_barrier.wait();
            worker_store.compare_and_swap(&BazaarCasRequest::new(None, candidate))
        }));
    }
    barrier.wait();
    let results: Vec<_> = workers
        .into_iter()
        .map(|worker| worker.join().expect("CAS worker did not panic"))
        .collect();

    let applied: Vec<_> = results
        .iter()
        .filter_map(|result| match result {
            Ok(BazaarCasOutcome::Applied { current, .. }) => Some(current.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(applied.len(), 1, "at most one absent-head CAS may win");
    assert_eq!(store.load().unwrap(), Some(applied[0].clone()));
    assert!(results.iter().all(|result| matches!(
        result,
        Ok(BazaarCasOutcome::Applied { .. })
            | Ok(BazaarCasOutcome::Stale { .. })
            | Err(BazaarRestartError::Busy)
    )));
}

#[test]
fn restart_reopens_the_complete_successor_and_distinguishes_one_byte() {
    let scratch = ScratchDir::new("restart");
    let before = state(b"state-key-v1\0authority\0revision=1\0all-fields");
    let after = state(b"state-key-v1\0authority\0revision=2\0all-fields");
    {
        let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
        store
            .compare_and_swap(&BazaarCasRequest::new(None, before.clone()))
            .unwrap();
        store
            .compare_and_swap(&BazaarCasRequest::new(Some(before.clone()), after.clone()))
            .unwrap();
    }

    let reopened = DurableBazaarHeadStore::open(scratch.path()).unwrap();
    assert_eq!(reopened.load().unwrap(), Some(after.clone()));

    let mut one_byte_wrong = after.as_bytes().to_vec();
    one_byte_wrong[20] ^= 1;
    let stale = reopened
        .compare_and_swap(&BazaarCasRequest::new(
            Some(CanonicalStateBytes::new(one_byte_wrong).unwrap()),
            state(b"state-key-v1\0authority\0revision=3\0all-fields"),
        ))
        .unwrap();
    assert_eq!(
        stale,
        BazaarCasOutcome::Stale {
            observed: Some(after)
        }
    );
}

#[test]
fn corrupt_head_and_sticky_recovery_lock_fail_closed() {
    let scratch = ScratchDir::new("corrupt");
    let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
    store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"valid-head")))
        .unwrap();

    let head = scratch.path().join("bazaar-head-v1.bin");
    let mut corrupt = fs::read(&head).unwrap();
    corrupt[15] ^= 1;
    fs::write(&head, corrupt).unwrap();
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire("checksum"))
    ));

    // Restore a separate valid store and model a process that crashed while
    // holding the create-new lock. The next writer refuses; it never steals.
    let locked = ScratchDir::new("locked");
    let locked_store = DurableBazaarHeadStore::open(locked.path()).unwrap();
    fs::write(locked.path().join("bazaar-head-v1.lock"), b"stale\n").unwrap();
    assert!(matches!(
        locked_store.compare_and_swap(&BazaarCasRequest::new(None, state(b"candidate"))),
        Err(BazaarRestartError::Busy)
    ));
    assert_eq!(locked_store.load().unwrap(), None);
}

#[test]
fn durable_head_decoder_refuses_resealed_version_length_and_trailing_lies() {
    let scratch = ScratchDir::new("strict-head");
    let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
    store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"valid-head")))
        .unwrap();
    let head_path = scratch.path().join("bazaar-head-v1.bin");
    let original = fs::read(&head_path).unwrap();

    let mut version = original.clone();
    version[9] = 2;
    fs::write(&head_path, reseal_head(version)).unwrap();
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire("head version"))
    ));

    let mut empty = original.clone();
    empty[10..14].copy_from_slice(&0u32.to_be_bytes());
    fs::write(&head_path, reseal_head(empty)).unwrap();
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire("empty canonical state"))
    ));

    let mut trailing = original;
    trailing.truncate(trailing.len() - 32);
    trailing.push(0x99);
    let checksum = blake3::derive_key(HEAD_CHECKSUM_DOMAIN, &trailing);
    trailing.extend_from_slice(&checksum);
    fs::write(&head_path, trailing).unwrap();
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire("head trailing bytes"))
    ));
}

#[cfg(unix)]
#[test]
fn store_refuses_a_symlink_root() {
    use std::os::unix::fs::symlink;

    let scratch = ScratchDir::new("symlink-parent");
    let target = scratch.path().join("target");
    fs::create_dir(&target).unwrap();
    let link = scratch.path().join("link");
    symlink(&target, &link).unwrap();
    assert!(matches!(
        DurableBazaarHeadStore::open(&link),
        Err(BazaarRestartError::UnsafePath("root is a symlink"))
    ));
}

#[cfg(unix)]
#[test]
fn durable_load_refuses_a_symlink_head_even_when_the_target_is_valid() {
    use std::os::unix::fs::symlink;

    let scratch = ScratchDir::new("symlink-head");
    let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
    store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"valid-head")))
        .unwrap();
    let head = scratch.path().join("bazaar-head-v1.bin");
    let target = scratch.path().join("target.bin");
    fs::rename(&head, &target).unwrap();
    symlink(&target, &head).unwrap();
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::UnsafePath("head is a symlink"))
    ));
}
