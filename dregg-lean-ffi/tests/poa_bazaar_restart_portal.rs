#[path = "../src/poa_bazaar_restart_portal.rs"]
mod portal;

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Barrier};

use dregg_lean_ffi::poa_bazaar_restart_portal::DurableBazaarHeadStore as RegisteredDurableBazaarHeadStore;
use portal::{
    BazaarCasOutcome, BazaarCasRequest, BazaarRestartError, BazaarStoreIdentity,
    CanonicalEventBytes, CanonicalStateBytes, CasFault, DurableBazaarHeadStore,
};

const HEAD_CHECKSUM_DOMAIN: &str = "dregg.poa-bazaar.durable-head.v2";
const JOURNAL_RECORD_CHECKSUM_DOMAIN: &str = "dregg.poa-bazaar.journal-record.v3";

struct ScratchDir(PathBuf);

impl ScratchDir {
    fn new(label: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let temp_root = fs::canonicalize(std::env::temp_dir())
            .expect("canonicalize the existing system temp directory");
        let path = temp_root.join(format!(
            "dregg-poa-bazaar-{label}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).expect("create isolated Bazaar test directory");
        make_private(&path, 0o700);
        Self(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

#[cfg(unix)]
fn make_private(path: &Path, mode: u32) {
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
}

#[cfg(not(unix))]
fn make_private(_path: &Path, _mode: u32) {}

fn write_private(path: &Path, bytes: &[u8]) {
    fs::write(path, bytes).unwrap();
    make_private(path, 0o600);
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn state(bytes: &[u8]) -> CanonicalStateBytes {
    CanonicalStateBytes::new(bytes.to_vec()).expect("bounded non-empty state")
}

fn reseal_head(mut bytes: Vec<u8>) -> Vec<u8> {
    bytes.truncate(bytes.len() - 32);
    let identity: [u8; 32] = bytes[10..42].try_into().unwrap();
    let checksum = identity_bound_digest(HEAD_CHECKSUM_DOMAIN, &identity, &bytes);
    bytes.extend_from_slice(&checksum);
    bytes
}

fn identity_bound_digest(domain: &str, identity: &[u8; 32], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hasher.update(identity);
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn journal_bound_digest(
    domain: &str,
    identity: &[u8; 32],
    deployment_id: &[u8; 32],
    bytes: &[u8],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hasher.update(identity);
    hasher.update(deployment_id);
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn reseal_first_journal_sequence(mut bytes: Vec<u8>, sequence: u64) -> Vec<u8> {
    let header_len = 8 + 2 + 32 + 32 + 32;
    let identity: [u8; 32] = bytes[10..42].try_into().unwrap();
    let deployment_id: [u8; 32] = bytes[42..74].try_into().unwrap();
    let record_len =
        u32::from_be_bytes(bytes[header_len..header_len + 4].try_into().unwrap()) as usize;
    let record_start = header_len + 4;
    let record_end = record_start + record_len;
    let sequence_start = record_start + 8 + 2;
    bytes[sequence_start..sequence_start + 8].copy_from_slice(&sequence.to_be_bytes());
    let checksum_start = record_end - 32;
    let checksum = journal_bound_digest(
        JOURNAL_RECORD_CHECKSUM_DOMAIN,
        &identity,
        &deployment_id,
        &bytes[record_start..checksum_start],
    );
    bytes[checksum_start..record_end].copy_from_slice(&checksum);
    bytes
}

#[test]
fn production_restart_portal_is_registered_and_opens_an_empty_store() {
    let scratch = ScratchDir::new("registered-module");
    let store = RegisteredDurableBazaarHeadStore::open(scratch.path()).unwrap();
    assert_eq!(store.load().unwrap(), None);
}

#[test]
fn deployment_identity_cannot_be_added_after_state_or_rebound() {
    let legacy = ScratchDir::new("identity-missing-with-state");
    let legacy_store = DurableBazaarHeadStore::open(legacy.path()).unwrap();
    legacy_store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"unbound-state")))
        .unwrap();
    assert!(matches!(
        DurableBazaarHeadStore::open_bound(legacy.path(), BazaarStoreIdentity::test(0x11)),
        Err(BazaarRestartError::UnsafePath(
            "store identity is absent beside existing durable state"
        ))
    ));

    let bound = ScratchDir::new("identity-rebind");
    DurableBazaarHeadStore::open_bound(bound.path(), BazaarStoreIdentity::test(0x22)).unwrap();
    assert!(matches!(
        DurableBazaarHeadStore::open_bound(bound.path(), BazaarStoreIdentity::test(0x23)),
        Err(BazaarRestartError::UnsafePath(
            "store identity does not match pinned deployment"
        ))
    ));
}

#[test]
fn embedded_identity_refuses_coherent_cross_store_journal_and_head_swaps() {
    let first = ScratchDir::new("identity-swap-first");
    let second = ScratchDir::new("identity-swap-second");
    let first_store =
        DurableBazaarHeadStore::open_bound(first.path(), BazaarStoreIdentity::test(0x41)).unwrap();
    let second_store =
        DurableBazaarHeadStore::open_bound(second.path(), BazaarStoreIdentity::test(0x42)).unwrap();
    first_store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"first-store-state")))
        .unwrap();
    second_store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"second-store-state")))
        .unwrap();

    let second_journal = fs::read(second.path().join("bazaar-cas-v1.journal")).unwrap();
    fs::copy(
        first.path().join("bazaar-cas-v1.journal"),
        second.path().join("bazaar-cas-v1.journal"),
    )
    .unwrap();
    fs::copy(
        first.path().join("bazaar-head-v1.bin"),
        second.path().join("bazaar-head-v1.bin"),
    )
    .unwrap();
    assert!(matches!(
        second_store.load(),
        Err(BazaarRestartError::InvalidWire(
            "journal store identity mismatch"
        ))
    ));

    write_private(
        &second.path().join("bazaar-cas-v1.journal"),
        &second_journal,
    );
    assert!(matches!(
        second_store.load(),
        Err(BazaarRestartError::InvalidWire(
            "head store identity mismatch"
        ))
    ));
}

#[test]
fn legacy_unbound_durable_formats_refuse_explicitly() {
    let journal = ScratchDir::new("legacy-journal");
    let journal_store =
        DurableBazaarHeadStore::open_bound(journal.path(), BazaarStoreIdentity::test(0x51))
            .unwrap();
    write_private(&journal.path().join("bazaar-cas-v1.journal"), b"POAJNL01");
    assert!(matches!(
        journal_store.load(),
        Err(BazaarRestartError::InvalidWire(
            "legacy journal format lacks embedded store identity"
        ))
    ));

    let state_only = ScratchDir::new("legacy-state-only-journal");
    let state_only_store =
        DurableBazaarHeadStore::open_bound(state_only.path(), BazaarStoreIdentity::test(0x53))
            .unwrap();
    write_private(
        &state_only.path().join("bazaar-cas-v1.journal"),
        b"POAJNL02",
    );
    assert!(matches!(
        state_only_store.load(),
        Err(BazaarRestartError::InvalidWire(
            "legacy state-only journal lacks canonical command events"
        ))
    ));

    let head = ScratchDir::new("legacy-head");
    let head_store =
        DurableBazaarHeadStore::open_bound(head.path(), BazaarStoreIdentity::test(0x52)).unwrap();
    write_private(&head.path().join("bazaar-head-v1.bin"), b"POAHEAD1");
    assert!(matches!(
        head_store.load(),
        Err(BazaarRestartError::InvalidWire(
            "legacy head format lacks embedded store identity"
        ))
    ));
}

#[cfg(target_os = "macos")]
#[test]
fn macos_temp_alias_refuses_while_its_canonical_target_is_accepted() {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let alias_root = std::env::temp_dir();
    let canonical_root = fs::canonicalize(&alias_root).unwrap();
    assert_ne!(
        alias_root, canonical_root,
        "macOS temp root should expose its /var alias"
    );
    let alias_path = alias_root.join(format!(
        "dregg-poa-bazaar-macos-alias-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&alias_path).unwrap();
    make_private(&alias_path, 0o700);
    let canonical_path = fs::canonicalize(&alias_path).unwrap();

    assert!(matches!(
        DurableBazaarHeadStore::open(&alias_path),
        Err(BazaarRestartError::UnsafePath(_))
    ));
    assert_eq!(
        DurableBazaarHeadStore::open(&canonical_path)
            .unwrap()
            .load()
            .unwrap(),
        None
    );
    fs::remove_dir_all(&canonical_path).unwrap();
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
fn journaled_cas_retains_exact_command_payload_and_binds_deployment() {
    let scratch = ScratchDir::new("journaled-command");
    let store = DurableBazaarHeadStore::open_bound_deployment(
        scratch.path(),
        BazaarStoreIdentity::test(0x61),
        [0x71; 32],
    )
    .unwrap();
    let replacement = state(b"typed-replay-state-1");
    let command = CanonicalEventBytes::new(b"lean-command-event-1".to_vec()).unwrap();
    store
        .compare_and_swap_journaled(
            &BazaarCasRequest::new(None, replacement.clone()),
            command.clone(),
        )
        .unwrap();

    let records = store.load_authenticated_journal_records().unwrap();
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].sequence, 0);
    assert_eq!(records[0].expected, None);
    assert_eq!(records[0].replacement, replacement);
    assert_eq!(records[0].command_event, command);

    let wrong_deployment = DurableBazaarHeadStore::open_bound_deployment(
        scratch.path(),
        BazaarStoreIdentity::test(0x61),
        [0x72; 32],
    )
    .unwrap();
    assert!(matches!(
        wrong_deployment.load(),
        Err(BazaarRestartError::InvalidWire(
            "journal deployment identity mismatch"
        ))
    ));
}

#[test]
fn typed_replay_refuses_a_state_only_v3_record() {
    let scratch = ScratchDir::new("state-only-v3-record");
    let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
    store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"state-only")))
        .unwrap();
    assert!(matches!(
        store.load_authenticated_journal_records(),
        Err(BazaarRestartError::InvalidWire(
            "journal record lacks canonical command event"
        ))
    ));
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
    // Corrupt the payload, not the embedded store identity metadata.
    corrupt[46] ^= 1;
    fs::write(&head, corrupt).unwrap();
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire("checksum"))
    ));

    // Restore a separate valid store and model a process that crashed while
    // holding the create-new lock. The next writer refuses; it never steals.
    let locked = ScratchDir::new("locked");
    let locked_store = DurableBazaarHeadStore::open(locked.path()).unwrap();
    write_private(&locked.path().join("bazaar-head-v1.lock"), b"stale\n");
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
    version[9] = 3;
    fs::write(&head_path, reseal_head(version)).unwrap();
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire("head version"))
    ));

    let mut empty = original.clone();
    empty[42..46].copy_from_slice(&0u32.to_be_bytes());
    fs::write(&head_path, reseal_head(empty)).unwrap();
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire("empty canonical state"))
    ));

    let mut trailing = original;
    trailing.truncate(trailing.len() - 32);
    trailing.push(0x99);
    let identity: [u8; 32] = trailing[10..42].try_into().unwrap();
    let checksum = identity_bound_digest(HEAD_CHECKSUM_DOMAIN, &identity, &trailing);
    trailing.extend_from_slice(&checksum);
    fs::write(&head_path, trailing).unwrap();
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire("head trailing bytes"))
    ));
}

#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "macos",
    target_os = "ios"
))]
#[test]
fn store_refuses_a_symlink_ancestor() {
    use std::os::unix::fs::symlink;

    let scratch = ScratchDir::new("symlink-parent");
    let target = scratch.path().join("target");
    fs::create_dir(&target).unwrap();
    make_private(&target, 0o700);
    let nested = target.join("nested");
    fs::create_dir(&nested).unwrap();
    make_private(&nested, 0o700);
    let link = scratch.path().join("link");
    symlink(&target, &link).unwrap();
    assert!(matches!(
        DurableBazaarHeadStore::open(link.join("nested")),
        Err(BazaarRestartError::UnsafePath(_))
    ));
}

#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "macos",
    target_os = "ios"
))]
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
        Err(BazaarRestartError::UnsafePath(_))
    ));
}

#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "macos",
    target_os = "ios"
))]
#[test]
fn store_refuses_permissive_root_and_wrong_expected_owner() {
    use std::os::unix::fs::MetadataExt;

    let permissive = ScratchDir::new("permissive-root");
    make_private(permissive.path(), 0o755);
    assert!(matches!(
        DurableBazaarHeadStore::open(permissive.path()),
        Err(BazaarRestartError::UnsafePath(
            "root permissions are not private"
        ))
    ));

    let wrong_owner = ScratchDir::new("wrong-owner");
    let actual = fs::metadata(wrong_owner.path()).unwrap().uid();
    assert!(matches!(
        DurableBazaarHeadStore::open_with_expected_owner(
            wrong_owner.path(),
            actual.wrapping_add(1)
        ),
        Err(BazaarRestartError::UnsafePath(
            "root owner does not match trusted runtime user"
        ))
    ));
}

#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "macos",
    target_os = "ios"
))]
#[test]
fn store_refuses_permissive_head_journal_and_lock_files() {
    let head_scratch = ScratchDir::new("head-mode");
    let head_store = DurableBazaarHeadStore::open(head_scratch.path()).unwrap();
    head_store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"private-head")))
        .unwrap();
    make_private(&head_scratch.path().join("bazaar-head-v1.bin"), 0o644);
    assert!(matches!(
        head_store.load(),
        Err(BazaarRestartError::UnsafePath(
            "store entry permissions are not private"
        ))
    ));

    let journal_scratch = ScratchDir::new("journal-mode");
    let journal_store = DurableBazaarHeadStore::open(journal_scratch.path()).unwrap();
    journal_store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"private-journal")))
        .unwrap();
    make_private(&journal_scratch.path().join("bazaar-cas-v1.journal"), 0o644);
    assert!(matches!(
        journal_store.load(),
        Err(BazaarRestartError::UnsafePath(
            "store entry permissions are not private"
        ))
    ));

    let lock_scratch = ScratchDir::new("lock-mode");
    let lock_store = DurableBazaarHeadStore::open(lock_scratch.path()).unwrap();
    let lock = lock_scratch.path().join("bazaar-head-v1.lock");
    write_private(&lock, b"stale\n");
    make_private(&lock, 0o644);
    assert!(matches!(
        lock_store.compare_and_swap(&BazaarCasRequest::new(None, state(b"candidate"))),
        Err(BazaarRestartError::UnsafePath(
            "store entry permissions are not private"
        ))
    ));
}

#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "macos",
    target_os = "ios"
))]
#[test]
fn head_journal_and_lock_each_refuse_hardlink_aliases() {
    let head_scratch = ScratchDir::new("head-hardlink");
    let head_store = DurableBazaarHeadStore::open(head_scratch.path()).unwrap();
    head_store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"hardlink-head")))
        .unwrap();
    fs::hard_link(
        head_scratch.path().join("bazaar-head-v1.bin"),
        head_scratch.path().join("head-alias"),
    )
    .unwrap();
    assert!(matches!(
        head_store.load(),
        Err(BazaarRestartError::UnsafePath(
            "store entry link count is not one"
        ))
    ));

    let journal_scratch = ScratchDir::new("journal-hardlink");
    let journal_store = DurableBazaarHeadStore::open(journal_scratch.path()).unwrap();
    journal_store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"hardlink-journal")))
        .unwrap();
    fs::hard_link(
        journal_scratch.path().join("bazaar-cas-v1.journal"),
        journal_scratch.path().join("journal-alias"),
    )
    .unwrap();
    assert!(matches!(
        journal_store.load(),
        Err(BazaarRestartError::UnsafePath(
            "store entry link count is not one"
        ))
    ));

    let lock_scratch = ScratchDir::new("lock-hardlink");
    let lock_store = DurableBazaarHeadStore::open(lock_scratch.path()).unwrap();
    let lock = lock_scratch.path().join("bazaar-head-v1.lock");
    write_private(&lock, b"stale\n");
    fs::hard_link(&lock, lock_scratch.path().join("lock-alias")).unwrap();
    assert!(matches!(
        lock_store.compare_and_swap(&BazaarCasRequest::new(None, state(b"candidate"))),
        Err(BazaarRestartError::UnsafePath(
            "store entry link count is not one"
        ))
    ));
}

#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "macos",
    target_os = "ios"
))]
#[test]
fn pathname_inode_substitution_is_detected_even_with_identical_bytes() {
    let scratch = ScratchDir::new("inode-substitution");
    let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
    store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"same-byte-head")))
        .unwrap();
    assert!(matches!(
        store.detect_head_inode_substitution(),
        Err(BazaarRestartError::UnsafePath(
            "store entry inode changed during operation"
        ))
    ));
}

#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "macos",
    target_os = "ios"
))]
#[test]
fn configured_root_rename_and_inode_substitution_is_detected() {
    let scratch = ScratchDir::new("root-inode-substitution");
    let root = scratch.path().join("store");
    fs::create_dir(&root).unwrap();
    make_private(&root, 0o700);
    let store = DurableBazaarHeadStore::open(&root).unwrap();
    store
        .compare_and_swap(&BazaarCasRequest::new(None, state(b"anchored-head")))
        .unwrap();

    let moved = scratch.path().join("moved-store");
    fs::rename(&root, &moved).unwrap();
    fs::create_dir(&root).unwrap();
    make_private(&root, 0o700);
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::UnsafePath(
            "configured root inode changed during operation"
        ))
    ));
}

#[test]
fn every_uncertain_write_stage_preserves_a_sticky_recovery_lock() {
    for fault in [
        CasFault::AfterJournalWrite,
        CasFault::AfterJournalSync,
        CasFault::AfterHeadRename,
    ] {
        let scratch = ScratchDir::new(&format!("fault-{fault:?}"));
        let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
        let request = BazaarCasRequest::new(None, state(b"fault-injected-head"));
        assert!(matches!(
            store.compare_and_swap_with_fault(&request, fault),
            Err(BazaarRestartError::IndeterminateCommit(_))
        ));
        assert!(scratch.path().join("bazaar-head-v1.lock").exists());
        assert!(matches!(
            store.compare_and_swap(&request),
            Err(BazaarRestartError::Busy)
        ));
    }
}

#[test]
fn synced_journal_crash_refuses_until_validated_recovery_then_continues_exactly() {
    let scratch = ScratchDir::new("recover-synced-journal");
    let store = DurableBazaarHeadStore::open_bound(scratch.path(), BazaarStoreIdentity::test(0x31))
        .unwrap();
    let first = state(b"canonical-lean-state-1");
    let request = BazaarCasRequest::new(None, first.clone());
    assert!(matches!(
        store.compare_and_swap_with_fault(&request, CasFault::AfterJournalSync),
        Err(BazaarRestartError::IndeterminateCommit(_))
    ));
    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire(
            "journal has records but head cache is absent"
        ))
    ));
    assert!(matches!(
        store.compare_and_swap(&request),
        Err(BazaarRestartError::Busy)
    ));

    let recovered = store
        .recover_sticky_head(|wire| Ok(wire == first.as_bytes()))
        .unwrap();
    assert_eq!(recovered.record_count, 1);
    assert_eq!(recovered.recovered_head, first);
    assert!(!scratch.path().join("bazaar-head-v1.lock").exists());
    assert_eq!(store.load().unwrap(), Some(first.clone()));

    let second = state(b"canonical-lean-state-2");
    assert!(matches!(
        store
            .compare_and_swap(&BazaarCasRequest::new(Some(first), second.clone()))
            .unwrap(),
        BazaarCasOutcome::Applied { current, .. } if current == second
    ));
}

#[test]
fn recovery_refuses_corrupt_or_divergent_journal_and_keeps_sticky_lock() {
    for (label, mutate) in [("corrupt", false), ("resealed-divergent-sequence", true)] {
        let scratch = ScratchDir::new(&format!("recover-{label}"));
        let store =
            DurableBazaarHeadStore::open_bound(scratch.path(), BazaarStoreIdentity::test(0x52))
                .unwrap();
        let request = BazaarCasRequest::new(None, state(b"canonical-tail"));
        assert!(matches!(
            store.compare_and_swap_with_fault(&request, CasFault::AfterJournalSync),
            Err(BazaarRestartError::IndeterminateCommit(_))
        ));
        let journal_path = scratch.path().join("bazaar-cas-v1.journal");
        let mut journal = fs::read(&journal_path).unwrap();
        if mutate {
            journal = reseal_first_journal_sequence(journal, 1);
        } else {
            let last = journal.len() - 1;
            journal[last] ^= 1;
        }
        fs::write(&journal_path, journal).unwrap();

        assert!(store.recover_sticky_head(|_| Ok(true)).is_err());
        assert!(scratch.path().join("bazaar-head-v1.lock").exists());
        assert!(matches!(
            store.compare_and_swap(&request),
            Err(BazaarRestartError::Busy)
        ));
    }
}

#[test]
fn recovery_refuses_noncanonical_tail_and_keeps_sticky_lock() {
    let scratch = ScratchDir::new("recover-noncanonical");
    let store = DurableBazaarHeadStore::open_bound(scratch.path(), BazaarStoreIdentity::test(0x73))
        .unwrap();
    let request = BazaarCasRequest::new(None, state(b"rust-opaque-but-not-lean-canonical"));
    assert!(matches!(
        store.compare_and_swap_with_fault(&request, CasFault::AfterJournalSync),
        Err(BazaarRestartError::IndeterminateCommit(_))
    ));
    assert!(matches!(
        store.recover_sticky_head(|_| Ok(false)),
        Err(BazaarRestartError::InvalidWire(
            "journal replacement is not a canonical Lean StateKey"
        ))
    ));
    assert!(scratch.path().join("bazaar-head-v1.lock").exists());
}

#[test]
fn replay_audits_every_record_and_refuses_reordered_history() {
    let scratch = ScratchDir::new("reordered-journal");
    let first = state(b"journal-state-1");
    let second = state(b"journal-state-2");
    let store = DurableBazaarHeadStore::open(scratch.path()).unwrap();
    store
        .compare_and_swap(&BazaarCasRequest::new(None, first.clone()))
        .unwrap();
    store
        .compare_and_swap(&BazaarCasRequest::new(Some(first), second))
        .unwrap();

    let journal_path = scratch.path().join("bazaar-cas-v1.journal");
    let journal = fs::read(&journal_path).unwrap();
    let header_len = 8 + 2 + 32 + 32 + 32;
    let first_len =
        u32::from_be_bytes(journal[header_len..header_len + 4].try_into().unwrap()) as usize;
    let first_end = header_len + 4 + first_len;
    let mut reordered = Vec::with_capacity(journal.len());
    reordered.extend_from_slice(&journal[..header_len]);
    reordered.extend_from_slice(&journal[first_end..]);
    reordered.extend_from_slice(&journal[header_len..first_end]);
    fs::write(&journal_path, reordered).unwrap();

    assert!(matches!(
        store.load(),
        Err(BazaarRestartError::InvalidWire(
            "journal sequence is not contiguous"
        ))
    ));
}
