//! Integration tests for the tokenizer daemon service.

use std::path::PathBuf;
use std::time::Duration;

use dregg_tokenizer::client::TokenizerClient;
use dregg_tokenizer::service::{KeyRing, ServiceConfig, TokenizerService};

/// Create a temp socket path for testing.
fn temp_socket_path() -> PathBuf {
    let dir = std::env::temp_dir();
    dir.join(format!("dregg-tokenizer-test-{}.sock", std::process::id()))
}

#[tokio::test]
async fn test_seal_unseal_roundtrip() {
    let socket_path = temp_socket_path();
    let config = ServiceConfig {
        socket_path: socket_path.clone(),
        key_store_path: PathBuf::from("/tmp/dregg-test-keys-1"),
    };
    let keyring = KeyRing::generate();
    let service = TokenizerService::new(config, keyring);

    // Spawn service.
    tokio::spawn(async move {
        service.serve().await.unwrap();
    });

    // Wait for socket to appear.
    tokio::time::sleep(Duration::from_millis(50)).await;

    // Connect client.
    let mut client = TokenizerClient::new(&socket_path);
    client.connect().await.unwrap();

    // Seal.
    let plaintext = b"super-secret-api-key-12345";
    let sealed = client.seal(plaintext).await.unwrap();
    assert!(!sealed.is_empty());
    assert_ne!(&sealed, plaintext);

    // Unseal.
    let decrypted = client.unseal(&sealed).await.unwrap();
    assert_eq!(decrypted, plaintext);

    // Shutdown.
    client.shutdown().await.unwrap();

    // Cleanup.
    let _ = std::fs::remove_file(&socket_path);
}

#[tokio::test]
async fn test_get_public_key() {
    let socket_path = std::env::temp_dir().join(format!(
        "dregg-tokenizer-test-pk-{}.sock",
        std::process::id()
    ));
    let config = ServiceConfig {
        socket_path: socket_path.clone(),
        key_store_path: PathBuf::from("/tmp/dregg-test-keys-2"),
    };
    let keyring = KeyRing::generate();
    let service = TokenizerService::new(config, keyring);

    tokio::spawn(async move {
        service.serve().await.unwrap();
    });

    tokio::time::sleep(Duration::from_millis(50)).await;

    let mut client = TokenizerClient::new(&socket_path);
    client.connect().await.unwrap();

    let pk = client.get_public_key().await.unwrap();
    // Public key should be 32 bytes, non-zero.
    assert_ne!(pk, [0u8; 32]);

    // Getting it again should return the same key.
    let pk2 = client.get_public_key().await.unwrap();
    assert_eq!(pk, pk2);

    client.shutdown().await.unwrap();
    let _ = std::fs::remove_file(&socket_path);
}

#[tokio::test]
async fn test_key_rotation() {
    let socket_path = std::env::temp_dir().join(format!(
        "dregg-tokenizer-test-rotate-{}.sock",
        std::process::id()
    ));
    let config = ServiceConfig {
        socket_path: socket_path.clone(),
        key_store_path: PathBuf::from("/tmp/dregg-test-keys-3"),
    };
    let keyring = KeyRing::generate();
    let service = TokenizerService::new(config, keyring);

    tokio::spawn(async move {
        service.serve().await.unwrap();
    });

    tokio::time::sleep(Duration::from_millis(50)).await;

    let mut client = TokenizerClient::new(&socket_path);
    client.connect().await.unwrap();

    // Get original public key.
    let pk1 = client.get_public_key().await.unwrap();

    // Seal with original key.
    let plaintext = b"pre-rotation-secret";
    let sealed_before = client.seal(plaintext).await.unwrap();

    // Rotate.
    let new_pk = client.rotate().await.unwrap();
    assert_ne!(pk1, new_pk);

    // New public key should match.
    let pk_after = client.get_public_key().await.unwrap();
    assert_eq!(new_pk, pk_after);

    // Old sealed secret should still decrypt (old key retained).
    let decrypted = client.unseal(&sealed_before).await.unwrap();
    assert_eq!(decrypted, plaintext);

    // New seal uses new key.
    let plaintext2 = b"post-rotation-secret";
    let sealed_after = client.seal(plaintext2).await.unwrap();
    let decrypted2 = client.unseal(&sealed_after).await.unwrap();
    assert_eq!(decrypted2, plaintext2);

    client.shutdown().await.unwrap();
    let _ = std::fs::remove_file(&socket_path);
}

#[tokio::test]
async fn test_unseal_wrong_data_returns_error() {
    let socket_path = std::env::temp_dir().join(format!(
        "dregg-tokenizer-test-err-{}.sock",
        std::process::id()
    ));
    let config = ServiceConfig {
        socket_path: socket_path.clone(),
        key_store_path: PathBuf::from("/tmp/dregg-test-keys-4"),
    };
    let keyring = KeyRing::generate();
    let service = TokenizerService::new(config, keyring);

    tokio::spawn(async move {
        service.serve().await.unwrap();
    });

    tokio::time::sleep(Duration::from_millis(50)).await;

    let mut client = TokenizerClient::new(&socket_path);
    client.connect().await.unwrap();

    // Trying to unseal garbage should fail.
    let result = client.unseal(&[0u8; 100]).await;
    assert!(result.is_err());

    // Too-short data should also fail.
    let result = client.unseal(&[1u8; 10]).await;
    assert!(result.is_err());

    client.shutdown().await.unwrap();
    let _ = std::fs::remove_file(&socket_path);
}

#[tokio::test]
async fn test_multiple_operations_same_connection() {
    let socket_path = std::env::temp_dir().join(format!(
        "dregg-tokenizer-test-multi-{}.sock",
        std::process::id()
    ));
    let config = ServiceConfig {
        socket_path: socket_path.clone(),
        key_store_path: PathBuf::from("/tmp/dregg-test-keys-5"),
    };
    let keyring = KeyRing::generate();
    let service = TokenizerService::new(config, keyring);

    tokio::spawn(async move {
        service.serve().await.unwrap();
    });

    tokio::time::sleep(Duration::from_millis(50)).await;

    let mut client = TokenizerClient::new(&socket_path);
    client.connect().await.unwrap();

    // Multiple seal/unseal operations on the same connection.
    for i in 0..10 {
        let msg = format!("secret-number-{}", i);
        let sealed = client.seal(msg.as_bytes()).await.unwrap();
        let decrypted = client.unseal(&sealed).await.unwrap();
        assert_eq!(decrypted, msg.as_bytes());
    }

    client.shutdown().await.unwrap();
    let _ = std::fs::remove_file(&socket_path);
}

#[tokio::test]
async fn test_keyring_unit() {
    // Unit test for KeyRing without the daemon.
    let mut ring = KeyRing::generate();
    assert_eq!(ring.len(), 1);

    let plaintext = b"keyring-direct-test";
    let sealed = ring.seal(plaintext).unwrap();
    let decrypted = ring.unseal(&sealed).unwrap();
    assert_eq!(decrypted, plaintext);

    // Rotate.
    let old_pk = ring.current_public_key();
    let new_pk = ring.rotate();
    assert_ne!(old_pk, new_pk);
    assert_eq!(ring.len(), 2);

    // Old sealed data still decrypts.
    let decrypted2 = ring.unseal(&sealed).unwrap();
    assert_eq!(decrypted2, plaintext);

    // New seal works.
    let sealed2 = ring.seal(b"new").unwrap();
    let decrypted3 = ring.unseal(&sealed2).unwrap();
    assert_eq!(decrypted3, b"new");
}
