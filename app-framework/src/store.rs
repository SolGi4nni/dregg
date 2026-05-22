//! Generic async content store backed by `Arc<RwLock<HashMap>>`.
//!
//! Extracted from the identical `state.rs` patterns in bounty-board and compute-exchange.
//! Provides a simple in-memory CRUD store keyed by 32-byte identifiers.

use std::collections::HashMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

/// A 32-byte identifier used as the store key.
pub type Bytes32 = [u8; 32];

/// A generic async content store keyed by `[u8; 32]`.
///
/// Thread-safe (via `Arc<RwLock>`) and cloneable (clone shares the same data).
///
/// # Example
///
/// ```ignore
/// use pyana_app_framework::store::ContentStore;
///
/// #[derive(Clone, serde::Serialize, serde::Deserialize)]
/// struct Order { amount: u64 }
///
/// let store = ContentStore::<Order>::new();
/// store.insert([1u8; 32], Order { amount: 100 }).await;
/// let order = store.get(&[1u8; 32]).await;
/// ```
#[derive(Clone)]
pub struct ContentStore<T: Serialize + for<'de> Deserialize<'de> + Clone> {
    inner: Arc<RwLock<HashMap<Bytes32, T>>>,
}

impl<T: Serialize + for<'de> Deserialize<'de> + Clone> ContentStore<T> {
    /// Create a new empty content store.
    pub fn new() -> Self {
        Self {
            inner: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Insert an item. Overwrites any existing item with the same ID.
    pub async fn insert(&self, id: Bytes32, item: T) {
        let mut map = self.inner.write().await;
        map.insert(id, item);
    }

    /// Get an item by ID (cloned).
    pub async fn get(&self, id: &Bytes32) -> Option<T> {
        let map = self.inner.read().await;
        map.get(id).cloned()
    }

    /// Update an item in-place. Returns `true` if the item existed and was updated.
    pub async fn update(&self, id: &Bytes32, f: impl FnOnce(&mut T)) -> bool {
        let mut map = self.inner.write().await;
        if let Some(item) = map.get_mut(id) {
            f(item);
            true
        } else {
            false
        }
    }

    /// Remove an item by ID, returning it if it existed.
    pub async fn remove(&self, id: &Bytes32) -> Option<T> {
        let mut map = self.inner.write().await;
        map.remove(id)
    }

    /// List all items as (id, item) pairs.
    pub async fn list(&self) -> Vec<(Bytes32, T)> {
        let map = self.inner.read().await;
        map.iter().map(|(k, v)| (*k, v.clone())).collect()
    }

    /// Find items matching a predicate.
    pub async fn find(&self, pred: impl Fn(&T) -> bool) -> Vec<(Bytes32, T)> {
        let map = self.inner.read().await;
        map.iter()
            .filter(|(_, v)| pred(v))
            .map(|(k, v)| (*k, v.clone()))
            .collect()
    }

    /// Return the number of items in the store.
    pub async fn len(&self) -> usize {
        let map = self.inner.read().await;
        map.len()
    }

    /// Check if the store is empty.
    pub async fn is_empty(&self) -> bool {
        let map = self.inner.read().await;
        map.is_empty()
    }
}

impl<T: Serialize + for<'de> Deserialize<'de> + Clone> Default for ContentStore<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    struct TestItem {
        value: u64,
        label: String,
    }

    #[tokio::test]
    async fn insert_and_get() {
        let store = ContentStore::<TestItem>::new();
        let id = [0xAA; 32];
        let item = TestItem {
            value: 42,
            label: "hello".into(),
        };

        store.insert(id, item.clone()).await;
        let got = store.get(&id).await.unwrap();
        assert_eq!(got, item);
    }

    #[tokio::test]
    async fn get_missing_returns_none() {
        let store = ContentStore::<TestItem>::new();
        assert_eq!(store.get(&[0u8; 32]).await, None);
    }

    #[tokio::test]
    async fn update_existing() {
        let store = ContentStore::<TestItem>::new();
        let id = [0xBB; 32];
        store
            .insert(
                id,
                TestItem {
                    value: 1,
                    label: "x".into(),
                },
            )
            .await;

        let updated = store.update(&id, |item| item.value = 99).await;
        assert!(updated);

        let got = store.get(&id).await.unwrap();
        assert_eq!(got.value, 99);
    }

    #[tokio::test]
    async fn update_missing_returns_false() {
        let store = ContentStore::<TestItem>::new();
        let updated = store.update(&[0u8; 32], |_| {}).await;
        assert!(!updated);
    }

    #[tokio::test]
    async fn remove() {
        let store = ContentStore::<TestItem>::new();
        let id = [0xCC; 32];
        store
            .insert(
                id,
                TestItem {
                    value: 5,
                    label: "rem".into(),
                },
            )
            .await;

        let removed = store.remove(&id).await;
        assert!(removed.is_some());
        assert_eq!(store.get(&id).await, None);
    }

    #[tokio::test]
    async fn list_and_find() {
        let store = ContentStore::<TestItem>::new();
        store
            .insert(
                [1; 32],
                TestItem {
                    value: 10,
                    label: "a".into(),
                },
            )
            .await;
        store
            .insert(
                [2; 32],
                TestItem {
                    value: 20,
                    label: "b".into(),
                },
            )
            .await;
        store
            .insert(
                [3; 32],
                TestItem {
                    value: 30,
                    label: "c".into(),
                },
            )
            .await;

        let all = store.list().await;
        assert_eq!(all.len(), 3);

        let big = store.find(|item| item.value >= 20).await;
        assert_eq!(big.len(), 2);
    }
}
