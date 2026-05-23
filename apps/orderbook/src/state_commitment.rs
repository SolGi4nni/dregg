//! Order book state commitment via Merkle tree.
//!
//! The book state is committed to a Merkle root so that any user can verify
//! their order is included in the canonical book state. This root is published
//! to the federation (via cell state), making the book state auditable without
//! trusting the matcher.
//!
//! The Merkle tree is a binary hash tree over serialized order entries sorted
//! by their content-addressed order ID.

use crate::order::{Order, OrderId};

/// A Merkle proof demonstrating that a specific order is included in the book.
#[derive(Clone, Debug)]
pub struct OrderInclusionProof {
    /// The order ID being proved.
    pub order_id: OrderId,
    /// Sibling hashes along the path from the leaf to the root.
    pub siblings: Vec<[u8; 32]>,
    /// Direction bits: false = left child, true = right child.
    pub path_bits: Vec<bool>,
    /// The leaf hash (hash of the order).
    pub leaf_hash: [u8; 32],
}

/// The committed state of the order book at a point in time.
#[derive(Clone, Debug)]
pub struct BookStateCommitment {
    /// The Merkle root of all live orders.
    pub root: [u8; 32],
    /// The federation block height at which this commitment was made.
    pub height: u64,
    /// Total number of live orders in the tree.
    pub order_count: usize,
    /// Sequence number (monotonically increasing with each state change).
    pub sequence: u64,
}

/// Compute a leaf hash for an order (deterministic serialization).
pub fn order_leaf_hash(order: &Order) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-leaf-v1");
    hasher.update(&order.id);
    hasher.update(order.trader.as_bytes());
    let type_bytes = postcard::to_allocvec(&order.order_type).unwrap_or_default();
    hasher.update(&type_bytes);
    hasher.update(&order.remaining_amount.to_le_bytes());
    hasher.update(&order.created_at.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Compute the Merkle root from a set of order leaf hashes.
///
/// Orders are sorted by their ID before tree construction to ensure determinism.
pub fn compute_merkle_root(orders: &[Order]) -> [u8; 32] {
    if orders.is_empty() {
        return [0u8; 32]; // Empty tree sentinel.
    }

    // Sort by order ID for deterministic tree structure.
    let mut leaves: Vec<[u8; 32]> = orders.iter().map(|o| order_leaf_hash(o)).collect();

    // Sort leaves by corresponding order ID.
    let mut indexed: Vec<(OrderId, [u8; 32])> = orders
        .iter()
        .map(|o| o.id)
        .zip(leaves.iter().copied())
        .collect();
    indexed.sort_by(|a, b| a.0.cmp(&b.0));
    leaves = indexed.into_iter().map(|(_, h)| h).collect();

    // Pad to next power of two with zero hashes.
    let target_len = leaves.len().next_power_of_two();
    while leaves.len() < target_len {
        leaves.push([0u8; 32]);
    }

    // Build tree bottom-up.
    while leaves.len() > 1 {
        let mut next_level = Vec::with_capacity(leaves.len() / 2);
        for pair in leaves.chunks(2) {
            next_level.push(hash_pair(&pair[0], &pair[1]));
        }
        leaves = next_level;
    }

    leaves[0]
}

/// Generate a Merkle inclusion proof for a specific order.
pub fn generate_inclusion_proof(
    orders: &[Order],
    target_id: &OrderId,
) -> Option<OrderInclusionProof> {
    if orders.is_empty() {
        return None;
    }

    // Sort by order ID for deterministic tree structure.
    let mut indexed: Vec<(OrderId, [u8; 32])> =
        orders.iter().map(|o| (o.id, order_leaf_hash(o))).collect();
    indexed.sort_by(|a, b| a.0.cmp(&b.0));

    // Find the target leaf index.
    let leaf_idx = indexed.iter().position(|(id, _)| id == target_id)?;
    let leaf_hash = indexed[leaf_idx].1;

    let mut leaves: Vec<[u8; 32]> = indexed.into_iter().map(|(_, h)| h).collect();

    // Pad to next power of two.
    let target_len = leaves.len().next_power_of_two();
    while leaves.len() < target_len {
        leaves.push([0u8; 32]);
    }

    let mut siblings = Vec::new();
    let mut path_bits = Vec::new();
    let mut idx = leaf_idx;

    // Build proof while constructing tree.
    let mut current_level = leaves;
    while current_level.len() > 1 {
        let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
        siblings.push(current_level[sibling_idx]);
        path_bits.push(idx % 2 != 0); // true if we're the right child

        let mut next_level = Vec::with_capacity(current_level.len() / 2);
        for pair in current_level.chunks(2) {
            next_level.push(hash_pair(&pair[0], &pair[1]));
        }
        current_level = next_level;
        idx /= 2;
    }

    Some(OrderInclusionProof {
        order_id: *target_id,
        siblings,
        path_bits,
        leaf_hash,
    })
}

/// Verify a Merkle inclusion proof against a claimed root.
pub fn verify_inclusion_proof(proof: &OrderInclusionProof, root: &[u8; 32]) -> bool {
    let mut current = proof.leaf_hash;

    for (sibling, is_right) in proof.siblings.iter().zip(proof.path_bits.iter()) {
        if *is_right {
            current = hash_pair(sibling, &current);
        } else {
            current = hash_pair(&current, sibling);
        }
    }

    current == *root
}

/// Hash two nodes together to form a parent node.
fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-orderbook-node-v1");
    hasher.update(left);
    hasher.update(right);
    *hasher.finalize().as_bytes()
}

/// Helper: collect all live orders from the book for computing the root.
/// This iterates both sides and collects all resting orders.
pub fn collect_live_orders(book: &crate::book::OrderBook) -> Vec<Order> {
    let mut orders = Vec::new();
    for level in book.ask_levels() {
        for order in &level.orders {
            orders.push(order.clone());
        }
    }
    for level in book.bid_levels() {
        for order in &level.orders {
            orders.push(order.clone());
        }
    }
    orders
}
