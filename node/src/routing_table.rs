//! Local routing table mapping CellId -> reachable peers.
//!
//! When a turn containing an `Effect::Introduce` is executed, the receipt
//! carries `RoutingDirective`s. This module consumes those directives and
//! maintains a mapping from CellId to the peer address through which that
//! cell is reachable — enabling three-party introductions to produce actual
//! network-level connectivity.

use std::collections::HashMap;
use std::net::SocketAddr;

use pyana_cell::CellId;
use pyana_turn::RoutingDirective;

/// A single route entry describing how to reach a cell.
#[derive(Clone, Debug)]
pub struct RouteEntry {
    /// The peer address through which this cell is reachable.
    pub via_peer: SocketAddr,
    /// The cell that authorized this introduction.
    pub introduced_by: CellId,
    /// Block height at which this route expires (None = no expiry).
    pub expires: Option<u64>,
    /// Timestamp (unix seconds) when this route was created.
    pub created_at: u64,
}

/// A local routing table that maps CellId -> set of reachable peers.
///
/// Populated from `RoutingDirective`s extracted from turn receipts.
/// Expired entries are pruned periodically or on lookup.
#[derive(Clone, Debug, Default)]
pub struct RoutingTable {
    routes: HashMap<CellId, Vec<RouteEntry>>,
}

impl RoutingTable {
    /// Create a new empty routing table.
    pub fn new() -> Self {
        Self {
            routes: HashMap::new(),
        }
    }

    /// Process a routing directive, adding a route for the target cell
    /// reachable via the given peer address.
    ///
    /// `via_peer` is the peer address from which the turn containing
    /// this directive was received.
    pub fn apply_directive(&mut self, directive: &RoutingDirective, via_peer: SocketAddr) {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        let entry = RouteEntry {
            via_peer,
            introduced_by: directive.sender,
            expires: directive.expires,
            created_at: now,
        };

        self.routes
            .entry(directive.target)
            .or_default()
            .push(entry);
    }

    /// Look up routes to reach a given cell.
    ///
    /// Returns only non-expired entries. Expired entries are lazily pruned.
    pub fn lookup(&mut self, cell: &CellId, current_height: u64) -> Vec<&RouteEntry> {
        if let Some(entries) = self.routes.get_mut(cell) {
            // Prune expired entries lazily on lookup.
            entries.retain(|e| match e.expires {
                Some(exp) => current_height < exp,
                None => true,
            });
        }

        self.routes
            .get(cell)
            .map(|entries| entries.iter().collect())
            .unwrap_or_default()
    }

    /// Look up routes without mutating (no pruning). Returns all entries
    /// including potentially expired ones.
    pub fn lookup_immut(&self, cell: &CellId) -> &[RouteEntry] {
        self.routes.get(cell).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Remove all expired routes given the current block height.
    pub fn prune_expired(&mut self, current_height: u64) {
        self.routes.retain(|_cell, entries| {
            entries.retain(|e| match e.expires {
                Some(exp) => current_height < exp,
                None => true,
            });
            !entries.is_empty()
        });
    }

    /// Total number of route entries across all cells.
    pub fn len(&self) -> usize {
        self.routes.values().map(|v| v.len()).sum()
    }

    /// Whether the routing table is empty.
    pub fn is_empty(&self) -> bool {
        self.routes.is_empty()
    }

    /// Remove all routes associated with a specific peer address
    /// (e.g., when a peer disconnects).
    pub fn remove_peer(&mut self, peer: &SocketAddr) {
        self.routes.retain(|_cell, entries| {
            entries.retain(|e| &e.via_peer != peer);
            !entries.is_empty()
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cell_id(byte: u8) -> CellId {
        CellId([byte; 32])
    }

    fn make_directive(sender_byte: u8, target_byte: u8, expires: Option<u64>) -> RoutingDirective {
        RoutingDirective {
            sender: make_cell_id(sender_byte),
            target: make_cell_id(target_byte),
            authorizing_turn: [0xAA; 32],
            expires,
        }
    }

    #[test]
    fn test_apply_and_lookup() {
        let mut table = RoutingTable::new();
        let peer: SocketAddr = "192.168.1.1:9000".parse().unwrap();
        let directive = make_directive(1, 2, None);

        table.apply_directive(&directive, peer);

        let routes = table.lookup(&make_cell_id(2), 0);
        assert_eq!(routes.len(), 1);
        assert_eq!(routes[0].via_peer, peer);
        assert_eq!(routes[0].introduced_by, make_cell_id(1));
    }

    #[test]
    fn test_expiry_prunes_on_lookup() {
        let mut table = RoutingTable::new();
        let peer: SocketAddr = "192.168.1.1:9000".parse().unwrap();

        // Route that expires at height 100.
        let directive = make_directive(1, 2, Some(100));
        table.apply_directive(&directive, peer);

        // Before expiry: visible.
        let routes = table.lookup(&make_cell_id(2), 50);
        assert_eq!(routes.len(), 1);

        // At expiry height: pruned.
        let routes = table.lookup(&make_cell_id(2), 100);
        assert_eq!(routes.len(), 0);
    }

    #[test]
    fn test_prune_expired() {
        let mut table = RoutingTable::new();
        let peer: SocketAddr = "192.168.1.1:9000".parse().unwrap();

        table.apply_directive(&make_directive(1, 2, Some(50)), peer);
        table.apply_directive(&make_directive(1, 3, None), peer);
        table.apply_directive(&make_directive(1, 4, Some(200)), peer);

        assert_eq!(table.len(), 3);

        table.prune_expired(100);

        // Cell 2 expired (50 < 100), Cell 3 no expiry (kept), Cell 4 not expired (200 > 100).
        assert_eq!(table.len(), 2);
        assert!(table.lookup_immut(&make_cell_id(2)).is_empty());
        assert_eq!(table.lookup_immut(&make_cell_id(3)).len(), 1);
        assert_eq!(table.lookup_immut(&make_cell_id(4)).len(), 1);
    }

    #[test]
    fn test_remove_peer() {
        let mut table = RoutingTable::new();
        let peer_a: SocketAddr = "192.168.1.1:9000".parse().unwrap();
        let peer_b: SocketAddr = "192.168.1.2:9000".parse().unwrap();

        table.apply_directive(&make_directive(1, 2, None), peer_a);
        table.apply_directive(&make_directive(3, 2, None), peer_b);

        assert_eq!(table.len(), 2);

        table.remove_peer(&peer_a);

        assert_eq!(table.len(), 1);
        let routes = table.lookup_immut(&make_cell_id(2));
        assert_eq!(routes.len(), 1);
        assert_eq!(routes[0].via_peer, peer_b);
    }

    #[test]
    fn test_multiple_routes_same_target() {
        let mut table = RoutingTable::new();
        let peer_a: SocketAddr = "192.168.1.1:9000".parse().unwrap();
        let peer_b: SocketAddr = "192.168.1.2:9000".parse().unwrap();

        table.apply_directive(&make_directive(1, 5, None), peer_a);
        table.apply_directive(&make_directive(2, 5, None), peer_b);

        let routes = table.lookup_immut(&make_cell_id(5));
        assert_eq!(routes.len(), 2);
    }
}
