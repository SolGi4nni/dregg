# pyana-gallery

Federated art gallery with commit-reveal auctions on the pyana protocol.

## Quick Start

```bash
# Headless demo (no server needed)
cargo run -p pyana-gallery --example demo

# Full API demo (starts server, exercises HTTP endpoints)
cargo run -p pyana-gallery --example devnet_gallery

# Or with curl (requires server running separately)
cargo run -p pyana-gallery
./demo.sh
```

## Architecture

```
Federation nodes (3-node devnet)
    | wire protocol
Gallery Backend (axum API server using pyana-sdk)
    | REST/WebSocket
Browser Frontend (vanilla JS/HTML using WASM SDK + browser extension)
```

## API Endpoints

```
GET  /artworks              List all artworks
GET  /artworks/:id          Artwork details + provenance
POST /artworks              Register new artwork
GET  /auctions              List active auctions
GET  /auctions/:id          Auction details + bid history
POST /auctions              Create auction for artwork
POST /auctions/:id/bid      Submit bid commitment
POST /auctions/:id/reveal   Reveal bid
GET  /auctions/:id/result   Settlement result
WS   /ws                    Live updates
POST /admin/height          Advance block height (devnet)
POST /admin/settle/:id      Trigger settlement (devnet)
GET  /health                Health check
```

## Auction Lifecycle

1. **Register** artwork (artist signs, creates cell)
2. **Create** auction (artist specifies duration, reserve)
3. **Bid** phase: bidders submit BLAKE3 commitments (amounts hidden)
4. **Reveal** phase: bidders prove their commitments
5. **Settle**: TurnComposer atomically transfers ownership + payment
6. **Provenance** updated with new owner

## Pyana Primitives Used

- **Cells**: Each artwork is a cell
- **Capabilities**: Ownership as delegatable capability
- **Commit-Reveal**: BLAKE3 bid commitments
- **Escrow**: Bidder funds locked during auction
- **TurnComposer**: Atomic multi-party settlement
- **ConditionalTurn**: Auto-refund for losing bidders
- **TemporalPredicate**: Block-height phase enforcement
