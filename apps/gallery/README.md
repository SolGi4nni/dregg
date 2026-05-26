# `dregg` Gallery

Privacy-preserving art auction platform with zero-knowledge proofs.

## Quick Start

```bash
# Headless demo
cargo run -p dregg-gallery --example demo

# Full API server
cargo run -p dregg-gallery --example devnet_gallery

# Production
cargo build --release -p dregg-gallery
DREGG_ADMIN_TOKEN=secret ./target/release/dregg-gallery --listen 0.0.0.0:3000
```

## Auction Modes

| Mode | Privacy Level | Best For |
|------|--------------|----------|
| Sealed-bid (commit-reveal) | Bids hidden until reveal | Simple auctions |
| Vickrey (second-price) | Incentive-compatible | High-value items |
| Private Vickrey Phase 1-4 | Full (see below) | Maximum confidentiality |
| Dutch (descending) | First buyer wins | Editions, drops |

### Private Vickrey Auction

A single protocol that achieves full auction privacy. Nobody learns anything except "an auction concluded correctly" — not the bids, not the payment amount, not who won.

**What's hidden:**
- All bid amounts (federation collectively garbles the comparison circuit; no single party sees any bid)
- The payment amount (output is a Pedersen commitment, not a plaintext number)
- The winner's identity (ring membership proof proves "a valid bidder settled" without revealing which one)
- The delivery address (one-time stealth address, unlinkable across auctions)

**How it works (one protocol, sequential steps):**
1. Federation nodes collectively garble a second-price comparison circuit (distributed randomness, no single node sees the tables)
2. Each bidder obtains their input labels via oblivious transfer with each federation node (no node learns which labels were selected)
3. Anyone evaluates the garbled circuit → output is a Pedersen commitment to the second price (not plaintext)
4. The winner (identified by threshold-decrypted index) decrypts the committed price and produces:
   - A ring membership proof ("I am one of the N bidders")
   - A committed payment matching the auction output (equality proof)
   - A stealth address for artwork delivery
5. Federation verifies all proofs without learning identity or amount

**Publicly verifiable:** A STARK proof of correct circuit evaluation is produced. Anyone can verify the auction was conducted fairly.

**Cryptographic guarantees:** Computational (STARK soundness, Pedersen binding, ring membership). Not trust-based.

## Architecture

```
Browser (frontend/)         Extension (window.dregg.signTurn)
    |                           |
    +------ REST + WebSocket ---+
                |
    Axum Server (server.rs)
                |
    DreggEngine (turns, proofs)
                |
    Blocklace (consensus, finality)
```

## API

```
GET  /artworks              List all artworks
GET  /artworks/:id          Details + provenance chain
POST /artworks              Register (artist signs)
GET  /auctions              Active auctions
GET  /auctions/:id          State + bid history
POST /auctions              Create (reserve, duration, mode)
POST /auctions/:id/bid      Submit commitment
POST /auctions/:id/reveal   Reveal (amount + nonce)
WS   /ws                    Live events
POST /admin/settle          Trigger settlement
POST /admin/height          Advance height
GET  /health                Health check
```

## Settlement

Atomic via TurnComposer:
- Winner's escrow releases → payment to artist
- Ownership capability → delegated to winner
- Both happen or neither (journal rollback)
- Losers auto-refunded (ConditionalTurn timeout)

## Provenance

Verifiable ownership chain:
- Each transfer = capability delegation
- Integrity-checked (tamper-evident)
- Factory provenance tracked (EROS)
- Anyone can audit the full history

## Configuration

| Variable | Purpose | Default |
|----------|---------|---------|
| `DREGG_ADMIN_TOKEN` | Admin auth | (unset = open) |
| `DREGG_STATE_FILE` | Persistence | `gallery_state.json` |
| `DREGG_NODE_URL` | Node API | `http://localhost:8080` |

## Cryptography

BLAKE3 (commitments), Garbled Circuits (private comparison), Oblivious Transfer (label selection), Threshold Decryption (federation decode), Pedersen/Ristretto (committed values), Schnorr (equality proofs), Bulletproofs (range), Ring Membership/BlindedMerkle (anonymity), Stealth Addresses/X25519 (unlinkable delivery), STARK (verifiable evaluation), ChaCha20-Poly1305 (winner decryption).

## Anti-Sniping

Bids within the last 2 blocks of deadline extend it by 3 blocks. Configurable via `AntiSnipingConfig`.

## Frontend

`frontend/` — vanilla HTML/JS/CSS:
- Dark theme, responsive
- WebSocket live updates
- Client-side commitment generation (amounts never leave browser)
- Extension bridge for signing
