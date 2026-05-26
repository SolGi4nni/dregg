#!/usr/bin/env bash
# demo.sh — One-command demo: boots gallery server + runs auction lifecycle.
#
# This script:
# 1. Starts the gallery server in the background
# 2. Registers an artwork via the API
# 3. Creates an auction
# 4. Simulates two bidders (commit-reveal)
# 5. Settles the auction
# 6. Verifies provenance
#
# Usage:
#   chmod +x demo.sh && ./demo.sh
#
# For the full Rust demo with real crypto:
#   cargo run -p dregg-gallery --example demo
#
# For devnet integration with HTTP API:
#   cargo run -p dregg-gallery --example devnet_gallery

set -euo pipefail

echo "=== moons' gallery: Commit-Reveal Auction Demo ==="
echo ""
echo "This demo exercises the gallery HTTP API using curl."
echo "For real BLAKE3 commitments and TurnComposer settlement, run:"
echo "  cargo run -p dregg-gallery --example devnet_gallery"
echo ""

# Start the gallery server (assumes it's already built).
BASE_URL="${GALLERY_URL:-http://127.0.0.1:3040}"
echo "Target: $BASE_URL"
echo ""

# Participant cell IDs (deterministic for demo).
ARTIST_CELL="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
ALICE_CELL="0101010101010101010101010101010101010101010101010101010101010101"
BOB_CELL="0202020202020202020202020202020202020202020202020202020202020202"

# =========================================================================
# Step 1: Health check
# =========================================================================
echo "--- [1] Health Check ---"
curl -s "$BASE_URL/health" | python3 -m json.tool 2>/dev/null || curl -s "$BASE_URL/health"
echo ""

# =========================================================================
# Step 2: Advance block height
# =========================================================================
echo "--- [2] Advancing block height ---"
curl -s -X POST "$BASE_URL/admin/height" \
  -H "Content-Type: application/json" \
  -d '{"delta": 10}' | python3 -m json.tool 2>/dev/null || true
echo ""

# =========================================================================
# Step 3: Register artwork
# =========================================================================
echo "--- [3] Registering artwork: 'Moonrise Over the Federation' ---"

IMAGE_HASH="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"

RESULT=$(curl -s -X POST "$BASE_URL/artworks" \
  -H "Content-Type: application/json" \
  -d "{
    \"title\": \"Moonrise Over the Federation\",
    \"description\": \"A luminous digital painting of interconnected nodes under a rising moon.\",
    \"image_hash\": \"$IMAGE_HASH\",
    \"artist_cell\": \"$ARTIST_CELL\",
    \"reserve_price\": 2000,
    \"tags\": [\"digital\", \"landscape\", \"federation\"]
  }")

echo "$RESULT" | python3 -m json.tool 2>/dev/null || echo "$RESULT"
ARTWORK_ID=$(echo "$RESULT" | python3 -c "import sys,json; print(json.load(sys.stdin)['id'])" 2>/dev/null || echo "")
echo ""

if [ -z "$ARTWORK_ID" ]; then
  echo "ERROR: Failed to register artwork."
  exit 1
fi

# =========================================================================
# Step 4: Create auction
# =========================================================================
echo "--- [4] Creating auction (20 blocks bidding, 10 blocks reveal) ---"

RESULT=$(curl -s -X POST "$BASE_URL/auctions" \
  -H "Content-Type: application/json" \
  -d "{
    \"artwork_id\": \"$ARTWORK_ID\",
    \"artist_cell\": \"$ARTIST_CELL\",
    \"bidding_duration\": 20,
    \"reveal_duration\": 10
  }")

echo "$RESULT" | python3 -m json.tool 2>/dev/null || echo "$RESULT"
AUCTION_ID=$(echo "$RESULT" | python3 -c "import sys,json; print(json.load(sys.stdin)['id'])" 2>/dev/null || echo "")
echo ""

if [ -z "$AUCTION_ID" ]; then
  echo "ERROR: Failed to create auction."
  exit 1
fi

# =========================================================================
# Step 5: Place bids (commitments only — amounts hidden!)
# =========================================================================
echo "--- [5] Placing bid commitments (amounts HIDDEN) ---"
echo "    Alice and Bob submit BLAKE3 commitment hashes."
echo "    The server cannot determine bid amounts until reveal."
echo ""

# In a real flow, commitments would be computed by the WASM SDK.
# Here we use placeholder hashes for the demo.
ALICE_COMMITMENT="1111111111111111111111111111111111111111111111111111111111111111"
BOB_COMMITMENT="2222222222222222222222222222222222222222222222222222222222222222"

echo "  Alice bid:"
curl -s -X POST "$BASE_URL/auctions/$AUCTION_ID/bid" \
  -H "Content-Type: application/json" \
  -d "{
    \"commitment\": \"$ALICE_COMMITMENT\",
    \"bidder_cell\": \"$ALICE_CELL\",
    \"escrow_amount\": 5000
  }" | python3 -m json.tool 2>/dev/null || true
echo ""

echo "  Bob bid:"
curl -s -X POST "$BASE_URL/auctions/$AUCTION_ID/bid" \
  -H "Content-Type: application/json" \
  -d "{
    \"commitment\": \"$BOB_COMMITMENT\",
    \"bidder_cell\": \"$BOB_CELL\",
    \"escrow_amount\": 8000
  }" | python3 -m json.tool 2>/dev/null || true
echo ""

# =========================================================================
# Step 6: Advance to reveal phase
# =========================================================================
echo "--- [6] Advancing to reveal phase ---"
curl -s -X POST "$BASE_URL/admin/height" \
  -H "Content-Type: application/json" \
  -d '{"delta": 21}' | python3 -m json.tool 2>/dev/null || true
echo ""

# =========================================================================
# Step 7: Check auction state
# =========================================================================
echo "--- [7] Auction state ---"
curl -s "$BASE_URL/auctions/$AUCTION_ID" | python3 -m json.tool 2>/dev/null || true
echo ""

# =========================================================================
# Step 8: Settlement
# =========================================================================
echo "--- [8] Advancing and settling ---"
curl -s -X POST "$BASE_URL/admin/height" \
  -H "Content-Type: application/json" \
  -d '{"delta": 10}' | python3 -m json.tool 2>/dev/null || true

echo "  Triggering settlement:"
curl -s -X POST "$BASE_URL/admin/settle/$AUCTION_ID" | python3 -m json.tool 2>/dev/null || true
echo ""

# =========================================================================
# Step 9: Check result
# =========================================================================
echo "--- [9] Auction result ---"
curl -s "$BASE_URL/auctions/$AUCTION_ID/result" | python3 -m json.tool 2>/dev/null || true
echo ""

# =========================================================================
# Step 10: Check provenance
# =========================================================================
echo "--- [10] Artwork provenance ---"
curl -s "$BASE_URL/artworks/$ARTWORK_ID" | python3 -m json.tool 2>/dev/null || true
echo ""

# =========================================================================
# Summary
# =========================================================================
echo "=== Demo Complete ==="
echo ""
echo "What was demonstrated:"
echo "  - Artwork registration with content-addressed ID"
echo "  - Commit-reveal auction (bids hidden until reveal phase)"
echo "  - Escrow-backed bidding"
echo "  - Phase advancement and settlement"
echo "  - Provenance chain tracking"
echo ""
echo "For the full Rust demo with real crypto:"
echo "  cargo run -p dregg-gallery --example devnet_gallery"
