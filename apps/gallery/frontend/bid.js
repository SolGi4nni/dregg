/**
 * bid.js — Bidding logic: commitment generation, reveal protocol.
 *
 * Implements the client-side of the commit-reveal bidding protocol:
 * 1. Generate a random nonce
 * 2. Compute commitment = BLAKE3(bidder_cell || amount_le || nonce)
 * 3. Store (amount, nonce) locally for reveal phase
 * 4. Submit commitment to the server
 * 5. During reveal phase, submit (amount, nonce) to prove the commitment
 */

const Bidding = (() => {
    // Local storage key prefix for bid secrets.
    const STORAGE_PREFIX = 'dregg_gallery_bid_';

    /**
     * Generate a cryptographic random nonce (32 bytes).
     * Returns hex-encoded string.
     */
    function generateNonce() {
        const bytes = new Uint8Array(32);
        crypto.getRandomValues(bytes);
        return bytesToHex(bytes);
    }

    /**
     * Compute a bid commitment: BLAKE3(bidder_cell || amount_le || nonce).
     *
     * This uses a simplified hash for the browser demo. In production,
     * the WASM SDK provides the real BLAKE3 keyed derivation.
     *
     * @param {string} bidderCell - Hex-encoded bidder cell ID (64 chars).
     * @param {number} amount - Bid amount as integer.
     * @param {string} nonce - Hex-encoded nonce (64 chars).
     * @returns {string} Hex-encoded commitment hash (64 chars).
     */
    function computeCommitment(bidderCell, amount, nonce) {
        // Concatenate: bidder_cell (32 bytes) || amount (8 bytes LE) || nonce (32 bytes)
        const bidderBytes = hexToBytes(bidderCell);
        const amountBytes = new Uint8Array(8);
        const view = new DataView(amountBytes.buffer);
        view.setBigUint64(0, BigInt(amount), true); // little-endian
        const nonceBytes = hexToBytes(nonce);

        // Combine all bytes.
        const combined = new Uint8Array(bidderBytes.length + amountBytes.length + nonceBytes.length);
        combined.set(bidderBytes, 0);
        combined.set(amountBytes, bidderBytes.length);
        combined.set(nonceBytes, bidderBytes.length + amountBytes.length);

        // BLAKE3-like hash (simplified for demo; real version uses WASM BLAKE3).
        return blake3Hash(combined);
    }

    /**
     * Create a bid (generate nonce, compute commitment, store secrets).
     *
     * @param {string} auctionId - The auction to bid on.
     * @param {string} bidderCell - The bidder's cell ID.
     * @param {number} amount - The bid amount.
     * @returns {object} { commitment, nonce, amount }
     */
    function createBid(auctionId, bidderCell, amount) {
        const nonce = generateNonce();
        const commitment = computeCommitment(bidderCell, amount, nonce);

        // Store bid secrets locally for reveal phase.
        const bidData = {
            auctionId,
            bidderCell,
            amount,
            nonce,
            commitment,
            timestamp: Date.now(),
        };

        localStorage.setItem(
            STORAGE_PREFIX + auctionId + '_' + bidderCell,
            JSON.stringify(bidData)
        );

        return { commitment, nonce, amount };
    }

    /**
     * Retrieve stored bid data for reveal.
     *
     * @param {string} auctionId - The auction ID.
     * @param {string} bidderCell - The bidder's cell ID.
     * @returns {object|null} Stored bid data, or null if not found.
     */
    function getStoredBid(auctionId, bidderCell) {
        const key = STORAGE_PREFIX + auctionId + '_' + bidderCell;
        const data = localStorage.getItem(key);
        return data ? JSON.parse(data) : null;
    }

    /**
     * Verify a commitment matches the expected inputs.
     *
     * @param {string} commitment - The commitment to verify.
     * @param {string} bidderCell - The bidder's cell ID.
     * @param {number} amount - The claimed amount.
     * @param {string} nonce - The claimed nonce.
     * @returns {boolean} True if the commitment is valid.
     */
    function verifyCommitment(commitment, bidderCell, amount, nonce) {
        const expected = computeCommitment(bidderCell, amount, nonce);
        return expected === commitment;
    }

    /**
     * List all stored bids for the current user.
     *
     * @returns {Array} Array of stored bid objects.
     */
    function listStoredBids() {
        const bids = [];
        for (let i = 0; i < localStorage.length; i++) {
            const key = localStorage.key(i);
            if (key && key.startsWith(STORAGE_PREFIX)) {
                try {
                    bids.push(JSON.parse(localStorage.getItem(key)));
                } catch (e) {
                    // Skip malformed entries.
                }
            }
        }
        return bids;
    }

    /**
     * Clear stored bid data after successful reveal.
     */
    function clearBid(auctionId, bidderCell) {
        localStorage.removeItem(STORAGE_PREFIX + auctionId + '_' + bidderCell);
    }

    // =========================================================================
    // Utility functions
    // =========================================================================

    function bytesToHex(bytes) {
        return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
    }

    function hexToBytes(hex) {
        const bytes = new Uint8Array(hex.length / 2);
        for (let i = 0; i < bytes.length; i++) {
            bytes[i] = parseInt(hex.substr(i * 2, 2), 16);
        }
        return bytes;
    }

    /**
     * Simplified BLAKE3 hash for browser demo.
     *
     * NOTE: In production, this is replaced by the dregg WASM SDK which
     * provides real BLAKE3 with keyed derivation ("dregg-gallery-bid-commitment-v1").
     * This demo version uses a simpler hash that produces deterministic 32-byte output.
     */
    function blake3Hash(data) {
        // Use SubtleCrypto SHA-256 as a stand-in for BLAKE3 in the demo.
        // For synchronous operation in the demo, use a simple hash.
        let h0 = 0x6a09e667;
        let h1 = 0xbb67ae85;
        let h2 = 0x3c6ef372;
        let h3 = 0xa54ff53a;
        let h4 = 0x510e527f;
        let h5 = 0x9b05688c;
        let h6 = 0x1f83d9ab;
        let h7 = 0x5be0cd19;

        for (let i = 0; i < data.length; i++) {
            const v = data[i];
            h0 = (h0 ^ v) * 0x01000193 | 0;
            h1 = (h1 ^ (v << 1)) * 0x01000193 | 0;
            h2 = (h2 ^ (v << 2)) * 0x01000193 | 0;
            h3 = (h3 ^ (v << 3)) * 0x01000193 | 0;
            h4 = (h4 ^ (v << 4)) * 0x01000193 | 0;
            h5 = (h5 ^ (v << 5)) * 0x01000193 | 0;
            h6 = (h6 ^ (v << 6)) * 0x01000193 | 0;
            h7 = (h7 ^ (v << 7)) * 0x01000193 | 0;
        }

        const result = new Uint8Array(32);
        const view = new DataView(result.buffer);
        view.setInt32(0, h0, true);
        view.setInt32(4, h1, true);
        view.setInt32(8, h2, true);
        view.setInt32(12, h3, true);
        view.setInt32(16, h4, true);
        view.setInt32(20, h5, true);
        view.setInt32(24, h6, true);
        view.setInt32(28, h7, true);

        return bytesToHex(result);
    }

    return {
        generateNonce,
        computeCommitment,
        createBid,
        getStoredBid,
        verifyCommitment,
        listStoredBids,
        clearBid,
    };
})();
