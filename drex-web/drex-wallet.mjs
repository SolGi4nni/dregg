// drex-wallet.mjs — the DrEX wallet adapter over the REAL Dragon's Egg
// Cipherclerk wasm (extension/dregg_wasm.js + dregg_wasm_bg.wasm).
//
// Everything this module returns marked { grade: 'ATTESTED' | 'PROVED' } is
// produced by the SAME wasm the browser extension ships — no mock, no stub.
// It loads the identical dregg_wasm.js the extension loads as a
// web-accessible resource, instantiates the identical 50MB wasm, and calls the
// identical exported entry points:
//
//   cipherclerk_make_action_turn  → a REAL Ed25519-signed dregg Turn (the order)
//   assemble_signed_turn_envelope → the REAL hybrid ed25519 + ML-DSA-65 (FIPS-204)
//                                    SignedTurn wire envelope
//   prove_conservation            → a REAL conservation proof: Schnorr excess
//                                    (value balance) + one Bulletproof range
//                                    proof per output (bulletproofs v5)
//   verify_conservation_proof     → the REAL verifier (native on wasm32)
//   prove_anonymous_membership    → a REAL blinded ring-membership tag
//
// Isomorphic: browser fetches the wasm from the dev server's /wasm/ mount;
// Node reads it straight from ../extension.

let wb = null;

function extUrlsForNode() {
  // drex-web/drex-wallet.mjs → ../extension/
  const base = new URL('../extension/', import.meta.url);
  return {
    js: new URL('dregg_wasm.js', base),
    bin: new URL('dregg_wasm_bg.wasm', base),
  };
}

export async function initWallet(opts = {}) {
  if (wb) return wb;
  let code, bytes;
  if (typeof window === 'undefined') {
    const fs = await import('node:fs');
    const { js, bin } = extUrlsForNode();
    code = fs.readFileSync(js, 'utf8');
    bytes = fs.readFileSync(bin);
  } else {
    const jsUrl = opts.wasmJsUrl || '/wasm/dregg_wasm.js';
    const binUrl = opts.wasmBinUrl || '/wasm/dregg_wasm_bg.wasm';
    code = await (await fetch(jsUrl)).text();
    bytes = new Uint8Array(await (await fetch(binUrl)).arrayBuffer());
  }
  // The extension ships dregg_wasm.js as a classic script that binds a global
  // `wasm_bindgen`; wrap-and-return it without polluting the page.
  wb = new Function(code + '\nreturn wasm_bindgen;')();
  await wb({ module_or_path: bytes });
  return wb;
}

const hex = (u8) => Array.from(u8).map(b => b.toString(16).padStart(2, '0')).join('');
const enc = (s) => new TextEncoder().encode(s);
const rand32 = () => {
  const u = new Uint8Array(32);
  (globalThis.crypto || require('crypto').webcrypto).getRandomValues(u);
  return u;
};
const randHex = () => hex(rand32());

// A deterministic 32-byte "cipherclerk secret key" for a named trader (demo
// key material — a real wallet holds this in the extension's sealed store).
export function traderKey(seedByte) {
  return Uint8Array.from({ length: 32 }, (_, i) => (i * 7 + seedByte * 13 + 3) & 0xff);
}

// ── STEP A — sign the order-turn (REAL Ed25519 + hybrid PQ envelope) ──
// The order card the user approved in confirm-intent becomes the memo of a real
// signed dregg Turn. Returns the turn_id (canonical turn hash), the agent cell,
// and the hybrid SignedTurn envelope bytes (the exact POST /turns/submit-signed
// wire), all produced by the wallet wasm.
export function signOrderTurn(order, key) {
  const memo = JSON.stringify(order);
  const spec = JSON.stringify({
    sender_privkey: Array.from(key),
    method: 'drex_place_order',
    memo_json: memo,
  });
  const turn = wb.cipherclerk_make_action_turn(spec); // real Ed25519 over canonical action bytes
  let envelopeBytes = null;
  try {
    const tb = Array.isArray(turn.turn_bytes)
      ? Uint8Array.from(turn.turn_bytes)
      : enc(JSON.stringify(turn.turn_bytes));
    envelopeBytes = wb.assemble_signed_turn_envelope(tb, key); // hybrid ed25519 + ML-DSA-65
  } catch (_e) { /* envelope is a bonus; the signed Turn already stands */ }
  return {
    grade: 'ATTESTED',
    turnId: turn.turn_id,
    agentCell: turn.agent_cell_id,
    memo,
    turnBytesLen: Array.isArray(turn.turn_bytes) ? turn.turn_bytes.length : null,
    envelopeLen: envelopeBytes ? envelopeBytes.length : null,
    envelopeHex: envelopeBytes ? hex(envelopeBytes.slice(0, 16)) + '…' : null,
  };
}

// ── STEP B — prove solvency of the order (REAL conservation proof) ──
// Solvency statement: holdings = offer + change, with a Bulletproof range proof
// per output ⇒ change ≥ 0 ⇒ holdings ≥ offer (the offer is covered), AND every
// output is a non-negative 64-bit value (the negative-value / mod-wrap inflation
// attack is ruled out). The proof is BOUND to this exact order via
// message_hex = the order-turn id: tamper the order and the id changes and the
// proof no longer verifies. Fail-closed: a trader who does not hold ≥ offer
// cannot construct the proof (change would be negative — no valid u64 output).
export function proveSolvency(holdings, offer, orderTurnId) {
  if (holdings < offer) {
    return { grade: 'ATTESTED', ok: false, reason: 'insufficient holdings — cannot construct a non-negative change output (fail-closed)' };
  }
  const change = holdings - offer;
  const inputs = JSON.stringify([{ value: holdings, blinding_hex: randHex() }]);
  const outputs = JSON.stringify([
    { value: offer, blinding_hex: randHex() },
    { value: change, blinding_hex: randHex() },
  ]);
  const messageHex = orderTurnId; // BINDS the proof to the exact signed order
  const proof = wb.prove_conservation(inputs, outputs, messageHex);
  const v = wb.verify_conservation_proof(
    JSON.stringify(proof.input_commitments),
    JSON.stringify(proof.output_commitments),
    JSON.stringify(proof.proof),
    proof.message_hex,
    JSON.stringify(proof.output_range_proofs),
  );
  return {
    grade: 'ATTESTED',
    ok: v.valid && v.range_proofs_checked,
    valid: v.valid,
    rangeProofsChecked: v.range_proofs_checked,
    holdings, offer, change,
    messageHex,
    inputCommitments: proof.input_commitments.length,
    outputCommitments: proof.output_commitments.length,
    rangeProofs: (proof.output_range_proofs || []).length,
    proof, // kept so the app can re-verify / a tamper demo
  };
}

// Tamper demo: re-verify the same proof against a different message (a
// substituted order). Real verifier ⇒ valid:false.
export function tamperCheck(solvency, forgedOrderTurnId) {
  const p = solvency.proof;
  const v = wb.verify_conservation_proof(
    JSON.stringify(p.input_commitments),
    JSON.stringify(p.output_commitments),
    JSON.stringify(p.proof),
    forgedOrderTurnId,
    JSON.stringify(p.output_range_proofs),
  );
  return { valid: v.valid, error: v.error || null };
}

// ── STEP C — prove trading eligibility (REAL blinded ring membership) ──
// Prove the trader is in the exchange's eligible-trader ring WITHOUT revealing
// which member — the sealed-bid anonymity property. Returns a presentation tag
// (the double-spend / one-order-per-batch nullifier) and the set root.
export function proveEligibility(traderIdHex, ringHexIds) {
  const r = wb.prove_anonymous_membership(traderIdHex, JSON.stringify(ringHexIds));
  return {
    grade: 'ATTESTED',
    presentationTag: r.presentation_tag_full_hex,
    setRoot: r.set_root,
    ringSize: r.ring_size,
    proofSizeBytes: r.proof_size_bytes,
  };
}

// ── sealed-bid commit / reveal (SealedAuction.lean realization) ──
// Commit phase (before batch T): publish H(order || salt), hiding the order.
// Reveal phase (at T): publish (order, salt); anyone checks the hash binds.
export async function sealedCommit(order, salt) {
  const bytes = enc(JSON.stringify(order) + '|' + salt);
  const subtle = (globalThis.crypto && globalThis.crypto.subtle)
    || (await import('node:crypto')).webcrypto.subtle;
  const digest = new Uint8Array(await subtle.digest('SHA-256', bytes));
  return hex(digest);
}
export async function sealedReveal(commit, order, salt) {
  const recomputed = await sealedCommit(order, salt);
  return { ok: recomputed === commit, commit, recomputed };
}

export { randHex, hex };
