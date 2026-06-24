/**
 * SAMPLE SNAPSHOT runtime — the explorer's clearly-labeled offline fallback.
 *
 * When the devnet is unreachable the explorer offers (never auto-substitutes
 * silently) this static, deterministic snapshot so the inspector surfaces can
 * be browsed. EVERY surface that renders it is labeled SAMPLE: the connection
 * chrome switches to "SAMPLE DATA", a persistent banner stays on screen, and
 * every object carries `sample: true` plus a `_sample_note`.
 *
 * The shapes mirror the node API responses the RemoteRuntime normalizes
 * (ReceiptInfo / CellDetailResponse / federation + block views) so the SAME
 * platform inspectors render it — no bespoke sample-only rendering paths.
 * The story told is real-shaped: two agent cells and one factory-born escrow
 * cell (cell/src/blueprint.rs lifecycle UNINIT → OPEN → RELEASED) with a
 * receipt chain whose pre/post state commitments chain correctly.
 */

import { attachRuntimeObjectAdapter } from '../_includes/studio/runtime-object-adapter.js';

const NOTE = 'SAMPLE DATA — not from a node. The devnet was unreachable; this is a labeled static snapshot.';

// Deterministic, visibly-synthetic 64-hex ids (repeating tag + counter).
function sid(tag, n) {
  const word = (tag + n).padEnd(8, '0').slice(0, 8);
  return word.repeat(8).slice(0, 64).replace(/[^0-9a-f]/g, 'e');
}

const ALICE = sid('a11ce', 1);
const BOB = sid('b0b', 1);
const ESCROW = sid('e5c0', 1);

const T0 = 1765000000; // fixed sample epoch (seconds)

function receipt(i, { agent, pre, post, effects, witness = 0, proof = false }) {
  return {
    sample: true,
    _sample_note: NOTE,
    chain_index: i,
    chain_head: false,
    receipt_hash: sid('cafe', i),
    turn_hash: sid('cafe', i),
    agent,
    pre_state: pre,
    post_state: post,
    timestamp: T0 + i * 60,
    computrons_used: 40 + i * 7,
    action_count: 1,
    previous_receipt_hash: i > 0 ? sid('cafe', i - 1) : null,
    finality: 'committed',
    was_encrypted: false,
    was_burn: false,
    has_proof: proof,
    executor_signed: true,
    has_witness: witness > 0,
    witness_count: witness,
    effect_kinds: effects,
    touched_cells: [agent === ESCROW ? ALICE : ESCROW, agent],
  };
}

const RECEIPTS = [
  receipt(0, { agent: ALICE, pre: sid('57a7e', 0), post: sid('57a7e', 1), effects: ['create_cell_from_factory'], proof: true }),
  receipt(1, { agent: ALICE, pre: sid('57a7e', 1), post: sid('57a7e', 2), effects: ['set_field'], witness: 1, proof: true }),
  receipt(2, { agent: ALICE, pre: sid('57a7e', 2), post: sid('57a7e', 3), effects: ['transfer'], proof: true }),
  receipt(3, { agent: ESCROW, pre: sid('57a7e', 3), post: sid('57a7e', 4), effects: ['set_field'], witness: 1, proof: true }),
  receipt(4, { agent: ESCROW, pre: sid('57a7e', 4), post: sid('57a7e', 5), effects: ['set_field', 'transfer'], witness: 2, proof: true }),
  receipt(5, { agent: BOB, pre: sid('57a7e', 5), post: sid('57a7e', 6), effects: ['increment_nonce'] }),
];
RECEIPTS[RECEIPTS.length - 1].chain_head = true;

const CELLS = {
  [ALICE]: {
    sample: true, _sample_note: NOTE, id: ALICE, cell_id: ALICE, found: true,
    balance: 750, nonce: 3, capability_count: 2, num_capabilities: 2,
    has_delegate: false, delegate: null, has_program: false,
    public_key: sid('ab1e', 7), token_id: sid('70cen', 1),
    proved_state: true, delegation_epoch: 0,
    state_commitment: sid('57a7e', 6), program_kind: 'None',
    fields: new Array(8).fill('0'.repeat(64)),
  },
  [BOB]: {
    sample: true, _sample_note: NOTE, id: BOB, cell_id: BOB, found: true,
    balance: 250, nonce: 1, capability_count: 1, num_capabilities: 1,
    has_delegate: false, delegate: null, has_program: false,
    public_key: sid('b0bb', 7), token_id: sid('70cen', 2),
    proved_state: true, delegation_epoch: 0,
    state_commitment: sid('57a7e', 6), program_kind: 'None',
    fields: new Array(8).fill('0'.repeat(64)),
  },
  [ESCROW]: {
    sample: true, _sample_note: NOTE, id: ESCROW, cell_id: ESCROW, found: true,
    balance: 0, nonce: 2, capability_count: 0, num_capabilities: 0,
    has_delegate: false, delegate: null, has_program: true,
    public_key: sid('e5c0', 7), token_id: sid('70cen', 3),
    proved_state: true, delegation_epoch: 0,
    state_commitment: sid('57a7e', 6), program_kind: 'Predicate',
    // escrow slot story: STATE=2 (RESOLVED_A/released), VALUE=250, parties, condition, witness
    fields: [
      '0'.repeat(63) + '2',
      '0'.repeat(60) + '00fa',
      sid('a11ce', 1), sid('b0b', 1),
      '0'.repeat(63) + '7',
      '0'.repeat(64),
      '0'.repeat(64),
      '0'.repeat(63) + '7',
    ],
    program: {
      kind: 'Predicate',
      constraints: [
        { kind: 'AllowedTransitions', slot_index: 0, allowed: [['0', '0'], ['0', '1'], ['1', '1'], ['1', '2'], ['1', '3']] },
        { kind: 'Immutable', index: 2 },
        { kind: 'Immutable', index: 3 },
      ],
    },
  },
};

const BLOCKS = [
  { sample: true, _sample_note: NOTE, height: 1, hash: sid('b10c', 1), prev_hash: '0'.repeat(64), proposer: 'sample-node-0', timestamp: T0, receipt_count: 3 },
  { sample: true, _sample_note: NOTE, height: 2, hash: sid('b10c', 2), prev_hash: sid('b10c', 1), proposer: 'sample-node-0', timestamp: T0 + 180, receipt_count: 3 },
];

const FEDERATIONS = [
  { sample: true, _sample_note: NOTE, federation_id: sid('fed', 1), name: 'sample-federation (SAMPLE)', committee_size: 1, height: 2 },
];

const INTENTS = [
  { sample: true, _sample_note: NOTE, intent_id: sid('1d:ea', 1), id: sid('1d:ea', 1), kind: 'storage (SAMPLE)', status: 'open' },
];

/**
 * Build a read-only runtime over the snapshot, with the same signal-shaped
 * surface as the RemoteRuntime so every platform inspector works unchanged.
 */
export function createSampleRuntime({ signals }) {
  const { signal } = signals;
  const sig = (v) => signal(v);
  const cellList = Object.values(CELLS).map((c) => ({ ...c }));
  const notPermitted = (op) => () => { throw new Error(`${op}: the SAMPLE snapshot is read-only`); };

  const cellSignals = new Map();
  const receiptSignals = new Map();

  return attachRuntimeObjectAdapter({
    caps: { readOnly: true, sample: true },
    source: { kind: 'sample', label: 'SAMPLE snapshot (devnet unreachable)' },
    sample: true,
    sampleNote: NOTE,
    version: sig(1),
    cursor: sig(2),
    events: new EventTarget(),

    listCells: () => sig(cellList),
    getCell(id) {
      const key = String(id || '').toLowerCase();
      if (!cellSignals.has(key)) cellSignals.set(key, sig(CELLS[key] ? { ...CELLS[key] } : null));
      return cellSignals.get(key);
    },
    listReceipts: () => sig(RECEIPTS.map((r) => ({ ...r, pre_state_hash: r.pre_state, post_state_hash: r.post_state }))),
    listCellReceipts(id) {
      const want = String(id || '').toLowerCase();
      return sig(RECEIPTS
        .filter((r) => r.agent === want || (r.touched_cells || []).includes(want))
        .map((r) => ({ ...r, pre_state_hash: r.pre_state, post_state_hash: r.post_state })));
    },
    getReceipt(id) {
      const want = String(id || '').toLowerCase();
      if (!receiptSignals.has(want)) {
        const r = RECEIPTS.find((x) => x.receipt_hash === want || x.turn_hash === want) || null;
        receiptSignals.set(want, sig(r ? { ...r, pre_state_hash: r.pre_state, post_state_hash: r.post_state } : null));
      }
      return receiptSignals.get(want);
    },
    getTurn(id) { return this.getReceipt(id); },
    listBlocks: () => sig(BLOCKS),
    getBlock: () => sig(BLOCKS[BLOCKS.length - 1]),
    listIntents: () => sig(INTENTS),
    getIntent: (id) => sig(INTENTS.find((i) => i.intent_id === String(id || '').toLowerCase()) || null),
    listCapabilities: () => sig([]),
    getCapability: () => sig(null),
    getOutbox: () => sig([]),
    listKnownFederations: () => sig(FEDERATIONS),
    getFederation: () => sig(FEDERATIONS[0]),
    getTraceEvents: () => sig([]),

    createAgent: notPermitted('createAgent'),
    createCell: notPermitted('createCell'),
    executeTurn: notPermitted('executeTurn'),
    mintToken: notPermitted('mintToken'),
    advanceHeight: notPermitted('advanceHeight'),

    destroy() {},
  });
}

export const SAMPLE_IDS = { ALICE, BOB, ESCROW };
export const SAMPLE_NOTE = NOTE;
