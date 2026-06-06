// starbridge-apps/storage-gateway-mandate/pages/turn-builders.js
//
// JS shim for storage-gateway mandate turn presets. Mirrors build_storage_*_action
// and build_init_gateway_action in src/lib.rs.

const OBJECT_KEY_SLOT = 0;
const LAST_OP_SLOT = 1;
const VOLUME_SPENT_SLOT = 2;
const COMMITMENT_ANCHOR_SLOT = 3;
const VOLUME_CEILING_SLOT = 4;
const KEY_PREFIX_HASH_SLOT = 5;
const READ_COMPARTMENT_SLOT = 6;

const OP_GET = 0;
const OP_PUT = 1;
const OP_LIST = 2;

const OP_COST = { GET: 1, PUT: 5, LIST: 2 };

function u64BE(n) {
  const view = new Uint8Array(32);
  const bn = BigInt(n);
  for (let i = 0; i < 8; i += 1) {
    view[31 - i] = Number((bn >> BigInt(i * 8)) & 0xffn);
  }
  return Array.from(view);
}

async function keyField(key) {
  if (window.dregg?.blake3) {
    return window.dregg.blake3(new TextEncoder().encode(key));
  }
  const buf = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(key));
  return Array.from(new Uint8Array(buf));
}

function fieldToU64(bytes) {
  let v = 0n;
  for (let i = 24; i < 32; i += 1) {
    v = (v << 8n) | BigInt(bytes?.[i] ?? 0);
  }
  return Number(v);
}

/**
 * Generic storage op — mirrors build_storage_op_action.
 */
async function storage_op(gatewayUri, opCode, objectKey, spent, blobHash = 0) {
  const keyFieldVal = await keyField(objectKey);
  const newSpent = spent + (opCode === OP_GET ? OP_COST.GET : opCode === OP_PUT ? OP_COST.PUT : OP_COST.LIST);
  const opName = opCode === OP_GET ? 'GET' : opCode === OP_PUT ? 'PUT' : 'LIST';
  return window.dregg.signTurn({
    target: gatewayUri,
    method: `storage_${opName.toLowerCase()}`,
    effects: [
      { kind: 'SetField', cell: gatewayUri, index: OBJECT_KEY_SLOT, value: keyFieldVal },
      { kind: 'SetField', cell: gatewayUri, index: LAST_OP_SLOT, value: u64BE(opCode) },
      { kind: 'SetField', cell: gatewayUri, index: VOLUME_SPENT_SLOT, value: u64BE(newSpent) },
      {
        kind: 'EmitEvent',
        cell: gatewayUri,
        topic: 'storage-op-committed',
        data: [keyFieldVal, u64BE(opCode), u64BE(newSpent), u64BE(blobHash)],
      },
    ],
  });
}

async function storage_get(gatewayUri, objectKey) {
  const cell = await window.dregg.readCell(gatewayUri);
  const spent = fieldToU64(cell?.state?.fields?.[VOLUME_SPENT_SLOT]);
  return storage_op(gatewayUri, OP_GET, objectKey, spent);
}

async function storage_put(gatewayUri, objectKey, blobHash = 0) {
  const cell = await window.dregg.readCell(gatewayUri);
  const spent = fieldToU64(cell?.state?.fields?.[VOLUME_SPENT_SLOT]);
  return storage_op(gatewayUri, OP_PUT, objectKey, spent, blobHash);
}

async function storage_list(gatewayUri, prefix = 'uploads/') {
  const cell = await window.dregg.readCell(gatewayUri);
  const spent = fieldToU64(cell?.state?.fields?.[VOLUME_SPENT_SLOT]);
  return storage_op(gatewayUri, OP_LIST, prefix, spent);
}

async function init_gateway(gatewayUri, opts = {}) {
  const anchor = opts.commitmentAnchor ?? 42;
  const ceiling = opts.volumeCeiling ?? 10;
  const prefix = opts.keyPrefix ?? 'uploads/';
  const readComp = opts.readCompartment ?? 'storage-read';
  const prefixHash = await keyField(prefix);
  const readHash = await keyField(readComp);
  return window.dregg.signTurn({
    target: gatewayUri,
    method: 'init_gateway',
    effects: [
      { kind: 'SetField', cell: gatewayUri, index: COMMITMENT_ANCHOR_SLOT, value: u64BE(anchor) },
      { kind: 'SetField', cell: gatewayUri, index: VOLUME_CEILING_SLOT, value: u64BE(ceiling) },
      { kind: 'SetField', cell: gatewayUri, index: KEY_PREFIX_HASH_SLOT, value: prefixHash },
      { kind: 'SetField', cell: gatewayUri, index: READ_COMPARTMENT_SLOT, value: readHash },
      {
        kind: 'EmitEvent',
        cell: gatewayUri,
        topic: 'storage-gateway-initialized',
        data: [u64BE(anchor), u64BE(ceiling), prefixHash, readHash],
      },
    ],
  });
}

const builders = { storage_get, storage_put, storage_list, init_gateway };

if (typeof window !== 'undefined') {
  window.dregg = window.dregg || {};
  window.dregg.builders = window.dregg.builders || {};
  window.dregg.builders.storageGatewayMandate = builders;
}

export { storage_get, storage_put, storage_list, init_gateway, builders };