// src/explain.ts — the extension's port of sdk/src/explain.rs renderings.
//
// These tests pin the PROSE PARITY contract: the extension must describe a
// turn in the same human terms the SDK's `explain_effect` / `auth_mode` /
// `explain_turn` render. If sdk/src/explain.rs rewording lands, these
// hardcoded strings fail and force the port to follow.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { effectBody, authMode, explainAction, explainTurn, hx32 } from './.build/explain.mjs';

const cid = (n) => Array(32).fill(n);
const cidHex = (n) => n.toString(16).padStart(2, '0').repeat(32);

test('effect prose matches sdk/src/explain.rs effect_body word-for-word', () => {
  const cases = [
    [{ Transfer: { from: cid(1), to: cid(2), amount: 5 } },
      `transfer 5 computrons from cell ${cidHex(1)} to cell ${cidHex(2)}`],
    [{ SetField: { cell: cid(1), index: 2, value: cid(7) } },
      `set state field #2 of cell ${cidHex(1)} to 0x${cidHex(7)}`],
    [{ GrantCapability: { from: cid(1), to: cid(2), cap: { target: cid(9), slot: 3 } } },
      `grant capability (target ${cidHex(9)} slot 3) from cell ${cidHex(1)} to cell ${cidHex(2)}`],
    [{ RevokeCapability: { cell: cid(1), slot: 4 } },
      `revoke capability in slot 4 of cell ${cidHex(1)}`],
    [{ EmitEvent: { cell: cid(1), event: { topic: cid(3), data: [cid(1)] } } },
      `emit event (topic 0x${cidHex(3)}, 1 data field(s)) from cell ${cidHex(1)}`],
    [{ IncrementNonce: { cell: cid(1) } },
      `increment the nonce of cell ${cidHex(1)}`],
    [{ CreateCell: { public_key: cid(1), token_id: cid(2), balance: 100 } },
      `create a new cell (owner 0x${cidHex(1)}, token 0x${cidHex(2)}) with balance 100`],
    [{ SetPermissions: { cell: cid(1), new_permissions: {} } },
      `set the permissions of cell ${cidHex(1)} (applied last in the action)`],
    [{ SetVerificationKey: { cell: cid(1), new_vk: null } },
      `set the verification key of cell ${cidHex(1)} to none (applied last in the action)`],
    [{ NoteSpend: { value: 10, asset_type: 0 } },
      'spend a private note (value 10, asset 0)'],
    [{ NoteCreate: { value: 10, asset_type: 0 } },
      'create a private note (value 10, asset 0)'],
    [{ SpawnWithDelegation: { child_public_key: cid(1), max_staleness: 60 } },
      `spawn a child cell (owner 0x${cidHex(1)}) with a delegation snapshot (max staleness 60s)`],
    // Unit variant arrives as a bare string on the JSON wire.
    ['RefreshDelegation',
      "refresh this cell's delegation snapshot from its parent"],
    [{ RevokeDelegation: { child: cid(2) } },
      `revoke delegation to child cell ${cidHex(2)} (by bumping the parent epoch)`],
    [{ BridgeMint: { portable_proof: {} } },
      'mint a note locally from a portable cross-federation spend proof'],
    [{ Introduce: { introducer: cid(1), recipient: cid(2), target: cid(3) } },
      `introduce cell ${cidHex(1)} to cell ${cidHex(2)} on target cell ${cidHex(3)}`],
    [{ PipelinedSend: { target: {}, action: { effects: [1] } } },
      'pipeline a send to an eventual ref, carrying 1 sub-effect(s)'],
    [{ ExerciseViaCapability: { cap_slot: 0, inner_effects: [1] } },
      'exercise the capability in slot 0, performing 1 inner effect(s)'],
    [{ MakeSovereign: { cell: cid(1) } },
      `make cell ${cidHex(1)} sovereign (store only its state commitment)`],
    [{ CreateCellFromFactory: { factory_vk: cid(13), owner_pubkey: cid(1), token_id: cid(2) } },
      `create a cell from factory 0x${cidHex(13)} (owner 0x${cidHex(1)}, token 0x${cidHex(2)})`],
    [{ Refusal: { cell: cid(1), offered_action_commitment: cid(18) } },
      `record a refusal on cell ${cidHex(1)} of offered action 0x${cidHex(18)}`],
    [{ CellSeal: { target: cid(1), reason: cid(20) } },
      `seal cell ${cidHex(1)} (reason commitment 0x${cidHex(20)})`],
    [{ CellUnseal: { target: cid(1) } },
      `unseal cell ${cidHex(1)} (return it to live)`],
    [{ CellDestroy: { target: cid(1), certificate: {} } },
      `permanently destroy cell ${cidHex(1)} (bind its death certificate)`],
    [{ Burn: { target: cid(1), slot: 0, amount: 5 } },
      `burn 5 from slot 0 of cell ${cidHex(1)} (supply reduced, disclosed)`],
    [{ AttenuateCapability: { cell: cid(1), slot: 0 } },
      `narrow (attenuate) the capability in slot 0 of cell ${cidHex(1)}`],
    [{ ReceiptArchive: { prefix_end_height: 42, checkpoint: {} } },
      "archive this cell's receipt-chain prefix up to height 42"],
  ];
  for (const [effect, expected] of cases) {
    const r = effectBody(effect);
    assert.equal(r.body, expected);
    assert.equal(r.unknown, false, `marked unknown: ${JSON.stringify(effect)}`);
  }
});

test('authorization modes match sdk/src/explain.rs auth_mode', () => {
  const cases = [
    [{ Signature: [cid(1), cid(2)] }, 'an Ed25519 signature'],
    [{ Proof: { proof_bytes: [], bound_action: '', bound_resource: '' } }, 'a zero-knowledge proof'],
    [{ Breadstuff: cid(1) }, 'a capability token'],
    [{ Bearer: {} }, 'a bearer capability (delegation chain)'],
    ['Unchecked', 'NO authorization (unchecked — only valid if the cell permits)'],
    [{ CapTpDelivered: {} }, 'a verified CapTP delivery certificate'],
    [{ Custom: {} }, 'an app-defined witnessed predicate'],
    [{ OneOf: {} }, 'one of several candidate authorizations'],
    [{ Stealth: {} }, 'a one-time stealth key'],
    [{ Token: {} }, 'a biscuit/macaroon credential'],
  ];
  for (const [auth, expected] of cases) {
    const r = authMode(auth);
    assert.equal(r.mode, expected);
    assert.equal(r.unknown, false);
  }
});

test('explainTurn renders the whole forest and binds the canonical turn hash', () => {
  const turn = {
    agent: cid(1),
    nonce: 5,
    fee: 100,
    memo: null,
    call_forest: {
      roots: [{
        action: {
          target: cid(1),
          authorization: 'Unchecked',
          balance_change: null,
          effects: [
            { Transfer: { from: cid(1), to: cid(2), amount: 5 } },
            { IncrementNonce: { cell: cid(1) } },
          ],
        },
        children: [{
          action: {
            target: cid(2),
            authorization: { Signature: [cid(3), cid(4)] },
            balance_change: 7,
            effects: ['RefreshDelegation'],
          },
          children: [],
          hash: cid(0),
        }],
        hash: cid(0),
      }],
      forest_hash: cid(0),
    },
  };
  const turnId = 'ab'.repeat(32);
  const r = explainTurn(turn, turnId);
  assert.equal(r.hasUnknown, false);
  const expected =
    `Turn by agent ${cidHex(1)} (nonce 5, fee 100)\n` +
    '2 action(s) in the call forest:\n' +
    `[0] Action on cell ${cidHex(1)}, authorized by NO authorization (unchecked — only valid if the cell permits):\n` +
    '  2 effect(s):\n' +
    `    1. transfer 5 computrons from cell ${cidHex(1)} to cell ${cidHex(2)}\n` +
    `    2. increment the nonce of cell ${cidHex(1)}\n` +
    '\n' +
    `[1] Action on cell ${cidHex(2)}, authorized by an Ed25519 signature, balance change 7:\n` +
    '  1 effect(s):\n' +
    "    1. refresh this cell's delegation snapshot from its parent\n" +
    '\n' +
    `[turn ${turnId}]`;
  assert.equal(r.text, expected);
});

test('memo is rendered when present', () => {
  const turn = { agent: cid(1), nonce: 0, fee: 0, memo: 'hello', call_forest: { roots: [] } };
  const r = explainTurn(turn, '00'.repeat(32));
  assert.match(r.text, /memo "hello"/);
});

test('unknown effect/authorization variants are surfaced, never elided', () => {
  const e = effectBody({ TotallyNewEffect: { cell: cid(1) } });
  assert.equal(e.unknown, true);
  assert.match(e.body, /UNKNOWN effect "TotallyNewEffect"/);

  const a = explainAction({
    target: cid(1),
    authorization: { FutureAuth: {} },
    effects: [{ AlsoNew: {} }],
  });
  assert.equal(a.hasUnknown, true);

  const turn = {
    agent: cid(1), nonce: 0, fee: 0, memo: null,
    call_forest: { roots: [{ action: { target: cid(1), authorization: 'Unchecked', effects: [{ Mystery: {} }] }, children: [] }] },
  };
  assert.equal(explainTurn(turn, '00'.repeat(32)).hasUnknown, true);
});

test('the [turn ...] tag separates renderings of different turns', () => {
  const turn = { agent: cid(1), nonce: 0, fee: 0, memo: null, call_forest: { roots: [] } };
  const a = explainTurn(turn, 'aa'.repeat(32));
  const b = explainTurn(turn, 'bb'.repeat(32));
  assert.notEqual(a.text, b.text);
});

test('hx32 is total over malformed input', () => {
  assert.equal(hx32(null), '??');
  assert.equal(hx32(undefined), '??');
  assert.equal(hx32('nope'), '??');
  assert.equal(hx32([0, 255]), '00ff');
});
