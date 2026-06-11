// src/sse.ts — the incremental SSE parser the background uses to consume the
// node's receipt stream (/api/events/stream). The frame shapes here mirror
// what node/src/events.rs emits: `event: receipt` + `id: <chain index>` +
// one JSON data line, plus `: hb` keep-alive comments every 30s.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createSseParser } from './.build/sse.mjs';

test('parses a node receipt frame', () => {
  const p = createSseParser();
  const events = p.feed('event: receipt\nid: 4\ndata: {"receipt_hash":"abc"}\n\n');
  assert.equal(events.length, 1);
  assert.deepEqual(events[0], { event: 'receipt', data: '{"receipt_hash":"abc"}', id: '4' });
});

test('reassembles frames split across arbitrary chunk boundaries', () => {
  const frame = 'event: receipt\nid: 7\ndata: {"chain_index":7}\n\n';
  for (const splitAt of [1, 5, 14, frame.length - 2]) {
    const p = createSseParser();
    const first = p.feed(frame.slice(0, splitAt));
    const rest = p.feed(frame.slice(splitAt));
    const events = [...first, ...rest];
    assert.equal(events.length, 1, `split at ${splitAt}`);
    assert.equal(events[0].id, '7');
    assert.equal(events[0].event, 'receipt');
  }
});

test('heartbeat comments produce no events', () => {
  const p = createSseParser();
  assert.deepEqual(p.feed(': hb\n\n: hb\n\n'), []);
});

test('multiple frames in one chunk, multi-line data, CRLF endings', () => {
  const p = createSseParser();
  const events = p.feed(
    'event: receipt\r\nid: 1\r\ndata: {"a":\r\ndata: 1}\r\n\r\n' +
    'data: plain\n\n',
  );
  assert.equal(events.length, 2);
  assert.equal(events[0].data, '{"a":\n1}');
  assert.equal(events[0].id, '1');
  assert.equal(events[1].event, 'message'); // no event: field -> default
  assert.equal(events[1].data, 'plain');
});

test('id persists across frames (Last-Event-ID resume semantics)', () => {
  const p = createSseParser();
  const first = p.feed('id: 3\ndata: x\n\n');
  const second = p.feed('data: y\n\n');
  assert.equal(first[0].id, '3');
  assert.equal(second[0].id, '3'); // unchanged until the server sends a new one
});
