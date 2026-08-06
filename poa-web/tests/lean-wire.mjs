import assert from "node:assert/strict";

/**
 * READ THE KEY SET OUT OF THE LEAN ENCODER THAT EMITS IT.
 *
 * Every document this page parses is checked against an EXACT key set, and an
 * exact set is only a contract while it is the same set the emitter produces.
 * Held against a copy of itself it is decoration; held against
 * `Reply.toJson` / `ViewWire.toJson` it is a gate, and the day a Lean encoder
 * grows, moves, or renames a field it goes red HERE — at a name, in a test —
 * instead of in a browser as a total refusal nobody can read.
 *
 * This reads the emitted key names out of an encoder body: the encoders are
 * hand-written string concatenations of the form `",\"field\":" ++ …`, so the
 * keys are literally in the source in emission order.
 */

const DECLARATION = /\n(?:private\s+|protected\s+|partial\s+|noncomputable\s+)*(?:def|theorem|abbrev|instance|structure|inductive|@\[)/;

export function encoderBody(source, encoder) {
  const start = source.indexOf(`def ${encoder}`);
  assert.notEqual(start, -1, `the Lean encoder ${encoder} is gone; this guard names a definition that no longer exists`);
  const rest = source.slice(start + `def ${encoder}`.length);
  const end = rest.search(DECLARATION);
  return rest.slice(0, end === -1 ? rest.length : end);
}

/** The key names one Lean encoder emits, in emission order. */
export function emittedKeys(source, encoder) {
  return [...encoderBody(source, encoder).matchAll(/\\"([a-z0-9_]+)\\":/g)].map((match) => match[1]);
}

/**
 * The guard's own self-check.
 *
 * A key-set guard that has stopped seeing keys passes silently and forever, so
 * every caller runs this first: the extractor must find a known field of a
 * specimen encoder, and must find nothing in a body that emits no keys.
 */
export function assertEncoderReaderWorks(source, encoder, expectedMember) {
  const keys = emittedKeys(source, encoder);
  assert.ok(keys.length > 0, `the encoder reader found no keys in ${encoder} — it has stopped reading Lean`);
  assert.ok(keys.includes(expectedMember), `the encoder reader no longer sees ${expectedMember} in ${encoder}`);
  assert.deepEqual(emittedKeys('def Nothing.toJson (x : X) : String :=\n  "[]"\n', "Nothing.toJson"), [],
    "the encoder reader invents keys where an encoder emits none");
}
