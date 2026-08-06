import { ArtifactRefusal } from "./poag1.js";

/**
 * ONE SHAPE CHECKER FOR EVERY NODE DOCUMENT THIS PAGE READS.
 *
 * The slot publication, the station panel, the records view and the Galley
 * status all have the same contract: an EXACT key set, decided by a Lean encoder
 * or a serde struct, and a small vocabulary of field kinds (a 32-byte digest, a
 * natural, a bounded array, a bounded string). Written once because two copies
 * of "is this the exact set of keys" are two copies that will disagree the day
 * one route grows a field, and the copy that quietly tolerates it is the one
 * that will still be in the page.
 *
 * ⚠ `exactKeys` REFUSES an unknown key rather than ignoring it, and that is the
 * whole point of it. A reader that ignores unknown fields cannot distinguish a
 * node that grew a field from a node answering a different question, so it can
 * only ever claim "a superset of the shape I checked" — which is not a shape.
 * When a route legitimately grows a field, the exact set here is TAUGHT the new
 * one against the bytes that shipped. It is never widened to anything-goes.
 *
 * Every refusal is an `ArtifactRefusal`, the same class the POAG1 boundary
 * throws, so a caller has one thing to catch and one `code` to report. The codes
 * are the CALLER's: this module takes them as arguments rather than inventing a
 * `wire-*` namespace, because the code a player sees should name the organ that
 * refused, not the helper that noticed.
 */

const HEX_32 = /^[0-9a-f]{64}$/;

export function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

export function isPlainObject(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

/**
 * The exact key set, no more and no less.
 *
 * `codes.shape` is for "this is not an object at all"; `codes.field` is for "it
 * is an object with the wrong keys". They are distinct because they mean
 * different things about the sender: the first got the document wrong, the
 * second got the version wrong.
 */
export function exactKeys(value, expected, at, codes) {
  refuse(isPlainObject(value), codes.shape, `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  refuse(
    actual.length === wanted.length && actual.every((key, index) => key === wanted[index]),
    codes.field,
    `${at} has an unknown or missing field; the exact set is: ${wanted.join(", ")}`,
  );
  return value;
}

export function digest32(value, at, code) {
  refuse(typeof value === "string" && HEX_32.test(value), code, `${at} must be 64 lowercase hexadecimal digits`);
  return value;
}

export function natural(value, at, code) {
  refuse(Number.isSafeInteger(value) && value >= 0, code, `${at} must be a non-negative safe integer`);
  return value;
}

export function bool(value, at, code) {
  refuse(typeof value === "boolean", code, `${at} must be a boolean`);
  return value;
}

/**
 * A string with a length bound. Every text field on these routes is either a
 * label from a Lean encoder or an operator-authored claim, and both are short;
 * an unbounded one is a document this page should not have been handed.
 */
export function text(value, at, code, max = 4096) {
  refuse(typeof value === "string" && value.length > 0 && value.length <= max, code, `${at} must be text of at most ${max} characters`);
  return value;
}

/** An array with a length bound, so one served document cannot become a render loop. */
export function boundedArray(value, at, code, max) {
  refuse(Array.isArray(value) && value.length <= max, code, `${at} must be an array of at most ${max} entries`);
  return value;
}

export { HEX_32 };
