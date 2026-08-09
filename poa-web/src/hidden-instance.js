import { ArtifactRefusal } from "./poag1.js";

/**
 * The declaration every counter-7 descriptor carries IN PLACE OF its instance.
 *
 * Before the split each game shipped its answer: Signal carried `target` and an
 * `outcomes` table scored against it, Relay carried `run_seed` plus the
 * `selected` board index it drew, Salvage carried `glyph_id` on every action.
 * A reader who never played could recompute all three.
 *
 * What ships now is the complete RULE FAMILY and a statement of how the live
 * member is drawn — never which member it is. This module checks that statement.
 * It deliberately does not implement the derivation: reproducing
 * `Dregg2.Games.PathOfAngels.HiddenInstance` in JavaScript would put a second
 * copy of the draw in the client, and the client has no secret to feed it.
 *
 * Two disclosures, and they mean different things to a player:
 *
 *   oracle-only    the member is never named during the run. The host answers
 *                  questions about it and the answers land in the transcript.
 *   per-run-open   the member is opened when the run starts, so the player sees
 *                  the board they are playing. The commitment still binds it,
 *                  which is what stops the host choosing it after the fact.
 */

const DISCLOSURES = Object.freeze(["oracle-only", "per-run-open"]);
const HEX_32 = /^[0-9a-f]{64}$/;

/**
 * The two draw methods `EmitJson.symbolDrawJson` can emit, and what each one
 * costs. A byte stream is uniform; a SYMBOL below `bound` drawn out of it is not
 * automatically so, and which of the two you did is the whole difference between
 * a fair hidden target and a biased one.
 *
 *   rejection  `SeedDraw.drawBelow?` — bytes at or above `256 - 256 % bound` are
 *              DISCARDED, so every symbol has exactly `256 / bound` preimages for
 *              any bound. Uniform always; may run out of stream and refuse.
 *   modulo     bare `byte % bound`. Total, never refuses, and uniform ONLY when
 *              `bound` divides 256. Otherwise the low `256 % bound` symbols are
 *              over-represented — the defect a curator counter shipped once.
 */
const DRAW_METHODS = Object.freeze(["rejection", "modulo"]);
const SEED_DRAW_MODULE = "Dregg2.Games.PathOfAngels.SeedDraw";

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function object(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function keys(value, expected, at) {
  refuse(object(value), "instance-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  refuse(
    actual.length === wanted.length && actual.every((key, index) => key === wanted[index]),
    "instance-field",
    `${at} has an unknown or missing field`,
  );
}

function integer(value, min, max) {
  return Number.isSafeInteger(value) && value >= min && value <= max;
}

/**
 * Fields that NAMED the live instance in the pre-split bundle. A descriptor
 * carrying any of them is the old shape and is REFUSED, never reinterpreted:
 * quietly ignoring `target` would let a leaked bundle load and look healthy.
 */
export const BANNED_INSTANCE_FIELDS = Object.freeze({
  target: "states the hidden instance outright",
  run_seed: "determines the instance through the public derivation",
  outcomes: "tabulates the rules against one instance, which is the instance",
  selected: "names which member of the family is live",
  seed_byte: "names the published byte that draws it",
});

export function refuseNamedInstance(value, at) {
  for (const [field, why] of Object.entries(BANNED_INSTANCE_FIELDS)) {
    refuse(
      !object(value) || !(field in value),
      "instance-published",
      `${at} carries \`${field}\`, which ${why}; this is the pre-split POAG1 shape and must be re-emitted from Lean`,
    );
  }
}

/**
 * Parse the `symbol_draw` block, RECOMPUTING every derived field.
 *
 * ⚠ This is the one block in the declaration whose fields are not independent
 * facts: `byte_ceilings`, `consumes_rejected_bytes`, `on_exhausted` and
 * `refuses` are all FUNCTIONS of `method` and `bounds`, and the emitter computes
 * them (`EmitJson.symbolDrawJson`). A client that reads them is believing an
 * arithmetic claim it is perfectly able to check, which is the same shrug that
 * `station-panel.js` refuses for its gauges. So this recomputes all four and
 * refuses on disagreement rather than rendering the artifact's own figure back.
 *
 * It deliberately does NOT decide whether a biased draw is allowed — that is the
 * emitter's and the design gate's call, not a browser's. It reports the bias
 * (`uniform`) so the verification fold can say it out loud.
 */
export function loadSymbolDraw(block, at) {
  keys(block, [
    "method", "module", "function", "bounds", "byte_ceilings",
    "consumes_rejected_bytes", "on_exhausted", "refuses",
  ], `${at} symbol draw`);
  const method = block.method;
  refuse(DRAW_METHODS.includes(method), "instance-draw-method", `${at} symbol draw declares an unknown method`);
  const rejection = method === "rejection";
  refuse(
    Array.isArray(block.bounds) && block.bounds.length > 0 && block.bounds.every((bound) => integer(bound, 2, 256)),
    "instance-draw-bounds",
    `${at} symbol draw declares no usable bounds`,
  );
  // A rejection draw names the Lean function that performs it; a modulo draw has
  // none to name, and may not borrow the name of the one that would have been safe.
  refuse(
    rejection
      ? block.module === SEED_DRAW_MODULE && block.function === "drawBelow?"
      : block.module === null && block.function === null,
    "instance-draw-module",
    `${at} symbol draw does not name the function its method actually uses`,
  );
  const ceilings = block.bounds.map((bound) => (rejection ? 256 - (256 % bound) : 256));
  refuse(
    Array.isArray(block.byte_ceilings) && block.byte_ceilings.length === ceilings.length &&
      block.byte_ceilings.every((value, index) => value === ceilings[index]),
    "instance-draw-ceilings",
    `${at} symbol draw states byte ceilings its own method and bounds do not produce`,
  );
  const refuses = rejection && block.bounds.some((bound) => 256 % bound !== 0);
  refuse(block.consumes_rejected_bytes === rejection, "instance-draw-rejects", `${at} symbol draw disagrees with its own method about discarding bytes`);
  refuse(block.refuses === refuses, "instance-draw-exhaustion", `${at} symbol draw states an exhaustion behaviour its bounds do not produce`);
  refuse(
    block.on_exhausted === (refuses ? "refuse" : "unreachable"),
    "instance-draw-exhaustion",
    `${at} symbol draw states an exhaustion behaviour its bounds do not produce`,
  );
  // Uniformity is the fact a player would actually want, and it is NOT stated in
  // the artifact — it is derived here from the two fields that decide it.
  const uniform = rejection || block.bounds.every((bound) => 256 % bound === 0);
  return Object.freeze({
    method,
    bounds: Object.freeze([...block.bounds]),
    uniform,
    mayRunOut: refuses,
  });
}

/**
 * Parse a `per-run-hidden-draw` declaration. `expectedDisclosure` comes from the
 * signed catalog, so a descriptor cannot quietly downgrade `oracle-only` to
 * `per-run-open` and start handing the board out.
 */
export function loadHiddenInstanceDeclaration(block, expectedDisclosure, at) {
  refuse(DISCLOSURES.includes(expectedDisclosure), "instance-disclosure", `${at} expects an unknown disclosure`);
  keys(block, [
    "kind", "derivation_module", "disclosure", "symbol_draw", "commitment", "draw",
    "sponge", "practice", "operator_knows_instance",
  ], at);
  refuse(block.kind === "per-run-hidden-draw", "instance-kind", `${at} is not a per-run hidden draw`);
  refuse(block.disclosure === expectedDisclosure, "instance-disclosure", `${at} disclosure is not ${expectedDisclosure}`);
  refuse(typeof block.derivation_module === "string" && block.derivation_module.length > 0, "instance-derivation", `${at} names no derivation module`);

  keys(block.commitment, ["published_in", "domain", "preimage", "binding_bits", "opened_after"], `${at} commitment`);
  refuse(block.commitment.published_in === "slot-opening", "instance-commitment", `${at} does not publish its commitment in the slot opening`);
  refuse(block.commitment.opened_after === "slot-close", "instance-commitment", `${at} does not open its commitment at slot close`);
  refuse(integer(block.commitment.binding_bits, 100, 512), "instance-commitment", `${at} declares an implausible commitment binding`);

  const symbolDraw = loadSymbolDraw(block.symbol_draw, at);

  keys(block.draw, ["domain", "preimage", "purposes"], `${at} draw`);
  keys(block.draw.purposes, ["judged", "practice"], `${at} draw purposes`);
  refuse(
    integer(block.draw.purposes.judged, 0, 255) && integer(block.draw.purposes.practice, 0, 255) &&
      block.draw.purposes.judged !== block.draw.purposes.practice,
    "instance-draw",
    `${at} does not separate its judged and practice draw purposes`,
  );

  keys(block.sponge, [
    "permutation", "width", "rate", "capacity", "lane_bytes", "lane_reject_at_or_above", "squeeze_blocks",
  ], `${at} sponge`);

  keys(block.practice, ["seed", "scored", "purpose_tag", "transcript_field"], `${at} practice`);
  refuse(block.practice.scored === false, "instance-practice", `${at} declares practice runs scored`);
  refuse(block.practice.purpose_tag === block.draw.purposes.practice, "instance-practice", `${at} practice purpose tag disagrees with its draw`);
  refuse(block.practice.transcript_field === "mode", "instance-practice", `${at} does not separate practice from judged in the transcript`);

  return Object.freeze({
    disclosure: block.disclosure,
    derivationModule: block.derivation_module,
    symbolDraw,
    bindingBits: block.commitment.binding_bits,
    practicePurpose: block.draw.purposes.practice,
    judgedPurpose: block.draw.purposes.judged,
    // Stated, not hidden: whoever holds the slot secret knows every instance.
    // A player who wants a game the operator cannot see does not have one here.
    operatorKnowsInstance: block.operator_knows_instance === true,
  });
}

/**
 * A curator-signed slot opening. Without one there is no commitment, and without
 * a commitment the host could pick the instance after reading the transcript, so
 * a judged run refuses to start. The signature is checked upstream against the
 * curator key; this checks the shape and the mission it claims.
 */
export function loadSlotOpening(opening, missionId, at = "slot opening") {
  keys(opening, ["slot", "mission_id", "commitment", "curator_pubkey", "signature"], at);
  refuse(integer(opening.slot, 0, Number.MAX_SAFE_INTEGER), "opening-slot", `${at}.slot is invalid`);
  refuse(opening.mission_id === missionId, "opening-mission", `${at} is for a different mission`);
  refuse(typeof opening.commitment === "string" && HEX_32.test(opening.commitment), "opening-commitment", `${at}.commitment is invalid`);
  refuse(typeof opening.curator_pubkey === "string" && HEX_32.test(opening.curator_pubkey), "opening-curator", `${at}.curator_pubkey is invalid`);
  refuse(typeof opening.signature === "string" && /^[0-9a-f]{128}$/.test(opening.signature), "opening-signature", `${at}.signature is invalid`);
  return Object.freeze({ ...opening });
}
