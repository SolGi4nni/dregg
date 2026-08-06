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
 * Parse a `per-run-hidden-draw` declaration. `expectedDisclosure` comes from the
 * signed catalog, so a descriptor cannot quietly downgrade `oracle-only` to
 * `per-run-open` and start handing the board out.
 */
export function loadHiddenInstanceDeclaration(block, expectedDisclosure, at) {
  refuse(DISCLOSURES.includes(expectedDisclosure), "instance-disclosure", `${at} expects an unknown disclosure`);
  keys(block, [
    "kind", "derivation_module", "disclosure", "commitment", "draw", "sponge",
    "practice", "operator_knows_instance",
  ], at);
  refuse(block.kind === "per-run-hidden-draw", "instance-kind", `${at} is not a per-run hidden draw`);
  refuse(block.disclosure === expectedDisclosure, "instance-disclosure", `${at} disclosure is not ${expectedDisclosure}`);
  refuse(typeof block.derivation_module === "string" && block.derivation_module.length > 0, "instance-derivation", `${at} names no derivation module`);

  keys(block.commitment, ["published_in", "domain", "preimage", "binding_bits", "opened_after"], `${at} commitment`);
  refuse(block.commitment.published_in === "slot-opening", "instance-commitment", `${at} does not publish its commitment in the slot opening`);
  refuse(block.commitment.opened_after === "slot-close", "instance-commitment", `${at} does not open its commitment at slot close`);
  refuse(integer(block.commitment.binding_bits, 100, 512), "instance-commitment", `${at} declares an implausible commitment binding`);

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
