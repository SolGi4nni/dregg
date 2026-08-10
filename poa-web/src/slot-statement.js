/**
 * The ONE spelling of the bytes a curator signs to open a slot.
 *
 * It lives alone in its own module because two different readers must reproduce
 * it identically — `today-board.js`, checking the opening published BEFORE a
 * session, and `slot-opening-receipt.js`, checking the reveal published after the
 * slot closes. A second copy would be a second encoding, and the failure it
 * produces is the worst kind available here: a signature that verifies against
 * bytes that are not the statement beside them.
 *
 * The encoding is pinned on three other sides that never call this one —
 * `persist/src/poa_signal_slot.rs`'s `PoaSlotOpeningStatementV1::signing_message`,
 * `poa-curator/src/slot_opening.rs`'s independent re-derivation, and
 * `node/src/poa_slot_reveal_verify.rs` — so a change here that is not made there
 * stops the next ceremony rather than shipping quietly.
 */

export const STATEMENT_SCHEMA = "POA-SLOT-OPENING-STATEMENT-1";

/**
 * The exact bytes the curator signed, rebuilt field by field in the documented
 * order.
 *
 * ⚠ Written as one template rather than `JSON.stringify(received)` on purpose:
 * stringifying what arrived would re-serialise whatever order and whatever extra
 * keys the node sent, which is verifying a signature against the attacker's bytes
 * with extra steps.
 */
export function slotStatementMessage(statement) {
  return `{"schema":"${STATEMENT_SCHEMA}","authority_id":"${statement.authorityId}",` +
    `"mission_id":${statement.missionId},"slot":${statement.slot},"commitment":"${statement.commitment}"}`;
}
