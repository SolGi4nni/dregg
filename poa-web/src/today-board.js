import { ArtifactRefusal } from "./poag1.js";
import { STATION_CREW_ROUTE, STATION_PANEL_ROUTE } from "./station-panel.js";

/**
 * WHAT IS TRUE RIGHT NOW — and, where nothing is, the honest shape of the
 * absence.
 *
 * Four tiles: what is on the rack, is a judged slot open, what does the salvage
 * crate hold, what is the ship's headline figure. Each one is EITHER a value this
 * page actually fetched and checked, OR a sealed tile that says why there is no
 * value. There is no third option and no placeholder: a fabricated number here
 * would be the most expensive kind, because it is the first thing anybody reads.
 *
 * ⚠ A SUCCESSFUL REQUEST IS NOT A VERDICT. `open: true` off the wire means the
 * node said so. This module re-derives the exact statement bytes the curator
 * signed — the encoding is pinned in `poa_signal_slot_api.rs`, which deliberately
 * does NOT publish the pre-encoded message so a client cannot verify a signature
 * against bytes it was handed — and checks the Ed25519 against the curator key
 * the content bundle is already pinned to. An opening that does not verify
 * presents as REFUSED, never as closed and never as open.
 */

const SLOT_FORMAT = "POA-SIGNAL-SLOT-1";
const STATEMENT_SCHEMA = "POA-SLOT-OPENING-STATEMENT-1";
const HEX_32 = /^[0-9a-f]{64}$/;
const HEX_64 = /^[0-9a-f]{128}$/;

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function object(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function exactKeys(value, expected, at) {
  refuse(object(value), "slot-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  refuse(
    actual.length === wanted.length && actual.every((key, index) => key === wanted[index]),
    "slot-field",
    `${at} has an unknown or missing field; the exact set is: ${wanted.join(", ")}`,
  );
}

function hexBytes(hex) {
  return Uint8Array.from(hex.match(/../g) ?? [], (pair) => Number.parseInt(pair, 16));
}

/**
 * The exact bytes the curator signed, rebuilt field by field in the documented
 * order. Written as one template rather than `JSON.stringify(received)` on
 * purpose: stringifying what arrived would re-serialise whatever order and
 * whatever extra keys the node sent, which is verifying a signature against the
 * attacker's bytes with extra steps.
 */
export function slotStatementMessage(statement) {
  return `{"schema":"${STATEMENT_SCHEMA}","authority_id":"${statement.authorityId}",` +
    `"mission_id":${statement.missionId},"slot":${statement.slot},"commitment":"${statement.commitment}"}`;
}

/** Parse a published slot document. Shape only; the signature is checked after. */
export function parseSlotDocument(value, authorityId) {
  exactKeys(value, ["format", "authority_id", "federation_id", "open", "opening", "consensus_finality"], "slot publication");
  refuse(value.format === SLOT_FORMAT, "slot-format", `unsupported slot publication format: ${value.format}`);
  refuse(value.authority_id === authorityId, "slot-authority", "slot publication is for another authority");
  refuse(typeof value.federation_id === "string" && HEX_32.test(value.federation_id), "slot-federation", "slot publication federation id is invalid");
  refuse(typeof value.open === "boolean", "slot-open", "slot publication `open` must be a boolean");
  refuse(typeof value.consensus_finality === "string", "slot-finality", "slot publication must restate its finality position");
  if (value.open === false) {
    refuse(value.opening === null, "slot-open", "a closed slot must publish no opening");
    return Object.freeze({ open: false, opening: null, consensusFinality: value.consensus_finality });
  }
  exactKeys(value.opening, ["statement", "curator_key", "signature"], "slot opening");
  const statement = value.opening.statement;
  exactKeys(statement, ["schema", "authority_id", "mission_id", "slot", "commitment"], "slot opening statement");
  refuse(statement.schema === STATEMENT_SCHEMA, "slot-statement", "unsupported slot opening statement schema");
  refuse(statement.authority_id === authorityId, "slot-statement", "slot opening statement names another authority");
  refuse(Number.isSafeInteger(statement.mission_id) && statement.mission_id >= 0, "slot-statement", "slot opening mission id is invalid");
  refuse(Number.isSafeInteger(statement.slot) && statement.slot >= 0, "slot-statement", "slot number is invalid");
  refuse(typeof statement.commitment === "string" && HEX_32.test(statement.commitment), "slot-statement", "slot commitment is invalid");
  refuse(typeof value.opening.curator_key === "string" && HEX_32.test(value.opening.curator_key), "slot-curator", "slot opening curator key is invalid");
  refuse(typeof value.opening.signature === "string" && HEX_64.test(value.opening.signature), "slot-signature", "slot opening signature is invalid");
  return Object.freeze({
    open: true,
    consensusFinality: value.consensus_finality,
    opening: Object.freeze({
      statement: Object.freeze({
        schema: statement.schema,
        authorityId: statement.authority_id,
        missionId: statement.mission_id,
        slot: statement.slot,
        commitment: statement.commitment,
      }),
      curatorKey: value.opening.curator_key,
      signature: value.opening.signature,
    }),
  });
}

async function verifyOpening(opening, curatorPublicKey) {
  refuse(
    typeof curatorPublicKey === "string" && HEX_32.test(curatorPublicKey),
    "slot-curator-pin",
    "verifying a slot opening needs the curator key the content bundle is pinned to",
  );
  refuse(
    opening.curatorKey === curatorPublicKey,
    "slot-curator-pin",
    "the published slot opening names a curator key that is not this deployment's pin",
  );
  const subtle = globalThis.crypto?.subtle;
  refuse(subtle, "crypto-unavailable", "Web Crypto Ed25519 is required to check a slot opening");
  let key;
  try { key = await subtle.importKey("raw", hexBytes(curatorPublicKey), { name: "Ed25519" }, false, ["verify"]); }
  catch (cause) { throw new ArtifactRefusal("ed25519-unavailable", "curator Ed25519 key could not be imported", cause); }
  const message = new TextEncoder().encode(slotStatementMessage(opening.statement));
  const valid = await subtle.verify({ name: "Ed25519" }, key, hexBytes(opening.signature), message);
  refuse(valid, "slot-bad-signature", "the published slot opening is not signed by the pinned curator key");
  return true;
}

/**
 * Read the published slot for this authority.
 *
 * Never throws: every failure is a STATE. `unreachable` and `refused` both mean
 * "no judged play here", which is the safe direction — this can only ever fail
 * toward practice, never toward claiming a slot that is not open.
 */
export async function loadSlotState({ authorityId, curatorPublicKey, baseUrl, fetchImpl = globalThis.fetch, prefix = "/node" } = {}) {
  if (typeof authorityId !== "string" || !HEX_32.test(authorityId)) {
    return Object.freeze({ state: "unreachable", code: "slot-authority", reason: "This terminal has no authority id to ask about" });
  }
  if (typeof fetchImpl !== "function") {
    return Object.freeze({ state: "unreachable", code: "slot-fetch", reason: "No fetch is available in this environment" });
  }
  const url = new URL(`${prefix}/api/poa/signal/${authorityId}/slot`, baseUrl ?? globalThis.location?.href ?? "https://invalid.local/");
  let document;
  try {
    const response = await fetchImpl(url, { cache: "no-store", credentials: "same-origin" });
    if (!response?.ok) {
      return Object.freeze({ state: "unreachable", code: "slot-status", reason: `The authority answered HTTP ${response?.status ?? "nothing"}` });
    }
    document = JSON.parse(await response.text());
  } catch {
    return Object.freeze({ state: "unreachable", code: "slot-fetch", reason: "No PoA authority answered on this origin" });
  }
  let parsed;
  try {
    parsed = parseSlotDocument(document, authorityId);
  } catch (error) {
    return Object.freeze({ state: "refused", code: error?.code ?? "slot-shape", reason: error?.message ?? "the slot publication was refused" });
  }
  if (!parsed.open) {
    return Object.freeze({ state: "closed", consensusFinality: parsed.consensusFinality });
  }
  try {
    await verifyOpening(parsed.opening, curatorPublicKey);
  } catch (error) {
    return Object.freeze({ state: "refused", code: error?.code ?? "slot-bad-signature", reason: error?.message ?? "the slot opening did not verify" });
  }
  return Object.freeze({
    state: "open",
    slot: parsed.opening.statement.slot,
    missionId: parsed.opening.statement.missionId,
    commitment: parsed.opening.statement.commitment,
    consensusFinality: parsed.consensusFinality,
  });
}

/**
 * The salvage crate, read off the station.
 *
 * ⚠ THIS PIN WAS `null` AND IS NOT ANY MORE. It used to say "no node serves a
 * crate surface", which was true when it was written and stopped being true in
 * `21294c52d` without anything noticing — the guard that was supposed to notice
 * had been keyed on the substring `crate`, and the route that landed spells it
 * `station`. The tile went on saying "not wired yet" for as long as that took.
 *
 * So the pin now names the route this page actually reads, and the guard in
 * `tests/today-board.test.mjs` checks BOTH directions: the route named here must
 * exist in the node, and the node's station routes must be the ones named here.
 * A rename on either side reds it; neither side can drift quietly.
 *
 * `crewRoute` is recorded but never called. It takes a 64-hex crew key and this
 * terminal binds no crew identity, so asking it would mean inventing one.
 */
export const CRATE_SURFACE = Object.freeze({
  id: "crate",
  route: STATION_PANEL_ROUTE,
  crewRoute: STATION_CREW_ROUTE,
});

function slotTile(slot) {
  if (!slot) {
    return { id: "slot", eyebrow: "JUDGED SLOT", state: "pending", headline: "Asking the authority", detail: "Reading whether a curator-committed slot is open." };
  }
  if (slot.state === "open") {
    return {
      id: "slot",
      eyebrow: "JUDGED SLOT",
      state: "live",
      headline: `Slot ${slot.slot} is open`,
      detail: `Commitment ${slot.commitment.slice(0, 16)}…, signed by this deployment's pinned curator key and checked here. A judged run can be submitted; it settles only once a node finalizes it.`,
    };
  }
  if (slot.state === "closed") {
    return {
      id: "slot",
      eyebrow: "JUDGED SLOT",
      state: "sealed",
      headline: "No slot is open",
      detail: "The authority publishes no curator-committed opening, so every drill on the rack is practice. That is the ordinary state, not a fault.",
    };
  }
  if (slot.state === "refused") {
    return {
      id: "slot",
      eyebrow: "JUDGED SLOT",
      state: "refused",
      headline: "Slot publication refused",
      detail: `An opening was published and this terminal would not accept it (${slot.code}). Practice only.`,
    };
  }
  return {
    id: "slot",
    eyebrow: "JUDGED SLOT",
    state: "sealed",
    headline: "No authority answered",
    detail: `${slot.reason}. Every drill on the rack is practice.`,
  };
}

/**
 * ⚠ The eyebrow says SALVAGE CRATE and not DAILY CRATE, and the copy never says
 * "today". The station carries no current-period pointer — `SalvageCrate.State`
 * has no public producer — so this tile cannot know which period is live, and a
 * word implying a day turned over would be the page inventing the one fact the
 * organ deliberately does not publish.
 */
function crateTile(station) {
  if (!station || station.state === "pending") {
    return { id: "crate", eyebrow: "SALVAGE CRATE", state: "pending", headline: "Reading the crate", detail: "Asking the station what the authored crate holds." };
  }
  if (station.state === "refused") {
    return {
      id: "crate",
      eyebrow: "SALVAGE CRATE",
      state: "refused",
      headline: "Station panel refused",
      detail: `A panel was served and this terminal would not accept it (${station.code}). No crate figure is shown.`,
    };
  }
  if (station.state !== "ready") {
    return {
      id: "crate",
      eyebrow: "SALVAGE CRATE",
      state: "sealed",
      headline: "No station answered",
      detail: `${station.reason}. Nothing about the crate is claimed here.`,
    };
  }
  const doc = station.view.station;
  const schedule = `${doc.tableRows} loot row${doc.tableRows === 1 ? "" : "s"} and ${doc.ticketCount} ticket entries across periods ${doc.opensAt}–${doc.closesAt}`;
  const noPointer = "There is no current-period pointer on this route, so which period is live is not a question it answers: the rotation is the whole authored schedule, not one day of it.";
  if (doc.admitted > 0) {
    return {
      id: "crate",
      eyebrow: "SALVAGE CRATE",
      state: "live",
      headline: `${doc.admitted} opening${doc.admitted === 1 ? "" : "s"} admitted`,
      detail: `The station reports ${doc.observed} observed and ${doc.admitted} admitted against ${schedule}. ${noPointer}`,
    };
  }
  return {
    id: "crate",
    eyebrow: "SALVAGE CRATE",
    state: "sealed",
    headline: "No draw is possible",
    detail: `The station serves the authored crate — ${schedule} — and no opening has ever been admitted. ${noPointer} That is the ordinary state, not a fault.`,
  };
}

function shipTile(recorder) {
  if (!recorder || recorder.state === "pending") {
    return { id: "ship", eyebrow: "SHIP WAKE", state: "pending", headline: "Reading the wake", detail: "Loading the installed flight recorder." };
  }
  if (recorder.state === "refused") {
    return {
      id: "ship",
      eyebrow: "SHIP WAKE",
      state: "refused",
      headline: "Wake unreadable",
      detail: `The installed recorder was refused (${recorder.code}). No ship figure is asserted.`,
    };
  }
  if (recorder.source === "live-api") {
    return {
      id: "ship",
      eyebrow: "SHIP WAKE",
      state: "live",
      headline: `${recorder.reportedTransitionCount} transitions`,
      detail: `${recorder.transitions} of them linked and checked in this view. Digest continuity only — consensus finality is ${recorder.consensusFinality}.`,
    };
  }
  return {
    id: "ship",
    eyebrow: "SHIP WAKE",
    state: "sealed",
    headline: "No live figure",
    detail: `The installed recorder is a ${recorder.source} rehearsal, so its ${recorder.transitions} transitions are a demonstration and not the ship. No live number is reachable from this build.`,
  };
}

function rackTile(contentAuthority, cards) {
  const open = cards.filter((card) => card.state === "open").length;
  const sealed = cards.length - open;
  if (contentAuthority?.state === "refused") {
    return { id: "rack", eyebrow: "THE RACK", state: "refused", headline: "The rack is sealed", detail: "The signed content epoch did not authenticate, so no drill opens and no browser fallback exists." };
  }
  if (contentAuthority?.state !== "ready") {
    return { id: "rack", eyebrow: "THE RACK", state: "pending", headline: "Checking the rack", detail: "Authenticating the signed catalog before anything opens." };
  }
  return {
    id: "rack",
    eyebrow: "THE RACK",
    state: "live",
    headline: `${open} drill${open === 1 ? "" : "s"} open`,
    detail: `${sealed} more ${sealed === 1 ? "slot is" : "slots are"} on the rack and sealed. Runs stay local until a node judges and finalizes them.`,
  };
}

/** The four things the front page may claim right now. */
export function buildTodayBoard({ slot = null, recorder = null, contentAuthority = null, cards = [], station = null } = {}) {
  return Object.freeze({
    lead: "Night watch. Here is what is true right now.",
    tiles: Object.freeze([
      Object.freeze(rackTile(contentAuthority, cards)),
      Object.freeze(slotTile(slot)),
      Object.freeze(crateTile(station)),
      Object.freeze(shipTile(recorder)),
    ]),
  });
}

function element(tag, className, textContent) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (textContent !== undefined) node.textContent = textContent;
  return node;
}

export function mountTodayBoard(root, board) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a today-board root is required");
  const lead = element("p", "today-board__lead", board.lead);
  const grid = element("div", "today-board__grid");
  for (const tile of board.tiles) {
    const card = element("article", `today-tile today-tile--${tile.state}`);
    card.dataset.tile = tile.id;
    card.dataset.state = tile.state;
    card.append(
      element("p", "today-tile__eyebrow", tile.eyebrow),
      element("b", "today-tile__headline", tile.headline),
      element("span", "today-tile__detail", tile.detail),
    );
    grid.append(card);
  }
  root.replaceChildren(lead, grid);
  return root;
}
