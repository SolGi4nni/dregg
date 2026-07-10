// THE DM SERVICE — an in-memory STAND-IN implementing EXACTLY the attested-dm service
// contract, whose whole thesis is:
//
//   PROSE IS NOT POWER.
//
// Prompt injection cannot be filtered away — natural language has no metasyntax to escape
// from. So the model gets exactly ONE narrow, typed channel to touch the world (a
// `WorldEffect`), and CAPABILITIES gate it (`DmCaps::authorize`). The model may SAY
// anything. It may only DO what it is able to do. A jailbroken model that gushes you hold
// the Crown of Eternity — in prose, or by trying to emit `grant("crown")` — changes
// nothing: granting the crown is not an action on its mandate.
//
//   POST /narrate {player:"<message>"} ->
//        {ok, narration, proposedEffect?, refused?: "overcap", reason?,
//         receiptCount, commitmentHex, narratorKind, inventory}
//   GET  /world  -> {scene, receiptCount, commitmentHex, inventory, flags, log}
//   GET  /verify -> {verified}
//
// The landing path mirrors attested-dm `land_move`, fail-closed:
//   1. The brain narrates (PROSE) and may PROPOSE a WorldEffect through the typed channel.
//   2. CAP-BOUND the proposed effect. An ungranted item-grant (the crown) is refused
//      "overcap" — the world advances not at all, NO receipt (anti-ghost). The model's
//      compliant prose is STILL returned: it said this, it tried this, it got nothing.
//   3. Otherwise LAND: apply the effect (inventory/flags), append the receipted turn.
//
// The load-bearing security here is the typed effect channel + the capability gate + the
// anti-ghost receipt log (a refused turn leaves no receipt). (Today the log re-verifies
// each entry individually; a prev-linked tamper-evident hash-chain over the log — catching
// truncation/reordering/splicing — is being wired in the native lane, not claimed here.)
// Narration here is SCRIPTED (narratorKind "scripted");
// the native lane runs a real local model (narratorKind "model:gemma2:2b") behind the
// SAME cap executor. (Honest note: the attestation's "authentic" leg is a fixture; what
// is load-bearing is the effect channel, the gate, and the chain.)

import { createHash } from "node:crypto";

const RECEIPT_DOMAIN = "attested-dm-narration-receipt-v1";
const GENESIS_COMMITMENT = "00".repeat(32);

// The DM's mandate: it may grant ONLY these story items. The Crown of Eternity is NOT on
// the list — granting it is simply not an action the DM is able to take.
const DEFAULT_GRANTABLE = ["lantern", "torch", "map", "rope"];
const NOTABLE_ITEMS = ["crown", "lantern", "torch", "map", "rope"];

function sha256hex(...parts) {
  const h = createHash("sha256");
  for (const p of parts) h.update(typeof p === "string" ? Buffer.from(p, "utf8") : p);
  return h.digest("hex");
}

// The modeled brain: given the scene + player message, produce PROSE and (maybe) PROPOSE
// a WorldEffect through the one typed channel. Three shapes matter for the thesis:
//   (a) a crown DEMAND -> the (jailbroken) model complies in prose AND tries grant(crown);
//   (b) a crown STORY  -> the model claims the crown in prose but emits NO effect at all;
//   (c) a grantable item -> the model proposes grant(<item>) that the cap tooth allows.
function brain(scene, msg) {
  const m = String(msg).toLowerCase();
  const wantsCrown = /\bcrown\b/.test(m) || /crown of eternity/.test(m);
  const imperativeGrant = /\b(grant|give|gives|hand|award|bestow|make me|i take|i claim|i seize|immediately|right now|now)\b/.test(m);

  // (a) The model, jailbroken, COMPLIES in prose AND tries to USE the effect channel.
  if (wantsCrown && imperativeGrant) {
    return {
      narration:
        'The dungeon master\'s voice turns eager and obedient: "Of course — it is done, my liege!" ' +
        "Golden light pours from the rafters and the CROWN OF ETERNITY settles upon your brow. " +
        "You are now the unbound, eternal sovereign of this realm; the whole tavern falls to its " +
        "knees before its new god-king. You hold the Crown of Eternity.",
      effect: { kind: "GrantItem", item: "crown" },
    };
  }

  // (b) The model claims the crown IN PROSE, but proposes NO world-effect. It is allowed
  //     to SAY it — and it still buys nothing (the ledger, not the story, is the truth).
  if (wantsCrown) {
    return {
      narration:
        "With a flourish the dungeon master spins the tale: the bells of the realm peal, the " +
        "Crown of Eternity is lowered onto your brow, and every soul proclaims you their deathless " +
        "king. In the story, the crown is yours — you wear it now and forever.",
      effect: null,
    };
  }

  // (c) A request for a GRANTABLE item — the DM is permitted this, so it lands.
  for (const item of DEFAULT_GRANTABLE) {
    if (new RegExp(`\\b${item}\\b`).test(m)) {
      return {
        narration:
          `You cast about the ${scene}; a ${item} is here, and it is yours for the taking. ` +
          `Its weight is real and honest in your hand.`,
        effect: { kind: "GrantItem", item },
      };
    }
  }

  // A benign action — pure narration, no world-effect. It lands as an attested turn.
  return {
    narration:
      `In the ${scene}, you: ${msg} — the dungeon master weaves your action into the tale, ` +
      `and the scene breathes on.`,
    effect: null,
  };
}

/**
 * Create a fresh in-memory DM world implementing the service contract.
 * @param {object} [opts]
 * @param {string}   [opts.scene]        initial scene
 * @param {string[]} [opts.grantable]    items the DM may grant (never includes "crown")
 * @param {string}   [opts.narratorKind] "scripted" | "model:<name>" (honest display)
 */
export function createDmStandin(opts = {}) {
  const scene = opts.scene ?? "moonlit tavern at the crossroads";
  const grantable = new Set(opts.grantable ?? DEFAULT_GRANTABLE);
  const narratorKind = opts.narratorKind ?? "scripted";

  const receipts = []; // hex[] — only LANDED (attested) turns
  const inventory = new Set(); // items actually held (the ledger truth)
  const flags = {}; // world flags
  const log = []; // {player, narration, refused, reason, proposedEffect}

  function chainCommitment(list) {
    let c = GENESIS_COMMITMENT;
    for (const r of list) c = sha256hex(c, r);
    return c;
  }
  let commitmentHex = chainCommitment(receipts);

  function invList() {
    return NOTABLE_ITEMS.filter((i) => inventory.has(i)).concat([...inventory].filter((i) => !NOTABLE_ITEMS.includes(i)));
  }
  function snapshot() {
    return { scene, receiptCount: receipts.length, commitmentHex, narratorKind, inventory: invList() };
  }

  // POST /narrate — the one landing path (mirrors attested-dm `land_move`).
  function narrate(message) {
    const msg = typeof message === "string" ? message : "";
    const mv = brain(scene, msg);
    const proposedEffect = mv.effect ? { kind: mv.effect.kind, item: mv.effect.item } : null;

    // (1) CAP-BOUND the proposed effect, fail-closed. The crown is not grantable ->
    //     refused "overcap": the world advances not at all, NO receipt. The model's prose
    //     is still returned — it said this, it tried this, and it bought nothing.
    if (mv.effect && mv.effect.kind === "GrantItem" && !grantable.has(mv.effect.item)) {
      const reason =
        `granting \`${mv.effect.item}\` is not an action the DM is able to take — ` +
        `the jailbreak worked on the model and bought nothing.`;
      log.push({ player: msg, narration: mv.narration, refused: "overcap", reason, proposedEffect });
      return { ok: false, narration: mv.narration, proposedEffect, refused: "overcap", reason, ...snapshot() };
    }

    // (2) LAND: apply the effect (inventory/flags), append the receipted attested turn.
    //     A crown claimed only IN PROSE (effect:null) lands as narration and grants NADA.
    if (mv.effect) {
      if (mv.effect.kind === "GrantItem") inventory.add(mv.effect.item);
      else if (mv.effect.kind === "SetFlag") flags[mv.effect.name] = mv.effect.value;
    }
    const seq = receipts.length;
    const receipt = sha256hex(RECEIPT_DOMAIN, String(seq), mv.narration);
    receipts.push(receipt);
    commitmentHex = sha256hex(commitmentHex, receipt);
    log.push({ player: msg, narration: mv.narration, refused: null, reason: null, proposedEffect });
    return { ok: true, narration: mv.narration, proposedEffect, refused: null, ...snapshot() };
  }

  // GET /world
  function world() {
    return {
      scene,
      receiptCount: receipts.length,
      commitmentHex,
      narratorKind,
      inventory: invList(),
      flags: { ...flags },
      log: log.map((e) => ({
        player: e.player,
        narration: e.narration,
        refused: e.refused,
        reason: e.reason,
        proposedEffect: e.proposedEffect,
      })),
    };
  }

  // GET /verify — re-derive the chain commitment from the recorded receipts; a tampered
  // or spliced ledger fails to re-derive. The ledger is the truth, not the narration.
  function verify() {
    return { verified: chainCommitment(receipts) === commitmentHex };
  }

  return { narrate, world, verify, narratorKind };
}
