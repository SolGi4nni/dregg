const ZERO = "0".repeat(64);
const ONE = "1".repeat(64);
const TWO = "2".repeat(64);
const FOUR = "4".repeat(64);

export const FIXTURE_COMMITMENT = "a".repeat(64);

export function fixtureAuthority(instanceDisclosure) {
  return {
    missionId: 7,
    manifestDigest: `sha256:${ZERO}`,
    activationDigest: `sha256:${ONE}`,
    contentEpoch: 2,
    curatorCounter: 9,
    federationId: TWO,
    contentRoot: `sha256:${FOUR}`,
    contentSession: ONE,
    instanceDisclosure,
    rewardClass: "non-economic-demo",
  };
}

export function fixtureOpening(missionId = 7) {
  return {
    slot: 41,
    mission_id: missionId,
    commitment: FIXTURE_COMMITMENT,
    curator_pubkey: "b".repeat(64),
    signature: "c".repeat(128),
  };
}

const security = (disclosure) => ({
  classification: "committed-hidden-instance",
  instance_visibility: disclosure,
  competitive_rewards: false,
  economic_rewards: false,
});

const output = () => ({ requires: "terminal", contribution: "mission_reward", artifact: "mission_artifact" });

/** The shared hidden-instance declaration, byte-for-byte the Lean-emitted shape. */
export function instanceDeclaration(disclosure) {
  return {
    kind: "per-run-hidden-draw",
    derivation_module: "Dregg2.Games.PathOfAngels.HiddenInstance",
    disclosure,
    commitment: {
      published_in: "slot-opening",
      domain: "POAC",
      preimage: ["domain", "slot", "slot_secret"],
      binding_bits: 124,
      opened_after: "slot-close",
    },
    draw: {
      domain: "POAD",
      preimage: ["domain", "purpose", "slot", "mission_id", "epoch", "slot_secret", "federation_id", "content_session", "player_key"],
      purposes: { judged: 1, practice: 2 },
    },
    sponge: {
      permutation: "poseidon2-babybear-w16",
      width: 16,
      rate: 8,
      capacity: 8,
      lane_bytes: 1,
      lane_reject_at_or_above: 2013265920,
      squeeze_blocks: 6,
    },
    practice: { seed: "client-chosen", scored: false, purpose_tag: 2, transcript_field: "mode" },
    operator_knows_instance: true,
  };
}

function rows(states, actions, dispatch) {
  return states.flatMap((state) => actions.map((action) => {
    const result = dispatch(state.id, action.id);
    return result.next === null
      ? { state: state.id, action: action.id, verdict: "refuse", next: null, reason: result.reason }
      : { state: state.id, action: action.id, verdict: "accept", next: result.next, reason: null };
  }));
}

/**
 * Literal dispatcher fixture: it deliberately does not implement Relay rules.
 *
 * Each of the `modulus` machines is the same spanning shape with a different
 * price sheet, which is enough to exercise family parsing, per-board views and
 * the family-size gate without smuggling a Relay reachability rule in here.
 */
export function relayFixture(modulus = 8) {
  const actions = [
    { id: "alpha-beta", label: "Install Alpha-Beta", from: "alpha", to: "beta" },
    { id: "alpha-gamma", label: "Install Alpha-Gamma", from: "alpha", to: "gamma" },
    { id: "beta-delta", label: "Install Beta-Delta", from: "beta", to: "delta" },
    { id: "gamma-delta", label: "Install Gamma-Delta", from: "gamma", to: "delta" },
    { id: "delta-omega", label: "Install Delta-Omega", from: "delta", to: "omega" },
  ];
  // A spanning dispatch over 25 ids: every state is reachable, r14 is the only
  // terminal, and each refusal reason in the vocabulary is provoked somewhere.
  const children = {
    r0: ["r1", "r2", null, null, null],
    r1: [null, "r3", "r14", "r4", "r5"],
    r2: ["r6", "r7", "r8", "r9", "r10"],
    r3: ["r11", "r12", "r13", "r15", "r16"],
    r4: ["r17", "r18", "r19", "r20", "r21"],
    r5: ["r22", "r23", "r24", null, null],
  };
  const shallow = new Set(["r0", "r1", "r2", "r3", "r4", "r5", "r14", "r6", "r7", "r8", "r9", "r10"]);
  const depth = (id) => {
    if (id === "r0") return 0;
    if (id === "r1" || id === "r2") return 1;
    return shallow.has(id) ? 2 : 3;
  };
  const states = Array.from({ length: 25 }, (_, index) => {
    const id = `r${index}`;
    const solved = id === "r14";
    return {
      id,
      terminal: solved,
      view: {
        installed: id === "r1" ? ["alpha-beta"] : solved ? ["alpha-beta", "beta-delta"] : [],
        spares: solved ? 2 : 6 - depth(id),
        turns: depth(id),
        solved,
        stranded: id === "r6",
      },
    };
  });
  const reason = (state, index) => {
    if (state === "r14") return "solved";
    if (state === "r1" && index === 0) return "already-installed";
    if (state === "r5") return "no-spares";
    if (state === "r6") return "stranded";
    return "turn-limit";
  };
  const dispatch = (state, action) => {
    const index = actions.findIndex((candidate) => candidate.id === action);
    const next = (children[state] ?? [])[index] ?? null;
    return next === null ? { next: null, reason: reason(state, index) } : { next };
  };
  // Distinct prices per board: the loader refuses a family with two identical
  // members, because that family is smaller than it says it is.
  const board = (index) => ({
    index,
    spares: 6,
    costs: {
      "alpha-beta": 1 + (index % 4),
      "alpha-gamma": 1 + ((index + 1) % 3),
      "beta-delta": 2,
      "gamma-delta": 1 + ((index + 2) % 3),
      "delta-omega": 1,
    },
  });
  return {
    format: "POAG1-GAME",
    schema_version: 1,
    game_id: "relay-repair",
    ruleset: "relay-v3",
    engine_module: "Dregg2.Games.PathOfAngels.RelayRepair",
    action_limit: 3,
    security: security("per-run-open"),
    instance: {
      modulus,
      source: "alpha",
      sink: "omega",
      draw: instanceDeclaration("per-run-open"),
      boards: Array.from({ length: modulus }, (_, index) => board(index)),
    },
    state_machine: {
      initial_state: "r0",
      actions,
      machines: Array.from({ length: modulus }, (_, index) => ({
        board: index,
        states: structuredClone(states),
        transitions: rows(states, actions, dispatch),
      })),
    },
    output: output(),
  };
}

/**
 * The 90-board Salvage practice space: every arrangement of two copies each of
 * three glyphs over six plates, generated by enumeration rather than by a rule.
 */
function salvagePracticeBoards() {
  const boards = [];
  const walk = (prefix, remaining) => {
    if (prefix.length === 6) return void boards.push([...prefix]);
    for (const glyph of [0, 1, 2]) {
      if (remaining[glyph] === 0) continue;
      remaining[glyph] -= 1;
      walk([...prefix, glyph], remaining);
      remaining[glyph] += 1;
    }
  };
  walk([], [2, 2, 2]);
  return boards;
}

/**
 * Literal dispatcher fixture for the parametric shape: a small table whose
 * second exposure is an ORACLE row. The fixture states both branches; which one
 * a run takes is not decided anywhere in this file.
 */
export function salvageFixture() {
  const actions = Array.from({ length: 6 }, (_, slot) => ({
    id: `slot-${slot}`,
    label: `Expose plate ${slot}`,
    slot,
  }));
  // s0 sealed; s1..s6 hold plate n-1 face up; s7 is a cleared pair; s8 is a
  // cleared board (terminal); s9 is a mismatch that closed the window.
  const states = [
    { id: "s0", terminal: false, view: { cleared: [], exposed: null, turns: 0, solved: false } },
    ...Array.from({ length: 6 }, (_, slot) => ({
      id: `s${slot + 1}`,
      terminal: false,
      view: { cleared: [], exposed: slot, turns: 1, solved: false },
    })),
    { id: "s7", terminal: false, view: { cleared: [0, 1], exposed: null, turns: 2, solved: false } },
    { id: "s8", terminal: true, view: { cleared: [0, 1, 2, 3, 4, 5], exposed: null, turns: 3, solved: true } },
    { id: "s9", terminal: false, view: { cleared: [], exposed: null, turns: 2, solved: false } },
  ];
  const transitions = states.flatMap((state) => actions.map((action) => {
    const base = { state: state.id, action: action.id };
    if (state.id === "s8") return { ...base, verdict: "refuse", reason: "solved", next: null, on_match: null, on_mismatch: null };
    if (state.id === "s0") return { ...base, verdict: "accept", reason: null, next: `s${action.slot + 1}`, on_match: null, on_mismatch: null };
    if (state.id === "s7" || state.id === "s9") {
      return action.slot === 5
        ? { ...base, verdict: "accept", reason: null, next: "s8", on_match: null, on_mismatch: null }
        : { ...base, verdict: "refuse", reason: "turn-limit", next: null, on_match: null, on_mismatch: null };
    }
    // A face-up state: re-exposing the same plate is refused, any other plate is
    // the second of a pair and the emitted table defers it to the hidden board.
    const exposed = Number(state.id.slice(1)) - 1;
    return action.slot === exposed
      ? { ...base, verdict: "refuse", reason: "already-exposed", next: null, on_match: null, on_mismatch: null }
      : { ...base, verdict: "resolve", reason: null, next: null, on_match: "s7", on_mismatch: "s9" };
  }));
  return {
    format: "POAG1-GAME",
    schema_version: 1,
    game_id: "salvage-lock",
    ruleset: "salvage-v2",
    engine_module: "Dregg2.Games.PathOfAngels.SalvageLock",
    action_limit: 12,
    security: security("oracle-only"),
    instance: instanceDeclaration("oracle-only"),
    state_machine: { initial_state: "s0", states, actions, transitions },
    practice: {
      instance_space: 90,
      instance_shape: "two copies of each of three glyphs over six plates",
      scored: false,
      boards: salvagePracticeBoards(),
    },
    output: output(),
  };
}

/** The fixture's state count, so the loader spec can be pinned against it. */
export const SALVAGE_FIXTURE_STATES = 10;
