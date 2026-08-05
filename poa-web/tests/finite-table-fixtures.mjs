const ZERO = "0".repeat(64);
const ONE = "1".repeat(64);
const TWO = "2".repeat(64);
const THREE = "3".repeat(64);
const FOUR = "4".repeat(64);

export function fixtureAuthority(runSeed = THREE) {
  return {
    missionId: 7,
    manifestDigest: `sha256:${ZERO}`,
    activationDigest: `sha256:${ONE}`,
    contentEpoch: 2,
    curatorCounter: 9,
    federationId: TWO,
    contentRoot: `sha256:${FOUR}`,
    contentSession: ONE,
    runSeed,
    rewardClass: "non-economic-demo",
  };
}

const security = () => ({
  classification: "transparent-beta-demo",
  target_visibility: "public",
  competitive_rewards: false,
  economic_rewards: false,
});

const output = () => ({ requires: "terminal", contribution: "mission_reward", artifact: "mission_artifact" });

function rows(states, actions, dispatch) {
  return states.flatMap((state) => actions.map((action) => {
    const result = dispatch(state.id, action.id);
    return result.next === null
      ? { state: state.id, action: action.id, verdict: "refuse", next: null, reason: result.reason }
      : { state: state.id, action: action.id, verdict: "accept", next: result.next, reason: null };
  }));
}

/** Literal dispatcher fixture: it deliberately does not implement Relay rules. */
export function relayFixture() {
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
  const board = (index) => ({
    index,
    spares: 6,
    costs: {
      "alpha-beta": 1 + (index % 3),
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
    ruleset: "relay-v2",
    engine_module: "Dregg2.Games.PathOfAngels.RelayRepair",
    action_limit: 3,
    run_seed: THREE,
    security: security(),
    // THREE's first byte is 0x33 = 51, and 51 % 8 = 3, so the published draw is
    // the one the run seed makes.  The loader refuses any other `selected`.
    instance: {
      seed_byte: 0,
      modulus: 8,
      selected: 3,
      source: "alpha",
      sink: "omega",
      boards: Array.from({ length: 8 }, (_, index) => board(index)),
    },
    state_machine: { initial_state: "r0", states, actions, transitions: rows(states, actions, dispatch) },
    output: output(),
  };
}

/** Literal dispatcher fixture: glyph placement and pairing are data, not JS rules. */
export function salvageFixture() {
  const glyphs = [2, 0, 1, 2, 0, 1];
  const actions = glyphs.map((glyph, slot) => ({
    id: `slot-${slot}`,
    label: `Expose plate ${slot}`,
    slot,
    glyph_id: glyph,
    glyph_label: `glyph-${glyph}`,
  }));
  const depth = (index) => index === 0 ? 0 : index <= 6 ? 1 : index <= 42 ? 2 : 3;
  const states = Array.from({ length: 164 }, (_, index) => ({
    id: `s${index}`,
    terminal: index === 163,
    view: {
      cleared: index === 163 ? [0, 1, 2, 3, 4, 5] : [],
      exposed: index === 1 || index === 162 ? 0 : null,
      turns: depth(index),
      solved: index === 163,
    },
  }));
  const dispatch = (state, action) => {
    const stateIndex = Number(state.slice(1));
    const actionIndex = Number(action.slice(5));
    if (state === "s163") return { next: null, reason: "solved" };
    if (state === "s162" && action === "slot-0") return { next: null, reason: "already-exposed" };
    const child = stateIndex * 6 + actionIndex + 1;
    if (child < states.length) return { next: `s${child}` };
    return { next: null, reason: "turn-limit" };
  };
  return {
    format: "POAG1-GAME",
    schema_version: 1,
    game_id: "salvage-lock",
    ruleset: "salvage-v1",
    engine_module: "Dregg2.Games.PathOfAngels.SalvageLock",
    action_limit: 12,
    run_seed: THREE,
    security: security(),
    state_machine: { initial_state: "s0", states, actions, transitions: rows(states, actions, dispatch) },
    output: output(),
  };
}
