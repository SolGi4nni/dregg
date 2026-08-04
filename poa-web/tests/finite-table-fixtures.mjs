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
  ];
  const states = Array.from({ length: 15 }, (_, index) => ({
    id: `r${index}`,
    terminal: index === 14,
    view: {
      installed: index === 1 ? ["alpha-beta"] : index === 14 ? ["alpha-beta", "beta-delta"] : [],
      spares: index === 0 ? 4 : index === 14 ? 2 : 3,
      turns: index === 0 ? 0 : index === 14 ? 2 : 1,
      solved: index === 14,
    },
  }));
  const dispatch = (state, action) => {
    if (state === "r0" && action === "alpha-beta") return { next: "r1" };
    if (state === "r0" && action === "alpha-gamma") return { next: "r2" };
    if (state === "r1" && action === "beta-delta") return { next: "r14" };
    if (state === "r2") return { next: `r${3 + actions.findIndex((candidate) => candidate.id === action)}` };
    if (state === "r3") return { next: `r${7 + actions.findIndex((candidate) => candidate.id === action)}` };
    if (state === "r4" && action !== "gamma-delta") return { next: `r${11 + actions.findIndex((candidate) => candidate.id === action)}` };
    if (state === "r14") return { next: null, reason: "solved" };
    if (state === "r1" && action === "alpha-beta") return { next: null, reason: "already-installed" };
    return { next: null, reason: "turn-limit" };
  };
  return {
    format: "POAG1-GAME",
    schema_version: 1,
    game_id: "relay-repair",
    ruleset: "relay-v1",
    engine_module: "Dregg2.Games.PathOfAngels.RelayRepair",
    action_limit: 4,
    run_seed: THREE,
    security: security(),
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
