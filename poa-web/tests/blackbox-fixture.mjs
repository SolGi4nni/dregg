/**
 * ⚠ READ THIS BEFORE TRUSTING A GREEN BLACK BOX TEST.
 *
 * `poa/artifacts/poag1/games/black-box-reconstruction.json` DOES NOT EXIST. The
 * Lean emitter can produce it (`POA_EMIT_MODE=descriptors`, EmitMain.lean:60) but
 * it is not committed, it is not in `canonicalArtifacts`, and it is not in the
 * manifest — so it currently carries no bundle integrity at all.
 *
 * This fixture is therefore a HAND-BUILT MIRROR of the shape reported from
 * `Emit.lean` (`blackBoxDescriptorJson`, pinned by `validateBlackBoxDescriptor`).
 * A passing test here says the consumer is self-consistent against my reading of
 * the emitter. It does NOT say the consumer parses the bytes Lean writes, and no
 * test in this repo can say that until the descriptor is emitted and committed.
 *
 * What is claimed and where it came from:
 *   - 120 instances = permutations of 5 fragments over 5 slots, Lehmer-indexed
 *   - 25 probes, slot-major, column j = 5*slot + fragment
 *   - cell '1' iff the instance places `fragment` at `slot`; 5 per row
 *   - action_limit 15, ruleset "blackbox-v2", class_alphabet "01"
 *
 * The permutation enumeration below is a SECOND implementation of `orderRow`,
 * which is exactly the mirror this repo keeps paying for. It is confined to a
 * test input and must be DELETED the moment real bytes land.
 */

const SLOTS = 5;

/** Lehmer-code enumeration of the 120 permutations of five fragments. */
function orders() {
  const all = [];
  for (let index = 0; index < 120; index += 1) {
    const pool = [0, 1, 2, 3, 4];
    const order = [];
    let rest = index;
    for (let position = SLOTS; position >= 1; position -= 1) {
      const factorial = [1, 1, 2, 6, 24, 120][position - 1];
      const pick = Math.floor(rest / factorial);
      rest %= factorial;
      order.push(pool.splice(pick, 1)[0]);
    }
    all.push(order);
  }
  return all;
}

export function blackBoxProbes() {
  const probes = [];
  for (let slot = 0; slot < SLOTS; slot += 1) {
    for (let fragment = 0; fragment < SLOTS; fragment += 1) {
      probes.push({
        id: `probe-${slot}-${fragment}`,
        label: `Ask whether fragment ${fragment} belongs at position ${slot}`,
        slot,
        fragment,
      });
    }
  }
  return probes;
}

export function blackBoxFixture(overrides = {}) {
  const probes = blackBoxProbes();
  const table = orders().map((order) => probes.map((probe) => (order[probe.slot] === probe.fragment ? "1" : "0")).join(""));
  return {
    format: "POAG1-GAME",
    schema_version: 1,
    game_id: "black-box-reconstruction",
    ruleset: "blackbox-v2",
    engine_module: "Dregg2.Games.PathOfAngels.BlackBoxReconstruction",
    action_limit: 15,
    security: {
      classification: "committed-hidden-instance",
      instance_visibility: "oracle-only",
      competitive_rewards: false,
      economic_rewards: false,
    },
    instance: {
      kind: "per-run-hidden-draw",
      derivation_module: "Dregg2.Games.PathOfAngels.HiddenInstance",
      disclosure: "oracle-only",
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
    },
    oracle: {
      instance_space: 120,
      instance_shape: "a permutation of five fragments over five positions",
      required_per_instance: 5,
      settles: "slot-and-fragment",
      class_alphabet: "01",
      classes: [{ id: "mismatch", solving: false }, { id: "match", solving: true }],
      probes,
      table,
    },
    refusals: ["solved", "turn-limit", "repeated-probe", "settled-slot", "settled-fragment"],
    output: { requires: "terminal", contribution: "mission_reward", artifact: "mission_artifact" },
    ...overrides,
  };
}

export function blackBoxMission() {
  return {
    missionId: 4,
    gameId: "black-box-reconstruction",
    title: "Black Box Reconstruction",
    actionLimit: 15,
    instanceDisclosure: "oracle-only",
    federationId: "7".repeat(64),
    contentSession: "8".repeat(64),
    contentRoot: `sha256:${"9".repeat(64)}`,
    contentEpoch: 1,
    curatorCounter: 7,
    activationDigest: `sha256:${"e".repeat(64)}`,
    rewardClass: "non-economic-demo",
  };
}

export function blackBoxOpening(missionId = 4) {
  return {
    slot: 5,
    mission_id: missionId,
    commitment: "a".repeat(64),
    curator_pubkey: "b".repeat(64),
    signature: "c".repeat(128),
  };
}
