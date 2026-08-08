import { ArtifactRefusal } from "./poag1.js";
import { contentRoot } from "./signal-runtime.js";

const SHA256 = /^sha256:[0-9a-f]{64}$/;
const HEX32 = /^[0-9a-f]{64}$/;
const METRIC_LIMIT = 1_000_000;
/**
 * Relic ids are ONE namespace shared by every mission — the world state carries a
 * single `discovered_relics` set, so two missions naming the same number name the
 * same relic. Each mission owns the block `missionId * RELIC_BLOCK` up to
 * `+ RELIC_BLOCK - 1`, and `relic / RELIC_BLOCK` names its owner.
 *
 * ⚠ This client used to require `allowed_relics === [missionId]` — a convention
 * from when every game banked exactly one relic. Deck Descent banks four (mouth,
 * west, and TWO on the east spur), so the convention was false; and because it
 * also fixed the numbers at the mission ids, Descent's `{5,6,7,8}` collided with
 * missions 6 and 7 the moment they enrolled. The rule below is the correction: a
 * mission may declare MORE than one relic, and may not declare one that belongs
 * to another mission. `RELIC_BLOCK` mirrors `MISSION_RELIC_BLOCK` in
 * `Dregg2.Games.PathOfAngels.RelicNamespace` and is re-checked against the signed
 * schema's own declaration below, so a drift is a refusal, not a reinterpretation.
 */
const RELIC_BLOCK = 16;
const RELIC_NAMESPACE = Object.freeze({
  scheme: "per-mission-block",
  block_width: RELIC_BLOCK,
  owner: "relic_id / block_width == mission_id",
  cross_mission: "disjoint-by-construction",
  authored_in: "Dregg2.Games.PathOfAngels.RelicNamespace",
  violation: "refuse",
});
const relicOwner = (relic) => Math.floor(relic / RELIC_BLOCK);
/**
 * ⚠ `disclosure` is pinned here, in the SIGNED catalog's consumer, and the game
 * descriptors are checked against it. A descriptor that quietly relabelled
 * itself `per-run-open` would start handing out the board it is supposed to
 * withhold, and nothing inside that descriptor could contradict it.
 *
 * `relics` is the exact allowlist each game is expected to declare — its own
 * block's slots, in ascending order. Descent's four are the only multi-relic
 * entry, and they are slots 0..3 of block 5.
 */
const GAME_SPECS = Object.freeze([
  Object.freeze({
    missionId: 1,
    relics: Object.freeze([16]),
    gameId: "signal-triangulation",
    title: "Signal Triangulation",
    engineModule: "Dregg2.Games.PathOfAngels.SignalTriangulation",
    ruleset: "signal-v2",
    disclosure: "oracle-only",
    actionLimit: 5,
    descriptorPath: "games/signal-triangulation.json",
    fixtureId: "signal-solved-preview-v1",
  }),
  Object.freeze({
    missionId: 2,
    relics: Object.freeze([32]),
    gameId: "relay-repair",
    title: "Relay Repair",
    engineModule: "Dregg2.Games.PathOfAngels.RelayRepair",
    ruleset: "relay-v3",
    disclosure: "per-run-open",
    actionLimit: 3,
    descriptorPath: "games/relay-repair.json",
    fixtureId: "relay-solved-preview-v1",
  }),
  Object.freeze({
    missionId: 3,
    relics: Object.freeze([48]),
    gameId: "salvage-lock",
    title: "Salvage Lock",
    engineModule: "Dregg2.Games.PathOfAngels.SalvageLock",
    ruleset: "salvage-v2",
    disclosure: "oracle-only",
    actionLimit: 12,
    descriptorPath: "games/salvage-lock.json",
    fixtureId: "salvage-solved-preview-v1",
  }),
  Object.freeze({
    missionId: 4,
    relics: Object.freeze([64]),
    gameId: "black-box-reconstruction",
    title: "Black Box Reconstruction",
    engineModule: "Dregg2.Games.PathOfAngels.BlackBoxReconstruction",
    ruleset: "blackbox-v2",
    disclosure: "oracle-only",
    actionLimit: 15,
    descriptorPath: "games/black-box-reconstruction.json",
    fixtureId: "blackbox-solved-preview-v1",
  }),
  Object.freeze({
    missionId: 5,
    relics: Object.freeze([80, 81, 82, 83]),
    gameId: "deck-descent",
    title: "Deck Descent",
    engineModule: "Dregg2.Games.PathOfAngels.DeckDescent",
    ruleset: "descent-v1",
    disclosure: "oracle-only",
    actionLimit: 9,
    descriptorPath: "games/deck-descent.json",
    fixtureId: "descent-solved-preview-v1",
  }),
  Object.freeze({
    missionId: 6,
    relics: Object.freeze([96]),
    gameId: "artificer-logic",
    title: "Artificer Logic",
    engineModule: "Dregg2.Games.PathOfAngels.ArtificerLogic",
    ruleset: "artificer-v1",
    disclosure: "oracle-only",
    actionLimit: 5,
    descriptorPath: "games/artificer-logic.json",
    fixtureId: "artificer-solved-preview-v1",
  }),
  Object.freeze({
    missionId: 7,
    relics: Object.freeze([112]),
    gameId: "vent-crawl",
    title: "Vent Crawl",
    engineModule: "Dregg2.Games.PathOfAngels.VentCrawl",
    ruleset: "push-your-luck-v1",
    disclosure: "oracle-only",
    actionLimit: 6,
    descriptorPath: "games/vent-crawl.json",
    fixtureId: "vent-solved-preview-v1",
  }),
]);

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function object(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function exactKeys(value, expected, at) {
  refuse(object(value), "catalog-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  refuse(actual.length === wanted.length && actual.every((key, index) => key === wanted[index]), "catalog-field", `${at} has an unknown or missing field`);
}

function integer(value, min = 0, max = Number.MAX_SAFE_INTEGER) {
  return Number.isSafeInteger(value) && value >= min && value <= max;
}

function exactNumericArray(value, at, maxLength = 64) {
  refuse(Array.isArray(value) && value.length <= maxLength && value.every((item) => integer(item)), "catalog-array", `${at} is invalid`);
  refuse(new Set(value).size === value.length, "catalog-array", `${at} contains a duplicate`);
  return Object.freeze([...value]);
}

function contribution(value, at, relicsAreArray) {
  exactKeys(value, ["intel", "supplies", "cohesion", "influence", "score", "relics"], at);
  for (const field of ["intel", "supplies", "cohesion", "influence", "score"]) {
    refuse(integer(value[field], 0, METRIC_LIMIT), "catalog-contribution", `${at}.${field} is invalid`);
  }
  const relics = relicsAreArray
    ? exactNumericArray(value.relics, `${at}.relics`)
    : integer(value.relics, 0, 64) && value.relics;
  refuse(relics !== false, "catalog-contribution", `${at}.relics is invalid`);
  return Object.freeze({ ...value, relics });
}

function artifactRef(value, at, expected, manifest, artifactPin) {
  exactKeys(value, ["mission_id", "artifact_id", "source_digest", "content_digest"], at);
  refuse(artifactPin && typeof artifactPin.sha256 === "string", "catalog-artifact", `${at} descriptor pin is absent`);
  refuse(
    value.mission_id === expected.missionId && value.artifact_id === expected.missionId &&
      value.source_digest === manifest.sourceDigest && value.content_digest === artifactPin.sha256,
    "catalog-artifact",
    `${at} is not the exact manifest-bound beta artifact`,
  );
  return Object.freeze({ ...value });
}

function world(value, at, betaArtifact) {
  exactKeys(value, ["intel", "supplies", "cohesion", "influence", "score", "discovered_relics", "beta_artifacts", "sequence"], at);
  for (const field of ["intel", "supplies", "cohesion", "influence", "score"]) {
    refuse(integer(value[field], 0, METRIC_LIMIT), "catalog-world", `${at}.${field} is invalid`);
  }
  refuse(integer(value.sequence), "catalog-world", `${at}.sequence is invalid`);
  const discoveredRelics = exactNumericArray(value.discovered_relics, `${at}.discovered_relics`, 4096);
  refuse(Array.isArray(value.beta_artifacts) && value.beta_artifacts.length <= 4096, "catalog-world", `${at}.beta_artifacts is invalid`);
  const betaArtifacts = value.beta_artifacts.map((artifact, index) => {
    exactKeys(artifact, ["mission_id", "artifact_id", "source_digest", "content_digest"], `${at}.beta_artifacts[${index}]`);
    return Object.freeze({ ...artifact });
  });
  if (betaArtifact) {
    const [actual] = betaArtifacts;
    refuse(
      betaArtifacts.length === 1 && actual.mission_id === betaArtifact.mission_id &&
        actual.artifact_id === betaArtifact.artifact_id && actual.source_digest === betaArtifact.source_digest &&
        actual.content_digest === betaArtifact.content_digest,
      "catalog-preview",
      `${at} does not contain the mission beta artifact`,
    );
  } else refuse(betaArtifacts.length === 0, "catalog-preview", `${at} base world must not contain a beta artifact`);
  return Object.freeze({ ...value, discovered_relics: discoveredRelics, beta_artifacts: Object.freeze(betaArtifacts) });
}

/** Parse the complete authenticated seven-mission catalog and its exact bytes. */
export async function loadMissionCatalog(bundle) {
  const catalog = bundle?.payloads?.["catalog.json"]?.json;
  exactKeys(catalog, ["format", "schema_version", "missions", "fixtures"], "catalog.json");
  refuse(catalog.format === "POAG1-CATALOG" && catalog.schema_version === 1, "catalog-format", "unsupported POAG1 catalog");
  refuse(Array.isArray(catalog.missions) && catalog.missions.length === GAME_SPECS.length, "catalog-missions", "catalog must contain the exact seven-mission set");
  refuse(Array.isArray(catalog.fixtures) && catalog.fixtures.length === GAME_SPECS.length, "catalog-fixtures", "catalog must contain one exact preview per mission");
  refuse(bundle.contentEpoch?.schema === "POA-CONTENT-EPOCH-SIGNATURE-V1", "catalog-activation", "catalog requires an authenticated content epoch");
  refuse(bundle.manifestDigest === bundle.contentEpoch.manifestDigest && SHA256.test(bundle.manifestDigest), "catalog-activation", "catalog manifest activation binding is invalid");
  refuse(SHA256.test(bundle.contentEpoch.activationDigest), "catalog-activation", "catalog activation digest is invalid");
  refuse(integer(bundle.contentEpoch.contentEpoch) && integer(bundle.contentEpoch.counter), "catalog-activation", "catalog activation counters are invalid");

  // The relic namespace rule is PUBLISHED in the signed schema, and this client
  // pins its own copy. A bundle whose rule differs from `RELIC_NAMESPACE` is
  // refused rather than followed: the numbers below only mean anything under the
  // rule that produced them.
  const schema = bundle.payloads["schema.json"]?.json;
  refuse(object(schema) && object(schema.contract), "catalog-schema", "bundle publishes no schema contract");
  const declaredNamespace = schema.contract.relic_namespace;
  exactKeys(declaredNamespace, Object.keys(RELIC_NAMESPACE), "schema relic_namespace");
  refuse(
    Object.entries(RELIC_NAMESPACE).every(([key, expected]) => declaredNamespace[key] === expected),
    "catalog-relic-namespace",
    "bundle declares a relic namespace this client was not built for",
  );

  const descriptorEntries = GAME_SPECS.map((spec) => {
    const payload = bundle.payloads[spec.descriptorPath];
    refuse(payload?.bytes instanceof Uint8Array && object(payload.json), "catalog-descriptor", `${spec.descriptorPath} is absent`);
    return [spec.descriptorPath, payload.bytes];
  });
  const measuredRoot = await contentRoot(descriptorEntries);
  const pins = new Map(bundle.manifest.artifacts.map((pin) => [pin.path, pin]));

  // Every relic id any mission has claimed so far, and which mission claimed it.
  // A relic is a shared namespace; this map is the only thing that sees it whole.
  const claimedRelics = new Map();
  const missions = GAME_SPECS.map((spec, index) => {
    const value = catalog.missions[index];
    exactKeys(value, [
      "mission_id", "title", "engine_module", "ruleset", "reward_class", "action_limit",
      "privacy_grade", "ballot_regime", "epoch", "federation_id", "content_root", "activation",
      "content_session", "instance", "budget", "allowed_relics", "descriptor_path",
      "allowed_beta_discoveries",
    ], `catalog missions[${index}]`);
    refuse(
      value.mission_id === spec.missionId && value.title === spec.title &&
        value.engine_module === spec.engineModule && value.ruleset === spec.ruleset &&
        value.action_limit === spec.actionLimit && value.descriptor_path === spec.descriptorPath,
      "catalog-mission-identity",
      `catalog missions[${index}] does not match the supported game`,
    );
    refuse(value.reward_class === "non-economic-demo" && value.privacy_grade === "public" && value.ballot_regime === "none", "catalog-policy", `${spec.title} must remain a public zero-economy demo`);
    refuse(value.epoch === bundle.contentEpoch.contentEpoch, "catalog-epoch", `${spec.title} epoch does not match its authenticated activation`);
    refuse(HEX32.test(value.federation_id) && HEX32.test(value.content_session), "catalog-domain", `${spec.title} has an invalid domain separator`);
    // ⚠ `run_seed` is GONE. It named the live instance of every mission in a
    // file the client fetches unauthenticated-readable, so the answer shipped
    // with the question. The catalog now states only how the seed is DERIVED.
    exactKeys(value.instance, ["binding", "disclosure", "derivation_module", "commitment_published_in"], `${spec.title} instance`);
    refuse(value.instance.binding === "per-run-hidden-draw", "catalog-instance", `${spec.title} does not bind a per-run hidden draw`);
    refuse(value.instance.disclosure === spec.disclosure, "catalog-instance", `${spec.title} disclosure is not ${spec.disclosure}`);
    refuse(value.instance.commitment_published_in === "slot-opening", "catalog-instance", `${spec.title} does not publish its commitment in the slot opening`);
    refuse(typeof value.instance.derivation_module === "string" && value.instance.derivation_module.length > 0, "catalog-instance", `${spec.title} names no derivation module`);
    refuse(value.content_root === measuredRoot && SHA256.test(value.content_root), "catalog-content-root", `${spec.title} does not bind the complete descriptor set`);
    exactKeys(value.activation, ["state", "digest_source"], `${spec.title} activation`);
    refuse(
      value.activation.state === "detached-signature-required" && value.activation.digest_source === bundle.contentEpoch.schema,
      "catalog-activation",
      `${spec.title} activation contract is invalid`,
    );
    const budget = contribution(value.budget, `${spec.title} budget`, false);
    const allowedRelics = exactNumericArray(value.allowed_relics, `${spec.title} allowed_relics`);
    // ⚠ ORDER. The collision sweep runs FIRST and against every mission read so far,
    // because ownership implies disjointness: if the block rule were checked first,
    // no catalog could ever reach the collision refusal and it would be a branch that
    // cannot go red. Checked in this order, both are reachable — a relic claimed
    // twice trips the first, a relic outside its block trips the second.
    for (const relic of allowedRelics) {
      const claimant = claimedRelics.get(relic);
      refuse(claimant === undefined, "catalog-relic-collision", `${spec.title} claims relic ${relic}, already claimed by ${claimant}`);
      claimedRelics.set(relic, spec.title);
    }
    refuse(
      allowedRelics.length >= 1 && allowedRelics.length <= RELIC_BLOCK,
      "catalog-relic-namespace",
      `${spec.title} declares ${allowedRelics.length} relics, outside 1..${RELIC_BLOCK}`,
    );
    refuse(
      allowedRelics.every((relic) => relicOwner(relic) === spec.missionId),
      "catalog-relic-namespace",
      `${spec.title} declares a relic outside its own block`,
    );
    // The exact allowlist this client was built for. A mission may declare more than
    // one relic — Descent declares four — but not a different set than the one the
    // emitted catalog is pinned to here.
    refuse(JSON.stringify(allowedRelics) === JSON.stringify([...spec.relics]), "catalog-relics", `${spec.title} relic allowlist drifted`);
    refuse(Array.isArray(value.allowed_beta_discoveries) && value.allowed_beta_discoveries.length === 1, "catalog-artifact", `${spec.title} must declare one beta artifact`);
    const betaArtifact = artifactRef(value.allowed_beta_discoveries[0], `${spec.title} beta artifact`, spec, bundle.manifest, pins.get(spec.descriptorPath));

    const preview = catalog.fixtures[index];
    exactKeys(preview, ["id", "mission_id", "base_world", "contribution", "preview_world"], `catalog fixtures[${index}]`);
    refuse(preview.id === spec.fixtureId && preview.mission_id === spec.missionId, "catalog-preview", `${spec.title} preview identity is invalid`);
    const reward = contribution(preview.contribution, `${spec.title} preview contribution`, true);
    // SUBSET, not equality: a preview banks what one solved line actually earns, and
    // Descent's preview banks the east pair — two of its four declared relics. This is
    // the client's copy of `MissionSpec.acceptsContribution`, whose relic clause is
    // `c.relics ⊆ mission.allowedRelics`; requiring equality was the same one-relic
    // convention as the allowlist pin above, and would have refused Descent too.
    refuse(reward.relics.every((relic) => allowedRelics.includes(relic)), "catalog-preview", `${spec.title} preview relics are outside its allowlist`);
    for (const field of ["intel", "supplies", "cohesion", "influence", "score"]) {
      refuse(reward[field] <= budget[field], "catalog-preview", `${spec.title} preview contribution exceeds its budget`);
    }
    refuse(reward.relics.length <= budget.relics, "catalog-preview", `${spec.title} preview relic count exceeds its budget`);
    const baseWorld = world(preview.base_world, `${spec.title} preview base_world`, null);
    refuse(preview.preview_world !== null, "catalog-preview", `${spec.title} preview world is absent`);
    const previewWorld = world(preview.preview_world, `${spec.title} preview preview_world`, betaArtifact);
    return Object.freeze({
      ...spec,
      rewardClass: value.reward_class,
      epoch: value.epoch,
      privacyGrade: value.privacy_grade,
      ballotRegime: value.ballot_regime,
      federationId: value.federation_id,
      contentRoot: value.content_root,
      contentSession: value.content_session,
      instanceDisclosure: value.instance.disclosure,
      instanceBinding: value.instance.binding,
      derivationModule: value.instance.derivation_module,
      activation: Object.freeze({ state: value.activation.state, digestSource: value.activation.digest_source }),
      activationDigest: bundle.contentEpoch.activationDigest,
      contentEpoch: bundle.contentEpoch.contentEpoch,
      curatorCounter: bundle.contentEpoch.counter,
      activatedManifest: bundle.manifestDigest,
      budget,
      allowedRelics,
      betaArtifact,
      reward,
      baseWorld,
      previewWorld,
    });
  });
  refuse(new Set(missions.map((mission) => mission.missionId)).size === missions.length, "catalog-missions", "mission ids are duplicated");
  refuse(new Set(missions.map((mission) => mission.federationId)).size === 1, "catalog-domain", "missions do not share one federation id");
  return Object.freeze(missions);
}

/**
 * The authenticated envelope a finite-table descriptor is checked against.
 *
 * ⚠ `runSeed` is GONE. It was here so the loader could confirm the descriptor's
 * published `run_seed` matched the catalog's — two copies of the answer agreeing
 * with each other. What travels now is the DISCLOSURE the signed catalog
 * declares, which the descriptor must match and cannot widen.
 */
export function finiteTableAuthority(mission) {
  return Object.freeze({
    missionId: mission.missionId,
    manifestDigest: mission.activatedManifest,
    activationDigest: mission.activationDigest,
    contentEpoch: mission.contentEpoch,
    curatorCounter: mission.curatorCounter,
    federationId: mission.federationId,
    contentRoot: mission.contentRoot,
    contentSession: mission.contentSession,
    instanceDisclosure: mission.instanceDisclosure,
    rewardClass: mission.rewardClass,
  });
}

export function missionByGameId(missions, gameId) {
  const matches = missions.filter((mission) => mission.gameId === gameId);
  refuse(matches.length === 1, "catalog-game", `unsupported or duplicated game id: ${gameId}`);
  return matches[0];
}
