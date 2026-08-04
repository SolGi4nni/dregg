import { launchCatalogMission } from "/poa-web/src/mission-launcher.js";
import { loadRelayRepairDescriptor } from "/poa-web/src/relay-runtime.js";
import { loadSalvageLockDescriptor } from "/poa-web/src/salvage-runtime.js";

const result = document.getElementById("result");
const signalRoot = document.getElementById("signal-root");
const finiteRoot = document.getElementById("finite-root");
const json = async (path) => {
  const response = await fetch(path);
  if (!response.ok) throw new Error(`${path}: HTTP ${response.status}`);
  return response.json();
};

try {
  const [catalog, relayJson, salvageJson] = await Promise.all([
    json("/poa/artifacts/poag1/catalog.json"),
    json("/poa/artifacts/poag1/games/relay-repair.json"),
    json("/poa/artifacts/poag1/games/salvage-lock.json"),
  ]);
  const rawMission = (id) => catalog.missions.find((mission) => mission.mission_id === id);
  const mission = (id, gameId) => ({ missionId: id, gameId });
  const authority = (raw, fill) => ({
    missionId: raw.mission_id,
    manifestDigest: `sha256:${fill.repeat(64)}`,
    activationDigest: `sha256:${fill.repeat(64)}`,
    contentEpoch: raw.epoch,
    curatorCounter: 1,
    federationId: raw.federation_id,
    contentRoot: raw.content_root,
    contentSession: raw.content_session,
    runSeed: raw.run_seed,
    rewardClass: raw.reward_class,
  });
  const relay = loadRelayRepairDescriptor(relayJson, authority(rawMission(2), "a"));
  const salvage = loadSalvageLockDescriptor(salvageJson, authority(rawMission(3), "b"));

  let signalLaunches = 0;
  const signal = launchCatalogMission({
    mission: mission(1, "signal-triangulation"),
    descriptor: { gameId: "signal-triangulation", missionId: 1 },
    signalRoot,
    finiteRoot,
    launchSignal: () => { signalLaunches += 1; signalRoot.textContent = "SIGNAL CONTROLLER"; },
  });
  if (signal.gameId !== "signal-triangulation" || signalLaunches !== 1) throw new Error("Signal did not launch exactly once");

  const relayLaunch = launchCatalogMission({ mission: mission(2, "relay-repair"), descriptor: relay, signalRoot, finiteRoot, launchSignal() {} });
  finiteRoot.querySelector('[data-action="alpha-beta"]').click();
  if (relayLaunch.controller.getRun().stateId === relay.initialState) throw new Error("Relay control did not dispatch its emitted row");
  relayLaunch.controller.destroy();

  const salvageLaunch = launchCatalogMission({ mission: mission(3, "salvage-lock"), descriptor: salvage, signalRoot, finiteRoot, launchSignal() {} });
  finiteRoot.querySelector('[data-action="slot-0"]').click();
  if (salvageLaunch.controller.getRun().stateId === salvage.initialState) throw new Error("Salvage control did not dispatch its emitted row");
  salvageLaunch.controller.destroy();

  for (const [selected, descriptor, code] of [
    [mission(77, "unknown-game"), { gameId: "unknown-game", authority: { missionId: 77 } }, "mission-game-unsupported"],
    [mission(2, "relay-repair"), { gameId: "signal-triangulation", missionId: 2 }, "mission-controller-mismatch"],
  ]) {
    try {
      launchCatalogMission({ mission: selected, descriptor, signalRoot, finiteRoot, launchSignal: () => { signalLaunches += 1; } });
      throw new Error(`${code} was accepted`);
    } catch (error) {
      if (error.code !== code) throw error;
    }
  }
  if (signalLaunches !== 1) throw new Error("refusal path fell back to Signal");
  document.body.dataset.status = "pass";
  result.textContent = "PASS: Signal, Relay, and Salvage launched; unknown and mismatched games refused without fallback.";
} catch (error) {
  document.body.dataset.status = "fail";
  result.textContent = `FAIL: ${error.stack ?? error}`;
}

