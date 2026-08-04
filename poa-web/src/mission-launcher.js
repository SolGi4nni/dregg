import { ArtifactRefusal } from "./poag1.js";
import { mountRelayRepair } from "./relay-controller.js";
import { mountSalvageLock } from "./salvage-controller.js";

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function descriptorMissionId(descriptor) {
  return descriptor.missionId ?? descriptor.authority?.missionId;
}

/**
 * Exact game/controller dispatch. Unknown ids and mission/descriptor mismatch
 * refuse; there is deliberately no default or Signal fallback.
 */
export function launchCatalogMission({ mission, descriptor, signalRoot, finiteRoot, launchSignal, callbacks = {} }) {
  refuse(mission && descriptor, "mission-launch", "mission and descriptor are required");
  refuse(descriptor.gameId === mission.gameId, "mission-controller-mismatch", "descriptor game id does not match the selected catalog mission");
  refuse(descriptorMissionId(descriptor) === mission.missionId, "mission-controller-mismatch", "descriptor mission id does not match the selected catalog mission");
  refuse(
    mission.gameId === "signal-triangulation" || mission.gameId === "relay-repair" || mission.gameId === "salvage-lock",
    "mission-game-unsupported",
    `no controller exists for ${mission.gameId}`,
  );

  if (mission.gameId === "signal-triangulation") {
    refuse(typeof launchSignal === "function" && signalRoot, "mission-launch", "Signal controller is unavailable");
    finiteRoot.hidden = true;
    signalRoot.hidden = false;
    return Object.freeze({ gameId: mission.gameId, controller: launchSignal(descriptor) ?? null });
  }
  refuse(finiteRoot && signalRoot, "mission-launch", "finite-table mission roots are unavailable");
  signalRoot.hidden = true;
  finiteRoot.hidden = false;
  if (mission.gameId === "relay-repair") {
    return Object.freeze({ gameId: mission.gameId, controller: mountRelayRepair(finiteRoot, descriptor, callbacks) });
  }
  if (mission.gameId === "salvage-lock") {
    return Object.freeze({ gameId: mission.gameId, controller: mountSalvageLock(finiteRoot, descriptor, callbacks) });
  }
  throw new ArtifactRefusal("mission-game-unsupported", `no controller exists for ${mission.gameId}`);
}
