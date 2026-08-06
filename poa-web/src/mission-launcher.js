import { ArtifactRefusal } from "./poag1.js";
import { mountBlackBox } from "./blackbox-controller.js";
import { mountRelayRepair } from "./relay-controller.js";
import { mountSalvageLock } from "./salvage-controller.js";

/**
 * The dispatch table IS the list of games this client can play.
 *
 * It is exported because the rack has to be able to answer "is there a
 * controller for this?" without keeping a second list — a second list is how a
 * card ends up offering a game the launcher then refuses, or sealing one that
 * would have opened. Adding a game is one line here and one presentation record
 * in `game-rack.js`.
 *
 * ⚠ A controller installed here is NOT a game enrolled. Enrolment is the signed
 * catalog's, and only its. Black Box's controller sits in this table with no
 * descriptor to feed it, which is exactly the state the rack renders as a sealed
 * slot: the drill is built and the curator has not activated it.
 */
const FINITE_CONTROLLERS = Object.freeze({
  "relay-repair": mountRelayRepair,
  "salvage-lock": mountSalvageLock,
  "black-box-reconstruction": mountBlackBox,
});

/** Signal has its own authored surface in the page; the rest mount generically. */
export const SIGNAL_GAME_ID = "signal-triangulation";

export const INSTALLED_GAME_IDS = Object.freeze([SIGNAL_GAME_ID, ...Object.keys(FINITE_CONTROLLERS)]);

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
  refuse(INSTALLED_GAME_IDS.includes(mission.gameId), "mission-game-unsupported", `no controller exists for ${mission.gameId}`);

  if (mission.gameId === SIGNAL_GAME_ID) {
    refuse(typeof launchSignal === "function" && signalRoot, "mission-launch", "Signal controller is unavailable");
    finiteRoot.hidden = true;
    signalRoot.hidden = false;
    return Object.freeze({ gameId: mission.gameId, controller: launchSignal(descriptor) ?? null });
  }
  refuse(finiteRoot && signalRoot, "mission-launch", "finite-table mission roots are unavailable");
  signalRoot.hidden = true;
  finiteRoot.hidden = false;
  const mount = FINITE_CONTROLLERS[mission.gameId];
  refuse(typeof mount === "function", "mission-game-unsupported", `no controller exists for ${mission.gameId}`);
  return Object.freeze({ gameId: mission.gameId, controller: mount(finiteRoot, descriptor, callbacks) });
}
