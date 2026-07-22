/**
 * Presentation-only action menu for the Lean-native browser Descent.
 *
 * `NativeDescentOffering::actions_for` remains the source of truth for eligibility,
 * and the executor remains the referee when a move is submitted. This module does
 * not infer or reproduce a game rule. It only turns the complete action vocabulary
 * into a useful decision surface:
 *
 * - moves decorated `enabled: true` are the primary buttons;
 * - every other move remains present in an accessible disclosure;
 * - malformed affordances fail closed into that unavailable disclosure;
 * - a settled run exposes no clickable move, even if stale input says otherwise.
 */

const LOCKED_REASON = "Not legal in the current committed state.";
const ENDED_REASON = "The run is already settled.";
const MALFORMED_REASON = "Malformed affordance withheld.";
let menuSequence = 0;

function normalizeAction(row, index) {
  const source = row && typeof row === "object" ? row : {};
  const label = typeof source.label === "string" && source.label.trim()
    ? source.label.trim()
    : `Unnamed move ${index + 1}`;
  const turn = typeof source.turn === "string" ? source.turn : "";
  const arg = Number(source.arg);
  const wellFormed = turn.length > 0 && Number.isSafeInteger(arg);
  return {
    label,
    turn,
    arg,
    enabled: source.enabled === true && wellFormed,
    wellFormed,
  };
}

/**
 * Build the deterministic view model consumed by every browser render.
 *
 * Ordering inside each band is stable, preserving the Offering's authored order.
 * Every input row appears exactly once in `available` or `unavailable`.
 */
export function buildDescentActionMenu(actions, { ended = false } = {}) {
  const rows = Array.isArray(actions) ? actions.map(normalizeAction) : [];
  const available = [];
  const unavailable = [];

  for (const action of rows) {
    if (!ended && action.enabled) {
      available.push(action);
      continue;
    }
    unavailable.push({
      ...action,
      reason: !action.wellFormed
        ? MALFORMED_REASON
        : ended
          ? ENDED_REASON
          : LOCKED_REASON,
    });
  }

  const availableCount = available.length;
  const unavailableCount = unavailable.length;
  return {
    available,
    unavailable,
    availableCount,
    unavailableCount,
    heading: ended ? "Run settled" : "Choose your next turn",
    summary: ended
      ? "No further moves can land on this settled record."
      : availableCount === 0
        ? "No move is currently admissible. Verify the record before continuing."
        : `${availableCount} ${availableCount === 1 ? "move is" : "moves are"} available now.`,
    unavailableLabel: `${unavailableCount} unavailable ${unavailableCount === 1 ? "move" : "moves"}`,
  };
}

function appendText(document, parent, tag, className, text) {
  const child = document.createElement(tag);
  if (className) child.className = className;
  child.textContent = text;
  parent.appendChild(child);
  return child;
}

/**
 * Mount the action decision surface with text nodes only.
 *
 * `onChoose` receives the exact normalized `{turn, arg}` selected by the player.
 * The low-level world still parses that pair and the executor still decides whether
 * it lands; an optimistic `enabled` decoration never becomes authority here.
 */
export function mountDescentActionMenu(
  container,
  actions,
  { ended = false, onChoose = () => {} } = {},
) {
  if (!container || !container.ownerDocument) {
    throw new TypeError("a DOM container is required");
  }
  const document = container.ownerDocument;
  const menu = buildDescentActionMenu(actions, { ended });
  const fragment = document.createDocumentFragment();
  const menuId = ++menuSequence;
  const headingId = `nd-action-heading-${menuId}`;
  const assuranceId = `nd-action-assurance-${menuId}`;

  container.setAttribute("role", "region");
  container.setAttribute("aria-labelledby", headingId);
  container.dataset.availableCount = String(menu.availableCount);
  container.dataset.unavailableCount = String(menu.unavailableCount);

  const header = document.createElement("header");
  header.className = "nd-action-header";
  const heading = appendText(document, header, "h2", "nd-action-heading", menu.heading);
  heading.id = headingId;
  const summary = appendText(document, header, "p", "nd-action-summary", menu.summary);
  summary.setAttribute("aria-live", "polite");
  fragment.appendChild(header);

  const assurance = appendText(
    document,
    fragment,
    "p",
    "nd-action-assurance",
    "Eligibility is a preview; the executor checks the selected move again before anything advances.",
  );
  assurance.id = assuranceId;

  const available = document.createElement("div");
  available.className = "nd-actions";
  available.setAttribute("aria-label", "Available moves");
  for (const action of menu.available) {
    const button = document.createElement("button");
    button.type = "button";
    button.textContent = action.label;
    button.dataset.turn = action.turn;
    button.dataset.arg = String(action.arg);
    button.setAttribute("aria-describedby", assuranceId);
    button.addEventListener("click", () => onChoose(action));
    available.appendChild(button);
  }
  fragment.appendChild(available);

  if (menu.unavailableCount > 0) {
    const details = document.createElement("details");
    details.className = "nd-unavailable";
    const detailsSummary = document.createElement("summary");
    detailsSummary.textContent = menu.unavailableLabel;
    detailsSummary.setAttribute(
      "aria-label",
      `${menu.unavailableLabel}. Expand to learn which moves cannot land now.`,
    );
    details.appendChild(detailsSummary);
    const list = document.createElement("ul");
    for (const action of menu.unavailable) {
      const item = document.createElement("li");
      appendText(document, item, "span", "nd-unavailable-label", action.label);
      appendText(document, item, "span", "nd-unavailable-reason", action.reason);
      list.appendChild(item);
    }
    details.appendChild(list);
    fragment.appendChild(details);
  }

  container.replaceChildren(fragment);
  return menu;
}
