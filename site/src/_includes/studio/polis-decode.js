/**
 * polis-decode.js — the PURE polis cell decoder (no DOM, node-importable).
 *
 * This is the browser port of the legibility half of the polis layer:
 *
 *   * `inspectCouncil` ports `starbridge_polis::council::inspect_council`
 *     (starbridge-apps/polis/src/lib.rs) — the SAME slot logic the CLI
 *     (`dregg polis council`) and the Discord `/council-status` surface use.
 *   * `inspectConstitution` / `inspectMandate` read the slot schemas
 *     documented in `starbridge_polis::{constitution, mandate}`.
 *   * `classifyConstraints` recognizes which polis family a constraint set
 *     is (council / amendment / constitution / worker-mandate) and decodes
 *     the charter terms BAKED into it (threshold M from the `AffineLe` gate,
 *     member count N from the per-member approval-slot teeth, pinned
 *     parameter literals from the `pin_term` AnyOf shape, the amendment
 *     cooling gate from the `when_state(EXECUTED, TemporalGate)` shape).
 *
 * Everything here is read FROM data (a descriptor's serde constraints, a
 * node's program view, a cell's 8 field slots) — nothing is hand-set.
 *
 * Slot schemas (starbridge-apps/polis/src/lib.rs):
 *   council:      0 STATE · 1 PROPOSAL_HASH · 2 APPROVED_FLAG · 3..5 approvals
 *                 · 6 MEMBERS_COMMIT · 7 reserved
 *   constitution: 0 STATE · 1 VERSION · 2 COUNCIL_THRESHOLD ·
 *                 3 AMENDMENT_DELAY · 4 TREASURY_CAP · 5 SUCCESSOR_HASH · 6,7 reserved
 *   mandate:      0 STATE · 1 SLICE · 2 TOOL_SCOPE · 3 ORCHESTRATOR ·
 *                 4 WORKER_TAG · 5..7 reserved
 */

// --- slot constants (mirror starbridge_polis) -------------------------------

export const STATE_SLOT = 0;

export const COUNCIL = {
  PROPOSAL_HASH_SLOT: 1,
  APPROVED_FLAG_SLOT: 2,
  FIRST_APPROVAL_SLOT: 3,
  MEMBERS_COMMIT_SLOT: 6,
  RESERVED_SLOT: 7,
  MAX_MEMBERS: 3,
  STATES: { 0: 'DRAFT', 1: 'PROPOSED', 2: 'REJECTED', 3: 'APPROVED', 4: 'EXECUTED' },
  TERMINAL: [2, 4],
  // The machine rows (state → state), self-loops omitted for the diagram.
  EDGES: [[0, 1], [1, 2], [1, 3], [3, 4]],
};

export const CONSTITUTION = {
  VERSION_SLOT: 1,
  COUNCIL_THRESHOLD_SLOT: 2,
  AMENDMENT_DELAY_SLOT: 3,
  TREASURY_CAP_SLOT: 4,
  SUCCESSOR_HASH_SLOT: 5,
  STATES: { 0: 'UNINIT', 1: 'ACTIVE', 2: 'SUPERSEDED' },
  TERMINAL: [2],
  EDGES: [[0, 1], [1, 2]],
};

export const MANDATE = {
  SLICE_SLOT: 1,
  TOOL_SCOPE_SLOT: 2,
  ORCHESTRATOR_SLOT: 3,
  WORKER_TAG_SLOT: 4,
  STATES: { 0: 'UNINIT', 1: 'ACTIVE', 2: 'REVOKED' },
  TERMINAL: [2],
  EDGES: [[0, 1], [1, 2]],
};

// --- field-element coercion --------------------------------------------------
// Fields arrive as 32-byte arrays (descriptor serde shape), 64-hex strings
// (node / wasm views), short hex, or decimal strings (program-view transition
// rows). `fieldU64` mirrors the Rust decoder exactly: the trailing 8 bytes,
// big-endian.

export function fieldU64(f) {
  if (f == null) return 0;
  if (Array.isArray(f)) {
    let v = 0n;
    for (const b of f.slice(-8)) v = (v << 8n) | BigInt(Number(b) & 0xff);
    return Number(v);
  }
  if (typeof f === 'number') return f;
  const s = String(f).trim();
  if (/^0x[0-9a-f]+$/i.test(s)) return Number(BigInt(s));
  if (/^[0-9a-f]{64}$/i.test(s)) return Number(BigInt('0x' + s.slice(-16)));
  if (/^\d+$/.test(s)) return Number(s);
  if (/^[0-9a-f]+$/i.test(s)) return Number(BigInt('0x' + s.slice(-16)));
  return 0;
}

/** Normalize any field representation to a lowercase 64-hex string. */
export function fieldHex(f) {
  if (f == null) return '0'.repeat(64);
  if (Array.isArray(f)) return f.map((b) => (Number(b) & 0xff).toString(16).padStart(2, '0')).join('');
  const s = String(f).trim().replace(/^0x/i, '').toLowerCase();
  if (/^[0-9a-f]+$/.test(s)) return s.padStart(64, '0').slice(-64);
  if (/^\d+$/.test(s)) return BigInt(s).toString(16).padStart(64, '0');
  return '0'.repeat(64);
}

export function fieldIsZero(f) {
  return /^0*$/.test(fieldHex(f));
}

// --- constraint normalization -------------------------------------------------
// Two wire shapes exist for the SAME StateConstraint enum:
//   * serde (descriptors, factory-samples):  { "WriteOnce": { "index": 1 } }
//   * view  (node / wasm StateConstraintView): { "kind": "WriteOnce", "index": 1 }
// Normalize both to { kind, ...body } with nested variants normalized too.

export function normalizeConstraint(sc) {
  if (!sc || typeof sc !== 'object') return null;
  let kind, body;
  if (typeof sc.kind === 'string') {
    ({ kind, ...body } = sc);
  } else {
    const keys = Object.keys(sc);
    if (keys.length !== 1) return null;
    kind = keys[0];
    body = sc[kind];
    if (body == null || typeof body !== 'object' || Array.isArray(body)) body = { value: body };
  }
  const out = { kind, ...body };
  if (Array.isArray(out.variants)) out.variants = out.variants.map(normalizeConstraint).filter(Boolean);
  // SimpleStateConstraint::Not(Box<...>) — serde: { "Not": { "FieldEquals": {...} } }.
  if (kind === 'Not') {
    const inner = normalizeConstraint(body.value !== undefined ? body.value : body);
    return { kind: 'Not', inner };
  }
  return out;
}

export function normalizeConstraints(list) {
  return (Array.isArray(list) ? list : []).map(normalizeConstraint).filter(Boolean);
}

// --- shape recognizers ---------------------------------------------------------

/** pin_term(slot, lit) = AnyOf[ FieldEquals(STATE,0), FieldEquals(slot,lit) ]. */
function pinnedLiteral(cs, slot) {
  for (const c of cs) {
    if (c.kind !== 'AnyOf' || !Array.isArray(c.variants) || c.variants.length !== 2) continue;
    const [a, b] = c.variants;
    if (a?.kind === 'FieldEquals' && Number(a.index) === STATE_SLOT && fieldIsZero(a.value)
      && b?.kind === 'FieldEquals' && Number(b.index) === slot) {
      return b.value;
    }
  }
  return null;
}

/** pinned_zero(slot) = bare FieldEquals(slot, 0) at the top level. */
function pinnedZero(cs, slot) {
  return cs.some((c) => c.kind === 'FieldEquals' && Number(c.index) === slot && fieldIsZero(c.value));
}

/** when_state(gate, q) = AnyOf[ Not(FieldEquals(STATE,gate)), q ] → returns q. */
function whenState(cs, gateState, innerKind) {
  for (const c of cs) {
    if (c.kind !== 'AnyOf' || !Array.isArray(c.variants) || c.variants.length !== 2) continue;
    const [a, b] = c.variants;
    if (a?.kind === 'Not' && a.inner?.kind === 'FieldEquals'
      && Number(a.inner.index) === STATE_SLOT && fieldU64(a.inner.value) === gateState
      && b?.kind === innerKind) {
      return b;
    }
  }
  return null;
}

/** AllowedTransitions on slot 0 → Set of "from>to" u64 rows (incl. self-loops). */
function transitionRows(cs) {
  const t = cs.find((c) => c.kind === 'AllowedTransitions' && Number(c.slot_index) === STATE_SLOT);
  if (!t || !Array.isArray(t.allowed)) return null;
  return new Set(t.allowed.map(([from, to]) => `${fieldU64(from)}>${fieldU64(to)}`));
}

// --- family classification -------------------------------------------------------

/**
 * Classify a constraint set (descriptor serde OR node view shape) as a polis
 * family and decode the charter terms baked into it.
 *
 * Returns null when the set is not polis-shaped, else:
 * {
 *   family: 'council' | 'amendment' | 'constitution' | 'mandate',
 *   // council/amendment (threshold null when reading a node VIEW — the
 *   // AffineLe gate has no StateConstraintView projection yet, so a live
 *   // program view honestly cannot carry M):
 *   threshold, members, membersCommit, pinnedProposalHash, enactNotBefore,
 *   // constitution:
 *   version, councilThreshold, amendmentDelay, treasuryCap,
 *   // mandate:
 *   slice, toolScope, orchestrator, workerTag,
 *   thresholdInData: boolean,  // false ⇒ M not present in this shape
 * }
 */
export function classifyConstraints(rawConstraints) {
  const cs = normalizeConstraints(rawConstraints);
  if (!cs.length) return null;
  const rows = transitionRows(cs);
  if (!rows) return null;

  const isCouncilMachine = rows.has('0>1') && rows.has('1>3') && rows.has('3>4') && rows.has('1>2');
  const isTwoStep = !isCouncilMachine && rows.has('0>1') && rows.has('1>2');

  if (isCouncilMachine) {
    // threshold M + member count N from the AffineLe gate when present
    // (descriptor serde); from the per-member approval teeth otherwise (view).
    const affine = cs.find((c) => c.kind === 'AffineLe' && Array.isArray(c.terms));
    let threshold = null;
    let members = 0;
    if (affine) {
      for (const [coef, slot] of affine.terms) {
        if (Number(slot) === COUNCIL.APPROVED_FLAG_SLOT && Number(coef) > 0) threshold = Number(coef);
        if (Number(coef) < 0) members++;
      }
    } else {
      // View fallback: a member slot has Monotonic teeth; a non-member slot is
      // pinned zero. (MemberOf/AffineLe have no view projection.)
      for (let i = 0; i < COUNCIL.MAX_MEMBERS; i++) {
        const slot = COUNCIL.FIRST_APPROVAL_SLOT + i;
        if (cs.some((c) => c.kind === 'Monotonic' && Number(c.index) === slot)) members++;
      }
    }
    const pinnedProposalHash = pinnedLiteral(cs, COUNCIL.PROPOSAL_HASH_SLOT);
    const temporal = whenState(cs, 4 /* EXECUTED */, 'TemporalGate');
    return {
      family: pinnedProposalHash != null || temporal ? 'amendment' : 'council',
      threshold,
      thresholdInData: threshold != null,
      members,
      membersCommit: pinnedLiteral(cs, COUNCIL.MEMBERS_COMMIT_SLOT),
      pinnedProposalHash,
      enactNotBefore: temporal && temporal.not_before != null ? Number(temporal.not_before) : null,
    };
  }

  if (isTwoStep) {
    const hasSuccessorWriteOnce = cs.some(
      (c) => c.kind === 'WriteOnce' && Number(c.index) === CONSTITUTION.SUCCESSOR_HASH_SLOT
    );
    if (hasSuccessorWriteOnce) {
      return {
        family: 'constitution',
        version: fieldU64(pinnedLiteral(cs, CONSTITUTION.VERSION_SLOT)),
        councilThreshold: fieldU64(pinnedLiteral(cs, CONSTITUTION.COUNCIL_THRESHOLD_SLOT)),
        amendmentDelay: fieldU64(pinnedLiteral(cs, CONSTITUTION.AMENDMENT_DELAY_SLOT)),
        treasuryCap: fieldU64(pinnedLiteral(cs, CONSTITUTION.TREASURY_CAP_SLOT)),
      };
    }
    // Mandate: four pinned terms + slots 5..7 pinned zero.
    const slice = pinnedLiteral(cs, MANDATE.SLICE_SLOT);
    const toolScope = pinnedLiteral(cs, MANDATE.TOOL_SCOPE_SLOT);
    if (slice != null && toolScope != null && pinnedZero(cs, 5)) {
      return {
        family: 'mandate',
        slice: fieldU64(slice),
        toolScope,
        orchestrator: pinnedLiteral(cs, MANDATE.ORCHESTRATOR_SLOT),
        workerTag: pinnedLiteral(cs, MANDATE.WORKER_TAG_SLOT),
      };
    }
  }
  return null;
}

/** Extract the constraint list from a cell's program view or a descriptor. */
export function constraintsOf(programOrDescriptor) {
  const p = programOrDescriptor;
  if (!p) return [];
  if (Array.isArray(p.state_constraints)) return p.state_constraints; // FactoryDescriptor
  if (Array.isArray(p.constraints)) return p.constraints;             // CellProgram::Predicate view
  if (Array.isArray(p.cases)) return p.cases.flatMap((c) => c.constraints || []);
  return [];
}

// --- the inspect_council port ----------------------------------------------------

/**
 * Port of `starbridge_polis::council::inspect_council` (pure over the 8 field
 * slots). `charter` is { threshold, members } where members is a COUNT (the
 * member ids are not needed to decode the machine) plus an optional
 * `membersCommit` literal (the pin from the descriptor) to check slot 6
 * against. threshold may be null (node view — see classifyConstraints).
 */
export function inspectCouncil(charter, fields) {
  const f = Array.isArray(fields) ? fields : [];
  const stateCode = fieldU64(f[STATE_SLOT]);
  const n = Math.min(Number(charter?.members ?? 0), COUNCIL.MAX_MEMBERS);
  const approvals = [];
  for (let i = 0; i < n; i++) approvals.push(fieldU64(f[COUNCIL.FIRST_APPROVAL_SLOT + i]) === 1);
  const approvalCount = approvals.filter(Boolean).length;
  return {
    stateCode,
    state: COUNCIL.STATES[stateCode] ?? `UNKNOWN(${stateCode})`,
    terminal: COUNCIL.TERMINAL.includes(stateCode),
    proposalHash: fieldHex(f[COUNCIL.PROPOSAL_HASH_SLOT]),
    proposalStaged: !fieldIsZero(f[COUNCIL.PROPOSAL_HASH_SLOT]),
    membersCommit: fieldHex(f[COUNCIL.MEMBERS_COMMIT_SLOT]),
    membersCommitMatches: charter?.membersCommit != null
      ? fieldHex(f[COUNCIL.MEMBERS_COMMIT_SLOT]) === fieldHex(charter.membersCommit)
      : null, // unknown without the charter pin
    approvals,
    approvalCount,
    threshold: charter?.threshold ?? null,
    certified: fieldU64(f[COUNCIL.APPROVED_FLAG_SLOT]) === 1,
  };
}

/** Decode a constitution cell's 8 slots (slot schema above). */
export function inspectConstitution(fields) {
  const f = Array.isArray(fields) ? fields : [];
  const stateCode = fieldU64(f[STATE_SLOT]);
  return {
    stateCode,
    state: CONSTITUTION.STATES[stateCode] ?? `UNKNOWN(${stateCode})`,
    terminal: CONSTITUTION.TERMINAL.includes(stateCode),
    version: fieldU64(f[CONSTITUTION.VERSION_SLOT]),
    councilThreshold: fieldU64(f[CONSTITUTION.COUNCIL_THRESHOLD_SLOT]),
    amendmentDelay: fieldU64(f[CONSTITUTION.AMENDMENT_DELAY_SLOT]),
    treasuryCap: fieldU64(f[CONSTITUTION.TREASURY_CAP_SLOT]),
    successorHash: fieldHex(f[CONSTITUTION.SUCCESSOR_HASH_SLOT]),
    superseded: stateCode === 2 && !fieldIsZero(f[CONSTITUTION.SUCCESSOR_HASH_SLOT]),
  };
}

/** Decode a worker-mandate cell's 8 slots. `balance` is the live remaining slice. */
export function inspectMandate(fields, balance = null) {
  const f = Array.isArray(fields) ? fields : [];
  const stateCode = fieldU64(f[STATE_SLOT]);
  return {
    stateCode,
    state: MANDATE.STATES[stateCode] ?? `UNKNOWN(${stateCode})`,
    terminal: MANDATE.TERMINAL.includes(stateCode),
    revoked: stateCode === 2,
    slice: fieldU64(f[MANDATE.SLICE_SLOT]),
    toolScope: fieldHex(f[MANDATE.TOOL_SCOPE_SLOT]),
    orchestrator: fieldHex(f[MANDATE.ORCHESTRATOR_SLOT]),
    workerTag: fieldHex(f[MANDATE.WORKER_TAG_SLOT]),
    remaining: balance == null ? null : Number(balance),
  };
}

// --- the amendment-ceremony ladder ------------------------------------------------

/**
 * Derive the ceremony ladder for a council/amendment cell from its DECODED
 * state (the monotone slots witness which steps have happened — that is the
 * inductive-invariant design of the machine, so this is a sound readback,
 * not a guess). Receipts remain the canonical per-step record; this maps the
 * machine's progress onto the propose → approve×M → certify → enact ladder.
 */
export function ceremonyLadder(status) {
  const s = status;
  const reached = (code) => s.stateCode >= code && s.state !== `UNKNOWN(${s.stateCode})`;
  const rejected = s.stateCode === 2;
  return [
    {
      step: 'propose',
      detail: 'stage the action hash (WriteOnce) + publish the membership commitment; DRAFT → PROPOSED',
      done: s.proposalStaged || reached(1),
    },
    {
      step: `approve × ${s.threshold ?? 'M'}`,
      detail: `per-member approval bits, monotone — ${s.approvalCount}${s.threshold != null ? ` of ${s.threshold} required` : ''} set`,
      done: s.threshold != null ? s.approvalCount >= s.threshold : s.certified,
      progress: s.approvals,
    },
    {
      step: 'certify',
      detail: 'arm the approved flag — the executor admits this only when Σ approvals ≥ M (AffineLe)',
      done: s.certified,
    },
    {
      step: rejected ? 'rejected' : 'enact / execute',
      detail: rejected
        ? 'PROPOSED → REJECTED: terminal, inert'
        : 'APPROVED → EXECUTED, exactly once (no outgoing row after); amendments additionally gated by the cooling-period TemporalGate',
      done: rejected || s.stateCode === 4,
      terminalBranch: rejected,
    },
  ];
}
