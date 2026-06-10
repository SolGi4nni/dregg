// Polis inspector decode fidelity: the pure decoder (polis-decode.js — the
// browser port of starbridge_polis::council::inspect_council) must decode the
// GENERATED council/constitution samples (produced by running the real Rust
// constructors) to the same facts the Rust side bakes in, and must replicate
// the slot semantics of the Rust unit tests in starbridge-apps/polis/src/lib.rs.
//
// Run: node site/tests/polis-inspector.mjs

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const SITE = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const STUDIO = path.join(SITE, 'src', '_includes', 'studio');

const {
  classifyConstraints, constraintsOf, inspectCouncil, inspectConstitution,
  inspectMandate, ceremonyLadder, fieldU64, fieldHex, COUNCIL, CONSTITUTION, MANDATE,
} = await import(path.join(STUDIO, 'polis-decode.js'));

const samples = JSON.parse(fs.readFileSync(path.join(STUDIO, 'factory-samples.generated.json'), 'utf8'));

let failures = 0;
function check(cond, what) {
  if (!cond) { console.error(`FAIL: ${what}`); failures++; }
  else console.log(`ok: ${what}`);
}

// hex field helpers for synthetic cell slots (the node view shape)
const ZERO = '0'.repeat(64);
const u64hex = (n) => BigInt(n).toString(16).padStart(64, '0');

// --- the generated council sample (2-of-3 charter run through Rust) ---------
{
  const cls = classifyConstraints(constraintsOf(samples.council.descriptor));
  check(cls && cls.family === 'council', 'council sample classifies as family=council');
  check(cls.threshold === 2, `council sample threshold decodes to 2 (got ${cls?.threshold})`);
  check(cls.thresholdInData === true, 'council sample carries M in data (AffineLe present in serde)');
  check(cls.members === 3, `council sample member count decodes to 3 (got ${cls?.members})`);
  check(cls.membersCommit != null, 'council sample membership-commitment pin decoded');
  check(cls.pinnedProposalHash == null, 'plain council has no pinned proposal hash');
  check(cls.enactNotBefore == null, 'plain council has no cooling gate');

  // Decode the machine over synthetic slots, mirroring the Rust unit tests.
  const charter = { threshold: cls.threshold, members: cls.members, membersCommit: cls.membersCommit };

  // birth: all-zero state = DRAFT, nothing staged
  const born = inspectCouncil(charter, new Array(8).fill(ZERO));
  check(born.state === 'DRAFT' && !born.proposalStaged && born.approvalCount === 0 && !born.certified,
    'all-zero birth decodes DRAFT / unstaged / 0 approvals / uncertified');

  // proposed with the published commitment (the pin literal)
  const proposed = [...new Array(8).fill(ZERO)];
  proposed[0] = u64hex(1);                       // STATE = PROPOSED
  proposed[1] = u64hex(0xac7a);                  // staged hash
  proposed[6] = fieldHex(cls.membersCommit);     // published commitment
  const p = inspectCouncil(charter, proposed);
  check(p.state === 'PROPOSED' && p.proposalStaged, 'proposed state decodes PROPOSED with staged hash');
  check(p.membersCommitMatches === true, 'published commitment matches the descriptor pin');

  // commitment tamper → mismatch
  const tampered = [...proposed];
  tampered[6] = u64hex(999);
  check(inspectCouncil(charter, tampered).membersCommitMatches === false,
    'tampered commitment slot reported as ≠ charter pin');

  // two approvals + armed flag + APPROVED (the council_threshold_gates_flag pass case)
  const approvedState = [...proposed];
  approvedState[0] = u64hex(3);   // APPROVED
  approvedState[2] = u64hex(1);   // flag armed
  approvedState[3] = u64hex(1);   // member 0
  approvedState[4] = u64hex(1);   // member 1
  const a = inspectCouncil(charter, approvedState);
  check(a.state === 'APPROVED' && a.certified, 'APPROVED + armed flag decode');
  check(a.approvalCount === 2 && a.approvals.join(',') === 'true,true,false',
    `per-member approval bits decode in charter order (got ${a.approvals.join(',')})`);
  check(a.approvalCount >= a.threshold, 'decoded count meets decoded threshold');

  // executed = terminal; unknown code labeled honestly
  const executed = [...approvedState]; executed[0] = u64hex(4);
  check(inspectCouncil(charter, executed).terminal === true, 'EXECUTED decodes terminal');
  const weird = [...approvedState]; weird[0] = u64hex(9);
  check(inspectCouncil(charter, weird).state === 'UNKNOWN(9)', 'foreign state code → UNKNOWN(9)');

  // the ceremony ladder readback
  const ladder = ceremonyLadder(a);
  check(ladder.length === 4 && ladder[0].done && ladder[1].done && ladder[2].done && !ladder[3].done,
    'ladder at APPROVED: propose/approve/certify done, enact pending');
  const ladderExec = ceremonyLadder(inspectCouncil(charter, executed));
  check(ladderExec[3].done && !ladderExec[3].terminalBranch, 'ladder at EXECUTED: enact done');
}

// --- amendment variant: pin + cooling gate (synthesized in serde shape) -----
{
  const lit = (n) => { const a = new Array(32).fill(0); a[31] = n; return a; };
  const base = samples.council.descriptor.state_constraints;
  const amendment = [
    ...base,
    { AnyOf: { variants: [{ FieldEquals: { index: 0, value: lit(0) } }, { FieldEquals: { index: 1, value: lit(0xc7) } }] } },
    { AnyOf: { variants: [{ Not: { FieldEquals: { index: 0, value: lit(4) } } }, { TemporalGate: { not_before: 500, not_after: null } }] } },
  ];
  const cls = classifyConstraints(amendment);
  check(cls && cls.family === 'amendment', 'pinned hash + cooling gate classify as amendment');
  check(fieldU64(cls.pinnedProposalHash) === 0xc7, 'pinned successor hash literal decoded');
  check(cls.enactNotBefore === 500, `cooling gate decodes 500 (got ${cls?.enactNotBefore})`);
}

// --- node-VIEW shape (kind-tagged, decimal strings; no AffineLe projection) -
{
  const view = {
    kind: 'Predicate',
    constraints: [
      { kind: 'AllowedTransitions', slot_index: 0, allowed: [['0', '0'], ['0', '1'], ['1', '1'], ['1', '2'], ['1', '3'], ['3', '3'], ['3', '4']] },
      { kind: 'WriteOnce', index: 1 },
      { kind: 'Monotonic', index: 2 },
      { kind: 'Monotonic', index: 3 },
      { kind: 'Monotonic', index: 4 },
      { kind: 'FieldEquals', index: 5, value: ZERO }, // non-member slot pinned zero
      { kind: 'FieldEquals', index: 7, value: ZERO },
    ],
  };
  const cls = classifyConstraints(constraintsOf(view));
  check(cls && cls.family === 'council', 'view-shaped council classifies');
  check(cls.threshold === null && cls.thresholdInData === false,
    'view shape honestly carries NO threshold (AffineLe has no view projection)');
  check(cls.members === 2, `view shape member count from Monotonic teeth = 2 (got ${cls?.members})`);
}

// --- the generated constitution sample ---------------------------------------
{
  const cls = classifyConstraints(constraintsOf(samples.constitution.descriptor));
  check(cls && cls.family === 'constitution', 'constitution sample classifies as constitution');
  check(cls.version === 1, `version pin decodes 1 (got ${cls?.version})`);
  check(cls.councilThreshold === 2, `council-threshold pin decodes 2 (got ${cls?.councilThreshold})`);
  check(cls.amendmentDelay === 1024, `amendment-delay pin decodes 1024 (got ${cls?.amendmentDelay})`);
  check(cls.treasuryCap === 10000, `treasury-cap pin decodes 10000 (got ${cls?.treasuryCap})`);

  // live slots: active then superseded
  const active = [u64hex(1), u64hex(1), u64hex(2), u64hex(1024), u64hex(10000), ZERO, ZERO, ZERO];
  const st = inspectConstitution(active);
  check(st.state === 'ACTIVE' && !st.superseded && st.version === 1 && st.treasuryCap === 10000,
    'ACTIVE constitution slots decode');
  const superseded = [...active]; superseded[0] = u64hex(2); superseded[5] = u64hex(0xdeed);
  const st2 = inspectConstitution(superseded);
  check(st2.state === 'SUPERSEDED' && st2.superseded && st2.terminal && fieldU64(st2.successorHash) === 0xdeed,
    'SUPERSEDED constitution records nonzero successor and is terminal');
}

// --- mandate (synthesized serde, mirrors worker_state_constraints) -----------
{
  const lit = (vals) => { const a = new Array(32).fill(0); for (const [i, v] of vals) a[i] = v; return a; };
  const u64lit = (n) => { const a = new Array(32).fill(0); let x = BigInt(n); for (let i = 31; i >= 24 && x > 0n; i--) { a[i] = Number(x & 0xffn); x >>= 8n; } return a; };
  const zero = new Array(32).fill(0);
  const pin = (slot, v) => ({ AnyOf: { variants: [{ FieldEquals: { index: 0, value: zero } }, { FieldEquals: { index: slot, value: v } }] } });
  const cs = [
    { AllowedTransitions: { slot_index: 0, allowed: [[zero, zero], [zero, u64lit(1)], [u64lit(1), u64lit(1)], [u64lit(1), u64lit(2)]] } },
    pin(1, u64lit(30)),
    pin(2, lit([[0, 0xab]])),
    pin(3, lit([[0, 0xcd]])),
    pin(4, u64lit(7)),
    { FieldEquals: { index: 5, value: zero } },
    { FieldEquals: { index: 6, value: zero } },
    { FieldEquals: { index: 7, value: zero } },
  ];
  const cls = classifyConstraints(cs);
  check(cls && cls.family === 'mandate', 'worker mandate constraint set classifies as mandate');
  check(cls.slice === 30, `slice pin decodes 30 (got ${cls?.slice})`);
  check(fieldHex(cls.toolScope).startsWith('ab'), 'tool-scope pin decoded');
  check(fieldHex(cls.orchestrator).startsWith('cd'), 'orchestrator pin decoded');

  const activeFields = [u64hex(1), u64hex(30), 'ab' + '0'.repeat(62), 'cd' + '0'.repeat(62), u64hex(7), ZERO, ZERO, ZERO];
  const st = inspectMandate(activeFields, 12);
  check(st.state === 'ACTIVE' && !st.revoked && st.slice === 30 && st.remaining === 12,
    'ACTIVE mandate decodes slice + remaining balance');
  const revokedFields = [...activeFields]; revokedFields[0] = u64hex(2);
  const st2 = inspectMandate(revokedFields, 0);
  check(st2.revoked && st2.terminal, 'REVOKED mandate decodes terminal/inert');
}

// --- escrow/obligation samples must NOT classify as polis ---------------------
{
  check(classifyConstraints(constraintsOf(samples.escrow.descriptor)) === null,
    'escrow sample does not classify as a polis family (no false positives)');
}

// --- field coercion parity with the Rust to_u64 (trailing 8 bytes, BE) --------
{
  const arr = new Array(32).fill(0); arr[31] = 4; arr[30] = 1; // 0x0104 = 260
  check(fieldU64(arr) === 260, 'fieldU64 over 32-byte array = trailing-8-bytes BE');
  check(fieldU64('0'.repeat(60) + '0104') === 260, 'fieldU64 over 64-hex string');
  check(fieldU64('260') === 260, 'decimal strings accepted (program-view transition rows)');
}

if (failures) { console.error(`\n${failures} failure(s)`); process.exit(1); }
console.log('\nall polis-inspector checks passed');
