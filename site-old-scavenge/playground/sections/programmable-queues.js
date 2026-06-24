// Programmable Queues — a queue is NOT a kernel verb. dregg3 dissolves the
// old queue wire family into the `queue` FACTORY PATTERN: a plain cell whose
// program admits or rejects writes. This section builds that admission policy
// out of the REAL constraint grammar (cell/src/program.rs StateConstraint —
// the same atoms the generated predicate catalog documents and the explorer
// renders on live cells), then try-enqueues candidates against it.
//
// The four atoms staged here are the post-uplift ones worth teaching:
//   SenderIs       — bind the producer identity (literal pk)
//   FieldLteOther  — the cross-slot capacity bound (len ≤ cap)
//   BalanceGte     — the cell's OWN post-turn balance floor (fee reserve)
//   PreimageGate   — the knowledge gate (reveal the committed preimage)
//
// The program panel is the platform <dregg-cell-program> inspector — the
// exact element the Studio and Explorer use — fed the same StateConstraintView
// shapes the node serves.

import { mountSection, sha256, hex, shortHex, blake3CommitmentLike } from './_newworld.js';
import { renderProgrammableQueueSvg } from '../visualizers/programmable-queue.js';
import '../../_includes/studio/inspectors/cell-program.js';
import { getWasm } from '../playground.js';

// Slot layout of the modeled queue cell.
const SLOT_LEN = 0;        // queue length
const SLOT_CAP = 1;        // capacity
const SLOT_COMMITMENT = 2; // preimage commitment (PreimageGate target)

const DEFAULT_SECRET = 'open sesame';

/** Human gloss per constraint, shown in the visualizer + constraint list. */
function describe(c) {
  switch (c.kind) {
    case 'SenderIs':      return `sender must be the bound producer (${shortHex(c.pk, 6)})`;
    case 'FieldLteOther': return `capacity: slot[len] ≤ slot[cap] (cross-slot bound)`;
    case 'BalanceGte':    return `fee reserve: own balance must stay ≥ ${c.min}`;
    case 'PreimageGate':  return `reveal the preimage of slot[${c.commitment_index}] (${c.hash_kind})`;
    default:              return c.kind;
  }
}

export function initProgrammableQueues(_wasm) {
  mountSection('programmable-queues', (api) => {
    const { html, signal } = api;

    // --- the queue cell (modeled) ---------------------------------------
    const queueLen = signal(0);
    const queueCap = signal(4);
    const balance = signal(10);
    const commitment = signal('');   // slot[2]: hash of DEFAULT_SECRET
    const hashKind = signal('Blake3');

    // --- two identities the candidate can send as ------------------------
    const producerPk = signal('');
    const strangerPk = signal('');

    (async () => {
      const wasmExports = getWasm();
      const commit = await blake3CommitmentLike(wasmExports, DEFAULT_SECRET);
      commitment.value = commit.hex;
      // Honest labeling: hash_kind states what was ACTUALLY used. The real
      // grammar's HashKind is Blake3 | Poseidon2; if the wasm BLAKE3 path is
      // unavailable we fall back and say so rather than claim Blake3.
      hashKind.value = commit.algo === 'blake3' ? 'Blake3' : 'Sha256 (wasm BLAKE3 unavailable — labeled fallback)';
      producerPk.value = hex(await sha256('producer-identity'));
      strangerPk.value = hex(await sha256('stranger-identity'));
    })();

    // Which constraints are active (all real StateConstraint kinds).
    const active = signal({ SenderIs: true, FieldLteOther: true, BalanceGte: true, PreimageGate: true });

    // The program, in the SAME StateConstraintView shapes the node serves
    // (cell/src/program.rs StateConstraintView) — fed to <dregg-cell-program>.
    function constraintViews() {
      const out = [];
      if (active.value.SenderIs) out.push({ kind: 'SenderIs', pk: producerPk.value });
      if (active.value.FieldLteOther) out.push({ kind: 'FieldLteOther', index: SLOT_LEN, other: SLOT_CAP, delta: 0 });
      if (active.value.BalanceGte) out.push({ kind: 'BalanceGte', min: 5 });
      if (active.value.PreimageGate) out.push({ kind: 'PreimageGate', commitment_index: SLOT_COMMITMENT, hash_kind: hashKind.value });
      return out;
    }

    // --- candidate enqueue action ----------------------------------------
    const candidatePayload = signal('hello');
    const candidateSender = signal('producer');
    const candidatePreimage = signal(DEFAULT_SECRET);
    const decisions = signal([]); // { accept, label, reason }

    /**
     * Evaluate one constraint against the candidate's post-state, faithfully
     * to the kernel semantics: an enqueue is a write `len += 1` that costs
     * the queue cell 1 from its own balance (the relay fee it pays).
     */
    async function evalConstraint(c, post) {
      switch (c.kind) {
        case 'SenderIs':
          return post.sender === c.pk
            ? { ok: true }
            : { ok: false, reason: `sender ${shortHex(post.sender, 6)} ≠ bound pk ${shortHex(c.pk, 6)}` };
        case 'FieldLteOther': {
          const lhs = post.slots[c.index];
          const rhs = post.slots[c.other] + (c.delta || 0);
          return lhs <= rhs
            ? { ok: true }
            : { ok: false, reason: `slot[len]=${lhs} > slot[cap]=${rhs} (queue full)` };
        }
        case 'BalanceGte':
          return post.balance >= c.min
            ? { ok: true }
            : { ok: false, reason: `post balance ${post.balance} < reserve floor ${c.min}` };
        case 'PreimageGate': {
          const revealed = await blake3CommitmentLike(getWasm(), post.preimage);
          return revealed.hex === commitment.value
            ? { ok: true }
            : { ok: false, reason: `hash(preimage) ≠ slot[${c.commitment_index}] commitment` };
        }
        default: return { ok: true };
      }
    }

    async function tryEnqueue() {
      const post = {
        sender: candidateSender.value === 'producer' ? producerPk.value : strangerPk.value,
        slots: { [SLOT_LEN]: queueLen.value + 1, [SLOT_CAP]: queueCap.value },
        balance: balance.value - 1,
        preimage: candidatePreimage.value,
      };
      let firstFailure = null;
      for (const c of constraintViews()) {
        const res = await evalConstraint(c, post);
        if (!res.ok) { firstFailure = { c, reason: res.reason }; break; }
      }
      const label = `${candidateSender.value}/${candidatePayload.value.slice(0, 12)}`;
      if (firstFailure) {
        decisions.value = [...decisions.value, { accept: false, label, reason: `${firstFailure.c.kind}: ${firstFailure.reason}` }].slice(-40);
      } else {
        queueLen.value += 1;
        balance.value -= 1;
        decisions.value = [...decisions.value, { accept: true, label }].slice(-40);
      }
    }

    function resetCell() {
      queueLen.value = 0;
      balance.value = 10;
      decisions.value = [];
    }

    function toggle(kind) {
      active.value = { ...active.value, [kind]: !active.value[kind] };
    }

    const App = api.reactive(() => {
      const views = constraintViews();
      const program = { kind: 'Predicate', constraints: views };
      return html`
      <section class="vizzer" aria-label="Programmable queue demo">
        <header class="vizzer__head">
          <h3 class="vizzer__title">Programmable queue</h3>
          <p class="vizzer__sub">
            cell: len=${queueLen.value} · cap=${queueCap.value} · balance=${balance.value}
            · slot[${SLOT_COMMITMENT}]=<span class="hex" title=${commitment.value}>${shortHex(commitment.value)}</span>
          </p>
          <div class="vizzer__controls">
            <button class="inline" onClick=${resetCell}>reset cell</button>
          </div>
        </header>
        <div class="vizzer__body" style="display:flex;flex-direction:column;gap:12px;">

          <div style="font-size:12px;color:var(--fg-dim);line-height:1.55;">
            There is no <code>queue</code> verb in the kernel — the old queue wire family
            dissolved into the <code>queue</code> <strong>factory pattern</strong>: a plain cell whose
            <strong>program</strong> admits or rejects writes. The constraints below are the real
            grammar (<code>cell/src/program.rs StateConstraint</code>), rendered by the same
            <code>&lt;dregg-cell-program&gt;</code> inspector the Explorer uses on live cells.
          </div>

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">admission policy (real StateConstraint atoms)</h3>
            <div style="display:flex;gap:6px;flex-wrap:wrap;margin-bottom:8px;">
              ${['SenderIs', 'FieldLteOther', 'BalanceGte', 'PreimageGate'].map(kind => html`
                <button key=${kind} class="inline" data-tone=${active.value[kind] ? 'ok' : undefined}
                        onClick=${() => toggle(kind)}>
                  ${active.value[kind] ? '✓' : '+'} ${kind}
                </button>
              `)}
            </div>
            <dregg-cell-program data-program=${JSON.stringify(program)}></dregg-cell-program>
          </div>

          <div class="grid-2">
            <label class="field">payload
              <input value=${candidatePayload.value} onInput=${e => candidatePayload.value = e.target.value} />
            </label>
            <label class="field">send as
              <select value=${candidateSender.value} onInput=${e => candidateSender.value = e.target.value}
                      style="background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:4px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;">
                <option value="producer">producer (the bound pk)</option>
                <option value="stranger">stranger (some other key)</option>
              </select>
            </label>
            <label class="field">preimage reveal (PreimageGate witness)
              <input value=${candidatePreimage.value} onInput=${e => candidatePreimage.value = e.target.value}
                     placeholder='the committed secret is "${DEFAULT_SECRET}"' />
            </label>
            <div style="display:flex;align-items:flex-end;">
              <button class="inline" onClick=${tryEnqueue}>try_enqueue (a write against the program)</button>
            </div>
          </div>

          ${renderProgrammableQueueSvg(html,
            views.map(c => ({ label: describe(c) })),
            decisions.value)}

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">recent decisions</h3>
            <div class="log" role="log" aria-live="polite">
              ${decisions.value.slice().reverse().map((d, i) => html`
                <div key=${i} class="log__entry" data-kind=${d.accept ? 'ok' : 'err'}>
                  ${d.accept ? `ACCEPT  ${d.label}` : `REJECT  ${d.label} — ${d.reason}`}
                </div>
              `)}
              ${decisions.value.length === 0 ? html`<div style="color:var(--fg-muted);">no candidates yet — an accepted enqueue writes len+1 and pays 1 from the cell's balance.</div>` : null}
            </div>
          </div>
        </div>
      </section>
    `;
    });
    return html`<${App} />`;
  }, {
    title: 'Programmable queues',
    lede: 'A queue is a cell program, not a kernel verb. Stage real grammar atoms — SenderIs, FieldLteOther (capacity), BalanceGte (fee reserve), PreimageGate — then try-enqueue candidates and watch the policy accept or reject each one.',
    fallback: 'Interactive constraint-builder + try-enqueue demo.',
  });
}
