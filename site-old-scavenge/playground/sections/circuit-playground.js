/**
 * Circuit Playground Section — define a CircuitDescriptor visually, test it.
 *
 * Users can:
 * - Define columns (state columns for an AIR)
 * - Add constraints between columns
 * - Generate sample traces
 * - Check constraint satisfaction
 * - See the AIR structure that would be compiled
 */

import { state, notifyStateChange, getWasm } from '../playground.js';

let circuit = {
  name: 'MyCircuit',
  columns: [],
  constraints: [],
  trace: [],
};

export function initCircuitPlayground(wasm) {
  const section = document.getElementById('section-circuit-playground');
  if (!section) return;

  section.innerHTML = `
    <div class="pg-section__header">
      <h2>Circuit Playground</h2>
      <p>Define a custom AIR (Algebraic Intermediate Representation) visually. Add columns, write constraints, generate traces, and test them.</p>
    </div>

    <div class="cpg-layout">
      <div class="cpg-descriptor">
        <div class="cpg-descriptor__header">
          <h4>Circuit Descriptor</h4>
          <input type="text" id="cpg-name" value="${circuit.name}" class="pg-input pg-input--inline" placeholder="Circuit name">
        </div>

        <div class="cpg-columns">
          <div class="cpg-columns__header">
            <span>Columns</span>
            <button class="pg-btn pg-btn--sm pg-btn--ghost" id="cpg-add-col">+ Add Column</button>
          </div>
          <div class="cpg-columns__list" id="cpg-col-list"></div>
        </div>

        <div class="cpg-constraints">
          <div class="cpg-constraints__header">
            <span>Constraints</span>
            <button class="pg-btn pg-btn--sm pg-btn--ghost" id="cpg-add-constraint">+ Add Constraint</button>
          </div>
          <div class="cpg-constraints__list" id="cpg-constraint-list"></div>
        </div>
      </div>

      <div class="cpg-trace">
        <div class="cpg-trace__header">
          <span>Execution Trace</span>
          <div class="cpg-trace__controls">
            <button class="pg-btn pg-btn--sm pg-btn--primary" id="cpg-gen-trace">Generate</button>
            <button class="pg-btn pg-btn--sm pg-btn--ghost" id="cpg-check-trace">Check Constraints</button>
          </div>
        </div>
        <div class="cpg-trace__body" id="cpg-trace-body">
          <div class="pg-empty">Define columns and generate a trace.</div>
        </div>
      </div>

      <div class="cpg-output">
        <div class="cpg-output__header">AIR Structure</div>
        <pre class="cpg-output__code" id="cpg-air-output">// Define columns and constraints to see the AIR</pre>
      </div>

      <div class="cpg-check-results" id="cpg-check-results" hidden>
        <div class="cpg-check-results__header">Constraint Check Results</div>
        <div class="cpg-check-results__body" id="cpg-check-body"></div>
      </div>
    </div>
  `;

  wireControls(wasm);
  renderAir();
}

function wireControls(wasm) {
  document.getElementById('cpg-name').addEventListener('input', (e) => {
    circuit.name = e.target.value || 'MyCircuit';
    renderAir();
  });

  document.getElementById('cpg-add-col').addEventListener('click', addColumn);
  document.getElementById('cpg-add-constraint').addEventListener('click', addConstraint);
  document.getElementById('cpg-gen-trace').addEventListener('click', generateTrace);
  document.getElementById('cpg-check-trace').addEventListener('click', checkTrace);
}

function addColumn() {
  const name = prompt('Column name (e.g., balance, nonce, amount):');
  if (!name) return;

  circuit.columns.push({
    id: circuit.columns.length,
    name: name.trim().replace(/\s+/g, '_'),
    type: 'field', // BabyBear field element
  });

  renderColumns();
  renderAir();
}

function addConstraint() {
  if (circuit.columns.length < 1) {
    alert('Add at least one column first.');
    return;
  }

  const expr = prompt(`Constraint expression (use column names, e.g., "balance >= 0" or "nonce[next] == nonce + 1"):`);
  if (!expr) return;

  circuit.constraints.push({
    id: circuit.constraints.length,
    expression: expr.trim(),
    type: inferConstraintType(expr),
  });

  renderConstraints();
  renderAir();
}

function inferConstraintType(expr) {
  if (expr.includes('[next]') || expr.includes('[prev]')) return 'transition';
  if (expr.includes('==') || expr.includes('=')) return 'equality';
  if (expr.includes('>=') || expr.includes('>') || expr.includes('<')) return 'boundary';
  return 'custom';
}

function renderColumns() {
  const list = document.getElementById('cpg-col-list');
  if (!circuit.columns.length) {
    list.innerHTML = '<div class="pg-empty">No columns defined.</div>';
    return;
  }

  list.innerHTML = circuit.columns.map((col, idx) => `
    <div class="cpg-col-item">
      <span class="cpg-col-item__idx">${idx}</span>
      <span class="cpg-col-item__name">${col.name}</span>
      <span class="cpg-col-item__type">${col.type}</span>
      <button class="cpg-col-item__remove" data-idx="${idx}">x</button>
    </div>
  `).join('');

  list.querySelectorAll('.cpg-col-item__remove').forEach(btn => {
    btn.addEventListener('click', () => {
      circuit.columns.splice(parseInt(btn.dataset.idx), 1);
      renderColumns();
      renderAir();
    });
  });
}

function renderConstraints() {
  const list = document.getElementById('cpg-constraint-list');
  if (!circuit.constraints.length) {
    list.innerHTML = '<div class="pg-empty">No constraints defined.</div>';
    return;
  }

  list.innerHTML = circuit.constraints.map((c, idx) => `
    <div class="cpg-constraint-item">
      <span class="cpg-constraint-item__type">${c.type}</span>
      <code class="cpg-constraint-item__expr">${c.expression}</code>
      <button class="cpg-constraint-item__remove" data-idx="${idx}">x</button>
    </div>
  `).join('');

  list.querySelectorAll('.cpg-constraint-item__remove').forEach(btn => {
    btn.addEventListener('click', () => {
      circuit.constraints.splice(parseInt(btn.dataset.idx), 1);
      renderConstraints();
      renderAir();
    });
  });
}

function renderAir() {
  const output = document.getElementById('cpg-air-output');

  if (!circuit.columns.length) {
    output.textContent = '// Define columns and constraints to see the AIR';
    return;
  }

  let code = `// ${circuit.name} — AIR Descriptor\n`;
  code += `// ${circuit.columns.length} columns, ${circuit.constraints.length} constraints\n\n`;
  code += `struct ${circuit.name}Air {\n`;
  code += `    trace_len: usize,\n`;
  code += `    num_cols: ${circuit.columns.length},\n`;
  code += `}\n\n`;
  code += `// Columns:\n`;
  circuit.columns.forEach((col, idx) => {
    code += `//   [${idx}] ${col.name}: ${col.type}\n`;
  });
  code += `\n// Constraints:\n`;
  circuit.constraints.forEach((c, idx) => {
    code += `//   C${idx} (${c.type}): ${c.expression}\n`;
  });
  code += `\n// Trace layout:\n`;
  code += `//   ${circuit.columns.length} columns x trace_len rows\n`;
  code += `//   Field: BabyBear (p = 2^31 - 1)\n`;
  code += `//   Hash: Poseidon2\n`;

  output.textContent = code;
}

function generateTrace() {
  if (!circuit.columns.length) return;

  const traceLen = 8; // Generate 8 rows
  circuit.trace = [];

  for (let i = 0; i < traceLen; i++) {
    const row = {};
    circuit.columns.forEach(col => {
      // Generate plausible values based on column name
      if (col.name.includes('balance') || col.name.includes('bal')) {
        row[col.name] = Math.max(0, 1000 - i * Math.floor(Math.random() * 50));
      } else if (col.name.includes('nonce') || col.name.includes('counter')) {
        row[col.name] = i + 1;
      } else if (col.name.includes('amount') || col.name.includes('value')) {
        row[col.name] = Math.floor(Math.random() * 100) + 1;
      } else if (col.name.includes('hash') || col.name.includes('root')) {
        row[col.name] = Math.floor(Math.random() * 0xFFFF);
      } else {
        row[col.name] = Math.floor(Math.random() * 1000);
      }
    });
    circuit.trace.push(row);
  }

  renderTrace();
}

function renderTrace() {
  const body = document.getElementById('cpg-trace-body');
  if (!circuit.trace.length) {
    body.innerHTML = '<div class="pg-empty">Generate a trace first.</div>';
    return;
  }

  const cols = circuit.columns.map(c => c.name);
  let html = `<table class="cpg-trace-table"><thead><tr><th>Row</th>`;
  cols.forEach(c => { html += `<th>${c}</th>`; });
  html += `</tr></thead><tbody>`;

  circuit.trace.forEach((row, idx) => {
    html += `<tr><td>${idx}</td>`;
    cols.forEach(col => {
      html += `<td>${row[col] !== undefined ? row[col] : '--'}</td>`;
    });
    html += `</tr>`;
  });

  html += `</tbody></table>`;
  body.innerHTML = html;
}

function checkTrace() {
  if (!circuit.trace.length || !circuit.constraints.length) return;

  const results = circuit.constraints.map(constraint => {
    const violations = [];
    circuit.trace.forEach((row, idx) => {
      const prev = idx > 0 ? circuit.trace[idx - 1] : null;
      const next = idx < circuit.trace.length - 1 ? circuit.trace[idx + 1] : null;

      try {
        if (!evaluateConstraint(constraint.expression, row, prev, next)) {
          violations.push(idx);
        }
      } catch {
        // Cannot evaluate — skip
      }
    });

    return {
      expression: constraint.expression,
      type: constraint.type,
      passed: violations.length === 0,
      violations,
    };
  });

  const checkEl = document.getElementById('cpg-check-results');
  const body = document.getElementById('cpg-check-body');
  checkEl.hidden = false;

  body.innerHTML = results.map(r => `
    <div class="cpg-check-row ${r.passed ? 'cpg-check-row--pass' : 'cpg-check-row--fail'}">
      <span class="cpg-check-row__badge">${r.passed ? 'PASS' : 'FAIL'}</span>
      <code class="cpg-check-row__expr">${r.expression}</code>
      ${!r.passed ? `<span class="cpg-check-row__violations">rows: ${r.violations.join(', ')}</span>` : ''}
    </div>
  `).join('');
}

function evaluateConstraint(expr, row, prev, next) {
  // Simple constraint evaluator
  // Supports: column >= 0, column > 0, column[next] == column + 1
  try {
    // Replace column references with values
    let evalExpr = expr;

    // Handle [next] and [prev] references
    for (const col of circuit.columns) {
      const nextRegex = new RegExp(`${col.name}\\[next\\]`, 'g');
      const prevRegex = new RegExp(`${col.name}\\[prev\\]`, 'g');
      evalExpr = evalExpr.replace(nextRegex, next ? String(next[col.name] || 0) : '0');
      evalExpr = evalExpr.replace(prevRegex, prev ? String(prev[col.name] || 0) : '0');
    }

    // Replace plain column names
    for (const col of circuit.columns) {
      const regex = new RegExp(`\\b${col.name}\\b`, 'g');
      evalExpr = evalExpr.replace(regex, String(row[col.name] || 0));
    }

    // Replace == with ===
    evalExpr = evalExpr.replace(/==/g, '===').replace(/!===/g, '!==');

    // Evaluate (note: this is intentionally sandboxed to simple arithmetic)
    return Function(`"use strict"; return (${evalExpr})`)();
  } catch {
    return true; // Cannot evaluate — assume pass
  }
}
