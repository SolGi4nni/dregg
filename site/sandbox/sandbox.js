// pyana sandbox — execution engine
// Loads WASM, wraps it in a safe eval context, manages console output.

import { scenarios } from './scenarios.js';

// ============================================================================
// State
// ============================================================================

let wasm = null;
let wasmReady = false;
let isRunning = false;
let adminConnected = false;
let adminKeyBytes = null;

// ============================================================================
// DOM References
// ============================================================================

const editor = document.getElementById('editor');
const output = document.getElementById('output');
const btnRun = document.getElementById('btn-run');
const btnClear = document.getElementById('btn-clear');
const scenarioBar = document.getElementById('scenario-bar');
const wasmStatus = document.getElementById('wasm-status');
const runIndicator = document.getElementById('run-indicator');
const fedPanel = document.getElementById('federation-panel');
const adminBtn = document.getElementById('btn-admin');
const adminKeyInput = document.getElementById('admin-key-input');
const adminSection = document.getElementById('admin-section');
const adminStatus = document.getElementById('admin-status');

// ============================================================================
// WASM Loading
// ============================================================================

async function loadWasm() {
  wasmStatus.textContent = 'loading wasm...';
  wasmStatus.className = 'status-badge loading';

  try {
    const { default: init, ...exports } = await import('../demo/pkg/pyana_wasm.js');
    await init();
    wasm = exports;
    wasmReady = true;
    wasmStatus.textContent = 'wasm ready';
    wasmStatus.className = 'status-badge ready';
    btnRun.disabled = false;
  } catch (e) {
    wasmStatus.textContent = 'wasm error';
    wasmStatus.className = 'status-badge error';
    appendOutput('error', `Failed to load WASM: ${e.message}\n\nBuild with: cd wasm && wasm-pack build --target web --out-dir ../site/demo/pkg`);
  }
}

// ============================================================================
// Pyana API Wrapper
// ============================================================================

function createPyanaApi() {
  return {
    generateRootKey: () => wasm.generate_root_key(),
    mintToken: (keyBytes, location) => wasm.mint_token(keyBytes, location),
    attenuate: (token, keyBytes, service, actions, expiresSecs) =>
      wasm.attenuate_token(token, keyBytes, service, actions, expiresSecs),
    verifyToken: (token, keyBytes, appId, action) =>
      wasm.verify_token(token, keyBytes, appId, action),
    generateStarkProof: (leafValue, depth) => wasm.generate_stark_proof(leafValue, depth),
    verifyStarkProof: (json) => wasm.verify_stark_proof(json),
    tamperProof: (json) => wasm.tamper_stark_proof(json),
    merkleRoot: (leaves) => wasm.compute_merkle_root(JSON.stringify(leaves)),
    merkleMembership: (leaves, target) => wasm.merkle_membership_proof(JSON.stringify(leaves), target),
    evaluateDatalog: (facts, req) => wasm.evaluate_datalog(JSON.stringify(facts), JSON.stringify(req)),
    demonstrateFold: (facts, remove) => wasm.demonstrate_fold(JSON.stringify(facts), JSON.stringify(remove)),
    computeIntentId: (json) => wasm.compute_intent_id(json),
    blake3Hash: (input) => wasm.blake3_hash(input),
  };
}

// ============================================================================
// Output Console
// ============================================================================

function clearOutput() {
  output.innerHTML = '';
}

function appendOutput(type, text) {
  const entry = document.createElement('div');
  entry.className = `output-entry ${type}`;

  const timestamp = new Date().toLocaleTimeString([], {
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    fractionalSecondDigits: 3,
  });

  const timeSpan = document.createElement('span');
  timeSpan.className = 'output-time';
  timeSpan.textContent = timestamp;

  const textSpan = document.createElement('span');
  textSpan.className = 'output-text';
  textSpan.textContent = text;

  entry.appendChild(timeSpan);
  entry.appendChild(textSpan);
  output.appendChild(entry);
  output.scrollTop = output.scrollHeight;
}

function createSandboxConsole() {
  return {
    log: (...args) => {
      const text = args.map(a => {
        if (a === undefined) return 'undefined';
        if (a === null) return 'null';
        if (typeof a === 'object') {
          try { return JSON.stringify(a, null, 2); }
          catch { return String(a); }
        }
        return String(a);
      }).join(' ');
      appendOutput('log', text);
    },
    error: (...args) => {
      appendOutput('error', args.map(String).join(' '));
    },
    warn: (...args) => {
      appendOutput('warn', args.map(String).join(' '));
    },
    info: (...args) => {
      appendOutput('info', args.map(String).join(' '));
    },
  };
}

// ============================================================================
// Code Execution
// ============================================================================

async function executeCode() {
  if (!wasmReady || isRunning) return;

  const code = editor.value;
  if (!code.trim()) return;

  isRunning = true;
  btnRun.disabled = true;
  runIndicator.classList.add('active');
  clearOutput();

  const pyana = createPyanaApi();
  const console = createSandboxConsole();
  const startTime = performance.now();

  try {
    // Wrap user code in an async function and execute
    const asyncFn = new Function('pyana', 'console', 'performance', `
      return (async () => {
        ${code}
      })();
    `);

    await asyncFn(pyana, console, performance);

    const elapsed = (performance.now() - startTime).toFixed(1);
    appendOutput('timing', `Completed in ${elapsed}ms`);
  } catch (e) {
    appendOutput('error', `Error: ${e.message || e}`);
    if (e.stack) {
      // Clean up the stack trace to be more readable
      const cleanStack = e.stack
        .split('\n')
        .filter(line => !line.includes('sandbox.js') && !line.includes('Function'))
        .slice(0, 5)
        .join('\n');
      if (cleanStack.trim()) {
        appendOutput('error', cleanStack);
      }
    }
  } finally {
    isRunning = false;
    btnRun.disabled = false;
    runIndicator.classList.remove('active');
  }
}

// ============================================================================
// Scenario Loading
// ============================================================================

function loadScenario(scenario) {
  editor.value = scenario.code.trim();
  // Update active button
  document.querySelectorAll('.scenario-btn').forEach(b => b.classList.remove('active'));
  const btn = document.querySelector(`[data-scenario="${scenario.id}"]`);
  if (btn) btn.classList.add('active');
}

function setupScenarios() {
  scenarios.forEach(scenario => {
    const btn = document.createElement('button');
    btn.className = 'scenario-btn';
    btn.dataset.scenario = scenario.id;
    btn.textContent = scenario.name;
    btn.title = scenario.description;
    btn.addEventListener('click', () => loadScenario(scenario));
    scenarioBar.appendChild(btn);
  });
}

// ============================================================================
// Federation Status Panel
// ============================================================================

async function fetchFederationStatus() {
  try {
    const resp = await fetch('../discovery.json');
    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
    const data = await resp.json();
    renderFederationStatus(data);
  } catch (e) {
    renderFederationStatus(null);
  }
}

function renderFederationStatus(data) {
  if (!data) {
    fedPanel.innerHTML = `
      <div class="fed-item">
        <span class="fed-label">Status</span>
        <span class="fed-value fed-offline">offline</span>
      </div>
    `;
    return;
  }

  const nodeCount = data.federation?.length || 0;
  const updated = data.updated_at ? new Date(data.updated_at).toLocaleString() : '--';
  const commit = data.commit ? data.commit.slice(0, 8) : '--';
  const intentService = data.intent_service || 'none';

  fedPanel.innerHTML = `
    <div class="fed-item">
      <span class="fed-label">Nodes</span>
      <span class="fed-value">${nodeCount}</span>
    </div>
    <div class="fed-item">
      <span class="fed-label">Intent Pool</span>
      <span class="fed-value">${intentService}</span>
    </div>
    <div class="fed-item">
      <span class="fed-label">Updated</span>
      <span class="fed-value">${updated}</span>
    </div>
    <div class="fed-item">
      <span class="fed-label">Commit</span>
      <span class="fed-value fed-mono">${commit}</span>
    </div>
  `;

  // Render individual nodes if any
  if (data.federation && data.federation.length > 0) {
    const nodesHtml = data.federation.map(node => `
      <div class="fed-node">
        <span class="fed-node-name">${node.name || node.id || 'node'}</span>
        <span class="fed-node-status ${node.status || 'unknown'}">${node.status || '?'}</span>
      </div>
    `).join('');
    fedPanel.innerHTML += `<div class="fed-nodes">${nodesHtml}</div>`;
  }
}

// ============================================================================
// Admin Connection
// ============================================================================

function setupAdmin() {
  adminBtn.addEventListener('click', () => {
    const keyHex = adminKeyInput.value.trim();
    if (!keyHex) {
      adminStatus.textContent = 'enter a hex key';
      adminStatus.className = 'admin-status error';
      return;
    }

    if (!/^[0-9a-fA-F]{64}$/.test(keyHex)) {
      adminStatus.textContent = 'invalid key (need 64 hex chars)';
      adminStatus.className = 'admin-status error';
      return;
    }

    // Convert hex to Uint8Array
    adminKeyBytes = new Uint8Array(32);
    for (let i = 0; i < 32; i++) {
      adminKeyBytes[i] = parseInt(keyHex.slice(i * 2, i * 2 + 2), 16);
    }

    adminConnected = true;
    adminStatus.textContent = 'connected as admin';
    adminStatus.className = 'admin-status connected';
    adminSection.classList.add('visible');
    adminBtn.textContent = 'Disconnect';
    adminBtn.classList.add('connected');

    // Toggle disconnect behavior
    adminBtn.removeEventListener('click', arguments.callee);
    adminBtn.addEventListener('click', disconnectAdmin);
  });
}

function disconnectAdmin() {
  adminConnected = false;
  adminKeyBytes = null;
  adminStatus.textContent = '';
  adminStatus.className = 'admin-status';
  adminSection.classList.remove('visible');
  adminBtn.textContent = 'Connect';
  adminBtn.classList.remove('connected');
  adminKeyInput.value = '';

  // Re-setup connect handler
  setupAdmin();
}

function setupAdminActions() {
  document.getElementById('btn-admin-mint').addEventListener('click', async () => {
    if (!adminConnected || !wasmReady) return;
    const service = document.getElementById('admin-mint-service').value || 'default';
    try {
      const result = wasm.mint_token(adminKeyBytes, service);
      appendOutput('info', `[Admin] Minted token for "${service}": ${result.token.slice(0, 40)}...`);
    } catch (e) {
      appendOutput('error', `[Admin] Mint failed: ${e.message}`);
    }
  });

  document.getElementById('btn-admin-cells').addEventListener('click', async () => {
    if (!adminConnected || !wasmReady) return;
    appendOutput('info', '[Admin] Querying ledger cells...');
    // The WASM module does not have a direct cell query — show placeholder
    appendOutput('info', '[Admin] Demo ledger: no cells committed yet. Use the Full Pipeline scenario to generate state.');
  });

  document.getElementById('btn-admin-submit').addEventListener('click', async () => {
    if (!adminConnected || !wasmReady) return;
    const turnData = document.getElementById('admin-turn-data').value.trim();
    if (!turnData) {
      appendOutput('warn', '[Admin] Enter turn data (JSON)');
      return;
    }
    try {
      const intentId = wasm.compute_intent_id(turnData);
      appendOutput('info', `[Admin] Intent submitted. ID: ${intentId}`);
    } catch (e) {
      appendOutput('error', `[Admin] Submit failed: ${e.message}`);
    }
  });
}

// ============================================================================
// Keyboard Shortcuts
// ============================================================================

function setupKeyboard() {
  editor.addEventListener('keydown', (e) => {
    // Ctrl/Cmd + Enter to run
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
      e.preventDefault();
      executeCode();
    }

    // Tab inserts spaces
    if (e.key === 'Tab') {
      e.preventDefault();
      const start = editor.selectionStart;
      const end = editor.selectionEnd;
      editor.value = editor.value.substring(0, start) + '  ' + editor.value.substring(end);
      editor.selectionStart = editor.selectionEnd = start + 2;
    }
  });
}

// ============================================================================
// Initialize
// ============================================================================

async function init() {
  setupScenarios();
  setupKeyboard();
  setupAdmin();
  setupAdminActions();

  btnRun.addEventListener('click', executeCode);
  btnClear.addEventListener('click', clearOutput);

  // Load first scenario by default
  if (scenarios.length > 0) {
    loadScenario(scenarios[0]);
  }

  // Fetch federation status
  fetchFederationStatus();
  // Refresh every 30s
  setInterval(fetchFederationStatus, 30000);

  // Load WASM
  await loadWasm();
}

init();
