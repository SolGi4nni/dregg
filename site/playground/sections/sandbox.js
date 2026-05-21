// Sandbox section — free-form JS execution against the WASM API

import { state, notifyStateChange } from '../playground.js';

export function initSandbox(wasm) {
  const container = document.getElementById('section-sandbox');
  container.innerHTML = `
    <div class="section-header">
      <h2>Code Sandbox</h2>
      <p>
        Write and execute arbitrary JavaScript against the full pyana WASM API. The
        <code>pyana</code> object is available with all methods. Use Ctrl+Enter to run.
        Explore freely — everything executes client-side in your browser.
      </p>
    </div>

    <div class="controls-row" style="margin-bottom: 8px;">
      <button class="btn btn-primary" id="sb-run" ${wasm ? '' : 'disabled'}>Run (Ctrl+Enter)</button>
      <button class="btn btn-secondary" id="sb-clear">Clear Output</button>
      <select id="sb-scenarios" style="font-family:var(--mono);font-size:11px;padding:6px 10px;background:var(--surface-2);border:1px solid var(--border-2);border-radius:var(--radius);color:var(--text);outline:none;">
        <option value="">-- Load scenario --</option>
        <option value="mint">Mint & Attenuate</option>
        <option value="stark">STARK Proof</option>
        <option value="merkle">Merkle Tree</option>
        <option value="datalog">Datalog Policy</option>
        <option value="pipeline">Full Pipeline</option>
      </select>
    </div>

    <textarea class="sandbox-editor" id="sb-editor" spellcheck="false" placeholder="// Write JavaScript that calls the pyana WASM API...
// The 'pyana' object is available with all methods.

const key = await pyana.generateRootKey();
console.log('Root key:', key.key_hex);

const minted = await pyana.mintToken(key.key_bytes, 'pyana.dev');
console.log('Token:', minted.token.slice(0, 40) + '...');
"></textarea>

    <div class="sandbox-output" id="sb-output">
      <div style="color: var(--text-muted);">Output will appear here...</div>
    </div>

    <div class="sandbox-api-ref">
      <div class="sandbox-api-ref__title">API Reference</div>
      <div class="sandbox-api-ref__list">
        <div><span>pyana.generateRootKey</span>() &rarr; {key_hex, key_bytes}</div>
        <div><span>pyana.mintToken</span>(keyBytes, location) &rarr; {token}</div>
        <div><span>pyana.attenuate</span>(token, keyBytes, svc, actions, expiresBigInt) &rarr; {token, caveats_added}</div>
        <div><span>pyana.verifyToken</span>(token, keyBytes, appId, action) &rarr; {allowed, policy}</div>
        <div><span>pyana.generateStarkProof</span>(leafU32, depth) &rarr; {proof_size_bytes, trace_rows, ...}</div>
        <div><span>pyana.verifyStarkProof</span>(jsonStr) &rarr; {valid, error}</div>
        <div><span>pyana.tamperProof</span>(jsonStr) &rarr; tamperedJsonStr</div>
        <div><span>pyana.merkleRoot</span>(leavesArr) &rarr; {root_hex, num_leaves, tree_depth}</div>
        <div><span>pyana.merkleMembership</span>(leavesArr, target) &rarr; {verified, leaf_index, proof_path}</div>
        <div><span>pyana.evaluateDatalog</span>(factsArr, reqObj) &rarr; {decision, matched_rule, steps}</div>
        <div><span>pyana.demonstrateFold</span>(factsArr, removeArr) &rarr; {old_root, new_root, verified}</div>
        <div><span>pyana.blake3Hash</span>(input) &rarr; hexStr</div>
      </div>
    </div>
  `;

  if (!wasm) return;

  const editor = container.querySelector('#sb-editor');
  const output = container.querySelector('#sb-output');
  const runBtn = container.querySelector('#sb-run');
  const clearBtn = container.querySelector('#sb-clear');
  const scenarioSelect = container.querySelector('#sb-scenarios');

  // Pyana API wrapper
  const pyana = {
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

  function appendOutput(level, text) {
    const entry = document.createElement('div');
    entry.className = `output-entry ${level}`;
    entry.textContent = text;
    output.appendChild(entry);
    output.scrollTop = output.scrollHeight;
  }

  function clearOutput() {
    output.innerHTML = '';
  }

  async function executeCode() {
    const code = editor.value.trim();
    if (!code) return;

    clearOutput();
    const startTime = performance.now();

    const sandboxConsole = {
      log: (...args) => appendOutput('info', formatArgs(args)),
      error: (...args) => appendOutput('error', formatArgs(args)),
      warn: (...args) => appendOutput('warning', formatArgs(args)),
      info: (...args) => appendOutput('info', formatArgs(args)),
    };

    try {
      const fn = new Function('pyana', 'console', 'performance', `return (async () => { ${code} })();`);
      await fn(pyana, sandboxConsole, performance);
      const elapsed = (performance.now() - startTime).toFixed(1);
      appendOutput('success', `Completed in ${elapsed}ms`);
    } catch (e) {
      appendOutput('error', `Error: ${e.message || e}`);
    }
  }

  function formatArgs(args) {
    return args.map(a => {
      if (a === undefined) return 'undefined';
      if (a === null) return 'null';
      if (typeof a === 'object') {
        try { return JSON.stringify(a, null, 2); }
        catch { return String(a); }
      }
      return String(a);
    }).join(' ');
  }

  // Events
  runBtn.addEventListener('click', executeCode);
  clearBtn.addEventListener('click', clearOutput);

  editor.addEventListener('keydown', (e) => {
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
      e.preventDefault();
      executeCode();
    }
    if (e.key === 'Tab') {
      e.preventDefault();
      const start = editor.selectionStart;
      const end = editor.selectionEnd;
      editor.value = editor.value.substring(0, start) + '  ' + editor.value.substring(end);
      editor.selectionStart = editor.selectionEnd = start + 2;
    }
  });

  // Scenario loading
  const scenarios = {
    mint: `// Mint & Attenuate — full token lifecycle
const root = await pyana.generateRootKey();
console.log("Root key:", root.key_hex);

const minted = await pyana.mintToken(root.key_bytes, "pyana.dev");
console.log("Minted:", minted.token.slice(0, 40) + "...");

const att = await pyana.attenuate(minted.token, root.key_bytes, "dns", "read", 3600n);
console.log("Attenuated (dns/read):", att.token.slice(0, 40) + "...");
console.log("Caveats added:", att.caveats_added);

const v1 = await pyana.verifyToken(att.token, root.key_bytes, "my-app", "read");
console.log("Verify read:", v1.allowed ? "ALLOWED" : "DENIED");

const v2 = await pyana.verifyToken(att.token, root.key_bytes, "my-app", "write");
console.log("Verify write:", v2.allowed ? "ALLOWED" : "DENIED");`,

    stark: `// STARK Proof — generate, verify, tamper, re-verify
const t0 = performance.now();
const proof = await pyana.generateStarkProof(42, 4);
console.log("Proof generated in", (performance.now() - t0).toFixed(1), "ms");
console.log("Size:", proof.proof_size_bytes, "bytes");
console.log("Trace rows:", proof.trace_rows);

const valid = await pyana.verifyStarkProof(JSON.stringify(proof));
console.log("Verify:", valid.valid ? "VALID" : "INVALID");

const tampered = await pyana.tamperProof(JSON.stringify(proof));
const invalid = await pyana.verifyStarkProof(tampered);
console.log("Tampered:", invalid.valid ? "VALID" : "INVALID (expected)");`,

    merkle: `// Merkle Tree — build, prove membership, prove absence
const leaves = ["alice", "bob", "carol", "dave", "eve"];
const tree = await pyana.merkleRoot(leaves);
console.log("Root:", tree.root_hex);
console.log("Leaves:", tree.num_leaves, "| Depth:", tree.tree_depth);

const proof = await pyana.merkleMembership(leaves, "bob");
console.log("Bob membership:", proof.verified, "at index", proof.leaf_index);

const tree2 = await pyana.merkleRoot([...leaves, "frank"]);
console.log("New root (with frank):", tree2.root_hex);
console.log("Root changed:", tree.root_hex !== tree2.root_hex);`,

    datalog: `// Datalog — policy evaluation with derivation trace
const facts = [
  { predicate: "app", terms: ["my-app", "read,write"] },
  { predicate: "service", terms: ["dns", "read,write"] },
];

const req1 = { app_id: "my-app", action: "read", now: Date.now() / 1000 | 0 };
const r1 = await pyana.evaluateDatalog(facts, req1);
console.log("my-app/read:", r1.decision, "-", r1.matched_rule);

const req2 = { app_id: "my-app", action: "delete", now: Date.now() / 1000 | 0 };
const r2 = await pyana.evaluateDatalog(facts, req2);
console.log("my-app/delete:", r2.decision, "-", r2.matched_rule || "default deny");`,

    pipeline: `// Full Pipeline — mint -> attenuate -> commit -> prove -> verify
const t0 = performance.now();

const root = await pyana.generateRootKey();
console.log("1. Key:", root.key_hex.slice(0, 16) + "...");

const minted = await pyana.mintToken(root.key_bytes, "pyana.dev");
console.log("2. Token:", minted.token.slice(0, 32) + "...");

const att = await pyana.attenuate(minted.token, root.key_bytes, "dns", "read", 3600n);
console.log("3. Attenuated:", att.caveats_added, "caveats");

const hash = await pyana.blake3Hash(att.token);
const tree = await pyana.merkleRoot([hash, "other-1", "other-2", "other-3"]);
console.log("4. Merkle root:", tree.root_hex.slice(0, 24) + "...");

const proof = await pyana.generateStarkProof(42, 4);
console.log("5. STARK proof:", proof.proof_size_bytes, "bytes");

const tokenOk = await pyana.verifyToken(att.token, root.key_bytes, "app", "read");
const proofOk = await pyana.verifyStarkProof(JSON.stringify(proof));
console.log("6. Token valid:", tokenOk.allowed, "| Proof valid:", proofOk.valid);
console.log("\\nPipeline complete in", (performance.now() - t0).toFixed(1), "ms");`,
  };

  scenarioSelect.addEventListener('change', () => {
    const id = scenarioSelect.value;
    if (id && scenarios[id]) {
      editor.value = scenarios[id];
      scenarioSelect.value = '';
    }
  });
}
