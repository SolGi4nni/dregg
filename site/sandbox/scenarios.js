// dregg sandbox — pre-built code scenarios
// Each scenario is a named snippet that users can load into the editor.

export const scenarios = [
  {
    id: 'mint-attenuate',
    name: 'Mint & Attenuate',
    description: 'Mint a root token, attenuate it twice with service restrictions, and verify.',
    code: `// Mint & Attenuate — full token lifecycle
const root = await dregg.generateRootKey();
console.log("Root key:", root.key_hex);

// Mint a root token
const minted = await dregg.mintToken(root.key_bytes, "dregg.dev");
console.log("Minted token:", minted.token.slice(0, 40) + "...");

// Attenuate: restrict to DNS service, read-only, 1hr expiry
const att1 = await dregg.attenuate(minted.token, root.key_bytes, "dns", "read", 3600n);
console.log("Attenuated (dns/read):", att1.token.slice(0, 40) + "...");
console.log("Caveats added:", att1.caveats_added);

// Further attenuate: restrict to specific app
const att2 = await dregg.attenuate(att1.token, root.key_bytes, "dns", "read", 1800n);
console.log("Attenuated again (shorter expiry):", att2.token.slice(0, 40) + "...");

// Verify against allowed action
const v1 = await dregg.verifyToken(att1.token, root.key_bytes, "my-app", "read");
console.log("Verify (read):", v1.allowed ? "ALLOWED" : "DENIED", "-", v1.policy);

// Verify against disallowed action
const v2 = await dregg.verifyToken(att1.token, root.key_bytes, "my-app", "write");
console.log("Verify (write):", v2.allowed ? "ALLOWED" : "DENIED", "-", v2.policy);
`,
  },
  {
    id: 'stark-proof',
    name: 'Generate STARK Proof',
    description: 'Generate a real STARK proof, verify it, tamper with it, and verify again.',
    code: `// STARK Proof — generate, verify, tamper, re-verify
const t0 = performance.now();
const proof = await dregg.generateStarkProof(42, 4);
const proveTime = (performance.now() - t0).toFixed(1);

console.log("Proof generated in", proveTime, "ms");
console.log("Proof size:", proof.proof_size_bytes, "bytes");
console.log("Trace rows:", proof.trace_rows);
console.log("FRI queries:", proof.num_fri_queries);

// Verify the valid proof
const t1 = performance.now();
const valid = await dregg.verifyStarkProof(JSON.stringify(proof));
const verifyTime = (performance.now() - t1).toFixed(1);
console.log("\\nVerification:", valid.valid ? "VALID" : "INVALID", "(" + verifyTime + "ms)");

// Tamper with the proof
const tampered = await dregg.tamperProof(JSON.stringify(proof));
console.log("\\nTampered proof (bits flipped in trace values)");

// Verify tampered proof — should fail
const invalid = await dregg.verifyStarkProof(tampered);
console.log("Tampered verification:", invalid.valid ? "VALID (unexpected!)" : "INVALID (expected)");
if (invalid.error) console.log("Error:", invalid.error);
`,
  },
  {
    id: 'merkle-tree',
    name: 'Merkle Tree',
    description: 'Build a BLAKE3 Merkle tree, prove membership, and prove absence.',
    code: `// Merkle Tree — build, membership proof, absence proof
const leaves = ["alice", "bob", "carol", "dave", "eve"];

// Compute root
const tree = await dregg.merkleRoot(leaves);
console.log("Merkle root:", tree.root_hex);
console.log("Leaves:", tree.num_leaves, "| Depth:", tree.tree_depth);

// Membership proof for "bob"
console.log("\\n--- Membership proof (bob) ---");
const memberProof = await dregg.merkleMembership(leaves, "bob");
console.log("Verified:", memberProof.verified);
console.log("Leaf index:", memberProof.leaf_index);
console.log("Path length:", memberProof.proof_path?.length || 0);

// Membership proof for "eve"
console.log("\\n--- Membership proof (eve) ---");
const eveProof = await dregg.merkleMembership(leaves, "eve");
console.log("Verified:", eveProof.verified);
console.log("Leaf index:", eveProof.leaf_index);

// Non-membership (absence) for "frank"
console.log("\\n--- Absence proof (frank) ---");
try {
  const absence = await dregg.merkleMembership(leaves, "frank");
  console.log("Found:", absence.verified);
} catch (e) {
  console.log("Correctly rejected: frank is not in the tree");
}

// Show how root changes when adding a leaf
const leaves2 = [...leaves, "frank"];
const tree2 = await dregg.merkleRoot(leaves2);
console.log("\\nNew root (with frank):", tree2.root_hex);
console.log("Root changed:", tree.root_hex !== tree2.root_hex);
`,
  },
  {
    id: 'datalog-policy',
    name: 'Datalog Policy',
    description: 'Evaluate RBAC rules with the Datalog engine, show full derivation trace.',
    code: `// Datalog Policy — RBAC evaluation with derivation trace
const facts = [
  { predicate: "app", terms: ["my-app", "read,write"] },
  { predicate: "service", terms: ["dns", "read,write"] },
  { predicate: "service", terms: ["compute", "execute"] },
];

// Request that should be ALLOWED (app has read permission)
console.log("--- Request: my-app/read ---");
const req1 = { app_id: "my-app", action: "read", now: Date.now() / 1000 | 0 };
const result1 = await dregg.evaluateDatalog(facts, req1);
console.log("Decision:", result1.decision);
console.log("Matched rule:", result1.matched_rule);
if (result1.steps) {
  result1.steps.forEach((s, i) => console.log("  Step " + (i+1) + ":", s.rule, "->", s.result));
}

// Request that should be DENIED (no delete permission)
console.log("\\n--- Request: my-app/delete ---");
const req2 = { app_id: "my-app", action: "delete", now: Date.now() / 1000 | 0 };
const result2 = await dregg.evaluateDatalog(facts, req2);
console.log("Decision:", result2.decision);
console.log("Matched rule:", result2.matched_rule || "(default deny)");

// Request with unrestricted token
console.log("\\n--- Request: unrestricted token ---");
const unrestrictedFacts = [{ predicate: "unrestricted", terms: ["true"] }];
const req3 = { app_id: "anything", action: "nuke", now: Date.now() / 1000 | 0 };
const result3 = await dregg.evaluateDatalog(unrestrictedFacts, req3);
console.log("Decision:", result3.decision);
console.log("Matched rule:", result3.matched_rule);
`,
  },
  {
    id: 'fold-chain',
    name: 'Fold Chain',
    description: 'Demonstrate attenuation narrowing via cryptographic fold operations.',
    code: `// Fold Chain — cryptographic attenuation narrowing
// Start with broad permissions, narrow them down

const initialFacts = [
  "owns:secret.txt",
  "owns:public.txt",
  "can_read:secret.txt",
  "can_read:public.txt",
  "can_write:secret.txt",
  "can_write:public.txt",
  "can_execute:deploy.sh",
];

console.log("Initial facts:", initialFacts.length);
initialFacts.forEach(f => console.log("  +", f));

// First fold: remove write access to secret.txt
console.log("\\n--- Fold 1: Remove write to secret ---");
const remove1 = ["can_write:secret.txt"];
const fold1 = await dregg.demonstrateFold(initialFacts, remove1);
console.log("Old root:", fold1.old_root?.slice(0, 16) + "...");
console.log("New root:", fold1.new_root?.slice(0, 16) + "...");
console.log("Verified:", fold1.verified);
console.log("Remaining facts:", fold1.remaining_count);

// Second fold: also remove read access to secret.txt
console.log("\\n--- Fold 2: Remove read to secret ---");
const factsAfter1 = initialFacts.filter(f => !remove1.includes(f));
const remove2 = ["can_read:secret.txt"];
const fold2 = await dregg.demonstrateFold(factsAfter1, remove2);
console.log("Old root:", fold2.old_root?.slice(0, 16) + "...");
console.log("New root:", fold2.new_root?.slice(0, 16) + "...");
console.log("Verified:", fold2.verified);
console.log("Remaining facts:", fold2.remaining_count);

// Third fold: remove execute permission
console.log("\\n--- Fold 3: Remove execute ---");
const factsAfter2 = factsAfter1.filter(f => !remove2.includes(f));
const remove3 = ["can_execute:deploy.sh"];
const fold3 = await dregg.demonstrateFold(factsAfter2, remove3);
console.log("Verified:", fold3.verified);
console.log("Remaining facts:", fold3.remaining_count);

console.log("\\nAttenuation chain: 7 facts -> 6 -> 5 -> 4");
console.log("Each fold produces a new cryptographic commitment.");
`,
  },
  {
    id: 'full-pipeline',
    name: 'Full Pipeline',
    description: 'Complete flow: mint, attenuate, commit to Merkle tree, generate STARK proof, verify.',
    code: `// Full Pipeline — mint -> attenuate -> commit -> prove -> verify
const t0 = performance.now();

// Step 1: Generate root key
console.log("=== Step 1: Generate Root Key ===");
const root = await dregg.generateRootKey();
console.log("Key:", root.key_hex.slice(0, 16) + "...");

// Step 2: Mint token
console.log("\\n=== Step 2: Mint Token ===");
const minted = await dregg.mintToken(root.key_bytes, "dregg.dev");
console.log("Token:", minted.token.slice(0, 32) + "...");

// Step 3: Attenuate
console.log("\\n=== Step 3: Attenuate (dns/read, 1hr) ===");
const att = await dregg.attenuate(minted.token, root.key_bytes, "dns", "read", 3600n);
console.log("Attenuated token:", att.token.slice(0, 32) + "...");
console.log("Caveats:", att.caveats_added);

// Step 4: Commit to Merkle tree
console.log("\\n=== Step 4: Merkle Commitment ===");
const tokenHash = await dregg.blake3Hash(att.token);
const leaves = [tokenHash, "other-commitment-1", "other-commitment-2", "other-commitment-3"];
const tree = await dregg.merkleRoot(leaves);
console.log("Merkle root:", tree.root_hex.slice(0, 24) + "...");
console.log("Tree depth:", tree.tree_depth);

// Step 5: Generate STARK proof
console.log("\\n=== Step 5: STARK Proof ===");
const proof = await dregg.generateStarkProof(42, 4);
console.log("Proof size:", proof.proof_size_bytes, "bytes");
console.log("Trace rows:", proof.trace_rows);

// Step 6: Verify everything
console.log("\\n=== Step 6: Verify ===");
const tokenOk = await dregg.verifyToken(att.token, root.key_bytes, "my-app", "read");
console.log("Token valid:", tokenOk.allowed);

const proofOk = await dregg.verifyStarkProof(JSON.stringify(proof));
console.log("Proof valid:", proofOk.valid);

const elapsed = (performance.now() - t0).toFixed(1);
console.log("\\n=== Pipeline complete in", elapsed, "ms ===");
console.log("All cryptographic operations ran client-side in WASM.");
`,
  },
];
