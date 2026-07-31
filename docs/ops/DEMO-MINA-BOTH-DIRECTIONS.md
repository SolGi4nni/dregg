# DEMO-MINA-BOTH-DIRECTIONS — two commands, two light clients

A rehearsed, scripted demonstration that **Mina verifies dregg** and **dregg
verifies Mina**, one command per direction:

```bash
bridge/demo/mina-verifies-dregg.sh      # a Mina zkApp moves its dregg head because a proof verified
bridge/demo/dregg-verifies-mina.sh      # dregg reads Mina's protocol off the peer-to-peer wire
```

Both are safe to run by default. The first touches no chain without
`--broadcast`; the second has no broadcast at all, because a client reading a
chain has nothing to send.

**Honest scope up front.** Throwaway-key, no-real-value **Mina devnet**. The
dregg side of direction 1 is gated on artifacts that do not exist yet — the
131-program compile and the 905-instance prove — and the script says
`BLOCKED` at exactly those steps rather than substituting anything. **The live
broadcast is ember-gated**: this document and both scripts prepare and verify;
ember passes `--broadcast`.

---

## State measured while writing this runbook (2026-07-30, on hbox unless noted)

| Thing | Status | Detail |
|---|---|---|
| Mina devnet GraphQL | ✅ live | `api.minascan.io/node/devnet/v1/graphql`, `SYNCED`, height **540265** |
| devnet deployer balance | ✅ funded | **294.6 MINA**, nonce 11 — no faucet round trip needed |
| devnet p2p seeds | ✅ reachable | `get_best_tip` returned **48,075** then **74,313 bytes** of `Protocol_state.Value` in ~1–2 s (size varies with the block) |
| hbox | ✅ ready | 24 c / 123 G, node **v20.16.0**, `linux-x64`, `npm ci` clean in 51 s |
| `@o1js/native-linux-x64` | ✅ installs | lands from `package-lock.json` via `npm ci`; no extra step |
| `O1JS_BACKEND=native` on hbox | ✅ **and the VK is bit-identical** | see the table below |
| `dregg-verifies-mina.sh` | ✅ **7/7 PASS** | full run, local, ~2 min including a release build; see §1.3 |
| `head-anchor` tier-0 | ✅ green | 12 out-of-circuit checks, **1.2 s** (local) |
| `head-gate-rehearsal` | ✅ green | 7 checks, **55.2 s** on hbox with the native backend |
| `head-anchor` tier-1 | ❌ **RED** | its accept row fails — **the harness, not the gate**; see §4 |
| `dregg-chain-pins.json` | ❌ absent | the 131-program compile has not run |
| terminal proof + seal preimage | ❌ absent | the 905-instance prove has not run, and nothing writes the preimage |
| proof-gated zkApp address | ❌ **needs a key ember must mint** | see §3.3 |

### The backend measurement, in full

Same probe (`npm run backend-probe`), same box, back to back:

| backend | compile | prove | verify | vkHash |
|---|---|---|---|---|
| default | 9.05 s | 7.09 s | 0.57 s | `2765220854366458311541571349876276113477426626758184243303679106217303748` `7108` |
| `O1JS_BACKEND=native` | **2.22 s** | **3.81 s** | **0.17 s** | *the same* |

4.1× compile, 1.9× prove, 3.4× verify. **The bit-identical verification key is
the load-bearing half**, not the speed: a deployed zkApp's *address* is a
function of its VK, and `DreggHeadGate` puts its chain pins *in* the VK by
design. Because the two backends agree, "compile on hbox with the native
backend, deploy from anywhere" is not a flag day. If they had disagreed it would
have been one, silently.

The scripts set `O1JS_BACKEND=native` themselves when the platform binary is
present and say so; on a platform where it is not, they say that too and run
slower. **They never fall back quietly.**

---

## 0. Preflight, both directions

```bash
cd /Users/ember/dev/breadstuffs          # or ~/dev/breadstuffs on hbox
node --version                            # >= 20 required; hbox has v20.16.0
python3 -c 'import cryptography; print(cryptography.__version__)'
```

**Expect:** `v20.16.0` and a version string. **A failure here means:** node is
too old (the o1js scripts refuse), or the Noise XX handshake in
`bridge/tools/mina-besttip.py` cannot run and direction 2 loses its live wire.

On hbox, run through the lane so the box stays safe:

```bash
PBUILD_HOST=hbox scripts/pbuild mina-deploy-demo 'cd bridge/mina-zkapp && npm ci --no-audit --no-fund'
```

**Expect:** `added 61 packages`, and `node_modules/@o1js/native-linux-x64`
present. **A failure here means:** the lane did not sync, or npm could not reach
the registry. Nothing downstream will work; fix it before anything else.

---

## 1. DIRECTION — dregg verifies Mina

```bash
bridge/demo/dregg-verifies-mina.sh
```

Read-only. No key exists for any step and none is needed: the chain-id
pre-shared key the p2p handshake uses is a **public devnet constant**, and the
helper mints ephemeral session keys per run.

### 1.1 What each step prints, and what a failure means

| step | expect | a failure means |
|---|---|---|
| **0 · preflight** | python + `cryptography`; the Lean archive's size | no archive ⇒ steps 4–5 report `BLOCKED`, because the decode and the selection rule **are** the archive. A client that cannot run the rule must not report that it ran |
| **1 · live wire** | `~48,000 bytes of Protocol_state.Value from a live devnet seed (peer …)` in ~1–3 s | the devnet seeds are unreachable *from this host* — a firewall or an outage, not a defect in the client. Reported `BLOCKED`, and the offline steps still run |
| **2 · transcription** | `blockchain_length 540186`, `field elements: 38`, `packed items: 819`, `max packed chunk < p: True`, and two state hashes | **FAIL is a real defect.** This is offline and deterministic: it recomputes a pinned block's state hash from its bytes. A change here means the packing drifted |
| **3 · the link** | `CONSECUTIVE PAIR: 540221 -> 540222` and `MATCH` | **FAIL is a real defect.** `derive_state_hash(N) == block N+1's previous_state_hash`, with both sides off the daemon's wire — the child block *is* the answer key, so no server is trusted |
| **4 · fork choice** | `test result: ok. N passed` for `mina_head` | the pairwise selection rule or the finalized-height ratchet broke. ⚑ Pairwise, never a fold: `beats_not_transitive` proves genuine 3-cycles at real Mina constants, so a `max_by` over a candidate set is order-dependent and exploitable |
| **5 · opening check** | the example proves and verifies on devnet block 539508 | either the Lean archive lacks `mina_state_hash_word_ok` (exit 2, reported `BLOCKED`), or the four byte-pinned opening descriptors were re-emitted and their sha256 pins no longer resolve — which is the **intended** failure mode of a re-emit, not a bug |

### 1.2 Options

```bash
bridge/demo/dregg-verifies-mina.sh --live-pair   # capture a FRESH consecutive pair (up to 25 min)
bridge/demo/dregg-verifies-mina.sh --offline     # no network at all
```

`--live-pair` waits for two tips whose `blockchain_length` differ by exactly 1.
Devnet blocks are ~3 minutes apart, so **expect 1–2 polls plus a wait**. Without
it the step replays the already-captured pair, which exercises the same
derivation over the same real bytes and takes seconds. The default is the replay
because a 25-minute wait in the middle of a demonstration is not a
demonstration.

⚠ Run the capture through the script, not by hand: `mina-consecutive-pair.py`'s
default `--out` **overwrites a tracked Lean source file**
(`metatheory/Dregg2/Bridge/MinaStateHashRealBlock.lean`). The script points it at
its own log directory.

### 1.3 The measured transcript (local, 2026-07-30)

```
PASS  python3 3.14.6 with cryptography 49.0.0
PASS  Lean archive present (149M) — the decode and the selection rule are the VERIFIED ones
PASS  74313 bytes of Protocol_state.Value from a live devnet seed (peer 12200c1f124de82a…)
PASS  state-hash transcription reproduces the pinned block
        [state_hash(540186) = 231507932081652385080107460246461513275005576881036378008873691820278099265
        08]
PASS  CONSECUTIVE PAIR: 540221 -> 540222 (protocol states 1544 and 1544 bytes) — MATCH
PASS  mina_head — test result: ok. 11 passed; 0 failed
PASS  opening check proved and verified on a real devnet block
```

Step 5's own line, which is the one worth quoting:

```
block 539508 | 4 slices x 1024 x 2131 = 8728576 cells | descriptors 5768911 B
resolve 60.8ms | witness 206.4ms | prove 15.36s | verify 263.3ms | proof 1120987 B
observer wall clock: 15.93s
descriptors (LEAN-AUTHORED, sha-pinned):
  dregg-pasta-rcb-sg-derive-{0,3640,7281,10921}-of-10922::v1
⚑ scope: 12 of 32,768 SRS generators are bound; this is ONE leg of the IPA
  verifier's two statements; the FRI/STARK floor and P10 are undischarged.
```

That last line is the example's own, printed on every run. It is not a caveat
added here — the leg reports its own scope, which is why this runbook does not
have to.

---

## 2. DIRECTION — Mina verifies dregg

```bash
bridge/demo/mina-verifies-dregg.sh                # rehearse
bridge/demo/mina-verifies-dregg.sh --broadcast    # BROADCAST → ember only
```

### 2.1 What each step prints, and what a failure means

| step | expect | a failure means |
|---|---|---|
| **0 · preflight** | node version, native-backend line, `Mina devnet SYNCED at height …` | the endpoint is down ⇒ step 4 is `BLOCKED`; steps 1–3 are local and still run |
| **1 · out of circuit** (`MINA_TIER=0`) | `12 out-of-circuit checks`, ~1 s | **FAIL is a real defect** in the head decision, the seal, or the bootstrap. On this directory's own record the cheap exhaustive differential is the *better* instrument — it is what found every defect the affordable proof runs missed |
| **2 · the deploy path** | deploy → `genesis` → `ACCEPTED` (head moves to H, turns = 3) → **4 refusals**, ~55 s on hbox | **FAIL is a real defect in the gate.** This compiles real Pickles circuits and runs a real `prove()` on a LocalBlockchain. It depends on **no dregg verification key** |
| **3 · the pins** | `dregg-chain-pins.json present: <label>` | `BLOCKED` today. Emitted by `npm run head-anchor-pins -- --emit` against a completed 131-program compile |
| **4 · on chain** | a deploy tx and an `advanceHead` tx, both included | `BLOCKED` without `--broadcast`, without pins, or without a fresh zkApp key. The two npm scripts refuse again on their own account and exit **3**, so "waiting on a named input" is distinguishable from "broken" |

### 2.2 The four refusals step 2 measures

Each is a real constraint failure against a real `prove()`:

- **the vk pin** — a proof of a *different program*, under its own real key.
- **`chainVkRoot`** — a seal computed under a different key-list root.
- **`totalSteps`** — a seal at a *shorter* chain. This one is not decoration: the
  chain's last block position emits `Provable.if(isQ[Q-1], seal, step)`, so the
  **same program and therefore the same key** produces a proof at every query. A
  chain that walked six of nineteen queries carries the identical claim, and
  pinning the key alone would accept it.
- **the extension check** — a segment that does not start at this client's head.

---

## 3. BROADCAST → the three things ember does

Everything below is outward-facing and irreversible. Nothing in this repository
performs any of it without an explicit flag.

### 3.1 Fund (already done, recorded here for a fresh reproduction)

```bash
cd bridge/mina-zkapp && npm run devnet:fund
```

The deployer holds **294.6 MINA**; the faucet is one-per-address, so this
reports `already funded` and exits 0. **A failure means** `rate-limit-ip` (wait
an hour) or a faucet outage — fund by hand at
`https://faucet.minaprotocol.com/?address=<deployer>`, choosing Devnet.

### 3.2 Deploy the proof-gated anchor

```bash
cd bridge/mina-zkapp && npm run devnet:head-deploy -- --broadcast
```

Writes `devnet-head-deployment.json` — public data only, plus the pins the VK
commits to and the weak-subjectivity attestation, so a third party can rebuild
the gate from the record and check that the address follows.

### 3.3 ⚑ THE ONE KEY THAT DOES NOT EXIST

The deployed `B62qkiRhX1tKdkYSXRHFASHQHj1tPf5VcLzgUhqkL3kuFViX9ckcSaN` holds
`DreggAttestedGate` and its address is published in `devnet-deployment.json`.
`DreggHeadGate` is a different contract whose pins live in its verification key
and therefore in its address, so it **must** deploy at a fresh one.

**`devnet-head-deploy.ts` will not mint it.** Key material is the operator's, and
a script that silently minted an address it then published would be publishing
an address whose provenance nobody can state. The refusal prints the exact
command; it is throwaway devnet key material and it goes in the same 0600 file
outside the repo:

```bash
node --input-type=module -e "import {PrivateKey} from 'o1js';
import {readFileSync,writeFileSync} from 'node:fs';
const p=process.env.HOME+'/.config/dregg-mina/devnet-keys.json';
const j=JSON.parse(readFileSync(p,'utf8'));
if(j.headZkAppPrivate)throw new Error('already present — refusing to overwrite');
const k=PrivateKey.random();
j.headZkAppPrivate=k.toBase58(); j.headZkAppPublic=k.toPublicKey().toBase58();
writeFileSync(p,JSON.stringify(j,null,2),{mode:0o600});
console.log(j.headZkAppPublic)"
```

### 3.4 Advance the head

```bash
cd bridge/mina-zkapp && npm run devnet:head-advance -- --broadcast
```

**This is the whole point.** `PLACEHOLDER_CUTOVER`'s P4 trigger is *one
observable thing*: an `advanceHead` transaction included on devnet, against pins
emitted by a real chain compile, consuming a real terminal proof. Not "the gate
compiles". Not "the stand-in is accepted".

The script checks three things out of circuit before spending a fee — that the
gate compiled from the current pins still has the **deployed** VK hash, that the
supplied key is the one the pins name, and that the exhibited seal preimage
reproduces the proof's boundary — so a mismatch is a printed comparison rather
than an opaque constraint failure inside a Pickles prove.

**A failure means:** if the head does not move, get the daemon to say why. A
zkApp transaction whose precondition failed is **included and failed** — it
spends the fee and bumps the nonce, and its effects are discarded. "The state
did not change" is only circumstantial evidence:

```bash
npm run devnet:tx-status -- <txHash>
```

⚑ `bestChain` reaches back a bounded number of blocks, so run that within about
an hour. After that the explorer is the record.

---

## 4. ⚑ Two defects this rehearsal found, and where they live

Both are in `bridge/mina-zkapp/scripts/head-anchor.ts`, which is another lane's
file. Neither is in the contract.

**(a) `MINA_TIER=1 npm run head-anchor` is RED.** Measured locally 2026-07-30:
seven rows print `REFUSED`, then the honest accept dies at `prevs_verified`.
`DreggTerminalProof.maxProofsVerified` is **1** — correct for the real object,
since `RootFriUniform`'s terminal program verifies its predecessor — while the
harness's stand-in producer has no proof input and is therefore **0**. Give the
producer a method that verifies a `SelfProof` and the **same gate accepts**:
head moves to H, turns = 3, in 6.2 s. Measured in
`scripts/head-gate-rehearsal.ts` §[2].

**(b) the vk-pin row is green over a false premise.** The harness prints
`compiled two stand-in producers … (vk hashes differ: false)` and then treats
the next row as evidence about the vk pin. Two o1js `ZkProgram`s differing
**only in name** compile to the **same verification key** — measured in
`head-gate-rehearsal.ts` §[0] — so the pin compares two equal fields and passes.
That row was refused by defect (a), not by the pin. A "different program" row
needs a different **constraint system**.

`head-gate-rehearsal.ts` is written around both: its producer B carries extra
constraints and therefore a genuinely different key, and its producers have a
`relay` method so their `maxProofsVerified` matches. It is what step 2 of the
demo runs.

---

## 5. What only the final VKs block

Everything in this list is waiting on **artifacts**, not on unwritten code. The
scripts exist, refuse precisely, and exit 3.

| # | blocked on | what it unblocks |
|---|---|---|
| 1 | **the 131-program compile** → `.fullchain/uniform-claim/key-*.json` | `npm run head-anchor-pins -- --emit` → `dregg-chain-pins.json` → the gate's VK → the deployed address |
| 2 | **the 905-instance prove** → `proof-<terminal spec>-q<Q>.json` | the object `advanceHead` consumes |
| 3 | **a seal-preimage handoff** — see below | the caller cannot exhibit the terminal seal without it |
| 4 | **one fresh zkApp keypair** (§3.3) | the address to deploy at |
| 5 | **the root proof re-bake** — `whole_history_proof.bin` is stale (`OodEvaluationMismatch`) after the last-row flag day | everything above it |

### ⚑ Item 3 is a gap in an emit, and it is small

`advanceHead(terminal, vk, friCommit, accOutDigest)` needs `friCommit` and
`accOutDigest`. They are **not recoverable from the proof** — the terminal seal
is a hash of them — and `root-fri-uniform.ts` writes per-instance meta
(`publicInput`, `publicOutput`, `vkHash`) that does not include them, though its
own `context()` holds both. So the prove run must write them down:

```jsonc
// .fullchain/terminal-handoff.json
{ "spec": "<uniformProgramName of the LAST block position>", "q": <last query index>,
  "proofPath": ".fullchain/uniform-claim/proof-<spec>-q<Q>.json",
  "vkPath":    ".fullchain/uniform-claim/key-<spec>.json",
  "friCommit": "<decimal Field>", "accOutDigest": "<decimal Field>" }
```

`devnet-head-advance.ts` also takes all four as `HEAD_PROOF`, `HEAD_VK`,
`HEAD_FRI_COMMIT`, `HEAD_ACC_OUT_DIGEST`, so a coordinator holding the numbers
does not have to wait for the emit.

---

## 6. When the chain is ready: how many commands, and how long

Two commands, in this order, both on hbox with `O1JS_BACKEND=native`:

```bash
bridge/demo/dregg-verifies-mina.sh                # direction 2 — no gating artifact
bridge/demo/mina-verifies-dregg.sh --broadcast    # direction 1 — needs items 1-4 above
```

| leg | measured / predicted | time |
|---|---|---|
| direction 2, steps 0–3 (live wire, transcription, link) | **measured** | ~10 s |
| direction 2, step 4 (`mina_head`) | measured, warm lane | ~1 min |
| direction 2, step 5 (opening check) | **predicted** — this leg is coupled to the dregg circuit crate and the four descriptor sha pins, so a re-emit turns it red | minutes |
| direction 1, steps 1–2 (tier-0 + rehearsal) | **measured on hbox** | 56 s |
| direction 1, step 4 deploy — compile `DreggHeadGate` at real pins | **predicted**, extrapolated from 12.1 s at stand-in pins; the real terminal proof's feature flags are wider | ~1–3 min |
| direction 1, step 4 deploy — inclusion on devnet | measured on the 2026-07-28 deploy | ~1 block, 1–3 min |
| direction 1, step 4 advance — prove + inclusion | **predicted** | ~2–5 min |

**Both directions demonstrated live: two commands, ~10 minutes of wall clock**,
of which most is Mina devnet block time and none is a rebuild — provided items
1–4 of §5 are in hand. Direction 2 alone is **under two minutes** and is ready
now.

---

## 7. What the demonstration shows, and what it does not

Stated here rather than left to a reader, and identical to what the scripts
print at the end of a run.

**Direction 1, an accepted advance establishes:** dregg's state went from `G` to
`H` in `N` turns with ordered-history commitment `D`, `G` was the head this
client already held, and a batch-STARK over the root's seven AIRs verified for
exactly that claim under the key list this gate's verification key names.

**It does not establish** that the committed function is low degree — the
FRI/STARK soundness floor is as undischarged here as everywhere in this tree —
nor that `H` is the head dregg **finalized**. A segment proof establishes that
`N` turns are *executable* from `G` to `H`; which executable future is canonical
is dregg's consensus's answer, and no committee signature or blocklace
certificate rides in this proof. `reportFork` exists because of exactly that,
and it **halts** rather than picking, because a client that picked would be
implementing first-come-wins and calling it finality.

**Direction 2 establishes:** bytes taken off Mina's own peer-to-peer stack decode
under a Lean-verified binprot decoder, hash to the state hash the *next* block
names as its parent, and drive a chain-selection rule and a finalized-height
ratchet that are machine-checked theorems rather than a hand-written `select`.

**It does not establish** that an accepted segment is the chain the network
selected — the opening check accepts an *anchored segment*, and two `k`-deep
segments under different anchors are indistinguishable to it. And the p2p helper
is **trusted for availability only**: every byte it produces goes through the
Lean decoder's refusals, so the worst a malicious helper achieves is to be
refused or to withhold — and withholding is the one thing no light client can be
defended against by any means.

---

## 8. Related

- `docs/ops/DEPLOY-SOLANA-COSMOS-TESTNET.md` — the same shape, for the Groth16
  settlement verifier on Solana devnet and a CosmWasm testnet.
- `docs/ops/VK-CEREMONY.md` — what a verification-key rotation is and what it
  invalidates.
- `bridge/mina-zkapp/src/DreggHeadAnchor.ts` §7 `PLACEHOLDER_CUTOVER` — the
  phases P1–P5, what each is done when, and what refuses to load after P5.
- `bridge/mina-zkapp/devnet-deployment.json` — the **signature-gated**
  `DreggAttestedGate` that is live today, and its own `sourcesMovedPast` block
  saying so.
