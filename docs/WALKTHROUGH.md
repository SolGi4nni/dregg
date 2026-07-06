# Walkthrough — driving a locally-hosted dregg, for real

This is not a scripted movie. It is a step-by-step of **real operations you run
against a genuinely-usable local instance**: you stand up a node in-process, rent
and drive a confined agent grain, watch its actions land as committed kernel turns
on a real receipt log, re-verify them yourself trusting no host, and mint conserved
USD-credit from an audited DECO/zkTLS payment attestation.

Everything below runs from a clean checkout on `localhost`. Where a step is a
*deploy* (a homelab federation node) or needs a *key* (a live model), it is labelled
as such — those beats are named honestly, not faked.

Run the whole thing in one shot:

```bash
bash dregg-agent/demo/grain-local.sh
```

That script is just the two runnable examples below, narrated. Read on to run each
step by hand and understand what it proves.

---

## Step 1+2 — rent, drive, and self-verify a local-hosted grain

```bash
cargo run -p agent-platform --example grain_local_e2e
```

Source: [`agent-platform/examples/grain_local_e2e.rs`](../agent-platform/examples/grain_local_e2e.rs)

What it does, in order:

1. **Node.** Stands up the built-in local node — a real in-process ledger with a
   finalized, light-client-verifiable receipt log. No external daemon required.
2. **Rent.** Rents a confined agent grain (`caps=fs`, a budget, a workdir under a
   real temp dir). Confinement is lexical: a raw `shell` cap is refused; fs grants
   resolve against the grain's own rented workdir.
3. **Drive.** Runs the *served* drive path (`drive_serving`), which welds every
   admitted action to a genuine committed kernel turn and lands the committed
   receipt on the node's finalized log. Three fs operations become three turns.
4. **Verify — trusting no host.** Three independent checks a renter can run:
   - **R0** — the receipt chain re-witnesses: signed, unbroken, within budget.
   - **R2** — every receipt is a *view* over a kernel turn the minter actually
     committed (`verify_r2`, reporting linked-turn count).
   - **LANDED** — `verify_landed` runs the node's own `verify_receipt_chain` (the
     light-client verify) and asserts every manifest turn is present on the
     finalized log. `finalized_len == manifest_len` or it fails.
5. **Attest.** Exports the renter's re-verifiable attestation artifact (bytes you
   can hand a third party to re-witness offline).

Expected tail:

```
[LAND ] turns landed on the local node: finalized_len=3 manifest_len=3
== GREEN: a real local node committed the grain's turns; a renter re-verified
   them (R0 + R2 + landed) trusting no host. ==
```

### What is local-real vs. what is a deploy

- **Local-single-node is real.** The node here is in-process, but it is a real
  executor with a real finalized receipt chain — the half a single node runs. The
  light-client re-verification is genuine.
- **Multi-node blocklace finality is a deploy step, not operated here.** Point the
  platform at an external federation node with:
  ```bash
  DREGG_NODE_URL=http://<homelab>:8421 cargo run -p agent-platform --example grain_local_e2e
  ```
  The turns still mint + verify on the local node; the HTTP forward to that node's
  ingress is the operational deploy step. That node is your homelab, not something
  this example spins up.
- **Whole-history R3.** Proving the turns *ran* under a whole-chain STARK is the
  remaining leg (`grain_verify::WHOLE_HISTORY_GAP`); R0/R2/landed above do not
  claim it.

---

## Step 3 — earn: the audited DECO/zkTLS money-in

```bash
cargo run -p dregg-bridge --example deco_money_in --features test-utils
```

Source: [`bridge/examples/deco_money_in.rs`](../bridge/examples/deco_money_in.rs)

This exercises the trustless Stripe money-in: mint dregg USD-credit **only** against
an attestation that a settled Stripe payment occurred, and let you re-verify the
binding by hand. In order:

1. **Attestation.** Decomposes the disclosed facts (payment intent, amount,
   currency, recipient) to a committed felt identity via the one canonical encoder
   the in-AIR DECO leaf recomputes.
2. **Verify.** The production entry (`verify_money_in`) dispatches to the DECO path:
   gate-5 range check, felt-commitment binding, currency/bounds, consume-once
   nullifier (the double-mint gate).
3. **Mint.** `mint_against_deco` records the verified backing and draws a conserved
   `Effect::Mint`, so `live_supply <= total_verified_payments` bites.
4. **Self-verify.** You recompute the canonical felt over the disclosed facts
   through the *same* encoder the executor, the deployed producer, and the in-AIR
   leaf all use, and check it matches the mint. A forged-facts attestation cannot
   reproduce it.
5. **Anti-vacuity tooth.** A forged attestation (amount bumped after the identity
   was committed) is refused with `DecoCommitmentMismatch` — no mint. This is why
   step 4's recompute is meaningful, not vacuous.

### Honest label — the `test-utils` feature is compiler-enforced honesty

The example carries a **test-mode fixture attestation** (`zk_tls_proof: None`), so it
must be built with `--features test-utils`. That is not convenience: a production
build (`DECO_REQUIRES_STARK_PROOF = cfg!(not(any(test, feature = "test-utils")))`)
refuses a `None`-carrier attestation with `DecoProofMissing`. This run proves the
**verification teeth** (range + felt-commitment binding + conserved mint) over a
fixture; it does **not** claim a live Stripe session occurred. The live prover that
turns a real Stripe TLS session into a genuine DECO leaf STARK lives in the
`dregg-deco-prove` crate (`prove_stripe_deco`, MPC-TLS/notary capture).

---

## Going further — the real daemon, a live brain, a physical jail

These extend the walkthrough beyond the two examples. Each is labelled by what it
actually needs.

### The real node daemon + faucet + CLI

```bash
scripts/run-node-10min.sh
```

From a fresh checkout to a running, health-checked `dregg-node` in ~10 minutes: it
links the verified Lean executor via the seed release artifact when one is fetchable
(else a marshal-only build, on purpose), starts the node with the faucet on, and
curls `/status` + a faucet round-trip to prove a real turn lands. It reports whether
the running node is `state_producer:lean` (verified) or marshal-only. This is the
real node the `DREGG_NODE_URL` deploy step above points at.

### Drive the grain with a LIVE model (needs a key)

The recorded brain (`PlannedBrain`) is the honest default and keeps the platform
hermetic. To have a real model reason → act → observe over the grain — with every
model tool-call crossing the same cap-gate before it becomes a receipt — build with
the `live-brain` feature and provide a key in the environment:

```bash
# BYO key. Recognized: DREGG_LLM_API_KEY / ANTHROPIC_API_KEY / OPENAI_API_KEY / NVIDIA_API_KEY
export DREGG_LLM_API_KEY=sk-...
# Optional: point at any OpenAI-compatible endpoint + model.
#   NVIDIA Nemotron:  DREGG_LLM_BASE=https://integrate.api.nvidia.com  DREGG_LLM_MODEL=<nemotron-model>
export DREGG_LLM_BASE=https://api.openai.com        # default
export DREGG_LLM_MODEL=gpt-4o-mini                  # default
cargo run -p agent-platform --features live-brain --example grain_local_e2e
```

Off-by-default is deliberate: no key, no network, fully reproducible. The live path
(`drive_live`) wires dregg-agent's OpenAI-compatible HTTP transport as the session's
brain; the cap-gate and receipting are identical to the recorded path.

### The physically-jailed brain — "dregg is the host" (macOS today)

```bash
cd deos-hermes && cargo test --test dregg_hosts_the_agent
```

Proves the polarity inversion by *running*, not by compiling: the agent is jailed
inside a dregg PD; dregg's tools are its only effective effect-path (a cap-gated,
receipted turn on the verified executor); the base-tool escape (unconfined shell,
host-FS read, arbitrary socket) is neutralized at the OS level; and egress is a
structured, cap-gated, opt-in, revocable door. **macOS-confined today** — the Linux
egress-door path is a parallel lane. This is the "physically bounded" beat: the jail
is enforced by the OS, not by the agent's cooperation.

---

## What you proved

Running the two examples, all local, all real:

- a confined agent grain drove three kernel turns onto a real local node ledger;
- those turns are on the node's finalized, light-client-verifiable receipt log;
- you re-verified R0 + R2 + landed trusting no host;
- you minted conserved USD-credit from a DECO attestation and recomputed its
  commitment by hand; a forged-facts attestation was refused.

The honest edges: multi-node finality is a homelab deploy (`DREGG_NODE_URL`), a live
model needs a key + `live-brain`, the DECO run is a fixture (live prover is
`dregg-deco-prove`), whole-history R3 STARK is still a gap, and the physical jail is
macOS-only for now.
