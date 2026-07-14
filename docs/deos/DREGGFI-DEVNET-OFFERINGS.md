# DreggFi Devnet Offerings — the verified mechanism family as pickable offerings

**What this is.** DreggFi is a family of verified financial mechanisms built into
one engine (`fhegg-solver`) under one soundness discipline: *every clearing carries
a certificate a buyer re-checks from scratch — verify-not-find*. The mechanisms are
BUILT (the engine + benchmarks + the `fhir` typed-product compiler prove that). This
doc turns them into **pickable offerings**: a menu where a user selects an offering
and it RUNS the real engine locally, showing the clearing, the certificate, and the
privacy tier. It states honestly, per offering, what is **built**, what is
**deployable-now** (a clickable local surface + a real run), what is **stubbed /
spec'd**, and what is **ember-gated** (public devnet broadcast, live tokens).

**Scope discipline (read first).** This is a **devnet-DEMO surface**: the real engine,
run LOCAL, each clearing showing its certificate. It is NOT a live deployment. Actual
PUBLIC devnet deployment — a hosted node, live broadcast, real value at stake — is the
**ember-gated** step (named per offering below, never performed here). No mock: every
number a card shows is the runner bin's certificate.

---

## The offerings menu (the new surface)

`drex-web/offerings.mjs` (a NEW, self-contained server on `:8790`, sibling to the
ring-DrEX `serve.mjs` on `:8781`) serves `offerings.html` and runs the real engine per
offering through thin JSON-CLI runner bins:

```
node drex-web/offerings.mjs            → http://localhost:8790
  GET  /offerings                       → the menu manifest (stage per offering)
  POST /offering/derivatives            → pricecert_clear  (Price-Cert: European + American)
  POST /offering/package                → package_clear     (all-or-none combinatorial clearing)
  POST /offering/drex-shielded          → fhegg_clear       (PDHG circulation + Cert-F + AIR gate)
```

The two Price-Cert / package runners are NEW (`fhegg-solver/src/bin/pricecert_clear.rs`,
`package_clear.rs`), modeled exactly on the existing `fhegg_clear.rs` shielded-clearing
CLI: read params/orders on stdin, run the SAME library the benchmarks exercise
(`solve_price_cert` / `solve_snell_cert` / `clear_package`), emit ONLY the world-visible
certificate JSON. The ring DrEX and the launchpad are LINKED to their own surfaces
(`:8781`, `:8785`), not re-run here. Build the runners with:

```
cargo build --release -p fhegg-solver --bin pricecert_clear --bin package_clear   # in fhegg-solver/
```

---

## Stage-per-offering table

| Offering | Mechanism | Built | Deployable-now (local demo) | Stubbed / spec'd | Ember-gated |
|---|---|---|---|---|---|
| **(a) Ring / multilateral DrEX** | TTC ring match → verified_settle | ✅ `solver.rs` + `Market/*` proofs; `drex_clear` bin | ✅ `serve.mjs` :8781 (real solver + wallet + live-node settle) | shielded N-leg partial-fill | public devnet broadcast; on-chain settle |
| **(b) Derivatives desk (Price-Cert)** | state-price LP (European) + Snell LP (American) | ✅ `pricecert.rs` + `pricecert-bench` | ✅ **WIRED** `/offering/derivatives` → `pricecert_clear` (runs here) | shielded wrap (cert_f_prove) for the private tier | hosted devnet |
| **(c) Package / combinatorial auction** | all-or-none clearing + certified α=W/UB bound | ✅ `package.rs` + `package-bench` | ✅ **WIRED** `/offering/package` → `package_clear` (runs here) | shielded wrap | hosted devnet |
| **(d) Shielded batch clearing** | PDHG circulation + Cert-F + verified AIR gate | ✅ `pdhg.rs`/`cert.rs`/`air.rs` + `fhegg_clear` | ✅ **WIRED** `/offering/drex-shielded` → `fhegg_clear` (runs here) | the reveal-nothing STARK wrap is `cert_f_prove` (separate action) | hosted devnet |
| **(e) Portfolio / Fisher / CFMM** | QP portfolio + Eisenberg–Gale + CFMM routing | ✅ `qp.rs`/`fisher.rs`/`cfmm.rs` (lib + in `fhir`) | ⚠ **not wired** — engine runs, JSON-CLI runner not yet written | the one-file `portfolio_clear` sibling is the wire needed | hosted devnet |
| **(f) Anti-rug launchpad** | clearing-attested eligibility + solvent pool | ✅ 985-LOC contracts, **29/29 gate green** | ✅ `launchpad-web` :8785 (real wallet, real bytecode) | Groth16 `IClearingAttestor` (rung-1 replayable today); `x·y=k` graduation curve | mainnet money-in launch; VK-epoch flip + re-genesis |

**The `fhir` typed-product compiler** (`fhir/`, bin `fhir-demo`) sits under all of these:
15 example products, each compiling to a `(mechanism, tier, certificate)` triple, 9 running
through the real engine, 5 rejections (4 privacy over-claims + 1 arbitrage). It is the
type-checked catalogue the offerings menu presents a runnable slice of. `cargo run
--release --bin fhir-demo` (in `fhir/`) prints every product's inferred tier + cert + run.

---

## What is wired end-to-end (cited local runs)

All three wired offerings were run through the offerings server (`:8790`) — the real
`fhegg-solver` bins, no mock — and returned valid certificates:

- **Derivatives — American put** (`{"kind":"american","steps":256}`):
  certified value **6.087258** over a 33,153-node CRR Snell tree; certificate `valid:true`
  (dominates + superharmonic, both shortfalls 0); negative polarity **REJECTED** (denting
  the root value below its continuation breaks superharmonicity).
- **Derivatives — European state-price** (`{"kind":"european","scenarios":64,"instruments":16}`):
  certified price **2.416333**, duality gap ~0 (tight), `valid:true` (π≥0, Hπ=a residual
  1.3e-15, yᵀH≥h); arbitrage market (inflated bond mark) **REJECTED** (no certificate).
- **Package — sample auction**: welfare **18**, upper bound **18**, certified ratio **1.0**
  (exactly optimal), `valid:true` (integral, capacity, prices≥0, W≤UB); the accepted bundles
  are `{0}` + `{1,2}`.
- **Package — random sweep** (`{"random":{"items":20,"bids":80,"seed":1}}`): welfare
  **163.21**, upper bound **184.51**, certified ratio **0.885**, `valid:true` — a genuine
  certified near-optimality bound on an NP-hard instance.
- **Shielded batch clearing** (3-order ring DREGG↔USDC↔ETH): cleared volume **12**, the
  Cert-F AIR **ACCEPTS** the honest certificate and **REJECTS** the tampered one (broken
  conservation on edge 0). The reveal-nothing STARK wrap is the named next stage
  (`cert_f_prove`), not run in the click path.

The certificate a card shows is the bin's — `serve.mjs`/`offerings.mjs` never synthesizes it.

---

## The privacy tiers (the dial each offering rides)

Per `docs/deos/DREGGFI-PRIVACY-TIERS.md` and the `fhir` crate (`fhir/src/tier.rs`), one
exchange with a privacy dial, ordered by privacy `Dark < Shielded < Open`:

- **Tier 0 DARK** — no viewer; FHE, encrypted inputs, only the result opens. Admissible iff
  FHE-tractable. Status: **frontier** (FHE PoC; N≈32–512 orders/pair at minute cadence).
- **Tier 1 SHIELDED** — private-from-the-world, the solver sees plaintext; the world sees only
  a reveal-nothing STARK. Admissible iff STARK-tractable. Status: **building** (2-leg AIR green,
  hiding PCS built; the reveal-nothing theorem is the named research crux).
- **Tier 2 OPEN** — public, fully general. Status: **shippable now** (the ring/TTC DrEX).

**Honest note on the demos' tier.** The derivatives / package / shielded offerings RUN in the
**Open** tier here — the plaintext certificate is shown and re-checked. The `fhir` compiler
reports each product's most-private *admissible* tier (derivatives European → Dark; American →
Shielded; package → Shielded), which is the CAPABILITY, not what this demo surface displays.
The shielded batch offering shows the Cert-F in the clear and NAMES the STARK wrap that would
hide it — the same honesty `fhegg_clear` already prints.

---

## The honest devnet-deploy path

**One-step-from-devnet (real engine, needs only a hosted target):**

- The **offerings menu** (`offerings.mjs`) is a devnet-demo surface today. To host it on the
  hbox LAN/tailnet, bind it the same firewalled way `serve.mjs` documents
  (`OFFERINGS_BIND=192.168.50.39`, or `OFFERINGS_ALLOW_WILDCARD=1` only behind a default-deny
  ufw allowing LAN + tailscale0). No code change — the wildcard guard is already in place.
- The **ring DrEX** already lands a cleared batch as one real turn on a live single-node dregg
  instance (`serve.mjs` `/settle` → `/turn/submit` → effect-VM → prove_pool). Wiring the
  derivatives / package / shielded clearings to the SAME settle path (emit the clearing as a
  Transfer + EmitEvent cohort) is a small, non-gated addition — the settle machinery exists.
- The **launchpad** is forge-deploy-to-a-public-testnet + run-one-launch away; that is "not new
  work" (contracts pass the 29/29 gate against local bytecode).

**Ember-gated (ember's call, named, not performed):**

- A **public hosted devnet** (a node reachable off-box carrying real broadcast) and any launch
  **with value at stake**.
- **VK-epoch flip + re-genesis** (the launchpad mainnet path).
- **Live tokens** ($DREGG buys services, never features — per the public-surfaces posture).
- Tier-1/Tier-0 privacy *deployment* rests on the reveal-nothing theorem (research) and the FHE
  envelope (frontier); those are engine-maturity gates, not deploy buttons.

**The remaining wire (spec'd, honest):**

- **(e) Portfolio / Fisher / CFMM** — the library (`qp.rs` / `fisher.rs` / `cfmm.rs`) and the
  `fhir` products run; the click surface needs one file: a `portfolio_clear` runner bin (a
  sibling of `pricecert_clear`) reading a portfolio/market spec on stdin and emitting the
  CertQp / CertEq / CertRoute certificate JSON, plus a `/offering/portfolio` route in
  `offerings.mjs`. Same pattern, ~120 lines. Then the card flips from spec'd to deployable-now.
```
