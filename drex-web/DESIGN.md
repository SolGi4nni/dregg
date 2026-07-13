# DrEX — Dragon's EXchange · frontend/UX design

A sealed-bid, multilateral, batch-clearing exchange whose every trust claim is
graded, and whose order-signing + solvency proving runs **in the trader's own
wallet** (the Dragon's Egg Cipherclerk extension) — not on the exchange's
servers. The exchange never sees your key, and it cannot mint, over-fill, or
front-run you without breaking a Lean-proved property you can point at.

This doc is the UX + the wire. The runnable prototype that realizes it lives
beside it (`index.html` + `app.js` + `drex-wallet.mjs` + `drex-clearside.js`);
`README.md` says how to open it.

---

## 0. The one-sentence pitch

> You place a **sealed** order. Your **wallet** signs it and proves — in your
> browser, with real cryptography — that you can cover it, without revealing
> your balance or which trader you are. At batch time all orders reveal and a
> **multilateral ring matcher** clears them at once, giving you a fill that is
> **conserving, within your limits, and fair** — each of those a property with a
> machine-checked proof and an honest trust grade.

## 1. Trust grades (the vocabulary the whole UI speaks)

Every claim in DrEX carries one or more grades. Nothing is asserted ungraded.

| grade | means | example |
|---|---|---|
| **PROVED** | a Lean theorem, checked for *all* inputs | `clearing_respects_limits` (Market/Fairness.lean) |
| **ATTESTED** | produced/verified by real wallet crypto this run | the Bulletproofs solvency proof (`prove_conservation`) |
| **REPLAYABLE** | recomputed on *this* batch and shown checking | per-asset conservation on the cleared legs |
| **NOT-IN-THIS-BATCH** | proved in Lean, but this rung isn't exercised by the discrete clear-book batch | uniform-price no-arbitrage (the priced rung) |

The "why it's fair" panel is literally a table of these, each with its Lean
citation (`file · theorem`). A cofounder or whale reads the panel and sees
exactly *what* is guaranteed and *by what*.

---

## 2. The wallet flows (on the extension — Dragon's Egg Cipherclerk)

The wallet is the trust root. DrEX is a page that *asks* the wallet to do things;
the wallet decides, signs, and proves. Reused surfaces from the shipped
extension:

### 2a. Place order → confirm-intent (anti-blind-sign)
The exchange page calls `window.dregg` / posts a `dregg:intentConfirmation`. The
cipherclerk pops the **confirm-intent card** (`extension/confirm-intent.html`),
nonce-bound, rendering the order in human terms:

> **Sign order · Dragon's Egg Cipherclerk**
> sell **10 GOLD**, want **≥ 4 ART**, limit **½**, **SEALED until batch T**
> `[order drex_place_order]` … the cipherclerk signs this exact order (nonce-bound) — nothing else.

The approval binds to *what was displayed* (the existing card echoes the turn id
+ domain so post-confirmation substitution is a decline). The prototype reuses
this card verbatim as a modal.

### 2b. Sign the order-turn — **REAL**
On approve, the wallet builds a real signed dregg `Turn`:
`cipherclerk_make_action_turn({ sender_privkey, method:"drex_place_order",
memo_json:<order> })` → a **real Ed25519 signature over the canonical action
bytes**, yielding a `turn_id` (canonical turn hash) + `turn_bytes`. Then
`assemble_signed_turn_envelope(turn_bytes, key)` produces the **hybrid
ed25519 + ML-DSA-65 (FIPS-204)** `SignedTurn` — the exact
`POST /api/turns/submit-signed` wire bytes (custody.ts). PQ-safe from the client.

### 2c. Prove solvency (holdings) — **REAL**
The order must be *covered*. The wallet proves it with `prove_conservation`:
statement `holdings = offer + change`, with a **Bulletproof range proof per
output** ⇒ `change ≥ 0` ⇒ `holdings ≥ offer`, and every output a non-negative
64-bit value (the negative-value / mod-wrap **inflation attack is ruled out**).
The proof is **bound to the exact order** via `message_hex = turn_id`; substitute
the order and `verify_conservation_proof` returns `valid:false`. A trader who
does *not* hold enough **cannot construct the proof** (change would be negative —
no valid u64 output). This is `prove_committed_threshold`'s intent, realized on
the engine that is actually live in this wasm build (that hand-STARK path is
retired and fails closed — see §6).

### 2d. Prove eligibility — **REAL, anonymous**
`prove_anonymous_membership(trader_id, eligible_ring)` proves the trader is in
the exchange's eligible-trader set **without revealing which member**, and emits
a **presentation tag** = the one-order-per-batch nullifier (double-submit
guard). This is the sealed-bid anonymity property.

### 2e. The scoped trading MANDATE (disclosure-picker)
For delegated / agent trading, `extension/disclosure-picker.html` attenuates a
biscuit down to a scoped mandate — *"trade up to $X in GOLD/ART until date Y,
sealed-bid only"* — a capability the trader hands to a bot or co-signer that
**cannot** exceed the scope. (Design surface; the prototype exercises the direct
single-trader path.)

### 2f. Sealed-bid commit → reveal (`SealedAuction.lean`)
- **Commit** (before batch T): publish `H(order‖salt)`; the order is hidden.
- **Reveal** (at T): publish `(order, salt)`; anyone checks the commitment binds.
The prototype implements both with SHA-256 (SubtleCrypto in-browser).

---

## 3. The web app exchange surface

Three columns, echoing the cockpit aesthetic (`starbridge-v2/web/cockpit.html`
palette: GitHub-dark, `ui-monospace`, dragon-purple accent):

- **Left — sealed batch / order book.** Resting orders shown as committed
  hashes (`H(order‖salt)`) while sealed; they flip to revealed amounts at clear
  time. Your order is highlighted. A batch clock.
- **Center — the ticket + the wallet flow.** The order form (sell/want/limit/
  holdings) and a **live flow log** that narrates each step with a badge:
  `REAL wasm` (green) vs `clear-side mirror` (orange). Each step shows the real
  artifacts it produced (turn id, envelope bytes, `valid=true`, nullifier).
- **Right — cleared batch + "why it's fair".** Your fill + everyone's
  allocations (sent/received, IR + budget checks), per-asset conservation bars,
  and the graded fairness ledger (§1) with Lean citations.

Charts: per-asset conservation bars (in = out); the flow log doubles as the
audit trail.

---

## 4. The wire (web app → extension → matcher → settlement → web app)

```
 ┌────────────┐  dregg:intentConfirmation   ┌───────────────────────────┐
 │  DrEX web  │ ─────────(order card)──────▶ │  Cipherclerk (extension)  │
 │  app.js    │                              │                           │
 │            │  ◀──approve (nonce-bound)──  │  confirm-intent.html      │
 │            │                              │                           │
 │            │  ── sign + prove request ──▶ │  dregg_wasm.js  [REAL]:   │
 │            │                              │   cipherclerk_make_action │
 │            │  ◀ turn_id, hybrid envelope, │     _turn (Ed25519)        │
 │            │    solvency proof (valid),   │   assemble_signed_turn_env │
 │            │    eligibility nullifier ──  │     (ed25519 + ML-DSA-65)  │
 │            │                              │   prove_conservation       │
 │            │                              │     (Bulletproofs+Schnorr) │
 │            │                              │   prove_anonymous_membership│
 └─────┬──────┘                              └───────────────────────────┘
       │ sealed commit  … batch T … reveal
       ▼
 ┌────────────────────────────────────────────────────────────────────┐
 │  MATCHER + SETTLEMENT   [LABELED: clear-side mirror in the proto]    │
 │   real engine = intent/src/solver.rs  (Johnson circuits + TTC ring) │
 │              + intent/src/verified_settle.rs (fold each leg through  │
 │                the Lean-proved Exec.recKExec per-asset kernel)       │
 │              + intent/examples/drex_clear_book.rs (the runnable e2e) │
 └─────┬──────────────────────────────────────────────────────────────┘
       │ cleared allocations + reject-polarity
       ▼   DrEX web app renders the fill + graded "why it's fair" panel
```

In production the browser↔extension hop is the shipped
`window.dregg` / content-script / `chrome.runtime` bridge (`extension/src/
page.ts` + `content.ts`). In the prototype the app loads the **same
`dregg_wasm.js`** directly (dev harness — same wasm, same entry points) so the
proving is real without requiring the packed extension to be installed.

---

## 5. What is REAL vs a labeled stand-in

| piece | status | how |
|---|---|---|
| Order-turn signature | **REAL** | `cipherclerk_make_action_turn` — Ed25519 over canonical action bytes |
| PQ envelope | **REAL** | `assemble_signed_turn_envelope` — hybrid ed25519 + ML-DSA-65, 11 KB wire |
| Solvency / no-inflation proof | **REAL** | `prove_conservation` + `verify_conservation_proof` → `valid:true, range_proofs_checked:true`; tamper → `valid:false` |
| Anonymous eligibility | **REAL** | `prove_anonymous_membership` → blinded tag + nullifier |
| Sealed commit/reveal | **REAL** | SHA-256 commitment, binds on reveal |
| Confirm-intent approve | **REAL surface** | the shipped card, reused verbatim, nonce-bound |
| **Matcher + settlement** | **LABELED mirror** | `drex-clearside.js` mirrors solver.rs/verified_settle.rs/drex_clear_book.rs (same ring, same conservation + limit + reject-polarity checks). Not the verified executor — that needs the B_IROOT Rust build. Every property it recomputes cites the Lean theorem that PROVES it. |

The matcher is the *only* stand-in, and it is honestly labeled everywhere it
appears (flow-log badge, panel citations, this table). The full engine already
exists and runs (`cargo run -p dregg-intent --example drex_clear_book`); the
mirror exists so the UI clears a batch without a fresh Rust toolchain build.

## 6. Honesty notes worth stating once
- The wasm is **fail-closed**: `prove_committed_threshold` in this build refuses
  ("the hand-STARK engine was retired … fail-closed"). DrEX therefore proves
  solvency on the *live* conservation engine (Bulletproofs+Schnorr), which is a
  strictly stronger statement (balance **and** per-output range) and actually
  runs. No proof is faked; if a `prove_*` can't run, the flow says so.
- `uniform_price_*` and `pool_solvent_forever` are **PROVED** in Lean but graded
  **NOT-IN-THIS-BATCH**: the discrete clear-book batch exercises rungs 1/2/4
  (ring clearing, aggregation, reject-polarity), not the priced/pool rungs.
- Demo key material is deterministic (`traderKey`); a real wallet holds the seed
  in the extension's sealed store.
