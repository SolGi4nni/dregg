# The dregg attestation zkApp, live on Mina Devnet

*Deployment record, 2026-07-28. `docs/MINA-DREGG-ZKAPP-BRIDGE.md` mapped the Mina↔dregg bridge and
shipped a PoC that ran a bare `ZkProgram` in a scratch directory over the literals `[1,2,3,4]`. This
document records the next resolution up: a **`SmartContract` deployed to a public network**, which
consumed a recursive attestation proof in a transaction that a block producer accepted, and refused
one it did not. It states exactly what that does and — at greater length — what it does not
demonstrate.*

---

## 0. What is live

| | |
|---|---|
| **Network** | Mina **Devnet** (`https://api.minascan.io/node/devnet/v1/graphql`), chain id `29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6` |
| **zkApp address** | `B62qkiRhX1tKdkYSXRHFASHQHj1tPf5VcLzgUhqkL3kuFViX9ckcSaN` |
| **Contract** | `DreggAttestedGate` (`bridge/mina-zkapp/src/DreggPoseidonAttestation.ts`) |
| **zkApp VK hash** | `18259224799046289794653728189970443815216123546422294759906737389909903001257` |
| **Inner attestation VK hash** | `15990086229449428195652199478086393224646730752932942884262475971185394292035` (`DreggMembershipAttestation`, depth 32 — **unchanged** across both deployments) |
| **Relay** | `B62qnViwxRUH8HrqyPzQnoWQMMqGcUGXjESLP45Bh4JigF1ZYaX1cJw` — the only key `setDreggRoot` accepts (§1), held on chain in `app_state_2/3` |
| **Attested root** | `0x388feba5822b4d3f66ed14bda2bd72898cf9ca83ad05d826a6b42bdbf9966460` (emitted by the dregg-side Rust hasher — §2) |
| **Attested leaf** | `a8935dca69b63466e6e517173f1f5d4385631802`, this repository's commit |
| **Deployer** | `B62qqqmJk56HN9YJmV9hAFZQRuYshGTjr26mbzZY7dbPN4iHynUfDs7` (faucet-funded; unchanged, and no new funds were needed for the redeploy) |
| **Deploy tx** | `5Juneee81a8yUBoRBu4gyRa32asVfXcLK6D7TdvQ2LK63j1qqT5g` — block 539534, applied |
| **Anchor-root tx** | `5Ju4a1gSFhJubAXVgUziNPmG4YwHDzNWWeMBdScPUCfW6baid3Bg` — block 539535, applied. It carries an in-circuit Schnorr check against the key in `app_state_2/3`. ⚑ That check is a **PLACEHOLDER**, not the anchor's authorization design — see §1.1. This transaction PREDATES the proof obligation `setDreggRoot` now carries, so the deployed contract at the address above is the SIGNATURE-ONLY shape; re-deploying is a VK rotation and has not been done |
| **ACCEPT tx** (honest witness) | `5Ju3uMFNRK4Xa7HxUyt7WARbepMoGQZNjUujZjavt4pERe1Bg57Q` — block 539536, **applied** |
| root advance (placeholder-signed) | `5JtgZYmZmHzu3UgTzJPcD3a4Hy7m8mB34UsCoGC3iagEUk2C3E9u` — block 539537, applied |
| **REJECT tx** (replayed witness) | `5Jv7MRgqHfb7VtoCcReZZ3g5ayJnbFBEJfjfprTQwwc4Qot7xFoK` — block 539538, **included and failed**, `Account_app_state_0_precondition_unsatisfied` |
| **CONTROL tx** (§3, R2b) | `5JuhgtwrsA4uW7YuyYFvuVEAYGwU7Ldj7qTujTkuspw9TsuLeRxV` — block 539540, **applied**. The *identical proof bytes* the daemon had refused minutes earlier on a different account update |

**Superseded — the same contract without an authorisation check.**
`B62qo54w6YftnPHCXTrcEYDcKYwg8CCeW5wiTsW9x8Tp1Hm5BS5xCeD`, deployed at `7af1883f2` earlier the same
day, VK hash `5302519670984547173190284200080041659426793795939996099701086393384665512020`. Its
`setDreggRoot` took no authorisation while its comment claimed one (§1), and fixing that moved the
zkApp's verification key — so the address stopped corresponding to the sources and was replaced
rather than left to drift. It is a throwaway and remains on chain; its accept/reject record is §3,
and it is the R1 evidence, because `actOnAttestedLeaf` is byte-identical between the two versions.

| Its record | Tx | Block | Verdict |
|---|---|---|---|
| deploy | `5JuBT6fJuX4ciV3Nfn831Mqujfhi7VioT2ioSerhiPwR7dbedb5t` | 539517 | applied |
| anchor | `5JtrbadxW6nhomfWBCTfBMKkkC8mWqn6jdyfKk9k2tvMNBqEErsp` | 539518 | applied |
| **ACCEPT** (honest witness) | `5JubGa2yehQGS7TgWT9ifCV2HmPFQ9Ew9pgK3KnQKuPdLKKuKT8A` | 539520 | **applied** |
| root advance | `5JtdG1EL7jpXtHPiffsZcbHd2eQVeTLkGi4SC3BYrfTa7NJPyVC9` | 539521 | applied |
| **REJECT** (replayed witness) | `5JtmftP3JSfYTWrAQSCU1oXZ6BsDo8WdcyqtbiX9bjhBgfr3FXHj` | 539522 | **included and failed** — `Account_app_state_0_precondition_unsatisfied` |

⚑ **Devnet only, throwaway keys, faucet funds.** Nothing here holds value and no existing dregg key
material was reused. The private keys live at `~/.config/dregg-mina/devnet-keys.json` (0600, outside
the repository); the repository holds public addresses only. This deployment has **not** been
published or announced anywhere.

---

## 1. What the contract actually checks

`DreggAttestedGate` holds four field slots of state — `dreggRoot` (the anchored dregg-side root, and
deliberately `app_state_0`), `lastAttestedLeaf`, and a `placeholderRelay` **public key** (two
slots) — and exposes two methods:

- `setDreggRoot(anchor, placeholderAuth)` — anchors a root under **two conditions of different
  kinds**:
  1. **A PROOF OBLIGATION.** `anchor` must be a verifying proof of `DreggAnchorStatement`, and the
     anchored root **is that proof's public input** — so there is no way to write a value the proof
     does not claim. The statement: the anchored Pasta root is a Mina-Poseidon Merkle root whose
     **slot 0** holds `Poseidon(R_bb)` for a BabyBear-Poseidon2 MMCS root `R_bb` the prover
     exhibited an opening of, under the DEPLOYED `TruncatedPermutation<Perm,2,8,16>`. Slot 0 is
     structural — the circuit folds LEFT at every level, so the position is not witnessed.
  2. **A PLACEHOLDER SIGNATURE.** `placeholderAuth` must be a Schnorr signature by
     `placeholderRelay` over `[oldRoot, newRoot]`, checked in circuit.
- `actOnAttestedLeaf(proof)` — takes a **recursive proof** from `DreggMembershipAttestation`,
  `.verify()`s it, asserts `proof.publicInput == this.dreggRoot.getAndRequireEquals()`, and records
  `proof.publicOutput` as the attested leaf.

### 1.1 ⚑ The relay key is a STOPGAP. It is not the anchor's design, and this document previously said otherwise.

The history, so it is not repeated. The FIRST version took `setDreggRoot(newRoot)` with an empty
body and a comment reading "relay-authorized" — open to everyone, since producing a proof of an
unconditional method is what any caller can do. The SECOND version closed that with an **in-circuit
Schnorr signature by a relay key held in state**, and this document recorded it as
"the anchor is authenticated" and "a real trust boundary". **That framing was wrong for this
project.** dregg's thesis is proof-as-capability: `chain/contracts/DreggPeerRegistry.sol` accepts a
peer root because a finality proof verified — no owner, no committee. An anchor accepted because
**one key signed it** is an oracle bridge wearing a zkApp, and calling it the fix let a trusted key
stand as an achievement.

What is true as of 2026-07-28:

- The anchor now carries a **real proof obligation** (condition 1 above), and the anchored value is
  the proof's public input rather than a free parameter. That narrows the anchor from "any field
  element" to "a commitment somebody built and can open" — Poseidon preimage resistance forbids
  working backwards from a chosen anchor.
- **The obligation does not authorize.** It says nothing about dregg's state, no dregg turn, no
  dregg proof, no legal transition. **Anyone can build a Merkle tree.**
- **The placeholder key is still the only thing making the anchor unforgeable.** It is named
  `placeholderRelay` / `placeholderAuth` in the source, the word "authorization" is not applied to
  it, and it is scheduled for deletion by the FRI verifier — not by a better signature scheme.
  Deleting it today would make the anchor world-writable, which is a strict weakening.
- **The honest distance is measured, not guessed.** `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.9–3.10:
  a depth-22 Merkle opening is **58,971 Kimchi rows** (more than one Pickles step's usable rows),
  and **one** FRI query at the deployed knobs is **684,726 rows** — 13–15 steps. Nineteen queries is
  237–272 steps for the query walk alone, before the DEEP quotient, the AIR evaluation or the
  challenger. That is the size of the thing this key is standing in for.

What condition 2 does **not** prevent, said here rather than implied away: a signature for
`oldRoot -> newRoot` becomes usable again if the anchored root ever returns to `oldRoot`. Roots here
are fresh Poseidon images, so that is not reachable in practice; the contract does not itself forbid
it.

`DreggMembershipAttestation` is the inner `ZkProgram`. Its public input is the dregg-side root; its
private inputs are a leaf and a 32-level Poseidon-Merkle authentication path; its public output is
the opened leaf. In circuit it folds the path with `Poseidon.hash([left, right])` — the Kimchi-native
Mina-Poseidon gate — and asserts the fold equals the public root. **497 rows** for the fold; the
zkApp method that recursively verifies it is **340 rows**.

So the deployed object checks, in zero knowledge: *"I know a leaf and a path that Poseidon-fold to
the root this contract anchors."*

---

## 2. The root is emitted by the dregg side, and it is fresh

This is the part that changed relative to the PoC, and it is the part worth scrutinising.

The PoC's attested root was `RUST_MERKLE_ROOT_1234`, a committed fixture — and, as
`bridge/mina-zkapp/src/rust-gold-vectors.ts` says in its own provenance note, those vectors were
**generated by o1js and pasted into the Rust probe**. Verifying a constant that the verifying side
produced is not a cross-implementation result.

The deployed root is produced the other way round. `npm run devnet:emit-root`:

1. builds four leaves that **cannot have been precomputed** — a domain tag, the emitting tree's git
   `HEAD`, a millisecond timestamp, and a 128-bit random nonce;
2. shells out to the **dregg-side Rust hasher**
   (`circuit-prove/sketches/mina-pasta-hash-probe`, `mina-poseidon` over Pasta Fp, the sponge Kimchi
   itself uses) with the new `merkle <depth> <leafIndex> <leaf...>` subcommand, which emits the
   depth-32 sparse authentication path and its root;
3. **refuses to continue** unless o1js independently reproduces the root *and all 32 siblings*
   elementwise, and unless the emitted path folds to the emitted root.

Rust/arkworks and o1js's OCaml-compiled-to-WASM sponge are independent implementations, so step 3 is
a real cross-implementation agreement over data neither side had seen before. The exact emitted
object is committed at `bridge/mina-zkapp/devnet-root.json`.

The attested leaf is the git commit `a8935dca69b63466e6e517173f1f5d4385631802` — so the live zkApp
records, on a public chain, a proof that that commit is a member of a tree whose root the dregg-side
hasher emitted. (The superseded deployment attested `0e66ea63c79f63981c39b1cb18946456f35b5936` the
same way, under a different root.)

**⚑ These leaves are not dregg cell state.** Nothing in dregg emits a Mina-Poseidon root over real
state today; see §5.

---

## 3. The accept, and the reject — and where a zkApp actually refuses things

A deploy that only ever sees the happy path proves nothing, so both polarities were exercised on
chain. But the mechanism deserves precision, because the obvious description of it is wrong.

**In a zkApp, a tampered witness is not "rejected by the chain". It is UNPROVABLE.**
`current.assertEquals(dreggRoot)` makes the constraint system unsatisfiable, so no proof exists and
no transaction can be built at all. That refusal is real, and it is the one doing the cryptographic
work — but it happens in the prover, on the submitter's machine, and it leaves no transaction hash.

What the *chain* checks is exactly two things, and only these can produce a rejected transaction:

| | Refusal | Where it happens | Leaves a hash? |
|---|---|---|---|
| **R1** | the account-state **precondition** — `getAndRequireEquals()` commits the transaction to the root it was proved against | at inclusion, in a block | **yes** |
| **R2** | the **proof itself** | at the daemon, before a block | no — never enters one |
| **R3** | an unsatisfiable **witness** | in the prover, locally | no — no transaction exists |

So the on-chain rejection is staged as a **stale attestation**, which is a real scenario rather than
a contrived one: roots advance, and an attestation against a retired root must not still spend.

| Step | Tx | Block | Daemon verdict |
|---|---|---|---|
| **ACCEPT** — the honest depth-32 attestation | `5Ju3uMFNRK4Xa7HxUyt7WARbepMoGQZNjUujZjavt4pERe1Bg57Q` | 539536 | **APPLIED** |
| the relay advances the anchored root | `5JtgZYmZmHzu3UgTzJPcD3a4Hy7m8mB34UsCoGC3iagEUk2C3E9u` | 539537 | **APPLIED** |
| **REJECT** — the *same* attestation, replayed | `5Jv7MRgqHfb7VtoCcReZZ3g5ayJnbFBEJfjfprTQwwc4Qot7xFoK` | 539538 | **INCLUDED AND FAILED** — `accountUpdate[1]: Account_app_state_0_precondition_unsatisfied` |

(The superseded deployment produced the same three rows in blocks 539520–539522; §0 records them.
This is a re-run against the current address, not a citation of the old one.)

The accept made `lastAttestedLeaf` the attested leaf. The reject was built and proved **before** the
root advanced, so the transaction exists and carries a precondition pinning the **old** root;
submitted after the advance, it entered a block, consumed its fee, bumped the nonce, and **its
effects did not apply**.

⚑ **That last cell is the network's own word, not our inference.** `app_state_0` is `dreggRoot` —
the daemon is saying, in its own vocabulary, that it refused the transaction because the root the
attestation was bound to is not the root the contract holds. Read it back at any time with
`npm run devnet:tx-status -- <hash>`; "the state did not change" would only have been circumstantial.

That the account update carries this precondition at all was not assumed either — it was confirmed
before deployment by inspecting a built transaction, which pins the anchored root in state slot 0.

**R3 was re-checked against the live artifacts** (a tampered sibling could not be proved), and
`npm run gate` checks both R3 polarities at depth 2 against the gold root on every run.

### R2: parse-refusal is not verification-refusal, and the difference is now shown

The first deployment's only proof probe flipped a character in the transaction's serialised proof and
got `Invalid rich scalar: Proof KChzdGF0…`. That is a **parse** error: the corruption broke the
proof's *encoding*, so the daemon refused it before any cryptography ran. It shows a malformed proof
does not get through, and nothing whatsoever about verification. The write-up said so, and this is
the repair. The probe is kept, as R2a below, precisely as the contrast case — re-run here, same
answer.

The honest experiment keeps the proof **well-formed** and varies only the **statement**. Two valid
`setDreggRoot` transactions are built and proved, and the proof of one is moved onto the account
update of the other. That splice is legitimate rather than a trick: Mina's transaction commitment
covers account-update **bodies**, not authorisations, so the fee-payer signature stays valid and every
byte of the proof is a proof the prover itself produced. Nothing can refuse it except the verification
equation. Then the **same bytes** are submitted on their own account update, and are accepted.
Rejected then accepted, one variable changed, and the variable is the statement.

**On chain, this deployment, `npm run devnet:attest`:**

| | What was submitted | What came back | Refused at |
|---|---|---|---|
| **R2a** | the proof with one character flipped | `Invalid rich scalar: Proof KChzdGF0…` | **decode** |
| **R2b** | a valid, untouched proof on a **different** account update | `Invalid_proof` — but you do not see that string; read the ⚑ below | **verification** |
| **control** | the *identical bytes* on their own account update | applied, block **539540** | — |

Neither refusal entered a block: both were refused at admission, so neither has a hash. The control
does — `5JuhgtwrsA4uW7YuyYFvuVEAYGwU7Ldj7qTujTkuspw9TsuLeRxV`.

⚑ **What R2b's verdict is called, and what it is.** The message that actually reaches an operator is
*"Couldn't send zkApp command: Stale verification key detected. Please make sure that deployed
verification key reflects latest zkApp changes."* That is **o1js's rewrite, not the network's word**:
`node_modules/o1js/dist/node/lib/mina/v1/errors.js` carries a replacement rule mapping
`(invalid (Invalid_proof "In progress"))` onto that sentence. `Invalid_proof` is the daemon saying
*this proof does not verify*; the stale-key phrasing is a guess at why, and here it is wrong — the
verification key is current, which the control transaction settles by being **accepted against the
same key, on the same account, with the same proof bytes, four blocks later**. The receipt records
the classification and whose wording it is, because a proof-verification failure that reads as an
operator's deployment mistake is exactly how this kind of result gets miscounted.

`npm run gate` runs the same experiment offline on every invocation, at two levels, and requires
both — so this does not depend on devnet being up:

| Level | Submitted | Result |
|---|---|---|
| `ZkProgram` proof | untouched, round-tripped through JSON | **verifies** |
| | same bytes, public input replaced by a foreign root | **parses, then FAILS VERIFICATION** |
| | encoding damaged | **does not parse** (`Sexplib.Sexp.of_string: incomplete S-expression`) |
| account update, local chain | a valid proof moved onto a different account update | **`Invalid proof for account update`** |
| | the identical bytes on their own account update | **applied** (the control) |

Each of those can go red: the `--self-test` makes the spliced statement equal to the honest one and
the gate refuses to report a result, because an experiment that has stopped varying anything is not
an experiment.

⚑ **Said exactly.** What this shows is that the verifier does not accept a proof whose prover had no
witness for the statement it is attached to — soundness in the direction that matters. It does **not**
show that no such witness *exists*: that would be a claim about Poseidon preimages, and nothing here
proves one. "A proof of a false statement" in the soundness-game sense is demonstrated; "false" in the
sense of provably unsatisfiable is not, and cannot be by this method.

---

## 4. Reproducing it

Toolchain, pinned and load-bearing:

| | |
|---|---|
| **o1js** | `2.15.0` (exact, no caret — `package.json`; the gate fails if the resolved tree disagrees) |
| **Node** | `v26.4.0` (floor: v20; o1js 1.9.1's prover bindings abort during `compile()` on Node ≥ 26, which is why the pin moved) |
| **Rust probe** | `mina-poseidon` / `mina-curves` from o1-labs `proof-systems` rev `36a8b510` |

```sh
# 0. The offline gate, all three legs, plus the fault injections that prove each
#    can go red. No network. This is the `local-gates.sh` row and the `ci.yml`
#    job; run it rather than the individual npm targets.
bash scripts/check-mina-attestation.sh
bash scripts/check-mina-attestation.sh --self-test

cd bridge/mina-zkapp
npm ci

# 1. Mint throwaway devnet keys (~/.config/dregg-mina/devnet-keys.json: deployer,
#    zkApp and RELAY keypairs) and fund the deployer from the faucet. A key file
#    predating the relay-authorized `setDreggRoot` refuses to load rather than
#    being reinterpreted — move it aside and re-mint.
npm run devnet:fund

# 2. Emit a FRESH dregg-side root and cross-check it against o1js.
npm run devnet:emit-root

# 3. Deploy the zkApp and anchor the root.
npm run devnet:deploy

# 4. Exercise it: honest attestation ACCEPTS, stale attestation is REFUSED.
npm run devnet:attest
```

Steps 1–4 write `devnet-root.json`, `devnet-deployment.json` and
`devnet-attestation-receipt.json` — all public data, all committed.

**On the faucet.** It gates on a ZK sum-to-100 captcha; a hand-rolled `POST` to
`/api/v1/faucet` returns `challenge-required` forever, so funding must go through `Mina.faucet`
(o1js ≥ 2.15), which fetches the challenge, compiles the tiny circuit, proves, and submits. The
budget is **5/hour and 10/day per IP**, and *probing the endpoint to discover this burns the same
budget* — this deployment lost an hour to exactly that.

**On block times, and why the scripts are idempotent.** Devnet blocks land every few minutes and the
attest run takes ~15 minutes end to end, so these scripts *will* be killed mid-flight. `devnet:deploy`
therefore skips the deploy when the address already carries a zkApp and skips the anchor when the root
is already anchored. That happened during this deployment: the run that sent the deploy and anchor
transactions was killed while polling for inclusion, both transactions landed anyway, and the rerun
correctly took the skip path — so it recorded `null` for hashes it had not itself sent. **The two
hashes in §0 were recovered from the chain** by scanning `bestChain` for zkapp commands with this
deployer as fee payer, and `devnet-deployment.json` says so in its `hashProvenance` field rather than
presenting them as its own. Anyone can re-check them with `devnet:tx-status`.

Note also that re-sending at the same fee gets `Insufficient_replace_fee` when the earlier attempt is
still pending — that is the mempool refusing a same-fee replacement, not a failure. Wait rather than
raise the fee.

**Safety rails.** `assertDevnet()` refuses any endpoint whose URL does not say `devnet`, so these
scripts cannot be pointed at mainnet by changing one variable.

---

## 5. What this demonstrates — and what it does not

**It does demonstrate, on a public network:**

- A Mina zkApp with a **verification key committed on chain** that consumes a **real recursive
  Pickles proof** and gates its state transition on it.
- That the proof's binding to the contract's anchored root is **enforced by the network**, in the
  network's own words: the replayed attestation entered block 539538 and the daemon recorded
  `Account_app_state_0_precondition_unsatisfied` against it. Both polarities are on chain, in
  consecutive blocks, from the same proof.
- That the anchor is **authorised by a condition the circuit asserts** — the two root anchors in
  blocks 539535 and 539537 each carry an in-circuit Schnorr check against the relay key held in
  `app_state_2/3`, so neither transaction could have been built without that key.
- That a **well-formed proof of a statement its prover had no witness for is refused by the daemon's
  verifier**, with the identical proof bytes accepted on their own account update four blocks later
  as the control (§3, R2b).
- **Bit-for-bit agreement** between two independent Mina-Poseidon implementations (Rust/arkworks
  `mina-poseidon` and o1js's WASM sponge) over a root and 32 siblings that neither had seen before,
  with the **Rust side emitting** and the Mina side verifying.

**It does not demonstrate — and no wording here should be read to suggest — any of the following:**

1. **Mina did not verify a dregg proof.** It verified a dregg **commitment**. The attested object is
   a Poseidon-Merkle root, not a STARK. This is the same boundary
   `MINA-DREGG-ZKAPP-BRIDGE.md` §6.1 draws, unchanged by deployment.
   - Verifying dregg's real proof — a **gnark Groth16 on BN254** — inside Kimchi is **infeasible**:
     Kimchi has no pairing gate and emulating one blows past the 2^16-row step ceiling.
   - Verifying dregg's **inner FRI-STARK** directly is *feasible-but-huge*: **~2.2 × 10^7 Kimchi
     rows ⇒ ~500–800 chained Pickles step circuits** at deployed parameters, ~250–350 after the
     dregg-side FRI knobs, with a floor near ~200 (`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md`). The cost
     driver is the `mod p` reduction of a 31-bit BabyBear prime inside a 255-bit Pasta field, not
     the hash. Nothing here reduces that number.
2. **The attested leaves are not dregg state.** They are a domain tag, a git commit, a timestamp and
   a nonce. Nothing in dregg emits a Mina-Poseidon root over live cell state, so the root is a
   **re-commitment computed in plain Rust, outside any STARK**. Whoever computes it is trusted for
   that hash.
3. **The root anchor carries a PROOF OBLIGATION, and is still gated on a PLACEHOLDER KEY.**
   `setDreggRoot` writes the anchor proof's public input, and that proof pins the anchored tree's
   slot 0 to `Poseidon(R_bb)` for a BabyBear-Poseidon2 MMCS root with a known opening (§1). So the
   anchored value is no longer an arbitrary field element. **But the obligation is a shape
   constraint, not a claim about dregg** — anyone can build a Merkle tree — and the
   `placeholderRelay` key remains the only thing that makes the anchor unforgeable. Nothing on
   chain checks that the root corresponds to anything in dregg. ⚑ **This document used to call the
   signature "authentication" and a "real trust boundary"; §1.1 retracts that framing.** The key is
   a stopgap for a FRI verify whose cost is now measured (`MINA-VERIFIES-DREGG-FRI-SIZE.md`
   §3.9–3.10), not an authorization design.
4. **The chain did not catch a forged Merkle path.** The prover caught it first (§3). Only the
   precondition failure is an on-chain refusal.
5. **Proof-verification refusal IS demonstrated on chain now — state precisely against what.** §3's
   R2b sent a well-formed, fully-decoding proof on an account update it was not proved for; the
   devnet daemon answered `Invalid_proof`, and the identical bytes were then accepted on their own
   account update in block 539540. That replaces the earlier attempt, which corrupted the *encoding*
   and so was refused at parsing before any cryptography ran, and which this document previously
   listed here as a thing believed rather than shown. What is still **not** shown is that the
   rejected statement is *unsatisfiable*: no witness is known for it, which is what soundness is
   about, but proving none exists is a Poseidon preimage claim and nothing here proves one.
6. **The mutual bridge is still asymmetric.** Direction 1 (dregg verifies a real Kimchi proof, in
   Lean, modulo three named crypto carriers) remains the strong half. This deployment strengthens
   direction 2 from "a `ZkProgram` ran off-pin in a scratch directory over `[1,2,3,4]`" to "a
   deployed zkApp on a public network consumed a recursive attestation over a freshly Rust-emitted
   root" — which is a real step, and still a **commitment attestation, not a proof check**.

The honest one-line summary: **a Mina zkApp is live and provably gates on a dregg-emitted Poseidon
commitment; it does not verify a dregg proof, and the route that would is priced at several hundred
step circuits.**

---

## 6. What breaks, and what re-emits

- Changing `DreggPoseidonAttestation.ts` in any way that alters the constraint system changes the
  zkApp's **verification key**, so the deployed address no longer corresponds to the sources. There
  is no migration: deploy a new address and update this document. The old address is a throwaway.
  **This has now happened once, which is why §0 has a superseded row** — adding the relay
  authorisation to `setDreggRoot` moved the zkApp VK from `530251967…` to `182592247…`, so the
  address deployed at `7af1883f2` was retired the same day and a new one deployed. Note what did
  *not* move: `DreggMembershipAttestation` was untouched, so the **inner** attestation VK hash is
  identical across both deployments. Only the contract that consumes it changed.
- Changing `ATTEST_DEPTH` changes the inner VK, hence the outer VK, hence the address's meaning.
- The devnet key file (`~/.config/dregg-mina/devnet-keys.json`) gained `relayPrivate`/`relayPublic`
  at the same time, and a file lacking them now **refuses to load** with the recovery step named,
  rather than being reinterpreted into an unsatisfiable circuit ten minutes later.
- `devnet-root.json` is reproducible from its own `leaves` field by re-running the probe; the
  timestamp and nonce make it non-regenerable from scratch, which is the point.
- The devnet is wiped periodically by the Mina foundation. When it is, this address stops existing
  and the reproduction steps above are the recovery path — they are one command each.

## 7. Coverage

`scripts/check-mina-attestation.sh` (a `local-gates.sh` row and a `ci.yml` job, both with a
`--self-test` that proves the gate can go red) covers everything offline, in **three legs**:

| Leg | What runs | Needs |
|---|---|---|
| 1 | `attestation-gate.ts`: the KATs, the in-circuit path, a real Pickles compile/prove/verify, the tamper refusals, the zkApp composition on a local chain, the **relay-authorisation polarities** (§1) and the **parse-vs-verify experiment** (§3) | node ≥ 20, o1js 2.15.0 |
| 2 | `poseidon2-babybear-rows.ts`: the Poseidon2-w16-BabyBear rows/perm ratchet | node |
| 3 | `probe-gate.ts`: `cargo test --locked` in the dregg-side probe crate, then its `merkle` subcommand end to end on unprecomputable leaves, cross-checked against o1js elementwise | node, **cargo**, git |

**Leg 3 is new, and the reason it is new is this document's own §7 from the first deployment**, which
recorded that the gate was "deliberately Node-only" and that the probe's tests therefore did not run.
That reads like a scoping decision; what it actually meant is that the half of the bridge which
*produces* the attested root ran in no gate at all. The probe crate is its own workspace
(`[workspace]` in its `Cargo.toml`), so no cargo job in the repo reached it either, and the `merkle`
subcommand that emits the deployed root ran only inside `npm run devnet:emit-root` — which needs
devnet keys and is deliberately ungated. **A missing `cargo` is now a gate failure, not a skip.**

The `--self-test` injects **thirteen** faults into scratch copies of both the TypeScript and the Rust
crate — never the shared tree — and requires each to turn the gate red; all thirteen do. One is
chosen to separate the instruments: bending the root that the `merkle` subcommand *prints* leaves
every `cargo test` passing and is caught only by the elementwise cross-check. Nothing in the crate
covers its own emit path, which is the gap leg 3 exists to close.

The devnet scripts are **not** gated and must not be: they need network, faucet budget and real
block times. This document is their record.
