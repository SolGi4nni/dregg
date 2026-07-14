# The Zama Eclipse — dregg vs Zama on confidential onchain finance

*An honest, cited competitive analysis. Zama is the reference product in confidential
onchain finance: FHE on an EVM, a shipped mainnet, a named token standard, live yield.
This doc grades both sides truthfully. The thesis: **dregg's technology genuinely
eclipses Zama's on depth — verified + post-quantum + fair-by-proof + no-viewer +
committee-free + dial-able — while Zama is genuinely ahead on shipping, product surface,
and standardization.** The eclipse is real on tech; the gap is real on product. Both are
stated plainly, and every ambitious edge names its grade. This is a strategy artifact and
a productization TODO, not marketing.*

Zama facts are cited to Zama's own docs / EIPs / reputable coverage; dregg facts are cited
to this repo (file, and `file:line`/theorem where load-bearing). The Zama domain migrated
`zama.ai → zama.org`; both resolve.

---

## 0. Five-line summary + the sharpest line

1. **Zama ships; dregg has the deeper machine.** Zama is live on Ethereum mainnet
   (Dec 30 2025), has a Draft EIP standard (ERC-7984), a live confidential-yield vault, an
   SDK, and a crisp institutional pitch. dregg has none of that shipped — it has a
   *verified* kernel and a *deeper* privacy architecture, in build.
2. **The eclipse is five-fold and cited.** dregg is (a) **committee-free** — no decryption
   committee that *can* read a trade (Zama's confidentiality rests on a 13-node threshold
   KMS that decrypts on demand); (b) **fair-by-proof** — sealed-batch uniform price, no
   sniping *as a Lean theorem*, where Zama's confidential DeFi is an AMM still exposed to
   ordering/MEV; (c) **machine-checked** — Lean-proven soundness cores vs Zama's
   audits-only; (d) **post-quantum on the whole surface it targets** — hash/STARK/lattice
   floors, where Zama is PQ on FHE but *not* on its ZK layer; (e) **a dial**
   (Dark/Shielded/Open), not one fixed posture.
3. **The verified cores are real and kernel-clean.** `Market/CertF.lean`
   (verify-not-find: a linear certificate ⇒ ε-optimality), `Market/FhEggClearing.lean`
   (uniform-price fold→crossing→conserving/optimal clearing), and `Market/RevealNothing.lean`
   (`View = Sim∘Q`: two different trade-sets with equal public leakage produce an identical
   transcript) are proven with adversarial teeth and `#assert_all_clean` axiom hygiene.
4. **The honest caveats.** dregg's Tier-0 no-viewer clearing is **measured-slow** (FHE
   tractable only at N≈32–512 orders/pair at minute cadence); the clearing-level
   reveal-nothing theorem is **conditional on a named PCS-ZK floor** (not a `sorry`, not yet
   discharged); the value-binding is **still classical DLog** today and the PQ cutover is a
   named build; and the product surface is **well-posed, not all discharged**. dregg is
   building what Zama has shipped.
5. **So the strategy is: lead with the eclipse (verified + fair + PQ + committee-free +
   dial), close the product gap deliberately.** Confidentiality is the floor; dregg sells
   the finish line.

**The single sharpest eclipse line:**

> **Zama makes a trade invisible to everyone except a 13-node committee that can decrypt it
> on request. dregg proves the trade was fair, conserving, and post-quantum — and a Lean
> theorem shows the public transcript is simulatable from the price and totals alone, so
> there is no committee, because there is nothing to decrypt.**

---

## 1. What Zama HAS that dregg is missing (stated plainly)

This is not close. On product, standardization, and shipping, **Zama is ahead of dregg**,
and pretending otherwise would be exactly the self-congratulatory dishonesty this repo
forbids. The gaps, each real:

| # | What Zama has shipped | dregg's state | Grade gap |
|---|---|---|---|
| 1 | **A live mainnet product.** fhEVM on Ethereum mainnet since **Dec 30 2025**; first confidential stablecoin (cUSDT) transfer, ~$0.13 gas. [litepaper] | DrEX Tier-2 is ≈ shippable; Tiers 0/1 in build. No confidential-finance mainnet. | Zama SHIPPED; dregg BUILDING |
| 2 | **A crisp product surface: Shield / Unshield / Send.** Wrap an ERC-20 into a confidential token and back, one SDK call. [ERC-7984 explainer] | dregg has a shielded pool + verified clearing but **has not surfaced Shield/Unshield/Send primitives** to users. | Zama has UX; dregg has kernel |
| 3 | **A named interop standard: ERC-7984** (Confidential Fungible Token), Draft EIP, Zama + OpenZeppelin + Inco "Confidential Token Association". [EIP-7984] | dregg has no published token standard and no EIP. | Zama has a standard; dregg has none |
| 4 | **A live confidential-DeFi product: Confidential Earn.** Zama + Morpho + Steakhouse confidential-USDC yield vault, deposits open ~June 23 2026. [The Block] | DrEX clearing is proven at model level; no live yield product. | Zama has live yield; dregg has proofs |
| 5 | **An institutional-compliance pitch that lands.** "Compliant confidentiality," selective disclosure via KMS user-decryption + on-chain ACLs (auditor access). [Figment; KMS docs] | dregg has the stronger *verified* story but **has not packaged it** as a compliance pitch. | Zama has framing; dregg has substance, unframed |
| 6 | **Funding + traction: first FHE unicorn.** Series B $57M @ $1B+ (June 2025), Pantera + Blockchange; named genesis KMS operators (Ledger, Fireblocks, OpenZeppelin, Etherscan, LayerZero…). [CoinDesk; litepaper] | dregg is pre-catalyst; $DREGG launched early (see memory `reference-dregg-token-market`). | Zama has capital + logos |

**The honest read:** Zama took the productization seriously first, and it shows. A
developer can ship a confidential token on Zama *today* with an audited standard and an SDK.
On dregg, that same developer would today be composing verified Lean cores by hand. **The
eclipse below is a technology-depth and positioning thesis plus a productization TODO — it
is not a claim that dregg is a more finished product. It is not.**

---

## 2. THE ECLIPSE — where dregg's tech is genuinely stronger (point-by-point, graded)

Now the other direction, and here it *is* decisive. Five axes on which dregg's technology
surpasses Zama's, each cited on both sides, each graded proven-vs-frontier.

### (a) Committee-free vs a decryption committee that CAN read your trade

**Zama.** Confidentiality on Zama is *encryption whose plaintext a committee can recover.*
Ciphertexts (`euint` handles) live off-chain at the coprocessor; the FHE decryption key is
**secret-shared across a 13-node threshold KMS with a 2/3-majority rule (~9-of-13)**, run
inside AWS Nitro enclaves, and **any value can be decrypted** when on-chain ACLs permit
[KMS docs; litepaper]. The trust model is an **honest-majority committee (≤1/3 malicious)
that holds the power to decrypt.** Selective disclosure to an auditor is the *same
mechanism* pointed at a new party. So "confidential" on Zama means: *nobody sees it unless
9 of 13 named operators (or an ACL) decide otherwise.*

**dregg.** Two strictly stronger postures over one verified kernel
(`DREGGFI-PRIVACY-TIERS.md`):
- **Tier 1 SHIELDED is committee-free.** The clearing runs for one computing party (the
  solver) and the public transcript exposes only `[nullifier, root, value_binding]` per leg.
  **There is no decryption committee at all** — nothing is encrypted-to-be-decrypted; the
  private data lives in a STARK witness under a hiding PCS and is never recoverable by any
  quorum. `Market/RevealNothing.lean` proves `same_leakage_indistinguishable`: two clearings
  with the *same public leakage* but *genuinely different trades* produce the **identical**
  transcript — an observer, operator included, learns only the leakage class.
- **Tier 0 DARK is no-viewer.** Clearing runs on ciphertexts; a threshold committee holds
  only *decryption-key shares* and decrypts **only the public clearing price `p*`** — never
  an order. Even a fully-corrupt committee **cannot see a trade** (privacy is unconditional
  on committee honesty; only correctness is conditional, and the proof catches that)
  [`DREX-NO-VIEWER-SURPASS.md §3`].

**The eclipse.** Zama's committee *can* read every trade; it is a feature (auditor access)
and a risk (9 honest-of-13). dregg's Tier 1 has **no such committee** and Tier 0's committee
**cannot read a trade even if it wanted to.**

**Grade.** Tier 1 committee-free architecture: **BUILT/PROVEN at spec** (`shielded_ring_clears`,
`RevealNothing.same_leakage_indistinguishable`, kernel-clean) — the N-leg apex and deployed
binding are in build. Tier 0 no-viewer: **FRONTIER** (FHE PoC bounds feasibility; measured-slow,
§(e) and caveat 6.2).

### (b) Fair-by-proof vs a confidential AMM that is still snipe-able

**Zama.** Zama's live confidential DeFi (Confidential Earn) and its confidential-swap demos
are built on the **AMM shape**: encrypting the *amounts* in a constant-product swap. But an
AMM still updates pool reserves and price, and **transaction ordering (sequencing MEV)
remains a chain-level property** — encrypting the amount blunts amount/direction-based
front-running but does **not** make the venue MEV-immune. Zama's confidential swap surface is
testnet/demo + one GSR OTC trade, not a live first-party AMM [litepaper; community]; the
"MEV-proof" framing is a marketing claim on demos, not a proven live guarantee.

**dregg.** DrEX is not an AMM. It is a **sealed-batch uniform-price call auction**, and
fairness is a *theorem*, not a mitigation:
- `Market/FhEggClearing.lean`: the book folds into a monotone demand/supply curve
  (`demand_perm` — order-independent, so arrival order and thus sniping-by-ordering is
  *structurally irrelevant*), crosses once at a single `p*` (`crossing_is_least`,
  `Fstep_monotone`), and every fill transacts at that one uniform price.
- `Market/Optimality.lean` (composed in): `uniform_price_optimal` — the clearing is
  no-arbitrage, envy-free, individually rational. Every filled order gets the *same* price;
  there is no ordering to exploit and no per-order price to snipe.

**The eclipse.** Zama's confidential DeFi hides the number in an AMM that a sequencer can
still reorder around. dregg's uniform-price sealed batch makes **sniping/front-running
un-representable** — a single-price batch has no intra-batch order for MEV to attack, and
that is a machine-checked property, not a mempool trick. **This is the thing Zama's AMM
architecture structurally cannot do.**

**Grade.** **PROVEN at model level** (`uniform_price_optimal`, `FhEggClearing` cores,
kernel-clean with teeth: `noCrossBook_no_crossing`, `leakBatch_refused`). Ledger-realization
(binding the histogram fold to on-chain fills in-circuit) is the named circuit step, not yet
discharged.

### (c) Machine-checked + post-quantum vs classical + audited-only

**Zama.** (i) **Not formally verified.** Assurance is *parameter choice + manual audit*
(OpenZeppelin audited the confidential-token contracts); no machine-checked soundness proof
of fhEVM, the KMS, or the TFHE stack exists (searched; none found). (ii) **Post-quantum is
partial and Zama says so.** The FHE/MPC rests on TFHE (CGGI), which is LWE-based and thus
plausibly PQ, and Zama claims "our FHE scheme is post-quantum" — **but the ZK
proofs-of-knowledge (ZKPoK) are not yet PQ**; Zama states it is *working toward* a
lattice-based PQ ZK [litepaper]. So Zama's end-to-end PQ is aspirational.

**dregg.** (i) **Machine-checked.** The soundness cores are Lean theorems whose *statements*
are audited, not just `#assert_axioms`-clean: `CertF.weak_duality` /
`certifies_epsilon_optimal`, `FhEggClearing.clearedBatch_conserves` /
`clearedBatch_optimal`, `RevealNothing.reveal_nothing`, all `#assert_all_clean`. The STARK
soundness floor itself is proven (BCIKS20 list-decoding, deployed FRI ~112.6-bit; memory
`project-linking-tower-forgery-closure`). (ii) **PQ by construction on the privacy + proof
surface** — Poseidon2/FRI hashing, statistical-ZK PCS, lattice FHE at Tier 0 — the two
things regulated institutions with a decade horizon should actually demand.

**The honest symmetry (no overclaim).** dregg has its *own* PQ hole and this repo names it:
the shielded **value-binding is today classical discrete-log** (Pedersen/Ristretto + Schnorr
excess + Bulletproof range), which is Shor-broken — so dregg's *no-mint* soundness is not yet
PQ either [`PQ-SHIELDED-COMMITMENT.md §1`]. The difference is that dregg has (1) *diagnosed
it precisely*, (2) *scoped the fix* (Option A: Poseidon2 hash-commitment + fully-in-AIR STARK
conservation, retiring all DLog), and (3) *proven the pieces it can* (field⇒integer
conservation no-wrap; Poseidon2 value-binding hiding). Zama's ZKPoK PQ gap and dregg's
binding PQ gap are *both real*; dregg's is the one with a verified closure lane.

**Grade.** Verification: **PROVEN** (the cited cores). PQ privacy/proof: **BUILT/PROVEN**.
PQ value-binding: **FRONTIER** (the Option-A cutover is a named `M`-difficulty build).

### (d) A dial vs one posture

**Zama.** One posture: FHE-everything, committee-decryptable. Every value is an encrypted
handle; the trust model and cost are fixed.

**dregg.** **One kernel, three postures** — Tier 0 DARK (no viewer), Tier 1 SHIELDED
(private-from-the-world, solver sees), Tier 2 OPEN (public, fair-by-proof) — and *the same
verified soundness guarantee holds at every tier* (`DREGGFI-PRIVACY-TIERS.md §2`): fair,
conserving, no-mint, uniform-price-optimal, proof-carrying are **identical across the dial**;
only privacy, mechanism-generality, and cost move. The tier a product can run at is a *type*
in `fhIR` — the compiler reports the most-private tier the math actually delivers and refuses
to promise more.

**The eclipse.** Zama forces one privacy/cost point and one trust model. dregg lets the user,
market, or individual trade pick the point, with an unchanging can't-be-cheated guarantee
underneath.

**Grade.** Tier 2 **NOW**; Tier 1 **BUILDING**; Tier 0 **FRONTIER**. `fhIR` and its
admissibility theorem are a **named research target** (the theorem *shape* is written, not
discharged) [`FHEGG-PRODUCT-ORDER-FRONTIER.md`].

### (e) Verify-not-find (µs solver + STARK) vs FHE-everything (slow)

**Zama.** FHE computes *everything* homomorphically, and it is slow: current fhEVM
throughput is **>20 TPS** (up from 0.2), with **500–1,000 TPS via GPU by end-2026 as a
roadmap projection, not a measured number** [litepaper]. Per-operation FHE latency is heavy
by nature (an encrypted 16-bit compare ≈ tens of ms on CPU [TFHE-rs benchmarks]).

**dregg.** dregg does **not** compute the answer under encryption at Tiers 1–2. It runs an
*untrusted* fast solver (plaintext at Tier 1, µs-scale; GPU) and then **verifies a small
certificate**. `Market/CertF.lean` is the keystone: for the volume-max circulation LP, a
primal-dual triple `(f, π, s)` with duality gap `≤ ε` **certifies ε-optimality — independent
of how it was found** (`certifies_epsilon_optimal`). The certificate check is a *linear* AIR
of size `O(m + nnz A)`, **not** `O(T·m)` (proving the solver's T iterations). This is dregg's
DNA: prove the *checker*, not the *search*.

**The eclipse.** Zama pays FHE cost to *compute* the clearing. dregg pays a cheap linear
*check* over a fast plaintext/GPU solve and gets a machine-checked optimality certificate.
For the confidential-*matching* problem, verify-not-find is categorically cheaper than
FHE-compute.

**Grade.** **PROVEN** (`CertF` cores, kernel-clean, with emit bridge to AIR constraints and
teeth). The Tier-0 FHE path — where dregg *does* pay FHE cost to get no-viewer — is exactly
where dregg is **measured-slow** and honest about it (§6.2).

---

## The comparison table (per axis, cited)

| Axis | **Zama** (cited) | **dregg** (cited) | Eclipse verdict |
|---|---|---|---|
| **Confidentiality mechanism** | FHE on encrypted `euint` handles; committee-decryptable [litepaper] | Tier 1 hiding STARK (no committee); Tier 0 FHE decrypt-price-only; Tier 2 public [`PRIVACY-TIERS`] | dregg stronger (committee-free / no-viewer) |
| **Trust to keep a trade private** | 9-of-13 KMS honest-majority + Nitro TEEs [KMS docs] | Tier 1: none (hiding PCS); Tier 0: unconditional on committee honesty [`NO-VIEWER §3`] | **dregg decisive** |
| **Fairness / MEV** | Confidential AMM; encrypted amounts, ordering still exposed [litepaper] | Sealed-batch uniform price; sniping un-representable, PROVEN [`Optimality`, `FhEggClearing`] | **dregg decisive** |
| **Formal verification** | None; audits only (OpenZeppelin) | Lean cores, `#assert_all_clean`, statements audited [`CertF`,`RevealNothing`,`FhEggClearing`] | **dregg decisive** |
| **Post-quantum** | FHE/MPC PQ (LWE); **ZKPoK not yet PQ** [litepaper] | Privacy+proof PQ (Poseidon2/FRI/lattice); **binding not yet PQ**, fix scoped [`PQ-SHIELDED-COMMITMENT`] | dregg stronger surface, both have a named gap |
| **Postures** | One (FHE-everything) | Dial: Dark/Shielded/Open, one verified kernel [`PRIVACY-TIERS §2`] | dregg stronger |
| **Compute model** | FHE-everything (>20 TPS; 500–1k roadmap) [litepaper] | Verify-not-find (µs solver + linear cert) [`CertF`] | dregg stronger for matching |
| **Shipped product** | Mainnet, cUSDT, Confidential Earn LIVE [The Block] | Tier-2 ≈ shippable; Tiers 0/1 building | **Zama decisive** |
| **Standard** | ERC-7984 Draft EIP + association [EIP-7984] | None published | **Zama decisive** |
| **SDK / UX** | Relayer SDK, FHE.sol, Shield/Unshield/Send [docs] | npm/pip SDKs exist; primitives not surfaced | **Zama decisive** |
| **Institutional framing** | "Compliant confidentiality," KMS selective disclosure [Figment] | Stronger substance (verified/PQ), unpackaged | Zama decisive *today* |
| **Funding / traction** | Series B $57M @ $1B, first FHE unicorn [CoinDesk] | Pre-catalyst | **Zama decisive** |

The pattern is clean: **dregg wins every technology-depth axis; Zama wins every
shipping/product/standardization axis.** That is the whole strategic situation in one table.

---

## 3. The eclipse positioning — "Confidentiality is the floor, not the finish line"

**The one line.** *Confidentiality is the floor, not the finish line.* Zama proved you can
hide a balance onchain. dregg's thesis is that hiding is table stakes — what regulated,
adversarial, decade-horizon finance actually needs is hiding **plus** the four things Zama's
architecture cannot give at once.

**The expanded pitch.** Not just confidential —

- **+ FAIR.** A sealed-batch uniform price where sniping and front-running are
  *un-representable*, proven, not mitigated (`Optimality.lean`, `FhEggClearing.lean`). An
  AMM, confidential or not, cannot make this claim.
- **+ VERIFIED.** Machine-checked soundness cores, statements audited, kernel-clean — the
  assurance an institution can *check the proof of*, not merely trust an auditor's PDF.
- **+ POST-QUANTUM.** Hash/STARK/lattice floors on the privacy and proof surface — because a
  confidential ledger that a future quantum adversary can retro-decrypt is not confidential,
  it is time-delayed public.
- **+ COMMITTEE-FREE.** No 9-of-13 quorum that *can* read your trade; Tier 1 has no
  decryption committee, Tier 0's committee cannot read an order.
- **+ DIAL-ABLE.** One kernel, three postures — you are not locked to one privacy/cost/trust
  point.

**The institutional framing** (Zama's strongest ground — meet it and surpass it):
- *Verified compliance.* Zama offers selective disclosure through a committee; dregg offers
  the same disclosure *plus a machine-checked proof that the disclosed clearing was fair,
  conserving, and minted nothing.* Compliance you verify, not compliance you trust.
- *PQ future-proofing.* A confidential position taken today on a classical-ZK system is
  decryptable by a future quantum adversary; dregg's target surface is PQ.
- *No-committee-trust.* Your confidential position does not depend on 9 named operators
  staying honest.
- *Provable fairness.* Your fill was at the one uniform price the whole batch got — as a
  theorem, not a promise.

---

## 4. dregg's version of each Zama use-case (map + strengthen)

For each Zama use-case: what it is, dregg's stronger version, what dregg has *now*, and the
productization gap.

### 4.1 Confidential RWA / institutional allocation

**Zama.** Confidential balances/positions for institutions "without broadcasting to
competitors or front-runners"; selective disclosure to auditors via the KMS [The Block;
Figment].

**dregg's stronger version.** Investor identity, cap-table, and deal-terms hidden **and**
distribution *provably fair* — the launchpad is the vehicle: `DreggLaunchpad.sol`
(commit → reveal → uniform-price clear → settle) makes the dominant launch abuses
*unconstructable* (a Lean theorem forbids them), and `Market/GraduationPool.lean` proves the
graduated pool is **never-insolvent** (`pool_solvent_forever`, a disclosed reserve floor that
a fill can never breach) — unlike a drainable bonding curve or a solvency-theorem-free
Raydium pool [`DREGG-LAUNCHPAD-DESIGN.md`]. Plus verified + PQ + no-committee.

**Now vs gap.** *Now:* the sealed-bid clearing spec (`shielded_ring_clears`), the solvency
keystone, and the launchpad design over proved machinery. *Gap:* the launchpad is a **design
over proved primitives, not a shipped product** (its own §5 is the build path); the shielded
allocation-commitment (Tier-1 SetField attestation) is component 5, difficulty `L`
[`SHIELDED-DREX-ASSURANCE-ROADMAP.md`].

### 4.2 Confidential payments / payroll

**Zama.** ERC-7984 confidential tokens: encrypted balances + transfer amounts; Shield an
ERC-20 in, Send confidentially, Unshield out (an explicit KMS decrypt) [EIP-7984].

**dregg's stronger version.** The shielded pool already hides amounts with **PQ-safe
privacy** (perfect Pedersen hiding + statistical-ZK STARK path), and settlement is
*proof-carrying* — a payment carries a machine-checked conservation/no-mint receipt, not
just an encrypted number a committee could open. And it is **committee-free**: no quorum can
decrypt a payroll amount.

**Now vs gap.** *Now:* the shielded value pool, hiding commitments, conservation proofs.
*Gap:* the **Shield/Unshield/Send primitives are not surfaced** as a product (§5.1); and the
value-binding PQ cutover (`PQ-SHIELDED-COMMITMENT.md` Option A) must land for the *no-mint*
side to match the *privacy* side on PQ.

### 4.3 Confidential DeFi / trading

**Zama.** Confidential Earn (live Morpho vault) and confidential-swap demos — the AMM shape
with encrypted amounts.

**dregg's stronger version.** The fhEgg engine: **private AND fair clearing** — a
sealed-batch uniform-price call auction (`FhEggClearing.lean`) with a verify-not-find convex
certificate (`CertF.lean`) for richer products. This is **the thing Zama structurally cannot
do**: an AMM has intra-block ordering to exploit; a single-price sealed batch does not, and
the fairness is proven.

**Now vs gap.** *Now:* the verified clearing + certificate cores, kernel-clean. *Gap:*
ledger-realization of `uniform_price_optimal` (binding the model-level clearing to on-chain
fills in-circuit); the N-leg apex + partial-fill inequality (`SHIELDED-DREX-ASSURANCE-ROADMAP`
components 1, 6); and the private-node STARK-proving path productized.

### 4.4 Confidential token distribution

**Zama.** Confidential token transfers / vesting via ERC-7984 (Zama ran its own token sale
as a sealed-bid Dutch auction on the protocol) [litepaper].

**dregg's stronger version.** The provably-fair launchpad: vesting/airdrop amounts hidden
**and** *no-hidden-supply provable* — the supply-authority biconditional and the sealed-bid
commit→reveal→uniform-price clear make hidden mints and insider-supply
*unconstructable*, and graduation lands in a solvency-proven pool
[`DREGG-LAUNCHPAD-DESIGN.md`, `Market/GraduationPool.lean`]. Hidden distribution *without*
hidden supply.

**Now vs gap.** *Now:* the launchpad design over proved machinery + the graduation solvency
proof. *Gap:* ship the on-chain launchpad + wire the shielded distribution to the deployed
nullifier accumulator (component 4).

---

## 5. The productization roadmap — how to actually ship the eclipse

Honest sequencing. **Lead with the fast-strong offering (Tier 1): committee-free, fair,
verified, PQ-on-privacy — it needs no FHE and is measured-fast.** Tier 0 (no-viewer) is the
frontier headline, not the launch vehicle (it is measured-slow).

**Phase 1 — Surface the confidential-token primitives (the missing UX).**
Expose **Shield / Unshield / Send** from the existing shielded pool — the exact primitive
users know from Zama, but committee-free and PQ-privacy. This is a *packaging* task over
built machinery, not new cryptography. Ship the npm/pip SDK calls (the SDKs exist — memory
`project-adoption-deployability-epoch`). *Blocking dependency:* land the value-binding PQ
cutover (Option A) so the no-mint side is PQ too.

**Phase 2 — Ship the use-case product surface.**
Confidential Payments (Shield/Send/Unshield) → Confidential Trading (the fhEgg Tier-1
sealed-batch DEX: private + fair) → Confidential Distribution (the launchpad) → Confidential
RWA/allocation. Each rides the *same verified kernel*; the product is the surface, the
guarantee is shared.

**Phase 3 — The institutional-compliance framing, packaged.**
Take dregg's substance (verified clearing, PQ, committee-free, provable fairness) and write
the *pitch* — the thing Zama did and dregg has not. Verified-compliance,
PQ-future-proofing, no-committee-trust, provable-fairness — §3, as a deck and a docs surface,
not just a design note.

**Phase 4 — A dregg confidential standard (or ERC-7984 compat).**
Two options, non-exclusive: (i) **ERC-7984 compatibility** — implement the confidential-token
interface so dregg tokens interoperate with the emerging standard while delivering the
committee-free/PQ/verified backend underneath; (ii) a **dregg confidential-clearing
standard** for the thing ERC-7984 does *not* standardize — fair sealed-batch clearing with a
verify-not-find certificate. Compat wins distribution; the dregg standard wins the axis Zama
has no answer for.

**Phase 5 — The SDK, hardened.**
The npm/pip SDKs exist; harden them around the Phase-1 primitives and the Phase-2 surfaces so
a developer ships confidential-fair finance in a few calls — matching Zama's developer
ergonomics with a strictly stronger backend.

**Sequencing note (honest).** Phase 1–2 (Tier 1) is the shippable eclipse and should lead.
Tier 0 (no-viewer FHE) is a **research ladder**: non-verifiable proto ~6–12 mo,
verifiable-via-re-eval ~1–2 yr, succinct-for-light-clients ~2–4 yr
[`DREX-NO-VIEWER-SURPASS.md §6`]. Sell Tier 0 as the frontier it is, never as the launch
product, and never dress a lower rung as a higher one.

---

## 6. Honest caveats (the eclipse is a thesis + a TODO, not a finished win)

Every one of these is stated so the eclipse claim stays true.

**6.1 Zama shipped; dregg is building.** The single most important caveat (§1). Zama is live
on mainnet with a standard, an SDK, and live yield. dregg's confidential-finance surface is
in build. The eclipse is *technology depth + positioning*, plus a productization TODO — not a
claim that dregg is more finished. It is not.

**6.2 The no-viewer tier is measured-slow.** Tier 0 FHE clearing is tractable only at
**N ≈ 32–512 orders per pair at minute cadence** and *breaks at N in the thousands* — a real,
measured envelope [`DREX-NO-VIEWER-SURPASS.md §2`]. It is the frontier headline, not the fast
offering. The fast-strong offering is **Tier 1** (committee-free, fair, verified,
PQ-on-privacy), which needs no FHE.

**6.3 Reveal-nothing is floor-conditional.** `Market/RevealNothing.lean` proves the tractable
core — `View = Sim∘Q`, `same_leakage_indistinguishable`, the `Q`-faithful simulator shell,
the anti-vacuity teeth (`leaky_no_simulator`) — **conditional on a named PCS-ZK floor**
(`RevealBundle.reveal_law` = the `HidingFriPcs` statistical-ZK + hash-hiding +
nullifier-unlinkability obligation). That floor is an explicit graded structure field — **not
a `sorry`, not yet a discharged theorem.** Do not read this as "reveal-nothing is proved"; it
is proved *conditional on the PCS-ZK floor*, the same shape the linking tower is
`HashCR`-conditional.

**6.4 dregg has its own PQ hole, named.** The value-binding is **classical DLog today**
(Pedersen/Ristretto), so *no-mint* soundness is not yet PQ [`PQ-SHIELDED-COMMITMENT.md`]. The
privacy side is PQ; the binding side is a named `M`-difficulty cutover (Option A). Symmetric
honesty with Zama's ZKPoK-not-yet-PQ gap: both real, dregg's has a verified closure lane.

**6.5 The products are well-posed, not all discharged.** `fhIR` and its admissibility theorem
are a **research target** (theorem *shape* written, not proved)
[`FHEGG-PRODUCT-ORDER-FRONTIER.md`]; the launchpad is a **design over proved primitives**, not
a shipped product; ledger-realization of the model-level clearing/optimality proofs is the
named circuit step. The eclipse rests on *cited, proven cores* (`CertF`, `FhEggClearing`, the
`RevealNothing` tractable core, `Optimality`, `GraduationPool`) plus *honestly-graded
frontier* around them — not on claiming the frontier is done.

**The eclipse, stated exactly.** dregg's technology genuinely surpasses Zama's — verified,
post-quantum-on-the-privacy-surface, fair-by-proof, committee-free, dial-able, verify-not-find
— and every one of those is cited to a proven core or an honestly-graded frontier. Zama
genuinely surpasses dregg on shipping, product surface, standardization, and traction. The
strategy writes itself: **lead with the eclipse, close the product gap deliberately, and
never dress a frontier as a finished product or a lower rung as a higher one.**

---

## See also

- `docs/deos/DREGGFI-PRIVACY-TIERS.md` — the Dark/Shielded/Open dial over one verified kernel.
- `docs/deos/FHEGG-KERNEL.md` · `docs/deos/PRIVATE-CONVEX-ENGINE.md` — the aggregation-monoid + Cert-F engine.
- `docs/deos/FHEGG-PRODUCT-ORDER-FRONTIER.md` — `fhIR`, Price-Cert, the admissibility theorem (research target).
- `docs/deos/DREX-NO-VIEWER-SURPASS.md` — the Tier-0 FHE envelope + the measured slow numbers.
- `docs/deos/PQ-SHIELDED-COMMITMENT.md` — the value-binding PQ diagnosis + Option-A cutover.
- `docs/deos/SHIELDED-DREX-ASSURANCE-ROADMAP.md` — the six-component Tier-1 build map + the reveal-nothing crux.
- `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` — the provably-fair launchpad.
- `metatheory/Market/{CertF,FhEggClearing,RevealNothing,Optimality,GraduationPool}.lean` — the verified cores.

## Zama sources (cited)

- Zama Protocol litepaper (architecture, 13-node KMS, PQ posture, throughput): https://docs.zama.org/protocol/zama-protocol-litepaper
- Zama KMS / threshold decryption (9-of-13, Shamir over Galois rings, Nitro TEEs): https://docs.zama.org/protocol/protocol/overview/kms
- ERC-7984 Confidential Fungible Token (Draft EIP): https://eips.ethereum.org/EIPS/eip-7984
- ERC-7984 explainer + Confidential Token Association: https://www.zama.org/post/erc-7984-the-confidential-token-standard-explained
- OpenZeppelin confidential contracts + audit: https://docs.openzeppelin.com/confidential-contracts/token · https://www.openzeppelin.com/news/zama-confidential-fungible-token-audit
- Confidential Earn (Zama + Morpho + Steakhouse, live vault): https://www.theblock.co/post/404992/zama-morpho-steakhouse-launch-first-confidential-defi-yield-vault-ethereum
- Ethereum mainnet launch / cUSDT: https://phemex.com/news/article/zama-mainnet-launches-with-successful-cusdt-privacy-stablecoin-transfer-50405
- Relayer SDK / FHE.sol (developer surface): https://docs.zama.org/protocol/relayer-sdk-guides · https://github.com/zama-ai/fhevm-solidity
- Series B $57M @ $1B (first FHE unicorn): https://www.coindesk.com/tech/2025/06/25/zama-raises-57m-becomes-first-unicorn-involved-with-fully-homomorphic-encryption
- Institutional framing (Figment first look): https://www.figment.io/insights/zama-first-look-bringing-compliant-confidentiality-on-chain/
- TFHE-rs benchmarks (per-op FHE cost): https://docs.zama.org/tfhe-rs/get-started/benchmarks/cpu/cpu-integer-operations
