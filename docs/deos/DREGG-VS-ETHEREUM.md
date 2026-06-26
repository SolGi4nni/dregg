# dregg vs Ethereum — model comparison + ERC/EIP survey

What dregg *is*, set against what Ethereum *is*, grounded in dregg's actual code
(file:line) and the Ethereum standards corpus. The goal is honest: name where
dregg's object model is genuinely stronger, and name where Ethereum's ecosystem,
tooling, and — above all — its *standardization discipline* are a real lesson we
should learn.

The dregg through-line throughout: **a turn is the exercise of an attenuable
proof-carrying token over owned state, leaving a verifiable receipt.**

---

## 1. Model / protocol comparison

### The fundamental inversion

Ethereum and dregg sit on opposite sides of one axis: **where authority comes
from.**

| | Ethereum | dregg |
|---|---|---|
| Authority source | **Ambient** — `msg.sender` is whoever signed the outer tx; any contract you call sees your address and can act on the *full* authority your address carries | **Designated** — you can only act by *presenting* a capability you hold; there is no `msg.sender` to consult, no ambient identity to impersonate (`cell/src/capability.rs:42` `CapabilityRef`; `turn/src/action.rs:215` `Authorization`) |
| State model | One global mutable state trie; contracts hold `mapping(address => …)` balances keyed by ambient identity | Sovereign **cells** own their own state and c-list; a cell is identity + signed balance + capability table (`cell/src/cell.rs:249`) |
| Asset identity | A *deployed contract address* (ERC-20/721/1155 each a separate deployment) | **`AssetId := issuer cell's `token_id`** — the issuer cell *is* the asset; supply is the issuer's signed-negative "well" (`turn/src/executor/atomic.rs:247`; `turn/src/rotation_witness.rs:86`) |
| Value safety | Solidity arithmetic + audits; conservation is whatever the contract code happens to enforce | **Per-asset conservation Σδ=0 is a protocol law**, checked in the executor *and* re-proven in-circuit so a light client needs no ledger (`turn/src/executor/atomic.rs:1297`; `turn/src/executor/proof_verify.rs:1220`) |
| Execution | EVM bytecode metered by **gas**; re-executed by every full node | Turns produce **STARK proofs**; verifiers check a proof, they do not re-execute (`lightclient/src/lib.rs`; whole-history fold in `circuit-prove/src/ivc_turn_chain.rs`) |
| Trust model | Re-execution (every node runs every tx) → ZK/optimistic rollups bolt verification on *afterwards* | **Verification-native**: the proof *is* the artifact; the light client is unfoolable by construction (`verifyBatch accept ⟹ ∃ genuine kernel transition`) |
| Authorization | One scheme: an ECDSA signature over the tx (ERC-1271 later generalized contract sigs) | A **lattice of authorization modes** as first-class data: `Signature`, `Proof`, `Bearer` delegation chain, `Token` (biscuit/macaroon), `CapTpDelivered`, `Stealth`, `OneOf`, `Custom{vk_hash}` (`turn/src/action.rs:215`–431; `cell/src/permissions.rs:5`) |

The one-sentence version: **Ethereum is account-based and ambient-authority;
dregg is object-capability and designated-authority.** Everything below follows
from that inversion.

### What each makes easy vs hard

**dregg makes easy** (because authority is designated and attenuable):

- **Least-authority delegation.** Handing someone a *narrowed* capability is the
  default operation, not a thing you bolt on. `is_attenuation(held, granted) ⟺
  granted.is_narrower_or_equal(held)` is the lattice (`cell/src/capability.rs:779`),
  with effect-mask facets (`cell/src/facet.rs:136` `is_facet_attenuation`,
  bitwise subset) and order-theoretic auth narrowing
  (`cell/src/permissions.rs:52` `Impossible ⊆ Signature/Proof ⊆ Either ⊆ None`).
  On Ethereum, "let this app spend *up to 50 USDC/day and nothing else*" requires
  a bespoke contract; here it is a faceted, caveat-carrying cap.
- **No confused deputy.** Because a callee never sees ambient `msg.sender`
  authority — only the specific cap you chose to present — the classic confused-
  deputy / approval-drain class of bugs is structurally absent.
- **Light-client verification with no chain replay.** A turn carries its proof;
  the whole-history light client folds proofs (`circuit-prove/src/ivc_turn_chain.rs`)
  and cannot be fooled. Ethereum needs a separate rollup/prover stack to get
  near this.
- **Conservation as a free theorem.** Σδ=0 per asset is checked off-ledger and
  in-circuit; you cannot forge value within or across an asset
  (`turn/src/executor/proof_verify.rs:1220`).
- **Private / shielded value.** UTXO-style notes with nullifiers
  (`cell/src/note.rs:40`; `Effect::NoteSpend`/`NoteCreate`) are native, not a
  bolted-on mixer.

**Ethereum makes easy** (and these are real advantages we must respect):

- **Discoverability and composability *right now*.** Any contract can read any
  other contract's public state and call its functions synchronously in one
  atomic tx. dregg's cross-cell reads go through OFE/serviced methods and the
  object-capability discipline deliberately makes "just reach into another
  object" *not* the default — safer, but more ceremony.
- **A deep, agreed standard library.** ERC-20/721/1155/165/4626 are *social
  facts*: every wallet, indexer, explorer, and DEX already speaks them. This is
  Ethereum's single biggest lead and the core lesson of §3.
- **Tooling and mindshare.** Etherscan, Foundry/Hardhat, The Graph, wallet
  infra, a decade of audited reference implementations. dregg's proof/cap model
  is more sound but the surrounding ecosystem is nascent.
- **Permissionless deployment + immediate liquidity.** Deploy a contract, it's
  live and composable with the entire DeFi graph. dregg's stronger isolation is
  also a higher integration bar.

**Honest verdict:** dregg's *object model and trust model are a generation ahead*
— ambient authority and global re-execution are the two original sins ERC after
ERC has spent years patching (4337, 1271, 7702 are all "make accounts behave
more like capabilities"). But Ethereum's *ecosystem layer* — standardized
interfaces as social coordination, plus tooling — is where dregg is genuinely
behind, and it is catchable only by deliberately adopting the ERC *discipline*,
not the ERC *mechanisms*.

---

## 2. ERC / EIP survey

Each standard classified: **(A) already-native** in dregg (with the stronger
dregg primitive cited), **(B) a real lesson** dregg should adopt, or **(C) N/A**
(chain-specific, no analog needed).

### Classification table

| ERC/EIP | What it is (Ethereum) | Class | dregg's position |
|---|---|---|---|
| **ERC-20** fungible token | balance `mapping` per contract | **A** | Cell signed balance keyed on `token_id`; `AssetId := issuer cell` (`atomic.rs:247`). Stronger: supply is a conserved well, mint cap-gated, Σδ=0 a law. |
| **ERC-721** NFT | unique tokenId per contract | **A** | A cell *is* a unique object (identity = `blake3(pubkey‖token_id)`); or a note with `fields[0]=unique_id` (`cell/src/note.rs`). Stronger: the NFT is a sovereign object that can itself hold caps/value. |
| **ERC-1155** multi-token | `mapping(id => balance)` + batch | **A** | Per-asset wells + multi-action turns give batch natively; `balance_change` deltas net per asset in one turn (`action.rs:99`). |
| **ERC-165** interface detection | `supportsInterface(bytes4)` | **A** | `InterfaceDescriptor{interface_id, methods}` content-addressed by sorted-Poseidon2 root (`cell/src/interface.rs:214`). Stronger: the id *is* the hash of the methods, not a hand-picked 4-byte tag that can collide or lie. |
| **ERC-2535** Diamonds (facets) | multiple impl facets behind one proxy | **A** | E-language **facets** = effect-mask views (`cell/src/facet.rs:36`), `route_method` via verified DFA (`interface.rs:361`). Stronger: facets are *capability attenuations* (subset-enforced), not just code routing. |
| **ERC-1271** contract signatures | `isValidSignature()` for smart accounts | **A** | `AuthRequired::{Proof, Custom{vk_hash}}` + `Authorization::{Proof, Custom, Bearer, Token}` (`action.rs:215`; `permissions.rs:5`). Stronger: proofs/tokens/bearer-chains are first-class auth, not a signature-shaped escape hatch. |
| **ERC-777** reactive hooks | `tokensReceived` callback on transfer | **A** | **Reactor** — `filter()`/`react()` → `ReactionPlan`, cap-gated (`app-framework/src/reactor.rs:209`). Stronger: reactions desugar to ordinary kernel Effects the proof already covers; no reentrancy surprise (777's hooks were a notorious reentrancy vector). |
| **ERC-4337** account abstraction | UserOps, bundlers, EntryPoint, paymasters | **A (partial)** | Caps *are* account abstraction — auth is data, delegation/session-keys are attenuated caps. `invoke()` is the command front-door, no privileged EntryPoint (`app-framework/src/invoke.rs:325`). **Lesson half:** the *paymaster UX pattern* (sponsored fees) is worth importing — see §3. |
| **EIP-7702** set-EOA-code | EOA temporarily delegates to contract code | **A** | This is Ethereum *retrofitting capabilities onto accounts*. dregg never had ambient EOAs to retrofit; delegation is native (`Effect::SpawnWithDelegation`, `action.rs:1081`). Validates the direction of travel. |
| **ERC-4626** tokenized vault | standard deposit/withdraw/share-price | **A (sketch)** | Vault capacity (`cell/src/vault.rs`) + **derived cells** for share accounting (`cell/src/derived.rs`). Honest status: vault is a *factory-wired Rust sketch* (forge-detector tests), not yet an individually-proven Lean rung. The *standard interface* lesson (§3) applies hard here. |
| **ERC-3643 / ERC-1404** permissioned tokens | transfer restricted by on-chain identity/whitelist | **A** | Caveat-gated transfer: `CapabilityCaveat::Witnessed(WitnessedPredicate)` with `MerkleMembership`/`NonMembership`/`Dfa` (`cell/src/predicate.rs:128`,`231`). Stronger: the predicate is a *witnessed proof*, not a mutable on-chain whitelist read. |
| **ERC-6551** token-bound accounts | give an NFT a smart-account wallet | **A** | Cells own cells natively: `SpawnWithDelegation`/`RefreshDelegation`/`RevokeDelegation` (`action.rs:1081`). Stronger: 6551 is an *add-on registry* bolting an account onto an NFT; here every cell already is an account that can hold caps and spawn children. |
| **ERC-7521 / ERC-7683** intents | declarative intents + solver settlement | **A (partial)** | Conditional/eventual turns, guarded holes, promise pipelining (Partial-Turn epoch: `turn/src/{eventual,conditional,pending}.rs`); escrow/blueprint settlement (`cell/src/blueprint.rs`). **Lesson half:** the *standard intent struct* (one `GaslessCrossChainOrder` any solver fills) is a social-coordination win — see §3. |
| **ERC-2612** permit (gasless approve) | sign an approval off-chain, relay on-chain | **A** | Bearer caps + `Authorization::Token`/`Stealth` already separate "authorize" from "who pays/relays" (`action.rs:237`,`394`,`431`). |
| **ERC-5192 / ERC-4973** soulbound | non-transferable tokens | **A** | A cell whose transfer facet is `Impossible`, or a cap with no `EFFECT_TRANSFER` bit (`facet.rs`). Attenuation makes "can't move this" a one-line facet. |
| **ERC-5805 / Governor / OZ-Governance** on-chain governance | votes, proposals, timelocks | **B** | dregg has threshold auth (`Authorization::Custom` threshold-sig predicate, `action.rs:325`) and governed namespaces (`cell/src/state.rs`), but **no standard governance interface**. A real lesson — see §3. |
| **EIP-1559** fee market | base-fee burn + priority tip | **C / B** | dregg meters `computron` transfers (`action.rs:969`) but has no congestion-priced fee market. Mostly N/A (no global mempool auction), but the *predictable-fee UX* goal is worth a glance. |
| **ERC-4844** blob space / DA | cheap rollup data availability | **C** | Chain-scaling concern; dregg's proof-carrying model sidesteps the DA-for-rollups framing. N/A. |
| **EIP-2930 / 4844 / 7702 tx types** | EVM tx plumbing | **C** | EVM-specific. N/A. |
| **ERC-7579 / ERC-6900** modular smart-account modules | plug-in validators/executors for accounts | **B** | The *module registry + standard validator interface* idea maps onto dregg's `Custom{vk_hash}` verifiers — but there's no agreed registry/namespace. A lesson for the standard-interface library (§3). |

**Reading of the table:** the overwhelming majority of the *capability/account/
interface* ERCs are **already-native and structurally stronger** in dregg —
precisely because they are Ethereum re-deriving object-capability properties one
patch at a time (4337, 1271, 6551, 7702, 2535 are all "make this account/object
behave like a capability"). dregg started there. The **(B) lessons are almost
all at the *social/standardization* layer**, not the mechanism layer:
governance interfaces, intent structs, module registries, paymaster UX. That is
the real finding.

---

## 3. Recommendations — what to learn / adopt, ranked

The pattern across the survey: dregg wins the *mechanism* and trails the
*coordination*. The recommendations are ranked by leverage.

### R1 — A "Dregg Standard Interfaces" library (THE lesson) ★★★★★

**What it is.** ERCs are not mostly *technology* — they are *social contracts*. The
reason a token deployed by a stranger shows up correctly in every wallet is that
"ERC-20" names an agreed `InterfaceDescriptor`. dregg has the *mechanism* for this
already — `InterfaceDescriptor` is content-addressed by a sorted-Poseidon2 root
over its method signatures (`cell/src/interface.rs:214`,`246`) — but there is **no
agreed *set* of canonical interface descriptors**. Every app invents its own
method symbols, so nothing interops by default.

The recommendation: publish a versioned, frozen registry of canonical
`InterfaceDescriptor`s — `DSI-1 Fungible`, `DSI-2 Unique/NFT`, `DSI-3 Vault`,
`DSI-4 Governed`, `DSI-5 Interface-Detection`, etc. — each a fixed `interface_id`
(its Poseidon2 root) with a stable method list, a reference Lean rung where
relevant, and a reference Rust impl. Plus the *process*: a lightweight DSI
proposal track (the ERC Magicians/EIP-process lesson) so the set grows by social
consensus, not by fiat.

**Why it helps dregg.** This is the single highest-leverage adoption move. Today a
wallet cannot know that an arbitrary cell "is a fungible token" without
app-specific knowledge. With DSI, any wallet/indexer/app can call
`InterfaceDescriptor::route_method` against a known `interface_id` and interoperate
with a cell it has never seen — exactly the property that made ERC-20 the
substrate of an ecosystem. It directly serves the Pug/stranger-usable bar.

**How it lands on dregg's primitives.** Zero new kernel surface. A DSI is *just* a
canonical `InterfaceDescriptor` value (`interface.rs:214`) plus its `interface_id`
constant. `derive_replayable` (`interface.rs:294`) already lifts a cell's
`CellProgram::Cases` guards into `MethodSig`s, so conformance is *checkable*: a
cell conforms to DSI-N iff its descriptor's root matches. Ship them as a
`dregg-std-interfaces` crate of constants + conformance checks; the social
process is docs + a HORIZONLOG track.

### R2 — Standardize the asset/vault/governance interfaces specifically ★★★★☆

**What it is.** Pick the three highest-traffic ERCs — **ERC-20 (fungible)**,
**ERC-4626 (vault)**, **ERC-5805/Governor (governance)** — and ship their dregg
equivalents as first DSIs, *closing the honest gaps the survey found*: the vault
capacity is currently a factory-wired Rust sketch (`cell/src/vault.rs`, no
individual Lean rung) and governance has threshold auth but no standard
interface.

**Why it helps dregg.** These three are where "already-native (sketch)" and "(B)
lesson" cluster. Promoting vault and governance from sketch/ad-hoc to a proven
rung + standard interface turns a hand-wave into an interoperable, attested
primitive — and gives the strongest concrete demos of "dregg does what DeFi does,
soundly."

**How it lands.** Vault → finish the Lean rung à la the already-proven
`Deos/{Membrane,DerivedCell,SealedEscrow,StandingObligation}.lean` family, with
share accounting as a **derived cell** (`derived.rs`) so share-price is a
verifiable function of reserves — strictly stronger than ERC-4626, which has had
real-world inflation/donation share-price exploits that a *proven* derived-cell
invariant rules out. Governance → a DSI over the existing threshold
`Authorization::Custom` predicate (`action.rs:325`) + governed namespaces
(`state.rs`), no new effect.

### R3 — Adopt the paymaster / sponsored-fee UX pattern ★★★★☆

**What it is.** ERC-4337's most-loved *product* feature is the **paymaster**:
someone other than the actor pays the fee, enabling gasless onboarding and
"pay fees in any token." dregg already *separates authority from who-relays* —
bearer caps, `Authorization::Token`/`Stealth` (`action.rs:237`,`394`,`431`) mean
the signer need not be the fee-payer — but there is no *named, standard* sponsor
pattern at the app layer.

**Why it helps dregg.** Onboarding UX is where adoption lives or dies. "Click and
it just works, someone else covered the computrons" is the AOL-wonder bar. The
mechanism exists; what's missing is a blessed pattern so wallets implement it
uniformly.

**How it lands.** A standard "sponsor" Reactor (`reactor.rs:209`) that observes an
unfunded `invoke()` and supplies the `computron` `Transfer` (`action.rs:969`)
under a faceted, rate-limited cap (allowance capacity, `cell/src/allowance.rs`).
This is pure app-layer composition over existing Effects — no kernel change — and
it lands as another DSI ("DSI-Sponsor").

### R4 — A standard intent struct + solver settlement interface ★★★☆☆

**What it is.** ERC-7683's win is *one* `GaslessCrossChainOrder` struct that any
solver can fill — a shared shape, not new tech. dregg has the deeper machinery
(conditional/eventual turns, guarded holes, promise pipelining; escrow/blueprint
settlement, `cell/src/blueprint.rs`) but no *agreed intent envelope* a third-party
solver can discover and fill.

**Why it helps dregg.** Intents are the frontier of Ethereum UX; a standard intent
DSI lets a marketplace of solvers form around dregg's *provably-settled* escrow —
which is stronger than ERC-7683 (settlement is proof-carrying and atomic via
`SealedEscrow`, not solver-trust + dispute windows).

**How it lands.** A DSI intent interface over the existing
`conditional`/`eventual`/`pending` turn fragments and the blueprint escrow
factory; the "fill" is an ordinary multi-party atomic turn (`atomic.rs:89`). No
new kernel surface — codify the envelope shape and the solver-facing method set.

### R5 — Borrow the standardization *process*, not just the standards ★★★☆☆

**What it is.** The durable lesson is meta: Ethereum's edge is the **EIP/ERC
process** — numbered proposals, a Magicians forum, reference implementations,
"Final/Draft/Stagnant" lifecycle, social ratification. dregg has rigorous *proofs*
but no public *proposal track* for cross-app conventions.

**Why it helps dregg.** Proofs make a primitive *sound*; a process makes it
*adopted*. The standard-interface library (R1) only stays alive if there's a
lightweight way for a stranger to propose DSI-N and have it ratified. This is the
"works without ember in the loop" property at the ecosystem scale.

**How it lands.** A `docs/dsi/` track mirroring `docs/reference/` discipline:
each DSI is a doc grounded to a frozen `interface_id` + reference impl + (where
load-bearing) a Lean rung, with a Draft→Final lifecycle. Cheap; pure
documentation + a registry crate.

### Ranked summary

1. **R1 — Dregg Standard Interfaces library** (the core ERC lesson; mechanism
   exists, social set is missing). ★★★★★
2. **R2 — Standardize fungible/vault/governance first**, closing the vault-sketch
   and governance-interface gaps. ★★★★☆
3. **R3 — Paymaster/sponsored-fee UX pattern** as a standard Reactor. ★★★★☆
4. **R4 — Standard intent envelope + solver interface** over existing settlement.
   ★★★☆☆
5. **R5 — Adopt the EIP-style proposal *process*** so the standard set grows by
   consensus. ★★★☆☆

Every recommendation lands as **app-layer / documentation work over existing
primitives** — none touches the kernel, the effect set, or the VK. That is itself
the verdict: dregg's *protocol* has already internalized the hard lessons the ERC
corpus spent a decade discovering; the work that remains is the *coordination
layer* Ethereum is still best-in-class at.

---

## Appendix — primary code anchors (verify against HEAD)

- Effects / authorization: `turn/src/action.rs` (`Effect` enum @962; `Authorization` @215; `Mint` @1407, `Burn` @1283)
- Capabilities + attenuation lattice: `cell/src/capability.rs` (`CapabilityRef` @42; `is_attenuation` @779)
- Facets: `cell/src/facet.rs` (effect masks @36; `is_facet_attenuation` @136; `EFFECT_MINT` @106, `EFFECT_BURN` @73)
- Auth lattice: `cell/src/permissions.rs:52` (`is_narrower_or_equal`)
- Predicates / caveats: `cell/src/predicate.rs` (`WitnessedPredicate` @128; `WitnessedPredicateKind` @200)
- Conservation Σδ=0: `turn/src/executor/atomic.rs:1297`; `turn/src/executor/proof_verify.rs:1220`; `AssetId := issuer` @`atomic.rs:247`
- Interfaces: `cell/src/interface.rs` (`InterfaceDescriptor` @214; root @246; `derive_replayable` @294; `route_method` @361)
- App layer: `app-framework/src/invoke.rs:325`; `app-framework/src/reactor.rs:209`
- House capacities: `cell/src/{membrane,derived,escrow_sealed,obligation_standing,vault,allowance,blueprint}.rs`; `docs/deos/HOUSE-CAPACITY-FRAMEWORK.md`
- Notes (shielded value): `cell/src/note.rs:40`
- Delegation / cells-own-cells: `turn/src/action.rs:1081` (`SpawnWithDelegation`/`RefreshDelegation`/`RevokeDelegation`); `cell/src/delegation.rs`, `cell/src/revocation_channel.rs`
- Light client (whole-history, unfoolable): `lightclient/src/lib.rs`; `circuit-prove/src/ivc_turn_chain.rs`
