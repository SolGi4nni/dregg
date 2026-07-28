# MUTUAL PROOF SYSTEMS — landscape + honest novelty assessment

> ## ⚑ CORRECTED 2026-07-27 — this document's central novelty claim was FALSE and has been RETRACTED
>
> As first written (2026-07-27, morning) this document claimed dregg had **the first and only
> verified-in-Lean Kimchi verifier, "at any fidelity."** That is **refuted by public prior art
> that predates ours by roughly four weeks.** It also carried a **fabricated numeric citation**
> ("~34.4 billion MSMs"), a **field assignment inverted** from its own source, and a **"no prior
> system" absence claim** that two public repositories refute.
>
> Evidence and per-claim verdicts: `docs/AUDIT-IMPORTER-AND-DOCS.md` (commits `d7dcbf5d2`,
> `14b4475b5`). Every correction below was **re-verified first-hand** during this pass — against
> `gh api` and a local clone of `l-adic/snarky`, a live fetch of the =nil; page, and the
> `~/dev/proof-systems` / `~/dev/mina` / `~/dev/mina-rust` checkouts — not taken on the audit's word.
>
> **A reader who saw the earlier version should treat its §5(b) and its "Bottom line" as
> withdrawn.** Corrections are marked inline as **[CORRECTED 2026-07-27]**; claims that could not
> be checked are marked **[UNVERIFIED]** rather than left reading as established. This pass only
> ever weakened or corrected: no claim here was strengthened, and where a correction leaves a
> thesis unsupported the doc now says so instead of finding a new argument for it.

*A cited survey of the research + practice landscape around the directions dregg is exploring:
mutual (bidirectional) proof verification, cross-proof-system verification, recursive
composition / IVC, Mina-in-Mina / Zeko, and — the point of the exercise — what is genuinely
**novel** about dregg's directions versus what re-treads known ground.*

**Scope of "dregg's directions" as read from the repo (not restated from memory):**
- dregg is a **BabyBear STARK (Plonky3 / FRI)** with a **Lean-authored/generated AIR** (House Law #1: constraints are EMITTED from Lean, never hand-written in Rust; `circuit/src/field.rs`, `circuit/src/lib.rs`, `GOAL-STARK-KILL.md`). Its STARK security rests on an **undischarged FRI/STARK soundness floor** (`docs/reference/CHAIN-INVENTORY-GROUNDED.md:28`, quoted in full: *"FRI extraction floor — undischarged (no adversary model; the bit-count is a density reading, NOT a soundness bound)"*) — describe everything below at that resolution. **[CORRECTED 2026-07-27]** the earlier version elided *"the bit-count is a density reading, NOT a soundness bound"* from this quote, and the cut ran toward this doc's own point (audit F-D8).
- **What already ships as cross-proof-system verification:** a **BabyBear FRI/STARK verified inside a BN254 Groth16 circuit** — the gnark "wrap"/shrink (`chain/gnark/settlement_circuit.go`, ~12M-R1CS in-circuit FRI/STARK verifier; `circuit-prove/src/apex_shrink*.rs`), used for on-chain settlement. And **STARK-in-STARK IVC** for whole-history recursion — dregg verifying *itself* (`lightclient/src/lib.rs`, `grain-verify/src/r3.rs`, Lean `RecursiveAggregation.lean` / `r3_unfoolable`).
- **What is mutual and realized:** the **"true peers"** set — dregg ↔ **{ETH/Base, Cosmos, Solana, Midnight}** (`docs/TRUE-PEERS-ARCHITECTURE-2026-07-26.md`, `chain/contracts/DreggPeerRegistry.sol`). dregg verifies each chain's **consensus** (a Lean "no-forgery" theorem per chain: `eth_no_forgery`, `tmNoForgery`, `sol_no_forgery`, `mid_no_forgery`); each chain verifies dregg's **Groth16-wrapped STARK**. *Mutual, but consensus-verification + STARK-settlement — NOT two proof systems verifying each other.*
- The Mina work is the two-directional, *cross-proof-system* bet (`docs/MINA-KIMCHI-VERIFIER-PLAN.md` §"Two directions"):
  - **INWARD** — verify a **Mina Kimchi/Pickles-over-Pasta** proof *inside dregg* (a Lean-emitted Kimchi verifier: `metatheory/Dregg2/Circuit/Emit/KimchiVerify.lean`, exercised against a **real** o1-labs proof in `metatheory/Dregg2/Circuit/Emit/KimchiRealProofGate.lean`).
  - **OUTWARD** — settle **dregg's** state to Mina as a **Pickles-verifiable proof** Mina checks cheaply.
  - Together: **BabyBear-STARK ↔ Kimchi/Pickles-over-Pasta, mutual** — two chains with **different native proof systems** each verifying the other.
- **Honest status today** (`docs/MINA-REALITY-GATE.md`): INWARD reproduces the reference Kimchi verifier's exact intermediate scalars over the real 255-bit Pasta field (C8 `combined_inner_product`, C5 `ft_eval0`), composed into one in-kernel accept `kimchiVerifyDecisionField` — **modulo three named crypto carriers** (C3 Fr-sponge values, C6 custom-gate token streams, C9 IPA `msm==0`). It **does not verify Mina** yet. OUTWARD *to Mina* is a plan (though OUTWARD *to the EVM* — the STARK-in-Groth16 wrap — ships). So a *Mina↔dregg* "mutual, end-to-end" loop is a **target, not a shipped fact**; the novelty below is assessed as *the direction*, with that caveat stated wherever it bites.
- **A discipline point worth recording:** dregg already **deleted** a Rust Mina bridge that *looked* like mutual recursion — the "Level 2" pipeline (BabyBear STARK verified inside a Kimchi circuit, wrapped via Pickles into a Mina zkApp proof) was removed because *"its pickles step never verified the Kimchi proof in-circuit, so the recursion was vacuous scaffolding"* (`bridge/src/mina.rs`; it is now observation-only). This is the honest register the novelty claims below must keep — a wrapper that doesn't actually verify the inner proof is not cross-proof-system verification, it's plumbing.

---

## Query 1 — Mutually-proof-based systems (two chains verify EACH OTHER's proofs)

**The distinction that matters:** "bidirectional" is common; **"bidirectional across *different* proof systems"** is not. Almost every bidirectional design uses the **same construction in both directions**.

- **Cosmos IBC — mutual light clients, same proof system.** The canonical mutual design: each chain runs a light client of the counterparty, so a connection is a *pair* of light clients, one per chain. Both sides run the **Tendermint/CometBFT** client — same construction each way; it is *trust-minimized, not trustless* (safety inherits both chains' safety).
  - <https://ibc.cosmos.network/main/ibc/light-clients/tendermint/overview/> · <https://github.com/cosmos/ibc-go/wiki/Light-clients>
  - IBC does support *heterogeneous* pairings (e.g. a Tendermint client on Ethereum + an Ethereum client on Cosmos), but each client verifies **consensus/state roots**, not a ZK proof, and the two clients are independent constructions — not "each verifies the other's proof system."

- **zkBridge (Polyhedra) — bidirectional, but same zk-SNARK construction each way.** A block-header relay + updater contract on the receiver chain; run in both directions it is symmetric. It is a **SNARK light client**, not two proof systems checking each other.
  - Paper: *zkBridge: Trustless Cross-chain Bridges Made Practical* — <https://arxiv.org/pdf/2210.00264> · Docs: <https://docs.zkbridge.com/>

- **Succinct Telepathy — the closest thing to a live bidirectional ZK bridge.** Demonstrated a **bi-directional** bridge (Goerli ↔ Gnosis) via "proof of consensus." Still one construction (a SNARK proving Ethereum's light-client protocol) mirrored, not two heterogeneous provers.
  - <https://hackmd.io/@succinctlabs/SytMDX6Jh>

- **Mina "Proof of Everything" / internet of proofs — appchains "verify each other," but all inside one proof system.** Mina's framing is that its recursive ZKPs "enable a network of appchains and Layer 2s that can verify each other," each inheriting the "proof of everything" property. But every participant is **Kimchi/Pickles over Pasta** — this is *mutual within one system*, the strongest existing analog to what dregg wants, and precisely why it is not the same claim. The Mina blog does **not** claim Mina verifies foreign (STARK/other-system) proofs.
  - <https://minaprotocol.com/blog/reintroducing-mina>

**Where dregg's *realized* mutual sits.** dregg's shipped "true peers" (dregg ↔ ETH/Base, Cosmos, Solana, Midnight) is a **mutual** design — dregg verifies each chain's consensus (Lean no-forgery theorem), each chain verifies dregg's Groth16-wrapped STARK. But this is structurally the **IBC family**: dregg light-clients foreign *consensus*, foreign chains verify a dregg *settlement proof*. Neither side verifies the other's **ZK proof system**, because ETH/Cosmos/Solana/Midnight don't expose one to verify. It is a real, symmetric, proof-backed bridge — and it is **not** the cross-proof-system claim. That claim is reserved for the (unbuilt) Mina pairing.

- **⚑ Kimchi/Pickles inside a foreign zkVM, and foreign zkVM proofs inside Kimchi — BOTH legs exist publicly, and one is o1-labs' own.** **[CORRECTED 2026-07-27 — this bullet did not exist in the earlier version, and its absence is what made the Query-1 finding below overstate.]**
  - **`o1-labs/o1js-to-zkvm`** (not a fork; last pushed 2026-05-31) — README verbatim: *"Verify a pickles proof (Mina blockchain SNARK or any compatible kimchi-wrap recursive proof) inside the SP1 zkVM."* Its layout names a `crates/pickles-verifier` covering *"kimchi wrap + stage-1 deferred + stage-2 accumulator."* **Kimchi/Pickles verified inside a STARK zkVM, by the company that builds Kimchi.** (`Nori-zk/o1js-to-zkvm`, pushed 2026-06-19, is a fork of it.)
    <https://github.com/o1-labs/o1js-to-zkvm>
  - **`Nori-zk/proof-conversion`** (fork of `geometers/o1js-blobstream`; pushed 2026-07-13) — README verbatim: *"enables verification of **PLONK** and **Groth16** proofs generated by **SP1**, **RISC Zero zkVMs** and **Snarkjs** inside **o1js** circuits."* **A foreign proof system verified inside Kimchi.**
    <https://github.com/Nori-zk/proof-conversion>
  - Both READMEs were pulled directly via `gh api` during this pass (a prior lane in this workstream had a WebFetch return invented file contents, so page-fetching was not trusted here). What is **[UNVERIFIED]**: whether either runs on mainnet, and whether any single deployed system runs *both* legs between the same chain pair. Neither is claimed.

**Finding for Query 1 — [CORRECTED 2026-07-27]. The strong form is RETRACTED.**

The earlier version said: *"I found **no prior system** where two chains with different native proof
systems each natively verify the other's proofs in both directions."* **That is refuted.** Both legs
of exactly that pair exist publicly and separately — Pickles-inside-SP1 (o1-labs' own repo) and
SP1/RISC0-inside-o1js (Nori-zk) — so the individual directions are not unclaimed, and one of them was
built by Kimchi's own authors.

What survives is the **weak** form, and it is the only one this doc should ever have printed:
everything *mutual* found by this survey is either (i) same-system light clients (IBC, zkBridge,
Telepathy — and dregg's own "true peers" is in this family), or (ii) same-system recursion (Mina's own
appchain mesh); the heterogeneous work found is **one-directional per artifact**. So a **single system
running both directions across different native proof systems** is an **under-populated cell** in what
this survey found — an unbounded absence claim, worth exactly what the search behind it is worth, and
**not** a first-of-kind claim. dregg has closed *neither* direction of the *Mina* pairing end-to-end.

---

## Query 2 — Cross-proof-system verification (one proof system inside another)

This cell is **well-populated but almost entirely one-directional** (wrap / aggregate a foreign proof into a single verifiable form). The Kimchi↔EVM literature is the direct precedent for dregg's INWARD direction.

- **=nil; Foundation — Placeholder wrapping Kimchi.** Mina's Kimchi state proof is too expensive to verify directly on the EVM, so =nil; wraps the **Kimchi verification algorithm** in a **Placeholder** (their FRI/PLONK-style) proof and verifies *that* on-chain.
  **[CORRECTED 2026-07-27 — a FABRICATED figure was deleted from this bullet.]** The earlier version
  read: *"They quote the cost of the wrapped Kimchi verification at ~**34.4 billion MSMs** … (the
  **only** prior cryptographic Kimchi-wrap; **cited in dregg's own plan as the cost reference**)."*
  **All three of those are false.** The =nil; page contains no "34.4 billion" and no "billion" at all
  — I refetched it during this pass and searched the rendered text; the only literal `34.4` on the
  page is a coordinate inside an SVG logo path. dregg's plan does not cite the figure either:
  `MINA-KIMCHI-VERIFIER-PLAN.md:74`'s actual number is *"a **65536-element non-native Vesta MSM ≈
  10^7–10^8 gates**."* And the unit is incoherent on its face — MSMs are operations, not a cost.
  The audit's forensics add that the string appears in **no tool result** in the authoring
  transcript; it first appears in the authoring agent's own `Write` call.
  **The page's real, verified-in-context figures** (all fetched and read this pass):
  - **`3594270` gas** for a single on-chain Placeholder verification — *"Leading verification cost
    gets brought by these two MSMs, so in total they would roughly consume: `1828050 + 1766220 =
    3594270` gas"*, against a stated `5000000` gas limit, and explicitly *"a very rough estimation."*
    The two MSMs are of size **2^18** and **2^17**.
  - **`401080320` constraints** — the page's estimate of what the **R1CS alternative** would have
    cost (`2^18 × 255 × 6`), i.e. the thing Placeholder was invented to avoid. It is *not* the
    Placeholder circuit's size; do not quote it as one.
  - *"the **only** prior cryptographic Kimchi-wrap"* is **[UNVERIFIED]** — no exhaustive search
    backs the word "only"; it is now dropped from the claim rather than repeated.
  - <https://nil.foundation/blog/post/mina-ethereum-bridge> · <https://blog.nil.foundation/2022/06/28/mina-integration.html> · <https://nil.foundation/blog/post/proof-market>
  - **[CORRECTED 2026-07-27]** =nil; is filed here as one-directional, but **the second URL this doc
    itself supplies describes a bidirectional design**: that page is subtitled *"How will a Mina
    Protocol's bridge become **bi-directional**?"* and specifies the ETH→Mina leg as *"'Wrap' the
    state/query proof (generated with the Placeholder proof system) by implementing the verification
    algorithm as a **Kimchi circuit**"* — a published **2022** design for the cell this doc calls
    under-populated. The honest distinction is **conceived vs built**: both `NilFoundation` repos are
    archived and it was never built. Drawing that line is mandatory — a reviewer would otherwise
    sink the claim with a link this document handed them.

- **lambdaclass `mina_bridge` → Aligned Layer verifies Kimchi.** Mina Proof-of-State (Kimchi) proofs are submitted to **Aligned Layer** operators, which run a Kimchi verifier off-chain and attest on Ethereum. **One-directional** (Mina→ETH); no STARK/gnark in the path; Ethereum is not verified on Mina.
  - <https://github.com/lambdaclass/mina_bridge>

- **NEBRA UPA — universal proof aggregation.** Recursive SNARKs aggregate proofs **from different circuits/systems** (zkEVMs, zkVMs, SP1) into one on-chain verification. This is the strongest "heterogeneous proofs, one verifier" system in production — but it **aggregates into a single BN254 verifier**, it does not have two systems verify *each other*.
  - <https://docs.nebra.one/introduction/what-is-nebra-upa> · <https://github.com/NebraZKP/upa> · SP1 support: <https://blog.nebra.one/succinct-sp1-support-on-nebra-upa/>

- **zkVM STARK→SNARK wrap (SP1, RISC Zero).** Both prove over a STARK (RISC-V trace) and **wrap the final STARK into a Groth16/PLONK SNARK** for cheap on-chain verification. This is *self*-system wrapping (their own STARK → their own SNARK), and verifying a **foreign** proof inside the zkVM is documented as awkward/limited.
  - Auditor's guide (STARK→SNARK wrap): <https://blog.sigmaprime.io/sp1-zkvm-security-guide.html>
  - RISC0 "unable to verify starks/snarks inside the zkvm": <https://github.com/risc0/risc0/issues/1267>

- **STARK-in-SNARK, concretely (Circle STARK → gnark Groth16).** Herodotus's `stwo-gnark-verifier` ports the **Stwo Circle-STARK verifier into a gnark Groth16/PLONK circuit** — a real "verify one proof system inside another" artifact, and the closest public analog to dregg's **OUTWARD** (wrap a STARK for a foreign verifier). Again one-directional.
  - <https://github.com/HerodotusDev/stwo-gnark-verifier> · recursive Groth16+PLONK verifier: <https://github.com/succinctlabs/snark-bn254-verifier>

- **FRI-in-SNARK / hybrid recursion primitives.** Plonky2 (PLONK + FRI over Goldilocks) and Boojum (zkSync) make *verification itself a provable computation*, enabling FRI-proof-in-circuit recursion; STARKPack aggregates **heterogeneous FRI-based** proofs (e.g. ethSTARK + Plonky2) in one argument.
  - Plonky2: <https://polygon.technology/blog/introducing-plonky2> · STARKPack: <https://www.nethermind.io/blog/starkpack-aggregating-starks-for-shorter-proofs-and-faster-verification> · amortization for FRI-SNARKs (eprint 2024/661): <https://eprint.iacr.org/2024/661>

- **Curve-cycle / field-mismatch literature (the reason cross-system is hard).** Cross-system verification runs into a field/curve mismatch.
  **[CORRECTED 2026-07-27 — the earlier sentence was self-refuting.]** It read: *"a Vesta-proof
  verifier circuit lives over Pallas's scalar field, so all **Fq** arithmetic is non-native and
  emulated"* — but **Pallas's scalar field IS Fq**, so that sentence says Fq arithmetic is non-native
  in a circuit whose native field is Fq. The error was inherited from `KIMCHI-VERIFY-SPEC.md` §0,
  which had the Pasta field assignment inverted (audit F-D1; both are fixed as of this pass).
  Sourced correctly, from `~/dev/proof-systems/curves/src/pasta/curves/vesta.rs:21-22` —
  `type BaseField = Fq; type ScalarField = Fp` (and `pallas.rs:21,23` is the mirror,
  `BaseField = Fp; ScalarField = Fq`): a circuit doing **Vesta** group operations natively must live
  over Vesta's **base** field **Fq** — which is Pallas's *scalar* field — so Vesta point coordinates
  are native and it is **Fp** (Vesta's scalar field: the challenges and polynomial evaluations) that
  is non-native and emulated. Note this describes the **Pickles** arrangement, not dregg's: dregg's
  K5 emits over **BabyBear**, where *both* Pasta fields are non-native (9×30-bit limbs,
  `PastaField.lean:138-140`). **Authoritative source for this fact is the Lean, not this doc** —
  `Dregg2/Circuit/Emit/PastaField.lean:120-132` has always named `pN` correctly as *"the Pallas base
  / Vesta scalar prime"*, and `KimchiVerify`/`KimchiRealProofGate` run over `ZMod pN`. Only the two
  prose docs were wrong. Foundational reading:
  - Pasta 2-cycle (Pallas/Vesta) as used by Pickles: <https://o1-labs.github.io/proof-systems/pickles/overview> **[CORRECTED 2026-07-27 — link repaired.]** The URL previously printed here (and again under Query 3) ended in `.html` and returns **HTTP 404**; I re-verified both the 404 and that dropping `.html` returns 200.
  - *Embedded Curves and Embedded Families for SNARK-Friendly Curves* (eprint 2024/1737): <https://eprint.iacr.org/2024/1737.pdf>
  - Mozak, *A Recursive zk-based State Update System* (eprint 2024/1402) — recursive/heterogeneous state proofs: <https://eprint.iacr.org/2024/1402.pdf>

**Finding for Query 2.** Verifying Kimchi inside another system is **prior art** (=nil; Placeholder is the direct precedent; Aligned/lambdaclass verify it off-chain). Verifying a STARK inside a SNARK is **prior art** (stwo-gnark). What is *not* prior art: doing the Kimchi-verify side as a **Lean-authored/emitted** circuit with machine-checked forcing (see Query 5b), and pairing it with the reverse direction into a mutual loop (Query 1).

---

## Query 3 — Recursive proof composition / IVC / folding (the theory dregg's deferral sits in)

dregg's Kimchi plan explicitly sits in this line: K5's key move is to **defer the dominant MSM** rather than verify it in-circuit — the same "accumulate now, check once at the end" idea that IVC/accumulation formalizes (`MINA-KIMCHI-VERIFIER-PLAN.md` §"K5 design crux": *Pickles DEFERS the 65536-element Vesta MSM via the `sg` split, accumulated across recursion, checked once*).

**Theory line (cite the roots, not the blog posts):**
- **Valiant, IVC (TCC 2008)** — the origin of incrementally verifiable computation; 2019 TCC Test-of-Time. <https://link.springer.com/chapter/10.1007/978-3-540-78524-8_1>
- **Chiesa–Tromer, Proof-Carrying Data (ICS 2010)** — PCD, the DAG generalization of IVC for mutually distrustful parties. <https://people.csail.mit.edu/alexch/research/pcd/pcd-ics.pdf>
- **Bitansky–Canetti–Chiesa–Tromer, Recursive Composition & Bootstrapping for SNARKs and PCD (STOC 2013 / eprint 2012/095)** — recursion-of-SNARKs ⇒ PCD ⇒ IVC. <https://eprint.iacr.org/2012/095.pdf>
- **Valiant's conjecture / IVC-from-random-oracles impossibility (eprint 2022/542)** — the negative-result boundary (relevant to any "just recurse the hash" claim, and to dregg's FRI-floor honesty). <https://eprint.iacr.org/2022/542>

**Accumulation / no-trusted-setup recursion (the line dregg's deferral is in):**
- **Halo — recursive proof composition without a trusted setup (Bowe–Grigg–Hopwood, eprint 2019/1021)** — amortize IPA verification; the nested-amortization idea dregg's MSM-deferral mirrors. <https://eprint.iacr.org/2019/1021.pdf>
- **Bünz–Chiesa–Mishra–Spooner, Proof-Carrying Data from Accumulation Schemes (eprint 2020/499)** — formalizes accumulation; the theory under Halo2/Pickles-style deferral. <https://eprint.iacr.org/2020/499>
- **Pickles (Mina)** — inductive Kimchi-in-Kimchi over the Pasta cycle; Step/Wrap circuits; the deferred-`sg` accumulator dregg's K5 targets. <https://o1-labs.github.io/proof-systems/pickles/overview> **[CORRECTED 2026-07-27 — the `.html` form printed here was a 404.]**

**Folding schemes (the modern IVC branch):**
- **Nova (Kothapalli–Setty–Tzialla)** — IVC from folding relaxed R1CS. <https://github.com/microsoft/Nova>
- **SuperNova (eprint 2022/1758)** — non-uniform IVC (per-instruction circuits). <https://eprint.iacr.org/2022/1758.pdf>
- **HyperNova (eprint 2023/573)** — folding for CCS (customizable constraint systems). <https://eprint.iacr.org/2023/573.pdf>
- **PCD from multi-folding (eprint 2023/1282)**, **MicroNova — on-chain-efficient folding (eprint 2024/2099)**, **PCD via Holography Accumulation (eprint 2026/538)** — the frontier. <https://eprint.iacr.org/2023/1282> · <https://eprint.iacr.org/2024/2099.pdf> · <https://eprint.iacr.org/2026/538>

**dregg's own position in this line (from the repo).** dregg *implements* IVC as **STARK-in-STARK** recursion today (`circuit-prove/src/ivc_turn_chain.rs`: fold finalized turn proofs into one running recursive proof, binding `prev.NEW_COMMIT == next.OLD_COMMIT`). It **surveyed folding and deliberately declined it**: `docs/deos/FOLDING-RECURSION-PRIMER.md` reviews Nova / SuperNova / HyperNova / ProtoStar / ProtoGalaxy / NeutronNova / LatticeFold and rejects adoption because folding collides with **"TWO things dregg deliberately chose"** — *"post-quantum safety and the small (BabyBear) field"* (**[CORRECTED 2026-07-27]** — the earlier version cut *"TWO things dregg deliberately chose"* from this quote; audit F-D8, and like the other elision it cut toward this doc's point), flagging **LatticeFold/LatticeFold+** (PQ, lattice-based folding) as the future watch item. So dregg is a *conscious non-adopter* of the folding branch — worth stating so nobody frames a folding scheme as dregg's missing piece.
  - LatticeFold (PQ folding) — the watch item: search "LatticeFold post-quantum folding" (eprint 2024/257 and its successor LatticeFold+).

**Finding for Query 3.** dregg's **MSM-deferral / accumulate-and-check-once** (K5) is textbook accumulation-scheme (Halo / BCMS 2020/499 / Pickles). Its shipped IVC is textbook STARK-in-STARK recursion. Both are *correct applications of known techniques*, not new ones. The novelty (if any) is not the deferral or the recursion; it's the substrate they're expressed in (Lean-emitted, forcing-checked) — see Query 5.

---

## Query 4 — Mina-in-Mina / Zeko / internet-of-proofs

- **Zeko — a nested Mina ledger inside a Mina zkApp account.** Zeko is a ZK rollup "isomorphic to Mina": a **nested instantiation of the Mina ledger within a zkApp account on the Mina L1**, an outer-L1 / inner-L2 pair. The sequencer batches L2 account-updates into a **binary tree of transaction SNARKs** composing to one **constant-size root proof** committed to L1 — leveraging **Kimchi/Pickles**'s "arbitrary infinite recursive proof construction." Notably it uses Mina's recursive-proof *capability* to compress transactions; per the docs it does **not** claim to recursively verify Mina's full **consensus** inside itself.
  - <https://docs.zeko.io/architecture/zeko-core-concepts> · <https://minaprotocol.com/blog/bringing-the-mina-stack-to-life-with-zeko>
- **Mina as a settlement/verification layer for "proofs from other systems."** Mina positions L1 as "the natural choice for settlement-only applications that primarily verify proofs from other systems or act as bridges." This is the transitive **internet-of-proofs** bet dregg's INWARD direction rides: *verify Mina ⇒ transitively verify anything that settles a Kimchi proof to Mina.* dregg's own plan flags the transitive set is **small today** but names it as the bet (`MINA-KIMCHI-VERIFIER-PLAN.md` §"INWARD").
  - <https://minaprotocol.com/blog/reintroducing-mina> · Protokit (another Mina L2): <https://zkok.io/mina/protokit/> · recursive zkRollups on Mina: <https://minaprotocol.com/blog/recursive-zkrollups-hazook>

**Finding for Query 4.** "Recursive rollup that settles to Mina" is **solved and in production** (Zeko, Protokit). dregg's OUTWARD (settle dregg to Mina) is *the same idea as a Zeko/Protokit settlement*, except the thing being settled is a **foreign (BabyBear-STARK) system**, not a Mina-native ledger — which is the cross-system twist Zeko does not have (Zeko is Mina-native by construction). The "internet of proofs" framing dregg leans on is **Mina's own marketing framing**, not a dregg coinage — cite it as such.

---

## Query 5 — The novelty question (honest)

Three claims, graded. Rule applied throughout: describe at **current** resolution, and separate *"authored/emitted in Lean with machine-checked forcing + real-proof differential"* (what dregg has) from *"machine-checked soundness of the protocol"* (what the formal-methods line targets) — they are **different guarantees** and conflating them would be the over-claim.

### (a) dregg↔Mina **mutual cross-proof-system** verification — **an under-populated cell as one system; the individual directions are NOT unclaimed. Not demonstrated end-to-end.**
- **[CORRECTED 2026-07-27.]** The earlier version opened *"No prior system has two chains with different native proof systems verify **each other**"* and concluded the pairing was *"unclaimed."* Both legs of a Kimchi↔STARK-zkVM pair exist publicly (Query 1: `o1-labs/o1js-to-zkvm`, `Nori-zk/proof-conversion`). What this survey did not find is a **single system running both directions between the same chain pair** — an unbounded absence claim, hedged as one, and not a first-of-kind claim. Bidirectional designs found are same-system (IBC/zkBridge/Telepathy); Mina's mutual mesh is same-system. The **specific** pairing BabyBear-STARK ↔ Kimchi/Pickles was not found built — which is a much weaker statement than the one this doc used to make.
- **Honest deductions.** (i) INWARD does **not** verify Mina — it is C1+C8+C5 over the real field modulo named crypto carriers (`MINA-REALITY-GATE.md` is the authority on the current carrier count; the "three carriers" figure repeated throughout this doc was accurate when written and may now understate what has been retired — it is **deliberately not updated upward here**, because this pass only weakens). (ii) **OUTWARD is not merely unbuilt — its sibling doc assesses it INFEASIBLE.** **[CORRECTED 2026-07-27]**: this doc said only *"OUTWARD is a plan"* / *"Plan-stage only"*, while `MINA-DREGG-ZKAPP-BRIDGE.md:17` says direction 2 is **"infeasible in-circuit today"** — dregg's proof is a BN254 Groth16, Kimchi has **no pairing gate**, and emulating one blows past the 2^16-row step ceiling by orders of magnitude. Since the whole 5(a) claim is the *mutual* pairing, "assessed infeasible in-circuit" versus "merely unbuilt" is material and the stronger (worse) reading is the sourced one. (iii) Both directions inherit **undischarged opening-soundness floors** (dregg's FRI floor; Kimchi's IPA `msm==0`), so even if wired, "mutual verification" is at that resolution, not unconditional. **Verdict: a direction, not a result — and one whose second leg is currently assessed infeasible, not pending. Claim it as a target, with the carriers, the floors, and the infeasibility named.**

### (b) A **verified-in-Lean Kimchi verifier** — ⚑ **the "first-of-kind" claim is RETRACTED. We are not first. Prior art predates ours by ~4 weeks and reaches further.**

**[CORRECTED 2026-07-27 — this subsection is a full rewrite; the earlier text is withdrawn.]** It
claimed *"genuinely novel; nobody else has one, partial or otherwise"* and *"still a **first** (there
is no other Lean Kimchi verifier at any fidelity)."* **Both halves are false.** Every element below
was pulled first-hand this pass via `gh api` plus a local clone of the repository — not via a fetched
web page, and not on the audit's word.

**The prior art: `l-adic/snarky`, directory `formal/`.**
- `fork: false`, created 2025-11-05, last pushed 2026-07-26. `l-adic` is a one-member org; the member
  is **`martyall` = Martin Allen**, GitHub `company: @o1-labs` — an engineer at the company that
  builds Kimchi. <https://github.com/l-adic/snarky>
- **An executable Lean 4 Kimchi verifier.** `formal/kimchi/Kimchi/Verifier/Kimchi.lean` (27,151
  bytes) defines `kimchiVerify` at line **471**, docstring *"The kimchi verifier transcribed from
  proof-systems `kimchi/src/verifier.rs`."* I downloaded the file and grepped it: **zero `sorry`.**
- **Soundness capstones we do not have.** `formal/kimchi/Kimchi/Verifier/Capstone/Standard.lean` carries `kimchiVesta_sound`
  (:166), `kimchiPallas_sound` (:214), `kimchiVesta_run_sound` (:275), `kimchiPallas_run_sound` (:355);
  `Capstone/Algebraic.lean` carries `kimchiProof_sound_algebraic` and `_ft`; `Capstone/Reflection.lean`
  carries the lifts. The **only** `axiom`s in the capstone chain are the Fiat–Shamir/random-oracle
  assumptions (`kimchi_fiat_shamir_vesta` / `_pallas`, `Reflection.lean:56,73`).
- **They also have** knowledge-soundness of the batched/chunked IPA opening
  (`formal/bulletproof-pcs/Bulletproof/Soundness.lean`), Kimchi gate semantics proved faithful to
  **Mathlib's** elliptic-curve group law (`WeierstrassCurve.Affine`), the permutation/grand-product
  argument, and **five production proof fixtures** across both curves at chunk counts `nc ∈ {1,2,8}`
  with corruption cases that flip the verdict (`formal/kimchi/scripts/check_kimchi_verifier.lean`).
- **Priority is not close.** Paginating `gh api repos/l-adic/snarky/commits?path=formal` returns
  **109** commits, the oldest dated **2026-06-24** (*"Lean/Mathlib formalization of kimchi gates:
  scaffolding + AddComplete (#159)"*). Our `metatheory/Dregg2/Circuit/Emit/KimchiVerify.lean` was
  first committed **2026-07-26 19:15:58** (`78ae2edf7`). **Roughly four to four-and-a-half weeks
  behind.** (The audit read 2026-06-29 from an unpaginated first page; paginating pushes their start
  *earlier*, so the gap is if anything larger than the audit stated.)

**Why the old hedge did not save the claim.** The earlier text carefully disclaimed a
protocol-soundness theorem and *then* asserted a "first at any fidelity." The hedge defended the
flank we were not exposed on. There **is** another Lean Kimchi verifier, and it reaches **past** the
guarantee we disclaimed.

**The evidence the claim rested on was stale and self-interested.** The earlier version called the
declined Mina RFC *"strong external evidence it doesn't exist elsewhere."* It is a **nonexistence
assertion by a grant applicant**, written March 2026 — three months before `l-adic/snarky`'s `formal/`
work began — never audited, and Mina declined to fund it. That framing is deleted, not softened.

**The RFC itself, restated to its source [CORRECTED 2026-07-27].** The thread is **real** (the audit
pulled the live thread JSON, HTTP 200, and the dates and wording check out): submitted
**2026-03-26T10:03:04Z** by `isurvivable`; declined **2026-04-29T10:15:29Z** by `hgedia` — *"As we
discussed on Discord. Thanks for putting down this proposal, but it is not something we are looking
to fund at this time."* Three framings around it were wrong and are fixed here:
1. It is **not "Mina's own" RFC.** It is an **outside proposal submitted TO** Mina's Core-Grants
   process — not Mina proposing to verify its own stack. That inversion is what made the sentence
   persuasive.
2. It does **not** say "no machine-checked Kimchi **verifier** exists." Its words are *"Their
   correctness has been established through audits and testing, but **no machine-checked proofs
   exist**."* Proofs-of-correctness ≠ a verifier implementation — **and that is exactly the
   distinction the novelty claim turned on.** The source was narrower than the restatement.
3. *"declined **by the Mina Foundation**"* is an **inference**, not established: the record shows
   `hgedia` declined it and does not establish `hgedia`'s Foundation affiliation. **[UNVERIFIED]**
   - <https://forums.minaprotocol.com/t/rfc-formal-verification-of-kimchi-proof-system-and-pickles-recursive-layer-in-lean-4/7056>

- **ArkLib — [CORRECTED 2026-07-27].** The earlier text said ArkLib formalizes *"sum-check, Spartan, STIR, WHIR, Binius, FRI — **not Plonk**, Kimchi, or IPA."* The Kimchi and IPA half holds (a code search for `Kimchi` in the repo returns `total_count: 0`); **the "not Plonk" clause does not** — `ArkLib/ProofSystem/ConstraintSystem/Plonk.lean` exists with real content (`Selector` with `qL qR qO qM qC`, `Gate`, `Gate.eval`, `Gate.accepts`), plus a `ProofSystem/Plonk/Basic.lean` skeleton. Correct wording: **a Plonk *constraint-system relation* but no Plonk *protocol* formalization, and no Kimchi or IPA.** Related: *Formal Verification of the Sumcheck Protocol* (2402.06093), and *Formal Verification of the S-two AIR in Lean 4* (StarkWare Stwo, Mersenne31) — a STARK-AIR verification, not a Kimchi one. **[UNVERIFIED]** — neither arXiv paper was fetched in this pass or the audit.
  - ArkLib: <https://github.com/Verified-zkEVM/ArkLib> · <https://lean-lang.org/use-cases/arklib/> · Sumcheck: <https://arxiv.org/pdf/2402.06093> · S-two AIR: <https://arxiv.org/pdf/2606.04311>

**What ours concretely is — stated without a novelty claim attached.** dregg's `KimchiVerify.lean` /
`KimchiRealProofGate.lean` are a **Lean-emitted verifier gadget targeting dregg's BabyBear STARK
AIR**, with (i) forcing lemmas (the gadget forces the real field op mod the Pasta prime) and (ii) a
differential reproducing o1-labs' reference verifier's exact intermediate scalars on a **real**
proof — axiom-clean, in-kernel, tamper-rejecting, modulo the carriers named in
`MINA-REALITY-GATE.md`. It is **not** a soundness theorem of the Kimchi protocol, and it is **not
first.** The one difference from `l-adic/snarky` that is structural rather than a ranking: theirs is
a **standalone executable Lean verifier over abstract fields**; ours is a **constraint-system (AIR)
emitter** meant to run inside dregg's prover. That is a difference in **target**, and it is stated
here as a difference, not as a merit.

**Verdict: no novelty claim. We are not first; the prior art is ahead on essentially every axis
measured here, including axes (IPA knowledge soundness, group-law-faithful gate semantics, multi-curve
production fixtures) where the earlier version implied we led.** Describe ours by what it contains.

**One adjacent question, left OPEN rather than converted into a smaller claim.** Both projects
explicitly exclude Kimchi's **Plookup** argument and **Pickles recursion**: `l-adic/snarky` declares
*"no lookups (the wire records carry none) and no recursion (`prev_challenges` absent)"*
(`formal/kimchi/Kimchi/Verifier/Kimchi.lean:32-33`), *"Flagged optional gates (range check, foreign field, lookups) are out
of scope"* (`Index/Basic.lean:40`), and *"Lookup data and `prev_challenges` are absent — declared
deferrals"* (`formal/kimchi/Kimchi/Verifier/Wire.lean:45-46`); ours freezes the same two (`KimchiVerify.lean:104,1211-1212`
— *"v1 FREEZES: no recursion (`prevLen = 0`), no lookups"*). **So this is a gap in BOTH, not a dregg
distinctive, and no narrowed novelty claim is printed here.** I grepped their full `formal/` tree
(101 Lean files, cloned locally) for lookup/Plookup and Pickles/recursion: no formalization of either.
I also checked the two places a narrowed claim might have hidden and both go the wrong way — they
**do** have the Pickles `Shifted_value` Type1/Type2 algebra (`formal/pasta/Pasta/Shifted.lean`, which
is also our P2), and they **do** model the `sg`-correctness check inside the IPA
(`Bulletproof/Protocol.lean:140,148`); what neither has is the Pickles **deferred-`sg` accumulator
discharge across recursion** (our `PicklesRecursion.lean` P1) — and our own file states P3/P4, *"the
hard crux,"* are **not built**. Whether anyone formalizes Plookup or the Pickles recursive layer
elsewhere is **[UNVERIFIED]** and stays an open question.

> **[UPDATE 2026-07-28 — one half of that sentence moved, and it is a change of FACT, not a claim.]**
> dregg's `prev_challenges` freeze is retired: `KimchiVerify.shapeOkRec` is now the upstream index
> check (`verifier.rs:810-813`), the recursion commitments and the prev-challenge digest are in the
> transcript, the `RecursionChallenge` b-poly evaluations at the head of the
> `combined_inner_product` list are RECOMPUTED and compared (`prevChalFoldOk`), and
> `KimchiRecursionGate` runs the composed decision on a real `prev_challenges = 2` Kimchi proof
> that `kimchi::verifier::verify` accepts. (So the quotation above from
> `KimchiVerify.lean:104,1211-1212` no longer describes that file.) `l-adic/snarky` still declares
> `prev_challenges` absent — **as read 2026-07-27, not re-checked since, and their `formal/` moves
> weekly**. What this is NOT: a Pickles-recursion formalization. It is the *base Kimchi verifier's*
> recursion-challenge path, one rung below Step/Wrap; P3 (`finalize_other_proof`) and P4 (the
> transcript-equality binding — the actual soundness of the recursion) are unbuilt here.
> **Plookup remains a gap in both.** No novelty claim is printed and none is intended.
>
> Two measurements this pass that go the OTHER way. They have the **Fq-state Poseidon sponge**
> (`formal/poseidon/Poseidon/{ConstantsFq,FqSponge}.lean` plus a `poseidon_fq_vectors.json`
> fixture) — which dregg only built on 2026-07-28, and built from `mina-poseidon` directly, not
> from theirs (**no license there; read-only**) — and they have the same squaring-ladder trick for
> high powers (`powPow2`, `Kimchi.lean:221`) that our `sqIter`/`bEvalSq` needs. Their
> `Bulletproof/Soundness.lean` (IPA knowledge soundness) and `Verifier/Capstone/*` (AGM soundness,
> axiomatising only Fiat–Shamir) remain the two axes on which they are ahead of anything in this
> tree, and nothing above narrows that.

### (c) **dregg-in-dregg recursive self-verification** — **re-treads well-known ground *as a concept*; only the substrate is unusual.**
- **The concept is standard.** A STARK verifying its own STARK is production practice: Plonky2, Boojum, SP1, RISC0 all do recursive self-verification / STARK→SNARK wrap; the theory is Valiant-IVC / BCCT-PCD / Halo-accumulation / Nova-folding (Query 3). dregg-in-dregg **as recursion** is not new.
  - <https://polygon.technology/blog/introducing-plonky2> · <https://github.com/microsoft/Nova> · <https://eprint.iacr.org/2020/499>
- **dregg already ships it** as STARK-in-STARK whole-history IVC (`lightclient/src/lib.rs`, `grain-verify/src/r3.rs`, with the accept decision extracted from Lean and soundness = the proved `r3_unfoolable` / `light_client_verifies_whole_history`). That it is *shipped* only underscores that it's a solved, standard construction.
- **The only unusual part** is doing it with a **Lean-authored AIR + machine-checked accept core** on the verifier circuit (House Law #1), rather than a hand-written Rust recursion circuit — and even that soundness rests on the same undischarged FRI-recursion floor, named as an unprovable-in-Lean hypothesis in `RecursiveAggregation.lean`. That assurance posture is uncommon — but it is a *property of dregg's whole stack*, not a new recursion result. **Verdict: not novel as recursion; do not headline it. If mentioned, frame it strictly as "standard IVC/accumulation, expressed over a Lean-emitted AIR, above the FRI floor."**

---

## Closest-prior-art map (one line each)

**[CORRECTED 2026-07-27 — two rows of this table were false and are rewritten; the "Bottom line" below is
substantially withdrawn.]**

| dregg direction | Closest prior art | How dregg differs (honest) |
|---|---|---|
| INWARD: verify Kimchi in dregg | **`l-adic/snarky` `formal/`** — an executable Lean 4 `kimchiVerify` **plus** AGM soundness capstones, sorry-free, by an o1-labs engineer, ~4 weeks ahead; **=nil; Placeholder wraps Kimchi** for EVM; lambdaclass/Aligned verify Kimchi off-chain | dregg's is a **Lean-emitted AIR gadget** for a BabyBear STARK rather than a standalone executable verifier — a difference in **target**, not a lead. It is **incomplete** (named carriers) where =nil;'s is a shipped wrap, and it is **behind** `l-adic/snarky` on soundness, IPA knowledge soundness, group-law-faithful gate semantics and production fixtures |
| OUTWARD: settle dregg's STARK to a foreign verifier | **stwo-gnark** (Circle-STARK→gnark Groth16); **SP1/RISC0** STARK→SNARK wrap | dregg **already ships this to the EVM** (`chain/gnark/settlement_circuit.go`, ~12M-R1CS FRI/STARK-in-Groth16) — same idea as stwo-gnark, not novel. The *Mina* target is **assessed infeasible in-circuit today**, not merely plan-stage (`MINA-DREGG-ZKAPP-BRIDGE.md:17`) |
| OUTWARD to Mina specifically | **Zeko / Protokit** settle to Mina | Zeko/Protokit settle a **Mina-native** ledger; dregg would settle a **foreign BabyBear STARK**. **Assessed infeasible in-circuit today** (no pairing gate; emulation ≫ the 2^16-row step ceiling) |
| Mutual (both directions) | **IBC** mutual light clients; **Mina** appchain mesh; **zkBridge/Telepathy** bidirectional; **`o1-labs/o1js-to-zkvm`** (Pickles inside SP1) + **`Nori-zk/proof-conversion`** (SP1/RISC0 inside o1js) | The first three are **same-system** in each direction; the last two are **cross-system and exist**, one leg each. What was not found is **one system running both legs between the same chain pair**. dregg↔Mina is unbuilt on both legs |
| MSM-deferral in K5 | **Halo / BCMS accumulation / Pickles `sg` deferral** | Correct application of a known technique; not a new scheme |
| Verified-in-Lean Kimchi | ⚑ **`l-adic/snarky` `formal/`** — `kimchiVerify` + `kimchi{Vesta,Pallas}_sound`, sorry-free, from 2026-06-24; an **outside** RFC to Mina's Core-Grants, declined 2026-04-29; **ArkLib** (sumcheck/FRI/WHIR + a Plonk constraint-system relation, no Kimchi, no IPA); **S-two AIR** (STARK, not Kimchi) | **dregg is NOT first and does not have the only one.** Ours is verified-emit + real-proof differential over an emitted AIR, with carriers; theirs is an executable verifier with soundness capstones. **[CORRECTED 2026-07-27 — this row previously read "dregg has the only Lean Kimchi verifier."]** |
| dregg-in-dregg recursion | **Plonky2 / Boojum / SP1 / RISC0 / Nova / Pickles** | Standard recursion; only the **Lean-authored AIR** substrate is unusual |

## Bottom line **[REWRITTEN 2026-07-27]**

The earlier bottom line led with *"Most novel, defensible: the Lean-authored Kimchi verifier … no
Lean Kimchi verifier exists at any fidelity — dregg's is a first."* **That is retracted.** Its
replacement is deliberately shorter, because **the corrections leave this document without a
first-of-kind claim to make, and no substitute claim is offered.**

- **Retracted: the Kimchi-verifier novelty claim (5b).** `l-adic/snarky` has an executable Lean 4
  Kimchi verifier with soundness capstones, sorry-free, from an o1-labs engineer, ~4 weeks ahead of
  ours. Describe dregg's by its contents — a Lean-emitted AIR gadget with forcing lemmas and a
  real-proof differential, carriers named — and attach **no** priority or uniqueness claim to it.
- **Weakened: mutual cross-proof-system dregg↔Mina (5a).** The *individual* directions are claimed
  prior art. What is under-populated is one system doing both across different native proof systems —
  an unbounded absence claim from one survey. INWARD is partial; OUTWARD is assessed **infeasible
  in-circuit today**, not pending. Claim neither direction as a result.
- **Unchanged, and it was always right: dregg-in-dregg recursion (5c) is not novel.** Standard
  IVC/accumulation; the Lean-emitted AIR is a stack property, not a recursion result. Don't headline it.
- **Cross-cutting honesty:** every "verifies" here sits above **undischarged opening-soundness floors**
  (dregg's FRI floor — a *density reading, not a soundness bound*; Kimchi's IPA `msm==0`). These are
  *fidelity/emit* results with named residuals, not unconditional verification. The earlier version
  added that this framing *"is exactly what the =nil;/Aligned/Zeko prior art does not make legible"* —
  **that comparative is withdrawn as unsupported**: `l-adic/snarky` makes its trust surface legible
  down to naming its two Fiat–Shamir axioms, and no survey here establishes the others do not.
- **What this document no longer supports.** It was compiled to answer "what is genuinely novel here."
  On its own corrected evidence the answer for the Kimchi work is **nothing that this survey can
  establish**, and for the mutual pairing it is a hedged, unbounded negative. Stating that plainly is
  the correct output; manufacturing a smaller claim to fill the gap is the failure mode this pass exists
  to remove.

---

## ⚑ Which external citations here were actually checked **[ADDED 2026-07-27]**

The earlier version presented every external citation in a uniform voice, so a reader had no way to
tell a fetched-and-read source from a restated one. That is the mechanism that let a fabricated figure
sit beside real ones for a day. This list fixes it.

**Fetched and read first-hand** (by the audit, this pass, or both): the `l-adic/snarky` repository
(metadata, `formal/` commit history paginated, `formal/kimchi/Kimchi/Verifier/Kimchi.lean`, the three
`Verifier/Capstone/*.lean`, `formal/kimchi/Kimchi/Verifier/Wire.lean`, `Index/Basic.lean`,
`pasta/Pasta/Shifted.lean`, `Bulletproof/{Soundness,Protocol}.lean`,
`formal/kimchi/scripts/check_kimchi_verifier.lean`, and a full-tree grep from a local clone); `martyall`'s GitHub
profile; `o1-labs/o1js-to-zkvm` and `Nori-zk/proof-conversion` (metadata + READMEs, via `gh api`);
the Mina Core-Grants RFC thread JSON; the ArkLib repo README and its Plonk files; the =nil;
`mina-ethereum-bridge` page (rendered text searched for every figure quoted above); and the
`o1-labs.github.io/proof-systems/pickles/overview` URL (both the 404 and the live form).

**[UNVERIFIED] — not fetched by the audit or this pass. Do not cite these onward as checked:**
arXiv 2606.04311 (S-two AIR); arXiv 2402.06093 (Sumcheck); eprint 2026/538, 2024/2099, 2023/1282,
2023/573, 2022/1758, 2022/542, 2020/499, 2019/1021, 2024/661, 2024/1737, 2024/1402, 2210.00264;
RISC0 issue #1267; the NEBRA, stwo-gnark, Telepathy, zkBridge, Zeko, Protokit, lambdaclass/Aligned,
Plonky2/Boojum and IBC characterizations; the Mina "reintroducing Mina" / "internet of proofs"
framing; and the claim that =nil; Placeholder is the **only** prior cryptographic Kimchi-wrap. Several
are almost certainly fine — the point is that **nobody has checked**, and the uniform voice of the
earlier draft implied otherwise.

**Also [UNVERIFIED] and load-bearing elsewhere in this scope** (audit §6): the o1js absence claims
(*".verify() consumes only Pickles proofs"*, *"DynamicProof is dynamic-VK, not dynamic-proof-system"*)
— the local `~/dev/o1js` is **v0.16.2 (2024-02-23)** and contains **no `DynamicProof` class at all**,
predating the feature, while the PoC ran on o1js 2.15.0; and *"Pickles does not chunk step circuits"* —
the 2^16/2^15 figures are exact but **no code asserting non-chunking was located**.

*Sources are linked inline. Primary dregg grounding: `docs/MINA-KIMCHI-VERIFIER-PLAN.md`, `docs/MINA-REALITY-GATE.md`, `docs/KIMCHI-VERIFY-SPEC.md`, `docs/TRUE-PEERS-ARCHITECTURE-2026-07-26.md`, `docs/reference/CHAIN-INVENTORY-GROUNDED.md`, `docs/deos/FOLDING-RECURSION-PRIMER.md`, `bridge/src/mina.rs`, `chain/gnark/settlement_circuit.go`, `lightclient/src/lib.rs`, `grain-verify/src/r3.rs`, `metatheory/Dregg2/Circuit/RecursiveAggregation.lean`. Compiled 2026-07-27; corrected the same day against `docs/AUDIT-IMPORTER-AND-DOCS.md`.*
