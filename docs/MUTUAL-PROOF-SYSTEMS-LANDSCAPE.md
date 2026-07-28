# MUTUAL PROOF SYSTEMS — landscape + honest novelty assessment

*A cited survey of the research + practice landscape around the directions dregg is exploring:
mutual (bidirectional) proof verification, cross-proof-system verification, recursive
composition / IVC, Mina-in-Mina / Zeko, and — the point of the exercise — what is genuinely
**novel** about dregg's directions versus what re-treads known ground.*

**Scope of "dregg's directions" as read from the repo (not restated from memory):**
- dregg is a **BabyBear STARK (Plonky3 / FRI)** with a **Lean-authored/generated AIR** (House Law #1: constraints are EMITTED from Lean, never hand-written in Rust; `circuit/src/field.rs`, `circuit/src/lib.rs`, `GOAL-STARK-KILL.md`). Its STARK security rests on an **undischarged FRI/STARK soundness floor** (`docs/reference/CHAIN-INVENTORY-GROUNDED.md`: *"FRI extraction floor — undischarged, no adversary model"*) — describe everything below at that resolution.
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

**Finding for Query 1.** I found **no prior system where two chains with *different native proof systems* each natively verify the other's proofs in both directions.** Everything mutual is either (i) same-system light clients (IBC, zkBridge, Telepathy — and dregg's own "true peers" is in this family), or (ii) same-system recursion (Mina's own appchain mesh). The cross-system work that exists (Query 2) is **one-directional**. So dregg↔Mina as **mutual + cross-proof-system** occupies a genuinely under-populated cell — with the honest caveat that dregg has not closed *either* direction of the *Mina* pairing end-to-end yet.

---

## Query 2 — Cross-proof-system verification (one proof system inside another)

This cell is **well-populated but almost entirely one-directional** (wrap / aggregate a foreign proof into a single verifiable form). The Kimchi↔EVM literature is the direct precedent for dregg's INWARD direction.

- **=nil; Foundation — Placeholder wrapping Kimchi (the *only* prior cryptographic Kimchi-wrap; cited in dregg's own plan as the cost reference).** Mina's Kimchi state proof is too expensive to verify directly on the EVM, so =nil; wraps the **Kimchi verification algorithm** in a **Placeholder** (their FRI/PLONK-style) proof and verifies *that* on-chain. They quote the cost of the wrapped Kimchi verification at ~**34.4 billion MSMs** — a useful order-of-magnitude for why dregg's plan *defers* the MSM (see Query 3 / K5).
  - <https://nil.foundation/blog/post/mina-ethereum-bridge> · <https://blog.nil.foundation/2022/06/28/mina-integration.html> · <https://nil.foundation/blog/post/proof-market>

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

- **Curve-cycle / field-mismatch literature (the reason cross-system is hard).** Cross-system verification runs into the field/curve mismatch dregg's plan calls out (`KIMCHI-VERIFY-SPEC.md` §0: a Vesta-proof verifier circuit lives over Pallas's scalar field, so all Fq arithmetic is **non-native** and emulated). Foundational reading:
  - Pasta 2-cycle (Pallas/Vesta) as used by Pickles: <https://o1-labs.github.io/proof-systems/pickles/overview.html>
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
- **Pickles (Mina)** — inductive Kimchi-in-Kimchi over the Pasta cycle; Step/Wrap circuits; the deferred-`sg` accumulator dregg's K5 targets. <https://o1-labs.github.io/proof-systems/pickles/overview.html>

**Folding schemes (the modern IVC branch):**
- **Nova (Kothapalli–Setty–Tzialla)** — IVC from folding relaxed R1CS. <https://github.com/microsoft/Nova>
- **SuperNova (eprint 2022/1758)** — non-uniform IVC (per-instruction circuits). <https://eprint.iacr.org/2022/1758.pdf>
- **HyperNova (eprint 2023/573)** — folding for CCS (customizable constraint systems). <https://eprint.iacr.org/2023/573.pdf>
- **PCD from multi-folding (eprint 2023/1282)**, **MicroNova — on-chain-efficient folding (eprint 2024/2099)**, **PCD via Holography Accumulation (eprint 2026/538)** — the frontier. <https://eprint.iacr.org/2023/1282> · <https://eprint.iacr.org/2024/2099.pdf> · <https://eprint.iacr.org/2026/538>

**dregg's own position in this line (from the repo).** dregg *implements* IVC as **STARK-in-STARK** recursion today (`circuit-prove/src/ivc_turn_chain.rs`: fold finalized turn proofs into one running recursive proof, binding `prev.NEW_COMMIT == next.OLD_COMMIT`). It **surveyed folding and deliberately declined it**: `docs/deos/FOLDING-RECURSION-PRIMER.md` reviews Nova / SuperNova / HyperNova / ProtoStar / ProtoGalaxy / NeutronNova / LatticeFold and rejects adoption because folding *"collides with post-quantum safety and the small (BabyBear) field,"* flagging **LatticeFold/LatticeFold+** (PQ, lattice-based folding) as the future watch item. So dregg is a *conscious non-adopter* of the folding branch — worth stating so nobody frames a folding scheme as dregg's missing piece.
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

### (a) dregg↔Mina **mutual cross-proof-system** verification — **genuinely under-populated cell; not yet demonstrated end-to-end.**
- **Real, if closed.** No prior system has two chains with **different native proof systems** verify **each other** (Query 1). Cross-system verification exists only one-directionally (Query 2); bidirectional systems are same-system (IBC/zkBridge/Telepathy); Mina's mutual mesh is same-system. The specific pairing **BabyBear-STARK ↔ Kimchi/Pickles** in **both** directions is, as far as this survey found, unclaimed.
- **Honest deductions.** (i) INWARD does **not** verify Mina yet — it is C1+C8+C5 over the real field modulo three crypto carriers (`MINA-REALITY-GATE.md`). (ii) OUTWARD is a plan. (iii) Both directions inherit **undischarged opening-soundness floors** (dregg's FRI floor; Kimchi's IPA `msm==0`), so even when wired, "mutual verification" is at that resolution, not unconditional. **Verdict: a real and rare *direction*; not yet a *result*. Claim it as a target, with the carriers and floors named.**

### (b) A **verified-in-Lean Kimchi verifier** — **genuinely novel; nobody else has one, partial or otherwise.**
- **Strong external evidence it doesn't exist elsewhere.** A Mina Core-Grants **RFC to formally verify Kimchi + Pickles in Lean 4** was submitted **2026-03-26** and **declined by the Mina Foundation 2026-04-29** ("not something we are looking to fund at this time"); the RFC itself states it would build *"the first formal model of Kimchi/Pickles in Lean 4"* and that **no machine-checked Kimchi verifier exists.**
  - <https://forums.minaprotocol.com/t/rfc-formal-verification-of-kimchi-proof-system-and-pickles-recursive-layer-in-lean-4/7056>
- **The nearest Lean work stops short of Kimchi.** **ArkLib** (Verified-zkEVM) formalizes sum-check, Spartan, STIR, WHIR, Binius, FRI — **not Plonk, Kimchi, or IPA.** Related: *Formal Verification of the Sumcheck Protocol* (2402.06093), and **Formal Verification of the S-two AIR in Lean 4** (StarkWare Stwo, Mersenne31) — a *STARK-AIR* verification, not a Kimchi one.
  - ArkLib: <https://github.com/Verified-zkEVM/ArkLib> · <https://lean-lang.org/use-cases/arklib/> · Sumcheck: <https://arxiv.org/pdf/2402.06093> · S-two AIR: <https://arxiv.org/pdf/2606.04311>
- **Honest scoping of what dregg's actually is.** dregg's is a **Lean-emitted verifier *circuit/gadget*** with (i) **forcing lemmas** (the gadget forces the real field/curve op mod the prime) and (ii) a **differential** that reproduces o1-labs' reference verifier's exact scalars on a **real** proof — axiom-clean, in-kernel, non-vacuous (tamper ⇒ reject). This is **not** the RFC/ArkLib deliverable (a machine-checked **soundness** theorem of the Kimchi *protocol*). It is a **verified-emit + real-proof-fidelity** result — still a **first** (there is no other Lean Kimchi verifier at any fidelity), but it must be named precisely, not sold as "Kimchi's soundness is proven." **Verdict: a real contribution and a first-of-kind; the precise contribution is "the first Lean-authored Kimchi verifier gadget with machine-checked forcing + real-proof differential," carriers named.**

### (c) **dregg-in-dregg recursive self-verification** — **re-treads well-known ground *as a concept*; only the substrate is unusual.**
- **The concept is standard.** A STARK verifying its own STARK is production practice: Plonky2, Boojum, SP1, RISC0 all do recursive self-verification / STARK→SNARK wrap; the theory is Valiant-IVC / BCCT-PCD / Halo-accumulation / Nova-folding (Query 3). dregg-in-dregg **as recursion** is not new.
  - <https://polygon.technology/blog/introducing-plonky2> · <https://github.com/microsoft/Nova> · <https://eprint.iacr.org/2020/499>
- **dregg already ships it** as STARK-in-STARK whole-history IVC (`lightclient/src/lib.rs`, `grain-verify/src/r3.rs`, with the accept decision extracted from Lean and soundness = the proved `r3_unfoolable` / `light_client_verifies_whole_history`). That it is *shipped* only underscores that it's a solved, standard construction.
- **The only unusual part** is doing it with a **Lean-authored AIR + machine-checked accept core** on the verifier circuit (House Law #1), rather than a hand-written Rust recursion circuit — and even that soundness rests on the same undischarged FRI-recursion floor, named as an unprovable-in-Lean hypothesis in `RecursiveAggregation.lean`. That assurance posture is uncommon — but it is a *property of dregg's whole stack*, not a new recursion result. **Verdict: not novel as recursion; do not headline it. If mentioned, frame it strictly as "standard IVC/accumulation, expressed over a Lean-emitted AIR, above the FRI floor."**

---

## Closest-prior-art map (one line each)

| dregg direction | Closest prior art | How dregg differs (honest) |
|---|---|---|
| INWARD: verify Kimchi in dregg | **=nil; Placeholder wraps Kimchi** for EVM; lambdaclass/Aligned verify Kimchi off-chain | dregg's verifier side is **Lean-emitted + forcing-checked**, not a hand-built prover circuit; but dregg's is **not complete** (3 carriers) where =nil;'s is a shipped wrap |
| OUTWARD: settle dregg's STARK to a foreign verifier | **stwo-gnark** (Circle-STARK→gnark Groth16); **SP1/RISC0** STARK→SNARK wrap | dregg **already ships this to the EVM** (`chain/gnark/settlement_circuit.go`, ~12M-R1CS FRI/STARK-in-Groth16) — same idea as stwo-gnark, not novel. The *Mina* target (settle via Pickles) is plan-stage |
| OUTWARD to Mina specifically | **Zeko / Protokit** settle to Mina | Zeko/Protokit settle a **Mina-native** ledger; dregg would settle a **foreign BabyBear STARK** via a Pasta-native terminal recursion — the cross-system twist. Plan-stage only |
| Mutual (both directions) | **IBC** mutual light clients; **Mina** appchain mesh; **zkBridge/Telepathy** bidirectional | Those are **same-system** in each direction; dregg↔Mina would be **two different proof systems** each verifying the other — unclaimed, but unbuilt |
| MSM-deferral in K5 | **Halo / BCMS accumulation / Pickles `sg` deferral** | Correct application of a known technique; not a new scheme |
| Verified-in-Lean Kimchi | **Mina's own declined RFC**; **ArkLib** (sumcheck/FRI/WHIR, no Kimchi); **S-two AIR** (STARK, not Kimchi) | dregg has the **only** Lean Kimchi verifier; but it's **verified-emit + differential**, not a protocol **soundness** theorem |
| dregg-in-dregg recursion | **Plonky2 / Boojum / SP1 / RISC0 / Nova / Pickles** | Standard recursion; only the **Lean-authored AIR** substrate is unusual |

## Bottom line
- **Most novel, defensible:** the **Lean-authored Kimchi verifier** (5b). Mina's own foundation declined to fund the (different, harder) soundness version in April 2026, and no Lean Kimchi verifier exists at any fidelity — dregg's is a first. Name it precisely (verified-emit + real-proof differential + named carriers), never as "Kimchi soundness proven."
- **Novel direction, not yet a result:** **mutual cross-proof-system** dregg↔Mina (5a). The cell is genuinely under-populated, but INWARD is partial and OUTWARD is a plan; claim the *direction*, name the carriers/floors.
- **Not novel, don't headline:** **dregg-in-dregg recursion** (5c) — standard IVC/accumulation; the Lean-emitted AIR is the only distinctive part, and that's a stack property, not a recursion result.
- **Cross-cutting honesty:** every "verifies" here sits above **undischarged opening-soundness floors** (dregg's FRI floor; Kimchi's IPA `msm==0`). At current resolution, these are *fidelity/emit* results with named residuals, not unconditional verification. That framing is the contribution's strength, not a weakness — it is exactly what the =nil;/Aligned/Zeko prior art does **not** make legible.

---
*Sources are linked inline. Primary dregg grounding: `docs/MINA-KIMCHI-VERIFIER-PLAN.md`, `docs/MINA-REALITY-GATE.md`, `docs/KIMCHI-VERIFY-SPEC.md`, `docs/TRUE-PEERS-ARCHITECTURE-2026-07-26.md`, `docs/reference/CHAIN-INVENTORY-GROUNDED.md`, `docs/deos/FOLDING-RECURSION-PRIMER.md`, `bridge/src/mina.rs`, `chain/gnark/settlement_circuit.go`, `lightclient/src/lib.rs`, `grain-verify/src/r3.rs`, `metatheory/Dregg2/Circuit/RecursiveAggregation.lean`. Compiled 2026-07-27.*
