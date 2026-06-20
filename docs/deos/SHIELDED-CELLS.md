# Shielded cells — privacy M2: a multi-asset shielded pool + private programmable cells that attest

> The thesis: **fully private programmable cells that issue verifiable attestations** = the
> bounded-predicate cell-program + Plonky3's hiding PCS. The bounded model is *precisely* why this
> is tractable and safe (small ZK circuits, decidable policy — not a zkVM, no halting problem). The
> multi-asset shielded pool is the first concrete instance; the general shielded transition + ZK
> attestation is the frontier it opens — the *same* machinery throughout.

## The crypto foundation (don't hand-roll — it's already the right thing)
The ZK path rides **Plonky3's `HidingFriPcs`** (`p3_fri`, `ZK=true`) over `p3_merkle_tree::
MerkleTreeHidingMmcs` (salted leaves) — `circuit/src/stark_zk.rs`. Its own decision note: *"Rather
than bolt masking onto the hand-rolled FRI (error prone, easy to get subtly wrong), we adopt
Plonky3's battle-tested hiding PCS… do not hand-roll masking."* It does trace-doubling-with-random-
rows + a random FRI codeword + leaf salting, statistically-ZK by construction, **zero AIR changes**.
(Honest scope: there is *also* a non-ZK hand-rolled custom STARK in `crate::stark` and a CG-1
recursion gadget with a BLAKE3-isn't-algebraic residual — neither is the ZK path. Shielded cells ride
the p3 `HidingFriPcs` uni-stark path only.)

## Why NO Turing-completeness / lambda calculus (load-bearing, not a gap)
Cell programs are bounded, decidable **predicates** (the Pred algebra, biscuit-Datalog-descended,
compiled to a descriptor + `canonical_program_vk`, interpreted in-circuit by `effect_vm`/
`descriptor_ir2`). Keeping them bounded is a feature on two axes:
- **Safety:** the right-skewed flow algebra makes policy refinement *decidable* (the Büchi game) —
  you can prove properties of a bounded program; you can't of a Turing-complete one. No gas, no halting.
- **ZK-tractability (the load-bearing one):** a Turing-complete VM in ZK is a **zkVM** — a huge, slow
  universal circuit. A bounded predicate is a **small, fast circuit.** The bounded model is exactly
  what makes "ZK cell programs" real instead of a research project.

Expressiveness comes from **composition**, not a Turing-complete inner language: bounded-per-turn,
composable across turns via the flow algebra (sequence/choice) and **partial-turns/promises**
(pipelined multi-step, each step bounded, the pipeline arbitrary). The one thing the model refuses —
unbounded inner computation in a single step — it refuses on purpose; compose it across turns.

## What dregg already has (the pieces of a shielded pool are its spine)
- **`AssetId := issuer-cell` + per-asset `Σδ=0`** — *this is the multi-asset balance check*, already
  the conservation law. An Orchard-ZSA-style multi-asset pool isn't bolted on; it's the native model.
- **`value_commitment.rs`** (Pedersen, homomorphic — the balance check primitive) · **notes /
  `note_encryption` (ECIES) / `stealth`** · the **nullifier set** (the noteSpend grow-gate =
  double-spend prevention) · the **sorted-Poseidon2 commitment tree** · the p3 `HidingFriPcs`.

## The M2 arc (mine, in `circuit/src/shielded/`)
A **shielded-action circuit**: prove a transfer (spend input notes → mint output notes) with
**value + asset-type + owner all hidden**, proving (a) per-asset value balance via the homomorphic
value commitments, (b) input-note membership in the commitment tree, (c) nullifier derivation (no
double-spend), (d) spend authority — all hidden via `HidingFriPcs`.
- **M2-a** — one **single-asset** shielded transfer end-to-end (balance + membership + nullifier,
  hidden), the blind verifier. The toehold.
- **M2-b** — the **multi-asset pool** (ZSA): per-asset balance, asset-type hidden, cross-asset in one action.
- **M2-c** — the **general shielded *transition***: any kernel action (grant/revoke/setfield/…)
  proven over hidden state — shielding is uniform because every transition is already proven
  in-circuit; the hiding layer applies to the general transition, not just value.
- **M2-d** — **ZK attestations**: a private cell program issuing a *public verifiable claim* —
  "this hidden cell satisfies predicate P / made this valid transition," checkable, revealing nothing
  else. Privacy-preserving **verifiable credentials** — the natural fusion of dregg's lineage
  (macaroons/biscuits were always attenuable proof-carrying tokens; + the hiding PCS = a token that
  proves a claim about private state without disclosing it). Prove-over-18, prove-balance-positive,
  prove-a-confidential-credential — all bounded predicates, ZK'd. *The jewel.*

## The seam (approved)
`circuit/src/shielded/` is its **own AIR + proof**, composed over the existing notes / value-
commitments / nullifiers / commitment-tree + the p3 `HidingFriPcs`. It is **NOT woven into
`effect_vm`/`descriptor_ir2`** (ember's effect-descriptor correctness refactor) — the two meet only
at *"a shielded transfer is a kind of conserving turn."* I own `circuit/src/shielded/`; ember owns
the effect-descriptor lane. **VK perturbation is free** (ember: "i don't care how often or for what
reason the vk changes — it is not used at all"), so no separate `shielded` VK variant is needed —
just change the circuit; the VK changes.

## Status
Design banked; the seam is approved; M2 is **mine**. It waits on ember's circuit refactor *compiling*
(not its design) and is a real ZK-circuit build (the shielded-action AIR is substantial — not a weld),
but every primitive it needs is in-tree on the proper (p3) crypto floor.
