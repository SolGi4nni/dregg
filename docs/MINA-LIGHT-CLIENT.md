# Following Mina — what dregg verifies, and what it still trusts

**Status: 2026-07-30.** This document is written at CURRENT resolution. Where a row says
*trusted*, nothing in this tree checks it, and no amount of surrounding green changes that.

---

## The change this document records

Until today `bridge/src/mina_observer.rs` asked a Mina node **`bestChain`** — the node's own
answer to fork choice — and treated the reply as the canonical chain. A client that asks a node
which chain is canonical is *trusting* one, not following one. Every piece of Samasika formalism
in this tree sat beside a component that never consulted it.

Two things blocked connecting them, and only one of them was real:

1. **Fork choice was formalized but unexported.** `Dregg2/Bridge/MinaChainSelection.lean` landed
   `select` on 2026-07-29 and deliberately shipped no `@[export]`.
2. **The data source could not feed it.** The long-range branch reads `sub_window_densities`, and
   `subWindowDensities` **is not a field of the public GraphQL `ConsensusState`** — the resolver
   list is `proof_of_stake.ml:2449-2536` and it has no arm for it. So the lane that wrote `select`
   was right to refuse: an export the caller cannot feed is an un-called gate.

The blocker was a **data source**, not a formalization. It is closed by speaking Mina's own
peer-to-peer protocol, where `sub_window_densities` is an ordinary positional field.

---

## Where each thing lives, and why

| Layer | Substrate | Why there |
|---|---|---|
| The socket (pnet, Noise XX, yamux, `coda/rpcs/0.0.1`) | **Rust / openmina** | I/O. Not semantics. Hand-writing Salsa20 and a Noise state machine into this repo would reconstruct a thing that already exists. |
| **What the bytes mean** (binprot `Protocol_state.Value`) | **Lean** — `Dregg2/Bridge/MinaBinprot.lean` | ⚑ **A parser IS semantics.** Which bytes are `min_window_density` is the content fork choice operates on. In Rust it would be a mirror of openmina's `p2p-messages` whose correctness is a *differential test*. |
| Fork choice (`select`) | **Lean** — `MinaChainSelection` + `MinaForkChoiceGate` | House law: decision logic is Lean-authored, `@[export]`ed over the C ABI. |
| The rolling head + ratchet | **Lean decides, Rust stores** — `MinaForkChoiceGate.rollHead`, `bridge/src/mina_head.rs` | Rust holds bytes and a number; the gate decides whether either changes. |

The payoff of the second row is that there is **no second `ConsensusState`**.
`MinaBinprot.decodeProtocolState` returns `MinaChainSelection.ConsensusState` — the exact structure
`select_reads_only_eight_fields` and `beats_not_transitive` are stated over. No intermediate type,
no conversion function, nothing to keep in agreement.

---

## The per-step table

| # | Step | Status | What is actually checked, and by what |
|---|---|---|---|
| 1 | **Getting bytes from a peer** | *trusted for availability only* | The helper speaks Mina's stack and hands over bytes. It cannot make the client accept a chain — every byte goes through the Lean decoder's refusals and then through `select`. The worst a malicious source achieves is to be refused, or to **withhold**, and withholding is not defensible by any light client. |
| 2 | **binprot decode of `Protocol_state.Value`** | ✅ **verified (Lean), reality-gated** | `MinaBinprot`. Canonical integer widths enforced; every field element checked `< p`; density count bounded hard at 11; `slots_per_epoch = 0` refused. `MinaBinprotRealBlock` decodes **devnet block 540186** — 1,544 real wire bytes — with **exact fit**, every field matching openmina's independent decode. Refutable: truncation, a flipped count byte, a one-byte shift are all REFUSALS. |
| 3 | **Blake2b of `last_vrf_output`** | ✅ **derived (Lean)** | `Blake2bGadget.Ref.compress`, anchored against `hashlib.blake2b` vectors. Not a carrier bit from Rust. |
| 4 | **Carried protocol constants** | ✅ **refused, never adopted** | A block carries `k`, `slots_per_epoch`, `slots_per_sub_window`, `grace_period_slots`, `delta`. They are **peer-supplied**, so the gate PINS its own (`grace_period_end = 2237`, not the 1440 in the spec table *and* in openmina) and refuses a block that disagrees. Otherwise a peer supplying the states could supply the constants that make its fork win. |
| 5 | **Fork choice (`select`)** | ✅ **verified (Lean), exported, ours** | `dregg_mina_better_tip`. Determinism-with-content, irreflexivity, asymmetry, ties-only-on-equal-keys — all proven. Driven end-to-end on real devnet bytes through the String C ABI. **This replaces `bestChain`.** |
| 6 | **The rolling head** | ✅ **verified (Lean), Rust stores** | `dregg_mina_head_advance`. `rollHead_finalized_monotone`: the finalized height never decreases, on any input, under any presentation order. `rollHead_fails_closed_without_the_segment`: an unverified segment moves nothing. |
| 7 | **The density window** | ✅ **verified (Lean)**, ⚠ *not yet wired to the head* | `MinaSlidingWindow` replays **849 real consecutive canonical devnet transitions** from one seed and the slot sequence alone, zero mismatches. Checkable **from two consecutive headers and nothing else**. The head currently consumes a *served* window and bound-checks it rather than re-deriving it from the parent. |
| 8 | **Anchored segment / confirmation depth** | ✅ **verified (Lean)** | `dregg_mina_lc_verify` (`LightClientMinaGate`) — non-empty segment, submitted height at or above the pin, WITNESSED depth. Feeds the head as the `sg` bit. |
| 9 | **Block proofs — Wrap *preamble*** | ✅ **verified (Lean), runtime-checkable** | `dregg_mina_wrap_shape_ok`, `dregg_mina_proof_chain_ok`, `dregg_mina_state_hash_word_ok`. Byte-exact decode of `Mina_base.Proof.Stable.V2`. |
| 10 | **Block proofs — Wrap *arithmetic*** | ⚠ **fixture-bound** | The IPA/MSM verification is driven end-to-end for **one** height's transcript (block 539508). It is not a per-block runtime check. A client that "verifies each block's proof" does not, at this resolution. |
| 11 | **The Wrap verifier index** | ❌ **trusted config** | `MinaWrapIndexParams::DEVNET_BLOCKCHAIN`. Nothing derives it from the chain. This is the largest single trusted object the proof story rests on. |
| 12 | **`state_hash` re-derivation** | ✅ **derived (Lean), and the served value is CHECKED** (2026-07-30) | `Dregg2.Bridge.MinaStateHashDerive` recomputes `Poseidon_Fp(salt "MinaProtoState")[previous_state_hash; Poseidon_Fp(salt "MinaProtoStateBody")(pack_input (Body.to_input body))]` from the binprot bytes. The wire carries **every** field the preimage needs — the earlier "GraphQL cannot supply it" finding was true and about the wrong wire; what had to change is that `MinaBinprot` stopped walking the `Blockchain_state` and throwing it away. `MinaForkChoiceGate.decodeSide?` REFUSES a block whose bytes do not hash to the hash presented with them, so `eh`/`ch`/`ph`/`th`/`vh` are claims, not carriers — which in particular removes a peer's ability to name its own value for `select`'s final (numeric-hash) tie-break. The primitives are anchored outside the repo (both salts against openmina's pinned regression constants, SHA-256 against `hashlib`, Poseidon against six o1js golds); the **order** — ~30 field elements and ~1,400 packed bits across four places where `Body.to_input` disagrees with the binprot record order — was **settled against the chain** by `MinaStateHashRealBlock`, which needs **no oracle**: `deriveStateHash(block_N) = block_{N+1}.previous_state_hash` on a consecutive pair the peer itself served. MEASURED on live devnet **540221 → 540222**: it HOLDS, in 26 s of kernel `decide` (no `native_decide`, zero axioms), and red-proofs on a one-bit change to the oracle. ⚠ Residual: the hash fields are still *passed in* rather than returned by the gate; deleting them outright is hygiene and no longer changes what an adversary can do. |
| 13 | **Leader election / VRF threshold** | ❌ **not checkable by any verifier** | `vrf_output` needs the delegator's **secret scalar**: `eval sk m = H(m, sk·H₂(m))`. It can only be *proved*, and Mina ships no standalone VRF verifier (openmina's `mina_vrf` is evaluation-only). A client that verifies the Pickles proof **inherits** the threshold check. `MinaVrfThreshold` is a specification of what that proof asserts, not an independent check. |
| 14 | **The weak-subjectivity pin** | ❌ **operator-supplied, by construction** | A light client cannot bootstrap trust from nothing. `MinaVerifiedHead::pinned` is the operator's act; everything after it is decided by the rule. |

---

## ⚑ The exposure that is a theorem, not a caveat

`select` is a **tournament, not an order**. `beats_not_transitive` proves genuine 3-cycles at real
mainnet constants, `decide`-checked, by two independent mechanisms:

1. `is_short_range` partitions pairs differently, so different *pairs* are judged by different rules;
2. even in the long regime alone, the relative minimum window density is **not an intrinsic scalar
   but a function of the pair** via `max_slot`.

The consequence for any client that rolls a head pairwise — which is what the daemon does, and what
openmina does — is that a peer controlling presentation order can walk the head around the cycle.
`head_can_be_walked_in_a_cycle` executes exactly that: three advances, each a legitimate Samasika
verdict, returning the head to **exactly** its starting value.

**What survives it**: `the_cycle_moves_the_head_but_not_the_finalized_point` — the ratchet held at
710 the whole way round, and it depends on no axioms. The head is a preference and it cycles; the
finalized point is a ratchet and it does not.

So: **never fold `select` over a candidate set.** Folding is order-dependent and it is the
exploitable form. The pairwise shape is the mitigation, and it is deliberate.

---

## ⚑ On differentials against openmina

This tree holds a proven result that openmina's chain-selection **semantics disagree with the
daemon's** (`MinaChainSelectionDifferential`: 8 of 57 rows differ in the final verdict; three
compounding defects; `three_renderings_three_answers` pins one question at 50 / 23 / 28). Nothing
here takes openmina's verdict about anything.

The reality gate in row 2 is a differential against a **decoder**, which is a different object.
openmina's `p2p-messages` types are machine-derived from the OCaml `.bin_prot` shapes, so on the
question *"which bytes are which field"* it transcribes the daemon rather than holding an opinion.
Agreement on the parse is evidence. Agreement on a verdict would not have been.

That gate earned its keep immediately: it caught **two real defects** on the first run against real
bytes, both leaf encodings rather than layout —

* `sok_digest : unit` is **one `0x00` byte**, not free. The resulting one-byte shift survived
  *twenty* canonical field-element checks before surfacing as a block timestamp of 0.
* `body_reference` is a **length-prefixed byte string**, not a bare 32-byte digest.

The record layout had been read correctly from the daemon *and* from openmina. The hand-built test
vectors could not have caught either: an encoder written by the same hand as the decoder agrees
with it by construction.

---

## The honest one-line answer

**Does dregg follow Mina's chain rather than trust a node's answer?**

For **fork choice**, yes: the decision is `select`, evaluated by us, in Lean, on binprot bytes off
the peer-to-peer wire, over inputs the public GraphQL cannot supply — and the head that results is
persisted and rolls forward under a proven ratchet.

For **block validity**, not yet: rows 10–13 are the distance. The Wrap *arithmetic* is fixture-bound
to one height, the verifier index is trusted config, and leader election is not checkable by any
verifier at all. (Row 12 closed on 2026-07-30: `state_hash` IS re-derived, and a served value that
the bytes do not have is refused.) A chain of blocks whose proofs are only
*structurally* checked is a chain a sufficiently resourced adversary can fabricate, and the fork
choice on top of it is then choosing between two fabrications.

Fork choice moved from *trusted* to *ours*. Block validity did not.
