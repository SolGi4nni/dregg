# ⚑ ACTIVE GOAL LANES — this repo runs MULTIPLE concurrent `/goal` sessions

**Why this file exists:** several terminals each set a `/goal` against this one repo. They
share no isolation — the canonical `GOAL.md` is whatever the last goal-writer wrote (right
now: storage-in-lean), so it is NOT a reliable per-goal indicator. Each lane keeps its OWN
trail file. This board is the map. Any goal session: read this first; edit only YOUR trail
file; never clobber another lane's.

| lane | trail file | one-line mission |
|---|---|---|
| **storage-in-lean** | `GOAL.md` | rebuild the Rust storage layer IN LEAN (proven), package to Rust via `@[export]`; decentralized providers + erasure/PoR + market, all Lean-verified |
| **distributed-deos** | `GOAL-DISTRIBUTED-DEOS.md` | the sovereign live image, across machines — the distributed inhabited world |
| **fable** | `GOAL-fable.md` | make it real, and keep it honest (general Fable driver) |
| **federation** | `GOAL-FEDERATION.md` | make the corpus RUN FOR REAL on the living federation, and know WHY |
| **stark-kill** | `GOAL-STARK-KILL.md` | kill `circuit/src/stark.rs` + ~45 hand AIRs by re-deriving every circuit from Lean; climb the refinement ladder (Rung 1 functional → Rung 2 semantic → Rung 3 fold → apex) |
| **no-prequantum** | `GOAL-PQ.md` | leave no classical-only load-bearing crypto standing: hybridize every signature (ed25519∧ML-DSA, enrolled+pinned) + key-exchange (X25519+ML-KEM); per the 07-09 audit |
| **pq-frontiers** | `GOAL-PQ-FRONTIERS.md` | retire every honestly-open frontier of the crypto-to-protocol-soundness proof by FORMALIZING the literature (Unmasking-TRaccoon adaptive · Canetti UC composition · FIPS-204 @[export] extraction · surface-3 executor seam) — no smuggling, no giving up. **DONE 07-09** |
| **verified-system** | `GOAL-VERIFIED-SYSTEM.md` | ⚠ **RETRACTED 07-09** — declared "done" on NAMED carriers (`StarkSound`/`RestHashIffFrame`/toy models); superseded by **honest-verification** |
| **honest-verification** | `GOAL-HONEST-VERIFICATION.md` | RETIRE THE CARRIER DEBT: discharge every DEBT-A (`StarkSound`) + DEBT-B (finite-map / `RestHashIffFrame`) carrier to a PROVED theorem or a genuine floor item, so the apex rests only on `{Poseidon2SpongeCR, lattice/DL, leanc}` — no `seL4-cited`, nothing named. Hub for `CARRIER-CENSUS` + `DEBT-B` + `DELTA-FUTURE` |
| **dreggic-collectivity-web** | `GOAL-COLLECTIVE-FICTION-DEMO.md` | make the verifiable collective-fiction/game WEB platform as good as possible — attested-dm engine + demo/ arcade frontend/UX + collective voting/co-authoring + dregg-dice/pqvrf verifiable randomness + verify_replay trust + authoring + docs |
| **arklib-vacuity** | `GOAL-ARKLIB-VACUITY.md` | complete the ArkLib KZG evaluation-binding vacuity repair + wire the generic-group security bounds into ONE sound end-to-end theorem over ArkLib's real `tSdhExperiment` (`tSdh_ggm_sound`); owns `docs/reference/arklib-kzg-vacuity/` + the `emberian/ArkLib` fork branches |
| **greens-that-mean-something** | `GOAL-GREENS-THAT-MEAN-SOMETHING.md` | make every green REDS-when-broken (hollow tests, skip-green gates, vacuous theorems, silent no-op mechanisms) + plain quality (inefficiency, bad patterns, reinvented wheels). Owns the CI-meaningfulness sweep + the Lean FFI archive shrink (trim 272MB→23.87MB; generate-only next) |
| **multichain-settlement** | `GOAL-MULTICHAIN-SETTLEMENT.md` | dregg = the trustless plug for every chain — proof-carrying settlement + non-custodial proof-of-holdings governance (Solana/EVM/Cosmos) + the STARK→EVM wrap made efficient (chain/gnark BN254-native-hash) + verified light clients toward rung-3 folded. Owns chain/gnark + bridge/light-clients + gov cross-chain spine + dregg-deploy; stark-kill owns trace_rotated.rs/AIRs |

**Shared-tree discipline (all lanes):** additive-only in swarms; commit surgically — NEVER
stage another lane's files (e.g. `dregg-lean-ffi/src/lib.rs`, another `GOAL-*.md`); no git
from subagents; unsigned commits fine. The purge-unverified-Rust philosophy is shared by
storage-in-lean, stark-kill, and the "purge-campaign" commits — coordinate, don't collide.

*(Maintained by the stark-kill lane 2026-07-07; append your lane if it's missing.)*
