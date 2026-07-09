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

**Shared-tree discipline (all lanes):** additive-only in swarms; commit surgically — NEVER
stage another lane's files (e.g. `dregg-lean-ffi/src/lib.rs`, another `GOAL-*.md`); no git
from subagents; unsigned commits fine. The purge-unverified-Rust philosophy is shared by
storage-in-lean, stark-kill, and the "purge-campaign" commits — coordinate, don't collide.

*(Maintained by the stark-kill lane 2026-07-07; append your lane if it's missing.)*
