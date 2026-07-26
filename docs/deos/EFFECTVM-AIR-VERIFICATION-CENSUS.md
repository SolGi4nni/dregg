# EffectVM AIR verification census — "what does the AIR NOT verify?"

A grounded, op-by-op audit of the EffectVM AIR (the deployed IR-v2 multi-table
descriptor circuit) answering one question: **for every op / declared column, is
the property GENUINELY forced in-circuit (so a light client that checks the STARK
witnesses it), or is the real check delegated to an out-of-circuit / off-AIR
verifier (a TRUSTED SURFACE the bare STARK does not witness)?**

Provenance: triggered by the `Effect::Custom` `proofBind` finding — the in-AIR op
is `| .proofBind _ => True` (`metatheory/Dregg2/Circuit/DescriptorIR2.lean:601`);
the genuine sub-proof check lives outside the EffectVM STARK: the deployed fold
re-proves the sub-proof leaf and folds it in-circuit at the aggregation layer, and
that is now the ONLY enforcement — there is no off-AIR re-executor check. (The Rust
`verify_proof_bind` this line used to name died with stark-kill `dd038c08e`; nothing
verifies a proof-bind off-AIR any more, and since the fold's no-carrier arm is
fail-closed for the custom member (`require_no_unbacked_proof_bind`) a custom leg
cannot reach a root without that in-circuit connect.) This census asks what ELSE is in that
class.

Verified against Lean (`DescriptorIR2.lean`, `CircuitOpenFronts.lean`) and the
deployed Rust AIR (`circuit/src/descriptor_ir2.rs`, `circuit/src/effect_vm/{air,
pi,trace,trace_rotated,columns}.rs`, `turn/src/executor/{proof_verify,authorize}.rs`)
at HEAD.

## Classification key

- **(1) GENUINELY ENFORCED** — a real in-AIR polynomial / bus constraint forces
  the property; the light client witnesses it. The good case.
- **(2) ROW-LOCAL-`True`, FORCED ELSEWHERE IN-CIRCUIT** — the per-row denotation
  is `True`, but the content is a GLOBAL leg realized by an in-circuit LogUp bus
  (memory / universal-memory balance). A bad witness cannot satisfy the bus →
  fail-closed → NOT a soundness hole.
- **(3) TRUSTED-OUT-OF-CIRCUIT** — the in-AIR op only records columns / PI; the
  real check is an off-AIR Rust verifier (recursive STARK verify, signature
  verify). The bare EffectVM STARK does NOT witness it. **These are the answer.**
- **(4) CARRIED-NOT-FORCED column** — a column the AIR records but no constraint
  binds (a column-level version of (3)).

## The op grammar (`VmConstraint2`, `DescriptorIR2.lean:390`)

| op | per-row semantics | in-circuit realization | class | honest? |
|----|-------------------|------------------------|-------|---------|
| `base (Gate/Boundary/Transition)` | polynomial `= 0` (`VmConstraint.holdsVm`) | `assert_zero` / `when_first/last/transition` | **1** | n/a |
| `base (PiBinding)` | `local[col] − pi[i] = 0` (`Emit/EffectVmEmit.lean:490-495`) | boundary `assert_zero` binding column↔PI | **1** | n/a |
| `lookup (Lookup)` | `tuple.map eval ∈ table` (`DescriptorIR2.lean:450`) | LogUp bus (`BUS_FACT`, byte/range buses) | **1** | n/a |
| `mapOp (MapOp)` | `opensTo`/`writesTo` row-local (`:514`) | Poseidon2 Merkle path on the chip bus `BUS_P2`; functional under CR (`opensTo_functional :485`) | **1** | n/a |
| `memOp (MemOp)` | `True` row-local (`:598`) | global `Satisfied2` legs: `memDisciplined`/`memBalanced`/`memTableFaithful` → `BUS_MEM_LOG/CHECK/ADDRS` LogUp (Blum `memcheck_sound`) | **2** | honest |
| `umemOp (UMemOp)` | `True` row-local (`:600`) | global `Satisfied2U` legs: `umemBalanced`/`umemDisciplined`/`umemAddrs`/`umemNullifierInsertOnly` → `BUS_UMEM_LOG/CHECK/ADDRS` LogUp (`universal_memory_sound`) | **2** | honest |
| `windowGate (WindowConstraint)` | two-row poly `= 0` (`:368`) | windowed `assert_zero` (`when_transition`) | **1** | n/a |
| `proofBind (ProofBind)` | `True` row-local (`:601`) | **NONE in the EffectVM STARK** — no bus, bounds-check only (`descriptor_ir2.rs:1457-1465`); the eight `(commit, vk)` columns are published as descriptor PIs, and the deployed FOLD backs them: the custom sub-proof leaf is re-proven in-circuit and its 8-felt PI commitment recomputed and `connect`ed lane-by-lane (`prove_custom_binding_node_segmented`); the fold's floor is the named `EngineBinding`/`recursive_sound` hypothesis | **3** (bare STARK) / in-circuit at the fold | honest |

`base`/`lookup`/`mapOp`/`windowGate` are genuinely enforced. `memOp`/`umemOp` are
row-local `True` but their content rides real in-circuit LogUp buses (the memory /
universal-memory balance arguments are arithmetized in the deployed descriptor —
`descriptor_ir2.rs:1-30`, bus constants `:349-361`), so they are fail-closed, not
holes. **`proofBind` is the only op kind with no realization inside the EffectVM
batch STARK** — no bus, no polynomial; the column pair `(commit, vk)` is
declaration-and-bounds only there. Its content is realized in-circuit one layer up:
the deployed recursion fold re-proves the custom sub-proof as a leaf and recomputes
+ `connect`s the commitment (`custom_proof_bind.rs:1-21`), so a forged or unbacked
commitment is UNSAT at the fold — but a client running ONLY the bare EffectVM STARK
does not witness it.

## The PI-carried surfaces (column-level, not `VmConstraint2` ops)

The EffectVM AIR records many values in the public inputs that an **off-AIR
verifier** (`turn::executor::proof_verify` / `verify_effect_binding_proofs`) reads.
Two distinct sub-classes:

### Benign: off-AIR PI-MATCH reconstruction (class 2-equivalent)

The bulk of "off-AIR verifier" comments in `pi.rs` / `trace.rs` describe the
verifier RECONSTRUCTING a value from PUBLIC turn data (call_forest, ACTOR_NONCE,
emit-event counts, bilateral roots, note/burn schemas, …) and matching it to the
in-circuit-bound PI. Because (a) the PI is bound to the trace in-circuit via
`PiBinding`, and (b) the reconstruction is a deterministic function of public data,
**a light client reproduces both legs itself** — this is the standard public-input
contract, NOT a trusted surface. Examples: `pi.rs:125,597,609,649,679`;
`trace.rs:23,644,1019,1322`. No action needed; named here so they are not mistaken
for class (3).

### Trusted: off-AIR recursion / signature (class 3)

| surface | PI slots | real check (outside the EffectVM STARK) | status | honest? |
|---------|----------|----------------------|--------|---------|
| **Custom proof_bind** | `CUSTOM_PROOFS_*` + descriptor cols 68/72 (+ the member-local commit-teeth columns) | deployed fold ONLY: the sub-proof leaf is re-proven in-circuit, its commitment recomputed and lane-connected (`prove_custom_binding_node_segmented`); there is NO off-AIR re-executor path (`verify_proof_bind` died with stark-kill `dd038c08e`) | LIVE; commitment is the full 8-felt `WideHash` (~124-bit, `PROOF_BIND_COMMIT_WIDTH`, `custom_proof_bind.rs:87-104`); old 4-felt custom artifacts are REFUSED at the versioned admission boundary (`require_custom_carrier_vk8`), and a custom leg presented WITHOUT a carrier witness is refused at the fold's arm selection (`require_no_unbacked_proof_bind`) so the connect cannot be dodged | honest |
| **Sovereign transition proof (Phase 2)** | `SOVEREIGN_TRANSITION_PROOF_{VK_HASH,COMMITMENT}`, `HAS_TRANSITION_PROOF` (`pi.rs:257-267`) | none — **RETIRED**: `execute.rs:938-948` fails closed on any v1 `transition_proof`; `populate_sovereign_witness_pi` has no caller | **RETIRED / REPURPOSED** — the commitment column carries the sovereign AUTHORITY DIGEST, bound in-circuit by the re-proved sovereign-authority leaf + `prove_sovereign_binding_node_segmented` (`pi.rs:209-231`); no inner recursive verifier exists or is trusted | honest |
| **Sovereign witness signature + sequence** | `SOVEREIGN_WITNESS_{KEY_COMMIT,SEQUENCE}`, `IS_SOVEREIGN_CELL` (`pi.rs:240-252`) | Ed25519 signature verify off-AIR, inline in the executor: `VerifyingKey::verify_strict` over `SovereignCellWitness::signing_message_for_federation` (`execute.rs:878-895`) + monotonic-sequence chain-walk just below (`execute.rs:896-908`) | LIVE; PI carries only a 4-felt key DIGEST + sequence, "backed off-AIR by the actual signature verification" (`pi.rs:234-238`) | honest |

All are explicitly NAMED at the code level (the Lean comments, the Rust
`pi.rs`/`trace.rs` doc-comments, and `docs/deos/CUSTOM-VK-AUTHORIZATION.md` are all
scrupulous). None is a *laundered* overclaim (no code/doc asserts these are
in-circuit where they are not). The live rows ARE genuine trusted surfaces for a
client that runs only the bare EffectVM STARK: it does not witness them and must
additionally verify the fold / run the signature verify (or trust the federation
verifier that does).

## Re-verdict on the two completeness claims

### (a) "proofBind was the last vacuous gate" (commit `b597fe342`)

**Partly true, but easy to misread.** What the commit actually did: it closed the
last vacuous per-effect *gate* (`Effect::Custom`'s `descriptorRefines` was vacuous
— a prover could bind any sub-proof) by adding a **verifier-side** genuine
recursive verify (`custom_proof_bind.rs`). The commit body is scrupulous:
"verifier-side soundness, VK-FREE; no Lean".

But it did NOT make `proofBind` enforced *inside the EffectVM AIR*:

- The in-AIR op is STILL `| .proofBind _ => True` (`DescriptorIR2.lean:601`) and
  STILL bounds-only in Rust (`descriptor_ir2.rs:1457-1465`).
- THREE row-local `=> True` ops remain (`memOp`, `umemOp`, `proofBind`). The first
  two are benign (class 2 — forced by in-circuit LogUp buses). `proofBind` is the
  one whose content lives outside the EffectVM batch STARK.
- So "GENUINELY verifies" is true at the fold and verifier-side, false inside the
  EffectVM AIR itself; the recursion soundness is the named
  `EngineBinding`/`recursive_sound` hypothesis (`DescriptorIR2.lean:976`), not an
  arithmetized EffectVM constraint.

The in-circuit fix has since landed at the fold layer: the commitment is the full
8-felt `WideHash` (~124-bit, `PROOF_BIND_COMMIT_WIDTH`; old 4-felt custom artifacts
are refused at `require_custom_commit_teeth_v2`, `custom_proof_bind.rs:87-104`), and
the deployed fold's custom leaf re-proves the sub-proof and recomputes + `connect`s
the commitment lane-by-lane (`prove_custom_binding_node_segmented`, wired into
`prove_chain_core_rotated`) — a forged or unbacked commitment is UNSAT at the fold.
What remains named is the floor: the fold rests on `recursive_sound`, and the bare
EffectVM STARK alone still does not witness the sub-proof.

### (b) `Circuit.CircuitOpenFronts.countOpenFronts = 0` / "32/32 effects"

**Honest for what it measures; it UNDERCOUNTS the trusted-surface class.**
`countOpenFronts` is `openFronts.length` (`CircuitOpenFronts.lean:88-117`), and
`openFronts` is the **per-effect adversarial-witness-EXTRACTION** lane (circuit ⊑
spec refinement: an arbitrary PI-bound satisfying trace forces the genuine kernel
step). That lane is genuinely closed for the 32 enumerated effects.

What the metric does NOT count:

1. Row-local `=> True` ops whose content is a global leg (`memOp`/`umemOp` — benign
   anyway, but invisible to this count).
2. The `proofBind`/Custom recursion — realized in-circuit at the fold, unwitnessed
   by the bare EffectVM STARK (and `Effect::Custom` is not even one of the 32 — it
   rides the `closedLogExtract_all_genuine` catch-all
   `| (n+1) => rds.other (n+1)`, `ClosureFanoutGenuine.lean:1186`; see the apex
   memory correction).
3. The sovereign off-AIR signature surface (table above; the Phase-2
   transition-proof surface is retired).

So `countOpenFronts = 0` is NOT a "the AIR verifies everything" certificate — it is
"no open refinement front in the extraction lane." The trusted-out-of-circuit
surfaces sit OUTSIDE its accounting. The Custom undercount was already corrected in
`project-circuit-soundness-apex.md`; the sovereign surfaces are an additional class
this census surfaces.

## Ranked answer — "what else does the EffectVM AIR NOT verify?"

1. **Custom program correctness** (`Effect::Custom` / `proofBind`) — the bound
   sub-proof is not witnessed by the EffectVM batch STARK itself. On the deployed
   fold path it IS realized in-circuit one layer up: the sub-proof leaf is
   re-proven and its full 8-felt (~124-bit) PI commitment recomputed in-circuit and
   lane-connected (`custom_proof_bind.rs:87-104`; 4-felt artifacts refused at
   `require_custom_commit_teeth_v2`), resting on the named `recursive_sound` floor.
   Already documented (`docs/deos/CUSTOM-VK-AUTHORIZATION.md`).
2. **Sovereign witness Ed25519 signature + replay sequence** — signature verified
   off-AIR inline in the executor (`verify_strict`, `execute.rs:878-895`; distinct
   from the action-authorization `verify_ed25519_signature` at `authorize.rs:933`),
   replay via off-AIR chain-walk; the AIR carries only
   a 4-felt key digest + sequence. By design the signature binds the full 256-bit
   key off-circuit; honest but a genuine trusted surface for the bare STARK.

RETIRED from this list: the **sovereign inner transition proof (Phase 2)**. There is
no staged inner recursive verifier to trust — `execute.rs:938-948` fails closed on
any v1 `transition_proof`, and the commitment column is repurposed to carry the
sovereign authority digest, bound in-circuit by the re-proved sovereign-authority
leaf + binding node (`pi.rs:209-231`).

Everything else in the EffectVM AIR is genuinely enforced (class 1) or fail-closed
via an in-circuit LogUp bus (class 2). The trusted-surface class for the bare STARK
is exactly these two recursion/auth surfaces — plus the broad benign off-AIR
PI-match reconstruction surface (light-client-reproducible, not a hole).
