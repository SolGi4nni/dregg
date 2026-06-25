# dregg — adversarial assurance assessment

*Audience: a reviewer who has built l4v. No spin. The question is not "is there impressive
formal work here" (there is) — it is "does this give a real reason to trust the **deployed**
system, and how far is it from binary-to-spec, single-top-theorem, minimal-and-explicit-TCB
assurance." All file:line references are to the tree as it stands at the time of writing.
Several gaps an earlier internal critique recorded have since been closed in the Lean corpus;
this document was written against the **current** source, re-verified by reading the actual
theorem statements and proofs, not their headings or prose.*

---

## 1. Verdict (one paragraph)

dregg's assurance today is a **strong, honestly-bounded model-level case with a thin, largely
unverified bridge to the running binary** — genuinely above the typical "we wrote some Lean"
bar, and not l4v-grade. Within Lean it now has what it lacked a snapshot ago: a single composed
theorem, `deployed_system_secure` (`AssuranceCase.lean:733`), whose conclusion is the literal
conjunction A ∧ B ∧ C ∧ D ∧ E and whose legs are real keystones (no `:= trivial` apexes
survive); and the unfoolability headline now **derives** conservation-over-history from `verify
agg.root` alone (`verified_history_conserves` / `kernelChained_of_verified`,
`HistoryAggregation.lean:374,342`), discharging the prover-supplied `StateChained` state-continuity
hypothesis that an earlier review flagged as critical — `root_tooth_pins_kernel`
(`HistoryAggregation.lean:205`) genuinely recovers *state* equality `s.post.kernel = s'.pre.kernel`,
not merely commitment equality, under the Poseidon CR set. Those are real closures and a reviewer
should credit them. But the gap between that Lean corpus and the **binary the node ships** is
essentially unverified, and it is exactly the gap l4v exists to close: (i) the verified Lean
executor is **not authoritative** — on the live commit path it runs as a co-producer and its state
is installed *only when its root matches the unverified Rust executor*, which wins every
disagreement (`lean_apply.rs:1143`); (ii) the deployed credential check is an **echo oracle** in
Lean while real ed25519/STARK verification happens in **unverified Rust** outside the drawn
boundary (`FFI.lean:3167`, `authorize.rs:407-417,1410`); (iii) the wire **codec is in the TCB and
explicitly "not proved"** (`FFI.lean:92`), and the circuit a light client checks is a
**hand-re-parsed second/third interpreter** of a Lean-emitted descriptor, agreement by byte-pinning
+ tests, not a refinement theorem (`effect_vm_descriptors.rs:65`); (iv) the unfoolability headline's
per-leaf circuit soundness (`leaf_sound`) is an **assumed structure field witnessed only by an
accept-everything verifier** (`RecursiveAggregation.lean:127,312`); (v) the deployed consensus is
**n=1 and skips the ordering rule**, so its Byzantine-safety theorems are vacuous on the running
node (`blocklace_sync.lean … blocklace_sync.rs:548,658`). Net: there is a real reason to trust the
**abstract kernel** under a small, mostly-honest crypto floor, and a real reason to trust that *if*
the binary computes the model *then* the properties hold — but no machine-checked reason to believe
the binary computes the model. l4v's headline deliverable (the running artifact refines the spec,
the spec is the security property, the TCB is a closed explicit list) is the thing that is absent.

**Distance to l4v-grade.** The *Lean composition* is now roughly where an l4v top-level theorem
sits: one statement, real antecedents. The *spec-to-binary refinement* — the entire reason l4v is
hard and respected — does not exist here in any machine-checked form. That, plus the missing
cryptographic-composability (UC) layer and the n=1 consensus collapse, is the whole remaining
distance, and it is large.

---

## 2. What is genuinely established (do not undersell this)

These are real, checked, non-vacuous (witnessed both holding and rejecting), and several are not
easy. They are the strongest claims I was able to confirm by reading the proofs.

1. **A single composing security theorem now exists.** `deployed_system_secure`
   (`AssuranceCase.lean:733-789`) has conclusion `A ∧ B ∧ C(c1) ∧ C(c2) ∧ D ∧ E1 ∧ E2`, each leg
   discharged from a named keystone over a deployed-system input (a committed `execFullForestG`
   forest, a live `recCexec` move, a committed `noteSpend`, a verified aggregate). It is
   `#assert_axioms`-clean on `{propext, Classical.choice, Quot.sound}`. The earlier "five
   side-by-side aggregations, two `:= trivial` anchors" structure is gone; the apex carries content.
   (Its real limitation is subject-independence — MEDIUM-7 — but it is a genuine conjunction, not a
   prose DAG.)

2. **The running-entry soundness is real and over the FFI body.** `running_entry_sound`
   (`AssuranceCase.lean:633`) conjoins per-asset conservation, per-edge non-amplification, and
   per-node gated attestation over `execFullForestG` — the body behind the
   `dregg_exec_full_forest_auth` export the node invokes — with fail-closed teeth
   (`execFullForestG_unauthorized_fails`). The forest delegation edges are genuinely **executed**
   through `delegateAttenA`/`recCDelegateAtten` against threaded state, not decorative; the earlier
   "delegation is decorative" concern is closed at this layer.

3. **Unfoolability now derives conservation from verification — the previously-critical gap is
   closed in Lean.** This is the most important change since the earlier critique, and I verified it
   in the proof bodies, not the comments. `kernelChained_of_verified` (`HistoryAggregation.lean:342`)
   derives whole-chain kernel continuity from the **verified** `ChainBound` root tooth via
   `root_tooth_pins_kernel` (`:205`, which delivers genuine `s.post.kernel = s'.pre.kernel` *state*
   equality through `recStateCommit_binds_kernel` under the full Poseidon CR set plus a
   `recKExec`-preserved `AccountsWF` invariant). `kernelChained_conserves` (`:306`) then gets
   conservation by direct induction on per-step `recKExec_conserves`, never touching the receipt log.
   The composite `verified_history_conserves` (`:374`) takes only a *public* genesis pin plus the
   non-cryptographic structural envelope `SeamStruct` (matched turn-contexts + `AccountsWF`) — **no
   `StateChained` prover hypothesis**. `unfoolability_guarantee` (`AssuranceCase.lean:536`) conjoins
   this with `light_client_verifies_whole_history`, and the anti-ghost teeth are real (positional
   `Forall₂` leaf-pairing defeats leg-swap; `tampered_aggregate_cannot_bind`).
   The one honestly-named residual: the *full* `Run` (`attested_history_is_run`) still needs
   `StateChained` because it includes the receipt **log**, which the §8 state root does not bind —
   but *conservation* does not, and that factoring is correct.

4. **Per-layer keystones have teeth.** `amplifying_grant_rejected`, `chC_bad_not_bridge`,
   `noteSpendStmt_replay_rejected`, `IssuerMove.recKMintAsset_breaks_exact` each falsify the
   predicate on a tampered input — the guarantees discriminate, they are not `:= True`.

5. **Per-effect FULL-STATE circuit soundness, per cell — not a conservation projection.**
   For transfer/mint/burn, `transferDescriptor_full_sound` + `transferDescriptor_commit_binds_state`
   force the whole absorbed post-state-block and bind it injectively into the published commitment
   under the named `Poseidon2SpongeCR`, with a concrete tamper-rejected witness. This is genuine
   whole-state binding *per cell*, which a conservation-only bridge could never deliver.

6. **Conservation is exact-zero as a reachability invariant, and the deployment caveats are
   discharged on the chain.** `reachable_total_zero` proves `∀ a, recTotalAsset = 0` on every
   reachable state (`AssetId := CellId`, issuer wells carry −supply). The two previously-named
   deployment gaps (devnet genesis seeding; legacy fee-burn epilogue) are reported closed on the
   deployed chain: signed `i64` wells, `GenesisMove` from a `−total_issued` issuer well,
   fees-as-moves to a zero-seeded fee well (`AssuranceCase.lean:893-904`).

7. **The crypto floor is disciplined.** Every cryptographic assumption enters as a `Prop` typeclass
   field / hypothesis, never as an `axiom`; no load-bearing `axiom` decls exist (only a Widget demo).
   The sponge-CR reduction is real (`spongeCR_of_reduction`, a genuine Merkle–Damgård induction, both
   polarities). The §8 `PortalFloor` lists each primitive with a carrier `Prop` + a `*_sound` theorem
   + a `Forge`/`Collide` instance making the carrier provably false (no surviving `:= True`). The
   host-context seam is *partially* discharged (`HostCorrespondence.admissible_sound_of_reflects` +
   under-report teeth).

8. **The integrity backbone is a clean memory-program square.** `UniversalBridge` proves, for the
   three compressed verbs (gwrite/move/create), that the total 17-field-plus-receipt-log projection
   of the post-state equals the Blum-trace fold over the pre-state projection
   (`move_is_memory_program` et al.) — a real constructive "the receipt determines the whole
   post-state" fact at the step level.

The named-seams discipline (the case names the prover partition, the host-fed inputs, the producer
coverage, the `RESERVED` column) is itself a strength a reviewer should credit: the case mostly does
not launder its own gaps. Where it overstates, it does so in prose headings, not in the theorem
statements.

---

## 3. The gaps, ranked by how badly each undermines "a reason to trust the deployed system"

The ranking is by **deployment impact**, not by Lean elegance. The Lean composition is now in good
shape; the binary bridge is where trust actually leaks, so the deployed-binary seams dominate.

### CRITICAL-1 — The verified executor is not authoritative; the unverified Rust executor wins every disagreement.

- **Claimed.** "THE SWAP" — the verified Lean executor is the authoritative state producer; the
  Rust `TurnExecutor` is demoted to a differential cross-check. The proofs are about the running
  system because the running system calls the proved function.
- **Actually established.** On the live commit path, `produce_via_lean` (`turn/src/lean_apply.rs`)
  runs **both** Lean and Rust and installs the Lean post-state **only when**
  `lean_committed == rust_committed && lean_root == rust_root` (`lean_apply.rs:1143`). On
  disagreement it keeps the **Rust** post-state (the "conservative, keeps Rust" `Fallback`); on any
  unmappable/root-gap effect it falls back to Rust before Lean even runs (`:1104-1134`).
- **The gap.** The deployed transition correctness rests on the **Rust** executor — the artifact
  dregg2 exists to *replace because it is buggy*. A verified executor that is committed only when it
  reproduces the unverified executor's root cannot tighten a wrong Rust accept that yields the same
  root, cannot override a Rust reject, and cannot be the reason to trust the transition. "The running
  system calls the proved function" is true, but the proved function's output is gated behind
  agreement with the thing being replaced. This is the inverse of an l4v refinement (there the C code
  *is* the subject; here the verified subject is a redundant co-producer). **This single fact
  dominates the deployed trust story** — until it is inverted, nothing downstream changes it.
- **Refs.** `turn/src/lean_apply.rs:1098-1173`; `node/src/executor_setup.rs` (`execute_via_producer`).

### CRITICAL-2 — No machine-checked spec-to-binary refinement; the codec is in the TCB and unproven.

- **Claimed.** The Lean kernel *is* the executor; "no field of the post-state left uncommitted"; the
  crypto floor is "the complete trust boundary; nothing else is load-bearing" (`ASSURANCE.md:135`).
- **Actually established.** The node calls a **String → String** export (`execFullForestAuthStep`,
  `FFI.lean:3313`) whose body invokes the proved `execFullForestG`. The proved theorems are over the
  abstract `FullForestG`, one type-boundary away from the String the FFI receives. Between them sit:
  an unverified Rust marshaller (`lean_shadow.rs` `effect_to_wire`, `ledger_to_wire_state`), the Lean
  parser `parseWWire` + lift `liftForestG`, and a Rust reconstitutor (`lean_apply` `wire_state_to_ledger`).
  The wire codec is **explicitly labeled "TCB, not proved"** at four sites
  (`FFI.lean:92,752,1041,3085`); there is no parse round-trip lemma and no theorem that the
  String→String export refines `execFullForestG`.
- **The gap.** This is precisely the binary-to-spec link l4v machine-checks and dregg asserts (via
  `assert_axioms` + guard examples). The Lean→C / lean-runtime / `libdregg_lean.a` link boundary is
  additionally in the TCB and unmentioned by the §2 floor, so the literal claim "nothing else is
  load-bearing" is false: the actual TCB is `{crypto carriers} ∪ {wire codec} ∪ {Lean→C
  runtime/link} ∪ {Rust verify+routing}`.
- **Refs.** `FFI.lean:92,752,3285,3313-3332`; `turn/src/lean_shadow.rs`; `docs/ASSURANCE.md:128-135`.

### CRITICAL-3 — The deployed WHO-leg is an echo oracle; real signature/STARK verification is unverified Rust outside the boundary.

- **Claimed.** "No out-of-band 'this turn was authorized' premise"; the per-node gate enforces
  credential validity.
- **Actually established.** The verified Lean WHO-leg `portalVerify` over the deployed
  `cryptoAuthPortal` realizes credential-check as `Crypto.Reference`'s **echo** oracle — "a genuine
  credential (proof echoes statement)" (`FFI.lean:3167`); `CryptoKernel.verify stmt sig` decides
  `stmt = sig`. Real ed25519 (`VerifyingKey::from_bytes` + `verify_strict`) and real `stark::verify`
  run in **unverified Rust** (`authorize.rs:407,417,882,892,1246,1410,1541`). The §8 `PortalFloor`
  extern oracles are declared but consumed nowhere on the deployed path. Additionally the deployed
  *root-node* WHAT and caveat legs are **pinned to admit**: `liftForestG` installs
  `.unchecked (Guard.all [])` with `authModeAdmits = true` (`FFI.lean:3164,3249`); only child edges
  gate on `keep`/`parentCap`, and caveat *content* is chosen by the unverified Rust marshaller.
- **The gap.** The "no out-of-band authorization premise" claim is false for the deployed WHO-leg — a
  trusted unverified Rust signature check *is* that premise, outside the drawn boundary.
  `running_entry_sound` proves a full three-leg gate *with teeth over the abstract `FullForestG`*, but
  the **deployed** wire path enforces a strictly weaker gate (two legs admit-pinned, the WHO-leg
  delegated to Rust). The proved teeth do not all bind the deployed turn.
- **Refs.** `FFI.lean:3163-3170,3249-3267,3313-3332`; `turn/src/executor/authorize.rs:407-417,882-892,1410`.

### HIGH-4 — The circuit a light client verifies is a re-parsed second interpreter; AIR⟺executor agreement is test-attested, and the per-leaf soundness is *assumed*.

- **Claimed.** "Zero Rust-authored constraints" — the descriptor is emitted from Lean, so a light
  client "verifies the same object the executor committed"; per-effect circuit⟺executor soundness is
  "already proved" and lifted to the leaf boundary.
- **Actually established.** The descriptor is emitted by a Lean executable to JSON, `include_str!`'d
  with sha256 fingerprints (`effect_vm_descriptors.rs:65`), then **re-parsed by Rust**
  (`parse_vm_descriptor`) into a *second* interpreter (`EffectVmDescriptorAir::eval`); the Lean
  soundness is over `satisfiedVm`, a *third* interpreter. Their agreement is by byte-pinning +
  differential tests, **not** a refinement theorem. Worse, in the unfoolability composition the
  per-leaf soundness `leaf_sound` is a **structure field (assumption)** of `EngineSound`
  (`RecursiveAggregation.lean:127`), never discharged from the `*_compile_sound` theorems, and its
  only non-vacuity witness `real_engine_sound` (`:343`) uses `RealProof := Unit`,
  `acceptAll := fun _ => true` (`:312`) — so it is satisfied *trivially* by an accept-everything
  verifier that never exercises circuit soundness.
- **The gap.** Two untrusted seams the kernel triple does not cover: (a) `satisfiedVm` (Lean
  denotation) ⟺ `EffectVmDescriptorAir::eval` (the AIR the prover actually constrains) ⟺ the JSON
  parser; (b) the leaf-to-statement implication itself. So "every turn executed correctly" rests on an
  **assumed** leaf, witnessed only by an accept-all verifier, with a hand-re-parsed evaluator between
  the verified denotation and the proven circuit. A real aggregation/extraction bug between "proof
  verified" and "executor ran" would live precisely here. This is the gap l4v's whole point is to
  forbid.
- **Refs.** `circuit/src/effect_vm_descriptors.rs:65`; `sdk/src/full_turn_proof.rs:387-392`;
  `metatheory/Dregg2/Circuit/RecursiveAggregation.lean:127,312,343`;
  `metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean` (`satisfiedVm`).

### HIGH-5 — The prover partition: a real, open, named subset of deployed turn shapes is decided by unverified hand-AIR.

- **Claimed.** One circuit, Lean-derived; producer coverage burns down toward total.
- **Actually established.** The Lean-emitted descriptor AIR is the default only for the graduated
  selectors (`CUTOVER_READY_SELECTORS`); every other turn shape falls back — logged, not silent — to
  the legacy hand-written AIR (`circuit/src/effect_vm_p3_full_air.rs`, `full_turn_proof.rs:387`),
  where circuit⟺kernel agreement is **test-attested, not theorem-attested**. On the producer side, the
  verified executor is authoritative only for the root-agreeing covered set (~22 of 27 effect kinds);
  `Refusal`/`ReceiptArchive` are root-gaps decided by Rust, and `CreateCell` is deliberately not
  projected.
- **The gap.** For any non-graduated shape, the circuit a light client verifies is **not**
  theorem-attested to agree with the verified kernel, and a structural primitive (`CreateCell`) plus
  the audit effects are in the unverified-Rust set. Per the project's own stated law a named gap is
  not a deliverable; this is carried, not closed. l4v-grade requires the fallback set empty.
- **Refs.** `sdk/src/full_turn_proof.rs:387-392`; `turn/src/lean_shadow.rs` (covered-set partition);
  `AssuranceCase.lean:803-814` (seam 1).

### HIGH-6 — Deployed consensus is n=1 and skips the ordering rule; Byzantine-safety theorems are vacuous on the running node.

- **Claimed.** Lean proofs establish Byzantine (DAG-BFT) safety; adversary assumptions are structure
  fields, not axioms.
- **Actually established.** The abstract `cordial_agreement` / `bft_safety` hold under an *assumed*
  `BFTModel` whose only inhabitant is an **empty adversary with zero Byzantine** (`BFT.lean:195`), and
  liveness is an **assumed** oracle `gst_liveness` (`World.lean:104`) with the pacemaker left open.
  The deployed node runs **solo (n=1)**: it finalizes every block immediately and **does not run
  `tau`/the ordering rule** (`blocklace_sync.rs:548,658,945`). Lean approval uses a *global*
  equivocator predicate while Rust reads *observer-local* equivocation; the quorum is `n − f` under a
  separate threshold hypothesis, not the Rust two-thirds floor (unification pending, task #170). There
  is **no consensus apex** in `AssuranceCase` — consensus is not one of the composed guarantees.
- **The gap.** At n=1 the fault budget is zero and quorum intersection is trivial, so the deployed
  configuration **voids** the very property the proofs target; the many-validator path exists in code
  but no deployed multi-validator devnet exercises it, and the heart of safety (the adversary model)
  and liveness are both *assumed*, never derived from signatures/gossip/a pacemaker.
- **Refs.** `turn/src/blocklace_sync.rs:548,658,945`; consensus Lean (`…/BFT.lean:69-88,195,293-299`,
  `World.lean:104`, the ordering vs `CordialMiners` equivocation-predicate divergence).

### HIGH-7 — No UC / simulation security; "cannot be fooled" is a soundness lemma under assumed crypto, and the CryptHOL discharge is for a primitive the system does not deploy.

- **Claimed.** "Unfoolability" — a thin verifier cannot be fooled into accepting an incorrect
  protocol evolution — presented in user-facing docs as THE property the design exists to protect; the
  `binding`/`unlinkable` carriers are "discharged by a real proof in a real UC tool."
- **Actually established.** `light_client_verifies_whole_history` is a **soundness-of-the-proof-system**
  statement, not a game-based cryptographic theorem: IF `verify agg.root` accepts AND the FRI/STARK
  carrier holds AND Poseidon2-CR holds, THEN the history folded correctly — **no adversary, no
  advantage bound, no probability**. The dynamic-UC layer is a `DynamicUCResidual` (or perfect-fragment
  `PerfectUC`) whose composition/PPT/negligibility fields are discharged only for a toy reference with
  literal `True`; the static `unfoolable_of_floor` reduction is instantiated only to a `ℕ`/echo toy,
  never to `recCexec`/`stark::verify`. The CryptHOL discharge proves **standalone Pedersen** F_com
  realization (real, AFP-grade) — but the deployed shielded commitment is Poseidon2/sponge, "this Lean
  `commit` IS that Isabelle Pedersen" is a **human-checked** cross-logic correspondence
  (`UCBridge.lean:36-41`), and the green Isabelle build was **not reproduced** on the dev machine
  (`UCBridge.lean:52-56`).
- **The gap.** The headline product claim is an intuition backed by a structural lemma under assumed
  crypto, presented with the rhetorical force of a proven security game; concurrent-session / replay /
  cross-session attacks are unmodeled. The "discharged in a real UC tool" claim is real for an object
  the system may not deploy, joined by prose, and silently widens the trust base to Isabelle's kernel +
  the AFP + an unverified transport + an unreproduced build.
- **Refs.** `metatheory/Dregg2/Crypto/LightClientUC.lean:159,323-375`;
  `metatheory/Dregg2/Crypto/UCBridge.lean:36-56`; `uc-crypthol/Dregg2_FCom.thy`; `docs/ASSURANCE.md`.

### MEDIUM-7 — The composed apex conjoins facts over *independent* subjects, not one turn/history end-to-end.

- **Claimed.** `deployed_system_secure` shows the guarantees **chain** over "the things the deployed
  node actually produces"; "a single committed forest is simultaneously non-amplifying, conserving,
  and integrity-attesting."
- **Actually established.** The theorem's hypotheses bind a forest `f`, a move `sm/tm`, a noteSpend
  `nf/k`, and an aggregate `agg/g/steps` as **four independently universally-quantified** subjects
  (`AssuranceCase.lean:733-754`). The integrity-C(c2) leg (`move_is_memory_program`) is over an
  *arbitrary* `recCexec` move, **not** over the forest `f` the node ran; D is over an arbitrary
  noteSpend; E is over an arbitrary aggregate.
- **The gap.** This is a genuine `∧` (a real improvement over the prior side-by-side pile), but it
  proves "for any committed X and any committed Y …, all five hold," not "this one deployed turn, and
  the history it extends, are jointly secured." The whole-post-state integrity (C2) is therefore *not*
  shown to bind the running-entry forest's post-state; the C delivered over `execFullForestG` is the
  per-node ledger/chainlink obligation (c1), a different proposition from the receipt-binds-whole-
  post-state memory-program fact (c2). The reader who wants "the turn the node committed is fully
  secured, and it chains into the history" does not yet get it from one theorem.
- **Refs.** `AssuranceCase.lean:733-789` (separate binders, separate keystones).

### MEDIUM-8 — Integrity's whole-post-state binding is per-step (3 verbs) and not yet in-circuit per turn.

- **Claimed.** "A receipt binds the WHOLE post-state" as the integrity guarantee.
- **Actually established.** The memory-program square is proved for exactly **three** single-step
  verbs (gwrite/move/create, `UniversalBridge`); the integrity apex is over a single `recCexec` move.
  No theorem composes these to a whole turn or to `execFullForestG`. By the case's own admission
  (`AssuranceCase.lean:856-891`) the universal-memory commitment is bound **today by the kernel
  theorems, not by the per-turn proof** — the in-circuit per-turn binding is the staged rotation
  (`heap_root` not yet circuit-committed; `RESERVED` prover-chosen).
- **The gap.** Integrity-C holds, in its strong "whole post-state" form, for one move verb at the
  *executor-model* level — not over what the node runs, and not in-circuit. The 17-field projection is
  total per-step but there is no per-turn/per-forest composition, and the verbs other than the three
  are not covered by the memory-program backbone.
- **Refs.** `metatheory/Dregg2/Exec/UniversalBridge.lean`; `metatheory/Dregg2/AssuranceCase.lean:856-891`.

### MEDIUM-9 — Hash-valued state fields are modeled as low-64-bit projections.

- **Claimed.** The wire faithfully transports the turn with full 256-bit digests.
- **Actually established.** Credential digests cross full-width, but nullifiers, note commitments, VK
  hashes, and death-certificate hashes are collapsed to their low 64 bits at the marshaller
  (`lean_shadow.rs` `low_u64_be`). The Lean kernel makes freshness/integrity decisions over a **64-bit
  projection** of a 256-bit value; distinct nullifiers/commitments/VKs sharing low-64 **collide in the
  model**. Full-fidelity binding is delegated to the unproved Rust circuit.
- **The gap.** Faithful holds for the credential but not for the hash-valued fields guarantees C and D
  turn on; the model's freshness/integrity live over a lossy projection.
- **Refs.** `turn/src/lean_shadow.rs` (`low_u64_be` sites: ~970,998,1003,1071,1424).

### MEDIUM-10 — Privacy is a perfect-view collapse plus an unproven carrier; metadata leakage is characterized, not bounded.

- **Claimed.** Stealth/unlinkable give "two payments to the same recipient are computationally
  indistinguishable"; the channel key-epoch "darkens ciphertext."
- **Actually established.** Tier-3 indistinguishability is *equality of a modelled observer-view* plus
  a k-anonymity cardinality law — perfect (information-theoretic) hiding on the modelled view, which the
  module itself says is not the full computational property; the PPT/negligible `unlinkable` carrier is
  never proven. Metadata privacy is honestly *characterized* (payload hidden at the DAG boundary, but
  partners/timing/volume proven to **leak**, k→1 under unique metadata — `Privacy/Metadata.lean`) with
  **no proven leakage bound**. "Darkens ciphertext" (`ChannelGroup.lean`) is an ordering/rewrite law
  over opaque commitment scalars; the actual forward secrecy (a removed member cannot *decrypt* future
  traffic) is explicitly a §8 AEAD portal, **undischarged** (no AEAD definition exists in the Lean tree).
- **The gap.** The disclosure dial is exactly where a UC/simulation argument is indispensable, and it is
  exactly where everything reduces to a `Prop` carrier or a perfect-view collapse. "Darkens" is a
  confidentiality word; what is proven is that the commitment scalar changes and ordering can't be
  rewound. Correctly disclosed — must not be read as a privacy guarantee.
- **Refs.** `metatheory/Dregg2/Privacy/Metadata.lean:156-197,267`;
  `metatheory/Dregg2/Apps/ChannelGroup.lean:408-413`; `metatheory/Dregg2/Privacy.lean`.

### LOW-11 — Three-way hand-written codec consistency is test-kept; `RESERVED` is prover-chosen; the FRI carrier is opaque.

Eligibility (`forest_is_marshallable` / `effect_is_mappable`), the projector (`effect_to_wire`), and the
Lean grammar (`parseWWire`) are three independently hand-authored artifacts kept in sync only by
differential tests; a divergence in the *encoding* is invisible to the root-agreement check when both
sides are fed the same mis-encoding (the translation-validation gap). The `RESERVED` EffectVM column is
absorbed by no hash site, so its value is prover-chosen (no live verb can set it; harmless today, but
outside the binding — `reserved_not_bound_by_commitment`). And `EngineSound.recursive_sound` is honestly
a named `Prop` but **opaque**: no security parameter, no FRI-config binding, no Fiat-Shamir-in-ROM
statement, while bundling FRI low-degree soundness + PCS binding + Fiat-Shamir for the exact plonky3
config — an l4v reviewer wants this quantified and config-pinned like seL4's handful of explicit axioms.

---

## 4. The TCB and assumption floor, as it actually stands

The §2 floor in `ASSURANCE.md` lists items 1–8 below and claims "nothing else is load-bearing." That
claim is false as stated. The **actual** trust base of the *deployed* system is:

**Cryptographic carriers (correctly entered as `Prop`, never `axiom`) — legitimate, l4v-comparable:**
1. Poseidon2-permutation collision-resistance (sponge/Merkle/state-commit/MMR reduce to it).
2. BLAKE3 collision-resistance (out-of-circuit content/transcript hash).
3. ed25519 EUF-CMA (turn/strand signatures).
4. HMAC PRF/MAC unforgeability (macaroon caveat chains).
5. AEAD confidentiality+integrity (sealed payloads; the channel forward-secrecy portal rides this) —
   **named with no module and no discharge** (MEDIUM-10).
6. Discrete-log hardness (Pedersen value commitments — *but the deployed shielded commitment is
   Poseidon2/sponge; the UC discharge is for Pedersen*, MEDIUM-10/HIGH-7).
7. FRI / STARK / **Fiat-Shamir-in-the-ROM** soundness + extractability (`recursive_sound`,
   `ExtractsTo`). The ROM is silently folded in and not named as a distinct assumption; this is the
   deepest assumption in the system, *assumed at the leaf/aggregate level*, with no extractor and no
   connection to the concrete plonky3 verifier in Lean (LOW-11).
8. PostGSTProgress (eventual synchrony; the consensus liveness carrier — and the deployed node is n=1,
   so the consensus it would support is not exercised, HIGH-6).

**Engineering-trust items that are load-bearing but absent from the advertised floor — these are the
difference between "abstract kernel sound" and "deployed system sound":**
9.  **The wire codec** — explicitly "TCB, not proved" (`FFI.lean:92`); three hand-written
    implementations kept in sync by tests (CRITICAL-2, LOW-11).
10. **The Lean→C / lean-runtime / `libdregg_lean.a` link boundary** — no binary-correspondence
    statement that the linked `.a` *is* the `@[export]`ed Lean (CRITICAL-2).
11. **The unverified Rust on the live path** — `authorize.rs` (real ed25519/STARK/HMAC verification,
    CRITICAL-3), the Rust `TurnExecutor` (which **wins every co-producer disagreement**, CRITICAL-1),
    and the routing in `lean_shadow.rs`/`lean_apply.rs`.
12. **The hand-re-parsed Rust AIR evaluator** (`EffectVmDescriptorAir::eval` + the JSON parser) and the
    **hand-AIR fallback** for non-graduated turn shapes — test-attested, theorem-attested for none
    (HIGH-4, HIGH-5).
13. **The assumed `leaf_sound`** (HIGH-4) — a structure field witnessed only by an accept-all verifier,
    not derived from the per-effect soundness.
14. **The low-64 hash projection** (MEDIUM-9) — model collisions delegated to the unproved circuit.
15. **The Lean↔Isabelle UC transport** (HIGH-7) — human-checked, unverified, build unreproduced.
16. **The host-fed `ShadowHostCtx`** admission inputs (partially discharged by `HostCorrespondence`;
    residual = producer-coverage, engineering-shaped, a legitimately-named boundary).

**Honest reading.** Items 1–4, 7–8 are a legitimate, l4v-spirited crypto floor (l4v itself assumes the
compiler and hardware). Items 9–15 are not footnotes — they carry the deployment claim. The case's
"nothing else is load-bearing" sentence must be retracted in favor of a single TCB manifest enumerating
1–16 with each cross-referenced to its discharge-or-trust point. There is no closed-list answer to
"what is your TCB, exactly?" today.

---

## 5. Closure roadmap to l4v-grade (in dependency order)

The Lean composition is largely done; the remaining work is almost entirely **the bridge to the
binary**, plus the UC layer and the consensus model. In order:

**Stage 0 — make the verified executor authoritative (closes CRITICAL-1).** Install the Lean-produced
post-state unconditionally on covered turns; demote the Rust executor to a *verified-against* reference
or delete it on covered shapes. A verified producer that commits only on agreement with the buggy
executor is a differential, not a refinement. This requires no new mathematics — only inverting the
authority at `lean_apply.rs:1143` — and until it lands, *nothing downstream changes the deployed trust
story*.

**Stage 1 — the spec-to-binary refinement (CRITICAL-2, CRITICAL-3, HIGH-4).**
- A parse round-trip lemma for `parseWWire`/`effect_to_wire`, and a theorem that the String→String
  export **refines** `execFullForestG` on parseable inputs — bringing the codec inside the verified
  surface.
- Generate the Rust marshaller/reconstitutor **from Lean** with an extraction-correctness argument, or
  prove the Rust-to-wire encoding correct (the l4v translation-validation analogue); discharge
  `EffectVmDescriptorAir::eval ≈ satisfiedVm` **by construction**, not by differential corpus.
- A binary-correspondence statement that the linked `libdregg_lean.a` *is* the `@[export]`ed Lean (the
  seL4 C-to-binary analogue), and a TCB manifest replacing "nothing else is load-bearing."
- Put the WHO-leg inside the boundary (prove `authorize.rs`'s ed25519/STARK against the portal spec, or
  wire the dead `PortalFloor` oracles into the deployed `CryptoKernel` instance) — or explicitly list it
  as trusted. Stop pinning the deployed root WHAT/caveat legs to admit (`liftForestG`). Carry full-width
  256-bit hashes (MEDIUM-9).

**Stage 2 — discharge the per-leaf circuit soundness and empty the partition (HIGH-4, HIGH-5).**
- **Derive** `leaf_sound` in Lean: prove `satisfiedVm d_effect env ∧ RowEncodes env … → recCexec pre
  turn = some post` per graduated effect, with `RowEncodes` **forced by the trace-builder**, so the
  hypothesis the recursion consumes is a *theorem* — and replace the `acceptAll`/`Unit` non-vacuity
  witness with a real instance.
- Empty the hand-AIR fallback: all deployed shapes (including `CreateCell`, `Refusal`,
  `ReceiptArchive`) on the Lean-emitted descriptor AIR, theorem-attested. Bind `RESERVED` into the
  commitment and land the rotation so `heap_root` is circuit-committed per turn.

**Stage 3 — tie the apex to one turn/history; compose integrity to whole-turn (MEDIUM-7, MEDIUM-8).**
- Refactor `deployed_system_secure` so the C(c2) memory-program leg is over the *same* forest `f` (and
  the history `steps` extends it), and compose the per-verb memory programs to a whole-turn /
  whole-forest memory program, so "a receipt binds the whole post-state" holds over `execFullForestG`,
  bound in-circuit per turn.

**Stage 4 — the missing UC proof (HIGH-7, MEDIUM-10).** An interactive-machine / probabilistic-execution
model in one logic (adversary, environment, scheduler, PPT bound, negligible `≈`) with the dregg ideal
functionalities (selective-disclosure, channel-key, sealed-bid) defined as machines; a real simulator +
hybrid/reduction proof per functionality, reducing to the named primitives, discharged **natively** (a
CryptHOL-in-Lean port) or via a **machine-checked** transport — the human-checked Lean↔Isabelle
correspondence is exactly the seam l4v rejects. Instantiate AEAD and bind it to the channel-key flow so
"darkens ciphertext" becomes a forward-secrecy theorem; make metadata/side-channel leakage an explicit,
bounded part of the threat model or explicitly excluded. Instantiate `unfoolable_of_floor` to
`recCexec`/`stark::verify`, not the `ℕ`/echo toy.

**Stage 5 — consensus-model fidelity (HIGH-6).** Deploy and exercise an n>1 devnet that *runs the
ordering rule*; replace the empty-adversary `BFTModel` inhabitant and the assumed `gst_liveness` oracle
with a model derived from signatures/gossip/a real pacemaker; reconcile the Lean global-equivocator
predicate with the Rust observer-local one and unify the `n − f` vs two-thirds quorum into one formula;
add a Lean-vs-Rust commit refinement; and make consensus a leg of the composed apex.

**Stage 6 — config-pin the crypto floor (LOW-11).** State FRI/Fiat-Shamir as an extractor-based premise
(ideally against an extracted plonky3 verifier) with a security parameter and the ROM named, so the
floor is quantified and config-pinned in the seL4 style — the only out-of-Lean premises, each on a
closed list.

Only when Stages 0–6 land does "a light client trusting the aggregate trusts a no-mint/no-burn history,
having re-executed nothing" become a **theorem about the deployed artifact** — rather than (as today) a
real theorem about the *abstract kernel* sitting behind a co-producer that must agree with the buggy
executor, an echo-oracle credential check, a TCB wire codec, a re-parsed circuit interpreter, and an
n=1 consensus that does not run.
