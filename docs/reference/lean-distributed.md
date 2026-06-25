# Lean: the distributed theory

What this subsystem IS at HEAD. The distributed theory in `metatheory/` answers
one question across many modules: **what survives when there is more than one
machine?** The single-machine kernel proofs (attenuation, conservation,
light-client unfoolability) are sharpened to hold across topology, fault, and
revocation when `n > 1`, and the `n = 1` collapse recovers the strong local
statement. Two faces are named in this doc: **settlement soundness** (the
keystone — authority live *at settlement*, not branch time) and the **membrane**
(reshare/stitch attenuation across hops).

Everything below is cited to `Module.decl` or `file:line`. Every keystone module
carries its own `#assert_axioms` CI tripwire forcing the proof closed under
`{propext, Classical.choice, Quot.sound}` (e.g.
`SettlementSoundness.lean:501-515`, `EntangledJoint.lean:560-573`).

## Two namespaces

- `Dregg2.Distributed.*` — the deployed-tree distributed proofs, 25 modules
  (`metatheory/Dregg2/Distributed/*.lean`), 22 of them imported into the `Dregg2`
  rollup (`Dregg2.lean:104,420-437,520-521,646,766-768`).
- `Metatheory.SettlementSoundness` — a self-contained Lean-4 core that composes
  the settlement keystone over the `KeyLeak` cap+revocation model
  (`Metatheory/SettlementSoundness.lean:55`).

The two settlement files are deliberately paired: the `Metatheory` one is the
abstract keystone over a faithful restated model; the `Dregg2.Circuit` one is the
same theorem composed against the *real* deployed circuit
(`recStateCommit`/`verifyBatch`) — see §3.

---

## 1. The revocation model — the one non-monotone operation

`Dregg2/Distributed/Revocation.lean` is the load-bearing foundation. Revocation is
the only operation that *removes* authority, so it is the only place where
carrying branch-time authority forward is wrong.

- `Topology` — a propagation-delay model with one law: a node sees its own
  revocations immediately, `selfDelay : ∀ m, delay m m = 0`
  (`Revocation.lean:84-90`).
- `localRevSet T log n t` — what node `n` *locally believes* is revoked at time
  `t`: a `RevocationSet` reconstructed from the log, including an event iff
  `event.issuedAt + T.delay event.origin n ≤ t` (`Revocation.lean:110`,
  characterized by `mem_localRevSet`, `Revocation.lean:117`).
- `honors T log cred n t` — `verify (localRevSet T log n t) cred`: fail-closed
  per-node honor decision (`Revocation.lean:152-154`).
- **`eventual_bounded_revocation`** (THE KEYSTONE) — a credential revoked at origin
  `m` at time `τ` is NOT honored by any node `n` at any `t ≥ τ + delay m n`
  (`Revocation.lean:188`). Distributed ⇒ *eventual-bounded*.
- `immediate_revocation` — under `Instantaneous T` (`delay ≡ 0`, the single-machine
  principle), honoring stops at `τ` itself; a corollary of the keystone
  (`Revocation.lean:228`, `Instantaneous` at `:211`).
- The bound is **tight**, witnessed: `tightness_tooth` shows a revoke issued at
  node 0 is still honored at node 1 up to the propagation bound
  (`Revocation.lean:278`), and `single_machine_collapse` collapses that window to
  `τ` under instantaneous propagation (`Revocation.lean:301`).

The whole distributed gap lives in the substitution of `localRevSet` (a per-node
view) for a global one (`Revocation.lean:146`, in-source comment).

---

## 2. Settlement soundness — authority live AT settlement

`Metatheory/SettlementSoundness.lean` extends light-client unfoolability ("accept
⟹ genuine transition") to "accept ⟹ genuine transition whose authority was *live
at settlement*." It reuses the `KeyLeak` model verbatim
(`SettlementSoundness.lean:57`): `Cap`/`reaches` is the attenuation floor
(`granted ⊆ held`, `KeyLeak.lean:108`), `honors`/`Topo` is the revocation gate
(`KeyLeak.lean:292`, mirroring `Revocation`).

### The model

- `AuthCap` — a `Cap` paired with the `CredId` whose revocation kills it
  (`SettlementSoundness.lean:79`).
- `Tip` — the settlement tip: the finalizing `(node, time)`
  (`SettlementSoundness.lean:87`).
- `LiveAtTip T log held tip ac` — both legs: `reaches held ac.cap` (held as an
  attenuation) **and** `honors T log ac.cred tip.node tip.time = true` (not yet
  revoked at the tip) (`SettlementSoundness.lean:108`).

### The binding obligation as a *type*, never an axiom

- `SettlePred` — a predicate deciding whether a turn exercising `ac` settles into
  the finalized root (`SettlementSoundness.lean:127`).
- `BindsLiveAuthority S` — the typed hypothesis: settling entails live-at-tip
  authority, `∀ …, S … → LiveAtTip …` (`SettlementSoundness.lean:137`). This is
  the "bind the settlement-time revocation set into the commitment" obligation; a
  predicate that carries branch-time authority forward simply fails to inhabit it.
  No `axiom`.

### The keystones

- **`settlement_soundness`** — under any `BindsLiveAuthority S`, a settled turn
  necessarily exercised a `LiveAtTip` authority (`SettlementSoundness.lean:153`).
  Projected legs: `settled_authority_held` (`:162`), `settled_authority_honored`
  (`:168`).
- **`revoke_before_tip_unsettleable`** (the contrapositive) — if `ac`'s credential
  was revoked at `m`/`τ` and that revoke propagated to the tip
  (`τ + T.delay m tip.node ≤ tip.time`), then `ac` CANNOT settle
  (`SettlementSoundness.lean:192`). Fail-closed regardless of the stale
  branch-time view.
- `revoke_unsettleable_immediate` — the `n = 1` collapse: under `delay ≡ 0`, a
  revoke at any `τ ≤ tip.time` forecloses settlement immediately
  (`SettlementSoundness.lean:212`).

### Tautological vs deployed closure (the non-vacuity discipline)

The interface is inhabited two ways, and the file is explicit about which proves
what:

- `liveSettlement := LiveAtTip` makes `liveSettlement_binds` *tautological*
  (`LiveAtTip → LiveAtTip`, `h => h`) — it only witnesses the interface is
  non-empty (`SettlementSoundness.lean:233,244`).
- `deployedSettle` is **structured**: `reaches held ac.cap ∧ tipHonored … = true`,
  where `tipHonored` reads the *tip-time* `honors` gate
  (`SettlementSoundness.lean:280,289`). `deployedSettle_binds_live_authority`
  discharges the honored-leg from that gate — non-tautological
  (`SettlementSoundness.lean:305`).
- The closure **bites** on the predicate class: `branchSettle` (the failure mode —
  evaluate revocation at a stale *branch* coordinate) does NOT satisfy
  `BindsLiveAuthority` (`branchSettle_NOT_binds`, `SettlementSoundness.lean:408`),
  refuted by a concrete cap revoked-at-the-tip;
  `deployed_closure_discriminates` (`:428`) separates faithful from unfaithful
  settlements.
- Non-vacuity over the data: the SAME cap settles inside the stale window
  (`demo_settles_when_live`, `:356`) and is unsettleable once the revoke has
  propagated (`demo_unsettleable_when_revoked`, `:368`); assembled in
  `settlement_nonvacuous` (`:378`). Executable `#guard`s confirm
  (`SettlementSoundness.lean:446-452`).

### What it closes — three converging frontiers

- KeyLeak's named settlement seam: a leaked-then-revoked cap cannot settle
  (`leaked_then_revoked_cannot_settle`, `SettlementSoundness.lean:464`).
- The membrane stitch: the linear DROP is unsettleable revoked authority — "a cap
  I have since revoked cannot ride a stitch into my real world"
  (`stitch_drops_revoked_authority`, `SettlementSoundness.lean:477`).
- Light-client unfoolability: a settled root attests authority-was-live-at-settle
  (`settled_root_attests_live_authority`, `SettlementSoundness.lean:490`).

---

## 3. The deployed compose — `Dregg2.Circuit.SettlementSoundness`

The same theorem against the real circuit, declared a COMPOSE of three
already-proven legs (`Dregg2/Circuit/SettlementSoundness.lean:12-39`):

1. The finalized light-client apex
   `ClosureFinal.lightclient_unfoolable_circuit_sound`: a verifying batch yields a
   genuine kernel transition whose published commitment binds `post.kernel`
   (which carries the `revoked` registry).
2. `finalized_commit_binds_revoked` — equal finalized roots force equal `revoked`
   registries, the revoked-only projection of `recStateCommit_binds_kernel`
   (`Circuit/SettlementSoundness.lean:168`). So the commitment is *binding* on the
   revocation set; it cannot be equivocated.
3. `settled_revocation_bounded` — `eventual_bounded_revocation` read at the
   settlement coordinate `(nSettle, tSettle)`
   (`Circuit/SettlementSoundness.lean:139`); `settled_revocation_immediate` for
   the `n = 1` collapse (`:150`).

The settlement view is `settledRevView st = localRevSet T log nSettle tSettle`
(`Circuit/SettlementSoundness.lean:112`), and `honorsAtSettlement st cred =
verify (settledRevView st) cred` (`:119`, `honorsAtSettlement_eq` at `:123`).

**`settlement_soundness`** (the deployed theorem) — from a verifying finalized
batch (`verifyBatch (vkOfRegistry Rfix) pi π = accept`) plus a settlement
coordinate `st`: there exist decoded endpoints with a genuine `kstepAll`
transition committed to `(pi.pre, pi.post)`, AND any credential revoked before the
settlement-tip propagation bound is `honorsAtSettlement st cred = false`
(`Circuit/SettlementSoundness.lean:210-242`). Axiom-clean
(`Circuit/SettlementSoundness.lean:244`).

The **named residual** is explicitly *not* a Lean gap (`:49-56`): that the
deployed rest-hash encoder absorbs the `#139` revocation-channel wire root into
the finalized commitment (`RestHashIffFrame`'s `revoked` conjunct realized at the
wire) is a Rust circuit-emit conformance obligation; leg 2 carries the binding as
a named floor exactly as every other field does.

---

## 4. The membrane — `Dregg2.Deos.Membrane`

The membrane is reshare-across-hops, and its content is attenuation
non-amplification (`Dregg2/Deos/Membrane.lean`).

- `hop keep cap := attenuate keep cap`; one hop attenuates
  (`oneHop_attenuates`, `Membrane.lean:62,67`).
- `reshare keepAB keepBC cap := hop keepBC (hop keepAB cap)` (A→B→C),
  `reshareN` for chains (`Membrane.lean:80,85`).
- **`reshare_chain_attenuates`** (KEYSTONE) — `reshare A→B→C` confers a subset of
  what A held: `capAuthConferred (reshare …) ⊆ capAuthConferred cap`, by per-hop
  `⊆` and transitivity (`Membrane.lean:100`). `reshare_bounded_by_middle` gives
  the `C ⊆ B` half (`:112`).
- `reshareN_attenuates` — the n-hop generalization by induction over the chain:
  confinement survives arbitrarily long reacquisition chains (`Membrane.lean:122`).
- `reshare_refuses_amplification` (the negative tooth) — naming an unheld authority
  in a downstream keep-set does NOT conjure it; the membrane refuses to amplify
  (`Membrane.lean:145`).

The `Dregg2.Deos` rollup pins the membrane as one of its four targets and notes
the Rust `Membrane` is its realization (`Dregg2/Deos.lean:20-24,58`). Settlement's
`stitch_drops_revoked_authority` (§2) is the membrane's *settlement* face: a
stitch into the real world is an unsettleable DROP if the conferred authority was
revoked before the tip.

---

## 5. Joint turns across machines — `Dregg2.Distributed.EntangledJoint`

The N-cell atomic joint turn at `n > 1` (faithful to `atomic.rs`):

- `JointTurn` over a list of `Leg`s; `jointApplyAll k legs : Option …` folds them
  (`EntangledJoint.lean:110,134`).
- **`jointApplyAll_atomic`** — every leg of a committed joint turn committed at some
  intermediate state (`EntangledJoint.lean:162`); `jointApplyAll_dichotomy` — the
  only two outcomes are full commit or untouched input, no partial state
  (`:178`).
- No-authority-amplification at `n ≥ 2`: `jointApplyAll_all_authorized` — every
  committed leg passed the real `authorizedB` gate (`EntangledJoint.lean:195`); and
  `jointApplyAll_caps_frame` — the joint turn grants NO capability, the cap table
  is invariant across all legs (`:225`). Authority cannot be amplified by
  *coordinating* N turns.
- `jointApplyAll_conserves` — joint conservation; all axiom-clean
  (`EntangledJoint.lean:560-573`).

---

## 6. The rest of the distributed tree (what each module is)

The deployed-tree modules, each `#assert_axioms`-clean, each a faithful model of a
named Rust component:

- **Consensus** (`Consensus.lean`) — resilience as an asymmetric PAIR, not a
  scalar. `ResiliencePair` separates safety `tS` and liveness `tL`
  (`Consensus.lean:126`); the concrete `cfg = ⟨4,1,3⟩` (`n=4, f=1, quorum=3`,
  `:150`) gives `dreggResilience` with `tS=1, tL=0` (`:157`). The strict gap is a
  *feature*: `resilience_gap_real : tL < tS` (`:168`), `safety_resilience_high :
  tS = f` (`:173`).
- **BlocklaceFinality** (`BlocklaceFinality.lean`) — an executable model of the
  node's real finalization rule (`blocklace/src/ordering.rs::tau`):
  `computeRounds`/`roundOf`/`superMajority`/`waveLeader` over a `Lace`
  (`:95,100,106,119`).
- **FinalizedLightClient** (`FinalizedLightClient.lean`) — the three-leg light
  client adding a `FinalityCert` quorum leg; `light_client_accepts_finalized_history`
  (`:187`), `finalized_history_conserves` (`:211`).
- **HistoryAggregation** (`HistoryAggregation.lean`) — the IVC fold: a chain of
  `ChainStep`s whose roots are the `recStateCommit`; `Continues`/`ChainBound`
  temporal tooth (`:105,110`), `WellFormedChain` (`:135`).
- **QuorumThreshold** (`QuorumThreshold.lean`) — `supermajorityThreshold n = 2n/3+1`
  (`:66`), the byte-for-byte twin of `ordering.rs::supermajority_threshold`;
  `supermajority_intersection` and `two_quorums_share_honest` (`:151,169`) — two
  quorums always share an honest member.
- **LaceMerge** (`LaceMerge.lean`) — `mergeLace` is a join-semilattice on lace id
  sets: `merge_comm`/`merge_assoc`/`merge_idem`/`merge_absorb`/`merge_monotone`
  (`:138,143,151,157,167`).
- **CatchupConverges** (`CatchupConverges.lean`) — catch-up is order-independent and
  converges to the leader's lace; `catchup_order_independent` (`:133`),
  `catchup_converges_to_leader` (`:169`).
- **Fibration** (`Fibration.lean`) — distributed-adversarial semantics as one
  fibration over `Topology × FaultModel × CryptoStrength`; the single-machine
  principle is `lift_from_apex` reindexing (`Dregg2.lean:105`).

Plus the federation/admission/economics modules, each cited in the `Dregg2.lean`
import comments: **StrandIntegrity** (`:421`, no-equivocation per feed),
**StrandAdmission** (`:422`, hybrid stake-or-vouch Sybil gate),
**Economics** (`:425`, fee/DoS bounds), **CellMigration** (`:426`,
no-double-existence cross-federation handoff), **ThresholdDecrypt** (`:427`,
t-of-n Shamir), **EpochReconfig** (`:432`, validator-set handoff with no safety
gap), **CheckpointPrune** (`:433`, prune preserves the finalized prefix),
**BlsQuorumCert** (`:434`, a QC has an honest signer), **ThresholdAdmission**
(`:435`, host threshold-downgrade defense), **DirectoryLaws** (`:437`, monotone
name directory), **FeeHistory** (`:520`, history conserves modulo the burn),
**PrivateLeg** (`:646`, witnessless ZK-only leg in a joint turn).

---

## How it composes

The through-line: the single-machine kernel proofs are reindexed over a topology.
`Revocation` supplies the one non-monotone gate; `SettlementSoundness` welds that
gate to the finalized commitment so a light client checks authority *at the tip*;
the `Membrane` carries attenuation across reshare hops; `EntangledJoint` keeps
atomicity and non-amplification across N coordinated machines; and `Consensus` /
`QuorumThreshold` / `BlocklaceFinality` supply the finality the settlement tip is
read against. The `n = 1` collapse (`immediate_revocation`,
`revoke_unsettleable_immediate`, `lift_from_apex`) recovers the strong local
statement at every layer.
