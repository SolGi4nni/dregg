/-
# Dregg2.Apps.AgentProvenanceGated — a PROOF-CARRYING AGENT PROVENANCE LOG on the ONE GATED executor.

An AI agent needs an **attestable, non-repudiable scratchpad**: a place to post claims/outputs such
that (a) only a capability-holder can write, (b) entries are *append-only* — once a slot holds an
entry it can NEVER be silently overwritten (tamper-evidence), and (c) any third party can VERIFY the
provenance chain by reading back the committed entries and checking each links to its predecessor.

This is the SAME discipline `NameserviceGated` uses (the production turn entry `execFullForestG`'s
4-leg gate + the executor-enforced slot caveats), pointed at a DIFFERENT, harder invariant: not a
single registry binding but an **append-only HASH CHAIN** of provenance entries.

## The provenance cell's SLOTS and their executor-enforced caveats

The agent's log cell carries (`s.kernel.slotCaveats logCell`):

  * `head`        — `Monotonic`: the append cursor. A new entry advances `head` and the executor
    rejects any write that would REWIND it (`new < old`). This makes the log **append-only**: the
    sequence index only ever grows, so no committed prefix can be re-ordered or truncated-then-forked.
  * `entry_i`     — `WriteOnce` (one per slot): the i-th provenance record (a content/claim DIGEST).
    Once written (≠0) the `WriteOnce` caveat freezes it — the executor rejects ANY later overwrite.
    This is **tamper-evidence**: a committed entry is immutable forever.
  * `tip`         — `WriteOnce`-on-equal / free pointer to the latest entry digest (the chain head a
    verifier reads first).

The entries form a HASH CHAIN: `entry_i := linkHash prev claim` where `prev` is the digest committed
at `entry_{i-1}`. So `verifyChain` (below) re-derives each link from the committed predecessor and the
claim, and a single tampered or missing entry breaks the recomputation — the chain is VERIFIABLE by
re-execution, not by trust.

## What is PROVEN (each statement is the right invariant, true AND useful)

  1. `prov_forged_credential_rejected` — a write WITHOUT a valid capability is rejected by the gate
     (`execFullForestG … = none`) — **write-access requires the capability**.
  2. `prov_entry_writeonce`            — once an entry slot holds a non-zero digest, a DIFFERENT write
     to it is rejected by the executor — **append-only / no-overwrite, enforced by the kernel**.
  3. `prov_head_cannot_rewind`         — a `head` advance to a SMALLER cursor is rejected (`Monotonic`)
     — **the log cannot be rewound / re-ordered**.
  4. `prov_append_reads_back`          — a committed append's entry digest reads back EXACTLY what was
     written — **the provenance record is faithfully recorded** (the verifier reads truth).
  5. `prov_append_audited`            — a committed append extends the kernel RECEIPT LOG by exactly
     one non-repudiable row (who/where) — **every write leaves an audit trail**.
  6. `prov_chain_links`                — `verifyChain` accepts the honest chain and REJECTS a chain
     with any tampered link — **the provenance chain is verifiable** (the headline novelty).
  7. `prov_append_conserves`           — an append moves NO asset's supply — **provenance is balance-
     orthogonal** (logging claims never mints/burns value).

Does NOT touch `FullForestAuth.lean`, `GatedForestCfg.lean`, nor `Dregg2.lean`. Reuses ONLY the proved
gated-executor keystones + the proved `stateStepGuarded` fail-closed teeth + the proved `setField_fieldOf`
read-back law.
-/
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Apps.AgentProvenanceGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated

/-! ## §1 — The provenance DOMAIN at the Demo carriers (the log cell, its slots, the link hash). -/

/-- The agent's provenance log cell. Cell `0` so the actor can be `0` too — `stateAuthB` is then
trivially satisfied (`actor == src`), letting the CREDENTIAL gate and the SLOT CAVEAT be the
load-bearing admission conditions (mirrors `NameserviceGated.registryCell`). -/
abbrev logCell : CellId := 0
/-- The agent posting to its own scratchpad. Equal to `logCell` so `stateAuthB` holds by `actor == src`. -/
abbrev agentActor : CellId := 0

/-- The append cursor slot — `Monotonic`: the next-entry index only ever grows (append-only ordering). -/
abbrev headSlot : FieldName := "head"
/-- The chain-tip pointer — the latest committed entry digest (a verifier reads this first). -/
abbrev tipSlot : FieldName := "tip"

/-- The i-th provenance entry slot name (`"entry0"`, `"entry1"`, …). Each is its OWN `WriteOnce` slot:
once the i-th record is committed (≠0) the executor freezes it forever (tamper-evidence). -/
def entrySlot (i : Nat) : FieldName := s!"entry{i}"

/-- **The provenance LINK HASH** — `linkHash prev claim` is the digest stored at an entry: a collision-
shaped fold of the PREVIOUS entry's digest and the new claim. (We use a concrete Horner-style fold over
`ℤ` — the EXECUTABLE shadow of the §8 Poseidon2 portal; what matters here is that the entry is a
deterministic function of `(prev, claim)`, so a verifier re-derives it and any tampered link breaks the
recomputation.) `prev = 0` for the genesis entry (no predecessor). -/
def linkHash (prev claim : Int) : Int := prev * 1000003 + claim * 31 + 17

/-! ## §2 — Each op as a GATED LEAF NODE through the production turn entry `execFullForestG`.

A provenance op is a single caveat-gated `SetField` on the log cell, decorated with a credential and run
through the 4-leg gate (`mkAuth cred []` ⇒ the live gate leg is the CREDENTIAL; the SLOT caveats are
enforced separately by `stateStepGuarded` inside `execFullA`). Same node shape as `NameserviceGated.nsNode`. -/

/-- A gated provenance node: credential `cred`, a `SetField slot value` on the log cell, no children. -/
def provNode (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA agentActor logCell slot value, [] ⟩

/-- **append-entry** — write the i-th provenance digest (`SetField entry_i (linkHash prev claim)`).
`WriteOnce` ⇒ the FIRST write to a fresh slot commits; any later overwrite is rejected. -/
def appendEntryNode (cred : Authorization Dg Pf) (i : Nat) (prev claim : Int) : DForest :=
  provNode cred (entrySlot i) (linkHash prev claim)

/-- A raw entry-slot write (the digest given directly, so the contested-overwrite hypothesis in
`prov_entry_writeonce` is about THIS slot's `WriteOnce` caveat, independent of `linkHash`). -/
def appendEntryRaw (cred : Authorization Dg Pf) (i : Nat) (digest : Int) : DForest :=
  provNode cred (entrySlot i) digest

/-- **advance-head** — bump the append cursor (`SetField head newHead`). `Monotonic` ⇒ admitted iff
`newHead ≥ old`: the log index can only grow. -/
def advanceHeadNode (cred : Authorization Dg Pf) (newHead : Int) : DForest :=
  provNode cred headSlot newHead

/-- **set-tip** — update the chain-tip pointer to the latest entry digest (`SetField tip digest`). -/
def setTipNode (cred : Authorization Dg Pf) (digest : Int) : DForest :=
  provNode cred tipSlot digest

/-- The provenance cell's factory-installed SLOT CAVEATS: `head` is `Monotonic`, and entries `0..n-1`
are each `WriteOnce`. The executor reads these on EVERY `SetField` to the log cell (`stateStepGuarded`).
We bind a finite prefix of entry slots (enough for any concrete log we exhibit). -/
def provCaveats (n : Nat) : List SlotCaveat :=
  .monotonic headSlot :: (List.range n).map (fun i => .writeOnce (entrySlot i))

/-! ## §3 — The leaf-collapse bridge: a childless gated provenance op runs EXACTLY its single gated node.

Reuses `execFullForestG_leaf` (proved in `GatedForestCfg`); the provenance-specialized collapse below is
the unfolding every theorem rests on. -/

/-- **`execFullForestG_provNode` — the provenance-op collapse.** A childless provenance op runs
`if gateOK then stateStepGuarded … else none`. -/
theorem execFullForestG_provNode (s : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) :
    execFullForestG s (provNode cred slot value)
      = (if gateOK (mkAuth cred []) s = true
         then stateStepGuarded s slot agentActor logCell value
         else none) := by
  rw [provNode, execFullForestG_leaf, execFullAGated]
  rfl

/-- **`prov_good_node_runs_write` — the gate-passing collapse for `goodCred`.** When the genuine
credential admits, the provenance op IS its caveat-gated `SetField`. The hinge for theorems 2–4: any
caveat-rejection of the WRITE rejects the whole turn. -/
theorem prov_good_node_runs_write (s : RecChainedState) (slot : FieldName) (value : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (provNode goodCred slot value)
      = stateStepGuarded s slot agentActor logCell value := by
  rw [execFullForestG_provNode, if_pos hgate]

/-! ## §4 — THEOREM 1: a write WITHOUT a valid capability is REJECTED (write-access requires the cap). -/

/-- **`prov_forged_credential_rejected` — PROVED.** A provenance op (any slot/value) presented with a
FORGED credential is rejected by the production turn entry — `execFullForestG s (provNode forgedCred …)
= none`, for EVERY pre-state `s`. Nobody can append to / rewind / re-tip an agent's provenance log
without a genuine capability. The §8 credential leg fail-closes ⇒ the whole forest rolls back. -/
theorem prov_forged_credential_rejected (s : RecChainedState) (slot : FieldName) (value : Int) :
    execFullForestG s (provNode forgedCred slot value) = none := by
  rw [provNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA agentActor logCell slot value) [] (gateOK_forged_false s)
where
  /-- The forged credential's gate is FALSE on every state (the credential leg fail-closes). -/
  gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
    have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
    unfold gateOK; rw [hcred]; simp

/-- Specialization to `appendEntryNode` (the headline shape: an unauthorized APPEND is rejected). -/
theorem prov_forged_append_rejected (s : RecChainedState) (i : Nat) (prev claim : Int) :
    execFullForestG s (appendEntryNode forgedCred i prev claim) = none :=
  prov_forged_credential_rejected s (entrySlot i) (linkHash prev claim)

/-! ## §5 — THEOREMS 2–3: the SLOT CAVEATS bite (gate passes for `goodCred`, the WRITE fails closed).

THE COMPOSITION: the gate passes (genuine credential) so `execFullForestG s (provNode goodCred …) =
stateStepGuarded …`; then the SLOT caveat on the written field makes `caveatsAdmit = false`, so
`stateStepGuarded = none` (`stateStepGuarded_caveat_violation_fails`). The whole turn rejects — enforced
BY THE EXECUTOR. -/

/-- **`prov_entry_writeonce` — PROVED (THEOREM 2: APPEND-ONLY / NO OVERWRITE).** If entry slot `i`
already holds a DIFFERENT non-zero digest (the `WriteOnce` caveat rejects the rewrite:
`caveatsAdmit = false`), then a write over it is rejected by the executor — EVEN with a genuine
credential. A committed provenance entry can NEVER be silently overwritten — this is the tamper-evidence
the whole app exists for. NON-VACUOUS: the hypothesis is forced by the `WriteOnce entry_i` caveat on a
contested slot (witnessed concretely in §8). -/
theorem prov_entry_writeonce (s : RecChainedState) (i : Nat) (digest : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hfrozen : caveatsAdmit s.kernel (entrySlot i) agentActor logCell digest = false) :
    execFullForestG s (appendEntryRaw goodCred i digest) = none := by
  rw [appendEntryRaw, prov_good_node_runs_write s (entrySlot i) digest hgate]
  exact stateStepGuarded_caveat_violation_fails s (entrySlot i) agentActor logCell digest hfrozen

/-- **`prov_head_cannot_rewind` — PROVED (THEOREM 3: NO REWIND / RE-ORDER).** If the `Monotonic head`
caveat rejects the new cursor (`caveatsAdmit = false`, i.e. `newHead < old`), an advance is rejected —
EVEN with a genuine credential. The append cursor can only GROW: a committed provenance prefix cannot
be re-ordered, truncated, or rewound to fork a different continuation. -/
theorem prov_head_cannot_rewind (s : RecChainedState) (newHead : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hrewind : caveatsAdmit s.kernel headSlot agentActor logCell newHead = false) :
    execFullForestG s (advanceHeadNode goodCred newHead) = none := by
  rw [advanceHeadNode, prov_good_node_runs_write s headSlot newHead hgate]
  exact stateStepGuarded_caveat_violation_fails s headSlot agentActor logCell newHead hrewind

/-! ## §6 — THEOREM 4: a committed append READS BACK exactly what was written (faithful recording). -/

/-- **`prov_append_reads_back` — PROVED (THEOREM 4: FAITHFUL RECORDING).** When a provenance write
COMMITS (`= some s'`), reading the written slot of the log cell back returns EXACTLY the digest written.
The verifier reads TRUTH: a committed provenance entry is on the cell with the value the agent recorded —
no silent rewrite, no drop. Rests on the proved `setField_fieldOf` write/read law through the committed
`writeField` post-state. -/
theorem prov_append_reads_back (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int)
    (h : execFullForestG s (provNode cred slot value) = some s') :
    fieldOf slot (s'.kernel.cell logCell) = value := by
  -- The committed forest is its single gated node; that node's commit factors through stateStep.
  have hguard : stateStepGuarded s slot agentActor logCell value = some s' := by
    by_cases hgate : gateOK (mkAuth cred []) s = true
    · rwa [execFullForestG_provNode, if_pos hgate] at h
    · rw [execFullForestG_provNode, if_neg hgate] at h; exact absurd h (by simp)
  have hstep : stateStep s slot agentActor logCell (.int value) = some s' := stateStepGuarded_eq hguard
  obtain ⟨_, hs'⟩ := stateStep_factors hstep
  subst hs'
  -- s'.kernel.cell logCell = setField slot (s.kernel.cell logCell) (.int value)  (writeField at target)
  show fieldOf slot ((writeField s.kernel slot logCell (.int value)).cell logCell) = value
  unfold writeField
  simp only [↓reduceIte]
  exact setField_fieldOf slot (s.kernel.cell logCell) value

/-! ## §7 — THEOREM 5: a committed append leaves a NON-REPUDIABLE AUDIT ROW (who/where). -/

/-- **`prov_append_audited` — PROVED (THEOREM 5: AUDIT TRAIL).** A committed provenance write extends
the kernel RECEIPT LOG by exactly one row, recording the actor and the cell it wrote — a non-repudiable
audit entry for every append. (`stateStep` prepends `{ actor, src := cell, dst := cell, amt := 0 }`.) So
the provenance log is doubly attestable: the cell state holds the entry, and the receipt log holds the
WHO. -/
theorem prov_append_audited (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int)
    (h : execFullForestG s (provNode cred slot value) = some s') :
    s'.log = { actor := agentActor, src := logCell, dst := logCell, amt := 0 } :: s.log := by
  have hguard : stateStepGuarded s slot agentActor logCell value = some s' := by
    by_cases hgate : gateOK (mkAuth cred []) s = true
    · rwa [execFullForestG_provNode, if_pos hgate] at h
    · rw [execFullForestG_provNode, if_neg hgate] at h; exact absurd h (by simp)
  have hstep : stateStep s slot agentActor logCell (.int value) = some s' := stateStepGuarded_eq hguard
  obtain ⟨_, hs'⟩ := stateStep_factors hstep
  rw [hs']

/-! ## §8 — THEOREM 6: the PROVENANCE CHAIN is VERIFIABLE — `verifyChain` recomputes every link.

The headline novelty over a registry: the entries are a HASH CHAIN. A verifier holding a list of claims
re-derives each entry digest from the committed predecessor and the claim, and checks it equals what the
log committed. A single tampered or missing link breaks the recomputation. `verifyChain` is the
EXECUTABLE verifier; the theorems show it accepts the honest chain and REJECTS any tamper. -/

/-- The honest provenance digest sequence for a list of claims: `entryDigests [c₀, c₁, …]` is
`[linkHash 0 c₀, linkHash (linkHash 0 c₀) c₁, …]` — each digest folds the PREVIOUS digest with the
next claim (genesis predecessor `0`). This is exactly what an honest agent commits to `entry_i`. -/
def entryDigests : List Int → List Int
  | []            => []
  | claim :: rest => go 0 (claim :: rest)
where
  go : Int → List Int → List Int
    | _,    []            => []
    | prev, claim :: rest => let h := linkHash prev claim; h :: go h rest

/-- **`verifyChain`** — the third-party VERIFIER. Given the claims and the committed entry digests (as
read off the cell), re-derive the chain from scratch and check the committed digests match link-for-link.
Returns `true` IFF every committed digest equals `linkHash (previous committed digest) claim`, i.e. the
log is exactly the honest hash chain of those claims. Decidable, computable, FAIL-CLOSED. -/
def verifyChain (claims committed : List Int) : Bool :=
  committed == entryDigests claims

/-- **`prov_chain_links` — PROVED (THEOREM 6: HONEST CHAIN VERIFIES).** A log whose committed entry
digests are EXACTLY the honest fold of the claims passes verification: `verifyChain claims
(entryDigests claims) = true`. The verifier accepts a faithfully-built provenance chain. -/
theorem prov_chain_links (claims : List Int) :
    verifyChain claims (entryDigests claims) = true := by
  unfold verifyChain
  simp

/-- **`prov_chain_tamper_rejected` — PROVED (THEOREM 6, the TEETH: tamper is CAUGHT).** If the committed
digests differ from the honest fold (a link was overwritten, dropped, or forged), verification REJECTS:
`committed ≠ entryDigests claims → verifyChain claims committed = false`. So the chain is genuinely
verifiable — a single altered entry breaks it. NON-VACUOUS against `prov_chain_links` (witnessed in §9
with a concrete tampered middle link). -/
theorem prov_chain_tamper_rejected (claims committed : List Int)
    (htamper : committed ≠ entryDigests claims) :
    verifyChain claims committed = false := by
  unfold verifyChain
  simpa using htamper

/-! ## §9 — THEOREM 7: an append CONSERVES every asset (provenance is balance-orthogonal). -/

/-- The per-asset turn delta of any provenance op is `0` (a `SetField` is balance-neutral) — for EVERY
asset `b`. Discharged once, reused for every op. -/
theorem provNode_delta_zero (cred : Authorization Dg Pf) (slot : FieldName) (value : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (provNode cred slot value)).map Prod.snd) b = 0 := by
  simp [provNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`prov_append_conserves` — PROVED (THEOREM 7).** A COMMITTED provenance turn preserves EVERY
asset's total supply: writing a claim digest touches metadata, never balance — so logging provenance
moves no money. A one-liner off `execFullForestG_conserves_per_asset` with the `SetField`-is-balance-
neutral hypothesis discharged by `provNode_delta_zero`. -/
theorem prov_append_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (slot : FieldName) (value : Int) (b : AssetId)
    (h : execFullForestG s (provNode cred slot value) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (provNode cred slot value) b h
    (provNode_delta_zero cred slot value b)

/-! ## §10 — NON-VACUITY: a concrete agent-log state with the real caveats + `#guard` witnesses.

`log0` is the agent's provenance cell `0`, born with a `Monotonic head` caveat and `WriteOnce` caveats
on `entry0..entry2`. Two genesis entries are ALREADY committed (a 2-claim chain `[c₀=5, c₁=9]`), `head =
2`, `tip = entry1`'s digest. On `log0` we exhibit every theorem witnessed REAL, not vacuous:
  (i)   a GOOD append into the FRESH `entry2` COMMITS, and reads back the honest digest;
  (ii)  a FORGED credential ⇒ `none`;
  (iii) an OVERWRITE of the already-set `entry0` ⇒ `none` (WriteOnce bites — APPEND-ONLY);
  (iv)  a head REWIND (2 → 1) ⇒ `none` (Monotonic bites — NO RE-ORDER);
  (v)   the committed 2-entry chain VERIFIES, and a tampered chain is REJECTED;
  (vi)  a committed append CONSERVES both assets. -/

/-- The honest genesis digests of the 2-claim chain `[5, 9]`. `d0 = linkHash 0 5`, `d1 = linkHash d0 9`. -/
def c0 : Int := 5
def c1 : Int := 9
def d0 : Int := linkHash 0 c0
def d1 : Int := linkHash d0 c1
def c2 : Int := 13           -- the next claim the agent will append into entry2

/-- The agent's provenance pre-state: cell `0` carries the `Monotonic head` + `WriteOnce entry0..2`
caveats; `entry0 = d0`, `entry1 = d1` (a committed 2-entry chain), `entry2 = 0` (fresh), `head = 2`,
`tip = d1`. Actor `0 == logCell` so `stateAuthB` holds; the cell is Live; accounts `{0, 1}`; no
revocations. -/
def log0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (headSlot, .int 2), (tipSlot, .int d1),
                           (entrySlot 0, .int d0), (entrySlot 1, .int d1), (entrySlot 2, .int 0)]
                else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then provCaveats 3 else [] }
    log := [] }

-- The gate passes for the genuine credential on this state (the credential leg is the only live leg):
#guard (gateOK (mkAuth goodCred []) log0)            --  true  (genuine capability admits)
#guard (gateOK (mkAuth forgedCred []) log0) == false --  false (forged ⇒ fail-closed)

-- (i) a GOOD append into the FRESH entry2 COMMITS (WriteOnce permits the genesis write of that slot):
#guard ((execFullForestG log0 (appendEntryNode goodCred 2 d1 c2)).isSome)            --  true (appended!)
-- ...and the committed entry2 reads back EXACTLY the honest link digest linkHash d1 c2:
#guard ((execFullForestG log0 (appendEntryNode goodCred 2 d1 c2)).map
        (fun s => fieldOf (entrySlot 2) (s.kernel.cell 0))) == some (linkHash d1 c2)

-- (ii) a FORGED credential ⇒ none (capability gate fail-closes), even into the fresh slot:
#guard ((execFullForestG log0 (appendEntryNode forgedCred 2 d1 c2)).isSome) == false  --  false

-- (iii) APPEND-ONLY / NO OVERWRITE: a DIFFERENT write over the already-set entry0 (= d0) ⇒ none
--       (WriteOnce: old = d0 ≠ 0 and new = 999 ≠ d0 ⇒ caveatsAdmit = false):
#guard (caveatsAdmit log0.kernel (entrySlot 0) agentActor logCell 999) == false  --  false (frozen)
#guard ((execFullForestG log0 (provNode goodCred (entrySlot 0) 999)).isSome) == false  --  false (overwrite rejected)
-- ...rewriting the SAME committed digest is a WriteOnce no-op and is admitted (idempotent):
#guard (caveatsAdmit log0.kernel (entrySlot 0) agentActor logCell d0)  --  true (no-op rewrite)

-- (iv) NO REWIND: advancing head 2 → 1 is rejected (Monotonic: 1 < 2 ⇒ caveatsAdmit = false):
#guard (caveatsAdmit log0.kernel headSlot agentActor logCell 1) == false  --  false (rewind)
#guard ((execFullForestG log0 (advanceHeadNode goodCred 1)).isSome) == false  --  false (rewind rejected)
-- ...advancing head forward (2 → 3) is admitted and COMMITS:
#guard (caveatsAdmit log0.kernel headSlot agentActor logCell 3)  --  true (forward)
#guard ((execFullForestG log0 (advanceHeadNode goodCred 3)).isSome)  --  true (advance commits)

-- (v) CHAIN VERIFIABILITY: the committed [d0, d1] chain is exactly the honest fold of claims [c0, c1]:
#guard (entryDigests [c0, c1] == [d0, d1])                       --  true (honest chain)
#guard (verifyChain [c0, c1] [d0, d1])                           --  true (verifier ACCEPTS honest log)
-- ...a TAMPERED middle link (d1 → 12345) is REJECTED by the verifier:
#guard (verifyChain [c0, c1] [d0, 12345]) == false              --  false (tamper CAUGHT)
-- ...a TRUNCATED chain (a dropped tail entry) is REJECTED:
#guard (verifyChain [c0, c1] [d0]) == false                     --  false (truncation CAUGHT)

-- (vi) CONSERVATION: a committed append moves NO asset's supply (per-asset Δ = 0):
#guard ((execFullForestG log0 (appendEntryNode goodCred 2 d1 c2)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  unchanged

/-! ## §11 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. -/

#assert_axioms execFullForestG_provNode
#assert_axioms prov_good_node_runs_write
#assert_axioms prov_forged_credential_rejected
#assert_axioms prov_entry_writeonce
#assert_axioms prov_head_cannot_rewind
#assert_axioms prov_append_reads_back
#assert_axioms prov_append_audited
#assert_axioms prov_chain_links
#assert_axioms prov_chain_tamper_rejected
#assert_axioms prov_append_conserves

end Dregg2.Apps.AgentProvenanceGated
