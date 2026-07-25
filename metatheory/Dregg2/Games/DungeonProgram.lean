/-
# Dregg2.Games.DungeonProgram — the DEPLOYED descent cell program, AUTHORED IN LEAN.

The reimagined descent (`Dregg2.Games.Dungeon` — the model, the design laws) is deployed as
THIS `CellProgram` value: emitted to the checked-in artifact
`dungeon-on-dregg/program/dungeon_program.json` (regen + drift-gated by
`dungeon-on-dregg/program/regen.sh`) and loaded by `dungeon_on_dregg::descent`
(`Deployment::program()` resolves the symbolic slot/method names against the
translation-validated `dregg-schema` allocator). There is NO hand-rolled Rust
`CellProgram` in the descent's path — the deployed program IS this Lean object by
construction (edit a rule here, re-emit, and the deployed game changes: the canary).

## What is NEW here relative to the tug pattern (`MultiwayTugProgram.lean`)

1. **Guards are part of the authored object** — not just `MethodIs`: the program carries
   `SlotChanged`-guarded RIDER cases (`slotChangedForMethods`, lowered by the loader to
   `AllOf[SlotChanged, AnyOf[MethodIs…]]`). This retires the standing
   stapleable-slot falsifier *structurally*: ANY verb that moves `depth` pays the delve
   law, ANY verb that flips a `way_w` must EXHIBIT the carried key-relic, ANY verb that
   moves `bank`/`fate` pays the banking law, and ANY exertion (a `spent` change) pays
   the conservation/ratchet/capacity commons. The method list inside the guard keeps the
   executor's method-default-deny intact (`unknown_method_refused`).

2. **The proofs run against the LAW-#1 evaluator.** `toExec` lifts this program into
   `Dregg2.Exec.RecordProgram` — the name-keyed algebra the Rust evaluator mirrors — and
   the theorems below are admission-soundness INVERSIONS over ARBITRARY record values
   (attacker-supplied writes), not structural pins:
     * `admitted_verb_conserves` — any admitted verb turn's post-state sums the relic
       zones to exactly `RELICS` (no dupe, no burn);
     * `admitted_verb_capacity` — any admitted verb turn satisfies
       `pack + depth ≤ CAP` (attenuation reaches the deployed teeth);
     * `admitted_verb_pays` — any admitted verb turn strictly spends breath, capped at
       `BREATH` (the clock);
     * `admitted_verb_alive` — any admitted verb turn starts from `fate = 0`
       (the banked tomb is frozen: `banked_tomb_refuses`);
     * `way_flip_exhibits_key` — any admitted turn that flips `way_w` carries the
       `0 → 1` transition AND the post-state holds key-relic `w−1` CARRIED;
     * `unknown_method_refused` — a method outside the six verbs is default-denied.

3. **Custody projections are exact, not parallel bookkeeping.** The spent rider
   carries six `countFieldsEq` aggregate teeth.  Every ordinary verb therefore proves
   that `pack`, `bank`, and each floor hoard are the exact census of the eight
   individually committed relic custody fields.  A forged loot can neither advance a
   counter without moving a relic nor move two relics behind one `pack += 1` receipt.

4. **The model and the program share ONE substrate** (name-keyed records): `encode`
   embeds the model `DState` into `Exec.Value`, and the `#guard` battery DRIVES the
   crowned run of `Dungeon.lean` through `RecordProgram.admits` step by step — the
   model-legal run IS admitted — while eight named attacks (dupe, keyless way, staple,
   tomb move, dead light, fake flee, relic teleport, genesis replay) are REFUSED.
   Tug could not do this (its model lived on multisets, a different substrate); the
   reimagined dungeon was AUTHORED so the refinement is direct. ⚑ The way-flip inversion is
   now proven for ALL THREE locked ways (`way_flip_exhibits_key` ⇒ `way2/3/4_flip_exhibits_key`),
   closing the audit's "ways 3/4 are Rust-driven" gap.

## Honest scope

* The theorems hold of the Lean `Exec.RecordProgram` evaluator — a name-keyed record MODEL
  of the referee. ⚑ `docs/audit/GAME-PROOF-LARP-AUDIT.md` correctly flagged that this is NOT the
  evaluator `eval.rs` calls, and that it had DIVERGED from the deployed one: `Exec`'s field
  compares (`affineLe`/`fieldGe`) are signed unbounded `Int`, whereas the deployed field is
  UNSIGNED 256-bit (`eval.rs:2842`). The SEMANTICS axis of that disconnect is now closed at its
  source: the pure (context-free, witness-free) constraint teeth are AUTHORED ONCE over the
  DEPLOYED substrate (`[FieldElement;16]` + heap, UNSIGNED-256) in
  `Dregg2.Exec.DeployedConstraint.admits`, `@[export dregg_constraint_admits]`-ed and CALLED by the
  deployed node (`eval.rs`'s `evaluate_constraint_full` routes the subset through it via the
  `dregg_cell::program::ConstraintOracle` seam installed by `dregg-exec-lean`; the reality-gate
  canary in `dregg-lean-ffi`/`exec-lean` tests proves the deployed decision IS the Lean source, and
  the differential gate pins Lean == Rust across the subset). These dungeon inversions remain over
  the signed-`Int` `Exec` MODEL — their honest scope — and reaching the deployed unsigned evaluator
  is the register-substrate refinement the audit named (NOT re-claimed here). The Rust-side agreement
  the descent crate's executor tests exercise (illegal turns are REAL `WorldError::Refused`) is now
  ALSO backed by the differential gate, not prose alone.
* The per-relic custody ratchet (`monotonic` + `memberOf {home, CARRIED, BANKED}`),
  zone-counter conservation, and the exact custody↔counter census are all enforced.
  The aggregate is over this game's fixed eight custody keys; an unbounded dynamic
  inventory still belongs on the first-class collection/AIR path.

## ⚑ DeployedConstraint refinement — why tug lands and the descent is BOUNDED (LARP-audit fix #4/#5)

The tug game's action teeth ALL live in `Dregg2.Exec.DeployedConstraint`'s exported PURE subset
(`sumEquals`/`writeOnce`/`strictMonotonic`/`fieldGte`/`heapField`-atoms) over NONNEG counters, so
tug's forward refinement was RE-STATED against the deployed evaluator itself
(`MultiwayTugProgram §4I` `program_admits_legal_play_deployed`). The descent is TWO honest steps
short of that, and this is a structural fact, not an omission:

  1. **Vocabulary.** The descent's teeth use `affineLe` (capacity), `allowedTransitions`
     (fate/way), `inRangeTwoSided` (zone ranges) and `fieldDelta` (posted prices) — NONE of which
     are in `DeployedConstraint`'s exported pure subset (which is context-free/witness-free field &
     heap atoms). Only `admitted_verb_conserves` (`sumEquals`) and `admitted_verb_pays`
     (`strictMonotonic`+`fieldLte`) sit inside the pure subset; capacity/alive/way-flip do not.
  2. **Signedness.** The inversions quantify over ARBITRARY `Exec.Value`s, where a scalar is a
     SIGNED unbounded `Int`. `DeployedConstraint` is UNSIGNED 256-bit `Nat` — the EXACT divergence
     the audit flagged. On a negative attacker scalar the two evaluators genuinely DISAGREE, so an
     arbitrary-`Value` inversion CANNOT be faithfully re-stated over `DeployedConstraint`. The two
     agree only on the NONNEG `encode` image — i.e. via the weld below, not the inversions.

  So the honest descent scope is: the inversions are proven over the signed-`Int` `Exec` MODEL
  (all three ways now included); a faithful `DeployedConstraint` refinement would hold only on the
  nonneg `encode` image and only for the pure-subset teeth (conserves/pays), routed through the
  ∀-weld. That is the NAMED remainder — it needs the ∀-weld (below) plus a nonneg `Int→Nat`
  register marshalling, not a new substrate.

## ⚑ The model↔program WELD — DRIVEN status, honestly (LARP-audit fix #5)

The weld `model-legal step ⟹ program-admitted` (the FORWARD refinement direction) is DRIVEN, not
yet a ∀-theorem: `programAdmitsRun crownedRun = true` checks it for ONE legal run (genesis + 17
verbs), and nine attack `#guard`s check named forgeries are refused. The GENERAL ∀-weld
(`∀ s m s', step s m = some s' → RecordProgram.admits dungeonExec (moveIdx m) (encode s)
(encode s') = true`) is NAMED, not proven here: it is a per-move, tooth-by-tooth discharge of every
matching verb case + `SlotChanged` rider over the SHARED `Exec` substrate (large — ~5 moves × the
verb+rider teeth, with custody-`countP` conservation/ratchet lemmas — but tractable, and NOT a new
substrate). Several of its consequences ARE already ∀-theorems in the REVERSE direction (the
inversions `admitted_verb_*`, `banked_tomb_refuses`, `dead_light_refuses`, `way{2,3,4}_flip_*`),
which is why the driven attacks each correspond to a proven inversion. What remains driven is the
forward completeness (legal ⇒ admitted) beyond the single crowned run.
-/
import Dregg2.Games.Dungeon
import Dregg2.Exec.Program

namespace Dregg2.Games.Dungeon.Prog

open Dregg2.Exec (Value)

/-! ⚑ THE TEETH ARE PARAMETRIC IN THE DAY'S WORLD. `homeCode`, `genesisHoard` and the
guardian teeth read `Dungeon.homeFloors` / `Dungeon.guardHp`, which are now functions of
the drawn map (`Dungeon.WorldParam`) rather than compile-time constants — so every
definition and every inversion below carries the world it is stated over, and the emit
(§6) renders ONE program per family member. -/
variable [WorldParam]

-- The world parameter is blanket-scoped over the file (every rule and law is stated over
-- the day's drawn map); a handful of pure list/count helpers legitimately do not mention
-- it, and the section-variable linter would otherwise report each one.
set_option linter.unusedSectionVars false

/-! ## 1. The symbolic vocabulary (names, not indices — the loader resolves). -/

/-- A heap-key reference: a schema collection by NAME, or the spween genesis-done
sentinel (`spween_dregg::GENESIS_DONE_EXT_KEY`). -/
inductive HeapKeyRef where
  | named (name : String)
  | sentinel
deriving Repr, DecidableEq

/-- The heap-atom subset the descent uses. -/
inductive HeapAtom where
  | equals (v : Nat)
  | immutable
  | monotonic
  | memberOf (set : List Nat)
  | deltaEquals (d : Int)
deriving Repr, DecidableEq

/-- The simple (anyOf-liftable) subset. -/
inductive Simple where
  | fieldEquals (reg : String) (v : Nat)
  | fieldGte (reg : String) (v : Nat)
  | fieldLte (reg : String) (v : Nat)
  | immutable (reg : String)
  | negate (inner : Simple)
deriving Repr, DecidableEq

/-- The `StateConstraint` subset the descent's teeth are built from. -/
inductive Constraint where
  | fieldEquals (reg : String) (v : Nat)
  | fieldGte (reg : String) (v : Nat)
  | fieldLte (reg : String) (v : Nat)
  | fieldDelta (reg : String) (d : Nat)          -- every posted price is a positive step
  | strictMonotonic (reg : String)
  | immutable (reg : String)
  | sumEquals (regs : List String) (v : Nat)
  | affineLe (terms : List (Int × String)) (c : Int)
  | inRangeTwoSided (reg : String) (lo hi : Nat)
  | allowedTransitions (reg : String) (allowed : List (Nat × Nat))
  | anyOf (variants : List Simple)
  | heapField (key : HeapKeyRef) (atom : HeapAtom)
  | countFieldsEq (keys : List HeapKeyRef) (value : Nat) (reg : String)
deriving Repr, DecidableEq

/-- Guards: the descent authors BOTH method dispatch AND slot-changed riders. A rider
`slotChangedForMethods reg ms` lowers to `AllOf[SlotChanged reg, AnyOf[MethodIs m | m ∈ ms]]`
— the anti-staple gate that still keeps method-default-deny (the method disjunct). -/
inductive Guard where
  | methodIs (method : String)
  | slotChangedForMethods (reg : String) (methods : List String)
deriving Repr, DecidableEq

structure Case where
  guard : Guard
  constraints : List Constraint
deriving Repr, DecidableEq

inductive CellProgram where
  | cases (cs : List Case)
deriving Repr, DecidableEq

/-! ## 2. The descent's teeth (the design of `Dungeon.lean`, as deployed constraints). -/

def relicName (i : Nat) : String := s!"relic_{i}"
def wayName (w : Nat) : String := s!"way_{w}"
def hoardName (d : Nat) : String := s!"hoard_{d}"

/-- The relic-zone registers summed by conservation (`Σ = RELICS` on every turn). -/
def zones : List String :=
  ["pack", "bank", "hoard_1", "hoard_2", "hoard_3", "hoard_4"]

/-- The individually committed relic custody fields, in their canonical mint order. -/
def relicKeys : List HeapKeyRef :=
  (List.range RELICS).map fun i => .named (relicName i)

/-- Each relic's minted home floor — THE SAME list the model mints from
(`Dungeon.homeFloors`); the emit reads the model, so the world and its teeth cannot
drift apart. -/
def homeCode (i : Nat) : Nat := homeFloors.getD i 0

/-- The genesis hoard census — a PROJECTION of `homeFloors` (relics at floor d). -/
def genesisHoard (d : Nat) : Nat := (homeFloors.filter (· == d)).length

def verbs : List String := ["delve", "unlock", "smite", "loot", "flee"]

/-- **The core commons** — on EVERY verb case and every rider:
conservation, capacity attenuation, the strictly-spending capped clock, and the
aliveness/banking fate law (`0→0` stay alive, `0→1` bank; a banked run matches nothing). -/
def coreTeeth : List Constraint :=
  [ .sumEquals zones RELICS,
    .affineLe [((1 : Int), "pack"), ((1 : Int), "depth")] (CAP : Int),
    .strictMonotonic "spent",
    .fieldLte "spent" BREATH,
    .allowedTransitions "fate" [(0, 0), (0, 1)] ]

/-- Per-relic provenance ratchet: custody codes only ascend `home → CARRIED → BANKED`
and only through the legal alphabet (no floor-to-floor teleport). -/
def custodyTeeth : List Constraint :=
  (List.range RELICS).flatMap fun i =>
    [ .heapField (.named (relicName i)) .monotonic,
      .heapField (.named (relicName i)) (.memberOf [homeCode i, CARRIED, BANKED]) ]

/-- Zone counters live in `[0, RELICS]` — no field-wrap tricks. -/
def rangeTeeth : List Constraint :=
  zones.map fun z => .inRangeTwoSided z 0 RELICS

/-- Bind every register projection to the exact census of the eight custody fields.
This is the heap/object ↔ register bridge: conservation among counters can no longer
be satisfied by counters that describe a different custody state. -/
def projectionTeeth : List Constraint :=
  [ .countFieldsEq relicKeys CARRIED "pack",
    .countFieldsEq relicKeys BANKED "bank",
    .countFieldsEq relicKeys 1 (hoardName 1),
    .countFieldsEq relicKeys 2 (hoardName 2),
    .countFieldsEq relicKeys 3 (hoardName 3),
    .countFieldsEq relicKeys 4 (hoardName 4) ]

/-- Freeze a register set (a verb's write-frame: what it does NOT own, it cannot touch). -/
def frozen (regs : List String) : List Constraint := regs.map .immutable

/-- Freeze every relic's custody (verbs that do not move relics). -/
def relicFreeze : List Constraint :=
  (List.range RELICS).map fun i => .heapField (.named (relicName i)) .immutable

/-- `depth = d ⇒ way_d open` (delve teeth; way 1 is the always-open first stair). -/
def wayTooth (d : Nat) : Constraint :=
  .anyOf [.negate (.fieldEquals "depth" d), .fieldGte (wayName d) 1]

/-- `depth = d ⇒ wounds ≤ guardHp d` (a guardian cannot be over-slain). -/
def guardCapTooth (d : Nat) : Constraint :=
  .anyOf [.negate (.fieldEquals "depth" d), .fieldLte "wounds" (guardHp d)]

/-- `depth = d ⇒ wounds ≥ guardHp d` (loot only over a slain guardian). -/
def guardSlainTooth (d : Nat) : Constraint :=
  .anyOf [.negate (.fieldEquals "depth" d), .fieldGte "wounds" (guardHp d)]

/-- `depth ≠ d ⇒ hoard_d frozen` (loot may only draw from the standing floor;
conservation then forces the −1 exactly). -/
def hoardFrameTooth (d : Nat) : Constraint :=
  .anyOf [.fieldEquals "depth" d, .immutable (hoardName d)]

/-- **genesis** — the world's one-shot mint, pinned EXACTLY: the spween sentinel `0→1`
plus the canonical seed (all counters, every relic at its `homeFloors` floor). The
receipt chain of every relic replays to THIS turn. -/
def genesisCase : Case :=
  ⟨.methodIs "genesis",
    [ .heapField .sentinel (.equals 1),
      .heapField .sentinel (.deltaEquals 1),
      .fieldEquals "depth" 0, .fieldEquals "spent" 0, .fieldEquals "wounds" 0,
      .fieldEquals "fate" 0, .fieldEquals "pack" 0, .fieldEquals "bank" 0,
      .fieldEquals (wayName 2) 0, .fieldEquals (wayName 3) 0, .fieldEquals (wayName 4) 0,
      .fieldEquals (hoardName 1) (genesisHoard 1),
      .fieldEquals (hoardName 2) (genesisHoard 2),
      .fieldEquals (hoardName 3) (genesisHoard 3),
      .fieldEquals (hoardName 4) (genesisHoard 4) ]
    ++ (List.range RELICS).map (fun i => .heapField (.named (relicName i)) (.equals (homeCode i)))⟩

/-- **delve** — descend exactly one floor: pay 1 breath, the way to the NEW floor must
be open, the guardian below is fresh (`wounds = 0`), and nothing else moves. -/
def delveCase : Case :=
  ⟨.methodIs "delve",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldDelta "depth" 1,
      .fieldEquals "wounds" 0, .fieldEquals "fate" 0,
      wayTooth 2, wayTooth 3, wayTooth 4 ]
    ++ frozen ["pack", "bank", wayName 2, wayName 3, wayName 4,
               hoardName 1, hoardName 2, hoardName 3, hoardName 4]
    ++ relicFreeze⟩

/-- **unlock** — exercise a carried key: pay 1 breath; WHICH way may flip (and that its
key is exhibited) is the way-riders' law. Everything else frozen. -/
def unlockCase : Case :=
  ⟨.methodIs "unlock",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldEquals "fate" 0 ]
    ++ frozen ["depth", "wounds", "pack", "bank",
               hoardName 1, hoardName 2, hoardName 3, hoardName 4]
    ++ relicFreeze⟩

/-- **smite** — wound the standing guardian by exactly 1: pay 2 breath (it strikes
back); never below the surface's edge (`depth ≥ 1`); never past the guardian's
vitality. Nothing else moves. -/
def smiteCase : Case :=
  ⟨.methodIs "smite",
    coreTeeth ++
    [ .fieldDelta "spent" 2, .fieldDelta "wounds" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardCapTooth 1, guardCapTooth 2, guardCapTooth 3, guardCapTooth 4 ]
    ++ frozen ["depth", "pack", "bank", wayName 2, wayName 3, wayName 4,
               hoardName 1, hoardName 2, hoardName 3, hoardName 4]
    ++ relicFreeze⟩

/-- **loot** — take ONE relic from the standing floor's hoard: pay 1 breath, the
guardian must be slain, only THIS floor's hoard may move (conservation forces the −1),
and the capacity commons attenuate what you may carry. Relics are NOT frozen here —
the looted relic's custody ratchets (`custodyTeeth` on the spent-rider bind it). -/
def lootCase : Case :=
  ⟨.methodIs "loot",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldDelta "pack" 1,
      .fieldGte "depth" 1, .fieldEquals "fate" 0,
      guardSlainTooth 1, guardSlainTooth 2, guardSlainTooth 3, guardSlainTooth 4,
      hoardFrameTooth 1, hoardFrameTooth 2, hoardFrameTooth 3, hoardFrameTooth 4 ]
    ++ frozen ["depth", "wounds", "bank", wayName 2, wayName 3, wayName 4]⟩

/-- **flee** — the run ends: pay 1 breath, the pack empties into the bank
(`pack' = 0` + hoards frozen + conservation ⇒ `bank' = bank + pack`), fate `0→1`. -/
def fleeCase : Case :=
  ⟨.methodIs "flee",
    coreTeeth ++
    [ .fieldDelta "spent" 1, .fieldEquals "fate" 1, .fieldEquals "pack" 0 ]
    ++ frozen ["depth", "wounds", wayName 2, wayName 3, wayName 4,
               hoardName 1, hoardName 2, hoardName 3, hoardName 4]⟩

/-! ### The riders — `SlotChanged` carries the gate (the stapleable-slot fix). -/

/-- ANY verb that moves `depth` pays the delve law. -/
def depthRider : Case :=
  ⟨.slotChangedForMethods "depth" verbs,
    coreTeeth ++ [.fieldDelta "depth" 1, .fieldEquals "wounds" 0,
                  wayTooth 2, wayTooth 3, wayTooth 4]⟩

/-- ANY verb that flips `way_w` must carry the `0→1` transition AND exhibit the carried
key-relic for `w` — the key is an owned capability, exercised, receipted. -/
def wayRider (w : Nat) : Case :=
  ⟨.slotChangedForMethods (wayName w) verbs,
    coreTeeth ++
    [ .allowedTransitions (wayName w) [(0, 1)],
      .heapField (.named (relicName (keyFor w))) (.equals CARRIED) ]⟩

/-- ANY verb that flips `fate` is a lawful banking (`0→1`, pack emptied). -/
def fateRider : Case :=
  ⟨.slotChangedForMethods "fate" verbs,
    coreTeeth ++ [.allowedTransitions "fate" [(0, 1)], .fieldEquals "pack" 0]⟩

/-- ANY verb that moves `bank` is a banking turn (`fate' = 1`, pack emptied). -/
def bankRider : Case :=
  ⟨.slotChangedForMethods "bank" verbs,
    coreTeeth ++ [.fieldEquals "fate" 1, .fieldEquals "pack" 0]⟩

/-- ANY exertion (a `spent` change — every verb) pays the heavy commons: zone ranges,
the per-relic provenance ratchet, and the genesis-sentinel freeze. -/
def spentRider : Case :=
  ⟨.slotChangedForMethods "spent" verbs,
    coreTeeth ++ rangeTeeth ++ custodyTeeth ++ projectionTeeth ++
      [.heapField .sentinel .immutable]⟩

/-- The deployed case list: the six verb arms + the six riders. -/
def programCases : List Case :=
  [ genesisCase, delveCase, unlockCase, smiteCase, lootCase, fleeCase,
    depthRider, wayRider 2, wayRider 3, wayRider 4, fateRider, bankRider, spentRider ]

/-- **`dungeonProgram` — the DEPLOYED descent teeth, authored in Lean.** -/
def dungeonProgram : CellProgram := .cases programCases

/-! ## 3. The lift into the LAW-#1 algebra (`Dregg2.Exec`) — proofs run HERE. -/

/-- The reserved record field standing for the spween genesis-done sentinel. -/
def sentinelField : String := "genesis_done"

def HeapKeyRef.field : HeapKeyRef → String
  | .named n  => n
  | .sentinel => sentinelField

/-- Method-name interning for the Exec algebra (`methodIs (method : Nat)`). -/
def methodIdx : String → Nat
  | "genesis" => 0
  | "delve"   => 1
  | "unlock"  => 2
  | "smite"   => 3
  | "loot"    => 4
  | "flee"    => 5
  | _         => 1000

def Simple.toExec : Simple → Dregg2.Exec.SimpleConstraint
  | .fieldEquals r v => .fieldEquals r (v : Int)
  | .fieldGte r v    => .fieldGe r (v : Int)
  | .fieldLte r v    => .fieldLe r (v : Int)
  | .immutable r     => .immutable r
  | .negate inner    => .not inner.toExec

def HeapAtom.toExec (f : String) : HeapAtom → Dregg2.Exec.StateConstraint
  | .equals v      => .simple (.fieldEquals f (v : Int))
  | .immutable     => .simple (.immutable f)
  | .monotonic     => .simple (.monotonic f)
  | .memberOf set  => .simple (.memberOf f (set.map (fun v => (v : Int))))
  | .deltaEquals d => .simple (.fieldDelta f d)

def Constraint.toExec : Constraint → Dregg2.Exec.StateConstraint
  | .fieldEquals r v => .simple (.fieldEquals r (v : Int))
  | .fieldGte r v    => .simple (.fieldGe r (v : Int))
  | .fieldLte r v    => .simple (.fieldLe r (v : Int))
  | .fieldDelta r d  => .simple (.fieldDelta r (d : Int))
  | .strictMonotonic r => .simple (.strictMono r)
  | .immutable r     => .simple (.immutable r)
  | .sumEquals rs v  => .sumEquals rs (v : Int)
  | .affineLe ts c   => .affineLe (ts.map (fun t => (t.1, t.2))) c
  | .inRangeTwoSided r lo hi => .simple (.inRangeTwoSided r (lo : Int) (hi : Int))
  | .allowedTransitions r al =>
      .allowedTransitions r (al.map (fun p => ((p.1 : Int), (p.2 : Int))))
  | .anyOf vs        => .anyOf (vs.map Simple.toExec)
  | .heapField k a   => a.toExec k.field
  | .countFieldsEq ks v r =>
      .countFieldsEq (ks.map HeapKeyRef.field) (v : Int) r

def Guard.toExec : Guard → Dregg2.Exec.TransitionGuard
  | .methodIs m => .methodIs (methodIdx m)
  | .slotChangedForMethods reg ms =>
      .allOf [.slotChanged reg, .anyOf (ms.map (fun m => .methodIs (methodIdx m)))]

def Case.toExec (c : Case) : Dregg2.Exec.TransitionCase :=
  ⟨c.guard.toExec, c.constraints.map Constraint.toExec⟩

def CellProgram.toExec : CellProgram → Dregg2.Exec.RecordProgram
  | .cases cs => .cases (cs.map Case.toExec)

/-- The deployed program in the LAW-#1 algebra. -/
def dungeonExec : Dregg2.Exec.RecordProgram := dungeonProgram.toExec

/-! ## 4. Admission-soundness inversions (over ARBITRARY record values). -/

open Dregg2.Exec in
/-- If a `Cases` program admits, then EVERY member case whose guard matches has all its
constraints satisfied (the executor ANDs all matching arms). -/
theorem admits_cases_mem {tcs : List TransitionCase} {m : Nat} {o n : Value}
    (h : RecordProgram.admits (.cases tcs) m o n = true)
    {tc : TransitionCase} (hmem : tc ∈ tcs)
    (hmatch : tc.guard.matches m o n = true) :
    ∀ c ∈ tc.constraints, evalConstraint c o n = true := by
  simp only [RecordProgram.admits] at h
  have hmemf : tc ∈ tcs.filter (fun tc => tc.guard.matches m o n) :=
    List.mem_filter.mpr ⟨hmem, hmatch⟩
  cases hfil : tcs.filter (fun tc => tc.guard.matches m o n) with
  | nil => rw [hfil] at hmemf; cases hmemf
  | cons a as =>
    rw [hfil] at h hmemf
    have hall := (List.all_eq_true.mp h) tc hmemf
    intro c hc
    exact (List.all_eq_true.mp hall) c hc

open Dregg2.Exec in
/-- Every verb case's teeth BEGIN with `coreTeeth`; an admitted verb turn therefore
satisfies every core tooth. (`m` ranges over the five verb indices.) -/
theorem verb_core_teeth {m : Nat} (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    ∀ c ∈ coreTeeth, evalConstraint c.toExec o n = true := by
  intro c hc
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := delveCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [delveCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := unlockCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [unlockCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := smiteCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [smiteCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := lootCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [lootCase, List.mem_append, hc]))
  · exact admits_cases_mem (tcs := programCases.map Case.toExec) h
      (tc := fleeCase.toExec)
      (List.mem_map_of_mem (by simp [programCases])) (by rfl)
      c.toExec (List.mem_map_of_mem (by simp [fleeCase, List.mem_append, hc]))

open Dregg2.Exec in
/-- **No dupe, no burn — deployed**: any admitted verb turn's post-state sums the six
relic zones to exactly `RELICS`, whatever the writes were. -/
theorem admitted_verb_conserves {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    sumScalars n zones = some (RELICS : Int) := by
  have := verb_core_teeth hm h (.sumEquals zones RELICS) (by simp [coreTeeth])
  simpa [Constraint.toExec, evalConstraint] using this

open Dregg2.Exec in
/-- **Attenuation — deployed**: any admitted verb turn's post-state satisfies
`pack + depth ≤ CAP`. -/
theorem admitted_verb_capacity {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    ∃ p d : Int, n.scalar "pack" = some p ∧ n.scalar "depth" = some d
      ∧ p + d ≤ (CAP : Int) := by
  have hT := verb_core_teeth hm h
    (.affineLe [((1 : Int), "pack"), ((1 : Int), "depth")] (CAP : Int))
    (by simp [coreTeeth])
  have hT' : evalConstraint
      (.affineLe [((1 : Int), "pack"), ((1 : Int), "depth")] (CAP : Int)) o n = true := hT
  obtain ⟨s, hsum, hle⟩ :=
    (evalConstraint_affineLe_iff [((1 : Int), "pack"), ((1 : Int), "depth")]
      (CAP : Int) o n).mp hT'
  cases hp : n.scalar "pack" with
  | none => simp [affineSum, hp] at hsum
  | some p =>
    cases hd : n.scalar "depth" with
    | none => simp [affineSum, hp, hd] at hsum
    | some d =>
      refine ⟨p, d, rfl, rfl, ?_⟩
      simp only [affineSum, List.foldr_cons, List.foldr_nil, hp, hd] at hsum
      injection hsum with hsum
      omega

open Dregg2.Exec in
/-- **The clock — deployed**: any admitted verb turn strictly spends breath, and the
post-state clock is capped at `BREATH`. -/
theorem admitted_verb_pays {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    ∃ a b : Int, o.scalar "spent" = some a ∧ n.scalar "spent" = some b
      ∧ a < b ∧ b ≤ (BREATH : Int) := by
  have hs := verb_core_teeth hm h (.strictMonotonic "spent") (by simp [coreTeeth])
  have hs' : evalSimple (.strictMono "spent") o n = true := hs
  have hl := verb_core_teeth hm h (.fieldLte "spent" BREATH) (by simp [coreTeeth])
  have hl' : evalSimple (.fieldLe "spent" (BREATH : Int)) o n = true := hl
  obtain ⟨a, b, ha, hb, hab⟩ := (evalSimple_strictMono_iff "spent" o n).mp hs'
  refine ⟨a, b, ha, hb, hab, ?_⟩
  simp only [evalSimple, hb] at hl'
  exact of_decide_eq_true hl'

open Dregg2.Exec in
/-- **Aliveness — deployed**: any admitted verb turn STARTS alive (`old fate = 0`);
its post-fate is `0` (still alive) or `1` (banked this turn). -/
theorem admitted_verb_alive {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true) :
    o.scalar "fate" = some 0
      ∧ (n.scalar "fate" = some 0 ∨ n.scalar "fate" = some 1) := by
  have hT := verb_core_teeth hm h (.allowedTransitions "fate" [(0, 0), (0, 1)])
    (by simp [coreTeeth])
  have hT' : evalConstraint
      (.allowedTransitions "fate" [((0 : Int), (0 : Int)), ((0 : Int), (1 : Int))])
      o n = true := hT
  cases ha : o.scalar "fate" with
  | none =>
    simp only [evalConstraint, ha] at hT'
    exact absurd hT' (by decide)
  | some a =>
    cases hb : n.scalar "fate" with
    | none =>
      simp only [evalConstraint, ha, hb] at hT'
      exact absurd hT' (by decide)
    | some b =>
      simp only [evalConstraint, ha, hb, List.any_cons, List.any_nil, Bool.or_false,
                 Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hT'
      rcases hT' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by rw [← h1], Or.inl (by rw [← h2])⟩
      · exact ⟨by rw [← h1], Or.inr (by rw [← h2])⟩

open Dregg2.Exec in
/-- **The banked tomb is frozen — deployed**: from `old fate = 1` NO verb is admitted. -/
theorem banked_tomb_refuses {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (hf : o.scalar "fate" = some 1) :
    RecordProgram.admits dungeonExec m o n = false := by
  cases hadm : RecordProgram.admits dungeonExec m o n with
  | false => rfl
  | true =>
    have := (admitted_verb_alive hm hadm).1
    rw [hf] at this
    cases this

open Dregg2.Exec in
/-- **The dead light refuses — deployed**: at `old spent = BREATH` NO verb is admitted
(strict spend + the cap are jointly unsatisfiable). -/
theorem dead_light_refuses {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (hs : o.scalar "spent" = some (BREATH : Int)) :
    RecordProgram.admits dungeonExec m o n = false := by
  cases hadm : RecordProgram.admits dungeonExec m o n with
  | false => rfl
  | true =>
    obtain ⟨a, b, ha, hb, hab, hcap⟩ := admitted_verb_pays hm hadm
    rw [hs] at ha
    injection ha with ha
    omega

open Dregg2.Exec in
/-- **Keys are exercised capabilities — deployed, ALL THREE WAYS.** Any admitted VERB turn that
flips `way_w` (`w ∈ {2,3,4}`) carries the lawful `0→1` transition AND exhibits its carried key-relic
`keyFor w = w−1` CARRIED in the post-state. The rider guard makes this METHOD-INDEPENDENT across the
verb set — there is no verb from which a keyless way-flip is admissible. ⚑ This GENERALIZES the
former way-2-only inversion: ways 3 and 4 (`way3_flip_exhibits_key`, `way4_flip_exhibits_key` below)
are now proven, not Rust-driven — the audit's "ways 3/4 are Rust-driven" gap is closed. -/
theorem way_flip_exhibits_key (w : Nat) (hw : w = 2 ∨ w = 3 ∨ w = 4)
    {m : Nat} (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true)
    (hflip : (o.scalar (wayName w) == n.scalar (wayName w)) = false) :
    n.scalar (relicName (keyFor w)) = some (CARRIED : Int)
      ∧ o.scalar (wayName w) = some 0 ∧ n.scalar (wayName w) = some 1 := by
  have hmem : (wayRider w).toExec ∈ programCases.map Case.toExec := by
    rcases hw with rfl | rfl | rfl <;> exact List.mem_map_of_mem (by simp [programCases])
  have hmatch : (wayRider w).toExec.guard.matches m o n = true := by
    rcases hm with rfl | rfl | rfl | rfl | rfl <;>
      simp [wayRider, Case.toExec, Guard.toExec, verbs, methodIdx,
            TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch, hflip]
  have hall := admits_cases_mem (tcs := programCases.map Case.toExec) h
    (tc := (wayRider w).toExec) hmem hmatch
  have hkey := hall ((Constraint.heapField (.named (relicName (keyFor w))) (.equals CARRIED)).toExec)
    (List.mem_map_of_mem (by simp [wayRider, List.mem_append]))
  have htrans := hall ((Constraint.allowedTransitions (wayName w) [(0, 1)]).toExec)
    (List.mem_map_of_mem (by simp [wayRider, List.mem_append]))
  have hkey' : evalSimple (.fieldEquals (relicName (keyFor w)) (CARRIED : Int)) o n = true := hkey
  refine ⟨?_, ?_, ?_⟩
  · have := hkey'
    simp only [evalSimple] at this
    cases hk : n.scalar (relicName (keyFor w)) with
    | none => rw [hk] at this; cases this
    | some k =>
      rw [hk] at this
      rw [show k = (CARRIED : Int) from by simpa using this]
  all_goals
    (have hT : evalConstraint
        (.allowedTransitions (wayName w) [((0 : Int), (1 : Int))]) o n = true := htrans
     cases ha : o.scalar (wayName w) with
     | none =>
       simp only [evalConstraint, ha] at hT
       exact absurd hT (by decide)
     | some a =>
       cases hb : n.scalar (wayName w) with
       | none =>
         simp only [evalConstraint, ha, hb] at hT
         exact absurd hT (by decide)
       | some b =>
         simp only [evalConstraint, ha, hb, List.any_cons, List.any_nil, Bool.or_false,
                    Bool.and_eq_true, beq_iff_eq] at hT
         obtain ⟨h1, h2⟩ := hT
         first
           | rw [← h1]
           | rw [← h2])

open Dregg2.Exec in
/-- Way 2 (`keyFor 2 = 1`) — the original inversion, now a corollary of the general lemma. -/
theorem way2_flip_exhibits_key {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true)
    (hflip : (o.scalar (wayName 2) == n.scalar (wayName 2)) = false) :
    n.scalar (relicName 1) = some (CARRIED : Int)
      ∧ o.scalar (wayName 2) = some 0 ∧ n.scalar (wayName 2) = some 1 :=
  way_flip_exhibits_key 2 (Or.inl rfl) hm h hflip

open Dregg2.Exec in
/-- Way 3 (`keyFor 3 = 2`) — proven, not Rust-driven. -/
theorem way3_flip_exhibits_key {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true)
    (hflip : (o.scalar (wayName 3) == n.scalar (wayName 3)) = false) :
    n.scalar (relicName 2) = some (CARRIED : Int)
      ∧ o.scalar (wayName 3) = some 0 ∧ n.scalar (wayName 3) = some 1 :=
  way_flip_exhibits_key 3 (Or.inr (Or.inl rfl)) hm h hflip

open Dregg2.Exec in
/-- Way 4 (`keyFor 4 = 3`) — proven, not Rust-driven. -/
theorem way4_flip_exhibits_key {m : Nat}
    (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5)
    {o n : Value} (h : RecordProgram.admits dungeonExec m o n = true)
    (hflip : (o.scalar (wayName 4) == n.scalar (wayName 4)) = false) :
    n.scalar (relicName 3) = some (CARRIED : Int)
      ∧ o.scalar (wayName 4) = some 0 ∧ n.scalar (wayName 4) = some 1 :=
  way_flip_exhibits_key 4 (Or.inr (Or.inr rfl)) hm h hflip

open Dregg2.Exec in
/-- **Method-default-deny survives the riders**: a method outside the six verbs is
refused outright — no case (method arm or rider) matches it. -/
theorem unknown_method_refused {m : Nat} (hm : 6 ≤ m) (o n : Value) :
    RecordProgram.admits dungeonExec m o n = false := by
  have h0 : ((0 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h1 : ((1 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h2 : ((2 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h3 : ((3 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h4 : ((4 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  have h5 : ((5 : Nat) == m) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp [dungeonExec, dungeonProgram, programCases, CellProgram.toExec, Case.toExec,
        Guard.toExec, verbs, methodIdx, RecordProgram.admits,
        TransitionGuard.matches, Dregg2.Exec.allMatch, Dregg2.Exec.anyMatch,
        genesisCase, delveCase, unlockCase, smiteCase, lootCase, fleeCase,
        depthRider, wayRider, fateRider, bankRider, spentRider,
        List.map_cons, List.map_nil, List.filter_cons, List.filter_nil,
        h0, h1, h2, h3, h4, h5]

/-! ## 5. The model↔program weld — encode the model state, DRIVE the runs. -/

/-- Embed the model state into the record substrate the deployed teeth read. Every
counter is a PROJECTION of custody (`pack`/`bank`/`hoardAt` are the model's own
definitions), so the encoding cannot disagree with the model about counts. -/
def encode (s : DState) : Value :=
  .record
    ([ ("depth", .int s.depth), ("spent", .int s.spent), ("wounds", .int s.wounds),
       ("fate", .int s.fate), ("pack", .int (pack s)), ("bank", .int (bank s)),
       (wayName 2, .int (s.ways.getD 0 0)), (wayName 3, .int (s.ways.getD 1 0)),
       (wayName 4, .int (s.ways.getD 2 0)),
       (hoardName 1, .int (hoardAt s 1)), (hoardName 2, .int (hoardAt s 2)),
       (hoardName 3, .int (hoardAt s 3)), (hoardName 4, .int (hoardAt s 4)) ]
     ++ (List.range RELICS).map (fun i => (relicName i, .int (s.custody.getD i 0)))
     ++ [(sentinelField, .int 1)])

/-- The pre-genesis cell: every register field-zero, the sentinel birthed at 0, the
relic heap keys unwritten (absent — on the heap, absent ≠ present-zero). -/
def preGenesis : Value :=
  .record
    [ ("depth", .int 0), ("spent", .int 0), ("wounds", .int 0), ("fate", .int 0),
      ("pack", .int 0), ("bank", .int 0),
      (wayName 2, .int 0), (wayName 3, .int 0), (wayName 4, .int 0),
      (hoardName 1, .int 0), (hoardName 2, .int 0), (hoardName 3, .int 0),
      (hoardName 4, .int 0), (sentinelField, .int 0) ]

def moveIdx : Move → Nat
  | .delve    => 1
  | .unlock _ => 2
  | .smite    => 3
  | .loot _   => 4
  | .flee     => 5

/-- Drive a model script through the DEPLOYED program: every step must be BOTH
model-legal and program-admitted on the encoded transition. -/
def programAdmitsRun (ms : List Move) : Bool :=
  Dregg2.Exec.RecordProgram.admits dungeonExec (methodIdx "genesis") preGenesis
      (encode genesisState)
    && go genesisState ms
where
  go (s : DState) : List Move → Bool
    | [] => true
    | m :: rest =>
      match step s m with
      | none => false
      | some s' =>
          Dregg2.Exec.RecordProgram.admits dungeonExec (moveIdx m) (encode s) (encode s')
            && go s' rest

/-- A convenience: the state a legal prefix reaches (the mint if the prefix is illegal —
the attack guards below always use legal prefixes, checked by the crowned-run guard). -/
def st (ms : List Move) : DState := (replay ms).getD genesisState

/-- Patch one register field of a record (the attack-forge builder). -/
def setF (v : Value) (f : String) (x : Int) : Value :=
  match v with
  | .record fs => .record (fs.map (fun p => if p.1 = f then (f, .int x) else p))
  | v => v

/-- Mutation-canary referee: the deployed program with exactly the six
object↔projection census teeth deleted from the spent rider.  This is not an
alternative ruleset; it exists to demonstrate that the aggregate tooth, rather
than another overlapping constraint, is what rejects the two-relic/one-counter
forgery below. -/
private def spentRiderWithoutProjection : Case :=
  ⟨.slotChangedForMethods "spent" verbs,
    coreTeeth ++ rangeTeeth ++ custodyTeeth ++ [.heapField .sentinel .immutable]⟩

private def dungeonExecWithoutProjection : Dregg2.Exec.RecordProgram :=
  CellProgram.toExec (.cases
    [ genesisCase, delveCase, unlockCase, smiteCase, lootCase, fleeCase,
      depthRider, wayRider 2, wayRider 3, wayRider 4, fateRider, bankRider,
      spentRiderWithoutProjection ])

/-! ### The weld, DRIVEN (`#guard` — kernel-evaluated, no axioms):
the model-legal crowned run is admitted END TO END by the deployed program object,
and the named attacks are refused. ⚑ This is the FORWARD weld for ONE run; the general
∀-weld (every legal step admitted) is the NAMED remainder — see the module header's WELD note.
The reverse direction (admitted ⇒ the named laws) IS ∀-proven by the inversions in §4.
The runs below are driven on DAY 0 (the shipped map); the family-wide drive — every
drawn day's crowned line admitted by that day's emitted teeth — is `crownedRunAdmitted`
at the end of this section. -/

section CanonWeld
local instance : WorldParam := instAt 0

-- ⚑ THE CROWNED RUN IS ADMITTED (genesis + all 17 verbs, each step model-legal AND
-- program-admitted on the same encoded transition).
#guard programAdmitsRun crownedRun = true

-- Attack 1 — DUPE: a loot-shaped turn that mints a pack relic out of nothing
-- (pack +1, no hoard debit) breaks conservation and is refused.
#guard
  (let s := st [.delve, .smite]
   Dregg2.Exec.RecordProgram.admits dungeonExec 4 (encode s)
     (setF (setF (encode s) "pack" 1) "spent" 4)) = false

-- Attack 1b — OBJECT/PROJECTION SPLIT: debit one hoard unit and increment pack
-- by one while advancing TWO custody objects to CARRIED.  Conservation, the
-- loot frame, and both per-object ratchets all pass; the exact census is the
-- indispensable rejecting tooth.  The mutation canary proves that deleting
-- precisely `projectionTeeth` makes the same forged transition admit.
#guard
  (let s := st [.delve, .smite]
   let forged := setF (setF (setF (setF (setF (encode s)
      (relicName 1) CARRIED) (relicName 4) CARRIED)
      "pack" 1) (hoardName 1) 2) "spent" 4
   Dregg2.Exec.RecordProgram.admits dungeonExec 4 (encode s) forged) = false
#guard
  (let s := st [.delve, .smite]
   let forged := setF (setF (setF (setF (setF (encode s)
      (relicName 1) CARRIED) (relicName 4) CARRIED)
      "pack" 1) (hoardName 1) 2) "spent" 4
   Dregg2.Exec.RecordProgram.admits dungeonExecWithoutProjection 4 (encode s) forged) = true

-- Attack 2 — KEYLESS WAY: flipping way_2 without carrying key-relic 1 is refused
-- (the rider demands the exhibited key).
#guard
  (let s := st [.delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 2 (encode s)
     (setF (setF (encode s) (wayName 2) 1) "spent" 2)) = false

-- Attack 3 — STAPLE: a loot turn that ALSO descends (depth moves under method loot)
-- is refused (the loot frame freezes depth; the depth rider would demand the delve law).
#guard
  (let s := st [.delve, .smite]
   Dregg2.Exec.RecordProgram.admits dungeonExec 4
     (encode s)
     (setF (setF (setF (encode s) "pack" 1) "spent" 4) "depth" 2)) = false

-- Attack 4 — TOMB MOVE: after banking (fate = 1), a delve-shaped turn is refused.
#guard
  (let s := st [.delve, .flee]
   Dregg2.Exec.RecordProgram.admits dungeonExec 1 (encode s)
     (setF (setF (encode s) "depth" 2) "spent" 4)) = false

-- Attack 5 — FAKE FLEE: banking with a non-empty pack (keep the relics AND the score)
-- is refused (`pack' = 0` is the flee law; the fate rider re-demands it).
#guard
  (let s := st [.delve, .smite, .loot 1]
   Dregg2.Exec.RecordProgram.admits dungeonExec 5 (encode s)
     (setF (setF (encode s) "fate" 1) "spent" 5)) = false

-- Attack 6 — RELIC TELEPORT: moving a relic's custody floor→floor (code 1→2) under a
-- smite is refused (relics frozen on smite; the spent-rider's memberOf refuses code 2
-- for a floor-1-minted relic on every verb).
#guard
  (let s := st [.delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 3 (encode s)
     (setF (setF (setF (encode s) (relicName 4) 2) "spent" 3) "wounds" 1)) = false

-- Attack 7 — GENESIS REPLAY: re-running genesis after the mint (sentinel already 1)
-- is refused (the one-shot `equals 1 ∧ deltaEquals 1` is unsatisfiable from old = 1).
#guard
  (Dregg2.Exec.RecordProgram.admits dungeonExec 0 (encode genesisState)
     (encode genesisState)) = false

-- Attack 8 — UNKNOWN METHOD: a method outside the six verbs is default-denied even
-- with a fully-lawful-looking write set.
#guard
  (let s := st [.delve]
   Dregg2.Exec.RecordProgram.admits dungeonExec 7 (encode s)
     (setF (encode s) "spent" 2)) = false

-- The 27th breath: from a legally-exhausted clock nothing is admitted (driven twin of
-- `dead_light_refuses`; spent = 25 + smite(2) would break the cap).
#guard
  (let s := st [.delve, .smite]
   -- forge the clock to BREATH (the model cannot legally reach 26+2, so drive the
   -- deployed tooth directly: old spent = 26 refuses any further exertion)
   Dregg2.Exec.RecordProgram.admits dungeonExec 3
     (setF (encode s) "spent" 26)
     (setF (setF (encode s) "spent" 28) "wounds" 1)) = false

end CanonWeld

/-- **THE FAMILY WELD**: for the day at family index `k`, the crowned line generated from
that day's map is model-legal AND admitted end to end by the teeth emitted for that day.
This is the day-varying twin of the single `programAdmitsRun crownedRun` drive above. -/
def crownedRunAdmitted (k : Nat) : Bool :=
  @programAdmitsRun (instAt k) (@crownedRun (instAt k))

-- ⚑ EVERY DAY IN THE FAMILY IS PLAYABLE ON ITS OWN DEPLOYED TEETH.
#guard (List.range dayCount).all crownedRunAdmitted

/-! ## 6. The JSON emit (the checked-in artifact renderer — names, not indices). -/

private def jList (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

private def jStr (s : String) : String := "\"" ++ s ++ "\""

def HeapKeyRef.toJson : HeapKeyRef → String
  | .named n  => "{\"kind\":\"named\",\"name\":" ++ jStr n ++ "}"
  | .sentinel => "{\"kind\":\"sentinel\"}"

def HeapAtom.toJson : HeapAtom → String
  | .equals v      => "{\"kind\":\"equals\",\"value\":" ++ toString v ++ "}"
  | .immutable     => "{\"kind\":\"immutable\"}"
  | .monotonic     => "{\"kind\":\"monotonic\"}"
  | .memberOf set  => "{\"kind\":\"memberOf\",\"set\":" ++ jList (set.map toString) ++ "}"
  | .deltaEquals d => "{\"kind\":\"deltaEquals\",\"d\":" ++ toString d ++ "}"

def Simple.toJson : Simple → String
  | .fieldEquals r v => "{\"kind\":\"fieldEquals\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldGte r v    => "{\"kind\":\"fieldGte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldLte r v    => "{\"kind\":\"fieldLte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .immutable r     => "{\"kind\":\"immutable\",\"reg\":" ++ jStr r ++ "}"
  | .negate inner    => "{\"kind\":\"not\",\"inner\":" ++ inner.toJson ++ "}"

def jPair (p : Nat × Nat) : String :=
  "[" ++ toString p.1 ++ "," ++ toString p.2 ++ "]"

def jTerm (t : Int × String) : String :=
  "[" ++ toString t.1 ++ "," ++ jStr t.2 ++ "]"

def Constraint.toJson : Constraint → String
  | .fieldEquals r v => "{\"kind\":\"fieldEquals\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldGte r v    => "{\"kind\":\"fieldGte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldLte r v    => "{\"kind\":\"fieldLte\",\"reg\":" ++ jStr r ++ ",\"value\":" ++ toString v ++ "}"
  | .fieldDelta r d  => "{\"kind\":\"fieldDelta\",\"reg\":" ++ jStr r ++ ",\"d\":" ++ toString d ++ "}"
  | .strictMonotonic r => "{\"kind\":\"strictMonotonic\",\"reg\":" ++ jStr r ++ "}"
  | .immutable r     => "{\"kind\":\"immutable\",\"reg\":" ++ jStr r ++ "}"
  | .sumEquals rs v  => "{\"kind\":\"sumEquals\",\"regs\":" ++ jList (rs.map jStr) ++ ",\"value\":" ++ toString v ++ "}"
  | .affineLe ts c   => "{\"kind\":\"affineLe\",\"terms\":" ++ jList (ts.map jTerm) ++ ",\"c\":" ++ toString c ++ "}"
  | .inRangeTwoSided r lo hi =>
      "{\"kind\":\"inRangeTwoSided\",\"reg\":" ++ jStr r ++ ",\"lo\":" ++ toString lo ++ ",\"hi\":" ++ toString hi ++ "}"
  | .allowedTransitions r al =>
      "{\"kind\":\"allowedTransitions\",\"reg\":" ++ jStr r ++ ",\"allowed\":" ++ jList (al.map jPair) ++ "}"
  | .anyOf vs        => "{\"kind\":\"anyOf\",\"variants\":" ++ jList (vs.map Simple.toJson) ++ "}"
  | .heapField k a   => "{\"kind\":\"heapField\",\"key\":" ++ k.toJson ++ ",\"atom\":" ++ a.toJson ++ "}"
  | .countFieldsEq ks v r =>
      "{\"kind\":\"countFieldsEq\",\"keys\":" ++ jList (ks.map HeapKeyRef.toJson)
        ++ ",\"value\":" ++ toString v ++ ",\"reg\":" ++ jStr r ++ "}"

def Guard.toJson : Guard → String
  | .methodIs m => "{\"kind\":\"methodIs\",\"method\":" ++ jStr m ++ "}"
  | .slotChangedForMethods reg ms =>
      "{\"kind\":\"slotChangedForMethods\",\"reg\":" ++ jStr reg
        ++ ",\"methods\":" ++ jList (ms.map jStr) ++ "}"

def Case.toJson (c : Case) : String :=
  "    {\"guard\":" ++ c.guard.toJson ++ ",\"constraints\":["
    ++ String.intercalate "," (c.constraints.map Constraint.toJson) ++ "]}"

/-- The scene id that fixes the deterministic world-cell identity
(must match `dungeon_on_dregg::descent::SCENE_ID`). -/
def sceneId : String := "dungeon-on-dregg/descent1"

/-- **`emitJson` — render ONE day's descent program to artifact bytes.**
One case per line for stable diffs; a deterministic function of `dungeonProgram`. -/
def emitJson (p : CellProgram) : String :=
  match p with
  | .cases cs =>
    "{\n  \"scene\": " ++ jStr sceneId ++ ",\n  \"cases\": [\n"
      ++ String.intercalate ",\n" (cs.map Case.toJson)
      ++ "\n  ]\n}\n"

/-- One family member as an artifact entry: the drawn map (for the loader's mover) plus
the FULL teeth emitted for exactly that map. The loader never assembles a constraint —
it resolves names to slots inside the case list Lean wrote. -/
def worldJson (k : Nat) : String :=
  let W := worldAt k
  "    {\"day\":" ++ toString k
    ++ ",\"homes\":" ++ jList (W.homes.map toString)
    ++ ",\"ghp\":" ++ jList (W.ghp.map toString)
    ++ ",\"cases\":[\n"
    ++ String.intercalate ",\n" ((match (@dungeonProgram (instAt k)) with | .cases cs => cs).map Case.toJson)
    ++ "\n    ]}"

/-- **The deployed artifact: the WHOLE drawn family, one emitted program per day.**
The committed day-seed picks the index; every index here is a checked, driven-completable
map (`Dungeon.drawFamily_wf`, `Dungeon.winsAt_true`). -/
def emitFamilyJson : String :=
  "{\n  \"scene\": " ++ jStr sceneId
    ++ ",\n  \"days\": " ++ toString dayCount
    ++ ",\n  \"worlds\": [\n"
    ++ String.intercalate ",\n" ((List.range dayCount).map worldJson)
    ++ "\n  ]\n}\n"

section CanonEmit
local instance : WorldParam := instAt 0

-- The emit runs and carries the scene header + all 13 cases, for every day.
#guard (emitJson dungeonProgram).startsWith "{\n  \"scene\": \"dungeon-on-dregg/descent1\""
#guard (match dungeonProgram with | .cases cs => cs.length) = 13
#guard emitFamilyJson.startsWith "{\n  \"scene\": \"dungeon-on-dregg/descent1\",\n  \"days\": 16"
#guard (List.range dayCount).all
        (fun k => (match (@dungeonProgram (instAt k)) with | .cases cs => cs).length == 13)

end CanonEmit

/-! ## 7. Axiom hygiene — every connection theorem on the standard kernel triple. -/

#assert_axioms admits_cases_mem
#assert_axioms verb_core_teeth
#assert_axioms admitted_verb_conserves
#assert_axioms admitted_verb_capacity
#assert_axioms admitted_verb_pays
#assert_axioms admitted_verb_alive
#assert_axioms banked_tomb_refuses
#assert_axioms dead_light_refuses
#assert_axioms way_flip_exhibits_key
#assert_axioms way2_flip_exhibits_key
#assert_axioms way3_flip_exhibits_key
#assert_axioms way4_flip_exhibits_key
#assert_axioms unknown_method_refused

end Dregg2.Games.Dungeon.Prog
