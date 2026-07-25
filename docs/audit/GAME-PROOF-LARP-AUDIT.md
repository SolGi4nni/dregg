# Game-Proof LARP Audit — tug "admission refinement closed" + dungeon "deployed-teeth soundness"

**Status:** adversarial audit, 2026-07-18. READ-ONLY — no source edited, nothing committed.
**Scope:** the two just-committed "proofs":
- `1145f6680` — multiway-tug: "CLOSE the admission refinement … PROVEN to admit exactly the legal game".
  Files: `metatheory/Dregg2/Games/{MultiwayTug,MultiwayTugAir,MultiwayTugProgram}.lean`.
- `6d4d83bd5` — The Descent: "proven against arbitrary attacker states … DEPLOYED-TEETH SOUNDNESS".
  Files: `metatheory/Dregg2/Games/{Dungeon,DungeonProgram}.lean`, `metatheory/EmitDungeonProgram.lean`.

**Default posture (honesty guarantee): REFUTED until shown load-bearing AND reaching the deployed Rust object.**

---

## 0. The one finding that governs everything

Both commits emit the **program DATA** (which constraints, in which cases, at which thresholds)
from Lean, drift-gate it (`regen.sh --check`), and load it into Rust
(`include_str!` + `serde_json::from_str`, resolved against the schema allocator). **That data
connection is REAL and is a genuine improvement** over the old hand-rolled Rust teeth.

But every "refinement"/"soundness" theorem proves a property of a **Lean evaluator**, not of the
Rust evaluator that actually admits/rejects turns:

- Tug proves against `Prog.Constraint.admits` / `Prog.HeapAtom.admits` / `Prog.CellProgram.admitsMethod`
  (`MultiwayTugProgram.lean:342-386`) — a **hand-authored Lean copy** of `cell/src/program/eval.rs`.
- Dungeon proves against `Dregg2.Exec.RecordProgram.admits` (`Exec/Program.lean:648`) — the same
  parallel Lean evaluator the pre-existing `docs/audit/SEMANTIC-LEAN-BOUNDARY.md` (Class B, rows 73-77)
  already flagged as "never reaches the deployed Rust object."

**Ground-truth checks run for THIS audit (all confirmed):**
- `grep -c '@[export]'` on `Exec/Program.lean`, `DungeonProgram.lean`, `MultiwayTugProgram.lean` → **0, 0, 0.**
  Rust does not call the Lean evaluator; there is no FFI.
- `cell/src/program/eval.rs` references Lean only in **comments** ("mirrors Lean …") — prose doc-pins.
- **No differential harness** runs the Lean `admits` against Rust `evaluate_constraint_full` on shared inputs.
- The Lean and Rust evaluators **already disagree**, concretely:
  - **immutable heap atom.** Lean `HeapAtom.admits … | .immutable, old, new => decide (new = old)`
    (`MultiwayTugProgram.lean:359`). Rust `HeapAtom::Immutable => match old_v { None => Ok(()), Some(a) => new_v == Some(a) }`
    (`eval.rs:2382-2398`). For absent-old, Lean **refuses** any write, Rust **admits the first write**. (Harmless in
    the proven tug cases only because the sentinel is always `some 1` — but it proves the Lean `admits` is an
    independent authoring, not a reading of eval.rs.)
  - **numeric model.** Lean Exec `.fieldGe f v => intLe val x` = **signed unbounded `Int`** (`Exec/Program.lean:456`);
    Rust `field_gte(a,b) = a >= b` = **unsigned 256-bit big-endian FieldElement** (`eval.rs:2842`). These disagree near
    the field modulus and on the sign boundary — the exact confirmed divergence in `SEMANTIC-LEAN-BOUNDARY.md:74`.
  - Lean tug `Constraint.admits` takes `old new : Counters` **both present**; Rust's register constraints all carry a
    `None` (old-state absent / `nonce == 0` genesis) branch (`eval.rs:363-370,390-397,413-420,438-445`) the Lean model
    omits entirely.

So the disease `SEMANTIC-LEAN-BOUNDARY.md` maps — **PARALLEL-DISCONNECTED** — is **not closed by these commits; it is
reproduced one layer inward.** The theorems are honest theorems about a Lean model of the referee; the
model==eval.rs link is prose ("faithful reading", "the Rust evaluator mirrors") plus per-case driven Rust tests.

---

## 1. TUG — per-theorem classification (`MultiwayTugProgram.lean` unless noted)

| Theorem | Line | Class | Why |
|---|---|---|---|
| `program_admits_legal_play` | 621 | **MODEL-DISCONNECTED + HYPOTHESIS-LADEN + FORWARD-ONLY** | Proves `admitsMethod multiwayTugProgram (methodOf a) (abstract o) (abstract (applyLegal o p a)) = true`. (a) `admitsMethod`/`Constraint.admits` is the hand-authored Lean copy of eval.rs (see §0). (b) Carries `hcons : (totalCards o).card = 21` — the seeded-deck invariant, undischarged here (only holds on the α-image of model runs). (c) **Forward only**: proves legal ⇒ admitted; the reverse (admitted ⇒ legal) is NOT proven and *cannot* be for a cardinality-blind counter program. The whole statement lives in the image of `abstract` — it says nothing about arbitrary attacker counters. |
| `commonAndAction_admits` | 566 | MODEL-DISCONNECTED + HYPOTHESIS-LADEN | The engine of the above; each tooth discharged against a proven model invariant, but against the Lean `admits` and under `hcons`. |
| `winTooth_admits_iff_Won_p1` / `_p2` | 649 / 659 | **MODEL-DISCONNECTED** (else REAL) — ⚑ **DELETED 2026-07-25, and the audit's own verdict was too kind** | A genuine, non-vacuous **iff** between the win-tooth's Lean `admits` on `scoredCounters s who` and `Won s p`. Closest thing to a soundness bridge — but at the Lean-evaluator layer, and over `scoredCounters` (α-image with `winner` injected), not arbitrary attacker counters. **⚑ THE MISS:** the theorem was TRUE and that was the bug. It certified that the deployed gate IS `Won`, the ABSOLUTE bar — while the model's terminal rule is `roundWinner`, which adjudicates every sub-threshold round. So the deployed referee provably REFUSED the winner the proven rule names, and the played game drew a measured 78.5% of rounds against the model's 5.1%. An audit that reads a theorem's proof but not its SUBJECT cannot see this class: the statement was sound, the object it was about was the wrong one. Replaced by `scoreBranchTeeth_admits_iff_branch` (one deployed case per clause of `roundWinner`). |
| `Won_iff_program_thresholds` | 282 | **TAUTOLOGY** | `Won s p ↔ (winCharmThreshold ≤ charmScore ∨ winGuildThreshold ≤ geishaScore) := Iff.rfl`. `Won` is *defined* as exactly that, and `winCharmThreshold` is `abbrev`= `charmWinThreshold`. This is `Won ↔ (Won unfolded)`. **The doc-comment claim "edit `winCharmThreshold` here and this theorem REDS" is false** — both sides read the same abbrev, so `Iff.rfl` survives any value change. |
| `winGate_thresholds_match_Won` | 271 | TRIVIAL-but-REAL | `winCharmThreshold = 11 ∧ winGuildThreshold = 4 := ⟨rfl,rfl⟩`. A literal pin of the abbrev values; honestly labeled "structural pin." (This one *would* red on an abbrev edit — unlike the `Iff.rfl` above.) |
| `winTooth_shape` | 288 | TAUTOLOGY (unfold `:= rfl`) | Legibility pin; fine. ⚑ DELETED 2026-07-25 with `winTooth` itself; the successor pin is `scoreBranchTeeth_threshold_shape`. |
| `conservation_tooth_covers_totalCards` | 300 | TAUTOLOGY (`⟨rfl,rfl⟩`) | Arity + literal-list pin of `conservationRegs`. Real as a shape check. |
| `program_has_one_case_per_method` | 308 | TAUTOLOGY (`:= rfl`) | Emitted-DATA shape check. Real, trivial. |
| `score_case_carries_both_win_gates` | 315 | REAL (structural, `decide`) | Non-vacuous check on the emitted DATA that the score case contains both win teeth. About shape, not semantics. |
| `conservationSum_eq` | 472 | REAL (Lean-model) | `(conservationRegs.map (abstract s).reg).sum = (totalCards s).card`. Ties the Lean `SumEquals` read to `totalCards`. Real, but Lean-model-side. |
| `conservationValue_eq`, `flagNames_literal`, `scoreNames_literal` | 163/145/151 | REAL (`decide` byte-pins) | The un-mirror: derived deck-size 21 + generated wire names. Genuinely good. |
| `genesis_admits_first` / `genesis_restaple_refused` | 676 / 684 | **DRIVEN-NOT-PROVEN + MODEL-DISCONNECTED** | `decide` on two specific `sentinelCounters`. Lean twins of the runtime one-shot canary — specific cases against the Lean evaluator, not ∀. |
| `play_admitted_by_both` | 701 | MODEL-DISCONNECTED + HYPOTHESIS-LADEN | Composes `airPlay` (carries `hsound : MerkleSound M`) with `program_admits_legal_play` (carries `hcons`). Two undischarged hypotheses; both referees are Lean. |
| `airPlay_iff_applyAction` (`MultiwayTugAir.lean`) | 138 | **HYPOTHESIS-LADEN + MODEL-DISCONNECTED** | Non-vacuous within Lean (`MerkleSound` is load-bearing), but `MerkleSound M` is a **carried hypothesis** for the deployed Poseidon2 STARK, and `airPlay`↔`fold.rs::membership_leaf_for_play` is pure prose ("the Lean shadow of fold.rs"). The file header now self-labels this "⚠ NOT connected to the deployed Rust fold" — honest. |

**Non-vacuity note:** the tug model theorems in `MultiwayTug.lean` (`conservation`, `used_monotone`,
`geishaCount_mono`, `won_needs_control`, `winState_wins`, `conservation_along_run`) are **REAL, non-vacuous
theorems about the multiset model.** They are not the LARP; they just do not reach the deployed object on their own.

---

## 2. DUNGEON — per-theorem classification

### 2a. `Dungeon.lean` — model laws (the rulebook `step`)

`capacity_attenuates` (497), `the_light_dies` (503), `run_bounded` (518), `banked_run_frozen` (545),
`keyless_unlock_impossible` (554), `custody_ratchet` (565), `no_run_banks_everything` (616),
`crowned_bank_le_four` (636): **REAL, non-vacuous ∀-theorems about the Lean `step` model** (genuine
inductive invariant `Inv`, real multiset/`countP` arithmetic, driven crowned run + 5 refusals as `#guard`s).
Classification: **REAL-MODEL.** They are about `Dungeon.step`, which is **not** the deployed object — they
reach deployment only through the `DungeonProgram` bridge below, which is Exec-level.

### 2b. `DungeonProgram.lean` — the "deployed-teeth" inversions

| Theorem | Line | Class | Why |
|---|---|---|---|
| `admitted_verb_conserves` | 420 | **MODEL-DISCONNECTED** | Genuine ∀ over arbitrary `o n : Value`: any admitted verb ⇒ `sumScalars n zones = some RELICS`. But against `Dregg2.Exec.RecordProgram.admits` (Lean evaluator), not eval.rs. Also conserves the **register** zone-mirror only; the custody↔counter bijection is a named seam (§2c). |
| `admitted_verb_capacity` | 430 | **MODEL-DISCONNECTED** | `pack + depth ≤ CAP` via `affineLe`. Exec `affineLe` is **signed `Int` `intLe`**; the deployed field compare is **unsigned 256-bit** (`eval.rs:2842`). The proof does not capture the deployed wrap semantics. |
| `admitted_verb_pays` | 457 | **MODEL-DISCONNECTED** | `strictMono spent` + `fieldLe spent BREATH`, both signed-`Int` Exec vs unsigned-field Rust. |
| `admitted_verb_alive` | 474 | MODEL-DISCONNECTED | `allowedTransitions "fate" [(0,0),(0,1)]`. Real ∀ over Exec Values. |
| `banked_tomb_refuses` | 502 | MODEL-DISCONNECTED | Corollary of `admitted_verb_alive`; real over Exec. |
| `dead_light_refuses` | 516 | MODEL-DISCONNECTED | Corollary of `admitted_verb_pays`; inherits the signed/unsigned gap. |
| `way2_flip_exhibits_key` | 533 | **MODEL-DISCONNECTED (+ substrate-collapse)** | The one heap-atom-dependent inversion. `toExec` lowers `HeapAtom.equals CARRIED` on the relic **heap key** to `.simple (.fieldEquals (relicName 1) CARRIED)` — a **record scalar** (`DungeonProgram.lean:332`). Rust keeps relics as heap keys (`descent.rs: self.key(...) → Slot::Heap`) with distinct fail-closed absent-semantics. The Lean proof never sees that distinction. Proven for way 2 only; ways 3/4 are Rust-driven. |
| `unknown_method_refused` | 582 | MODEL-DISCONNECTED (else REAL) | Real ∀ `m ≥ 6` default-deny over Exec. Good theorem, wrong evaluator. |
| `admits_cases_mem`, `verb_core_teeth` | 372, 391 | plumbing | Sound structural lemmas over Exec `RecordProgram.admits`. |

### 2c. The driven weld + the honest seam

- `#guard programAdmitsRun crownedRun = true` (663) + 9 attack `#guard`s (665-729): **DRIVEN-NOT-PROVEN** —
  a single legal run and specific forged transitions, against the Exec evaluator. The model↔program weld
  (**model-legal ⟺ program-admitted**) is checked on `crownedRun` only; there is **no ∀-theorem** that a
  model-legal step is program-admitted (the commit admits: "∀-completeness is driven for the script, not a theorem").
- **count↔custody bijection: honestly named, genuinely absent from the teeth.** `pack`/`bank`/`hoard_d` are
  register scalars; custody is per-relic heap. The deployed teeth enforce `sumEquals zones = RELICS` (registers)
  and per-relic custody ratchet (heap) **separately** — nothing ties "the `pack` register = count of `CARRIED`
  custody codes." That equality lives only in `Dungeon.lean` (`pack := custody.countP (·==CARRIED)`) and is
  carried by `encode`. So `admitted_verb_conserves` does NOT forbid a register/custody disagreement on an
  attacker Value. Correctly flagged as a seam in the file header (56-58) and commit body.

---

## 3. Honest bottom line — what is REAL vs LARP

### TUG (`1145f6680`)
- **REAL:** the emitted program DATA (cases/teeth/thresholds/generated names/derived deck-size 21) is
  Lean-authored, drift-gated, and loaded by Rust; the `MultiwayTug.lean` multiset model + its
  conservation/win-safety theorems; `winTooth_admits_iff_Won` and `conservationSum_eq` as **Lean-evaluator**
  bridges; the un-mirror (generated wire names, single-source thresholds).
- **LARP / over-claim:** the commit title **"PROVEN to admit exactly the legal game."** "Exactly" claims an
  **iff**; only the **forward** direction (`legal ⇒ admitted`) is proven, and only against a **hand-authored Lean
  copy** of eval.rs, under the carried `card = 21` hypothesis, over the α-image of model states. The reverse
  (soundness: `admitted ⇒ legal`) is neither proven nor provable for the cardinality-blind counter program — it
  is punted to `airPlay` (itself gated on undischarged `MerkleSound`) and a "NAMED next step" substrate bridge.
  `Won_iff_program_thresholds` is an `Iff.rfl` tautology whose "canary reds on edit" narration is false.
  **Nothing machine-checks `Prog.Constraint.admits` == Rust `evaluate_constraint_full`; they already diverge (§0).**

### DUNGEON (`6d4d83bd5`)
- **REAL:** the emitted DATA connection (as tug); `Dungeon.lean` is a strong, non-vacuous native model; the
  `DungeonProgram` inversions are **genuine ∀-theorems over arbitrary `Value`s** (strictly stronger than tug's
  forward-only α-image result — this IS the payoff the header claims tug couldn't reach); `SlotChanged` riders
  structurally retire the stapleable-slot class **within the Exec model**; 14 real-executor `#[test]`s refuse the
  named attacks (real `WorldError::Refused`).
- **LARP / over-claim:** the headline **"proven against arbitrary attacker states"** / **"DEPLOYED-TEETH
  SOUNDNESS … the theorems run against the LAW-#1 Exec evaluator."** The theorems run against the **Lean `Exec`
  evaluator**, which is a **parallel-disconnected copy** of Rust `eval.rs` (no `@[export]`, substrate mismatch,
  confirmed signed-`Int`-vs-unsigned-256-bit divergence, `toExec` collapses heap keys to record scalars). The word
  "deployed"/"mirrors" imports an **unproven** Exec == eval.rs equivalence. "Arbitrary attacker states" is true of
  arbitrary Exec `Value`s — **not** of arbitrary deployed `CellState`s (`[FieldElement;16]` + heap map). The
  model↔program weld and ways-3/4 are **driven**, not proven.

**One-line verdict:** both commits genuinely move *which teeth* into Lean (real, drift-gated, loaded). Neither
moves *what the teeth mean* into the proof's reach — the referee semantics the theorems quantify over is a Lean
re-authoring of `eval.rs`, tied to the deployed evaluator by prose + per-case tests, and demonstrably already
divergent. Dungeon is the more honest and stronger of the two (real ∀-inversions, self-named seams); tug's
"admit **exactly**" is the sharper over-claim (forward-only, tautology canary, cardinality-blind).

---

## 4. The concrete path to make each real (the missing gate)

The single missing gate, for both, is a **machine-checked tie between the Lean evaluator and Rust
`evaluate_constraint_full`**. In descending order of fidelity:

1. **Collapse the two evaluators into one (the CLAUDE.md-correct fix).** `@[export]` a single Lean decision
   procedure for `admits` (over the real substrate) and have Rust `eval.rs` **call into it** instead of carrying
   its own `match`. Then eval.rs is a thin caller, not a parallel semantics, and the existing theorems become
   theorems about the deployed evaluator. Requires the Lean evaluator to adopt the Rust state model
   (`[FieldElement;16]` + heap map, **unsigned** field arithmetic) — see step 3.
2. **If Rust must keep its own evaluator (perf/field math): add a DIFFERENTIAL CI gate.** Run the Lean `admits`
   and Rust `evaluate_constraint_full` on the **same** `(program, old, new)` samples — fuzzed, and explicitly
   including the boundaries where they are known to diverge (**field modulus / sign boundary; absent-vs-zero;
   absent-old immutable/write-once; genesis `nonce == 0`**) — and assert byte-equal accept/reject. This is not a
   ∀-proof, but it converts the prose "mirror" into a checked correspondence and would immediately catch the
   immutable-atom and signed/unsigned bugs found in §0.
3. **Unify the substrate (prerequisite for 1, hardens 2).** Give the Lean evaluator the deployed state model and
   **unsigned 256-bit** compares (kill the signed-`Int` `intLe`). Then also discharge the **symbolic-name ↔
   slot-index** layer: today the Lean uses names and Rust's `allocate_checked` resolves them; that translation is
   asserted "translation-validated" but is **not audited or proven** in these commits — it is a second unchecked
   seam under the data connection.
4. **Tug-specific:** either prove the **reverse** direction (`admitsMethod ⇒ legal`) — impossible for the
   cardinality-blind counter program alone, so it must go through a **discharged** `airPlay` (discharge
   `MerkleSound` = the Poseidon2 STARK soundness + the fold IVC) — or stop titling it "admit **exactly**" and call
   it forward completeness. Fix the `Won_iff_program_thresholds` narration: make `Won` and the gate read
   **independent** constants and prove them equal (a real pin), or drop the false "reds on edit" canary claim.
5. **Dungeon-specific:** turn the model↔program weld into a ∀-theorem (`step s m = some s' ⟹
   RecordProgram.admits dungeonExec (moveIdx m) (encode s) (encode s') = true`, and the soundness converse over
   the reachable image), and prove ways 3/4 (not just way 2). Add a teeth-level tie for the count↔custody
   bijection, or accept it as an explicit engine-enforced invariant with its own driven gate.
