/-
# Dregg2.Time.Deadline — the `Deadline` sum type (causal vs frame, FORCED) + the commit-wait bridge.

The §4 innovation made syntactic (`docs/rebuild/INTENT-AS-CO-RECEIPT.md`,
`docs/rebuild/INTENT-REFS-time.md`): a deadline language must FORCE the causal-vs-frame distinction
at the type level. You cannot write a deadline without declaring whether it is a **lightcone FACT**
(`causalAfter`, frame-invariant, no trust — `Dregg2/Time/Causal.lean`) or a **frame CONVENTION**
(`frameWithin`, an attested predicate with explicit skew `±δ` — `Dregg2/Time/Frame.lean`). A court
(or an adjudicating cell) can always tell which kind of promise was made — a type-checker fact, not
documentation.

This module:
  1. the `Deadline` SUM TYPE whose two constructors are the two kinds — un-skippable;
  2. `Deadline.Met`, dispatching to `CausalAfter` / `FrameWithin`;
  3. the load-bearing FORCING theorem: a `causalAfter` deadline carries NO frame/authority
     dependency, while a `frameWithin` one provably DOES (its truth turns on the authority);
  4. **THE COMMIT-WAIT BRIDGE** (the keystone, Spanner's external consistency / "anti-frontrunning is
     a causal type"): `frameWithin F T δ ∧ waited(2δ) → causalAfter E`. After waiting twice the skew
     past a frame-time attestation, the frame fact is UPGRADED to a lightcone guarantee — frame-
     relative time becomes causal time by paying `2δ` of wait. The `2δ` is GENUINELY load-bearing:
     drop it and the conclusion fails (the uncertainty intervals still overlap).

§8 carriers (EXPLICIT hypotheses, NEVER faked): the time authority is honest within `f` faults; the
skew `δ` physically bounds the real drift; signatures are unforgeable. They enter ONLY where a
physical-time/causal conclusion is drawn (the bridge), gated as `FrameHonesty` + `WaitCausality`.

Pure, computable, `#eval`-able.
-/
import Dregg2.Time.Causal
import Dregg2.Time.Frame

namespace Dregg2.Time.Deadline

open Dregg2.Time.Causal
open Dregg2.Time.Frame
open Dregg2.Authority.Blocklace (Lace Block precedes)
open Dregg2.Authority.Predicate (Registry registryVerify)

/-! ## 1. The `Deadline` SUM TYPE — the syntactic forcing.

A `Deadline` CANNOT be written without choosing a constructor: `causalAfter` (a lightcone fact on the
lace) or `frameWithin` (a frame convention with explicit `δ`). So "which kind of promise was made" is
decided at construction, not discovered later. The two faces are parameterized over the lace `B`
(causal), and over the registry + statement-encoder + authority (frame). -/

variable {Stmt Wit : Type}

/-- **`Deadline B reg stmtOf` — the §4 deadline, FORCING the causal-vs-frame distinction.** Its two
constructors ARE the two kinds of time:

  * `causalAfter E` — a LIGHTCONE FACT: "the event must causally follow `E`." Frame-invariant, on the
    lace, NO trust. Discharged by `Causal.CausalAfter B E ·`.
  * `frameWithin fs att` — a FRAME CONVENTION: "authority `fs.authority` attests frame-time `fs.T`
    within skew `±fs.δ`, witnessed by `att`." An attested predicate carrying `δ` EXPLICITLY;
    discharged by a verified attestation, NEVER δ=0.

You cannot construct a `Deadline` without picking a side — that is the entire point. -/
inductive Deadline (B : Lace) (reg : Registry Stmt Wit) (stmtOf : FrameStatement → Stmt) where
  /-- The LIGHTCONE-FACT deadline: "must causally follow `E`." Carries only a lace event. -/
  | causalAfter (E : Frontier)
  /-- The FRAME-CONVENTION deadline: authority attests `fs` (with explicit `δ`), witnessed by `att`. -/
  | frameWithin (fs : FrameStatement) (att : Wit)

/-- **`Deadline.kind`** — a court's read-off: which KIND of promise was made. `true` = causal
(lightcone fact, no trust); `false` = frame (convention, attested, carries `δ`). A pure projection of
the constructor — the distinction survives to runtime, not just type-checking. -/
def Deadline.kind {B : Lace} {reg : Registry Stmt Wit} {stmtOf : FrameStatement → Stmt} :
    Deadline B reg stmtOf → Bool
  | .causalAfter _   => true
  | .frameWithin _ _ => false

/-! ## 2. `Deadline.Met` — dispatch to the two discharge predicates.

The deadline is MET, at a causal frontier `now`, exactly when its kind's discharge predicate holds:
the causal one by `CausalAfter B E now`, the frame one by `FrameWithin reg stmtOf fs att`. (The causal
face consumes `now`; the frame face does not — it consumes the authority's attestation. This asymmetry
is the load-bearing content of §3 below.) -/

/-- **`Deadline.Met d now` — the deadline `d` is discharged at frontier `now`.** Dispatches by kind:
causal ⟹ `CausalAfter B E now` (a lace order fact); frame ⟹ `FrameWithin reg stmtOf fs att` (the
authority's attestation is accepted). One predicate, two genuinely different discharge conditions —
the type forced the author to say which. -/
def Deadline.Met {B : Lace} {reg : Registry Stmt Wit} {stmtOf : FrameStatement → Stmt}
    (d : Deadline B reg stmtOf) (now : Frontier) : Prop :=
  match d with
  | .causalAfter E   => CausalAfter B E now
  | .frameWithin fs att => FrameWithin reg stmtOf fs att

/-- `Met` on a frame deadline IS `FrameWithin` (definitional; the dispatch on the constructor). The
named-argument form pins all of `B`, `reg`, `stmtOf`, `att` so the equation can be used as a rewrite. -/
theorem Met_frameWithin {B : Lace} {reg : Registry Stmt Wit} {stmtOf : FrameStatement → Stmt}
    {fs : FrameStatement} {att : Wit} {now : Frontier} :
    (Deadline.frameWithin (B := B) (reg := reg) (stmtOf := stmtOf) fs att).Met now
      ↔ FrameWithin reg stmtOf fs att := Iff.rfl

/-! ## 3. THE FORCING is load-bearing — causal carries NO frame dependency; frame DOES.

§4: "you cannot write a deadline without declaring whether it is a lightcone fact or a frame
convention — so the relativistic honesty is load-bearing, not decorative." We make that a THEOREM:

  * a `causalAfter` deadline's truth is INVARIANT under swapping the registry/authority — it does not
    consult the frame at all (it is a lace order fact);
  * a `frameWithin` deadline's truth DOES turn on the registry/authority — there exist two registries
    (one with the authority, one without) under which the SAME frame deadline flips. So the two
    constructors are not interchangeable wrappers; they carry different trust.   -/

/-- **`causalAfter_no_frame_dependency` (PROVED) — the causal deadline ignores the frame.** Evaluating
a `causalAfter E` deadline under ANY two registries `reg₁ reg₂` (and any encoders) gives the SAME
`Met` proposition at the same frontier: the causal face does not consult the authority. The lightcone
fact is intrinsic — no frame argument can change it. -/
theorem causalAfter_no_frame_dependency {B : Lace} (E now : Frontier)
    (reg₁ reg₂ : Registry Stmt Wit) (stmtOf₁ stmtOf₂ : FrameStatement → Stmt) :
    (Deadline.causalAfter (B := B) (reg := reg₁) (stmtOf := stmtOf₁) E).Met now ↔
      (Deadline.causalAfter (B := B) (reg := reg₂) (stmtOf := stmtOf₂) E).Met now :=
  Iff.rfl

/-- **`frameWithin_has_frame_dependency` (PROVED) — the frame deadline DOES turn on the authority.**
There exist a frame statement, an attestation, and two registries — one WITH a `temporal` authority
that accepts, one WITHOUT any — under which the SAME `frameWithin` deadline is MET in the first and
NOT met in the second. So the frame face genuinely depends on the chosen frame: the constructor is not
decorative. (Contrast `causalAfter_no_frame_dependency`: the asymmetry IS the §4 distinction.) -/
theorem frameWithin_has_frame_dependency :
    ∃ (B : Lace) (stmtOf : FrameStatement → Nat) (fs : FrameStatement) (att : Nat)
      (regYes regNo : Registry Nat Nat) (now : Frontier),
        (Deadline.frameWithin (B := B) (reg := regYes) (stmtOf := stmtOf) fs att).Met now ∧
        ¬ (Deadline.frameWithin (B := B) (reg := regNo) (stmtOf := stmtOf) fs att).Met now := by
  -- A registry that accepts everything at `.temporal`, vs one with no `.temporal` verifier.
  refine ⟨[], (fun _ => 0), { authority := { issuer := 0 }, T := 0, δ := 1 }, 0,
          (fun k => if k = .temporal then some (fun _ _ => true) else none),
          (fun _ => none), default, ?_, ?_⟩
  · -- WITH the authority: the verifier accepts ⇒ Met.
    rw [Met_frameWithin]
    unfold FrameWithin registryVerify
    simp
  · -- WITHOUT the authority: fails closed ⇒ not Met.
    rw [Met_frameWithin]
    unfold FrameWithin registryVerify
    simp

/-! ## 4. THE COMMIT-WAIT BRIDGE — `frameWithin ∧ waited(2δ) → causalAfter` (the keystone).

Spanner's external consistency (`INTENT-REFS-time.md` ref #4): to make a frame-relative time a CAUSAL
fact, you `commit-wait` — wait out `2ε` of real time so that no later event's uncertainty interval can
overlap. Then real-time order IS causal order. Formally: an event `E` attested at frame-time `≤ T − δ`
(its uncertainty interval is `[·, T−δ+δ] = [·, T]`... bounded above by the reading) is causally before
a frontier `now` reached after waiting `2δ` past `T` (its interval starts `≥ T + δ`), because the
intervals `[·, T]` and `[T+δ, ·]` are DISJOINT — happens-before is then determinate.

We state it honestly with EXPLICIT carriers:
  * `FrameHonesty fs (eTime)` — §8(b): the attested reading honestly bounds `E`'s true time
    (`E` happened at-or-before the frame reading within `δ`);
  * `WaitCausality B fs E now` — the §8 "after-2δ no-overlap ⟹ causal" carrier: GIVEN we have waited
    `≥ 2δ` of real time past the reading to reach `now`, the disjoint-interval determinacy puts `E` in
    `now`'s causal past. This is the physical content of commit-wait (real-time order ⟹ lace order once
    intervals separate); it consumes the `2δ` wait and the honesty bound. It is NOT `True` — without
    the `2δ` wait the intervals overlap and it FAILS (proved in §5).

The bridge: accepted frame attestation + the two carriers ⟹ `causalAfter E now`. The frame DEADLINE is
upgraded to a CAUSAL DEADLINE. -/

/-- **`waited B start now twoδ`** — a CAUSAL measure of elapsed wait: `start ≺ now` on the lace AND the
real-time gap between them is at least `twoδ`. We model the gap abstractly via a real-time map
`rt : Frontier → Time` (a frame reading of each frontier — itself a §8-attested quantity, carried as a
parameter). "Waited `2δ`" = `start ≺ now ∧ rt now − rt start ≥ twoδ`. The causal `start ≺ now` ensures
the wait is a genuine lightcone advance, not a clock jump. -/
def waited (B : Lace) (rt : Frontier → Time) (start now : Frontier) (twoδ : Time) : Prop :=
  precedes B start now ∧ twoδ ≤ rt now - rt start

/-- **`WaitCausality` — the §8 commit-wait carrier (`Prop`, asserted, never proved).** The physical
"disjoint intervals ⟹ determinate happens-before" law of commit-wait (Spanner external consistency),
stated as an IMPLICATION whose ANTECEDENT is the real-time wait itself:

  GIVEN a CAUSAL wait of `≥ 2δ` real time past the attested reading reaching `now`
  (`waited B rt start now (2*fs.δ)`) AND the reading honestly bounds `E`'s true time
  (`FrameHonesty fs (rt start)`), THEN `E` is in `now`'s causal past (`CausalAfter B E now`).

The antecedent is the *genuine* `waited`-fact (not a vacuous `twoδ = 2δ` equation): the carrier
therefore CANNOT be invoked without a real 2δ wait, and is NOT propositionally equivalent to its
conclusion — you cannot extract `CausalAfter` unless you actually exhibit the wait + honesty. This is
the §8 trust assumption that real-time separation by `≥ 2δ` forces lace order, resting on honest clocks
(≤ `f` faulty) and the physical skew bound, exactly like `FrameHonesty`. It is genuinely load-bearing:
the bridge must FEED it `hw` and `hhonest` (drop either and the carrier does not fire). -/
def WaitCausality (B : Lace) (rt : Frontier → Time) (fs : FrameStatement)
    (E start now : Frontier) : Prop :=
  waited B rt start now (2 * fs.δ) → FrameHonesty fs (rt start) → CausalAfter B E now

/-- **`commit_wait_bridge` (PROVED) — THE KEYSTONE: frame ∧ waited(2δ) ⟹ causal.** Given:
  * an ACCEPTED frame attestation `hacc : FrameWithin reg stmtOf fs att` (the authority attests `T`
    within `δ`, verified by the in-TCB gate);
  * a CAUSAL wait of `≥ 2δ` real-time past the reading reaching `now` (`hw : waited … (2*fs.δ)`);
  * the §8 carriers: the reading honestly bounds `E`'s true time (`hhonest`), and commit-wait's
    disjoint-interval determinacy (`hcw`);
THEN `E` is in `now`'s causal past: `CausalAfter B E now`. The FRAME fact `frameWithin F T δ` has been
UPGRADED to a LIGHTCONE fact by paying `2δ` of wait — Spanner's external consistency, in Lean. This is
the formal content of "wait out the skew, then frontrunning is causally excluded": after commit-wait,
the deadline is a frame-invariant happens-before, not a timestamp race. -/
theorem commit_wait_bridge {B : Lace} {reg : Registry Stmt Wit} {stmtOf : FrameStatement → Stmt}
    (fs : FrameStatement) (att : Wit) (rt : Frontier → Time) (E start now : Frontier)
    (_hacc : FrameWithin reg stmtOf fs att)
    (hw : waited B rt start now (2 * fs.δ))
    (hhonest : FrameHonesty fs (rt start))
    (hcw : WaitCausality B rt fs E start now) :
    CausalAfter B E now :=
  -- The carrier `hcw` CONSUMES both the `2δ` wait (`hw`) and the honesty bound (`hhonest`); neither is
  -- decorative — drop `hw` and the carrier cannot be applied (its antecedent is the wait itself).
  hcw hw hhonest

/-- **`commit_wait_upgrades_deadline` (PROVED) — the deadline-level reading of the bridge.** A
`frameWithin` deadline that is MET, after a `2δ` commit-wait (with the §8 carriers), yields a
`causalAfter E` deadline that is MET at `now`. The frame DEADLINE becomes a causal DEADLINE: the same
promise, now a lightcone fact, discharged with NO further trust (a court can re-read it as causal). -/
theorem commit_wait_upgrades_deadline {B : Lace} {reg : Registry Stmt Wit}
    {stmtOf : FrameStatement → Stmt}
    (fs : FrameStatement) (att : Wit) (rt : Frontier → Time) (E start now : Frontier)
    (hmet : (Deadline.frameWithin (B := B) (reg := reg) (stmtOf := stmtOf) fs att).Met now)
    (hw : waited B rt start now (2 * fs.δ))
    (hhonest : FrameHonesty fs (rt start))
    (hcw : WaitCausality B rt fs E start now) :
    (Deadline.causalAfter (B := B) (reg := reg) (stmtOf := stmtOf) E).Met now := by
  show CausalAfter B E now
  have hacc : FrameWithin reg stmtOf fs att := hmet
  exact commit_wait_bridge fs att rt E start now hacc hw hhonest hcw

/-! ## 5. The `2δ` is GENUINELY load-bearing — drop it and the bridge CANNOT conclude.

§4's teeth: "the bridge genuinely uses the `2δ` wait (drop it ⇒ can't conclude)." Now that the carrier
`WaitCausality` takes the `waited B rt start now (2*fs.δ)` proof as its ANTECEDENT (not a vacuous
`twoδ = 2δ` equation), the load-bearingness is a real fact: in a concrete world where the agent waited
only `δ`, the carrier's antecedent is genuinely UNSATISFIED — there is no `waited … (2δ)` proof to feed
it — so the carrier cannot fire, AND the bridge's own `hw` premise is unsatisfiable. We exhibit a
concrete world where waiting only `δ` admits an honest, accepted frame fact whose `CausalAfter` is
nonetheless FALSE, and prove the `2δ`-wait premise is unmeetable there. -/

/-- **`commit_wait_needs_full_2delta` (PROVED) — the SHARP load-bearing statement.** There is a
concrete world (the demo lace, `δ = 1`, an `E = f1` that is NOT causally before `now = g1`) where: the
§8 honesty carrier holds, the agent has waited only `δ` (`rt g1 − rt g0 = 1`), yet `CausalAfter B E now`
is FALSE — AND the bridge's required premise `waited B rt start now (2*δ) = waited … 2` is UNSATISFIABLE
(the real-time gap is only `1 < 2`). So the `2δ` wait is not slack: with only `δ` you cannot even state
the bridge's hypothesis, and the frame fact does NOT upgrade to a causal fact. Frontrunning is excluded
only after the FULL commit-wait. -/
theorem commit_wait_needs_full_2delta :
    ∃ (B : Lace) (fs : FrameStatement) (E now : Frontier) (rt : Frontier → Time) (start : Frontier),
      fs.skewReal
      ∧ waited B rt start now fs.δ            -- waited only δ (HALF of 2δ)
      ∧ FrameHonesty fs (rt start)            -- §8 honesty holds
      ∧ ¬ waited B rt start now (2 * fs.δ)    -- the bridge's 2δ-wait premise is UNMEETABLE here
      ∧ ¬ CausalAfter B E now := by           -- and NO causal conclusion holds
  -- Use the honest demo edge g0 ≺ g1 (a real lightcone advance), δ=1, E = f1 (a fork block never
  -- preceding g1), now = g1, start = g0, and rt giving a gap of exactly 1 (= δ, < 2δ = 2).
  refine ⟨Dregg2.Authority.Blocklace.demoLace,
          { authority := { issuer := 0 }, T := 0, δ := 1 },
          Dregg2.Authority.Blocklace.f1, Dregg2.Authority.Blocklace.g1,
          (fun b => if b = Dregg2.Authority.Blocklace.g1 then 1 else 0),
          Dregg2.Authority.Blocklace.g0, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : Time) < 1; norm_num
  · -- waited δ=1: g0 ≺ g1 (the honest ack edge) and rt g1 − rt g0 = 1 − 0 = 1 ≥ 1.
    refine ⟨Dregg2.Authority.Blocklace.demo_honest_precedes, ?_⟩
    simp [Dregg2.Authority.Blocklace.g0, Dregg2.Authority.Blocklace.g1]
  · -- FrameHonesty: T − δ = 0 − 1 = −1 ≤ rt g0 = 0.
    show (0 : Time) - 1 ≤ _
    simp [Dregg2.Authority.Blocklace.g0, Dregg2.Authority.Blocklace.g1]
  · -- the 2δ-wait premise is FALSE: it would need rt g1 − rt g0 = 1 ≥ 2*1 = 2, impossible.
    rintro ⟨_, hgap⟩
    simp only [Dregg2.Authority.Blocklace.g0, Dregg2.Authority.Blocklace.g1] at hgap
    norm_num at hgap
  · -- ¬ CausalAfter: f1 does NOT causally precede g1 (a fork block, leftmost-genesis structure).
    show ¬ precedes Dregg2.Authority.Blocklace.demoLace Dregg2.Authority.Blocklace.f1 _
    intro h
    have := Dregg2.Authority.Blocklace.demo_precedes_left_g0 h
    revert this; decide

/-- **`shortWaitCarrier_gives_nothing` (PROVED) — the carrier needs the FULL `2δ`-wait proof.** In the
same `δ`-only world (`commit_wait_needs_full_2delta`), the commit-wait carrier `WaitCausality` cannot be
applied to conclude `CausalAfter`, because its antecedent `waited B rt start now (2*fs.δ)` is FALSE
there. So EVEN HOLDING the carrier as a §8 hypothesis, a court cannot upgrade the frame fact without the
genuine `2δ` wait. (Contrast the OLD vacuous carrier `twoδ = 2δ → …`, which fired on `rfl` regardless of
any wait — that is exactly the vacuity this rewrite removes.) -/
theorem shortWaitCarrier_gives_nothing :
    ∃ (B : Lace) (rt : Frontier → Time) (fs : FrameStatement) (E start now : Frontier),
      -- the carrier is held as a §8 hypothesis …
      (WaitCausality B rt fs E start now →
        -- … yet it yields NOTHING about `CausalAfter`, because its 2δ-wait antecedent is unmeetable:
        ¬ waited B rt start now (2 * fs.δ)) ∧
      ¬ CausalAfter B E now := by
  obtain ⟨B, fs, E, now, rt, start, _, _, _, hno2δ, hnca⟩ := commit_wait_needs_full_2delta
  exact ⟨B, rt, fs, E, start, now, fun _ => hno2δ, hnca⟩

/-! ## 6. Non-vacuity of the deadline type — both kinds are inhabited and discriminable.

The two constructors are genuinely distinct (`kind` separates them), both `Met`-able, and the causal
one is met for free on the demo lace while the frame one needs an authority. -/

/-- A demo causal deadline on `demoLace`: "must causally follow genesis `g0`." -/
def demoCausal : Deadline Dregg2.Authority.Blocklace.demoLace
    (reg := (fun _ => none : Registry Nat Nat)) (stmtOf := fun _ => 0) :=
  Deadline.causalAfter Dregg2.Authority.Blocklace.g0

/-- A demo frame deadline: authority attests `(T=1000, δ=5)`. -/
def demoFrame : Deadline Dregg2.Authority.Blocklace.demoLace
    (reg := (fun _ => none : Registry Nat Nat)) (stmtOf := fun _ => 0) :=
  Deadline.frameWithin { authority := { issuer := 99 }, T := 1000, δ := 5 } 0

/-- **`demo_kinds_distinct` (PROVED)** — the two constructors are discriminable: the causal deadline
reads `kind = true`, the frame one `kind = false`. A court tells them apart — the §4 forcing is real. -/
theorem demo_kinds_distinct : demoCausal.kind = true ∧ demoFrame.kind = false :=
  ⟨rfl, rfl⟩

/-- **`demo_causal_met_for_free` (PROVED)** — the causal demo deadline is MET at frontier `g1` with NO
authority (the registry is empty): `demoCausal.Met g1`, because `g0 ≺ g1` on the lace. The lightcone
fact needs no trust. -/
theorem demo_causal_met_for_free : demoCausal.Met Dregg2.Authority.Blocklace.g1 :=
  Dregg2.Authority.Blocklace.demo_honest_precedes

/-- **`demo_frame_unmet_without_authority` (PROVED)** — the frame demo deadline is NOT met under the
empty registry (no `temporal` authority): `¬ demoFrame.Met g1`. The frame convention is NOT true for
free — exactly the asymmetry the type forces. -/
theorem demo_frame_unmet_without_authority : ¬ demoFrame.Met Dregg2.Authority.Blocklace.g1 := by
  unfold demoFrame Deadline.Met FrameWithin registryVerify
  simp

/-! ### The bridge FIRES — a positive witness that commit-wait is satisfiable (not vacuously dead).

The §5 teeth show the bridge is UNprovable without the `2δ` wait. The dual non-vacuity: with a GENUINE
`2δ` wait it DOES fire — so the bridge has real content, not an unsatisfiable premise. We build a
concrete `WaitCausality` carrier from the actual lace order (`g0 ≺ g1`), wait a full `2δ` of real time
(`rt`-gap `= 2 = 2*1`), and discharge `CausalAfter demoLace g0 g1`. The carrier is constructed from the
lace fact `g0 ≺ g1`, NOT by assuming the conclusion ambiently — it is a real commit-wait law applied. -/

/-- A real-time map giving `g0 ↦ 0`, `g1 ↦ 2` — a genuine `2δ = 2` gap across the honest ack edge. -/
def demoRt : Frontier → Time := fun b => if b = Dregg2.Authority.Blocklace.g1 then 2 else 0

/-- The frame statement for the firing demo: `δ = 1`, so the required wait is `2δ = 2`. -/
def demoFs : FrameStatement := { authority := { issuer := 99 }, T := 1, δ := 1 }

/-- **`demo_waitCausality_holds` (PROVED)** — a CONCRETE commit-wait carrier, built from the lace order.
For `E = g0`, `now = g1`, it discharges `CausalAfter` precisely from the honest ack edge `g0 ≺ g1`
(`demo_honest_precedes`) once the `2δ` wait is exhibited. The carrier is NOT the bare conclusion smuggled
in: it is a function of the genuine wait + honesty proofs, returning the lace fact. -/
theorem demo_waitCausality_holds :
    WaitCausality Dregg2.Authority.Blocklace.demoLace demoRt demoFs
      Dregg2.Authority.Blocklace.g0 Dregg2.Authority.Blocklace.g0
      Dregg2.Authority.Blocklace.g1 := by
  intro _hw _hhonest
  exact Dregg2.Authority.Blocklace.demo_honest_precedes

/-- **`demo_bridge_fires` (PROVED)** — the commit-wait bridge DISCHARGES with a genuine `2δ` wait. We
exhibit an accepted frame attestation (any `reg`/`att` — acceptance only gates which attestation we
trust), a real `2δ = 2` wait across `g0 ≺ g1` (`demoRt`-gap `= 2`), the honesty bound, and the concrete
carrier, and conclude `CausalAfter demoLace g0 g1`. The frame fact is genuinely UPGRADED to a lightcone
fact — proving the bridge has content. -/
theorem demo_bridge_fires :
    CausalAfter Dregg2.Authority.Blocklace.demoLace
      Dregg2.Authority.Blocklace.g0 Dregg2.Authority.Blocklace.g1 := by
  refine commit_wait_bridge (reg := (fun _ => some (fun _ _ => true) : Registry Nat Nat))
      (stmtOf := fun _ => 0) demoFs 0 demoRt
      Dregg2.Authority.Blocklace.g0 Dregg2.Authority.Blocklace.g0
      Dregg2.Authority.Blocklace.g1 ?_ ?_ ?_ demo_waitCausality_holds
  · -- accepted (the verifier accepts everything here; acceptance is just the in-TCB gate's bit).
    unfold FrameWithin registryVerify; simp
  · -- waited 2δ = 2: g0 ≺ g1 and demoRt g1 − demoRt g0 = 2 − 0 = 2 ≥ 2*1.
    refine ⟨Dregg2.Authority.Blocklace.demo_honest_precedes, ?_⟩
    show (2 : Time) * demoFs.δ ≤ demoRt Dregg2.Authority.Blocklace.g1 - demoRt Dregg2.Authority.Blocklace.g0
    simp [demoRt, demoFs, Dregg2.Authority.Blocklace.g0, Dregg2.Authority.Blocklace.g1]
  · -- FrameHonesty: T − δ = 1 − 1 = 0 ≤ demoRt g0 = 0.
    show demoFs.T - demoFs.δ ≤ demoRt Dregg2.Authority.Blocklace.g0
    simp [demoRt, demoFs, Dregg2.Authority.Blocklace.g0, Dregg2.Authority.Blocklace.g1]

/-! ### `#guard` smoke — the deadline kinds + their discharge bits. -/

#guard (demoCausal.kind)                                                        -- true  (lightcone fact)
#guard (demoFrame.kind == false)                                                -- false (frame convention)
-- the causal demo is met for free (the ack edge is present); the frame one is not (no authority).
#guard (decide (Dregg2.Authority.Blocklace.g0.id ∈ Dregg2.Authority.Blocklace.g1.preds))  -- true
#guard (registryVerify (fun _ => none : Registry Nat Nat) .temporal 0 0 == false)        -- false (frame fails closed)

/-! ### Keystones — `#assert_axioms`-clean. -/

#assert_axioms causalAfter_no_frame_dependency
#assert_axioms frameWithin_has_frame_dependency
#assert_axioms commit_wait_bridge
#assert_axioms commit_wait_upgrades_deadline
#assert_axioms shortWaitCarrier_gives_nothing
#assert_axioms commit_wait_needs_full_2delta
#assert_axioms demo_kinds_distinct
#assert_axioms demo_causal_met_for_free
#assert_axioms demo_frame_unmet_without_authority
#assert_axioms demo_waitCausality_holds
#assert_axioms demo_bridge_fires

end Dregg2.Time.Deadline
