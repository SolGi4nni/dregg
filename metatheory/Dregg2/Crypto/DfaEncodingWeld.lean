/-
# Dregg2.Crypto.DfaEncodingWeld — the `Value ↪ ℕ` faithfulness-carrying WELD.

Two verified DFA layers meet in the tree but were never joined by a proof:

  * the **compiler side** (`Crypto/Deriv/TableDfa.lean`) — a `TableDfa` over the RICH carriers
    `State := PredRE`, `Sym := Value`, whose `accepts` is proven faithful to the denotational
    language `Matches R` (`Deriv.PredRE.tableDfa_faithful`: a table that agrees with dregg's
    derivative matcher `derives · R` on every word decides EXACTLY `Matches R`);

  * the **AIR side** (`Crypto/DfaAcceptanceAir.lean`) — a `TableDfa` over `State := ℕ`, `Sym := ℕ`
    (the `BabyBear::new` field ids the real `dregg-dfa-routing-v1` STARK binds via its rolling
    Poseidon2 route commitment). Its `classify` is what the AIR's public `finalState` equals
    (`air_final_state_is_classification`) and what `route_commitment_binds_trace` cryptographically
    pins.

They previously met only INDIVIDUALLY at `Crypto/Dfa.lean`'s `DfaAccepts`. The missing join is a
`Value → ℕ` (and `PredRE`-state → ℕ) encoding that CARRIES `Matches`-faithfulness across the type
gap — the design §"localized gaps" `Value↪ℕ` weld. This file supplies it.

## What is proven (GAP B — the compiler-table ↔ AIR-table gap — genuinely closed)

  * `airOf` — transport a compiler-side `Deriv.TableDfa S Y` THROUGH an encode/decode pair into an
    AIR-side `DfaAcceptanceAir.TableDfa ℕ ℕ`: `step n m := encS (td.step (decS n) (decY m))`,
    `start := encS td.start`, `accepts n := td.accept (decS n)`.
  * `classifyFrom_transport` / `classify_transport` — the AIR-side `classify` of the encoded word
    is the ENCODED compiler-side run: `classify (airOf td …) (w.map encY) = encS (td.runState start w)`.
    (Needs ONLY the decode LEFT-INVERSE `decS ∘ encS = id`, `decY ∘ encY = id` — i.e. injectivity.)
  * `airOf_accepts_word_iff` — hence the AIR-side automaton word-accepts EXACTLY when the compiler-side
    one does. BOTH directions, no residual.
  * **`weld_matches`** (the keystone) — specialised to `S := PredRE`, `Y := Value`: the AIR-side table
    `airOf td …` word-accepts EXACTLY `Matches R`. "The table the AIR certifies decides exactly the
    denotational language."  Chains `tableDfa_faithful`.
  * **`air_finalState_decides_matches`** — the strong form tying the CRYPTO-BOUND AIR (`Satisfies`,
    the full Poseidon2 hash-chain AIR) to `Matches`: any AIR-satisfying trace over `airOf td …` whose
    read symbols are the encoded word `w` has its public `finalState` S accept iff `Matches w R`.
  * `weld_matches_of_injective` / `weld_matches_encV` — the injectivity-driven forms, the second
    with the REAL in-tree proven-injective `encV : Value → ℕ`
    (`Circuit/Poseidon2Binding.lean::Reference.encV`, `encV_injective`) supplied CONCRETELY, so the
    ONLY remaining hypothesis is an injective canonical numbering of the automaton STATES.
  * `decodeV_encV` — the concrete Value-encoding lemma (`decode ∘ encV = id`, from `encV_injective`).

The `Value → ℕ` half is CONCRETE (reuses the tree's proven-injective encoder). The `PredRE`-state
→ ℕ half is left as a supplied injective numbering: its EXISTENCE is underwritten by
`Deriv.der_finite` (the reachable derivative state space is finite up to `≅`, so it admits an
injection into `ℕ`); building it explicitly over the whole `Pred`/`StateConstraint` algebra is a
separate serialization subproject and NOT the mathematical content of the weld (which is
encoding-AGNOSTIC transport). See the closing residual note.

GAP A (`Deriv/Determinize.lean:171` `derivativeCompile_eq_tableDfa`, the literal powerset-table
equality) is a DIFFERENT obligation — a Lean model of `compiler.rs::determinize`'s powerset
construction — and is left NAMED, not touched here.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.TableDfa
import Dregg2.Crypto.DfaAcceptanceAir
import Dregg2.Crypto.Dfa
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Tactics

namespace Dregg2.Crypto.DfaEncodingWeld

open Dregg2.Exec (Value)
open Dregg2.Crypto.Deriv.PredRE (Matches derives)
open Dregg2.Crypto.DfaAcceptanceAir
  (classify classifyFrom classifyFrom_nil classifyFrom_cons Satisfies Row symbols
   air_final_state_is_classification)
open Dregg2.Circuit.Poseidon2Binding.Reference (encV encV_injective)

/-- The compiler-side rich DFA (`Crypto/Deriv/TableDfa.lean`), generic in its carriers. -/
abbrev CDfa (S Y : Type) := Dregg2.Crypto.Deriv.PredRE.TableDfa S Y

/-- The AIR-side field-id DFA (`Crypto/DfaAcceptanceAir.lean`) over `ℕ`/`ℕ`. -/
abbrev ADfa := Dregg2.Crypto.DfaAcceptanceAir.TableDfa Nat Nat

-- `Function.invFun`/`leftInverse_invFun` on `PredRE` needs it nonempty; there is no in-tree
-- `Inhabited PredRE`, so declare it here (the empty-word regex inhabits it).
instance : Nonempty Dregg2.Crypto.Deriv.PredRE := ⟨Dregg2.Crypto.Deriv.PredRE.ε⟩

/-! ## §1 — `airOf`: transport a compiler-side DFA into an AIR-side DFA through an encode/decode pair. -/

/-- **`airOf td encS decS encY decY`** — the AIR-side `TableDfa ℕ ℕ` obtained by relabelling the
compiler-side `td`'s states through `encS`/`decS` and symbols through `encY`/`decY`. The step reads a
state/symbol id, decodes to the rich carriers, takes the genuine `td` transition, and re-encodes the
result; the accept set is `td.accept` on the decoded state. When `decS`/`decY` are left inverses of
`encS`/`encY` this is a faithful relabelling of `td` onto the field ids the AIR binds. -/
def airOf {S Y : Type} (td : CDfa S Y) (encS : S → Nat) (decS : Nat → S)
    (encY : Y → Nat) (decY : Nat → Y) : ADfa where
  step n m := encS (td.step (decS n) (decY m))
  start := encS td.start
  accepts n := td.accept (decS n)

/-! ## §2 — the run/acceptance transport (the encoding lemma at work). -/

/-- **`classifyFrom_transport`** — from any encoded start id `encS q`, the AIR-side `classifyFrom`
over the encoded word equals the ENCODED compiler-side run. The ONLY facts used are the decode
left-inverses `decS (encS ·) = ·` and `decY (encY ·) = ·` (i.e. injectivity of the encodings) — the
faithfulness-carrying content of the `Value↪ℕ` weld. -/
theorem classifyFrom_transport {S Y : Type} (td : CDfa S Y)
    (encS : S → Nat) (decS : Nat → S) (encY : Y → Nat) (decY : Nat → Y)
    (hS : ∀ s, decS (encS s) = s) (hY : ∀ a, decY (encY a) = a) (q : S) (w : List Y) :
    classifyFrom (airOf td encS decS encY decY) (encS q) (w.map encY)
      = encS (td.runState q w) := by
  induction w generalizing q with
  | nil => simp only [List.map_nil, classifyFrom_nil]; rfl
  | cons a as ih =>
    simp only [List.map_cons, classifyFrom_cons]
    have hstep : (airOf td encS decS encY decY).step (encS q) (encY a) = encS (td.step q a) := by
      show encS (td.step (decS (encS q)) (decY (encY a))) = encS (td.step q a)
      rw [hS, hY]
    rw [hstep, ih (td.step q a)]
    rfl

/-- **`classify_transport`** — the AIR-side `classify` (from `start`) of the encoded word is the
encoded compiler-side final state. -/
theorem classify_transport {S Y : Type} (td : CDfa S Y)
    (encS : S → Nat) (decS : Nat → S) (encY : Y → Nat) (decY : Nat → Y)
    (hS : ∀ s, decS (encS s) = s) (hY : ∀ a, decY (encY a) = a) (w : List Y) :
    classify (airOf td encS decS encY decY) (w.map encY)
      = encS (td.runState td.start w) := by
  show classifyFrom (airOf td encS decS encY decY) (encS td.start) (w.map encY) = _
  exact classifyFrom_transport td encS decS encY decY hS hY td.start w

/-- **`airOf_accepts_word_iff`** — the AIR-side automaton word-accepts the encoded word EXACTLY when
the compiler-side automaton accepts the word. Both directions; the sole ingredient is the decode
left-inverse. -/
theorem airOf_accepts_word_iff {S Y : Type} (td : CDfa S Y)
    (encS : S → Nat) (decS : Nat → S) (encY : Y → Nat) (decY : Nat → Y)
    (hS : ∀ s, decS (encS s) = s) (hY : ∀ a, decY (encY a) = a) (w : List Y) :
    (airOf td encS decS encY decY).accepts
        (classify (airOf td encS decS encY decY) (w.map encY))
      ↔ td.accepts w := by
  rw [classify_transport td encS decS encY decY hS hY w]
  show td.accept (decS (encS (td.runState td.start w))) ↔ td.accepts w
  rw [hS]
  exact Iff.rfl

/-! ## §3 — the WELD: the AIR-side table decides exactly `Matches R` (GAP B closed). -/

/-- **`weld_matches` — THE KEYSTONE.** For the rich carriers `PredRE`/`Value`: an AIR-side table
`airOf td …`, obtained by relabelling a compiler-side table `td` that agrees with dregg's derivative
matcher `derives · R`, word-accepts the encoded word EXACTLY when the original `Value`-word matches
`R` denotationally. "The table the AIR certifies decides exactly the denotational language `Matches R`."
The `Value↪ℕ` and `PredRE↪ℕ` encodings (via their decode left-inverses `hS`/`hY`) carry the
`tableDfa_faithful` guarantee across the type gap. -/
theorem weld_matches (td : CDfa Dregg2.Crypto.Deriv.PredRE Value) (R : Dregg2.Crypto.Deriv.PredRE)
    (encS : Dregg2.Crypto.Deriv.PredRE → Nat) (decS : Nat → Dregg2.Crypto.Deriv.PredRE)
    (encY : Value → Nat) (decY : Nat → Value)
    (hS : ∀ s, decS (encS s) = s) (hY : ∀ a, decY (encY a) = a)
    (hfaith : ∀ w, td.accepts w ↔ derives w R = true) (w : List Value) :
    (airOf td encS decS encY decY).accepts
        (classify (airOf td encS decS encY decY) (w.map encY))
      ↔ Matches w R := by
  rw [airOf_accepts_word_iff td encS decS encY decY hS hY w]
  exact Dregg2.Crypto.Deriv.PredRE.tableDfa_faithful td R hfaith w

/-- **`air_finalState_decides_matches` — the strong form to the CRYPTO-BOUND AIR.** Given a genuine
`dregg-dfa-routing-v1` AIR-satisfying trace over the transported table `airOf td …` (the FULL
Poseidon2 hash-chain `Satisfies` predicate) whose read symbol column is the encoded image of a
`Value`-word `w`, the AIR's public `finalState` S — the state `route_commitment_binds_trace`
cryptographically pins — accepts EXACTLY when `Matches w R`. This chains `weld_matches` with
`air_final_state_is_classification` (`finalState = classify (airOf …) (symbols rows)`), so the
soundness pivot the STARK certifies decides the denotational language. -/
theorem air_finalState_decides_matches
    {Dg : Type} [AddCommGroup Dg] [Dregg2.Crypto.CryptoPrimitives Dg]
    (td : CDfa Dregg2.Crypto.Deriv.PredRE Value) (R : Dregg2.Crypto.Deriv.PredRE)
    (encS : Dregg2.Crypto.Deriv.PredRE → Nat) (decS : Nat → Dregg2.Crypto.Deriv.PredRE)
    (encY : Value → Nat) (decY : Nat → Value)
    (hS : ∀ s, decS (encS s) = s) (hY : ∀ a, decY (encY a) = a)
    (hfaith : ∀ w, td.accepts w ↔ derives w R = true)
    (encState encSym : Nat → Dg) (tableCommitment : Dg)
    (initialState finalState : Nat) (routeCommitment : Dg)
    (rows : List (Row Nat Nat Dg))
    (hsat : Satisfies (airOf td encS decS encY decY) encState encSym tableCommitment
              initialState finalState routeCommitment rows)
    (hstart : (airOf td encS decS encY decY).start = initialState)
    (w : List Value) (hsyms : symbols rows = w.map encY) :
    (airOf td encS decS encY decY).accepts finalState ↔ Matches w R := by
  have hcl := air_final_state_is_classification (airOf td encS decS encY decY)
    encState encSym tableCommitment initialState finalState routeCommitment rows hsat hstart
  rw [hcl, hsyms]
  exact weld_matches td R encS decS encY decY hS hY hfaith w

/-! ## §4 — the injectivity-driven forms; the CONCRETE `Value → ℕ` encoding lemma. -/

/-- **`weld_matches_of_injective`** — the weld from bare INJECTIVITY of the encodings (the decode is
the canonical `Function.invFun`, whose left-inverse property is `Function.leftInverse_invFun`). This
is item (1)'s "decode/injectivity property sufficient to transport acceptance." -/
theorem weld_matches_of_injective
    (td : CDfa Dregg2.Crypto.Deriv.PredRE Value) (R : Dregg2.Crypto.Deriv.PredRE)
    (encS : Dregg2.Crypto.Deriv.PredRE → Nat) (encY : Value → Nat)
    (hS : Function.Injective encS) (hY : Function.Injective encY)
    (hfaith : ∀ w, td.accepts w ↔ derives w R = true) (w : List Value) :
    (airOf td encS (Function.invFun encS) encY (Function.invFun encY)).accepts
        (classify (airOf td encS (Function.invFun encS) encY (Function.invFun encY)) (w.map encY))
      ↔ Matches w R :=
  weld_matches td R encS (Function.invFun encS) encY (Function.invFun encY)
    (Function.leftInverse_invFun hS) (Function.leftInverse_invFun hY) hfaith w

/-- **`decodeV`** — the decoder for the REAL in-tree `Value → ℕ` encoder `encV`. -/
noncomputable def decodeV : Nat → Value := Function.invFun encV

/-- **`decodeV_encV` — the concrete `Value` encoding lemma** (`decode ∘ encV = id`), from the tree's
proven `encV_injective`. This is the `Value↪ℕ` half made concrete: it reuses
`Circuit/Poseidon2Binding.lean::Reference.encV`, the system's own provably-injective canonical
`Value` serializer, rather than inventing a new one. -/
theorem decodeV_encV : ∀ v : Value, decodeV (encV v) = v :=
  Function.leftInverse_invFun encV_injective

/-- **`weld_matches_encV` — the headline with the REAL `Value` encoder concrete.** Only an injective
canonical numbering `encS` of the automaton STATES remains hypothetical; the `Value` symbol side is
the tree's `encV`. Given such an `encS`, the AIR-side table (over the genuine field ids) decides
EXACTLY `Matches R`. -/
theorem weld_matches_encV
    (td : CDfa Dregg2.Crypto.Deriv.PredRE Value) (R : Dregg2.Crypto.Deriv.PredRE)
    (encS : Dregg2.Crypto.Deriv.PredRE → Nat) (hS : Function.Injective encS)
    (hfaith : ∀ w, td.accepts w ↔ derives w R = true) (w : List Value) :
    (airOf td encS (Function.invFun encS) encV decodeV).accepts
        (classify (airOf td encS (Function.invFun encS) encV decodeV) (w.map encV))
      ↔ Matches w R :=
  weld_matches_of_injective td R encS encV hS encV_injective hfaith w

/-! ## §5 — axiom hygiene. -/

#assert_all_clean [
  classifyFrom_transport, classify_transport, airOf_accepts_word_iff,
  weld_matches, air_finalState_decides_matches,
  weld_matches_of_injective, decodeV_encV, weld_matches_encV
]

/-! ## §6 — non-vacuity: the transport FIRES on a concrete automaton (reusing the Reference router).

The `dregg-dfa-routing-v1` 4-state router (`DfaAcceptanceAir.Reference.routerStep`) as a COMPILER-side
`CDfa ℕ ℕ`, transported through the IDENTITY encodings (trivially injective, `id ∘ id = id`) into an
AIR-side `ADfa`. We check the transported classification computes the genuine run, discriminates
accept from reject (BOTH polarities), and that `airOf_accepts_word_iff` fires as a real `↔`. This
exercises the transport machinery end-to-end with NO `sorry` and NO abstract carrier. -/

namespace Demo

open Dregg2.Crypto.DfaAcceptanceAir.Reference (routerStep)

/-- The router as a compiler-side table (start `IDLE=0`, accept `LOCAL=1`). -/
def cRouter : CDfa Nat Nat where
  step := routerStep
  start := 0
  accept n := n = 1

/-- Transported to the AIR side through identity encodings (injective; `id ∘ id = id`). -/
def aRouter : ADfa := airOf cRouter id id id id

-- The transported classification IS the genuine router run: `[internal,external,internal]` → LOCAL=1.
example : classify aRouter [0, 1, 0] = 1 := by decide
-- …and the REJECTING input `[unknown,internal,external]` → REJECT=3 (absorbing).
example : classify aRouter [3, 0, 1] = 3 := by decide

-- The transport lemma FIRES concretely (identity encodings): classify = the compiler run.
example : classify aRouter (([0, 1, 0] : List Nat).map id) = id (cRouter.runState 0 [0, 1, 0]) :=
  classify_transport cRouter id id id id (fun _ => rfl) (fun _ => rfl) [0, 1, 0]

-- The word-acceptance `↔` is a genuine, non-vacuous instance of the transport theorem.
example (w : List Nat) :
    aRouter.accepts (classify aRouter (w.map id)) ↔ cRouter.accepts w :=
  airOf_accepts_word_iff cRouter id id id id (fun _ => rfl) (fun _ => rfl) w

-- Non-vacuity in BOTH polarities: the accepting input is accepted…
example : aRouter.accepts (classify aRouter [0, 1, 0]) := by
  show classify aRouter [0, 1, 0] = 1; decide
-- …and the rejecting input is NOT (fail-closed).
example : ¬ aRouter.accepts (classify aRouter [3, 0, 1]) := by
  show ¬ classify aRouter [3, 0, 1] = 1; decide

/-- The real `Value → ℕ` encoder distinguishes distinct `sym` leaves (non-vacuous injectivity). -/
example : encV (.sym 7) ≠ encV (.sym 9) := by decide

/-- The concrete `Value` encoding lemma round-trips a concrete value. -/
example : decodeV (encV (.sym 7)) = .sym 7 := decodeV_encV (.sym 7)

end Demo

/-!
## Residual — the two named seams (NOT closed here; neither blocks the weld).

1. **The concrete `PredRE`-state → ℕ numbering.** `weld_matches_encV` supplies the `Value` side with
   the tree's proven-injective `encV` and leaves ONE hypothesis: an injective `encS : PredRE → ℕ`.
   Its EXISTENCE is underwritten by `Deriv.der_finite` — the reachable derivative state space is
   finite up to `≅`, and a finite carrier injects into `ℕ`. Building `encS` EXPLICITLY means
   serialising the whole `Pred`/`StateConstraint` algebra (which nests through `List Pred`,
   `ClearanceGraph`, `SimpleConstraint`, …) injectively — a self-contained serialization subproject,
   the exact twin of `Poseidon2Binding.Reference.encV`'s hand construction for `Value`, and NOT the
   mathematical content of the weld (the transport in §2–§3 is encoding-AGNOSTIC: it consumes ONLY
   injectivity). The weld is therefore genuinely closed MODULO a supplied injective canonical
   numbering, with the `Value` half fully concrete.

2. **GAP A — `Deriv/Determinize.lean:171` `derivativeCompile_eq_tableDfa`.** The literal equality of
   the derivative automaton's table with `compiler.rs::determinize`'s POWERSET table is a DIFFERENT
   obligation: it needs a Lean model of the powerset construction, then a language/bisim equivalence.
   The table-opaque AIR only ever needs LANGUAGE agreement (which `tableDfa_faithful` + this weld
   already deliver), so gap A is not on the critical path for "the AIR-certified table decides
   `Matches`"; it is left NAMED, exactly as `Determinize.lean`'s closing note leaves it.
-/

end Dregg2.Crypto.DfaEncodingWeld
