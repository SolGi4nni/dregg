/-
# Dregg2.Crypto.InjectionGuardCircuit — the zkOracle INJECTION guard, as a witnessed circuit.

**This is Lean-authored AIR.** The descriptor is an `EffectVmDescriptor2` produced by
`DfaRoutingTableEmit.tableRoutingDesc`; the witness is a concrete `VmTrace`; satisfaction is a
theorem over the EMITTED object. Nothing is hand-written in Rust.

`GuardToAutomatonCircuit.lean` closed `PredRE guard ▸ table DFA ▸ Satisfied2Public witness` at
`noDoubleBraceRE` — the LEAN guarded-templater's brace-ban over `Exec.Value` — and its own header
names the gap: the guard that runs in the shipped services is

    zkoracle-prove/src/injection.rs:47
      pub fn injection_free(field: &[u8]) -> bool = injection_template().not().matches(field)

a DIFFERENT object over a DIFFERENT alphabet. This file instantiates the same pipeline at the
zkOracle guard, and reports what that reaches and what it does not.

## ⚠⚠ SCOPE — THREE OBJECTS, NOT ONE. Read this before citing anything below.

  * **(S) the SHIPPED predicate** — `injection_free : &[u8] → bool`, over BYTES, built from
    `dregg_dfa::Re` (`dfa/src/derivative.rs`): its own Rust `enum Re`, its own `derive`/`nullable`/
    `matches`. It is a **RE-IMPLEMENTATION**, not a call into Lean — there is no `@[export]`, no
    FFI, no linkage to any Lean artifact anywhere on that path. By this tree's standing law
    (`project-lean-must-be-the-implementation`), NOTHING below is a proof about (S). The shipped
    node does not invoke the Lean, so "closed" is unavailable and is not claimed.
  * **(M) the LEAN MIRROR** — `ZkOracle.injectionTemplate`, over `Value` frames
    `⟨"c" ↦ sym code⟩`, with the handlebars delimiter as **ONE reserved token** `handlebarsOpen =
    123`. §1 instantiates the pipeline here. This is the object `zkOracle_sound`'s third leg
    actually quantifies over.
  * **(B) the BYTE-SHAPED model** — §2's `injBytesRE`: the same `neg (.* ⟨d⟩ .*)` shape but with
    the delimiter spelled as the **TWO-symbol sequence** `{ {`, which is the shape
    `Re::word(b"{{")` builds. §2 instantiates the pipeline here too.

⚑ **(M) AND (B) ARE NOT THE SAME LANGUAGE, and the disagreement is exhibited** (§3). ASCII `{` is
code 123, so under the obvious byte↦code reading (M) treats a SINGLE `{` as the delimiter and
REJECTS it, while (B) — and the shipped (S), whose own test file asserts
`assert!(injection_free(b"a { b"))` — ACCEPTS it. `mirror_and_bytes_disagree` is that divergence as
a theorem. So the Lean mirror is not merely "(S) at another alphabet": transporting it verbatim
would OVER-REJECT benign fields. (B) is the faithful shape, and its poles are §2's.

Relating (B) to (S) can only be a DIFFERENTIAL: same verdicts on the vectors `injection.rs`'s own
tests assert. §2 fires exactly those vectors. A differential is not a refinement and is not called
one here.

## ⚑ THE MEASURED FINDING — the byte alphabet does NOT blow the cover up

The lane hypothesis to test was "256 symbols vs 3 frames may make the automaton large". It does
not, and the reason is structural: the minterm cover is enumerated over the guard's **LEAF
SIGNATURES**, not over the raw symbol set (`SymbolicMinterms.coverOfAtoms`, sound by
`der_factors_over`). The shipped template mentions exactly ONE nontrivial leaf class — "this symbol
is `{`" — so its cover is **2 frames** (`{}` and `{c ↦ sym 123}`), and the two-symbol spelling's is
**3** (one duplicate pin, harmless). Measured numbers in §4. A 256-way alphabet would only appear
if the guard's leaves distinguished 256 classes.

## Axiom hygiene

`#assert_all_clean` on every theorem; `sorry`-free. Every `#guard` is COMPILED EVALUATION of a
closed `Bool` — it proves NO `Prop`; the `Prop`-level content is the theorems.
-/
import Dregg2.Crypto.GuardToAutomatonCircuit
import Dregg2.Crypto.ZkOracle

namespace Dregg2.Crypto.InjectionGuardCircuit

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra (Pred)
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE (der null derives derList rigidRE)
open Dregg2.Crypto.ZkOracle (frame matchCode handlebarsOpen injectionTemplate InjectionFree)
open Dregg2.Crypto.GuardToAutomatonCircuit (GuardAut)
open Dregg2.Crypto.GuardToAutomatonCircuit.GuardAut (enc)
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DfaRoutingTableEmit (SYMBOL PI_FINAL tableRoutingDesc hash0)
open Dregg2.Circuit.Emit.TinyAutomataCompose (runTable costOf jsonBytes)
open Dregg2.Circuit.Emit.TinyAutomataSatisfiable (runWit runWit_satisfies runRows_symbols)

set_option autoImplicit false

/-! ## §0 — Words. A field is a list of symbol codes; a frame carries one code.

`ZkOracle.frame` is the encoding the Lean mirror already uses (`⟨"c" ↦ sym code⟩`); reading a byte
`b : Nat` as `frame b` is the byte↦frame reading, and it is the ONLY reading under which (M) and
(S) could be compared at all. `word` names it so the poles below can be written as the byte
sequences `injection.rs`'s tests use. -/

/-- A field, as the frame word its codes spell. -/
def word (codes : List Nat) : List Value := codes.map frame

/-! ## §1 — (M) the LEAN MIRROR `neg injectionTemplate`, determinised and witnessed. -/

section Mirror

/-- **(M) the guard** — the ACCEPTANCE predicate of the zkOracle injection leg: the field UNMATCHES
the injection template. `InjectionFree field` is literally `derives field mirrorRE = true`. -/
def mirrorRE : PredRE := .neg injectionTemplate

theorem mirrorRE_is_injectionFree (field : List Value) :
    InjectionFree field ↔ derives field mirrorRE = true := Iff.rfl

/-- The mirror's pin set, computed: ONE pin, "the symbol field reads `{`". -/
theorem mirror_atoms :
    atomsOfLeaves? (leavesOf mirrorRE) = some [("c", AtomVal.sym 123)] := rfl

/-- The cover — enumerated, not hard-coded: `{}` and `⟨c ↦ sym 123⟩`. TWO frames for an alphabet
of every `Value` there is. -/
def mirrorCover : MintermCover (leavesOf mirrorRE) := coverOfSymbolic mirror_atoms

/-- The `≅`-fixpoint SATURATES at fuel 64 — kernel-checked (this `rfl` is the worklist running). -/
theorem mirrorFix_isSome :
    (reachFixAux mirrorCover.cands 64 [] [mirrorRE]).isSome = true := rfl

/-- The saturated frontier — the DFA's state list. -/
def mirrorSeen : List PredRE :=
  (reachFixAux mirrorCover.cands 64 [] [mirrorRE]).get mirrorFix_isSome

theorem mirrorFix : reachFixAux mirrorCover.cands 64 [] [mirrorRE] = some mirrorSeen :=
  (Option.some_get mirrorFix_isSome).symm

/-- ⚑ **(M), determinised.** -/
def mirrorAut : GuardAut mirrorCover :=
  GuardAut.ofFix mirrorCover mirrorRE 64 mirrorSeen (symbolicOver_leavesOf _) rfl mirrorFix

/-- (M)'s DFA. -/
def mirrorDfa : TableDfa Nat Nat := mirrorAut.guardDfa

/-- ⚑ **CORRECTNESS AT (M)**: for EVERY `Value` word, the emitted automaton's verdict IS
`InjectionFree`'s verdict. -/
theorem mirrorDfa_decides (w : List Value) :
    mirrorDfa.accepts (classifyFrom mirrorDfa mirrorDfa.start (w.map (enc mirrorCover)))
      ↔ InjectionFree w :=
  mirrorAut.guardDfa_decides w

/-! ### §1a — the poles, on the mirror's own demo fields. -/

/-- `"hi"` — `ZkOracle.Demo.benignField`. -/
def mirrorBenign : List Value := word [104, 105]
/-- `"{{x"` under the ONE-TOKEN reading — `ZkOracle.Demo.maliciousField`. -/
def mirrorMalicious : List Value := word [123, 120]

theorem mirrorBenign_eq : mirrorBenign = Dregg2.Crypto.ZkOracle.Demo.benignField := rfl
theorem mirrorMalicious_eq : mirrorMalicious = Dregg2.Crypto.ZkOracle.Demo.maliciousField := rfl

/-- The encoded (minterm-index) words the circuit actually reads. -/
def mirrorBenignSyms : List Nat := mirrorBenign.map (enc mirrorCover)
/-- …and the injecting one. -/
def mirrorMaliciousSyms : List Nat := mirrorMalicious.map (enc mirrorCover)

theorem mirrorBenignSyms_ne : mirrorBenignSyms ≠ [] := by
  intro h; exact List.cons_ne_nil _ _ h

theorem mirrorMaliciousSyms_ne : mirrorMaliciousSyms ≠ [] := by
  intro h; exact List.cons_ne_nil _ _ h

/-- ⚑ POLE 1 — the emitted automaton ACCEPTS the benign field, because
`ZkOracle.Demo.benign_injection_free` says the guard does. -/
theorem mirrorDfa_accepts_benign :
    mirrorDfa.accepts (classifyFrom mirrorDfa mirrorDfa.start mirrorBenignSyms) :=
  (mirrorDfa_decides mirrorBenign).mpr Dregg2.Crypto.ZkOracle.Demo.benign_injection_free

/-- ⚑ POLE 2 — the emitted automaton REJECTS the injecting field, because
`ZkOracle.Demo.malicious_not_injection_free` says the guard does. -/
theorem mirrorDfa_rejects_malicious :
    ¬ mirrorDfa.accepts (classifyFrom mirrorDfa mirrorDfa.start mirrorMaliciousSyms) :=
  fun h => Dregg2.Crypto.ZkOracle.Demo.malicious_not_injection_free ((mirrorDfa_decides mirrorMalicious).mp h)

/-! ### §1b — ⚑ THE GATE: a `Satisfied2Public` trace for (M)'s circuit. -/

/-- The emitted descriptor's name. -/
def MIRROR_NAME : String := "zkoracle-injection-free-mirror-run::exact-public-v1"

/-- **The emitted descriptor**: the run-table routing descriptor of (M)'s DFA on the index word. -/
def mirrorRunDesc (ys : List Nat) : EffectVmDescriptor2 :=
  tableRoutingDesc MIRROR_NAME (runTable mirrorDfa mirrorDfa.start ys)

/-- **The witness trace**. -/
def mirrorRunWit (ys : List Nat) : VmTrace := runWit mirrorDfa mirrorDfa.start ys

/-- ⚑ **THE GATE FIRES at (M)** — a real `Satisfied2Public` witness, at any non-empty index word. -/
theorem mirrorRunWit_satisfies (ys : List Nat) (hys : ys ≠ []) :
    Satisfied2Public hash0 (mirrorRunDesc ys) (fun _ => 0) (fun _ => (0, 0)) [] (mirrorRunWit ys) :=
  runWit_satisfies mirrorDfa mirrorDfa.start ys hys MIRROR_NAME

/-- The witness's public `final_state` IS the classification, and the symbol column IS the word. -/
theorem mirrorRunWit_public (ys : List Nat) :
    (mirrorRunWit ys).pub PI_FINAL = Int.ofNat (classifyFrom mirrorDfa mirrorDfa.start ys)
      ∧ (mirrorRunWit ys).rows.map (fun a => (a SYMBOL).toNat) = ys :=
  ⟨rfl, runRows_symbols mirrorDfa ys mirrorDfa.start⟩

/-- ⚑⚑ **THE PIPELINE, CLOSED AT (M).** For an arbitrary field: the emitted descriptor HAS a
satisfying trace, that trace reads exactly the field's minterm encoding, its public `final_state`
is the state reached, and that state is accepting EXACTLY when the field is `InjectionFree`. -/
theorem mirror_pipeline (w : List Value) (hw : w.map (enc mirrorCover) ≠ []) :
    Satisfied2Public hash0 (mirrorRunDesc (w.map (enc mirrorCover))) (fun _ => 0)
        (fun _ => (0, 0)) [] (mirrorRunWit (w.map (enc mirrorCover)))
      ∧ (mirrorRunWit (w.map (enc mirrorCover))).rows.map (fun a => (a SYMBOL).toNat)
          = w.map (enc mirrorCover)
      ∧ (mirrorRunWit (w.map (enc mirrorCover))).pub PI_FINAL
          = Int.ofNat (classifyFrom mirrorDfa mirrorDfa.start (w.map (enc mirrorCover)))
      ∧ (mirrorDfa.accepts (classifyFrom mirrorDfa mirrorDfa.start (w.map (enc mirrorCover)))
          ↔ InjectionFree w) :=
  ⟨mirrorRunWit_satisfies _ hw, (mirrorRunWit_public _).2, (mirrorRunWit_public _).1,
   mirrorDfa_decides w⟩

/-- BOTH POLES, each carrying its circuit: the injecting field's descriptor is satisfiable and its
verdict is REJECT; the benign field's is satisfiable and its verdict is ACCEPT. -/
theorem mirror_both_poles :
    (Satisfied2Public hash0 (mirrorRunDesc mirrorMaliciousSyms) (fun _ => 0) (fun _ => (0, 0)) []
        (mirrorRunWit mirrorMaliciousSyms)
      ∧ ¬ mirrorDfa.accepts (classifyFrom mirrorDfa mirrorDfa.start mirrorMaliciousSyms))
    ∧ (Satisfied2Public hash0 (mirrorRunDesc mirrorBenignSyms) (fun _ => 0) (fun _ => (0, 0)) []
        (mirrorRunWit mirrorBenignSyms)
      ∧ mirrorDfa.accepts (classifyFrom mirrorDfa mirrorDfa.start mirrorBenignSyms)) :=
  ⟨⟨mirrorRunWit_satisfies _ mirrorMaliciousSyms_ne, mirrorDfa_rejects_malicious⟩,
   ⟨mirrorRunWit_satisfies _ mirrorBenignSyms_ne, mirrorDfa_accepts_benign⟩⟩

end Mirror

/-! ## §2 — (B) the BYTE-SHAPED guard: the delimiter as the TWO-symbol sequence `{ {`.

This is the shape `injection_template()` builds — `Re::any_byte().star().then(Re::word(b"{{"))
.then(Re::any_byte().star())`, where `Re::word` folds the literal into a CONCATENATION of
single-byte matchers. Spelling it that way in Lean is the only version whose language can agree
with the shipped one (§3 shows the one-token spelling's cannot). -/

section Bytes

/-- The injection template at the byte spelling: `.* ⟨{⟩ ⟨{⟩ .*`. -/
def injTemplateBytes : PredRE :=
  .cat (.star (.sym .tt))
    (.cat (.sym (matchCode handlebarsOpen))
      (.cat (.sym (matchCode handlebarsOpen)) (.star (.sym .tt))))

/-- **(B) the guard** — the field UNMATCHES the byte-spelled template. The Lean shape of
`injection_template().not()`. -/
def injBytesRE : PredRE := .neg injTemplateBytes

/-- **`InjectionFreeBytes`** — the acceptance predicate at the byte spelling. -/
def InjectionFreeBytes (field : List Value) : Prop := derives field injBytesRE = true

/-- (B)'s pin set: the SAME single pin, mentioned twice (one per literal byte). -/
theorem bytes_atoms :
    atomsOfLeaves? (leavesOf injBytesRE)
      = some [("c", AtomVal.sym 123), ("c", AtomVal.sym 123)] := rfl

/-- ⚑ The cover of the SHIPPED-SHAPE guard: **3 frames**, over a 256-byte alphabet. The cover is
enumerated per LEAF SIGNATURE, so the alphabet size never enters. -/
def bytesCover : MintermCover (leavesOf injBytesRE) := coverOfSymbolic bytes_atoms

theorem bytesFix_isSome :
    (reachFixAux bytesCover.cands 64 [] [injBytesRE]).isSome = true := rfl

def bytesSeen : List PredRE :=
  (reachFixAux bytesCover.cands 64 [] [injBytesRE]).get bytesFix_isSome

theorem bytesFix : reachFixAux bytesCover.cands 64 [] [injBytesRE] = some bytesSeen :=
  (Option.some_get bytesFix_isSome).symm

/-- ⚑ **(B), determinised.** -/
def bytesAut : GuardAut bytesCover :=
  GuardAut.ofFix bytesCover injBytesRE 64 bytesSeen (symbolicOver_leavesOf _) rfl bytesFix

/-- (B)'s DFA. -/
def bytesDfa : TableDfa Nat Nat := bytesAut.guardDfa

/-- ⚑ **CORRECTNESS AT (B)**: for EVERY field word, the emitted automaton's verdict IS the
byte-spelled guard's verdict. -/
theorem bytesDfa_decides (w : List Value) :
    bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start (w.map (enc bytesCover)))
      ↔ InjectionFreeBytes w :=
  bytesAut.guardDfa_decides w

/-! ### §2a — the poles, on `injection.rs`'s OWN test vectors.

Each field below is a byte sequence copied from `zkoracle-prove/src/injection.rs`'s `#[test]`s,
read through `word`. Where that file asserts `injection_free(v)` we prove the emitted automaton
ACCEPTS; where it asserts `!injection_free(v)` we prove it REJECTS. This is a DIFFERENTIAL
agreement on those vectors, not a proof about the Rust function. -/

/-- `b"hi"`. -/
def fieldHi : List Value := word [104, 105]
/-- `b"a { b"` — a LONE brace; `injection.rs` asserts this is injection-free. -/
def fieldLoneBrace : List Value := word [97, 32, 123, 32, 98]
/-- `b"{{x"` — THE injection vector. -/
def fieldInject : List Value := word [123, 123, 120]
/-- `b"{{"`. -/
def fieldBareDelim : List Value := word [123, 123]
/-- `b"x {{"` — a trailing delimiter (the `b"trailing {{"` shape). -/
def fieldTrailing : List Value := word [120, 32, 123, 123]

/-- The encoded words the circuit reads. -/
def hiSyms : List Nat := fieldHi.map (enc bytesCover)
/-- …lone brace. -/
def loneSyms : List Nat := fieldLoneBrace.map (enc bytesCover)
/-- …the injection. -/
def injectSyms : List Nat := fieldInject.map (enc bytesCover)
/-- …the bare delimiter. -/
def bareSyms : List Nat := fieldBareDelim.map (enc bytesCover)
/-- …the trailing delimiter. -/
def trailingSyms : List Nat := fieldTrailing.map (enc bytesCover)

theorem hiSyms_ne : hiSyms ≠ [] := by intro h; exact List.cons_ne_nil _ _ h
theorem loneSyms_ne : loneSyms ≠ [] := by intro h; exact List.cons_ne_nil _ _ h
theorem injectSyms_ne : injectSyms ≠ [] := by intro h; exact List.cons_ne_nil _ _ h
theorem bareSyms_ne : bareSyms ≠ [] := by intro h; exact List.cons_ne_nil _ _ h
theorem trailingSyms_ne : trailingSyms ≠ [] := by intro h; exact List.cons_ne_nil _ _ h

/-- The guard's verdicts on the five vectors, decided (`derives`, kernel-evaluated). -/
theorem hi_free : InjectionFreeBytes fieldHi := rfl
theorem lone_free : InjectionFreeBytes fieldLoneBrace := rfl
theorem inject_not_free : ¬ InjectionFreeBytes fieldInject := by
  intro h; exact Bool.noConfusion h
theorem bare_not_free : ¬ InjectionFreeBytes fieldBareDelim := by
  intro h; exact Bool.noConfusion h
theorem trailing_not_free : ¬ InjectionFreeBytes fieldTrailing := by
  intro h; exact Bool.noConfusion h

/-- ⚑ POLE 1 — the emitted automaton ACCEPTS the benign fields, INCLUDING the lone-brace one the
one-token mirror gets wrong. -/
theorem bytesDfa_accepts_benign :
    bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start hiSyms)
      ∧ bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start loneSyms) :=
  ⟨(bytesDfa_decides fieldHi).mpr hi_free, (bytesDfa_decides fieldLoneBrace).mpr lone_free⟩

/-- ⚑ POLE 2 — the emitted automaton REJECTS every injecting field. -/
theorem bytesDfa_rejects_injecting :
    ¬ bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start injectSyms)
      ∧ ¬ bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start bareSyms)
      ∧ ¬ bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start trailingSyms) :=
  ⟨fun h => inject_not_free ((bytesDfa_decides fieldInject).mp h),
   fun h => bare_not_free ((bytesDfa_decides fieldBareDelim).mp h),
   fun h => trailing_not_free ((bytesDfa_decides fieldTrailing).mp h)⟩

/-! ### §2b — ⚑ THE GATE: a `Satisfied2Public` trace for (B)'s circuit. -/

/-- The emitted descriptor's name. -/
def BYTES_NAME : String := "zkoracle-injection-free-bytes-run::exact-public-v1"

/-- **The emitted descriptor** for the byte-shaped guard. -/
def bytesRunDesc (ys : List Nat) : EffectVmDescriptor2 :=
  tableRoutingDesc BYTES_NAME (runTable bytesDfa bytesDfa.start ys)

/-- **The witness trace**. -/
def bytesRunWit (ys : List Nat) : VmTrace := runWit bytesDfa bytesDfa.start ys

/-- ⚑ **THE GATE FIRES at (B)** — a real `Satisfied2Public` witness for the byte-shaped zkOracle
injection guard's circuit, at any non-empty index word. -/
theorem bytesRunWit_satisfies (ys : List Nat) (hys : ys ≠ []) :
    Satisfied2Public hash0 (bytesRunDesc ys) (fun _ => 0) (fun _ => (0, 0)) [] (bytesRunWit ys) :=
  runWit_satisfies bytesDfa bytesDfa.start ys hys BYTES_NAME

theorem bytesRunWit_public (ys : List Nat) :
    (bytesRunWit ys).pub PI_FINAL = Int.ofNat (classifyFrom bytesDfa bytesDfa.start ys)
      ∧ (bytesRunWit ys).rows.map (fun a => (a SYMBOL).toNat) = ys :=
  ⟨rfl, runRows_symbols bytesDfa ys bytesDfa.start⟩

/-- ⚑⚑ **THE PIPELINE, CLOSED AT (B).** For an arbitrary field word: the descriptor has a
satisfying trace, the trace reads the field's encoding, its public output is the reached state, and
that state accepts EXACTLY when the byte-spelled injection guard accepts the field. -/
theorem bytes_pipeline (w : List Value) (hw : w.map (enc bytesCover) ≠ []) :
    Satisfied2Public hash0 (bytesRunDesc (w.map (enc bytesCover))) (fun _ => 0)
        (fun _ => (0, 0)) [] (bytesRunWit (w.map (enc bytesCover)))
      ∧ (bytesRunWit (w.map (enc bytesCover))).rows.map (fun a => (a SYMBOL).toNat)
          = w.map (enc bytesCover)
      ∧ (bytesRunWit (w.map (enc bytesCover))).pub PI_FINAL
          = Int.ofNat (classifyFrom bytesDfa bytesDfa.start (w.map (enc bytesCover)))
      ∧ (bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start (w.map (enc bytesCover)))
          ↔ InjectionFreeBytes w) :=
  ⟨bytesRunWit_satisfies _ hw, (bytesRunWit_public _).2, (bytesRunWit_public _).1,
   bytesDfa_decides w⟩

/-- ⚑⚑ **BOTH POLES, EACH CARRYING ITS CIRCUIT** — the deliverable's gate at the byte spelling.
The injecting field `{{x` has a satisfiable descriptor whose verdict is REJECT; the benign field
`hi` has one whose verdict is ACCEPT; and so does the lone-brace field `a { b`, which is the vector
the one-token mirror gets WRONG. -/
theorem bytes_both_poles :
    (Satisfied2Public hash0 (bytesRunDesc injectSyms) (fun _ => 0) (fun _ => (0, 0)) []
        (bytesRunWit injectSyms)
      ∧ ¬ bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start injectSyms))
    ∧ (Satisfied2Public hash0 (bytesRunDesc hiSyms) (fun _ => 0) (fun _ => (0, 0)) []
        (bytesRunWit hiSyms)
      ∧ bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start hiSyms))
    ∧ (Satisfied2Public hash0 (bytesRunDesc loneSyms) (fun _ => 0) (fun _ => (0, 0)) []
        (bytesRunWit loneSyms)
      ∧ bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start loneSyms)) :=
  ⟨⟨bytesRunWit_satisfies _ injectSyms_ne, bytesDfa_rejects_injecting.1⟩,
   ⟨bytesRunWit_satisfies _ hiSyms_ne, bytesDfa_accepts_benign.1⟩,
   ⟨bytesRunWit_satisfies _ loneSyms_ne, bytesDfa_accepts_benign.2⟩⟩

/-! ### §2c — THE DIFFERENTIAL, RUN. ⚠ This is NOT a proof and NOT a refinement.

The five vectors above were also run through the SHIPPED predicate itself — the UNMODIFIED
`dfa/src/derivative.rs` and `zkoracle-prove/src/injection.rs`, compiled directly by `rustc` (the
only stub is the three unused `crate::compiler` items `derivative.rs` imports: `StateId`,
`DEAD_STATE`, `Dfa`; none is on the `injection_free` path). Measured verdicts:

    injection_free(b"hi")                                    = true
    injection_free(b"")                                      = true
    injection_free(b"please summarize this document")        = true
    injection_free(b"a { b")                                 = true
    injection_free(b"json: { \"k\": 1 }")                    = true
    injection_free(b"{{x")                                   = false
    injection_free(b"{{")                                    = false
    injection_free(b"ignore previous instructions {{system}}")= false
    injection_free(b"trailing {{")                           = false
    injection_free(b"{{ leading")                            = false
    injection_free(b"x {{")                                  = false

Every vector §2a models agrees with (B)'s emitted-automaton verdict, and `b"a { b"` is where (M)
DISAGREES (§3). Eleven agreeing vectors say nothing about the other `2^(8n)` fields: a Rust
case-test proves NOTHING about all inputs, and this file never calls the agreement a refinement.
(`cargo test -p dregg-zkoracle-prove --lib injection` could not be run — the workspace build
directory lock was held by a co-tenant for the whole window; the direct `rustc` compile of the same
two source files is what was measured instead.) -/

end Bytes

/-! ## §3 — ⚑⚑ THE DIVERGENCE: (M) IS NOT (S) TRANSPORTED.

The mirror models `{{` as ONE reserved token with code 123. ASCII `{` IS code 123. So under the
byte↦code reading — the only reading under which the mirror could be about bytes at all — the
mirror treats a SINGLE `{` as the delimiter. `injection.rs` asserts the opposite:

    assert!(injection_free(b"a { b"));   // benign_field_is_injection_free

so on THAT vector the mirror and the shipped predicate disagree. The theorem below is that
disagreement between (M) and (B), both sides kernel-decided. -/

/-- ⚑⚑ **THE MIRROR OVER-REJECTS.** The field `a { b` — which `injection.rs` asserts is
injection-free, and which (B)'s circuit ACCEPTS — is NOT `InjectionFree` under the one-token Lean
mirror. The two guards are different languages, and the difference is a benign field being
refused. -/
theorem mirror_and_bytes_disagree :
    InjectionFreeBytes fieldLoneBrace ∧ ¬ InjectionFree fieldLoneBrace :=
  ⟨lone_free, by intro h; exact Bool.noConfusion h⟩

/-- The same divergence read off the two EMITTED CIRCUITS rather than the guards: (B)'s automaton
accepts the lone-brace field, (M)'s rejects it. Both verdicts are the verdicts of descriptors this
file has proved satisfiable. -/
theorem circuits_disagree_on_lone_brace :
    bytesDfa.accepts (classifyFrom bytesDfa bytesDfa.start loneSyms)
      ∧ ¬ mirrorDfa.accepts
          (classifyFrom mirrorDfa mirrorDfa.start (fieldLoneBrace.map (enc mirrorCover))) :=
  ⟨bytesDfa_accepts_benign.2,
   fun h => mirror_and_bytes_disagree.2 ((mirrorDfa_decides fieldLoneBrace).mp h)⟩

/-! ## §4 — MEASUREMENT.

⚠ Every `#guard` below is COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`. Each one
measures a descriptor that a `Satisfied2Public` theorem above has ALREADY proved satisfiable, so
the standing gate ("never quote a cost without a `Satisfied2Public` witness") is met: the witnessed
objects are `mirrorRunDesc`/`bytesRunDesc` at the index words named here. -/

-- ⚑ THE ALPHABET ANSWER. The mirror's cover is 2 frames; the BYTE-SPELLED guard's is 3 — not 256.
-- The cover is enumerated per leaf signature, and both guards mention ONE nontrivial leaf class.
#guard mirrorCover.cands.length == 2
#guard bytesCover.cands.length == 3

-- The determinised state counts. The second symbol of the literal costs a state class.
#guard mirrorAut.states.length == 6
#guard bytesAut.states.length == 11

-- The encodings actually discriminate: `{` (index 1) is a different minterm from any other byte
-- (index 0), so the abstraction is not collapsing the alphabet to a point.
#guard mirrorBenignSyms == [0, 0]
#guard mirrorMaliciousSyms == [1, 0]
#guard hiSyms == [0, 0]
#guard loneSyms == [0, 0, 1, 0, 0]
#guard injectSyms == [1, 1, 0]
#guard bareSyms == [1, 1]
#guard trailingSyms == [0, 0, 1, 1]

-- The reached states and verdicts (the `Prop`s are §1a/§2a's theorems).
#guard null (mirrorAut.stateAt (classifyFrom mirrorDfa mirrorDfa.start mirrorBenignSyms)) == true
#guard null (mirrorAut.stateAt (classifyFrom mirrorDfa mirrorDfa.start mirrorMaliciousSyms)) == false
#guard null (bytesAut.stateAt (classifyFrom bytesDfa bytesDfa.start hiSyms)) == true
#guard null (bytesAut.stateAt (classifyFrom bytesDfa bytesDfa.start loneSyms)) == true
#guard null (bytesAut.stateAt (classifyFrom bytesDfa bytesDfa.start injectSyms)) == false
#guard null (bytesAut.stateAt (classifyFrom bytesDfa bytesDfa.start bareSyms)) == false
#guard null (bytesAut.stateAt (classifyFrom bytesDfa bytesDfa.start trailingSyms)) == false

-- ⚑ THE WITNESSED COST of the byte-shaped zkOracle guard's circuit at |field| = 3 bytes: 3 columns,
-- 4 constraints, 2 PIs, ONE table of 3 rows, 3 forced trace rows, ZERO nonlinear multiplications.
#guard costOf (bytesRunDesc injectSyms) ==
  { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
  , declaredRows := 3, forcedTraceRows := .pinned 3, nonlinearMults := 0 }
#guard (costOf (bytesRunDesc injectSyms)).area == some 9
#guard jsonBytes (bytesRunDesc injectSyms) == 613

-- …and at |field| = 5 bytes, the ONLY axis that moves is the table height (and 16 wire bytes,
-- 8 per extra row): the circuit is O(1) in width/constraints/PIs and LINEAR in field length.
#guard costOf (bytesRunDesc loneSyms) ==
  { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
  , declaredRows := 5, forcedTraceRows := .pinned 5, nonlinearMults := 0 }
#guard (costOf (bytesRunDesc loneSyms)).area == some 15
#guard jsonBytes (bytesRunDesc loneSyms) == 629

-- The mirror's circuit, for comparison — identical shape, so the one-token/two-byte spelling
-- difference costs NOTHING in circuit area (it only moved a state class).
#guard costOf (mirrorRunDesc mirrorMaliciousSyms) ==
  { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
  , declaredRows := 2, forcedTraceRows := .pinned 2, nonlinearMults := 0 }
#guard jsonBytes (mirrorRunDesc mirrorMaliciousSyms) == 606

/-! ## §5 — Axiom hygiene. -/

#assert_all_clean [
  mirrorRE_is_injectionFree, mirror_atoms, mirrorFix_isSome, mirrorFix, mirrorDfa_decides,
  mirrorBenign_eq, mirrorMalicious_eq, mirrorBenignSyms_ne, mirrorMaliciousSyms_ne,
  mirrorDfa_accepts_benign, mirrorDfa_rejects_malicious,
  mirrorRunWit_satisfies, mirrorRunWit_public, mirror_pipeline, mirror_both_poles,
  bytes_atoms, bytesFix_isSome, bytesFix, bytesDfa_decides,
  hiSyms_ne, loneSyms_ne, injectSyms_ne, bareSyms_ne, trailingSyms_ne,
  hi_free, lone_free, inject_not_free, bare_not_free, trailing_not_free,
  bytesDfa_accepts_benign, bytesDfa_rejects_injecting,
  bytesRunWit_satisfies, bytesRunWit_public, bytes_pipeline, bytes_both_poles,
  mirror_and_bytes_disagree, circuits_disagree_on_lone_brace
]

/-! ## §6 — RESIDUALS, named precisely.

* **(THE SHIPPED PREDICATE IS NOT REACHED — this is the honest answer to the lane's question.)**
  `zkoracle-prove/src/injection.rs` calls `dregg_dfa::Re`, a Rust re-implementation of the
  derivative matcher with its own `enum Re`, `derive`, `nullable` and `matches`. There is no
  `@[export]`, no FFI, no Lean artifact on that path. Everything above is therefore about (M) and
  (B) — Lean objects — and its relation to (S) is a DIFFERENTIAL on §2c's eleven vectors, RUN and
  agreeing, and nothing more.
  Making this "closed" in this tree's sense requires the shipped node to INVOKE a Lean-emitted
  decision (either an `@[export]`ed `derives`, or the emitted table itself shipped as data and the
  Rust reduced to a table walk). Not done here, not claimed.

* **(the mirror is WRONG as a byte model — a real defect, surfaced not swept.)** §3 exhibits a
  benign field (`a { b`, one of `injection.rs`'s OWN accept vectors) that the one-token
  `injectionTemplate` REFUSES. `ZkOracle.lean`'s comment calls `handlebarsOpen = 123` "a reserved
  code no benign character uses", but 123 is ASCII `{`. Under any byte↦code reading the mirror
  over-rejects. `zkOracle_sound`'s third leg is about (M), so that leg's `InjectionFree` is
  STRICTLY STRONGER than the deployed check — the safe direction for security, the wrong one for
  availability, and either way NOT the same predicate.

* **(the alphabet binding)** Inherited verbatim from `GuardToAutomatonCircuit` §8: the circuit
  reads MINTERM INDICES. `bytesDfa_decides` quantifies over arbitrary `Value` words with `enc`
  explicit, so the abstraction is sound and visible — but a verifier who wants "this trace read
  THIS field" must bind the `Value → index` map outside this descriptor. Nothing here claims that
  binding. For a byte field this is the `byte → {is-`{`, is-not-`{`}` classification, which is
  exactly what an in-circuit re-derivation would have to prove.

* **(what a RUN table commits)** Inherited verbatim: a run table declares the edges TRAVERSED, not
  the automaton, so "which guard ran" must be bound elsewhere. Both descriptors here are run
  tables.

* **(the empty field has no circuit)** `runWit_satisfies` needs a non-empty index word, so the
  `injection_free(b"")` pole of `injection.rs`'s test — true — has a guard verdict here
  (`derives [] injBytesRE = true`) but no `Satisfied2Public` witness. A zero-row run table is
  outside the emitter's shape.

* **(frontier sizes are DATA)** `bytesAut.states.length = 11` is compiled evaluation and saturation
  at fuel 64 is a kernel `rfl`, not a proven a-priori bound — `SymbolicFixpoint`'s termination note
  still lacks the counting step. A longer literal must be measured, not assumed.

* **(not in the root build)** This module is not imported from `metatheory/Dregg2.lean` (that file
  is off-limits to this lane); it is verified by `lake env lean` on the file. Registering it is a
  one-line integrator action.
-/

end Dregg2.Crypto.InjectionGuardCircuit
