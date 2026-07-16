/-
# Dregg2.Crypto.SlotConfinement — a `{{`-free attested field cannot perturb committed control structure.

**Honest scope.** This is *attested-field slot-confinement*: if a field disclosed from an authenticated
source is `{{`-free, interpolating it into a committed template preserves the template's control-token
(`{{`) structure — the number and positions of `{{` frames are exactly those of the committed literal
segments, and the field contributes zero. It is **NOT** an LLM-prompt-injection defense. dregg does not
build model prompts by string-interpolating untrusted data between `{{` delimiters: the LLM call assembles
a *structured* provider request (a JSON `messages` array with typed `role`/`content` slots — see
`deos-hermes/src/brain.rs::request_body`), so there is no string-template surface for a `{{`-check to
defend. The real use is `dregg-oracle`'s disclosed-field flow: a field extracted from an authenticated
web response must not corrupt the surrounding committed frame it is embedded in. That is what
`slot_confinement` certifies, and the hypothesis it requires is EXACTLY the zkOracle injection-free leg
(`ZkOracle.InjectionFree`) the oracle already attests for that field.

## Two honest views of one setup — this file vs `Crypto/Handlebars.lean`

`Crypto/Handlebars.lean` is AUTHORITATIVE for the handlebars template type and the CFG-membership framing:
its `HandlebarsTemplate` over the byte-level alphabet `Tok = {brace, data}` is THE template type, its
`render_mem_language` proves confinement as *whole-output membership in the template's context-free
language*, decided by the extractable STARK via `Cfg.cfg_verify_sound`. In that view `{{` is a two-`brace`
ADJACENCY (a single `{` is fine) and confinement is a byte-level parse property.

This module is a DIFFERENT view, and its lemma is genuinely NOT subsumed. Here `{{` is a SINGLE atomic
lexed frame (the reserved `handlebarsOpen` code, one `Value`), and confinement is `{{`-token-COUNT
preservation across an interpolation — proved by the verified derivative matcher (`Crypto/Deriv`) over the
same `injectionTemplate` as `Crypto/ZkOracle`. This is a statement about the count/structure of `{{`
tokens surviving an interpolation, whereas `render_mem_language` is a statement about the whole output
landing in a language: two different theorems about the same setup, both true.

The matcher machinery is inherently over `List Value` — there is NO `injectionTemplate` over `Tok`, and the
`filter`-based `controlTokens` (which composes over `++`) cannot detect a two-token `{{` adjacency — so this
view keeps its native `List Value` alphabet and its own template vehicle (`Seg`/`Template`/`render` below).
That vehicle is local to THIS lemma; `Handlebars.HandlebarsTemplate` remains the one authoritative template
type. No merge is faked: the derivative-matcher proof does not typecheck over `Tok`, so it is not forced
onto it.

Non-vacuity is pinned in BOTH polarities: a `{{`-free field PRESERVES the structure (`benign_preserves`
+ `#guard`s), and a `{{`-bearing field CHANGES it — injects exactly one extra control token
(`malicious_injects`) — so the guard is load-bearing, not decorative.

Rides entirely on the verified derivative matcher (`Crypto/Deriv`): `derives_cat`, `derives_sym`,
`derives_neg`, `derives_star_cons` and the `injectionTemplate` of `Crypto/ZkOracle`. No new axioms.
-/
import Dregg2.Crypto.ZkOracle
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Tactics

namespace Dregg2.Crypto.SlotConfinement

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.ZkOracle

/-! ## The control-token reader.

A control token is a frame whose `"c"` field is the reserved `handlebarsOpen` code — EXACTLY the frame
`injectionTemplate` detects (its middle leaf is `sym (matchCode handlebarsOpen)`). `controlTokens` keeps
only those frames, so it reads off "the `{{` structure" of a token list. -/

/-- **`isControl a`** — is frame `a` the handlebars control token `{{`? The SAME leaf predicate the
zkOracle `injectionTemplate` fires on (`leaf (matchCode handlebarsOpen)`). -/
def isControl (a : Value) : Bool := PredRE.leaf (matchCode handlebarsOpen) a

/-- **`controlTokens w`** — the control-token structure of a token list: the sublist of `{{` frames,
in order. Its equality across two token lists is "they carry the same handlebars control structure." -/
def controlTokens (w : List Value) : List Value := w.filter isControl

/-! ## Templates and rendering — the derivative-matcher view's local vehicle.

`Handlebars.HandlebarsTemplate` (over `Tok`) is the authoritative template type; these `List Value`
segments are the vehicle that carries `slot_confinement` in the matcher view, where a `{{` is one atomic
control frame rather than a two-`brace` adjacency. -/

/-- A template **segment**: fixed template bytes `lit ts` (MAY contain control tokens `{{` — the committed
frame's own delimiters), or a `slot n` hole where the untrusted attested field `binding n` lands. -/
inductive Seg (Name : Type) where
  | lit  (ts : List Value)
  | slot (n : Name)
  deriving Repr

/-- A **template** is a list of segments. -/
abbrev Template (Name : Type) := List (Seg Name)

variable {Name : Type}

/-- **`render b T`** — the rendered token list: concatenate the template left-to-right, substituting each
`slot n` with the attested field `binding n = b n`. -/
def render (b : Name → List Value) : Template Name → List Value
  | []                 => []
  | Seg.lit ts :: rest => ts ++ render b rest
  | Seg.slot n :: rest => b n ++ render b rest

/-- **`litOnly T`** — the template's LITERAL bytes alone (drop every slot). The committed frame the
disclosure published; the reference an attested field must not perturb. -/
def litOnly : Template Name → List Value
  | []                 => []
  | Seg.lit ts :: rest => ts ++ litOnly rest
  | Seg.slot _ :: rest => litOnly rest

/-! ## The `{{`-free hypothesis is exactly the zkOracle injection-free leg.

`InjectionFree w` (`Crypto/ZkOracle`) is `derives w (neg injectionTemplate) = true`. We show this holds
iff `w` carries no control token, connecting the ZK guard to `controlTokens`. -/

/-- `star (sym tt)` matches EVERY word — the `.*` wings of `injectionTemplate`. -/
theorem derives_star_tt (w : List Value) : derives w (PredRE.star (PredRE.sym Pred.tt)) = true := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    rw [derives_star_cons, derives_cat]
    refine ⟨[], as, rfl, ?_, ih⟩
    -- der a (sym tt) = ε  (leaf tt a = true), so derives [] (der a (sym tt)) = true
    have hd : der a (PredRE.sym Pred.tt) = PredRE.ε := by simp [der, leaf, Pred.eval]
    rw [hd]; rfl

/-- **`derives_injection_iff`** — the zkOracle injection template fires on `w` IFF `w` contains a
handlebars control token. Peels the `.* ⟨{{⟩ .*` structure through the verified `derives_cat`/
`derives_sym` lemmas. -/
theorem derives_injection_iff (w : List Value) :
    derives w injectionTemplate = true ↔ ∃ a ∈ w, isControl a = true := by
  unfold injectionTemplate
  rw [derives_cat]
  constructor
  · rintro ⟨w1, w2, rfl, -, h2⟩
    rw [derives_cat] at h2
    obtain ⟨u1, u2, rfl, hsym, -⟩ := h2
    rw [derives_sym] at hsym
    obtain ⟨a, rfl, hfire⟩ := hsym
    exact ⟨a, by simp, hfire⟩
  · rintro ⟨a, ha, hfire⟩
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
    refine ⟨pre, a :: post, rfl, derives_star_tt pre, ?_⟩
    rw [derives_cat]
    exact ⟨[a], post, rfl, (derives_sym [a] (matchCode handlebarsOpen)).mpr ⟨a, rfl, hfire⟩,
           derives_star_tt post⟩

/-- **`injection_false_of_free`** — an injection-free field does NOT match the injection template. -/
theorem injection_false_of_free (w : List Value) (h : InjectionFree w) :
    derives w injectionTemplate = false := by
  unfold InjectionFree at h
  rw [derives_neg] at h
  cases hd : derives w injectionTemplate with
  | false => rfl
  | true  => rw [hd] at h; simp at h

/-- **`injectionFree_forall`** — the zkOracle `{{`-free hypothesis IS "no frame is a control token." -/
theorem injectionFree_forall (w : List Value) :
    InjectionFree w ↔ ∀ a ∈ w, isControl a = false := by
  constructor
  · intro h a ha
    have hfalse := injection_false_of_free w h
    by_contra hc
    have htrue : isControl a = true := by
      cases hh : isControl a with
      | true  => rfl
      | false => exact absurd hh hc
    have hcontra : derives w injectionTemplate = true := (derives_injection_iff w).mpr ⟨a, ha, htrue⟩
    rw [hfalse] at hcontra; exact Bool.noConfusion hcontra
  · intro h
    have hfalse : derives w injectionTemplate = false := by
      by_contra hc
      have htrue : derives w injectionTemplate = true := by
        cases hh : derives w injectionTemplate with
        | true  => rfl
        | false => exact absurd hh hc
      obtain ⟨a, ha, hfire⟩ := (derives_injection_iff w).mp htrue
      rw [h a ha] at hfire; exact Bool.noConfusion hfire
    unfold InjectionFree
    rw [derives_neg, hfalse]; rfl

/-- An injection-free field contributes NO control tokens: its `controlTokens` filter is empty. -/
theorem filter_control_nil_of_forall (w : List Value)
    (h : ∀ a ∈ w, isControl a = false) : w.filter isControl = [] := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    have ha0 : isControl a = false := h a (by simp)
    have hrest : as.filter isControl = [] := ih (fun x hx => h x (by simp [hx]))
    simp [ha0, hrest]

/-! ## THE THEOREM — slot confinement. -/

/-- **`slot_confinement`** — the committed frame is intact. If every attested field bound into template `T`
is `{{`-free (`InjectionFree`, the zkOracle injection-free leg), then the control-token structure of the
rendered token list EQUALS that of the template's literal segments alone. The field contributes ZERO
control tokens: it cannot add or alter a single `{{`. -/
theorem slot_confinement (T : Template Name) (b : Name → List Value)
    (hb : ∀ n, Seg.slot n ∈ T → InjectionFree (b n)) :
    controlTokens (render b T) = controlTokens (litOnly T) := by
  induction T with
  | nil => rfl
  | cons seg rest ih =>
    cases seg with
    | lit ts =>
      have hrec := ih (fun n hn => hb n (List.mem_cons_of_mem _ hn))
      simp only [render, litOnly, controlTokens, List.filter_append] at hrec ⊢
      rw [hrec]
    | slot n =>
      have hrec := ih (fun m hm => hb m (List.mem_cons_of_mem _ hm))
      have hn0 : (b n).filter isControl = [] :=
        filter_control_nil_of_forall (b n)
          ((injectionFree_forall (b n)).mp (hb n (by simp)))
      simp only [render, litOnly, controlTokens, List.filter_append] at hrec ⊢
      rw [hn0, List.nil_append, hrec]

/-- **`slot_confinement_count`** — the sharper counting form: the number of `{{` control tokens in the
rendered output equals the number in the template literals. (A corollary of the structural equality;
enough on its own for the security claim — the field cannot change the `{{` count.) -/
theorem slot_confinement_count (T : Template Name) (b : Name → List Value)
    (hb : ∀ n, Seg.slot n ∈ T → InjectionFree (b n)) :
    (render b T).countP isControl = (litOnly T).countP isControl := by
  have h := slot_confinement T b hb
  simp only [controlTokens] at h
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter, h]

/-! ## Corollary — a single attested field between fixed committed bytes. -/

/-- **`attested_field_confined`** — restated for a single field slot between fixed committed bytes: a
committed prefix (`before`), the field's hole, and a committed suffix (`after`). If the field is
injection-free — EXACTLY the property the zkOracle attestation certifies for a disclosed field — then the
control-token structure of the whole rendered output equals that of the template literals alone: the
committed frame survives the field's interpolation verbatim. -/
theorem attested_field_confined (before after field : List Value) (nm : Name)
    (hSafe : InjectionFree field) :
    controlTokens (render (fun _ => field) [Seg.lit before, Seg.slot nm, Seg.lit after])
      = controlTokens (litOnly [Seg.lit before, Seg.slot nm, Seg.lit after]) := by
  apply slot_confinement
  intro _ _
  exact hSafe

/-! ## Non-vacuity — BOTH polarities, on concrete data.

A concrete committed template whose LITERAL carries one real control token `{{` (a frame delimiter), and
a `slot "field"` for the untrusted attested field. We show: a benign (`{{`-free) field PRESERVES the one
control token, and a malicious (`{{`-bearing) field INJECTS a second — so the guard is load-bearing. -/

namespace Demo

/-- A committed template: one literal control token `{{` (a frame delimiter), then the field's slot. -/
def committedTemplate : Template String := [Seg.lit [frame handlebarsOpen], Seg.slot "field"]

/-- A benign attested field `"hi"` (codes 104,105) — carries no handlebars delimiter. -/
def benignField : String → List Value := fun _ => [frame 104, frame 105]

/-- A malicious field `"{{x"` — smuggles the handlebars delimiter `{{` (code 123). -/
def maliciousField : String → List Value := fun _ => [frame handlebarsOpen, frame 120]

/-- **(a) WITNESS** — the benign field is injection-free (the hypothesis is SATISFIABLE). -/
theorem benign_injection_free : InjectionFree (benignField "field") := by
  unfold InjectionFree benignField injectionTemplate frame matchCode handlebarsOpen
  decide

/-- **(a) WITNESS** — with a `{{`-free field, the rendered output has the SAME control structure as
the template literals: `slot_confinement` fires, the conclusion is meaningful (one preserved `{{`). -/
theorem benign_preserves :
    controlTokens (render benignField committedTemplate) = controlTokens (litOnly committedTemplate) := by
  apply slot_confinement
  intro n _
  show InjectionFree (benignField n)
  unfold InjectionFree benignField injectionTemplate frame matchCode handlebarsOpen
  decide

/-- **(b) COUNTER** — the malicious field is NOT injection-free (the guard rejects it). -/
theorem malicious_not_injection_free : ¬ InjectionFree (maliciousField "field") := by
  unfold InjectionFree maliciousField injectionTemplate frame matchCode handlebarsOpen
  decide

/-- **(b) COUNTER** — WITHOUT the `{{`-free guard the field INJECTS a control token: the rendered
output has EXACTLY ONE MORE `{{` than the template literals. The guard is load-bearing, not decorative. -/
theorem malicious_injects :
    (controlTokens (render maliciousField committedTemplate)).length
      = (controlTokens (litOnly committedTemplate)).length + 1 := by decide

/-! ### Runnable `#guard`s (Nat lengths / Bool — `Value` has no `DecidableEq`, so we count). -/

-- The benign field is `{{`-free; the malicious field is not (the zkOracle guard, decided).
#guard derives (benignField "field") (.neg injectionTemplate) = true
#guard derives (maliciousField "field") (.neg injectionTemplate) = false

-- Template literals carry ONE control token `{{`.
#guard (controlTokens (litOnly committedTemplate)).length = 1
-- Benign field PRESERVES it (still 1) — structure unchanged.
#guard (controlTokens (render benignField committedTemplate)).length = 1
-- Malicious field INJECTS one (now 2) — structure changed: the guard is load-bearing.
#guard (controlTokens (render maliciousField committedTemplate)).length = 2

-- Sharper pure-slot form: an empty-literal template has NO control tokens; a benign field keeps it 0,
-- a malicious field forces it to 1 — injection is possible EXACTLY when the guard is dropped.
#guard (controlTokens (litOnly [Seg.slot "f"])).length = 0
#guard (controlTokens (render benignField [Seg.slot "f"])).length = 0
#guard (controlTokens (render maliciousField [Seg.slot "f"])).length = 1

end Demo

/-! ## Axiom hygiene — the slot-confinement tower is kernel-clean. -/

#assert_all_clean [
  derives_star_tt, derives_injection_iff, injection_false_of_free, injectionFree_forall,
  filter_control_nil_of_forall, slot_confinement, slot_confinement_count, attested_field_confined
]

#print axioms slot_confinement
#print axioms attested_field_confined

end Dregg2.Crypto.SlotConfinement
