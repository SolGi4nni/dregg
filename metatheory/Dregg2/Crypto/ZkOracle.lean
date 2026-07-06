/-
# Dregg2.Crypto.ZkOracle — the zkOracle capstone: authentic ∧ well-formed ∧ injection-free.

Composes the three verified cones into ONE attestation about an API request:

  * **authentic** — `Crypto/Deco` (DECO/zkTLS): an accepting proof certifies a genuine TLS session
    (server key signed the session key, transcript MAC'd under it, opens to the encoded facts);
  * **well-formed** — `Crypto/Cfg`: an accepting proof certifies the request body is in a JSON
    context-free language (NESTED structure the regular DFA cascade cannot express);
  * **injection-free** — `Crypto/Deriv`: the user-supplied field UNMATCHES a handlebars/injection
    template, expressed as a match against the NATIVE VERIFIED COMPLEMENT `neg` (dregg's boolean-closed
    derivative matcher) — "the input does not contain the template delimiter."

`zkOracle_sound` conjoins the three `verify_sound` discharges: an accepting DECO proof + an accepting
CFG proof + an injection-free field TOGETHER attest an authentic, well-formed, injection-free request,
reducing to the STARK `extractable` carriers + the §8 crypto floor DECO already names. The concrete
`Demo` section catches a real prompt-injection attempt: the benign field matches `neg template` (accepted),
the malicious field does NOT (rejected) — both decided by the verified matcher.
-/
import Dregg2.Crypto.Cfg
import Dregg2.Crypto.Deco
import Dregg2.Crypto.DecoUnforgeable
import Dregg2.Crypto.Deriv.Core
import Dregg2.Tactics

namespace Dregg2.Crypto.ZkOracle

open Dregg2.Crypto
open Dregg2.Crypto.Cfg
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Exec
open Dregg2.Exec.PredAlgebra

/-! ## The handlebars / prompt-injection template as a NATIVE-COMPLEMENT pattern.

A frame is a single character/token `⟨"c" ↦ sym code⟩`; `matchCode n` is the leaf predicate reading it.
The injection template is "the input CONTAINS the handlebars delimiter token" = `.* ⟨{{⟩ .*`. The
anti-injection property "the input UNMATCHES the template" is a match against `neg injectionTemplate`
— dregg's native, verified complement (`Crypto/Deriv`, discharged through the derivative determinizer).
No regex engine without verified complement can state this directly. -/

/-- A single input character/token as a derivative-matcher frame: the record `⟨"c" ↦ sym code⟩`. -/
def frame (code : Nat) : Value := .record [("c", .sym code)]

/-- The leaf predicate matching a frame whose char-code is `n`. -/
def matchCode (n : Nat) : Pred := .symEq "c" n

/-- The handlebars open-delimiter token `{{` (a reserved code no benign character uses). -/
def handlebarsOpen : Nat := 123

/-- **`injectionTemplate`** — "the input contains the handlebars delimiter `{{`": `.* ⟨{{⟩ .*`. A user
field matching THIS is a prompt-injection attempt (it can break out of / inject into the template). -/
def injectionTemplate : PredRE :=
  .cat (.star (.sym .tt)) (.cat (.sym (matchCode handlebarsOpen)) (.star (.sym .tt)))

/-- **`InjectionFree field`** — the field UNMATCHES the injection template: it matches the native
verified complement `neg injectionTemplate` (i.e. contains no handlebars delimiter). Decidable. -/
def InjectionFree (field : List Value) : Prop :=
  derives field (.neg injectionTemplate) = true

/-! ## The zkOracle capstone. -/

/-- **`zkOracle_sound`** — the whole zkOracle attestation in one statement. Given the DECO and CFG
STARK carriers and an accepting proof for each, plus the §8 ed25519/HMAC unforgeability carriers and an
injection-free user field, the request is simultaneously:
  (1) **authentic** — `F_attestation` emitted this: a genuine Stripe TLS session disclosed exactly these
      facts to this serverKey (the ideal-world statement `decoAuthenticated`, UNFORGEABLE — not merely a
      satisfying trace exists);
  (2) **well-formed** — the request body lies in the JSON context-free language;
  (3) **injection-free** — the user field unmatches the injection template.
Legs (2)/(3) are `verify_sound`/decidable discharges; leg (1) is the rung-4 realization
`DecoUnforgeable.deco_attestation_realizes` — the deployed verifier REALIZES the ideal attestation
functionality, so `authentic` now reads "F_attestation emitted this" rather than "∃ a satisfying trace."
The whole reduces to the two `extractable` carriers plus the standard §8 floor DECO names (ed25519
EUF-CMA + HMAC). This is the composition the goal asks for: authentic ∧ well-formed ∧ no-injection. -/
theorem zkOracle_sound
    {Dg Pd : Type} [KD : Deco.DecoVerifierKernel Dg Pd]
    {T Pc : Type} [KC : Cfg.CfgVerifierKernel T Pc]
    (jsonGrammar : ContextFreeGrammar T)
    (SK : PortalFloor.SignatureKernel Dg Dg Dg) (MK : PortalFloor.MacKernelE Dg Dg Dg)
    (hsigEq : KD.sigVerify = SK.sigVerify) (hmacEq : KD.macVerify = MK.verifyTag)
    (hsig : SK.unforgeable) (hmac : MK.unforgeable)
    (hDext : KD.extractable) (hCext : KC.extractable)
    (decoStmt : Deco.Statement Dg) (decoPf : Pd)
    (hDacc : KD.verify decoStmt decoPf = true)
    (body : List T) (cfgPf : Pc)
    (hCacc : KC.verify ⟨jsonGrammar, body⟩ cfgPf = true)
    (field : List Value) (hSafe : InjectionFree field) :
    DecoUnforgeable.decoAuthenticated SK MK KD.compress KD.encode decoStmt ∧
    body ∈ jsonGrammar.language ∧
    InjectionFree field := by
  refine ⟨DecoUnforgeable.deco_attestation_realizes SK MK hsigEq hmacEq hDext hsig hmac
      decoStmt decoPf hDacc, ?_, hSafe⟩
  exact Cfg.cfg_verify_sound hCext ⟨jsonGrammar, body⟩ cfgPf hCacc

#assert_axioms zkOracle_sound

/-! ## Demo — the anti-injection guard catches a real prompt-injection attempt.

Two concrete user fields decided by the verified matcher: a benign field (`"hi"`) matches `neg template`
(accepted — no delimiter), and a malicious field (`"{{ ..."`) does NOT (rejected — it carries the
handlebars delimiter). The rejection is exactly the zkOracle guard refusing an injecting request. -/

namespace Demo

/-- Benign user content `"hi"` (codes 104, 105) — no handlebars delimiter. -/
def benignField : List Value := [frame 104, frame 105]

/-- Malicious user content `"{{x"` — carries the handlebars delimiter `{{` (code 123). -/
def maliciousField : List Value := [frame handlebarsOpen, frame 120]

/-- The benign field is INJECTION-FREE: it matches the native complement `neg injectionTemplate`. -/
theorem benign_injection_free : InjectionFree benignField := by
  unfold InjectionFree benignField injectionTemplate frame matchCode
  decide

/-- The malicious field is NOT injection-free — it matches the template, so it FAILS `neg`. This is the
zkOracle guard REJECTING a prompt-injection attempt (the attestation cannot be produced). -/
theorem malicious_not_injection_free : ¬ InjectionFree maliciousField := by
  unfold InjectionFree maliciousField handlebarsOpen injectionTemplate frame matchCode
  decide

end Demo

/-! ## A concrete JSON grammar + a NESTED parse — well-formedness the DFA cascade cannot express.

A minimal JSON grammar (values = strings, arrays, objects; arrays and objects nest). We exhibit a genuine
parse certificate for `[[str]]` — a doubly-nested array — and land it in the language via `cfg_bridge`.
Balanced arbitrary-depth nesting is the canonical NON-regular property, so this is exactly the structural
guarantee `Crypto/Dfa`/`Crypto/Deriv` provably cannot give: the CFG layer is doing real work. -/

namespace Json

/-- JSON structural tokens. -/
inductive JTok | lbrace | rbrace | lbrack | rbrack | strTok
  deriving DecidableEq, Repr

/-- JSON nonterminals: value, array, object. -/
inductive JNT | jV | jArr | jObj
  deriving DecidableEq, Repr

open JTok JNT

/-- `V → str`. -/ def rV_str : ContextFreeRule JTok JNT := ⟨jV, [Symbol.terminal strTok]⟩
/-- `V → Arr`. -/ def rV_arr : ContextFreeRule JTok JNT := ⟨jV, [Symbol.nonterminal jArr]⟩
/-- `V → Obj`. -/ def rV_obj : ContextFreeRule JTok JNT := ⟨jV, [Symbol.nonterminal jObj]⟩
/-- `Arr → [ V ]`. -/ def rArr : ContextFreeRule JTok JNT :=
  ⟨jArr, [Symbol.terminal lbrack, Symbol.nonterminal jV, Symbol.terminal rbrack]⟩
/-- `Obj → { }`. -/ def rObj : ContextFreeRule JTok JNT :=
  ⟨jObj, [Symbol.terminal lbrace, Symbol.terminal rbrace]⟩

/-- The JSON grammar `V → str | Arr | Obj`, `Arr → [ V ]`, `Obj → { }`. -/
def jsonGrammar : ContextFreeGrammar JTok := ⟨JNT, jV, {rV_str, rV_arr, rV_obj, rArr, rObj}⟩

/-- A `Produces` that rewrites the nonterminal `r.input` sitting between contexts `p` and `q`, using a
rule `r` of the grammar. The reusable brick for building parse certificates by hand. -/
theorem produces_at (r : ContextFreeRule JTok JNT) (hr : r ∈ jsonGrammar.rules)
    (p q : List (Symbol JTok JNT)) :
    jsonGrammar.Produces (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) :=
  ⟨r, hr, ContextFreeRule.rewrites_of_exists_parts r p q⟩

theorem mem_rV_str : rV_str ∈ jsonGrammar.rules := Finset.mem_insert_self _ _
theorem mem_rV_arr : rV_arr ∈ jsonGrammar.rules :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
theorem mem_rArr : rArr ∈ jsonGrammar.rules :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))

/-- The doubly-nested array `[[str]]` as a token list. -/
def nestedBody : List JTok := [lbrack, lbrack, strTok, rbrack, rbrack]

/-- The leftmost parse of `[[str]]`: `V ⟹ Arr ⟹ [V] ⟹ [Arr] ⟹ [[V]] ⟹ [[str]]`. -/
def parseChain : List (List (Symbol JTok JNT)) :=
  [ [Symbol.nonterminal jV],
    [Symbol.nonterminal jArr],
    [Symbol.terminal lbrack, Symbol.nonterminal jV, Symbol.terminal rbrack],
    [Symbol.terminal lbrack, Symbol.nonterminal jArr, Symbol.terminal rbrack],
    [Symbol.terminal lbrack, Symbol.terminal lbrack, Symbol.nonterminal jV,
       Symbol.terminal rbrack, Symbol.terminal rbrack],
    [Symbol.terminal lbrack, Symbol.terminal lbrack, Symbol.terminal strTok,
       Symbol.terminal rbrack, Symbol.terminal rbrack] ]

/-- **`nested_accepts`** — `[[str]]` is a genuine accepting parse of the JSON grammar (`CfgAccepts`). -/
theorem nested_accepts : CfgAccepts jsonGrammar nestedBody parseChain := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact produces_at rV_arr mem_rV_arr [] []
  · exact produces_at rArr mem_rArr [] []
  · exact produces_at rV_arr mem_rV_arr [Symbol.terminal lbrack] [Symbol.terminal rbrack]
  · exact produces_at rArr mem_rArr [Symbol.terminal lbrack] [Symbol.terminal rbrack]
  · exact produces_at rV_str mem_rV_str
      [Symbol.terminal lbrack, Symbol.terminal lbrack] [Symbol.terminal rbrack, Symbol.terminal rbrack]

/-- **`nested_well_formed`** — the doubly-nested `[[str]]` is WELL-FORMED JSON: it lies in the grammar's
language. The concrete well-formedness witness the zkOracle CFG leg attests (here decided directly;
in the ZK setting `cfg_verify_sound` delivers it from an accepting STARK proof). -/
theorem nested_well_formed : nestedBody ∈ jsonGrammar.language :=
  (cfg_bridge jsonGrammar nestedBody).mp ⟨parseChain, nested_accepts⟩

end Json

/-! ## The concrete end-to-end demonstration — all three legs fired on real data. -/

/-- **`zkOracle_demo`** — a CONCRETE zkOracle attestation, end to end: a reference DECO/zkTLS
verifier PROOF authenticates the session (`F_attestation` emits on `sampleStmt` — a genuine Stripe
session backs the disclosed facts, via `reference_authenticates_payment`), the doubly-nested JSON body
`[[str]]` is well-formed, and the benign user field is injection-free. Three independently-verified
legs, discharged together on concrete inputs — authentic ∧ well-formed ∧ injection-free, with nothing
left abstract. The authentic leg is now the ideal-world `decoAuthenticated`, matching the strengthened
`zkOracle_sound` capstone. -/
theorem zkOracle_demo :
    DecoUnforgeable.decoAuthenticated Deco.Reference.refSigKernel Deco.Reference.refMacKernel
        Deco.Reference.refKernel.compress Deco.Reference.refKernel.encode Deco.Reference.sampleStmt ∧
    Json.nestedBody ∈ Json.jsonGrammar.language ∧
    InjectionFree Demo.benignField :=
  ⟨Deco.Reference.reference_authenticates_payment,
   Json.nested_well_formed,
   Demo.benign_injection_free⟩

#assert_axioms zkOracle_demo

/-! ## Runnable demonstrations — the verified guard, executed. -/

section Runnable
open Demo

-- The benign field `"hi"` UNMATCHES the injection template → `neg` matches → `true` (ACCEPTED).
#eval derives benignField (.neg injectionTemplate)      -- true

-- The malicious field `"{{x"` MATCHES the injection template → `neg` fails → `false` (REJECTED).
#eval derives maliciousField (.neg injectionTemplate)   -- false

-- The doubly-nested `[[str]]` is well-formed JSON (a parse certificate exists).
#eval (Json.parseChain.length, Json.nestedBody.length)  -- (6, 5): 6 forms / 5 rewrites over a 5-token body

end Runnable

end Dregg2.Crypto.ZkOracle
