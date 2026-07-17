# The Proof-Producing Templater — design

**What this is.** A forward-design doc for turning dregg's two prototype "handlebars" modules into one
coherent capability: a templater whose `render(T, data)` emits not just an output but a **proof** — the
leftmost-derivation witness certifying "this output was generated from template `T` with data confined to
its holes." The witness is exactly the context-free parse certificate dregg's extractable STARK already
verifies, so every render becomes a **receipt** (dregg's thesis — "a turn is the exercise of a
proof-carrying token leaving a receipt" — applied to *generation*), injection-freedom holds **by
construction**, and renders **compose** (a hole filled by another proof-carrying render nests the proofs).

**But first, honesty about the surface.** The `{{`-prompt-injection framing that motivates the older module
is *not* a real dregg attack surface. This doc opens by retiring it to its true, narrow scope, then designs
the general machinery that is worth building for its own sake.

**Status legend.** BUILT = in-tree at HEAD, verified, file:line cited. PROPOSED = designed here, unbuilt.
Every "would"/"proposed" is design; every present-tense claim is checked against code at HEAD.

---

## 1. Retire the brace framing honestly (the surface is not what the name says)

The name "injection-free" invites the reading: *dregg builds LLM prompts by string-interpolating untrusted
data into a `{{handlebars}}` template, and we defend against a `{{`-delimiter breakout.* **That is not how
dregg talks to a model, and it is important to say so plainly.**

The actual LLM call is `deos-hermes/src/brain.rs::request_body` (`deos-hermes/src/brain.rs:457`). It builds
a **structured** provider request — a JSON `messages` array of `{"role", "content"}` objects
(`brain.rs:460`), a separate `"system"` string, a separate `"tools"` array — never a single interpolated
template string. The untrusted player field lands as the `content` of its own `role:"user"` message
(`brain.rs:459`); it is *data in a typed slot*, not text spliced between control delimiters. There is no
`{{`-templating on the path to the model, so **a `{{`-delimiter check defends nothing on the LLM path.** Any
doc or comment that implies otherwise is overclaiming; this design does not.

So what *is* the real value? Two things, and only these:

1. **Slot-confinement for a disclosed fact (the narrow real property).** When dregg discloses a field
   extracted from an *authenticated* web response — `dregg-oracle`'s trustless-web-facts flow, whose portable
   proof "re-derives the zkOracle legs (well-formed CFG certificate, injection-free) over the authenticated
   body" (`dregg-oracle/src/lib.rs:9`, and the three asserted legs `authentic` / `well-formed` /
   `injection-free` at `dregg-oracle/src/lib.rs:173-182`) — the honest guarantee is that the disclosed field
   **cannot perturb the surrounding committed structure**. That is *slot-confinement*, and it is already a
   proven theorem: `SlotConfinement.slot_confinement` (`metatheory/Dregg2/Crypto/SlotConfinement.lean:190`) shows a
   `{{`-free field bound into a template preserves the template's control-token structure verbatim. This
   property is *real and worth keeping* — it is about an attested field not corrupting a committed frame, not
   about defending an LLM.

2. **The general machinery below (the actual prize).** The `{{`-question was a *first concrete instance* of a
   far more valuable pattern: **generation with a checkable certificate**. The value is not the delimiter
   check; it is that "output ∈ language of template-grammar `T`" is (a) the correct *structural* framing of
   confinement, (b) decided by the **same** extractable STARK that already backs the CFG well-formedness leg,
   and (c) the seed of a verified grammar→circuit compiler and a proof-producing templater. That is what
   §§3–4 design.

**Register discipline for the whole codebase (a recommendation this doc makes):** wherever a comment says
"injection-free defends prompt injection," rewrite it to "slot-confinement: a disclosed/attested field
cannot alter the committed structure it is embedded in." The `Handlebars.lean` header already half-does this
(it calls the deployed `ZkOracle.InjectionFree` a "coarse denylist stand-in", `Handlebars.lean:4`); finish
the job and drop the LLM-defense connotation entirely.

---

## 2. Reconcile the two handlebars modules (do not ship two parallel framings)

There are two modules today, built from opposite ends, and they overlap. They must be reconciled into one
authoritative framing plus one surviving narrow lemma — not left as parallel copies.

### 2.1 What each module actually is (BUILT)

**`metatheory/Dregg2/Crypto/Handlebars.lean`** (BUILT this session, commit `d68fd6f8f`) — the **CFG-membership
framing**, and the *right* one:

- A template is literally a context-free grammar: `handlebarsToGrammar T` (`Handlebars.lean:180`) maps fixed
  segments to terminals and each hole to a right-linear "no `{{`" sub-grammar (`holeRules`, `Handlebars.lean:149`).
- `injectionFree T output := output ∈ (handlebarsToGrammar T).language` (`Handlebars.lean:296`) — confinement
  *as language membership*, carrying a generation/parse witness, not a substring denylist.
- Generation soundness is **proven**: `render_mem_language` (`Handlebars.lean:283`) — safe rendering always
  produces a language member — with the load-bearing lemma `safe_state_derives` (`Handlebars.lean:215`), all
  `#assert_axioms`-clean (`Handlebars.lean:314-317`).
- The circuit tie is **proven and shared**: `injectionFree_of_verify` (`Handlebars.lean:308`) decides
  membership through the *existing* `Cfg.cfg_verify_sound` — the same extractable STARK the well-formedness
  leg rides, no fresh checker.
- Honest residuals are named, not `sorry`-ed: round-trip uniqueness needs CFG-unambiguity (mathlib lacks the
  API, `Handlebars.lean:326`), and per-hole `NoDoubleBrace` misses a `{{` that forms at a hole/literal *seam*
  (`Handlebars.lean:337`). Its `RustTwin` (`Handlebars.lean:359`) pins agreement with `zkoracle-prove/src/injection.rs`.

**`metatheory/Dregg2/Crypto/SlotConfinement.lean`** (the older module, PRE-EXISTING as `ZkHandlebars.lean`
since Jul 10; rehomed under this name by `7396df797` — §2.2's plan, landed) — the **delimiter/control-token
framing**:

- A template is segments + slots; `render` (`SlotConfinement.lean:91`) interpolates the bindings.
- `controlTokens w` (`SlotConfinement.lean:69`) reads the sublist of `{{` frames; `slot_confinement`
  (`SlotConfinement.lean:190`) proves a `{{`-free binding preserves the literal segments' control structure
  verbatim, with the counting corollary `slot_confinement_count` (`SlotConfinement.lean:212`) and both
  polarities of non-vacuity (`benign_preserves` / `malicious_injects`, `SlotConfinement.lean:258`/`273`).
- `derives_injection_iff` (`SlotConfinement.lean:122`) proves the zkOracle `injectionTemplate` fires iff `w`
  contains a control token, tying the `{{`-free hypothesis to `ZkOracle.InjectionFree`.

They **overlap** on the central object (a template = literal segments + holes/slots, and a "no `{{`"
condition on hole data) but diverge on what is proven: `Handlebars.lean` proves *membership in a grammar
language* (structural, circuit-backed); `SlotConfinement.lean` proves *control-token count preservation*
(delimiter-structural, matcher-backed via `Crypto/Deriv`).

### 2.2 Recommendation — `Handlebars.lean` is authoritative; one lemma survives from `ZkHandlebars.lean`

**Authoritative framing: `Handlebars.lean` (CFG-membership).** It is the right abstraction (confinement =
language membership), it is circuit-backed through the *shared* `cfg_verify_sound` rather than a bespoke
derivative matcher, and it is the foundation the compiler (§3) and templater (§4) build on. This is the
module the north star extends.

**What survives from `ZkHandlebars.lean`: exactly `slot_confinement`** (and its supporting `derives_injection_iff`,
`injectionFree_forall`, `slot_confinement_count`). This is the §1.1 narrow real property — an attested field
cannot alter committed control structure — and it is genuinely *not* subsumed by `render_mem_language`:
`slot_confinement` is a statement about the *count/structure of `{{` tokens being preserved across an
interpolation*, whereas `render_mem_language` is a statement about *the whole output landing in a language*.
They are different theorems about the same setup and both are true.

**Concrete reconciliation plan (LANDED, `7396df797`)** — recorded below as it was decided; the rename and
the rescoped header are in the tree. One correction the execution forced: the "re-prove `slot_confinement`
over `Tok`" step suggested below is **false** and was not taken — a `NoDoubleBrace` hole may contain a single
brace that `render` counts, so brace-count preservation does not hold over `Tok`, and the two supports
(`derives_injection_iff`, `injectionFree_forall`) are theorems about the `List Value` `InjectionFree` with no
`Tok` analogue. The two views are kept honestly distinct instead of faked into one.

- **STAYS (rehomed):** rename `ZkHandlebars.lean` → `metatheory/Dregg2/Crypto/SlotConfinement.lean`, scoped to
  *exactly* the narrow property, with a header that states §1's honesty (structured-Messages, not
  string-templating; this is about attested-field confinement, not LLM defense). Keep `slot_confinement`,
  `slot_confinement_count`, `dm_rules_intact`, `derives_injection_iff`, `injectionFree_forall`, and their
  non-vacuity demos. Retire the "AI dungeon-master / prompt" narration in the header to "attested field bound
  into a committed frame."
- **RETIRES (the framing, not the file):** the `{{`-injection-*defends-the-LLM* reading. The `Template`/`render`
  types in the rehomed module are fine as the vehicle for `slot_confinement`; what retires is any claim that
  a `{{`-check is the security property for model prompting.
- **DELETES:** nothing of the *proofs* — but the `Template`/`Seg`/`render` **duplication** between the two
  modules should collapse. `Handlebars.lean`'s `HandlebarsTemplate`/`Segment`/`render` (`Handlebars.lean:62-80`)
  is the authoritative template type; the rehomed slot-confinement module should either (a) re-express
  `slot_confinement` over `HandlebarsTemplate` + `Tok` (unifying the alphabets), or (b) if the `Value`-frame
  alphabet is load-bearing for the `Crypto/Deriv` matcher tie, keep its own `Seg`/`render` but document the
  bridge to `HandlebarsTemplate`. **Recommendation: (a)** — unify on `HandlebarsTemplate`/`Tok`, re-proving
  `slot_confinement` as "the `brace`-token count of `render T d` equals that of the literal segments when
  every `d h` is `NoDoubleBrace`," which is a short induction mirroring the existing one. This leaves exactly
  **one** template type in the codebase.
- **MERGES:** the `RustTwin`/`Demo` agreement blocks fold together — one place pins the single-`{`-fine /
  `{{`-flagged split against `zkoracle-prove/src/injection.rs`.

Net: one authoritative module (`Handlebars.lean`, CFG-membership, circuit-backed) + one narrow surviving
lemma (`slot_confinement`, rehomed and honestly scoped) + one template type. No two parallel framings.

---

## 3. The verified grammar → zkcircuit compiler (PROPOSED)

`Cfg.lean` and `CfgCompact.lean` are the two ends of a grammar→circuit compiler that is *implicit* in the
tree but never named as a general pipeline. This section names it and designs it as a **translation-validated**
compiler — the identical discipline as `docs/DESIGN-verified-layout-optimizer.md`, aimed at grammars instead
of AIR layouts.

### 3.1 The two ends that already exist (BUILT)

- **The floor — `cfg_bridge`** (`Cfg.lean:113`): a parse certificate (a derivation form-chain) is satisfiable
  **iff** the input is in the grammar's language — *fully proven, both directions, no primitive seam*. This is
  the denotational anchor: "the circuit's accept predicate ⟺ language membership."
- **The compact wire — `CfgCompact.Replay` + `replay_derives`** (`CfgCompact.lean:48`/`67`): the O(tokens)
  certificate is a **leftmost rule sequence** replayed as a pushdown run; `compact_sound` (`CfgCompact.lean:81`)
  gives accept ⇒ language membership, and `compact_to_chain` (`CfgCompact.lean:90`) ties it back to the
  `CfgAccepts` object. **This rule sequence is the generation witness** — the same object the templater emits
  (§4).
- **The ceiling — the extractable STARK** (`Cfg.CfgVerifierKernel`, `Cfg.lean:144`): `extractable` is STARK
  soundness (accept ⇒ a satisfying parse chain exists), and `cfg_verify_sound` (`Cfg.lean:160`) composes it
  with `cfg_bridge` to give "in-circuit accept ⇒ language membership." The carrier is the *only* crypto
  residue; everything else is proven.

So the *soundness* direction of grammar→circuit is welded end to end already: a grammar `g`, an in-circuit
CFG-verifier accept over `(g, input)`, and you get `input ∈ g.language`, for **any** context-free `g`,
including the handlebars grammars of §2 (that is exactly `injectionFree_of_verify`).

### 3.2 What the compiler adds (PROPOSED) — the pipeline

The missing piece is a *checked compiler* that takes a grammar and emits a concrete AIR/descriptor for the
CFG-verifier over that grammar, with a **refinement theorem** that the emitted circuit accepts *exactly* the
grammar's language. Architecture (translation validation):

```
  grammar g   (a ContextFreeGrammar T — e.g. handlebarsToGrammar T, or a JSON grammar)
       │
       ▼
  [ UNTRUSTED grammar→AIR compiler ]   ← arbitrary encoding heuristics; NOT trusted
       │   proposes descriptor d_g  +  a decoding map ψ (circuit trace → parse chain)
       ▼
  [ TRANSLATION VALIDATOR ]            ← TRUSTED Lean checker
       │   attempts to PROVE the refinement:
       │       ∀ input proof,  Verify d_g (g, input) proof = true  ↔  input ∈ g.language
       │   soundness (⟹) via `extractable` + `cfg_bridge`;  completeness (⟸) via a parse witness
       ├── proof closes  ─────────►  ACCEPT d_g  (emit the descriptor for g)
       └── proof fails   ─────────►  REJECT     (a miscompiled grammar circuit never ships)
```

The refinement theorem shape (PROPOSED):

```lean
-- PROPOSED: the grammar→circuit refinement obligation the validator discharges per grammar g
theorem cfg_circuit_refines (g : ContextFreeGrammar T) (d_g : /- descriptor for g -/)
    [K : CfgVerifierKernel T Proof] (hext : K.extractable) :
    ∀ (input : List T) (proof : Proof),
      K.verify ⟨g, input⟩ proof = true  ↔  input ∈ g.language
```

The **⟹ direction is essentially done** — it is `cfg_verify_sound` (`Cfg.lean:160`) — for any `g`, given
`extractable`. The general compiler wraps that as a per-`g` accepted output. The **⟸ direction is the hard
part** (§3.4): "in-language ⟹ some proof the circuit accepts," i.e. the honest prover can always build the
compact replay for a language member. `replay_derives`/`compact_sound` give one direction of the
Replay↔language correspondence; the converse (every language member has an *accepting replay the emitted AIR
verifies*) is where the completeness work lives.

### 3.3 Relation to the existing `dregg-dsl/gen_*` backends — REUSE, do not supersede

dregg already has a multi-backend compiler from a DSL IR to circuits: `dregg-dsl/src/gen_air.rs`
(AIR constraint descriptors), `gen_plonky3.rs` (native `p3_air::Air`), `gen_kimchi.rs` (Kimchi gates),
`gen_sp1.rs` (RISC-V zkVM guest), `gen_midnight.rs` (ZKIR v3), `gen_datalog.rs`, `gen_rust.rs`. Its IR
(`dregg-dsl/src/ir.rs::ConstraintIr`) is **arithmetic-relational** — params, `require!` comparisons,
`Mutate` old/new columns, `Membership`/Merkle — i.e. it compiles *state-transition constraints*, not
*language recognizers*.

**The grammar→circuit compiler is a NEW front-end that REUSES the existing backends, not a replacement.**
Concretely:

- The grammar→circuit compiler's job is to lower a `ContextFreeGrammar` into the **`ConstraintIr`** that
  encodes the pushdown-replay verifier (stack column(s), a rule-index input column, the terminal-match and
  rule-application constraints of `CfgCompact.Replay`). Once it is `ConstraintIr`, **all seven `gen_*`
  backends apply unchanged** — you get the CFG-verifier AIR (`gen_air`), a native Plonky3 impl (`gen_plonky3`),
  an SP1 guest (`gen_sp1`, a natural fit: `gen_sp1.rs`'s header explicitly cites "complex constraints that
  don't map cleanly to arithmetic circuits"), etc., for free.
- What the grammar front-end adds that the DSL lacks: the **refinement theorem** tying the emitted IR back to
  `g.language` (§3.2). The `gen_*` backends today have `gen_diff_test.rs` (differential testing) but no
  language-level refinement proof; the grammar front-end supplies the missing *proof* that the whole IR
  denotes the intended recognizer.

So: **reuse** the backends as the code-emission layer; **add** a verified grammar→`ConstraintIr` front-end
plus the translation validator that proves `cfg_circuit_refines`. The compiler is "translation-validated
grammar → (existing) DSL IR → (existing) multi-backend circuit."

### 3.4 The hard parts (named)

1. **Completeness (⟸): in-language ⟹ circuit-accept.** Soundness rides `extractable` + `cfg_bridge` for free;
   completeness requires that the honest prover can *always* construct an accepting compact replay for any
   language member, and that the *emitted AIR* verifies it. `CfgCompact.lean`'s own header is explicit that
   prover-side completeness is "witnessed constructively by the Rust prover... not restated as a Lean theorem"
   (`CfgCompact.lean:23`). Making it a Lean theorem — `input ∈ g.language → ∃ rs, ReplayAccepts g rs input` —
   is real automata-theory work (the leftmost-derivation-to-rule-sequence extraction).
2. **Unambiguity for uniqueness.** For grammars where the *decoded parse must be unique* (a hole's data must
   be uniquely recoverable — the round-trip residual of `Handlebars.lean:326`), the compiler needs a grammar
   **unambiguity** side-condition. mathlib has no CFG-unambiguity API (`Handlebars.lean:334`); this is
   foundational work, and it gates the uniqueness half of the templater's composition story.
3. **The decoding map ψ must be checked, not trusted** — exactly as `φ` in the layout optimizer
   (`DESIGN-verified-layout-optimizer.md` §6.3): if the untrusted compiler supplies a wrong trace→parse-chain
   map, the proof must *fail*, so ψ carries its own well-formedness obligation in the validator's input.
4. **Grammar → `ConstraintIr` encoding fidelity.** The pushdown stack is unbounded in principle; the AIR
   encoding needs a bounded stack column with a depth budget, and the refinement must hold *within budget*
   (or prove the budget suffices for the template class). This is the CFG analogue of the layout optimizer's
   "positions vs whole-AIR" honesty (`DESIGN-verified-layout-optimizer.md` §6.5).

---

## 4. The proof-producing templater (the north star, PROPOSED)

### 4.1 The API

Today `render : HandlebarsTemplate → (HoleId → List Tok) → List Tok` (`Handlebars.lean:80`) returns only the
output. The north star extends the codomain to carry the witness:

```lean
-- PROPOSED: render emits (output, generation-proof)
structure GenerationProof (T : HandlebarsTemplate) (output : List Tok) where
  /-- the leftmost rule sequence — a CfgCompact.Replay certificate -/
  rules  : List (ContextFreeRule Tok (handlebarsToGrammar T).NT)
  /-- the certificate is an ACCEPTING replay of `output` from the grammar's start -/
  accepts : CfgCompact.ReplayAccepts (handlebarsToGrammar T) rules output

def renderWithProof (T : HandlebarsTemplate) (d : HoleId → List Tok) (hsafe : safe T d) :
    Σ output : List Tok, GenerationProof T output
```

The proof object is **the leftmost-derivation witness = the `CfgCompact` rule sequence** (`CfgCompact.lean:60`).
This is not a new artifact type: it is precisely the compact certificate the extractable STARK already
verifies (`compact_sound`, `CfgCompact.lean:81`), and it expands to the `CfgAccepts` chain the capstone
consumes (`compact_to_chain`, `CfgCompact.lean:90`).

### 4.2 By-construction injection-freedom (slot-confinement, honestly named)

`render_mem_language` (`Handlebars.lean:283`) already proves safe rendering lands in the language — but it
proves *existence* of a derivation; the templater's job is to **produce** the specific rule sequence. The key
new lemma (PROPOSED):

```lean
-- PROPOSED: the generation witness certifies confinement, constructively
theorem renderWithProof_confined (T : HandlebarsTemplate) (d : HoleId → List Tok) (hsafe : safe T d) :
    let ⟨output, gp⟩ := renderWithProof T d hsafe
    output = render T d ∧ output ∈ (handlebarsToGrammar T).language
```

with `output ∈ language` obtained *from `gp.accepts`* via `compact_sound` — so the confinement property is a
**corollary of the emitted proof**, not a separate existence argument. "Injection impossible by construction"
means: the only way `renderWithProof` produces an output is with an accompanying accepting replay, and an
accepting replay *is* a proof of language membership = slot-confinement. There is no code path that emits an
output without the witness.

Honest scope (carrying §1 forward): this is *slot-confinement of the rendered structure*, and it inherits the
two named residuals of `Handlebars.lean` — the junction-breakout granularity (`Handlebars.lean:337`: a `{`
ending a hole abutting a `{` starting a literal forms a `{{` at the seam that `∈ language` still admits) and
the round-trip uniqueness caveat. The templater does **not** claim to defend an LLM prompt; it claims that
each render carries a machine-checkable certificate of how it was generated.

### 4.3 zk-compilation of the render proof

The `GenerationProof.rules` sequence is fed to the §3 grammar→circuit compiler's verifier for
`handlebarsToGrammar T`: the compact certificate is the exact witness `CfgVerifierKernel.verify ⟨g, output⟩`
consumes, and `injectionFree_of_verify` (`Handlebars.lean:308`) is the already-proven bridge that an accepting
in-circuit verification decides `injectionFree T output`. So the pipeline is:

```
  renderWithProof T d hsafe  ──►  (output, rules)
       │
       ▼   rules = the CfgCompact certificate
  CFG-verifier AIR for (handlebarsToGrammar T)     [§3 compiler; verifier = compact replay]
       │
       ▼   extractable STARK
  a portable proof "output was generated from T with data confined to holes"
       │  (verifiable exactly like a dregg-oracle ProofEnvelope leg)
       ▼
  RECEIPT
```

### 4.4 Composition — nested proof-carrying renders

The composition story is the reason this is a north star and not a gadget. If a hole `h` of `T` is filled not
by raw data but by the *output of another proof-carrying render* `renderWithProof T' d' hsafe' = ⟨output', gp'⟩`,
then:

- `output'` is a language member of `handlebarsToGrammar T'` (by `gp'`), which for a "safe data" sub-grammar
  means `output'` is `NoDoubleBrace`-confined, which is exactly the `safe T d` obligation at hole `h`. So the
  outer `renderWithProof` *consumes the inner proof as its safety hypothesis* — no re-checking.
- The outer certificate `gp.rules` and the inner `gp'.rules` **nest**: this is the CFG substitution operation
  (§3 completeness / the "hole whose data must be in `L2`" of the vision). The composed certificate is a
  single leftmost derivation over the substituted grammar, and its acceptance is the conjunction of the two
  replays glued at the hole.

This is *language composition* (a hole typed by a sub-grammar `L2`) proved at the certificate level: a
proof-carrying render nests inside another, and the resulting output carries a proof that is the composition
of the two. The regular layer already has boolean closure via `Crypto/Deriv/*` (complement/intersection); the
CFG layer gets substitution here. **The hard part is the substituted-grammar unambiguity** (§3.4 #2) needed
for the *unique* decoding of nested holes.

---

## 5. Primitive vs library — recommendation: **library-first**, with a named path to effect-hood

The question: should proof-producing render be a dregg **kernel primitive** (a verb/effect) or an
**SDK-level library/tool** (an attestation producer, like the oracle)? Both weighed:

### 5.1 The case against a primitive (strong)

- **The kernel is a *closed*, theorem-guarded set.** `metatheory/Dregg2/Substrate/VerbRegistry.lean` reifies
  exactly eight survivor verbs (`VerbRegistry.lean:7`, `:94`) with **two live theorems**: `completeness` (a
  wire variant that is not classified will not compile — the exhaustiveness check *is* the completeness proof,
  `VerbRegistry.lean:18`) and `minimality` (`verbProvides` exhibits, for each verb, a behavior no other verb
  provides; drop any one and that behavior is lost, `VerbRegistry.lean:41-43`). Adding a ninth verb is not an
  edit — it is a re-proof of minimality and completeness against a Rust ratchet
  (`turn/tests/verb_registry_gate.rs`, `VerbRegistry.lean:23`). Heavy, and probably *wrong*.
- **Rendering is a pure function, not a state mutation.** The eight verbs are each "the structural rule of
  exactly one substance's law" (`VerbRegistry.lean:70`) — they mutate owned state (create/write/move/grant/
  revoke/…). `render : T → data → output` mutates nothing; it *computes an output and a proof*. The kernel's
  own taxonomy has a home for exactly this: it is not a verb, it is *composition/receipt artifact*
  (`TurnStructure`, `VerbRegistry.lean:127`). A render-receipt is the kind of thing that is **produced by**
  exercising caps, not a new cap.
- **The doomed-family lesson.** `VerbRegistry.lean` records that whole verb families were *deleted* because
  their behavior was re-providable as "factory descriptor + Pred + survivor verbs" (`VerbRegistry.lean:147`,
  `:185`). A render primitive would almost certainly be re-provable the same way — which is the *definition*
  of something that should not be a kernel verb.

### 5.2 The case for a library (strong)

- **It has an exact, proven precedent: the oracle.** `dregg-oracle` produces a `ProofEnvelope` with named,
  independently-re-derivable legs (`authentic` / `well-formed` / `injection-free`, `dregg-oracle/src/lib.rs:173`)
  that "anyone can re-check" (`lib.rs:4`). A proof-producing templater is the *same shape*: `renderWithProof`
  emits `(output, certificate)`; the certificate is verified exactly like an oracle leg (through the *same*
  `cfg_verify_sound` STARK). It slots into the existing zkoracle machinery with **zero kernel change**.
- **It composes with what exists.** The certificate rides `CfgVerifierKernel` (`Cfg.lean:144`) and the
  `zkoracle-prove` Rust twins (`CfgCompact.lean:20`) — the library is "the oracle's injection-free leg, turned
  from a *checker* into a *producer*," reusing every downstream consumer.
- **It is where the composition story lives.** Nested proof-carrying renders (§4.4) are an SDK-level
  combinator, not a kernel operation.

### 5.3 Recommendation

**Build it as a library/tool first** — an SDK-level `renderWithProof` that emits attestations verifiable like
the oracle, composing with the existing `CfgVerifierKernel` / `zkoracle-prove` machinery and requiring **no**
change to the eight-verb kernel. This matches the codebase's own values: rendering is a pure function
(`TurnStructure`, not a verb), the kernel is minimality/completeness-locked, and the oracle already proves the
attestation-producer pattern works.

**Named path to effect-hood (do not foreclose it).** *If* a concrete use demands that a render-receipt become
part of *owned state a turn mutates* — e.g. a cell whose committed content must carry "this field was rendered
from template `T` with proof `π`" as an on-chain-checked invariant, not just an off-path attestation — then
the correct move is **not** a ninth verb but a **factory descriptor + Pred over survivor verbs** (the exact
mechanism `VerbRegistry.lean:147` documents for re-providing behavior without growing the kernel): a `write`
whose `Pred` requires an accepting CFG-verifier proof over `(handlebarsToGrammar T, content)`. That keeps the
kernel closed while giving render-receipts effect-level enforcement. The trigger for taking that path is a
real use that needs render-provenance *checked at commit time*, not merely *attestable*.

---

## 6. The first buildable slice (PROPOSED — smallest end-to-end thing)

**Slice: make `Handlebars.lean`'s render emit the `CfgCompact` witness, on the module that already exists.**

This is the smallest end-to-end proof-producing render because both ends are already built: `render_mem_language`
(`Handlebars.lean:283`) proves the derivation *exists*, and `CfgCompact.Replay`/`replay_derives`
(`CfgCompact.lean:48`/`67`) is the certificate format the STARK verifies. The slice *constructs* the specific
certificate and proves it accepts. No new circuit, no compiler, no kernel change.

**Exact next objects (all in a new `metatheory/Dregg2/Crypto/HandlebarsWitness.lean`, PROPOSED):**

1. **`renderRules : (T : HandlebarsTemplate) → (d : HoleId → List Tok) → List (ContextFreeRule Tok (handlebarsToGrammar T).NT)`**
   — the constructive leftmost rule sequence: the `startRule T` (`Handlebars.lean:167`) followed by, per
   segment, either nothing (literal — its terminals are matched by `Replay.term`) or the hole's `holeRules`
   (`Handlebars.lean:149`) sequence that spells out `d h` under the `safeD`/`safeB` recognizer. This is the
   *executable* version of the existence argument inside `safe_state_derives` (`Handlebars.lean:215`) and
   `body_derives` (`Handlebars.lean:257`).
2. **`renderRules_accepts : safe T d → CfgCompact.ReplayAccepts (handlebarsToGrammar T) (renderRules T d) (render T d)`**
   — the load-bearing new theorem: the constructed rule sequence *is* an accepting replay of the rendered
   output. Proof mirrors the existing `safe_state_derives` induction (`Handlebars.lean:215`), reusing its case
   structure (`safeD`/`safeB` states, the `brace`-after-`brace` impossibility) but building a `Replay` instead
   of a `Derives`. This is where the real work is, and it is bounded — the derivation already exists; the slice
   makes it a concrete `Replay` term.
3. **`renderWithProof`** (§4.1) — the packaging: `⟨render T d, ⟨renderRules T d, renderRules_accepts …⟩⟩`.
4. **`renderWithProof_sound`** — the corollary tying it to the existing property:
   `compact_sound (handlebarsToGrammar T) (renderRules T d) (render T d) (renderRules_accepts hsafe)` reproves
   `render T d ∈ (handlebarsToGrammar T).language` — i.e. **the emitted witness re-derives
   `render_mem_language` constructively**, closing the loop against the already-proven `Handlebars.lean:283`.
5. **Non-vacuity** — run it on the existing `Demo.greetT`/`greetD` (`Handlebars.lean:379`): exhibit
   `renderRules greetT greetD` as a concrete rule list and `#assert_axioms` the acceptance. This reuses the
   module's own live demo.

**Why this slice and not the compiler or the templater API first:** it de-risks the *witness construction*
(the one genuinely new proof) on the module that already has the grammar, the safety predicate, and the
existence proof — before any circuit emission (§3) or kernel/library packaging (§5). Once `renderRules_accepts`
closes, the render is proof-producing, and everything above it (the grammar→circuit compiler, composition,
the library surface) is wiring `CfgCompact` machinery that already ships.

---

## 7. The hard parts (consolidated, named, not papered)

1. **Completeness of the grammar→circuit compiler (⟸).** Soundness is free via `extractable` + `cfg_bridge`;
   "in-language ⟹ accepting compact replay the emitted AIR verifies" is real automata work
   (`CfgCompact.lean:23` explicitly leaves it to the Rust prover today). This is the largest general task.
2. **CFG unambiguity (mathlib has no API).** Needed for round-trip *uniqueness* (`Handlebars.lean:334`) — the
   unique decoding of a hole's data, and of nested holes under substitution (§4.4). Foundational.
3. **Junction breakout granularity.** Per-hole `NoDoubleBrace` admits a `{{` formed at a hole/literal seam
   (`Handlebars.lean:337`); `∈ language` captures in-slot confinement but not this byte-level seam. A sharper
   guarantee needs a junction-aware `safe` or a template class whose literals never abut hole braces. Real,
   recorded, not hidden.
4. **The witness-construction proof (`renderRules_accepts`, §6.2).** Bounded but non-trivial: building a
   concrete `Replay` term where only a `Derives` existence proof exists today.
5. **Bounded pushdown stack in the AIR encoding (§3.4 #4).** The refinement must hold within a depth budget.
6. **Checked decoding/witness maps (ψ, §3.4 #3).** The untrusted compiler's trace→parse-chain map must carry
   its own well-formedness obligation, or the trust boundary leaks — same discipline as `φ` in the layout
   optimizer.

---

### Cross-references (verified to exist at HEAD)

- `metatheory/Dregg2/Crypto/Handlebars.lean` (BUILT `d68fd6f8f`) — CFG-membership framing; `render_mem_language`
  (`:283`), `injectionFree_of_verify` (`:308`), residuals (`:319`).
- `metatheory/Dregg2/Crypto/SlotConfinement.lean` (BUILT; rehomed from `ZkHandlebars.lean` by `7396df797`) —
  `slot_confinement` (`:190`), the surviving narrow lemma, with `slot_confinement_count` (`:212`) and
  `attested_field_confined` (`:226`).
- `metatheory/Dregg2/Crypto/Cfg.lean` — `cfg_bridge` (`:113`, the floor), `CfgVerifierKernel` (`:144`),
  `cfg_verify_sound` (`:160`, the ceiling).
- `metatheory/Dregg2/Crypto/CfgCompact.lean` — `Replay` (`:48`), `replay_derives` (`:67`), `compact_sound`
  (`:81`), `compact_to_chain` (`:90`) — the certificate the templater emits.
- `metatheory/Dregg2/Crypto/Deriv/*` — the boolean-closed regular layer (complement/intersection).
- `dregg-dsl/src/gen_{air,plonky3,kimchi,sp1,midnight,datalog,rust}.rs` + `ir.rs` (`ConstraintIr`) — the
  existing multi-backend circuit compiler the grammar front-end REUSES.
- `docs/DESIGN-verified-layout-optimizer.md` — the translation-validation pattern this doc mirrors for grammars.
- `dregg-oracle/src/lib.rs` (`:9`, `:173`) — the attestation-producer precedent for the library recommendation.
- `deos-hermes/src/brain.rs:457` (`request_body`) — the structured-`messages` LLM path proving `{{`-injection
  is not a real surface.
- `metatheory/Dregg2/Substrate/VerbRegistry.lean` (`:41`, `:94`, `:147`) — the eight-verb kernel's
  minimality/completeness lock and the factory-route path to effect-hood.
