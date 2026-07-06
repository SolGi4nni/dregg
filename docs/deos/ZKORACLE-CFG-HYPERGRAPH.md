# zkOracle — verified CFG parsing, composed with DECO/zkTLS, generalized to hypergraph reductions

This subsystem attests that an API request (to Anthropic, or any TLS endpoint) is simultaneously
**authentic**, **well-formed**, and **injection-free** — each a formally-verified, kernel-clean
(`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}`) discharge — and then observes that the
certificate machinery underneath is a special case of *arbitrary hypergraph reduction*.

Three files, `metatheory/Dregg2/Crypto/{Cfg,ZkOracle,Hypergraph}.lean`, wired into `Dregg2.lean`.

## 1. `Crypto/Cfg` — the CFG parse-certificate kernel (nested structure the DFA cannot express)

The DFA cascade (`Crypto/Dfa`, `Crypto/Deriv/*`) certifies REGULAR structure. It provably cannot
certify balanced/nested structure (arbitrary bracket depth) — exactly what a JSON payload needs. `Cfg`
lifts the "prover supplies a locally-checkable certificate; verifier checks each step; bridge says
certificate ⟺ language" pattern to context-free grammars.

- **Spec** = mathlib's verified `ContextFreeGrammar` (`Produces`/`Derives`/`language`/`mem_language_iff`),
  read as the trusted denotational language exactly as `Crypto/Dfa` leans on mathlib's automata.
- **Certificate** (home-grown) = a **derivation form-chain** `producesChain`: the sentential forms
  `[initial] ⟶ … ⟶ input`, each consecutive pair a single-rule `Produces`. The CF analogue of
  `Dfa.lean`'s `DfaAccepts` run.
- `cfg_bridge : (∃ chain, CfgAccepts g input chain) ↔ input ∈ g.language`.
- `CfgVerifierKernel` + `cfg_verify_sound` (accept ⇒ `input ∈ g.language`, derived off the bridge + the
  STARK `extractable` carrier — the only crypto residue).
- Non-vacuity: the Dyck grammar `S → [ S ] | ε` (context-free but NOT regular) with a genuine parse of
  `[]` landed in the language via the bridge.

## 2. `Crypto/ZkOracle` — the capstone: authentic ∧ well-formed ∧ injection-free

`zkOracle_sound` composes three verified cones into one attestation about a request:

| Property | Cone | Discharge |
|---|---|---|
| **authentic** | `Crypto/Deco` (DECO/zkTLS) | `deco_verify_sound`: server key signed the session key, transcript MAC'd under it, opens to the encoded facts |
| **well-formed** | `Crypto/Cfg` | `cfg_verify_sound`: the body lies in a JSON context-free language (nested structure) |
| **injection-free** | `Crypto/Deriv` | the user field UNMATCHES a handlebars template = matches the NATIVE VERIFIED COMPLEMENT `neg` (dregg's boolean-closed derivative matcher) |

The anti-injection leg is the distinctive part: "the input *unmatches* the template" is stated directly
as a match against `neg injectionTemplate` ("contains no handlebars delimiter `{{`"). No regex engine
*without verified complement* can state this — dregg's `neg` (discharged through the derivative
determinizer, `Crypto/Deriv/Powerset`) makes it a theorem.

**Runnable demo** (`#eval`, executed at build): the benign field `"hi"` matches `neg template` → `true`
(ACCEPTED); the malicious field `"{{x"` does not → `false` (REJECTED — the guard refusing a prompt
injection). Plus `nested_well_formed`: a doubly-nested `[[str]]` is well-formed JSON via an explicit
parse certificate.

The whole capstone reduces to the two STARK `extractable` carriers + the §8 crypto floor DECO already
names (ed25519 EUF-CMA, HMAC, Poseidon2 CR) + the external Web-PKI/honest-endpoint floor.

## 3. `Crypto/Hypergraph` — arbitrary hypergraph reductions (the generalization)

The CFG chain↔`Derives` proof is not about grammars at all — it is generic over ANY reduction relation:

    bridge (R : α → α → Prop) (start goal) :
        (∃ c, Cert R start goal c) ↔ Relation.ReflTransGen R start goal

A locally-checkable chain certificate exists IFF `start` reduces to `goal` in the reflexive-transitive
closure. That *is* a proof of an arbitrary reduction. Two instantiations:

- `hypergraph_reduction_bridge` — `R := Reduces rule`, hyperedge replacement on `Hypergraph L V`
  (`⟨pre ++ e :: post⟩ ↝ ⟨pre ++ rhs ++ post⟩` when `rule e rhs`). ZK-checkable certificates for
  arbitrary hypergraph reductions. Concrete witness `red_reduces` (`A[0,1] ↝ {B[0,1], C[0,1]}`).
- `cfg_parse_via_reduction` — `R := g.Produces` recovers CFG parsing (`input ∈ g.language`). Context-free
  parsing is the linear/string instance of hypergraph reduction: **one verified certificate framework
  covers both.**

## 4. `Crypto/GraphRewrite` — full graph rewriting over arbitrary bytes (matchings included)

`Hypergraph.Reduces` is only *positional* edge splicing. Full graph rewriting adds a genuine **match** and
runs over arbitrary node/label carriers `V`/`L` (instantiate at `UInt8` for byte graphs):

- **matching** — `IsHom f pat host` (a node map sending every pattern edge to a host edge); `Matches`
  (a homomorphism exists) and `Embeds` (an injective one = subgraph isomorphism onto its image). This is
  graph pattern matching / subgraph matching as a first-class relation over arbitrary bytes.
- **rules + steps** — `Rule Var L = ⟨lhs, rhs⟩` over pattern variables; `RewriteStep rules G H` is the
  double-pushout step: a rule, a MATCH `σ : Var → V` embedding `lhs` into `G`, a preserved CONTEXT, with
  `G.edges ~ ctx ++ σ·lhs` and `H.edges = ctx ++ σ·rhs` (match, delete, glue).
- `graphRewrite_bridge` = the generic `bridge` at `RewriteStep rules` — ZK-checkable certificates for
  ARBITRARY graph-rewriting derivations. `step_matches` proves every rewrite step is witnessed by a graph
  matching, so rewriting is inseparable from matching. Concrete `UInt8`-byte witnesses: `patA_matches_host`
  (a subgraph match), `g0_rewrites_g1` (a match-driven step), `g0_reduces_g1` (the reduction, certified).

Because a rule encodes any local graph transformation and `bridge` closes it reflexive-transitively, this
expresses **arbitrary relations on arbitrary byte-labeled graphs** — with graph matching as the primitive.

## Trust base

STARK `extractable` (per leg) + the §8 primitives (ed25519 / HMAC / Poseidon2) + the external
Web-PKI/honest-endpoint floor. The CFG spec adds mathlib's `ContextFreeGrammar.language` definition (a
transparent, inspectable denotational spec, already in the trust story via `Crypto/Deriv/Thompson`'s
mathlib-automata dependence). Nothing implementation-specific survives as a Lean assumption.

## Open extensions

- A reference `CfgVerifierKernel` faces the same decidability obstacle as `Dfa`'s (deciding `CfgAccepts`
  against an arbitrary grammar) — a decidable-rule refactor, not the generic cascade (already proved).
- Binding the SAME body across legs (the Fiat–Shamir shared commitment: DECO's `encode facts` = the
  CFG input's Poseidon2 commitment) is currently an explicit hypothesis; a deployed circuit threads it
  as a shared witness.
- Compact (non-quadratic) parse certificates (the linear CFG-parsing scheme, IACR 2024/562) are an
  efficiency refinement over the form-chain — correctness-first here.
