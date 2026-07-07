# C18 REPORT — the loop-free descent automation covers a BATCH of DEPLOYED serve-stage decisions, and one HONEST map of what remains to the whole serve

Three more REAL, deployed decision cores from `Reactor.Deploy.deployStagesFull2`
(the drorb orb serve) each close their full spec→machine-code descent with a
**one-line** bespoke core proof — `[oracles: DISK_THM] [axioms: ]`, 0 axioms,
0 cheats, `hyps = 0`, kernel-checked, green on hbox. Together with C17's redirect
fragment the front-end now covers the serve's **scalar branch-decision class** at
three of the four guard kinds the Pancake parser emits (`=`, `<`, `<=`/`>=`); the
one guard kind real serve needed beyond C17 (`<=`/`>=` = `Cmp NotLess`) is closed
by a small program-agnostic companion added **once**. The rest of this report is
the honest map: which deployed computations are loop-free-covered, which are
**fold-over-list** (the C16 fold-loop schema's target), and which are general
loops.

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**HOL4 Trindemossen-2 stdknl, CakeML `ed31510b3`** — the exact tree C1–C17 used.
**Dir:** `docs/engine/probes/compiler/hol-c18/` (built on hbox `~/hol-c18`, all
theories `OK`). Sibling agents own `hol-c16` (fold-loop) and `hol-c17` (done); C18
stays out of both.

---

## 0. What this probe answers

C17 asked *does the loop-free automation reach the deployed serve?* and closed
ONE real fragment (`Redirect.Code.status`, an `=`-dispatch). C18 asks the breadth
question: **descend a BATCH of other loop-free decision functions from the real
`deployStagesFull2` stages, and honestly map what remains.** It closes three more
(cache freshness, rate-limit admit, ASCII case-class), discovers the ONE new guard
kind real serve code needs (`<=`/`>=`), closes it with a reusable companion, and
draws the loop-free-vs-fold-loop line across all fourteen deployed stages.

## 1. THE three fragments — real, deployed, genuinely loop-free

Each is a decision core of a stage that sits in `Reactor.Deploy.deployStagesFull2`
(`Reactor/Deploy.lean:1496`), is total, and has no recursion / no `While`. Each is
encoded exactly as C17's redirect fragment was — one input word staged by
`@load_vec`, the decision word reported by `@report_vec` — so the whole
wrapper/Sem/Install/EndToEnd/LinkB chain transferred **verbatim** (N=1 read, +8w
store), the per-fragment residual being the spec, the parser-dumped core `Def`, and
a one-line tactic call.

| # | fragment (drorb source) | deployed via | decision | guard kind |
|---|---|---|---|---|
| 1 | `Cache.Meta.isFresh` (`Cache.lean`) | `cacheEmptyStage`, stage 4 | `if age < lifetime then fresh(1) else stale(0)` | `<` (`Cmp Less`) |
| 2 | `Rate.tryAdmit` (`Rate/Bucket.lean`) | `rateStage`, stage 3 | `if 1 <= tokens then admit(1) else reject(0)` | `<=` (`Cmp NotLess`) |
| 3 | `Gzip.lowerByte` uppercase test (`Reactor/Stage/Gzip.lean`) | `gzipStage`, stage 10 (+ CORS/header byte-canonicalization) | `if 65 <= b && b <= 90 then 1 else 0` | `<=` cascade, **both operand orientations** |

- **Fragment 1 — `Cache.Meta.isFresh`.** The RFC 9111 §4.2 freshness gate
  `response_is_fresh = (freshness_lifetime > current_age)`, consulted by
  `Reactor.Stage.Cache.Config.onReq` (line 56-57, `if e.meta.isFresh cfg.now`).
  Loop-free: a single `<` on the resolved age vs the stored lifetime. Modeled at
  the deployed freshness lifetime (100); `age` is the one runtime input.
- **Fragment 2 — `Rate.tryAdmit`.** The token-bucket admit decision
  `if 1 <= b.tokens then (admit,true) else (reject,false)`, consulted by
  `Reactor.Stage.Rate.admits` (line 106-107). Loop-free: a single `<=` on the
  post-`refill` token count.
- **Fragment 3 — `Gzip.lowerByte`'s uppercase test.** `lowerByte b =
  if 65 <= b && b <= 90 then b+32 else b` (line 37-38) is the per-byte ASCII
  case-fold used by `Gzip.lower` — the header canonicalization the deployed serve
  runs in `Gzip.acceptsGzip` and the CORS canonical-origin path. Its loop-free
  DECISION core (is `b` an uppercase letter — whether to subtract 32) is a nested
  cascade of two `<=` guards.

## 2. THE three closed theorems

Each headline theorem (verbatim shape, e.g. `rateAdmitEndToEnd$rateAdmit_machine_code`):

```
[oracles: DISK_THM] [axioms: ]
⊢ ( … the standard CakeML machine-state install package, taken VERBATIM from
     <frag>Prog_linkB's antecedent … ) ∧ rateAdmitFFI code s ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (rateAdmit code)) F) rb])}
```

**Reading it:** under the standard install package and the single FFI-oracle
contract, every observable behaviour of the installed x64 machine code emitted for
the fragment is the single terminating trace whose reported word is exactly the
drorb Lean spec applied to the input — `n2w (Cache.Meta.isFresh …)`,
`n2w (Rate.tryAdmit … .2)`, `n2w (Gzip.lowerByte-uppercase …)` respectively.

**Machine-checked audit** (`verify<Frag>Script.sml`), all three:

| theorem | oracles | axioms | hyps |
|---|---|---|---|
| `cacheFresh_machine_code` | `[DISK_THM]` | `[]` | 0 |
| `rateAdmit_machine_code`  | `[DISK_THM]` | `[]` | 0 |
| `gzipUpper_machine_code`  | `[DISK_THM]` | `[]` | 0 |

`DISK_THM` is the benign disk-export tag on every CakeML theory — no `cheat`, no
`mk_thm`, no axiom, identical trust footing to C11–C17.

**leanc is OUT of the TCB.** Each `<Frag>Prog` is the VERIFIED parser's output on
the emitted bytes (`<Frag>Prog_is_parser_output`, `oracles=[DISK_THM] axioms=[]`).
The core `Def`s were transcribed from the parser AST dump (`dumpScript.sml`,
`Cmp Less (Var «age») (Const 100w)`, `Cmp NotLess (Var «tokens») (Const 1w)`,
`Cmp NotLess (Var «b») (Const 65w)` + `Cmp NotLess (Const 90w) (Var «b»)`) — no
hand-invention; the wrapper's ML `Term.subst` fires against the parser body.

## 3. The bespoke per-fragment proof — 1 line each

The Link-A decision core of each fragment is a single reusable-tactic call:

```
Theorem evaluate_cacheFreshCore: … Proof panLinkA_branch    (…) [“age < 100n”]              QED  (* C15 tactic, UNCHANGED *)
Theorem evaluate_rateAdmitCore:  … Proof panLinkA_branch_le (…) [“1 <= tks”]                QED  (* C18 tactic *)
Theorem evaluate_gzipUpperCore:  … Proof panLinkA_branch_le (…) [“65 <= b”, “b <= 90”]      QED  (* C18 tactic *)
```

`[oracles: DISK_THM] [axioms: ]`. **Zero bespoke tactic steps** — the only
per-fragment inputs are the three definitional theorems and the finite guard list.

| primitive | shape | bespoke Link-A core proof |
|---|---|---:|
| C13 `boundScan` | bounds + scan-`While` | ~629 lines |
| C14 `step` | 2-guard nested `If` | ~55 lines |
| C15 `statusClass` (toy) | 4-guard `<` cascade | ~2 lines |
| C17 `Redirect.Code.status` | 3-guard `=` dispatch | ~2 lines |
| **C18 `Cache.Meta.isFresh`** | 1-guard `<` | **1 line** (`panLinkA_branch`) |
| **C18 `Rate.tryAdmit`** | 1-guard `<=` | **1 line** (`panLinkA_branch_le`) |
| **C18 `Gzip.lowerByte` upper** | 2-guard `<=` cascade | **1 line** (`panLinkA_branch_le`) |

## 4. Guard-kind coverage — the ONE new kind real serve needed

The Pancake parser (`panPtreeConversion`, lines 176-181) lowers the four scalar
comparison operators to exactly three `asm$word_cmp` guards:

| Lean/source | parser emits | `word_cmp` | machinery |
|---|---|---|---|
| `==` | `Cmp Equal e1 e2` | `w1 = w2` | C17 `eval_eq_pinned` |
| `<` | `Cmp Less e1 e2` | `w1 < w2` | C15 `eval_lt_pinned` |
| `>=` | `Cmp NotLess e1 e2` | `~(w1 < w2)` | **C18 `eval_ge_pinned`** (var-left) |
| `<=` | `Cmp NotLess e2 e1` | `~(w1 < w2)` | **C18 `eval_ge_pinned_rhs`** (var-right) |
| `>`  | `Cmp Less e2 e1` | `w1 < w2` | C15 `eval_lt_pinned` (swapped) |

- **`<` reaches real serve VERBATIM (fragment 1).** C15's ordered-`<` cascade
  machinery — built and only ever exercised on a TOY classifier — descends the
  real `Cache.Meta.isFresh` with **zero new metatheory**: the same
  `panLinkA_branch` tactic, one guard. (C17 showed the same for `=`.)
- **`<=`/`>=` (`Cmp NotLess`) is the ONE genuinely new guard kind real serve needs
  (fragments 2, 3).** A numeric threshold (`1 <= tokens`) and an ASCII range
  (`65 <= b && b <= 90`) both lower to `Cmp NotLess`, which C15's `Less`-only and
  C17's `Equal`-only lemmas do not cover. The whole delta, added **once** and
  reusable for every future threshold/range serve fragment:
  - `panAutoScript.sml` (+2 program-agnostic theorems): `eval_ge_pinned` (the
    generic `Cmp NotLess` guard-evaluator, variable-on-left) and
    `eval_ge_pinned_rhs` (variable-on-right — the `<=` upper-bound orientation the
    parser emits, e.g. `b <= 90` → `Cmp NotLess 90 b`).
  - `panAutoLib.sml` (+1 ML tactic): `panLinkA_branch_le` — byte-for-byte
    `panLinkA_branch` with the guard kind swapped and the operand orientation read
    off which side is the pinned local. Everything else (`evaluate_If_reduce`,
    `cond1w_ne0`, `Annot_Seq_eval`, `evaluate_Assign_const`, the finite leaf
    case-split) is guard-agnostic and reused unchanged.
  This is **~90 lines of reusable metatheory added once**. Fragment 3 needed both
  operand orientations of the same guard (var-left `65 <= b`, var-right `b <= 90`)
  — no further additions.

After the `NotLess` companion, the front-end covers **the full set of scalar
comparison dispatches the parser emits** (`=`, `<`, `<=`, `>=`, `>`). The
wrapper/Sem/Install/EndToEnd/LinkB chain and `mk_linkB` transferred with **zero
proof changes** (only mechanical renames + the input-local name), exactly as C17.

## 5. The honest map — loop-free-covered vs fold-loop vs general-loop across `deployStagesFull2`

The deployed serve is fourteen stages. Classifying each stage's decision core by
what schema its descent needs:

### LOOP-FREE, scalar branch — COVERED end-to-end (C15/C17/C18)
| stage | decision core | guard | probe |
|---|---|---|---|
| `redirectStage` (5) | `Redirect.Code.status` — RFC redirect-status pick | `=` | C17 |
| `cacheEmptyStage` (4) | `Cache.Meta.isFresh` — §4.2 freshness | `<` | **C18** |
| `rateStage` (3) | `Rate.tryAdmit` — token-bucket admit bit | `<=` | **C18** |
| `gzipStage` (10) | `Gzip.lowerByte` — per-byte ASCII case-class | `<=` cascade | **C18** |

This is the whole scalar branch-decision class the deployed serve contains: the
numeric-threshold gate cores (rate limit, cache age) and the enum/range
classifications (redirect status, ASCII case). Each is now
spec→machine-code with a one-line proof.

### FOLD-OVER-LIST — needs the C16 fold-loop schema (a bounded fold over a header/byte/token list; the per-element decision is often already C18-covered)
- `gzipStage` `acceptsGzip`: `headers.any (…isInfix "gzip"…)` — fold over the
  header list **and** an infix scan of each value; `Gzip.lower`: `map lowerByte`
  — a fold whose per-element decision **is** the C18 fragment-3 core.
- `deployCorsStage` `Cors.acaoValue` → `originAllowed`: `allowedOrigins.contains o`
  — fold over the allowlist, each step a `String` (byte-list) equality.
- `headerStage` hop-strip: `filter` over headers + `isHopByHop` name-set membership
  (byte-string compares); `securityheadersStage` / `headerRewriteStage`
  (`Header.run`): folds building/rewriting the header list.
- `cacheEmptyStage` `Store.get?` (`find?` over entries) and `keyOf`/`hashBytes`
  (`foldl` over the key bytes); `rateStage` `seqOf` (`length` over the seq bytes).
- `htmlrewriteStage`, `basicStage` (credential byte-compare), `jwtAdminStage`
  `isAdminPath`/`isPrefixB` (structural recursion over the target bytes).

### GENERAL LOOP — needs a general `While` / the parse scan
- The HTTP/1.1 arena **parse scan** (`ctxOf` → request parse): the `boundScan`
  `While` — already closed as a primitive in **C13**.
- `ipfilterStage` `IpFilter.permits`: deny-precedence walk over the ruleset with a
  per-rule CIDR prefix bit-match (a fold-of-fold).
- `traversalStage` `targetEscapes`/`escapesSegs`: split the target into segments,
  then `any` a `..` segment (scan + fold); `policyStage`
  `policyReserved`/`deployDecisionOf`: walk the declared surfaces + a dotfile
  prefix test.
- `jwtAdminStage` `Jwt.authenticate` (the bearer FSM); `gzipStage`
  `Gzip.gzipStored` (the DEFLATE compressor).

**The line.** What sits between here and the WHOLE serve is almost entirely
**fold-over-list** computation — every header/byte/token/origin/surface traversal
— plus a small set of genuinely general loops (the parse `While` [C13-closed], the
DEFLATE compressor, the JWT FSM, the CIDR/ruleset walk). The scalar branch
decisions are done; the next lever is the C16 fold-loop schema, and several
fold bodies (e.g. `Gzip.lower`'s per-byte case-class) are already C18-covered
cores that the fold would wrap.

## 6. Line ledger

| component | lines | kind |
|---|---:|---|
| bespoke core `Proof` (each fragment) | **1** | per-fragment (library-tactic call) |
| `NotLess` companion (`eval_ge_pinned` + `eval_ge_pinned_rhs` + `panLinkA_branch_le`) | ~90 | **reusable, added ONCE** (new guard kind) |
| `panAuto` + `panAutoLib` + `c14Generic` (C15/C17 machinery) | ~650 | **reusable, carried with ZERO new proof** |
| per-fragment spec + parser-dumped core `Def` + relation | ~50 each | declarations (irreducible inputs) |
| wrapper / Sem / Install / EndToEnd / LinkB templates | ~478 each | template, prefix + input-local rename only |

Genuinely **bespoke per-fragment proof residual: 1 line** (the core `Proof`). The
per-fragment work is declarations + the two-parameter template edit (read-count
N=1, result offset +8w) — identical to C15/C17, so free.

## 7. Files (`docs/engine/probes/compiler/hol-c18/`)

- `panAutoScript.sml` — REUSABLE program-agnostic theory; **C18 adds
  `eval_ge_pinned`, `eval_ge_pinned_rhs`** (the `<=`/`>=` `Cmp NotLess`
  companions, both operand orientations).
- `panAutoLib.sml` — REUSABLE automation; **C18 adds `panLinkA_branch_le`** (the
  threshold-guard Link-A tactic). `panLinkA_branch` / `panLinkA_branch_eq` /
  `mk_linkB` unchanged.
- `c14GenericScript.sml` — program-agnostic descent machinery, byte-identical to
  C15/C17.
- `cachefresh.pnk` / `rateadmit.pnk` / `gzipupper.pnk` — the emitted decision cores
  (leanc's artifact; the verified parser's input).
- `<Frag>CoreScript.sml` — spec (`= drorb Lean fn`), verbatim core `Def` (dumped
  from the parser), relation, `evaluate_<Frag>Core` **by the one-line tactic**.
- `<Frag>{Wrapper,MainRefine,Sem,Install,LinkBInst,EndToEnd}Script.sml` — the
  guard-agnostic templates (N=1, +8w), transferred verbatim from C17.
- `verify<Frag>Script.sml` — the machine-checked oracle/axiom audit.
- `dumpScript.sml` — scaffolding: parses each `.pnk` with the verified parser and
  prints `functions <prog>` (provenance for the transcribed cores; not in the trust
  chain).
- `Holmakefile` — includes the CakeML pancake/backend/proofs dirs;
  `CAKEMLDIR=~/src/cakeml`.

## 8. Verdict

- **How many real serve-stage decisions now auto-descend spec→machine-code?**
  **Four** (C17 redirect + C18 cache-fresh, rate-admit, gzip-uppercase), each
  `[oracles: DISK_THM] [axioms: ]`, 0 axioms, 0 cheats, `hyps=0`, green on hbox.
  Bespoke hand-proof per fragment: **1 line**.
- **Any new guard kinds real serve needed?** **One:** `<=`/`>=` = `Cmp NotLess`
  (numeric threshold `1 <= tokens`, ASCII range `65 <= b && b <= 90`), closed by a
  ~90-line program-agnostic companion (`eval_ge_pinned` + `eval_ge_pinned_rhs` +
  `panLinkA_branch_le`) added ONCE. The front-end now covers the full scalar
  comparison-dispatch set the parser emits (`=`, `<`, `<=`, `>=`, `>`).
- **The honest remaining map:** the deployed serve's loop-free scalar branch
  decisions are DONE. What remains to the WHOLE serve is fold-over-list computation
  (every header/byte/token/origin/surface traversal — the C16 fold-loop schema's
  target, some of whose fold-bodies are already C18-covered) plus a handful of
  general loops (the parse `While` [C13-closed], the DEFLATE compressor, the JWT
  FSM, the CIDR/ruleset walk).
