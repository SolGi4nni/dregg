import Lean

/-!
# Hygiene — axiom-footprint and vacuity assertions that CAN FAIL A BUILD

`#print axioms X` writes to the *info* stream. It is a diagnostic: it can never
fail `lake build`, so the 2,200-odd `#print axioms` invocations in this tree are
documentation, not a gate. Nothing stops a proof from silently acquiring a new
axiom dependency — the info message just changes, and nobody reads it.

This module supplies the assertions that DO fail a build:

* `#assert_axioms X ⊆ [g₁, g₂, …]` — `X`'s transitive axiom footprint (the exact
  set `#print axioms` prints, via the same `Lean.collectAxioms`) must be a subset
  of the named set. Anything outside it is a `throwError`.
* `#assert_axioms_exact X = [g₁, …]` — as above, plus every listed axiom must
  actually be *used*. This catches an over-broad advertisement (a theorem that
  says it leans on the crypto seam but does not), which `⊆` cannot.
* `#assert_nonvacuous X` — rejects a theorem whose statement has no content:
  `a = a`, `a ↔ a`, `HEq a a`, `True`, and the `∃ y, f x = y` restatement of
  function-hood. A statement of that shape holds for EVERY definition of the same
  arity, so a load-bearing NAME on one is a false advertisement.

`Hygiene.SelfTest` demonstrates each of these CATCHING a violation, with the
error text pinned by `#guard_msgs` — so if an assertion is ever weakened into a
no-op, the self-test goes red.

## Axiom sets

An entry in the bracketed list is either a **group name** from the table below
(resolved to literal `Name`s, so it may be written in a file that does not import
the group's home module) or a **constant name**, which is resolved against the
environment — a typo'd axiom name is an error, not a silently-widened allowance.

* `stdAxioms`  — `propext`, `Classical.choice`, `Quot.sound`. The Lean-standard
  three; a proof depending only on these is a proof in plain classical logic.
* `cryptoSeam` — the 25 `Crypto.Assumptions` / `Crypto.Xwing` axioms that shadow
  the `@[extern]` HACL*/EverCrypt (and aws-lc) primitives. These are the FFI
  trust boundary: each says "the C the shim calls behaves as its F*/audit spec
  says". Discharged OUTSIDE Lean, so a theorem carrying them is conditional on
  that external proof.
* `hashOracle` — `Cache.VaryKey.hash`, an uninterpreted digest oracle.
* `pqSeam` — the post-quantum / header-protection key-schedule assumptions
  (`TlsHandshake.tls_keyschedule_hybrid_dualPRF`, `QuicHeaderProt.chacha20Raw_valid`).

* `nativeDecide` — a SHAPE, not a list: Lean 4.30's `native_decide` mints a fresh
  per-declaration axiom `<thm>._native.native_decide.ax_1_1`, so no static group
  can name them. Listing `nativeDecide` admits exactly that shape. It is a loud
  declaration: the proof was closed by RUNNING COMPILED CODE, so the Lean
  compiler, the C toolchain and the evaluator are in its trusted base.
* `compilerAxioms` (`Lean.ofReduceBool` / `Lean.ofReduceNat` / `Lean.trustCompiler`)
  — the older shape of the same trust. Deliberately NOT folded into any other
  group.
-/

namespace Drorb.Hygiene

open Lean Elab Command

/-! ## The named axiom sets -/

/-- The three Lean-standard axioms. -/
def stdAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/-- The FFI crypto trust boundary: the `Crypto.Assumptions` / `Crypto.Xwing`
axioms shadowing the `@[extern]` HACL*/EverCrypt and aws-lc primitives. Written
as literal names so this module needs no import of `Crypto`. -/
def cryptoSeam : Array Name :=
  #[ `Crypto.Assumptions.chacha_open_seal_roundtrip
   , `Crypto.Assumptions.chacha_open_authentic
   , `Crypto.Assumptions.aesgcm_open_seal_roundtrip
   , `Crypto.Assumptions.aesgcm_open_authentic
   , `Crypto.Assumptions.aes_ecb_block_valid
   , `Crypto.Assumptions.x25519_dh_agree
   , `Crypto.Assumptions.crypto_box_open_seal_roundtrip
   , `Crypto.Assumptions.crypto_box_open_authentic
   , `Crypto.Assumptions.crypto_box_agree
   , `Crypto.Assumptions.ed25519_pubOf
   , `Crypto.Assumptions.ed25519_sign_verify_roundtrip
   , `Crypto.Assumptions.ecdsaP256Genuine
   , `Crypto.Assumptions.ecdsaP256Verify_authentic
   , `Crypto.Assumptions.rsaPssGenuine
   , `Crypto.Assumptions.rsaPssVerify_authentic
   , `Crypto.Assumptions.rsaPkcs1Genuine
   , `Crypto.Assumptions.rsaPkcs1Verify_authentic
   , `Crypto.Assumptions.sha256_len
   , `Crypto.Assumptions.sha384_len
   , `Crypto.Assumptions.mlDsaPubOf
   , `Crypto.Assumptions.mlDsaGenuine
   , `Crypto.Assumptions.mlDsaVerify_authentic
   , `Crypto.Xwing.xwing_kdf_dualPRF
   , `Crypto.Xwing.mlKemSource
   , `Crypto.Xwing.mlKem_ind_cca ]

/-- The uninterpreted digest oracle behind the Vary-key cache. -/
def hashOracle : Array Name := #[`Cache.VaryKey.hash]

/-- Post-quantum / header-protection key-schedule assumptions. -/
def pqSeam : Array Name :=
  #[ `TlsHandshake.tls_keyschedule_hybrid_dualPRF
   , `QuicHeaderProt.chacha20Raw_valid ]

/-- The classic Lean *compiler*-trusting axioms. Never folded into another
group: they widen the TCB to include the code generator. -/
def compilerAxioms : Array Name :=
  #[`Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler]

/-- The group table consulted by `#assert_axioms`. -/
def axiomGroups : List (Name × Array Name) :=
  [ (`stdAxioms, stdAxioms)
  , (`cryptoSeam, cryptoSeam)
  , (`hashOracle, hashOracle)
  , (`pqSeam, pqSeam)
  , (`compilerAxioms, compilerAxioms) ]

/-- `native_decide` in Lean 4.30 does not go through `Lean.ofReduceBool`: it
mints a FRESH per-declaration axiom, `<thm>._native.native_decide.ax_1_1`. Those
names cannot be enumerated in a static group, so the set name `nativeDecide` is
handled specially — it admits exactly this shape and nothing else.

Writing `nativeDecide` in an allowed set is a deliberate statement: *this proof
is closed by RUNNING COMPILED CODE*, so the Lean compiler, the C toolchain and
the evaluator are all in its trusted base. It is not the same claim as a
kernel-checked proof, and a set that lists it says so out loud. -/
def isNativeDecideAxiom (n : Name) : Bool :=
  ((toString n).splitOn "._native.native_decide.").length > 1

/-! ## `#assert_axioms` -/

/-- Resolve one bracketed entry: a group name expands to its members; anything
else must resolve to a real constant, so a typo cannot widen the allowance. -/
private def resolveEntry (id : Ident) : CommandElabM (Array Name) := do
  if id.getId == `nativeDecide then return #[]  -- handled by `allowNative`, below
  match axiomGroups.lookup id.getId with
  | some g => return g
  | none   => return #[← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id]

private def resolveSet (ids : Array Ident) : CommandElabM (Array Name) := do
  let mut out : Array Name := #[]
  for id in ids do
    out := out ++ (← resolveEntry id)
  return out

/-- Render a name set on ONE line. Deliberately a `String`, not `MessageData`:
the pretty-printer would wrap long lists at the terminal width, which makes the
error text width-dependent and `#guard_msgs` in `Hygiene.SelfTest` fragile. -/
private def fmtNames (ns : Array Name) : String :=
  "[" ++ String.intercalate ", " ((ns.qsort Name.lt).map toString).toList ++ "]"

/-- Shared checker. `exact? = true` additionally requires every allowed name to
be used. -/
private def checkAxioms (declId : Ident) (ids : Array Ident) (exact? : Bool) :
    CommandElabM Unit := do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo declId
  let allowNative := ids.any (·.getId == `nativeDecide)
  let allowed ← resolveSet ids
  let actual ← collectAxioms c
  let extra := actual.filter fun a =>
    !allowed.contains a && !(allowNative && isNativeDecideAxiom a)
  unless extra.isEmpty do
    throwError m!"axiom-footprint violation: '{c}' depends on {fmtNames extra}, \
which the declared set does not allow.\n  declared: {fmtNames allowed}\n  actual:   {fmtNames actual}"
  if exact? then
    let unused := allowed.filter (!actual.contains ·)
    unless unused.isEmpty do
      throwError m!"axiom-footprint over-declaration: '{c}' does NOT depend on \
{fmtNames unused}, but the exact set claims it does.\n  actual: {fmtNames actual}"
    if allowNative && !actual.any isNativeDecideAxiom then
      throwError m!"axiom-footprint over-declaration: '{c}' does NOT use \
`native_decide`, but the exact set claims it does.\n  actual: {fmtNames actual}"
  logInfo m!"'{c}' axiom footprint OK: {fmtNames actual}"

/-- `#assert_axioms X ⊆ [stdAxioms, cryptoSeam, …]` — fail the build if `X`'s
transitive axiom footprint escapes the declared set. -/
syntax (name := assertAxiomsCmd)
  "#assert_axioms " ident " ⊆ " "[" ident,* "]" : command

/-- `#assert_axioms_exact X = [ … ]` — as `⊆`, and additionally reject an
over-broad declaration (listed-but-unused axioms). -/
syntax (name := assertAxiomsExactCmd)
  "#assert_axioms_exact " ident " = " "[" ident,* "]" : command

@[command_elab assertAxiomsCmd]
def elabAssertAxioms : CommandElab := fun stx => do
  match stx with
  | `(#assert_axioms $c:ident ⊆ [$ids,*]) => checkAxioms c ids.getElems false
  | _ => throwUnsupportedSyntax

@[command_elab assertAxiomsExactCmd]
def elabAssertAxiomsExact : CommandElab := fun stx => do
  match stx with
  | `(#assert_axioms_exact $c:ident = [$ids,*]) => checkAxioms c ids.getElems true
  | _ => throwUnsupportedSyntax

/-! ## `#assert_nonvacuous` -/

/-- Classify a *conclusion* (the body under a `∀`-telescope) as content-free, and
say why. Every shape here holds for ANY function of the right arity, so it
constrains the named definition not at all. -/
private def vacuityReason? (body : Expr) : MetaM (Option String) := do
  if body.isConstOf ``True then
    return some "conclusion is `True`"
  if let some (_, a, b) := body.eq? then
    if a == b then return some "conclusion is `a = a` (reflexivity - holds for every function)"
  if let some (a, b) := body.iff? then
    if a == b then return some "conclusion is `a <-> a`"
  if let some (_, a, _, b) := body.heq? then
    if a == b then return some "conclusion is `HEq a a`"
  -- `∃ y, f x = y` / `∃ y, y = f x`: function-hood restated. Holds for every `f`.
  if body.isAppOfArity ``Exists 2 then
    let p := body.appArg!
    if p.isLambda then
      return ← Meta.lambdaTelescope p fun xs inner => do
        if h : xs.size = 1 then
          let x := xs[0]
          if let some (_, a, b) := inner.eq? then
            let xId := x.fvarId!
            if (b == x && !a.containsFVar xId) || (a == x && !b.containsFVar xId) then
              return some "conclusion is `exists y, f .. = y` (function-hood restated - holds for every function)"
        return none
  return none

/-- `#assert_nonvacuous X` — fail the build if `X`'s STATEMENT is content-free.

Deliberately syntactic: it compares the two sides of the conclusion up to
structural equality, not definitional equality. A `rfl`-proved theorem whose
sides differ syntactically (`serialize resp = statusLine ++ …`) is real content
and passes; only `a = a` and friends are rejected. -/
syntax (name := assertNonvacuousCmd) "#assert_nonvacuous " ident : command

@[command_elab assertNonvacuousCmd]
def elabAssertNonvacuous : CommandElab := fun stx => do
  match stx with
  | `(#assert_nonvacuous $c:ident) => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
    let info ← getConstInfo n
    let reason? ← liftTermElabM <|
      Meta.forallTelescope info.type fun _ body => vacuityReason? body
    match reason? with
    | some why =>
      throwError m!"vacuous statement: '{n}' - {why}. A theorem of this shape holds for \
EVERY definition of the same arity, so the name advertises a property the statement does \
not carry. Prove the real property or delete it."
    | none => logInfo m!"'{n}' is not vacuous"
  | _ => throwUnsupportedSyntax

end Drorb.Hygiene
