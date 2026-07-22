/-
# Dregg2.Logic.CompilationCertificateBundle

A small, fail-closed reference checker for a future extracted checker.

This file does **not** claim a CakeML implementation.  It fixes the object that
such an implementation would have to refine: a source Boolean formula, a
separate target gate tree, a versioned compilation certificate, a deterministic
checker, and a canonical prefix byte encoding.  The checker accepts exactly
when the version is known and the target is the canonical lowering of the
source.  Its main theorem turns that syntactic check into source/target semantic
equivalence.

The wire model uses `Nat` as an abstract byte and rejects any value outside
`[0, 255]`.  Both source and target terms use disjoint prefix tags, so parsing is
self-delimiting.  Unknown versions, unknown tags, malformed terms, and trailing
bytes all fail closed.

Standalone additive artifact: no central import is changed.
-/

import Dregg2.Tactics

namespace Dregg2.Logic.CompilationCertificateBundle

/-! ## 1. Source, independent target, and semantics -/

/-- The source language is kept first-order and finitary so the reference parser
and checker have no hidden elaborator dependency. -/
inductive Source where
  | atom (name : Nat)
  | top
  | bot
  | not (p : Source)
  | and (p q : Source)
  | or (p q : Source)
  deriving Repr, DecidableEq

/-- A deliberately small target graph language.  It is independent of the
source syntax even though the canonical compiler is structurally direct. -/
inductive Target where
  | input (atom : Nat)
  | truth
  | falsity
  | inv (a : Target)
  | conj (a b : Target)
  | disj (a b : Target)
  deriving Repr, DecidableEq

def Source.eval (env : Nat -> Bool) : Source -> Bool
  | .atom a => env a
  | .top => true
  | .bot => false
  | .not p => !(Source.eval env p)
  | .and p q => Source.eval env p && Source.eval env q
  | .or p q => Source.eval env p || Source.eval env q

def Target.eval (env : Nat -> Bool) : Target -> Bool
  | .input a => env a
  | .truth => true
  | .falsity => false
  | .inv a => !(Target.eval env a)
  | .conj a b => Target.eval env a && Target.eval env b
  | .disj a b => Target.eval env a || Target.eval env b

/-- The one canonical source-to-target lowering checked by this version. -/
def lower : Source -> Target
  | .atom a => .input a
  | .top => .truth
  | .bot => .falsity
  | .not p => .inv (lower p)
  | .and p q => .conj (lower p) (lower q)
  | .or p q => .disj (lower p) (lower q)

theorem lower_correct (env : Nat -> Bool) (source : Source) :
    Target.eval env (lower source) = Source.eval env source := by
  induction source <;> simp [lower, Target.eval, Source.eval, *]

/-! ## 2. Versioned certificate and deterministic reference checker -/

def currentVersion : Nat := 1

/-- A compilation certificate binds the claimed target to its source and wire
version.  Future versions may carry richer witnesses without silently changing
the meaning of version 1. -/
structure Bundle where
  version : Nat
  source : Source
  target : Target
  deriving Repr, DecidableEq

/-- Boolean equality check suitable for direct reimplementation by a small
first-order checker.  No proof object is trusted. -/
def check (bundle : Bundle) : Bool :=
  decide (bundle.version = currentVersion) &&
    decide (bundle.target = lower bundle.source)

/-- The unique certificate emitted for a source by version 1. -/
def certify (source : Source) : Bundle where
  version := currentVersion
  source := source
  target := lower source

theorem check_certify (source : Source) : check (certify source) = true := by
  simp [check, certify]

theorem check_known_version {bundle : Bundle} (hcheck : check bundle = true) :
    bundle.version = currentVersion := by
  have hall : bundle.version = currentVersion /\
      bundle.target = lower bundle.source := by
    simpa [check] using hcheck
  exact hall.1

theorem check_target_canonical {bundle : Bundle} (hcheck : check bundle = true) :
    bundle.target = lower bundle.source := by
  have hall : bundle.version = currentVersion /\
      bundle.target = lower bundle.source := by
    simpa [check] using hcheck
  exact hall.2

/-- An accepted certificate relates semantically equivalent source and target
programs for every atom environment. -/
theorem check_sound {bundle : Bundle} (hcheck : check bundle = true) :
    forall env, Target.eval env bundle.target = Source.eval env bundle.source := by
  have htarget := check_target_canonical hcheck
  intro env
  rw [htarget]
  exact lower_correct env bundle.source

theorem check_rejects_unknown_version {bundle : Bundle}
    (hversion : bundle.version ≠ currentVersion) : check bundle = false := by
  simp [check, hversion]

/-! ## 3. Canonical abstract-byte wire format -/

abbrev Byte := Nat

def bytesValid (bytes : List Byte) : Bool :=
  bytes.all fun byte => byte < 256

def magic : List Byte := [68, 82, 69, 71] -- ASCII `DREG`

def sourceTagAtom : Byte := 0
def sourceTagTop : Byte := 1
def sourceTagBot : Byte := 2
def sourceTagNot : Byte := 3
def sourceTagAnd : Byte := 4
def sourceTagOr : Byte := 5

def targetTagInput : Byte := 16
def targetTagTruth : Byte := 17
def targetTagFalsity : Byte := 18
def targetTagInv : Byte := 19
def targetTagConj : Byte := 20
def targetTagDisj : Byte := 21

def encodeSource : Source -> List Byte
  | .atom a => [sourceTagAtom, a]
  | .top => [sourceTagTop]
  | .bot => [sourceTagBot]
  | .not p => sourceTagNot :: encodeSource p
  | .and p q => sourceTagAnd :: (encodeSource p ++ encodeSource q)
  | .or p q => sourceTagOr :: (encodeSource p ++ encodeSource q)

def encodeTarget : Target -> List Byte
  | .input a => [targetTagInput, a]
  | .truth => [targetTagTruth]
  | .falsity => [targetTagFalsity]
  | .inv a => targetTagInv :: encodeTarget a
  | .conj a b => targetTagConj :: (encodeTarget a ++ encodeTarget b)
  | .disj a b => targetTagDisj :: (encodeTarget a ++ encodeTarget b)

/-- Fuel makes malformed recursive inputs total.  A successful canonical term
needs only its tree depth as fuel. -/
def decodeSourceFuel : Nat -> List Byte -> Option (Source × List Byte)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, tag :: rest =>
      if tag = sourceTagAtom then
        match rest with
        | atom :: tail => some (.atom atom, tail)
        | [] => none
      else if tag = sourceTagTop then some (.top, rest)
      else if tag = sourceTagBot then some (.bot, rest)
      else if tag = sourceTagNot then do
        let (p, tail) <- decodeSourceFuel fuel rest
        pure (.not p, tail)
      else if tag = sourceTagAnd then do
        let (p, tail) <- decodeSourceFuel fuel rest
        let (q, tail') <- decodeSourceFuel fuel tail
        pure (.and p q, tail')
      else if tag = sourceTagOr then do
        let (p, tail) <- decodeSourceFuel fuel rest
        let (q, tail') <- decodeSourceFuel fuel tail
        pure (.or p q, tail')
      else none

def decodeTargetFuel : Nat -> List Byte -> Option (Target × List Byte)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, tag :: rest =>
      if tag = targetTagInput then
        match rest with
        | atom :: tail => some (.input atom, tail)
        | [] => none
      else if tag = targetTagTruth then some (.truth, rest)
      else if tag = targetTagFalsity then some (.falsity, rest)
      else if tag = targetTagInv then do
        let (a, tail) <- decodeTargetFuel fuel rest
        pure (.inv a, tail)
      else if tag = targetTagConj then do
        let (a, tail) <- decodeTargetFuel fuel rest
        let (b, tail') <- decodeTargetFuel fuel tail
        pure (.conj a b, tail')
      else if tag = targetTagDisj then do
        let (a, tail) <- decodeTargetFuel fuel rest
        let (b, tail') <- decodeTargetFuel fuel tail
        pure (.disj a b, tail')
      else none


/-- Version 1 is canonical: one header, one source prefix term, one target
prefix term, and no trailing bytes.  Serialization itself is fail-closed: an
atom name that does not fit in the abstract byte model yields `none` rather than
being truncated. -/
def encodeBundle (bundle : Bundle) : Option (List Byte) :=
  let bytes := magic ++ [bundle.version] ++
    encodeSource bundle.source ++ encodeTarget bundle.target
  if bytesValid bytes then some bytes else none

/-- The fail-closed wire decoder.  Fuel is the full byte length, so it exceeds
the depth of every well-formed encoded subterm while bounding malformed input. -/
def decodeBundle (bytes : List Byte) : Option Bundle :=
  if bytesValid bytes then
    match bytes with
    | 68 :: 82 :: 69 :: 71 :: version :: body =>
        if version = currentVersion then do
          let (source, rest) <- decodeSourceFuel bytes.length body
          let (target, trailing) <- decodeTargetFuel bytes.length rest
          if trailing.isEmpty then
            some { version := version, source := source, target := target }
          else none
        else none
    | _ => none
  else none

def checkBytes (bytes : List Byte) : Bool :=
  match decodeBundle bytes with
  | some bundle => check bundle
  | none => false


/-- Main byte-boundary theorem: if untrusted bytes are accepted, they decode to
a known-version certificate whose source and target agree in every environment. -/
theorem checkBytes_sound {bytes : List Byte} (hcheck : checkBytes bytes = true) :
    exists bundle, decodeBundle bytes = some bundle /\
      bundle.version = currentVersion /\
      forall env, Target.eval env bundle.target = Source.eval env bundle.source := by
  cases hdecode : decodeBundle bytes with
  | none => simp [checkBytes, hdecode] at hcheck
  | some bundle =>
      have hbundle : check bundle = true := by
        simpa [checkBytes, hdecode] using hcheck
      exact ⟨bundle, rfl, check_known_version hbundle, check_sound hbundle⟩

/-- Unknown wire versions are rejected before term parsing. -/
theorem decodeBundle_rejects_unknown_version (version : Byte) (body : List Byte)
    (hversion : version ≠ currentVersion) :
    decodeBundle (68 :: 82 :: 69 :: 71 :: version :: body) = none := by
  simp [decodeBundle, hversion]

/-- Unknown source and target tags fail closed. -/
theorem decodeSourceFuel_rejects_unknown_tag {fuel tag : Nat}
    (hAtom : tag ≠ sourceTagAtom) (hTop : tag ≠ sourceTagTop)
    (hBot : tag ≠ sourceTagBot) (hNot : tag ≠ sourceTagNot)
    (hAnd : tag ≠ sourceTagAnd) (hOr : tag ≠ sourceTagOr) :
    decodeSourceFuel (fuel + 1) (tag :: []) = none := by
  simp [decodeSourceFuel, hAtom, hTop, hBot, hNot, hAnd, hOr]

theorem decodeTargetFuel_rejects_unknown_tag {fuel tag : Nat}
    (hInput : tag ≠ targetTagInput) (hTruth : tag ≠ targetTagTruth)
    (hFalsity : tag ≠ targetTagFalsity) (hInv : tag ≠ targetTagInv)
    (hConj : tag ≠ targetTagConj) (hDisj : tag ≠ targetTagDisj) :
    decodeTargetFuel (fuel + 1) (tag :: []) = none := by
  simp [decodeTargetFuel, hInput, hTruth, hFalsity, hInv, hConj, hDisj]

/-! A concrete canonical specimen pins the byte order and the no-trailing-byte
rule without asking an eventual reimplementation to infer either convention. -/

def canonicalTopBytes : List Byte :=
  [68, 82, 69, 71, currentVersion, sourceTagTop, targetTagTruth]

theorem canonicalTopBytes_decode :
    decodeBundle canonicalTopBytes = some (certify .top) := by
  rfl

theorem canonicalTopBytes_encode :
    encodeBundle (certify .top) = some canonicalTopBytes := by
  rfl

theorem canonicalTopBytes_check : checkBytes canonicalTopBytes = true := by
  rfl

theorem canonicalTopBytes_rejects_trailing :
    decodeBundle (canonicalTopBytes ++ [0]) = none := by
  rfl

theorem encodeBundle_rejects_nonByteAtom :
    encodeBundle (certify (.atom 256)) = none := by
  rfl


#assert_all_clean [
  lower_correct,
  check_certify,
  check_known_version,
  check_target_canonical,
  check_sound,
  check_rejects_unknown_version,
  checkBytes_sound,
  decodeBundle_rejects_unknown_version,
  decodeSourceFuel_rejects_unknown_tag,
  decodeTargetFuel_rejects_unknown_tag,
  canonicalTopBytes_decode,
  canonicalTopBytes_encode,
  canonicalTopBytes_check,
  canonicalTopBytes_rejects_trailing,
  encodeBundle_rejects_nonByteAtom
]

end Dregg2.Logic.CompilationCertificateBundle
