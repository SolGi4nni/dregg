/-
# `Dregg2.Deos.DocCommit` — the dregg DOCUMENT COMMITMENT over the real Poseidon2, binding the
atom's type+content+provenance AND — the load-bearing new part — BOTH alternatives of a stored
conflict (conflict-as-state soundness).

Foundation piece **F2** of `docs/DREGG-DOCUMENT-FOUNDATION.md` §2. Differential target: the Rust
`dregg-doc/src/commit.rs` + `atom.rs`.

## The problem this closes (from the F2 audit)

`dregg-doc/src/commit.rs:24-29` folds the document with a **non-cryptographic `DefaultHasher`**
outside `--features substrate`, so every Rust anti-forge test proves its property under a TOY hash;
and `commit.rs:95 provenance()` binds provenance in the preimage but there is **no theorem** that a
stored CONFLICT binds BOTH live alternatives — so a light client could be shown a two-branch conflict
hiding a FORGED alternative (the seven-forgery-bugs shape, in the document layer).

## The idiom (the same as `Storage/Deployed.lean` + `Storage/BucketCommitment.lean`)

"The fast Rust primitive at the leaf, Lean logic + proof on top." The document is canonically encoded
to a `List ℤ` preimage (self-delimiting, length-prefixed — the anti-concatenation-ambiguity
discipline of `commit.rs::Encoder`), then hashed by the abstract sponge `hash : List ℤ → ℤ`. The
binding proofs assume ONLY `Poseidon2SpongeCR` (the §8 collision-resistance carrier) about that
sponge, THREADED AS A HYPOTHESIS — never a new Lean axiom, exactly like `contentRoot_injective`. The
deployed instantiation (`docCommitDeployed`) fixes the sponge to the executable `poseidon2Hash` of
`Storage/Deployed.lean`, whose leaf is the fast Rust `@[extern "dregg_poseidon2_2to1"]` Poseidon2 —
so the commitment is executable native and (per §4) in the tab.

## What is delivered

* `encode` / `decode` — a canonical, self-delimiting `List ℤ` (de)serialization of a single-cell
  `Doc` (atoms + order-edges + fields), with a total left-inverse `decDoc` giving `encode_injective`.
  Per atom it binds the TYPE tag (`Content.text` vs `Content.element`, matching `atom.rs::AtomContent`
  and `canonical_bytes`'s leading discriminant byte), the content bytes, the `Status`, and the
  `(author, patch)` provenance.
* `docCommit` — `hash (encode d)`: the Poseidon2 fold. `docCommitDeployed` fixes the executable
  Rust-leaf sponge.
* `docCommit_injective` — equal commitments ⟹ equal committed document (atoms + provenance),
  reducing to `Poseidon2SpongeCR` (a HYPOTHESIS). No ghost atom hides under a genuine root.
* `docCommit_conflict_binds_both` — **THE NEW ONE (conflict-as-state soundness).** A commitment to a
  two-alternative conflict at a field DETERMINES both live alternatives AND their provenance; a
  substituted/forged alternative changes the commitment (CR-refused). This is the anti-forge tooth
  for conflicts (the `DocMerge.field_not_iconfluent` / `ConflictAt` shape given a real hash).
* `forge_changes_root` (NON-VACUITY) — a concrete conflict whose forged alternative (SAME rendered
  value bytes, FORGED author) provably changes the root, PROVED THROUGH `docCommit_conflict_binds_both`
  (so that keystone is non-vacuous). Backed by `#guard`s that the preimages genuinely differ.

Only `Poseidon2SpongeCR` is assumed (checked by `#assert_axioms`, ⊆ {propext, Classical.choice,
Quot.sound} + the named carrier as a hypothesis). Single-cell: the composed-carrier lift is F1's job
(`DocMergeComposed`); a `ComposedDoc` commit is a componentwise fold of these per-cell `docCommit`s —
a NOTE, not built here.

**F4b seam (named, not built):** retiring `commit.rs`'s `DefaultHasher` = wiring the Rust
`dregg-doc::commit` to call `@[export dregg_doc_commit]` (over `commit.rs::canonical_bytes`, batched
per §4), so the one implementation is this proven core. The `@[extern]` Rust primitive already exists:
`dregg_poseidon2_2to1` (`Storage/Deployed.lean`), realized by `circuit::binding` Poseidon2.
-/
import Dregg2.Storage.Deployed
import Dregg2.Tactics
import Mathlib.Logic.Function.Basic

namespace Dregg2.Deos.DocCommit

open Dregg2.Storage (poseidon2Hash)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## 1. The single-cell document model — the commitment's view of `dregg-doc`. -/

/-- Provenance `(author, patch)` (`atom.rs::Provenance`) — the load-bearing binding for the conflict
view: each alternative carries WHO wrote it. -/
structure Prov where
  author : ℤ
  patch : ℤ
deriving DecidableEq, Repr

/-- Type-tagged atom content — the commitment's view of `atom.rs::AtomContent`. The discriminant
(`text` vs `element`) IS the leading byte of `canonical_bytes` (`0` for Text, `1` for Element), so a
structural node and a text run with equal payload bytes commit DIFFERENTLY (the anti-alias tooth).
`bytes` is the canonical content payload (`canonical_bytes` after its tag byte — for an Element, the
length-prefixed tag/attrs/children whose own injective grammar is the Rust `canonical_bytes` roundtrip
at the F4b leaf). -/
inductive Content where
  | text (bytes : List ℤ)
  | element (bytes : List ℤ)
deriving DecidableEq, Repr

/-- Liveness (`atom.rs::Status`). -/
inductive Status where
  | alive
  | dead
deriving DecidableEq, Repr

/-- A document atom (`atom.rs::Atom`): id, typed content, status, provenance. -/
structure Atom where
  id : ℤ
  content : Content
  status : Status
  prov : Prov
deriving DecidableEq, Repr

/-- A single field assignment: a value together with its provenance (`commit.rs`'s field section:
`value ‖ provenance`). Two assignments at one name = a stored CONFLICT; each is one live alternative,
carrying who authored it. -/
structure FieldAssign where
  value : List ℤ
  prov : Prov
deriving DecidableEq, Repr

/-- A field entry: the field name and its (ordered) assignments. `≥ 2` assignments is a conflict —
the `DocMerge.field_not_iconfluent` two-value clash, now WITH provenance at the commitment layer. -/
structure FieldEntry where
  name : ℤ
  assigns : List FieldAssign
deriving DecidableEq, Repr

/-- A single-cell document (`graph.rs::DocGraph`), in canonical (sorted) order: the atoms, the
order-edges, the field entries. Canonical order is a precondition (the Rust rides `BTreeMap`); the
commitment binds the ordered form. -/
structure Doc where
  atoms : List Atom
  edges : List (ℤ × ℤ)
  fields : List FieldEntry
deriving DecidableEq, Repr

/-! ## 2. The canonical, self-delimiting `List ℤ` encoding (`commit.rs::Encoder`). -/

/-- One status byte (`Encoder::status`). -/
def encStatus : Status → ℤ
  | .alive => 0
  | .dead => 1

/-- Provenance = author then patch, two fixed cells (`Encoder::provenance`). -/
def encProv (p : Prov) : List ℤ := [p.author, p.patch]

/-- A length-prefixed run (`Encoder::bytes_run`): the length, then the elements. Self-delimiting. -/
def encRun (xs : List ℤ) : List ℤ := (xs.length : ℤ) :: xs

/-- Content: the leading TYPE tag (`0` = Text, `1` = Element — `canonical_bytes`'s discriminant),
then the length-prefixed payload run. -/
def encContent : Content → List ℤ
  | .text b => 0 :: encRun b
  | .element b => 1 :: encRun b

/-- One atom: id, content (tag + run), status byte, provenance — each self-delimiting, in
`commit.rs` order. -/
def encAtom (a : Atom) : List ℤ :=
  a.id :: (encContent a.content ++ (encStatus a.status :: encProv a.prov))

/-- One order-edge `(from, to)` — two fixed cells. -/
def encPair (p : ℤ × ℤ) : List ℤ := [p.1, p.2]

/-- One field assignment: the value run, then the provenance (`value ‖ provenance`). -/
def encAssign (a : FieldAssign) : List ℤ := encRun a.value ++ encProv a.prov

/-- Concatenate a self-delimiting encoder over a list. -/
def encList {α : Type} (enc : α → List ℤ) : List α → List ℤ
  | [] => []
  | x :: xs => enc x ++ encList enc xs

/-- Count-prefixed list of self-delimiting elements. -/
def encListWith {α : Type} (enc : α → List ℤ) (xs : List α) : List ℤ :=
  (xs.length : ℤ) :: encList enc xs

/-- One field entry: the name, then the length-prefixed list of assignments. Both clashing
alternatives' provenance is bound here — the conflict-as-state binding. -/
def encField (f : FieldEntry) : List ℤ := f.name :: encListWith encAssign f.assigns

/-- **`encode`** — the canonical document preimage: the atoms section, the edges section, the fields
section, each a count-prefixed list of self-delimiting elements. This is the byte-for-byte spirit of
`commit.rs::commit` (atoms ‖ edges ‖ fields, every run length-prefixed). -/
def encode (d : Doc) : List ℤ :=
  encListWith encAtom d.atoms ++ encListWith encPair d.edges ++ encListWith encField d.fields

/-! ## 3. The total left-inverse decoder (parser-combinator style) ⟹ `encode` is injective. -/

/-- A decoder: consume a prefix, return the value + the remainder. -/
abbrev Dec (α : Type) := List ℤ → Option (α × List ℤ)

def decRun : Dec (List ℤ)
  | [] => none
  | n :: rest => some (rest.take n.toNat, rest.drop n.toNat)

def decProv : Dec Prov
  | a :: p :: rest => some (⟨a, p⟩, rest)
  | _ => none

def decStatus : Dec Status
  | [] => none
  | z :: rest => if z = 0 then some (.alive, rest) else if z = 1 then some (.dead, rest) else none

def decContent : Dec Content
  | [] => none
  | t :: rest =>
    match decRun rest with
    | some (b, rest') =>
      if t = 0 then some (.text b, rest')
      else if t = 1 then some (.element b, rest') else none
    | none => none

def decAtom : Dec Atom
  | [] => none
  | id :: rest =>
    match decContent rest with
    | some (c, r1) =>
      match decStatus r1 with
      | some (s, r2) =>
        match decProv r2 with
        | some (p, r3) => some (⟨id, c, s, p⟩, r3)
        | none => none
      | none => none
    | none => none

def decPair : Dec (ℤ × ℤ)
  | a :: b :: rest => some ((a, b), rest)
  | _ => none

def decAssign : Dec FieldAssign := fun s =>
  match decRun s with
  | some (v, r1) =>
    match decProv r1 with
    | some (p, r2) => some (⟨v, p⟩, r2)
    | none => none
  | none => none

/-- Apply a decoder `k` times, threading the remainder. -/
def decN {α : Type} (dec : Dec α) : Nat → Dec (List α)
  | 0, s => some ([], s)
  | k + 1, s =>
    match dec s with
    | some (a, s') =>
      match decN dec k s' with
      | some (as, s'') => some (a :: as, s'')
      | none => none
    | none => none

/-- Decode a count-prefixed list. -/
def decListWith {α : Type} (dec : Dec α) : Dec (List α)
  | [] => none
  | n :: rest => decN dec n.toNat rest

def decField : Dec FieldEntry
  | [] => none
  | name :: rest =>
    match decListWith decAssign rest with
    | some (assigns, r1) => some (⟨name, assigns⟩, r1)
    | none => none

def decDoc : Dec Doc := fun s =>
  match decListWith decAtom s with
  | some (atoms, r1) =>
    match decListWith decPair r1 with
    | some (edges, r2) =>
      match decListWith decField r2 with
      | some (fields, r3) => some (⟨atoms, edges, fields⟩, r3)
      | none => none
    | none => none
  | none => none

/-! ### Roundtrip lemmas: each `dec (enc x ++ rest) = some (x, rest)`. -/

theorem decRun_enc (xs rest : List ℤ) : decRun (encRun xs ++ rest) = some (xs, rest) := by
  show decRun ((xs.length : ℤ) :: (xs ++ rest)) = some (xs, rest)
  simp only [decRun, Int.toNat_natCast, List.take_left, List.drop_left]

theorem decProv_enc (p : Prov) (rest : List ℤ) : decProv (encProv p ++ rest) = some (p, rest) := by
  cases p; rfl

theorem decStatus_enc (s : Status) (rest : List ℤ) :
    decStatus (encStatus s :: rest) = some (s, rest) := by
  cases s <;> simp [decStatus, encStatus]

theorem decContent_enc (c : Content) (rest : List ℤ) :
    decContent (encContent c ++ rest) = some (c, rest) := by
  cases c with
  | text b => simp [encContent, decContent, decRun_enc]
  | element b => simp [encContent, decContent, decRun_enc]

theorem decAtom_enc (a : Atom) (rest : List ℤ) : decAtom (encAtom a ++ rest) = some (a, rest) := by
  cases a with
  | mk id c s p =>
    show decAtom (id :: (encContent c ++ (encStatus s :: encProv p) ++ rest)) = _
    simp only [decAtom, List.append_assoc, List.cons_append, decContent_enc, decStatus_enc,
      decProv_enc]

theorem decPair_enc (p : ℤ × ℤ) (rest : List ℤ) : decPair (encPair p ++ rest) = some (p, rest) := by
  cases p; rfl

theorem decAssign_enc (a : FieldAssign) (rest : List ℤ) :
    decAssign (encAssign a ++ rest) = some (a, rest) := by
  cases a with
  | mk v p =>
    show decAssign (encRun v ++ encProv p ++ rest) = _
    simp only [decAssign, List.append_assoc, decRun_enc, decProv_enc]

theorem decN_enc {α : Type} (enc : α → List ℤ) (dec : Dec α)
    (hrt : ∀ a r, dec (enc a ++ r) = some (a, r)) :
    ∀ (xs : List α) (rest : List ℤ), decN dec xs.length (encList enc xs ++ rest) = some (xs, rest) := by
  intro xs
  induction xs with
  | nil => intro rest; rfl
  | cons a as ih =>
    intro rest
    show decN dec (as.length + 1) (enc a ++ encList enc as ++ rest) = some (a :: as, rest)
    rw [List.append_assoc]
    simp only [decN, hrt a (encList enc as ++ rest), ih rest]

theorem decListWith_enc {α : Type} (enc : α → List ℤ) (dec : Dec α)
    (hrt : ∀ a r, dec (enc a ++ r) = some (a, r)) (xs : List α) (rest : List ℤ) :
    decListWith dec (encListWith enc xs ++ rest) = some (xs, rest) := by
  show decListWith dec ((xs.length : ℤ) :: (encList enc xs ++ rest)) = some (xs, rest)
  show decN dec ((xs.length : ℤ)).toNat (encList enc xs ++ rest) = some (xs, rest)
  rw [Int.toNat_natCast]
  exact decN_enc enc dec hrt xs rest

theorem decField_enc (f : FieldEntry) (rest : List ℤ) :
    decField (encField f ++ rest) = some (f, rest) := by
  cases f with
  | mk name assigns =>
    show decField (name :: (encListWith encAssign assigns ++ rest)) = _
    simp only [decField, decListWith_enc encAssign decAssign decAssign_enc]

theorem decDoc_enc (d : Doc) (rest : List ℤ) : decDoc (encode d ++ rest) = some (d, rest) := by
  cases d with
  | mk atoms edges fields =>
    show decDoc (encListWith encAtom atoms ++ encListWith encPair edges ++
      encListWith encField fields ++ rest) = _
    simp only [decDoc, List.append_assoc,
      decListWith_enc encAtom decAtom decAtom_enc,
      decListWith_enc encPair decPair decPair_enc,
      decListWith_enc encField decField decField_enc]

/-- **`encode` is injective** — the canonical encoding has a total left inverse (`decDoc`), so equal
preimages force equal documents. Purely combinatorial: no crypto yet. -/
theorem encode_injective : Function.Injective encode := by
  intro d d' h
  have hd : decDoc (encode d) = some (d, ([] : List ℤ)) := by
    have := decDoc_enc d []; rwa [List.append_nil] at this
  have hd' : decDoc (encode d') = some (d', ([] : List ℤ)) := by
    have := decDoc_enc d' []; rwa [List.append_nil] at this
  rw [h, hd', Option.some.injEq, Prod.mk.injEq] at hd
  exact hd.1.symm

/-! ## 4. `docCommit` — the Poseidon2 fold — and its binding, discharged by `Poseidon2SpongeCR`. -/

/-- **`docCommit`** — the document commitment: the abstract Poseidon2 sponge over the canonical
preimage. Binds, per atom, its TYPE tag + content + provenance; per field, every assignment's value +
provenance (BOTH conflict alternatives). Executable when `hash` is the deployed Rust-leaf sponge
(`docCommitDeployed`). -/
def docCommit (hash : List ℤ → ℤ) (d : Doc) : ℤ := hash (encode d)

/-- **`docCommit_injective` (THE BINDING).** Equal commitments ⟹ equal committed document (atoms +
edges + fields, WITH provenance). Reduces to `Poseidon2SpongeCR` — the collision-resistance carrier,
THREADED AS A HYPOTHESIS, never a Lean axiom (exactly like `contentRoot_injective`) — composed with
`encode_injective`. No ghost atom hides under a genuine root. -/
theorem docCommit_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ d d' : Doc, docCommit hash d = docCommit hash d' → d = d' :=
  fun _ _ h => encode_injective (hCR _ _ h)

/-- The field's assignments at a name, if present (the conflict view: `some [a, b]` = a two-branch
conflict at `name`). -/
def fieldAt (d : Doc) (name : ℤ) : Option (List FieldAssign) :=
  (d.fields.find? (fun e => e.name == name)).map (·.assigns)

/-- **`docCommit_conflict_binds_both` (CONFLICT-AS-STATE SOUNDNESS — the new tooth).** If two
documents commit EQUAL and each stores a two-alternative conflict at the same field `name`, then both
live alternatives — value AND provenance — are IDENTICAL. So a substituted/forged alternative (even
one that renders identically but is authored by someone else) CANNOT hide under an equal commitment:
it would change the root, refused by collision-resistance. This is the seven-forgery-bugs shape closed
in the document layer — a light client shown a conflict binds both branches, not one. -/
theorem docCommit_conflict_binds_both
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d d' : Doc) (name : ℤ) (a1 a2 a1' a2' : FieldAssign)
    (hd : fieldAt d name = some [a1, a2])
    (hd' : fieldAt d' name = some [a1', a2'])
    (heq : docCommit hash d = docCommit hash d') :
    a1 = a1' ∧ a2 = a2' := by
  have hdd : d = d' := docCommit_injective hash hCR d d' heq
  subst hdd
  rw [hd, Option.some.injEq] at hd'
  simp only [List.cons.injEq, and_true] at hd'
  exact ⟨hd'.1, hd'.2⟩

/-! ## 5. NON-VACUITY — a concrete forged conflict provably changes the root. -/

/-- Author X, author Y — two distinct authoring identities. -/
def provX : Prov := ⟨7, 100⟩
def provY : Prov := ⟨9, 200⟩

/-- Alternative A: value bytes `[65]` ("A"), authored by X. -/
def altA : FieldAssign := ⟨[65], provX⟩
/-- Alternative B: value bytes `[66]` ("B"), authored by Y. -/
def altB : FieldAssign := ⟨[66], provY⟩
/-- The FORGED alternative: the SAME rendered value bytes `[66]` as `altB`, but a FORGED author
(`13`, not `9`). Renders identically; authorship is forged — the exact case the tooth must bite. -/
def altBforged : FieldAssign := ⟨[66], ⟨13, 200⟩⟩

/-- A document with a genuine two-alternative conflict at field `0`: `[altA, altB]`. -/
def conflictDoc : Doc := ⟨[], [], [⟨0, [altA, altB]⟩]⟩
/-- The forged document: alternative B's provenance is forged (`altBforged`), rendered text unchanged. -/
def forgedDoc : Doc := ⟨[], [], [⟨0, [altA, altBforged]⟩]⟩

-- The two docs are genuinely different (the forge is real, not a no-op).
#guard decide (conflictDoc ≠ forgedDoc)
-- The PREIMAGES differ — so under any CR sponge the ROOTS differ. Machine-checked non-vacuity.
#guard decide (encode conflictDoc ≠ encode forgedDoc)
-- Each doc really stores the stated two-branch conflict at field 0.
#guard decide (fieldAt conflictDoc 0 = some [altA, altB])
#guard decide (fieldAt forgedDoc 0 = some [altA, altBforged])

/-- **`forge_changes_root` (NON-VACUITY of the conflict tooth).** A forged conflict alternative —
same rendered value, forged author — provably yields a DIFFERENT commitment under collision
resistance. Proved THROUGH `docCommit_conflict_binds_both`: were the roots equal, that keystone would
force `altB = altBforged`, which is false by `decide`. So the light client cannot be shown the forged
conflict, and the binding theorem is non-vacuous (its conclusion is genuinely refutable). -/
theorem forge_changes_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    docCommit hash conflictDoc ≠ docCommit hash forgedDoc := by
  intro h
  have hb := docCommit_conflict_binds_both hash hCR conflictDoc forgedDoc 0
    altA altB altA altBforged (by decide) (by decide) h
  exact absurd hb.2 (by decide)

/-! ## 6. The DEPLOYED instantiation — executable, the fast Rust Poseidon2 at the leaf. -/

/-- **`docCommitDeployed`** — `docCommit` at the deployed sponge `poseidon2Hash` (`Storage/Deployed`),
whose leaf is the fast Rust `@[extern "dregg_poseidon2_2to1"]` Poseidon2. The verified LOGIC (the
canonical fold) is Lean; the hot PRIMITIVE is Rust. Executable native and (per §4) in the tab. -/
def docCommitDeployed (d : Doc) : ℤ := docCommit poseidon2Hash d

/-- **`docCommitDeployed_injective`** — the extracted, real-crypto form of `docCommit_injective`,
discharged by the collision-resistance carrier for the deployed Poseidon2 (a HYPOTHESIS, never a Lean
axiom). No ghost document hides under a genuine deployed root. -/
theorem docCommitDeployed_injective (hCR : Poseidon2SpongeCR poseidon2Hash) :
    ∀ d d' : Doc, docCommitDeployed d = docCommitDeployed d' → d = d' :=
  docCommit_injective poseidon2Hash hCR

/-! ## 7. Axiom hygiene — every keystone kernel-clean (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms encode_injective
#assert_axioms docCommit_injective
#assert_axioms docCommit_conflict_binds_both
#assert_axioms forge_changes_root
#assert_axioms docCommitDeployed_injective

end Dregg2.Deos.DocCommit
