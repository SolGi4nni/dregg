/-
# Dregg2.Apps.StorageGatewayMandate.Core — object-store mandate + VFS admissibility (Phase A).

A storage-gateway mandate models a content-addressed object store: bucket/prefix labels, GET/PUT/LIST
ops, a Stingray `Slice` volume budget, and compartment clearance for reads. Pure, computable,
`#eval`-able. No `sorry`/`admit`/`native_decide`.
-/
import Dregg2.Authority.ClearanceGraph
import Dregg2.Exec.Kernel
import Dregg2.Exec.Value
import Dregg2.Proof.Stingray
import Dregg2.Tactics

namespace Dregg2.Apps.StorageGatewayMandate

open Dregg2.Exec
open Dregg2.Authority.ClearanceGraph
open Dregg2.Proof.Stingray

/-! ## Object-store types. -/

/-- Storage gateway operation (VFS row: GET / PUT / LIST). -/
inductive StorageOp where
  | GET
  | PUT
  | LIST
  deriving Repr, DecidableEq

/-- Encode an op as an `Int` field value for `setFieldA`. -/
def StorageOp.toInt : StorageOp → Int
  | .GET  => 0
  | .PUT  => 1
  | .LIST => 2

/-- Decode an op field value (demo-facing). -/
def StorageOp.ofInt (n : Int) : Option StorageOp :=
  if n = 0 then some .GET
  else if n = 1 then some .PUT
  else if n = 2 then some .LIST
  else none

/-- Content-addressed blob reference (BLAKE3 hash stand-in). -/
structure BlobRef where
  hash : Nat
  deriving Repr, DecidableEq

/-- One storage request: op + object key + optional blob hash (PUT). -/
structure StorageRequest where
  op   : StorageOp
  key  : String
  blob : Option BlobRef := none
  deriving Repr, DecidableEq

/-- The storage-gateway mandate carried by the gateway cell. -/
structure StorageMandate where
  bucket          : Label
  keyPrefix       : String
  allowedOps      : List StorageOp
  putCost         : Nat
  getCost         : Nat
  listCost        : Nat
  actorLabels     : List Label
  clearanceGraph  : ClearanceGraph
  readCompartment : Label
  volumeBudget    : Slice
  anchor          : Nat := 42
  tracker         : CellId := 0
  deriving Repr, DecidableEq

/-! ## Admissibility predicates. -/

/-- Whether `op` is listed in the mandate's allowed set. -/
def opAllowed (m : StorageMandate) (op : StorageOp) : Bool :=
  m.allowedOps.contains op

/-- Object key lies under the mandated prefix (`pfx.isPrefixOf key`). -/
def keyUnderPrefix (pfx key : String) : Bool :=
  pfx.isPrefixOf key

/-- PUT is authorized only when the key matches the mandated prefix. -/
def putPrefixOK (m : StorageMandate) (key : String) : Bool :=
  keyUnderPrefix m.keyPrefix key

/-- GET requires compartment clearance on `readCompartment`. -/
def getClearanceOK (m : StorageMandate) : Bool :=
  mayRead m.clearanceGraph m.actorLabels m.readCompartment

/-- Per-op volume debit against the Stingray slice. -/
def opCost (m : StorageMandate) (op : StorageOp) : Nat :=
  match op with
  | .GET  => m.getCost
  | .PUT  => m.putCost
  | .LIST => m.listCost

/-- **Runtime mandate state**: live Stingray slice + commitment anchor. -/
structure SgmRuntime where
  volume : Slice
  anchor : Nat
  deriving Repr, DecidableEq

def SgmRuntime.WF (s : SgmRuntime) : Prop := s.volume.spent ≤ s.volume.ceiling

def SgmRuntime.init (m : StorageMandate) : SgmRuntime :=
  { volume := m.volumeBudget, anchor := m.anchor }

instance (s : SgmRuntime) : Decidable (s.WF) := by
  unfold SgmRuntime.WF; infer_instance

/-- **`sgmAdmitM`** — predicate-level one-step admission: op allowed, prefix/clearance gates,
volume debit via `Slice.tryDebit`. -/
def sgmAdmitM (m : StorageMandate) (s : SgmRuntime) (req : StorageRequest) : Option SgmRuntime :=
  if opAllowed m req.op then
    match req.op with
    | .GET =>
      if getClearanceOK m then
        (s.volume.tryDebit m.getCost).map fun v => { s with volume := v }
      else
        none
    | .PUT =>
      if putPrefixOK m req.key then
        (s.volume.tryDebit m.putCost).map fun v => { s with volume := v }
      else
        none
    | .LIST =>
      (s.volume.tryDebit m.listCost).map fun v => { s with volume := v }
  else
    none

/-! ## One-step lemmas. -/

theorem tryDebit_preserves_spent_le (s s' : Slice) (cost : Nat) (hwf : s.spent ≤ s.ceiling)
    (h : s.tryDebit cost = some s') : s'.spent ≤ s'.ceiling := by
  obtain ⟨hsp, hcl⟩ := tryDebit_spent h
  have hrem := (tryDebit_isSome_iff s cost).mp (by rw [h]; simp)
  have hbound : cost ≤ s.ceiling - s.spent := by simpa [Slice.remaining] using hrem
  rw [hsp, hcl]
  omega

theorem sgm_op_not_allowed_rejected (m : StorageMandate) (s : SgmRuntime) (req : StorageRequest)
    (hop : opAllowed m req.op = false) :
    sgmAdmitM m s req = none := by
  unfold sgmAdmitM
  simp [hop]

theorem sgm_prefix_violation_rejected (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .PUT = true) (hpfx : putPrefixOK m key = false) :
    sgmAdmitM m s { op := .PUT, key := key } = none := by
  simp [sgmAdmitM, hop, hpfx, ↓reduceIte]

theorem sgm_clearance_fail_rejected (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .GET = true) (hcl : getClearanceOK m = false) :
    sgmAdmitM m s { op := .GET, key := key } = none := by
  simp [sgmAdmitM, hop, hcl, ↓reduceIte]

theorem sgm_over_debit_rejected_get (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .GET = true) (hdeb : (s.volume.tryDebit m.getCost).isSome = false) :
    sgmAdmitM m s { op := .GET, key := key } = none := by
  have hnone : s.volume.tryDebit m.getCost = none := by
    cases hvol : s.volume.tryDebit m.getCost with
    | none => rfl
    | some v => simp [hvol] at hdeb
  simp [sgmAdmitM, hop, hnone, Option.map_none, ↓reduceIte]

theorem sgm_over_debit_rejected_put (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .PUT = true) (hpfx : putPrefixOK m key = true)
    (hdeb : (s.volume.tryDebit m.putCost).isSome = false) :
    sgmAdmitM m s { op := .PUT, key := key } = none := by
  have hnone : s.volume.tryDebit m.putCost = none := by
    cases hvol : s.volume.tryDebit m.putCost with
    | none => rfl
    | some v => simp [hvol] at hdeb
  simp [sgmAdmitM, hop, hpfx, hnone, Option.map_none, ↓reduceIte]

theorem sgm_over_debit_rejected_list (m : StorageMandate) (s : SgmRuntime) (key : String)
    (hop : opAllowed m .LIST = true) (hdeb : (s.volume.tryDebit m.listCost).isSome = false) :
    sgmAdmitM m s { op := .LIST, key := key } = none := by
  have hnone : s.volume.tryDebit m.listCost = none := by
    cases hvol : s.volume.tryDebit m.listCost with
    | none => rfl
    | some v => simp [hvol] at hdeb
  simp [sgmAdmitM, hop, hnone, Option.map_none]

theorem sgm_over_debit_rejected (m : StorageMandate) (s : SgmRuntime) (req : StorageRequest)
    (hop : opAllowed m req.op = true)
    (hget : req.op = .GET → getClearanceOK m = true)
    (hput : req.op = .PUT → putPrefixOK m req.key = true)
    (hdeb : (s.volume.tryDebit (opCost m req.op)).isSome = false) :
    sgmAdmitM m s req = none := by
  obtain ⟨op, key, blob⟩ := req
  cases op with
  | GET =>
      simpa [opCost] using
        sgm_over_debit_rejected_get m s key hop (by simpa [opCost] using hdeb)
  | PUT =>
      simpa [opCost] using
        sgm_over_debit_rejected_put m s key hop (hput rfl) (by simpa [opCost] using hdeb)
  | LIST =>
      simpa [opCost] using
        sgm_over_debit_rejected_list m s key hop (by simpa [opCost] using hdeb)

theorem sgmAdmitM_preserves_WF_get (m : StorageMandate) (s s' : SgmRuntime) (key : String)
    (hwf : s.WF) (hop : opAllowed m .GET = true) (hcl : getClearanceOK m = true)
    (h : sgmAdmitM m s { op := .GET, key := key } = some s') : s'.WF := by
  unfold SgmRuntime.WF at hwf ⊢
  unfold sgmAdmitM at h
  simp only [hop, hcl, ↓reduceIte] at h
  cases hvol : s.volume.tryDebit m.getCost with
  | none =>
      exfalso
      simpa [hvol, Option.map_none] using h
  | some v =>
      have heq : s' = { s with volume := v } :=
        Eq.symm (Option.some.inj (by simpa [hvol, Option.map_some] using h))
      rw [heq]
      exact tryDebit_preserves_spent_le s.volume v m.getCost hwf hvol

theorem sgmAdmitM_preserves_WF_put (m : StorageMandate) (s s' : SgmRuntime) (key : String)
    (hwf : s.WF) (hop : opAllowed m .PUT = true) (hpfx : putPrefixOK m key = true)
    (h : sgmAdmitM m s { op := .PUT, key := key } = some s') : s'.WF := by
  unfold SgmRuntime.WF at hwf ⊢
  unfold sgmAdmitM at h
  simp only [hop, hpfx, ↓reduceIte] at h
  cases hvol : s.volume.tryDebit m.putCost with
  | none =>
      exfalso
      simpa [hvol, Option.map_none] using h
  | some v =>
      have heq : s' = { s with volume := v } :=
        Eq.symm (Option.some.inj (by simpa [hvol, Option.map_some] using h))
      rw [heq]
      exact tryDebit_preserves_spent_le s.volume v m.putCost hwf hvol

theorem sgmAdmitM_preserves_WF_list (m : StorageMandate) (s s' : SgmRuntime) (key : String)
    (hwf : s.WF) (hop : opAllowed m .LIST = true)
    (h : sgmAdmitM m s { op := .LIST, key := key } = some s') : s'.WF := by
  unfold SgmRuntime.WF at hwf ⊢
  unfold sgmAdmitM at h
  simp only [hop, ↓reduceIte] at h
  cases hvol : s.volume.tryDebit m.listCost with
  | none =>
      exfalso
      simpa [hvol, Option.map_none] using h
  | some v =>
      have heq : s' = { s with volume := v } :=
        Eq.symm (Option.some.inj (by simpa [hvol, Option.map_some] using h))
      rw [heq]
      exact tryDebit_preserves_spent_le s.volume v m.listCost hwf hvol

theorem sgmAdmitM_preserves_WF (m : StorageMandate) (s s' : SgmRuntime) (req : StorageRequest)
    (hwf : s.WF) (h : sgmAdmitM m s req = some s') : s'.WF := by
  obtain ⟨op, key, blob⟩ := req
  cases hop : opAllowed m op with
  | false =>
      exfalso
      simpa [sgmAdmitM, hop] using h
  | true =>
      cases op with
      | GET =>
          by_cases hcl : getClearanceOK m
          · exact sgmAdmitM_preserves_WF_get m s s' key hwf hop hcl h
          · exfalso; simpa [sgmAdmitM, hop, hcl, ↓reduceIte] using h
      | PUT =>
          by_cases hpfx : putPrefixOK m key
          · exact sgmAdmitM_preserves_WF_put m s s' key hwf hop hpfx h
          · exfalso; simpa [sgmAdmitM, hop, hpfx, ↓reduceIte] using h
      | LIST =>
          exact sgmAdmitM_preserves_WF_list m s s' key hwf hop h

/-! ## Demo mandate + guards. -/

abbrev objectKeySlot : FieldName := "object_key"
abbrev lastOpSlot : FieldName := "last_op"
abbrev volumeSpentSlot : FieldName := "volume_spent"
abbrev commitmentAnchorSlot : FieldName := "commitment_anchor"
abbrev mandateCell : CellId := 0

def demoGraph : ClearanceGraph :=
  { edges := [ (Label.named "writer", Label.named "storage-read") ] }

/-- Writer may PUT/GET/LIST under `uploads/` with a 10-unit Stingray slice. -/
def demoMandate : StorageMandate :=
  { bucket := Label.named "app-bucket"
  , keyPrefix := "uploads/"
  , allowedOps := [.PUT, .GET, .LIST]
  , putCost := 5
  , getCost := 1
  , listCost := 2
  , actorLabels := [Label.named "writer"]
  , clearanceGraph := demoGraph
  , readCompartment := Label.named "storage-read"
  , volumeBudget := { ceiling := 10, spent := 0 }
  , anchor := 42
  , tracker := 100 }

/-- Guest actor lacks read clearance (GET rejected). -/
def guestMandate : StorageMandate :=
  { demoMandate with actorLabels := [Label.named "guest"] }

/-- PUT-only mandate for prefix authorization demo. -/
def putOnlyMandate : StorageMandate :=
  { demoMandate with allowedOps := [.PUT] }

def demoPutReq : StorageRequest :=
  { op := .PUT, key := "uploads/doc.txt", blob := some { hash := 3735928559 } }

def demoBadPutReq : StorageRequest :=
  { op := .PUT, key := "secret/doc.txt", blob := some { hash := 2989 } }

def demoGetReq : StorageRequest :=
  { op := .GET, key := "uploads/doc.txt" }

#guard opAllowed demoMandate .PUT
#guard putPrefixOK demoMandate "uploads/doc.txt"
#guard putPrefixOK demoMandate "secret/doc.txt" == false
#guard getClearanceOK demoMandate
#guard getClearanceOK guestMandate == false
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoPutReq).isSome
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoBadPutReq).isSome == false
#guard (sgmAdmitM guestMandate (SgmRuntime.init guestMandate) demoGetReq).isSome == false
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoGetReq).isSome
#guard ((demoMandate.volumeBudget.tryDebit demoMandate.putCost).bind
          (fun s' => s'.tryDebit demoMandate.putCost)).isSome
#guard (((demoMandate.volumeBudget.tryDebit demoMandate.putCost).bind
           (fun s' => s'.tryDebit demoMandate.putCost)).bind
          (fun s'' => s''.tryDebit demoMandate.putCost)).isSome == false

#assert_axioms tryDebit_preserves_spent_le
#assert_axioms sgm_op_not_allowed_rejected
#assert_axioms sgm_prefix_violation_rejected
#assert_axioms sgm_clearance_fail_rejected
#assert_axioms sgm_over_debit_rejected
#assert_axioms sgmAdmitM_preserves_WF

end Dregg2.Apps.StorageGatewayMandate