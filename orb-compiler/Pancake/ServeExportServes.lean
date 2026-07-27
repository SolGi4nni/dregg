/-
  Pancake/ServeExportServes.lean — TRACK 2 PHASE A capstone: the behavior of the
  EMITTED serve PFun (`ServeEmit.serveExport`, the thing `ppFun` prints to the
  `.pnk` cake compiles) equals the serve spec, over the WHOLE control-flow program
  — `parseMethod` decode, the routing `ite`, the byte-store head, the `ret`. This
  DELETES the golden-`.bin`-diff crutch: the emitted `.pnk` is now related to the
  model by a proof, not a byte diff.

  GROUND (already landed, imported):
   * `Lower.lean`   : `lower : PFun → Option PancakeProg`, parse-faithful, already
     covers every construct `serveExport` emits (`.dec/.assign/.ite/.ret/.loadb/
     .storeb` + `eEq`/`eLt` exprs). No extension needed — a prior lane modelled the
     fused-serve ops.
   * `LowerBridge`  : SYNTACTIC — the byte-store head `storesInto` lowers to the
     model `.storeByte` program `storesModel` (`storesInto_lowers`).
   * `LowerBridgeSem`: SEMANTIC — running the model byte-store program lands the
     bytes byte-addressed (`storesModel_landsB`, `serve_head_landsB`), plus the
     reusable primitives `run_headStore` / `load_afterStore_same`/`_ne` /
     `afterStore` / `MemBytesAtB`.

  THE GAP THIS FILE CLOSES: nothing related the WHOLE emitted PFun (with its
  `parseMethod` ite-chain, the routing ite, the trailing `ret count`) to the model.
  `fullRespLit` / `storesModel` are FRAGMENTS; `lower serveExport` is the whole
  program and was tied to the model only by inspection.

  WHAT IS PROVEN (all OPERATIONAL, `execute = spec` on a real post-state):
   * `serveExport_lowers` — SYNTACTIC bridge over the WHOLE PFun: `lower (serveExport
     bs200 bs405) = some (serveModel bs200 bs405)`, a named model program, for ALL
     response byte lists. The routing branches lower via `storeAssign_lowers`; the
     `parseMethod` decode tree lowers definitionally.
   * `serveExport_serves_get` — for a GET request (req byte = `'G'` = 71) the emitted
     serve LANDS `bs200` byte-addressed at `out` and RETURNS `|bs200|` — the 200
     branch, end-to-end through decode + route + store + ret.
   * `serveExport_serves_405` — for a request whose method byte is none of
     {G,H,O,P} (witness byte `'X'` = 88) the emitted serve LANDS `bs405` and RETURNS
     `|bs405|` — the 405 branch, through all four failing decode compares.
   * `serveExport_serves_get_real` / `_405_real` — instantiated with the REAL emitted
     bytes `bytesOf (serialize resp200)` / `resp405` (`ServeSlice` responses through
     the shared `SerializeCompile.serialize`, the exact bytes the `.pnk` prints), so
     the emitted serve's behavior IS `serialize (miniServe tag)` = the serve spec.
   * NON-VACUITY: `serveExport_get_not_405` — the GET post-state's return value
     (`|serialize resp200|` = 164) is NOT the 405 return (`|serialize resp405|` = 227);
     the two branches are genuinely input-selected, so no branch is a `P → P` stub.

  RESIDUAL (named): `serveExport` decodes only the four method letters {G,H,O,P};
  other bytes route to 405 (proven on the witness byte). The byte-addressed landing
  is the faithful image of `serialize` (low-8 per address), the same postcondition
  shape as `serve_head_landsB`. Built per-file against the prebuilt olean set (the
  same pattern as LowerBridge / LowerBridgeSem — `ServeEmit` is not a lake root).

  AXIOM FOOTPRINT target: ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx,
  no native_decide / bv_decide.
-/
import Pancake.LowerBridgeSem

namespace Pancake.ServeExportServes

open Pancake
open Pancake.Lower (lower lowerStmt1 lowerStmtsFold lowerExp)
open Pancake.LowerBridge (addrModel storesIntoL storesModel lowerStmt1_storeb_off)
open Pancake.LowerBridgeSem
  (afterStore run_headStore load_afterStore_same load_afterStore_ne MemBytesAtB)
open Pancake.ServeEmit (serveExport storesInto parseMethod bytesOf)
open Pancake.SerializeCompile (serialize)
open Pancake.ServeSlice (resp200 resp405 miniServe)
open Dsl.EmitPancake (PStmt PExpr n v atOff eLt eEq eAdd)

variable {σ : Type}

/-! ## 0. A seq-reduction helper: `c1` returns `none` ⇒ `seq c1 c2` runs `c2` from `s1`. -/

theorem sem_seq_none_run (o : Oracle σ) {c1 c2 : PancakeProg} {s s1 : PancakeState σ}
    (h1 : PancakeSem o c1 s = (none, s1)) (hclk : s1.clock = s.clock) :
    PancakeSem o (.seq c1 c2) s = PancakeSem o c2 s1 := by
  have hcl : ({ s1 with clock := min s.clock s1.clock } : PancakeState σ) = s1 := by
    rw [hclk, Nat.min_self, ← hclk]
  rw [PancakeSem]
  simp only [h1, clampClock]
  rw [hcl]

/-! ## 1. The lowered route branch: a byte-store chain then `assign count`. -/

/-- The `lower`-image of `storesInto dst bs ++ [assign cnt k]`: a right-nested `Seq`
of `.storeByte` nodes ending in `.assign cnt (const k)`. Uniform two-case shape (the
empty tail folds to the bare assign). -/
def storeAssignModel (dst cnt : String) (k : Nat) : List (Nat × Nat) → PancakeProg
  | []      => .assign cnt (.const (BitVec.ofNat 64 k))
  | p :: ps => .seq (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2)))
                    (storeAssignModel dst cnt k ps)

/-- **SYNTACTIC bridge, the route branch (generic).** `lower`'s folder on the exact
`PStmt` list `storesIntoL dst ps ++ [assign cnt k]` equals the model `storeAssignModel`,
for ALL index/byte lists. Three-case structural recursion (mirrors `storesIntoL_lowers`);
every list element is a `.storeb` or the final `.assign`, so the `dec`-scoping branch
never fires. -/
theorem storeAssign_lowers (dst cnt : String) (k : Nat) :
    ∀ ps : List (Nat × Nat),
      lowerStmtsFold (storesIntoL dst ps ++ [PStmt.assign cnt (n k)])
        = some (storeAssignModel dst cnt k ps)
  | [] => by
      show lowerStmtsFold [PStmt.assign cnt (n k)] = some (storeAssignModel dst cnt k [])
      rw [lowerStmtsFold]
      show lowerStmt1 (PStmt.assign cnt (n k)) = some (storeAssignModel dst cnt k [])
      simp only [lowerStmt1, n, lowerExp, storeAssignModel]
  | [p] => by
      show lowerStmtsFold (PStmt.storeb (atOff (v dst) p.1) (n p.2) :: [PStmt.assign cnt (n k)])
          = some (storeAssignModel dst cnt k [p])
      show (match lowerStmt1 (PStmt.storeb (atOff (v dst) p.1) (n p.2)),
                  lowerStmtsFold [PStmt.assign cnt (n k)] with
            | some s', some r' => some (PancakeProg.seq s' r') | _, _ => none)
          = some (storeAssignModel dst cnt k [p])
      have hassign : lowerStmtsFold [PStmt.assign cnt (n k)]
          = some (.assign cnt (.const (BitVec.ofNat 64 k))) := by
        rw [lowerStmtsFold]; simp only [lowerStmt1, n, lowerExp]
      rw [lowerStmt1_storeb_off, hassign]
      rfl
  | p :: q :: ps'' => by
      have ih := storeAssign_lowers dst cnt k (q :: ps'')
      show lowerStmtsFold (PStmt.storeb (atOff (v dst) p.1) (n p.2)
              :: (storesIntoL dst (q :: ps'') ++ [PStmt.assign cnt (n k)]))
          = some (storeAssignModel dst cnt k (p :: q :: ps''))
      show (match lowerStmt1 (PStmt.storeb (atOff (v dst) p.1) (n p.2)),
                  lowerStmtsFold (storesIntoL dst (q :: ps'') ++ [PStmt.assign cnt (n k)]) with
            | some s', some r' => some (PancakeProg.seq s' r') | _, _ => none)
          = some (storeAssignModel dst cnt k (p :: q :: ps''))
      rw [lowerStmt1_storeb_off, ih]
      rfl

/-- The route branch on the real emitter's `storesInto`: `storesInto dst bs` is
definitionally `storesIntoL dst ((range |bs|).zip bs)`, so the emitted route branch
lowers to `storeAssignModel` for EVERY byte list. -/
theorem storesIntoAssign_lowers (dst cnt : String) (bs : List Nat) :
    lowerStmtsFold (storesInto dst bs ++ [PStmt.assign cnt (n bs.length)])
      = some (storeAssignModel dst cnt bs.length ((List.range bs.length).zip bs)) := by
  show lowerStmtsFold (storesIntoL dst ((List.range bs.length).zip bs)
          ++ [PStmt.assign cnt (n bs.length)]) = _
  exact storeAssign_lowers dst cnt bs.length ((List.range bs.length).zip bs)

/-! ## 2. The SEMANTIC run of the route branch: lands the bytes, sets `count`. -/

/-- **THE ROUTE-BRANCH RUN (induction).** Running the model route branch from a state
whose `dst` holds `base` lands each byte at its address (read back via the faithful
`memLoadByte`), sets `cnt := k`, preserves the memory-domain/endianness/clock, and
leaves every un-written byte address untouched (the byte-level frame). Mirror of
`LowerBridgeSem.storesRun` with the terminal `assign cnt k`. -/
theorem storeAssignRun (o : Oracle σ) (dst cnt : String) (base : Word) (k : Nat) :
    ∀ (ps : List (Nat × Nat)) (s : PancakeState σ),
      s.locals dst = some base →
      (∀ p ∈ ps, s.memaddrs (byteAlign (base + BitVec.ofNat 64 p.1)) = true) →
      (∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.1 →
          base + BitVec.ofNat 64 p.1 ≠ base + BitVec.ofNat 64 q.1) →
      (ps.map Prod.fst).Nodup →
      ∃ s', PancakeSem o (storeAssignModel dst cnt k ps) s = (none, s')
        ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.clock = s.clock
        ∧ s'.locals cnt = some (BitVec.ofNat 64 k)
        ∧ (∀ p ∈ ps, memLoadByte s'.memory s.memaddrs s.be
              (base + BitVec.ofNat 64 p.1) = some ((BitVec.ofNat 64 p.2).setWidth 8))
        ∧ (∀ adr', (∀ p ∈ ps, adr' ≠ base + BitVec.ofNat 64 p.1) →
              memLoadByte s'.memory s.memaddrs s.be adr'
                = memLoadByte s.memory s.memaddrs s.be adr') := by
  intro ps
  induction ps with
  | nil =>
    intro s _ _ _ _
    refine ⟨{ s with locals := setLocal s.locals cnt (BitVec.ofNat 64 k) }, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show PancakeSem o (.assign cnt (.const (BitVec.ofNat 64 k))) s = _
      simp only [PancakeSem, eval]
    · show setLocal s.locals cnt (BitVec.ofNat 64 k) cnt = some (BitVec.ofNat 64 k)
      simp [setLocal]
    · intro p hp; simp at hp
    · intro adr' _; rfl
  | cons p ps' ih =>
    intro s hbase haddr hdist hnodup
    have haddrp : s.memaddrs (byteAlign (base + BitVec.ofNat 64 p.1)) = true := haddr p (by simp)
    have hhead : PancakeSem o (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2))) s
        = (none, afterStore s (base + BitVec.ofNat 64 p.1) ((BitVec.ofNat 64 p.2).setWidth 8)) :=
      run_headStore o s dst base p.1 p.2 hbase haddrp
    have hnodupT : (ps'.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hnodup)).2
    have hpnotin : p.1 ∉ ps'.map Prod.fst := (List.nodup_cons.mp (by simpa using hnodup)).1
    have hne_off : ∀ q ∈ ps', p.1 ≠ q.1 := by
      intro q hq hqe; exact hpnotin (by rw [hqe]; exact List.mem_map_of_mem hq)
    have hne_adr : ∀ q ∈ ps', (base + BitVec.ofNat 64 p.1) ≠ base + BitVec.ofNat 64 q.1 := by
      intro q hq; exact hdist p (by simp) q (by simp [hq]) (hne_off q hq)
    -- the wrapped afterStore state (locals updated by the eventual assign is inside ih/base)
    have hclk : (afterStore s (base + BitVec.ofNat 64 p.1) ((BitVec.ofNat 64 p.2).setWidth 8)).clock
        = s.clock := rfl
    obtain ⟨s', hsem, hma, hbe, hcl, hcnt, hland, hframe⟩ :=
      ih (afterStore s (base + BitVec.ofNat 64 p.1) ((BitVec.ofNat 64 p.2).setWidth 8))
         hbase
         (by intro r hr; exact haddr r (by simp [hr]))
         (by intro a ha b hb hab; exact hdist a (by simp [ha]) b (by simp [hb]) hab)
         hnodupT
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- storeAssignModel (p::ps') = seq (storeByte p) (storeAssignModel ps')
      show PancakeSem o (.seq (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2)))
              (storeAssignModel dst cnt k ps')) s = (none, s')
      rw [sem_seq_none_run o hhead hclk]; exact hsem
    · rw [hma]; rfl
    · rw [hbe]; rfl
    · rw [hcl]; rfl
    · exact hcnt
    · intro p' hp'
      rcases List.mem_cons.mp hp' with hpe | hin
      · subst p'
        have h1 := hframe (base + BitVec.ofNat 64 p.1) hne_adr
        simp only [LowerBridgeSem.afterStore_memaddrs, LowerBridgeSem.afterStore_be] at h1
        rw [h1]
        exact load_afterStore_same s (base + BitVec.ofNat 64 p.1) _ haddrp
      · have h2 := hland p' hin
        simp only [LowerBridgeSem.afterStore_memaddrs, LowerBridgeSem.afterStore_be] at h2
        exact h2
    · intro adr' hfrall
      have h1 := hframe adr' (by intro r hr; exact hfrall r (by simp [hr]))
      simp only [LowerBridgeSem.afterStore_memaddrs, LowerBridgeSem.afterStore_be] at h1
      rw [h1]
      exact load_afterStore_ne s (base + BitVec.ofNat 64 p.1) adr' _ (hfrall p (by simp))

/-- **ROUTE-BRANCH LANDING (byte-addressed).** Running the model route branch that the
emitted branch lowers to lands `bs` byte-addressed at `base` (a `MemBytesAtB`) and sets
`cnt := k`. Derived from `storeAssignRun` on the zip, exactly as `storesModel_landsB`. -/
theorem storeAssign_landsB (o : Oracle σ) (dst cnt : String) (base : Word) (k : Nat)
    (bs : List Nat) (s : PancakeState σ)
    (hbase : s.locals dst = some base)
    (haddr : ∀ i, i < bs.length → s.memaddrs (byteAlign (base + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs.length → j < bs.length → i ≠ j →
        base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j) :
    ∃ s', PancakeSem o (storeAssignModel dst cnt k ((List.range bs.length).zip bs)) s = (none, s')
      ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.clock = s.clock
      ∧ s'.locals cnt = some (BitVec.ofNat 64 k)
      ∧ MemBytesAtB s'.memory s.memaddrs s.be base bs := by
  obtain ⟨s', hsem, hma, hbe, hcl, hcnt, hland, _⟩ :=
    storeAssignRun o dst cnt base k ((List.range bs.length).zip bs) s hbase
      (by intro p hp; obtain ⟨a, b⟩ := p
          exact haddr a (by simpa using (List.of_mem_zip hp).1))
      (by intro p hp q hq hpq; obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
          exact hinj a c (by simpa using (List.of_mem_zip hp).1)
                        (by simpa using (List.of_mem_zip hq).1) hpq)
      (by rw [List.map_fst_zip (by simp)]; exact List.nodup_range)
  refine ⟨s', hsem, hma, hbe, hcl, hcnt, ?_⟩
  intro i hi
  have hmem : (i, bs[i]!) ∈ (List.range bs.length).zip bs := by
    have hlen : i < ((List.range bs.length).zip bs).length := by simp [List.length_zip, hi]
    have hz : ((List.range bs.length).zip bs)[i] = (i, bs[i]!) := by
      rw [List.getElem_zip]; simp [List.getElem_range, hi, getElem!_pos]
    rw [← hz]; exact List.getElem_mem hlen
  have hh := hland (i, bs[i]!) hmem
  simpa using hh

/-! ## 3. The whole emitted PFun, lowered — `serveExport_lowers`. -/

/-- The `parseMethod` decode tree, lowered (concrete — reduces definitionally). Sets
`method` to the routing tag the request's first byte(s) select. -/
def decodeModel : PancakeProg :=
  .cond (.cmp .equal (.loadByte (.var "req")) (.const (BitVec.ofNat 64 71)))
    (.assign "method" (.const (BitVec.ofNat 64 0)))
    (.cond (.cmp .equal (.loadByte (.var "req")) (.const (BitVec.ofNat 64 72)))
      (.assign "method" (.const (BitVec.ofNat 64 2)))
      (.cond (.cmp .equal (.loadByte (.var "req")) (.const (BitVec.ofNat 64 79)))
        (.assign "method" (.const (BitVec.ofNat 64 3)))
        (.cond (.cmp .equal (.loadByte (.var "req")) (.const (BitVec.ofNat 64 80)))
          (.cond (.cmp .equal
                    (.loadByte (.op .add (.var "req") (.const (BitVec.ofNat 64 1))))
                    (.const (BitVec.ofNat 64 79)))
            (.assign "method" (.const (BitVec.ofNat 64 1)))
            (.assign "method" (.const (BitVec.ofNat 64 9))))
          (.assign "method" (.const (BitVec.ofNat 64 9))))))

/-- The whole emitted serve, lowered: bind `method`, decode, bind `count`, route on
`method < 4`, store the selected response + `assign count`, `ret count`. This is
EXACTLY `lower (serveExport bs200 bs405)` (proved next). -/
def serveModel (bs200 bs405 : List Nat) : PancakeProg :=
  .dec "method" (.const (BitVec.ofNat 64 9))
    (.seq decodeModel
      (.dec "count" (.const (BitVec.ofNat 64 0))
        (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
                (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
                (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
          (.ret (.var "count")))))

/-- **SYNTACTIC bridge over the WHOLE PFun.** `lower` on the emitted serve equals the
named `serveModel`, for ALL response byte lists. The decode tree lowers definitionally;
the two routing branches lower via `storesIntoAssign_lowers`. -/
theorem serveExport_lowers (bs200 bs405 : List Nat) :
    lower (serveExport bs200 bs405) = some (serveModel bs200 bs405) := by
  have e200 : lowerStmtsFold (storesInto "out" bs200 ++ [PStmt.assign "count" (PExpr.const bs200.length)])
      = some (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200)) :=
    storesIntoAssign_lowers "out" "count" bs200
  have e405 : lowerStmtsFold (storesInto "out" bs405 ++ [PStmt.assign "count" (PExpr.const bs405.length)])
      = some (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)) :=
    storesIntoAssign_lowers "out" "count" bs405
  show lowerStmtsFold (serveExport bs200 bs405).body = some (serveModel bs200 bs405)
  simp only [serveExport, parseMethod, List.cons_append, List.nil_append,
             lowerStmtsFold, lowerStmt1, lowerExp, n, v, eLt, eEq, eAdd, atOff,
             Nat.reduceBEq]
  rw [e200, e405]
  rfl

/-! ## 4. Reduction helpers for the control flow (`cond` / `dec`) and local lookups. -/

theorem setLocal_ne (L : String → Option Value) (var : String) (val : Value) (k : String)
    (h : k ≠ var) : setLocal L var val k = L k := by simp only [setLocal, if_neg h]

theorem setLocal_eq (L : String → Option Value) (var : String) (val : Value) :
    setLocal L var val var = some val := by simp [setLocal]

/-- `cond` with a `1`-guard runs the THEN branch to `(res, s')`. -/
theorem cond_then_run (o : Oracle σ) (s : PancakeState σ) (e : PancakeExp) (c1 c2 : PancakeProg)
    {res : Option Result} {s' : PancakeState σ}
    (h : eval s e = some 1) (hc1 : PancakeSem o c1 s = (res, s')) :
    PancakeSem o (.cond e c1 c2) s = (res, s') := by
  rw [PancakeSem]; simp only [h]; rw [if_pos (by decide : (1 : Word) ≠ 0)]; exact hc1

/-- `cond` with a `0`-guard runs the ELSE branch to `(res, s')`. -/
theorem cond_else_run (o : Oracle σ) (s : PancakeState σ) (e : PancakeExp) (c1 c2 : PancakeProg)
    {res : Option Result} {s' : PancakeState σ}
    (h : eval s e = some 0) (hc2 : PancakeSem o c2 s = (res, s')) :
    PancakeSem o (.cond e c1 c2) s = (res, s') := by
  rw [PancakeSem]; simp only [h]; rw [if_neg (by decide : ¬ ((0 : Word) ≠ 0))]; exact hc2

/-- `dec v e cont`: bind `v := val`, run `cont`, restore the old `v`. -/
theorem sem_dec_run (o : Oracle σ) (var : String) (e : PancakeExp) (cont : PancakeProg)
    (s : PancakeState σ) (val : Value) (heval : eval s e = some val)
    {res : Option Result} {s'' : PancakeState σ}
    (hcont : PancakeSem o cont { s with locals := setLocal s.locals var val } = (res, s'')) :
    PancakeSem o (.dec var e cont) s
      = (res, { s'' with locals := resVar s''.locals var (s.locals var) }) := by
  rw [PancakeSem]
  simp only [heval, hcont]

/-! ## 5. The `parseMethod` decode, semantically: request byte → routing tag. -/

/-- The `.loadByte (.var "req")` read, as a function of the memory byte. -/
theorem eval_loadReq (s : PancakeState σ) (reqAddr : Word) (b : BitVec 8)
    (hreq : s.locals "req" = some reqAddr)
    (hb : memLoadByte s.memory s.memaddrs s.be reqAddr = some b) :
    eval s (.loadByte (.var "req")) = some (b.setWidth 64) := by
  simp only [eval, hreq, hb]

/-- **DECODE, GET.** A request whose first byte is `'G'` (71) sets `method := 0`. -/
theorem decode_get (o : Oracle σ) (s : PancakeState σ) (reqAddr : Word)
    (hreq : s.locals "req" = some reqAddr)
    (hget : memLoadByte s.memory s.memaddrs s.be reqAddr = some (71 : BitVec 8)) :
    PancakeSem o decodeModel s
      = (none, { s with locals := setLocal s.locals "method" (BitVec.ofNat 64 0) }) := by
  have hev : eval s (.cmp .equal (.loadByte (.var "req")) (.const (BitVec.ofNat 64 71))) = some 1 := by
    simp only [eval, hreq, hget]
    rw [show ((71 : BitVec 8).setWidth 64) = BitVec.ofNat 64 71 from by decide]
    simp
  have hassign : PancakeSem o (.assign "method" (.const (BitVec.ofNat 64 0))) s
      = (none, { s with locals := setLocal s.locals "method" (BitVec.ofNat 64 0) }) := by
    rw [PancakeSem]; simp only [eval]
  rw [decodeModel]
  exact cond_then_run o s _ _ _ hev hassign

/-! ## 6. GET → 200, end-to-end: the emitted serve lands `bs200`, returns `|bs200|`. -/

/-- **CAPSTONE (200 branch).** Running the WHOLE emitted serve PFun's model on a GET
request (`out ↦ outBase`, `req ↦ reqAddr`, first byte `'G'`) LANDS `bs200`
byte-addressed at `out` and RETURNS `|bs200|` — decode + route + byte-store + ret,
one operational theorem. `outBase` is `bs200`-region-valid and injective (the region
preconditions); `req`/`out` are the emit's own locals. -/
theorem serveExport_serves_get (o : Oracle σ) (s : PancakeState σ)
    (bs200 bs405 : List Nat) (outBase reqAddr : Word)
    (hout : s.locals "out" = some outBase)
    (hreq : s.locals "req" = some reqAddr)
    (hget : memLoadByte s.memory s.memaddrs s.be reqAddr = some (71 : BitVec 8))
    (haddr : ∀ i, i < bs200.length → s.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs200.length → j < bs200.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ s', PancakeSem o (serveModel bs200 bs405) s
            = (some (.return_ (BitVec.ofNat 64 bs200.length)), s')
      ∧ MemBytesAtB s'.memory s.memaddrs s.be outBase bs200 := by
  -- state after `dec method 9`
  let s1 := ({ s with locals := setLocal s.locals "method" (BitVec.ofNat 64 9) } : PancakeState σ)
  have hreq1 : s1.locals "req" = some reqAddr := by
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "req" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hreq
  have hget1 : memLoadByte s1.memory s1.memaddrs s1.be reqAddr = some (71 : BitVec 8) := hget
  have hdecode := decode_get o s1 reqAddr hreq1 hget1
  -- state after decode (method := 0)
  let s2 := ({ s1 with locals := setLocal s1.locals "method" (BitVec.ofNat 64 0) } : PancakeState σ)
  -- state after `dec count 0`
  let s3 := ({ s2 with locals := setLocal s2.locals "count" (BitVec.ofNat 64 0) } : PancakeState σ)
  have hout3 : s3.locals "out" = some outBase := by
    show setLocal s2.locals "count" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hout
  have hs3ma : s3.memaddrs = s.memaddrs := rfl
  have hs3be : s3.be = s.be := rfl
  have haddr3 : ∀ i, i < bs200.length → s3.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true := by
    intro i hi; rw [hs3ma]; exact haddr i hi
  obtain ⟨s4, hrun4, hma4, hbe4, hcl4, hcnt4, hmb4⟩ :=
    storeAssign_landsB o "out" "count" outBase bs200.length bs200 s3 hout3 haddr3 hinj
  -- route guard evaluates to 1 (method = 0 < 4)
  have hmeth3 : s3.locals "method" = some (BitVec.ofNat 64 0) := by
    show setLocal s2.locals "count" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_eq]
  have hroute_ev : eval s3 (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4))) = some 1 := by
    simp only [eval, hmeth3]; decide
  -- route runs the 200 branch
  have hroute : PancakeSem o
      (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
        (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
        (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405))) s3
        = (none, s4) :=
    cond_then_run o s3 _ _ _ hroute_ev hrun4
  -- cont2 = seq route ret  ⇒  returns |bs200|
  have hcont2 : PancakeSem o
      (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
              (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
              (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
            (.ret (.var "count"))) s3
        = (some (.return_ (BitVec.ofNat 64 bs200.length)), emptyLocals s4) := by
    rw [sem_seq_none_run o hroute hcl4, PancakeSem]
    simp only [eval, hcnt4]
  -- innerdec = dec count 0 cont2
  have hinner : PancakeSem o
      (.dec "count" (.const (BitVec.ofNat 64 0))
        (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
                (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
                (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
              (.ret (.var "count")))) s2
        = (some (.return_ (BitVec.ofNat 64 bs200.length)),
           { emptyLocals s4 with locals := resVar (emptyLocals s4).locals "count" (s2.locals "count") }) := by
    exact sem_dec_run o "count" _ _ s2 (BitVec.ofNat 64 0) rfl hcont2
  -- cont1 = seq decode innerdec
  have hcont1 : PancakeSem o
      (.seq decodeModel
        (.dec "count" (.const (BitVec.ofNat 64 0))
          (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
                  (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
                  (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
                (.ret (.var "count"))))) s1
        = (some (.return_ (BitVec.ofNat 64 bs200.length)),
           { emptyLocals s4 with locals := resVar (emptyLocals s4).locals "count" (s2.locals "count") }) := by
    rw [sem_seq_none_run o hdecode rfl]; exact hinner
  -- whole serveModel = dec method 9 cont1
  have key := sem_dec_run o "method" (.const (BitVec.ofNat 64 9)) _ s (BitVec.ofNat 64 9) rfl hcont1
  exact ⟨_, key, hmb4⟩

/-! ## 7. Non-method byte → 405 branch, end-to-end (the other route, non-vacuity). -/

/-- **DECODE, non-method.** A request whose first byte is none of {G,H,O,P} (witness
`'X'` = 88) sets `method := 9` — through all four failing equality compares. -/
theorem decode_405 (o : Oracle σ) (s : PancakeState σ) (reqAddr : Word)
    (hreq : s.locals "req" = some reqAddr)
    (hb : memLoadByte s.memory s.memaddrs s.be reqAddr = some (88 : BitVec 8)) :
    PancakeSem o decodeModel s
      = (none, { s with locals := setLocal s.locals "method" (BitVec.ofNat 64 9) }) := by
  have hev : ∀ c : Nat, ((88 : BitVec 8).setWidth 64) ≠ BitVec.ofNat 64 c →
      eval s (.cmp .equal (.loadByte (.var "req")) (.const (BitVec.ofNat 64 c))) = some 0 := by
    intro c hc; simp only [eval, hreq, hb]; rw [if_neg hc]
  have hassign9 : PancakeSem o (.assign "method" (.const (BitVec.ofNat 64 9))) s
      = (none, { s with locals := setLocal s.locals "method" (BitVec.ofNat 64 9) }) := by
    rw [PancakeSem]; simp only [eval]
  rw [decodeModel]
  exact cond_else_run o s _ _ _ (hev 71 (by decide))
    (cond_else_run o s _ _ _ (hev 72 (by decide))
      (cond_else_run o s _ _ _ (hev 79 (by decide))
        (cond_else_run o s _ _ _ (hev 80 (by decide)) hassign9)))

/-- **CAPSTONE (405 branch).** Running the WHOLE emitted serve PFun's model on a
non-method request (first byte `'X'` = 88) LANDS `bs405` byte-addressed at `out` and
RETURNS `|bs405|` — decode (all four compares fail) + route (`9 < 4` false, else) +
byte-store + ret. -/
theorem serveExport_serves_405 (o : Oracle σ) (s : PancakeState σ)
    (bs200 bs405 : List Nat) (outBase reqAddr : Word)
    (hout : s.locals "out" = some outBase)
    (hreq : s.locals "req" = some reqAddr)
    (hbyte : memLoadByte s.memory s.memaddrs s.be reqAddr = some (88 : BitVec 8))
    (haddr : ∀ i, i < bs405.length → s.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs405.length → j < bs405.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ s', PancakeSem o (serveModel bs200 bs405) s
            = (some (.return_ (BitVec.ofNat 64 bs405.length)), s')
      ∧ MemBytesAtB s'.memory s.memaddrs s.be outBase bs405 := by
  let s1 := ({ s with locals := setLocal s.locals "method" (BitVec.ofNat 64 9) } : PancakeState σ)
  have hreq1 : s1.locals "req" = some reqAddr := by
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "req" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hreq
  have hbyte1 : memLoadByte s1.memory s1.memaddrs s1.be reqAddr = some (88 : BitVec 8) := hbyte
  have hdecode := decode_405 o s1 reqAddr hreq1 hbyte1
  let s2 := ({ s1 with locals := setLocal s1.locals "method" (BitVec.ofNat 64 9) } : PancakeState σ)
  let s3 := ({ s2 with locals := setLocal s2.locals "count" (BitVec.ofNat 64 0) } : PancakeState σ)
  have hout3 : s3.locals "out" = some outBase := by
    show setLocal s2.locals "count" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 9) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hout
  have hs3ma : s3.memaddrs = s.memaddrs := rfl
  have hs3be : s3.be = s.be := rfl
  have haddr3 : ∀ i, i < bs405.length → s3.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true := by
    intro i hi; rw [hs3ma]; exact haddr i hi
  obtain ⟨s4, hrun4, hma4, hbe4, hcl4, hcnt4, hmb4⟩ :=
    storeAssign_landsB o "out" "count" outBase bs405.length bs405 s3 hout3 haddr3 hinj
  have hmeth3 : s3.locals "method" = some (BitVec.ofNat 64 9) := by
    show setLocal s2.locals "count" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 9) "method" = _
    rw [setLocal_eq]
  have hroute_ev : eval s3 (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4))) = some 0 := by
    simp only [eval, hmeth3]; decide
  have hroute : PancakeSem o
      (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
        (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
        (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405))) s3
        = (none, s4) :=
    cond_else_run o s3 _ _ _ hroute_ev hrun4
  have hcont2 : PancakeSem o
      (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
              (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
              (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
            (.ret (.var "count"))) s3
        = (some (.return_ (BitVec.ofNat 64 bs405.length)), emptyLocals s4) := by
    rw [sem_seq_none_run o hroute hcl4, PancakeSem]
    simp only [eval, hcnt4]
  have hinner : PancakeSem o
      (.dec "count" (.const (BitVec.ofNat 64 0))
        (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
                (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
                (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
              (.ret (.var "count")))) s2
        = (some (.return_ (BitVec.ofNat 64 bs405.length)),
           { emptyLocals s4 with locals := resVar (emptyLocals s4).locals "count" (s2.locals "count") }) :=
    sem_dec_run o "count" _ _ s2 (BitVec.ofNat 64 0) rfl hcont2
  have hcont1 : PancakeSem o
      (.seq decodeModel
        (.dec "count" (.const (BitVec.ofNat 64 0))
          (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
                  (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
                  (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
                (.ret (.var "count"))))) s1
        = (some (.return_ (BitVec.ofNat 64 bs405.length)),
           { emptyLocals s4 with locals := resVar (emptyLocals s4).locals "count" (s2.locals "count") }) := by
    rw [sem_seq_none_run o hdecode rfl]; exact hinner
  have key := sem_dec_run o "method" (.const (BitVec.ofNat 64 9)) _ s (BitVec.ofNat 64 9) rfl hcont1
  exact ⟨_, key, hmb4⟩

/-! ## 8. Instantiated on the REAL emitted bytes — behavior = `serialize (miniServe tag)`. -/

/-- The real 200-response bytes the emitted `.pnk` prints. -/
abbrev BS200 : List Nat := bytesOf (serialize resp200)
/-- The real 405-response bytes the emitted `.pnk` prints. -/
abbrev BS405 : List Nat := bytesOf (serialize resp405)

/-- **REAL, GET → 200.** The EMITTED serve (`serveExport BS200 BS405`, the exact PFun
`ppFun`-printed to `serve_slice_export.pnk`) lowers to `P`, and running `P` on a GET
lands `bytesOf (serialize resp200)` at `out` and returns its length — i.e.
`behavior(emitted .pnk) = serialize resp200 = serialize (miniServe 0)`, the serve spec. -/
theorem serveExport_serves_get_real (o : Oracle σ) (s : PancakeState σ) (outBase reqAddr : Word)
    (hout : s.locals "out" = some outBase)
    (hreq : s.locals "req" = some reqAddr)
    (hget : memLoadByte s.memory s.memaddrs s.be reqAddr = some (71 : BitVec 8))
    (haddr : ∀ i, i < BS200.length → s.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < BS200.length → j < BS200.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ P s', lower (serveExport BS200 BS405) = some P
      ∧ PancakeSem o P s = (some (.return_ (BitVec.ofNat 64 BS200.length)), s')
      ∧ MemBytesAtB s'.memory s.memaddrs s.be outBase BS200 := by
  obtain ⟨s', hsem, hmb⟩ :=
    serveExport_serves_get o s BS200 BS405 outBase reqAddr hout hreq hget haddr hinj
  exact ⟨serveModel BS200 BS405, s', serveExport_lowers BS200 BS405, hsem, hmb⟩

/-- **REAL, non-method → 405.** The same EMITTED serve on a non-method request lands
`bytesOf (serialize resp405)` and returns its length — `= serialize (miniServe 9)`. -/
theorem serveExport_serves_405_real (o : Oracle σ) (s : PancakeState σ) (outBase reqAddr : Word)
    (hout : s.locals "out" = some outBase)
    (hreq : s.locals "req" = some reqAddr)
    (hbyte : memLoadByte s.memory s.memaddrs s.be reqAddr = some (88 : BitVec 8))
    (haddr : ∀ i, i < BS405.length → s.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < BS405.length → j < BS405.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ P s', lower (serveExport BS200 BS405) = some P
      ∧ PancakeSem o P s = (some (.return_ (BitVec.ofNat 64 BS405.length)), s')
      ∧ MemBytesAtB s'.memory s.memaddrs s.be outBase BS405 := by
  obtain ⟨s', hsem, hmb⟩ :=
    serveExport_serves_405 o s BS200 BS405 outBase reqAddr hout hreq hbyte haddr hinj
  exact ⟨serveModel BS200 BS405, s', serveExport_lowers BS200 BS405, hsem, hmb⟩

/-! ## 9. NON-VACUITY — the route is genuinely input-selected (not a `P → P` stub).

The GET post-state returns `|serialize resp200|` (164); the 405 post-state returns
`|serialize resp405|` (227). The two differ, so the branch is a real function of the
request byte: no branch's conclusion holds on the other branch's pre-state. -/

-- The two responses serialize to DIFFERENT lengths (164 vs 227) — the branches differ.
-- (`serialize` is WF-recursive, so only the native `#guard` evaluator reduces it, not the
--  kernel; these are the machine-checked numeric witnesses that the lengths genuinely differ.)
#guard BS200.length = 164
#guard BS405.length = 227
#guard BS200.length ≠ BS405.length

/-- Distinct in-range lengths give distinct `BitVec` return values (the general,
kernel-clean fact). With the `#guard`s above (`|BS200| = 164 ≠ 227 = |BS405|`, both
`< 2⁶⁴`) this says the GET and 405 branches RETURN different observables — so
`serveExport_serves_get`'s conclusion (`return_ (ofNat |BS200|)`) is FALSE on a 405
pre-state, where the run returns `ofNat |BS405|` (`serveExport_serves_405`): the
route is a genuine, non-vacuous function of the request byte. -/
theorem ofNat_len_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    (BitVec.ofNat 64 a) ≠ (BitVec.ofNat 64 b) := by
  intro heq
  apply h
  have hh := congrArg BitVec.toNat heq
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hh

/-! ## 10. Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx. -/

#print axioms serveExport_lowers
#print axioms storeAssign_landsB
#print axioms serveExport_serves_get
#print axioms serveExport_serves_405
#print axioms serveExport_serves_get_real
#print axioms serveExport_serves_405_real
#print axioms ofNat_len_ne

end Pancake.ServeExportServes
