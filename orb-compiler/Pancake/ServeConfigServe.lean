/-
  Pancake/ServeConfigServe.lean — TRACK 2 PHASE B: the emitted serve READS the
  config frame the host already delivers (config-as-data on the compiled path).

  Phase A (`ServeExportServes.serveExport_serves`) proved the WHOLE emitted serve
  PFun's behaviour equals the serve spec — but the serve routed on the request
  METHOD only and baked the 200 response as an emit-time literal, IGNORING the
  `cfgLen(4 BE) :: config :: request` frame the host peels (`drorb
  crates/dataplane/src/cake_serve.rs::unframe`). This file makes ONE decision
  config-driven — an HSTS on/off toggle read from `config[0]` — and re-runs the
  Phase-A bridge over the EXTENDED PFun (`serveExportCfg`). Each extension is a
  THEOREM, not a golden `.bin` diff — the reason Phase A had to land first.

  WHAT IS PROVEN (all OPERATIONAL, `execute = spec` on a real post-state):
   * `serveExportCfg_lowers` — SYNTACTIC bridge over the WHOLE extended PFun:
     `lower (serveExportCfg bs200 bs200Alt bs405) = some (serveModelCfg …)`, ∀ byte
     lists — the config read (4-BE `cfgLen`, the `clen ≠ 0` gate, the toggle read)
     and the nested 200-branch route lower faithfully.
   * `serveExportCfg_serves_get_default` — ★THE REGRESSION PIN: a GET with an EMPTY
     config frame (`cfgLen = 0`, the 4 length bytes are `0`) lands `bs200`
     byte-addressed and returns `|bs200|` — INDEPENDENT of `bs200Alt`. The empty
     frame reproduces today's baked-literal behaviour EXACTLY, as a theorem.
   * `serveExportCfg_serves_405_default` — a non-method request on the empty frame
     lands `bs405` (the 405 branch, config-independent).
   * `serveExportCfg_serves_get_present` — ★THE CONFIG-DRIVEN DECISION: a GET with a
     PRESENT config (`cfgLen = 1`, `config[0] = 1`) lands `bs200Alt` and returns
     `|bs200Alt|` — the response head is a genuine FUNCTION of the config frame.
   * `serveExportCfg_default_real_get` / `_405` — instantiated on the REAL emitted
     bytes `BS200`/`BS405` (`serialize resp200/405`): the empty-frame serve lands
     exactly the bytes today's `serveExport` lands (byte-identical-to-today pin).
   * NON-VACUITY: `serveExportCfg_return_config_dependent` — distinct 200-template
     lengths give distinct return `BitVec`s, so `_default` (returns `|bs200|`) and
     `_present` (returns `|bs200Alt|`) genuinely disagree: the route is a real
     function of the config frame, not a `P → P` stub.

  RESIDUAL (named): the config drives ONE decision (the 200-branch HSTS toggle);
  the 405 branch is config-independent; `bs200Alt` is a free byte list (wiring a
  concrete HSTS-on response corpus is downstream). The `ctrl` param is the
  config-frame base (`cfgLen(4 BE) :: config`); the drorb host owns handing it in
  (the serve-config lane). Built as a lakefile root over the prebuilt chain.

  AXIOM FOOTPRINT target: ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx,
  no native_decide / bv_decide.
-/
import Pancake.ServeExportServes

namespace Pancake.ServeConfigServe

open Pancake
open Pancake.Lower (lower lowerStmtsFold lowerStmt1 lowerExp)
open Pancake.LowerBridge (storesModel storesIntoL)
open Pancake.LowerBridgeSem (MemBytesAtB)
open Pancake.ServeExportServes
  (storeAssignModel storeAssign_landsB storesIntoAssign_lowers decodeModel decode_get decode_405
   cond_then_run cond_else_run sem_dec_run sem_seq_none_run setLocal_ne setLocal_eq
   ofNat_len_ne BS200 BS405)
open Pancake.ServeEmit (serveExportCfg readCfg be4 storesInto parseMethod bytesOf)
open Dsl.EmitPancake (PStmt PExpr n v atOff eLt eEq eAdd eMul)

variable {σ : Type}

/-! ## 1. The lowered 4-BE length expression, and its evaluation. -/

/-- The `lower`-image of `be4 (v c)`: the byte-addressed 4-BE assembly
`((b0*256 + b1)*256 + b2)*256 + b3` in the model expression language (`.mul` /
`.op .add` / `.loadByte`). This is EXACTLY `lowerExp (be4 (v c))` (checked by
`serveExportCfg_lowers`'s `rfl`). -/
def be4model (c : String) : PancakeExp :=
  .op .add
    (.mul (.op .add
            (.mul (.op .add
                    (.mul (.loadByte (.var c)) (.const (BitVec.ofNat 64 256)))
                    (.loadByte (.op .add (.var c) (.const (BitVec.ofNat 64 1)))))
                  (.const (BitVec.ofNat 64 256)))
            (.loadByte (.op .add (.var c) (.const (BitVec.ofNat 64 2)))))
          (.const (BitVec.ofNat 64 256)))
    (.loadByte (.op .add (.var c) (.const (BitVec.ofNat 64 3))))

/-- **The 4-BE length read, semantically.** With `ctrl ↦ cfgBase` and the four
length bytes readable byte-addressed, `eval be4model` is the assembled big-endian
value — the same `u32::from_be_bytes` the host writes (each `w2w` byte→word is
`setWidth 64`). -/
theorem eval_be4model (s : PancakeState σ) (cfgBase : Word) (b0 b1 b2 b3 : BitVec 8)
    (hc : s.locals "ctrl" = some cfgBase)
    (h0 : memLoadByte s.memory s.memaddrs s.be cfgBase = some b0)
    (h1 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 1) = some b1)
    (h2 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 2) = some b2)
    (h3 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 3) = some b3) :
    eval s (be4model "ctrl") = some
      ((((b0.setWidth 64) * BitVec.ofNat 64 256 + b1.setWidth 64) * BitVec.ofNat 64 256
          + b2.setWidth 64) * BitVec.ofNat 64 256 + b3.setWidth 64) := by
  simp only [be4model, eval, hc, h0, h1, h2, h3]

/-- Empty config frame (`cfgLen = 0`): the four length bytes are `0` ⇒ `eval
be4model = 0`. This is what makes the `clen == 0` gate fire on the empty frame. -/
theorem eval_be4model_zero (s : PancakeState σ) (cfgBase : Word)
    (hc : s.locals "ctrl" = some cfgBase)
    (h0 : memLoadByte s.memory s.memaddrs s.be cfgBase = some (0 : BitVec 8))
    (h1 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 1) = some (0 : BitVec 8))
    (h2 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 2) = some (0 : BitVec 8))
    (h3 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 3) = some (0 : BitVec 8)) :
    eval s (be4model "ctrl") = some (BitVec.ofNat 64 0) := by
  rw [eval_be4model s cfgBase 0 0 0 0 hc h0 h1 h2 h3]; decide

/-- Present config frame `00 00 00 01` (`cfgLen = 1`): `eval be4model = 1`, so the
`clen == 0` gate is FALSE and the toggle byte is read. -/
theorem eval_be4model_one (s : PancakeState σ) (cfgBase : Word)
    (hc : s.locals "ctrl" = some cfgBase)
    (h0 : memLoadByte s.memory s.memaddrs s.be cfgBase = some (0 : BitVec 8))
    (h1 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 1) = some (0 : BitVec 8))
    (h2 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 2) = some (0 : BitVec 8))
    (h3 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 3) = some (1 : BitVec 8)) :
    eval s (be4model "ctrl") = some (BitVec.ofNat 64 1) := by
  rw [eval_be4model s cfgBase 0 0 0 1 hc h0 h1 h2 h3]; decide

/-! ## 2. The whole extended PFun, lowered — `serveExportCfg_lowers`. -/

/-- The model image of the extended serve: bind `method`, decode, bind `hsts`
(default 0), bind `clen` (the 4-BE length), gate the toggle read on `clen == 0`,
bind `count`, route on `method < 4` with the nested `hsts == 0` 200-branch, `ret
count`. This is EXACTLY `lower (serveExportCfg …)` (proved next). -/
def serveModelCfg (bs200 bs200Alt bs405 : List Nat) : PancakeProg :=
  .dec "method" (.const (BitVec.ofNat 64 9))
    (.seq decodeModel
      (.dec "hsts" (.const (BitVec.ofNat 64 0))
        (.dec "clen" (be4model "ctrl")
          (.seq (.cond (.cmp .equal (.var "clen") (.const (BitVec.ofNat 64 0)))
                    .skip
                    (.assign "hsts" (.loadByte (.op .add (.var "ctrl") (.const (BitVec.ofNat 64 4))))))
            (.dec "count" (.const (BitVec.ofNat 64 0))
              (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
                      (.cond (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0)))
                        (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
                        (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt)))
                      (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
                (.ret (.var "count"))))))))

/-- **SYNTACTIC bridge over the WHOLE extended PFun.** `lower` on the emitted
config-serve equals the named `serveModelCfg`, for ALL response byte lists. The
config-read prefix lowers definitionally (`be4`, the `clen==0` gate, the toggle
read); the three routing branches lower via `storesIntoAssign_lowers`. -/
theorem serveExportCfg_lowers (bs200 bs200Alt bs405 : List Nat) :
    lower (serveExportCfg bs200 bs200Alt bs405) = some (serveModelCfg bs200 bs200Alt bs405) := by
  -- stated with `PExpr.const` (not `n`) to match the `n`-unfolded goal after simp
  have e200 : lowerStmtsFold (storesInto "out" bs200 ++ [PStmt.assign "count" (PExpr.const bs200.length)])
      = some (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200)) :=
    storesIntoAssign_lowers "out" "count" bs200
  have e200Alt : lowerStmtsFold (storesInto "out" bs200Alt ++ [PStmt.assign "count" (PExpr.const bs200Alt.length)])
      = some (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt)) :=
    storesIntoAssign_lowers "out" "count" bs200Alt
  have e405 : lowerStmtsFold (storesInto "out" bs405 ++ [PStmt.assign "count" (PExpr.const bs405.length)])
      = some (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)) :=
    storesIntoAssign_lowers "out" "count" bs405
  show lowerStmtsFold (serveExportCfg bs200 bs200Alt bs405).body = some (serveModelCfg bs200 bs200Alt bs405)
  simp only [serveExportCfg, readCfg, be4, parseMethod, List.cons_append, List.nil_append,
             lowerStmtsFold, lowerStmt1, lowerExp, n, v, eLt, eEq, eMul, eAdd, atOff,
             Nat.reduceBEq]
  rw [e200, e200Alt, e405]
  rfl

/-! ## 3. GET + EMPTY frame → 200 default, end-to-end (THE REGRESSION PIN). -/

/-- **CAPSTONE — the `cfgLen = 0` regression pin (200 branch).** Running the WHOLE
extended serve on a GET whose config frame is EMPTY (the 4 length bytes are `0`)
lands `bs200` byte-addressed at `out` and returns `|bs200|` — INDEPENDENT of
`bs200Alt`. The empty frame reproduces today's baked-literal 200 behaviour exactly.
Decode + config-read (gate fires, toggle stays 0) + route + nested 200-default +
byte-store + ret, one operational theorem. -/
theorem serveExportCfg_serves_get_default (o : Oracle σ) (s : PancakeState σ)
    (bs200 bs200Alt bs405 : List Nat) (outBase reqAddr cfgBase : Word)
    (hout : s.locals "out" = some outBase)
    (hreq : s.locals "req" = some reqAddr)
    (hctrl : s.locals "ctrl" = some cfgBase)
    (hget : memLoadByte s.memory s.memaddrs s.be reqAddr = some (71 : BitVec 8))
    (hc0 : memLoadByte s.memory s.memaddrs s.be cfgBase = some (0 : BitVec 8))
    (hc1 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 1) = some (0 : BitVec 8))
    (hc2 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 2) = some (0 : BitVec 8))
    (hc3 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 3) = some (0 : BitVec 8))
    (haddr : ∀ i, i < bs200.length → s.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs200.length → j < bs200.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ s', PancakeSem o (serveModelCfg bs200 bs200Alt bs405) s
            = (some (.return_ (BitVec.ofNat 64 bs200.length)), s')
      ∧ MemBytesAtB s'.memory s.memaddrs s.be outBase bs200 := by
  let s1 : PancakeState σ := { s with locals := setLocal s.locals "method" (BitVec.ofNat 64 9) }
  have hreq1 : s1.locals "req" = some reqAddr := by
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "req" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hreq
  have hget1 : memLoadByte s1.memory s1.memaddrs s1.be reqAddr = some (71 : BitVec 8) := hget
  have hdecode := decode_get o s1 reqAddr hreq1 hget1
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "method" (BitVec.ofNat 64 0) }
  let s3 : PancakeState σ := { s2 with locals := setLocal s2.locals "hsts" (BitVec.ofNat 64 0) }
  have hctrl3 : s3.locals "ctrl" = some cfgBase := by
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 0) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hctrl
  have he4 : eval s3 (be4model "ctrl") = some (BitVec.ofNat 64 0) :=
    eval_be4model_zero s3 cfgBase hctrl3 hc0 hc1 hc2 hc3
  let s4 : PancakeState σ := { s3 with locals := setLocal s3.locals "clen" (BitVec.ofNat 64 0) }
  have hclen4 : s4.locals "clen" = some (BitVec.ofNat 64 0) := by
    show setLocal s3.locals "clen" (BitVec.ofNat 64 0) "clen" = _
    rw [setLocal_eq]
  have hcondev : eval s4 (.cmp .equal (.var "clen") (.const (BitVec.ofNat 64 0))) = some 1 := by
    simp only [eval, hclen4]; decide
  have hskip : PancakeSem o (PancakeProg.skip) s4 = (none, s4) := by rw [PancakeSem]
  have hcondrun : PancakeSem o (.cond (.cmp .equal (.var "clen") (.const (BitVec.ofNat 64 0)))
        .skip (.assign "hsts" (.loadByte (.op .add (.var "ctrl") (.const (BitVec.ofNat 64 4)))))) s4
        = (none, s4) :=
    cond_then_run o s4 _ _ _ hcondev hskip
  let s5 : PancakeState σ := { s4 with locals := setLocal s4.locals "count" (BitVec.ofNat 64 0) }
  have hout5 : s5.locals "out" = some outBase := by
    show setLocal s4.locals "count" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s3.locals "clen" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hout
  have hs5ma : s5.memaddrs = s.memaddrs := rfl
  have haddr5 : ∀ i, i < bs200.length → s5.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true := by
    intro i hi; rw [hs5ma]; exact haddr i hi
  obtain ⟨s6, hrun6, hma6, hbe6, hcl6, hcnt6, hmb6⟩ :=
    storeAssign_landsB o "out" "count" outBase bs200.length bs200 s5 hout5 haddr5 hinj
  have hmeth5 : s5.locals "method" = some (BitVec.ofNat 64 0) := by
    show setLocal s4.locals "count" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s3.locals "clen" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_eq]
  have hhsts5 : s5.locals "hsts" = some (BitVec.ofNat 64 0) := by
    show setLocal s4.locals "count" (BitVec.ofNat 64 0) "hsts" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s3.locals "clen" (BitVec.ofNat 64 0) "hsts" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "hsts" = _
    rw [setLocal_eq]
  have hinnerev : eval s5 (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0))) = some 1 := by
    simp only [eval, hhsts5]; decide
  have hinnerrun : PancakeSem o (.cond (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0)))
        (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
        (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt))) s5
        = (none, s6) :=
    cond_then_run o s5 _ _ _ hinnerev hrun6
  have hrouteev : eval s5 (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4))) = some 1 := by
    simp only [eval, hmeth5]; decide
  have hroute : PancakeSem o (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
        (.cond (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0)))
          (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
          (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt)))
        (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405))) s5
        = (none, s6) :=
    cond_then_run o s5 _ _ _ hrouteev hinnerrun
  have hcont2 : PancakeSem o (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
          (.cond (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0)))
            (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
            (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt)))
          (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
        (.ret (.var "count"))) s5
        = (some (.return_ (BitVec.ofNat 64 bs200.length)), emptyLocals s6) := by
    rw [sem_seq_none_run o hroute hcl6, PancakeSem]
    simp only [eval, hcnt6]
  have hinner := sem_dec_run o "count" (.const (BitVec.ofNat 64 0)) _ s4 (BitVec.ofNat 64 0) rfl hcont2
  have hafterclen := (sem_seq_none_run o hcondrun rfl).trans hinner
  have hdecclen := sem_dec_run o "clen" (be4model "ctrl") _ s3 (BitVec.ofNat 64 0) he4 hafterclen
  have hdechsts := sem_dec_run o "hsts" (.const (BitVec.ofNat 64 0)) _ s2 (BitVec.ofNat 64 0) rfl hdecclen
  have hcont1 := (sem_seq_none_run o hdecode rfl).trans hdechsts
  have key := sem_dec_run o "method" (.const (BitVec.ofNat 64 9)) _ s (BitVec.ofNat 64 9) rfl hcont1
  exact ⟨_, key, hmb6⟩

/-! ## 4. Non-method + EMPTY frame → 405 (config-independent). -/

/-- **CAPSTONE (405 branch, empty frame).** A non-method request (`'X'` = 88) on
the empty frame lands `bs405` and returns `|bs405|` — decode (all four compares
fail) + config-read (gate fires, toggle 0) + route (`9 < 4` false, else). The 405
branch is config-independent. -/
theorem serveExportCfg_serves_405_default (o : Oracle σ) (s : PancakeState σ)
    (bs200 bs200Alt bs405 : List Nat) (outBase reqAddr cfgBase : Word)
    (hout : s.locals "out" = some outBase)
    (hreq : s.locals "req" = some reqAddr)
    (hctrl : s.locals "ctrl" = some cfgBase)
    (hbyte : memLoadByte s.memory s.memaddrs s.be reqAddr = some (88 : BitVec 8))
    (hc0 : memLoadByte s.memory s.memaddrs s.be cfgBase = some (0 : BitVec 8))
    (hc1 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 1) = some (0 : BitVec 8))
    (hc2 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 2) = some (0 : BitVec 8))
    (hc3 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 3) = some (0 : BitVec 8))
    (haddr : ∀ i, i < bs405.length → s.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs405.length → j < bs405.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ s', PancakeSem o (serveModelCfg bs200 bs200Alt bs405) s
            = (some (.return_ (BitVec.ofNat 64 bs405.length)), s')
      ∧ MemBytesAtB s'.memory s.memaddrs s.be outBase bs405 := by
  let s1 : PancakeState σ := { s with locals := setLocal s.locals "method" (BitVec.ofNat 64 9) }
  have hreq1 : s1.locals "req" = some reqAddr := by
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "req" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hreq
  have hbyte1 : memLoadByte s1.memory s1.memaddrs s1.be reqAddr = some (88 : BitVec 8) := hbyte
  have hdecode := decode_405 o s1 reqAddr hreq1 hbyte1
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "method" (BitVec.ofNat 64 9) }
  let s3 : PancakeState σ := { s2 with locals := setLocal s2.locals "hsts" (BitVec.ofNat 64 0) }
  have hctrl3 : s3.locals "ctrl" = some cfgBase := by
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 9) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hctrl
  have he4 : eval s3 (be4model "ctrl") = some (BitVec.ofNat 64 0) :=
    eval_be4model_zero s3 cfgBase hctrl3 hc0 hc1 hc2 hc3
  let s4 : PancakeState σ := { s3 with locals := setLocal s3.locals "clen" (BitVec.ofNat 64 0) }
  have hclen4 : s4.locals "clen" = some (BitVec.ofNat 64 0) := by
    show setLocal s3.locals "clen" (BitVec.ofNat 64 0) "clen" = _
    rw [setLocal_eq]
  have hcondev : eval s4 (.cmp .equal (.var "clen") (.const (BitVec.ofNat 64 0))) = some 1 := by
    simp only [eval, hclen4]; decide
  have hskip : PancakeSem o (PancakeProg.skip) s4 = (none, s4) := by rw [PancakeSem]
  have hcondrun : PancakeSem o (.cond (.cmp .equal (.var "clen") (.const (BitVec.ofNat 64 0)))
        .skip (.assign "hsts" (.loadByte (.op .add (.var "ctrl") (.const (BitVec.ofNat 64 4)))))) s4
        = (none, s4) :=
    cond_then_run o s4 _ _ _ hcondev hskip
  let s5 : PancakeState σ := { s4 with locals := setLocal s4.locals "count" (BitVec.ofNat 64 0) }
  have hout5 : s5.locals "out" = some outBase := by
    show setLocal s4.locals "count" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s3.locals "clen" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 9) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hout
  have hs5ma : s5.memaddrs = s.memaddrs := rfl
  have haddr5 : ∀ i, i < bs405.length → s5.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true := by
    intro i hi; rw [hs5ma]; exact haddr i hi
  obtain ⟨s6, hrun6, hma6, hbe6, hcl6, hcnt6, hmb6⟩ :=
    storeAssign_landsB o "out" "count" outBase bs405.length bs405 s5 hout5 haddr5 hinj
  have hmeth5 : s5.locals "method" = some (BitVec.ofNat 64 9) := by
    show setLocal s4.locals "count" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s3.locals "clen" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 9) "method" = _
    rw [setLocal_eq]
  have hrouteev : eval s5 (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4))) = some 0 := by
    simp only [eval, hmeth5]; decide
  have hroute : PancakeSem o (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
        (.cond (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0)))
          (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
          (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt)))
        (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405))) s5
        = (none, s6) :=
    cond_else_run o s5 _ _ _ hrouteev hrun6
  have hcont2 : PancakeSem o (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
          (.cond (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0)))
            (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
            (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt)))
          (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
        (.ret (.var "count"))) s5
        = (some (.return_ (BitVec.ofNat 64 bs405.length)), emptyLocals s6) := by
    rw [sem_seq_none_run o hroute hcl6, PancakeSem]
    simp only [eval, hcnt6]
  have hinner := sem_dec_run o "count" (.const (BitVec.ofNat 64 0)) _ s4 (BitVec.ofNat 64 0) rfl hcont2
  have hafterclen := (sem_seq_none_run o hcondrun rfl).trans hinner
  have hdecclen := sem_dec_run o "clen" (be4model "ctrl") _ s3 (BitVec.ofNat 64 0) he4 hafterclen
  have hdechsts := sem_dec_run o "hsts" (.const (BitVec.ofNat 64 0)) _ s2 (BitVec.ofNat 64 0) rfl hdecclen
  have hcont1 := (sem_seq_none_run o hdecode rfl).trans hdechsts
  have key := sem_dec_run o "method" (.const (BitVec.ofNat 64 9)) _ s (BitVec.ofNat 64 9) rfl hcont1
  exact ⟨_, key, hmb6⟩

/-! ## 5. GET + PRESENT frame → 200 ALT (THE CONFIG-DRIVEN DECISION). -/

/-- **CAPSTONE — the config-driven decision (200 alt branch).** A GET whose config
frame is PRESENT (`cfgLen = 1`, `config[0] = 1`) reads the toggle, takes the
`hsts ≠ 0` 200-branch, lands `bs200Alt` byte-addressed and returns `|bs200Alt|`.
The response head is a genuine FUNCTION of the config frame — with `bs200Alt ≠
bs200` this differs from `serveExportCfg_serves_get_default`'s `bs200`. -/
theorem serveExportCfg_serves_get_present (o : Oracle σ) (s : PancakeState σ)
    (bs200 bs200Alt bs405 : List Nat) (outBase reqAddr cfgBase : Word)
    (hout : s.locals "out" = some outBase)
    (hreq : s.locals "req" = some reqAddr)
    (hctrl : s.locals "ctrl" = some cfgBase)
    (hget : memLoadByte s.memory s.memaddrs s.be reqAddr = some (71 : BitVec 8))
    (hc0 : memLoadByte s.memory s.memaddrs s.be cfgBase = some (0 : BitVec 8))
    (hc1 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 1) = some (0 : BitVec 8))
    (hc2 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 2) = some (0 : BitVec 8))
    (hc3 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 3) = some (1 : BitVec 8))
    (hc4 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 4) = some (1 : BitVec 8))
    (haddr : ∀ i, i < bs200Alt.length → s.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs200Alt.length → j < bs200Alt.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ s', PancakeSem o (serveModelCfg bs200 bs200Alt bs405) s
            = (some (.return_ (BitVec.ofNat 64 bs200Alt.length)), s')
      ∧ MemBytesAtB s'.memory s.memaddrs s.be outBase bs200Alt := by
  let s1 : PancakeState σ := { s with locals := setLocal s.locals "method" (BitVec.ofNat 64 9) }
  have hreq1 : s1.locals "req" = some reqAddr := by
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "req" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hreq
  have hget1 : memLoadByte s1.memory s1.memaddrs s1.be reqAddr = some (71 : BitVec 8) := hget
  have hdecode := decode_get o s1 reqAddr hreq1 hget1
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "method" (BitVec.ofNat 64 0) }
  let s3 : PancakeState σ := { s2 with locals := setLocal s2.locals "hsts" (BitVec.ofNat 64 0) }
  have hctrl3 : s3.locals "ctrl" = some cfgBase := by
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 0) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hctrl
  have he4 : eval s3 (be4model "ctrl") = some (BitVec.ofNat 64 1) :=
    eval_be4model_one s3 cfgBase hctrl3 hc0 hc1 hc2 hc3
  let s4 : PancakeState σ := { s3 with locals := setLocal s3.locals "clen" (BitVec.ofNat 64 1) }
  have hclen4 : s4.locals "clen" = some (BitVec.ofNat 64 1) := by
    show setLocal s3.locals "clen" (BitVec.ofNat 64 1) "clen" = _
    rw [setLocal_eq]
  have hctrl4 : s4.locals "ctrl" = some cfgBase := by
    show setLocal s3.locals "clen" (BitVec.ofNat 64 1) "ctrl" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hctrl3
  have hcondev : eval s4 (.cmp .equal (.var "clen") (.const (BitVec.ofNat 64 0))) = some 0 := by
    simp only [eval, hclen4]; decide
  -- else branch: hsts := config[0] = cfgBase[4] = 1
  have htog : eval s4 (.loadByte (.op .add (.var "ctrl") (.const (BitVec.ofNat 64 4))))
      = some ((1 : BitVec 8).setWidth 64) := by
    have hc4' : memLoadByte s4.memory s4.memaddrs s4.be (cfgBase + BitVec.ofNat 64 4) = some (1 : BitVec 8) := hc4
    simp only [eval, hctrl4, hc4']
  let s4b : PancakeState σ := { s4 with locals := setLocal s4.locals "hsts" ((1 : BitVec 8).setWidth 64) }
  have hassignrun : PancakeSem o (.assign "hsts" (.loadByte (.op .add (.var "ctrl") (.const (BitVec.ofNat 64 4))))) s4
      = (none, { s4 with locals := setLocal s4.locals "hsts" ((1 : BitVec 8).setWidth 64) }) := by
    rw [PancakeSem]; simp only [htog]
  have hcondrun : PancakeSem o (.cond (.cmp .equal (.var "clen") (.const (BitVec.ofNat 64 0)))
        .skip (.assign "hsts" (.loadByte (.op .add (.var "ctrl") (.const (BitVec.ofNat 64 4)))))) s4
        = (none, s4b) :=
    cond_else_run o s4 _ _ _ hcondev hassignrun
  let s5 : PancakeState σ := { s4b with locals := setLocal s4b.locals "count" (BitVec.ofNat 64 0) }
  have hout5 : s5.locals "out" = some outBase := by
    show setLocal s4b.locals "count" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s4.locals "hsts" ((1 : BitVec 8).setWidth 64) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s3.locals "clen" (BitVec.ofNat 64 1) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 0) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s.locals "method" (BitVec.ofNat 64 9) "out" = _
    rw [setLocal_ne _ _ _ _ (by decide)]; exact hout
  have hs5ma : s5.memaddrs = s.memaddrs := rfl
  have haddr5 : ∀ i, i < bs200Alt.length → s5.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true := by
    intro i hi; rw [hs5ma]; exact haddr i hi
  obtain ⟨s6, hrun6, hma6, hbe6, hcl6, hcnt6, hmb6⟩ :=
    storeAssign_landsB o "out" "count" outBase bs200Alt.length bs200Alt s5 hout5 haddr5 hinj
  have hmeth5 : s5.locals "method" = some (BitVec.ofNat 64 0) := by
    show setLocal s4b.locals "count" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s4.locals "hsts" ((1 : BitVec 8).setWidth 64) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s3.locals "clen" (BitVec.ofNat 64 1) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s2.locals "hsts" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s1.locals "method" (BitVec.ofNat 64 0) "method" = _
    rw [setLocal_eq]
  have hhsts5 : s5.locals "hsts" = some ((1 : BitVec 8).setWidth 64) := by
    show setLocal s4b.locals "count" (BitVec.ofNat 64 0) "hsts" = _
    rw [setLocal_ne _ _ _ _ (by decide)]
    show setLocal s4.locals "hsts" ((1 : BitVec 8).setWidth 64) "hsts" = _
    rw [setLocal_eq]
  have hinnerev : eval s5 (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0))) = some 0 := by
    simp only [eval, hhsts5]; decide
  have hinnerrun : PancakeSem o (.cond (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0)))
        (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
        (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt))) s5
        = (none, s6) :=
    cond_else_run o s5 _ _ _ hinnerev hrun6
  have hrouteev : eval s5 (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4))) = some 1 := by
    simp only [eval, hmeth5]; decide
  have hroute : PancakeSem o (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
        (.cond (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0)))
          (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
          (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt)))
        (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405))) s5
        = (none, s6) :=
    cond_then_run o s5 _ _ _ hrouteev hinnerrun
  have hcont2 : PancakeSem o (.seq (.cond (.cmp .less (.var "method") (.const (BitVec.ofNat 64 4)))
          (.cond (.cmp .equal (.var "hsts") (.const (BitVec.ofNat 64 0)))
            (storeAssignModel "out" "count" bs200.length ((List.range bs200.length).zip bs200))
            (storeAssignModel "out" "count" bs200Alt.length ((List.range bs200Alt.length).zip bs200Alt)))
          (storeAssignModel "out" "count" bs405.length ((List.range bs405.length).zip bs405)))
        (.ret (.var "count"))) s5
        = (some (.return_ (BitVec.ofNat 64 bs200Alt.length)), emptyLocals s6) := by
    rw [sem_seq_none_run o hroute hcl6, PancakeSem]
    simp only [eval, hcnt6]
  have hinner := sem_dec_run o "count" (.const (BitVec.ofNat 64 0)) _ s4b (BitVec.ofNat 64 0) rfl hcont2
  have hafterclen := (sem_seq_none_run o hcondrun rfl).trans hinner
  have hdecclen := sem_dec_run o "clen" (be4model "ctrl") _ s3 (BitVec.ofNat 64 1) he4 hafterclen
  have hdechsts := sem_dec_run o "hsts" (.const (BitVec.ofNat 64 0)) _ s2 (BitVec.ofNat 64 0) rfl hdecclen
  have hcont1 := (sem_seq_none_run o hdecode rfl).trans hdechsts
  have key := sem_dec_run o "method" (.const (BitVec.ofNat 64 9)) _ s (BitVec.ofNat 64 9) rfl hcont1
  exact ⟨_, key, hmb6⟩

/-! ## 6. Instantiated on the REAL emitted bytes — byte-identical-to-today pin. -/

/-- **REAL, GET + EMPTY frame (THE PIN).** The extended serve on an empty config
frame lands `BS200 = bytesOf (serialize resp200)` — the EXACT bytes today's
`serveExport` lands (`serveExport_serves_get_real`) — and returns `|BS200|`,
INDEPENDENT of `bs200Alt`. `cfgLen = 0` is byte-identical to today, as a theorem. -/
theorem serveExportCfg_default_real_get (o : Oracle σ) (s : PancakeState σ)
    (bs200Alt : List Nat) (outBase reqAddr cfgBase : Word)
    (hout : s.locals "out" = some outBase)
    (hreq : s.locals "req" = some reqAddr)
    (hctrl : s.locals "ctrl" = some cfgBase)
    (hget : memLoadByte s.memory s.memaddrs s.be reqAddr = some (71 : BitVec 8))
    (hc0 : memLoadByte s.memory s.memaddrs s.be cfgBase = some (0 : BitVec 8))
    (hc1 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 1) = some (0 : BitVec 8))
    (hc2 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 2) = some (0 : BitVec 8))
    (hc3 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 3) = some (0 : BitVec 8))
    (haddr : ∀ i, i < BS200.length → s.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < BS200.length → j < BS200.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ P s', lower (serveExportCfg BS200 bs200Alt BS405) = some P
      ∧ PancakeSem o P s = (some (.return_ (BitVec.ofNat 64 BS200.length)), s')
      ∧ MemBytesAtB s'.memory s.memaddrs s.be outBase BS200 := by
  obtain ⟨s', hsem, hmb⟩ :=
    serveExportCfg_serves_get_default o s BS200 bs200Alt BS405 outBase reqAddr cfgBase
      hout hreq hctrl hget hc0 hc1 hc2 hc3 haddr hinj
  exact ⟨serveModelCfg BS200 bs200Alt BS405, s', serveExportCfg_lowers BS200 bs200Alt BS405, hsem, hmb⟩

/-- **REAL, non-method + EMPTY frame.** The same serve on a non-method request +
empty frame lands `BS405 = bytesOf (serialize resp405)` and returns `|BS405|`. -/
theorem serveExportCfg_default_real_405 (o : Oracle σ) (s : PancakeState σ)
    (bs200Alt : List Nat) (outBase reqAddr cfgBase : Word)
    (hout : s.locals "out" = some outBase)
    (hreq : s.locals "req" = some reqAddr)
    (hctrl : s.locals "ctrl" = some cfgBase)
    (hbyte : memLoadByte s.memory s.memaddrs s.be reqAddr = some (88 : BitVec 8))
    (hc0 : memLoadByte s.memory s.memaddrs s.be cfgBase = some (0 : BitVec 8))
    (hc1 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 1) = some (0 : BitVec 8))
    (hc2 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 2) = some (0 : BitVec 8))
    (hc3 : memLoadByte s.memory s.memaddrs s.be (cfgBase + BitVec.ofNat 64 3) = some (0 : BitVec 8))
    (haddr : ∀ i, i < BS405.length → s.memaddrs (byteAlign (outBase + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < BS405.length → j < BS405.length → i ≠ j →
        outBase + BitVec.ofNat 64 i ≠ outBase + BitVec.ofNat 64 j) :
    ∃ P s', lower (serveExportCfg BS200 bs200Alt BS405) = some P
      ∧ PancakeSem o P s = (some (.return_ (BitVec.ofNat 64 BS405.length)), s')
      ∧ MemBytesAtB s'.memory s.memaddrs s.be outBase BS405 := by
  obtain ⟨s', hsem, hmb⟩ :=
    serveExportCfg_serves_405_default o s BS200 bs200Alt BS405 outBase reqAddr cfgBase
      hout hreq hctrl hbyte hc0 hc1 hc2 hc3 haddr hinj
  exact ⟨serveModelCfg BS200 bs200Alt BS405, s', serveExportCfg_lowers BS200 bs200Alt BS405, hsem, hmb⟩

/-! ## 7. NON-VACUITY — the response head is a genuine function of the config frame.

`_default` (empty frame) returns `ofNat |bs200|`; `_present` (config[0] = 1)
returns `ofNat |bs200Alt|`. With distinct in-range template lengths these are
distinct `BitVec`s, so the two runs — SAME GET request, DIFFERENT config frame —
genuinely disagree. No branch is a `P → P` stub. -/

/-- Distinct 200-template lengths ⇒ the empty-frame and present-frame GET runs
RETURN different observables: the route is a real function of the config frame. -/
theorem serveExportCfg_return_config_dependent (bs200 bs200Alt : List Nat)
    (h : bs200.length < 2 ^ 64) (h' : bs200Alt.length < 2 ^ 64)
    (hne : bs200.length ≠ bs200Alt.length) :
    (BitVec.ofNat 64 bs200.length) ≠ (BitVec.ofNat 64 bs200Alt.length) :=
  ofNat_len_ne h h' hne

-- A concrete kernel-clean witness that distinct templates exist (lengths 1 ≠ 2),
-- so `_default` and `_present` provably diverge on some input.
#guard ([1] : List Nat).length ≠ ([2, 3] : List Nat).length

/-! ## 8. Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx. -/

#print axioms eval_be4model
#print axioms serveExportCfg_lowers
#print axioms serveExportCfg_serves_get_default
#print axioms serveExportCfg_serves_405_default
#print axioms serveExportCfg_serves_get_present
#print axioms serveExportCfg_default_real_get
#print axioms serveExportCfg_default_real_405
#print axioms serveExportCfg_return_config_dependent

end Pancake.ServeConfigServe
