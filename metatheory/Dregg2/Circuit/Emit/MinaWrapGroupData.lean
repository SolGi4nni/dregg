import Dregg2.Circuit.Emit.PastaScalarMul
/-!
# `Dregg2.Circuit.Emit.MinaWrapGroupData` — the Wrap `ft_comm` rung's TYPE, GROUP OPERATIONS
and the real block's LITERAL commitments. **No theorem lives here.**

## Why this module exists — a measured split, not taste

`MinaWrapGroupGate` proves its rung with thirteen `by decide`s, each of which reduces a 255-bit
Pallas ladder (`scMulLadderM` at width 255) in the KERNEL. That is minutes of kernel compute and
gigabytes of peak RSS per build. Every one of those theorems is about the objects declared here;
none of them is *used* by anything downstream.

⚑ **But `Pt`, `chunkedComm`, `smul`, `padd` are the TYPE and the OPERATIONS the whole Wrap gate
stack is written in**, so every consumer that wanted the type or a literal had to import the
gate — and therefore had to BUILD the thirteen kernel MSMs first. That is the
`MinaWrapPublicCommGate` wound one rung up the same chain: a module carrying both expensive
theorems and cheap literals, imported by a hot cone for the literals.

The data is **MOVED here, not copied** — a second `TCHUNKS`/`FT_COMM_GOLD` would be exactly the
twin this repo forbids — and it keeps the **same namespace**, so no consumer is renamed and
`MinaWrapGroupGate` still reads as one module to anything that imports the gate.

Consumers that cite a THEOREM keep importing `MinaWrapGroupGate`. Consumers that need only the
type, an operation or a literal import THIS module and stop paying for the ladders.
-/

namespace Dregg2.Circuit.Emit.MinaWrapGroupGate

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete
  (curveB3 rcbAddM Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.PastaScalarMul (scMulLadderM)

set_option autoImplicit false
set_option maxRecDepth 4000000


/-! ## §1 — the Pallas group operations this gate is built from (K4a/K4b, unmodified) -/

/-- A projective Pallas point `(X : Y : Z)` over `Fp`. -/
abbrev Pt := Nat × Nat × Nat

/-- `[k]·P` by K4b's RCB double-and-add ladder at the full 255-bit scalar width.
`PastaScalarMul.pallasLadder_forces` is the statement that the emitted gates force this fold. -/
def smul (k : Nat) (P : Pt) : Pt := scMulLadderM pN curveB3 k P 255

/-- `P + Q` by K4a's unified RCB complete add (`pallasCompleteAdd_forces`). -/
def padd (P Q : Pt) : Pt := rcbAddM pN curveB3 P Q

/-- `-P = (X : -Y : Z)`. -/
def pneg (P : Pt) : Pt := (P.1, (pN - P.2.1 % pN) % pN, P.2.2)

/-- **`chunkedComm`** — `PolyComm::chunk_commitment` (`poly-commitment/src/commitment.rs:55`):
Horner over the chunks in REVERSE order, `res := res * z + chunk`. -/
def chunkedComm (z : Nat) (cs : List Pt) : Pt :=
  cs.reverse.foldl (fun acc c => padd (smul z acc) c) Oproj

/-- **`msmComm`** — `PolyComm::multi_scalar_mul` over `(scalar, commitment)` pairs. -/
def msmComm (terms : List (Nat × Pt)) : Pt :=
  terms.foldl (fun acc t => padd acc (smul t.1 t.2)) Oproj

/-- **`ftCommOf`** — `verifier.rs:960-964`, verbatim in shape:
`chunk(f_comm) - (zeta^n - 1) * chunk(t_comm)`. The `chunk_commitment` on `f_comm` is kept
STRUCTURALLY (it is a no-op only because `f_comm` has one chunk — see
`fComm_chunking_is_a_no_op`), so a future multi-chunk `f_comm` cannot silently pass. -/
def ftCommOf (zSrs zDomM1 : Nat) (fTerms : List (Nat × Pt)) (tChunks : List Pt) : Pt :=
  padd (chunkedComm zSrs [msmComm fTerms])
       (pneg (smul zDomM1 (chunkedComm zSrs tChunks)))

/-! ## §2 — the REAL block's group-side inputs

Mina devnet block 539508, extracted by `wrap_group_export`. Coordinates are in Pallas's BASE
field `Fp`; the scalars are in Pallas's SCALAR field `Fq`. -/

/-- `perm_scalars(evals, beta, gamma, alphas, zkp(zeta))` — the one linearization scalar. -/
def PERM_SCALAR : Nat :=
  20751602151633737401462851548350130147491954693090596112024602804092692290009

/-- `sigma_comm[PERMUTS-1]` of the devnet blockchain Wrap verifier index — the only commitment
in the linearization MSM. -/
def SIGMA6 : Pt :=
  (14533069567859997931411338798235390554646264745565930216225706045991714547029,
   230076843026232836139391506383317233661567084986689891555547340509935178276, 1)

/-- `zeta ^ max_poly_size` (`max_poly_size = 2^15`). -/
def ZETA_SRS : Nat :=
  15199112795516872416106212443861736899936601524200361370335031980543972401501

/-- `zeta ^ domain_size - 1` (`domain_size = 2^14`) — the Maller scale factor. -/
def ZETA_DOM_M1 : Nat :=
  20843391792192674096379110139698302699561672883528276553958322214537139602543

/-- The block's 7 `t_comm` chunks (the quotient-polynomial commitment). -/
def TCHUNKS : List Pt :=
  [
   (23382640723964694244614085791475445140174010552771292844771632654515403160637,
     1834425776058360070273876000949243701887690872386450124343969476133859769530, 1),
   (20421658267027367715396074495602338935050916716372351871694070908013011010291,
     24431848814686580882043032326478904323942350405263998684862417862435806498393, 1),
   (8437767720651266631202563727333255559581696471435778762846494362061787126045,
     11276986670832462284960651932652973464490945278737402618488498179480309617836, 1),
   (7946241131025672692298578151903787293968439645740063827867729888285820337110,
     10927595987986011294975437109092797646265671668037593639956868614001961557309, 1),
   (26564729323297090951288357447546753591584304754088897300539740329975354266862,
     2181201359162068961615983739336332714150726042358881483612526948087798181421, 1),
   (4110088031160970227382256682674593565642387053186990253717819687287700780866,
     23181278874497781495038467624138916413686045969349349775091313531417351742833, 1),
   (15154573345641821923530881260783904955491958425041230890861501704167338868255,
     22756676604486925033925604003249612792946449252929603692866839983627837642314, 1)
  ]

/-- The one-term linearization MSM, as `(scalar, commitment)` pairs. -/
def F_TERMS : List (Nat × Pt) := [(PERM_SCALAR, SIGMA6)]

/-! ### The gold values — o1-labs' own outputs, not ours -/

/-- kimchi's `t_comm.chunk_commitment(zeta_to_srs_len)`. -/
def CHUNKED_T_GOLD : Pt :=
  (20497740943364408243543950747415106590539589896294100246850578129887943765380,
   6854424204379636012319966707808008192294116986763538741874486503997782616159, 1)

/-- kimchi's `PolyComm::multi_scalar_mul` on the linearization MSM. -/
def F_COMM_GOLD : Pt :=
  (19674326400533049625615225538021626157270526457556463284014696039483724147764,
   28695397289097617976568064802307687844707320509254944091000772912640603603518, 1)

/-- kimchi's `ft_comm` — **pinned by o1-labs' own `SRS::verify` on the real opening proof**
(and refuted at `ft_comm + G`). -/
def FT_COMM_GOLD : Pt :=
  (23134851620960708781201702572748654667024999231009061048008617507448700477719,
   11095341763140500863332709654083102487611440299358362125188480277634145783318, 1)

/-! ## §3 — the computed objects -/

/-- Our `f_comm`. -/
def fComm : Pt := msmComm F_TERMS

/-- Our chunked `t_comm`. -/
def chunkedT : Pt := chunkedComm ZETA_SRS TCHUNKS

/-- Our `ft_comm`. -/
def ftComm : Pt := ftCommOf ZETA_SRS ZETA_DOM_M1 F_TERMS TCHUNKS

end Dregg2.Circuit.Emit.MinaWrapGroupGate
