/-
# Dregg2.Circuit.Emit.GnarkVerifier.EmitJson — the canonical JSON byte grammar.

`emitGnarkJson` renders an emission package (`GnarkCircuitData`, via its proof-covered
wire form `emit d : Emitted`) to a deterministic node-grammar JSON string:

    {"name":S,
     "public_inputs":[{"name":S,"var":N},…],
     "gadgets":[{"gadget":S,"args":[N,…]},…],
     "gates":[{"op":"var"|"const"|"add"|"mul"|"select","args":[N,…],"out":N},…],
     "asserts":[{"l":N,"r":N},…]}

Gates are the flattened op-DAG in deterministic left-to-right emission order; a gate's
`out` is its own node id; `args` are node ids for `add`/`mul`/`select`, the frontend
variable index for `var`, and the canonical `Fr` residue (decimal) for `const`. Each
assert references the node ids of its two sides. The semantic content of these bytes is
exactly what `emit_faithful` covers (the byte renderer adds no constraint content: it is
a printing of `Emitted`, whose satisfaction IS `gHolds` — `EmitFaithful.lean`).

The golden pin: `canonicityToyJson` (the `CanonicityToy` package — the toy end-to-end
∀-refinement's emitted `AssertIsCanonical`) is `#guard`-pinned byte-for-byte below, and
the same bytes are committed at `chain/gnark/emitted/canonicity_toy.json`.
-/
import Dregg2.Circuit.Emit.GnarkVerifier.CanonicityToy
import Dregg2.Circuit.Emit.GnarkVerifier.EmitVerifier

namespace Dregg2.Circuit.Emit.GnarkVerifier

open Dregg2.Circuit.R1csFr

/-! ## §1 Gate flattening — the op-DAG as a node list. -/

/-- One flattened gate record: `{op, args, out}`. -/
structure GateRec where
  op   : String
  args : List Nat
  out  : Nat
  deriving Repr, DecidableEq

/-- Flatten one emitted wire into the gate list (left-to-right, post-order); returns the
node id denoting the wire. -/
def flatW : EWire → List GateRec → Nat × List GateRec
  | .var v, gs => (gs.length, gs ++ [⟨"var", [v], gs.length⟩])
  | .const c, gs => (gs.length, gs ++ [⟨"const", [c.val], gs.length⟩])
  | .add x y, gs =>
      let (ix, gs) := flatW x gs
      let (iy, gs) := flatW y gs
      (gs.length, gs ++ [⟨"add", [ix, iy], gs.length⟩])
  | .mul x y, gs =>
      let (ix, gs) := flatW x gs
      let (iy, gs) := flatW y gs
      (gs.length, gs ++ [⟨"mul", [ix, iy], gs.length⟩])
  | .select b x y, gs =>
      let (ib, gs) := flatW b gs
      let (ix, gs) := flatW x gs
      let (iy, gs) := flatW y gs
      (gs.length, gs ++ [⟨"select", [ib, ix, iy], gs.length⟩])

/-- Flatten the assert list: all gates plus the `(l, r)` node-id pair per assert. -/
def flatAsserts : List (EWire × EWire) → List GateRec → List (Nat × Nat) →
    List GateRec × List (Nat × Nat)
  | [], gs, ps => (gs, ps)
  | (l, r) :: rest, gs, ps =>
      let (il, gs) := flatW l gs
      let (ir, gs) := flatW r gs
      flatAsserts rest gs (ps ++ [(il, ir)])

/-! ## §2 The renderer. -/

private def jArr (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

def gateJson (g : GateRec) : String :=
  "{\"op\":\"" ++ g.op ++ "\",\"args\":" ++ jArr (g.args.map toString)
    ++ ",\"out\":" ++ toString g.out ++ "}"

def assertJson (p : Nat × Nat) : String :=
  "{\"l\":" ++ toString p.1 ++ ",\"r\":" ++ toString p.2 ++ "}"

def publicInputJson (p : String × Nat) : String :=
  "{\"name\":\"" ++ p.1 ++ "\",\"var\":" ++ toString p.2 ++ "}"

def gadgetJson (g : GadgetInvocation) : String :=
  "{\"gadget\":\"" ++ g.gadget ++ "\",\"args\":" ++ jArr (g.args.map toString) ++ "}"

/-- **`emitGnarkJson`** — the canonical wire bytes of an emission package (rendered from
its proof-covered `Emitted` form). -/
def emitGnarkJson (d : GnarkCircuitData) : String :=
  let e := emit d
  let (gs, ps) := flatAsserts e.asserts [] []
  "{\"name\":\"" ++ e.name
    ++ "\",\"public_inputs\":" ++ jArr (e.publicInputs.map publicInputJson)
    ++ ",\"gadgets\":" ++ jArr (e.gadgets.map gadgetJson)
    ++ ",\"gates\":" ++ jArr (gs.map gateJson)
    ++ ",\"asserts\":" ++ jArr (ps.map assertJson) ++ "}"

/-! ## §3 The golden — the toy canonicity package, byte-pinned. Committed verbatim at
`chain/gnark/emitted/canonicity_toy.json`. -/

/-- The canonical bytes of the toy `AssertIsCanonical` package. -/
def canonicityToyJson : String := emitGnarkJson canonicityData

-- The byte-for-byte golden pin (the committed artifact, verbatim).
#guard canonicityToyJson == r#"{"name":"babybear_assert_is_canonical_v1","public_inputs":[{"name":"v","var":0}],"gadgets":[{"gadget":"AssertIsCanonical","args":[0]}],"gates":[{"op":"var","args":[1],"out":0},{"op":"var","args":[1],"out":1},{"op":"mul","args":[0,1],"out":2},{"op":"var","args":[1],"out":3},{"op":"var","args":[2],"out":4},{"op":"var","args":[2],"out":5},{"op":"mul","args":[4,5],"out":6},{"op":"var","args":[2],"out":7},{"op":"var","args":[3],"out":8},{"op":"var","args":[3],"out":9},{"op":"mul","args":[8,9],"out":10},{"op":"var","args":[3],"out":11},{"op":"var","args":[4],"out":12},{"op":"var","args":[4],"out":13},{"op":"mul","args":[12,13],"out":14},{"op":"var","args":[4],"out":15},{"op":"var","args":[5],"out":16},{"op":"var","args":[5],"out":17},{"op":"mul","args":[16,17],"out":18},{"op":"var","args":[5],"out":19},{"op":"var","args":[6],"out":20},{"op":"var","args":[6],"out":21},{"op":"mul","args":[20,21],"out":22},{"op":"var","args":[6],"out":23},{"op":"var","args":[7],"out":24},{"op":"var","args":[7],"out":25},{"op":"mul","args":[24,25],"out":26},{"op":"var","args":[7],"out":27},{"op":"var","args":[8],"out":28},{"op":"var","args":[8],"out":29},{"op":"mul","args":[28,29],"out":30},{"op":"var","args":[8],"out":31},{"op":"var","args":[9],"out":32},{"op":"var","args":[9],"out":33},{"op":"mul","args":[32,33],"out":34},{"op":"var","args":[9],"out":35},{"op":"var","args":[10],"out":36},{"op":"var","args":[10],"out":37},{"op":"mul","args":[36,37],"out":38},{"op":"var","args":[10],"out":39},{"op":"var","args":[11],"out":40},{"op":"var","args":[11],"out":41},{"op":"mul","args":[40,41],"out":42},{"op":"var","args":[11],"out":43},{"op":"var","args":[12],"out":44},{"op":"var","args":[12],"out":45},{"op":"mul","args":[44,45],"out":46},{"op":"var","args":[12],"out":47},{"op":"var","args":[13],"out":48},{"op":"var","args":[13],"out":49},{"op":"mul","args":[48,49],"out":50},{"op":"var","args":[13],"out":51},{"op":"var","args":[14],"out":52},{"op":"var","args":[14],"out":53},{"op":"mul","args":[52,53],"out":54},{"op":"var","args":[14],"out":55},{"op":"var","args":[15],"out":56},{"op":"var","args":[15],"out":57},{"op":"mul","args":[56,57],"out":58},{"op":"var","args":[15],"out":59},{"op":"var","args":[16],"out":60},{"op":"var","args":[16],"out":61},{"op":"mul","args":[60,61],"out":62},{"op":"var","args":[16],"out":63},{"op":"var","args":[17],"out":64},{"op":"var","args":[17],"out":65},{"op":"mul","args":[64,65],"out":66},{"op":"var","args":[17],"out":67},{"op":"var","args":[18],"out":68},{"op":"var","args":[18],"out":69},{"op":"mul","args":[68,69],"out":70},{"op":"var","args":[18],"out":71},{"op":"var","args":[19],"out":72},{"op":"var","args":[19],"out":73},{"op":"mul","args":[72,73],"out":74},{"op":"var","args":[19],"out":75},{"op":"var","args":[20],"out":76},{"op":"var","args":[20],"out":77},{"op":"mul","args":[76,77],"out":78},{"op":"var","args":[20],"out":79},{"op":"var","args":[21],"out":80},{"op":"var","args":[21],"out":81},{"op":"mul","args":[80,81],"out":82},{"op":"var","args":[21],"out":83},{"op":"var","args":[22],"out":84},{"op":"var","args":[22],"out":85},{"op":"mul","args":[84,85],"out":86},{"op":"var","args":[22],"out":87},{"op":"var","args":[23],"out":88},{"op":"var","args":[23],"out":89},{"op":"mul","args":[88,89],"out":90},{"op":"var","args":[23],"out":91},{"op":"var","args":[24],"out":92},{"op":"var","args":[24],"out":93},{"op":"mul","args":[92,93],"out":94},{"op":"var","args":[24],"out":95},{"op":"var","args":[25],"out":96},{"op":"var","args":[25],"out":97},{"op":"mul","args":[96,97],"out":98},{"op":"var","args":[25],"out":99},{"op":"var","args":[26],"out":100},{"op":"var","args":[26],"out":101},{"op":"mul","args":[100,101],"out":102},{"op":"var","args":[26],"out":103},{"op":"var","args":[27],"out":104},{"op":"var","args":[27],"out":105},{"op":"mul","args":[104,105],"out":106},{"op":"var","args":[27],"out":107},{"op":"var","args":[28],"out":108},{"op":"var","args":[28],"out":109},{"op":"mul","args":[108,109],"out":110},{"op":"var","args":[28],"out":111},{"op":"var","args":[29],"out":112},{"op":"var","args":[29],"out":113},{"op":"mul","args":[112,113],"out":114},{"op":"var","args":[29],"out":115},{"op":"var","args":[30],"out":116},{"op":"var","args":[30],"out":117},{"op":"mul","args":[116,117],"out":118},{"op":"var","args":[30],"out":119},{"op":"var","args":[31],"out":120},{"op":"var","args":[31],"out":121},{"op":"mul","args":[120,121],"out":122},{"op":"var","args":[31],"out":123},{"op":"var","args":[0],"out":124},{"op":"const","args":[0],"out":125},{"op":"const","args":[1],"out":126},{"op":"var","args":[1],"out":127},{"op":"mul","args":[126,127],"out":128},{"op":"add","args":[125,128],"out":129},{"op":"const","args":[2],"out":130},{"op":"var","args":[2],"out":131},{"op":"mul","args":[130,131],"out":132},{"op":"add","args":[129,132],"out":133},{"op":"const","args":[4],"out":134},{"op":"var","args":[3],"out":135},{"op":"mul","args":[134,135],"out":136},{"op":"add","args":[133,136],"out":137},{"op":"const","args":[8],"out":138},{"op":"var","args":[4],"out":139},{"op":"mul","args":[138,139],"out":140},{"op":"add","args":[137,140],"out":141},{"op":"const","args":[16],"out":142},{"op":"var","args":[5],"out":143},{"op":"mul","args":[142,143],"out":144},{"op":"add","args":[141,144],"out":145},{"op":"const","args":[32],"out":146},{"op":"var","args":[6],"out":147},{"op":"mul","args":[146,147],"out":148},{"op":"add","args":[145,148],"out":149},{"op":"const","args":[64],"out":150},{"op":"var","args":[7],"out":151},{"op":"mul","args":[150,151],"out":152},{"op":"add","args":[149,152],"out":153},{"op":"const","args":[128],"out":154},{"op":"var","args":[8],"out":155},{"op":"mul","args":[154,155],"out":156},{"op":"add","args":[153,156],"out":157},{"op":"const","args":[256],"out":158},{"op":"var","args":[9],"out":159},{"op":"mul","args":[158,159],"out":160},{"op":"add","args":[157,160],"out":161},{"op":"const","args":[512],"out":162},{"op":"var","args":[10],"out":163},{"op":"mul","args":[162,163],"out":164},{"op":"add","args":[161,164],"out":165},{"op":"const","args":[1024],"out":166},{"op":"var","args":[11],"out":167},{"op":"mul","args":[166,167],"out":168},{"op":"add","args":[165,168],"out":169},{"op":"const","args":[2048],"out":170},{"op":"var","args":[12],"out":171},{"op":"mul","args":[170,171],"out":172},{"op":"add","args":[169,172],"out":173},{"op":"const","args":[4096],"out":174},{"op":"var","args":[13],"out":175},{"op":"mul","args":[174,175],"out":176},{"op":"add","args":[173,176],"out":177},{"op":"const","args":[8192],"out":178},{"op":"var","args":[14],"out":179},{"op":"mul","args":[178,179],"out":180},{"op":"add","args":[177,180],"out":181},{"op":"const","args":[16384],"out":182},{"op":"var","args":[15],"out":183},{"op":"mul","args":[182,183],"out":184},{"op":"add","args":[181,184],"out":185},{"op":"const","args":[32768],"out":186},{"op":"var","args":[16],"out":187},{"op":"mul","args":[186,187],"out":188},{"op":"add","args":[185,188],"out":189},{"op":"const","args":[65536],"out":190},{"op":"var","args":[17],"out":191},{"op":"mul","args":[190,191],"out":192},{"op":"add","args":[189,192],"out":193},{"op":"const","args":[131072],"out":194},{"op":"var","args":[18],"out":195},{"op":"mul","args":[194,195],"out":196},{"op":"add","args":[193,196],"out":197},{"op":"const","args":[262144],"out":198},{"op":"var","args":[19],"out":199},{"op":"mul","args":[198,199],"out":200},{"op":"add","args":[197,200],"out":201},{"op":"const","args":[524288],"out":202},{"op":"var","args":[20],"out":203},{"op":"mul","args":[202,203],"out":204},{"op":"add","args":[201,204],"out":205},{"op":"const","args":[1048576],"out":206},{"op":"var","args":[21],"out":207},{"op":"mul","args":[206,207],"out":208},{"op":"add","args":[205,208],"out":209},{"op":"const","args":[2097152],"out":210},{"op":"var","args":[22],"out":211},{"op":"mul","args":[210,211],"out":212},{"op":"add","args":[209,212],"out":213},{"op":"const","args":[4194304],"out":214},{"op":"var","args":[23],"out":215},{"op":"mul","args":[214,215],"out":216},{"op":"add","args":[213,216],"out":217},{"op":"const","args":[8388608],"out":218},{"op":"var","args":[24],"out":219},{"op":"mul","args":[218,219],"out":220},{"op":"add","args":[217,220],"out":221},{"op":"const","args":[16777216],"out":222},{"op":"var","args":[25],"out":223},{"op":"mul","args":[222,223],"out":224},{"op":"add","args":[221,224],"out":225},{"op":"const","args":[33554432],"out":226},{"op":"var","args":[26],"out":227},{"op":"mul","args":[226,227],"out":228},{"op":"add","args":[225,228],"out":229},{"op":"const","args":[67108864],"out":230},{"op":"var","args":[27],"out":231},{"op":"mul","args":[230,231],"out":232},{"op":"add","args":[229,232],"out":233},{"op":"const","args":[134217728],"out":234},{"op":"var","args":[28],"out":235},{"op":"mul","args":[234,235],"out":236},{"op":"add","args":[233,236],"out":237},{"op":"const","args":[268435456],"out":238},{"op":"var","args":[29],"out":239},{"op":"mul","args":[238,239],"out":240},{"op":"add","args":[237,240],"out":241},{"op":"const","args":[536870912],"out":242},{"op":"var","args":[30],"out":243},{"op":"mul","args":[242,243],"out":244},{"op":"add","args":[241,244],"out":245},{"op":"const","args":[1073741824],"out":246},{"op":"var","args":[31],"out":247},{"op":"mul","args":[246,247],"out":248},{"op":"add","args":[245,248],"out":249},{"op":"var","args":[32],"out":250},{"op":"var","args":[32],"out":251},{"op":"mul","args":[250,251],"out":252},{"op":"var","args":[32],"out":253},{"op":"var","args":[33],"out":254},{"op":"var","args":[33],"out":255},{"op":"mul","args":[254,255],"out":256},{"op":"var","args":[33],"out":257},{"op":"var","args":[34],"out":258},{"op":"var","args":[34],"out":259},{"op":"mul","args":[258,259],"out":260},{"op":"var","args":[34],"out":261},{"op":"var","args":[35],"out":262},{"op":"var","args":[35],"out":263},{"op":"mul","args":[262,263],"out":264},{"op":"var","args":[35],"out":265},{"op":"var","args":[36],"out":266},{"op":"var","args":[36],"out":267},{"op":"mul","args":[266,267],"out":268},{"op":"var","args":[36],"out":269},{"op":"var","args":[37],"out":270},{"op":"var","args":[37],"out":271},{"op":"mul","args":[270,271],"out":272},{"op":"var","args":[37],"out":273},{"op":"var","args":[38],"out":274},{"op":"var","args":[38],"out":275},{"op":"mul","args":[274,275],"out":276},{"op":"var","args":[38],"out":277},{"op":"var","args":[39],"out":278},{"op":"var","args":[39],"out":279},{"op":"mul","args":[278,279],"out":280},{"op":"var","args":[39],"out":281},{"op":"var","args":[40],"out":282},{"op":"var","args":[40],"out":283},{"op":"mul","args":[282,283],"out":284},{"op":"var","args":[40],"out":285},{"op":"var","args":[41],"out":286},{"op":"var","args":[41],"out":287},{"op":"mul","args":[286,287],"out":288},{"op":"var","args":[41],"out":289},{"op":"var","args":[42],"out":290},{"op":"var","args":[42],"out":291},{"op":"mul","args":[290,291],"out":292},{"op":"var","args":[42],"out":293},{"op":"var","args":[43],"out":294},{"op":"var","args":[43],"out":295},{"op":"mul","args":[294,295],"out":296},{"op":"var","args":[43],"out":297},{"op":"var","args":[44],"out":298},{"op":"var","args":[44],"out":299},{"op":"mul","args":[298,299],"out":300},{"op":"var","args":[44],"out":301},{"op":"var","args":[45],"out":302},{"op":"var","args":[45],"out":303},{"op":"mul","args":[302,303],"out":304},{"op":"var","args":[45],"out":305},{"op":"var","args":[46],"out":306},{"op":"var","args":[46],"out":307},{"op":"mul","args":[306,307],"out":308},{"op":"var","args":[46],"out":309},{"op":"var","args":[47],"out":310},{"op":"var","args":[47],"out":311},{"op":"mul","args":[310,311],"out":312},{"op":"var","args":[47],"out":313},{"op":"var","args":[48],"out":314},{"op":"var","args":[48],"out":315},{"op":"mul","args":[314,315],"out":316},{"op":"var","args":[48],"out":317},{"op":"var","args":[49],"out":318},{"op":"var","args":[49],"out":319},{"op":"mul","args":[318,319],"out":320},{"op":"var","args":[49],"out":321},{"op":"var","args":[50],"out":322},{"op":"var","args":[50],"out":323},{"op":"mul","args":[322,323],"out":324},{"op":"var","args":[50],"out":325},{"op":"var","args":[51],"out":326},{"op":"var","args":[51],"out":327},{"op":"mul","args":[326,327],"out":328},{"op":"var","args":[51],"out":329},{"op":"var","args":[52],"out":330},{"op":"var","args":[52],"out":331},{"op":"mul","args":[330,331],"out":332},{"op":"var","args":[52],"out":333},{"op":"var","args":[53],"out":334},{"op":"var","args":[53],"out":335},{"op":"mul","args":[334,335],"out":336},{"op":"var","args":[53],"out":337},{"op":"var","args":[54],"out":338},{"op":"var","args":[54],"out":339},{"op":"mul","args":[338,339],"out":340},{"op":"var","args":[54],"out":341},{"op":"var","args":[55],"out":342},{"op":"var","args":[55],"out":343},{"op":"mul","args":[342,343],"out":344},{"op":"var","args":[55],"out":345},{"op":"var","args":[56],"out":346},{"op":"var","args":[56],"out":347},{"op":"mul","args":[346,347],"out":348},{"op":"var","args":[56],"out":349},{"op":"var","args":[57],"out":350},{"op":"var","args":[57],"out":351},{"op":"mul","args":[350,351],"out":352},{"op":"var","args":[57],"out":353},{"op":"var","args":[58],"out":354},{"op":"var","args":[58],"out":355},{"op":"mul","args":[354,355],"out":356},{"op":"var","args":[58],"out":357},{"op":"var","args":[59],"out":358},{"op":"var","args":[59],"out":359},{"op":"mul","args":[358,359],"out":360},{"op":"var","args":[59],"out":361},{"op":"var","args":[60],"out":362},{"op":"var","args":[60],"out":363},{"op":"mul","args":[362,363],"out":364},{"op":"var","args":[60],"out":365},{"op":"var","args":[61],"out":366},{"op":"var","args":[61],"out":367},{"op":"mul","args":[366,367],"out":368},{"op":"var","args":[61],"out":369},{"op":"var","args":[62],"out":370},{"op":"var","args":[62],"out":371},{"op":"mul","args":[370,371],"out":372},{"op":"var","args":[62],"out":373},{"op":"const","args":[2013265920],"out":374},{"op":"const","args":[21888242871839275222246405745257275088548364400416034343698204186575808495616],"out":375},{"op":"var","args":[0],"out":376},{"op":"mul","args":[375,376],"out":377},{"op":"add","args":[374,377],"out":378},{"op":"const","args":[0],"out":379},{"op":"const","args":[1],"out":380},{"op":"var","args":[32],"out":381},{"op":"mul","args":[380,381],"out":382},{"op":"add","args":[379,382],"out":383},{"op":"const","args":[2],"out":384},{"op":"var","args":[33],"out":385},{"op":"mul","args":[384,385],"out":386},{"op":"add","args":[383,386],"out":387},{"op":"const","args":[4],"out":388},{"op":"var","args":[34],"out":389},{"op":"mul","args":[388,389],"out":390},{"op":"add","args":[387,390],"out":391},{"op":"const","args":[8],"out":392},{"op":"var","args":[35],"out":393},{"op":"mul","args":[392,393],"out":394},{"op":"add","args":[391,394],"out":395},{"op":"const","args":[16],"out":396},{"op":"var","args":[36],"out":397},{"op":"mul","args":[396,397],"out":398},{"op":"add","args":[395,398],"out":399},{"op":"const","args":[32],"out":400},{"op":"var","args":[37],"out":401},{"op":"mul","args":[400,401],"out":402},{"op":"add","args":[399,402],"out":403},{"op":"const","args":[64],"out":404},{"op":"var","args":[38],"out":405},{"op":"mul","args":[404,405],"out":406},{"op":"add","args":[403,406],"out":407},{"op":"const","args":[128],"out":408},{"op":"var","args":[39],"out":409},{"op":"mul","args":[408,409],"out":410},{"op":"add","args":[407,410],"out":411},{"op":"const","args":[256],"out":412},{"op":"var","args":[40],"out":413},{"op":"mul","args":[412,413],"out":414},{"op":"add","args":[411,414],"out":415},{"op":"const","args":[512],"out":416},{"op":"var","args":[41],"out":417},{"op":"mul","args":[416,417],"out":418},{"op":"add","args":[415,418],"out":419},{"op":"const","args":[1024],"out":420},{"op":"var","args":[42],"out":421},{"op":"mul","args":[420,421],"out":422},{"op":"add","args":[419,422],"out":423},{"op":"const","args":[2048],"out":424},{"op":"var","args":[43],"out":425},{"op":"mul","args":[424,425],"out":426},{"op":"add","args":[423,426],"out":427},{"op":"const","args":[4096],"out":428},{"op":"var","args":[44],"out":429},{"op":"mul","args":[428,429],"out":430},{"op":"add","args":[427,430],"out":431},{"op":"const","args":[8192],"out":432},{"op":"var","args":[45],"out":433},{"op":"mul","args":[432,433],"out":434},{"op":"add","args":[431,434],"out":435},{"op":"const","args":[16384],"out":436},{"op":"var","args":[46],"out":437},{"op":"mul","args":[436,437],"out":438},{"op":"add","args":[435,438],"out":439},{"op":"const","args":[32768],"out":440},{"op":"var","args":[47],"out":441},{"op":"mul","args":[440,441],"out":442},{"op":"add","args":[439,442],"out":443},{"op":"const","args":[65536],"out":444},{"op":"var","args":[48],"out":445},{"op":"mul","args":[444,445],"out":446},{"op":"add","args":[443,446],"out":447},{"op":"const","args":[131072],"out":448},{"op":"var","args":[49],"out":449},{"op":"mul","args":[448,449],"out":450},{"op":"add","args":[447,450],"out":451},{"op":"const","args":[262144],"out":452},{"op":"var","args":[50],"out":453},{"op":"mul","args":[452,453],"out":454},{"op":"add","args":[451,454],"out":455},{"op":"const","args":[524288],"out":456},{"op":"var","args":[51],"out":457},{"op":"mul","args":[456,457],"out":458},{"op":"add","args":[455,458],"out":459},{"op":"const","args":[1048576],"out":460},{"op":"var","args":[52],"out":461},{"op":"mul","args":[460,461],"out":462},{"op":"add","args":[459,462],"out":463},{"op":"const","args":[2097152],"out":464},{"op":"var","args":[53],"out":465},{"op":"mul","args":[464,465],"out":466},{"op":"add","args":[463,466],"out":467},{"op":"const","args":[4194304],"out":468},{"op":"var","args":[54],"out":469},{"op":"mul","args":[468,469],"out":470},{"op":"add","args":[467,470],"out":471},{"op":"const","args":[8388608],"out":472},{"op":"var","args":[55],"out":473},{"op":"mul","args":[472,473],"out":474},{"op":"add","args":[471,474],"out":475},{"op":"const","args":[16777216],"out":476},{"op":"var","args":[56],"out":477},{"op":"mul","args":[476,477],"out":478},{"op":"add","args":[475,478],"out":479},{"op":"const","args":[33554432],"out":480},{"op":"var","args":[57],"out":481},{"op":"mul","args":[480,481],"out":482},{"op":"add","args":[479,482],"out":483},{"op":"const","args":[67108864],"out":484},{"op":"var","args":[58],"out":485},{"op":"mul","args":[484,485],"out":486},{"op":"add","args":[483,486],"out":487},{"op":"const","args":[134217728],"out":488},{"op":"var","args":[59],"out":489},{"op":"mul","args":[488,489],"out":490},{"op":"add","args":[487,490],"out":491},{"op":"const","args":[268435456],"out":492},{"op":"var","args":[60],"out":493},{"op":"mul","args":[492,493],"out":494},{"op":"add","args":[491,494],"out":495},{"op":"const","args":[536870912],"out":496},{"op":"var","args":[61],"out":497},{"op":"mul","args":[496,497],"out":498},{"op":"add","args":[495,498],"out":499},{"op":"const","args":[1073741824],"out":500},{"op":"var","args":[62],"out":501},{"op":"mul","args":[500,501],"out":502},{"op":"add","args":[499,502],"out":503}],"asserts":[{"l":2,"r":3},{"l":6,"r":7},{"l":10,"r":11},{"l":14,"r":15},{"l":18,"r":19},{"l":22,"r":23},{"l":26,"r":27},{"l":30,"r":31},{"l":34,"r":35},{"l":38,"r":39},{"l":42,"r":43},{"l":46,"r":47},{"l":50,"r":51},{"l":54,"r":55},{"l":58,"r":59},{"l":62,"r":63},{"l":66,"r":67},{"l":70,"r":71},{"l":74,"r":75},{"l":78,"r":79},{"l":82,"r":83},{"l":86,"r":87},{"l":90,"r":91},{"l":94,"r":95},{"l":98,"r":99},{"l":102,"r":103},{"l":106,"r":107},{"l":110,"r":111},{"l":114,"r":115},{"l":118,"r":119},{"l":122,"r":123},{"l":124,"r":249},{"l":252,"r":253},{"l":256,"r":257},{"l":260,"r":261},{"l":264,"r":265},{"l":268,"r":269},{"l":272,"r":273},{"l":276,"r":277},{"l":280,"r":281},{"l":284,"r":285},{"l":288,"r":289},{"l":292,"r":293},{"l":296,"r":297},{"l":300,"r":301},{"l":304,"r":305},{"l":308,"r":309},{"l":312,"r":313},{"l":316,"r":317},{"l":320,"r":321},{"l":324,"r":325},{"l":328,"r":329},{"l":332,"r":333},{"l":336,"r":337},{"l":340,"r":341},{"l":344,"r":345},{"l":348,"r":349},{"l":352,"r":353},{"l":356,"r":357},{"l":360,"r":361},{"l":364,"r":365},{"l":368,"r":369},{"l":372,"r":373},{"l":378,"r":503}]}"#

-- Structure pins: 62 booleanity asserts + 2 recompositions; deterministic gate count.
#guard (flatAsserts (emit canonicityData).asserts [] []).2.length == 64
#guard (flatAsserts (emit canonicityData).asserts [] []).1.length == 504

/-! ## §4 The COMPACT full-verifier descriptor — `emitVerifierFullJson`.

`emitGnarkJson` (§2) is the FLAT byte grammar: it materializes every constraint of a leaf
as an op-DAG node. For the toy canonicity leaf that is 504 gates — fine. For the composed
`emitVerifier` (`EmitVerifier.lean`) UNROLLED across the deployed apex-shrink fixture shape
(38 queries × 16 FRI rounds, per-query Merkle openings of depth 18…3, four input-batch
openings of depth 19, the batch-STARK constraint DAG over 6 instances) the flat form is the
~12M-node dump we refuse to ship. This section emits, instead, a COMPACT DESCRIPTOR: the six
leaf gadgets of `emitVerifier` (one per `verifyAlgoO` conjunct, in disjoint `Nat.pair`
variable blocks) tagged with the fixture-shape MULTIPLICITIES by which the Go interpreter
(`emitted_interp.go`) replicates each gadget's expansion. The heavy constraint content —
poseidon2-bn254 compressions, babybear extension multiplies, 31-bit range checks, the
Merkle-compress ladders — materializes at INTERP time from these records, not in the file.

Faithfulness posture (named seam, not silent): the flat `emitGnarkJson` bytes are what
`emit_faithful` covers (the renderer adds no constraint content). This compact descriptor is
NOT covered by `emit_faithful`: it names each leaf gadget + the fixture multiplicity and
DEFERS the heavy expansion to the interpreter, whose per-gadget expansion must reproduce the
SAME constraints the Lean leaf `circuit` defines (`friFoldData`/`merklePathData`/… in the
leaf modules). That expansion equivalence is the interpreter's obligation — the compact
grammar below is the contract it expands against. The shape constants are the apex-shrink
fixture's own (`chain/gnark/fixtures/apex_shrink_fri_real.json`, the `fri` block + derived
Merkle depths); the gadget NAMES are cross-pinned below against the actual leaf `.gadgets`. -/

/-- Fixture-shape constants for the deployed apex-shrink 2-turn proof, read verbatim from
`chain/gnark/fixtures/apex_shrink_fri_real.json` (`fri` block). -/
structure VShape where
  logBlowup          : Nat
  numQueries         : Nat
  rounds             : Nat
  logFinalPolyLen    : Nat
  maxLogArity        : Nat
  queryPowBits       : Nat
  commitPowBits      : Nat
  extraQueryIndexBits : Nat
  logGlobalMaxHeight : Nat
  numInstances       : Nat
  inputRounds        : Nat
  -- The fixture's top-level `degree_bits`, one per batch instance (so its length IS
  -- `numInstances`). Lives here, not inlined in `verifierGadgets`, because it is a fixture
  -- constant like every other field: a re-mint moves it, and a second copy is a second
  -- thing to forget. `SelectorEmit` emits one selector template per DISTINCT entry.
  degreeBits         : List Nat
  -- The multi-height MMCS batch input-open shape (verifyOpenInputBatchNative): the
  -- tallest-first HEIGHT CLASSES a query opens (shared across the input rounds of this
  -- fixture) and the per-round per-class opened-row WIDTHS. `inputClassHeights.head` is the
  -- batch-tree max log-height (= the path depth); `inputRoundWidths` is one width list per
  -- input round (in round order), each aligned with `inputClassHeights`. These let the Go
  -- interpreter pick + bind the Lean-emitted `batchData` template per round shape.
  inputClassHeights  : List Nat
  inputRoundWidths   : List (List Nat)
  deriving Repr

/-- The apex-shrink fixture shape (`degree_bits` has 6 entries → 6 batch instances; 4
`input_rounds`). The input-open batch shape is read verbatim from the fixture's per-round
matrix log-heights/widths (`chain/gnark/fixtures/apex_shrink_fri_real.json` `input_rounds`,
grouped tallest-first): all four rounds open height classes {19,18,12,3}; the per-class
opened-row widths are trace [76,304,8,164], quotient [8,16,16,8], preprocessed [59,26,8,82],
permutation [72,32,8,164]. -/
def apexShrinkShape : VShape :=
  { logBlowup := 3, numQueries := 38, rounds := 16, logFinalPolyLen := 0, maxLogArity := 1,
    queryPowBits := 16, commitPowBits := 0, extraQueryIndexBits := 0, logGlobalMaxHeight := 19,
    numInstances := 6, inputRounds := 4,
    inputClassHeights := [19, 18, 12, 3],
    inputRoundWidths := [[76, 304, 8, 164], [8, 16, 16, 8], [59, 26, 8, 82], [72, 32, 8, 164]],
    degreeBits := [9, 9, 16, 15, 15, 0] }

/-- Commit-phase Merkle path depth per FRI round: `logGlobalMaxHeight-1-r` for round `r`,
i.e. `[18,17,…,3]` for the apex-shrink shape — byte-identical to the fixture's per-round
`merkle_paths` depths. -/
def commitMerkleDepths (s : VShape) : List Nat :=
  (List.range s.rounds).map (fun r => s.logGlobalMaxHeight - 1 - r)

/-- One compact gadget-invocation record: the composition BLOCK (the `Nat.pair` variable
block of `emitVerifier`), the gnark gadget NAME (the leaf's own `.gadgets` name), the
primitive the interpreter EXPANDS it through, the fixture-shape MULTIPLICITY `count`, and
the integer params the expansion needs. `params` is a flat assoc-list of `key → int list`. -/
structure VGadget where
  block  : Nat
  gadget : String
  expand : String
  count  : Nat
  params : List (String × List Nat)
  deriving Repr

/-- The six leaf gadgets of `emitVerifier`, in `verifyAlgoO` order, tagged with the
apex-shrink multiplicities. Block `i` is the `Nat.pair i ·` variable block. -/
def verifierGadgets (s : VShape) : List VGadget :=
  let depths := commitMerkleDepths s
  [ -- block 0: canonicity / VK-shape pin (canonicityData, "AssertIsCanonical")
    ⟨0, "AssertIsCanonical", "rangecheck", 1,
      [("limb_bits", [31, 31]), ("babybear_p", [2013265921])]⟩,
    -- block 1: FRI commit-phase fold (friFoldData, "FriFoldRowArity2" + "ExtAssertIsEqual")
    ⟨1, "FriFoldRowArity2", "babybear_ext_mul", s.numQueries * s.rounds,
      [("ext_degree", [4]), ("arity", [2]), ("num_queries", [s.numQueries]),
       ("rounds", [s.rounds])]⟩,
    ⟨1, "ExtAssertIsEqual", "babybear_ext_eq", s.numQueries,
      [("ext_degree", [4])]⟩,
    -- block 2: commit-phase Merkle openings (merklePathData, "VerifyMerklePathBn254")
    ⟨2, "VerifyMerklePathBn254", "poseidon2_bn254_compress", s.numQueries,
      [("depths", depths), ("leaf_width", [4])]⟩,
    -- block 2b: input-batch openings — the REAL multi-height MMCS batch tree
    -- (verifyOpenInputBatchNative), one per (query, input-round). Carries the shared
    -- tallest-first height classes + the per-round per-class opened-row widths so the
    -- interpreter picks + binds the Lean-emitted `batchData` template per round shape.
    ⟨2, "VerifyMerklePathBn254InputOpen", "poseidon2_bn254_compress",
      s.numQueries * s.inputRounds,
      [("depth", [s.logGlobalMaxHeight]), ("num_queries", [s.numQueries]),
       ("input_rounds", [s.inputRounds]),
       ("class_heights", s.inputClassHeights),
       ("round_widths", s.inputRoundWidths.flatten)]⟩,
    -- block 3: batch-STARK constraint algebra (batchTableData, "BatchTableInstance" ×n)
    ⟨3, "BatchTableInstance", "stark_constraint_dag", s.numInstances,
      [("degree_bits", s.degreeBits)]⟩,
    ⟨3, "LogUpBalance", "logup_sum", 1, []⟩,
    -- block 4: grinding-PoW query check (emitQueryPow, "SampleBitsDecomposed" + "AssertPowBitsZero")
    ⟨4, "SampleBitsDecomposed", "rangecheck", 1, [("bits", [31])]⟩,
    ⟨4, "AssertPowBitsZero", "zero_low_bits", 1, [("pow_bits", [s.queryPowBits])]⟩,
    -- block 5: settlement segment bind (segmentData, "AssertIsEqual" × numPublicLanes)
    ⟨5, "AssertIsEqual", "wire_eq", numPublicLanes, [("lane_base", [numPublicLanes])]⟩ ]

/-! ## §4b Renderer for the compact descriptor. -/

private def jStr (s : String) : String := "\"" ++ s ++ "\""

private def jNatArr (xs : List Nat) : String := jArr (xs.map toString)

private def jObj (kvs : List (String × String)) : String :=
  "{" ++ String.intercalate "," (kvs.map fun p => jStr p.1 ++ ":" ++ p.2) ++ "}"

private def paramsJson (ps : List (String × List Nat)) : String :=
  jObj (ps.map fun p => (p.1, jNatArr p.2))

def vgadgetJson (g : VGadget) : String :=
  jObj [ ("block", toString g.block), ("gadget", jStr g.gadget),
         ("expand", jStr g.expand), ("count", toString g.count),
         ("params", paramsJson g.params) ]

/-- The `var_blocks` map: block `i` ↔ its `Nat.pair` key ↔ its `verifyAlgoO` role. -/
def varBlocksJson : String :=
  jArr <| [(0, "canonicity"), (1, "fri_fold"), (2, "merkle"), (3, "batch_table"),
           (4, "query_pow"), (5, "segment")].map fun p =>
    jObj [("block", toString p.1), ("pair_key", toString p.1), ("role", jStr p.2)]

def shapeJson (s : VShape) : String :=
  jObj [ ("log_blowup", toString s.logBlowup), ("num_queries", toString s.numQueries),
         ("rounds", toString s.rounds), ("log_final_poly_len", toString s.logFinalPolyLen),
         ("max_log_arity", toString s.maxLogArity), ("query_pow_bits", toString s.queryPowBits),
         ("commit_pow_bits", toString s.commitPowBits),
         ("extra_query_index_bits", toString s.extraQueryIndexBits),
         ("log_global_max_height", toString s.logGlobalMaxHeight),
         ("digest_width", toString digestWidth), ("num_public_lanes", toString numPublicLanes),
         ("ext_degree", "4"), ("fold_arity", "2"),
         ("num_instances", toString s.numInstances), ("input_rounds", toString s.inputRounds) ]

/-- Honest derived multiplicities (a parity oracle for the interpreter's unroll): total FRI
fold rows, commit-phase / input-batch Merkle compressions, segment lane asserts. NO
fabricated grand total — the interpreter multiplies each compression by its poseidon2-bn254
per-permutation constraint count to reach the ~12M materialized constraints. -/
def derivedJson (s : VShape) : String :=
  jObj [ ("fold_rows", toString (s.numQueries * s.rounds)),
         ("commit_merkle_compressions",
            toString (s.numQueries * (commitMerkleDepths s).foldr (· + ·) 0)),
         ("input_merkle_compressions",
            toString (s.numQueries * s.inputRounds * s.logGlobalMaxHeight)),
         ("segment_lane_asserts", toString numPublicLanes) ]

/-- **`emitVerifierFullJson`** — the compact structured descriptor of the WHOLE composed
`emitVerifier`, unrolled to the deployed apex-shrink fixture shape. Names each leaf gadget +
its fixture multiplicity + expansion params; the ~12M constraints materialize at interp
time. Deterministic, ~1.5 KB. -/
def emitVerifierFullJson (s : VShape) : String :=
  jObj [ ("schema", jStr "dregg.gnark.verifier_full.v1"),
         ("name", jStr "gnark_fri_verifier_composed_v1"),
         ("fixture", jStr "apex_shrink_fri_real"),
         ("source", jStr "Dregg2/Circuit/Emit/GnarkVerifier/EmitVerifier.lean:emitVerifier"),
         ("shape", shapeJson s),
         ("var_blocks", varBlocksJson),
         ("gadgets", jArr ((verifierGadgets s).map vgadgetJson)),
         ("derived", derivedJson s) ]

/-- The apex-shrink full-verifier descriptor bytes (committed at
`chain/gnark/emitted/verifier_full.json`). -/
def verifierFullJson : String := emitVerifierFullJson apexShrinkShape

-- The byte-for-byte golden pin (the committed artifact `chain/gnark/emitted/verifier_full.json`).
#guard verifierFullJson == r#"{"schema":"dregg.gnark.verifier_full.v1","name":"gnark_fri_verifier_composed_v1","fixture":"apex_shrink_fri_real","source":"Dregg2/Circuit/Emit/GnarkVerifier/EmitVerifier.lean:emitVerifier","shape":{"log_blowup":3,"num_queries":38,"rounds":16,"log_final_poly_len":0,"max_log_arity":1,"query_pow_bits":16,"commit_pow_bits":0,"extra_query_index_bits":0,"log_global_max_height":19,"digest_width":8,"num_public_lanes":25,"ext_degree":4,"fold_arity":2,"num_instances":6,"input_rounds":4},"var_blocks":[{"block":0,"pair_key":0,"role":"canonicity"},{"block":1,"pair_key":1,"role":"fri_fold"},{"block":2,"pair_key":2,"role":"merkle"},{"block":3,"pair_key":3,"role":"batch_table"},{"block":4,"pair_key":4,"role":"query_pow"},{"block":5,"pair_key":5,"role":"segment"}],"gadgets":[{"block":0,"gadget":"AssertIsCanonical","expand":"rangecheck","count":1,"params":{"limb_bits":[31,31],"babybear_p":[2013265921]}},{"block":1,"gadget":"FriFoldRowArity2","expand":"babybear_ext_mul","count":608,"params":{"ext_degree":[4],"arity":[2],"num_queries":[38],"rounds":[16]}},{"block":1,"gadget":"ExtAssertIsEqual","expand":"babybear_ext_eq","count":38,"params":{"ext_degree":[4]}},{"block":2,"gadget":"VerifyMerklePathBn254","expand":"poseidon2_bn254_compress","count":38,"params":{"depths":[18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3],"leaf_width":[4]}},{"block":2,"gadget":"VerifyMerklePathBn254InputOpen","expand":"poseidon2_bn254_compress","count":152,"params":{"depth":[19],"num_queries":[38],"input_rounds":[4],"class_heights":[19,18,12,3],"round_widths":[76,304,8,164,8,16,16,8,59,26,8,82,72,32,8,164]}},{"block":3,"gadget":"BatchTableInstance","expand":"stark_constraint_dag","count":6,"params":{"degree_bits":[9,9,16,15,15,0]}},{"block":3,"gadget":"LogUpBalance","expand":"logup_sum","count":1,"params":{}},{"block":4,"gadget":"SampleBitsDecomposed","expand":"rangecheck","count":1,"params":{"bits":[31]}},{"block":4,"gadget":"AssertPowBitsZero","expand":"zero_low_bits","count":1,"params":{"pow_bits":[16]}},{"block":5,"gadget":"AssertIsEqual","expand":"wire_eq","count":25,"params":{"lane_base":[25]}}],"derived":{"fold_rows":608,"commit_merkle_compressions":6384,"input_merkle_compressions":2888,"segment_lane_asserts":25}}"#

/-! ## §4c Gadget-name drift pins — the descriptor's hardcoded gnark gadget names ARE the
leaf packages' own `.gadgets` names (defends against a leaf renaming out from under us). -/

#guard canonicityData.gadgets.map (·.gadget) == ["AssertIsCanonical"]
#guard (Merkle.merklePathData 5).gadgets.map (·.gadget) == ["VerifyMerklePathBn254"]
#guard (emitQueryPow 16).gadgets.map (·.gadget) == ["SampleBitsDecomposed", "AssertPowBitsZero"]
#guard segmentData.gadgets.map (·.gadget) == List.replicate numPublicLanes "AssertIsEqual"
#guard batchGadgets [] 0 == [(⟨"LogUpBalance", []⟩ : GadgetInvocation)]
/-- One `degree_bits` entry per batch instance — the fixture states the batch width twice
(the length of `degree_bits` and the instance count) and the shape must not let the two
drift apart. A named theorem, not a `#guard`: it is a fact about the shape, so it should
leave a term. -/
theorem apexShrink_degreeBits_length :
    apexShrinkShape.degreeBits.length = apexShrinkShape.numInstances := rfl

#assert_axioms apexShrink_degreeBits_length
-- Commit-phase Merkle depths are exactly the fixture's per-round path depths [18,…,3].
#guard commitMerkleDepths apexShrinkShape
  == [18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3]

end Dregg2.Circuit.Emit.GnarkVerifier
