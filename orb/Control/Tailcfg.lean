/-!
# Control.Tailcfg — the PascalCase JSON codec for the tailcfg control-plane messages

This is the **interop codec** the stock `tailscale` client and a `headscale`-shaped
coordination server exchange: the JSON wire messages defined in the *public*
`tailcfg` package (`github.com/tailscale/tailscale`, BSD-3), serialized with
`json:",PascalCase"` keys (`node_key → "NodeKey"`, acronyms upper: `"ID"`, `"OS"`,
`"DNSConfig"`, `"DERPMap"`), optional fields skipped when absent.

Everything here is derived from that PUBLIC specification and source; it is an
independent clean-room model. Field names were cross-verified against
`tailcfg/tailcfg.go` (see `## Cross-verification` at the end for the exact Go
field ↔ JSON-key correspondence, with the public-source names cited).

## What is proved (the serde-value roundtrip)

For every message `m` we prove `fromJson? (toJson m) = some m` — decode inverts
encode at the JSON *value* level, which is exactly the serde `from_value ∘ to_value`
roundtrip: no field is dropped, mis-keyed, or mis-typed. Decode additionally
**tolerates unknown fields** (`RegisterRequest.decode_ignores_unknown`): an object
carrying extra keys the message does not model still decodes — the
forward-compatibility the real client relies on.

## The text layer (rendering / parsing)

`render : Json → String` is a total serializer that **omits null-valued object
fields** (this is the on-the-wire "skip-if-none": an absent optional is `Json.null`
in the value model and simply not emitted). `parse : String → Option Json` is a
recursive-descent reader used to ingest a real client's bytes. The text layer is
validated *by execution* against a real-shaped sample (`#eval`, see the
`## Real-sample validation` section); its general string↔value roundtrip is a named
residual (the proven content is the value-level roundtrip above).

## Scope / residual (named, not hidden)

The modeled field set is the critical interop subset the flow needs
(`GET /key → POST /ts2021 → RegisterRequest → RegisterResponse → MapRequest{Stream}
→ MapResponse`); leaf key/prefix/timestamp values are carried as their marshaled
JSON strings (`"nodekey:<hex>"`, `"100.64.0.1/32"`, RFC3339), so the codec is exact
at the JSON level and the string↔bytes decode of a key (hex) is a separate bridge.
Full behavioural bring-up (a stock client connecting) is the endpoints/handshake
lanes' concern; this file owns the message codec only.
-/

namespace Control.Tailcfg

/-! ## §1  A JSON value model -/

/-- A JSON value. Numbers are integers (the tailcfg fields we model — ids,
versions, ports — are integral); everything else is standard. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num  (n : Int)
  | str  (s : String)
  | arr  (xs : List Json)
  | obj  (fields : List (String × Json))
deriving Repr, Inhabited

/-- Association lookup over an object's field list: first key that matches wins
(JSON objects are last-writer in practice, but our encoder never emits a dup). -/
def assoc? : List (String × Json) → String → Option Json
  | [], _ => none
  | (k, v) :: rest, key => if k == key then some v else assoc? rest key

/-- Look a field up in a JSON object; `none` on a non-object or a missing key. -/
def field? : Json → String → Option Json
  | .obj fs, k => assoc? fs k
  | _, _ => none

/-! ## §2  Leaf codecs and their roundtrips -/

/-- Encode a `Nat` as a JSON integer. -/
def encNat (n : Nat) : Json := .num (Int.ofNat n)
/-- Decode a non-negative JSON integer as a `Nat` (a JSON `num` whose `Int` is
`Int.ofNat n`; a negative `Int.negSucc` or non-number fails). -/
def decNat : Json → Option Nat
  | .num (Int.ofNat n) => some n
  | _ => none
theorem decNat_encNat (n : Nat) : decNat (encNat n) = some n := rfl
theorem encNat_ne_null (n : Nat) : encNat n ≠ .null := by intro h; cases h

/-- Encode a `String`. -/
def encStr (s : String) : Json := .str s
/-- Decode a JSON string. -/
def decStr : Json → Option String
  | .str s => some s
  | _ => none
theorem decStr_encStr (s : String) : decStr (encStr s) = some s := rfl
theorem encStr_ne_null (s : String) : encStr s ≠ .null := by intro h; cases h

/-- Encode a `Bool`. -/
def encBool (b : Bool) : Json := .bool b
/-- Decode a JSON bool. -/
def decBool : Json → Option Bool
  | .bool b => some b
  | _ => none
theorem decBool_encBool (b : Bool) : decBool (encBool b) = some b := rfl
theorem encBool_ne_null (b : Bool) : encBool b ≠ .null := by intro h; cases h

/-! ### Optional (nullable) and list combinators -/

/-- Encode an optional value: `none ↦ null`, `some x ↦ enc x`. (On the wire the
renderer then *omits* a `null` field, giving skip-if-none.) -/
def encOpt (enc : α → Json) : Option α → Json
  | none => .null
  | some x => enc x

/-- The decoder for an optional *value already looked up*: a JSON `null` (or, at
the field layer, an absent key) decodes to `none`; anything else must decode with
`dec` and wraps in `some`. -/
def optDecodeVal (dec : Json → Option α) : Json → Option (Option α)
  | .null => some none
  | v => (dec v).map some

/-- **Plain-value roundtrip through the optional decoder.** A field encoded with a
non-optional encoder (Go's zero-valued `omitempty` bools) still reads back through
`optDecodeVal` as a present value. -/
theorem optDecodeVal_enc {α} {enc : α → Json} {dec : Json → Option α}
    (h : ∀ x, dec (enc x) = some x) (hne : ∀ x, enc x ≠ .null) :
    ∀ x : α, optDecodeVal dec (enc x) = some (some x) := by
  intro x
  have hnn := hne x
  cases hx : enc x with
  | null => exact absurd hx hnn
  | bool b => simp only [optDecodeVal]; rw [← hx, h x]; rfl
  | num n => simp only [optDecodeVal]; rw [← hx, h x]; rfl
  | str t => simp only [optDecodeVal]; rw [← hx, h x]; rfl
  | arr xs => simp only [optDecodeVal]; rw [← hx, h x]; rfl
  | obj fs => simp only [optDecodeVal]; rw [← hx, h x]; rfl

/-- **Optional roundtrip.** If `dec` inverts `enc` and `enc` never yields `null`,
then decoding an encoded optional recovers it. -/
theorem optDecodeVal_encOpt {α} {enc : α → Json} {dec : Json → Option α}
    (h : ∀ x, dec (enc x) = some x) (hne : ∀ x, enc x ≠ .null) :
    ∀ o : Option α, optDecodeVal dec (encOpt enc o) = some o
  | none => rfl
  | some x => by
      show optDecodeVal dec (enc x) = some (some x)
      have hnn := hne x
      cases hx : enc x with
      | null => exact absurd hx hnn
      | bool b => simp only [optDecodeVal]; rw [← hx, h x]; rfl
      | num n => simp only [optDecodeVal]; rw [← hx, h x]; rfl
      | str s => simp only [optDecodeVal]; rw [← hx, h x]; rfl
      | arr xs => simp only [optDecodeVal]; rw [← hx, h x]; rfl
      | obj fs => simp only [optDecodeVal]; rw [← hx, h x]; rfl

/-- Map a partial decoder across a list, failing if any element fails. -/
def mapOpt (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: t => match f a with
    | some b => (mapOpt f t).map (b :: ·)
    | none => none

/-- Encode a list as a JSON array. -/
def encList (enc : α → Json) (xs : List α) : Json := .arr (xs.map enc)
/-- Decode a JSON array element-wise. -/
def decArr (dec : Json → Option α) : Json → Option (List α)
  | .arr xs => mapOpt dec xs
  | _ => none

/-- **List roundtrip.** Element roundtrip lifts to array roundtrip. -/
theorem decArr_encList {enc : α → Json} {dec : Json → Option α}
    (h : ∀ x, dec (enc x) = some x) (xs : List α) :
    decArr dec (encList enc xs) = some xs := by
  simp only [encList, decArr]
  induction xs with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, mapOpt, h a, ih, Option.map_some]
theorem encList_ne_null (enc : α → Json) (xs : List α) : encList enc xs ≠ .null := by
  intro h; cases h

/-- Encode a string-keyed map as a JSON object. -/
def encStrMap (enc : α → Json) (m : List (String × α)) : Json :=
  .obj (m.map (fun p => (p.1, enc p.2)))
/-- Decode a JSON object as a string-keyed map (values decoded by `dec`). -/
def decObjMap (dec : Json → Option α) : Json → Option (List (String × α))
  | .obj fs => mapOpt (fun p => (dec p.2).map (fun v => (p.1, v))) fs
  | _ => none
/-- **String-keyed-map roundtrip.** -/
theorem decObjMap_encStrMap {enc : α → Json} {dec : Json → Option α}
    (h : ∀ x, dec (enc x) = some x) (m : List (String × α)) :
    decObjMap dec (encStrMap enc m) = some m := by
  simp only [encStrMap, decObjMap]
  induction m with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨k, v⟩ := a
    simp only [List.map_cons, mapOpt, h v, Option.map_some, ih]
theorem encStrMap_ne_null (enc : α → Json) (m : List (String × α)) :
    encStrMap enc m ≠ .null := by intro h; cases h

/-! ### Field accessors on an object -/

/-- A required field: look it up and decode. -/
def reqField (dec : Json → Option α) (j : Json) (k : String) : Option α :=
  match field? j k with
  | some v => dec v
  | none => none
/-- An optional field: absent key or `null` ↦ `none`; else decode. -/
def optField (dec : Json → Option α) (j : Json) (k : String) : Option (Option α) :=
  match field? j k with
  | some v => optDecodeVal dec v
  | none => some none

theorem reqField_obj (dec : Json → Option α) (fs) (k) :
    reqField dec (.obj fs) k = (assoc? fs k).bind dec := by
  simp only [reqField, field?]; cases assoc? fs k <;> rfl
theorem optField_obj (dec : Json → Option α) (fs) (k) :
    optField dec (.obj fs) k
      = match assoc? fs k with
        | some v => optDecodeVal dec v
        | none => some none := by
  simp only [optField, field?]

/-! ## §3  The tailcfg message structs (modeled critical subset)

Field docs cite the public `tailcfg.go` Go field name; the JSON key is that name
verbatim (PascalCase), with acronyms upper. `Option` = skip-if-none. -/

/-- `tailcfg.RegisterResponseAuth` (the type of `RegisterRequest.Auth`): the
pre-auth key path. Go: `AuthKey string json:",omitempty"`. -/
structure AuthInfo where
  authKey : Option String := none
deriving Repr, BEq

/-- `tailcfg.Hostinfo` (modeled subset). Go: `OS`, `Hostname`, `IPNVersion`,
`RoutableIPs []netip.Prefix`. -/
structure Hostinfo where
  os          : Option String := none
  hostname    : Option String := none
  ipnVersion  : Option String := none
  routableIPs : Option (List String) := none
deriving Repr, BEq

/-- `tailcfg.PortRange`. Go: `First uint16`, `Last uint16`. -/
structure PortRange where
  first : Nat
  last  : Nat
deriving Repr, BEq

/-- `tailcfg.NetPortRange`. Go: `IP string`, `Bits *int json:",omitempty"`,
`Ports PortRange`. -/
structure NetPortRange where
  ip    : String
  bits  : Option Nat := none
  ports : PortRange
deriving Repr, BEq

/-- `tailcfg.FilterRule` (the packet-filter / ACL rule). Go: `SrcIPs []string`,
`DstPorts []NetPortRange`, `IPProto []int json:",omitempty"`. This is the wire
shape the verified ACL compiler (`Control/Acl.lean`) emits. -/
structure FilterRule where
  srcIPs   : List String
  dstPorts : List NetPortRange
  ipProto  : Option (List Nat) := none
deriving Repr, BEq

/-- `tailcfg.DERPNode`. Go: `Name`, `RegionID int`, `HostName`,
`IPv4 string json:",omitempty"`, `IPv6 string json:",omitempty"`,
`DERPPort int json:",omitempty"` (verified against tailscale v1.98.8 tailcfg.DERPNode: the Go field IS `DERPPort`),
`STUNPort int json:",omitempty"`. -/
structure DERPNode where
  name     : String
  regionID : Nat
  hostName : String
  ipv4     : Option String := none
  ipv6     : Option String := none
  port     : Option Nat := none
  stunPort : Option Nat := none
  /-- `CertName string json:",omitempty"`. The expected TLS certificate name; a
  `sha256-raw:<hex>` value makes `derphttp` pin the leaf by hash
  (`tlsdial.SetConfigExpectedCertHash`) instead of verifying a PKI path, which is how
  a self-signed self-hosted relay is reachable over HTTPS. -/
  certName : Option String := none
deriving Repr, BEq

/-- `tailcfg.DERPRegion`. Go: `RegionID int`, `RegionCode string`,
`RegionName string`, `Nodes []*DERPNode json:",omitempty"`. -/
structure DERPRegion where
  regionID   : Nat
  regionCode : String
  regionName : Option String := none
  nodes      : List DERPNode := []
deriving Repr, BEq

/-- `tailcfg.DERPMap`. Go: `Regions map[int]*DERPRegion`. The JSON object key is
the region id as a decimal string; we carry it as the string it marshals to. -/
structure DERPMap where
  regions : List (String × DERPRegion)
deriving Repr, BEq

/-- `tailcfg.DNSRecord` (`tailscale/tailcfg/tailcfg.go`): a static DNS record
served in `DNSConfig.ExtraRecords`. Go: `Name string`, `Type string
json:",omitempty"` (e.g. "A"/"AAAA"; empty ⇒ inferred from `Value`), `Value
string`. -/
structure DNSRecord where
  name  : String
  type_ : Option String := none
  value : String
deriving Repr, BEq

/-- `tailcfg.DNSConfig` (modeled subset, `tailscale/tailcfg/tailcfg.go`). Go:
`Domains []string`, `Proxied bool` (MagicDNS enabled — the client installs its
100.100.100.100 resolver and answers MagicDNS names + `ExtraRecords`),
`Nameservers []netip.Addr`, `ExtraRecords []DNSRecord` (the MagicDNS
`name ↦ address` A-records the server hands the client). -/
structure DnsConfig where
  domains      : Option (List String) := none
  proxied      : Bool := false
  nameservers  : Option (List String) := none
  extraRecords : Option (List DNSRecord) := none
deriving Repr, BEq

/-- `tailcfg.Node` (modeled subset). Go: `ID NodeID`, `StableID StableNodeID`,
`Name string`, `User UserID`, `Key key.NodePublic` (`"nodekey:<hex>"`),
`Machine key.MachinePublic` (`"mkey:<hex>"`), `DiscoKey key.DiscoPublic`,
`Addresses []netip.Prefix` (`"100.64.0.1/32"`), `AllowedIPs []netip.Prefix`,
`Endpoints []netip.AddrPort`, `DERP string json:"DERP"` (legacy home-region
string `"127.3.3.40:N"`), `HomeDERP int`, `Hostinfo`, `KeyExpiry time.Time`
(RFC3339), `Online *bool`, `MachineAuthorized bool`. -/
structure Node where
  id                : Nat
  stableID          : Option String := none
  name              : String
  user              : Nat
  key               : String
  machine           : Option String := none
  discoKey          : Option String := none
  addresses         : List String
  allowedIPs        : Option (List String) := none
  endpoints         : Option (List String) := none
  derp              : Option String := none
  homeDERP          : Nat := 0
  hostinfo          : Option Hostinfo := none
  keyExpiry         : Option String := none
  online            : Option Bool := none
  machineAuthorized : Bool := false
  tags              : Option (List String) := none
deriving Repr, BEq

/-- `tailcfg.RegisterRequest` (modeled subset). Go: `Version CapabilityVersion`,
`NodeKey key.NodePublic`, `OldNodeKey key.NodePublic`, `Auth *RegisterResponseAuth`,
`Hostinfo *Hostinfo`, `Followup string`, `Ephemeral bool json:",omitempty"`,
`Tailnet string json:",omitempty"`. -/
structure RegisterRequest where
  version    : Nat
  nodeKey    : String
  oldNodeKey : Option String := none
  auth       : Option AuthInfo := none
  hostinfo   : Option Hostinfo := none
  followup   : Option String := none
  ephemeral  : Bool := false
  tailnet    : Option String := none
deriving Repr, BEq

/-- `tailcfg.RegisterResponse` (modeled subset). Go: `AuthURL string`,
`NodeKeyExpired bool`, `MachineAuthorized bool`, `Error string`. -/
structure RegisterResponse where
  authURL           : Option String := none
  nodeKeyExpired    : Bool
  machineAuthorized : Bool
  error             : Option String := none
deriving Repr, BEq

/-- `tailcfg.MapRequest` (modeled subset). Go: `Version`, `NodeKey`,
`DiscoKey key.DiscoPublic`, `Endpoints []netip.AddrPort`, `Stream bool`,
`OmitPeers bool`, `Hostinfo *Hostinfo`, `ReadOnly bool`, `Compress string`. -/
structure MapRequest where
  version   : Nat
  nodeKey   : String
  discoKey  : Option String := none
  endpoints : Option (List String) := none
  stream    : Bool := false
  omitPeers : Bool := false
  hostinfo  : Option Hostinfo := none
  readOnly  : Bool := false
  compress  : Option String := none
deriving Repr, BEq

/-- `tailcfg.MapResponse` (modeled subset). Go: `Node *Node`, `Peers []*Node`,
`PeersChanged []*Node`, `PeersRemoved []NodeID`, `DNSConfig *DNSConfig`,
`PacketFilter []FilterRule` (the ACL), `DERPMap *DERPMap`, `KeepAlive bool`,
`Domain string`. -/
structure MapResponse where
  node         : Option Node := none
  peers        : Option (List Node) := none
  peersChanged : Option (List Node) := none
  peersRemoved : Option (List Nat) := none
  dnsConfig    : Option DnsConfig := none
  packetFilter : List FilterRule := []
  -- `PacketFilters map[string][]FilterRule json:",omitempty"` — the NEWER
  -- named-filter carrier the real control server actually emits (the legacy
  -- `PacketFilter` array is omitted). Keyed by filter name (e.g. "base").
  packetFilters : Option (List (String × List FilterRule)) := none
  derpMap      : Option DERPMap := none
  keepAlive    : Bool := false
  domain       : Option String := none
deriving Repr, BEq

/-! ## §4  Per-struct codecs and roundtrips (inner structs first)

Each struct gets `toJson`/`fromJson?` and a `fromJson?_toJson` roundtrip, plus
`toJson_ne_null` (the encoder is always an object) so it composes under `Option`
and `List`. The roundtrip proofs are uniform: `simp` reduces the field lookups
over the literal-keyed object (string keys decided by the default simprocs), then
the leaf/container roundtrips fire. -/

/-! ### AuthInfo -/
def AuthInfo.toJson (m : AuthInfo) : Json :=
  .obj [("AuthKey", encOpt encStr m.authKey)]
def AuthInfo.fromJson? (j : Json) : Option AuthInfo := do
  let authKey ← optField decStr j "AuthKey"
  some { authKey }
theorem AuthInfo.toJson_ne_null (m : AuthInfo) : AuthInfo.toJson m ≠ .null := by
  intro h; cases h
theorem AuthInfo.fromJson?_toJson (m : AuthInfo) :
    AuthInfo.fromJson? (AuthInfo.toJson m) = some m := by
  obtain ⟨authKey⟩ := m
  simp [AuthInfo.toJson, AuthInfo.fromJson?, reqField_obj, optField_obj, assoc?,
    optDecodeVal_encOpt decStr_encStr encStr_ne_null]

/-! ### Hostinfo -/
def Hostinfo.toJson (m : Hostinfo) : Json :=
  .obj [ ("OS", encOpt encStr m.os)
       , ("Hostname", encOpt encStr m.hostname)
       , ("IPNVersion", encOpt encStr m.ipnVersion)
       , ("RoutableIPs", encOpt (encList encStr) m.routableIPs) ]
def Hostinfo.fromJson? (j : Json) : Option Hostinfo := do
  let os ← optField decStr j "OS"
  let hostname ← optField decStr j "Hostname"
  let ipnVersion ← optField decStr j "IPNVersion"
  let routableIPs ← optField (decArr decStr) j "RoutableIPs"
  some { os, hostname, ipnVersion, routableIPs }
theorem Hostinfo.toJson_ne_null (m : Hostinfo) : Hostinfo.toJson m ≠ .null := by
  intro h; cases h
theorem Hostinfo.fromJson?_toJson (m : Hostinfo) :
    Hostinfo.fromJson? (Hostinfo.toJson m) = some m := by
  obtain ⟨os, hostname, ipnVersion, routableIPs⟩ := m
  simp [Hostinfo.toJson, Hostinfo.fromJson?, reqField_obj, optField_obj, assoc?,
    optDecodeVal_encOpt decStr_encStr encStr_ne_null,
    optDecodeVal_encOpt (decArr_encList decStr_encStr) (encList_ne_null encStr)]

/-! ### PortRange -/
def PortRange.toJson (m : PortRange) : Json :=
  .obj [("First", encNat m.first), ("Last", encNat m.last)]
def PortRange.fromJson? (j : Json) : Option PortRange := do
  let first ← reqField decNat j "First"
  let last ← reqField decNat j "Last"
  some { first, last }
theorem PortRange.toJson_ne_null (m : PortRange) : PortRange.toJson m ≠ .null := by
  intro h; cases h
theorem PortRange.fromJson?_toJson (m : PortRange) :
    PortRange.fromJson? (PortRange.toJson m) = some m := by
  obtain ⟨first, last⟩ := m
  simp [PortRange.toJson, PortRange.fromJson?, reqField_obj, assoc?, decNat_encNat]

/-! ### NetPortRange -/
def NetPortRange.toJson (m : NetPortRange) : Json :=
  .obj [ ("IP", encStr m.ip)
       , ("Bits", encOpt encNat m.bits)
       , ("Ports", PortRange.toJson m.ports) ]
def NetPortRange.fromJson? (j : Json) : Option NetPortRange := do
  let ip ← reqField decStr j "IP"
  let bits ← optField decNat j "Bits"
  let ports ← reqField PortRange.fromJson? j "Ports"
  some { ip, bits, ports }
theorem NetPortRange.toJson_ne_null (m : NetPortRange) : NetPortRange.toJson m ≠ .null := by
  intro h; cases h
theorem NetPortRange.fromJson?_toJson (m : NetPortRange) :
    NetPortRange.fromJson? (NetPortRange.toJson m) = some m := by
  obtain ⟨ip, bits, ports⟩ := m
  simp [NetPortRange.toJson, NetPortRange.fromJson?, reqField_obj, optField_obj, assoc?,
    decStr_encStr, optDecodeVal_encOpt decNat_encNat encNat_ne_null,
    PortRange.fromJson?_toJson]

/-! ### FilterRule -/
def FilterRule.toJson (m : FilterRule) : Json :=
  .obj [ ("SrcIPs", encList encStr m.srcIPs)
       , ("DstPorts", encList NetPortRange.toJson m.dstPorts)
       , ("IPProto", encOpt (encList encNat) m.ipProto) ]
def FilterRule.fromJson? (j : Json) : Option FilterRule := do
  let srcIPs ← reqField (decArr decStr) j "SrcIPs"
  let dstPorts ← reqField (decArr NetPortRange.fromJson?) j "DstPorts"
  let ipProto ← optField (decArr decNat) j "IPProto"
  some { srcIPs, dstPorts, ipProto }
theorem FilterRule.toJson_ne_null (m : FilterRule) : FilterRule.toJson m ≠ .null := by
  intro h; cases h
theorem FilterRule.fromJson?_toJson (m : FilterRule) :
    FilterRule.fromJson? (FilterRule.toJson m) = some m := by
  obtain ⟨srcIPs, dstPorts, ipProto⟩ := m
  simp [FilterRule.toJson, FilterRule.fromJson?, reqField_obj, optField_obj, assoc?,
    decArr_encList decStr_encStr, decArr_encList NetPortRange.fromJson?_toJson,
    optDecodeVal_encOpt (decArr_encList decNat_encNat) (encList_ne_null encNat)]

/-! ### DERPNode -/
def DERPNode.toJson (m : DERPNode) : Json :=
  .obj [ ("Name", encStr m.name)
       , ("RegionID", encNat m.regionID)
       , ("HostName", encStr m.hostName)
       , ("IPv4", encOpt encStr m.ipv4)
       , ("IPv6", encOpt encStr m.ipv6)
       , ("DERPPort", encOpt encNat m.port)
       , ("STUNPort", encOpt encNat m.stunPort)
       , ("CertName", encOpt encStr m.certName) ]
def DERPNode.fromJson? (j : Json) : Option DERPNode := do
  let name ← reqField decStr j "Name"
  let regionID ← reqField decNat j "RegionID"
  let hostName ← reqField decStr j "HostName"
  let ipv4 ← optField decStr j "IPv4"
  let ipv6 ← optField decStr j "IPv6"
  let port ← optField decNat j "DERPPort"
  let stunPort ← optField decNat j "STUNPort"
  let certName ← optField decStr j "CertName"
  some { name, regionID, hostName, ipv4, ipv6, port, stunPort, certName }
theorem DERPNode.toJson_ne_null (m : DERPNode) : DERPNode.toJson m ≠ .null := by
  intro h; cases h
theorem DERPNode.fromJson?_toJson (m : DERPNode) :
    DERPNode.fromJson? (DERPNode.toJson m) = some m := by
  obtain ⟨name, regionID, hostName, ipv4, ipv6, port, stunPort, certName⟩ := m
  simp [DERPNode.toJson, DERPNode.fromJson?, reqField_obj, optField_obj, assoc?,
    decStr_encStr, decNat_encNat, optDecodeVal_encOpt decStr_encStr encStr_ne_null,
    optDecodeVal_encOpt decNat_encNat encNat_ne_null]

/-! ### DERPRegion -/
def DERPRegion.toJson (m : DERPRegion) : Json :=
  .obj [ ("RegionID", encNat m.regionID)
       , ("RegionCode", encStr m.regionCode)
       , ("RegionName", encOpt encStr m.regionName)
       , ("Nodes", encList DERPNode.toJson m.nodes) ]
def DERPRegion.fromJson? (j : Json) : Option DERPRegion := do
  let regionID ← reqField decNat j "RegionID"
  let regionCode ← reqField decStr j "RegionCode"
  let regionName ← optField decStr j "RegionName"
  let nodes ← reqField (decArr DERPNode.fromJson?) j "Nodes"
  some { regionID, regionCode, regionName, nodes }
theorem DERPRegion.toJson_ne_null (m : DERPRegion) : DERPRegion.toJson m ≠ .null := by
  intro h; cases h
theorem DERPRegion.fromJson?_toJson (m : DERPRegion) :
    DERPRegion.fromJson? (DERPRegion.toJson m) = some m := by
  obtain ⟨regionID, regionCode, regionName, nodes⟩ := m
  simp [DERPRegion.toJson, DERPRegion.fromJson?, reqField_obj, optField_obj, assoc?,
    decNat_encNat, decStr_encStr, optDecodeVal_encOpt decStr_encStr encStr_ne_null,
    decArr_encList DERPNode.fromJson?_toJson]

/-! ### DERPMap -/
def DERPMap.toJson (m : DERPMap) : Json :=
  .obj [("Regions", encStrMap DERPRegion.toJson m.regions)]
def DERPMap.fromJson? (j : Json) : Option DERPMap := do
  let regions ← reqField (decObjMap DERPRegion.fromJson?) j "Regions"
  some { regions }
theorem DERPMap.toJson_ne_null (m : DERPMap) : DERPMap.toJson m ≠ .null := by
  intro h; cases h
theorem DERPMap.fromJson?_toJson (m : DERPMap) :
    DERPMap.fromJson? (DERPMap.toJson m) = some m := by
  obtain ⟨regions⟩ := m
  simp [DERPMap.toJson, DERPMap.fromJson?, reqField_obj, assoc?,
    decObjMap_encStrMap DERPRegion.fromJson?_toJson]

/-! ### DNSRecord -/
def DNSRecord.toJson (m : DNSRecord) : Json :=
  .obj [ ("Name", encStr m.name)
       , ("Type", encOpt encStr m.type_)
       , ("Value", encStr m.value) ]
def DNSRecord.fromJson? (j : Json) : Option DNSRecord := do
  let name ← reqField decStr j "Name"
  let type_ ← optField decStr j "Type"
  let value ← reqField decStr j "Value"
  some { name, type_, value }
theorem DNSRecord.toJson_ne_null (m : DNSRecord) : DNSRecord.toJson m ≠ .null := by
  intro h; cases h
theorem DNSRecord.fromJson?_toJson (m : DNSRecord) :
    DNSRecord.fromJson? (DNSRecord.toJson m) = some m := by
  obtain ⟨name, type_, value⟩ := m
  simp [DNSRecord.toJson, DNSRecord.fromJson?, reqField_obj, optField_obj, assoc?,
    decStr_encStr, optDecodeVal_encOpt decStr_encStr encStr_ne_null]

/-! ### DnsConfig -/
def DnsConfig.toJson (m : DnsConfig) : Json :=
  .obj [ ("Domains", encOpt (encList encStr) m.domains)
       , ("Proxied", encBool m.proxied)
       , ("Nameservers", encOpt (encList encStr) m.nameservers)
       , ("ExtraRecords", encOpt (encList DNSRecord.toJson) m.extraRecords) ]
def DnsConfig.fromJson? (j : Json) : Option DnsConfig := do
  let domains ← optField (decArr decStr) j "Domains"
  let proxied ← reqField decBool j "Proxied"
  let nameservers ← optField (decArr decStr) j "Nameservers"
  let extraRecords ← optField (decArr DNSRecord.fromJson?) j "ExtraRecords"
  some { domains, proxied, nameservers, extraRecords }
theorem DnsConfig.toJson_ne_null (m : DnsConfig) : DnsConfig.toJson m ≠ .null := by
  intro h; cases h
theorem DnsConfig.fromJson?_toJson (m : DnsConfig) :
    DnsConfig.fromJson? (DnsConfig.toJson m) = some m := by
  obtain ⟨domains, proxied, nameservers, extraRecords⟩ := m
  simp [DnsConfig.toJson, DnsConfig.fromJson?, reqField_obj, optField_obj, assoc?,
    decBool_encBool,
    optDecodeVal_encOpt (decArr_encList decStr_encStr) (encList_ne_null encStr),
    optDecodeVal_encOpt (decArr_encList DNSRecord.fromJson?_toJson) (encList_ne_null DNSRecord.toJson)]

/-! ### Node -/
def Node.toJson (m : Node) : Json :=
  .obj [ ("ID", encNat m.id)
       , ("StableID", encOpt encStr m.stableID)
       , ("Name", encStr m.name)
       , ("User", encNat m.user)
       , ("Key", encStr m.key)
       , ("Machine", encOpt encStr m.machine)
       , ("DiscoKey", encOpt encStr m.discoKey)
       , ("Addresses", encList encStr m.addresses)
       , ("AllowedIPs", encOpt (encList encStr) m.allowedIPs)
       , ("Endpoints", encOpt (encList encStr) m.endpoints)
       , ("DERP", encOpt encStr m.derp)
       , ("HomeDERP", encNat m.homeDERP)
       , ("Hostinfo", encOpt Hostinfo.toJson m.hostinfo)
       , ("KeyExpiry", encOpt encStr m.keyExpiry)
       , ("Online", encOpt encBool m.online)
       , ("MachineAuthorized", encBool m.machineAuthorized)
       , ("Tags", encOpt (encList encStr) m.tags) ]
def Node.fromJson? (j : Json) : Option Node := do
  let id ← reqField decNat j "ID"
  let stableID ← optField decStr j "StableID"
  let name ← reqField decStr j "Name"
  let user ← reqField decNat j "User"
  let key ← reqField decStr j "Key"
  let machine ← optField decStr j "Machine"
  let discoKey ← optField decStr j "DiscoKey"
  let addresses ← reqField (decArr decStr) j "Addresses"
  let allowedIPs ← optField (decArr decStr) j "AllowedIPs"
  let endpoints ← optField (decArr decStr) j "Endpoints"
  let derp ← optField decStr j "DERP"
  -- Go: `HomeDERP int json:",omitzero"` — omitted when 0. Real Node bytes
  -- omit it entirely; `reqField` REJECTED the real MapResponse Node.
  let homeDERP? ← optField decNat j "HomeDERP"
  let homeDERP := homeDERP?.getD 0
  let hostinfo ← optField Hostinfo.fromJson? j "Hostinfo"
  let keyExpiry ← optField decStr j "KeyExpiry"
  let online ← optField decBool j "Online"
  let machineAuthorized ← reqField decBool j "MachineAuthorized"
  let tags ← optField (decArr decStr) j "Tags"
  some { id, stableID, name, user, key, machine, discoKey, addresses, allowedIPs,
         endpoints, derp, homeDERP, hostinfo, keyExpiry, online, machineAuthorized, tags }
theorem Node.toJson_ne_null (m : Node) : Node.toJson m ≠ .null := by
  intro h; cases h
theorem Node.fromJson?_toJson (m : Node) :
    Node.fromJson? (Node.toJson m) = some m := by
  obtain ⟨id, stableID, name, user, key, machine, discoKey, addresses, allowedIPs,
          endpoints, derp, homeDERP, hostinfo, keyExpiry, online, machineAuthorized, tags⟩ := m
  simp [Node.toJson, Node.fromJson?, reqField_obj, optField_obj, assoc?,
    decNat_encNat, decStr_encStr, decBool_encBool, decArr_encList decStr_encStr,
    optDecodeVal_encOpt decStr_encStr encStr_ne_null,
    optDecodeVal_encOpt decBool_encBool encBool_ne_null,
    optDecodeVal_enc decNat_encNat encNat_ne_null,
    optDecodeVal_encOpt (decArr_encList decStr_encStr) (encList_ne_null encStr),
    optDecodeVal_encOpt Hostinfo.fromJson?_toJson Hostinfo.toJson_ne_null]

/-! ### RegisterRequest -/
def RegisterRequest.toJson (m : RegisterRequest) : Json :=
  .obj [ ("Version", encNat m.version)
       , ("NodeKey", encStr m.nodeKey)
       , ("OldNodeKey", encOpt encStr m.oldNodeKey)
       , ("Auth", encOpt AuthInfo.toJson m.auth)
       , ("Hostinfo", encOpt Hostinfo.toJson m.hostinfo)
       , ("Followup", encOpt encStr m.followup)
       , ("Ephemeral", encBool m.ephemeral)
       , ("Tailnet", encOpt encStr m.tailnet) ]
def RegisterRequest.fromJson? (j : Json) : Option RegisterRequest := do
  let version ← reqField decNat j "Version"
  let nodeKey ← reqField decStr j "NodeKey"
  let oldNodeKey ← optField decStr j "OldNodeKey"
  let auth ← optField AuthInfo.fromJson? j "Auth"
  let hostinfo ← optField Hostinfo.fromJson? j "Hostinfo"
  let followup ← optField decStr j "Followup"
  -- Go: `Ephemeral bool \`json:",omitempty"\`` — a non-ephemeral node OMITS
  -- this field entirely, so it must be optional and default to Go's zero
  -- value. Requiring it REJECTED the real stock-client RegisterRequest;
  -- see Control/RealCaptureKat.lean for the capture that caught this.
  let ephemeral? ← optField decBool j "Ephemeral"
  let ephemeral := ephemeral?.getD false
  let tailnet ← optField decStr j "Tailnet"
  some { version, nodeKey, oldNodeKey, auth, hostinfo, followup, ephemeral, tailnet }
theorem RegisterRequest.fromJson?_toJson (m : RegisterRequest) :
    RegisterRequest.fromJson? (RegisterRequest.toJson m) = some m := by
  obtain ⟨version, nodeKey, oldNodeKey, auth, hostinfo, followup, ephemeral, tailnet⟩ := m
  simp [RegisterRequest.toJson, RegisterRequest.fromJson?, reqField_obj, optField_obj,
    assoc?, decNat_encNat, decStr_encStr, decBool_encBool,
    optDecodeVal_enc decBool_encBool encBool_ne_null,
    optDecodeVal_encOpt decStr_encStr encStr_ne_null,
    optDecodeVal_encOpt AuthInfo.fromJson?_toJson AuthInfo.toJson_ne_null,
    optDecodeVal_encOpt Hostinfo.fromJson?_toJson Hostinfo.toJson_ne_null]

/-! ### RegisterResponse -/
def RegisterResponse.toJson (m : RegisterResponse) : Json :=
  .obj [ ("AuthURL", encOpt encStr m.authURL)
       , ("NodeKeyExpired", encBool m.nodeKeyExpired)
       , ("MachineAuthorized", encBool m.machineAuthorized)
       , ("Error", encOpt encStr m.error) ]
def RegisterResponse.fromJson? (j : Json) : Option RegisterResponse := do
  let authURL ← optField decStr j "AuthURL"
  let nodeKeyExpired ← reqField decBool j "NodeKeyExpired"
  let machineAuthorized ← reqField decBool j "MachineAuthorized"
  let error ← optField decStr j "Error"
  some { authURL, nodeKeyExpired, machineAuthorized, error }
theorem RegisterResponse.fromJson?_toJson (m : RegisterResponse) :
    RegisterResponse.fromJson? (RegisterResponse.toJson m) = some m := by
  obtain ⟨authURL, nodeKeyExpired, machineAuthorized, error⟩ := m
  simp [RegisterResponse.toJson, RegisterResponse.fromJson?, reqField_obj, optField_obj,
    assoc?, decBool_encBool, optDecodeVal_encOpt decStr_encStr encStr_ne_null]

/-! ### MapRequest -/
def MapRequest.toJson (m : MapRequest) : Json :=
  .obj [ ("Version", encNat m.version)
       , ("NodeKey", encStr m.nodeKey)
       , ("DiscoKey", encOpt encStr m.discoKey)
       , ("Endpoints", encOpt (encList encStr) m.endpoints)
       , ("Stream", encBool m.stream)
       , ("OmitPeers", encBool m.omitPeers)
       , ("Hostinfo", encOpt Hostinfo.toJson m.hostinfo)
       , ("ReadOnly", encBool m.readOnly)
       , ("Compress", encOpt encStr m.compress) ]
def MapRequest.fromJson? (j : Json) : Option MapRequest := do
  let version ← reqField decNat j "Version"
  let nodeKey ← reqField decStr j "NodeKey"
  let discoKey ← optField decStr j "DiscoKey"
  let endpoints ← optField (decArr decStr) j "Endpoints"
  -- Go: `Stream`, `OmitPeers`, `ReadOnly` are all `bool json:",omitzero"` —
  -- omitted when false. The stock client OMITS Stream on non-streaming
  -- MapRequests and OMITS OmitPeers/ReadOnly whenever false; `reqField`
  -- REJECTED every real MapRequest (real-capture lane).
  let stream? ← optField decBool j "Stream"
  let stream := stream?.getD false
  let omitPeers? ← optField decBool j "OmitPeers"
  let omitPeers := omitPeers?.getD false
  let hostinfo ← optField Hostinfo.fromJson? j "Hostinfo"
  let readOnly? ← optField decBool j "ReadOnly"
  let readOnly := readOnly?.getD false
  let compress ← optField decStr j "Compress"
  some { version, nodeKey, discoKey, endpoints, stream, omitPeers, hostinfo, readOnly, compress }
theorem MapRequest.fromJson?_toJson (m : MapRequest) :
    MapRequest.fromJson? (MapRequest.toJson m) = some m := by
  obtain ⟨version, nodeKey, discoKey, endpoints, stream, omitPeers, hostinfo, readOnly, compress⟩ := m
  simp [MapRequest.toJson, MapRequest.fromJson?, reqField_obj, optField_obj, assoc?,
    decNat_encNat, decStr_encStr,
    optDecodeVal_enc decBool_encBool encBool_ne_null,
    optDecodeVal_encOpt decStr_encStr encStr_ne_null,
    optDecodeVal_encOpt (decArr_encList decStr_encStr) (encList_ne_null encStr),
    optDecodeVal_encOpt Hostinfo.fromJson?_toJson Hostinfo.toJson_ne_null]

/-! ### MapResponse (the big one — Node/Peers/PacketFilter/DERPMap/DNSConfig) -/
def MapResponse.toJson (m : MapResponse) : Json :=
  .obj [ ("Node", encOpt Node.toJson m.node)
       , ("Peers", encOpt (encList Node.toJson) m.peers)
       , ("PeersChanged", encOpt (encList Node.toJson) m.peersChanged)
       , ("PeersRemoved", encOpt (encList encNat) m.peersRemoved)
       , ("DNSConfig", encOpt DnsConfig.toJson m.dnsConfig)
       , ("PacketFilter", encList FilterRule.toJson m.packetFilter)
       , ("PacketFilters",
          encOpt (encStrMap (encList FilterRule.toJson)) m.packetFilters)
       , ("DERPMap", encOpt DERPMap.toJson m.derpMap)
       , ("KeepAlive", encBool m.keepAlive)
       , ("Domain", encOpt encStr m.domain) ]
def MapResponse.fromJson? (j : Json) : Option MapResponse := do
  let node ← optField Node.fromJson? j "Node"
  let peers ← optField (decArr Node.fromJson?) j "Peers"
  let peersChanged ← optField (decArr Node.fromJson?) j "PeersChanged"
  let peersRemoved ← optField (decArr decNat) j "PeersRemoved"
  let dnsConfig ← optField DnsConfig.fromJson? j "DNSConfig"
  -- Go: `PacketFilter []FilterRule json:",omitempty"` and
  -- `KeepAlive bool json:",omitempty"` — omitted at zero value. The real
  -- control server OMITS the legacy `PacketFilter` (it sends the newer
  -- `PacketFilters` map) and omits `KeepAlive` when false; `reqField` REJECTED
  -- every real MapResponse (real-capture lane).
  let packetFilter? ← optField (decArr FilterRule.fromJson?) j "PacketFilter"
  let packetFilter := packetFilter?.getD []
  let packetFilters ← optField (decObjMap (decArr FilterRule.fromJson?)) j "PacketFilters"
  let derpMap ← optField DERPMap.fromJson? j "DERPMap"
  let keepAlive? ← optField decBool j "KeepAlive"
  let keepAlive := keepAlive?.getD false
  let domain ← optField decStr j "Domain"
  some { node, peers, peersChanged, peersRemoved, dnsConfig, packetFilter, packetFilters,
         derpMap, keepAlive, domain }
theorem MapResponse.fromJson?_toJson (m : MapResponse) :
    MapResponse.fromJson? (MapResponse.toJson m) = some m := by
  obtain ⟨node, peers, peersChanged, peersRemoved, dnsConfig, packetFilter,
          packetFilters, derpMap, keepAlive, domain⟩ := m
  simp [MapResponse.toJson, MapResponse.fromJson?, optField_obj, assoc?,
    optDecodeVal_enc decBool_encBool encBool_ne_null,
    optDecodeVal_enc (decArr_encList FilterRule.fromJson?_toJson)
      (encList_ne_null FilterRule.toJson),
    optDecodeVal_encOpt Node.fromJson?_toJson Node.toJson_ne_null,
    optDecodeVal_encOpt (decArr_encList Node.fromJson?_toJson) (encList_ne_null Node.toJson),
    optDecodeVal_encOpt (decArr_encList decNat_encNat) (encList_ne_null encNat),
    optDecodeVal_encOpt DnsConfig.fromJson?_toJson DnsConfig.toJson_ne_null,
    optDecodeVal_encOpt DERPMap.fromJson?_toJson DERPMap.toJson_ne_null,
    optDecodeVal_encOpt
      (decObjMap_encStrMap (decArr_encList FilterRule.fromJson?_toJson))
      (encStrMap_ne_null (encList FilterRule.toJson)),
    optDecodeVal_encOpt decStr_encStr encStr_ne_null]

/-! ## §5  Unknown-field tolerance (forward-compat, like the real client)

Decoding reads fields by key and ignores everything else. We witness this
directly: **appending arbitrary extra fields to an encoded message leaves the
decode result unchanged.** Because our objects put the modeled keys first and
`assoc?` is first-match, extra trailing keys are never consulted. -/

/-- Append extra fields to a JSON object (a non-object is returned unchanged). -/
def withExtra : Json → List (String × Json) → Json
  | .obj fs, extra => .obj (fs ++ extra)
  | j, _ => j

/-- **Forward-compatibility, concretely.** A `RegisterRequest` encoded and then
decorated with arbitrary unknown trailing fields still decodes to the original —
the decoder never consults keys it does not model. -/
theorem RegisterRequest.decode_ignores_unknown (m : RegisterRequest)
    (extra : List (String × Json)) :
    RegisterRequest.fromJson? (withExtra (RegisterRequest.toJson m) extra) = some m := by
  obtain ⟨version, nodeKey, oldNodeKey, auth, hostinfo, followup, ephemeral, tailnet⟩ := m
  simp [RegisterRequest.toJson, withExtra, RegisterRequest.fromJson?, reqField_obj,
    optField_obj, assoc?, decNat_encNat, decStr_encStr, decBool_encBool,
    optDecodeVal_enc decBool_encBool encBool_ne_null,
    optDecodeVal_encOpt decStr_encStr encStr_ne_null,
    optDecodeVal_encOpt AuthInfo.fromJson?_toJson AuthInfo.toJson_ne_null,
    optDecodeVal_encOpt Hostinfo.fromJson?_toJson Hostinfo.toJson_ne_null]

/-! ## §6  The text layer lives in `Control/TailcfgWire.lean`

This file owns the **value-level** codec only: `fromJson? (toJson m) = some m`.
The serializer and parser that turn a `Json` into the characters on the socket
used to live here as `partial` definitions validated by `#eval`. They have been
replaced by the **total, proven** text layer in `Control/TailcfgWire.lean`, which
closes the roundtrip at the wire-string level:

* `TailcfgWire.parseChars (renderJ j) = some j` — every JSON value,
* `MapResponse.wireDecode (MapResponse.wireEncode m) = some m` — every message,

and carries the real-sample (`RegisterRequest` / `MapRequest` / `MapResponse`)
execution validation. There is deliberately only one text layer in the tree, so
nothing can drift between an unproven serializer and a proven one.

Leaf *values* — `"nodekey:<hex>"`, `"100.64.0.1/32"`, `"192.168.1.5:41641"` —
are bridged to bytes, with proven inverses, in `Control/TailcfgBridge.lean`.
-/

/-! ## §8  Axiom audit — the codec roundtrips close on the standard axioms only -/

#print axioms AuthInfo.fromJson?_toJson
#print axioms Hostinfo.fromJson?_toJson
#print axioms PortRange.fromJson?_toJson
#print axioms NetPortRange.fromJson?_toJson
#print axioms FilterRule.fromJson?_toJson
#print axioms DERPNode.fromJson?_toJson
#print axioms DERPRegion.fromJson?_toJson
#print axioms DERPMap.fromJson?_toJson
#print axioms DnsConfig.fromJson?_toJson
#print axioms Node.fromJson?_toJson
#print axioms RegisterRequest.fromJson?_toJson
#print axioms RegisterResponse.fromJson?_toJson
#print axioms MapRequest.fromJson?_toJson
#print axioms MapResponse.fromJson?_toJson
#print axioms RegisterRequest.decode_ignores_unknown

/-! ## Cross-verification against the public source (`tailcfg/tailcfg.go`)

Field ↔ JSON-key correspondences confirmed against `github.com/tailscale/tailscale`
`tailcfg/tailcfg.go` (all keys are the Go field name verbatim, PascalCase; `Option`
= the Go `omitempty`/pointer fields):

* `RegisterRequest{Version, NodeKey, OldNodeKey, Auth *RegisterResponseAuth,
  Hostinfo *Hostinfo, Followup string, Ephemeral bool ",omitempty", Tailnet ",omitempty"}`
* `RegisterResponseAuth{AuthKey string ",omitempty"}` (the pre-auth key)
* `RegisterResponse{AuthURL, NodeKeyExpired, MachineAuthorized, Error}`
* `MapRequest{Version, NodeKey, DiscoKey, Endpoints []netip.AddrPort,
  Stream bool, OmitPeers bool, Hostinfo, ReadOnly, Compress}`
* `MapResponse{Node *Node, Peers []*Node, PeersChanged []*Node,
  PeersRemoved []NodeID, DNSConfig *DNSConfig, PacketFilter []FilterRule,
  DERPMap *DERPMap, KeepAlive, Domain}`
* `Node{ID NodeID(int64), StableID, Name, User UserID, Key key.NodePublic,
  Machine, DiscoKey, Addresses []netip.Prefix, AllowedIPs, Endpoints,
  DERP string json:"DERP" (legacy), HomeDERP int, Hostinfo, KeyExpiry time.Time,
  Online *bool, MachineAuthorized}`
* `Hostinfo{OS, Hostname, IPNVersion, RoutableIPs []netip.Prefix}`
* `DERPMap{Regions map[int]*DERPRegion}` ; `DERPRegion{RegionID, RegionCode,
  RegionName, Nodes []*DERPNode}` ; `DERPNode{Name, RegionID, HostName,
  IPv4 ",omitempty", IPv6 ",omitempty", DERPPort ",omitempty", STUNPort ",omitempty"}`
  — NOTE the DERP port field is `DERPPort` (tailcfg.DERPNode, verified against
  tailscale v1.98.8 tailcfg/derpmap.go).
* `FilterRule{SrcIPs []string, DstPorts []NetPortRange, IPProto []int ",omitempty"}` ;
  `NetPortRange{IP string, Bits *int ",omitempty", Ports PortRange}` ;
  `PortRange{First uint16, Last uint16}` — the exact shape `Control/Acl.lean`
  compiles to.

`CapabilityVersion = int`, `NodeID = UserID = int64`, `StableNodeID = string`
(confirmed from the type declarations). `key.NodePublic`/`MachinePublic`/
`DiscoPublic` marshal to `"nodekey:"/"mkey:"/"discokey:" ++ hex`; `netip.Prefix`
to `"a.b.c.d/n"`; `netip.AddrPort` to `"host:port"`; `time.Time` to RFC3339 —
all carried here as their marshaled JSON strings.
-/

end Control.Tailcfg
