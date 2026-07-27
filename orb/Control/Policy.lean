import Control.Acl
import Control.TailcfgWire

/-!
# Control.Policy — the operator-authored HuJSON policy file → the proven ACL compiler

`Control/Acl.lean` **proves** the policy→FilterRules→verdict compilation is *default-deny
sound* (`policy_default_deny`, `policy_allow_iff_entry`) — but it takes an already-tokenized
`Acl.Policy`. A homelab operator, however, authors a **HuJSON policy file**: JSON with `//`
and `/* */` comments and trailing commas, in the public Tailscale ACL syntax (kb/1337). This
module closes that gap:

1. **A HuJSON reader** (`readHuJSON`): a total, string-literal-aware preprocessor
   (`stripC` strips `//` line- and `/* */` block-comments; `dropTC` drops trailing commas)
   composed with `TailcfgWire.parseChars` (drorb's proven total JSON parser). It never touches
   bytes *inside* a string literal, so a policy value containing `//` or `,]` survives.

2. **`parsePolicy : Json → Except Error Acl.Policy`** — decodes the top-level
   `acls`/`groups`/`tagOwners`/`hosts` into `Acl.Policy`, resolving `group:`/`tag:`/host-name
   references to the concrete CIDR sets the compiler consumes, and expanding `dst`
   `"<host>:<ports>"` (with `*`, `22`, `80,443`, `1000-2000` port syntax — kb/1337).

3. **`parsePolicy_wf`** — a parsed policy is a **well-formed** input to the proven compiler
   (`Acl.wf`): every `src`/`dst` selector it emits is a *declared* reference (group/tag/host/
   autogroup/CIDR — a typo'd reference is *rejected*, fail-closed, not silently denied), and
   every destination port range is well-ordered. `parsePolicy` returns `.ok` **only** past this
   check, so the parser *feeds* the default-deny theorem — it can never hand the compiler a
   malformed policy that bypasses the soundness argument.

4. **A real homelab HuJSON file** (`Control/testdata/policy_homelab.hujson`, embedded here as
   `sampleHuJSON`) parses → compiles → the resulting `FilterRule`s resolve a `src group →
   dst:port` rule to exactly the intended `SrcIPs`/`DstPorts` (the four-corner accept/drop
   demonstration on `evalPolicy`).

## Field-name provenance
Every top-level key and value form is the PUBLIC Tailscale ACL syntax (kb/1337, cross-checked):
`acls`[{`action`,`src`,`proto`,`dst`}], `groups`, `tagOwners`, `hosts`; `dst` = `"<host>:<ports>"`;
ports `*` | `N` | `N,M` | `N-M`; selectors `*` | `group:` | `tag:` | `autogroup:` | host | CIDR.
No field is invented.

## Named residuals (explicit, not hidden)
- **IPv6 / `::` compression** in address text is not modeled — this parser is IPv4-CIDR (dotted
  quad + `/len`); v6 selectors are the residual boundary (the compiler's `Cidr` carries a `v6`
  family and `matchCidr` handles it, so this is a *parse-text* gap only, matching `IpFilter`'s
  own address-text residual).
- **`tag:` selectors are no longer a residual** (2026-07-25). A `tag:` token parses to a
  first-class `Acl.Selector.tag`, is *declared* by the `tagOwners` section (a typo'd tag is a
  parse ERROR — `gate_rejects_undeclared_tag`), and is BOUND to addresses at serve time by
  `Control.Tags.withTagBindings`, which is the only writer of `Policy.tags`
  (`parsePolicy_tags_empty`). §9a drives the whole chain.
- **`tagOwners` owner forms.** drorb identities are numeric user ids, so an owner is `user:<N>`
  or `*`. `group:`/`autogroup:`/email owner tokens are REJECTED with a message naming the token
  (`gate_rejects_unsupported_owner`) — never silently mapped. See the users-scope note in
  `Control/Acl.lean`.
- **Bare user-email `src`/`dst`** (e.g. `alice@example.com`) and **`autogroup:`** still resolve
  to the empty set; because `parsePolicy_wf` requires *declared* references, a policy leaning on
  an undeclared one is rejected rather than silently admitting nothing. Group members that are
  literal CIDRs / declared host-names *are* resolved here (a documented self-containedness
  convenience over kb/1337's user-only members).
- **Reader totality vs. round-trip**: `readHuJSON` is *total*; its correctness is *demonstrated*
  on the real file (`#eval`) and the `Json → Acl.Policy` half — the half carrying `parsePolicy_wf`
  — is fully machine-checked. A byte-level `readHuJSON (renderStr j) = some j` round-trip is
  future work (mirrors `TailcfgWire.parseChars_renderJ`).
-/

/-! ## §0  Well-formedness of a compiler input (in the `Acl` namespace) -/

namespace Control.Acl

open IpFilter (Cidr)

/-- A selector is *declared*: a literal CIDR always is; a `group:`/host name must be a
key of the group table; a `tag:` must be a key of `tagOwners`.

★A `.tag` is declared by `tagOwners`, NOT by the tag-binding table — the binding is a
runtime projection of the registry (`Control.Tags.tagBindings`) that is empty when the
file is parsed and changes as nodes come and go. Checking declaredness against
`tagOwners` is what makes `src: ["tag:sever"]` a loud parse ERROR instead of a silent
deny that an operator debugs for an hour. -/
def selDeclared (groups : List (String × List Cidr)) (ow : TagOwners) : Selector → Bool
  | .cidr _ => true
  | .group n => groups.any (fun g => g.1 == n)
  | .tag t => ow.any (fun e => e.1 == t)

/-- An entry is well-formed: nonempty `src`/`dst`, every selector declared, and every
destination port range well-ordered (`first ≤ last`). -/
def entryWf (groups : List (String × List Cidr)) (ow : TagOwners) (e : RawEntry) : Bool :=
  !e.src.isEmpty && !e.dst.isEmpty
    && e.src.all (selDeclared groups ow)
    && e.dst.all (fun sp => selDeclared groups ow sp.1 && decide (sp.2.first ≤ sp.2.last))

/-- A policy is well-formed: every ACL entry is (`Bool`). -/
def wfb (p : Policy) : Bool := p.acls.all (entryWf p.groups p.tagOwners)

/-- **`Acl.wf`** — a policy is a well-formed input to the proven compiler. -/
abbrev wf (p : Policy) : Prop := wfb p = true

end Control.Acl

namespace Control.Policy

open IpFilter (Family Addr Cidr matchCidr)
open Control.Acl
open Control.Tailcfg (Json field?)
open Control.TailcfgWire (parseChars isWs)
open Control.Bridge (parseNat)

/-! ## §1  The HuJSON reader — comment + trailing-comma preprocessing (total) -/

/- Strip `//` line comments and `/* */` block comments, never inside a string
literal. Structural recursion: every recursive call is on a syntactic sub-list of
the matched argument, so this is total with no fuel. -/
mutual
  def stripC : List Char → List Char
    | [] => []
    | '"' :: r => '"' :: copyStr r
    | '/' :: '/' :: r => skipLineC r
    | '/' :: '*' :: r => skipBlockC r
    | c :: r => c :: stripC r
  /-- Inside a `"…"` literal: copy verbatim (honoring `\x` escapes) until the closing
  quote, then resume comment-stripping. -/
  def copyStr : List Char → List Char
    | [] => []
    | '\\' :: c :: r => '\\' :: c :: copyStr r
    | '"' :: r => '"' :: stripC r
    | c :: r => c :: copyStr r
  /-- Drop a `//` comment body up to (and keeping) the newline. -/
  def skipLineC : List Char → List Char
    | [] => []
    | '\n' :: r => '\n' :: stripC r
    | _ :: r => skipLineC r
  /-- Drop a `/* */` comment body up to and including the closing `*/`. -/
  def skipBlockC : List Char → List Char
    | [] => []
    | '*' :: '/' :: r => stripC r
    | _ :: r => skipBlockC r
end

/-- After a comma (with intervening whitespace) does the next token close a
container (`}` / `]`)? If so the comma is trailing. -/
def closesNext : List Char → Bool
  | [] => false
  | c :: r => if isWs c then closesNext r else (c == '}' || c == ']')

/- Drop trailing commas (`,` immediately before a `}`/`]`, whitespace-permitting),
never inside a string literal. Total (structural). -/
mutual
  def dropTC : List Char → List Char
    | [] => []
    | '"' :: r => '"' :: dropTCStr r
    | ',' :: r => if closesNext r then dropTC r else ',' :: dropTC r
    | c :: r => c :: dropTC r
  def dropTCStr : List Char → List Char
    | [] => []
    | '\\' :: c :: r => '\\' :: c :: dropTCStr r
    | '"' :: r => '"' :: dropTC r
    | c :: r => c :: dropTCStr r
end

/-- The HuJSON reader: strip comments, drop trailing commas, then run the proven
total JSON parser. -/
def readHuJSONChars (cs : List Char) : Option Json :=
  parseChars (dropTC (stripC cs))

/-- The HuJSON reader over a `String`. -/
def readHuJSON (s : String) : Option Json :=
  readHuJSONChars s.toList

/-! ## §2  IPv4 dotted-quad / CIDR text → `IpFilter.Cidr` -/

/-- 8 bits of `n` (mod 256), most-significant first. -/
def byteBits (n : Nat) : List Bool :=
  (List.range 8).reverse.map (fun k => n.testBit k)

/-- Split a char list on a separator (keeps empty fields; never drops). -/
def splitOnC (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: r =>
    if c == sep then [] :: splitOnC sep r
    else match splitOnC sep r with
         | [] => [[c]]
         | h :: t => (c :: h) :: t

/-- Parse a whole decimal `< 256` (an IPv4 octet or a prefix length). -/
def parseByte (cs : List Char) : Option Nat :=
  match parseNat cs with
  | some (n, []) => if n < 256 then some n else none
  | _ => none

/-- Parse `a.b.c.d` to 32 big-endian bits. -/
def parseIPv4 (cs : List Char) : Option (List Bool) :=
  match splitOnC '.' cs with
  | [a, b, c, d] =>
    match parseByte a, parseByte b, parseByte c, parseByte d with
    | some na, some nb, some nc, some nd =>
        some (byteBits na ++ byteBits nb ++ byteBits nc ++ byteBits nd)
    | _, _, _, _ => none
  | _ => none

/-- Parse `a.b.c.d` (⇒ `/32`) or `a.b.c.d/len` (`len ≤ 32`) to an `IpFilter.Cidr`. -/
def parseCidr (cs : List Char) : Option Cidr :=
  match splitOnC '/' cs with
  | [ip] => (parseIPv4 ip).map (fun bits => ⟨Family.v4, bits, 32⟩)
  | [ip, lenCs] =>
    match parseIPv4 ip, parseByte lenCs with
    | some bits, some l => if l ≤ 32 then some ⟨Family.v4, bits, l⟩ else none
    | _, _ => none
  | _ => none

/-! ## §3  Selector / destination / port token parsing -/

/-- `0.0.0.0/0` — matches all IPv4. -/
def anyV4 : Cidr := ⟨Family.v4, [], 0⟩
/-- `::/0` — matches all IPv6. -/
def anyV6 : Cidr := ⟨Family.v6, [], 0⟩

/-- Does a token start with the literal `tag:` prefix (kb/1337's tag namespace)? -/
def isTagTok (tok : List Char) : Bool := tok.take 4 == "tag:".toList

/-- A `src`/`dst`-host token → selectors. `*` → all (v4 and v6); a literal CIDR/IP →
`Selector.cidr`; a `tag:`-prefixed token → **`Selector.tag`** (resolved through the
registry-derived tag-binding table, `Control.Tags`); anything else (`group:`/
`autogroup:`/host name/email) → `Selector.group <token>`, resolved through the policy's
group table. Both named forms are checked *declared* by `parsePolicy_wf`. -/
def parseSelTok (tok : List Char) : List Selector :=
  if tok == ['*'] then [Selector.cidr anyV4, Selector.cidr anyV6]
  else if isTagTok tok then [Selector.tag (String.ofList tok)]
  else match parseCidr tok with
       | some c => [Selector.cidr c]
       | none => [Selector.group (String.ofList tok)]

/-- Re-join a `:`-split host part (so `tag:web` survives a last-colon split). -/
def joinColon : List (List Char) → List Char
  | [] => []
  | [x] => x
  | x :: t => x ++ ':' :: joinColon t

/-- Split `"<host>:<ports>"` at the **last** `:` (IPv4-only; v6 `[…]:p` is residual). -/
def splitLastColon (cs : List Char) : Option (List Char × List Char) :=
  match (splitOnC ':' cs).reverse with
  | [] => none
  | [_] => none
  | ports :: hostRev => some (joinColon hostRev.reverse, ports)

/-- One port spec: `*` | `N` | `N-M` (`M ≤ 65535`, `N ≤ M`). -/
def parsePortRange1 (cs : List Char) : Option PortRange :=
  if cs == ['*'] then some ⟨0, 65535⟩
  else match splitOnC '-' cs with
    | [a] => match parseNat a with
             | some (n, []) => if n ≤ 65535 then some ⟨n, n⟩ else none
             | _ => none
    | [a, b] => match parseNat a, parseNat b with
             | some (na, []), some (nb, []) =>
                 if na ≤ nb ∧ nb ≤ 65535 then some ⟨na, nb⟩ else none
             | _, _ => none
    | _ => none

/-- A comma-separated port list (`80,443`) → the port ranges. -/
def parsePorts (cs : List Char) : Option (List PortRange) :=
  (splitOnC ',' cs).mapM parsePortRange1

/-- A `dst` token `"<host>:<ports>"` → `(selector, portRange)` pairs (host selectors
× port ranges). -/
def parseDstTok (tok : List Char) : Option (List (Selector × PortRange)) := do
  let (host, ports) ← splitLastColon tok
  let prs ← parsePorts ports
  pure ((parseSelTok host).flatMap (fun s => prs.map (fun pr => (s, pr))))

/-! ## §4  Protocol -/

/-- `tcp`/`udp`/`icmp` → IANA number, or a literal number (kb/1337 `proto`). -/
def protoNum (cs : List Char) : Option Nat :=
  if cs == "tcp".toList then some 6
  else if cs == "udp".toList then some 17
  else if cs == "icmp".toList then some 1
  else match parseNat cs with | some (n, []) => some n | _ => none

/-! ## §5  `parsePolicy` — the top-level decoder (permissive; `wf` gate is §7) -/

/-- Lift an `Option` into `Except` with a message. -/
def optE (msg : String) : Option α → Except String α
  | some a => .ok a
  | none => .error msg

/-- Require a field, else a decode error. -/
def reqField (j : Json) (k : String) : Except String Json :=
  match field? j k with
  | some v => .ok v
  | none => .error s!"missing field: {k}"

/-- A JSON string → its chars. -/
def jStr : Json → Except String (List Char)
  | .str s => .ok s.toList
  | _ => .error "expected string"

/-- A JSON array of strings → the char lists. -/
def jArrStr : Json → Except String (List (List Char))
  | .arr xs => xs.mapM jStr
  | _ => .error "expected array of strings"

/-- Decode `proto` (optional). -/
def parseProto (j? : Option Json) : Except String (List Nat) :=
  match j? with
  | none => .ok []
  | some (.str s) => match protoNum s.toList with
                     | some n => .ok [n]
                     | none => .error s!"bad proto: {s}"
  | some (.num i) => if i ≥ 0 then .ok [i.toNat] else .error "proto number must be ≥ 0"
  | some _ => .error "proto must be a string or number"

/-- Decode one `acls[]` entry (only `action:"accept"` — deny is the compiler's
default). -/
def parseEntry (j : Json) : Except String RawEntry := do
  let av ← reqField j "action"
  let actionChars ← jStr av
  let _ ← (if actionChars = "accept".toList then (.ok () : Except String Unit)
           else .error "only action=\"accept\" is supported (deny is default-deny)")
  let srcToks ← reqField j "src" >>= jArrStr
  let dstToks ← reqField j "dst" >>= jArrStr
  let protos ← parseProto (field? j "proto")
  let dstPairs ← dstToks.mapM (fun t => optE s!"bad dst token: {String.ofList t}" (parseDstTok t))
  pure { src := srcToks.flatMap parseSelTok
       , dst := dstPairs.flatMap id
       , protos := protos }

/-- Resolve a `groups` member to CIDRs: a literal CIDR, or a declared host name;
otherwise (email / undeclared) the empty set (residual — see module header). -/
def resolveMember (hosts : List (String × List Cidr)) (m : List Char) : List Cidr :=
  match parseCidr m with
  | some c => [c]
  | none => lookupGroup hosts (String.ofList m)

/-- `hosts`: `"<name>": "<cidr>"` → `(name, [cidr])`. -/
def parseHosts (j : Json) : Except String (List (String × List Cidr)) :=
  match field? j "hosts" with
  | none => .ok []
  | some (.obj fs) => fs.mapM (fun kv =>
      match kv.2 with
      | .str s => match parseCidr s.toList with
                  | some c => .ok (kv.1, [c])
                  | none => .error s!"bad host CIDR for {kv.1}: {s}"
      | _ => .error "host value must be a string")
  | some _ => .error "hosts must be an object"

/-- `groups`: `"group:<name>": [member]` → `(group:<name>, resolved CIDRs)`. -/
def parseGroups (hosts : List (String × List Cidr)) (j : Json)
    : Except String (List (String × List Cidr)) :=
  match field? j "groups" with
  | none => .ok []
  | some (.obj fs) => fs.mapM (fun kv =>
      match kv.2 with
      | .arr xs => do
          let members ← xs.mapM jStr
          .ok (kv.1, members.flatMap (resolveMember hosts))
      | _ => .error s!"group {kv.1} value must be an array")
  | some _ => .error "groups must be an object"

/-! ### `tagOwners` — WHO may apply a tag (the ownership declaration)

Public syntax: `"tagOwners": { "tag:web": [owner, …] }` (kb/1337). drorb's owner
principals are **numeric user ids** — `Control.Node.user` / `KeyAttrs.user` are `Nat`s
and drorb has no user directory, no email identity and no OIDC (see `Control.Acl`'s
users-scope note). So an owner token is `user:<N>` or `*`.

★An owner token drorb cannot resolve — `group:eng`, `autogroup:admin`, `alice@ex.com`,
`tag:base` — is **REJECTED, loudly**, naming the token. The alternative (resolve it to
"nobody") would compile to a silent deny that looks like a drorb bug; the alternative
(resolve it to "anybody") would be a security hole. Neither is acceptable, so the
operator is told. -/

/-- Parse one owner token: `user:<N>` or `*`. -/
def parseOwnerTok (tok : List Char) : Option Owner :=
  if tok == ['*'] then some Owner.anyUser
  else if tok.take 5 == "user:".toList then
    match parseNat (tok.drop 5) with
    | some (n, []) => some (Owner.user n)
    | _ => none
  else none

/-- `tagOwners`: `"tag:<name>": [owner…]` → the ownership table. A tag key that is not
`tag:`-prefixed, or an owner token that is not `user:<N>`/`*`, is rejected. -/
def parseTagOwners (j : Json) : Except String TagOwners :=
  match field? j "tagOwners" with
  | none => .ok []
  | some (.obj fs) => fs.mapM (fun kv =>
      if !(isTagTok kv.1.toList) then
        .error s!"tagOwners key must be tag:<name>, got: {kv.1}"
      else match kv.2 with
      | .arr xs => do
          let toks ← xs.mapM jStr
          let owners ← toks.mapM (fun t =>
            match parseOwnerTok t with
            | some o => .ok o
            | none => .error
                s!"tagOwners[{kv.1}]: unsupported owner '{String.ofList t}' — drorb identities are numeric user ids, so an owner must be \"user:<N>\" or \"*\" (no user directory / OIDC: see Control.Acl users-scope)")
          .ok (kv.1, owners)
      | _ => .error s!"tagOwners[{kv.1}] value must be an array of owners")
  | some _ => .error "tagOwners must be an object"

/-- The standard `autogroup:` names, declared (residual resolution). -/
def stdAutogroups : List (String × List Cidr) :=
  [ ("autogroup:internet", []), ("autogroup:member", []), ("autogroup:members", [])
  , ("autogroup:self", []), ("autogroup:admin", []), ("autogroup:nonroot", []) ]

/-- Decode the whole policy (permissive: emits `Selector.group` for any non-CIDR
token — the *declaredness* check is the `wf` gate in §7). -/
def parseRaw (j : Json) : Except String Policy := do
  let hosts ← parseHosts j
  let groups ← parseGroups hosts j
  let owners ← parseTagOwners j
  let table := hosts ++ groups ++ stdAutogroups
  let aclsv ← reqField j "acls"
  let entries ← (match aclsv with
                 | .arr xs => xs.mapM parseEntry
                 | _ => .error "acls must be an array")
  -- ★`tags := []` is NOT an omission: the tag→address BINDING is a projection of the
  -- node registry (`Control.Tags.withTagBindings`), never of the file. The parser can
  -- only DECLARE tags (`tagOwners`) and NAME them (`Selector.tag`) — it can never bind
  -- one. `parsePolicy_tags_empty` proves that, generally.
  .ok { groups := table, acls := entries, tagOwners := owners, tags := [] }

/-! ## §7  `parsePolicy` — decode **only** past the `wf` gate -/

/-- **The operator-facing entry point.** Decode the HuJSON-derived `Json`, and return
`.ok` **only** if the result is a well-formed compiler input; otherwise fail closed. -/
def parsePolicy (j : Json) : Except String Policy :=
  match parseRaw j with
  | .error e => .error e
  | .ok pol0 =>
    -- ★The tag→address BINDING is never file-authored: whatever `parseRaw` produced,
    -- the operator-facing entry point CLEARS it. Bindings can only come from
    -- `Control.Tags.withTagBindings`, a projection of the node registry under the
    -- `tagOwners` gate. `parsePolicy_tags_empty` is this line, as a theorem.
    if Control.Acl.wfb { pol0 with tags := ([] : List (String × List Cidr)) }
    then .ok { pol0 with tags := ([] : List (String × List Cidr)) }
    else .error "policy references an undeclared selector or has an invalid port range"

/-- Text → policy: read HuJSON, then decode. -/
def parseHuPolicy (s : String) : Except String Policy :=
  match readHuJSON s with
  | some j => parsePolicy j
  | none => .error "HuJSON parse failed"

/-- ★**THE THEOREM the parser must satisfy.** A successfully-parsed policy is a
**well-formed** input to the proven ACL compiler — so `Acl.policy_default_deny` /
`Acl.policy_allow_iff_entry` apply to it verbatim. The parser *feeds* the soundness
theorem; it can never emit a policy that bypasses the `wf` gate. -/
theorem parsePolicy_wf {j : Json} {pol : Policy}
    (h : parsePolicy j = .ok pol) : Control.Acl.wf pol := by
  unfold parsePolicy at h
  split at h
  · simp at h
  · next p0 _ =>
    split at h
    · next hw =>
        have hpp : { p0 with tags := ([] : List (String × List Cidr)) } = pol := by injection h
        exact hpp ▸ hw
    · simp at h

/-- **Corollary — parsed ⇒ default-deny sound.** A packet admitted by no ACL entry of
a parsed policy is Dropped. (Direct from `Acl.policy_default_deny`, RESTATED over the
tag-extended language: the admission spec resolves `.tag` selectors through `pol.tags`
as well.) -/
theorem parsed_default_deny {j : Json} {pol : Policy}
    (_h : parsePolicy j = .ok pol) (pkt : Packet)
    (hne : ∀ e ∈ pol.acls, entryAdmits pol.groups pol.tags e pkt = false) :
    evalPolicy pol pkt = Verdict.drop :=
  policy_default_deny pol pkt hne

/-- **Corollary — parsed ⇒ soundness.** A parsed policy Allows a packet iff some ACL
entry admits it (with group AND tag resolution). (Direct from
`Acl.policy_allow_iff_entry`, restated.) -/
theorem parsed_allow_iff_entry {j : Json} {pol : Policy}
    (_h : parsePolicy j = .ok pol) (pkt : Packet) :
    evalPolicy pol pkt = Verdict.allow
      ↔ ∃ e ∈ pol.acls, entryAdmits pol.groups pol.tags e pkt = true :=
  policy_allow_iff_entry pol pkt

/-- ★**A POLICY FILE CANNOT FORGE A TAG BINDING.** Whatever HuJSON an operator (or an
attacker with write access to the policy file) hands the parser, the resulting policy's
tag-binding table is EMPTY. Bindings can therefore only come from
`Control.Tags.withTagBindings`, which applies the `tagOwners` gate to the actual node
registry — so "which addresses does `tag:web` denote" is never an authorable field.

General over the input `Json`; this is what makes the `.tag`/`.group` namespace split
(`Acl.tt_tag_group_namespace_disjoint`) load-bearing rather than cosmetic. -/
theorem parsePolicy_tags_empty {j : Json} {pol : Policy}
    (h : parsePolicy j = .ok pol) : pol.tags = [] := by
  unfold parsePolicy at h
  split at h
  · simp at h
  · next p0 _ =>
    split at h
    · next _ =>
        have hpp : { p0 with tags := ([] : List (String × List Cidr)) } = pol := by injection h
        exact hpp ▸ rfl
    · simp at h

/-- **A declared tag is a real declaration.** If `parsePolicy` accepts a policy whose
entry sources a `.tag t`, then `t` is a key of the parsed `tagOwners` — a typo'd tag is
a parse ERROR, not a silent deny. (From `parsePolicy_wf` + `selDeclared`.) -/
theorem parsed_tag_declared {j : Json} {pol : Policy}
    (h : parsePolicy j = .ok pol) (e : RawEntry) (he : e ∈ pol.acls)
    (t : String) (hs : Selector.tag t ∈ e.src) :
    pol.tagOwners.any (fun x => x.1 == t) = true := by
  have hwf : wfb pol = true := parsePolicy_wf h
  rw [wfb, List.all_eq_true] at hwf
  have hE : entryWf pol.groups pol.tagOwners e = true := hwf e he
  rw [entryWf] at hE
  simp only [Bool.and_eq_true] at hE
  have hsrc : e.src.all (selDeclared pol.groups pol.tagOwners) = true := hE.1.2
  rw [List.all_eq_true] at hsrc
  exact hsrc _ hs

/-! ## §8  Non-vacuity — the `wf` gate is load-bearing

A HuJSON policy whose `src` names an **undeclared** group is *rejected* (fail-closed),
not silently compiled to a deny-everything rule. -/

/-- A policy with a typo'd group reference (`group:typo` is never declared). -/
def badHuJSON : String :=
  "{ \"acls\": [ { \"action\": \"accept\", \"src\": [\"group:typo\"], \"dst\": [\"10.0.0.0/8:22\"] } ] }"

/-! ## §9  ★THE GATE — a real homelab HuJSON file, end to end

The exact bytes of `Control/testdata/policy_homelab.hujson`. Comments and trailing
commas exercise the HuJSON reader; `group:admins → dst:port` exercises group
resolution to concrete `SrcIPs`/`DstPorts`. -/

def sampleHuJSON : String :=
"{
  // homelab tailnet policy — HuJSON: // and /* */ comments + trailing commas
  \"hosts\": {
    \"homeserver\": \"100.64.0.10/32\",
    \"lan\":        \"192.168.1.0/24\",
  },
  \"groups\": {
    /* group members resolved to CIDRs from `hosts` (self-contained) */
    \"group:admins\": [\"homeserver\"],
  },
  \"tagOwners\": {
    /* WHO may apply a tag. drorb identities are numeric user ids: \"user:<N>\" or \"*\". */
    \"tag:web\": [\"user:7\"],
  },
  \"acls\": [
    // admins: SSH to the LAN, and HTTP(S) to the homeserver
    { \"action\": \"accept\", \"src\": [\"group:admins\"],
      \"dst\": [\"lan:22\", \"homeserver:80,443\"], \"proto\": \"tcp\" },
    // the LAN may reach the homeserver on 443
    { \"action\": \"accept\", \"src\": [\"192.168.1.0/24\"], \"dst\": [\"homeserver:443\"] },
    // ★anyone in the LAN may reach whatever is TAGGED tag:web, on 443
    { \"action\": \"accept\", \"src\": [\"192.168.1.0/24\"], \"dst\": [\"tag:web:443\"] },
  ],
}"

/-- The `Json` value the HuJSON reader produces from `sampleHuJSON` (verified equal by
`#eval` demonstration below — `reader_yields_sampleJson`). The verified end-to-end gate
theorems run kernel-`decide` on the `Json → Acl.Policy → FilterRules → verdict` pipeline
from this literal; the fuel-bounded *text* parse is demonstrated, not kernel-reduced. -/
def sampleJson : Json :=
  .obj
    [("hosts", .obj [("homeserver", .str "100.64.0.10/32"), ("lan", .str "192.168.1.0/24")]),
     ("groups", .obj [("group:admins", .arr [.str "homeserver"])]),
     ("tagOwners", .obj [("tag:web", .arr [.str "user:7"])]),
     ("acls",
      .arr
        [.obj [("action", .str "accept"), ("src", .arr [.str "group:admins"]),
               ("dst", .arr [.str "lan:22", .str "homeserver:80,443"]), ("proto", .str "tcp")],
         .obj [("action", .str "accept"), ("src", .arr [.str "192.168.1.0/24"]),
               ("dst", .arr [.str "homeserver:443"])],
         .obj [("action", .str "accept"), ("src", .arr [.str "192.168.1.0/24"]),
               ("dst", .arr [.str "tag:web:443"])]])]

-- Demonstration: the HuJSON reader, on the real file bytes (comments + trailing
-- commas), yields exactly `sampleJson`. (#eval — the text parser is not kernel-reduced.)
#eval (reprStr (readHuJSON sampleHuJSON).get! == reprStr sampleJson)   -- expect: true
-- Demonstration: the parsed + compiled `FilterRule`s (group→CIDR resolution).
#eval match parsePolicy sampleJson with
  | .ok p => reprStr (Control.Acl.compile p)
  | .error e => e

/-- An IPv4 test address. -/
def mkAddr4 (a b c d : Nat) : Addr := ⟨Family.v4, byteBits a ++ byteBits b ++ byteBits c ++ byteBits d⟩

/-- The compiled test policy (the parse succeeds; `gate_parses`/`gate_wf` pin that). -/
def gp : Policy := (parsePolicy sampleJson).toOption.getD { groups := [], acls := [] }

/-! ### Test packets (source, destination, port, proto) -/
def pktAdminSsh   : Packet := ⟨mkAddr4 100 64 0 10, mkAddr4 192 168 1 5,  22, 6⟩   -- admin → lan:22 tcp
def pktAdminHttp  : Packet := ⟨mkAddr4 100 64 0 10, mkAddr4 100 64 0 10,  80, 6⟩   -- admin → home:80 tcp
def pktAdminHttps : Packet := ⟨mkAddr4 100 64 0 10, mkAddr4 100 64 0 10, 443, 6⟩   -- admin → home:443 tcp
def pktLanToHome  : Packet := ⟨mkAddr4 192 168 1 5, mkAddr4 100 64 0 10, 443, 17⟩  -- lan → home:443 (any proto)
def pktWrongPort  : Packet := ⟨mkAddr4 100 64 0 10, mkAddr4 192 168 1 5,  23, 6⟩   -- admin → lan:23 (only 22 open)
def pktOutsider   : Packet := ⟨mkAddr4 10 0 0 1,    mkAddr4 100 64 0 10, 443, 6⟩   -- non-member src
def pktWrongProto : Packet := ⟨mkAddr4 100 64 0 10, mkAddr4 192 168 1 5,  22, 17⟩  -- admin → lan:22 but udp (rule is tcp)

/-! ### ★THE GATE — verified end to end (kernel `decide`, `Json → verdict`) -/

set_option maxRecDepth 4000 in
/-- The real policy parses to a **well-formed** compiler input. -/
theorem gate_parses : (parsePolicy sampleJson).isOk = true := by decide

set_option maxRecDepth 4000 in
/-- ...and it satisfies `Acl.wf` (so `parsePolicy_wf` + the soundness theorems apply). -/
theorem gate_wf : Control.Acl.wfb gp = true := by decide

set_option maxRecDepth 4000 in
/-- **Resolution shape**: three compiled rules; rule 1 (`group:admins → …`) carries proto
`tcp`=6 and **three** `dst`s (`lan:22`, `homeserver:80`, `homeserver:443` — the `80,443`
port list expanded); rule 2 carries no proto constraint and one `dst`; ★rule 3 (`dst
tag:web:443`) compiles to **ZERO** `dst`s — the FILE alone binds no tag. The addresses
`tag:web` denotes come from the node registry (`Control.Tags.withTagBindings`), which
`gate_tag_*` below drives. -/
theorem gate_shape :
    (Control.Acl.compile gp).map (fun r => (r.protos, r.dsts.length))
      = [([6], 3), ([], 1), ([], 0)] := by
  decide

set_option maxRecDepth 4000 in
/-- **Resolution of `SrcIPs`**: the `group:admins` source of rule 1 resolved to exactly the
homeserver host CIDR `100.64.0.10/32`, and rule 2's literal source to `192.168.1.0/24`. -/
theorem gate_srcips :
    (Control.Acl.compile gp).map (fun r => r.srcs) =
      [ [⟨Family.v4, byteBits 100 ++ byteBits 64 ++ byteBits 0 ++ byteBits 10, 32⟩]
      , [⟨Family.v4, byteBits 192 ++ byteBits 168 ++ byteBits 1 ++ byteBits 0, 24⟩]
      , [⟨Family.v4, byteBits 192 ++ byteBits 168 ++ byteBits 1 ++ byteBits 0, 24⟩] ] := by
  decide

set_option maxRecDepth 4000 in
theorem gate_admin_ssh_allow   : evalPolicy gp pktAdminSsh   = Verdict.allow := by decide
set_option maxRecDepth 4000 in
theorem gate_admin_http_allow  : evalPolicy gp pktAdminHttp  = Verdict.allow := by decide
set_option maxRecDepth 4000 in
theorem gate_admin_https_allow : evalPolicy gp pktAdminHttps = Verdict.allow := by decide
set_option maxRecDepth 4000 in
theorem gate_lan_to_home_allow : evalPolicy gp pktLanToHome  = Verdict.allow := by decide
set_option maxRecDepth 4000 in
/-- Right src/dst but a port the policy never opened → Dropped (port check load-bearing). -/
theorem gate_wrong_port_drop   : evalPolicy gp pktWrongPort  = Verdict.drop := by decide
set_option maxRecDepth 4000 in
/-- A source in no `src` set → Dropped (default-deny). -/
theorem gate_outsider_drop     : evalPolicy gp pktOutsider   = Verdict.drop := by decide
set_option maxRecDepth 4000 in
/-- Right src/dst/port but wrong protocol (udp, rule is tcp) → Dropped (proto load-bearing). -/
theorem gate_wrong_proto_drop  : evalPolicy gp pktWrongProto = Verdict.drop := by decide

/-! ### Non-vacuity — the `wf` gate rejects an undeclared reference (fail-closed) -/

/-- `sampleJson` with `group:admins` mistyped as `group:typo` (never declared). -/
def badJson : Json :=
  .obj [("acls",
    .arr [.obj [("action", .str "accept"), ("src", .arr [.str "group:typo"]),
                ("dst", .arr [.str "10.0.0.0/8:22"])]])]

set_option maxRecDepth 4000 in
/-- **The gate is load-bearing**: a policy naming an undeclared selector is *rejected*,
not silently compiled to a deny-everything rule. -/
theorem gate_rejects_undeclared : (parsePolicy badJson).isOk = false := by decide

/-- LAN host → the (would-be) tagged node on 443. -/
def pktLanToTagged : Packet :=
  ⟨mkAddr4 192 168 1 5, mkAddr4 100 64 0 9, 443, 6⟩
/-- LAN host → the tagged node on **22** (the tag rule opens only 443, and the two
`homeserver` rules do not name `100.64.0.9`). -/
def pktLanToTaggedSsh : Packet :=
  ⟨mkAddr4 192 168 1 5, mkAddr4 100 64 0 9, 22, 6⟩

/-! ## §9a  Tag references in the file — declared, and unbound

`sampleJson`'s third ACL entry is `src 192.168.1.0/24 → dst tag:web:443`, and its
`tagOwners` says only **user 7** may apply `tag:web`. What this file can pin is the
FILE half of the chain: the declaration parses, the reference parses to a real
`Selector.tag`, and the binding table is EMPTY — the file alone confers nothing.

The registry half (a legitimately-tagged node making the rule fire, and an imposter
being denied) lives in `Control/AclTagGate.lean`, which can import `Control.Tags`
without `Control.Policy` the namespace colliding with `Control.Policy` the structure. -/

set_option maxRecDepth 8000 in
/-- **Tag file-gate 1 — the parsed file declares the ownership drorb can enforce.** -/
theorem gate_tagowners_parsed : gp.tagOwners = [("tag:web", [Owner.user 7])] := by decide

set_option maxRecDepth 8000 in
/-- **Tag file-gate 2 — the file binds NOTHING.** `parsePolicy` leaves the tag-binding
table empty (the general statement is `parsePolicy_tags_empty`), so before the registry
is consulted `tag:web` denotes no address and a LAN packet to the would-be tagged host
is DROPPED. -/
theorem gate_tag_unbound_drops :
    gp.tags = [] ∧ evalPolicy gp pktLanToTagged = Verdict.drop := by decide

/-! ### Non-vacuity — the tag surface fails CLOSED on operator error -/

/-- A policy naming `tag:typo`, which no `tagOwners` entry declares. -/
def badTagJson : Json :=
  .obj [("tagOwners", .obj [("tag:web", .arr [.str "user:7"])]),
        ("acls", .arr [.obj [("action", .str "accept"), ("src", .arr [.str "tag:typo"]),
                             ("dst", .arr [.str "10.0.0.0/8:22"])]])]

/-- A policy whose `tagOwners` uses an owner form drorb does not model. -/
def badOwnerJson : Json :=
  .obj [("tagOwners", .obj [("tag:web", .arr [.str "autogroup:admin"])]),
        ("acls", .arr [.obj [("action", .str "accept"), ("src", .arr [.str "tag:web"]),
                             ("dst", .arr [.str "10.0.0.0/8:22"])]])]

set_option maxRecDepth 4000 in
/-- **An undeclared tag is a parse ERROR**, not a silent deny: `tag:typo` never appears
in `tagOwners`, so `selDeclared` rejects it and the whole file is refused (the coord
then serves `safeDefaultPolicy`, deny-all). -/
theorem gate_rejects_undeclared_tag : (parsePolicy badTagJson).isOk = false := by decide

set_option maxRecDepth 4000 in
/-- **An owner form drorb cannot resolve is a parse ERROR**, naming the token — never
silently mapped to "nobody" (a confusing deny) or "anybody" (a hole). -/
theorem gate_rejects_unsupported_owner : (parsePolicy badOwnerJson).isOk = false := by
  decide

#eval gp.tagOwners
#eval evalPolicy gp pktLanToTagged          -- drop  (file alone binds nothing)
#eval parsePolicy badOwnerJson              -- the loud rejection message

/-! ## §9b  `autoApprovers` — the HuJSON auto-approval section → `Routes.AutoApprovers`

Public Tailscale ACL syntax (kb/1337, cross-checked; headscale mirrors it):

```
"autoApprovers": {
  "routes":   { "192.168.50.0/24": ["tag:home", "group:eng"] },
  "exitNode": ["tag:exit"]
}
```

`routes` maps a CIDR to the approver aliases permitted to advertise a route within
it; `exitNode` lists the approvers permitted to advertise an exit node (headscale:
*"`192.168.0.0/24` is automatically approved once announced by a subnet router that
advertises the tag `tag:router`"*). This parses the section into
`(List (Cidr × List String) × List String)` — the `routes` and `exitNode` approver
sets, over this module's native `IpFilter.Cidr` (via the existing `parseCidr`, so
no new import perturbs the `Acl.*` name resolution). `Control.RoutesServe` bridges
each `Cidr` to the coordination core's `Prefix` (`Control.Join.cidrToPrefix`),
wraps the result in `Control.Routes.AutoApprovers`, and `Control.Routes.autoApproves`
consumes it to decide auto-approval; an unparseable route CIDR is *rejected*
(fail-closed). -/

/-- A JSON array of approver aliases → the alias strings. -/
def parseApprovers (j : Json) : Except String (List String) :=
  match j with
  | .arr xs => xs.mapM (fun x => match x with
      | .str s => .ok s
      | _ => .error "approver must be a string")
  | _ => .error "autoApprovers value must be an array of approvers"

/-- `autoApprovers.routes`: `"<cidr>": [approver…]` → `(cidr, approvers)` (a bad
CIDR key is rejected, fail-closed). -/
def parseAutoRoutes (j : Json) : Except String (List (Cidr × List String)) :=
  match j with
  | .obj fs => fs.mapM (fun kv =>
      match parseCidr kv.1.toList with
      | some c => do let apps ← parseApprovers kv.2; pure (c, apps)
      | none => .error s!"bad autoApprovers route CIDR: {kv.1}")
  | _ => .error "autoApprovers.routes must be an object"

/-- **Parse the `autoApprovers` section** into the `(routes, exitNode)` approver
sets. An absent section is the empty (no auto-approval) config; a malformed one
fails closed. `Control.RoutesServe` wraps the result in `Routes.AutoApprovers`. -/
def parseAutoApprovers (j : Json) :
    Except String (List (Cidr × List String) × List String) :=
  match field? j "autoApprovers" with
  | none => .ok ([], [])
  | some jaa =>
    match jaa with
    | .obj _ => do
        let routes ← match field? jaa "routes" with
          | some r => parseAutoRoutes r
          | none => .ok []
        let exit ← match field? jaa "exitNode" with
          | some e => parseApprovers e
          | none => .ok []
        pure (routes, exit)
    | _ => .error "autoApprovers must be an object"

/-! ### The autoApprovers gate — the parse shape (decision tie: `Control.RoutesServe`) -/

/-- A homelab `autoApprovers`: `192.168.50.0/24` approvable by `tag:home`; an exit
node approvable by `tag:exit`. -/
def sampleAAJson : Json :=
  .obj [("autoApprovers",
    .obj [("routes", .obj [("192.168.50.0/24", .arr [.str "tag:home"])]),
          ("exitNode", .arr [.str "tag:exit"])])]

/-- The `(routes, exitNode)` value the section should parse to — the CIDR key
decoded to `IpFilter.Cidr` (v4, MSB-first 32-bit net, `/24`). -/
def expectedAA : List (Cidr × List String) × List String :=
  ([(⟨Family.v4, byteBits 192 ++ byteBits 168 ++ byteBits 50 ++ byteBits 0, 24⟩, ["tag:home"])],
    ["tag:exit"])

/-- **The section parses to the expected config** — `192.168.50.0/24 ↦ [tag:home]`
and `exitNode ↦ [tag:exit]`, the CIDR key decoded to `IpFilter.Cidr`. -/
theorem autoApprovers_parses :
    (parseAutoApprovers sampleAAJson).toOption = some expectedAA := by
  native_decide

/-- **Non-vacuity — a malformed route CIDR is rejected (fail-closed).** -/
def badAAJson : Json :=
  .obj [("autoApprovers", .obj [("routes", .obj [("not-a-cidr", .arr [.str "tag:x"])])])]
theorem aa_rejects_bad_cidr : (parseAutoApprovers badAAJson).isOk = false := by native_decide

/-! ## §10  Axiom audit -/

#print axioms parsePolicy_wf
#print axioms parsed_default_deny
#print axioms parsed_allow_iff_entry
#print axioms gate_parses
#print axioms gate_wf
#print axioms gate_shape
#print axioms gate_srcips
#print axioms gate_admin_ssh_allow
#print axioms gate_wrong_port_drop
#print axioms gate_outsider_drop
#print axioms gate_wrong_proto_drop
#print axioms gate_rejects_undeclared
#print axioms parsePolicy_tags_empty
#print axioms parsed_tag_declared
#print axioms gate_tagowners_parsed
#print axioms gate_tag_unbound_drops
#print axioms gate_rejects_undeclared_tag
#print axioms gate_rejects_unsupported_owner
#print axioms autoApprovers_parses
#print axioms aa_rejects_bad_cidr

end Control.Policy
