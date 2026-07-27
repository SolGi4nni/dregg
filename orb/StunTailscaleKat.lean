/-
# StunTailscaleKat — drorb's proven STUN Binding server, on the REAL bytes a stock
`tailscale` client sends when it is trying to discover a direct path

A stock `tailscale` client cannot attempt a direct (non-DERP) path to a peer unless it
knows its OWN reflexive transport address — the `host:port` a peer on the far side of the
NAT actually sees. It learns that from `netcheck`, which sends a **STUN Binding request**
(RFC 5389) to the STUN service of every DERP region in the netmap the coordinator served
it, and reads XOR-MAPPED-ADDRESS out of the reply.

When nothing answers, `netcheck` reports `udp=false` and the client's endpoint set
contains only local interface addresses:

    netcheck: netcheck: UDP is blocked, trying HTTPS
    netcheck: report: udp=false v4=false icmpv4=false ... derp=0
    magicsock: endpoints changed: 73.4.118.165:45991 (portmap),
               172.17.0.1:45991 (local), 192.168.50.39:45991 (local)

— no `(stun)` candidate anywhere. That was drorb's state before this module's sibling
work: `Control.Join.derpNodeToWire` never emitted `STUNPort`, and drorb ran no Binding
server, so every client STUNned into the void at the tailscale default `3478`.

`Stun.respond` is the PROVEN Binding-server step and `Stun.respond_success_correct` is
the ∀-theorem that its reply parses, echoes the transaction id, verifies its FINGERPRINT,
and carries an XOR-MAPPED-ADDRESS that decodes back to **exactly** the request's source.
This module closes the last gap between that theorem and the deployment: it pins the
theorem's hypotheses on the bytes a real tailscale 1.98.8 `netcheck` actually sent, so
`real_netcheck_reflected` is a statement about the datagram drorb will really receive —
not about a hand-made request.

## Provenance of the capture (honest)

Captured 2026-07-25 on hbox by binding `127.0.0.1:3478` (the STUN address drorb's served
netmap pointed a client at by default, where nothing was listening) while a stock
`tailscale` 1.98.8 client — enrolled against drorb's own verified coordinator via
`scripts/run-tailnet.sh` — ran its periodic `netcheck`. The 40 datagram bytes are
transcribed verbatim below; the SOFTWARE attribute reads `"tailnode"`, which is
tailscale's own netcheck client identifying itself.

    000100142112a442 0d3bea76fe3ba81243a2541f
    8022 0008 7461696c6e6f6465        (SOFTWARE = "tailnode")
    8028 0004 e0f365c0                (FINGERPRINT)
-/
import Stun
import Hygiene

namespace StunTailscaleKat

open Stun

/-! ## §1  The captured datagram -/

/-- The 12-byte transaction id of the captured `netcheck` Binding request. -/
def realTxid : Bytes :=
  [0x0d, 0x3b, 0xea, 0x76, 0xfe, 0x3b, 0xa8, 0x12, 0x43, 0xa2, 0x54, 0x1f]

/-- ASCII `"tailnode"` — the SOFTWARE (§15.10) value tailscale's netcheck sends. -/
def softwareTailnode : Bytes :=
  [0x74, 0x61, 0x69, 0x6c, 0x6e, 0x6f, 0x64, 0x65]

/-- **The real datagram**: 40 bytes, verbatim off the wire from stock tailscale 1.98.8
netcheck, addressed at the STUN port of the DERP region drorb's coordinator served. -/
def realBindingRequest : Bytes :=
  -- type 0x0001 (Binding request), length 0x0014, magic cookie 0x2112A442
  [0x00, 0x01, 0x00, 0x14, 0x21, 0x12, 0xa4, 0x42]
  -- transaction id
  ++ realTxid
  -- SOFTWARE (0x8022), length 8, "tailnode"
  ++ [0x80, 0x22, 0x00, 0x08] ++ softwareTailnode
  -- FINGERPRINT (0x8028), length 4
  ++ [0x80, 0x28, 0x00, 0x04, 0xe0, 0xf3, 0x65, 0xc0]

theorem realBindingRequest_length : realBindingRequest.length = 40 := by decide

/-! ## §2  The proven decoder accepts it, and classifies it as a Binding request -/

/-- The real datagram parses (the magic cookie, the declared length, and every TLV
check in `Stun.parse` pass on the real bytes). -/
theorem realBindingRequest_parses : (parse realBindingRequest).isSome = true := by decide

/-- It is a **Binding request** (§6) — the message type `respond` answers. -/
theorem realBindingRequest_typ :
    (parse realBindingRequest).map (·.typ) = some bindingRequest := by decide

/-- The decoder recovers the transaction id verbatim; the reply must echo it or the
client discards the response as belonging to another transaction (§7.3.3). -/
theorem realBindingRequest_txid :
    (parse realBindingRequest).map (·.txid) = some realTxid := by decide

/-- The decoder recovers both attributes tailscale sent: SOFTWARE and FINGERPRINT. -/
theorem realBindingRequest_attrs :
    (parse realBindingRequest).map (·.attrs)
      = some [ { type := 0x8022, value := softwareTailnode }
             , { type := 0x8028, value := [0xe0, 0xf3, 0x65, 0xc0] } ] := by decide

/-- **No 420.** Both attributes tailscale sends are comprehension-OPTIONAL
(type ≥ 0x8000), so `unknownComprehensionRequired` is empty and the proven server takes
the SUCCESS branch rather than answering `420 Unknown Attribute` (§7.3.1). This is the
hypothesis that decides whether a real client gets its address back or an error. -/
theorem realBindingRequest_no_unknown :
    (parse realBindingRequest).map (fun m => unknownComprehensionRequired m.attrs)
      = some [] := by decide

/-! ## §3  ★ The headline: drorb's answer to a real netcheck probe reflects the
client's real source address

Instantiating `Stun.respond_success_correct` at the captured bytes. For **every** IPv4
source, drorb's reply to this exact datagram parses as a Binding success, echoes the
captured transaction id, carries a FINGERPRINT that verifies, and carries an
XOR-MAPPED-ADDRESS that decodes back to precisely the source the datagram came from —
which is the reflexive endpoint the client adds to its candidate set. -/
theorem real_netcheck_reflected (src : Endpoint)
    (hport : src.port < 65536) (hfam : src.family = 1) (haddr : src.addr.length = 4) :
    ∃ r mr, respond realBindingRequest src = some r ∧ parse r = some mr ∧
      mr.typ = bindingSuccessType ∧ mr.txid = realTxid ∧
      fingerprintOk r = true ∧
      ∃ a ∈ mr.attrs, a.type = attrXorMappedAddress ∧
        decodeXorMapped realTxid a.value = some src := by
  -- Name the parsed message the decoder produced on the real bytes.
  cases hm : parse realBindingRequest with
  | none =>
      exact absurd (hm ▸ realBindingRequest_parses) (by simp)
  | some m =>
      have ht : m.typ = bindingRequest := by
        have h := realBindingRequest_typ
        rw [hm] at h
        simpa using h
      have htx : m.txid = realTxid := by
        have h := realBindingRequest_txid
        rw [hm] at h
        simpa using h
      have hu : unknownComprehensionRequired m.attrs = [] := by
        have h := realBindingRequest_no_unknown
        rw [hm] at h
        simpa using h
      obtain ⟨r, mr, h1, h2, h3, h4, h5, a, ha, hat, hdec⟩ :=
        respond_success_correct realBindingRequest m src hm ht hu hport
          (Or.inl ⟨hfam, haddr⟩)
      rw [htx] at h4 hdec
      exact ⟨r, mr, h1, h2, h3, h4, h5, a, ha, hat, hdec⟩

/-! ## §4  Runtime evidence -/

#guard realBindingRequest.length == 40
#guard (parse realBindingRequest).isSome
#guard (parse realBindingRequest).map (·.typ) == some bindingRequest
#guard (parse realBindingRequest).map (fun m => unknownComprehensionRequired m.attrs) == some []
-- the reply drorb sends a client whose datagram arrived from 192.168.50.39:45992
#guard (respond realBindingRequest { family := 1, port := 45992, addr := [192, 168, 50, 39] }).isSome
#guard (do
    let r ← respond realBindingRequest { family := 1, port := 45992, addr := [192, 168, 50, 39] }
    let m ← parse r
    let a ← m.attrs.find? (fun a => a.type == attrXorMappedAddress)
    decodeXorMapped realTxid a.value)
  == some { family := 1, port := 45992, addr := [192, 168, 50, 39] }

#assert_axioms realBindingRequest_parses ⊆ [stdAxioms]
#assert_axioms realBindingRequest_typ ⊆ [stdAxioms]
#assert_axioms realBindingRequest_txid ⊆ [stdAxioms]
#assert_axioms realBindingRequest_attrs ⊆ [stdAxioms]
#assert_axioms realBindingRequest_no_unknown ⊆ [stdAxioms]
#assert_axioms real_netcheck_reflected ⊆ [stdAxioms]

end StunTailscaleKat
