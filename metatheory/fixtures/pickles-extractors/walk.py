#!/usr/bin/env python3
"""Re-walk of bridge/src/mina_pickles.rs::decode_proof_at, in Python, to EXTRACT the
fields that walk discards. Validated against values already pinned in the Lean tree.
"""
import base64, json, sys

BLOCK = "/Users/ember/dev/breadstuffs/metatheory/fixtures/pickles-extractors/mina_devnet_block.json"

PN = 28948022309329048855892746252171976963363056481941560715954676764349967630337  # Pallas base
QN = 28948022309329048855892746252171976963363056481941647379679742748393362948097  # Pallas scalar


class R:
    def __init__(self, b):
        self.b = b
        self.i = 0

    def take(self, n):
        if self.i + n > len(self.b):
            raise ValueError(f"eof at {self.i} want {n}")
        v = self.b[self.i:self.i + n]
        self.i += n
        return v

    def u8(self):
        return self.take(1)[0]

    def nat0(self):
        c = self.u8()
        if c <= 0x7f:
            return c
        if c == 0xfe:
            return int.from_bytes(self.take(2), "little")
        if c == 0xfd:
            return int.from_bytes(self.take(4), "little")
        if c == 0xfc:
            return int.from_bytes(self.take(8), "little")
        raise ValueError(f"nat0 code {c:02x} at {self.i}")

    def int_(self):
        c = self.u8()
        if c <= 0x7f:
            return c
        if c == 0xff:
            return int.from_bytes(self.take(1), "little", signed=True)
        if c == 0xfe:
            return int.from_bytes(self.take(2), "little", signed=True)
        if c == 0xfd:
            return int.from_bytes(self.take(4), "little", signed=True)
        if c == 0xfc:
            return int.from_bytes(self.take(8), "little", signed=True)
        raise ValueError(f"int code {c:02x} at {self.i}")

    def unit(self):
        v = self.u8()
        assert v == 0, f"unit {v:02x} at {self.i-1}"

    def bool_(self):
        v = self.u8()
        assert v in (0, 1)
        return v == 1

    def field(self, mod, what=""):
        le = self.take(32)
        x = int.from_bytes(le, "little")
        assert x < mod, f"{what}: non-canonical at {self.i-32}"
        return x

    def point(self, mod, what=""):
        return (self.field(mod, what), self.field(mod, what))

    def pseq(self, n, f):
        out = [f(self) for _ in range(n)]
        self.unit()
        return out

    def opt(self, f):
        t = self.u8()
        if t == 0:
            return None
        assert t == 1, f"opt tag {t:02x} at {self.i-1}"
        return f(self)

    def arrayn(self, cap, f):
        n = self.nat0()
        assert n <= cap, f"arrayn {n} > {cap}"
        return [f(self) for _ in range(n)]


def challenge_v(r):
    limbs = r.pseq(2, lambda r: r.int_())
    return (limbs[0] & 0xFFFFFFFFFFFFFFFF) | ((limbs[1] & 0xFFFFFFFFFFFFFFFF) << 64)


def main():
    d = json.load(open(BLOCK))
    b64 = d["protocol_state_proof_base64_urlsafe"]
    raw = base64.urlsafe_b64decode(b64 + "=" * (-len(b64) % 4))
    r = R(raw)
    out = {}

    # ── statement.proof_state.deferred_values.plonk ───────────────────────────
    out["alpha"] = challenge_v(r)
    out["beta"] = challenge_v(r)
    out["gamma"] = challenge_v(r)
    out["zeta"] = challenge_v(r)
    assert r.opt(challenge_v) is None, "joint_combiner is Some"
    for _ in range(8):
        assert not r.bool_(), "a feature flag is set"
    out["bp_challenges"] = r.pseq(16, challenge_v)
    out["branch_proofs_verified"] = r.u8()
    out["branch_domain_log2"] = r.u8()

    # ── statement.proof_state (rest) ──────────────────────────────────────────
    limbs = r.pseq(4, lambda r: r.int_())
    out["sponge_digest"] = sum(
        (limbs[k] & 0xFFFFFFFFFFFFFFFF) << (64 * k) for k in range(4))
    out["mnw_comm"] = r.point(QN, "mnw_comm")
    out["mnw_challenges"] = [r.pseq(15, challenge_v) for _ in range(2)]
    r.unit()  # outer PaddedSeq<_,2> terminator

    # ── statement.messages_for_next_step_proof ────────────────────────────────
    r.unit()  # app_state : ()
    n = r.nat0()
    assert n <= 2
    out["acc_comm"] = [r.point(PN, "acc_comm") for _ in range(n)]
    n2 = r.nat0()
    assert n2 <= 2
    out["acc_challenges"] = [r.pseq(16, challenge_v) for _ in range(n2)]

    # ── prev_evals ────────────────────────────────────────────────────────────
    # In the Wrap proof, the previous (STEP) proof's evaluations. The Rust walk
    # checks them against the Pallas SCALAR modulus.
    def ev(r):
        a = r.arrayn(16, lambda r: r.field(QN, "prev_evals"))
        b = r.arrayn(16, lambda r: r.field(QN, "prev_evals"))
        return (a, b)

    out["pub_eval"] = (r.field(QN, "pi0"), r.field(QN, "pi1"))
    cols = {}
    cols["w"] = r.pseq(15, ev)
    cols["coefficients"] = r.pseq(15, ev)
    cols["z"] = [ev(r)]
    cols["s"] = r.pseq(6, ev)
    cols["selectors"] = [ev(r) for _ in range(6)]
    for _ in range(8):
        assert r.opt(ev) is None, "optional lookup/ff eval present"
    r.pseq(5, lambda r: r.opt(ev))
    for _ in range(5):
        assert r.opt(ev) is None
    assert r.opt(ev) is None
    out["cols"] = cols
    out["ft_eval1"] = r.field(QN, "ft_eval1")

    # ── proof: Pickles__Wrap_wire_proof.Stable.V1 ─────────────────────────────
    out["w_comm"] = [r.point(PN, "w_comm") for _ in range(15)]
    r.unit()
    out["z_comm"] = r.point(PN, "z_comm")
    out["t_comm"] = [r.point(PN, "t_comm") for _ in range(7)]
    r.unit()
    # the WRAP proof's own evaluations: (ζ, ζω) scalar pairs
    sp = lambda r: (r.field(QN, "ev"), r.field(QN, "ev"))
    wev = {}
    wev["w"] = r.pseq(15, sp)
    wev["coefficients"] = r.pseq(15, sp)
    wev["z"] = [sp(r)]
    wev["s"] = r.pseq(6, sp)
    wev["selectors"] = [sp(r) for _ in range(6)]
    out["wrap_evals"] = wev
    out["wrap_ft_eval1"] = r.field(QN, "ft_eval1")
    n = r.nat0()
    assert n <= 16
    out["lr"] = [(r.point(PN, "L"), r.point(PN, "R")) for _ in range(n)]
    out["z_1"] = r.field(QN, "z_1")
    out["z_2"] = r.field(QN, "z_2")
    out["delta"] = r.point(PN, "delta")
    out["sg"] = r.point(PN, "sg")
    out["_tail"] = len(raw) - r.i
    return out


if __name__ == "__main__":
    o = main()
    print("TAIL BYTES LEFT:", o["_tail"])
    print("alpha ", o["alpha"])
    print("beta  ", o["beta"])
    print("gamma ", o["gamma"])
    print("zeta  ", o["zeta"])
    print("sponge", o["sponge_digest"])
    print("branch", o["branch_proofs_verified"], o["branch_domain_log2"])
    print("bpchal", o["bp_challenges"][:2], "...", o["bp_challenges"][-1])
    print("acc_ch", len(o["acc_challenges"]), [len(v) for v in o["acc_challenges"]])
    print("ft1   ", o["ft_eval1"])
    print("pubev ", o["pub_eval"])
    for k, v in o["cols"].items():
        print("col", k, len(v), "chunk lens", sorted({(len(a), len(b)) for a, b in v}))
