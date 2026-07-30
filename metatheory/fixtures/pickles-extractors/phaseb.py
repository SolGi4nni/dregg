#!/usr/bin/env python3
"""Phase B: the Fr-sponge, xi, r, b, and combined_inner_product on block 539508."""
import os
import re
import walk
from deferred import (PN, ENDO, PUBLIC_INPUT, endo_map, root_of_unity, shift1, unshift1)

# ⚑ The Poseidon constants are read from the LEAN file, not copied: there must not be a second
# copy of `fp_kimchi` in this tree that can drift from the one the archive runs.
LEAN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                    "Dregg2", "Circuit", "Emit", "PastaPoseidon.lean")


def _grab(name):
    src = open(LEAN).read()
    i = src.index("def " + name + " : List (List Nat) :=")
    body = src[i:src.index("\n\n", i)]
    return [[int(x.strip()) for x in r.split(",")]
            for r in re.findall(r"\[([^\[\]]+)\]", body)]


MDS = _grab("mdsN")
RCS = _grab("rcsN")
assert len(MDS) == 3 and len(RCS) == 55
p = PN


def perm(st):
    for rc in RCS:
        sb = [pow(x, 7, p) for x in st]
        st = [(MDS[j][0] * sb[0] + MDS[j][1] * sb[1] + MDS[j][2] * sb[2] + rc[j]) % p
              for j in range(3)]
    return st


class Sponge:
    def __init__(self):
        self.st = [0, 0, 0]
        self.mode = ("A", 0)

    def absorb(self, x):
        k, n = self.mode
        if k == "A":
            if n == 2:
                self.st = perm(self.st)
                self.st[0] = (self.st[0] + x) % p
                self.mode = ("A", 1)
            else:
                self.st[n] = (self.st[n] + x) % p
                self.mode = ("A", n + 1)
        else:
            self.st[0] = (self.st[0] + x) % p
            self.mode = ("A", 1)

    def squeeze(self):
        k, n = self.mode
        if k == "S" and n != 2:
            self.mode = ("S", n + 1)
            return self.st[n]
        self.st = perm(self.st)
        self.mode = ("S", 1)
        return self.st[0]

    def challenge(self):
        return self.squeeze() % 2 ** 128


def hash_all(xs):
    s = Sponge()
    for x in xs:
        s.absorb(x)
    return s.squeeze()


def bpoly(chals, x):
    """challenge_polynomial: prod_i (1 + c_i * x^(2^(k-1-i)))."""
    k = len(chals)
    out = 1
    for i, c in enumerate(chals):
        out = out * ((1 + c * pow(x, 2 ** (k - 1 - i), p)) % p) % p
    return out


def main():
    o = walk.main()
    c = o["cols"]
    beta, gamma = o["beta"], o["gamma"]
    zeta = endo_map(ENDO, o["zeta"], p)
    alpha = endo_map(ENDO, o["alpha"], p)
    log2n = o["branch_domain_log2"]
    n = 2 ** log2n
    omega = root_of_unity(p, log2n)
    zetaw = zeta * omega % p

    # ── challenges_digest: a FRESH Fp sponge over the endo-lifted old bp challenges
    old_chals = [[endo_map(ENDO, ch, p) for ch in v] for v in o["acc_challenges"]]
    chal_digest = hash_all([x for v in old_chals for x in v])

    # ── the Fr sponge for the deferred values
    s = Sponge()
    s.absorb(o["sponge_digest"])
    s.absorb(chal_digest)
    s.absorb(o["ft_eval1"])
    s.absorb(o["pub_eval"][0])
    s.absorb(o["pub_eval"][1])
    # to_absorption_sequence order: z, 6 selectors, w(15), coefficients(15), s(6)
    seq = c["z"] + c["selectors"] + c["w"] + c["coefficients"] + c["s"]
    assert len(seq) == 43
    for a, b in seq:
        for x in a:
            s.absorb(x)
        for x in b:
            s.absorb(x)
    xi_chal = s.challenge()
    r_chal = s.challenge()
    xi = endo_map(ENDO, xi_chal, p)
    r = endo_map(ENDO, r_chal, p)
    print("xi_chal =", xi_chal, " slot9 =", PUBLIC_INPUT[9], xi_chal == PUBLIC_INPUT[9])

    # ── b
    bp = [endo_map(ENDO, ch, p) for ch in o["bp_challenges"]]
    b_actual = (bpoly(bp, zeta) + r * bpoly(bp, zetaw)) % p
    b_sh = shift1(b_actual, p)
    print("b       =", b_sh, " slot1 =", PUBLIC_INPUT[1], b_sh == PUBLIC_INPUT[1])

    # ── combined_inner_product, given ft_eval0
    # order: bpoly_0(pt), bpoly_1(pt), public(pt), ft, then to_absorption_sequence
    def col(idx, ft0, ft1):
        z_col = [bpoly(v, zeta) for v in old_chals] + [o["pub_eval"][0], ft0] + \
                [a[0] for a, _ in seq]
        w_col = [bpoly(v, zetaw) for v in old_chals] + [o["pub_eval"][1], ft1] + \
                [b[0] for _, b in seq]
        return z_col, w_col

    cip_target = unshift1(PUBLIC_INPUT[0], p)
    # cip = sum_k xi^k (z_k + r * w_k); solve for ft_eval0 (index 3)
    z_col, w_col = col(0, 0, o["ft_eval1"])
    acc = 0
    for k in range(len(z_col)):
        acc = (acc + pow(xi, k, p) * ((z_col[k] + r * w_col[k]) % p)) % p
    # the ft_eval0 slot (k = 3) currently contributes 0 in the zeta column
    ft0 = (cip_target - acc) % p * pow(pow(xi, 3, p), p - 2, p) % p
    print("implied ft_eval0 =", ft0)
    # recompute forward with that ft0 and confirm
    z_col, w_col = col(0, ft0, o["ft_eval1"])
    acc = 0
    for k in range(len(z_col)):
        acc = (acc + pow(xi, k, p) * ((z_col[k] + r * w_col[k]) % p)) % p
    print("cip     =", shift1(acc, p), " slot0 =", PUBLIC_INPUT[0],
          shift1(acc, p) == PUBLIC_INPUT[0], " (ft_eval0 solved, not derived)")
    print("n polys =", len(z_col))
    return dict(xi_chal=xi_chal, xi=xi, r_chal=r_chal, r=r, chal_digest=chal_digest,
                ft0=ft0, zeta=zeta, alpha=alpha, omega=omega, zetaw=zetaw, o=o, seq=seq,
                old_chals=old_chals, bp=bp, n=n)


if __name__ == "__main__":
    main()
