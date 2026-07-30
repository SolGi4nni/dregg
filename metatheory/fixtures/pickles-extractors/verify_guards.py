#!/usr/bin/env python3
"""Evaluate every #guard in MinaWrapDeferredWeld against the Python oracle."""
import io, contextlib, copy
import phaseb, walk
from deferred import PN, ENDO, endo_map, root_of_unity, shift1

buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    D0 = phaseb.main()
o = D0["o"]
seq = list(D0["seq"])
p = PN

PUBLIC_INPUT = [
    24419304084955781347126086756851183942391470709481893428346911935138434430569,
    3704055669176394204882118867085528376297324327166010249275631280543959110076,
    28253093736872809289651234116715748339046919777164536988932734978720774588272,
    28253093736872809289651234116715748339046919777164536988932734978720774588272,
    7936731386312087149597495386614535691216588017905596433290144424125540122277,
    313463181614075351545075628406585839803,
    192135724619941679018606360956682553776,
    20020606918071128765989674557881900859,
    330389166796541696025267191640936493743,
    282268845488303208229519822093349558173,
    27860000640749903405624349274249037823232876972870997514980343477933149550480,
    16694176452625101103339288558027392732723822717830151635447913532282294450543,
    24322017899265084126163599635783679345976168424021275192497824834098868742353,
]
FT0 = D0["ft0"]

E = dict(
    spongeDigest=o["sponge_digest"],
    oldChals=[list(v) for v in o["acc_challenges"]],
    ftEval1=o["ft_eval1"],
    pubEval=list(o["pub_eval"]),
    evals=[(a[0], b[0]) for a, b in seq],
    bpChals=list(o["bp_challenges"]),
    betaChal=o["beta"], gammaChal=o["gamma"], alphaChal=o["alpha"], zetaChal=o["zeta"],
    domainLog2=o["branch_domain_log2"],
)


def bpoly(chals, x):
    k = len(chals)
    out = 1
    for i, c in enumerate(chals):
        out = out * ((1 + c * pow(x, 2 ** (k - 1 - i), p)) % p) % p
    return out


def expand(e, ft0):
    n = 2 ** e["domainLog2"]
    omega = root_of_unity(p, e["domainLog2"])
    zeta = endo_map(ENDO, e["zetaChal"], p)
    alpha = endo_map(ENDO, e["alphaChal"], p)
    zetaw = zeta * omega % p
    old = [[endo_map(ENDO, c, p) for c in v] for v in e["oldChals"]]
    cd = phaseb.hash_all([x for v in old for x in v])
    s = phaseb.Sponge()
    for x in [e["spongeDigest"], cd, e["ftEval1"], e["pubEval"][0], e["pubEval"][1]]:
        s.absorb(x)
    for a, b in e["evals"]:
        s.absorb(a); s.absorb(b)
    xi_chal = s.challenge(); r_chal = s.challenge()
    xi = endo_map(ENDO, xi_chal, p); r = endo_map(ENDO, r_chal, p)
    bp = [endo_map(ENDO, c, p) for c in e["bpChals"]]
    w = [a for a, _ in e["evals"][7:22]]
    sg = [a for a, _ in e["evals"][37:43]]
    zzw = e["evals"][0][1]
    zkp = 1
    for k in (3, 2, 1):
        zkp = zkp * ((zeta - pow(omega, n - k, p)) % p) % p
    acc = zzw * e["betaChal"] % p * pow(alpha, 21, p) % p * zkp % p
    for i in range(6):
        acc = acc * ((e["gammaChal"] + e["betaChal"] * sg[i] + w[i]) % p) % p
    perm = shift1((-acc) % p, p)
    b = shift1((bpoly(bp, zeta) + r * bpoly(bp, zetaw)) % p, p)
    zcol = [bpoly(v, zeta) for v in old] + [e["pubEval"][0], ft0] + [a for a, _ in e["evals"]]
    wcol = [bpoly(v, zetaw) for v in old] + [e["pubEval"][1], e["ftEval1"]] + \
           [b2 for _, b2 in e["evals"]]
    cip = 0
    for k in range(len(zcol)):
        cip = (cip + pow(xi, k, p) * ((zcol[k] + r * wcol[k]) % p)) % p
    return dict(cip=shift1(cip, p), b=b,
                zetaToSrsLength=shift1(pow(zeta, 2 ** 16, p), p),
                zetaToDomainSize=shift1(pow(zeta, n, p), p),
                perm=perm, xi=xi_chal)


def mut(**kw):
    e = copy.deepcopy(E)
    e.update(kw)
    return e


ok = []


def g(label, cond):
    ok.append((label, cond))
    print(("PASS " if cond else "FAIL ") + label)


D = expand(E, FT0)
g("§3 xi", D["xi"] == PUBLIC_INPUT[9])
g("§3 b", D["b"] == PUBLIC_INPUT[1])
g("§3 zts", D["zetaToSrsLength"] == PUBLIC_INPUT[2])
g("§3 ztd", D["zetaToDomainSize"] == PUBLIC_INPUT[3])
g("§3 perm", D["perm"] == PUBLIC_INPUT[4])
g("§4 cip", D["cip"] == PUBLIC_INPUT[0])

g("3b seed->xi", expand(mut(spongeDigest=E["spongeDigest"] + 1), FT0)["xi"] != PUBLIC_INPUT[9])
g("3b ft1->xi", expand(mut(ftEval1=E["ftEval1"] + 1), FT0)["xi"] != PUBLIC_INPUT[9])
oc = copy.deepcopy(E["oldChals"]); oc[0][0] = 0
g("3b oldchals->xi", expand(mut(oldChals=oc), FT0)["xi"] != PUBLIC_INPUT[9])
ev = list(E["evals"]); ev[42] = (0, 0)
g("3b evals42->xi", expand(mut(evals=ev), FT0)["xi"] != PUBLIC_INPUT[9])
ev = list(E["evals"]); ev[20] = (ev[20][0], 0)
g("3b evals20snd->xi", expand(mut(evals=ev), FT0)["xi"] != PUBLIC_INPUT[9])
g("3b zeta->zts", expand(mut(zetaChal=E["zetaChal"] + 1), FT0)["zetaToSrsLength"] != PUBLIC_INPUT[2])
g("3b dl15 zts stays", expand(mut(domainLog2=15), FT0)["zetaToSrsLength"] == PUBLIC_INPUT[2])
g("3b dl15 ztd moves", expand(mut(domainLog2=15), FT0)["zetaToDomainSize"] != PUBLIC_INPUT[3])
g("3b beta->perm", expand(mut(betaChal=E["betaChal"] + 1), FT0)["perm"] != PUBLIC_INPUT[4])
g("3b gamma->perm", expand(mut(gammaChal=E["gammaChal"] + 1), FT0)["perm"] != PUBLIC_INPUT[4])
g("3b alpha->perm", expand(mut(alphaChal=E["alphaChal"] + 1), FT0)["perm"] != PUBLIC_INPUT[4])
ev = list(E["evals"]); ev[0] = (ev[0][0], 0)
g("3b z(zw)->perm", expand(mut(evals=ev), FT0)["perm"] != PUBLIC_INPUT[4])
ev = list(E["evals"]); ev[37] = (0, 0)
g("3b s0->perm", expand(mut(evals=ev), FT0)["perm"] != PUBLIC_INPUT[4])
ev = list(E["evals"]); ev[12] = (0, 0)
g("3b w5->perm", expand(mut(evals=ev), FT0)["perm"] != PUBLIC_INPUT[4])
bc = list(E["bpChals"]); bc[0] = 0
g("3b bp0->b", expand(mut(bpChals=bc), FT0)["b"] != PUBLIC_INPUT[1])
bc = list(E["bpChals"]); bc[15] = 0
g("3b bp15->b", expand(mut(bpChals=bc), FT0)["b"] != PUBLIC_INPUT[1])
g("3b seed->b", expand(mut(spongeDigest=E["spongeDigest"] + 1), FT0)["b"] != PUBLIC_INPUT[1])

w16 = root_of_unity(p, 16)
g("3c order 2^16", pow(w16, 2 ** 16, p) == 1)
g("3c not 2^15", pow(w16, 2 ** 15, p) != 1)
g("3c ladder", w16 * w16 % p == root_of_unity(p, 15))

oc = copy.deepcopy(E["oldChals"]); oc[1][15] = 0
g("4b oldchals->cip", expand(mut(oldChals=oc), FT0)["cip"] != PUBLIC_INPUT[0])
g("4b pubeval->cip",
  expand(mut(pubEval=[E["pubEval"][0] + 1, E["pubEval"][1]]), FT0)["cip"] != PUBLIC_INPUT[0])
g("4b ft1->cip", expand(mut(ftEval1=E["ftEval1"] + 1), FT0)["cip"] != PUBLIC_INPUT[0])
ev = list(E["evals"]); ev[0] = (0, 0)
g("4b ev0->cip", expand(mut(evals=ev), FT0)["cip"] != PUBLIC_INPUT[0])
ev = list(E["evals"]); ev[42] = (0, 0)
g("4b ev42->cip", expand(mut(evals=ev), FT0)["cip"] != PUBLIC_INPUT[0])
g("4b ft0+1->cip", expand(E, FT0 + 1)["cip"] != PUBLIC_INPUT[0])

g("§5 beta@5", E["betaChal"] == PUBLIC_INPUT[5])
g("§5 gamma@6", E["gammaChal"] == PUBLIC_INPUT[6])
g("§5 alpha@7", E["alphaChal"] == PUBLIC_INPUT[7])
# WIRE_539508 projections: alpha:=slot5, beta:=slot6, gamma:=slot7
g("§5 layout mislabel",
  expand(mut(betaChal=PUBLIC_INPUT[6], gammaChal=PUBLIC_INPUT[7],
             alphaChal=PUBLIC_INPUT[5]), FT0)["perm"] != PUBLIC_INPUT[4])

print()
print("ALL PASS" if all(c for _, c in ok) else "SOME FAILED")
