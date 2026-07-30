#!/usr/bin/env python3
"""Oracle for expand_deferred on devnet block 539508, phase A (no sponge)."""
import walk

PN = 28948022309329048855892746252171976963363056481941560715954676764349967630337
QN = 28948022309329048855892746252171976963363056481941647379679742748393362948097

# Endo.Wrap_inner_curve.scalar = Vesta::endo_scalar, a Tick.Field (= Fp = PN) element.
ENDO = 8503465768106391777493614032514048814691664078728891710322960303815233784505

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
]


def bit(x, i):
    return (x >> i) & 1


def endo_map(endo, chal, p, lenbits=128):
    a, b = 2, 2
    for i in reversed(range(lenbits // 2)):
        a = (a + a) % p
        b = (b + b) % p
        s = 1 if bit(chal, 2 * i) else p - 1
        if bit(chal, 2 * i + 1) == 0:
            b = (b + s) % p
        else:
            a = (a + s) % p
    return (a * endo + b) % p


def root_of_unity(p, log2n):
    t = p - 1
    s = 0
    while t % 2 == 0:
        t //= 2
        s += 1
    return pow(pow(5, t, p), 2 ** (s - log2n), p)


def shift1(x, p):
    """Shifted_value.Type1.of_field: (x - (2^255+1)) / 2."""
    return ((x - (2 ** 255 + 1)) * pow(2, p - 2, p)) % p


def unshift1(y, p):
    return (2 * y + 2 ** 255 + 1) % p


def main():
    o = walk.main()
    p = PN
    beta = o["beta"]
    gamma = o["gamma"]
    alpha_chal = o["alpha"]
    zeta_chal = o["zeta"]
    log2n = o["branch_domain_log2"]
    n = 2 ** log2n
    srs_log2 = 16

    print("wire alpha' =", alpha_chal, " slot7 =", PUBLIC_INPUT[7],
          alpha_chal == PUBLIC_INPUT[7])
    print("wire beta   =", beta, " slot5 =", PUBLIC_INPUT[5], beta == PUBLIC_INPUT[5])
    print("wire gamma  =", gamma, " slot6 =", PUBLIC_INPUT[6], gamma == PUBLIC_INPUT[6])
    print("wire zeta'  =", zeta_chal, " slot8 =", PUBLIC_INPUT[8],
          zeta_chal == PUBLIC_INPUT[8])
    print("all prev_evals < PN:",
          all(v < PN for col in o["cols"].values() for pr in col for lst in pr for v in lst))

    zeta = endo_map(ENDO, zeta_chal, p)
    alpha = endo_map(ENDO, alpha_chal, p)
    omega = root_of_unity(p, log2n)
    zetaw = (zeta * omega) % p

    zts = shift1(pow(zeta, 2 ** srs_log2, p), p)
    ztd = shift1(pow(zeta, n, p), p)
    print("\nzeta_to_srs_length =", zts, " slot2 =", PUBLIC_INPUT[2], zts == PUBLIC_INPUT[2])
    print("zeta_to_domain_size=", ztd, " slot3 =", PUBLIC_INPUT[3], ztd == PUBLIC_INPUT[3])

    # perm
    c = o["cols"]
    w0 = [c["w"][i][0][0] for i in range(15)]
    s0 = [c["s"][i][0][0] for i in range(6)]
    z1 = c["z"][0][1][0]  # z at zeta*omega
    zkp = 1
    for k in (3, 2, 1):
        zkp = zkp * (zeta - pow(omega, n - k, p)) % p
    acc = z1 * beta % p * pow(alpha, 21, p) % p * zkp % p
    for i in range(6):
        acc = acc * ((gamma + beta * s0[i] + w0[i]) % p) % p
    perm = shift1((-acc) % p, p)
    print("perm               =", perm, " slot4 =", PUBLIC_INPUT[4], perm == PUBLIC_INPUT[4])

    return dict(o=o, zeta=zeta, alpha=alpha, omega=omega, zetaw=zetaw, n=n, beta=beta,
                gamma=gamma)


if __name__ == "__main__":
    main()
