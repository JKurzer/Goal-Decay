"""simulate3.py - Gen-2 failure threshold scan + hierarchy table.

Companion to simulate.py / simulate2.py (both left untouched). Pure stdlib.
Run:  python simulate3.py

E = 0.091, q = 1 - E = 0.909, I0 = 1.

Sections
--------
1a. Constant coupling k:  I(g+1) = q * I(g)^(k+1), I0 = 1  ->  I(2) = q^(k+2).
    Print I(2) for k = 1..10; smallest k with I(2) < 0.5.
1b. Factorial stack:  I(g+1) = q * I(g)^m(g), m(i) = i + 2.
    Closed form I(g) = I0^P(g) * q^R(g) with
    P(0) = 1, P(g+1) = m(g)*P(g);  R(0) = 0, R(g+1) = m(g)*R(g) + 1.
    Verify P(g) == (g+1)! for g = 0..8; print I(g) for g = 0..6 and the
    first g with I(g) < 0.5, < 0.05, < 1e-6.
1c. Gen-1 stack-depth scan: m(0) = 2, m(1) in {2..12}, m(2) = m(1) + 1
    -> I(2) = q^(m(1)+1). Smallest m(1) with I(2) < 0.5; I(3) per m(1).
2.  Brute-force check: I(3), I(4) direct recurrence vs closed form.
3.  Hierarchy table at g = 10: log10(integrity) for
    (i) no-feedback q^g, (ii) k=1 q^(2^g - 1), (iii) k=6 q^((7^g-1)/6),
    (iv) factorial stack q^R(g).
4.  Raw dump to results3.csv.

CSV layout (long format, mirrors results2.csv):
  section, param, g, value, reference, note
  const_k    : param=k, g=2, value=I(2) by recurrence, reference=q^(k+2)
  factorial  : value=I(g) by recurrence, reference=I0^P(g)*q^R(g) closed form
  gen1_scan  : param=m(1), g in {2,3}, value=I(g), reference=q^exponent
  brute_check: value=direct recurrence I(g), reference=closed form
  hierarchy  : g=10, value=log10(integrity), reference=exact integer exponent
"""

import csv
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
E = 0.091
Q = 1.0 - E                     # 0.909
I0 = 1.0
K_SCAN = range(1, 11)           # section 1a: k = 1..10
M1_SCAN = range(2, 13)          # section 1c: m(1) in {2..12}
THRESHOLDS = (0.5, 0.05, 1e-6)  # section 1b
G_PRINT = 6                     # section 1b prints g = 0..6
G_CHECK = 8                     # P(g) == (g+1)! verified for g = 0..8
G_HIER = 10                     # section 3 horizon
PASS_TOL = 1e-12                # float-dust budget (same as simulate2.py)
CSV_PATH = os.path.join(HERE, "results3.csv")


def m_factorial(g):
    """Growing-model stack depth schedule: m(i) = i + 2."""
    return g + 2


def m_scan(m1):
    """Section 1c schedule: m(0) = 2, m(1) = m1, m(2) = m1 + 1."""
    def m(g):
        return (2, m1, m1 + 1)[g]
    return m


def run_recurrence(m, gens):
    """Direct recurrence I(g+1) = q * I(g)**m(g). Returns [I(0)..I(gens)]."""
    values = [I0]
    for g in range(gens):
        values.append(Q * values[-1] ** m(g))
    return values


def closed_form(m, gens):
    """I(g) = I0^P(g) * q^R(g); P(0)=1, P(g+1)=m(g)P(g); R(0)=0, R(g+1)=m(g)R(g)+1.

    Returns (values, P, R) lists over g = 0..gens. P and R are exact ints.
    """
    p, r = 1, 0
    values, ps, rs = [], [], []
    for g in range(gens + 1):
        values.append(I0 ** p * Q ** r)
        ps.append(p)
        rs.append(r)
        p, r = m(g) * p, m(g) * r + 1
    return values, ps, rs


def first_crossing(values, threshold):
    """First index g with values[g] < threshold, else None."""
    for g, v in enumerate(values):
        if v < threshold:
            return g
    return None


def section_1a(rows):
    print("=" * 66)
    print(f"1a. CONSTANT COUPLING k:  I(g+1) = q*I(g)^(k+1)   E={E}, q={Q}, I0={I0:g}")
    print("    with I0 = 1:  I(1) = q, so I(2) = q^(k+2) exactly")
    print("=" * 66)
    header = f"{'k':>3} | {'k+2':>4} | {'I(2) = q^(k+2)':>22} | vs 0.5"
    print(header)
    print("-" * len(header))
    smallest, dust = None, 0.0
    for k in K_SCAN:
        i2 = Q * (Q * I0 ** (k + 1)) ** (k + 1)       # two recurrence steps
        dust = max(dust, abs(i2 - Q ** (k + 2)))
        status = "FAIL < 0.5" if i2 < 0.5 else "pass"
        if i2 < 0.5 and smallest is None:
            smallest = k
        print(f"{k:>3} | {k + 2:>4} | {i2!r:>22} | {status}")
        rows.append(("const_k", k, 2, repr(i2), repr(Q ** (k + 2)), status))
    print(f"recurrence vs q^(k+2): max |diff| = {dust:.3e} (float dust)")
    print(f"-> smallest k with I(2) < 0.5: k = {smallest}"
          f"   [predicted k=6: q^8 ~ 0.466 fails; k=5: q^7 ~ 0.513 passes]")


def section_1b(rows):
    print("\n" + "=" * 66)
    print(f"1b. FACTORIAL STACK:  I(g+1) = q*I(g)^m(g), m(i)=i+2   q={Q}, I0={I0:g}")
    print("    closed form I(g) = I0^P(g) * q^R(g); P(0)=1, P(g+1)=m(g)P(g);")
    print("                                         R(0)=0, R(g+1)=m(g)R(g)+1")
    print("=" * 66)
    direct = run_recurrence(m_factorial, G_CHECK)
    closed, ps, rs = closed_form(m_factorial, G_CHECK)
    p_ok = all(ps[g] == math.factorial(g + 1) for g in range(G_CHECK + 1))
    print(f"verify P(g) == (g+1)! for g = 0..{G_CHECK}: "
          f"{'PASS' if p_ok else 'FAIL'}")
    crossings = {t: first_crossing(direct, t) for t in THRESHOLDS}
    header = (f"{'g':>3} | {'P(g)=(g+1)!':>11} | {'R(g)':>6} | "
              f"{'I(g)':>13} | {'log10 I(g)':>11}")
    print(header)
    print("-" * len(header))
    log10q = math.log10(Q)
    for g in range(G_PRINT + 1):
        lg = rs[g] * log10q + 0.0  # I0 = 1 -> P(g) term vanishes; +0.0 kills -0.0
        note = "; ".join(f"first I<{t:g}" for t in THRESHOLDS if crossings[t] == g)
        print(f"{g:>3} | {ps[g]:>11} | {rs[g]:>6} | {direct[g]:>13.6e} | "
              f"{lg:>11.6f}" + (f"   <- {note}" if note else ""))
        rows.append(("factorial", "m=i+2", g, repr(direct[g]), repr(closed[g]), note))
    for t in THRESHOLDS:
        g = crossings[t]
        print(f"first g with I(g) < {t:g}: g = {g}   (I({g}) = {direct[g]:.6e})")
    print(f"prediction check: I(2) = q^4  = {direct[2]:.6f} (~0.683), "
          f"I(3) = q^17 = {direct[3]:.6f} (~0.198),")
    print(f"                  I(4) = q^86 = {direct[4]:.6e} (~2.7e-4)")


def section_1c(rows):
    print("\n" + "=" * 66)
    print("1c. STACK-DEPTH-AT-GEN-1 SCAN: m(0)=2, m(1) in {2..12}, m(2)=m(1)+1")
    print(f"    -> I(2) = q^(m(1)+1) exactly, I(3) = q^(1+(m(1)+1)^2)   q={Q}, I0={I0:g}")
    print("=" * 66)
    header = (f"{'m(1)':>5} | {'m(2)':>5} | {'I(2)':>11} | {'log10':>9} | "
              f"{'I(3)':>13} | {'log10':>9} | vs 0.5")
    print(header)
    print("-" * len(header))
    smallest, dust = None, 0.0
    for m1 in M1_SCAN:
        m = m_scan(m1)
        i2 = run_recurrence(m, 2)[2]
        i3 = run_recurrence(m, 3)[3]
        dust = max(dust, abs(i2 - Q ** (m1 + 1)))
        status = "FAIL < 0.5" if i2 < 0.5 else "pass"
        if i2 < 0.5 and smallest is None:
            smallest = m1
        print(f"{m1:>5} | {m1 + 1:>5} | {i2:>11.6f} | {math.log10(i2):>9.4f} | "
              f"{i3:>13.6e} | {math.log10(i3):>9.4f} | {status}")
        note = "smallest m(1) with I(2)<0.5" if m1 == smallest else ""
        rows.append(("gen1_scan", m1, 2, repr(i2), repr(Q ** (m1 + 1)),
                     f"{status}; {note}".rstrip("; ")))
        rows.append(("gen1_scan", m1, 3, repr(i3),
                     repr(Q ** (1 + (m1 + 1) ** 2)), ""))
    print(f"recurrence vs q^(m(1)+1): max |diff| = {dust:.3e} (float dust)")
    print(f"-> smallest m(1) with I(2) < 0.5: m(1) = {smallest}   [predicted 7]")


def section_2(rows):
    print("\n" + "=" * 66)
    print("2. BRUTE-FORCE CHECK: direct recurrence vs closed form (factorial stack)")
    print("=" * 66)
    direct = run_recurrence(m_factorial, 4)
    closed, _, rs = closed_form(m_factorial, 4)
    for g in (3, 4):
        d, c = direct[g], closed[g]
        adiff = abs(d - c)
        rdiff = adiff / c if c else 0.0
        ok = "AGREE" if rdiff <= PASS_TOL else "MISMATCH"
        print(f"  I({g}): direct = {d:.15e}")
        print(f"       closed = {c:.15e}   (= q^{rs[g]} since I0=1)")
        print(f"       |diff| = {adiff:.3e}, rel = {rdiff:.3e}  "
              f"[{ok}, tol {PASS_TOL:g}]")
        rows.append(("brute_check", "m=i+2", g, repr(d), repr(c),
                     f"rel_diff={rdiff:.3e}"))


def section_3(rows):
    print("\n" + "=" * 66)
    print(f"3. HIERARCHY TABLE at g = {G_HIER}, E = {E}: log10(integrity)")
    print("   (more negative = faster goal-content decay)")
    print("=" * 66)
    g = G_HIER
    log10q = math.log10(Q)
    _, _, rs = closed_form(m_factorial, g)
    models = [
        ("(i)   no-feedback q^g", g),
        ("(ii)  k=1: q^(2^g - 1)", 2 ** g - 1),
        ("(iii) k=6: q^((7^g-1)/6)", (7 ** g - 1) // 6),
        ("(iv)  factorial stack q^R(g)", rs[g]),
    ]
    header = f"{'model':<30} | {'exponent of q':>13} | {'log10 I':>14} | I (float)"
    print(header)
    print("-" * len(header))
    for name, expo in models:
        lg = expo * log10q
        val = Q ** expo           # underflows to 0.0 for the huge exponents
        val_s = f"{val:.3e}" if val > 0.0 else "0.0 (underflow)"
        print(f"{name:<30} | {expo:>13} | {lg:>14.6f} | {val_s}")
        note = "value=log10(integrity)"
        if val == 0.0:
            note += "; I underflows double, log10 is exact integer arithmetic"
        rows.append(("hierarchy", name.strip(), g, f"{lg:.6f}", expo, note))
    _, _, rs_big = closed_form(m_factorial, 30)
    cross = next(g0 for g0 in range(1, 31) if rs_big[g0] > (7 ** g0 - 1) // 6)
    print(f"note: at g={g} the k=6 exponent (7^g-1)/6 exceeds factorial R(g),")
    print(f"      but R(g) ~ (e-2)*(g+1)! overtakes (7^g-1)/6 at g = {cross} "
          f"and never looks back.")


def write_csv(rows):
    with open(CSV_PATH, "w", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow(["section", "param", "g", "value", "reference", "note"])
        writer.writerows(rows)
    return len(rows)


def main():
    rows = []
    section_1a(rows)
    section_1b(rows)
    section_1c(rows)
    section_2(rows)
    section_3(rows)
    print()
    n = write_csv(rows)
    print(f"raw data: {n} rows -> {CSV_PATH}")


if __name__ == "__main__":
    main()
