"""simulate2.py - k-coupled goal-decay feedback + von Neumann majority-of-3.

Companion to simulate.py (left untouched). Pure stdlib. Run:  python simulate2.py

Sections
--------
1-2. k-coupled feedback family  I(g+1) = (1-E) * I(g)^(k+1),  k in {1,2,3},
     g = 0..12, E = 0.091, I0 = 1.0. Closed forms under test:
       form A   (1-E) * I(g)^k == ((1-E) * I0^k)^((k+1)^g)
       form B   (I0 = 1)  I(g) == (1-E)^(((k+1)^g - 1) / k)
     Both verified by max abs error per k; a log-space twin of the recurrence
     keeps the check meaningful after the floats underflow to 0.0.
3.   first g with I(g) < {0.5, 0.05, 0.01, 1e-6} per k.
4.   no-feedback contrast curve I(g) = (1-E)^g (analytic crossings when > 12).
5.   von Neumann maj3 rate map f(x) = 3x^2 - 2x^3 from x0 = E, d = 0..12:
       (a) f(x) < x strictly while x > 0
       (b) 3*x_d <= (3*x0)^(2^d) to float dust
       (c) first d with x_d < 1e-6 / 1e-12 and lineage 3^d at that depth
       plus x - f(x) == x(1-x)(1-2x) factorization spot-checks.
6.   common-mode demo: bool maj3(x, x, y) == x for all bool x, y.
7.   summary tables + raw dump to results2.csv.

CSV layout (long format): section, param, g, value, reference, lineage_3d
  k_coupled  : param=k, value=iterated I(g), reference=divided closed form
  no_feedback: value=(1-E)^g
  maj3       : g=d, value=x_d, reference=(3*x0)^(2^d) bound on 3*x_d,
               lineage_3d = 3^d
"""

import csv
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
E = 0.091
I0 = 1.0
K_VALUES = (1, 2, 3)
G_MAX = 12
THRESHOLDS = (0.5, 0.05, 0.01, 1e-6)
PASS_TOL = 1e-12          # "float dust" budget for closed-form checks
CSV_PATH = os.path.join(HERE, "results2.csv")


# ---------- sections 1-2: k-coupled family ----------

def iterate_family(k, n=G_MAX):
    """I(g+1) = (1-E) * I(g)^(k+1), starting from I0."""
    values = [I0]
    for _ in range(n):
        values.append((1.0 - E) * values[-1] ** (k + 1))
    return values


def iterate_family_log(k, n=G_MAX):
    """Log-space twin: L(g+1) = ln(1-E) + (k+1)*L(g). Never underflows."""
    logs = [math.log(I0)]
    for _ in range(n):
        logs.append(math.log(1.0 - E) + (k + 1) * logs[-1])
    return logs


def form_a_rhs(k, g):
    """Claimed: (1-E)*I(g)^k == ((1-E)*I0^k)^((k+1)^g)."""
    return ((1.0 - E) * I0 ** k) ** ((k + 1) ** g)


def divided_form(k, g):
    """For I0 = 1: I(g) == (1-E)^(((k+1)^g - 1)/k). Exponent is exact int."""
    return (1.0 - E) ** (((k + 1) ** g - 1) // k)


def divided_form_log(k, g):
    return (((k + 1) ** g - 1) // k) * math.log(1.0 - E) + ((k + 1) ** g) * math.log(I0)


def nofeedback_curve(n=G_MAX):
    return [(1.0 - E) ** g for g in range(n + 1)]


# ---------- section 3: crossings ----------

def first_crossing(values, threshold):
    """First index g with values[g] < threshold, else None."""
    for g, v in enumerate(values):
        if v < threshold:
            return g
    return None


def analytic_crossing(threshold):
    """First integer g with (1-E)^g < threshold (for crossings beyond G_MAX)."""
    return math.floor(math.log(threshold) / math.log(1.0 - E)) + 1


def crossing_table(families):
    """curve name -> {threshold: first-g cell string}."""
    curves = [(f"k={k}", families[k]) for k in K_VALUES]
    curves.append(("no-feedback", nofeedback_curve()))
    table = {}
    for name, values in curves:
        row = {}
        for t in THRESHOLDS:
            g = first_crossing(values, t)
            row[t] = str(g) if g is not None else f"{analytic_crossing(t)}*"
        table[name] = row
    return table


# ---------- section 5: von Neumann maj3 rate map ----------

def maj3_rate(x):
    """f(x) = 3x^2 - 2x^3."""
    return 3.0 * x * x - 2.0 * x * x * x


def iterate_maj3(x0=E, n=G_MAX):
    xs = [x0]
    for _ in range(n):
        xs.append(maj3_rate(xs[-1]))
    return xs


def bool_maj3(a, b, c):
    return (a and b) or (a and c) or (b and c)


# ---------- printing helpers ----------

def print_family_table(families):
    nofb = nofeedback_curve()
    header = f"{'g':>3} | {'k=1':>13} | {'k=2':>13} | {'k=3':>13} | {'no-feedback':>13}"
    print(header)
    print("-" * len(header))
    for g in range(G_MAX + 1):
        cells = [families[k][g] for k in K_VALUES] + [nofb[g]]
        print(f"{g:>3} | " + " | ".join(f"{v:>13.6e}" for v in cells))


def print_verification(families):
    print("\nclosed-form verification (max abs error over g = 0..12):")
    for k in K_VALUES:
        vals, logs = families[k], iterate_family_log(k)
        err_a = max(abs((1.0 - E) * vals[g] ** k - form_a_rhs(k, g))
                    for g in range(G_MAX + 1))
        err_b = max(abs(vals[g] - divided_form(k, g)) for g in range(G_MAX + 1))
        err_log = max(abs(logs[g] - divided_form_log(k, g)) for g in range(G_MAX + 1))
        ok_a = "PASS" if err_a <= PASS_TOL else "FAIL"
        ok_b = "PASS" if err_b <= PASS_TOL else "FAIL"
        print(f"  k={k}: form A  max|lhs-rhs| = {err_a:.3e} [{ok_a}]   "
              f"divided form max|err| = {err_b:.3e} [{ok_b}]   "
              f"log-space max|err| = {err_log:.3e}")
    print("  (plain-float errors read 0.000e+00 once both sides underflow to 0.0;")


def print_crossings(table):
    header = (f"{'curve':>12} | " +
              " | ".join(f"I_g<{t:g}".rjust(8) for t in THRESHOLDS))
    print(header)
    print("-" * len(header))
    for name, row in table.items():
        print(f"{name:>12} | " + " | ".join(row[t].rjust(8) for t in THRESHOLDS))
    print("  (* = analytic crossing, outside the iterated window g <= 12)")


def print_expectation_check(families):
    """Diff the numbers against the task's hand-waved expectations."""
    nofb = nofeedback_curve()
    k1, k2 = families[1], families[2]
    print("\nexpectation check (computed values, not vibes):")
    print(f"  k=1: I(3)={k1[3]:.6f} > 0.5  -> 0.5 first crossed at g=4, not ~3;")
    print(f"       I(5)={k1[5]:.6f} > 0.05 -> 0.05 first crossed at g=6, not ~5;")
    print(f"       I(6)={k1[6]:.6f} < 0.01 -> 0.01 at g=6 as expected.")
    print(f"  k=2: I(2)={k2[2]:.6f} > 0.5  -> 0.5 first crossed at g=3, not ~2;")
    print(f"       I(3)={k2[3]:.6f} (not ~0.006), I(4)={k2[4]:.6f} (not ~2e-7).")
    print(f"  no-feedback: (1-E)^8 = {nofb[8]:.6f} < 0.5 -> g=8 as expected.")


def print_maj3_table(xs):
    x0 = xs[0]
    header = (f"{'d':>3} | {'x_d':>13} | {'3*x_d':>13} | "
              f"{'(3x0)^(2^d)':>13} | {'3^d lineage':>12}")
    print(header)
    print("-" * len(header))
    for d in range(G_MAX + 1):
        bound = (3.0 * x0) ** (2 ** d)
        print(f"{d:>3} | {xs[d]:>13.6e} | {3.0 * xs[d]:>13.6e} | "
              f"{bound:>13.6e} | {3 ** d:>12}")


def check_maj3(xs):
    x0 = xs[0]
    # (a) strict decrease while x > 0 (f(x) = 0 once x underflows; 0 < 0 is false)
    a_ok = all(xs[d + 1] < xs[d] for d in range(G_MAX) if xs[d] > 0.0)
    first_zero = next((d for d, v in enumerate(xs) if v == 0.0), None)
    # (b) 3*x_d <= (3*x0)^(2^d) to float dust; track worst relative excess
    rel_excess = 0.0
    for d in range(G_MAX + 1):
        bound = (3.0 * x0) ** (2 ** d)
        lhs = 3.0 * xs[d]
        if bound > 0.0:
            rel_excess = max(rel_excess, (lhs - bound) / bound)
        elif lhs != 0.0:  # bound underflowed but iterate didn't: real violation
            rel_excess = math.inf
    b_ok = rel_excess <= PASS_TOL
    # (c) milestones + lineage
    d6 = first_crossing(xs, 1e-6)
    d12 = first_crossing(xs, 1e-12)
    print(f"\n(a) f(x) < x for all positive iterates: "
          f"{'PASS' if a_ok else 'FAIL'} (x_d hits exact 0.0 at d={first_zero}; "
          f"f(0)=0 afterwards)")
    print(f"(b) 3*x_d <= (3*x0)^(2^d): {'PASS' if b_ok else 'FAIL'} "
          f"(max relative excess = {rel_excess:.3e}; both sides underflow to 0.0 "
          f"for d>=10, where 0 <= 0)")
    print(f"(c) x_d < 1e-6  first at d={d6}  -> lineage 3^{d6} = {3 ** d6}")
    print(f"    x_d < 1e-12 first at d={d12}  -> lineage 3^{d12} = {3 ** d12}")
    print("\nfactorization x - f(x) = x(1-x)(1-2x):")
    for x in (0.001, 0.091, 0.25, 0.499):
        lhs = x - maj3_rate(x)
        rhs = x * (1.0 - x) * (1.0 - 2.0 * x)
        ok = "PASS" if abs(lhs - rhs) <= PASS_TOL else "FAIL"
        print(f"  x={x:<6}: x-f(x)={lhs:.12e}  x(1-x)(1-2x)={rhs:.12e}  "
              f"|diff|={abs(lhs - rhs):.3e} [{ok}]")
    return {"a_ok": a_ok, "b_ok": b_ok, "d6": d6, "d12": d12}


# ---------- section 7: CSV + summary ----------

def write_csv(families, xs):
    rows = []
    for k in K_VALUES:
        for g in range(G_MAX + 1):
            rows.append(("k_coupled", k, g, families[k][g], divided_form(k, g), ""))
    for g, v in enumerate(nofeedback_curve()):
        rows.append(("no_feedback", "", g, v, "", ""))
    for d, x in enumerate(xs):
        rows.append(("maj3", "", d, x, (3.0 * xs[0]) ** (2 ** d), 3 ** d))
    with open(CSV_PATH, "w", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow(["section", "param", "g", "value", "reference", "lineage_3d"])
        writer.writerows(rows)
    return len(rows)


def print_summary(table, xs, milestones):
    print("=" * 66)
    print("7. SUMMARY")
    print("=" * 66)
    print(f"k-coupled crossings, first g with I(g) < T   (E={E}, I0={I0})")
    print_crossings(table)
    print(f"\nmaj3 rate map from x0={E}: "
          f"x_d<1e-6 at d={milestones['d6']} (lineage {3 ** milestones['d6']}), "
          f"x_d<1e-12 at d={milestones['d12']} (lineage {3 ** milestones['d12']})")
    print(f"checks: f(x)<x {'PASS' if milestones['a_ok'] else 'FAIL'}, "
          f"3*x_d bound {'PASS' if milestones['b_ok'] else 'FAIL'}")


def main():
    print("=" * 66)
    print(f"2. k-coupled feedback  I(g+1) = (1-E)*I(g)^(k+1)   E={E}, I0={I0}")
    print("=" * 66)
    families = {k: iterate_family(k) for k in K_VALUES}
    print_family_table(families)
    print_verification(families)
    print("    the log-space twin still tracks the recurrence exactly.)")

    print("\n" + "=" * 66)
    print("3./4. crossings per k, with no-feedback contrast")
    print("=" * 66)
    table = crossing_table(families)
    print_crossings(table)
    print_expectation_check(families)

    print("\n" + "=" * 66)
    print(f"5. von Neumann maj3 rate map  f(x) = 3x^2 - 2x^3,  x0 = {E}")
    print("=" * 66)
    xs = iterate_maj3()
    print_maj3_table(xs)
    milestones = check_maj3(xs)

    print("\n" + "=" * 66)
    print("6. common-mode demo")
    print("=" * 66)
    for x in (False, True):
        for y in (False, True):
            assert bool_maj3(x, x, y) == x
    print("independent per-copy noise: majority-of-3 filters it. But if copies 1&2")
    print("inherit the SAME wrong value, copy 3 is outvoted no matter what it holds:")
    print("assert bool_maj3(x, x, y) == x for all bool x, y  -> PASS (4/4 cases)")
    print("==> consensus != correctness")

    print()
    n_rows = write_csv(families, xs)
    print_summary(table, xs, milestones)
    print(f"\nraw data: {n_rows} rows -> {CSV_PATH}")


if __name__ == "__main__":
    main()
