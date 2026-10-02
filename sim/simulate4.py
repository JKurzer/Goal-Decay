"""simulate4.py - Thresholds, survival horizons, simple-goals mapping, cliffs.

Companion to simulate.py / simulate2.py / simulate3.py (all left untouched).
Pure stdlib. Run:  python simulate4.py

Integrity I(g) with per-step fidelity q = 1 - E, I0 = 1.
Survival at horizon G:  I(G) >= tau, tau = 0.5 ("no worse than 50/50 outcomes").

Models (each is I(g) = q**X(g) with an exact integer exponent X):
  (i)   no-feedback:       X(g) = g
  (ii)  k-coupled tower:   X(g) = ((k+1)^g - 1)/k,        k in {1, 2, 6}
  (iii) factorial stack:   X(g) = R(g), R(0)=0, R(g+1) = (g+2)*R(g)+1

Sections
--------
1. Threshold table: max tolerable E* per model per horizon G.
   Closed form E* = 1 - tau**(1/X(G)); exact via expm1 while X fits the
   double range, else in the log10 domain (E* ~ ln(1/tau)/X, relative
   error ~ 1e-280 or better there).
2. Inverse table: survival horizon G_max = first G with I(G) < 0.5, for
   E in {1e-3, 1e-4, 1e-5, 1e-6}. Verifies the hand estimates at 1e-5.
3. Simple-goals mapping: E = L*eps with eps = 1e-9 per-site; implied E
   and k=1 survival horizon for L in {1e3, 1e6, 1e9, 1e12}.
4. Trajectories at E = 1e-5 (g = 0..20) for k=1 and k=6, plus the cliff
   generation: first g with I(g) < 0.5 after >= 3 consecutive gens > 0.9.
5. Raw dump to results4.csv (long format, mirrors results2/3.csv).
"""

import csv
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
CSV_PATH = os.path.join(HERE, "results4.csv")

TAU = 0.5
LOG2 = math.log(2.0)                    # = ln(1/tau)
HORIZONS = (2, 5, 10, 16, 20, 50, 100, 1000)
E_VALUES = (1e-3, 1e-4, 1e-5, 1e-6)
EPSILON = 1e-9                          # per-site error rate, section 3
GOAL_LENGTHS = (1e3, 1e6, 1e9, 1e12)
TRAJ_E = 1e-5
TRAJ_GMAX = 20
CLIFF_RUN = 3                           # gens > 0.9 required before a cliff
HORIZON_CAP = 20_000_000                # safety net for the no-feedback scan
EXPM1_CUTOFF = 10 ** 280                # below this X, expm1 is safe & exact


# ---------------------------------------------------------------- models ---

_R_CACHE = [0]


def factorial_R(g):
    """R(0) = 0, R(g+1) = (g+2)*R(g) + 1. Pure function + memo cache."""
    while len(_R_CACHE) <= g:
        n = len(_R_CACHE)               # R(n) = (n+1)*R(n-1) + 1
        _R_CACHE.append((n + 1) * _R_CACHE[-1] + 1)
    return _R_CACHE[g]


def tower(k):
    def x(g):
        return ((k + 1) ** g - 1) // k
    return x


MODELS = (
    ("no-feedback", lambda g: g),
    ("k=1", tower(1)),
    ("k=2", tower(2)),
    ("k=6", tower(6)),
    ("factorial", factorial_R),
)


# --------------------------------------------------------------- numerics ---

def log10_estar(x_of_g, G):
    """log10 of E* = 1 - tau**(1/X(G)). Returns (log10E, method)."""
    X = x_of_g(G)
    if X < EXPM1_CUTOFF:
        return math.log10(-math.expm1(-LOG2 / X)), "exact"
    # X huge: E* = -expm1(ln(tau)/X) ~ ln(1/tau)/X, rel err ~ 1e-281.
    return math.log10(LOG2) - math.log10(X), "asymptotic"


def sci(log10_val):
    """Render a positive double from its log10 as m.mmme±X (any exponent)."""
    e = math.floor(log10_val)
    m = 10.0 ** (log10_val - e)
    if m > 9.9995:                      # "%.3f" would print "10.000"
        m, e = 1.0, e + 1
    return f"{m:.3f}e{e}"


def survival_horizon(x_of_g, E, cap=HORIZON_CAP):
    """First G with I(G) < 0.5. None if E > 1 (nonsense) or beyond cap."""
    if E > 1.0:
        return None
    if E >= 1.0:                        # q = 0: I(1) = 0, instant death
        return 1
    # I(G) < 0.5  <=>  X(G) * (-ln q) > ln 2   (exact int-vs-float compare)
    thresh = LOG2 / (-math.log1p(-E))
    g = 1
    while g <= cap:
        if x_of_g(g) > thresh:
            return g
        g += 1
    return None


def integrity(x_of_g, g, E):
    """I(g) = q**X(g), computed as exp(X * log1p(-E))."""
    X = x_of_g(g)
    if X == 0:
        return 1.0
    if E >= 1.0:
        return 0.0
    return math.exp(X * math.log1p(-E))


def cliff_generation(traj):
    """First g with I(g) < 0.5 after >= CLIFF_RUN consecutive gens > 0.9."""
    run = 0
    qualified = False
    for g, val in enumerate(traj):
        if val > 0.9:
            run += 1
            qualified = qualified or run >= CLIFF_RUN
        else:
            run = 0
        if val < 0.5 and qualified:
            return g
    return None


def print_grid(title, headers, rows):
    """Aligned console table; one source of truth for console + CSV data."""
    print(title)
    widths = [max(len(h), *(len(r[i]) for r in rows))
              for i, h in enumerate(headers)]
    line = "  ".join(h.ljust(w) for h, w in zip(headers, widths))
    print(line)
    print("-" * len(line))
    for r in rows:
        print("  ".join(c.ljust(w) for c, w in zip(r, widths)))


# --------------------------------------------------------------- sections ---

def section_1(rows):
    print("=" * 78)
    print("1. THRESHOLD TABLE: max tolerable E* for survival to G (tau = 0.5)")
    print("   E* = 1 - tau**(1/X(G))  [expm1-exact, asymptotic in log10 past 1e280]")
    print("=" * 78)
    headers = ["G"] + [name for name, _ in MODELS]
    grid = []
    for G in HORIZONS:
        cells = [str(G)]
        for name, x_of_g in MODELS:
            l10, method = log10_estar(x_of_g, G)
            cells.append(sci(l10))
            rows.append(("threshold_E*", name, G, sci(l10),
                         f"1 - {TAU}**(1/{x_of_g(G) if G <= 20 else 'X'})",
                         f"X(G)={'exact-int' if G <= 20 else 'bigint'}; {method}"))
        grid.append(cells)
    print_grid("", headers, grid)
    print("read: at horizon G, survival requires per-step error E <= table value.")


def section_2(rows):
    print("\n" + "=" * 78)
    print("2. INVERSE TABLE: survival horizon G_max = first G with I(G) < 0.5")
    print("=" * 78)
    headers = ["E"] + [name for name, _ in MODELS]
    grid = []
    horizons = {}
    for E in E_VALUES:
        cells = [f"{E:g}"]
        for name, x_of_g in MODELS:
            g_max = survival_horizon(x_of_g, E)
            horizons[(E, name)] = g_max
            cells.append(str(g_max))
            rows.append(("inverse_G_max", name, g_max, repr(E), "",
                         "first G with I(G) < 0.5"))
        grid.append(cells)
    print_grid("", headers, grid)

    # verify the hand estimates at E = 1e-5
    est = {"no-feedback": (69315, 69315), "k=1": (16, 17), "k=2": (10, 11),
           "k=6": (6, 7), "factorial": (7, 8)}
    print("\nverify estimates at E = 1e-5:")
    for name, _ in MODELS:
        lo, hi = est[name]
        actual = horizons[(TRAJ_E, name)]
        ok = "OK " if lo <= actual <= hi else "MISS"
        rng = f"{lo}" if lo == hi else f"{lo}-{hi}"
        print(f"  [{ok}] {name:<12} actual {actual:<8} estimate {rng}")
        rows.append(("verify_estimates", name, actual, repr(TRAJ_E), rng, ok))


def section_3(rows):
    print("\n" + "=" * 78)
    print(f"3. SIMPLE-GOALS MAPPING: E = L*eps, eps = {EPSILON:g} per site, k=1 model")
    print("=" * 78)
    headers = ["L (goal length)", "implied E", "k=1 G_max", "note"]
    grid = []
    x_k1 = dict(MODELS)["k=1"]
    for L in GOAL_LENGTHS:
        E = L * EPSILON
        g_max = survival_horizon(x_k1, E)
        if E > 1.0:
            note = "E > 1: rate model breaks down (clamped sites die for sure)"
            g_s = "n/a"
        elif E >= 1.0:
            note = "q = 0: instant death at G = 1"
            g_s = str(g_max)
        else:
            note = ""
            g_s = str(g_max)
        grid.append([f"{L:g}", f"{E:g}", g_s, note])
        rows.append(("simple_goals_k1", f"L={L:g}", g_max if g_max else -1,
                     repr(E), f"eps={EPSILON:g}", note))
    print_grid("", headers, grid)
    print("read: even 'very low' per-site error forces tiny goal content once")
    print("      coupling compounds it -- 'extremely simple goals' quantified.")


def section_4(rows):
    print("\n" + "=" * 78)
    print(f"4. TRAJECTORIES at E = {TRAJ_E:g}, g = 0..{TRAJ_GMAX}: the cliff")
    print("=" * 78)
    headers = ["g", "X_k1(g)", "I_k1(g)", "X_k6(g)", "I_k6(g)"]
    x_k1, x_k6 = dict(MODELS)["k=1"], dict(MODELS)["k=6"]
    traj = {"k=1": [], "k=6": []}
    grid = []
    for g in range(TRAJ_GMAX + 1):
        i1 = integrity(x_k1, g, TRAJ_E)
        i6 = integrity(x_k6, g, TRAJ_E)
        traj["k=1"].append(i1)
        traj["k=6"].append(i6)
        grid.append([str(g), str(x_k1(g)), f"{i1:.6e}",
                     str(x_k6(g)), f"{i6:.6e}"])
        rows.append(("trajectory", "k=1", g, repr(i1), x_k1(g),
                     f"E={TRAJ_E:g}"))
        rows.append(("trajectory", "k=6", g, repr(i6), x_k6(g),
                     f"E={TRAJ_E:g}"))
    print_grid("", headers, grid)
    t = traj["k=1"]
    print(f"\nk=1 early gens look safe: I(2)={t[2]:.6f}, I(3)={t[3]:.6f}, "
          f"I(4)={t[4]:.6f}  (all > 0.9)")
    for name in ("k=1", "k=6"):
        c = cliff_generation(traj[name])
        val = traj[name][c] if c is not None else None
        print(f"  cliff generation {name}: g = {c}   "
              f"(I({c}) = {val:.6e}, I({c - 1}) = {traj[name][c - 1]:.6f})")
        rows.append(("cliff", name, c, repr(val),
                     f">={CLIFF_RUN} gens > 0.9 then I < 0.5", f"E={TRAJ_E:g}"))


def write_csv(rows):
    with open(CSV_PATH, "w", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow(["section", "param", "g", "value", "reference", "note"])
        writer.writerows(rows)
    return len(rows)


def main():
    rows = []
    section_1(rows)
    section_2(rows)
    section_3(rows)
    section_4(rows)
    print()
    n = write_csv(rows)
    print(f"raw data: {n} rows -> {CSV_PATH}")


if __name__ == "__main__":
    main()
