"""simulate5.py - Meta-stability & positive errors: escape routes from decay.

Companion to simulate.py / simulate2.py / simulate3.py / simulate4.py
(all left untouched). Pure stdlib; `random` with fixed SEED, reproducible.
Run:  python simulate5.py        (a few minutes; section 3 dominates)

Sections
--------
1. ABSORBING CATASTROPHE (the fuse): S(g) = (1-p)^g, T ~ Geometric(p).
   1a  fuse length G_half = ln2/p (the 50/50 survival horizon).
   1b  10,000 lineages per p: mean/median/max escape time, fraction past
       10*G_half (theory (1-p)^(10*G_half) ~ 2^-10 ~ 0.001), censoring at
       the 20M-generation cap. Exact inverse-CDF sampling
       T = ceil(ln U / ln(1-p))  =>  P(T > k) = (1-p)^k  (no per-gen loop).
2. GAMBLER'S RUIN (the price of climbing): birth-death walk on {0..50},
   start 25, P(up) = rho per step, absorbing at 0 and 50. 20,000 walks per
   rho vs exact P(hit 50) = (1 - q^25)/(1 - q^50), q = (1-rho)/rho.
3. VERIFIER-GATED BENEFIT (the black-box catch): integrity x in 0..100,
   start 90. Per generation: negative error w.p. d = 0.1*(x/100); positive
   error w.p. u = rho*0.1*(1-x/100), retained iff x >= theta (else wasted).
   Absorbing failure at x = 0, cap 200,000 generations. 5,000 lineages per
   (theta, rho). Exact event-skipping: waits ~ Geometric(d + u*[x>=theta]),
   embedded up/down chain exact; wasted positive errors only burn clock.
   3b  exact cross-check (no MC): tridiagonal Poisson/gambler solves give
       uncapped P(hit 99 before 0), mean calendar gens to the summit, and
       mean calendar gens to death -- the eval that validates the zeros.
4. Raw dump to results5.csv (long format, mirrors results2/3/4.csv).
"""

import csv
import math
import os
import random
import statistics
import time
from decimal import Decimal, localcontext

HERE = os.path.dirname(os.path.abspath(__file__))
CSV_PATH = os.path.join(HERE, "results5.csv")

SEED = 20250505                          # fixed seed -> reproducible

# --- section 1: the fuse
FUSE_PS = (1e-2, 1e-3, 1e-4, 1e-6)
FUSE_N = 10_000
FUSE_CAP = 20_000_000

# --- section 2: gambler's ruin
RUIN_RHOS = (0.10, 0.30, 0.45, 0.49, 0.50, 0.51, 0.60, 0.90)
RUIN_N = 20_000
RUIN_START = 25
RUIN_TOP = 50

# --- section 3: verifier-gated benefit
GATE_THETAS = (0, 30, 60, 80)
GATE_RHOS = (0.1, 0.5, 1.0, 2.0)
GATE_N = 5_000
GATE_CAP = 200_000
GATE_X0 = 90
GATE_TARGET = 99
GATE_RATE = 0.1                          # base per-generation error rate


# ------------------------------------------------------------- utilities ---

def num(x):
    """Human-readable cell across magnitudes (CSV keeps full precision)."""
    if isinstance(x, int):
        return f"{x:,d}"
    ax = abs(x)
    if ax == 0:
        return "0"
    if ax < 1e-4 or ax >= 1e15:
        return f"{x:.4e}"
    if ax < 1:
        return f"{x:.6f}"
    if ax < 1e4:
        return f"{x:,.2f}"
    return f"{x:,.0f}"


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


# -------------------------------------------------------------- section 1 ---

def section_1(rng, rows):
    print("=" * 78)
    print("1. ABSORBING CATASTROPHE (the fuse): S(g) = (1-p)^g, T ~ Geometric(p)")
    print("=" * 78)
    t0 = time.perf_counter()

    # ---- 1a: fuse length (pure closed form, no sim)
    headers = ["p", "G_half = ln2/p", "10*G_half", "S(10*G_half) theory"]
    grid = []
    for p in FUSE_PS:
        g_half = math.log(2.0) / p
        s_theory = (1.0 - p) ** (10.0 * g_half)
        grid.append([f"{p:g}", num(g_half), num(10.0 * g_half),
                     num(s_theory)])
        rows.append(("fuse_length", f"p={p:g}", "G_half", g_half,
                     "ln2/p", "1a"))
        rows.append(("fuse_length", f"p={p:g}", "S(10*G_half)_theory",
                     s_theory, "(1-p)^(10*ln2/p) ~ 2^-10", "1a"))
    print_grid("\n1a. FUSE LENGTH (the 50/50 survival horizon)", headers, grid)

    # ---- 1b: 10k lineages, exact geometric draws
    headers = ["p", "mean T (sim)", "1/p (theory)", "median T", "max T",
               "frac T>10*G_half", "2^-10", "censored@20M",
               "all dead in cap?"]
    grid = []
    for p in FUSE_PS:
        g_half = math.log(2.0) / p
        horizon = 10.0 * g_half
        log1mp = math.log1p(-p)
        rr = rng.random
        draws = []
        past = censored = 0
        for _ in range(FUSE_N):
            t = math.ceil(math.log(1.0 - rr()) / log1mp)
            if t > horizon:
                past += 1
            if t > FUSE_CAP:
                censored += 1
                t = FUSE_CAP              # censor for summary stats
            draws.append(t)
        mean_t = statistics.fmean(draws)
        med_t = statistics.median(draws)
        max_t = max(draws)
        frac_past = past / FUSE_N
        all_dead = "YES" if censored == 0 else f"NO ({censored} alive)"
        grid.append([f"{p:g}", num(mean_t), num(1.0 / p), num(med_t),
                     num(max_t), num(frac_past), num(2.0 ** -10),
                     str(censored), all_dead])
        tag = f"p={p:g}"
        rows.append(("fuse_sim", tag, "mean_T", mean_t, f"1/p={1.0 / p!r}",
                     "1b"))
        rows.append(("fuse_sim", tag, "median_T", med_t, "~ln2/p", "1b"))
        rows.append(("fuse_sim", tag, "max_T", max_t, "~ln(N)/p", "1b"))
        rows.append(("fuse_sim", tag, "frac_T>10*G_half", frac_past,
                     f"2^-10={2.0 ** -10!r}", "1b"))
        rows.append(("fuse_sim", tag, "censored_at_20M", censored,
                     "cap=20,000,000", "1b"))
        rows.append(("fuse_sim", tag, "all_dead_within_cap",
                     1 if censored == 0 else 0, "1=yes", "1b"))
    print_grid(f"\n1b. ESCAPE TIMES, {FUSE_N:,d} lineages per p "
               f"(cap {FUSE_CAP:,d} gens)", headers, grid)
    print("read: certain death, astronomical fuse -- every lineage dies, but")
    print("      at p=1e-6 the median lineage still runs ~7e5 generations and")
    print("      the luckiest of 10k outlives 10*G_half (~6.9M gens).")
    print(f"[section 1: {time.perf_counter() - t0:.1f}s]")


# -------------------------------------------------------------- section 2 ---

def ruin_exact(rho):
    """P(hit 50 before 0 | start 25); q = (1-rho)/rho."""
    if rho == 0.5:
        return RUIN_START / RUIN_TOP, 1.0
    q25 = ((1.0 - rho) / rho) ** RUIN_START
    return (1.0 - q25) / (1.0 - q25 * q25), q25


def section_2(rng, rows):
    print("\n" + "=" * 78)
    print("2. GAMBLER'S RUIN (the price of climbing): walk on {0..50}, start 25")
    print("=" * 78)
    t0 = time.perf_counter()
    headers = ["rho", "P(hit 50) sim", "P(hit 50) exact", "|diff|",
               "q^25", "regime"]
    grid = []
    exact_by_rho = {}
    for rho in RUIN_RHOS:
        rr = rng.random
        wins = 0
        for _ in range(RUIN_N):
            x = RUIN_START
            while 0 < x < RUIN_TOP:
                if rr() < rho:
                    x += 1
                else:
                    x -= 1
            if x == RUIN_TOP:
                wins += 1
        p_sim = wins / RUIN_N
        p_exact, q25 = ruin_exact(rho)
        exact_by_rho[rho] = p_exact
        if rho < 0.49:
            regime = "exponentially fatal"
        elif rho <= 0.51:
            regime = "CLIFF"
        else:
            regime = "almost-sure climb"
        grid.append([f"{rho:.2f}", num(p_sim), num(p_exact),
                     num(abs(p_sim - p_exact)), num(q25), regime])
        tag = f"rho={rho:g}"
        rows.append(("gamblers_ruin", tag, "P_hit50_sim", p_sim,
                     f"exact={p_exact!r}", f"N={RUIN_N:,d}"))
        rows.append(("gamblers_ruin", tag, "P_hit50_exact", p_exact,
                     "(1-q^25)/(1-q^50), q=(1-rho)/rho", regime))
        rows.append(("gamblers_ruin", tag, "q^25", q25,
                     "((1-rho)/rho)^25", regime))
    print_grid(f"\n2. P(reach 50 before 0), {RUIN_N:,d} walks per rho",
               headers, grid)
    lo, hi = exact_by_rho[0.49], exact_by_rho[0.51]
    print(f"read: the cliff at rho=1/2 -- 0.49 gives {lo:.6f}, 0.51 gives "
          f"{hi:.6f}; a 2-point edge in rho swings survival ~2.7x.")
    print(f"      (49/51)^25 = {(49 / 51) ** 25:.6f} ~ 1/e, so P(0.49) = "
          f"1/(1+(51/49)^25) ~ 1/(1+e) = {1 / (1 + math.e):.6f}.")
    print(f"[section 2: {time.perf_counter() - t0:.1f}s]")


# -------------------------------------------------------------- section 3 ---

def thomas(lo, dg, up, rhs):
    """Tridiagonal solve (Thomas algorithm). lo[1..n-1], dg[0..n-1],
    up[0..n-2]; lo[0] and up[n-1] are ignored. Systems here are M-matrices
    (diag 1, off-diags -a/-b with a+b <= 1), so the sweep is stable."""
    n = len(dg)
    cp = [0.0] * n
    dp = [0.0] * n
    cp[0] = up[0] / dg[0]
    dp[0] = rhs[0] / dg[0]
    for i in range(1, n):
        m = dg[i] - lo[i] * cp[i - 1]
        cp[i] = up[i] / m if i < n - 1 else 0.0
        dp[i] = (rhs[i] - lo[i] * dp[i - 1]) / m
    sol = [0.0] * n
    sol[-1] = dp[-1]
    for i in range(n - 2, -1, -1):
        sol[i] = dp[i] - cp[i] * sol[i + 1]
    return sol


def gate_exact(theta, rho, x0=GATE_X0):
    """Exact uncapped quantities for the section-3 chain (no Monte Carlo).

    Embedded birth-death on 0..100: a_x = u/s (up), b_x = d/s (down),
    calendar cost c_x = 1/s generations per state change, with
    d = RATE*x/100, u = rho*RATE*(1 - x/100) retained iff x >= theta.
    Returns (p99, T99, T0) from x0:
      p99  P(hit x >= 99 before 0)             [gambler solve]
      T99  mean calendar gens to hit {0, 99}   [Poisson solve]
      T0   mean calendar gens to hit 0         [Poisson solve]
    """
    # Decimal at 80 digits: the theta=0 barriers span e^+-100, where
    # float64 Thomas elimination goes ill-conditioned (it produced
    # p99 = 1.05 and T0 < 0 before this fix -- the eval caught it).
    with localcontext() as ctx:
        ctx.prec = 80
        one, zero = Decimal(1), Decimal(0)
        drho = Decimal(str(rho))
        drate = Decimal(str(GATE_RATE))
        a = [zero] * 101
        c = [zero] * 101
        for x in range(1, 101):
            d = drate * Decimal(x) / 100
            u = drho * drate * Decimal(100 - x) / 100 if x >= theta else zero
            s = d + u
            a[x] = u / s
            c[x] = one / s

        def solve(states, rhs_fn, top_value=None):
            """Unknowns t(x) for x in `states`; row t - a*t(x+1) - b*t(x-1)
            = rhs_fn(x). Boundary: last state fixed to top_value if given."""
            n = len(states)
            lo = [zero] * n
            dg = [one] * n
            up = [zero] * n
            rhs = [zero] * n
            for i, x in enumerate(states):
                lo[i] = -(one - a[x])
                rhs[i] = rhs_fn(x)
                if top_value is not None and x == states[-1]:
                    rhs[i] += a[x] * top_value  # t(99) known -> move to rhs
                else:
                    up[i] = -a[x]
            return thomas(lo, dg, up, rhs)

        mid = list(range(1, 99))                # states 1..98
        p99 = solve(mid, lambda x: zero, top_value=one)[x0 - 1]
        t99 = solve(mid, lambda x: c[x])[x0 - 1]
        full = list(range(1, 101))              # states 1..100, t(0) = 0
        t0 = solve(full, lambda x: c[x])[x0 - 1]
    assert zero <= p99 <= one, f"p99 out of range: {p99}"
    assert t99 > 0 and t0 > 0, f"negative hitting time: {t99}, {t0}"
    return float(p99), float(t99), float(t0)


def gate_tables(theta, rho):
    """Per-state exact event tables. State change rate s(x) = d + u if
    x >= theta (positive error retained), else s(x) = d (up is wasted).
    Returns (log(1-s[x]), P(up | change at x)) for x = 1..100."""
    log_wait = [0.0] * 101
    p_up = [0.0] * 101
    for x in range(1, 101):
        d = GATE_RATE * (x / 100.0)
        u = rho * GATE_RATE * (1.0 - x / 100.0) if x >= theta else 0.0
        s = d + u
        log_wait[x] = math.log1p(-s)
        p_up[x] = u / s
    return log_wait, p_up


def section_3(rng, rows):
    print("\n" + "=" * 78)
    print("3. VERIFIER-GATED BENEFIT (the black-box catch): integrity 0..100,")
    print(f"   start {GATE_X0}, absorbing failure at 0, cap {GATE_CAP:,d} "
          f"gens, {GATE_N:,d} lineages per cell")
    print("=" * 78)
    t0 = time.perf_counter()
    headers = ["theta", "rho", "frac hit x>=99", "frac dead by cap",
               "frac censored", "mean gens lived"]
    grid = []
    res = {}
    for theta in GATE_THETAS:
        for rho in GATE_RHOS:
            tc = time.perf_counter()
            log_wait, p_up = gate_tables(theta, rho)
            rr = rng.random
            cap = GATE_CAP
            hit99 = dead = 0
            gens_total = 0
            for _ in range(GATE_N):
                x = GATE_X0
                elapsed = 0
                seen99 = False
                while True:
                    # exact wait to next state change (Geom on {1,2,...})
                    w = math.ceil(math.log(1.0 - rr()) / log_wait[x])
                    if elapsed + w > cap:
                        gens_total += cap      # censored, alive at cap
                        break
                    elapsed += w
                    if rr() < p_up[x]:
                        x += 1
                        if x >= GATE_TARGET:
                            seen99 = True
                    else:
                        x -= 1
                        if x == 0:
                            dead += 1
                            gens_total += elapsed
                            break
                if seen99:
                    hit99 += 1
            f_hit = hit99 / GATE_N
            f_dead = dead / GATE_N
            f_cens = 1.0 - f_dead
            mean_g = gens_total / GATE_N
            res[(theta, rho)] = (f_hit, f_dead, mean_g)
            grid.append([str(theta), f"{rho:g}", num(f_hit), num(f_dead),
                         num(f_cens), num(mean_g)])
            tag = f"theta={theta},rho={rho:g}"
            note = f"start={GATE_X0}, cap={GATE_CAP:,d}, N={GATE_N:,d}"
            rows.append(("verifier_gate", tag, "frac_hit_99", f_hit,
                         "Monte Carlo", note))
            rows.append(("verifier_gate", tag, "frac_dead_by_cap", f_dead,
                         "Monte Carlo", note))
            rows.append(("verifier_gate", tag, "frac_censored", f_cens,
                         "alive at cap", note))
            rows.append(("verifier_gate", tag, "mean_gens_lived", mean_g,
                         "capped at 200k", note))
            print(f"  [theta={theta:<3} rho={rho:<3g} done in "
                  f"{time.perf_counter() - tc:5.1f}s]", flush=True)
    print_grid("\n3. GATE SWEEP: verifier retains positive errors only at "
               "x >= theta", headers, grid)

    # ---- 3b: exact cross-check, no Monte Carlo (the eval for the sim)
    headers = ["theta", "rho", "P(hit99) exact", "T99 exact gens",
               "T0 exact gens", "sim dead-frac", "sim mean lived"]
    grid = []
    for theta in GATE_THETAS:
        for rho in GATE_RHOS:
            p99, t99, t0x = gate_exact(theta, rho)
            f_hit, f_dead, mean_g = res[(theta, rho)]
            grid.append([str(theta), f"{rho:g}", num(p99), num(t99),
                         num(t0x), num(f_dead), num(mean_g)])
            tag = f"theta={theta},rho={rho:g}"
            rows.append(("gate_exact", tag, "P_hit99_uncapped_exact", p99,
                         "decimal-80 thomas/gambler solve", "3b"))
            rows.append(("gate_exact", tag, "T99_gens_exact", t99,
                         "poisson solve, uncapped", "3b"))
            rows.append(("gate_exact", tag, "T0_gens_exact", t0x,
                         "poisson solve, uncapped", "3b"))
    print_grid("\n3b. EXACT CROSS-CHECK (tridiagonal solves, no MC): why the "
               "hit-99 column is zero", headers, grid)

    r0 = [res[(0, r)] for r in GATE_RHOS]
    p99_0_2, t99_0_2, _ = gate_exact(0, 2.0)
    p99_80_2, _, t0_80_2 = gate_exact(80, 2.0)
    print(f"read: theta=0 (gate free): dead-by-cap falls "
          f"{r0[0][1]:.4f} -> {r0[1][1]:.4f} -> {r0[2][1]:.4f} -> "
          f"{r0[3][1]:.4f} as rho goes 0.1 -> 0.5 -> 1 -> 2.")
    print(f"      theta=80: dead ~1.0 at every rho <= 2 (exact T0 at rho=2 "
          f"is {t0_80_2:,.0f} gens); the gate above the start buys nothing.")
    print(f"      hit-99 = 0 in the sim is exact physics: free-gated at rho=2 "
          f"the summit is T99 = {t99_0_2:.2e} gens away (uncapped "
          f"P(hit99) = {p99_0_2:.7f}),")
    print(f"      because u ~ (1-x/100) vanishes near the top while d ~ x/100 "
          f"peaks; gated at theta=80, P(hit99) = {p99_80_2:.2e}, period.")
    print(f"[section 3: {time.perf_counter() - t0:.1f}s]")


# ------------------------------------------------------------------ dump ---

def write_csv(rows):
    with open(CSV_PATH, "w", newline="") as fh:
        writer = csv.writer(fh)
        writer.writerow(["section", "param", "metric", "value",
                         "reference", "note"])
        writer.writerows(rows)
    return len(rows)


def main():
    print(f"simulate5.py -- meta-stability & positive errors "
          f"(seed={SEED}, stdlib only)")
    rng = random.Random(SEED)
    rows = []
    section_1(rng, rows)
    section_2(rng, rows)
    section_3(rng, rows)
    print()
    n = write_csv(rows)
    print(f"raw data: {n} rows -> {CSV_PATH}")


if __name__ == "__main__":
    main()
