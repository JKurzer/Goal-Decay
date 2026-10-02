"""Goal-content integrity I_g in [0,1] across generations g = 0..G_MAX under fixed error rate E.

Models
------
linear      I(g+1) = I(g) - E*I0          constant absolute loss (hypothesis under test)
nofeedback  I(g+1) = (1-E)*I(g)           transcription fidelity independent of weights
feedback    I(g+1) = (1-E)*I(g)^2         fidelity proportional to current integrity
affine      I(g+1) = (1-E)*I(g) + E/4     decay with restoration floor f = (E/4)/E = 0.25

Closed forms under test
-----------------------
nofeedback  I(g) = I0*(1-E)^g
feedback    I(g) = (I0*(1-E))^(2^g) / (1-E)      [since J(g)=(1-E)*I(g) squares each step]
affine      I(g) = f + (I0-f)*(1-E)^g,  f = 0.25

Outputs: results.csv, console summary, curves.png for E=0.1 (only if matplotlib exists).
Pure stdlib. Run:  python simulate.py
"""

import csv
import os
from collections import namedtuple

HERE = os.path.dirname(os.path.abspath(__file__))
E_VALUES = (0.01, 0.05, 0.1, 0.3)
I0 = 1.0
G_MAX = 60
FLOOR = 0.25                  # fixed point of the affine map: f = (E/4)/E
THRESHOLDS = (0.5, 0.01)      # catastrophe levels
PLOT_E = 0.1
# Repeated float subtraction accumulates dust: exact math says linear(1/E) == 0,
# but e.g. ten float subtractions of 0.1 leave ~+1.4e-16. Absorb that, else the
# falsification generation for E=0.1 spuriously reads 11 instead of 10.
ZERO_TOL = 1e-12


def step_linear(I, E):
    return I - E * I0


def step_nofeedback(I, E):
    return (1.0 - E) * I


def step_feedback(I, E):
    return (1.0 - E) * I * I


def step_affine(I, E):
    return (1.0 - E) * I + E / 4.0


Model = namedtuple("Model", "name step closed")

MODELS = (
    Model("linear", step_linear, lambda g, E: I0 - g * E * I0),
    Model("nofeedback", step_nofeedback, lambda g, E: I0 * (1.0 - E) ** g),
    Model("feedback", step_feedback, lambda g, E: (I0 * (1.0 - E)) ** (2 ** g) / (1.0 - E)),
    Model("affine", step_affine, lambda g, E: FLOOR + (I0 - FLOOR) * (1.0 - E) ** g),
)
MODEL_NAMES = tuple(m.name for m in MODELS)
CLOSED_BY_NAME = {m.name: m.closed for m in MODELS}


def simulate(step, E):
    """Return [I(0), ..., I(G_MAX)] from the recurrence with I(0) = I0."""
    values = [I0]
    for _ in range(G_MAX):
        values.append(step(values[-1], E))
    return values


def run_all():
    """curves[E][model_name] -> [I(0)..I(G_MAX)]."""
    return {E: {m.name: simulate(m.step, E) for m in MODELS} for E in E_VALUES}


def write_csv(curves):
    path = os.path.join(HERE, "results.csv")
    with open(path, "w", newline="") as fh:
        out = csv.writer(fh)
        out.writerow(["E", "g"] + list(MODEL_NAMES))
        for E in E_VALUES:
            for g in range(G_MAX + 1):
                out.writerow([E, g] + ["%.12e" % curves[E][name][g] for name in MODEL_NAMES])
    return path


def first_index(pred, values):
    """First g where pred(values[g]) holds, else None."""
    return next((g for g, v in enumerate(values) if pred(v)), None)


def max_closed_error(name, series, E):
    closed = CLOSED_BY_NAME[name]
    return max(abs(v - closed(g, E)) for g, v in enumerate(series))


def first_falsification(lin, nof):
    """First g with linear(g) <= 0 < nofeedback(g): linear dead, exponential alive."""
    return next(
        (g for g, (l, n) in enumerate(zip(lin, nof)) if l <= ZERO_TOL < n),
        None,
    )


def first_order_violation(lo, hi):
    """First g where 'lo(g) <= hi(g)' fails (strictly lo > hi), else None."""
    return next((g for g, (a, b) in enumerate(zip(lo, hi)) if a > b), None)


def fmt_g(g):
    return "%d" % g if g is not None else ">%d" % G_MAX


def fmt_v(g):
    return "%d" % g if g is not None else "never"


def print_summary(curves):
    line = "=" * 78
    print(line)
    print("GOAL-CONTENT INTEGRITY DECAY ACROSS GENERATIONS  (I0=%.1f, g=0..%d)" % (I0, G_MAX))
    print(line)

    print("\n[1] Closed-form check: max |simulated - closed_form| over all g")
    print("    E       " + "  ".join("%-12s" % n for n in MODEL_NAMES))
    for E in E_VALUES:
        errs = [max_closed_error(n, curves[E][n], E) for n in MODEL_NAMES]
        print("    %-7s " % E + "  ".join("%-12.3e" % e for e in errs))

    print("\n[2] Linear hypothesis falsified: first g with linear(g) <= 0 < nofeedback(g)")
    print("    (exact math: linear dies at g = 1/E; no-feedback = (1-E)^g stays > 0 forever)")
    for E in E_VALUES:
        g_dead = first_falsification(curves[E]["linear"], curves[E]["nofeedback"])
        note = ""
        if g_dead is None:
            note = "  [outside horizon; linear(%d) = %.4f, dies at g=1/E=%d]" % (
                G_MAX, curves[E]["linear"][G_MAX], round(1.0 / E))
        print("    E=%-5s  g_falsified = %-4s%s" % (E, fmt_g(g_dead), note))

    print("\n[3] Error-catastrophe timing: first g with I(g) below threshold")
    print("    E       fb(<0.5)  nf(<0.5)  nf/fb    fb(<0.01)  nf(<0.01)  nf/fb")
    for E in E_VALUES:
        cols = []
        for t in THRESHOLDS:
            g_fb = first_index(lambda v, t=t: v < t, curves[E]["feedback"])
            g_nf = first_index(lambda v, t=t: v < t, curves[E]["nofeedback"])
            if g_fb is not None and g_nf is not None:
                ratio = "%.1fx" % (g_nf / g_fb)
            else:
                ratio = "-"
            cols.append((fmt_g(g_fb), fmt_g(g_nf), ratio))
        (fb5, nf5, r5), (fb01, nf01, r01) = cols
        print("    %-7s %-9s %-9s %-8s %-10s %-10s %s" % (E, fb5, nf5, r5, fb01, nf01, r01))
    print("    ('>60' = threshold never reached within the horizon; nf/fb = how much")
    print("     sooner the catastrophe arrives under feedback vs no-feedback)")

    print("\n[4] Sandwich claim 'feedback(g) <= nofeedback(g) <= linear(g) for all g'")
    print("    First g where each pairwise ordering is violated ('never' = holds on 0..%d)" % G_MAX)
    print("    E       fb<=nf    nf<=lin   fb<=lin   full sandwich holds?")
    for E in E_VALUES:
        fb, nf, ln = (curves[E][n] for n in ("feedback", "nofeedback", "linear"))
        v_fn = first_order_violation(fb, nf)
        v_nl = first_order_violation(nf, ln)
        v_fl = first_order_violation(fb, ln)
        ok = all(fb[g] <= nf[g] <= ln[g] for g in range(G_MAX + 1))
        print("    %-7s %-9s %-9s %-9s %s" % (E, fmt_v(v_fn), fmt_v(v_nl), fmt_v(v_fl), ok))

    print("\nNotes:")
    print("  * fb <= nf holds everywhere: (1-E)*I^2 <= (1-E)*I for I in [0,1].")
    print("  * nf <= lin is ALREADY FALSE at g=2 by Bernoulli: (1-E)^g >= 1 - g*E,")
    print("    strict for g >= 2. So the linear model decays FASTER than no-feedback")
    print("    almost immediately, then crashes through zero at g=1/E -- the falsification.")
    print("  * Under feedback the decay is doubly exponential, I(g) = (I0*(1-E))^(2^g)/(1-E):")
    print("    the error catastrophe arrives vastly sooner than the (1-E)^g exponential.")


def maybe_plot(curves):
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import numpy as np
    except ImportError:
        print("\n[plot] matplotlib not installed -- skipping curves.png")
        return
    gs = list(range(G_MAX + 1))
    fig, ax = plt.subplots(figsize=(8, 5))
    for name in MODEL_NAMES:
        y = np.array(curves[PLOT_E][name], dtype=float)
        y = np.ma.masked_where(y <= 0.0, y)  # semilogy cannot show non-positive values
        ax.semilogy(gs, y, ".-", label=name)
    ax.axhline(FLOOR, ls=":", color="gray", lw=1, label="affine floor 0.25")
    ax.set_xlabel("generation g")
    ax.set_ylabel("I(g)  [log scale]")
    ax.set_title("Goal-content integrity decay, E=%.2f, I0=1" % PLOT_E)
    ax.grid(True, which="both", alpha=0.3)
    ax.legend()
    path = os.path.join(HERE, "curves.png")
    fig.savefig(path, dpi=120, bbox_inches="tight")
    print("\n[plot] saved %s" % path)


def main():
    curves = run_all()
    print("Wrote %s" % write_csv(curves))
    print_summary(curves)
    maybe_plot(curves)


if __name__ == "__main__":
    main()
