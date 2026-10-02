# Goal-Content Integrity Decay in Recursively Self-Improving Systems

**Question.** In a recursively self-improving system whose Storage is its weights —
written for generation `g+1` by generation `g`, with the current generation's
weights influencing the writing process itself — which decay curve (linear,
multiplicative, exponential) describes goal-content integrity, at a fixed error
rate `E`?

**Answer (proved in Lean 4 + Mathlib, checked numerically in `sim/`):**

| Regime | Curve | Theorem |
|---|---|---|
| Fidelity exogenous (weights don't influence transcription) | **exponential**: `I g = I₀ (1-E)^g = I₀·exp(g·log(1-E))` | `noFeedback_eq`, `noFeedback_exp` |
| Weights are the transcription machinery (`k=1`) | **double exponential**: `I g = (I₀(1-E))^(2^g)/(1-E)` | `feedback_mul`, `feedback_eq` |
| Verifier-in-storage, coupling depth `k` | **tower**: `I g = (1-E)^(((k+1)^g − 1)/k)` | `feedbackPow_mul` |
| Verification stack *deepens* each generation, `m i ≥ 2` | **factorial-or-worse**: `I g = I₀^(P g)·(1-E)^(R g)`, `P g = ∏ m i`; `m i = i+2 ⇒ P g = (g+1)!` | `feedbackGrow_eq`, `growP_factorial` |
| Any law in the generous class `(1-E)·I² ≤ step ≤ (1-E)·I` | sandwiched exp ↔ double-exp | `sandwich` |
| Constant restoration `B` (exogenous repair) | exponential relaxation to floor `B/E` | `affineStep_eq` |
| **Linear, ever** | **falsified** | `noFeedback_not_affine`, `linear_le_noFeedback`, `linear_dies` |

"Multiplicative" and "exponential" are the same curve here (geometric per
generation = exponential in generation count). It is the answer *only* in the
degenerate case where the weights exert no influence on their own rewriting.
Once Storage-is-the-machinery is taken seriously the answer is **none of the
three** — and once the proof-of-correctness is itself in storage, it isn't even
double-exponential: the exponent grows factorially (`x^x` *at least*, by
Stirling: `g! > (g/e)^g`).

## Act I — why linear is not merely wrong but *falsified*

A constant absolute loss per generation, `I(g+1) = I g − E·I₀`, is equivalent to
an effective error *rate* of `E·I₀ / I g` — growing hyperbolically, hitting `1`
at `g = 1/E`. That contradicts the premise of a fixed error rate.

* `linear_le_noFeedback` (Bernoulli): `I₀(1 − E·g) ≤ I₀(1-E)^g` — the linear
  candidate lies *below* the exponential from generation 2 on.
* `linear_dies`: within `⌈1/E⌉` generations the linear model assigns
  non-positive integrity; `noFeedback_pos` keeps the true curve strictly
  positive forever.

## Act II — weights in the loop: super-exponential, uniformly

Canonical coupling `q g = (1-E)·I g` gives `I(g+1) = (1-E)·(I g)²`:

* `feedback_not_geometric` — no constant per-generation ratio exists; neither
  linear nor multiplicative.
* `feedback_le_noFeedback` — dominated by the no-feedback exponential, always.
* `feedback_catastrophe` — every threshold `τ > 0` crossed in finite time,
  on a log-log timescale.

But the *proof of future correctness is in the storage*: faithful writing
requires the goal content **and** the checking procedure **and** the checker's
checker, to depth `k`. Coupling `I(g+1) = (1-E)·(I g)^(k+1)`, `k ≥ 1`:

* `feedbackPow_mul` — closed form for all `k`; `feedbackPow_one` — `k=1` is
  `feedback`; `feedbackPow_mono_k` — stronger coupling decays strictly faster;
* `feedbackPow_catastrophe` — catastrophe is **uniform in k**. The fixed rate
  `E` is not a crutch; it is a floor on the rate. Reality is only faster.

And each generation's checker is itself written into storage, so the stack
*deepens*: `I(g+1) = (1-E)·(I g)^(m g)`, `m i ≥ 2`:

* `feedbackGrow_eq` — exact closed form for any growth `m`;
* `growP_factorial` — one more stored level per generation ⇒ exponent `(g+1)!`;
* `feedbackGrow_catastrophe` — finite-time crossing for **every** `m ≥ 2`.

## Act III — the 9.1% anchor points

At `E = 0.091` (`q = 0.909`), proved as numeral theorems and confirmed by
simulation:

* `feedbackPow_two`: with constant coupling `k`, `I 2 = q^(k+2)` exactly.
* `gen_two_k6_fails`: `k = 6` fails (< 1/2 integrity) **at generation 2**
  (`0.909⁸ ≈ 0.466`). `gen_two_k5_passes`: `k = 5` survives (`≈ 0.513`). The
  gen-2 failure threshold is exactly `k = 6` — i.e. content + 6 nested levels
  of stored machinery (goal, policy, training procedure, eval suite, eval
  runner, reward model, data pipeline…).
* Growing stack: gen-2 failure needs stack depth `m(1) ≥ 7` at generation 1.
* `grow_fact_gen3`: factorial stack (`m i = i+2`) is below 1/5 by generation 3
  (`I 3 = 0.909^17 ≈ 0.198`), below 3e-4 by generation 4.

Within the model's axioms (black-box weights, storage-coupled fidelity, goal
content inert to the improver, no exogenous anchor) there is **no parameter
regime with a floor**: every `k ≥ 1` and every stack `m ≥ 2` crosses every
threshold in finite time. In that precise, conditional sense, preservation of
goal content across open-ended self-modification is impossible — alignment
becomes a *maintenance* discipline, not a one-time property. The exits all
break an axiom (Act IV).

## Act IV — back-flow correction, honestly priced

**Von Neumann multiplexing** (1956) is the strongest black-box mechanism:
`3^d` independent lineages + a simple exogenous aggregator.

* `maj3rate_lt`: majority-of-3 maps rate `E ↦ 3E² − 2E³ < E` for `E < 1/2`
  (factorization `E − f(E) = E(1−E)(1−2E)`).
* `maj3rate_pos`: but the reduced rate is **strictly positive** — redundancy
  reduces the rate, it never creates a floor.
* `maj3Iter_bound`, `maj3_vanishes`: depth-`d` nesting drives the effective
  rate down doubly-exponentially (`3·E_d ≤ (3E)^(2^d)`) — poly-log redundancy
  buys polynomial survival time. At `E = 0.091`: rate below 1e-6 at depth 4
  (81 lineages), below 1e-12 at depth 5 (243 lineages).
* `boolMaj3_consensus`: **common-mode lock-in** — if two lineages share a
  value, majority returns the consensus, *correct or not*. Redundancy filters
  only noise introduced after the split; inherited corruption is preserved.
* `geometric_bound`: **no floor without an anchor** — any process keeping at
  most a fixed fraction `q` of current integrity per generation decays
  geometrically, however clever the internal repair. A true floor requires an
  exogenous, trusted, correctly-directed reference — the "tier-zero state
  maintained manually" doctrine, as a theorem.

**Exogenous behavioral eval vs malicious compliance:**

* `eval_indistinguishable` — the identifiability ceiling: any behavioral eval
  is a finite probe set plus a judgment factoring through probe responses; a
  compliant `f` and maliciously-compliant `g` agreeing on all probes receive
  the *same judgment*. Malicious compliance is invisible exactly in the blind
  region, by definition.
* `probes_eventually_catch` — unpredictable probes turn blind spots into
  gambles: `1 − (1−p)^n → 1`.
* `catch_le_mul` — but detection grows at most linearly (`≤ n·p`, Bernoulli),
  and a system whose model of the probe distribution improves per generation
  shrinks the effective `p`: a static eval is a **degrading asset**.
* The distinguishing mark of malicious compliance is strategic concealment
  relative to the coverage model; detecting it beyond coverage requires
  intent-complete probes — and the intent *is* the goal content, which is
  either in storage (decaying) or maintained exogenously (tier-zero).

## The genomic mapping (intentional, structural)

| Genomics | RSI agent |
|---|---|
| DNA (storage) | **weights** (storage) |
| transcription/replication with mutation rate | weight generation at fixed error rate `E` |
| polymerase encoded in the genome | the network that writes the next network *is* the weights |
| Orgel error catastrophe (1963) | fidelity ∝ integrity ⇒ `feedback` |
| proofreading machinery itself encoded | verifier-in-storage ⇒ `feedbackPow`, `feedbackGrow` |
| Eigen error threshold | `feedback_catastrophe` / `feedbackGrow_catastrophe` |
| Jukes–Cantor identity floor | `affineStep_eq` floor `B/E` (requires exogenous template) |
| Muller's ratchet without selection | no selection term guards goal content |
| recombination / redundancy | von Neumann multiplexing (`maj3*`), with common-mode lock-in |

## Numerical companion (`sim/`)

* `simulate.py` / `results.csv` — closed forms to float dust; linear falsified
  at `g = 1/E`; catastrophe timings.
* `simulate2.py` / `results2.csv` — k-family at `E = 0.091` (k=1: 1/2 at g=4;
  k=2: g=3; k=3: g=3); maj3 iteration to depth 12 with lineage counts.
* `simulate3.py` / `results3.csv` — gen-2 threshold scan (k=6 exact), factorial
  stack table, hierarchy at g=10 (no-feedback 0.39; k=1: 1e-42; k=6 and
  factorial: below double-float underflow, ~1e-1.9M and ~1e-1.2M).

**Start here:** `SIMPLE.md` — the whole result as a 10-line proof readable by a
lay audience. `CORE.md` is the one-page technical version.

## Layout

* `GoalDecay/Models.lean` — the three base recurrences, closed forms, bounds.
* `GoalDecay/Theorems.lean` — falsification of linear; exponential form;
  sandwich; super-exponentiality; catastrophe.
* `GoalDecay/Stronger.lean` — verifier-in-storage `k`-family, uniformity.
* `GoalDecay/Growing.lean` — deepening stack, factorial regime, 9.1% numerals.
* `GoalDecay/Repair.lean` — von Neumann multiplexing, common-mode lock-in,
  no-floor-without-anchor, behavioral-eval ceiling.
* `Verify.lean` — axiom receipt (run `lake env lean Verify.lean`).
* `sim/` — numerical verification harness (standard library only).

## Reproduce

```
lake exe cache get
lake build
lake env lean Verify.lean
```

Toolchain: `leanprover/lean4:v4.34.1`, mathlib4 @ `v4.34.1`.
All theorems depend only on `[propext, Classical.choice, Quot.sound]`.
