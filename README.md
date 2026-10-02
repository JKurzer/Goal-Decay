# Goal-Content Integrity Decay in Recursively Self-Improving Systems

**Question.** In a recursively self-improving system whose Storage is its
weights — written for generation `g+1` by generation `g`, with the current
generation's weights influencing the writing — which decay curve describes
goal-content integrity at a fixed error rate `E`?

**Answer.** None of the usual three (linear / multiplicative / exponential).
With weights in the loop, the decay is super-exponential: double-exponential
in the weakest coupling, a `(k+1)`-tower with the verifier in storage,
factorial if the verification stack deepens. Linear is falsified;
multiplicative ≡ exponential is only the degenerate no-influence case; a
floor exists only with an exogenous anchor. The full statement, with
attributions, is in `CORE.md`; the lay version is `SIMPLE.md`.

## Documents

* `SIMPLE.md` — the result as a 10-line proof for a lay audience. Start here.
* `CORE.md` — the one-page technical statement: model, master theorem,
  survival threshold, exit taxonomy, genomic mapping, falsifier. Single
  source of truth for the technical claims.
* `REVIEW.md` — independent fleet audit (2026-10-02): no major issues;
  includes the resolution log for all findings.
* This README — orientation only; intentionally thin so it cannot drift
  from the sources it points to.

## Verdict summary

| Regime | Curve | Key theorems |
|---|---|---|
| No weights-influence (degenerate) | exponential `I₀(1-E)^g` | `noFeedback_eq`, `noFeedback_exp` |
| Weakest coupling (fidelity ∝ integrity) | double-exponential `(I₀(1-E))^(2^g)/(1-E)` | `feedback_mul`, `feedback_eq` |
| Verifier-in-storage, depth `k ≥ 1` | tower `(1-E)^(((k+1)^g−1)/k)` | `feedbackPow_mul`, `feedbackPow_catastrophe` |
| Deepening stack, `m i ≥ 2` | factorial-or-worse exponent `P g = ∏ m i` (`(g+1)! ≥ (g/e)^g` for `m i = i+2`) | `feedbackGrow_eq`, `growP_factorial`, `feedbackGrow_catastrophe` |
| Any law in the generous class | band: tower ≤ `I g` ≤ exponential | `sandwich`, `goal_content_integrity` |
| Exogenous restoration `B` | exponential relaxation to floor `B/E` | `affineStep_eq` |
| Linear, ever | falsified | `geometric_not_affine`, `linear_dies`, `linear_le_geometric` |

At `E = 9.1%`: fatal (≤ 0.25% integrity) by generation 6 under the weakest
coupling; below 1/2 at generation 2 at depth `k = 6` (`gen_two_k6_fails`);
below 1/5 at generation 3 under the factorial stack (`grow_fact_gen3`).
Survival threshold: `E* ≈ k·ln(1/τ)/(k+1)^G` (`survival_threshold`) — no
`E > 0` tolerates an unbounded horizon. Details and attribution in `CORE.md`.

## Layout

* `GoalDecay/Models.lean` — base recurrences, closed forms, bounds.
* `GoalDecay/Theorems.lean` — linear falsified; exponential form; sandwich;
  catastrophe.
* `GoalDecay/Stronger.lean` — verifier-in-storage `k`-family.
* `GoalDecay/Growing.lean` — deepening stack, factorial regime, 9.1% numerals.
* `GoalDecay/Repair.lean` — von Neumann multiplexing; common-mode lock-in;
  no-floor-without-anchor; behavioral-eval ceiling.
* `GoalDecay/Core.lean` — self-contained distillation (imports only Mathlib).
* `GoalDecay.lean` — library root.
* `Verify.lean` — axiom receipt printer (44 theorems).
* `sim/` — numerical harness: `simulate{,2,3,4,5}.py` +
  `results{,2,3,4,5}.csv`. All closed forms verified to float dust;
  fully deterministic and byte-reproducible (see `REVIEW.md`).

## Reproduce

```
lake exe cache get
lake build
lake env lean Verify.lean
```

Toolchain: `leanprover/lean4:v4.34.1`, mathlib4 @ `v4.34.1` (pinned in
`lean-toolchain`, `lakefile.lean`, `lake-manifest.json`). All 44 receipted
theorems depend only on `[propext, Classical.choice, Quot.sound]`; two
depend on no axioms at all (see `REVIEW.md`).
