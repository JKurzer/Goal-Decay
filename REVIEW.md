# REVIEW — fleet audit of the goal-decay artifact

**Date:** 2026-10-02. **Scope:** all Lean sources, all prose docs (README, CORE.md,
SIMPLE.md), all sim scripts + CSVs, repo state, build/axiom receipts.
**Method:** three independent read-only auditors (Lean-statement, docs/math,
sims+repo) plus author pre-registration. Auditors re-ran sims in temp dirs,
rebuilt exact solvers from scratch, hand-checked closed forms, and re-executed
`lake env lean Verify.lean`. **Constraint:** no changes to the artifact; this
file is the only output.

## Verdict

**No major issues.** Every load-bearing number in every doc is exact or
correctly rounded. Every headline theorem statement matches its informal
claim, with honest quantifiers (`∀ τ > 0`, `¬∃`) and satisfiable hypothesis
classes. All 44 axiom receipts are clean: no `sorryAx`, no `sorry`/`admit`/
`native_decide`/`axiom`/`set_option` anywhere. Bonus: `boolMaj3_consensus`
and `growP_factorial` use **no axioms at all**, and `growR_ge` uses only
`[propext, Quot.sound]` — cleaner than the advertised
`[propext, Classical.choice, Quot.sound]` baseline. All five sims reproduce
their committed CSVs byte-for-byte; the sim5 exact solves were independently
rebuilt with exact rationals (0 relative difference on 6/6 sampled cells).
Manifest rev `d13f23b` == mathlib tag `v4.34.1`; toolchain matches.

All findings below are documentation-level. Nothing touches the thesis.

## Issues

### MINOR

1. **README Act III umbrella overstates proof coverage.** "proved as numeral
   theorems and confirmed by simulation" — but two sub-claims have no Lean
   numeral theorem: (i) "gen-2 failure needs stack depth `m(1) ≥ 7`"
   (sim-only, `results3.csv` gen1_scan); (ii) factorial "below 3e-4 by
   generation 4" (sim-only; `grow_fact_gen3` covers only `g=3, < 0.2`).
   Values are correct; coverage attribution is not.

2. **README Stirling gloss is literally false as stated.** "the exponent
   grows factorially (**x^x at least**, by Stirling: `g! > (g/e)^g`)" — the
   cited bound is `(x/e)^x`, which is *weaker* than `x^x` (factorial grows
   slower than `x^x` by a factor `e^x`). Correct gloss: "(x/e)^x at least" or
   "of order x^x up to an e^x factor". CORE.md's phrasing is correct; the
   docs are internally asymmetric.

3. **README Act I boundary off-by-one.** "effective rate `E·I₀/I g` … hitting
   1 at `g = 1/E`" — the rate `E/(1−gE)` hits 1 at `g = (1−E)/E = 1/E − 1`
   (e.g. `E=0.1 → g=9`, not 10) and *diverges* at `g = 1/E`, where the linear
   model is already 0. Prose-only; the formal `linear_dies` is correct.

4. **CORE.md exit 3 understates the summit wait.** "~10^16 generations" vs
   exact `8.571×10^16` (= 10^16.93; order-of-magnitude bucket 10^17).
   Direction is conservative for the thesis; magnitude is sloppy.

5. **README staleness.** (a) Layout section omits `GoalDecay/Core.lean` (the
   self-contained distillate) and root `GoalDecay.lean`. (b) Numerical
   companion section stops at `simulate3.py`/`results3.csv` — `simulate4.py`,
   `simulate5.py`, `results4.csv`, `results5.csv` are referenced only by
   CORE.md.

### COSMETIC

6. **"35 theorems" matches no count** (SIMPLE.md fine print; root commit
   message). Actual ledger: 76 theorem declarations total; **58 full
   theorems** (42 across Models/Theorems/Stronger/Growing/Repair + 16 in the
   Core.lean distillate); 18 `@[simp]` helper lemmas; **44 printed axiom
   receipts** in Verify.lean. Direction: under-promise, not overclaim.
   Defensible replacements: "44 theorems with axiom receipts" or "58
   theorems".

7. **"Its Lean proof is 7 lines" (SIMPLE.md).** Defensible but worth pinning:
   `feedback_mul` declaration spans Models.lean:78–85 (8 lines); `:= by`
   through the closing `rw` is exactly 7; the bare tactic block is 6.
   Suggest "7 lines (6 of tactics)" or leave as-is.

8. **README hierarchy "1e-42"** vs computed `4.08×10⁻⁴³` (10^-42.39) —
   order-of-magnitude loose.

### NITS (no action needed)

9. CORE.md exit 2 attributes "survival probability ≤ (1−p)^g" to
   `metastability`; that bound is `retention_bound` (`metastability` itself
   concludes the ∃g crossing via `retention_catastrophe`). The Lean docstring
   (Core.lean:243–250) attributes correctly.
10. CORE.md Falsifier says refutation would "*specifically*" show fidelity
    isn't storage-coupled — survival refutes the whole axiom conjunction,
    not only coupling.
11. CORE.md "0.90 →" is really 0.92 at g=13; ">99.9% for four generations"
    actually holds through g=6 (fails at g=7 = 99.873%). Both understate.
12. CORE.md "simple goals buy survival linearly" — generations bought are
    ~linear in log L, not L.
13. Unused underscore-hypotheses (`_hE0`, `_hI1`, `_hk`, `_hpos`) in
    `sandwich`, `goal_content_integrity`, `survival_threshold` — harmless
    over-hypotheses kept for API symmetry.
14. `two_pow_gt` is duplicated in Models.lean and Core.lean — **intentional**
    (Core.lean is the self-contained distillation). Recorded as design, not
    debt.
15. Archived build log `shell_bg_zsboroyy.log` shows 10 Core receipts
    (predates the `metastability` Verify edit) — stale but consistent;
    superseded by the fresh run (`shell_bg_enw8bylv.log`, all 44 clean).

## Confirmed headline checks (sample)

- `feedbackPow_mul` hand-verified at k=2, g=2: `(1-E)⁹I₀¹⁸ = ((1-E)I₀²)⁹`. 
- `growR` for `m(i)=i+2`: R(3) = 17 ; `growP(3) = 24 = 4!` .
- Numerals: `0.909⁸ = 0.46613 < 0.5`; `0.909⁷ = 0.51280 ≥ 0.5`;
  `0.909¹⁷ = 0.19751 < 0.2` .
- `goal_content_integrity` hypotheses are satisfiable (noFeedback witnesses
  both bounds; feedback witnesses the lower endpoint) — non-vacuous. 
- Catastrophe theorems quantify over **all** `τ > 0`, no watering. 
- Linear falsification generations: `g = ⌈1/E⌉` (E=0.05→20, 0.1→10, 0.3→4). 
- Survival thresholds at E=1e-5: 69315 / 17 / 11 / 7 / 8 (nf/k1/k2/k6/fact). 
- Gambler's ruin: ρ=0.49 → 1/(1+e) = 0.268915; cliff at ρ=1/2 exact. 

## Disposition

No changes were made, per instructions. Issues 1–8 are candidates for a
single future docs commit; nothing requires touching the proofs.
