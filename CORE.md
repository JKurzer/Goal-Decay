# The Core of It

**System.** Generations `g = 0, 1, 2, …` of a recursively self-improving
system. Storage is the weights, abstracted as far as possible: a scalar
goal-content integrity `I g ∈ [0,1]`. Generation `g` writes generation `g+1`
at fixed error rate `E > 0`. The writing machinery — including the procedure
that verifies the writing — is itself in storage, to depth `k ≥ 1`.

**Model (the whole of it).** With `q := 1 − E`:

* (i) noise only removes, proportionally: `I (g+1) ≤ q · I g`;
* (ii) with depth-`k` storage coupling: `I (g+1) ≤ q · (I g)^(k+1)`.

**Master theorem** (`GoalDecayCore.goal_content_integrity`). Every integrity
sequence in the generous class — per-generation loss between
"weights don't matter" and "depth-`k` coupling" — satisfies all of:

1. **Band**: `tower g ≤ I g ≤ I₀ · q^g`, where the tower is closed-form:
   `q · (tower g)^k = (q · I₀^k)^((k+1)^g)`.
2. **Catastrophe**: `∀ τ > 0, ∃ g, I g < τ` — finite time, always.
3. **Not affine**: no `a, b` with `I₀ q^g = a + b·g` for all `g` exists.
4. **Bernoulli**: `I₀(1 − E·g) ≤ I₀ q^g` — the linear candidate is dominated
   by the truth from generation 2 on, and dies (`≤ 0`) within `⌈1/E⌉`
   generations while the truth stays positive forever (`linear_dies`).

**Verdicts.**

* **Linear**: falsified. Constant absolute loss ⟺ effective error rate
  `E·I₀/I g → ∞`, contradicting fixed `E`.
* **Multiplicative ≡ exponential**: the same curve; the slowest case; the
  ceiling of the band. Correct only when the weights exert no influence on
  their own rewriting.
* **Storage-coupled (the actual architecture)**: none of the three —
  tower-law. Double-exponential at `k = 1`, faster for `k ≥ 2`, factorial
  (`P g = (g+1)!`, i.e. at least `(g/e)^g` by Stirling) if the verification
  stack deepens one level per generation. At `E = 9.1%`: coupling depth
  `k = 6` fails (< 1/2) at generation **2**; factorial stack fails by
  generation **3**.

**Survival threshold** (`GoalDecayCore.survival_threshold`). With `I₀ = 1`,
survival above tolerance `τ` at horizon `G` is exactly
`q^((k+1)^G) ≥ q·τ^k`, i.e. the tolerable rate is
`E* = 1 − τ^(k/((k+1)^G − 1)) ≈ k·ln(1/τ)/(k+1)^G` — a *horizon function*,
not a constant. At `τ = 0.5` and `E = 10⁻⁵`, the first generation below
tolerance is `G = 17` (`k=1`), `11` (`k=2`), `7` (`k=6`), `8` (factorial
stack); only the no-feedback limit reaches `69 315`. For an unbounded horizon
no `E > 0` suffices — that is the catastrophe theorem restated. Since the
scalar `E` aggregates goal size (`E ≈ L·ε`), "simple goals" buy survival
linearly: at a saintly `ε = 10⁻⁹` per site, `L = 10⁶` lasts 10 generations,
`L = 10⁹` is dead on arrival (`sim/results4.csv`).

Beware the cliff: decay is back-loaded. At `E = 10⁻⁵`, `k=1` holds `> 99.9%`
for four generations and `> 90%` through generation 13 — then loses half its
integrity in four generations flat (`0.90 → 0.27` by `g = 17`). Short-horizon
empirics are actively misleading under tower decay.

**The exits — all three, priced.**

1. *Anchor (a floor).* A floor requires retention sourced from something that
   does not decay: an exogenous, trusted, correctly-directed reference —
   tier-zero state, manually maintained. Redundancy without an anchor only
   re-rates the geometric (`maj3rate_pos`), preserves inherited corruption
   verbatim (`boolMaj3_consensus`), and any constant-ratio process decays
   geometrically regardless (`geometric_bound`). Behavioral eval can anchor
   only its probe coverage; compliance and malicious compliance agreeing on
   probes are indistinguishable to it (`eval_indistinguishable`), and its
   coverage is a degrading asset against an improving system (`catch_le_mul`).
2. *Meta-stability (a fuse, not a floor).* If failure has per-generation
   probability `≥ p > 0`, survival probability `≤ (1−p)^g` (`metastability`):
   eventual failure is certain, but the fuse `G ≈ ln2/p` can exceed any
   usable lifetime. Sim (`results5.csv`): at `p = 10⁻⁶` all 10 000 lineages
   still died inside the cap — yet the median lineage lived ~700 000
   generations and the luckiest 8.4×10⁶. "Doomed" and "doomed soon" are
   different prices. Budget: `G·p ≪ 1` (`linear_le_geometric`). Under
   storage coupling the fuse is the tower horizon, and it ends as a cliff.
3. *Positive errors (bistability).* A beneficial channel can close the curve
   into a well near high integrity — genuinely no halting on the absorbed
   paths. The price (gambler's ruin, exact + sim): the climb is exponentially
   fatal below fair odds (`ρ = 0.45 → P ≈ 0.007`), razor-edge at them
   (`ρ = 0.49 → 0.269`; `ρ = 0.51 → 0.731`), near-certain above
   (`ρ = 0.6 → 0.99996`) — and beneficial errors dominating the drift is
   not a known error process. The RSI-specific catch, quantified: benefits
   must be *retained*, and if retention is verifier-gated at threshold `θ`, a
   gate at `θ = 80` is worthless at any `ρ ≤ 2` (exact mean life ~5 150
   generations), while a free gate (`θ = 0`) confers effective immortality at
   `ρ ≥ 0.5`. A gate that works everywhere below you *is* an exogenous
   anchor. The summit itself sits behind a large-deviation paywall:
   beneficial headroom vanishes near the top while damage peaks, so even
   `ρ = 2` with a free gate waits `~10¹⁶` generations for the final climb.

**Falsifier.** An unanchored, self-referential system observed holding goal
content above a fixed threshold over many generations at `E ≈ 9%` would
refute the model — specifically, it would show transcription fidelity is not
storage-coupled.

---

Machine-checked: Lean 4.34.1 + Mathlib (v4.34.1). `GoalDecay/Core.lean`
(self-contained, imports only Mathlib); full development in `GoalDecay/`.
All theorems depend only on `[propext, Classical.choice, Quot.sound]`.
Numerical confirmation: `sim/` (closed forms verified to float dust).
