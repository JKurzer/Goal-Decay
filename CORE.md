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

**The conditional.** Within the model's axioms (black-box weights,
storage-coupled fidelity, goal content inert to the improver, no exogenous
anchor) there is no parameter regime with a floor: every `k ≥ 1` and every
stack `m ≥ 2` crosses every threshold in finite time. In that precise,
conditional sense, preserving goal content across open-ended
self-modification is impossible — alignment becomes a *maintenance*
discipline, not a one-time property. The exits below all break an axiom.

**Anchor points at `E = 9.1%`.** Proved as Lean numeral theorems: depth
`k = 6` fails (< 1/2) at generation 2 (`gen_two_k6_fails`), `k = 5` does not
(`gen_two_k5_passes`), and the factorial stack is below 1/5 by generation 3
(`grow_fact_gen3`, `0.909^17 ≈ 0.198`). Simulation-only (`results3.csv`):
the growing stack needs stack depth `m(1) ≥ 7` at generation 1 to fail at
generation 2; the factorial stack reaches `≈ 2.7×10⁻⁴` by generation 4;
and the hierarchy at `g = 10` reads: no-feedback `0.39`, `k = 1`:
`4.1×10⁻⁴³`, `k = 6` and factorial below double-float underflow
(`~10^(−1.9×10⁶)` and `~10^(−1.2×10⁶)`).

**Survival threshold** (`GoalDecayCore.survival_threshold`). With `I₀ = 1`,
survival above tolerance `τ` at horizon `G` is exactly
`q^((k+1)^G) ≥ q·τ^k`, i.e. the tolerable rate is
`E* = 1 − τ^(k/((k+1)^G − 1)) ≈ k·ln(1/τ)/(k+1)^G` — a *horizon function*,
not a constant. At `τ = 0.5` and `E = 10⁻⁵`, the first generation below
tolerance is `G = 17` (`k=1`), `11` (`k=2`), `7` (`k=6`), `8` (factorial
stack); only the no-feedback limit reaches `69 315`. For an unbounded horizon
no `E > 0` suffices — that is the catastrophe theorem restated. Since the
scalar `E` aggregates goal size (`E ≈ L·ε`), "simple goals" buy survival
roughly linearly in log L: at a saintly `ε = 10⁻⁹` per site, `L = 10⁶`
lasts 10 generations, `L = 10⁹` is dead on arrival (`sim/results4.csv`).

Beware the cliff: decay is back-loaded. At `E = 10⁻⁵`, `k=1` holds above
99.9% through generation 6 and above 90% through generation 13 — then loses
half its integrity in four generations flat (`0.92` at `g = 13` → `0.27` at
`g = 17`). Short-horizon empirics are actively misleading under tower decay.

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
   probability `≥ p > 0`, survival probability `≤ (1−p)^g`
   (`retention_bound`), and eventual failure is certain (`metastability`):
   the fuse `G ≈ ln2/p` can exceed any
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
   `ρ = 2` with a free gate waits `≈ 8.6×10¹⁶` (`≈ 10¹⁷`) generations for
   the final climb.

**The genomic mapping** (intentional, structural: `weights : agent ::
DNA : organism`).

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

The bio case has selection pushing back on the ratchet; this setup (fixed
`E`, goal content inert to the improver) does not — which is precisely why
the decay is unconditional rather than threshold-dependent.

**Falsifier.** An unanchored, self-referential system observed holding goal
content above a fixed threshold over many generations at `E ≈ 9%` would
refute the model's axiom conjunction — in particular, it would show
transcription fidelity is not storage-coupled.

---

Machine-checked: Lean 4.34.1 + Mathlib (v4.34.1). `GoalDecay/Core.lean`
(self-contained, imports only Mathlib); full development in `GoalDecay/`.
All theorems depend only on `[propext, Classical.choice, Quot.sound]`.
Numerical confirmation: `sim/` (closed forms verified to float dust).
