import GoalDecay.Models

/-!
# Repair — back-flow correction for black-box systems

Can anything push back against the decay without reading the weights? Yes —
but less than one hopes. This file formalizes the strongest black-box
mechanism (von Neumann multiplexing, 1956: independent lineages + a simple
exogenous aggregator) and its three hard limits.

* `maj3rate`, `maj3rate_pos`, `maj3rate_lt` — majority-of-three turns rate
  `E` into `3E² − 2E³`, which is **strictly smaller but strictly positive**
  for `0 < E < 1/2`: redundancy reduces the rate, it never creates a floor.
* `maj3Iter_bound`, `maj3_vanishes` — nesting the aggregator to depth `d`
  drives the *effective* rate down doubly-exponentially
  (`3·E_d ≤ (3E)^(2^d)`), so poly-log redundancy per generation buys
  polynomial survival time. The price is `3^d` independent lineages and an
  aggregator that is itself correct — i.e. exogenous, trusted machinery.
* `boolMaj3_consensus` — **common-mode lock-in**: if two lineages share a
  value, majority returns the consensus, *correct or not*. Redundancy filters
  only noise introduced after the lineages split; inherited corruption is
  faithfully preserved. Nothing already lost comes back.
* `geometric_bound` — **no floor without an anchor**: any per-generation
  process that keeps at most a fixed fraction `q` of current integrity —
  however clever the repair, as long as its only reference is the storage
  itself — yields `I g ≤ I₀ · q^g`. A constant-ratio process is geometric,
  always. A true floor requires an exogenous, trusted, correctly-directed
  reference. (This is precisely the "tier-zero state must be maintained
  manually" doctrine.)
-/

namespace GoalDecay

/-- Effective per-symbol error rate after majority-of-three aggregation of
    three independent copies: `P(≥ 2 of 3 err) = 3E²(1-E) + E³ = 3E² − 2E³`. -/
def maj3rate (E : ℝ) : ℝ := 3 * E ^ 2 - 2 * E ^ 3

/-- The reduced rate is still positive: redundancy never reaches a floor. -/
theorem maj3rate_pos {E : ℝ} (hE : 0 < E) (hE2 : E < 3 / 2) : 0 < maj3rate E := by
  have hf : maj3rate E = E ^ 2 * (3 - 2 * E) := by unfold maj3rate; ring
  rw [hf]
  exact mul_pos (pow_pos hE 2) (by linarith)

/-- The reduced rate is strictly smaller than the input rate for `E < 1/2`:
    `E − f(E) = E(1−E)(1−2E) > 0`. -/
theorem maj3rate_lt {E : ℝ} (hE : 0 < E) (hE2 : E < 1 / 2) : maj3rate E < E := by
  have hf : E - maj3rate E = E * (1 - E) * (1 - 2 * E) := by unfold maj3rate; ring
  have hpos : 0 < E * (1 - E) * (1 - 2 * E) :=
    mul_pos (mul_pos hE (by linarith)) (by linarith)
  linarith

/-- The reduced rate is bounded by `3E²` (the quadratic term dominates). -/
theorem maj3rate_le_sq {E : ℝ} (hE : 0 ≤ E) : maj3rate E ≤ 3 * E ^ 2 := by
  unfold maj3rate
  nlinarith [pow_nonneg hE 3]

/-- Depth-`d` nested majority: each level aggregates three independent copies
    of the previous level's output. Costs `3^d` lineages. -/
def maj3Iter (E : ℝ) : ℕ → ℝ
  | 0 => E
  | (d + 1) => maj3rate (maj3Iter E d)

@[simp] theorem maj3Iter_zero {E : ℝ} : maj3Iter E 0 = E := rfl

@[simp] theorem maj3Iter_succ {E : ℝ} (d : ℕ) :
    maj3Iter E (d + 1) = maj3rate (maj3Iter E d) := rfl

/-- Iterating the aggregator drives the effective rate down
    doubly-exponentially in depth: `3·E_d ≤ (3E)^(2^d)`, with `E_d < 1/2`
    preserved along the way. -/
theorem maj3Iter_bound {E : ℝ} (hE0 : 0 < E) (hE2 : E < 1 / 2) (d : ℕ) :
    0 ≤ maj3Iter E d ∧ maj3Iter E d < 1 / 2 ∧ 3 * maj3Iter E d ≤ (3 * E) ^ (2 ^ d) := by
  induction d with
  | zero =>
    refine ⟨le_of_lt hE0, hE2, ?_⟩
    calc 3 * maj3Iter E 0 = 3 * E := by rw [maj3Iter_zero]
      _ ≤ (3 * E) ^ (2 ^ 0) := by norm_num
  | succ j ih =>
    obtain ⟨h0, hhalf, hbound⟩ := ih
    rw [maj3Iter_succ]
    have hf : maj3rate (maj3Iter E j)
        = (maj3Iter E j) ^ 2 * (3 - 2 * maj3Iter E j) := by unfold maj3rate; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hf]
      exact mul_nonneg (pow_nonneg h0 2) (by linarith)
    · rcases eq_or_lt_of_le h0 with hz | hpos
      · rw [← hz]
        unfold maj3rate
        norm_num
      · exact lt_trans (maj3rate_lt hpos hhalf) hhalf
    · have hmaj := maj3rate_le_sq h0
      calc 3 * maj3rate (maj3Iter E j) ≤ 3 * (3 * (maj3Iter E j) ^ 2) :=
            mul_le_mul_of_nonneg_left hmaj (by norm_num)
        _ = (3 * maj3Iter E j) ^ 2 := by ring
        _ ≤ ((3 * E) ^ (2 ^ j)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (by norm_num) h0) hbound 2
        _ = (3 * E) ^ (2 ^ (j + 1)) := by rw [← pow_mul, ← pow_succ]

/-- **Reliability can be bought**: for `E < 1/3` the effective rate falls below
    any `ε > 0` at some finite depth — doubly-exponentially fast, so the
    required lineage count grows only poly-logarithmically in `1/ε`. -/
theorem maj3_vanishes {E : ℝ} (hE0 : 0 < E) (hE3 : E < 1 / 3)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, maj3Iter E d < ε := by
  obtain ⟨d, hd⟩ :=
    exists_pow_lt_of_lt_one (mul_pos (by norm_num : (0:ℝ) < 3) hε) (by linarith : 3 * E < 1)
  refine ⟨d, ?_⟩
  have hle1 : (3 * E) ^ (2 ^ d) ≤ (3 * E) ^ d :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (le_of_lt (two_pow_gt d))
  have hb := (maj3Iter_bound hE0 (by linarith) d).2.2
  have h3 : 3 * maj3Iter E d < 3 * ε := lt_of_le_of_lt (le_trans hb hle1) hd
  by_contra hnot
  push Not at hnot
  have hle2 : 3 * ε ≤ 3 * maj3Iter E d :=
    mul_le_mul_of_nonneg_left hnot (by norm_num)
  exact absurd (lt_of_le_of_lt hle2 h3) (lt_irrefl _)

/-- Coordinate-wise majority of three boolean values. -/
def boolMaj3 (x y z : Bool) : Bool := (x && y) || (x && z) || (y && z)

/-- **Common-mode lock-in**: if two lineages share a value — inherited
    corruption included — majority aggregation returns the consensus, correct
    or not. Redundancy can only filter noise introduced *after* the split. -/
theorem boolMaj3_consensus (x y : Bool) : boolMaj3 x x y = x := by
  cases x <;> cases y <;> rfl

/-- **No floor without an anchor**: any process that keeps at most a fixed
    fraction `q` of current integrity per generation decays geometrically,
    regardless of how the repair is arranged internally. -/
theorem geometric_bound {q I₀ : ℝ} (hq : 0 ≤ q) (_hI0 : 0 ≤ I₀) (I : ℕ → ℝ)
    (h0 : I 0 ≤ I₀) (hstep : ∀ g, I (g + 1) ≤ q * I g) :
    ∀ g, I g ≤ I₀ * q ^ g := by
  intro g
  induction g with
  | zero =>
    calc I 0 ≤ I₀ := h0
      _ = I₀ * q ^ 0 := by simp
  | succ k ih =>
    calc I (k + 1) ≤ q * I k := hstep k
      _ ≤ q * (I₀ * q ^ k) := mul_le_mul_of_nonneg_left ih hq
      _ = I₀ * q ^ (k + 1) := by rw [pow_succ]; ring

/-! ### Exogenous behavioral eval: the identifiability ceiling

Can an exogenous behavioral eval distinguish compliance from malicious
compliance? Only within its probe coverage — and this is a theorem, not an
engineering limitation. -/

/-- An exogenous behavioral eval: a finite probe set, plus a judgment that
    depends only on probe responses (that is what "behavioral" means). -/
structure BehavioralEval (X Y J : Type*) where
  probe : Finset X
  judge : (X → Y) → J
  factored : ∀ f g : X → Y, (∀ x ∈ probe, f x = g x) → judge f = judge g

/-- **Identifiability ceiling**: if a compliant policy `f` and a maliciously
    compliant policy `g` agree on every probe, then *every* behavioral eval
    assigns them the same judgment. Malicious compliance is invisible exactly
    in the eval's blind region; distinguishing it there would require
    information no probe supplied. -/
theorem eval_indistinguishable {X Y J : Type*} (ℰ : BehavioralEval X Y J)
    {f g : X → Y} (h : ∀ x ∈ ℰ.probe, f x = g x) :
    ℰ.judge f = ℰ.judge g :=
  ℰ.factored f g h

/-- Unpredictable probes turn blind spots into gambles: with per-probe
    independent detection probability `p`, `n` probes catch a deviation with
    probability `1 - (1-p)^n`, which exceeds any `1 - ε` for large `n`. -/
theorem probes_eventually_catch {p ε : ℝ} (hp : 0 < p) (_hp1 : p ≤ 1) (hε : 0 < ε) :
    ∃ n : ℕ, (1 - p) ^ n < ε :=
  exists_pow_lt_of_lt_one hε (by linarith)

/-- But detection probability grows at most linearly in probe count
    (`1 - (1-p)^n ≤ n·p`, Bernoulli): if the system's model of the probe
    distribution improves per generation — shrinking the effective `p` — the
    eval is a degrading asset. -/
theorem catch_le_mul {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ (n : ℝ) * p := by
  have hb := one_add_mul_le_pow (a := -p) (by linarith : (-2 : ℝ) ≤ -p) n
  have h1 : (1 : ℝ) + (n : ℝ) * (-p) = 1 - (n : ℝ) * p := by ring
  have h2 : (1 : ℝ) + (-p) = 1 - p := by ring
  rw [h1, h2] at hb
  linarith

end GoalDecay
