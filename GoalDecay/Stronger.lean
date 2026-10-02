import GoalDecay.Models

/-!
# Stronger — the verifier is in the storage

The canonical feedback model (`feedback`, coupling exponent `k = 1`) assumes the
transcription fidelity is proportional to storage integrity. But the *proof of
correctness* of the next generation is itself in the storage: to write
generation `g+1` faithfully, generation `g` needs its goal content intact **and**
the procedure that checks the writing **and** the meta-procedure that checks the
checker, to depth `k`. The honest coupling is therefore

  `I (g+1) = (1 - E) * (I g)^(k+1)`,   `k ≥ 1`,

and `k = 1` (`feedback`) is the *weakest* member — the most generous to the
system. This file shows the conclusion is uniform in `k`:

* `feedbackPow_mul` — closed form for every `k`:
  `(1-E) * (I g)^k = ((1-E) * I₀^k)^((k+1)^g)`, i.e. integrity decays like a
  tower `exp (-Θ((k+1)^g))`.
* `feedbackPow_one` — the `k = 1` case is exactly `feedback`.
* `feedbackPow_mono_k` — stronger coupling decays strictly faster, pointwise.
* `feedbackPow_catastrophe` — for **every** `k ≥ 1`, integrity falls below any
  positive threshold within finitely many generations.

So replacing the fixed rate by any realistic (stronger) coupling only tightens
the result: still super-exponential, still no floor, still finite-time
catastrophe — on an even shorter timescale.
-/

namespace GoalDecay

/-- `k`-coupled feedback: fidelity of the `g → g+1` transition requires the
    goal content and `k` levels of verification machinery to be intact. -/
def feedbackPow (E I₀ : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => I₀
  | (g + 1) => (1 - E) * (feedbackPow E I₀ k g) ^ (k + 1)

@[simp] theorem feedbackPow_zero {E I₀ : ℝ} {k : ℕ} : feedbackPow E I₀ k 0 = I₀ := rfl

@[simp] theorem feedbackPow_succ {E I₀ : ℝ} {k : ℕ} (g : ℕ) :
    feedbackPow E I₀ k (g + 1) = (1 - E) * (feedbackPow E I₀ k g) ^ (k + 1) := rfl

/-- Closed form, all-natural exponents: `(1-E) * (I g)^k = ((1-E) * I₀^k)^((k+1)^g)`.
    For `I₀ = 1` this is `I g = (1-E)^(((k+1)^g - 1)/k)`. -/
theorem feedbackPow_mul (E I₀ : ℝ) (k : ℕ) (g : ℕ) :
    (1 - E) * (feedbackPow E I₀ k g) ^ k
      = ((1 - E) * I₀ ^ k) ^ ((k + 1) ^ g) := by
  induction g with
  | zero => simp [mul_comm]
  | succ j ih =>
    have h1 : (1 - E) * ((1 - E) * feedbackPow E I₀ k j ^ (k + 1)) ^ k
        = ((1 - E) * (feedbackPow E I₀ k j) ^ k) ^ (k + 1) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (k + 1) k, pow_succ]
      ring
    rw [feedbackPow_succ, h1, ih, ← pow_mul, ← pow_succ]

/-- The `k = 1` case recovers the canonical feedback model. -/
theorem feedbackPow_one (E I₀ : ℝ) (g : ℕ) :
    feedbackPow E I₀ 1 g = feedback E I₀ g := by
  induction g with
  | zero => rfl
  | succ j ih => rw [feedback_succ, feedbackPow_succ, ih]

theorem feedbackPow_nonneg {E I₀ : ℝ} (hE : E ≤ 1) (hI : 0 ≤ I₀) (k g : ℕ) :
    0 ≤ feedbackPow E I₀ k g := by
  induction g with
  | zero => exact hI
  | succ j ih =>
    rw [feedbackPow_succ]
    exact mul_nonneg (sub_nonneg.mpr hE) (pow_nonneg ih (k + 1))

theorem feedbackPow_le_one {E I₀ : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hI0 : 0 ≤ I₀) (hI1 : I₀ ≤ 1) (k g : ℕ) :
    feedbackPow E I₀ k g ≤ 1 := by
  induction g with
  | zero => exact hI1
  | succ j ih =>
    rw [feedbackPow_succ]
    have h1 : (feedbackPow E I₀ k j) ^ (k + 1) ≤ 1 := by
      calc (feedbackPow E I₀ k j) ^ (k + 1) ≤ (1 : ℝ) ^ (k + 1) :=
            pow_le_pow_left₀ (feedbackPow_nonneg hE1 hI0 k j) ih (k + 1)
        _ = 1 := one_pow _
    calc (1 - E) * (feedbackPow E I₀ k j) ^ (k + 1) ≤ (1 - E) * 1 :=
          mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hE1)
      _ = 1 - E := mul_one _
      _ ≤ 1 := by linarith

/-- Stronger coupling decays faster, pointwise in every generation. -/
theorem feedbackPow_mono_k {E I₀ : ℝ} (hE0 : 0 < E) (hE1 : E < 1)
    (hI0 : 0 ≤ I₀) (hI1 : I₀ ≤ 1) (k g : ℕ) :
    feedbackPow E I₀ (k + 1) g ≤ feedbackPow E I₀ k g := by
  induction g with
  | zero => exact le_refl _
  | succ j ih =>
    rw [feedbackPow_succ, feedbackPow_succ]
    have hx0 : 0 ≤ feedbackPow E I₀ (k + 1) j :=
      feedbackPow_nonneg (le_of_lt hE1) hI0 (k + 1) j
    have hx1 : feedbackPow E I₀ (k + 1) j ≤ 1 :=
      feedbackPow_le_one (le_of_lt hE0) (le_of_lt hE1) hI0 hI1 (k + 1) j
    have h1 : (feedbackPow E I₀ (k + 1) j) ^ (k + 1 + 1)
        ≤ (feedbackPow E I₀ (k + 1) j) ^ (k + 1) := by
      rw [pow_succ]
      calc (feedbackPow E I₀ (k + 1) j) ^ (k + 1) * feedbackPow E I₀ (k + 1) j
          ≤ (feedbackPow E I₀ (k + 1) j) ^ (k + 1) * 1 :=
            mul_le_mul_of_nonneg_left hx1 (pow_nonneg hx0 (k + 1))
        _ = (feedbackPow E I₀ (k + 1) j) ^ (k + 1) := mul_one _
    have h2 : (feedbackPow E I₀ (k + 1) j) ^ (k + 1)
        ≤ (feedbackPow E I₀ k j) ^ (k + 1) :=
      pow_le_pow_left₀ (feedbackPow_nonneg (le_of_lt hE1) hI0 (k + 1) j) ih (k + 1)
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) (sub_nonneg.mpr (le_of_lt hE1))

/-- **Catastrophe is uniform in the coupling strength**: for every `k ≥ 1`,
    integrity drops below any positive threshold within finitely many
    generations. The timescale is `log_{k+1}` — stronger coupling, faster end. -/
theorem feedbackPow_catastrophe {E I₀ : ℝ} (hE0 : 0 < E) (hE1 : E < 1)
    (hI0 : 0 < I₀) (hI1 : I₀ ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ g : ℕ, feedbackPow E I₀ k g < τ := by
  set c := (1 - E) * I₀ ^ k with hc
  have hc0 : 0 < c := mul_pos (sub_pos.mpr hE1) (pow_pos hI0 k)
  have hc1 : c < 1 := by
    have hIk : I₀ ^ k ≤ 1 := by
      calc I₀ ^ k ≤ (1 : ℝ) ^ k := pow_le_pow_left₀ (le_of_lt hI0) hI1 k
        _ = 1 := one_pow _
    calc (1 - E) * I₀ ^ k ≤ (1 - E) * 1 :=
          mul_le_mul_of_nonneg_left hIk (sub_nonneg.mpr (le_of_lt hE1))
      _ = 1 - E := mul_one _
      _ < 1 := by linarith
  have hkg : ∀ g : ℕ, g ≤ (k + 1) ^ g := by
    intro g
    calc g ≤ 2 ^ g := le_of_lt (two_pow_gt g)
      _ ≤ (k + 1) ^ g := pow_le_pow_left₀ (by norm_num) (by omega) g
  obtain ⟨g, hg⟩ :=
    exists_pow_lt_of_lt_one (mul_pos (pow_pos hτ k) (sub_pos.mpr hE1)) hc1
  refine ⟨g, ?_⟩
  have hle : c ^ ((k + 1) ^ g) ≤ c ^ g :=
    pow_le_pow_of_le_one (le_of_lt hc0) (le_of_lt hc1) (hkg g)
  have h1 : (1 - E) * (feedbackPow E I₀ k g) ^ k ≤ c ^ g := by
    rw [feedbackPow_mul]
    simpa only [← hc] using hle
  have h2 : (1 - E) * (feedbackPow E I₀ k g) ^ k < τ ^ k * (1 - E) :=
    lt_of_le_of_lt h1 hg
  have h3 : (feedbackPow E I₀ k g) ^ k < τ ^ k := by
    by_contra hnot
    push Not at hnot
    have hle2 : τ ^ k * (1 - E) ≤ (feedbackPow E I₀ k g) ^ k * (1 - E) :=
      mul_le_mul_of_nonneg_right hnot (le_of_lt (sub_pos.mpr hE1))
    have hcomm : (1 - E) * (feedbackPow E I₀ k g) ^ k
        = (feedbackPow E I₀ k g) ^ k * (1 - E) := mul_comm _ _
    rw [hcomm] at h2
    exact absurd (lt_of_lt_of_le h2 hle2) (lt_irrefl _)
  by_contra hnot
  push Not at hnot
  have hle3 : τ ^ k ≤ (feedbackPow E I₀ k g) ^ k :=
    pow_le_pow_left₀ (le_of_lt hτ) hnot k
  exact absurd (lt_of_le_of_lt hle3 h3) (lt_irrefl _)

end GoalDecay
