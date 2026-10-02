import GoalDecay.Models

/-!
# Theorems — which curve is goal-content-integrity decay?

The verdict, formally:

* **Not linear.** The no-feedback law is not affine (`noFeedback_not_affine`).
  The linear candidate `I₀ (1 - E·g)` is dominated by the exponential from
  generation 2 onward (`linear_le_noFeedback`, Bernoulli) and hits `≤ 0` within
  `⌈1/E⌉` generations while the true curve stays positive forever
  (`linear_dies`). A constant absolute loss per generation is equivalent to an
  effective error *rate* growing like `1 / I g` — contradicting fixed `E`.
* **Multiplicative ≡ exponential.** With exogenous fidelity the closed form is
  `I₀ (1-E)^g = I₀ · exp (g · log (1-E))` (`noFeedback_eq`, `noFeedback_exp`).
* **Weights in the loop ⇒ strictly super-exponential.** The canonical coupling
  gives the double exponential `(I₀ (1-E))^(2^g) / (1-E)` (`feedback_mul`),
  which is not geometric (`feedback_not_geometric`), is dominated by the
  no-feedback exponential (`feedback_le_noFeedback`), and drops below any
  positive threshold within finitely many generations (`feedback_catastrophe`).
* **Every law in the generous class lies in the band.** Any integrity sequence
  with `(1-E)·I_g² ≤ I_{g+1} ≤ (1-E)·I_g` is sandwiched between the double
  exponential and the exponential (`sandwich`) — no structure of the weights
  assumed beyond the per-generation loss law.
* **Even with repair, still exponential.** A constant restoration term gives
  geometric relaxation to the floor `B / E` (`affineStep_eq`).
-/

namespace GoalDecay

/-- Multiplicative per-generation decay *is* exponential decay:
    `I₀ (1-E)^g = I₀ · exp (g · log (1-E))`. -/
theorem noFeedback_exp {E : ℝ} (hE : E < 1) (I₀ : ℝ) (g : ℕ) :
    noFeedback E I₀ g = I₀ * Real.exp ((g : ℝ) * Real.log (1 - E)) := by
  rw [noFeedback_eq]
  have hq : Real.exp (Real.log (1 - E)) = 1 - E := Real.exp_log (sub_pos.mpr hE)
  induction g with
  | zero => simp
  | succ k ih =>
    calc I₀ * (1 - E) ^ (k + 1) = (I₀ * (1 - E) ^ k) * (1 - E) := by
          rw [pow_succ]; ring
      _ = (I₀ * Real.exp ((k : ℝ) * Real.log (1 - E))) * Real.exp (Real.log (1 - E)) := by
          rw [ih, hq]
      _ = I₀ * Real.exp ((k : ℝ) * Real.log (1 - E) + Real.log (1 - E)) := by
          rw [Real.exp_add]; ring
      _ = I₀ * Real.exp (((k + 1 : ℕ) : ℝ) * Real.log (1 - E)) := by
          congr 1; congr 1; push_cast; ring

/-- The exponential law is not affine: its second finite difference
    `I₀ E² (1-E)^g` never vanishes, while affine sequences have zero second
    difference. -/
theorem noFeedback_not_affine {E I₀ : ℝ} (hE : E ≠ 0) (hI : I₀ ≠ 0) :
    ¬ ∃ a b : ℝ, ∀ g : ℕ, noFeedback E I₀ g = a + b * (g : ℝ) := by
  rintro ⟨a, b, h⟩
  have s1 : noFeedback E I₀ 0 - 2 * noFeedback E I₀ 1 + noFeedback E I₀ 2 = 0 := by
    rw [h 0, h 1, h 2]; push_cast; ring
  simp only [noFeedback_eq] at s1
  have s2 : I₀ * E ^ 2 = 0 := by
    have hr : I₀ * E ^ 2
        = I₀ * (1 - E) ^ 0 - 2 * (I₀ * (1 - E) ^ 1) + I₀ * (1 - E) ^ 2 := by ring
    rw [hr]; exact s1
  exact mul_ne_zero hI (pow_ne_zero 2 hE) s2

/-- Bernoulli: the linear candidate `I₀ (1 - E·g)` is dominated by the true
    exponential — linear decay is not even a conservative upper bound. -/
theorem linear_le_noFeedback {E I₀ : ℝ} (hE1 : E ≤ 1) (hI0 : 0 ≤ I₀) (g : ℕ) :
    I₀ * (1 - (g : ℝ) * E) ≤ noFeedback E I₀ g := by
  have hb := one_add_mul_le_pow (a := -E) (by linarith : (-2 : ℝ) ≤ -E) g
  have h1 : (1 : ℝ) + (g : ℝ) * (-E) = 1 - (g : ℝ) * E := by ring
  have h2 : (1 : ℝ) + (-E) = 1 - E := by ring
  rw [h1, h2] at hb
  rw [noFeedback_eq]
  exact mul_le_mul_of_nonneg_left hb hI0

/-- The linear hypothesis dies in finite time: within `⌈1/E⌉` generations it
    assigns nonpositive integrity, while the true curve stays positive forever. -/
theorem linear_dies {E I₀ : ℝ} (hE : 0 < E) (hE1 : E < 1) (hI : 0 < I₀) :
    ∃ g : ℕ, I₀ - E * I₀ * (g : ℝ) ≤ 0 ∧ 0 < noFeedback E I₀ g := by
  obtain ⟨g, hg⟩ := exists_nat_ge (1 / E)
  have hEg : (1 : ℝ) ≤ E * (g : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hg (le_of_lt hE)
    rwa [one_div, mul_inv_cancel₀ (ne_of_gt hE)] at h1
  refine ⟨g, ?_, noFeedback_pos hE1 hI g⟩
  have h2 : (1 : ℝ) - E * (g : ℝ) ≤ 0 := by linarith
  calc I₀ - E * I₀ * (g : ℝ) = I₀ * (1 - E * (g : ℝ)) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hI) h2

/-- **Sandwich theorem** (the generosity result): *any* integrity sequence whose
    per-generation loss law lies between "weights don't matter"
    (`I (g+1) ≤ (1-E) * I g`) and "weights fully determine fidelity"
    (`(1-E) * (I g)^2 ≤ I (g+1)`) is trapped between the exponential and the
    double exponential. No structure of the weights is assumed at all. -/
theorem sandwich {E I₀ : ℝ} (_hE0 : 0 < E) (hE1 : E < 1) (hI0 : 0 ≤ I₀) (_hI1 : I₀ ≤ 1)
    (I : ℕ → ℝ) (h0 : I 0 = I₀)
    (hlow : ∀ g, (1 - E) * (I g) ^ 2 ≤ I (g + 1))
    (hhigh : ∀ g, I (g + 1) ≤ (1 - E) * I g) :
    ∀ g, feedback E I₀ g ≤ I g ∧ I g ≤ noFeedback E I₀ g := by
  intro g
  induction g with
  | zero => rw [h0]; exact ⟨le_refl _, le_refl _⟩
  | succ k ih =>
    obtain ⟨hfb, hnf⟩ := ih
    constructor
    · rw [feedback_succ]
      calc (1 - E) * (feedback E I₀ k) ^ 2 ≤ (1 - E) * (I k) ^ 2 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (feedback_nonneg (le_of_lt hE1) hI0 k) hfb 2)
              (sub_nonneg.mpr (le_of_lt hE1))
        _ ≤ I (k + 1) := hlow k
    · rw [noFeedback_succ]
      calc I (k + 1) ≤ (1 - E) * I k := hhigh k
        _ ≤ (1 - E) * noFeedback E I₀ k :=
            mul_le_mul_of_nonneg_left hnf (sub_nonneg.mpr (le_of_lt hE1))

/-- The weights-in-the-loop law decays at least as fast as the
    weights-don't-matter law — feedback can only hurt. -/
theorem feedback_le_noFeedback {E I₀ : ℝ} (hE0 : 0 < E) (hE1 : E < 1)
    (hI0 : 0 ≤ I₀) (hI1 : I₀ ≤ 1) (g : ℕ) :
    feedback E I₀ g ≤ noFeedback E I₀ g := by
  have hx0 : ∀ k, 0 ≤ noFeedback E I₀ k :=
    fun k => noFeedback_nonneg (le_of_lt hE1) hI0 k
  have hx1 : ∀ k, noFeedback E I₀ k ≤ 1 :=
    fun k => noFeedback_le_one (le_of_lt hE0) (le_of_lt hE1) hI0 hI1 k
  have hlow : ∀ k, (1 - E) * (noFeedback E I₀ k) ^ 2 ≤ noFeedback E I₀ (k + 1) := by
    intro k
    rw [noFeedback_succ]
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (le_of_lt hE1))
    calc (noFeedback E I₀ k) ^ 2 = noFeedback E I₀ k * noFeedback E I₀ k :=
          pow_two _
      _ ≤ noFeedback E I₀ k * 1 := mul_le_mul_of_nonneg_left (hx1 k) (hx0 k)
      _ = noFeedback E I₀ k := mul_one _
  have hhigh : ∀ k, noFeedback E I₀ (k + 1) ≤ (1 - E) * noFeedback E I₀ k := by
    intro k
    rw [noFeedback_succ]
  exact (sandwich hE0 hE1 hI0 hI1 (noFeedback E I₀) noFeedback_zero hlow hhigh g).1

/-- The feedback curve is not geometric: its per-generation ratio
    `(1-E) · I g` shrinks with `I g`, so no constant ratio `r` exists. Hence it
    is *neither* linear *nor* multiplicative — it is super-exponential. -/
theorem feedback_not_geometric {E I₀ : ℝ} (hE0 : 0 < E) (hE1 : E < 1)
    (hI0 : 0 < I₀) (hI1 : I₀ ≤ 1) :
    ¬ ∃ r : ℝ, ∀ g : ℕ, feedback E I₀ (g + 1) = r * feedback E I₀ g := by
  rintro ⟨r, hr⟩
  set c := I₀ * (1 - E) with hc
  have hc0 : 0 < c := mul_pos hI0 (sub_pos.mpr hE1)
  have hc1 : c < 1 :=
    calc I₀ * (1 - E) ≤ 1 * (1 - E) :=
          mul_le_mul_of_nonneg_right hI1 (sub_nonneg.mpr (le_of_lt hE1))
      _ = 1 - E := one_mul _
      _ < 1 := by linarith
  -- Multiplying the supposed ratio law by `1-E` turns it into a law for `c^(2^g)`.
  have key : ∀ g : ℕ, c ^ (2 ^ (g + 1)) = r * c ^ (2 ^ g) := by
    intro g
    have h1 := congrArg (fun x : ℝ => (1 - E) * x) (hr g)
    rw [feedback_mul] at h1
    have h2 : (1 - E) * (r * feedback E I₀ g) = r * ((1 - E) * feedback E I₀ g) := by
      ring
    rw [h2, feedback_mul] at h1
    simpa only [← hc] using h1
  -- But `c^(2^(g+1)) = (c^(2^g))^2`, so `c^(2^g) = r` for every `g`.
  have hsq : ∀ g : ℕ, (c ^ (2 ^ g)) ^ 2 = c ^ (2 ^ (g + 1)) := by
    intro g
    rw [← pow_mul, ← pow_succ]
  have hcpow : ∀ g : ℕ, c ^ (2 ^ g) = r := by
    intro g
    have h := hsq g
    rw [key g] at h
    have hne : c ^ (2 ^ g) ≠ 0 := pow_ne_zero _ (ne_of_gt hc0)
    have hf : c ^ (2 ^ g) * (c ^ (2 ^ g) - r) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hf with h' | h'
    · exact absurd h' hne
    · exact sub_eq_zero.mp h'
  -- Two generations of `c^(2^g) = r` force `c = c²`, i.e. `c ∈ {0, 1}`.
  have e0 : c = r := by
    have h := hcpow 0
    rw [show (2 : ℕ) ^ (0 : ℕ) = 1 from rfl, pow_one] at h
    exact h
  have e1 : c ^ 2 = r := by
    have h := hcpow 1
    rw [show (2 : ℕ) ^ (1 : ℕ) = 2 from rfl] at h
    exact h
  rw [← e0] at e1
  have hcc : c * (c - 1) = 0 := by linear_combination e1
  rcases mul_eq_zero.mp hcc with h | h
  · exact absurd h (ne_of_gt hc0)
  · have hc1' : c = 1 := sub_eq_zero.mp h
    rw [hc1'] at hc1
    exact absurd hc1 (lt_irrefl 1)

/-- **Error catastrophe**: under weights-mediated feedback, integrity falls
    below *any* positive threshold within finitely many generations — and on a
    log-log timescale, since `feedback E I₀ g ≤ (I₀(1-E))^g / (1-E)`. -/
theorem feedback_catastrophe {E I₀ : ℝ} (hE0 : 0 < E) (hE1 : E < 1)
    (hI0 : 0 < I₀) (hI1 : I₀ ≤ 1) (τ : ℝ) (hτ : 0 < τ) :
    ∃ g : ℕ, feedback E I₀ g < τ := by
  set c := I₀ * (1 - E) with hc
  have hc0 : 0 < c := mul_pos hI0 (sub_pos.mpr hE1)
  have hc1 : c < 1 :=
    calc I₀ * (1 - E) ≤ 1 * (1 - E) :=
          mul_le_mul_of_nonneg_right hI1 (sub_nonneg.mpr (le_of_lt hE1))
      _ = 1 - E := one_mul _
      _ < 1 := by linarith
  obtain ⟨g, hg⟩ := exists_pow_lt_of_lt_one (mul_pos hτ (sub_pos.mpr hE1)) hc1
  refine ⟨g, ?_⟩
  have hle : c ^ (2 ^ g) ≤ c ^ g :=
    pow_le_pow_of_le_one (le_of_lt hc0) (le_of_lt hc1) (le_of_lt (two_pow_gt g))
  have h1 : (1 - E) * feedback E I₀ g ≤ c ^ g := by
    rw [feedback_mul]
    simpa only [← hc] using hle
  have hfb : (1 - E) * feedback E I₀ g < τ * (1 - E) := lt_of_le_of_lt h1 hg
  by_contra hnot
  push Not at hnot
  have hle2 : τ * (1 - E) ≤ feedback E I₀ g * (1 - E) :=
    mul_le_mul_of_nonneg_right hnot (le_of_lt (sub_pos.mpr hE1))
  have hcomm : (1 - E) * feedback E I₀ g = feedback E I₀ g * (1 - E) := mul_comm _ _
  rw [hcomm] at hfb
  exact absurd (lt_of_lt_of_le hfb hle2) (lt_irrefl _)

end GoalDecay
