import Mathlib

/-!
# Models — integrity recurrences for recursively self-improving systems

Storage is the weights, abstracted as generously as possible: the only state we
track is a scalar *goal-content integrity* `I g` at generation `g : ℕ`.
Generation `g` writes the storage of generation `g + 1` at a fixed error rate `E`.
The weights of generation `g` are the machinery that performs the writing, so the
fidelity of the `g → g+1` transition may depend on `I g`. This is the deliberate
mapping `weights : agent :: DNA : organism` — transcription-error accumulation
(Orgel's error-catastrophe feedback) applied to neural-net self-improvement.

Three per-generation loss laws:

* `noFeedback` — fidelity exogenous (weights don't influence transcription):
  `I (g+1) = (1-E) * I g`.
* `feedback` — fidelity proportional to the integrity of the weights doing the
  writing (weights *are* the transcription machinery):
  `I (g+1) = (1-E) * (I g)^2`.
* `affineStep` — transcription with a constant restoration term `B`
  (repair / back-mutation; the Jukes–Cantor-style floor):
  `I (g+1) = (1-E) * I g + B`.
-/

namespace GoalDecay

/-- No-feedback transcription: each generation keeps fraction `1 - E` of what remains. -/
def noFeedback (E I₀ : ℝ) : ℕ → ℝ
  | 0 => I₀
  | (g + 1) => (1 - E) * noFeedback E I₀ g

/-- Weights-mediated feedback: transcription fidelity at generation `g` is
    proportional to the integrity `I g` of the weights doing the transcribing. -/
def feedback (E I₀ : ℝ) : ℕ → ℝ
  | 0 => I₀
  | (g + 1) => (1 - E) * (feedback E I₀ g) ^ 2

/-- Transcription with a constant per-generation restoration term `B`. -/
def affineStep (E B I₀ : ℝ) : ℕ → ℝ
  | 0 => I₀
  | (g + 1) => (1 - E) * affineStep E B I₀ g + B

@[simp] theorem noFeedback_zero {E I₀ : ℝ} : noFeedback E I₀ 0 = I₀ := rfl

@[simp] theorem noFeedback_succ {E I₀ : ℝ} (g : ℕ) :
    noFeedback E I₀ (g + 1) = (1 - E) * noFeedback E I₀ g := rfl

@[simp] theorem feedback_zero {E I₀ : ℝ} : feedback E I₀ 0 = I₀ := rfl

@[simp] theorem feedback_succ {E I₀ : ℝ} (g : ℕ) :
    feedback E I₀ (g + 1) = (1 - E) * (feedback E I₀ g) ^ 2 := rfl

@[simp] theorem affineStep_zero {E B I₀ : ℝ} : affineStep E B I₀ 0 = I₀ := rfl

@[simp] theorem affineStep_succ {E B I₀ : ℝ} (g : ℕ) :
    affineStep E B I₀ (g + 1) = (1 - E) * affineStep E B I₀ g + B := rfl

/-- Auxiliary growth fact. -/
theorem two_pow_gt : ∀ g : ℕ, g < 2 ^ g := by
  intro g
  induction g with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

/-! ## Closed forms -/

/-- Fixed error rate with exogenous fidelity is exactly geometric —
    multiplicative per generation, i.e. exponential in the generation count. -/
theorem noFeedback_eq (E I₀ : ℝ) (g : ℕ) :
    noFeedback E I₀ g = I₀ * (1 - E) ^ g := by
  induction g with
  | zero => simp
  | succ k ih => rw [noFeedback_succ, ih, pow_succ]; ring

/-- Under weights-mediated feedback, integrity is doubly exponential:
    `I g = (I₀ (1-E))^(2^g) / (1-E)`. We prove the division-free form. -/
theorem feedback_mul (E I₀ : ℝ) (g : ℕ) :
    (1 - E) * feedback E I₀ g = (I₀ * (1 - E)) ^ (2 ^ g) := by
  induction g with
  | zero => simp [mul_comm]
  | succ k ih =>
    have h1 : (1 - E) * ((1 - E) * feedback E I₀ k ^ 2)
        = ((1 - E) * feedback E I₀ k) ^ 2 := by ring
    rw [feedback_succ, h1, ih, ← pow_mul, ← pow_succ]

/-- The divided (textbook) form of the feedback closed form. -/
theorem feedback_eq {E : ℝ} (hE : E ≠ 1) (I₀ : ℝ) (g : ℕ) :
    feedback E I₀ g = (I₀ * (1 - E)) ^ (2 ^ g) / (1 - E) := by
  have h : (1 - E) ≠ 0 := sub_ne_zero.mpr (Ne.symm hE)
  rw [eq_div_iff_mul_eq h, mul_comm]
  exact feedback_mul E I₀ g

/-- With constant restoration `B` the recurrence relaxes geometrically to the
    floor `B / E` — still exponential, never linear. -/
theorem affineStep_eq {E : ℝ} (hE : E ≠ 0) (B I₀ : ℝ) (g : ℕ) :
    affineStep E B I₀ g = B / E + (I₀ - B / E) * (1 - E) ^ g := by
  have key : (1 - E) * (B / E) + B = B / E := by field_simp; ring
  induction g with
  | zero => simp
  | succ k ih => rw [affineStep_succ, ih, pow_succ]; linear_combination key

/-! ## Basic bounds -/

theorem noFeedback_nonneg {E I₀ : ℝ} (hE : E ≤ 1) (hI : 0 ≤ I₀) (g : ℕ) :
    0 ≤ noFeedback E I₀ g := by
  rw [noFeedback_eq]
  exact mul_nonneg hI (pow_nonneg (sub_nonneg.mpr hE) g)

theorem noFeedback_pos {E I₀ : ℝ} (hE : E < 1) (hI : 0 < I₀) (g : ℕ) :
    0 < noFeedback E I₀ g := by
  rw [noFeedback_eq]
  exact mul_pos hI (pow_pos (sub_pos.mpr hE) g)

theorem noFeedback_le_one {E I₀ : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (_hI0 : 0 ≤ I₀) (hI1 : I₀ ≤ 1) (g : ℕ) :
    noFeedback E I₀ g ≤ 1 := by
  rw [noFeedback_eq]
  have h1 : (1 - E) ^ g ≤ 1 := by
    calc (1 - E) ^ g ≤ (1 : ℝ) ^ g :=
          pow_le_pow_left₀ (sub_nonneg.mpr hE1) (by linarith) g
      _ = 1 := one_pow _
  calc I₀ * (1 - E) ^ g ≤ 1 * 1 :=
        mul_le_mul hI1 h1 (pow_nonneg (sub_nonneg.mpr hE1) g) zero_le_one
    _ = 1 := one_mul 1

theorem feedback_nonneg {E I₀ : ℝ} (hE : E ≤ 1) (hI : 0 ≤ I₀) (g : ℕ) :
    0 ≤ feedback E I₀ g := by
  induction g with
  | zero => exact hI
  | succ k ih =>
    rw [feedback_succ]
    exact mul_nonneg (sub_nonneg.mpr hE) (pow_nonneg ih 2)

theorem feedback_le_one {E I₀ : ℝ} (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hI0 : 0 ≤ I₀) (hI1 : I₀ ≤ 1) (g : ℕ) :
    feedback E I₀ g ≤ 1 := by
  induction g with
  | zero => exact hI1
  | succ k ih =>
    rw [feedback_succ]
    have h2 : feedback E I₀ k ^ 2 ≤ 1 := by
      calc feedback E I₀ k ^ 2 ≤ (1 : ℝ) ^ 2 :=
            pow_le_pow_left₀ (feedback_nonneg hE1 hI0 k) ih 2
        _ = 1 := one_pow _
    calc (1 - E) * feedback E I₀ k ^ 2 ≤ (1 - E) * 1 :=
          mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hE1)
      _ = 1 - E := mul_one _
      _ ≤ 1 := by linarith

end GoalDecay
