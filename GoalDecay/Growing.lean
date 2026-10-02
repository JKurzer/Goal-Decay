import GoalDecay.Stronger

/-!
# Growing — the verification stack deepens every generation

The `k`-coupled family (`feedbackPow`) assumes a *constant* coupling depth.
But each generation's checking procedure is itself written into storage, so
generation `g` must keep intact not only the goal content but the checkers of
checkers, one more level per generation: the coupling exponent is a growing
function `m g` of the generation.

  `I (g+1) = (1 - E) * (I g)^(m g)`,   `m i ≥ 2`.

With `m i = i + 2` (one more stored level per generation) the exponent of the
initial integrity is `P g = (g+1)!` — factorial, i.e. *at least* `(g/e)^g` by
Stirling ("x^x at least"), and faster-growing `m` gives towers beyond that.
The results here are generic in `m`:

* `feedbackGrow_eq` — exact closed form for any stack-growth `m`:
  `I g = I₀^(P g) * (1-E)^(R g)` with `P (g+1) = m g * P g`,
  `R (g+1) = m g * R g + 1`.
* `growR_ge` — `R g ≥ g` whenever `m i ≥ 2`.
* `growP_factorial` — `m i = i+2` gives `P g = (g+1)!`.
* `feedbackGrow_catastrophe` — for **any** `m ≥ 2`, integrity falls below any
  positive threshold within finitely many generations.
* Numeral anchor points at `E = 0.091` (`gen_two_*`, `grow_fact_gen3`):
  constant coupling `k = 6` already fails (< 1/2 integrity) at generation 2;
  `k = 5` does not. Factorial stack fails by generation 3.
-/

namespace GoalDecay

/-- Growing-stack feedback: at generation `g`, faithful transcription requires
    `m g` nested levels of stored machinery to be intact. -/
def feedbackGrow (E I₀ : ℝ) (m : ℕ → ℕ) : ℕ → ℝ
  | 0 => I₀
  | (g + 1) => (1 - E) * (feedbackGrow E I₀ m g) ^ (m g)

/-- Exponent of the initial integrity: product of stack depths. -/
def growP (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | (g + 1) => m g * growP m g

/-- Exponent of the transcription factor: accumulated correction terms. -/
def growR (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (g + 1) => m g * growR m g + 1

@[simp] theorem feedbackGrow_zero {E I₀ : ℝ} {m : ℕ → ℕ} :
    feedbackGrow E I₀ m 0 = I₀ := rfl

@[simp] theorem growP_zero {m : ℕ → ℕ} : growP m 0 = 1 := rfl

@[simp] theorem growR_zero {m : ℕ → ℕ} : growR m 0 = 0 := rfl

@[simp] theorem feedbackGrow_succ {E I₀ : ℝ} {m : ℕ → ℕ} (g : ℕ) :
    feedbackGrow E I₀ m (g + 1)
      = (1 - E) * (feedbackGrow E I₀ m g) ^ (m g) := rfl

@[simp] theorem growP_succ {m : ℕ → ℕ} (g : ℕ) :
    growP m (g + 1) = m g * growP m g := rfl

@[simp] theorem growR_succ {m : ℕ → ℕ} (g : ℕ) :
    growR m (g + 1) = m g * growR m g + 1 := rfl

/-- Exact closed form for any stack growth. -/
theorem feedbackGrow_eq (E I₀ : ℝ) (m : ℕ → ℕ) (g : ℕ) :
    feedbackGrow E I₀ m g = I₀ ^ (growP m g) * (1 - E) ^ (growR m g) := by
  induction g with
  | zero => simp
  | succ j ih =>
    rw [feedbackGrow_succ, ih, mul_pow, ← pow_mul, ← pow_mul]
    have eP : growP m j * m j = m j * growP m j := Nat.mul_comm _ _
    have eR : growR m j * m j = m j * growR m j := Nat.mul_comm _ _
    rw [eP, eR, growP_succ]
    have hR : (1 - E) ^ (growR m (j + 1))
        = (1 - E) ^ (m j * growR m j) * (1 - E) := by
      rw [growR_succ, pow_add, pow_one]
    rw [hR]
    ring

/-- The correction exponent outruns the generation count. -/
theorem growR_ge (m : ℕ → ℕ) (hm : ∀ i, 2 ≤ m i) : ∀ g, g ≤ growR m g := by
  intro g
  induction g with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    rw [growR_succ]
    have hle : 2 * growR m j ≤ m j * growR m j :=
      Nat.mul_le_mul (hm j) le_rfl
    omega

/-- One more stored level per generation gives the factorial regime. -/
theorem growP_factorial (g : ℕ) :
    growP (fun i => i + 2) g = Nat.factorial (g + 1) := by
  induction g with
  | zero => rfl
  | succ j ih =>
    simp only [growP_succ]
    rw [ih, Nat.factorial_succ (j + 1), Nat.factorial_succ j]

/-- **Catastrophe for every stack growth** `m ≥ 2`: finite-time crossing of any
    positive threshold. The exponent `P g` can be factorial or worse; the
    conclusion only needs `R g ≥ g`. -/
theorem feedbackGrow_catastrophe {E I₀ : ℝ} (hE0 : 0 < E) (hE1 : E < 1)
    (hI0 : 0 < I₀) (hI1 : I₀ ≤ 1) (m : ℕ → ℕ) (hm : ∀ i, 2 ≤ m i)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ g : ℕ, feedbackGrow E I₀ m g < τ := by
  have hq : (0 : ℝ) < 1 - E := sub_pos.mpr hE1
  obtain ⟨g, hg⟩ := exists_pow_lt_of_lt_one hτ (by linarith : 1 - E < 1)
  refine ⟨g, ?_⟩
  rw [feedbackGrow_eq]
  have hP : I₀ ^ (growP m g) ≤ 1 := by
    calc I₀ ^ (growP m g) ≤ (1 : ℝ) ^ (growP m g) :=
          pow_le_pow_left₀ (le_of_lt hI0) hI1 _
      _ = 1 := one_pow _
  have hqR : (1 - E) ^ (growR m g) ≤ (1 - E) ^ g :=
    pow_le_pow_of_le_one (le_of_lt hq) (by linarith) (growR_ge m hm g)
  calc I₀ ^ (growP m g) * (1 - E) ^ (growR m g)
      ≤ 1 * (1 - E) ^ g :=
        mul_le_mul hP hqR (pow_nonneg (le_of_lt hq) _) zero_le_one
    _ = (1 - E) ^ g := one_mul _
    _ < τ := hg

/-! ### Concrete anchor points at `E = 0.091` -/

/-- With constant coupling `k`, generation-2 integrity is exactly `(1-E)^(k+2)`. -/
theorem feedbackPow_two (E : ℝ) (k : ℕ) :
    feedbackPow E 1 k 2 = (1 - E) ^ (k + 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, feedbackPow_succ,
    show (1 : ℕ) = 0 + 1 from rfl, feedbackPow_succ, feedbackPow_zero,
    one_pow, mul_one, show k + 2 = (k + 1) + 1 from rfl, pow_succ]
  ring

/-- At `E = 9.1%`, constant coupling `k = 6` fails (< 1/2) at generation 2. -/
theorem gen_two_k6_fails : feedbackPow (0.091 : ℝ) 1 6 2 < 0.5 := by
  rw [feedbackPow_two]
  norm_num

/-- At `E = 9.1%`, constant coupling `k = 5` still passes at generation 2.
    The gen-2 failure threshold is therefore exactly `k = 6`. -/
theorem gen_two_k5_passes : ¬ feedbackPow (0.091 : ℝ) 1 5 2 < 0.5 := by
  rw [feedbackPow_two]
  norm_num

/-- Factorial stack (`m i = i+2`) at `E = 9.1%`: below 1/5 by generation 3
    (`I 3 = 0.909^17 ≈ 0.198`). -/
theorem grow_fact_gen3 : feedbackGrow (0.091 : ℝ) 1 (fun i => i + 2) 3 < 0.2 := by
  rw [feedbackGrow_eq]
  norm_num [growP, growR]

end GoalDecay
