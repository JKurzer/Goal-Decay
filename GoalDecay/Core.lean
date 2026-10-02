import Mathlib

/-!
# Core — goal-content integrity decay, distilled

The parsimonious form of the whole investigation. One model, three theorems,
one escape. Self-contained: imports only Mathlib.

**Model.** `I g ∈ [0,1]` is goal-content integrity at generation `g`. Each
generation writes the next generation's storage (its weights) at fixed error
rate `E`, so per-generation retention is at most `q = 1 − E`. The writing
machinery — including the procedure that verifies the writing — is itself in
storage, to depth `k ≥ 1`, sharpening retention to at most `q · (I g)^k`
times what remains.

**Theorems.**

1. `retention_bound`, `retention_catastrophe` — decay is at least geometric,
   never slower than exponential, and every threshold is crossed in finite
   time. No floor.
2. `tower_closed`, `tower_upper`, `tower_catastrophe`, `law_catastrophe` —
   storage coupling makes it strictly super-geometric: every law at least as
   coupled as depth `k` is capped by the explicit tower
   `(1-E)·(I g)^k = ((1-E)·I₀^k)^((k+1)^g)` and catastrophizes.
3. `geometric_not_affine`, `linear_dies`, `linear_le_geometric` — the linear
   hypothesis is falsified: the geometric law is not affine, the affine
   approximation dies within `⌈1/E⌉` generations while the truth stays
   positive forever, and the linear candidate is dominated by the truth from
   generation 2 on (Bernoulli).

`goal_content_integrity` bundles the four headline conclusions into one
statement. The one escape (a floor) requires an exogenous anchor — retention
sourced from something that does not decay.
-/

namespace GoalDecayCore

/-- The tower: trajectory of the `k`-coupled recurrence
    `I (g+1) = (1-E) * (I g)^(k+1)`. -/
def tower (E I₀ : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => I₀
  | (g + 1) => (1 - E) * (tower E I₀ k g) ^ (k + 1)

@[simp] theorem tower_zero {E I₀ : ℝ} {k : ℕ} : tower E I₀ k 0 = I₀ := rfl

@[simp] theorem tower_succ {E I₀ : ℝ} {k : ℕ} (g : ℕ) :
    tower E I₀ k (g + 1) = (1 - E) * (tower E I₀ k g) ^ (k + 1) := rfl

/-- Auxiliary growth fact. -/
theorem two_pow_gt : ∀ g : ℕ, g < 2 ^ g := by
  intro g
  induction g with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

/-- Tower closed form, division-free:
    `(1-E) * (tower g)^k = ((1-E) * I₀^k)^((k+1)^g)`.
    For `I₀ = 1`: `tower g = (1-E)^(((k+1)^g − 1)/k)`. -/
theorem tower_closed (E I₀ : ℝ) (k : ℕ) (g : ℕ) :
    (1 - E) * (tower E I₀ k g) ^ k = ((1 - E) * I₀ ^ k) ^ ((k + 1) ^ g) := by
  induction g with
  | zero => simp [mul_comm]
  | succ j ih =>
    have h1 : (1 - E) * ((1 - E) * tower E I₀ k j ^ (k + 1)) ^ k
        = ((1 - E) * (tower E I₀ k j) ^ k) ^ (k + 1) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (k + 1) k, pow_succ]
      ring
    rw [tower_succ, h1, ih, ← pow_mul, ← pow_succ]

theorem tower_nonneg {E I₀ : ℝ} (hE : E ≤ 1) (hI : 0 ≤ I₀) (k g : ℕ) :
    0 ≤ tower E I₀ k g := by
  induction g with
  | zero => exact hI
  | succ j ih =>
    rw [tower_succ]
    exact mul_nonneg (sub_nonneg.mpr hE) (pow_nonneg ih (k + 1))

/-! ## I. Decay is at least geometric — never linear, no floor -/

/-- Any process that keeps at most a fixed fraction `q` of current integrity
    per generation decays geometrically. -/
theorem retention_bound {q I₀ : ℝ} (hq : 0 ≤ q) (I : ℕ → ℝ)
    (h0 : I 0 ≤ I₀) (hstep : ∀ g, I (g + 1) ≤ q * I g) :
    ∀ g, I g ≤ I₀ * q ^ g := by
  intro g
  induction g with
  | zero =>
    calc I 0 ≤ I₀ := h0
      _ = I₀ * q ^ 0 := by simp
  | succ j ih =>
    calc I (j + 1) ≤ q * I j := hstep j
      _ ≤ q * (I₀ * q ^ j) := mul_le_mul_of_nonneg_left ih hq
      _ = I₀ * q ^ (j + 1) := by rw [pow_succ]; ring

/-- …and therefore crosses every positive threshold in finite time. -/
theorem retention_catastrophe {q I₀ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hI0 : 0 < I₀)
    (I : ℕ → ℝ) (h0 : I 0 ≤ I₀) (hstep : ∀ g, I (g + 1) ≤ q * I g)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ g : ℕ, I g < τ := by
  obtain ⟨g, hg⟩ := exists_pow_lt_of_lt_one (div_pos hτ hI0) hq1
  refine ⟨g, ?_⟩
  have h2 : I₀ * q ^ g < I₀ * (τ / I₀) := mul_lt_mul_of_pos_left hg hI0
  rw [mul_div_cancel₀ τ (ne_of_gt hI0)] at h2
  exact lt_of_le_of_lt (retention_bound (le_of_lt hq0) I h0 hstep g) h2

/-! ## II. Storage coupling accelerates it super-geometrically -/

/-- Any law at least as coupled as depth `k` is capped by the tower. -/
theorem tower_upper {E I₀ : ℝ} (hE : E ≤ 1) (I : ℕ → ℝ) (k : ℕ)
    (h0 : I 0 ≤ I₀) (hpos : ∀ g, 0 ≤ I g)
    (hstep : ∀ g, I (g + 1) ≤ (1 - E) * (I g) ^ (k + 1)) :
    ∀ g, I g ≤ tower E I₀ k g := by
  intro g
  induction g with
  | zero => exact h0
  | succ j ih =>
    calc I (j + 1) ≤ (1 - E) * (I j) ^ (k + 1) := hstep j
      _ ≤ (1 - E) * (tower E I₀ k j) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos j) ih (k + 1))
            (sub_nonneg.mpr hE)
      _ = tower E I₀ k (j + 1) := (tower_succ j).symm

/-- Any law at most as coupled as depth `k` bounds the tower from above. -/
theorem tower_lower {E I₀ : ℝ} (hE : E ≤ 1) (hI0 : 0 ≤ I₀) (I : ℕ → ℝ) (k : ℕ)
    (h0 : I 0 = I₀) (hstep : ∀ g, (1 - E) * (I g) ^ (k + 1) ≤ I (g + 1)) :
    ∀ g, tower E I₀ k g ≤ I g := by
  intro g
  induction g with
  | zero => rw [h0]; exact le_refl _
  | succ j ih =>
    calc tower E I₀ k (j + 1) = (1 - E) * (tower E I₀ k j) ^ (k + 1) := tower_succ j
      _ ≤ (1 - E) * (I j) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (tower_nonneg hE hI0 k j) ih (k + 1))
            (sub_nonneg.mpr hE)
      _ ≤ I (j + 1) := hstep j

/-- The tower itself crosses every threshold in finite time — on a
    `log_{k+1}` timescale. -/
theorem tower_catastrophe {E I₀ : ℝ} (hE0 : 0 < E) (hE1 : E < 1)
    (hI0 : 0 < I₀) (hI1 : I₀ ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ g : ℕ, tower E I₀ k g < τ := by
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
  have h1 : (1 - E) * (tower E I₀ k g) ^ k ≤ c ^ g := by
    rw [tower_closed]
    simpa only [← hc] using hle
  have h2 : (1 - E) * (tower E I₀ k g) ^ k < τ ^ k * (1 - E) :=
    lt_of_le_of_lt h1 hg
  have h3 : (tower E I₀ k g) ^ k < τ ^ k := by
    by_contra hnot
    push Not at hnot
    have hle2 : τ ^ k * (1 - E) ≤ (tower E I₀ k g) ^ k * (1 - E) :=
      mul_le_mul_of_nonneg_right hnot (le_of_lt (sub_pos.mpr hE1))
    have hcomm : (1 - E) * (tower E I₀ k g) ^ k
        = (tower E I₀ k g) ^ k * (1 - E) := mul_comm _ _
    rw [hcomm] at h2
    exact absurd (lt_of_lt_of_le h2 hle2) (lt_irrefl _)
  by_contra hnot
  push Not at hnot
  have hle3 : τ ^ k ≤ (tower E I₀ k g) ^ k :=
    pow_le_pow_left₀ (le_of_lt hτ) hnot k
  exact absurd (lt_of_le_of_lt hle3 h3) (lt_irrefl _)

/-- **Uniformity**: every law at least as storage-coupled as depth `k ≥ 1`
    catastrophizes. -/
theorem law_catastrophe {E I₀ : ℝ} (hE0 : 0 < E) (hE1 : E < 1)
    (hI0 : 0 < I₀) (hI1 : I₀ ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    (I : ℕ → ℝ) (h0 : I 0 ≤ I₀) (hpos : ∀ g, 0 ≤ I g)
    (hstep : ∀ g, I (g + 1) ≤ (1 - E) * (I g) ^ (k + 1))
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ g : ℕ, I g < τ := by
  obtain ⟨g, hg⟩ := tower_catastrophe hE0 hE1 hI0 hI1 hk τ hτ
  exact ⟨g, lt_of_le_of_lt (tower_upper (le_of_lt hE1) I k h0 hpos hstep g) hg⟩

/-- Strict monotonicity of integer powers on nonnegatives, induction-only
    (no library-lemma roulette). -/
theorem pow_lt_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {n : ℕ} (hn : 1 ≤ n) :
    a ^ n < b ^ n := by
  induction n with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [pow_one, pow_one]
      exact hab
    · have ih' := ih (by omega)
      rw [pow_succ, pow_succ]
      calc a ^ j * a ≤ b ^ j * a :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha (le_of_lt hab) j) ha
        _ < b ^ j * b := mul_lt_mul_of_pos_left hab (pow_pos (lt_of_le_of_lt ha hab) j)

/-- **Survival threshold** (the dual of catastrophe), closed form: with
    `I₀ = 1`, integrity at horizon `G` is at least `τ` iff
    `(1-E)^((k+1)^G) ≥ (1-E)·τ^k`. Equivalently the tolerable error rate is
    `E* = 1 − τ^(k/((k+1)^G − 1)) ≈ k·ln(1/τ)/(k+1)^G` — a horizon function,
    not a constant: it shrinks double-exponentially in `G` under coupling,
    and no `E > 0` tolerates an unbounded horizon. -/
theorem survival_threshold {E : ℝ} (_hE0 : 0 < E) (hE1 : E < 1) {k : ℕ} (hk : 1 ≤ k)
    (G : ℕ) {τ : ℝ} (hτ0 : 0 < τ) (_hτ1 : τ ≤ 1) :
    tower E 1 k G ≥ τ ↔ (1 - E) ^ ((k + 1) ^ G) ≥ (1 - E) * τ ^ k := by
  have hq : (0 : ℝ) < 1 - E := sub_pos.mpr hE1
  have hcl := tower_closed E 1 k G
  rw [one_pow, mul_one] at hcl
  constructor
  · intro h
    rw [← hcl]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ0.le h k) (le_of_lt hq)
  · intro h
    rw [← hcl] at h
    by_contra hnot
    push Not at hnot
    have ht0 : 0 ≤ tower E 1 k G := tower_nonneg (le_of_lt hE1) zero_le_one k G
    have hlt : (tower E 1 k G) ^ k < τ ^ k := by
      rcases eq_or_lt_of_le ht0 with hz | hpos
      · rw [← hz]
        have hkk : k ≠ 0 := by omega
        rw [zero_pow hkk]
        exact pow_pos hτ0 k
      · exact pow_lt_of_lt (le_of_lt hpos) hnot hk
    have hlt2 : (1 - E) * (tower E 1 k G) ^ k < (1 - E) * τ ^ k :=
      mul_lt_mul_of_pos_left hlt hq
    exact absurd (lt_of_lt_of_le hlt2 h) (lt_irrefl _)

/-- **Meta-stability is a fuse, not a floor.** If failure has per-generation
    probability at least `p > 0` whenever it hasn't happened yet, survival
    probability obeys `S (g+1) ≤ (1-p)·S g`, decays geometrically
    (`retention_bound`), and eventual failure is certain
    (`retention_catastrophe`). Positive errors can stretch the fuse
    astronomically (`p` small, Kramers regime); they cannot remove it while
    `p > 0`. The budget for "effectively immortal": `G·p ≪ 1`
    (`linear_le_geometric`: `P(survive G) ≥ 1 − G·p`). -/
theorem metastability {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S : ℕ → ℝ)
    (h0 : S 0 ≤ 1) (hstep : ∀ g, S (g + 1) ≤ (1 - p) * S g) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℕ, S g < ε :=
  retention_catastrophe (sub_pos.mpr hp1) (by linarith) (by norm_num : (0 : ℝ) < 1)
    S h0 hstep ε hε

/-! ## III. Linear is not a model of any of this -/

/-- The geometric law is not affine: its second finite difference `I₀ E² q^g`
    never vanishes. -/
theorem geometric_not_affine {E I₀ : ℝ} (hE : E ≠ 0) (hI : I₀ ≠ 0) :
    ¬ ∃ a b : ℝ, ∀ g : ℕ, I₀ * (1 - E) ^ g = a + b * (g : ℝ) := by
  rintro ⟨a, b, h⟩
  have s1 : I₀ * (1 - E) ^ 0 - 2 * (I₀ * (1 - E) ^ 1) + I₀ * (1 - E) ^ 2 = 0 := by
    rw [h 0, h 1, h 2]; push_cast; ring
  have s2 : I₀ * E ^ 2 = 0 := by
    have hr : I₀ * E ^ 2
        = I₀ * (1 - E) ^ 0 - 2 * (I₀ * (1 - E) ^ 1) + I₀ * (1 - E) ^ 2 := by ring
    rw [hr]; exact s1
  exact mul_ne_zero hI (pow_ne_zero 2 hE) s2

/-- The affine approximation dies in finite time; the truth never does. -/
theorem linear_dies {E I₀ : ℝ} (hE : 0 < E) (hE1 : E < 1) (hI : 0 < I₀) :
    ∃ g : ℕ, I₀ - E * I₀ * (g : ℝ) ≤ 0 ∧ 0 < I₀ * (1 - E) ^ g := by
  obtain ⟨g, hg⟩ := exists_nat_ge (1 / E)
  have hEg : (1 : ℝ) ≤ E * (g : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hg (le_of_lt hE)
    rwa [one_div, mul_inv_cancel₀ (ne_of_gt hE)] at h1
  refine ⟨g, ?_, mul_pos hI (pow_pos (sub_pos.mpr hE1) g)⟩
  have h2 : (1 : ℝ) - E * (g : ℝ) ≤ 0 := by linarith
  calc I₀ - E * I₀ * (g : ℝ) = I₀ * (1 - E * (g : ℝ)) := by ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hI) h2

/-- Bernoulli: the linear candidate is dominated by the geometric truth. -/
theorem linear_le_geometric {E I₀ : ℝ} (hE1 : E ≤ 1) (hI0 : 0 ≤ I₀) (g : ℕ) :
    I₀ * (1 - (g : ℝ) * E) ≤ I₀ * (1 - E) ^ g := by
  have hb := one_add_mul_le_pow (a := -E) (by linarith : (-2 : ℝ) ≤ -E) g
  have h1 : (1 : ℝ) + (g : ℝ) * (-E) = 1 - (g : ℝ) * E := by ring
  have h2 : (1 : ℝ) + (-E) = 1 - E := by ring
  rw [h1, h2] at hb
  exact mul_le_mul_of_nonneg_left hb hI0

/-! ## The whole ballgame, one statement -/

/-- **Master theorem.** Every integrity sequence in the generous class —
    per-generation loss between "weights don't matter" and "depth-`k`
    coupling" — is trapped between the tower and the exponential envelope,
    crosses every threshold in finite time, and admits no affine model; the
    linear candidate is dominated by the envelope. -/
theorem goal_content_integrity {E I₀ : ℝ} (hE0 : 0 < E) (hE1 : E < 1)
    (hI0 : 0 < I₀) (_hI1 : I₀ ≤ 1) {k : ℕ} (_hk : 1 ≤ k)
    (I : ℕ → ℝ) (h0 : I 0 = I₀) (_hpos : ∀ g, 0 ≤ I g)
    (hlow : ∀ g, (1 - E) * (I g) ^ (k + 1) ≤ I (g + 1))
    (hhigh : ∀ g, I (g + 1) ≤ (1 - E) * I g) :
    (∀ g, tower E I₀ k g ≤ I g ∧ I g ≤ I₀ * (1 - E) ^ g)
      ∧ (∀ τ : ℝ, 0 < τ → ∃ g : ℕ, I g < τ)
      ∧ (¬ ∃ a b : ℝ, ∀ g : ℕ, I₀ * (1 - E) ^ g = a + b * (g : ℝ))
      ∧ (∀ g : ℕ, I₀ * (1 - (g : ℝ) * E) ≤ I₀ * (1 - E) ^ g) := by
  refine ⟨fun g => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact tower_lower (le_of_lt hE1) (le_of_lt hI0) I k h0 hlow g
  · exact retention_bound (sub_nonneg.mpr (le_of_lt hE1)) I (le_of_eq h0) hhigh g
  · intro τ hτ
    exact retention_catastrophe (sub_pos.mpr hE1) (by linarith) hI0 I
      (le_of_eq h0) hhigh τ hτ
  · exact geometric_not_affine (ne_of_gt hE0) (ne_of_gt hI0)
  · intro g
    exact linear_le_geometric (le_of_lt hE1) (le_of_lt hI0) g

end GoalDecayCore
