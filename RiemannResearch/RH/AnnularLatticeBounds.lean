import RiemannResearch.RH.AnnularLatticeCorrection

/-!
# Sharp bound for the annular lattice remainder
The complete signed Bernoulli combination reduces to eight cubic pieces.
The rational factor certificate proves the optimal constant without numerical
sampling. Sources: the annular-weight calculation and DLMF 24.4(ii),(iii) for
the classical Bernoulli symmetry and polynomial-sum context.
-/
noncomputable section
namespace RiemannResearch.RH

private lemma fract_nat_mul (d : ℕ) (x : ℝ) :
    Int.fract ((d : ℝ) * x) = Int.fract ((d : ℝ) * Int.fract x) := by
  apply Int.fract_eq_fract.mpr
  refine ⟨(d : ℤ) * Int.floor x, ?_⟩
  simp only [Int.cast_mul, Int.cast_natCast, Int.fract]
  ring

private lemma fract_on_Ico (x : ℝ) (k : ℤ)
    (h₀ : (k : ℝ) ≤ x) (h₁ : x < (k : ℝ) + 1) :
    Int.fract x = x - (k : ℝ) := by
  rw [Int.fract, Int.floor_eq_iff.mpr ⟨h₀, h₁⟩]

private def bernstein (a b c d t : ℝ) : ℝ :=
  a * (1 - t) ^ 3 + b * (3 * t * (1 - t) ^ 2) +
    c * (3 * t ^ 2 * (1 - t)) + d * t ^ 3

private lemma bernstein_bounds (a b c d lo hi t : ℝ)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi)
    (hc : lo ≤ c ∧ c ≤ hi) (hd : lo ≤ d ∧ d ≤ hi) :
    lo ≤ bernstein a b c d t ∧ bernstein a b c d t ≤ hi := by
  have hu : 0 ≤ 1 - t := by linarith
  have hw₀ : 0 ≤ (1 - t) ^ 3 := by positivity
  have hw₁ : 0 ≤ 3 * t * (1 - t) ^ 2 := by positivity
  have hw₂ : 0 ≤ 3 * t ^ 2 * (1 - t) := by positivity
  have hw₃ : 0 ≤ t ^ 3 := by positivity
  have hsum : (1 - t) ^ 3 + (3 * t * (1 - t) ^ 2) +
      (3 * t ^ 2 * (1 - t)) + t ^ 3 = 1 := by ring
  constructor
  · calc
      lo = lo * ((1 - t) ^ 3 + (3 * t * (1 - t) ^ 2) +
          (3 * t ^ 2 * (1 - t)) + t ^ 3) := by rw [hsum]; ring
      _ = lo * (1 - t) ^ 3 + lo * (3 * t * (1 - t) ^ 2) +
          lo * (3 * t ^ 2 * (1 - t)) + lo * t ^ 3 := by ring
      _ ≤ bernstein a b c d t :=
        add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right ha.1 hw₀)
          (mul_le_mul_of_nonneg_right hb.1 hw₁))
          (mul_le_mul_of_nonneg_right hc.1 hw₂))
          (mul_le_mul_of_nonneg_right hd.1 hw₃)
  · calc
      bernstein a b c d t ≤ hi * (1 - t) ^ 3 + hi * (3 * t * (1 - t) ^ 2) +
          hi * (3 * t ^ 2 * (1 - t)) + hi * t ^ 3 :=
        add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right ha.2 hw₀)
          (mul_le_mul_of_nonneg_right hb.2 hw₁))
          (mul_le_mul_of_nonneg_right hc.2 hw₂))
          (mul_le_mul_of_nonneg_right hd.2 hw₃)
      _ = hi * ((1 - t) ^ 3 + (3 * t * (1 - t) ^ 2) +
          (3 * t ^ 2 * (1 - t)) + t ^ 3) := by ring
      _ = hi := by rw [hsum]; ring

private def q0 (t : ℝ) : ℝ := -21 * t ^ 3 / 64
private def q1 (t : ℝ) : ℝ := -3 * (7 + 21 * t - 43 * t ^ 2 + 7 * t ^ 3) / 64
private def q2 (t : ℝ) : ℝ := -3 * (-8 - 44 * t + 26 * t ^ 2 + 7 * t ^ 3) / 64
private def q3 (t : ℝ) : ℝ := -3 * (t - 1) * (19 - 10 * t + 7 * t ^ 2) / 64

private lemma q0_bounds (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    -(10 / 9) ≤ q0 t ∧ q0 t ≤ 10 / 9 := by
  have h := bernstein_bounds 0 0 0 (-21 / 64) (-21 / 64) 0 t ht₀ ht₁
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have heq : bernstein 0 0 0 (-21 / 64) t = q0 t := by
    unfold bernstein q0; ring
  rw [heq] at h
  constructor <;> linarith [h.1, h.2]

private lemma q1_bounds (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    -(10 / 9) ≤ q1 t ∧ q1 t ≤ 10 / 9 := by
  have h := bernstein_bounds (-21 / 64) (-21 / 32) (-5 / 16) (3 / 8)
    (-21 / 32) (3 / 8) t ht₀ ht₁
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have heq : bernstein (-21 / 64) (-21 / 32) (-5 / 16) (3 / 8) t = q1 t := by
    unfold bernstein q1; ring
  rw [heq] at h
  constructor <;> linarith [h.1, h.2]

private lemma q2_bounds (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    -(10 / 9) ≤ q2 t ∧ q2 t ≤ 10 / 9 := by
  have h := bernstein_bounds (3 / 8) (17 / 16) (43 / 32) (57 / 64)
    0 2 t ht₀ ht₁
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have heq : bernstein (3 / 8) (17 / 16) (43 / 32) (57 / 64) t = q2 t := by
    unfold bernstein q2; ring
  rw [heq] at h
  have hfactor : 10 / 9 - q2 t = (3 * t - 2) ^ 2 * (106 + 21 * t) / 576 := by
    unfold q2; ring
  have hn : 0 ≤ (3 * t - 2) ^ 2 * (106 + 21 * t) / 576 := by positivity
  constructor <;> linarith [h.1]

private lemma q3_bounds (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    -(10 / 9) ≤ q3 t ∧ q3 t ≤ 10 / 9 := by
  have h := bernstein_bounds (57 / 64) (7 / 16) (1 / 4) 0
    0 (57 / 64) t ht₀ ht₁
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have heq : bernstein (57 / 64) (7 / 16) (1 / 4) 0 t = q3 t := by
    unfold bernstein q3; ring
  rw [heq] at h
  constructor <;> linarith [h.1, h.2]

/- The eight interval branches below are generated from the same exact floor formula.
   All endpoints are included using the half-open interval [k,k+1). -/
private lemma annularLatticeNumerator_bounds_on_eight (y : ℝ) (hy₀ : 0 ≤ y) (hy₈ : y < 8) :
    -(10 / 9) ≤ annularLatticeNumerator y ∧ annularLatticeNumerator y ≤ 10 / 9 := by
  by_cases h₁ : y < 1
  · have heq : annularLatticeNumerator y = q0 y := by
      unfold annularLatticeNumerator annularBernoulliCubic q0
      rw [fract_on_Ico y 0 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 2) 0 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 4) 0 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 8) 0 (by norm_num; linarith) (by norm_num; linarith)]
      norm_num; ring
    rw [heq]
    exact q0_bounds y hy₀ (by linarith)
  have hy₁ : 1 ≤ y := le_of_not_gt h₁
  by_cases h₂ : y < 2
  · have heq : annularLatticeNumerator y = q1 (y - 1) := by
      unfold annularLatticeNumerator annularBernoulliCubic q1
      rw [fract_on_Ico y 1 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 2) 0 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 4) 0 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 8) 0 (by norm_num; linarith) (by norm_num; linarith)]
      norm_num; ring
    rw [heq]
    exact q1_bounds (y - 1) (by linarith) (by linarith)
  have hy₂ : 2 ≤ y := le_of_not_gt h₂
  by_cases h₃ : y < 3
  · have heq : annularLatticeNumerator y = q2 (y - 2) := by
      unfold annularLatticeNumerator annularBernoulliCubic q2
      rw [fract_on_Ico y 2 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 2) 1 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 4) 0 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 8) 0 (by norm_num; linarith) (by norm_num; linarith)]
      norm_num; ring
    rw [heq]
    exact q2_bounds (y - 2) (by linarith) (by linarith)
  have hy₃ : 3 ≤ y := le_of_not_gt h₃
  by_cases h₄ : y < 4
  · have heq : annularLatticeNumerator y = q3 (y - 3) := by
      unfold annularLatticeNumerator annularBernoulliCubic q3
      rw [fract_on_Ico y 3 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 2) 1 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 4) 0 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 8) 0 (by norm_num; linarith) (by norm_num; linarith)]
      norm_num; ring
    rw [heq]
    exact q3_bounds (y - 3) (by linarith) (by linarith)
  have hy₄ : 4 ≤ y := le_of_not_gt h₄
  by_cases h₅ : y < 5
  · have heq : annularLatticeNumerator y = -q3 (5 - y) := by
      unfold annularLatticeNumerator annularBernoulliCubic q3
      rw [fract_on_Ico y 4 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 2) 2 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 4) 1 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 8) 0 (by norm_num; linarith) (by norm_num; linarith)]
      norm_num; ring
    rw [heq]
    have h := q3_bounds (5 - y) (by linarith) (by linarith)
    constructor <;> linarith [h.1, h.2]
  have hy₅ : 5 ≤ y := le_of_not_gt h₅
  by_cases h₆ : y < 6
  · have heq : annularLatticeNumerator y = -q2 (6 - y) := by
      unfold annularLatticeNumerator annularBernoulliCubic q2
      rw [fract_on_Ico y 5 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 2) 2 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 4) 1 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 8) 0 (by norm_num; linarith) (by norm_num; linarith)]
      norm_num; ring
    rw [heq]
    have h := q2_bounds (6 - y) (by linarith) (by linarith)
    constructor <;> linarith [h.1, h.2]
  have hy₆ : 6 ≤ y := le_of_not_gt h₆
  by_cases h₇ : y < 7
  · have heq : annularLatticeNumerator y = -q1 (7 - y) := by
      unfold annularLatticeNumerator annularBernoulliCubic q1
      rw [fract_on_Ico y 6 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 2) 3 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 4) 1 (by norm_num; linarith) (by norm_num; linarith),
        fract_on_Ico (y / 8) 0 (by norm_num; linarith) (by norm_num; linarith)]
      norm_num; ring
    rw [heq]
    have h := q1_bounds (7 - y) (by linarith) (by linarith)
    constructor <;> linarith [h.1, h.2]
  have hy₇ : 7 ≤ y := le_of_not_gt h₇
  have heq : annularLatticeNumerator y = -q0 (8 - y) := by
    unfold annularLatticeNumerator annularBernoulliCubic q0
    rw [fract_on_Ico y 7 (by norm_num; linarith) (by norm_num; linarith),
      fract_on_Ico (y / 2) 3 (by norm_num; linarith) (by norm_num; linarith),
      fract_on_Ico (y / 4) 1 (by norm_num; linarith) (by norm_num; linarith),
      fract_on_Ico (y / 8) 0 (by norm_num; linarith) (by norm_num; linarith)]
    norm_num; ring
  rw [heq]
  have h := q0_bounds (8 - y) (by linarith) (by linarith)
  constructor <;> linarith [h.1, h.2]

private lemma annularLatticeNumerator_reduce (x : ℝ) : annularLatticeNumerator x = annularLatticeNumerator (8 * Int.fract (x / 8)) := by
  have h8 := fract_nat_mul 8 (x / 8)
  have h4 := fract_nat_mul 4 (x / 8)
  have h2 := fract_nat_mul 2 (x / 8)
  norm_num at h8 h4 h2
  have e8 : (8 : ℝ) * (x / 8) = x := by ring
  have e4 : (4 : ℝ) * (x / 8) = x / 2 := by ring
  have e2 : (2 : ℝ) * (x / 8) = x / 4 := by ring
  rw [e8] at h8
  rw [e4] at h4
  rw [e2] at h2
  have er4 : 8 * Int.fract (x / 8) / 2 = 4 * Int.fract (x / 8) := by ring
  have er2 : 8 * Int.fract (x / 8) / 4 = 2 * Int.fract (x / 8) := by ring
  have er1 : 8 * Int.fract (x / 8) / 8 = Int.fract (x / 8) := by ring
  unfold annularLatticeNumerator
  rw [h8, h4, h2, er4, er2, er1, Int.fract_fract]

theorem annularLatticeNumerator_abs_le (x : ℝ) : |annularLatticeNumerator x| ≤ 10 / 9 := by
  rw [annularLatticeNumerator_reduce x]
  apply abs_le.mpr
  apply annularLatticeNumerator_bounds_on_eight
  · exact mul_nonneg (by norm_num) (Int.fract_nonneg _)
  · have h := Int.fract_lt_one (x / 8)
    linarith

theorem annularLatticeNumerator_at_eight_thirds : annularLatticeNumerator (8 / 3) = 10 / 9 := by
  unfold annularLatticeNumerator annularBernoulliCubic
  rw [fract_on_Ico (8 / 3) 2 (by norm_num) (by norm_num),
    fract_on_Ico (8 / 3 / 2) 1 (by norm_num) (by norm_num),
    fract_on_Ico (8 / 3 / 4) 0 (by norm_num) (by norm_num),
    fract_on_Ico (8 / 3 / 8) 0 (by norm_num) (by norm_num)]
  norm_num


/-- Sharp all-positive-real-cutoff decay for the complete lattice correction. -/
theorem annularLatticeFinite_abs_le {x : ℝ} (hx : 0 < x) :
    |annularLatticeFinite (Finset.Icc 1 (Nat.floor x)) x| ≤ 10/(27*x^2) := by
  rw [annularLatticeFinite_eq_bernoulli hx, abs_div,
    abs_of_pos (by positivity : 0 < 3*x^2)]
  calc
    |annularLatticeNumerator x|/(3*x^2) ≤ (10/9)/(3*x^2) :=
      div_le_div_of_nonneg_right (annularLatticeNumerator_abs_le x) (by positivity)
    _ = 10/(27*x^2) := by ring

theorem annularLatticeFinite_sharp_value :
    annularLatticeFinite (Finset.Icc 1 (Nat.floor (8/3:ℝ))) (8/3) = 5/96 := by
  rw [annularLatticeFinite_eq_bernoulli (by norm_num),
    annularLatticeNumerator_at_eight_thirds]
  norm_num

/-- No smaller global coefficient can replace 10/27. -/
theorem annularLatticeFinite_constant_optimal {C : ℝ}
    (hC : ∀ x : ℝ, 0 < x →
      |annularLatticeFinite (Finset.Icc 1 (Nat.floor x)) x| ≤ C/x^2) :
    (10/27:ℝ) ≤ C := by
  have h := hC (8/3) (by norm_num)
  rw [annularLatticeFinite_sharp_value] at h
  norm_num at h
  linarith

end RiemannResearch.RH
