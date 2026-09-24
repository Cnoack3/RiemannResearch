import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeErrorInverseLogSq

/-! Inverse-fourth-log weakening of the established MediumPNT estimate.
Source: square the existing inverse-square-log exponential comparison, then
use the established MediumPNT estimate. No new arithmetic hypothesis. -/

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

lemma Quantitative.exp_log_tenth_eventually_le_inverseLogFourth
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) ≤
        16 / (1 + Real.log x) ^ 4 := by
  filter_upwards [exp_log_tenth_eventually_le_inverseLogSq (half_pos hc)] with x hx
  have hs := mul_le_mul hx hx
    (Real.exp_pos (-(c / 2) * (Real.log x) ^ ((1 : ℝ) / 10))).le
    (show 0 ≤ 4 / (1 + Real.log x) ^ 2 by positivity)
  have he :
      Real.exp (-(c / 2) * (Real.log x) ^ ((1 : ℝ) / 10)) *
        Real.exp (-(c / 2) * (Real.log x) ^ ((1 : ℝ) / 10)) =
      Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hs
  calc
    _ ≤ (4 / (1 + Real.log x) ^ 2) * (4 / (1 + Real.log x) ^ 2) := hs
    _ = 16 / (1 + Real.log x) ^ 4 := by
      rw [div_mul_div_comm, ← pow_add]
      norm_num

theorem R_inverseLogFourth_bound_of_medium
    (hMedium : ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |R y| ≤ C * y / (1 + Real.log y) ^ 4 := by
  obtain ⟨c, hc, hmedium⟩ := hMedium
  obtain ⟨A, hA, hAbound⟩ := hmedium.exists_pos
  have htail : ∀ᶠ y : ℝ in atTop,
      |R y| ≤ (16 * A) * y / (1 + Real.log y) ^ 4 := by
    have hAbound' : ∀ᶠ y : ℝ in atTop,
        ‖Chebyshev.psi y - y‖ ≤
          A * ‖y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))‖ := by
      simpa only [Asymptotics.IsBigOWith, Pi.sub_apply, id_eq] using hAbound
    filter_upwards [hAbound',
      Quantitative.exp_log_tenth_eventually_le_inverseLogFourth hc,
      eventually_ge_atTop (1 : ℝ)] with y hbound hdecay hy
    have hy0 : 0 ≤ y := le_trans zero_le_one hy
    have hbound' : |R y| ≤
        A * (y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))) := by
      simpa only [R, Psi, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hy0 (Real.exp_pos _).le)] using hbound
    calc
      |R y| ≤ A * (y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))) := hbound'
      _ ≤ A * (y * (16 / (1 + Real.log y) ^ 4)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdecay hy0) hA.le
      _ = (16 * A) * y / (1 + Real.log y) ^ 4 := by ring
  obtain ⟨T, hT⟩ := eventually_atTop.mp htail
  let B : ℝ := max 1 T
  have hB : 1 ≤ B := le_max_left _ _
  obtain ⟨K, hKbound⟩ := R_locally_bounded B (le_trans zero_le_one hB)
  have hK : 0 ≤ K :=
    (abs_nonneg (R 0)).trans
      (hKbound 0 ⟨le_rfl, le_trans zero_le_one hB⟩)
  let C : ℝ := max (16 * A) (K * (1 + Real.log B) ^ 4)
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have hden : 0 < (1 + Real.log y) ^ 4 := by
    have := Real.log_nonneg hy
    positivity
  by_cases hTy : T ≤ y
  · exact (hT y hTy).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0) hden.le)
  · have hyB : y ≤ B := (lt_of_not_ge hTy).le.trans (le_max_right _ _)
    have hlog : Real.log y ≤ Real.log B :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one hy) hyB
    have hlogsq : (1 + Real.log y) ^ 4 ≤ (1 + Real.log B) ^ 4 := by
      have := Real.log_nonneg hy
      gcongr <;> first | exact hlog | exact hyB | positivity
    apply (le_div_iff₀ hden).2
    calc
      |R y| * (1 + Real.log y) ^ 4 ≤ K * (1 + Real.log y) ^ 4 :=
        mul_le_mul_of_nonneg_right (hKbound y ⟨hy0, hyB⟩) hden.le
      _ ≤ K * (1 + Real.log B) ^ 4 :=
        mul_le_mul_of_nonneg_left hlogsq hK
      _ ≤ C := le_max_right _ _
      _ ≤ C * y := le_mul_of_one_le_right hC.le hy

theorem R_inverseLogFourth_bound :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |R y| ≤ C * y / (1 + Real.log y) ^ 4 :=
  R_inverseLogFourth_bound_of_medium Quantitative.MediumPNT

end RiemannResearch.NumberTheory.PrimeNumberTheorem
