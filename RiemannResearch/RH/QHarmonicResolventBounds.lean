import RiemannResearch.RH.QHarmonicResolventApproximation
import RiemannResearch.RH.FeedbackSmoothing

/-! # Bounds for the smaller sign of the actual harmonic approximants -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QSquarefreeDisplacementResolvent

private theorem minimumHarmonicPrefixOf_nonneg (u : QHilbert) (X : ℕ) :
    0 ≤ minimumHarmonicPrefixOf u X := by
  have h (ε : ℝ) : 0 ≤ harmonicSideOf u ε X :=
    Finset.sum_nonneg (fun n _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n))
  exact le_min (h 1) (h (-1))

theorem twice_minimumHarmonicPrefixOf_le (u : QHilbert) (X : ℕ) :
    2 * minimumHarmonicPrefixOf u X ≤ Real.sqrt (zetaTwo * (X : ℝ)) * ‖u‖ := by
  rw [twice_minimumHarmonicPrefixOf, Real.sqrt_mul zetaTwo_pos.le,
    mul_comm (Real.sqrt zetaTwo) (Real.sqrt (X : ℝ))]
  exact (sub_le_self _ (abs_nonneg _)).trans (harmonicAbsPrefix_le_sqrt u X)

/-- Unconditional size bound valid simultaneously at every depth and cutoff. -/
theorem harmonic_resolvent_size_le (X j : ℕ) :
    2 * minimumHarmonicPrefixOf (resolventApprox j) X ≤
      Real.sqrt (zetaTwo * (X : ℝ)) * ((1+(1/3 : ℝ)^j) * ‖displacement‖) := by
  apply (twice_minimumHarmonicPrefixOf_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have htri : ‖resolventApprox j‖ ≤ ‖displacement‖ + ‖displacement-resolventApprox j‖ := by
    simpa using norm_sub_le displacement (displacement-resolventApprox j)
  linarith only [htri, resolvent_error_norm_le j, show
    (1+(1/3 : ℝ)^j) * ‖displacement‖ =
      ‖displacement‖ + (1/3 : ℝ)^j * ‖displacement‖ by ring]

/-- The complementary source gives an extra inverse square root of the depth
in the error on the signed harmonic minimum. -/
theorem harmonic_resolvent_sqrt_depth (X j : ℕ) :
    2 * Real.sqrt ((j:ℝ)+1) *
        |minimumHarmonicPrefix X - minimumHarmonicPrefixOf (resolventApprox j) X| ≤
      Real.sqrt (zetaTwo * (X : ℝ)) * ((1/3 : ℝ)^j * ‖limitingResidual‖) := by
  have he : |minimumHarmonicPrefix X - minimumHarmonicPrefixOf (resolventApprox j) X| ≤
      Real.sqrt (zetaTwo * (X : ℝ)) * ‖displacement - resolventApprox j‖ := by
    rw [Real.sqrt_mul zetaTwo_pos.le, mul_comm (Real.sqrt zetaTwo) (Real.sqrt (X : ℝ))]
    exact minimumHarmonicPrefixOf_error displacement (resolventApprox j) X
  calc
    _ ≤ (2 * Real.sqrt ((j:ℝ)+1)) *
        (Real.sqrt (zetaTwo * (X:ℝ)) * ‖displacement - resolventApprox j‖) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = Real.sqrt (zetaTwo * (X : ℝ)) *
        (2 * Real.sqrt ((j:ℝ)+1) * ‖displacement - resolventApprox j‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (resolvent_error_sqrt_depth j) (Real.sqrt_nonneg _)

/-- For any adaptively deep schedule the unconditional baseline improves to
little-o of the square root of the cutoff. -/
theorem harmonic_resolvent_adaptive_div_sqrt_tendsto_zero (j : ℕ → ℕ)
    (hj : ∀ X, X ≤ 9^(j X)) :
    Tendsto (fun X : ℕ => minimumHarmonicPrefixOf (resolventApprox (j X)) X /
      Real.sqrt (X : ℝ)) atTop (𝓝 0) := by
  let D := Real.sqrt zetaTwo * ‖displacement‖
  have hrt : Tendsto (fun X : ℕ => Real.sqrt (X : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have ht := minimumHarmonicPrefix_div_sqrt_tendsto_zero.add (hrt.const_div_atTop D)
  rw [add_zero] at ht
  apply squeeze_zero
    (fun X => div_nonneg (minimumHarmonicPrefixOf_nonneg _ _) (Real.sqrt_nonneg _)) _ ht
  intro X
  change _ ≤ minimumHarmonicPrefix X / Real.sqrt (X:ℝ) + D / Real.sqrt (X:ℝ)
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have he := (abs_le.mp (harmonic_resolvent_adaptive_error X (j X) (hj X))).1
  change -D ≤ _ at he
  linarith

private theorem harmonic_window_factor (X j : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hX : (X:ℝ) ≤ K * (9:ℝ)^j) :
    Real.sqrt (zetaTwo * (X:ℝ)) * (1/3 : ℝ)^j ≤ Real.sqrt zetaTwo * Real.sqrt K := by
  have heq : (9 : ℝ)^j = ((3 : ℝ)^j)^2 := by
    rw [show (9 : ℝ) = 3^2 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul]
  have hroot := Real.sqrt_le_sqrt hX
  rw [Real.sqrt_mul hK, heq, Real.sqrt_sq (by positivity)] at hroot
  rw [Real.sqrt_mul zetaTwo_pos.le, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [one_div, inv_pow, ← div_eq_mul_inv]
  exact (div_le_iff₀ (by positivity)).mpr hroot

/-- On the geometric window the physical prefix error now tends to zero as the
depth increases, with a quantitative 1 / sqrt(j + 1) bound. -/
theorem harmonic_geometric_error_sqrt_depth (X j : ℕ) (hX : X ≤ 9^j) :
    2 * Real.sqrt ((j:ℝ)+1) *
        |minimumHarmonicPrefix X - minimumHarmonicPrefixOf (resolventApprox j) X| ≤
      Real.sqrt zetaTwo * ‖limitingResidual‖ := by
  apply (harmonic_resolvent_sqrt_depth X j).trans
  have hc : (X:ℝ) ≤ (9:ℝ)^j := by exact_mod_cast hX
  have hf := harmonic_window_factor X j (K := 1) (by norm_num) (by simpa only [one_mul] using hc)
  rw [Real.sqrt_one, mul_one] at hf
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hf (norm_nonneg _)

/-- One more factor j + 1 in the physical window still costs a constant. -/
theorem harmonic_expanded_window_error (X j : ℕ) (hX : X ≤ (j+1)*9^j) :
    2 * |minimumHarmonicPrefix X - minimumHarmonicPrefixOf (resolventApprox j) X| ≤
      Real.sqrt zetaTwo * ‖limitingResidual‖ := by
  have hc : (X:ℝ) ≤ ((j:ℝ)+1) * (9:ℝ)^j := by exact_mod_cast hX
  have hf := harmonic_window_factor X j (K := (j:ℝ)+1) (by positivity) hc
  have he := harmonic_resolvent_sqrt_depth X j
  have hp := mul_le_mul_of_nonneg_right hf (norm_nonneg limitingResidual)
  have hs : 0 < Real.sqrt ((j:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  by_contra h
  have hh := mul_lt_mul_of_pos_left (lt_of_not_ge h) hs
  nlinarith only [he, hp, hh]

/-- A cofinal polylog estimate may now be tested with X up to (j+1) 9^j. -/
theorem riemannHypothesis_of_cofinal_expanded_harmonic_resolvent (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgood : ∃ᶠ X : ℕ in atTop, ∃ j : ℕ, X ≤ (j+1)*9^j ∧
      minimumHarmonicPrefixOf (resolventApprox j) X ≤ C * (Real.log (X : ℝ)) ^ B) :
    RiemannHypothesis := by
  let D := (Real.sqrt zetaTwo * ‖limitingResidual‖) / 2
  have hD : 0 ≤ D := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (by norm_num)
  apply riemannHypothesis_of_cofinal_harmonic_polylog B (C+D) hB (add_nonneg hC hD)
  have hlog : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  apply (hgood.and_eventually hlog).mono
  rintro X ⟨⟨j, hj, hbound⟩, hlogX⟩
  have he := harmonic_expanded_window_error X j hj
  have ha := le_abs_self (minimumHarmonicPrefix X - minimumHarmonicPrefixOf (resolventApprox j) X)
  have hsmall : minimumHarmonicPrefix X -
      minimumHarmonicPrefixOf (resolventApprox j) X ≤ D := by
    dsimp only [D]
    linarith only [he, ha]
  have hone := Real.one_le_rpow hlogX hB
  nlinarith only [hsmall, hbound, mul_le_mul_of_nonneg_left hone hD]

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
