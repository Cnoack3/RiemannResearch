import RiemannResearch.RH.ResidueDivisorReciprocalLimit
import RiemannResearch.RH.ThresholdRiemannHypothesis

/-!
# Actual zeta-zero obstructions for certified divisor sums

Source: the existing exact Mellin obstruction in ThresholdRiemannHypothesis,
the certified signed divisor statistic, and the proved residual dilation
bounds. This assembly makes a hypothetical actual zero quantitatively visible
in the arithmetic statistic. It does not assume RH or a zero independently of
the conditional zero statements. The arithmetic lower-budget hypotheses in
the exclusion theorems are explicit, and no provider is asserted.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

/-- A zero to the right of the critical line forces this positive lower
bound on the actual limiting projection defect. -/
theorem limitEnergy_lower_of_zeta_zero (ρ : ℂ)
    (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    (2 * ρ.re - 1) / ‖ρ‖ ^ 2 ≤ limitEnergy := by
  have hp : limitProjection ∈ closedSpace :=
    closedSpace.starProjection_apply_mem hilbertOne
  have hb := legalClosure_distance_sq_lower_bound_of_zeta
    {n : ℕ | 0 < n} (fun _ hn => hn) ρ hhalf hρ1 hzero
    (closedSpace_le_legalClosure hp)
  exact hb

/-- The zero's real part and height impose a definite negative limit for the
actual signed divisor statistic. This is an explicit zero obstruction. -/
theorem divisorReciprocalStatistic_zero_limit_bound (ρ : ℂ)
    (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    (2 - Real.sqrt 2) * ((2 * ρ.re - 1) / ‖ρ‖ ^ 2) ≤
      hilbertSequence limitResidual 1 := by
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hm := mul_le_mul_of_nonneg_left
    (limitEnergy_lower_of_zeta_zero ρ hhalf hρ1 hzero)
    (show 0 ≤ 2 - Real.sqrt 2 by linarith)
  have hb := firstCoordinate_energy_bounds.1
  nlinarith

/-- Every actual off-line zero forces eventual finite arithmetic values below
an explicit negative threshold. The cutoff is not claimed effective in ρ. -/
theorem divisorReciprocalStatistic_eventually_negative_of_zeta_zero (ρ : ℂ)
    (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    ∀ᶠ n : ℕ in atTop, divisorReciprocalStatistic n <
      -((2 - Real.sqrt 2) * ((2 * ρ.re - 1) / ‖ρ‖ ^ 2)) / 2 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    norm_num [h] at hhalf
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hp : 0 < (2 - Real.sqrt 2) * ((2 * ρ.re - 1) / ‖ρ‖ ^ 2) :=
    mul_pos (by linarith) (div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hρ0)))
  apply divisorReciprocalStatistic_tendsto.eventually_lt_const
  have hb := divisorReciprocalStatistic_zero_limit_bound ρ hhalf hρ1 hzero
  linarith

/-- A cofinal lower budget for the actual finite progression statistic gives
a quantitative constraint on every zero, without assuming zero residual. -/
theorem zeta_zero_bound_of_divisorReciprocalStatistic_cofinal_lower (A : ℝ)
    (hbudget : ∃ᶠ n : ℕ in atTop, -A < divisorReciprocalStatistic n)
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    (2 - Real.sqrt 2) * ((2 * ρ.re - 1) / ‖ρ‖ ^ 2) ≤ A := by
  by_contra hn
  have hlt : A < (2 - Real.sqrt 2) * ((2 * ρ.re - 1) / ‖ρ‖ ^ 2) :=
    lt_of_not_ge hn
  have hb := divisorReciprocalStatistic_zero_limit_bound ρ hhalf hρ1 hzero
  have he : ∀ᶠ n : ℕ in atTop, divisorReciprocalStatistic n < -A :=
    divisorReciprocalStatistic_tendsto.eventually_lt_const (by linarith)
  obtain ⟨n, hn, hn'⟩ := (hbudget.and_eventually he).exists
  linarith

/-- Quantitative zero exclusion from a single arithmetic lower budget. The
budget is the unresolved arithmetic input, whereas the implication is exact. -/
theorem zeta_ne_zero_of_divisorReciprocalStatistic_budget (A : ℝ)
    (hbudget : ∃ᶠ n : ℕ in atTop, -A < divisorReciprocalStatistic n)
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hmargin : A < (2 - Real.sqrt 2) * ((2 * ρ.re - 1) / ‖ρ‖ ^ 2)) :
    riemannZeta ρ ≠ 0 := by
  intro hzero
  exact (not_lt_of_ge
    (zeta_zero_bound_of_divisorReciprocalStatistic_cofinal_lower A hbudget
      ρ hhalf hρ1 hzero)) hmargin

/-- A budget A excludes all zeros in a bounded-radius right-half region
whenever A R² < (2−√2)2δ. All geometric quantities are explicit. -/
theorem zeta_ne_zero_in_bounded_region_of_divisor_budget
    (A R δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hbudget : ∃ᶠ n : ℕ in atTop, -A < divisorReciprocalStatistic n)
    (hmargin : A * R ^ 2 < (2 - Real.sqrt 2) * (2 * δ))
    (ρ : ℂ) (hρ1 : ρ ≠ 1) (hre : 1 / 2 + δ ≤ ρ.re) (hnorm : ‖ρ‖ ≤ R) :
    riemannZeta ρ ≠ 0 := by
  have hhalf : (1 / 2 : ℝ) < ρ.re := by linarith
  have hρ0 : ρ ≠ 0 := by
    intro h
    norm_num [h] at hhalf
  have hnorm0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hR : 0 ≤ R := (norm_nonneg ρ).trans hnorm
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hn2 : ‖ρ‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR).mpr hnorm
  have hleft := mul_le_mul_of_nonneg_left hn2 hA
  have hright := mul_le_mul_of_nonneg_left
    (show 2 * δ ≤ 2 * ρ.re - 1 by linarith)
    (show 0 ≤ 2 - Real.sqrt 2 by linarith)
  apply zeta_ne_zero_of_divisorReciprocalStatistic_budget A hbudget ρ hhalf hρ1
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ (sq_pos_of_pos hnorm0)).mpr
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
