import RiemannResearch.RH.ResidueDivisorZeroExclusion
import RiemannResearch.RH.ResidualMellinZeroConditions
import RiemannResearch.RH.ParetoMellinDilation

/-!
# An exact dyadic factor of the signed divisor limit

Source: algebraic factorization of the existing first-coordinate residual
identity, combined with the project's exact integer-dilation Mellin formula.
The zero-dependent bound retains the complex dyadic phase before its norm is
taken. No RH or zero-existence assumption is introduced. The zero exclusion
consumer keeps its arithmetic budget hypothesis explicit.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto

theorem dyadic_factor_energy (f : ThresholdHilbert) :
    (1 + Real.sqrt 2 / 2) *
      ‖f - (1 - Real.sqrt 2 / 2) • hilbertDilation 2 (by decide) f‖ ^ 2 =
        2 * ‖f‖ ^ 2 - inner ℝ f (hilbertDilation 2 (by decide) f) := by
  let a : ℝ := 1 + Real.sqrt 2 / 2
  let t : ℝ := 1 - Real.sqrt 2 / 2
  have hprod : a * t = 1 / 2 := by
    dsimp [a, t]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsum : a + t = 2 := by dsimp [a, t]; ring
  have hquad : a * (1 + 2 * t ^ 2) = 2 := by
    calc
      _ = a + 2 * (a * t) * t := by ring
      _ = a + t := by rw [hprod]; ring
      _ = 2 := hsum
  change a * ‖f - t • hilbertDilation 2 (by decide) f‖ ^ 2 = _
  calc
    _ = (a * (1 + 2 * t ^ 2)) * ‖f‖ ^ 2 -
        2 * (a * t) * inner ℝ f (hilbertDilation 2 (by decide) f) := by
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        inner_smul_right, hilbertDilation_norm_sq]
      norm_num
      ring
    _ = _ := by rw [hquad, hprod]; ring

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail

/-- A dyadic difference whose full energy is exactly the first residual
coordinate, after multiplication by 1+sqrt(2)/2. -/
def dyadicResidualFactor : ThresholdHilbert :=
  limitResidual - (1 - Real.sqrt 2 / 2) •
    hilbertDilation 2 (by decide) limitResidual

/-- The signed arithmetic limit is the negative of a complete norm square. -/
theorem firstCoordinate_eq_dyadicFactor_energy :
    hilbertSequence limitResidual 1 =
      (1 + Real.sqrt 2 / 2) * ‖dyadicResidualFactor‖ ^ 2 := by
  rw [dyadicResidualFactor, dyadic_factor_energy]
  have h := firstCoordinate_energy_identity
  change hilbertSequence limitResidual 1 = 2 * limitEnergy - _
  linarith

theorem divisorReciprocalStatistic_tendsto_dyadicFactor_energy :
    Tendsto divisorReciprocalStatistic atTop
      (𝓝 (-((1 + Real.sqrt 2 / 2) * ‖dyadicResidualFactor‖ ^ 2))) := by
  simpa only [firstCoordinate_eq_dyadicFactor_energy] using divisorReciprocalStatistic_tendsto

/-- At a genuine zero, the factor has an explicitly nontrivial Mellin value. -/
theorem dyadicResidualFactor_mellin_at_zero (ρ : ℂ)
    (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    paretoMellin dyadicResidualFactor ρ =
      (1 - ((1 - Real.sqrt 2 / 2 : ℝ) : ℂ) * (2 : ℂ) ^ (1 - ρ)) / ρ := by
  change paretoMellinContinuous ρ hhalf
    (limitResidual - (1 - Real.sqrt 2 / 2) •
      hilbertDilation 2 (by decide) limitResidual) = _
  rw [map_sub, map_smul]
  change paretoMellin limitResidual ρ - (1 - Real.sqrt 2 / 2) •
    paretoMellin (hilbertDilation 2 (by decide) limitResidual) ρ = _
  rw [paretoMellin_dilation, limitResidual_mellin_at_zero ρ hhalf hρ1 hzero,
    Complex.real_smul]
  ring

/-- A sharper actual-zero obstruction retaining the dyadic phase. -/
theorem divisorReciprocalStatistic_dyadic_zero_limit_bound (ρ : ℂ)
    (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    (1 + Real.sqrt 2 / 2) * (2 * ρ.re - 1) *
      ‖1 - ((1 - Real.sqrt 2 / 2 : ℝ) : ℂ) * (2 : ℂ) ^ (1 - ρ)‖ ^ 2 / ‖ρ‖ ^ 2 ≤
        hilbertSequence limitResidual 1 := by
  have hb := paretoMellin_norm_sq_le dyadicResidualFactor ρ hhalf
  rw [dyadicResidualFactor_mellin_at_zero ρ hhalf hρ1 hzero] at hb
  have hm := mul_le_mul_of_nonneg_left
    ((le_div_iff₀ (show 0 < 2 * ρ.re - 1 by linarith)).mp hb)
    (show 0 ≤ 1 + Real.sqrt 2 / 2 by positivity)
  rw [← firstCoordinate_eq_dyadicFactor_energy, norm_div, div_pow] at hm
  convert hm using 1 <;> first | rfl | ring

/-- The phase-sensitive multiplier dominates the universal coefficient
2−sqrt(2) throughout the right critical half-plane. -/
theorem dyadic_zero_multiplier_lower (ρ : ℂ)
    (hhalf : (1 / 2 : ℝ) ≤ ρ.re) :
    2 - Real.sqrt 2 ≤ (1 + Real.sqrt 2 / 2) *
      ‖1 - ((1 - Real.sqrt 2 / 2 : ℝ) : ℂ) * (2 : ℂ) ^ (1 - ρ)‖ ^ 2 := by
  let a : ℝ := 1 + Real.sqrt 2 / 2
  let t : ℝ := 1 - Real.sqrt 2 / 2
  let z : ℂ := (2 : ℂ) ^ (1 - ρ)
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hzn : ‖z‖ ≤ Real.sqrt 2 := by
    dsimp [z]
    have he : ‖(2 : ℂ) ^ (1 - ρ)‖ = (2 : ℝ) ^ (1 - ρ.re) := by
      simpa only [Complex.sub_re, Complex.one_re, Complex.ofReal_ofNat] using
        Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 2 by norm_num) (1 - ρ)
    rw [he, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
  have hmul : ‖(t : ℂ) * z‖ ≤ t * Real.sqrt 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left hzn ht
  have htri := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * z)
  rw [norm_one] at htri
  have htval : t * Real.sqrt 2 = Real.sqrt 2 - 1 := by
    dsimp [t]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [htval] at hmul
  have hlow : 2 - Real.sqrt 2 ≤ ‖1 - (t : ℂ) * z‖ := by linarith
  have hsq := (sq_le_sq₀ (show 0 ≤ 2 - Real.sqrt 2 by linarith)
    (norm_nonneg _)).mpr hlow
  have hcancel : a * (2 - Real.sqrt 2) = 1 := by
    dsimp [a]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hconstant : a * (2 - Real.sqrt 2) ^ 2 = 2 - Real.sqrt 2 := by
    calc
      _ = (a * (2 - Real.sqrt 2)) * (2 - Real.sqrt 2) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hm := mul_le_mul_of_nonneg_left hsq ha
  rw [hconstant] at hm
  exact hm

/-- A budget that is insufficient for the uniform bound can still exclude a
zero whose dyadic phase makes this strictly stronger margin exceed it. -/
theorem zeta_ne_zero_of_divisor_budget_dyadic_margin (A : ℝ)
    (hbudget : ∃ᶠ n : ℕ in atTop, -A < divisorReciprocalStatistic n)
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hmargin : A < (1 + Real.sqrt 2 / 2) * (2 * ρ.re - 1) *
      ‖1 - ((1 - Real.sqrt 2 / 2 : ℝ) : ℂ) * (2 : ℂ) ^ (1 - ρ)‖ ^ 2 / ‖ρ‖ ^ 2) :
    riemannZeta ρ ≠ 0 := by
  intro hzero
  have hb := divisorReciprocalStatistic_dyadic_zero_limit_bound ρ hhalf hρ1 hzero
  have he : ∀ᶠ n : ℕ in atTop, divisorReciprocalStatistic n < -A :=
    divisorReciprocalStatistic_tendsto.eventually_lt_const (by linarith)
  obtain ⟨n, hn, hn'⟩ := (hbudget.and_eventually he).exists
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
