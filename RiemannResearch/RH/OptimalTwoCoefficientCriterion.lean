import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ThresholdHilbertProjection
/-!
# A two-coefficient criterion for the actual optimal Pareto projections

Source: user-provided optimal-Gram coefficient question, 2026-09-22.
The polynomial argument below was independently developed in response to
that question; no claim of mathematical novelty is made.

The project's projection index n uses atoms g_2 through g_(n+1).
For these actual full-norm projections, convergence of
3 * coefficient n 2 + coefficient n 3 to 4 is equivalent to convergence
of the full squared Pareto error to zero, and implies Mathlib's RH.

The exact square identity and all geometric equivalences are unconditional.
The scalar limit remains an explicit Open domain-specific hypothesis.
No estimate establishing it, and no unconditional RH proof, is asserted.
-/

open scoped Topology
open Filter
noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
set_option backward.isDefEq.respectTransparency false

/-- The project's scaled dilation: (D f)(j) = 2 f(floor(j/2)), with f(0)=0. -/
def doubleDilation : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  hilbertDilationContinuous 2 (by decide)

theorem doubleDilation_inner (f g : ThresholdHilbert) :
    inner ℝ (doubleDilation f) (doubleDilation g) = 2 * inner ℝ f g := by
  exact hilbertDilation_inner 2 (by decide) f g

/-- Exact positive-square decomposition, using the complete Hilbert norm. -/
theorem doubleDilation_square_identity (x : ThresholdHilbert) :
    inner ℝ x ((14 : ℝ) • x - (13 : ℝ) • doubleDilation x + (3 : ℝ) • doubleDilation (doubleDilation x)) =
      (1 / 12 : ℝ) * ‖(6 : ℝ) • x - (13 / 2 : ℝ) • doubleDilation x +
        (3 : ℝ) • doubleDilation (doubleDilation x)‖ ^ 2 + (23 / 24 : ℝ) * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_sub_left, inner_add_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, doubleDilation_inner]
  simp only [real_inner_comm (doubleDilation x) x,
    real_inner_comm (doubleDilation (doubleDilation x)) x,
    real_inner_self_eq_norm_sq]
  ring

theorem doubleDilation_twice (x : ThresholdHilbert) :
    doubleDilation (doubleDilation x) = hilbertDilation 4 (by decide) x :=
  hilbertDilation_comp 2 2 (by decide) (by decide) x

/-- The Riesz vector for 3 C_2 + C_3 equals (14 I - 13 D + 3 D^2) one. -/
theorem twoThreeRiesz_eq_dilation :
    (-3 : ℝ) • mobiusRieszHilbert 2 - mobiusRieszHilbert 3 =
      (14 : ℝ) • hilbertOne - (13 : ℝ) • doubleDilation hilbertOne +
        (3 : ℝ) • doubleDilation (doubleDilation hilbertOne) := by
  rw [doubleDilation_twice]
  apply hilbertSequence_injective
  change hilbertSequenceLinear (_ - _) = hilbertSequenceLinear (_ + _)
  simp only [map_sub, map_smul, map_add]
  change (-3 : ℝ) • hilbertSequence (mobiusRieszHilbert 2) -
      hilbertSequence (mobiusRieszHilbert 3) =
    (14 : ℝ) • hilbertSequence hilbertOne -
      (13 : ℝ) • hilbertSequence (hilbertDilation 2 (by decide) hilbertOne) +
      (3 : ℝ) • hilbertSequence (hilbertDilation 4 (by decide) hilbertOne)
  rw [hilbertDilation_sequence, hilbertDilation_sequence, hilbertOne_sequence]
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
    mobiusRieszHilbert_sequence 2 j (by decide),
    mobiusRieszHilbert_sequence 3 j (by decide)]
  by_cases hj : j ≤ 3
  · interval_cases j <;> norm_num [dualCoeff, dilation, zeroAnchor,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  · have h2 : 2 < j := by omega
    have h3 : 3 < j := by omega
    have hz : j ≠ 0 := by omega
    have hd2 : j / 2 ≠ 0 := by omega
    have hd4 : j / 4 ≠ 0 := by omega
    simp [dualCoeff_eq_zero_of_lt (by decide : 0 < 2) h2,
      dualCoeff_eq_zero_of_lt (by decide : 0 < 3) h3,
      dilation, zeroAnchor, hz, hd2, hd4]
    norm_num

/-- Orthogonality converts the two coefficient defects into a coercive square. -/
theorem twoThreeLimit_square_identity :
    4 - 3 * limitCoefficient 2 - limitCoefficient 3 =
      (1 / 12 : ℝ) *
        ‖(6 : ℝ) • limitResidual - (13 / 2 : ℝ) • doubleDilation limitResidual +
          (3 : ℝ) • doubleDilation (doubleDilation limitResidual)‖ ^ 2 +
      (23 / 24 : ℝ) * limitEnergy := by
  have h := congrArg (fun y => inner ℝ limitResidual y) twoThreeRiesz_eq_dilation
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right] at h
  have hi (m : ℕ) : inner ℝ limitResidual (mobiusRieszHilbert m) =
      mobiusDifferenceCLM m limitResidual := by
    rw [real_inner_comm]
    exact mobiusRieszHilbert_inner m limitResidual
  rw [hi 2, hi 3, limitResidual_inner_one, doubleDilation_twice] at h
  change _ = 14 * limitEnergy -
    13 * inner ℝ limitResidual (hilbertDilation 2 (by decide) hilbertOne) +
    3 * inner ℝ limitResidual (hilbertDilation 4 (by decide) hilbertOne) at h
  rw [limitResidual_inner_dilation_one, limitResidual_inner_dilation_one] at h
  have h2 := limitCoefficient_eq_residual 2 (by decide)
  have h3 := limitCoefficient_eq_residual 3 (by decide)
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three] at h2 h3
  have hs := doubleDilation_square_identity limitResidual
  simp only [inner_add_right, inner_sub_right, real_inner_smul_right,
    doubleDilation_twice, real_inner_self_eq_norm_sq] at hs
  change _ = (1 / 12 : ℝ) * _ + (23 / 24 : ℝ) * limitEnergy at hs
  change _ = 14 * limitEnergy - 13 * inner ℝ limitResidual (doubleDilation limitResidual) +
    3 * inner ℝ limitResidual (hilbertDilation 4 (by decide) limitResidual) at h
  simp only [mobiusDifferenceCLM_apply] at h
  rw [show ‖limitResidual‖ ^ 2 = limitEnergy from rfl] at hs
  rw [doubleDilation_twice]
  linarith


theorem twoThreeLimit_energy_bound :
    (23 / 24 : ℝ) * limitEnergy ≤ 4 - 3 * limitCoefficient 2 - limitCoefficient 3 := by
  rw [twoThreeLimit_square_identity]
  have hn := sq_nonneg ‖(6 : ℝ) • limitResidual -
    (13 / 2 : ℝ) • doubleDilation limitResidual +
    (3 : ℝ) • doubleDilation (doubleDilation limitResidual)‖
  linarith

theorem twoThreeLimit_eq_four_iff_residual_zero :
    3 * limitCoefficient 2 + limitCoefficient 3 = 4 ↔ limitResidual = 0 := by
  constructor
  · intro h
    apply limitResidual_zero_iff_energy_zero.mpr
    have hb := twoThreeLimit_energy_bound
    have hn : 0 ≤ limitEnergy := sq_nonneg ‖limitResidual‖
    linarith
  · intro h
    have h2 := limitCoefficient_eq_residual 2 (by decide)
    have h3 := limitCoefficient_eq_residual 3 (by decide)
    rw [h, map_zero] at h2 h3
    norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three] at h2 h3
    linarith

theorem twoThreeCoefficients_tendsto :
    Tendsto (fun n => 3 * coefficient n 2 + coefficient n 3) atTop
      (𝓝 (3 * limitCoefficient 2 + limitCoefficient 3)) :=
  ((coefficient_tendsto 2).const_mul 3).add (coefficient_tendsto 3)

/-- Only the actual optimal projections are used in this equivalence. -/
theorem twoThreeCoefficients_tendsto_four_iff_energy_zero :
    Tendsto (fun n => 3 * coefficient n 2 + coefficient n 3) atTop (𝓝 4) ↔
      Tendsto energy atTop (𝓝 0) := by
  have hs : Tendsto (fun n => 3 * coefficient n 2 + coefficient n 3) atTop (𝓝 4) ↔
      3 * limitCoefficient 2 + limitCoefficient 3 = 4 := by
    constructor
    · intro h
      exact tendsto_nhds_unique twoThreeCoefficients_tendsto h
    · intro h
      simpa only [h] using twoThreeCoefficients_tendsto
  rw [hs, twoThreeLimit_eq_four_iff_residual_zero,
    ← limitCoefficients_eq_mobius_iff_residual_zero,
    limitCoefficients_eq_mobius_iff_energy_tendsto_zero]

/-- Conditional research reduction. Open: prove the displayed scalar limit. -/
theorem riemannHypothesis_of_twoThreeCoefficients
    (h : Tendsto (fun n => 3 * coefficient n 2 + coefficient n 3) atTop (𝓝 4)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_limitCoefficients
  exact limitCoefficients_eq_mobius_iff_energy_tendsto_zero.mpr
    (twoThreeCoefficients_tendsto_four_iff_energy_zero.mp h)


/-- Conditional research reduction: the two Mobius target limits already suffice. -/
theorem riemannHypothesis_of_second_and_third_coefficients
    (h2 : Tendsto (fun n => coefficient n 2) atTop (𝓝 1))
    (h3 : Tendsto (fun n => coefficient n 3) atTop (𝓝 1)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_twoThreeCoefficients
  simpa only [show (3 : ℝ) * 1 + 1 = 4 by norm_num] using
    (h2.const_mul 3).add h3

end RiemannResearch.RH.Pareto.CoefficientStabilization
