import RiemannResearch.RH.NymanBroadKernelBridge
import RiemannResearch.RH.NymanTransformNullity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic.LinearCombination

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Exact zeta value of the cumulative kernel mass

The kernel normalization is identified by integrating one actual compact
smooth seed through the proved arithmetic return and its proved transform.
A concrete positive-integral bump removes the seed hypothesis from the final
constant. Thus the broad coefficient is the literal coefficient in Lemma 6.1.
-/

open MeasureTheory Set
open scoped Topology
namespace RiemannResearch.RH
open RiemannResearch.Analysis MeasureTheory.BilateralLaplace
open ZetaConductorRegularization ArithmeticConductorCommonZeros

private theorem kernelMass_eq_conductorZeta_of_seed (n : ℕ) (hn : 0 < n)
    {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0)
    (hmass : (∫ x : ℝ, φ x) ≠ 0) :
    ((∫ t : ℝ, nymanReturnKernel n t : ℝ) : ℂ) = 2 * conductorZeta n (1 / 2) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hcompact := broadProfile_hasCompactSupport_of_bounds ha hb
  have hfi (j : ℕ) := broadProfile_integrable_iteratedDeriv hφ hcompact j
  have hfc (j : ℕ) := broadProfile_continuous_iteratedDeriv hφ j
  have hz (j : ℕ) (hj : 0 < j) := broadProfile_integral_iteratedDeriv_eq_zero hφ hcompact hj
  have hbmean := integral_broadKernelProfile (nymanReturnKernel n)
    (fun j => iteratedDeriv j φ) (integrable_nymanReturnKernel hn) hfi hfc
    (hz 1 (by omega)) (hz 2 (by omega)) (hz 3 (by omega)) 1
  simp only [iteratedDeriv_zero] at hbmean
  have heq : nymanBroadTest n φ 1 = fun x : ℝ =>
      (differentialBroadKernelProfile (nymanReturnKernel n) φ 1 x : ℂ) := by
    funext x
    simpa using nymanBroadTest_scaled_eq n hn hφ ha hb (by norm_num : (0 : ℝ) < 1) x
  have hmean : (∫ x : ℝ, nymanBroadTest n φ 1 x) =
      (((-(∫ t : ℝ, nymanReturnKernel n t) / 8) * (∫ x : ℝ, φ x) : ℝ) : ℂ) := by
    rw [heq, integral_complex_ofReal]
    exact congrArg Complex.ofReal hbmean
  have ht := centeredTransform_poleCancellation_nymanFullReturn n
    (contDiff_nymanBroadPotential hφ 1)
    (nymanBroadPotential_zero_below ha (by norm_num : (0 : ℝ) < 1))
    (nymanBroadPotential_zero_above hb (by norm_num : (0 : ℝ) < 1)) (1 / 2)
  have hU : nymanBroadPotential φ 1 = fun x : ℝ => (φ x : ℂ) := by
    funext x
    simp [nymanBroadPotential]
  change centeredTransform (nymanBroadTest n φ 1) (1 / 2) = _ at ht
  simp only [centeredTransform, transform, sub_self, kernel, neg_zero, zero_mul,
    Complex.exp_zero, mul_one, hU, integral_complex_ofReal] at ht
  rw [hmean] at ht
  push_cast at ht
  have hcancel : ((∫ x : ℝ, φ x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmass
  apply mul_right_cancel₀ hcancel
  linear_combination (-8 : ℂ) * ht

private def coefficientSeed : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private theorem coefficientSeed_zero_below : ∀ x < (-2 : ℝ), coefficientSeed x = 0 := by
  intro x hx
  apply coefficientSeed.zero_of_le_dist
  simp only [coefficientSeed, Real.dist_eq, sub_zero]
  nlinarith [neg_le_abs x]

private theorem coefficientSeed_zero_above : ∀ x > (2 : ℝ), coefficientSeed x = 0 := by
  intro x hx
  apply coefficientSeed.zero_of_le_dist
  simp only [coefficientSeed, Real.dist_eq, sub_zero]
  nlinarith [le_abs_self x]

/-- The exact kernel mass, unconditionally and independently of a chosen seed. -/
theorem integral_nymanReturnKernel_eq_conductorZeta (n : ℕ) (hn : 0 < n) :
    ((∫ t : ℝ, nymanReturnKernel n t : ℝ) : ℂ) = 2 * conductorZeta n (1 / 2) :=
  kernelMass_eq_conductorZeta_of_seed n hn coefficientSeed.contDiff
    coefficientSeed_zero_below coefficientSeed_zero_above coefficientSeed.integral_pos.ne'

/-- The broad limit coefficient in the actual kernel profile is exactly
the regularized conductor-zeta coefficient at one-half. -/
theorem nymanBroadLimitCoefficient_eq_conductorZeta (n : ℕ) (hn : 0 < n) :
    (((-(∫ t : ℝ, nymanReturnKernel n t) / 8) : ℝ) : ℂ) =
      -conductorZeta n (1 / 2) / 4 := by
  push_cast
  rw [integral_nymanReturnKernel_eq_conductorZeta n hn]
  ring

private theorem conductorSymbol_half (n : ℕ) (hn : 0 < n) :
    conductorSymbol n (1 / 2) = 1 / (n : ℂ) - 1 / (Real.sqrt n : ℂ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : Real.exp (-Real.log (n : ℝ) / 2) = (Real.sqrt n)⁻¹ := by
    rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hnR]
  unfold conductorSymbol
  have hexp : Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ)) =
      (Real.exp (-Real.log (n : ℝ) / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp, he]
  simp only [Complex.ofReal_inv, one_div]

/-- Literal Lemma 6.1 coefficient, retaining the conductor factor and the
actual zeta value at one-half. -/
theorem nymanBroadLimitCoefficient_eq_zeta_half (n : ℕ) (hn : 0 < n) :
    (((-(∫ t : ℝ, nymanReturnKernel n t) / 8) : ℝ) : ℂ) =
      -riemannZeta (1 / 2) * (1 / (n : ℂ) - 1 / (Real.sqrt n : ℂ)) / 4 := by
  rw [nymanBroadLimitCoefficient_eq_conductorZeta n hn,
    conductorZeta_of_ne_one n (by norm_num : (1 / 2 : ℂ) ≠ 1), conductorSymbol_half n hn]
  ring

end RiemannResearch.RH
