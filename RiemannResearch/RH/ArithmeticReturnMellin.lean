import RiemannResearch.RH.ArithmeticReturnSupport
import RiemannResearch.RH.NymanPeriodicLFunction
import RiemannResearch.Analysis.BilateralLaplaceTranslation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The actual arithmetic-return Mellin integral factors in its convergence half-plane

Source: user-provided argument, equation (4.2). The proof derives the Bochner
integral interchange from absolute summability of the actual Dirichlet series.
For each index, the integral of the norm is exactly the coefficient norm times
one fixed integral, by translation invariance. No Fubini or transform-factorization
hypothesis is introduced in the compact-test specialization.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open scoped BigOperators Topology

namespace RiemannResearch.RH

theorem halfDensity_kernel_log {k : ℕ} (hk : k ≠ 0) (s : ℂ) :
    ((Real.sqrt k : ℝ) : ℂ)⁻¹ * kernel (s - 1 / 2) (Real.log k) =
      ((k : ℂ) ^ s)⁻¹ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hsqrtpos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  have hsqrt : ((Real.sqrt k : ℝ) : ℂ) =
      Complex.exp ((Real.log k : ℂ) / 2) := by
    calc
      ((Real.sqrt k : ℝ) : ℂ) =
          ((Real.exp (Real.log (Real.sqrt k)) : ℝ) : ℂ) := by
        rw [Real.exp_log hsqrtpos]
      _ = _ := by
        rw [Real.log_sqrt (Nat.cast_nonneg k)]
        simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hpow : (k : ℂ) ^ s = Complex.exp ((Real.log k : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hk)]
    congr 2
    simpa using (Complex.ofReal_log (Nat.cast_nonneg k)).symm
  rw [hsqrt, hpow, kernel, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

/-- Exact pointwise transport of a half-density return term into a translated
fixed integrable function. The k=0 term vanishes on both sides. -/
theorem arithmeticReturn_integrand_term (c : ArithmeticFunction ℝ)
    (u : ℝ → ℂ) (s : ℂ) (k : ℕ) (y : ℝ) :
    ((c k / Real.sqrt k : ℝ) • u (y - Real.log k)) * kernel (s - 1 / 2) y =
      LSeries.term (fun j => (c j : ℂ)) s k *
        (u (y - Real.log k) * kernel (s - 1 / 2) (y - Real.log k)) := by
  by_cases hk : k = 0
  · simp [hk]
  have hshift : kernel (s - 1 / 2) y =
      kernel (s - 1 / 2) (y - Real.log k) * kernel (s - 1 / 2) (Real.log k) := by
    simpa only [sub_add_cancel] using
      kernel_add (s - 1 / 2) (y - Real.log k) (Real.log k)
  rw [Complex.real_smul, Complex.ofReal_div, hshift, LSeries.term_of_ne_zero hk]
  calc
    ((c k : ℂ) / (Real.sqrt k : ℝ)) * u (y - Real.log k) *
        (kernel (s - 1 / 2) (y - Real.log k) * kernel (s - 1 / 2) (Real.log k)) =
      (c k : ℂ) * (((Real.sqrt k : ℝ) : ℂ)⁻¹ *
        kernel (s - 1 / 2) (Real.log k)) *
          (u (y - Real.log k) * kernel (s - 1 / 2) (y - Real.log k)) := by ring
    _ = _ := by rw [halfDensity_kernel_log hk]; ring

/-- Actual Fubini theorem for the return series. Absolute convergence of the
coefficient series and one integrable weighted input are the precise hypotheses. -/
theorem centeredTransform_arithmeticReturn (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {s : ℂ}
    (hc : LSeriesSummable (fun j => (c j : ℂ)) s)
    (hu : Integrable (fun y : ℝ => u y * kernel (s - 1 / 2) y) volume) :
    centeredTransform (arithmeticReturn c u) s =
      LSeries (fun j => (c j : ℂ)) s * centeredTransform u s := by
  let G : ℝ → ℂ := fun y => u y * kernel (s - 1 / 2) y
  let T : ℕ → ℂ := LSeries.term (fun j => (c j : ℂ)) s
  let F : ℕ → ℝ → ℂ := fun k y => T k * G (y - Real.log k)
  have hT : Summable T := hc
  have hF : ∀ k, Integrable (F k) volume := by
    intro k
    exact (hu.comp_sub_right (Real.log k)).const_mul (T k)
  have hnorm (k : ℕ) : (∫ y : ℝ, ‖F k y‖) =
      ‖T k‖ * ∫ y : ℝ, ‖G y‖ := by
    simp only [F, norm_mul, integral_const_mul]
    exact congrArg (fun z : ℝ => ‖T k‖ * z)
      (integral_sub_right_eq_self (fun y : ℝ => ‖G y‖) (Real.log k))
  have hsum : Summable (fun k : ℕ => ∫ y : ℝ, ‖F k y‖) := by
    simp only [hnorm]
    exact hT.norm.mul_right _
  have hint (k : ℕ) : (∫ y : ℝ, F k y) = T k * centeredTransform u s := by
    dsimp [F]
    rw [integral_const_mul, integral_sub_right_eq_self]
    rfl
  calc
    centeredTransform (arithmeticReturn c u) s = ∫ y : ℝ, ∑' k : ℕ, F k y := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change (∑' k : ℕ, (c k / Real.sqrt k : ℝ) • u (y - Real.log k)) *
          kernel (s - 1 / 2) y = ∑' k : ℕ, F k y
      rw [← tsum_mul_right]
      apply tsum_congr
      intro k
      exact arithmeticReturn_integrand_term c u s k y
    _ = ∑' k : ℕ, ∫ y : ℝ, F k y :=
      (integral_tsum_of_summable_integral_norm hF hsum).symm
    _ = (∑' k : ℕ, T k) * centeredTransform u s := by
      simp only [hint]
      exact tsum_mul_right
    _ = LSeries (fun j => (c j : ℂ)) s * centeredTransform u s := rfl

/-- For the actual periodic beta coefficients the convergence hypothesis is
proved, yielding the actual half-plane integral factorization. -/
theorem centeredTransform_nymanFullReturn_of_exponentialMoments (n : ℕ) [NeZero n]
    {u : ℝ → ℂ} (hu : HasExponentialMoments u) {s : ℂ} (hs : 1 < s.re) :
    centeredTransform (nymanFullReturn n u) s =
      nymanConductorLFunction n s * centeredTransform u s := by
  rw [nymanConductorLFunction_eq_LSeries n hs]
  exact centeredTransform_arithmeticReturn (nymanConductorBeta n)
    (lSeriesSummable_nymanConductorBeta n hs) (integrable_integrand hu (s - 1 / 2))

/-- The concrete compact-test theorem requires only ordinary continuity and
compact support. Every series/integral interchange is discharged above. -/
theorem centeredTransform_nymanFullReturn_of_compactSupport (n : ℕ) [NeZero n]
    {u : ℝ → ℂ} (hu : Continuous u) (hcompact : HasCompactSupport u)
    {s : ℂ} (hs : 1 < s.re) :
    centeredTransform (nymanFullReturn n u) s =
      nymanConductorLFunction n s * centeredTransform u s :=
  centeredTransform_nymanFullReturn_of_exponentialMoments n
    (hasExponentialMoments_of_compactSupport hu hcompact) hs

/-- The actual bilateral integral carries the full zeta/conductor factor on
the arithmetic convergence half-plane; all coefficients and integrals are concrete. -/
theorem centeredTransform_nymanFullReturn_eq_zeta_cpow (n : ℕ) [NeZero n]
    {u : ℝ → ℂ} (hu : Continuous u) (hcompact : HasCompactSupport u)
    {s : ℂ} (hs : 1 < s.re) :
    centeredTransform (nymanFullReturn n u) s =
      (riemannZeta s * (1 / (n : ℂ) - (n : ℂ) ^ (-s))) * centeredTransform u s := by
  rw [centeredTransform_nymanFullReturn_of_compactSupport n hu hcompact hs,
    nymanConductorLFunction_eq_zeta_cpow n hs]

end RiemannResearch.RH
