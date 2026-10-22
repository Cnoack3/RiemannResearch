import RiemannResearch.RH.NymanBroadFamily
import RiemannResearch.Analysis.BroadKernelDifferentiation
import RiemannResearch.Analysis.BroadKernelMeanSquareRate

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual uniform bounds and mean-square rate for the broad arithmetic family

Every input to the abstract integral estimates is supplied by the actual
cumulative Nyman kernel and the actual compact smooth seed's derivatives.
The normalization is positive eventually; all derivatives have uniform L1
and sup bounds; and the normalized mean squared has an O(1/R) error.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH
open RiemannResearch.Analysis

private theorem broad_derivative_next (φ : ℝ → ℝ) (j : ℕ) :
    deriv (iteratedDeriv j φ) = iteratedDeriv (j+1) φ := by
  rw [iteratedDeriv_succ]

/-- The actual broad arithmetic normalization is eventually bounded below
by one positive constant depending only on the conductor and seed. -/
theorem eventually_nymanBroadNorm_lower_bound (n : ℕ) (hn : 2 ≤ n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (hmass : (∫x,φ x) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ R : ℝ in atTop, δ ≤ nymanBroadNorm n φ R := by
  obtain ⟨M,_,hM⟩ := broadProfile_exists_all_derivative_bounds hφ hc
  obtain ⟨K,hK0,hK⟩ := broadProfile_exists_lipschitz_bound hφ hc
  exact eventually_broadKernelNorm_lower_bound (nymanReturnKernel n)
    (fun j => iteratedDeriv j φ) (integrable_nymanReturnKernel (by omega))
    (broadProfile_integrable_iteratedDeriv hφ hc)
    (broadProfile_continuous_iteratedDeriv hφ) M hM K hK0
    (by simpa only [iteratedDeriv_zero] using hK)
    (integrable_abs_mul_abs_nymanReturnKernel (by omega))
    (integral_nymanReturnKernel_pos hn)
    (by simpa only [iteratedDeriv_zero] using
      broadProfile_integral_sq_pos_of_integral_ne_zero hφ hc hmass)

/-- Uniform estimates apply to the actual derivative tower of the actual
normalized arithmetic profile, rather than to an unrelated formal array. -/
theorem eventually_nymanBroadProfile_derivative_bounds (n : ℕ) (hn : 2 ≤ n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (hmass : (∫x,φ x) ≠ 0) :
    ∀ j : ℕ, ∃ L S : ℝ, 0 ≤ L ∧ 0 ≤ S ∧ ∀ᶠ R : ℝ in atTop,
      Integrable (iteratedDeriv j (nymanBroadProfile n φ R)) ∧
      (∫x,|iteratedDeriv j (nymanBroadProfile n φ R) x|) ≤ L ∧
      ∀ x, |iteratedDeriv j (nymanBroadProfile n φ R) x| ≤ S := by
  obtain ⟨M,_,hM⟩ := broadProfile_exists_all_derivative_bounds hφ hc
  obtain ⟨K,hK0,hK⟩ := broadProfile_exists_lipschitz_bound hφ hc
  have hfd (j : ℕ) : Differentiable ℝ (iteratedDeriv j φ) :=
    (broadProfile_contDiff_iteratedDeriv hφ j).differentiable (by simp)
  have hh := integrable_nymanReturnKernel (show 0<n by omega)
  intro j
  obtain ⟨L,S,hL,hS,hbound⟩ := eventually_normalizedBroadKernel_bounds
    (nymanReturnKernel n) (fun j => iteratedDeriv j φ) hh
    (broadProfile_integrable_iteratedDeriv hφ hc)
    (broadProfile_continuous_iteratedDeriv hφ) M hM K hK0
    (by simpa only [iteratedDeriv_zero] using hK)
    (integrable_abs_mul_abs_nymanReturnKernel (by omega))
    (integral_nymanReturnKernel_pos hn)
    (by simpa only [iteratedDeriv_zero] using
      broadProfile_integral_sq_pos_of_integral_ne_zero hφ hc hmass) j
  refine ⟨L,S,hL,hS,?_⟩
  filter_upwards [hbound] with R hR
  unfold nymanBroadProfile
  rw [iteratedDeriv_normalizedBroadKernelProfile _ _ hh hfd
    (broad_derivative_next φ) M hM]
  exact hR

/-- Every actual normalized derivative is differentiable, without restricting
the scale or assuming positivity of a totalized normalization. -/
theorem differentiable_iteratedDeriv_nymanBroadProfile (n : ℕ) (hn : 0<n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (j : ℕ) (R : ℝ) :
    Differentiable ℝ (iteratedDeriv j (nymanBroadProfile n φ R)) := by
  obtain ⟨M,_,hM⟩ := broadProfile_exists_all_derivative_bounds hφ hc
  have hfd (k : ℕ) : Differentiable ℝ (iteratedDeriv k φ) :=
    (broadProfile_contDiff_iteratedDeriv hφ k).differentiable (by simp)
  have hh := integrable_nymanReturnKernel hn
  unfold nymanBroadProfile
  rw [iteratedDeriv_normalizedBroadKernelProfile _ _ hh hfd
    (broad_derivative_next φ) M hM]
  intro x
  exact (hasDerivAt_normalizedBroadKernelDerivative _ _ hh hfd
    (broad_derivative_next φ) M hM j R x).differentiableAt

/-- Eventual exact unit squared norm of the concrete normalized profile. -/
theorem eventually_integral_sq_nymanBroadProfile (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (hmass : (∫x,φ x) ≠ 0) :
    ∀ᶠ R : ℝ in atTop, (∫x,nymanBroadProfile n φ R x^2)=1 := by
  obtain ⟨δ,hδ,hN⟩ := eventually_nymanBroadNorm_lower_bound n hn hφ hc hmass
  filter_upwards [hN] with R hR
  exact integral_sq_normalizedBroadKernelProfile _ _ R (lt_of_lt_of_le hδ hR)

/-- The normalized mean-square coefficient differs from the seed ratio by
O(1/R), with all kernel and profile assumptions discharged. -/
theorem eventually_nymanBroadProfile_mean_square_error (n : ℕ) (hn : 2≤n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (hmass : (∫x,φ x) ≠ 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ R : ℝ in atTop,
      R*|(∫x,nymanBroadProfile n φ R x)^2-(∫x,φ x)^2/(∫x,φ x^2)|≤C := by
  obtain ⟨M,_,hM⟩ := broadProfile_exists_all_derivative_bounds hφ hc
  obtain ⟨K,hK0,hK⟩ := broadProfile_exists_lipschitz_bound hφ hc
  simpa only [nymanBroadProfile,iteratedDeriv_zero] using
    eventually_mean_sq_normalizedBroadKernelProfile_error (nymanReturnKernel n)
      (fun j => iteratedDeriv j φ) (integrable_nymanReturnKernel (by omega))
      (broadProfile_integrable_iteratedDeriv hφ hc)
      (broadProfile_continuous_iteratedDeriv hφ) M hM K hK0
      (by simpa only [iteratedDeriv_zero] using hK)
      (integrable_abs_mul_abs_nymanReturnKernel (by omega))
      (integral_nymanReturnKernel_pos hn)
      (by simpa only [iteratedDeriv_zero] using
        broadProfile_integral_sq_pos_of_integral_ne_zero hφ hc hmass)
      (broadProfile_integral_iteratedDeriv_eq_zero hφ hc (by norm_num : 0<1))
      (broadProfile_integral_iteratedDeriv_eq_zero hφ hc (by norm_num : 0<2))
      (broadProfile_integral_iteratedDeriv_eq_zero hφ hc (by norm_num : 0<3))

end RiemannResearch.RH
