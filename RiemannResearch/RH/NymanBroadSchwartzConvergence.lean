import RiemannResearch.Analysis.WeightedNormalizationConvergence
import RiemannResearch.RH.NymanBroadFamilyBounds

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Convergence of every actual broad-profile Schwartz seminorm

The actual arithmetic kernel supplies every polynomial moment and the
actual compact smooth seed supplies every weighted derivative bound. The
normalization limit is the proved energy limit. The conclusion is uniform
convergence on the whole real line of every polynomially weighted derivative.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH
open RiemannResearch.Analysis

noncomputable def nymanBroadLimitScale (n : ℕ) (φ : ℝ → ℝ) : ℝ :=
  (-(∫ v, nymanReturnKernel n v)/8) /
    Real.sqrt ((-(∫ v, nymanReturnKernel n v)/8)^2 * ∫ x, φ x^2)

theorem nymanBroadLimitScale_eq_neg_inv_sqrt (n : ℕ) (hn : 2 ≤ n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hc : HasCompactSupport φ) (hmass : (∫ x, φ x) ≠ 0) :
    nymanBroadLimitScale n φ = -(Real.sqrt (∫ x, φ x^2))⁻¹ := by
  have hm : -(∫ v, nymanReturnKernel n v)/8 < 0 := by
    linarith [integral_nymanReturnKernel_pos hn]
  have hkernel : (∫ v, nymanReturnKernel n v) ≠ 0 :=
    (integral_nymanReturnKernel_pos hn).ne'
  have hq := broadProfile_integral_sq_pos_of_integral_ne_zero hφ hc hmass
  unfold nymanBroadLimitScale
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_neg hm]
  field_simp [hm.ne, hkernel, (Real.sqrt_pos.mpr hq).ne'] <;> ring

theorem integrable_weighted_abs_nymanReturnKernel {n : ℕ} (hn : 0 < n) (k j : ℕ) :
    Integrable (fun v => |v| ^j * polynomialWeight k v * |nymanReturnKernel n v|) := by
  apply integrable_abs_pow_mul_polynomialWeight
  intro i
  simpa only [abs_of_nonneg (nymanReturnKernel_nonneg hn _)] using
    integrable_pow_abs_nymanReturnKernel hn i

theorem eventually_weighted_iteratedDeriv_nymanBroadProfile_error_lt
    (n : ℕ) (hn : 2 ≤ n) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ)
    (hmass : (∫ x, φ x) ≠ 0) (k j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ x,
      polynomialWeight k x * |iteratedDeriv j (nymanBroadProfile n φ R) x -
        nymanBroadLimitScale n φ * iteratedDeriv j φ x| < ε := by
  have hn0 : 0 < n := by omega
  let h := nymanReturnKernel n
  let f : ℕ → ℝ → ℝ := fun i => iteratedDeriv i φ
  let g : ℕ → ℝ → ℝ := fun i => f (i+j)
  let m : ℝ := -(∫ v, h v)/8
  let N0 : ℝ := Real.sqrt (m^2 * ∫ x, φ x^2)
  have hh : Integrable h := integrable_nymanReturnKernel hn0
  have hmassh : 0 < ∫ v, h v := integral_nymanReturnKernel_pos hn
  have hphisq := broadProfile_integral_sq_pos_of_integral_ne_zero hφ hc hmass
  have hN0 : 0 < N0 := Real.sqrt_pos.mpr (mul_pos
    (sq_pos_of_ne_zero (div_ne_zero (neg_ne_zero.mpr hmassh.ne') (by norm_num))) hphisq)
  obtain ⟨U,_,hU⟩ := broadProfile_exists_all_derivative_bounds hφ hc
  obtain ⟨K,hK0,hK⟩ := broadProfile_exists_lipschitz_bound hφ hc
  have hfd (i : ℕ) : Differentiable ℝ (f i) :=
    (broadProfile_contDiff_iteratedDeriv hφ i).differentiable (by simp)
  have hnext (i : ℕ) : deriv (f i) = f (i+1) := by
    simp only [f, iteratedDeriv_succ]
  have hN : Tendsto (nymanBroadNorm n φ) atTop (𝓝 N0) := by
    change Tendsto (broadKernelNorm h f) atTop (𝓝 N0)
    simpa only [f, iteratedDeriv_zero, N0, m, h] using
      tendsto_broadKernelNorm h f hh (broadProfile_integrable_iteratedDeriv hφ hc)
        (broadProfile_continuous_iteratedDeriv hφ) U hU K hK0
        (by simpa only [f, iteratedDeriv_zero] using hK)
        (integrable_abs_mul_abs_nymanReturnKernel hn0)
  choose M hM0 hM using fun i => broadProfile_exists_weighted_derivative_bound hφ hc k i
  have hwm0 : Integrable (fun v => polynomialWeight k v * |h v|) := by
    simpa only [pow_zero, one_mul] using integrable_weighted_abs_nymanReturnKernel hn0 k 0
  have hwm1 : Integrable (fun v => |v| * polynomialWeight k v * |h v|) := by
    simpa only [pow_one] using integrable_weighted_abs_nymanReturnKernel hn0 k 1
  let E : ℝ := (∫v,polynomialWeight k v* |h v|)*(M (3+j)+M (2+j)+M (1+j))+
    M (j+1)*(∫v,|v| *polynomialWeight k v* |h v|)
  have hA (R : ℝ) (hR : 1 ≤ R) (x : ℝ) :
      polynomialWeight k x * |broadKernelProfile h g R x-m*f j x| ≤ E/R := by
    have hd : ∀ y, polynomialWeight k y * |deriv (g 0) y| ≤ M (j+1) := by
      simpa only [g, Nat.zero_add, hnext] using hM (j+1)
    have hgd : Differentiable ℝ (g 0) := by
      simpa only [g, Nat.zero_add] using hfd j
    simpa only [g, Nat.zero_add, E, m, f] using
      weighted_abs_broadKernelProfile_sub_limit_le h g hh
        (fun i => (hfd (i+j)).continuous) hgd k (fun i => M (i+j))
        (fun i => hM (i+j)) (M (j+1)) hd hwm0 hwm1 hR x
  have hconv := eventually_weighted_quotient_error_lt
    (fun R => broadKernelProfile h g R) (nymanBroadNorm n φ) (f j)
    (polynomialWeight k) N0 m E (M j) hN0 hN (polynomialWeight_nonneg k)
    hA (hM j) ε hε
  filter_upwards [hconv] with R hR
  intro x
  unfold nymanBroadProfile
  rw [iteratedDeriv_normalizedBroadKernelProfile h f hh hfd hnext U hU]
  exact hR x

theorem eventually_weighted_iteratedDeriv_nymanBroadProfile_bound
    (n : ℕ) (hn : 2 ≤ n) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ)
    (hmass : (∫ x, φ x) ≠ 0) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ R : ℝ in atTop, ∀ x,
      polynomialWeight k x * |iteratedDeriv j (nymanBroadProfile n φ R) x| ≤ C := by
  obtain ⟨M,hM0,hM⟩ := broadProfile_exists_weighted_derivative_bound hφ hc k j
  let c := nymanBroadLimitScale n φ
  refine ⟨1+ |c| *M, by positivity, ?_⟩
  filter_upwards [eventually_weighted_iteratedDeriv_nymanBroadProfile_error_lt
    n hn hφ hc hmass k j 1 (by norm_num)] with R hR
  intro x
  have ht := abs_add_le
    (iteratedDeriv j (nymanBroadProfile n φ R) x-c*iteratedDeriv j φ x)
    (c*iteratedDeriv j φ x)
  rw [sub_add_cancel, abs_mul] at ht
  have hs := mul_le_mul_of_nonneg_left ht (polynomialWeight_nonneg k x)
  have hm := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg c)
  have he := (hR x).le
  change polynomialWeight k x *
    |iteratedDeriv j (nymanBroadProfile n φ R) x-c*iteratedDeriv j φ x| ≤ 1 at he
  nlinarith

end RiemannResearch.RH
