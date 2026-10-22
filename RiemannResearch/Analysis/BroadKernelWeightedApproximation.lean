import RiemannResearch.Analysis.ScaledKernelWeightedApproximation
import RiemannResearch.Analysis.BroadKernelDifferentiation
import RiemannResearch.Analysis.BroadProfileRegularity

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# All weighted broad-profile estimates

The compact smooth input supplies every weighted derivative bound. The
actual finite differential kernel family converges uniformly with every
polynomial weight, with an explicit O(1/R) estimate.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.Analysis

theorem broadProfile_exists_weighted_derivative_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (hc : HasCompactSupport φ) (k j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x,
      polynomialWeight k x * |iteratedDeriv j φ x| ≤ M := by
  have hweight : Continuous (polynomialWeight k) := by unfold polynomialWeight; fun_prop
  have hfun : Continuous (fun x => polynomialWeight k x * |iteratedDeriv j φ x|) :=
    hweight.mul (broadProfile_continuous_iteratedDeriv hφ j).abs
  have hs : HasCompactSupport (fun x => polynomialWeight k x * |iteratedDeriv j φ x|) := by
    have hd : HasCompactSupport (fun x => |iteratedDeriv j φ x|) := by
      simpa only [Real.norm_eq_abs] using (broadProfile_hasCompactSupport_iteratedDeriv hc j).norm
    exact hd.mul_left
  obtain ⟨x₀, hx₀⟩ := hfun.exists_forall_ge_of_hasCompactSupport hs
  exact ⟨_, mul_nonneg (polynomialWeight_nonneg k x₀) (abs_nonneg _), hx₀⟩

theorem integrable_abs_pow_mul_polynomialWeight {h : ℝ → ℝ}
    (hm : ∀ j : ℕ, Integrable (fun v => |v| ^ j * |h v|)) (k j : ℕ) :
    Integrable (fun v => |v| ^ j * polynomialWeight k v * |h v|) := by
  induction k generalizing j with
  | zero => simpa only [polynomialWeight, pow_zero, mul_one] using hm j
  | succ k ih =>
      convert (ih j).add (ih (j+1)) using 1 <;>
        first | rfl | (ext v; simp only [Pi.add_apply, polynomialWeight, pow_succ]; ring)

private theorem abs_three_small_weighted {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (a b c : ℝ) :
    |r^3*a+r^2/2*b-r/4*c| ≤ r*(|a| + |b| + |c|) := by
  have h2 : r^2 ≤ r := by nlinarith
  have h3 : r^3 ≤ r := by nlinarith [mul_le_mul_of_nonneg_left h2 hr0]
  have ht := (abs_sub (r^3*a+r^2/2*b) (r/4*c)).trans
    (add_le_add (abs_add_le (r^3*a) (r^2/2*b)) le_rfl)
  rw [abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ r^3),
    abs_of_nonneg (by positivity : 0 ≤ r^2/2),
    abs_of_nonneg (by positivity : 0 ≤ r/4)] at ht
  nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c,
    mul_le_mul_of_nonneg_right h3 (abs_nonneg a),
    mul_le_mul_of_nonneg_right h2 (abs_nonneg b)]

theorem weighted_abs_broadKernelProfile_sub_limit_le (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ)
    (hh : Integrable h) (hfc : ∀ j, Continuous (f j)) (hfd : Differentiable ℝ (f 0))
    (k : ℕ) (M : ℕ → ℝ) (hM : ∀ j x, polynomialWeight k x * |f j x| ≤ M j)
    (D : ℝ) (hD : ∀ x, polynomialWeight k x * |deriv (f 0) x| ≤ D)
    (hm0 : Integrable (fun v => polynomialWeight k v * |h v|))
    (hm1 : Integrable (fun v => |v| * polynomialWeight k v * |h v|))
    {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    polynomialWeight k x * |broadKernelProfile h f R x - (-(∫ v, h v)/8)*f 0 x| ≤
      ((∫ v, polynomialWeight k v * |h v|)*(M 3+M 2+M 1)+
        D*(∫ v, |v| *polynomialWeight k v* |h v|))/R := by
  let w := polynomialWeight k x
  have hw : 0 ≤ w := polynomialWeight_nonneg k x
  have hR0 : 0 < R := by linarith
  have ht0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  have ht1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hsmall := abs_three_small_weighted ht0 ht1
    (w*scaledKernelConvolution h (f 3) R x)
    (w*scaledKernelConvolution h (f 2) R x)
    (w*scaledKernelConvolution h (f 1) R x)
  have hb (j : ℕ) := weighted_abs_scaledKernelConvolution_le h (f j) hh (hfc j)
    k (M j) (hM j) hm0 hR x
  have hMplain (y : ℝ) : |f 0 y| ≤ M 0 :=
    (le_mul_of_one_le_left (abs_nonneg _) (one_le_polynomialWeight k y)).trans (hM 0 y)
  have hbase := weighted_abs_scaledKernelConvolution_sub_mass_le h (f 0) hh hfd
    (M 0) hMplain k D hD hm1 hR x
  have hD0 : 0 ≤ D := (mul_nonneg (polynomialWeight_nonneg k 0) (abs_nonneg _)).trans (hD 0)
  have heq : w*(broadKernelProfile h f R x - (-(∫ v,h v)/8)*f 0 x) =
      ((R⁻¹)^3*(w*scaledKernelConvolution h (f 3) R x)+
       (R⁻¹)^2/2*(w*scaledKernelConvolution h (f 2) R x)-
       R⁻¹/4*(w*scaledKernelConvolution h (f 1) R x)) -
       (1/8)*(w*(scaledKernelConvolution h (f 0) R x-(∫ v,h v)*f 0 x)) := by
    unfold broadKernelProfile
    ring
  have htri := abs_sub
    ((R⁻¹)^3*(w*scaledKernelConvolution h (f 3) R x)+
     (R⁻¹)^2/2*(w*scaledKernelConvolution h (f 2) R x)-
     R⁻¹/4*(w*scaledKernelConvolution h (f 1) R x))
    ((1/8)*(w*(scaledKernelConvolution h (f 0) R x-(∫ v,h v)*f 0 x)))
  rw [← heq] at htri
  simp only [abs_mul, abs_of_nonneg hw,
    abs_of_pos (by norm_num : (0:ℝ)<1/8)] at htri hsmall
  have hs := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (hb 3) (hb 2)) (hb 1)) ht0
  have hm10 : 0 ≤ ∫ v, |v| *polynomialWeight k v* |h v| :=
    integral_nonneg (fun v => mul_nonneg (mul_nonneg (abs_nonneg v)
      (polynomialWeight_nonneg k v)) (abs_nonneg _))
  change w * |broadKernelProfile h f R x - (-(∫ v,h v)/8)*f 0 x| ≤ _
  change w * |scaledKernelConvolution h (f 0) R x - (∫ v,h v)*f 0 x| ≤ _ at hbase
  simp only [div_eq_mul_inv] at hbase htri hsmall hs ⊢
  nlinarith [mul_nonneg hD0 hm10, mul_nonneg (mul_nonneg hD0 hm10) ht0]

theorem eventually_weighted_broadKernelProfile_error_lt (h : ℝ → ℝ)
    (f : ℕ → ℝ → ℝ) (hh : Integrable h) (hfc : ∀ j, Continuous (f j))
    (hfd : Differentiable ℝ (f 0)) (k : ℕ) (M : ℕ → ℝ)
    (hM : ∀ j x, polynomialWeight k x * |f j x| ≤ M j)
    (D : ℝ) (hD : ∀ x, polynomialWeight k x * |deriv (f 0) x| ≤ D)
    (hm0 : Integrable (fun v => polynomialWeight k v * |h v|))
    (hm1 : Integrable (fun v => |v| * polynomialWeight k v * |h v|))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ x,
      polynomialWeight k x * |broadKernelProfile h f R x - (-(∫ v,h v)/8)*f 0 x| < ε := by
  let C := (∫ v, polynomialWeight k v* |h v|)*(M 3+M 2+M 1)+
    D*(∫ v,|v| *polynomialWeight k v* |h v|)
  have hlim : Tendsto (fun R : ℝ => C/R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul C
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlim.eventually_lt_const hε] with R hR hbound
  intro x
  exact (weighted_abs_broadKernelProfile_sub_limit_le h f hh hfc hfd k M hM D hD
    hm0 hm1 hR x).trans_lt hbound

end RiemannResearch.Analysis
