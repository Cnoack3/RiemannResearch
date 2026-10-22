import RiemannResearch.Analysis.ScaledKernelDerivative
import Mathlib.Analysis.Calculus.MeanValue

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Polynomially weighted uniform approximation by the actual scaled kernel

A weighted derivative bound controls translation on the entire intervening
segment. Dominated integration then gives an explicit O(1/R) estimate in
every weighted uniform seminorm; no Fourier growth theorem is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.Analysis

noncomputable def polynomialWeight (k : ℕ) (x : ℝ) : ℝ := (1 + |x|) ^ k

theorem polynomialWeight_nonneg (k : ℕ) (x : ℝ) : 0 ≤ polynomialWeight k x := by
  unfold polynomialWeight
  positivity

theorem one_le_polynomialWeight (k : ℕ) (x : ℝ) : 1 ≤ polynomialWeight k x := by
  simpa only [one_pow, polynomialWeight] using
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (show (1 : ℝ) ≤ 1+|x| by linarith [abs_nonneg x]) k

theorem polynomialWeight_le_of_abs_le (k : ℕ) {x y : ℝ} (h : |x| ≤ |y|) :
    polynomialWeight k x ≤ polynomialWeight k y := by
  exact pow_le_pow_left₀ (by positivity) (by linarith) k

theorem polynomialWeight_sub_mul (k : ℕ) (x u : ℝ) :
    polynomialWeight k x ≤ polynomialWeight k (x-u) * polynomialWeight k u := by
  have ha : |x| ≤ |x-u| + |u| := by
    simpa only [sub_add_cancel] using abs_add_le (x-u) u
  have hb : 1+|x| ≤ (1+|x-u|)*(1+|u|) := by
    nlinarith [abs_nonneg (x-u), abs_nonneg u]
  simpa only [polynomialWeight, mul_pow] using
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+|x|) hb k

theorem weighted_abs_translation_sub_le {f : ℝ → ℝ} (hfd : Differentiable ℝ f)
    (k : ℕ) (D : ℝ) (hD : ∀ x, polynomialWeight k x * |deriv f x| ≤ D)
    (x a : ℝ) :
    polynomialWeight k x * |f (x-a) - f x| ≤
      D * |a| * polynomialWeight k a := by
  have hD0 : 0 ≤ D := (mul_nonneg (polynomialWeight_nonneg k 0) (abs_nonneg _)).trans (hD 0)
  have hd (θ : ℝ) : HasDerivAt (fun q : ℝ => polynomialWeight k x * f (x-q*a))
      (polynomialWeight k x * deriv f (x-θ*a) * (-a)) θ := by
    have hin : HasDerivAt (fun q : ℝ => x-q*a) (-a) θ := by
      convert (hasDerivAt_const θ x).sub ((hasDerivAt_id θ).mul_const a) using 1 <;>
        first | rfl | ring
    convert ((hfd (x-θ*a)).hasDerivAt.comp θ hin).const_mul (polynomialWeight k x)
      using 1 <;> first | rfl | ring
  have hb (θ : ℝ) (hθ : θ ∈ Ico (0 : ℝ) 1) :
      ‖polynomialWeight k x * deriv f (x-θ*a) * (-a)‖ ≤
        D * |a| * polynomialWeight k a := by
    have hu : |θ*a| ≤ |a| := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      exact mul_le_of_le_one_left (abs_nonneg a) hθ.2.le
    have hw := (polynomialWeight_sub_mul k x (θ*a)).trans
      (mul_le_mul_of_nonneg_left (polynomialWeight_le_of_abs_le k hu)
        (polynomialWeight_nonneg k (x-θ*a)))
    have hv : polynomialWeight k x * |deriv f (x-θ*a)| ≤
        D * polynomialWeight k a := by
      calc
        _ ≤ (polynomialWeight k (x-θ*a) * polynomialWeight k a) *
            |deriv f (x-θ*a)| := mul_le_mul_of_nonneg_right hw (abs_nonneg _)
        _ = (polynomialWeight k (x-θ*a) * |deriv f (x-θ*a)|) *
            polynomialWeight k a := by ring
        _ ≤ D * polynomialWeight k a :=
          mul_le_mul_of_nonneg_right (hD _) (polynomialWeight_nonneg k a)
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (polynomialWeight_nonneg k x), abs_neg]
    nlinarith [mul_le_mul_of_nonneg_right hv (abs_nonneg a)]
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun θ _ => (hd θ).hasDerivWithinAt) hb
  simpa only [one_mul, zero_mul, sub_zero, ← mul_sub, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (polynomialWeight_nonneg k x)] using hm

theorem weighted_abs_scaledKernelConvolution_le (h f : ℝ → ℝ)
    (hh : Integrable h) (hfc : Continuous f) (k : ℕ) (M : ℝ)
    (hM : ∀ x, polynomialWeight k x * |f x| ≤ M)
    (hmoment : Integrable (fun v => polynomialWeight k v * |h v|))
    {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    polynomialWeight k x * |scaledKernelConvolution h f R x| ≤
      M * ∫ v, polynomialWeight k v * |h v| := by
  have hR0 : 0 < R := by linarith
  have hMplain (y : ℝ) : |f y| ≤ M :=
    (le_mul_of_one_le_left (abs_nonneg _) (one_le_polynomialWeight k y)).trans (hM y)
  have hi := integrable_scaledKernel_integrand h f hh hfc M hMplain R x
  have hw (v : ℝ) : polynomialWeight k x * |f (x-v/R)| ≤ M * polynomialWeight k v := by
    have hv : |v/R| ≤ |v| := by
      rw [abs_div, abs_of_pos hR0]
      exact div_le_self (abs_nonneg v) hR
    calc
      _ ≤ (polynomialWeight k (x-v/R)*polynomialWeight k (v/R))*|f (x-v/R)| :=
        mul_le_mul_of_nonneg_right (polynomialWeight_sub_mul k x (v/R)) (abs_nonneg _)
      _ = (polynomialWeight k (x-v/R)*|f (x-v/R)|)*polynomialWeight k (v/R) := by ring
      _ ≤ M * polynomialWeight k (v/R) :=
        mul_le_mul_of_nonneg_right (hM _) (polynomialWeight_nonneg k _)
      _ ≤ M * polynomialWeight k v := mul_le_mul_of_nonneg_left
        (polynomialWeight_le_of_abs_le k hv) ((abs_nonneg (f 0)).trans (hMplain 0))
  calc
    _ = |∫ v, polynomialWeight k x * (h v * f (x-v/R))| := by
      rw [integral_const_mul, abs_mul, abs_of_nonneg (polynomialWeight_nonneg k x)]
      rfl
    _ ≤ ∫ v, M * (polynomialWeight k v * |h v|) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hmoment.const_mul M)
      apply ae_of_all
      intro v
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (polynomialWeight_nonneg k x), abs_mul]
      nlinarith [mul_le_mul_of_nonneg_right (hw v) (abs_nonneg (h v))]
    _ = _ := integral_const_mul _ _

theorem weighted_abs_scaledKernelConvolution_sub_mass_le (h f : ℝ → ℝ)
    (hh : Integrable h) (hfd : Differentiable ℝ f) (M : ℝ) (hM : ∀ x, |f x| ≤ M)
    (k : ℕ) (D : ℝ) (hD : ∀ x, polynomialWeight k x * |deriv f x| ≤ D)
    (hmoment : Integrable (fun v => |v| * polynomialWeight k v * |h v|))
    {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    polynomialWeight k x * |scaledKernelConvolution h f R x - (∫ v, h v) * f x| ≤
      (D / R) * ∫ v, |v| * polynomialWeight k v * |h v| := by
  have hR0 : 0 < R := by linarith
  have hD0 : 0 ≤ D := (mul_nonneg (polynomialWeight_nonneg k 0) (abs_nonneg _)).trans (hD 0)
  have hleft := integrable_scaledKernel_integrand h f hh hfd.continuous M hM R x
  have hright := hh.mul_const (f x)
  have hid : scaledKernelConvolution h f R x - (∫ v, h v) * f x =
      ∫ v, h v * (f (x-v/R)-f x) := by
    unfold scaledKernelConvolution
    rw [← integral_mul_const, ← integral_sub hleft hright]
    congr 1
    funext v
    ring
  rw [hid]
  calc
    _ = |∫ v, polynomialWeight k x * (h v * (f (x-v/R)-f x))| := by
      rw [integral_const_mul, abs_mul, abs_of_nonneg (polynomialWeight_nonneg k x)]
    _ ≤ ∫ v, (D/R) * (|v| * polynomialWeight k v * |h v|) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hmoment.const_mul (D/R))
      apply ae_of_all
      intro v
      have hv : |v/R| ≤ |v| := by
        rw [abs_div, abs_of_pos hR0]
        exact div_le_self (abs_nonneg v) hR
      have ht := (weighted_abs_translation_sub_le hfd k D hD x (v/R)).trans
        (mul_le_mul_of_nonneg_left (polynomialWeight_le_of_abs_le k hv)
          (mul_nonneg hD0 (abs_nonneg _)))
      rw [abs_div, abs_of_pos hR0] at ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (polynomialWeight_nonneg k x), abs_mul]
      calc
        _ = (polynomialWeight k x * |f (x-v/R)-f x|) * |h v| := by ring
        _ ≤ (D*(|v|/R)*polynomialWeight k v)*|h v| :=
          mul_le_mul_of_nonneg_right ht (abs_nonneg _)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

theorem eventually_weighted_scaledKernelConvolution_error_lt (h f : ℝ → ℝ)
    (hh : Integrable h) (hfd : Differentiable ℝ f) (M : ℝ) (hM : ∀ x, |f x| ≤ M)
    (k : ℕ) (D : ℝ) (hD : ∀ x, polynomialWeight k x * |deriv f x| ≤ D)
    (hmoment : Integrable (fun v => |v| * polynomialWeight k v * |h v|))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ x : ℝ,
      polynomialWeight k x * |scaledKernelConvolution h f R x - (∫ v, h v) * f x| < ε := by
  have hlim : Tendsto (fun R : ℝ => (D/R) *
      ∫ v, |v| * polynomialWeight k v * |h v|) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      (tendsto_inv_atTop_zero.const_mul D).mul_const
        (∫ v, |v| * polynomialWeight k v * |h v|)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlim.eventually_lt_const hε] with R hR hbound
  intro x
  exact (weighted_abs_scaledKernelConvolution_sub_mass_le h f hh hfd M hM k D hD hmoment hR x).trans_lt hbound

end RiemannResearch.Analysis
