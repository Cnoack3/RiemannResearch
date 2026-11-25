import RiemannResearch.Analysis.LogarithmicFejerKernel
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Finite Fejér witnesses for the periodic distance

The Fejér kernel from `LogarithmicFejerKernel` is unnormalized. Its width is
`2*N`, so its mass is `2*N`. We subtract the smoothed tent's value at zero.
The Fourier computation uses the interval of representatives [-1/2,1/2]. -/

noncomputable section
open MeasureTheory AddCircle Filter Finset
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.DyadicZeroWasserstein

private theorem cosine_coe_real (k : ℕ) (x : ℝ) :
    (fourier (k : ℤ) (x : UnitAddCircle)).re = Real.cos (2 * Real.pi * k * x) := by
  rw [fourier_coe_apply, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

private theorem sine_coe_real (k : ℕ) (x : ℝ) :
    (fourier (k : ℤ) (x : UnitAddCircle)).im = Real.sin (2 * Real.pi * k * x) := by
  rw [fourier_coe_apply, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]

private theorem tent_repr_integral (f : UnitAddCircle → ℝ) :
    (∫ z, f z ∂haarAddCircle) = ∫ x in (-1/2 : ℝ)..(1/2 : ℝ), f x := by
  rw [integral_haarAddCircle]
  rw [← AddCircle.intervalIntegral_preimage 1 (-1/2 : ℝ) f]
  norm_num

/-- The cosine coefficient of the geodesic distance from zero, with Haar mass one. -/
theorem integral_tent_cosine {k : ℕ} (hk : 0 < k) :
    (∫ z : UnitAddCircle, ‖z‖ * (fourier (k : ℤ) z).re ∂haarAddCircle) =
      ((-1 : ℝ)^k - 1) / (2 * Real.pi^2 * (k : ℝ)^2) := by
  let a : ℝ := 2 * Real.pi * k
  have ha : a ≠ 0 := by dsimp [a]; positivity
  let F (x : ℝ) := x * Real.sin (a*x) / a + Real.cos (a*x) / a^2
  have hd (x : ℝ) : HasDerivAt F (x * Real.cos (a*x)) x := by
    have hx := (hasDerivAt_id x).const_mul a
    apply ((((hasDerivAt_id x).mul hx.sin).div_const a).add (hx.cos.div_const (a^2))).congr_deriv
    simp only [id_eq, mul_one, one_mul]
    field_simp [ha]
    ring
  have hi (b c : ℝ) : (∫ x in b..c, x * Real.cos (a*x)) = F c - F b :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((continuous_id.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
  rw [tent_repr_integral]
  have he : (∫ x in (-1/2 : ℝ)..(1/2 : ℝ), ‖(x : UnitAddCircle)‖ * (fourier (k : ℤ) (x : UnitAddCircle)).re) =
      ∫ x in (-1/2 : ℝ)..(1/2 : ℝ), |x| * Real.cos (a*x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2)] at hx
    change ‖(x : UnitAddCircle)‖ * (fourier (k:ℤ) (x : UnitAddCircle)).re = |x| * Real.cos (a*x)
    rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := x) one_ne_zero).2
      (by rw [abs_one, abs_le]; exact ⟨by linarith [hx.1], hx.2⟩), cosine_coe_real]
  rw [he]
  let g (x : ℝ) := |x| * Real.cos (a*x)
  have cg : Continuous g := continuous_abs.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  change (∫ x in (-1/2 : ℝ)..(1/2 : ℝ), g x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (cg.intervalIntegrable (-1/2) 0)
    (cg.intervalIntegrable 0 (1/2))]
  have hl : (∫ x in (-1/2 : ℝ)..0, g x) = -(F 0 - F (-1/2)) := by
    rw [← hi, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1/2 : ℝ) ≤ 0)] at hx
    simp [g, abs_of_nonpos hx.2]
  have hr : (∫ x in (0 : ℝ)..(1/2), g x) = F (1/2) - F 0 := by
    rw [← hi]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at hx
    simp [g, abs_of_nonneg hx.1]
  rw [hl, hr]
  have hp : a*(1/2) = (k : ℝ)*Real.pi := by dsimp [a]; ring
  have hm : a*(-1/2) = -((k : ℝ)*Real.pi) := by dsimp [a]; ring
  simp only [F, hp, hm, mul_zero, Real.sin_neg, Real.cos_neg, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi, Real.sin_zero, Real.cos_zero, neg_zero, zero_div, zero_add]
  dsimp [a]
  field_simp [Real.pi_ne_zero, Nat.cast_ne_zero.mpr hk.ne']
  ring

private theorem integral_tent_sine (k : ℕ) :
    (∫ z : UnitAddCircle, ‖z‖ * (fourier (k : ℤ) z).im ∂haarAddCircle) = 0 := by
  have hs (z : UnitAddCircle) : (fourier (k : ℤ) (-z)).im = -(fourier (k : ℤ) z).im := by
    induction z using QuotientAddGroup.induction_on with
    | _ x =>
      change (fourier (k : ℤ) ((-x : ℝ) : UnitAddCircle)).im = _
      rw [sine_coe_real, sine_coe_real, mul_neg, Real.sin_neg]
  have hi := integral_neg_eq_self
    (fun z : UnitAddCircle => ‖z‖ * (fourier (k : ℤ) z).im) haarAddCircle
  simp_rw [norm_neg, hs, mul_neg, integral_neg] at hi
  linarith

private theorem cosine_sub_circle (k : ℕ) (x y : UnitAddCircle) :
    (fourier (k : ℤ) (x-y)).re = (fourier (k : ℤ) x).re * (fourier (k : ℤ) y).re +
      (fourier (k : ℤ) x).im * (fourier (k : ℤ) y).im := by
  induction x using QuotientAddGroup.induction_on with
  | _ t =>
    induction y using QuotientAddGroup.induction_on with
    | _ u =>
      change (fourier (k : ℤ) ((t-u : ℝ) : UnitAddCircle)).re = _
      simp only [cosine_coe_real, sine_coe_real, mul_sub, Real.cos_sub]

private theorem shifted_tent_cosine {k : ℕ} (hk : 0 < k) (x : UnitAddCircle) :
    (∫ y : UnitAddCircle, ‖y‖ * (fourier (k : ℤ) (x-y)).re ∂haarAddCircle) =
      (fourier (k : ℤ) x).re * (((-1 : ℝ)^k - 1) / (2 * Real.pi^2 * (k:ℝ)^2)) := by
  let f := fourier (T := (1:ℝ)) (k:ℤ)
  have h (y : UnitAddCircle) : ‖y‖ * (fourier (k : ℤ) (x-y)).re =
      (f x).re * (‖y‖ * (f y).re) + (f x).im * (‖y‖ * (f y).im) := by
    rw [cosine_sub_circle]; dsimp [f]; ring
  simp_rw [h]
  rw [integral_add, integral_const_mul, integral_const_mul, integral_tent_cosine hk,
    integral_tent_sine]
  · simp [f]
  · exact (continuous_const.mul (continuous_norm.mul (Complex.continuous_re.comp f.continuous))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_const.mul (continuous_norm.mul (Complex.continuous_im.comp f.continuous))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

private theorem kernel_cont (H : ℕ) : Continuous (FractionalFejer.kernel H 0) := by
  change Continuous (fun t : UnitAddCircle => FractionalFejer.kernel H 0 t)
  simp only [FractionalFejer.kernel, sub_zero, one_mul, zero_mul, add_zero,
    FractionalFejer.dirichlet]
  exact (continuous_finsetSum (range H) fun (j : ℕ) _ =>
    (fourier (T := (1:ℝ)) (j:ℤ)).continuous).norm.pow 2

private theorem kernel_mass (H : ℕ) :
    (∫ t : UnitAddCircle, FractionalFejer.kernel H 0 t ∂haarAddCircle) = H := by
  have h := FractionalFejer.integral_kernel_mode H 0 0
  simpa [integral_complex_ofReal] using congrArg Complex.re h

def fejerConvolution (H : ℕ) (x : UnitAddCircle) : ℝ :=
  ∫ y, FractionalFejer.kernel H 0 y * ‖x-y‖ ∂haarAddCircle

private theorem convolution_lipschitz (H : ℕ) (x z : UnitAddCircle) :
    |fejerConvolution H x - fejerConvolution H z| ≤ (H : ℝ) * dist x z := by
  let K := FractionalFejer.kernel H 0
  have hK (t : UnitAddCircle) : 0 ≤ K t := FractionalFejer.kernel_nonneg le_rfl zero_le_one H t
  have hi (v : UnitAddCircle) : Integrable (fun y => K y * ‖v-y‖) haarAddCircle :=
    ((kernel_cont H).mul (continuous_const.sub continuous_id).norm).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [fejerConvolution, fejerConvolution, ← integral_sub (hi x) (hi z), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y, ‖K y * ‖x-y‖ - K y * ‖z-y‖‖ ∂haarAddCircle := norm_integral_le_integral_norm _
    _ ≤ ∫ y, K y * dist x z ∂haarAddCircle := by
      apply integral_mono ((hi x).sub (hi z)).norm
        (((kernel_cont H).mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      intro y
      change ‖K y * ‖x-y‖ - K y * ‖z-y‖‖ ≤ K y * dist x z
      rw [← mul_sub, norm_mul, Real.norm_eq_abs (K y), abs_of_nonneg (hK y)]
      apply mul_le_mul_of_nonneg_left _ (hK y)
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right, Real.norm_eq_abs]
        using abs_norm_sub_norm_le (x-y) (z-y)
    _ = _ := by rw [integral_mul_const, kernel_mass]

/-- The anchored odd-mode cosine polynomial at Fejér width `2*N`. -/
def fejerTentWeight (N j : ℕ) : ℝ :=
  (2 / Real.pi^2) * (1 - ((2*j+1 : ℕ) : ℝ)/(2*(N:ℝ))) / ((2*j+1 : ℕ) : ℝ)^2

def fejerTent (N : ℕ) : C(UnitAddCircle, ℝ) where
  toFun x := ∑ j ∈ range N, fejerTentWeight N j * (1 - (fourier (2*j+1 : ℕ) x).re)
  continuous_toFun := continuous_finsetSum _ fun _j _ =>
    continuous_const.mul (continuous_const.sub (Complex.continuous_re.comp (fourier _).continuous))

@[simp] theorem fejerTent_zero (N : ℕ) : fejerTent N 0 = 0 := by
  simp [fejerTent]

private theorem sum_paired (f : ℕ → ℝ) (N : ℕ) :
    ∑ h ∈ Ioc 0 (2*N), f h = ∑ j ∈ range N, (f (2*j+1) + f (2*j+2)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega), ih,
      sum_range_succ]; ring

private theorem convolution_expansion (H : ℕ) (x : UnitAddCircle) :
    fejerConvolution H x = (H : ℝ) * (∫ y : UnitAddCircle, ‖y‖ ∂haarAddCircle) +
      ∑ k ∈ Ioc 0 H, (2*((H:ℝ)-k)) * ((fourier (k : ℤ) x).re *
        (((-1:ℝ)^k-1)/(2*Real.pi^2*(k:ℝ)^2))) := by
  have hc (k : ℕ) : Continuous (fun y : UnitAddCircle =>
      (2*((H:ℝ)-k)) * (‖y‖ * (fourier (k:ℤ) (x-y)).re)) :=
    continuous_const.mul (continuous_norm.mul (Complex.continuous_re.comp
      ((fourier _).continuous.comp (continuous_const.sub continuous_id))))
  rw [fejerConvolution, ← integral_sub_left_eq_self _ haarAddCircle x]
  simp only [sub_sub_cancel]
  have he (y : UnitAddCircle) :
      FractionalFejer.kernel H 0 (x-y) * ‖y‖ =
        (H:ℝ)*‖y‖ + ∑ k ∈ Ioc 0 H, (2*((H:ℝ)-k)) * (‖y‖ * (fourier (k:ℤ) (x-y)).re) := by
    rw [FractionalFejer.kernel_cosine_expansion]; simp only [add_zero, add_mul, sum_mul]
    congr 1; apply sum_congr rfl; intro k _; ring
  simp_rw [he]
  rw [integral_add, integral_const_mul, integral_finsetSum]
  · congr 1; apply sum_congr rfl; intro k hk
    rw [integral_const_mul, shifted_tent_cosine (mem_Ioc.mp hk).1]
  · intro k hk; exact (hc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (continuous_const.mul continuous_norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (continuous_finsetSum _ fun k _ => hc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem fejerTent_eq_convolution {N : ℕ} (hN : 0 < N) (x : UnitAddCircle) :
    fejerTent N x = (fejerConvolution (2*N) x - fejerConvolution (2*N) 0) / (2*(N:ℝ)) := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  change (∑ j ∈ range N, fejerTentWeight N j * (1 - (fourier (2*j+1 : ℕ) x).re)) = _
  rw [convolution_expansion, convolution_expansion, add_sub_add_left_eq_sub, ← sum_sub_distrib, sum_paired,
    sum_div]
  apply sum_congr rfl
  intro j hj
  simp only [fourier_eval_zero, Complex.one_re, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_one, pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul, sub_self,
    zero_div, mul_zero, add_zero, fejerTentWeight]
  field_simp [hn, Real.pi_ne_zero]
  ring

/-- Positivity and the exact mass of the Fejér kernel preserve Lipschitz constant one. -/
theorem fejerTent_lipschitz (N : ℕ) (x y : UnitAddCircle) :
    |fejerTent N x - fejerTent N y| ≤ dist x y := by
  cases N with
  | zero => simp [fejerTent]
  | succ n =>
    have hN : 0 < n+1 := Nat.zero_lt_succ n
    rw [fejerTent_eq_convolution hN, fejerTent_eq_convolution hN, ← sub_div,
      sub_sub_sub_cancel_right, abs_div, abs_of_pos (by positivity : 0 < 2*((n+1 : ℕ) : ℝ))]
    apply (div_le_iff₀ (by positivity)).2
    simpa [mul_comm, Nat.cast_mul] using convolution_lipschitz (2*(n+1)) x y

end RiemannResearch.Analysis.DyadicZeroWasserstein
