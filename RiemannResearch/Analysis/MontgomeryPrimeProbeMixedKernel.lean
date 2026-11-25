import RiemannResearch.Analysis.MontgomeryPrimeProbeMertensTests
import RiemannResearch.Analysis.MontgomeryPrimeProbeQuadraticFourier
import Mathlib.MeasureTheory.Integral.Prod

/-! # The mixed prime–continuum term as a bounded sine-integral test -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set ZeroOrdinate
open scoped Topology BigOperators

def probeSi (x : ℝ) : ℝ := ∫ y in (0:ℝ)..x, Real.sinc y

private theorem probeSi_deriv (x : ℝ) : HasDerivAt probeSi (Real.sinc x) x :=
  intervalIntegral.integral_hasDerivAt_right (Real.continuous_sinc.intervalIntegrable 0 x)
    Real.continuous_sinc.stronglyMeasurable.stronglyMeasurableAtFilter
    Real.continuous_sinc.continuousAt

theorem abs_probeSi_le {x : ℝ} (hx : 0 ≤ x) : |probeSi x| ≤ 4 := by
  have small {v : ℝ} (hv : 0 ≤ v) : |probeSi v| ≤ v := by
    simpa [probeSi,Real.norm_eq_abs,abs_of_nonneg hv] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := v)
        (f := Real.sinc) (C := 1) (fun t _ => Real.abs_sinc_le_one t))
  by_cases hx1 : x ≤ 1
  · linarith only [small hx,hx1]
  have h1x : 1 ≤ x := le_of_not_ge hx1
  have hpos {t : ℝ} (ht : t ∈ uIcc 1 x) : 0 < t := by rw [uIcc_of_le h1x] at ht; linarith [ht.1]
  have hd (t : ℝ) (ht : t ∈ uIcc 1 x) : HasDerivAt (fun t => -Real.cos t/t)
      (Real.sinc t + Real.cos t/t^2) t := by
    have he : Real.sinc t + Real.cos t/t^2 =
        ((- -Real.sin t)*t-(-Real.cos t)*1)/t^2 := by
      rw [Real.sinc_of_ne_zero (hpos ht).ne']
      field_simp [(hpos ht).ne']
      <;> ring
    rw [he]
    exact (Real.hasDerivAt_cos t).neg.div (hasDerivAt_id t) (hpos ht).ne'
  have hi : IntervalIntegrable (fun t : ℝ => Real.cos t/t^2) volume 1 x :=
    (Real.continuous_cos.continuousOn.div (continuous_id.pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (hpos ht).ne')).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_sinc.intervalIntegrable 1 x).add hi)
  rw [intervalIntegral.integral_add (Real.continuous_sinc.intervalIntegrable 1 x) hi] at h
  have hi' : IntervalIntegrable (fun t : ℝ => 1/t^2) volume 1 x :=
    (continuousOn_const.div (continuous_id.pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (hpos ht).ne')).intervalIntegrable
  have hd' (t : ℝ) (ht : t ∈ uIcc 1 x) : HasDerivAt (fun t : ℝ => -t⁻¹) (1/t^2) t := by
    have h : HasDerivAt (fun s : ℝ => (-1)/s) ((0*t-(-1)*1)/t^2) t :=
      (hasDerivAt_const t (-1:ℝ)).div (hasDerivAt_id t) (hpos ht).ne'
    simpa [neg_div,one_div] using h
  have htail : |∫ t in (1:ℝ)..x, Real.cos t/t^2| ≤ 1 := calc
    _ ≤ ∫ t in (1:ℝ)..x, |Real.cos t/t^2| := intervalIntegral.abs_integral_le_integral_abs h1x
    _ ≤ ∫ t in (1:ℝ)..x, 1/t^2 := by
      apply intervalIntegral.integral_mono_on h1x hi.abs hi'
      intro y _
      rw [abs_div,abs_of_nonneg (sq_nonneg y)]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one y) (sq_nonneg _)
    _ ≤ _ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd' hi']
      simp
      positivity
  have hc : |Real.cos x / x| ≤ 1 := by
    rw [abs_div,abs_of_nonneg hx]
    exact (div_le_self (abs_nonneg _) h1x).trans (Real.abs_cos_le_one x)
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (Real.continuous_sinc.intervalIntegrable (μ := volume) 0 1)
    (Real.continuous_sinc.intervalIntegrable 1 x)
  have hsmall := abs_le.mp (small (zero_le_one : (0:ℝ) ≤ 1))
  unfold probeSi at hsmall
  unfold probeSi
  rw [← hsum,abs_le]
  rw [neg_div,div_one] at h
  constructor <;> linarith only [h,hsmall.1,hsmall.2,(abs_le.mp htail).1,
    (abs_le.mp htail).2,(abs_le.mp hc).1,(abs_le.mp hc).2,
    (abs_le.mp (Real.abs_cos_le_one 1)).1,(abs_le.mp (Real.abs_cos_le_one 1)).2]

def probeMixedKernel (B L y : ℝ) : ℝ := probeSi (B*y)+probeSi (B*(L-y))

private def mixedDeriv (B L y : ℝ) : ℝ := B*Real.sinc (B*y)-B*Real.sinc (B*(L-y))

private theorem mixedKernel_deriv (B L y : ℝ) :
    HasDerivAt (probeMixedKernel B L) (mixedDeriv B L y) y := by
  have h := ((probeSi_deriv _).comp y ((hasDerivAt_id y).const_mul B)).add
    ((probeSi_deriv _).comp y (((hasDerivAt_id y).const_sub L).const_mul B))
  unfold mixedDeriv
  rw [show B*Real.sinc (B*y)-B*Real.sinc (B*(L-y)) =
    Real.sinc (B*y)*(B*1)+Real.sinc (B*(L-y))*(B*(-1)) by ring]
  exact h

/-- Both boundary strips have bounded test amplitude. Only the interior needs a derivative bound. -/
theorem probeMixedKernel_test_uniform :
    ∃ C > (0:ℝ), ∀ {B L : ℝ}, 0 ≤ B → 2 ≤ L → |primeLogTest L (probeMixedKernel B L)| ≤ C := by
  obtain ⟨C,hC,h⟩ := primeLogTest_uniform
  refine ⟨C*(8+2), by positivity, fun {B L} hB hL =>
    h hL (H := 8) (J := 2) (by norm_num) (by norm_num) (mixedKernel_deriv B L)
      (by unfold mixedDeriv; fun_prop) ?_ ?_⟩
  · intro y hy
    apply (abs_add_le _ _).trans
    simpa only [show (4:ℝ)+4=8 by norm_num] using (add_le_add (abs_probeSi_le (mul_nonneg hB hy.1))
      (abs_probeSi_le (mul_nonneg hB (sub_nonneg.mpr hy.2))))
  · have one {y : ℝ} (hy : 1 ≤ y) : |B*Real.sinc (B*y)| ≤ 1 := by
      rcases hB.eq_or_lt with rfl | hB
      · simp
      have hy' : 0 < y := by linarith
      rw [Real.sinc_of_ne_zero (mul_pos hB hy').ne',
        show B*(Real.sin (B*y)/(B*y)) = Real.sin (B*y)/y by field_simp,
        abs_div,abs_of_pos hy']
      exact (div_le_self (abs_nonneg _) hy).trans (Real.abs_sin_le_one _)
    intro y hy
    have hy' : 1 ≤ L-y := by linarith [hy.2]
    apply (abs_sub _ _).trans
    simpa only [one_add_one_eq_two] using add_le_add (one hy.1) (one hy')

/-- Real scalar product on the complex Fourier amplitudes. -/
def probePair (a b : ℂ) : ℝ := a.re*b.re + a.im*b.im

private theorem pair_symm (a b : ℂ) : probePair a b = probePair b a := by unfold probePair; ring

private theorem pair_integral {a b : ℝ} (c : ℂ) {f : ℝ → ℂ} (hf : Continuous f) :
    probePair c (∫ x in a..b, f x) = ∫ x in a..b, probePair c (f x) := by
  let M : ℂ →L[ℝ] ℝ := c.re • Complex.reCLM + c.im • Complex.imCLM
  exact (M.intervalIntegral_comp_comm (hf.intervalIntegrable _ _)).symm

private theorem pair_phase (y x t : ℝ) :
    probePair (phase y t) (phase x t) = Real.cos ((x-y)*t) := by
  have h := congrArg Complex.re (phase_sub x y t)
  have hr : (phase (x-y) t).re = Real.cos ((x-y)*t) := Complex.exp_ofReal_mul_I_re _
  rw [← hr,h]
  simp [probePair,Complex.mul_re,mul_comm]

private theorem pair_box_phase (L y t : ℝ) : probePair (logBoxProbe L t) (phase y t) =
    y*Real.sinc (y*t) + (L-y)*Real.sinc ((L-y)*t) := by
  rw [pair_symm,logBoxProbe,pair_integral _ (by unfold phase; fun_prop)]
  simp_rw [pair_phase, mul_comm (_ - y) t]
  rw [intervalIntegral.integral_comp_sub_right (fun x => Real.cos (t*x)) y]
  by_cases ht : t = 0
  · simp [ht]
  rw [intervalIntegral.integral_comp_mul_left Real.cos ht, smul_eq_mul, integral_cos,
    zero_sub, mul_neg, Real.sin_neg]
  have he (s : ℝ) : s*Real.sinc (s*t) = Real.sin (t*s)/t := by
    by_cases hs : s = 0
    · simp [hs]
    · rw [Real.sinc_of_ne_zero (mul_ne_zero hs ht),mul_comm s t]
      field_simp
  rw [he y,← mul_comm (L-y) t, he (L-y)]
  ring

theorem probeMixedKernel_fourier (B L y : ℝ) :
    (∫ t in (0:ℝ)..B, probePair (logBoxProbe L t) (phase y t)) = probeMixedKernel B L y := by
  simp_rw [pair_box_phase]
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun t : ℝ => y*Real.sinc (y*t))).intervalIntegrable 0 B)
    ((by fun_prop : Continuous (fun t : ℝ => (L-y)*Real.sinc ((L-y)*t))).intervalIntegrable 0 B)]
  simp only [intervalIntegral.integral_const_mul,
    intervalIntegral.mul_integral_comp_mul_left,mul_zero]
  dsimp [probeMixedKernel,probeSi]
  rw [mul_comm y B,mul_comm (L-y) B]

private theorem continuous_pair {X : Type*} [TopologicalSpace X] {f g : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => probePair (f x) (g x)) :=
  ((Complex.continuous_re.comp hf).mul (Complex.continuous_re.comp hg)).add
    ((Complex.continuous_im.comp hf).mul (Complex.continuous_im.comp hg))

/-- The mixed term is exactly a smooth test of the signed arithmetic measure. -/
theorem primeLogDiscrepancy_mixed_eq {L B : ℝ} (hL : 0 < L) (hB : 0 ≤ B) :
    (∫ t in (0:ℝ)..B, probePair (logBoxProbe L t) (primeLogDiscrepancy L t)) =
      primeLogTest L (probeMixedKernel B L) := by
  let F := fun t y => probePair (logBoxProbe L t) (phase y t)
  have hc : Continuous (Function.uncurry F) := by
    apply continuous_pair ((continuous_logBoxProbe hL).comp continuous_fst)
    unfold phase
    fun_prop
  have hs : (∫ t in (0:ℝ)..B, ∫ y in (0:ℝ)..L, F t y) =
      ∫ y in (0:ℝ)..L, ∫ t in (0:ℝ)..B, F t y := by
    simp only [intervalIntegral.integral_of_le hB, intervalIntegral.integral_of_le hL.le]
    apply integral_integral_swap
    rw [Measure.prod_restrict]
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hi (t : ℝ) : probePair (logBoxProbe L t) (primeLogDiscrepancy L t) =
      (∑ n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊, primeAtomWeight n * F t (Real.log n)) -
      probePair (logBoxProbe L t) (logBoxProbe L t) := by
    let c := logBoxProbe L t
    let M : ℂ →L[ℝ] ℝ := c.re • Complex.reCLM + c.im • Complex.imCLM
    change M (primeLogPolynomial L t - c) = (∑ n ∈ _, primeAtomWeight n*F t (Real.log n)) - M c
    rw [map_sub,primeLogPolynomial,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    change probePair c ((primeAtomWeight n:ℂ)*phase (Real.log n) t) =
      primeAtomWeight n*probePair c (phase (Real.log n) t)
    simp only [probePair,Complex.re_ofReal_mul,Complex.im_ofReal_mul]
    ring
  have ha (t : ℝ) : probePair (logBoxProbe L t) (logBoxProbe L t) = ∫ y in (0:ℝ)..L, F t y :=
    pair_integral _ (by unfold phase; fun_prop)
  have hn (n : ℕ) : Continuous (fun t => primeAtomWeight n*F t (Real.log n)) :=
    continuous_const.mul (hc.comp (continuous_id.prodMk continuous_const))
  have harr : Continuous (fun t => probePair (logBoxProbe L t) (logBoxProbe L t)) :=
    continuous_pair (continuous_logBoxProbe hL) (continuous_logBoxProbe hL)
  simp_rw [hi]
  rw [intervalIntegral.integral_sub
    ((continuous_finsetSum _ (fun n _ => hn n)).intervalIntegrable 0 B)
    (harr.intervalIntegrable 0 B),intervalIntegral.integral_finsetSum
      (fun n _ => (hn n).intervalIntegrable 0 B)]
  simp_rw [intervalIntegral.integral_const_mul,ha,hs]
  change (∑ n ∈ _, primeAtomWeight n*(∫ t in (0:ℝ)..B, probePair _ (phase (Real.log n) t))) -
      (∫ y in (0:ℝ)..L, ∫ t in (0:ℝ)..B, probePair (logBoxProbe L t) (phase y t)) = _
  simp_rw [probeMixedKernel_fourier]
  rfl

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeLogDiscrepancy_mixed_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeLogDiscrepancy_mixed_eq

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.probeMixedKernel_test_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms probeMixedKernel_test_uniform

end RiemannResearch.Analysis.MontgomeryPrimeTrace
