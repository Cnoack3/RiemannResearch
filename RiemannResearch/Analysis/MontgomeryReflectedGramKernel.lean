import RiemannResearch.Analysis.MontgomeryCentralDifference
import RiemannResearch.Analysis.MontgomeryCauchyGram
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The quartic reflected Montgomery pair kernel

The central difference in each zero displacement keeps the horizontal shifts
together in the pair Gram. A complex Cauchy estimate preserves the Cauchy
weight in the ordinate separation uniformly up to the fourth derivative. -/

noncomputable section
open Filter Set Metric
namespace RiemannResearch.Analysis.MontgomeryCentralDifference
open MontgomeryPoisson

/-- Complex exponential and Laplace kernel at a horizontal shift. -/
def phaseKernel (u d : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((u:ℂ)*z) * (4 / (4 - (z + Complex.I*d)^2))

/-- Complete mixed central difference for a pair of reflected features. -/
def reflectedPairKernel (u a b d : ℝ) : ℂ :=
  central a (central b (fun x : ℝ => phaseKernel u d (x:ℂ))) 0

private theorem denominator_lower {z : ℂ} (d : ℝ)
    (hr : |z.re| ≤ 3 / 2) (hi : |z.im| ≤ 1 / 2) :
    (4+d^2)/4 ≤ ‖(4-(z+Complex.I*(d:ℂ))^2 : ℂ)‖ := by
  have he : (4-(z+Complex.I*(d:ℂ))^2 : ℂ).re = 4-z.re^2+(z.im+d)^2 := by
    simp [pow_two]
    ring
  have hr2 : z.re^2 ≤ (3 / 2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z.re) (by norm_num)).2 hr
  have hi2 : z.im^2 ≤ (1 / 2 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z.im) (by norm_num)).2 hi
  apply le_trans _ (Complex.re_le_norm _)
  rw [he]
  nlinarith [sq_nonneg (d + 2*z.im)]

private theorem phaseKernel_analytic (u d : ℝ) (z : ℂ)
    (hr : |z.re| ≤ 3 / 2) (hi : |z.im| ≤ 1 / 2) :
    AnalyticAt ℂ (phaseKernel u d) z := by
  have h := denominator_lower d hr hi
  have hn : (4-(z+Complex.I*(d:ℂ))^2 : ℂ) ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at h
    nlinarith [sq_nonneg d]
  unfold phaseKernel
  fun_prop (disch := exact hn)

private theorem phaseKernel_fourth {s x : ℝ} (u d : ℝ)
    (hxs : |x| ≤ s) (hs : s ≤ 1) :
    ‖iteratedDeriv 4 (phaseKernel u d) (x:ℂ)‖ ≤
      (1536*Real.exp 1)*(1+|u|)^4*Real.exp (|u| * s)*cauchyWeight d := by
  let r := 1/(2*(1+|u|))
  have hu := abs_nonneg u
  have hpos : 0 < 2*(1+|u|) := by positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrsmall : r ≤ 1 / 2 := (div_le_iff₀ hpos).2 (by linarith)
  have hursmall : |u| * r ≤ 1 := by
    dsimp [r]
    rw [mul_one_div]
    exact (div_le_iff₀ hpos).2 (by linarith)
  have near {z : ℂ} (hz : ‖z - (x:ℂ)‖ ≤ r) :
      |z.re| ≤ s+r ∧ |z.re| ≤ 3 / 2 ∧ |z.im| ≤ 1 / 2 := by
    have hnorm := norm_add_le (z-(x:ℂ)) (x:ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at hnorm
    have hre := Complex.abs_re_le_norm z
    have him := Complex.abs_im_le_norm (z-(x:ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    exact ⟨by linarith, by linarith, by linarith⟩
  have hdiff : DiffContOnCl ℂ (phaseKernel u d) (ball (x:ℂ) r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    intro z hz
    have h := near (mem_closedBall_iff_norm.mp hz)
    exact (phaseKernel_analytic u d z h.2.1 h.2.2).differentiableAt.differentiableWithinAt
  let B := Real.exp (|u| * s+1)*(4*cauchyWeight d)
  have hsup (z : ℂ) (hz : z ∈ sphere (x:ℂ) r) : ‖phaseKernel u d z‖ ≤ B := by
    obtain ⟨hzs,hre,him⟩ := near (mem_sphere_iff_norm.mp hz).le
    have he : ‖Complex.exp ((u:ℂ)*z)‖ ≤ Real.exp (|u| * s+1) := by
      rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      apply Real.exp_le_exp.mpr
      calc
        u*z.re ≤ |u*z.re| := le_abs_self _
        _ ≤ |u| * (s+r) := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hzs hu
        _ ≤ _ := by linarith only [hursmall]
    have hd := denominator_lower d hre him
    have hk : ‖(4/(4-(z+Complex.I*(d:ℂ))^2) : ℂ)‖ ≤ 4*cauchyWeight d := by
      rw [norm_div, show ‖(4:ℂ)‖ = 4 by norm_num]
      calc
        _ ≤ 4/((4+d^2)/4) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
        _ = _ := by
          unfold cauchyWeight
          simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    exact (norm_mul _ _).le.trans (mul_le_mul he hk (norm_nonneg _) (Real.exp_pos _).le)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 4 hr hdiff hsup
  apply h.trans_eq
  dsimp only [B,r]
  rw [Real.exp_add]
  rw [div_pow, one_pow, div_div_eq_mul_div, div_one]
  norm_num [Nat.factorial]
  ring

/-- Fourth-order pair estimate for all displacements and all phase frequencies.
Its ordinate weight is the original Cauchy weight. -/
theorem reflectedPairKernel_norm_le (u a b d : ℝ) (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    ‖reflectedPairKernel u a b d‖ ≤
      (1536 * Real.exp 1) * (1+|u|)^4 * Real.exp (|u| * (|a| + |b|)) *
        a^2*b^2*cauchyWeight d := by
  let s := |a| + |b|
  let M := (1536 * Real.exp 1) * (1+|u|)^4 * Real.exp (|u| * s) * cauchyWeight d
  let F := phaseKernel u d
  let jet := fun n : ℕ => fun x : ℝ => iteratedDeriv n F (x:ℂ)
  have hs : s ≤ 1 := by dsimp [s]; linarith
  have hj (n : ℕ) (x : ℝ) (hx : x ∈ Icc (-s) s) :
      HasDerivAt (jet n) (jet (n+1) x) x := by
    have hxr := (abs_le.mpr hx).trans hs
    have hf : AnalyticAt ℂ F (x:ℂ) := by
      apply phaseKernel_analytic u d (x:ℂ)
      · simpa using hxr.trans (by norm_num : (1:ℝ) ≤ 3 / 2)
      · norm_num
    have hjet : AnalyticAt ℂ (iteratedDeriv n F) (x:ℂ) := by
      induction n with
      | zero => simpa using hf
      | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
    simpa only [jet,iteratedDeriv_succ] using hjet.differentiableAt.hasDerivAt.comp_ofReal
  have hfirst (x : ℝ) (hx : x ∈ Icc (-s) s) : HasDerivAt (fun x : ℝ => F (x:ℂ)) (jet 1 x) x := by
    simpa only [jet,iteratedDeriv_zero] using hj 0 x hx
  have hfourth (x : ℝ) (hx : x ∈ Icc (-s) s) : ‖jet 4 x‖ ≤ M :=
    phaseKernel_fourth u d (abs_le.mpr hx) hs
  apply (mixed_central_norm_le (fun x : ℝ => F (x:ℂ)) (jet 1) (jet 2) (jet 3) (jet 4)
    a b M hfirst (hj 1) (hj 2) (hj 3) hfourth).trans_eq
  dsimp [M,s]
  ring

end RiemannResearch.Analysis.MontgomeryCentralDifference
