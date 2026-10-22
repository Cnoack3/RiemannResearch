import RiemannResearch.Analysis.ScaledKernelFirstOrder
import RiemannResearch.Analysis.BroadKernelNormalization
import RiemannResearch.Analysis.BroadProfileRegularity
import RiemannResearch.RH.NymanReturnKernelMoments

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Quadratic energy remainder for the actual broad arithmetic family

The kernel's first-order moment expansion has the form m φ+b φ'/R.
The cross energy vanishes exactly because the compact real seed satisfies
∫φφ'=0. A uniform quadratic remainder and actual L¹ bounds therefore give
the O(R⁻²) squared-norm estimate asserted in Lemma 6.1 of the continuation.
-/

open MeasureTheory Set
namespace RiemannResearch.Analysis

noncomputable section

private theorem abs_four_term_le (a b c d x y z w : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
    |a*x+b*y-c*z-d*w| ≤ a * |x|+b * |y|+c * |z|+d * |w| := by
  calc
    _ ≤ |a*x+b*y-c*z|+|d*w| := abs_sub _ _
    _ ≤ (|a*x+b*y|+|c*z|)+|d*w| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ ((|a*x|+|b*y|)+|c*z|)+|d*w| :=
      add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ = _ := by simp only [abs_mul,abs_of_nonneg ha,abs_of_nonneg hb,
      abs_of_nonneg hc,abs_of_nonneg hd]

/-- Actual sup-norm first-order expansion of the finite differential profile. -/
theorem differentialBroadKernelProfile_first_order_bound (h φ : ℝ → ℝ)
    (hh : Integrable h) (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (hc : HasCompactSupport φ)
    (hm1 : Integrable (fun v => |v| * |h v|))
    (hm2 : Integrable (fun v => v^2 * |h v|)) :
    ∃ E : ℝ, 0≤E ∧ ∀ R : ℝ, 1≤R → ∀ x : ℝ,
      |differentialBroadKernelProfile h φ R x - (-(∫v,h v)/8)*φ x -
        (((∫v,v*h v)/8-(∫v,h v)/4)/R)*deriv φ x| ≤ E/R^2 := by
  obtain ⟨M,hM0,hM⟩ := broadProfile_exists_all_derivative_bounds hφ hc
  have hM20 : 0 ≤ M 2 := hM0 2
  have hM30 : 0 ≤ M 3 := hM0 3
  have hd := hφ.differentiable (by simp)
  have hdd : Differentiable ℝ (deriv φ) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      (broadProfile_contDiff_iteratedDeriv hφ 1).differentiable (by simp)
  have hMbase (x : ℝ) : |φ x|≤M 0 := by simpa only [iteratedDeriv_zero] using hM 0 x
  have hMone (x : ℝ) : |deriv φ x|≤M 1 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hM 1 x
  have hMtwo (x : ℝ) : |deriv (deriv φ) x|≤M 2 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hM 2 x
  have hK (x y : ℝ) : |deriv φ x-deriv φ y|≤M 2 * |x-y| := by
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le
      (f:=deriv φ) (s:=univ) (x:=y) (y:=x)
      (fun z _ => hdd z) (fun z _ => by simpa only [Real.norm_eq_abs] using hMtwo z)
      convex_univ (mem_univ _) (mem_univ _)
    simpa only [Real.norm_eq_abs] using hm
  let H : ℝ := ∫v,|h v|
  let J : ℝ := ∫v,|v| * |h v|
  let Q : ℝ := ∫v,v^2 * |h v|
  let E : ℝ := H*(M 3+M 2)+M 2*J+M 2*Q
  have hH : 0≤H := integral_nonneg (fun v => abs_nonneg _)
  have hJ : 0≤J := integral_nonneg (fun v => by positivity)
  have hQ : 0≤Q := integral_nonneg (fun v => by positivity)
  refine ⟨E,by unfold E; positivity,?_⟩
  intro R hR x
  have hR0 : 0<R := by linarith
  let t : ℝ := R⁻¹
  have ht0 : 0≤t := inv_nonneg.mpr hR0.le
  have ht1 : t≤1 := inv_le_one_of_one_le₀ hR
  have ht2 : 0≤t^2 := sq_nonneg _
  have ht3 : t^3≤t^2 := by
    calc
      t^3 = t^2*t := by ring
      _ ≤ t^2*1 := mul_le_mul_of_nonneg_left ht1 ht2
      _ = t^2 := mul_one _
  let A3 : ℝ := scaledKernelConvolution h (iteratedDeriv 3 φ) R x
  let A2 : ℝ := scaledKernelConvolution h (iteratedDeriv 2 φ) R x
  let A1 : ℝ := scaledKernelConvolution h (deriv φ) R x-(∫v,h v)*deriv φ x
  let A0 : ℝ := scaledKernelConvolution h φ R x-(∫v,h v)*φ x+
    ((∫v,v*h v)/R)*deriv φ x
  have h3 : |A3|≤H*M 3 := abs_scaledKernelConvolution_le h _ hh _ (hM 3) R x
  have h2 : |A2|≤H*M 2 := abs_scaledKernelConvolution_le h _ hh _ (hM 2) R x
  have h1 : |A1|≤t*(M 2*J) := by
    have hb := abs_scaledKernelConvolution_sub_mass_le h (deriv φ) hh hdd.continuous
      (M 1) (M 2) hMone hK hm1 R x
    simpa only [abs_of_pos hR0,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,t,J,A1] using hb
  have h0 : |A0|≤t^2*(M 2*Q) := by
    have hb := abs_scaledKernelConvolution_first_order_le h φ hh hd hdd
      (M 0) (M 2) hMbase hMtwo hm1 hm2 R x
    simpa only [div_eq_mul_inv,inv_pow,mul_assoc,mul_comm,mul_left_comm,t,Q,A0] using hb
  have he : differentialBroadKernelProfile h φ R x - (-(∫v,h v)/8)*φ x -
      (((∫v,v*h v)/8-(∫v,h v)/4)/R)*deriv φ x =
      t^3*A3+t^2/2*A2-t/4*A1-(1/8)*A0 := by
    simp only [differentialBroadKernelProfile,broadKernelProfile,
      iteratedDeriv_succ,iteratedDeriv_zero,A3,A2,A1,A0,t]
    ring
  rw [he]
  calc
    _ ≤ t^3 * |A3|+t^2/2 * |A2|+t/4 * |A1|+(1/8) * |A0| :=
      abs_four_term_le _ _ _ _ _ _ _ _ (by positivity) (by positivity)
        (by positivity) (by norm_num)
    _ ≤ t^3*(H*M 3)+t^2/2*(H*M 2)+t/4*(t*(M 2*J))+
        (1/8)*(t^2*(M 2*Q)) := by gcongr
    _ ≤ t^2*(H*M 3)+t^2*(H*M 2)+t^2*(M 2*J)+t^2*(M 2*Q) := by
      have h3' := mul_le_mul_of_nonneg_right ht3 (mul_nonneg hH (hM0 3))
      have h2' : 0≤t^2*(H*M 2) := mul_nonneg ht2 (mul_nonneg hH hM20)
      have h1' : 0≤t^2*(M 2*J) := mul_nonneg ht2 (mul_nonneg hM20 hJ)
      have h0' : 0≤t^2*(M 2*Q) := mul_nonneg ht2 (mul_nonneg hM20 hQ)
      nlinarith
    _ = E/R^2 := by unfold E t; simp only [div_eq_mul_inv,inv_pow]; ring

/-- The first-order energy cross term vanishes for the actual real compact seed. -/
theorem broadProfile_integral_mul_deriv_eq_zero {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (hc : HasCompactSupport φ) :
    (∫x,φ x*deriv φ x)=0 := by
  have hd := hφ.differentiable (by simp)
  have hdc : Continuous (deriv φ) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      broadProfile_continuous_iteratedDeriv hφ 1
  have hi : Integrable (fun x=>φ x*deriv φ x) := by
    apply (hφ.continuous.mul hdc).integrable_of_hasCompactSupport
    exact hc.mul_right
  have hder (x : ℝ) : HasDerivAt (fun y=>φ y^2) (2*(φ x*deriv φ x)) x := by
    convert (hd x).hasDerivAt.pow 2 using 1 <;> first | rfl | (norm_num; ring)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hder (hi.const_mul 2)
    (broadProfile_integrable_sq hφ hc)
  rw [integral_const_mul] at hz
  linarith

/-- The O(R⁻²) energy rate for an actual smooth compact profile and actual kernel. -/
theorem differentialBroadKernelEnergy_second_order_bound (h φ : ℝ → ℝ)
    (hh : Integrable h) (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (hc : HasCompactSupport φ)
    (hm1 : Integrable (fun v=>|v| * |h v|))
    (hm2 : Integrable (fun v=>v^2 * |h v|)) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, 1≤R →
      |broadKernelEnergy h (fun j=>iteratedDeriv j φ) R-
        (-(∫v,h v)/8)^2*(∫x,φ x^2)|≤C/R^2 := by
  obtain ⟨E,hE,herr⟩ := differentialBroadKernelProfile_first_order_bound h φ hh hφ hc hm1 hm2
  obtain ⟨M,hM0,hM⟩ := broadProfile_exists_all_derivative_bounds hφ hc
  let F : ℕ → ℝ → ℝ := fun j=>iteratedDeriv j φ
  have hfi (j : ℕ) : Integrable (F j) := broadProfile_integrable_iteratedDeriv hφ hc j
  have hfc (j : ℕ) : Continuous (F j) := broadProfile_continuous_iteratedDeriv hφ j
  have hdi : Integrable (deriv φ) := by
    simpa only [F,iteratedDeriv_succ,iteratedDeriv_zero] using hfi 1
  have hdc : Continuous (deriv φ) := by
    simpa only [F,iteratedDeriv_succ,iteratedDeriv_zero] using hfc 1
  have hMbase (x : ℝ) : |φ x|≤M 0 := by simpa only [iteratedDeriv_zero] using hM 0 x
  have hMone (x : ℝ) : |deriv φ x|≤M 1 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hM 1 x
  have hpi : Integrable φ := by simpa only [F,iteratedDeriv_zero] using hfi 0
  have hip : Integrable (fun x=>φ x*deriv φ x) := by
    apply (hφ.continuous.mul hdc).integrable_of_hasCompactSupport
    exact hc.mul_right
  have hip2 := broadProfile_integrable_sq hφ hc
  have hid2 := integrable_sq_of_integrable_of_abs_le (deriv φ) hdi (M 1) hMone
  have hcross := broadProfile_integral_mul_deriv_eq_zero hφ hc
  let H : ℝ := ∫v,|h v|
  let m : ℝ := -(∫v,h v)/8
  let b : ℝ := (∫v,v*h v)/8-(∫v,h v)/4
  let L : ℝ := H*((∫x,|F 3 x|)+(∫x,|F 2 x|)+(∫x,|F 1 x|)+(∫x,|F 0 x|))
  let G : ℝ := |m| * (∫x,|φ x|)+|b| * (∫x,|deriv φ x|)
  let Q : ℝ := ∫x,deriv φ x^2
  have hH0 : 0≤H := integral_nonneg (fun x=>abs_nonneg _)
  have hL0 : 0≤L := by unfold L; positivity
  have hG0 : 0≤G := by unfold G; positivity
  have hQ0 : 0≤Q := integral_nonneg (fun x=>sq_nonneg _)
  let C : ℝ := E*(L+G)+b^2*Q
  refine ⟨C,by unfold C; positivity,?_⟩
  intro R hR
  have hR0 : 0<R := by linarith
  have hab : |b/R|≤|b| := by
    rw [abs_div,abs_of_pos hR0]
    exact div_le_self (abs_nonneg _) hR
  let g : ℝ → ℝ := fun x=>m*φ x+(b/R)*deriv φ x
  have hg : Integrable g := (hpi.const_mul m).add (hdi.const_mul (b/R))
  have hgb (x : ℝ) : |g x|≤|m| * M 0+|b| * M 1 := by
    calc
      _ ≤ |m*φ x|+|(b/R)*deriv φ x| := abs_add_le _ _
      _ = |m| * |φ x|+|b/R| * |deriv φ x| := by rw [abs_mul,abs_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (hMbase x) (abs_nonneg _))
        (mul_le_mul hab (hMone x) (abs_nonneg _) (abs_nonneg _))
  have hgL : (∫x,|g x|)≤G := by
    calc
      _ ≤ ∫x,|m| * |φ x|+|b| * |deriv φ x| := by
        apply integral_mono_ae hg.abs ((hpi.abs.const_mul _).add (hdi.abs.const_mul _))
        apply ae_of_all
        intro x
        calc
          _ ≤ |m*φ x|+|(b/R)*deriv φ x| := abs_add_le _ _
          _ = |m| * |φ x|+|b/R| * |deriv φ x| := by rw [abs_mul,abs_mul]
          _ ≤ |m| * |φ x|+|b| * |deriv φ x| :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hab (abs_nonneg _))
      _ = G := by
        rw [integral_add (hpi.abs.const_mul _) (hdi.abs.const_mul _)]
        simp only [integral_const_mul,G]
  have hgQ : (∫x,g x^2)=m^2*(∫x,φ x^2)+(b/R)^2*Q := by
    have hsum : Integrable (fun x =>
        m^2*φ x^2+(2*m*(b/R))*(φ x*deriv φ x)) :=
      (hip2.const_mul _).add (hip.const_mul _)
    calc
      _ = ∫x,(m^2*φ x^2+(2*m*(b/R))*(φ x*deriv φ x))+(b/R)^2*deriv φ x^2 := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x=>by dsimp [g]; ring)
      _ = _ := by
        rw [integral_add hsum (hid2.const_mul _),
          integral_add (hip2.const_mul _) (hip.const_mul _)]
        simp only [integral_const_mul,hcross,mul_zero,add_zero,Q]
  have hB := integrable_broadKernelProfile h F hh hfi hfc R
  have hBb := abs_broadKernelProfile_le h F hh M hM hR
  have hBL : (∫x,|broadKernelProfile h F R x|)≤L :=
    integral_abs_broadKernelProfile_le h F hh hfi hfc hR
  have hdiff (x : ℝ) : |broadKernelProfile h F R x-g x|≤E/R^2 := by
    have he : broadKernelProfile h F R x-g x =
        differentialBroadKernelProfile h φ R x - (-(∫v,h v)/8)*φ x -
          (((∫v,v*h v)/8-(∫v,h v)/4)/R)*deriv φ x := by
      dsimp [g,F,m,b,differentialBroadKernelProfile]
      ring
    rw [he]
    exact herr R hR x
  have hsq := abs_integral_sq_sub_le (broadKernelProfile h F R) g hB hg
    (H*(M 3+M 2+M 1+M 0)) (|m| * M 0+|b| * M 1) (E/R^2) hBb hgb hdiff
  have hsmall : |(∫x,g x^2)-m^2*(∫x,φ x^2)|=(b/R)^2*Q := by
    rw [hgQ,add_sub_cancel_left,abs_of_nonneg (mul_nonneg (sq_nonneg _) hQ0)]
  change |broadKernelEnergy h F R-m^2*(∫x,φ x^2)|≤C/R^2
  calc
    _ ≤ |broadKernelEnergy h F R-(∫x,g x^2)|+|(∫x,g x^2)-m^2*(∫x,φ x^2)| :=
      abs_sub_le _ _ _
    _ ≤ (E/R^2)*((∫x,|broadKernelProfile h F R x|)+(∫x,|g x|))+(b/R)^2*Q := by
      rw [hsmall]
      exact add_le_add hsq le_rfl
    _ ≤ (E/R^2)*(L+G)+(b/R)^2*Q := by
      exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hBL hgL)
        (div_nonneg hE (sq_nonneg _))) le_rfl
    _ = C/R^2 := by unfold C; rw [div_pow]; ring

end
end RiemannResearch.Analysis

namespace RiemannResearch.RH
open RiemannResearch.Analysis

/-- The precise O(R⁻²) energy remainder, instantiated with the actual
arithmetic kernel. All kernel moments are proved from its floor formula. -/
theorem nymanBroadKernelEnergy_second_order_bound {n : ℕ} (hn : 0<n)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0≤C ∧ ∀ R : ℝ, 1≤R →
      |broadKernelEnergy (nymanReturnKernel n) (fun j=>iteratedDeriv j φ) R-
        (-(∫v,nymanReturnKernel n v)/8)^2*(∫x,φ x^2)|≤C/R^2 := by
  apply differentialBroadKernelEnergy_second_order_bound _ _
    (integrable_nymanReturnKernel hn) hφ hc
    (integrable_abs_mul_abs_nymanReturnKernel hn)
  convert integrable_pow_abs_nymanReturnKernel hn 2 using 1
  ext v
  rw [sq_abs,abs_of_nonneg (nymanReturnKernel_nonneg hn v)]

end RiemannResearch.RH
