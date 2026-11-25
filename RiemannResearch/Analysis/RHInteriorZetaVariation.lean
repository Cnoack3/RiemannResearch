import RiemannResearch.Analysis.RHInteriorLogDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Varying the damping parameter off the real axis

On a zero-free segment the change in the logarithm of the modulus is
bounded by the segment length times the uniform logarithmic derivative.
In an interior strip for zeta this yields a power loss linear in the
length of the perturbation, uniformly at high ordinates. -/

noncomputable section
open Filter Complex Set
open scoped Topology
namespace RiemannResearch.Analysis.RHInteriorLogDerivative

theorem log_norm_variation_segment (f : ℂ → ℂ) (s v : ℂ) (K : ℝ)
    (hd : ∀ x ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ f (s+(x:ℂ)*v))
    (hz : ∀ x ∈ Icc (0:ℝ) 1, f (s+(x:ℂ)*v) ≠ 0)
    (hb : ∀ x ∈ Icc (0:ℝ) 1, ‖logDeriv f (s+(x:ℂ)*v)‖ ≤ K) :
    |Real.log ‖f s‖ - Real.log ‖f (s+v)‖| ≤ K*‖v‖ := by
  let p (x : ℝ) : ℂ := s+(x:ℂ)*v
  let g (x : ℝ) := f (p x)
  let h (x : ℝ) := Real.log (‖g x‖^2)
  have hp (x : ℝ) : HasDerivAt p v x := by
    have he : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := by simpa using (hasDerivAt_id x).ofReal_comp
    simpa only [one_mul] using (he.mul_const v).const_add s
  have hg x hx : HasDerivAt g (deriv f (p x)*v) x := (hd x hx).hasDerivAt.comp x (hp x)
  have hn x hx : 0 < ‖g x‖ := norm_pos_iff.mpr (hz x hx)
  have hh x hx := ((hg x hx).norm_sq).log (pow_pos (hn x hx) 2).ne'
  have hl : ‖h 0-h 1‖ ≤ (2*(K*‖v‖))*‖(0:ℝ)-1‖ := by
    apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Icc (0:ℝ) 1)
    · exact fun x hx => (hh x hx).differentiableAt
    · intro x hx
      rw [(hh x hx).deriv]
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (pow_pos (hn x hx) 2),abs_mul,abs_two]
      apply (div_le_iff₀ (pow_pos (hn x hx) 2)).mpr
      have hu := hb x hx
      rw [logDeriv_apply,norm_div,div_le_iff₀ (hn x hx)] at hu
      have hinner := abs_real_inner_le_norm (g x) (deriv f (p x)*v)
      rw [norm_mul] at hinner
      have hm := mul_le_mul_of_nonneg_right hu (norm_nonneg v)
      have hv := mul_le_mul_of_nonneg_left hm (norm_nonneg (g x))
      nlinarith only [hinner,hv]
    · exact convex_Icc _ _
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
  simp only [h,g,p,Complex.ofReal_zero,Complex.ofReal_one,zero_mul,one_mul,add_zero,
    Real.log_pow, Nat.cast_ofNat, Real.norm_eq_abs, zero_sub,abs_neg,abs_one,mul_one] at hl
  rw [←mul_sub,abs_mul,abs_two] at hl
  linarith

/-- A complex displacement of size r changes the reciprocal modulus by a
factor at most (2|t|)^(Cr) on each closed interior substrip. -/
theorem interior_zeta_norm_ratio_le (hRH : RiemannHypothesis) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1/4) :
    ∃ C > 0, ∀ (σ t : ℝ) (v : ℂ), 1/2+2*η ≤ σ → σ ≤ 5/4 → 3 ≤ |t| → ‖v‖ ≤ η →
      ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖ / ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I+v)‖ ≤
        (2*|t|) ^ (C*‖v‖) := by
  obtain ⟨C,hC,h⟩ := logDeriv_zeta_interior_of_riemannHypothesis hRH hη (by linarith)
  refine ⟨C,hC,?_⟩
  intro σ t v hσ hσ1 ht hv
  let s : ℂ := (σ:ℂ)+(t:ℂ)*I
  let p (x:ℝ) := s+(x:ℂ)*v
  have hstrip (x:ℝ) (hx:x ∈ Icc (0:ℝ) 1) :
      1/2+η ≤ (p x).re ∧ (p x).re ≤ 3/2 ∧ 2 ≤ |(p x).im| ∧ |(p x).im| ≤ 2*|t| := by
    have hxr := (Complex.abs_re_le_norm v).trans hv
    have hxi := (Complex.abs_im_le_norm v).trans hv
    have hrv : |x*v.re| ≤ η := by
      rw [abs_mul,abs_of_nonneg hx.1]
      exact (mul_le_mul_of_nonneg_right hx.2 (abs_nonneg _)).trans (by simpa using hxr)
    have hiv : |x*v.im| ≤ η := by
      rw [abs_mul,abs_of_nonneg hx.1]
      exact (mul_le_mul_of_nonneg_right hx.2 (abs_nonneg _)).trans (by simpa using hxi)
    have he' : (p x).re = σ+x*v.re := by simp [p,s,Complex.mul_re]
    have hi' : (p x).im = t+x*v.im := by simp [p,s,Complex.mul_im]
    rw [he',hi']
    have hlo := abs_sub_abs_le_abs_sub t (t+x*v.im)
    rw [abs_sub_comm t,add_sub_cancel_left] at hlo
    have hu := abs_add_le t (x*v.im)
    exact ⟨by linarith [(abs_le.mp hrv).1],by linarith [(abs_le.mp hrv).2],
      by linarith,by linarith⟩
  have hne (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : riemannZeta (p x) ≠ 0 := by
    have hs := hstrip x hx
    rcases lt_or_ge (p x).re 1 with hl | hr
    · exact RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mp hRH _ (by linarith [hs.1]) hl
    · exact riemannZeta_ne_zero_of_one_le_re hr
  have hvary := log_norm_variation_segment riemannZeta s v (C*Real.log (2*|t|))
    (fun x hx => differentiableAt_riemannZeta (show p x ≠ 1 from fun he => by
      have hm := (hstrip x hx).2.2.1; rw [he,Complex.one_im,abs_zero] at hm; linarith))
    hne (fun x hx => by
      obtain ⟨hl,hr,hlo,hup⟩ := hstrip x hx
      have hh := h (p x).re (p x).im hl hr hlo
      rw [Complex.re_add_im] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hup) hC.le))
  have h0 : 0 < ‖riemannZeta s‖ := by simpa [p] using norm_pos_iff.mpr (hne 0 (by constructor <;> norm_num))
  have h1 : 0 < ‖riemannZeta (s+v)‖ := by simpa [p] using norm_pos_iff.mpr (hne 1 (by constructor <;> norm_num))
  rw [Real.rpow_def_of_pos (show 0 < 2*|t| by linarith)]
  apply (Real.log_le_iff_le_exp (div_pos h0 h1)).mp
  rw [Real.log_div h0.ne' h1.ne']
  exact (le_abs_self _).trans (hvary.trans_eq (by ring))

end RiemannResearch.Analysis.RHInteriorLogDerivative

namespace RiemannResearch.Analysis.RHInteriorLogDerivative

/--
info: 'RiemannResearch.Analysis.RHInteriorLogDerivative.interior_zeta_norm_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms interior_zeta_norm_ratio_le

end RiemannResearch.Analysis.RHInteriorLogDerivative
