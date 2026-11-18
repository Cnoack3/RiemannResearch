import RiemannResearch.Analysis.GabrielStripInterpolation
import Mathlib.Tactic

/-!
# Gabriel interpolation on a physical vertical strip

The vertical-coordinate Jacobian cancels exactly against the mixed-norm
exponents. The endpoint bounds and observation lengths are stated at the
original heights in Chourasiya--Simonič, https://arxiv.org/html/2507.15184v2.
-/
noncomputable section
open Set Complex Complex.HadamardThreeLines MeasureTheory
namespace RiemannResearch.Analysis.InghamInterpolation

/-- The variable-exponent analytic interpolation inequality on any strip of
positive width, with the actual observation heights and exact constant one. -/
theorem gabriel_affine_window {F : ℂ → ℂ} {a d : ℝ} (hd : 0 < d)
    (hhol : DiffContOnCl ℂ F (verticalStrip a (a+d)))
    (hbd : ∃ C : ℝ, ∀ z ∈ verticalClosedStrip a (a+d), ‖F z‖ ≤ C)
    {θ L ML MR : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) (hL : 0 < L)
    (hML : 0 ≤ ML) (hMR : 0 ≤ MR)
    (hu0 : UniformContinuous (stripMomentDensity F a (4/3)))
    (hu1 : UniformContinuous (stripMomentDensity F (a+d) 2))
    (hut : UniformContinuous (stripMomentDensity F (a+d*θ) (4/(3-θ))))
    (hleft : ∀ y : ℝ, ∫ t in y..y+L, stripMomentDensity F a (4/3) t ≤ ML)
    (hright : ∀ y : ℝ, ∫ t in y..y+L, stripMomentDensity F (a+d) 2 t ≤ MR) (x : ℝ) :
    (∫ t in x..x+L, stripMomentDensity F (a+d*θ) (4/(3-θ)) t)^((3-θ)/4) ≤
      (ML^(3/4:ℝ))^(1-θ)*(MR^(1/2:ℝ))^θ := by
  let G (z : ℂ) := F ((a:ℂ)+(d:ℂ)*z)
  have hG : DiffContOnCl ℂ G (verticalStrip 0 1) := by
    apply hhol.comp (g := fun z : ℂ => (a:ℂ)+(d:ℂ)*z)
      ((differentiable_const _).add (differentiable_const _ |>.mul differentiable_id)).diffContOnCl
    intro z hz
    change 0 < z.re ∧ z.re < 1 at hz
    change a < _ ∧ _ < a+d
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    constructor <;> nlinarith [mul_pos hd hz.1, mul_pos hd (sub_pos.mpr hz.2)]
  obtain ⟨C,hC⟩ := hbd
  have hGB : ∃ M : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ‖G z‖ ≤ M := by
    refine ⟨C,fun z hz => hC _ ?_⟩
    change 0 ≤ z.re ∧ z.re ≤ 1 at hz
    change a ≤ _ ∧ _ ≤ a+d
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    constructor <;> nlinarith [mul_nonneg hd.le hz.1, mul_nonneg hd.le (sub_nonneg.mpr hz.2)]
  have dens (k p t : ℝ) :
      stripMomentDensity G k p t = stripMomentDensity F (a+d*k) p (d*t) := by
    unfold stripMomentDensity G
    congr 2
    push_cast
    ring
  have hucomp (k p : ℝ) (h : UniformContinuous (stripMomentDensity F (a+d*k) p)) :
      UniformContinuous (stripMomentDensity G k p) := by
    rw [show stripMomentDensity G k p = fun t => stripMomentDensity F (a+d*k) p (d*t)
      from funext (dens k p)]
    exact h.comp (uniformContinuous_const_smul (X := ℝ) d)
  have window (k p y : ℝ) :
      (∫ t in y..y+L/d, stripMomentDensity G k p t) =
        d⁻¹*(∫ t in d*y..d*y+L, stripMomentDensity F (a+d*k) p t) := by
    simp_rw [dens]
    rw [intervalIntegral.integral_comp_mul_left _ hd.ne', smul_eq_mul]
    have he : d*(y+L/d)=d*y+L := by field_simp
    rw [he]
  have eL (y : ℝ) : (∫ t in y..y+L/d, stripMomentDensity G 0 (4/3) t) ≤ d⁻¹ * ML := by
    rw [window]; simpa using mul_le_mul_of_nonneg_left (hleft (d*y)) (inv_nonneg.mpr hd.le)
  have eR (y : ℝ) : (∫ t in y..y+L/d, stripMomentDensity G 1 2 t) ≤ d⁻¹ * MR := by
    rw [window]; simpa using mul_le_mul_of_nonneg_left (hright (d*y)) (inv_nonneg.mpr hd.le)
  let Q := ∫ t in x..x+L, stripMomentDensity F (a+d*θ) (4/(3-θ)) t
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg (by linarith) (fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _)
  have h := gabriel_vertical_window hG hGB hθ (div_pos hL hd)
    (mul_nonneg (inv_nonneg.mpr hd.le) hML) (mul_nonneg (inv_nonneg.mpr hd.le) hMR)
    (hucomp 0 (4/3) (by simpa using hu0)) (hucomp 1 2 (by simpa using hu1))
    (hucomp θ _ hut) eL eR (x/d)
  rw [window, show d*(x/d)=x by field_simp] at h
  change (d⁻¹*Q)^((3-θ)/4) ≤ _ at h
  have hi := inv_pos.mpr hd
  have hm (v : ℝ) (hv : 0 ≤ v) (p q : ℝ) :
      ((d⁻¹*v)^p)^q = (d⁻¹)^(p*q)*(v^p)^q := by
    rw [Real.mul_rpow hi.le hv, Real.mul_rpow (Real.rpow_nonneg hi.le _) (Real.rpow_nonneg hv _),
      ← Real.rpow_mul hi.le]
  rw [Real.mul_rpow hi.le hQ,hm ML hML,hm MR hMR] at h
  have prod : (d⁻¹)^((3/4:ℝ)*(1-θ)) * (ML^(3/4:ℝ))^(1-θ) *
      ((d⁻¹)^((1/2:ℝ)*θ)*(MR^(1/2:ℝ))^θ) =
      (d⁻¹)^((3-θ)/4)*((ML^(3/4:ℝ))^(1-θ)*(MR^(1/2:ℝ))^θ) := by
    rw [show (3-θ)/4=(3/4:ℝ)*(1-θ)+(1/2:ℝ)*θ by ring,Real.rpow_add hi]
    ring
  rw [prod] at h
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hi _)).mp h

end RiemannResearch.Analysis.InghamInterpolation
