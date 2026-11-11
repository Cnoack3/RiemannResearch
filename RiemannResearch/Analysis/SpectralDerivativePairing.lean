import RiemannResearch.Analysis.SpectralResidualMeanSquare
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fourth-frequency energy and residual pairing

This formalizes the differentiated-polynomial step behind Sections 2–5 of
`FRZ_Strengthening_2026-11-10`: the second derivative is an actual derivative,
its coefficient energy is exactly J₄, and the residual pairing is controlled by
the proved weighted Montgomery–Vaughan estimate. Local frequency gaps are
retained; a uniform minimum gap is only a corollary.

This is an analytic finite-polynomial statement and asserts no unproved
mean-square property of the actual zeta counting discrepancy.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
open RiemannResearch.Analysis.ZeroOrdinate
open RiemannResearch.Analysis.DirichletMeanSquare
open RiemannResearch.Analysis.SpectralResidualMeanSquare

namespace RiemannResearch.Analysis.SpectralDerivativePairing

variable {ι : Type} [Fintype ι]

def derivativeCoeff (c : ι → ℂ) (ω : ι → ℝ) (i : ι) : ℂ :=
  ((ω i : ℂ) * Complex.I) * c i

def secondCoeff (c : ι → ℂ) (ω : ι → ℝ) (i : ι) : ℂ :=
  -((ω i : ℂ) ^ 2) * c i

/-- The actual grouped fourth-frequency energy J₄. -/
def fourthEnergy (c : ι → ℂ) (ω : ι → ℝ) : ℝ :=
  ∑ i, ‖c i‖ ^ 2 * (ω i) ^ 4

theorem hasDerivAt_phase (ω t : ℝ) :
    HasDerivAt (phase ω) (((ω : ℂ) * Complex.I) * phase ω t) t := by
  have heq : phase ω = fun x : ℝ =>
      Complex.exp (((ω : ℂ) * Complex.I) * (x : ℂ)) := by
    funext x
    unfold phase
    congr 1
    push_cast
    ring
  rw [heq]
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul ((ω : ℂ) * Complex.I)).cexp
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, mul_comm] using h

theorem hasDerivAt_polynomial (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) :
    HasDerivAt (polynomial c ω) (polynomial (derivativeCoeff c ω) ω t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i hi => (hasDerivAt_phase (ω i) t).const_mul (c i))
  have hs : polynomial (derivativeCoeff c ω) ω t =
      ∑ i, c i * (((ω i : ℂ) * Complex.I) * phase (ω i) t) := by
    unfold polynomial derivativeCoeff
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs]
  exact h

omit [Fintype ι] in
theorem derivativeCoeff_twice (c : ι → ℂ) (ω : ι → ℝ) :
    derivativeCoeff (derivativeCoeff c ω) ω = secondCoeff c ω := by
  funext i
  unfold derivativeCoeff secondCoeff
  calc
    _ = (ω i : ℂ) ^ 2 * Complex.I ^ 2 * c i := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem second_derivative_polynomial (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) :
    deriv (deriv (polynomial c ω)) t = polynomial (secondCoeff c ω) ω t := by
  have hd : deriv (polynomial c ω) = polynomial (derivativeCoeff c ω) ω :=
    funext (fun x => (hasDerivAt_polynomial c ω x).deriv)
  rw [hd]
  have h := (hasDerivAt_polynomial (derivativeCoeff c ω) ω t).deriv
  simpa only [derivativeCoeff_twice] using h

omit [Fintype ι] in
theorem norm_secondCoeff_sq (c : ι → ℂ) (ω : ι → ℝ) (i : ι) :
    ‖secondCoeff c ω i‖ ^ 2 = ‖c i‖ ^ 2 * (ω i) ^ 4 := by
  have hω : ‖(ω i : ℂ)‖ ^ 2 = (ω i) ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [secondCoeff, norm_mul, norm_neg, norm_pow, hω]
  ring

theorem polynomial_memLp (c : ι → ℂ) (ω : ι → ℝ) (A B : ℝ) :
    MemLp (polynomial c ω) 2 (volume.restrict (Set.Ioc A B)) := by
  classical
  refine MemLp.of_bound (polynomial_continuous c ω).aestronglyMeasurable
    (∑ i, ‖c i‖) (Filter.Eventually.of_forall ?_)
  intro t
  calc
    ‖polynomial c ω t‖ ≤ ∑ i, ‖c i * phase (ω i) t‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, phase_norm, mul_one]

/-- Exact J₄ mean square with the full local-gap error. -/
theorem abs_second_derivative_mean_square_sub_le
    (c : ι → ℂ) (ω δ : ι → ℝ) (hω : Function.Injective ω)
    (hδ : ∀ i, 0 < δ i) (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|)
    (A B : ℝ) :
    |(∫ t in A..B, ‖deriv (deriv (polynomial c ω)) t‖ ^ 2) -
      (B - A) * fourthEnergy c ω| ≤
      26 * ∑ i, (‖c i‖ ^ 2 * (ω i) ^ 4) / δ i := by
  classical
  simp only [second_derivative_polynomial]
  simpa only [norm_secondCoeff_sq, fourthEnergy] using
    abs_integral_norm_sq_sub_le (secondCoeff c ω) ω δ hω hδ hsep A B

/-- Direct residual pairing with the actual second derivative.
This gives the J₄ Cauchy step, with all local gaps still visible. -/
theorem residual_second_derivative_pairing_sq_le
    {A B : ℝ} (hAB : A ≤ B) {f p : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc A B)))
    (hp : MemLp p 2 (volume.restrict (Set.Ioc A B)))
    {R : ℝ} (hR : (∫ t in A..B, ‖f t - p t‖ ^ 2) ≤ R)
    (c : ι → ℂ) (ω δ : ι → ℝ) (hω : Function.Injective ω)
    (hδ : ∀ i, 0 < δ i) (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|) :
    ‖∫ t in A..B, (f t - p t) * deriv (deriv (polynomial c ω)) t‖ ^ 2 ≤
      R * ((B - A) * fourthEnergy c ω +
        26 * ∑ i, (‖c i‖ ^ 2 * (ω i) ^ 4) / δ i) := by
  have hmv := abs_second_derivative_mean_square_sub_le c ω δ hω hδ hsep A B
  have hupper := (abs_le.mp hmv).2
  have hK : (∫ t in A..B, ‖deriv (deriv (polynomial c ω)) t‖ ^ 2) ≤
      (B - A) * fourthEnergy c ω +
        26 * ∑ i, (‖c i‖ ^ 2 * (ω i) ^ 4) / δ i := by linarith
  simp only [second_derivative_polynomial, intervalIntegral.integral_of_le hAB]
    at hR hK ⊢
  exact norm_residual_pairing_sq_le hf hp (polynomial_memLp (secondCoeff c ω) ω A B) hR hK

/-- The usual uniform-gap J₄ estimate, as a specialization of the stronger
weighted estimate. -/
theorem residual_second_derivative_pairing_sq_le_uniform
    {A B : ℝ} (hAB : A ≤ B) {f p : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc A B)))
    (hp : MemLp p 2 (volume.restrict (Set.Ioc A B)))
    {R : ℝ} (hR : (∫ t in A..B, ‖f t - p t‖ ^ 2) ≤ R)
    (c : ι → ℂ) (ω : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ |ω i - ω j|) :
    ‖∫ t in A..B, (f t - p t) * deriv (deriv (polynomial c ω)) t‖ ^ 2 ≤
      R * ((B - A + 26 / δ) * fourthEnergy c ω) := by
  have hω : Function.Injective ω := by
    intro i j hij
    by_contra hne
    have hs := hsep i j hne
    rw [hij, sub_self, abs_zero] at hs
    exact (not_le_of_gt hδ) hs
  have h := residual_second_derivative_pairing_sq_le hAB hf hp hR c ω
    (fun _ => δ) hω (fun _ => hδ) hsep
  have heq : (B - A) * fourthEnergy c ω +
      26 * ∑ i, (‖c i‖ ^ 2 * (ω i) ^ 4) / δ =
      (B - A + 26 / δ) * fourthEnergy c ω := by
    rw [← Finset.sum_div]
    unfold fourthEnergy
    ring
  rwa [heq] at h

end RiemannResearch.Analysis.SpectralDerivativePairing
