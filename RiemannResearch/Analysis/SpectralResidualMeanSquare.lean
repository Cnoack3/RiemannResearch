import RiemannResearch.Analysis.MarkedIntegralCauchy
import RiemannResearch.Analysis.DirichletMeanSquare
import Mathlib.Tactic.Positivity

/-!
# Certified finite-spectrum approximation of an integrated discrepancy

Sections 3–5 and recommendation Third of `FRZ_Strengthening_2026-11-10`.
We first retain the exact signed square and the complete finite correlation
defect. The quantitative theorem then combines coefficientwise Fourier errors
with the already proved Montgomery–Vaughan estimate (constant 26).
Thus its right side is the spectral tail, the mean-square error, the weighted
MV separation error, and the weighted Fourier-correlation error.

The actual S₁ mean square and actual Fourier-correlation estimates remain
explicit mathematical hypotheses. This module does not assume the desired
residual estimate and does not assert those zeta-specific inputs.

The orthogonality theorem strengthens the fixed prime-polynomial choice:
any coefficients satisfying the finite normal equations minimize the actual
L² residual, with an exact Pythagorean identity, even for a nonorthogonal basis.

Source for the proposed S₁ subtraction: the cited FRZ note, Lemma 5.
Source for the continuous mean-value input: Montgomery and Vaughan,
"Hilbert's inequality", J. London Math. Soc. (2) 8 (1974), 73–82.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
open RiemannResearch.Analysis.MarkedIntegralCauchy

namespace RiemannResearch.Analysis.SpectralResidualMeanSquare

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Exact signed L² residual identity. -/
theorem integral_residual_sq_eq {f g : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖f x - g x‖ ^ 2 ∂μ) =
      (∫ x, ‖f x‖ ^ 2 ∂μ) + (∫ x, ‖g x‖ ^ 2 ∂μ) -
        2 * (∫ x, f x * star (g x) ∂μ).re := by
  change (∫ x, ‖(f - g) x‖ ^ 2 ∂μ) = _
  rw [integral_norm_sq_eq_toLp_norm_sq (hf.sub hg), hf.toLp_sub hg,
    integral_norm_sq_eq_toLp_norm_sq hf,
    integral_norm_sq_eq_toLp_norm_sq hg, integral_mul_star_eq_inner hf hg]
  have h := norm_sub_sq (𝕜 := ℂ) (hg.toLp g) (hf.toLp f)
  rw [norm_sub_rev] at h
  change ‖hf.toLp f - hg.toLp g‖ ^ 2 =
    ‖hf.toLp f‖ ^ 2 + ‖hg.toLp g‖ ^ 2 -
      2 * (inner ℂ (hg.toLp g) (hf.toLp f)).re
  change ‖hf.toLp f - hg.toLp g‖ ^ 2 =
    ‖hg.toLp g‖ ^ 2 - 2 * (inner ℂ (hg.toLp g) (hf.toLp f)).re +
      ‖hf.toLp f‖ ^ 2 at h
  linarith

variable {ι : Type} [Fintype ι]

/-- A finite spectral approximant, with no independence assumption on the modes. -/
def approximation (c : ι → ℂ) (e : ι → X → ℂ) (x : X) : ℂ :=
  ∑ i, c i * e i x

theorem approximation_memLp (c : ι → ℂ) {e : ι → X → ℂ}
    (he : ∀ i, MemLp (e i) 2 μ) :
    MemLp (approximation c e) 2 μ := by
  exact memLp_finsetSum Finset.univ (fun i _ => (he i).const_mul (c i))

/-- The correlation with a finite polynomial is exactly the weighted sum
of the actual correlations with its modes. -/
theorem integral_mul_star_approximation {f : X → ℂ} (hf : MemLp f 2 μ)
    (c : ι → ℂ) {e : ι → X → ℂ} (he : ∀ i, MemLp (e i) 2 μ) :
    (∫ x, f x * star (approximation c e x) ∂μ) =
      ∑ i, star (c i) * ∫ x, f x * star (e i x) ∂μ := by
  have hpoint (x : X) : f x * star (approximation c e x) =
      ∑ i, star (c i) * (f x * star (e i x)) := by
    simp only [approximation, star_sum, star_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro i hi
    exact (hf.integrable_mul (he i).star).const_mul (star (c i))

private theorem star_mul_self (z : ℂ) :
    star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  simpa only [Complex.star_def, mul_comm] using Complex.mul_conj z

/-- Exact signed Fourier-correlation defect. All modes remain grouped before
taking a norm. -/
theorem integral_correlation_eq {f : X → ℂ} (hf : MemLp f 2 μ)
    (c : ι → ℂ) {e : ι → X → ℂ} (he : ∀ i, MemLp (e i) 2 μ) (T : ℝ) :
    (∫ x, f x * star (approximation c e x) ∂μ) =
      ((T * ∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) +
        ∑ i, star (c i) *
          ((∫ x, f x * star (e i x) ∂μ) - (T : ℂ) * c i) := by
  rw [integral_mul_star_approximation hf c he]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hz := star_mul_self (c i)
  push_cast at hz
  rw [← hz]
  ring

/-- Exact residual square, separated into its spectral tail and its two signed
defects. No cancellation has been discarded. -/
theorem integral_residual_eq_signed_defects {f : X → ℂ} (hf : MemLp f 2 μ)
    (c : ι → ℂ) {e : ι → X → ℂ} (he : ∀ i, MemLp (e i) 2 μ) (T : ℝ) :
    (∫ x, ‖f x - approximation c e x‖ ^ 2 ∂μ) =
      (∫ x, ‖f x‖ ^ 2 ∂μ) - T * ∑ i, ‖c i‖ ^ 2 +
        ((∫ x, ‖approximation c e x‖ ^ 2 ∂μ) - T * ∑ i, ‖c i‖ ^ 2) -
        2 * (∑ i, star (c i) *
          ((∫ x, f x * star (e i x) ∂μ) - (T : ℂ) * c i)).re := by
  rw [integral_residual_sq_eq hf (approximation_memLp c he),
    integral_correlation_eq hf c he T]
  simp only [Complex.add_re, Complex.ofReal_re]
  ring

/-- The one signed defect relevant to approximation. It allows cancellation
between the S₁ energy error, polynomial error, and mixed-correlation error. -/
def signedDefect (f : X → ℂ) (c : ι → ℂ) (e : ι → X → ℂ)
    (T total : ℝ) (μ : Measure X) : ℝ :=
  ((∫ x, ‖f x‖ ^ 2 ∂μ) - T * total) +
    ((∫ x, ‖approximation c e x‖ ^ 2 ∂μ) - T * ∑ i, ‖c i‖ ^ 2) -
    2 * (∑ i, star (c i) *
      ((∫ x, f x * star (e i x) ∂μ) - (T : ℂ) * c i)).re

/-- Exact residual = spectral tail + combined signed defect. -/
theorem integral_residual_eq_tail_add_signedDefect {f : X → ℂ}
    (hf : MemLp f 2 μ) (c : ι → ℂ) {e : ι → X → ℂ}
    (he : ∀ i, MemLp (e i) 2 μ) (T total : ℝ) :
    (∫ x, ‖f x - approximation c e x‖ ^ 2 ∂μ) =
      T * (total - ∑ i, ‖c i‖ ^ 2) + signedDefect f c e T total μ := by
  rw [integral_residual_eq_signed_defects hf c he T]
  unfold signedDefect
  ring

/-- The sharp next analytic provider is necessary and sufficient: only the
combined signed defect must be bounded, rather than its three magnitudes
separately. No estimate for the actual zeta S₁ is asserted here. -/
theorem residual_bound_iff_signedDefect_bound {f : X → ℂ}
    (hf : MemLp f 2 μ) (c : ι → ℂ) {e : ι → X → ℂ}
    (he : ∀ i, MemLp (e i) 2 μ) (T total D : ℝ) :
    (∫ x, ‖f x - approximation c e x‖ ^ 2 ∂μ) ≤
      T * (total - ∑ i, ‖c i‖ ^ 2) + D ↔ signedDefect f c e T total μ ≤ D := by
  rw [integral_residual_eq_tail_add_signedDefect hf c he T total]
  exact add_le_add_iff_left _

/-- General quantitative residual theorem. Correlation errors are weighted
individually; replacing them by a common supremum is optional. -/
theorem integral_residual_sq_le {f : X → ℂ} (hf : MemLp f 2 μ)
    (c : ι → ℂ) {e : ι → X → ℂ} (he : ∀ i, MemLp (e i) 2 μ)
    (T total errS errP : ℝ) (errC : ι → ℝ)
    (hS : (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ T * total + errS)
    (hP : |(∫ x, ‖approximation c e x‖ ^ 2 ∂μ) -
      T * ∑ i, ‖c i‖ ^ 2| ≤ errP)
    (hC : ∀ i, ‖(∫ x, f x * star (e i x) ∂μ) - (T : ℂ) * c i‖ ≤ errC i) :
    (∫ x, ‖f x - approximation c e x‖ ^ 2 ∂μ) ≤
      T * (total - ∑ i, ‖c i‖ ^ 2) + errS + errP +
        2 * ∑ i, ‖c i‖ * errC i := by
  have herr : ‖∑ i, star (c i) *
      ((∫ x, f x * star (e i x) ∂μ) - (T : ℂ) * c i)‖ ≤
      ∑ i, ‖c i‖ * errC i := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i hi
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (hC i) (norm_nonneg _)
  have hre := Complex.re_le_norm
    (-(∑ i, star (c i) * ((∫ x, f x * star (e i x) ∂μ) - (T : ℂ) * c i)))
  simp only [Complex.neg_re, norm_neg] at hre
  have hp := (le_abs_self
    ((∫ x, ‖approximation c e x‖ ^ 2 ∂μ) - T * ∑ i, ‖c i‖ ^ 2)).trans hP
  rw [integral_residual_eq_signed_defects hf c he T]
  linarith

/-- Cauchy for the remaining signed pairing; its test norm can be the
Montgomery–Vaughan bound in terms of J₄. -/
theorem norm_residual_pairing_sq_le {f p g : X → ℂ}
    (hf : MemLp f 2 μ) (hp : MemLp p 2 μ) (hg : MemLp g 2 μ)
    {R K : ℝ}
    (hR : (∫ x, ‖f x - p x‖ ^ 2 ∂μ) ≤ R)
    (hK : (∫ x, ‖g x‖ ^ 2 ∂μ) ≤ K) :
    ‖∫ x, (f x - p x) * g x ∂μ‖ ^ 2 ≤ R * K := by
  have h := integral_mul_star_norm_sq_le (hf.sub hp) hg.star
  simp only [Pi.star_apply, star_star, norm_star, Pi.sub_apply] at h
  have hR0 : 0 ≤ R := (integral_nonneg (fun x => sq_nonneg ‖f x - p x‖)).trans hR
  exact h.trans (mul_le_mul hR hK (integral_nonneg (fun x => sq_nonneg _)) hR0)

/-- Orthogonal residuals yield an exact Pythagorean theorem. -/
theorem orthogonal_residual_pythagoras {f p h : X → ℂ}
    (hf : MemLp f 2 μ) (hp : MemLp p 2 μ) (hh : MemLp h 2 μ)
    (horth : (∫ x, (f x - p x) * star (h x) ∂μ) = 0) :
    (∫ x, ‖f x - (p x + h x)‖ ^ 2 ∂μ) =
      (∫ x, ‖f x - p x‖ ^ 2 ∂μ) + ∫ x, ‖h x‖ ^ 2 ∂μ := by
  have hid := integral_residual_sq_eq (hf.sub hp) hh
  simp only [Pi.sub_apply, horth, Complex.zero_re, mul_zero, sub_zero] at hid
  simpa only [sub_add_eq_sub_sub] using hid

/-- The finite normal equations certify the best possible residual in the
entire trial span. The basis need not be orthogonal or linearly independent. -/
theorem normal_equations_pythagoras {f : X → ℂ} (hf : MemLp f 2 μ)
    (a b : ι → ℂ) {e : ι → X → ℂ} (he : ∀ i, MemLp (e i) 2 μ)
    (horth : ∀ i, (∫ x, (f x - approximation a e x) * star (e i x) ∂μ) = 0) :
    (∫ x, ‖f x - approximation b e x‖ ^ 2 ∂μ) =
      (∫ x, ‖f x - approximation a e x‖ ^ 2 ∂μ) +
        ∫ x, ‖approximation (fun i => b i - a i) e x‖ ^ 2 ∂μ := by
  have ha := approximation_memLp a he
  have hh := approximation_memLp (fun i => b i - a i) he
  have hort : (∫ x, (f x - approximation a e x) *
      star (approximation (fun i => b i - a i) e x) ∂μ) = 0 := by
    have ho := integral_mul_star_approximation (hf.sub ha) (fun i => b i - a i) he
    simp only [Pi.sub_apply] at ho
    rw [ho]
    simp only [horth, mul_zero, Finset.sum_const_zero]
  have hid := orthogonal_residual_pythagoras hf ha hh hort
  have hsplit (x : X) : approximation a e x +
      approximation (fun i => b i - a i) e x = approximation b e x := by
    simp only [approximation, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa only [hsplit] using hid

theorem normal_equations_optimal {f : X → ℂ} (hf : MemLp f 2 μ)
    (a b : ι → ℂ) {e : ι → X → ℂ} (he : ∀ i, MemLp (e i) 2 μ)
    (horth : ∀ i, (∫ x, (f x - approximation a e x) * star (e i x) ∂μ) = 0) :
    (∫ x, ‖f x - approximation a e x‖ ^ 2 ∂μ) ≤
      ∫ x, ‖f x - approximation b e x‖ ^ 2 ∂μ := by
  rw [normal_equations_pythagoras hf a b he horth]
  exact le_add_of_nonneg_right (integral_nonneg (fun x => sq_nonneg _))

section SeparatedFrequencies
variable [DecidableEq ι]
open RiemannResearch.Analysis.ZeroOrdinate
open RiemannResearch.Analysis.DirichletMeanSquare

private theorem phase_memLp (ω A B : ℝ) :
    MemLp (phase ω) 2 (volume.restrict (Set.Ioc A B)) := by
  have hc : Continuous (phase ω) := by unfold phase; fun_prop
  exact MemLp.of_bound hc.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun t => (phase_norm ω t).le))

/-- A proved finite-spectrum residual estimate: the polynomial mean-square
input is discharged by Montgomery–Vaughan, with its full weighted constant 26.
Only the mean square and mode correlations of f are still input providers. -/
theorem separated_frequency_residual_sq_le
    {A B : ℝ} (hAB : A ≤ B) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc A B)))
    (c : ι → ℂ) (ω δ : ι → ℝ)
    (hω : Function.Injective ω) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|)
    (total errS : ℝ) (errC : ι → ℝ)
    (hS : (∫ t in A..B, ‖f t‖ ^ 2) ≤ (B - A) * total + errS)
    (hC : ∀ i, ‖(∫ t in A..B, f t * star (phase (ω i) t)) -
      ((B - A : ℝ) : ℂ) * c i‖ ≤ errC i) :
    (∫ t in A..B, ‖f t - polynomial c ω t‖ ^ 2) ≤
      (B - A) * (total - ∑ i, ‖c i‖ ^ 2) + errS +
        26 * ∑ i, ‖c i‖ ^ 2 / δ i + 2 * ∑ i, ‖c i‖ * errC i := by
  have hmv := abs_integral_norm_sq_sub_le c ω δ hω hδ hsep A B
  simp only [intervalIntegral.integral_of_le hAB] at hS hC hmv ⊢
  exact integral_residual_sq_le hf c (fun i => phase_memLp (ω i) A B)
    (B - A) total errS (26 * ∑ i, ‖c i‖ ^ 2 / δ i) errC hS hmv hC

end SeparatedFrequencies
end RiemannResearch.Analysis.SpectralResidualMeanSquare
