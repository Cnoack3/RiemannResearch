import RiemannResearch.Analysis.SpectralDerivativePairing
import RiemannResearch.Analysis.SpectralResidualMeanSquare
import RiemannResearch.Analysis.MarkedIntegralCauchy
import RiemannResearch.Analysis.DirichletMeanSquare
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed spectral defects controlled by the unretained coefficients

The exact comparison isolates the reference tail before Cauchy--Schwarz.
For a literal coefficient truncation of a finite exponential polynomial,
the combined signed defect is exactly the tail's off-diagonal mean square.
The weighted Montgomery--Vaughan bound therefore involves only tail
coefficients, not the energy of the retained head.

These are unconditional finite and Hilbert-space identities. Instantiating
the comparison with the actual S₁ still requires an actual approximation
bound; no classical zeta estimate or density theorem is assumed here.

Source: algebraic development from SpectralResidualMeanSquare, requested
in the November 11 FRZ investigation. The inherited mean-value ingredient
is Montgomery and Vaughan, "Hilbert's inequality", JLMS (2) 8 (1974), 73–82.
No mathematical novelty claim is intended.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
open RiemannResearch.Analysis.SpectralResidualMeanSquare
open RiemannResearch.Analysis.MarkedIntegralCauchy
open RiemannResearch.Analysis.DirichletMeanSquare
open RiemannResearch.Analysis.SpectralDerivativePairing
open RiemannResearch.Analysis.ZeroOrdinate

namespace RiemannResearch.Analysis.SpectralSignedTail
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Exact comparison retains only the reference tail in the mixed term. -/
theorem residual_comparison_eq {f g p : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hp : MemLp p 2 μ) :
    (∫ x, ‖f x - p x‖ ^ 2 ∂μ) =
      (∫ x, ‖f x - g x‖ ^ 2 ∂μ) +
      (∫ x, ‖g x - p x‖ ^ 2 ∂μ) +
      2 * (∫ x, (f x - g x) * star (g x - p x) ∂μ).re := by
  have h := integral_residual_sq_eq (hf.sub hg) (hg.sub hp).neg
  simp only [Pi.sub_apply, Pi.neg_apply, star_neg, mul_neg,
    integral_neg, Complex.neg_re, sub_neg_eq_add] at h
  have heq (x : X) : f x - g x + (g x - p x) = f x - p x := by ring
  simpa only [heq, norm_neg] using h

variable {ι : Type} [Fintype ι]

theorem signedDefect_comparison_eq {f g : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (c : ι → ℂ) {e : ι → X → ℂ} (he : ∀ i, MemLp (e i) 2 μ)
    (T total : ℝ) :
    signedDefect f c e T total μ = signedDefect g c e T total μ +
      (∫ x, ‖f x - g x‖ ^ 2 ∂μ) +
      2 * (∫ x, (f x - g x) * star (g x - approximation c e x) ∂μ).re := by
  have h := residual_comparison_eq hf hg (approximation_memLp c he)
  rw [integral_residual_eq_tail_add_signedDefect hf c he T total,
      integral_residual_eq_tail_add_signedDefect hg c he T total] at h
  linarith

theorem signedDefect_comparison_le {f g : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (c : ι → ℂ) {e : ι → X → ℂ} (he : ∀ i, MemLp (e i) 2 μ)
    (T total B K : ℝ)
    (hB : (∫ x, ‖f x - g x‖ ^ 2 ∂μ) ≤ B)
    (hK : (∫ x, ‖g x - approximation c e x‖ ^ 2 ∂μ) ≤ K) :
    signedDefect f c e T total μ ≤ signedDefect g c e T total μ +
      B + 2 * Real.sqrt (B * K) := by
  have hp := approximation_memLp c he
  have hB0 : 0 ≤ B := (integral_nonneg (fun x => sq_nonneg _)).trans hB
  have hsq := integral_mul_star_norm_sq_le (hf.sub hg) (hg.sub hp)
  simp only [Pi.sub_apply] at hsq
  have hprod : (∫ x, ‖f x - g x‖ ^ 2 ∂μ) *
      (∫ x, ‖g x - approximation c e x‖ ^ 2 ∂μ) ≤ B * K :=
    mul_le_mul hB hK (integral_nonneg (fun x => sq_nonneg _)) hB0
  have hn : ‖∫ x, (f x - g x) * star (g x - approximation c e x) ∂μ‖ ≤
      Real.sqrt (B * K) := by
    exact (Real.le_sqrt (norm_nonneg _) (le_trans
      (sq_nonneg _) (hsq.trans hprod))).mpr (hsq.trans hprod)
  have hre := (Complex.re_le_norm
    (∫ x, (f x - g x) * star (g x - approximation c e x) ∂μ)).trans hn
  rw [signedDefect_comparison_eq hf hg c he T total]
  linarith

theorem polynomial_sub (a c : ι → ℂ) (ω : ι → ℝ) :
    (fun t => polynomial a ω t - polynomial c ω t) =
      polynomial (fun i => a i - c i) ω := by
  funext t
  simp only [polynomial, sub_mul, Finset.sum_sub_distrib]

variable [DecidableEq ι]

theorem finite_signedDefect_eq {A B : ℝ} (hAB : A ≤ B)
    (a c : ι → ℂ) (ω : ι → ℝ) (total : ℝ) :
    signedDefect (polynomial a ω) c (fun i => phase (ω i)) (B - A) total
      (volume.restrict (Set.Ioc A B)) =
      (B - A) * ((∑ i, ‖a i - c i‖ ^ 2) - total + ∑ i, ‖c i‖ ^ 2) +
      (offDiagonal (fun i => a i - c i) ω A B).re := by
  classical
  have hf := polynomial_memLp a ω A B
  have he (i : ι) : MemLp (phase (ω i)) 2 (volume.restrict (Set.Ioc A B)) := by
    have hc : Continuous (phase (ω i)) := by unfold phase; fun_prop
    exact MemLp.of_bound hc.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun t => (phase_norm (ω i) t).le))
  have hid := integral_residual_eq_tail_add_signedDefect hf c he (B - A) total
  have hgram := congrArg Complex.re
    (integral_norm_sq_eq_diagonal_add (fun i => a i - c i) ω A B)
  simp only [Complex.add_re, Complex.ofReal_re] at hgram
  rw [intervalIntegral.integral_of_le hAB] at hgram
  have hp : approximation c (fun i => phase (ω i)) = polynomial c ω := rfl
  rw [hp] at hid
  have heq (t : ℝ) : polynomial a ω t - polynomial c ω t =
      polynomial (fun i => a i - c i) ω t := congrFun (polynomial_sub a c ω) t
  simp_rw [heq] at hid
  nlinarith

omit [DecidableEq ι] in
theorem finite_signedDefect_le {A B : ℝ} (hAB : A ≤ B)
    (a c : ι → ℂ) (ω δ : ι → ℝ) (total : ℝ)
    (hω : Function.Injective ω) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|) :
    signedDefect (polynomial a ω) c (fun i => phase (ω i)) (B - A) total
      (volume.restrict (Set.Ioc A B)) ≤
      (B - A) * ((∑ i, ‖a i - c i‖ ^ 2) - total + ∑ i, ‖c i‖ ^ 2) +
      26 * ∑ i, ‖a i - c i‖ ^ 2 / δ i := by
  classical
  rw [finite_signedDefect_eq hAB]
  exact add_le_add le_rfl ((Complex.re_le_norm _).trans
    (norm_offDiagonal_le_weighted (fun i => a i - c i) ω δ hω hδ hsep A B))


/-- On disjoint coefficient blocks, all head and head-tail terms cancel. -/
theorem finite_signedDefect_eq_tail {A B : ℝ} (hAB : A ≤ B)
    (a c : ι → ℂ) (ω : ι → ℝ) (total : ℝ)
    (henergy : (∑ i, ‖a i - c i‖ ^ 2) + (∑ i, ‖c i‖ ^ 2) = total) :
    signedDefect (polynomial a ω) c (fun i => phase (ω i)) (B - A) total
      (volume.restrict (Set.Ioc A B)) =
      (offDiagonal (fun i => a i - c i) ω A B).re := by
  rw [finite_signedDefect_eq hAB]
  have hz : (∑ i, ‖a i - c i‖ ^ 2) - total + ∑ i, ‖c i‖ ^ 2 = 0 := by linarith
  rw [hz, mul_zero, zero_add]

omit [DecidableEq ι] in
theorem finite_signedDefect_abs_le_tail {A B : ℝ} (hAB : A ≤ B)
    (a c : ι → ℂ) (ω δ : ι → ℝ) (total : ℝ)
    (henergy : (∑ i, ‖a i - c i‖ ^ 2) + (∑ i, ‖c i‖ ^ 2) = total)
    (hω : Function.Injective ω) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|) :
    |signedDefect (polynomial a ω) c (fun i => phase (ω i)) (B - A) total
      (volume.restrict (Set.Ioc A B))| ≤
      26 * ∑ i, ‖a i - c i‖ ^ 2 / δ i := by
  classical
  rw [finite_signedDefect_eq_tail hAB a c ω total henergy]
  exact (Complex.abs_re_le_norm _).trans
    (norm_offDiagonal_le_weighted (fun i => a i - c i) ω δ hω hδ hsep A B)

/-- Literal restriction of a coefficient vector. -/
def truncate (s : Finset ι) (a : ι → ℂ) (i : ι) : ℂ :=
  if i ∈ s then a i else 0

theorem truncation_energy (s : Finset ι) (a : ι → ℂ) :
    (∑ i, ‖a i - truncate s a i‖ ^ 2) + (∑ i, ‖truncate s a i‖ ^ 2) =
      ∑ i, ‖a i‖ ^ 2 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : i ∈ s <;> simp [truncate, hs]

theorem truncation_signedDefect_eq_tail {A B : ℝ} (hAB : A ≤ B)
    (s : Finset ι) (a : ι → ℂ) (ω : ι → ℝ) :
    signedDefect (polynomial a ω) (truncate s a) (fun i => phase (ω i))
      (B - A) (∑ i, ‖a i‖ ^ 2) (volume.restrict (Set.Ioc A B)) =
      (offDiagonal (fun i => a i - truncate s a i) ω A B).re :=
  finite_signedDefect_eq_tail hAB a (truncate s a) ω _ (truncation_energy s a)


end RiemannResearch.Analysis.SpectralSignedTail
