import RiemannResearch.RH.MellinWindowCount
import RiemannResearch.Analysis.ComplexKernelPairCorrelation
import Mathlib.Tactic.Linarith

/-!
# Zeta-envelope effects on the Mellin projection DPP

The intensity and window probabilities refer to the finite-rank sampling law
on real frequencies. The spectral count interpretation is Theorem 7 in
Hough, Krishnapur, Peres and Virág, *Determinantal Processes and Independence*,
https://arxiv.org/abs/math/0503110.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.MellinFrequency

open RiemannResearch.Analysis.ComplexKernel (envelopeKernel)

theorem kernel_diagonal_re_eq_envelope (n : ℕ) (t : ℝ) :
    (kernel n t t).re = ‖zetaEnvelope t‖ ^ 2 * (core n t t).re := by
  rw [kernel_factorization, envelopeKernel]
  rw [show zetaEnvelope t * star (zetaEnvelope t) =
      ((‖zetaEnvelope t‖ ^ 2 : ℝ) : ℂ) by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
      Complex.mul_conj (zetaEnvelope t)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem mellinWindowCount_expectation_envelope (n : ℕ) {I : Set ℝ}
    (hI : MeasurableSet I) :
    (∫ x, (mellinWindowCount n I x : ℝ) ∂mellinLaw n) =
      ∫ t in I, ‖zetaEnvelope t‖ ^ 2 * (core n t t).re ∂frequencyMeasure := by
  rw [mellinWindowCount_expectation_kernel n hI]
  simp_rw [kernel_diagonal_re_eq_envelope]

private theorem one_sub_sum_le_prod_compl {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    1 - (∑ i ∈ s, p i) ≤ ∏ i ∈ s, (1 - p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hsum : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg (fun i _ => (hp i).1)
    have hmul := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hp a).2)
    nlinarith only [hmul, mul_nonneg (hp a).1 hsum]

/-- Upper and lower hole bounds use the same envelope-weighted intensity integral. -/
theorem mellinWindowCount_hole_bounds_envelope (n : ℕ) {I : Set ℝ} (hI : MeasurableSet I) :
    let a := ∫ t in I, ‖zetaEnvelope t‖ ^ 2 * (core n t t).re ∂frequencyMeasure
    1 - a ≤ (mellinLaw n).real {x | mellinWindowCount n I x = 0} ∧
      (mellinLaw n).real {x | mellinWindowCount n I x = 0} ≤ Real.exp (-a) := by
  have he := (mellinWindowCount_expectation_envelope n hI).symm.trans
    (mellinWindowCount_moments n hI).1
  dsimp only
  constructor
  · rw [he, mellinWindowCount_hole n hI]
    exact one_sub_sum_le_prod_compl Finset.univ _ (mellinWindowEigenvalues_mem_Icc n hI)
  · simpa only [kernel_diagonal_re_eq_envelope] using mellinWindowCount_hole_le_exp n hI

end RiemannResearch.RH.Pareto.MellinFrequency
