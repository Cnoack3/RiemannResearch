import RiemannResearch.RH.ThresholdHilbertLegal
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ParetoCompressedMellinCosine
import RiemannResearch.LinearAlgebra.PairedAnnihilatorObstruction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Actual arithmetic providers for the compressed-Mellin obstruction

Source: `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`, Section 3,
and `dual-audit-phase-centering.md` (8 September 2026).

The proposition definitions record analytic obligations, not axioms.
`fullCosineIdentity` in `ParetoCompressedMellinNorm` supplies `FullCosineIdentity`;
the remaining analytic providers are OPEN. The closing theorems are CONDITIONAL research reductions on
the actual existing weighted Hilbert carrier and separately closed seed modules.
The complete compressed cell and phase are stated explicitly so that abstract
witness hypotheses cannot be mistaken for their arithmetic construction.
-/

namespace RiemannResearch.RH.Pareto.CompressedMellin
noncomputable section
open scoped BigOperators
open RiemannResearch.LinearAlgebra.PairedAnnihilatorObstruction

/-- Physical cell of the Riesz vector, indexed by the positive integer `n+1`.
This is the closed-form interval integral from the report. -/
def compressedMellinCell (t : ℝ) (n : ℕ) : ℂ :=
  ((((n : ℝ) + 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t * Real.log ((n : ℝ) + 1) : ℝ)) -
    (((n : ℝ) + 1 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (t * Real.log ((n : ℝ) + 2) : ℝ))) /
    (1 - Complex.I * (t : ℂ))

def phaseCenteredMellinCell (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-Complex.I * (t * Real.log t - t : ℝ)) * compressedMellinCell t n

/-- The full, untruncated weighted cell energy. -/
def compressedMellinEnergy (t : ℝ) : ℝ :=
  ∑' n, paretoWeight n * ‖compressedMellinCell t n‖ ^ 2

/-- Inner product linear in the physical function, as in the report. -/
def phaseCenteredPairing (t : ℝ) (f : ThresholdHilbert) : ℂ :=
  ∑' n, ((paretoWeight n * hilbertSequence f (n + 1) : ℝ) : ℂ) *
    star (phaseCenteredMellinCell t n)

/-- The exact full cosine identity, supplied by `fullCosineIdentity` in
`ParetoCompressedMellinNorm`. -/
def FullCosineIdentity : Prop :=
  ∀ t : ℝ, Summable (cosineDeficit t) ∧
    Summable (fun n => paretoWeight n * ‖compressedMellinCell t n‖ ^ 2) ∧
    compressedMellinEnergy t = cosineMass t / (1 + t ^ 2)

/-- OPEN: sharp asymptotic of the actual positive cosine series. -/
def CosineMassAsymptotic : Prop :=
  Filter.Tendsto (fun t : ℝ => cosineMass t / t) Filter.atTop (nhds Real.pi)

/-- OPEN: bounded operator representation, complete-tail norm bound and the
phase-centered derivative estimate.  The operator acts on real physical vectors,
so its norm is bounded by the complexified Riesz energy rather than identified
with that energy by an unjustified real/complex conversion. -/
def PhaseCenteredAnalyticProvider : Prop :=
  ∃ q : ℝ → ThresholdHilbert →L[ℝ] ℂ,
    (∀ t f, q t f = phaseCenteredPairing t f) ∧
    (∀ t : ℝ, 1 ≤ t → ‖q t‖ ^ 2 ≤ 7 / t) ∧
    (∀ t : ℝ, 1 ≤ t → ‖q t hilbertOne‖ = 1 / Real.sqrt (1 + t ^ 2)) ∧
    (∀ t : ℝ, 1 ≤ t → DifferentiableAt ℝ q t) ∧
    (∀ t : ℝ, 1 ≤ t → ‖deriv q t‖ ^ 2 ≤ 82 / t) ∧
    (∀ b : ℕ, 2 ≤ b → ∀ m : ℕ, 0 < m →
      ∀ f ∈ hilbertLegalClosure ({b} : Set ℕ),
        q (2 * Real.pi * (m : ℝ) / Real.log (b : ℝ)) f = 0)

/-- OPEN: the quantitatively paired annihilator provider for the actual two
separately closed seed spaces.  A proof must combine the preceding analytic
provider with the stated Dirichlet frequency selection; it is not supplied here. -/
def ActualPairedMellinProvider : Prop :=
  ∃ C δ₀ : ℝ,
    PairedAnnihilatorEstimates
      (hilbertLegalClosure ({2} : Set ℕ))
      (hilbertLegalClosure ({3} : Set ℕ)) hilbertOne C δ₀

/-- CONDITIONAL: no exact sum of vectors from the two separately closed spaces.
This says nothing against membership in the closure of their joint sum. -/
theorem actual_no_exact_decomposition (h : ActualPairedMellinProvider) :
    ¬ ∃ f ∈ hilbertLegalClosure ({2} : Set ℕ),
      ∃ g ∈ hilbertLegalClosure ({3} : Set ℕ), hilbertOne = f + g := by
  obtain ⟨C, δ₀, h⟩ := h
  exact no_exact_decomposition h

/-- CONDITIONAL: the report's reciprocal-error channel norm obstruction, with
explicit constants and the actual complete weighted Hilbert norm. -/
theorem actual_reciprocal_error_obstruction (h : ActualPairedMellinProvider) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
      ∀ f ∈ hilbertLegalClosure ({2} : Set ℕ),
      ∀ g ∈ hilbertLegalClosure ({3} : Set ℕ),
      ∀ ε : ℝ, 0 < ε → 2 * C * ε ≤ δ₀ →
      ‖hilbertOne - (f + g)‖ ≤ ε →
      1 / (4 * C * ε) ≤ ‖f‖ ∧ 1 / (4 * C * ε) ≤ ‖g‖ := by
  obtain ⟨C, δ₀, h⟩ := h
  exact ⟨C, δ₀, h.cost_pos, h.radius_pos,
    fun f hf g hg ε hε hsmall herr =>
      reciprocal_error_lower_bound h f g hf hg ε hε hsmall herr⟩

end
end RiemannResearch.RH.Pareto.CompressedMellin
