import RiemannResearch.Analysis.FiniteTranslationEnergy
import RiemannResearch.RH.WeilConverse
import Mathlib.Tactic.Linarith

/-!
# Pointwise approximate Weil factorizations and an exact obstruction

Source: user-provided `v_prime_side_factorization_A_F_audited.pdf`,
Tracks D3 and E (Conjecture 10.1). The repository's actual smooth Weil
criterion supplies the arithmetic and zero-multiplicity bridge.
Pointwise quadratic-value convergence is sufficient for positivity;
strong-resolvent or Mosco convergence is not required for this implication.
An actual off-line zero obstructs every family of norm-square approximants
on one fixed smooth test, by at least twice the zero's multiplicity.
The existence of a prime-side family satisfying these limits remains open.
-/

noncomputable section
open scoped Topology
open RiemannResearch.Analysis

namespace RiemannResearch.RH.SignedWeilCorrelation
open WeilExplicitFormula

/-- A weaker convergence target than the operator-limit target in the PDF.
Both limits are pointwise on every admissible test. The signed error is kept. -/
theorem riemannHypothesis_of_cutoff_gram_limit
    {H : Type*} [SeminormedAddCommGroup H]
    (A E : ℕ → (ℝ → ℂ) → ℝ) (R : ℕ → (ℝ → ℂ) → H)
    (hdecomp : ∀ n f, SmoothSuperexponentialDecay f →
      A n f = ‖R n f‖ ^ 2 + E n f)
    (hA : ∀ f, SmoothSuperexponentialDecay f →
      Filter.Tendsto (fun n => A n f) Filter.atTop (𝓝 (arithmeticWeilPairing f f).re))
    (hE : ∀ f, SmoothSuperexponentialDecay f →
      Filter.Tendsto (fun n => E n f) Filter.atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_arithmeticWeilPairing_nonneg.mpr
  intro f hf
  apply FiniteTranslationEnergy.nonneg_of_approximate_squares (hA f hf) (hE f hf)
  intro n
  rw [hdecomp n f hf]
  nlinarith [sq_nonneg ‖R n f‖]

/-- Exact quantitative falsification: the same genuine smooth test defeats
every member of the family. No simplicity assumption on the zero is made. -/
theorem off_line_forces_factorization_defect
    {H : Type*} [SeminormedAddCommGroup H]
    (R : ℕ → (ℝ → ℂ) → H)
    (ρ : Zeta23.zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ f : ℝ → ℂ, SmoothSuperexponentialDecay f ∧
      ∀ n,
        (arithmeticWeilPairing f f).re - ‖R n f‖ ^ 2 =
          -2 * (Zeta23.zeroMult ρ : ℝ) - ‖R n f‖ ^ 2 ∧
        2 * (Zeta23.zeroMult ρ : ℝ) ≤
          |(arithmeticWeilPairing f f).re - ‖R n f‖ ^ 2| := by
  obtain ⟨f, hf, hw⟩ := exists_smooth_negative_weil_of_off_line ρ hoff
  have hwR : (arithmeticWeilPairing f f).re =
      -2 * (Zeta23.zeroMult ρ : ℝ) := by
    rw [hw]
    simp
  refine ⟨f, hf, fun n => ?_⟩
  rw [hwR]
  refine ⟨rfl, ?_⟩
  have hm : (0 : ℝ) ≤ (Zeta23.zeroMult ρ : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonpos (by nlinarith [sq_nonneg ‖R n f‖])]
  nlinarith [sq_nonneg ‖R n f‖]

end RiemannResearch.RH.SignedWeilCorrelation
