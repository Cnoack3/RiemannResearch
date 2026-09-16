import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.NormNum

/-!
# The continued zeta expression is not a global Hilbert Gram kernel

Source: V_Zeta_Vector_Spaces_Research_2026-09-16.md, Section 5.
The report's positive kernel on Re(s)>1/2 is not constructed here.
This module proves an unconditional obstruction to extending the unchanged
expression to a domain containing zero, using Mathlib's exact zeta(0)=-1/2.
No Riemann-hypothesis premise or analytic provider is used.
-/

namespace RiemannResearch.RH.ZetaKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A Hilbert Gram kernel must have a nonnegative real diagonal. -/
private theorem gram_diagonal_re_nonneg {α : Type*} (Φ : α → E) (x : α) :
    0 ≤ (inner ℂ (Φ x) (Φ x)).re := by
  change 0 ≤ RCLike.re (inner ℂ (Φ x) (Φ x))
  rw [← norm_sq_eq_re_inner]
  exact sq_nonneg _

/-- The unchanged zeta kernel cannot be realized on any domain containing 0. -/
theorem no_zeta_gram_on_domain_containing_zero (D : Set ℂ) (hD : 0 ∈ D) :
    ¬ ∃ Φ : ℂ → E, ∀ s ∈ D, ∀ w ∈ D,
      inner ℂ (Φ s) (Φ w) = riemannZeta (s + star w) := by
  rintro ⟨Φ, hΦ⟩
  have hp := gram_diagonal_re_nonneg Φ 0
  have hz := hΦ 0 hD 0 hD
  rw [hz] at hp
  norm_num [riemannZeta_zero] at hp

theorem no_global_zeta_gram :
    ¬ ∃ Φ : ℂ → E, ∀ s w,
      inner ℂ (Φ s) (Φ w) = riemannZeta (s + star w) := by
  rintro ⟨Φ, hΦ⟩
  exact no_zeta_gram_on_domain_containing_zero (E := E) Set.univ (Set.mem_univ 0)
    ⟨Φ, fun s _ w _ => hΦ s w⟩

end RiemannResearch.RH.ZetaKernel
