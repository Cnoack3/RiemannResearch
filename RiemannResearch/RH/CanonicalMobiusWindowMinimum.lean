/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusTriangular
import RiemannResearch.RH.CanonicalMobiusCovarianceMinimum

/-!
# Unrestricted finite exact-head minimum from the canonical window

Source: the user's Pareto capacity handoff, Sections 10-11, and the finite
affine exhaustion proved in CanonicalMobiusTriangular. The minimum uses
the complete infinite Pareto tail and covers every finite legal candidate
at the stated conductor budget. The asymptotic capacity estimate is open.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

namespace SignedCovariance
open RiemannResearch.Analysis.FiniteHilbertGram

def canonicalWindowIndex (N M : ℕ) (i : Fin (M - N + 1)) : ℕ := N + i.val

theorem canonicalWindowIndex_ge (N M : ℕ) (i : Fin (M - N + 1)) :
    N ≤ canonicalWindowIndex N M i := by unfold canonicalWindowIndex; omega

theorem canonicalWindowIndex_le (N M : ℕ) (hNM : N ≤ M) (i : Fin (M - N + 1)) :
    canonicalWindowIndex N M i ≤ M := by unfold canonicalWindowIndex; omega

theorem canonicalWindowIndex_pos (N M : ℕ) (hN : 0 < N)
    (i : Fin (M - N + 1)) : 0 < canonicalWindowIndex N M i := by
  exact hN.trans_le (canonicalWindowIndex_ge N M i)

theorem canonicalWindow_combination_mem_finiteSpace (N M : ℕ) (hNM : N ≤ M)
    (c : Fin (M - N + 1) → ℝ) :
    combination (canonicalWindowIndex N M) c ∈ finiteSpace M := by
  unfold combination
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
    (canonicalWindowIndex_le N M hNM i)
    (canonicalMobiusHilbert_mem_finiteSpace (canonicalWindowIndex N M i))

/-- The actual inverse covariance capacity is the minimum full infinite tail
energy over every legal vector at conductor budget M+1 with this exact head. -/
theorem canonicalWindow_tail_isLeast_all_legal
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    IsLeast {E : ℝ | ∃ x : ThresholdHilbert, x ∈ finiteSpace M ∧
      (∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence x j = 1) ∧
      ‖hilbertTailShift x N‖ ^ 2 = E}
      (capacity N (canonicalWindowIndex N M) (canonicalWindowIndex_pos N M hN))⁻¹ := by
  constructor
  · refine ⟨optimizedAverage N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN), ?_, ?_, ?_⟩
    · exact canonicalWindow_combination_mem_finiteSpace N M hNM _
    · exact optimizedAverage_exact N (canonicalWindowIndex N M)
        (canonicalWindowIndex_pos N M hN) (canonicalWindowIndex_ge N M)
    · exact optimizedAverage_tail_energy N (canonicalWindowIndex N M)
        (canonicalWindowIndex_pos N M hN)
  · rintro E ⟨x, hx, hhead, rfl⟩
    obtain ⟨c, hc, hxc⟩ := exists_canonicalMobius_affine_expansion_of_exact_head
      N M hNM x hx hhead
    have hcomb : x = combination (canonicalWindowIndex N M) c := by
      simpa only [combination, canonicalWindowIndex, Fintype.linearCombination_apply] using hxc
    rw [hcomb, combination_tail]
    exact (affineCoefficients_isLeast
      (tailFamily N (canonicalWindowIndex N M))
      (normal N (canonicalWindowIndex N M) (canonicalWindowIndex_pos N M hN))
      (normal_equations N (canonicalWindowIndex N M)
        (canonicalWindowIndex_pos N M hN))).2 ⟨c, hc, rfl⟩

/-- Adding the fixed exact-head energy gives the unrestricted full norm minimum. -/
theorem canonicalWindow_full_isLeast_all_legal
    (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    IsLeast {E : ℝ | ∃ x : ThresholdHilbert, x ∈ finiteSpace M ∧
      (∀ j : ℕ, 0 < j → j ≤ N → hilbertSequence x j = 1) ∧ ‖x‖ ^ 2 = E}
      ((N : ℝ) / ((N : ℝ) + 1) +
        (capacity N (canonicalWindowIndex N M) (canonicalWindowIndex_pos N M hN))⁻¹) := by
  constructor
  · refine ⟨optimizedAverage N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN), ?_, ?_, ?_⟩
    · exact canonicalWindow_combination_mem_finiteSpace N M hNM _
    · exact optimizedAverage_exact N (canonicalWindowIndex N M)
        (canonicalWindowIndex_pos N M hN) (canonicalWindowIndex_ge N M)
    · exact optimizedAverage_norm_sq N (canonicalWindowIndex N M)
        (canonicalWindowIndex_pos N M hN) (canonicalWindowIndex_ge N M)
  · rintro E ⟨x, hx, hhead, rfl⟩
    rw [exact_head_norm_sq_split x N hhead]
    apply add_le_add le_rfl
    exact (canonicalWindow_tail_isLeast_all_legal N M hN hNM).2
      ⟨x, hx, hhead, rfl⟩

end SignedCovariance

end RiemannResearch.RH.Pareto.CoefficientStabilization
