/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteGramOneStepCapacity

/-!
# Exact affine calculus for finite Gram screening

Source: direct Hilbert Gram algebra in the user's directed RH attempt,
24 September 2026. These lemmas show that adding an old synthesized vector
does not affect the screened residual, scaling commutes with screening,
and screening cannot increase squared norm. They do not require the old
family to be independent. The concrete consumer is the canonical Mobius
window gain, whose reciprocal Mobius factor can then be cancelled exactly.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem screenedVector_norm_sq_le (v : ι → H) (f : H) :
    ‖screenedVector v f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hs := gram_quadratic v (screeningCoeff v f)
  rw [screeningCoeff_normal] at hs
  rw [screenedVector_energy, ← hs]
  exact sub_le_self _ (sq_nonneg _)

end RiemannResearch.Analysis.FiniteHilbertGram

namespace RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem screenedVector_eq_of_normal (v : ι → H) (f : H) (a : ι → ℝ)
    (ha : gram v a = cross v f) :
    screenedVector v f = f - Fintype.linearCombination ℝ v a := by
  have hg : gram v (screeningCoeff v f - a) = 0 := by
    rw [map_sub, screeningCoeff_normal, ha, sub_self]
  have hn : ‖Fintype.linearCombination ℝ v (screeningCoeff v f - a)‖ ^ 2 = 0 := by
    rw [gram_quadratic, hg]
    simp
  have hz : Fintype.linearCombination ℝ v (screeningCoeff v f - a) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  rw [map_sub, sub_eq_zero] at hz
  simp only [screenedVector, hz]

theorem screenedVector_add_synthesis_smul (v : ι → H) (f : H)
    (a : ι → ℝ) (t : ℝ) :
    screenedVector v (Fintype.linearCombination ℝ v a + t • f) =
      t • screenedVector v f := by
  have ha : gram v (a + t • screeningCoeff v f) =
      cross v (Fintype.linearCombination ℝ v a + t • f) := by
    rw [map_add, map_smul, screeningCoeff_normal]
    funext i
    change inner ℝ (v i) (Fintype.linearCombination ℝ v a) +
      t * inner ℝ (v i) f =
        inner ℝ (v i) (Fintype.linearCombination ℝ v a + t • f)
    rw [inner_add_right, inner_smul_right]
  rw [screenedVector_eq_of_normal v _ _ ha, map_add, map_smul, screenedVector]
  module

theorem screenedVector_add_family_smul (v : ι → H) (i : ι) (f : H) (t : ℝ) :
    screenedVector v (v i + t • f) = t • screenedVector v f := by
  classical
  have hi : Fintype.linearCombination ℝ v (fun j => if j = i then 1 else 0) = v i := by
    simp [Fintype.linearCombination_apply, ite_smul]
  simpa only [hi] using screenedVector_add_synthesis_smul v f
    (fun j => if j = i then 1 else 0) t

end RiemannResearch.Analysis.FiniteHilbertGram
