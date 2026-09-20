import RiemannResearch.RH.ResidueModeGramInverse
import RiemannResearch.RH.ParetoBoundedMellinLinearity
import RiemannResearch.RH.MellinFrequencyRegularization

/-!
# The Mellin inverse-Gram kernel is the orthonormal mode kernel

Source: user-requested Mellin DPP construction, 20 September 2026.
All transforms are the actual critical-line Mellin integrals; boundedness
of the finite residue combinations supplies the needed integral linearity.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.MellinFrequency
open CoefficientStabilization IntegerDPP
open RiemannResearch.Analysis.FiniteHilbertGram

theorem modeFeature_expansion (n : ℕ) (j : Fin n) (t : ℝ) :
    modeFeature j.val t = ∑ i : Fin n,
      (modeMatrix n j i : ℂ) * paretoMellin (residueAtom i.val) (criticalPoint t) := by
  unfold modeFeature
  rw [residueMode_expansion_finite n j,
    paretoMellin_fintype_sum_of_bounded]
  · simp only [paretoMellin_smul, Complex.real_smul]
  · intro i
    apply finiteSpace_sequence_bounded n
    apply (finiteSpace n).smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp

/-- Exact equality with the finite orthonormal projection kernel. -/
theorem kernel_eq_mode_sum (n : ℕ) (t u : ℝ) :
    kernel n t u = ∑ k : Fin n, modeFeature k.val t * star (modeFeature k.val u) := by
  simp only [kernel, fullGram_inverse_eq_modeMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [modeFeature_expansion n k t, modeFeature_expansion n k u]
  simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end RiemannResearch.RH.Pareto.MellinFrequency
