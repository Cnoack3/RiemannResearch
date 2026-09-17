import RiemannResearch.RH.ConditionalResidueNormalization

/-!
# The inverse formulas in the manuscript's normalized coordinates

Source: `ArithmeticVariationalProof.md`, Sections 5.1 and 6. The matrices
here are built from `g_d = R_d / d`. Positivity follows from the actual raw
arithmetic tail theorem and the proved invertible coefficient rescaling.
The literal normalized inverse formulas are identified with the previously
constructed attained minima.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.ConditionalFiniteMinimum
open Probability.ConditionalIID
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

theorem toRawCoefficients_ne_zero (D : ℕ) {c : Finset.Icc 2 D → ℝ} (hc : c ≠ 0) :
    toRawCoefficients D c ≠ 0 := by
  intro h
  apply hc
  calc
    c = toNormalizedCoefficients D (toRawCoefficients D c) :=
      (toNormalized_toRaw D c).symm
    _ = 0 := by
      rw [h]
      funext i
      simp [toNormalizedCoefficients]

theorem normalizedTailMatrix_quadratic_raw (N D : ℕ) (c : Finset.Icc 2 D → ℝ) :
    dotProduct c ((normalizedTailMatrix N D).mulVec c) =
      dotProduct (toRawCoefficients D c) ((T N D).mulVec (toRawCoefficients D c)) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [normalizedTailMatrix_entry]
  dsimp [toRawCoefficients]
  field_simp [modulus_ne_zero D i, modulus_ne_zero D j]
  <;> ring

theorem normalizedTailMatrix_quadratic (N D : ℕ) (c : Finset.Icc 2 D → ℝ) :
    dotProduct c ((normalizedTailMatrix N D).mulVec c) =
      conditionalMeanTailSquare N (normalizedSynthesis D c) := by
  rw [normalizedTailMatrix_quadratic_raw, T_quadratic, synthesis_toRaw]

theorem normalizedTailMatrix_posDef (N D : ℕ) : (normalizedTailMatrix N D).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · change (normalizedTailMatrix N D).conjTranspose = normalizedTailMatrix N D
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact conditionalTailPairing_comm N
      (cesaro (normalizedResidue j.1)) (cesaro (normalizedResidue i.1))
  · intro c hc
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp (T_posDef N D)).2
      (toRawCoefficients_ne_zero D hc)
    simpa only [star_trivial, ← normalizedTailMatrix_quadratic_raw N D c] using hpos

theorem normalizedGramMatrix_posDef (D : ℕ) : (normalizedGramMatrix D).PosDef :=
  normalizedTailMatrix_posDef 0 D

theorem normalizedGramMatrix_quadratic (D : ℕ) (c : Finset.Icc 2 D → ℝ) :
    dotProduct c ((normalizedGramMatrix D).mulVec c) =
      conditionalMeanSquare (normalizedSynthesis D c) := by
  simpa only [normalizedGramMatrix, conditionalMeanTailSquare,
    conditionalMeanSquare, Nat.add_zero] using normalizedTailMatrix_quadratic 0 D c

/-- The full attained minimum in literal normalized inverse-Gram notation. -/
theorem fullValue_eq_normalized_inverseMatrix (N D : ℕ) (hND : N + 1 ≤ D) :
    fullValue N D hND = dotProduct (fun _ : Fin N => (1 : ℝ))
      ((normalizedHeadMatrix N D * (normalizedGramMatrix D)⁻¹ *
        (normalizedHeadMatrix N D).transpose)⁻¹.mulVec (fun _ => 1)) := by
  have h := inverseMatrix_isLeast (normalizedGramMatrix D) (normalizedGramMatrix_posDef D)
    (normalizedHeadMatrix N D) (normalizedHeadMatrix_surjective N D hND) (fun _ => 1)
  simp_rw [normalizedGramMatrix_quadratic] at h
  exact (normalized_fullValue_isLeast N D hND).unique h

/-- The tail attained minimum in literal normalized inverse-tail notation. -/
theorem tailValue_eq_normalized_inverseMatrix (N D : ℕ) (hND : N + 1 ≤ D) :
    tailValue N D hND = dotProduct (fun _ : Fin N => (1 : ℝ))
      ((normalizedHeadMatrix N D * (normalizedTailMatrix N D)⁻¹ *
        (normalizedHeadMatrix N D).transpose)⁻¹.mulVec (fun _ => 1)) := by
  have h := inverseMatrix_isLeast (normalizedTailMatrix N D) (normalizedTailMatrix_posDef N D)
    (normalizedHeadMatrix N D) (normalizedHeadMatrix_surjective N D hND) (fun _ => 1)
  simp_rw [normalizedTailMatrix_quadratic] at h
  exact (normalized_tailValue_isLeast N D hND).unique h

/-- The manuscript's normalized version of the exact compulsory-head split. -/
theorem fullValue_eq_head_add_normalized_tail_inverse (N D : ℕ) (hND : N + 1 ≤ D) :
    fullValue N D hND = (N : ℝ) / ((N : ℝ) + 2) +
      dotProduct (fun _ : Fin N => (1 : ℝ))
        ((normalizedHeadMatrix N D * (normalizedTailMatrix N D)⁻¹ *
          (normalizedHeadMatrix N D).transpose)⁻¹.mulVec (fun _ => 1)) := by
  rw [fullValue_eq_head_add_tailValue, tailValue_eq_normalized_inverseMatrix]

end RiemannResearch.RH.Pareto.ConditionalFiniteMinimum
