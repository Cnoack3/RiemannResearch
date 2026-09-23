import RiemannResearch.Analysis.FiniteHilbertGramProjection

/-!
# Inverse Gram entries from biorthogonal vectors
Source: user-provided Pareto_Lean_Research_Connections_2026-09-23(1).md,
equations (2)--(3), for the statements. The proofs use the actual Gram inverse.
-/
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram
noncomputable section
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Row i, column j of the actual inverse Gram endomorphism. -/
def inverseEntry {v : ι → H} (hv : LinearIndependent ℝ v) (i j : ι) : ℝ :=
  (gramEquiv hv).symm (Pi.single j 1) i

theorem inverseCoeff_dual {v h : ι → H} (hv : LinearIndependent ℝ v)
    (hdual : ∀ i j, inner ℝ (v i) (h j) = if i = j then 1 else 0) (i j : ι) :
    inverseCoeff hv (h j) i = inverseEntry hv i j := by
  have hc : cross v (h j) = Pi.single j 1 := by
    funext k
    simp [cross, hdual, Pi.single_apply, eq_comm]
  simp only [inverseCoeff, inverseEntry, hc]

theorem projection_dual_inner {v h : ι → H} (hv : LinearIndependent ℝ v)
    (hdual : ∀ i j, inner ℝ (v i) (h j) = if i = j then 1 else 0) (i j : ι) :
    inner ℝ ((synthesisSpan v).starProjection (h i))
      ((synthesisSpan v).starProjection (h j)) = inverseEntry hv j i := by
  rw [← synthesis_inverseCoeff_eq_projection hv (h i),
    ← synthesis_inverseCoeff_eq_projection hv (h j), inner_synthesis_left]
  simp only [inverseCoeff_normal, cross, hdual]
  simpa using inverseCoeff_dual hv hdual j i

theorem inverseEntry_symm_of_dual {v h : ι → H} (hv : LinearIndependent ℝ v)
    (hdual : ∀ i j, inner ℝ (v i) (h j) = if i = j then 1 else 0) (i j : ι) :
    inverseEntry hv i j = inverseEntry hv j i := by
  rw [← projection_dual_inner hv hdual j i, real_inner_comm,
    projection_dual_inner hv hdual i j]

theorem residual_dual_bilinear {v h : ι → H} (hv : LinearIndependent ℝ v)
    (hdual : ∀ i j, inner ℝ (v i) (h j) = if i = j then 1 else 0) (i j : ι) :
    inner ℝ (h i - (synthesisSpan v).starProjection (h i))
      (h j - (synthesisSpan v).starProjection (h j)) =
      inner ℝ (h i) (h j) - inverseEntry hv i j := by
  rw [← synthesis_inverseCoeff_eq_projection hv (h i),
    ← synthesis_inverseCoeff_eq_projection hv (h j), residual_bilinear_schur]
  simp only [cross, hdual]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [inverseCoeff_dual hv hdual, inverseEntry_symm_of_dual hv hdual]

theorem residual_dual_norm_sq {v h : ι → H} (hv : LinearIndependent ℝ v)
    (hdual : ∀ i j, inner ℝ (v i) (h j) = if i = j then 1 else 0) (i : ι) :
    ‖h i - (synthesisSpan v).starProjection (h i)‖ ^ 2 =
      ‖h i‖ ^ 2 - inverseEntry hv i i := by
  simpa only [real_inner_self_eq_norm_sq] using residual_dual_bilinear hv hdual i i

end
end RiemannResearch.Analysis.FiniteHilbertGram
