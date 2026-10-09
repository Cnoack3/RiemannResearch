import RiemannResearch.RH.PhysicalResidualMean
import RiemannResearch.LinearAlgebra.MeanOneBlockSchur

/-!
# Complete screened source of the actual physical projection

The exact rank-two cross theorem
`MeanOneBlockSchur.rankTwo_residual_screenedSource_of_cross_matrix`
supplies the generic finite identity. Every finite matrix and cross block below
is formed from the actual physical Gram; no Baker or source lower bound is
needed for the exact identity.

Source: `crt_baker_mean_source_handoff.txt`, Section 6, complete signed
prime-adjunction source formula. The formula holds for every nested finite
packet set, not only prime adjunction.
-/

noncomputable section
open Matrix
namespace RiemannResearch.RH.Pareto.PhysicalScreenedSource
open PhysicalPacketCore PhysicalSchurCoupling PhysicalSourceProjection PhysicalResidualMean
open RiemannResearch.RH.Pareto.PhysicalSchurReindex
open RiemannResearch.LinearAlgebra.MeanOneBlockSchur
open RiemannResearch.LinearAlgebra.RankTwoWoodbury

/-- The actual fresh/old physical Gram cross block, with all signs retained. -/
def projectionAdjunctionCross (s t : Finset ℕ) (hst : s ⊆ t) :
    Matrix ↥(t \ s) s ℝ :=
  fun i j => ramanujanGramMatrix t
    (freshInclusion s t i) (oldInclusion s t hst j)

/-- The cross decomposition is proved from the complete physical Gram. -/
theorem projectionAdjunctionCross_eq_rankTwo (s t : Finset ℕ) (hst : s ⊆ t) :
    projectionAdjunctionCross s t hst =
      Real.pi • (crossCore s t hst)ᵀ + (1/2 : ℝ) •
        (vecMulVec (ramanujanVonMangoldtVector (t \ s))
          (ramanujanTotientVector s) +
          vecMulVec (ramanujanTotientVector (t \ s))
            (ramanujanVonMangoldtVector s)) := by
  ext i j
  unfold projectionAdjunctionCross
  rw [gram_eq_rankTwo_derivedCore]
  simp only [rankTwoMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  rw [core_fresh_old s t hst i j]
  rfl

/-- Complete actual residual source on a fresh packet block. Only ordinary
legal old-stage assumptions and the nested index sets are needed. The inverse,
projection normal equation, and cross decomposition are all discharged. -/
theorem projection_residual_screenedSource (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanVonMangoldtVector (t \ s) -
        projectionAdjunctionCross s t hst *ᵥ projectionCoefficients s =
      projectionResidualMean s • screenedLambda s t hst -
        (sourceProjectionCharge s / 2) • screenedTotient s t hst := by
  have h := rankTwo_residual_screenedSource_of_cross_matrix
    Real.pi (derivedCore s) (derivedCore s)⁻¹ (ramanujanGramMatrix s)
    (crossCore s t hst) (projectionAdjunctionCross s t hst)
    (ramanujanVonMangoldtVector s) (ramanujanTotientVector s)
    (projectionCoefficients s) (ramanujanVonMangoldtVector (t \ s))
    (ramanujanTotientVector (t \ s))
    (inverseCore_mul s hs ho) (gram_eq_rankTwo_derivedCore s)
    (projection_normalEquation s hs ho)
    (projectionAdjunctionCross_eq_rankTwo s t hst)
  simpa only [projectionResidualMean, screenedLambda, screenedTotient,
    projection_pairing] using h

end RiemannResearch.RH.Pareto.PhysicalScreenedSource
