import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Maximal Rayleigh values for real symmetric matrices

Source: the standard finite-dimensional Rayleigh principle, formalized in
Mathlib by LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional.
The concrete consumer is RH/SquarefreeResidueMatrixGrowth.
-/
namespace Matrix
noncomputable section
open scoped BigOperators

def maximalRayleigh {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℝ :=
  ⨆ x : {v : EuclideanSpace ℝ ι // v ≠ 0},
    inner ℝ (Matrix.toEuclideanLin A x.val) x.val / ‖x.val‖^2

theorem maximalRayleigh_hasEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin A) (maximalRayleigh A) := by
  have hT : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  exact hT.hasEigenvalue_iSup_of_finiteDimensional

theorem rayleigh_le_maximalRayleigh {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    inner ℝ (Matrix.toEuclideanLin A x) x / ‖x‖^2 ≤ maximalRayleigh A := by
  let C := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hb : BddAbove (Set.range (fun y : {v : EuclideanSpace ℝ ι // v ≠ 0} =>
      inner ℝ (Matrix.toEuclideanLin A y.val) y.val / ‖y.val‖^2)) := by
    refine ⟨‖C‖,?_⟩
    rintro y ⟨v,rfl⟩
    change C.rayleighQuotient v.val ≤ ‖C‖
    exact (le_abs_self _).trans (C.rayleighQuotient_le_norm _)
  exact le_ciSup hb ⟨x,hx⟩
end
end Matrix
