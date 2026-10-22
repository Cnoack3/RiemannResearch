import RiemannResearch.Analysis.LaguerreMeasure
import RiemannResearch.Analysis.LaguerreOrthogonality
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # The actual ordinary Laguerre vectors in exponential L2

This realizes the integral polynomials as orthonormal Hilbert-space vectors.
Completeness is proved separately in LaguerreCompleteness.
-/

noncomputable section
open MeasureTheory
namespace RiemannResearch.Analysis

theorem memLp_laguerreValue (n : ℕ) :
    MemLp (laguerreValue n) 2 laguerreMeasure := by
  apply (memLp_two_iff_integrable_sq
    (continuous_laguerreValue n).measurable.aestronglyMeasurable).2
  rw [integrable_laguerreMeasure_iff]
  exact integrableOn_laguerre_sq_mul_exp_neg n

def laguerreVector (n : ℕ) : LaguerreL2 :=
  (memLp_laguerreValue n).toLp (laguerreValue n)

theorem laguerreVector_coe (n : ℕ) :
    laguerreVector n =ᵐ[laguerreMeasure] laguerreValue n :=
  (memLp_laguerreValue n).coeFn_toLp

theorem laguerreVector_orthonormal : Orthonormal ℝ laguerreVector := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [laguerreVector, laguerreVector, inner_toLp_laguerreMeasure]
  exact integral_Ici_laguerre_mul_laguerre_mul_exp_neg m n

theorem inner_laguerreVector (f : LaguerreL2) (n : ℕ) :
    inner ℝ f (laguerreVector n) =
      ∫ t, f t * laguerreValue n t ∂laguerreMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [laguerreVector_coe n] with t ht
  simp [ht, mul_comm]

end RiemannResearch.Analysis
