import RiemannResearch.Probability.ContinuousProjectionLaw
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Symmetry and joint kernel density of finite projection laws

Source: the finite projection density from Hough--Krishnapur--Peres--Virág,
*Determinantal Processes and Independence*, Probability Surveys 3 (2006),
Section 2, https://doi.org/10.1214/154957806000000078.  This module proves
permutation invariance of that density and its equality with the determinant
of the projection kernel.
-/

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal ComplexConjugate

namespace ProbabilityTheory.ContinuousProjectionDPP

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- The finite projection kernel in the conjugate-second convention. -/
def kernel (ψ : Fin n → X → ℂ) (x y : X) : ℂ :=
  ∑ i, ψ i x * star (ψ i y)

lemma squaredDet_permute (ψ : Fin n → X → ℂ) (x : Fin n → X)
    (σ : Equiv.Perm (Fin n)) : squaredDet ψ (x ∘ σ) = squaredDet ψ x := by
  change ‖((evalMatrix ψ x).submatrix id σ).det‖ ^ 2 = _
  rw [Matrix.det_permute', norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp [hs, squaredDet]

lemma density_permute (ψ : Fin n → X → ℂ) (x : Fin n → X)
    (σ : Equiv.Perm (Fin n)) : density ψ (x ∘ σ) = density ψ x := by
  simp [density, squaredDet_permute]

lemma kernelMatrix_eq (ψ : Fin n → X → ℂ) (x : Fin n → X) :
    (fun i j => kernel ψ (x i) (x j)) =
      ((evalMatrix ψ x).conjTranspose * evalMatrix ψ x).transpose := by
  ext i j
  simp only [kernel, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, evalMatrix]
  congr 1
  ext k
  exact mul_comm _ _

/-- The squared Slater determinant is the determinant of the correlation kernel. -/
theorem det_kernelMatrix (ψ : Fin n → X → ℂ) (x : Fin n → X) :
    Matrix.det (fun i j => kernel ψ (x i) (x j)) = (squaredDet ψ x : ℂ) := by
  rw [kernelMatrix_eq, Matrix.det_transpose, Matrix.det_mul, Matrix.det_conjTranspose]
  simp [squaredDet, Complex.conj_mul', Complex.ofReal_pow]

/-- Exact normalized joint-density formula in terms of the projection kernel. -/
theorem density_eq_det_kernelMatrix (ψ : Fin n → X → ℂ) (x : Fin n → X) :
    (density ψ x : ℂ) =
      Matrix.det (fun i j => kernel ψ (x i) (x j)) / (n.factorial : ℂ) := by
  rw [det_kernelMatrix]
  simp [density]

/-- The actual joint measure is invariant under relabeling of its points. -/
theorem map_law_permute (μ : Measure X) [SigmaFinite μ]
    (ψ : Fin n → X → ℂ) (σ : Equiv.Perm (Fin n)) :
    (law μ ψ).map (fun x => x ∘ σ) = law μ ψ := by
  let T : (Fin n → X) ≃ᵐ (Fin n → X) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => X) σ.symm
  have hT : MeasurePreserving T (Measure.pi fun _ : Fin n => μ)
      (Measure.pi fun _ : Fin n => μ) :=
    measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ.symm
  have happly : ∀ x, T x = x ∘ σ := by
    intro x
    ext i
    simp [T, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      Equiv.piCongrLeft', eq_rec_constant]
  have hmap : (law μ ψ).map T = law μ ψ := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply T.measurable hs, law,
      withDensity_apply _ (T.measurable hs), withDensity_apply _ hs]
    calc
      (∫⁻ x in T ⁻¹' s, ENNReal.ofReal (density ψ x)
          ∂(Measure.pi fun _ : Fin n => μ)) =
        ∫⁻ x in T ⁻¹' s, ENNReal.ofReal (density ψ (T x))
          ∂(Measure.pi fun _ : Fin n => μ) := by
            apply lintegral_congr
            intro x
            rw [happly, density_permute]
      _ = _ := hT.setLIntegral_comp_preimage_emb T.measurableEmbedding
        (fun x => ENNReal.ofReal (density ψ x)) s
  have hfun : (T : (Fin n → X) → (Fin n → X)) = fun x => x ∘ σ := funext happly
  rwa [hfun] at hmap

end ProbabilityTheory.ContinuousProjectionDPP
