import RiemannResearch.RH.ParetoMellinSchur
import RiemannResearch.RH.ParetoMellinInnovationRemainder
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Exact reindexing of finite Mellin interpolation

Source: independently assembled finite change-of-index identities for the
user's sixth Ramanujan transfer program, 24 October 2026. The optimized
coefficients, complete kernel, capacity and full remainder are independent
of the enumeration. This is used in ordered innovation accounting.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem mellinCauchyGram_det_reindex (e : ι ≃ κ) (s : κ → ℂ) :
    (mellinCauchyGram (s ∘ e)).det = (mellinCauchyGram s).det := by
  change ((mellinCauchyGram s).submatrix e e).det = _
  exact Matrix.det_submatrix_equiv_self e (mellinCauchyGram s)

theorem mellinInverseCoefficients_reindex (e : ι ≃ κ) (s b : κ → ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    mellinInverseCoefficients (s ∘ e) (b ∘ e) =
      mellinInverseCoefficients s b ∘ e := by
  symm
  apply mellinInverseCoefficients_unique
  · rwa [mellinCauchyGram_det_reindex]
  · intro i
    calc
      _ = ∑ j : κ, mellinCauchyGram s (e i) j * mellinInverseCoefficients s b j :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = b (e i) := mellinInverseCoefficients_normal s b hdet (e i)

theorem mellinInverseCapacity_reindex (e : ι ≃ κ) (s b : κ → ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    mellinInverseCapacity (s ∘ e) (b ∘ e) = mellinInverseCapacity s b := by
  unfold mellinInverseCapacity
  rw [mellinInverseCoefficients_reindex e s b hdet]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem finiteMellinKernel_reindex (e : ι ≃ κ) (s c : κ → ℂ) (x : ℝ) :
    finiteMellinKernel (s ∘ e) (c ∘ e) x = finiteMellinKernel s c x := by
  unfold finiteMellinKernel
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem finiteMellinKernel_inverse_reindex (e : ι ≃ κ) (s b : κ → ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) (x : ℝ) :
    finiteMellinKernel (s ∘ e) (mellinInverseCoefficients (s ∘ e) (b ∘ e)) x =
      finiteMellinKernel s (mellinInverseCoefficients s b) x := by
  rw [mellinInverseCoefficients_reindex e s b hdet, finiteMellinKernel_reindex]

theorem mellinProjectionRemainder_reindex (e : ι ≃ κ) (f : ThresholdHilbert)
    (s : κ → ℂ) (hdet : (mellinCauchyGram s).det ≠ 0) :
    mellinProjectionRemainder f (s ∘ e) = mellinProjectionRemainder f s := by
  unfold mellinProjectionRemainder
  congr 1
  funext x
  have hk := finiteMellinKernel_inverse_reindex e s
    (fun i => paretoMellin f (s i)) hdet x
  simp only [Function.comp_def] at hk ⊢
  rw [hk]

end RiemannResearch.RH.Pareto
