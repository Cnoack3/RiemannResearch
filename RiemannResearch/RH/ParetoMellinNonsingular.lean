import RiemannResearch.LinearAlgebra.CauchyNonsingular
import RiemannResearch.RH.ParetoMellinGramOptimization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Automatic nonsingularity of distinct-point Mellin Cauchy-Gram matrices

Source: user-requested Ramanujan dual program, October 2026.
The general finite Cauchy matrix interpolation proof supplies the previously
explicit determinant hypothesis. The right-half-plane statement is an exact
criterion: nonsingularity is equivalent to distinctness of the test points.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No half-plane assumption is needed when the nonpole conditions are explicit. -/
theorem mellinCauchyGram_det_ne_zero_of_injective (s : ι → ℂ)
    (hinj : Function.Injective s)
    (hden : ∀ i j, s i + starRingEnd ℂ (s j) - 1 ≠ 0) :
    (mellinCauchyGram s).det ≠ 0 := by
  have hy : Function.Injective (fun j => starRingEnd ℂ (s j) - 1) := by
    intro i j hij
    apply hinj
    exact star_injective (sub_left_inj.mp hij)
  have hd : ∀ i j, s i + (starRingEnd ℂ (s j) - 1) ≠ 0 := by
    intro i j
    have he : s i + (starRingEnd ℂ (s j) - 1) =
        s i + starRingEnd ℂ (s j) - 1 := by ring
    rw [he]
    exact hden i j
  have hm : cauchyMatrix s (fun j => starRingEnd ℂ (s j) - 1) =
      mellinCauchyGram s := by
    funext i j
    dsimp [cauchyMatrix, mellinCauchyGram]
    congr 1
    ring
  rw [← hm]
  exact cauchyMatrix_det_ne_zero s _ hinj hy hd

/-- Repeated tests are the only cause of singularity in the strict half-plane. -/
theorem mellinCauchyGram_det_ne_zero_iff_injective (s : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    (mellinCauchyGram s).det ≠ 0 ↔ Function.Injective s := by
  classical
  constructor
  · intro hdet i j hij
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_row_eq hne
    funext k
    simp only [mellinCauchyGram, hij]
  · intro hinj
    apply mellinCauchyGram_det_ne_zero_of_injective s hinj
    intro i j hz
    have h := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re,
      Complex.one_re, Complex.zero_re] at h
    linarith [hs i, hs j]

end RiemannResearch.RH.Pareto
