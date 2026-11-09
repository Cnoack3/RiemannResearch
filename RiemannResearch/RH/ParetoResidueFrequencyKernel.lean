import RiemannResearch.RH.ParetoResidueMicroscopicGram
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring

/-!
# Frequency kernel of the nonzero residue partition

Source: the user's infinite-DPP question and the existing complete grouped
Mellin coordinates. Each feature is the Mellin transform of the normalized
indicator of one nonzero residue class. The algebraic feature-sum kernel is
exactly the grouped Gram after removing its Mellin factors.

This module proves the exact normalization. The orthonormal-family DPP
construction and the continuous-process convergence interpretation are recorded
in Infinite_DPP_and_Sine_Limits_20261109.md, with the Mellin--Plancherel argument
and references to Hough--Krishnapur--Peres--Virag (arXiv:math/0503110) and
Soshnikov (arXiv:math/0002099). No probability-law or RH assertion is introduced
as an assumption here. The partition space is larger than the legal space.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint)

/-- Mellin feature of a normalized nonzero residue-class indicator. -/
def classFrequencyFeature (N : ℕ) (r : Fin N) (t : ℝ) : ℂ :=
  classMellin N (criticalPoint t) r.castSucc /
    (criticalPoint t * (Real.sqrt (classWeight N r.castSucc) : ℂ))

/-- Feature-sum kernel before unfolding angular frequency. -/
def classFrequencyKernel (N : ℕ) (t u : ℝ) : ℂ :=
  ∑ r : Fin N, classFrequencyFeature N r t * star (classFrequencyFeature N r u)

theorem classFrequencyKernel_eq_crossSum (N : ℕ) (t u : ℝ) :
    classFrequencyKernel N t u =
      classCrossSum t u N / (criticalPoint t * star (criticalPoint u)) := by
  unfold classFrequencyKernel classCrossSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  have hsq :
      (Real.sqrt (classWeight N r.castSucc) : ℂ) ^ 2 = (classWeight N r.castSucc : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (classWeight_pos N r.castSucc).le]
  simp only [classFrequencyFeature, classCrossTerm, map_div₀, map_mul,
    Complex.star_def, Complex.conj_ofReal]
  rw [div_mul_div_comm]
  have hden :
      (criticalPoint t * (Real.sqrt (classWeight N r.castSucc) : ℂ)) *
          (starRingEnd ℂ (criticalPoint u) * (Real.sqrt (classWeight N r.castSucc) : ℂ)) =
        (criticalPoint t * starRingEnd ℂ (criticalPoint u)) *
          (classWeight N r.castSucc : ℂ) := by
    calc
      _ = (criticalPoint t * starRingEnd ℂ (criticalPoint u)) *
        (Real.sqrt (classWeight N r.castSucc) : ℂ) ^ 2 := by ring
      _ = _ := by rw [hsq]
  rw [hden, div_div]
  congr 1
  ring

/-- Under x=log(N+1)(t-t0)/(2*pi), the reference measure contributes this divisor. -/
theorem phaseStrippedCross_eq_classFrequencyKernel_div (N : ℕ) (t u : ℝ) :
    phaseStrippedCross t u N =
      classFrequencyKernel N t u / (Real.log ((N : ℝ) + 1) : ℂ) := by
  rw [classFrequencyKernel_eq_crossSum, phaseStrippedCross, classCross]
  simp only [div_div]
  congr 1
  ring

end RiemannResearch.RH.Pareto.ResidueMellin
