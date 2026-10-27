/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CountableJumpEnergyLimit
import RiemannResearch.RH.QSquarefreePrimeDirichletCriterion

/-!
# A finite-grid criterion for the actual squarefree correction

Source: the user's prime-resampling research agenda. This formulation uses
only each fixed finite grid of the moving correction, and allows its good
indices to depend on that grid. Thus no complete approximant Dirichlet form
or artificial truncation-boundary estimate is required. A finite common
bound remains the precise open arithmetic premise.
-/

noncomputable section
open Filter
open scoped Topology ENNReal
namespace RiemannResearch.RH.QSquarefreePrimeDirichletCriterion
open ZetaTwoHilbert QSquarefreeSmoothedProjection QCountableJumpEnergy PrimeResampling
open RiemannResearch.Analysis.CountableJumpEnergy
open RiemannResearch.Analysis.CountableJumpEnergyLimit

theorem movingWeightedSequence_tendsto (n : ℕ) :
    Tendsto (fun N => qWeightedSequence (movingCorrection N) n) atTop
      (𝓝 (qWeightedSequence correction n)) :=
  (qSequence_tendsto_of_tendsto movingCorrection_tendsto n).const_mul _

theorem movingFiniteGridEnergy_tendsto (S : Finset ℕ) :
    Tendsto (fun N => finiteSetEnergy primeFlow (qWeightedSequence (movingCorrection N)) S)
      atTop (𝓝 (finiteSetEnergy primeFlow (qWeightedSequence correction) S)) :=
  finiteSetEnergy_tendsto primeFlow primeFlow_coeff_ne_top
    (fun N => qWeightedSequence (movingCorrection N)) (qWeightedSequence correction)
    atTop movingWeightedSequence_tendsto S

/-- Actual finite grids of the actual moving corrections control the full
limiting prime-resampling Dirichlet form. -/
theorem correctionDirichletEnergy_le_of_frequently_finiteGrid_bound
    (C : ℝ≥0∞)
    (hC : ∀ S : Finset ℕ, ∃ᶠ N in atTop,
      finiteSetEnergy primeFlow (qWeightedSequence (movingCorrection N)) S ≤ C) :
    correctionDirichletEnergy ≤ C := by
  exact countableJumpEnergy_le_of_frequently_finiteSetEnergy_le
    primeFlow primeFlow_coeff_ne_top (fun N => qWeightedSequence (movingCorrection N))
    (qWeightedSequence correction) atTop movingWeightedSequence_tendsto C hC

theorem residual_zero_of_frequently_finiteGrid_bound
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ S : Finset ℕ, ∃ᶠ N in atTop,
      finiteSetEnergy primeFlow (qWeightedSequence (movingCorrection N)) S ≤ C) :
    ZetaTwoOptimizerStage.limitingResidual = 0 :=
  residual_zero_of_correctionDirichletEnergy_ne_top
    (ne_top_of_le_ne_top hCfinite
      (correctionDirichletEnergy_le_of_frequently_finiteGrid_bound C hC))

/-- The only open premise is a common finite bound on cofinally many actual
moving corrections for each fixed finite physical grid. -/
theorem riemannHypothesis_of_frequently_finiteGrid_bound
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hC : ∀ S : Finset ℕ, ∃ᶠ N in atTop,
      finiteSetEnergy primeFlow (qWeightedSequence (movingCorrection N)) S ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_correctionDirichletEnergy_ne_top
    (ne_top_of_le_ne_top hCfinite
      (correctionDirichletEnergy_le_of_frequently_finiteGrid_bound C hC))

/-- The finite-grid criterion is equivalent to zero actual residual. This
does not assert the converse implication from RH to squarefree density. -/
theorem residual_zero_iff_frequently_finiteGrid_bound :
    ZetaTwoOptimizerStage.limitingResidual = 0 ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ S : Finset ℕ, ∃ᶠ N in atTop,
        finiteSetEnergy primeFlow (qWeightedSequence (movingCorrection N)) S ≤ C := by
  constructor
  · intro hr
    refine ⟨1, by norm_num, ?_⟩
    intro S
    have hc : correction = 0 := by simp [correction, hr]
    have hq : qSequence (0 : QHilbert) = 0 := qSequenceLinear.map_zero
    have hz : finiteSetEnergy primeFlow (qWeightedSequence correction) S = 0 := by
      simp [hc, qWeightedSequence, hq, finiteSetEnergy]
    have ht := movingFiniteGridEnergy_tendsto S
    rw [hz] at ht
    exact (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))).frequently.mono
      (fun N hN => le_of_lt hN)
  · rintro ⟨C, hCfinite, hC⟩
    exact residual_zero_of_frequently_finiteGrid_bound C hCfinite hC

/-- A nonzero actual residual forces finite-grid energies to infinity for
every physical-head schedule tending to infinity. -/
theorem movingFiniteGridEnergy_tendsto_top_of_residual_ne_zero
    (hr : ZetaTwoOptimizerStage.limitingResidual ≠ 0)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto
      (fun N => finiteSetEnergy primeFlow (qWeightedSequence (movingCorrection N))
        (Finset.range (H N))) atTop (𝓝 ⊤) := by
  exact finiteSetEnergy_range_tendsto_top primeFlow primeFlow_coeff_ne_top
    (fun N => qWeightedSequence (movingCorrection N)) (qWeightedSequence correction)
    atTop movingWeightedSequence_tendsto
    (correctionDirichletEnergy_eq_top_iff_residual_ne_zero.mpr hr) H hH

end RiemannResearch.RH.QSquarefreePrimeDirichletCriterion
