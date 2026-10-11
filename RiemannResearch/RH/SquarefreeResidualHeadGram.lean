/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Part of the RiemannResearch project.
Authors: Christian Noack
-/

import RiemannResearch.RH.SquarefreeResidualSampling
import RiemannResearch.Analysis.FiniteWeightedResidualGram

-- The Apache-specific header convention does not determine project licensing.
set_option linter.style.header false

/-!
# Exact finite-head residual energy in the full filtered inverse Gram

Source: structural completion of the October 2026 squarefree residual-sampling
argument. All squarefree conductors in the actual cutoff occur. The full
Hilbert Gram inverse supplies the coefficients; only the observation head is
finite. Every signed linear and quadratic term is retained.

These identities provide no cofinal arithmetic estimate and no proof of RH.
-/

noncomputable section
open scoped BigOperators


namespace RiemannResearch.RH.Pareto.SquarefreeSampling

open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.RH.ArithmeticCumulative

/-- Exactly the squarefree conductors from 2 through n+1. -/
abbrev FilteredIndex (n : ℕ) := {j : Fin n // Squarefree (j.val + 2)}

def filteredResidueAtom (n : ℕ) (i : FilteredIndex n) : ThresholdHilbert :=
  CoefficientStabilization.residueAtom i.val.val

/-- The full Hilbert inverse Gram, not a finite-head Gram inverse. -/
def filteredInverseCoefficient (n : ℕ) : FilteredIndex n → ℝ :=
  (gramMatrix (filteredResidueAtom n))⁻¹.mulVec
    (fun i => inner ℝ (filteredResidueAtom n i) hilbertOne)

/-- Physical coordinate k is the positive integer k+1. -/
def filteredResidueValue (n : ℕ) (i : FilteredIndex n) (k : ℕ) : ℝ :=
  residueFraction (i.val.val + 2) (k + 1)

def finiteHeadSource (n : ℕ) (A : Finset ℕ) (i : FilteredIndex n) : ℝ :=
  ∑ k ∈ A, paretoWeight k * filteredResidueValue n i k

/-- Complete signed physical Gram entries on the observation head. -/
def finiteHeadGram (n : ℕ) (A : Finset ℕ)
    (i j : FilteredIndex n) : ℝ :=
  ∑ k ∈ A,
    paretoWeight k * filteredResidueValue n i k * filteredResidueValue n j k

/-- The actual full residual energy is the exact Schur complement for the
same filtered Hilbert Gram matrix used in every head formula. -/
theorem energy_eq_filteredInverseGram (n : ℕ) :
    energy n = 1 - dotProduct
      (fun i : FilteredIndex n => inner ℝ (filteredResidueAtom n i) hilbertOne)
      (filteredInverseCoefficient n) := by
  classical
  have hv : LinearIndependent ℝ (filteredResidueAtom n) :=
    filteredResidueAtoms_linearIndependent n
  have hspan : finiteSpace n = synthesisSpan (filteredResidueAtom n) := by
    exact finiteSpace_eq_filteredResidueSpan n
  have hc : filteredInverseCoefficient n = inverseCoeff hv hilbertOne := by
    unfold filteredInverseCoefficient
    exact gramMatrix_inverseSource hv (cross (filteredResidueAtom n) hilbertOne)
  have hp : (finiteSpace n).starProjection hilbertOne =
      (synthesisSpan (filteredResidueAtom n)).starProjection hilbertOne := by
    simp only [hspan]
  have hs := residual_schur_value hv hilbertOne
  rw [synthesis_inverseCoeff_eq_projection hv hilbertOne, ← hp,
    hilbertOne_norm_sq, ← hc] at hs
  calc
    energy n = 1 - ∑ i : FilteredIndex n,
        filteredInverseCoefficient n i *
          cross (filteredResidueAtom n) hilbertOne i := hs
    _ = _ := by
      congr 1
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _

theorem physical_residual_eq_filteredInverseGram (n k : ℕ) :
    hilbertGibbsPhysical (residual n) k =
      1 - ∑ i : FilteredIndex n,
        filteredInverseCoefficient n i * filteredResidueValue n i k := by
  classical
  have hprojection : (finiteSpace n).starProjection hilbertOne =
      ∑ i : FilteredIndex n,
        filteredInverseCoefficient n i • filteredResidueAtom n i :=
    projection_eq_filteredInverseGram n
  have h1 : physicalEvaluationCLM k hilbertOne = 1 := by
    rw [physicalEvaluationCLM_apply, hilbertOne_sequence]
    simp [zeroAnchor]
  have hp : physicalEvaluationCLM k ((finiteSpace n).starProjection hilbertOne) =
      ∑ i : FilteredIndex n,
        filteredInverseCoefficient n i * filteredResidueValue n i k := by
    rw [hprojection, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, physicalEvaluationCLM_apply,
      filteredResidueAtom, CoefficientStabilization.residueAtom,
      normalizedResidueHilbert_sequence]
    rfl
  rw [hilbertGibbsPhysical_eq, ← physicalEvaluationCLM_apply,
    residual, map_sub, h1, hp]

/-- Exact finite-head residual energy with the entire inverse-Gram
coefficient vector and every signed mixed term. -/
theorem residual_head_energy_eq_signedInverseGram (n : ℕ) (A : Finset ℕ) :
    (∑ k ∈ A, paretoWeight k * (hilbertGibbsPhysical (residual n) k) ^ 2) =
      (∑ k ∈ A, paretoWeight k) -
        2 * (∑ i : FilteredIndex n,
          filteredInverseCoefficient n i * finiteHeadSource n A i) +
        ∑ i : FilteredIndex n, ∑ j : FilteredIndex n,
          filteredInverseCoefficient n i * filteredInverseCoefficient n j *
            finiteHeadGram n A i j := by
  classical
  simp_rw [physical_residual_eq_filteredInverseGram]
  exact RiemannResearch.Analysis.weighted_finite_head_square_expansion
    A paretoWeight (filteredInverseCoefficient n) (filteredResidueValue n)

/-- The actual residual sampling head mass is the signed inverse-Gram
head energy divided by the actual full residual norm square. -/
theorem headMass_eq_signedInverseGram (n : ℕ) (A : Finset ℕ) :
    headMass n A =
      ((∑ k ∈ A, paretoWeight k) -
        2 * (∑ i : FilteredIndex n,
          filteredInverseCoefficient n i * finiteHeadSource n A i) +
        ∑ i : FilteredIndex n, ∑ j : FilteredIndex n,
          filteredInverseCoefficient n i * filteredInverseCoefficient n j *
            finiteHeadGram n A i j) / energy n := by
  classical
  unfold headMass siteMass
  rw [← Finset.sum_div, residual_head_energy_eq_signedInverseGram]

end RiemannResearch.RH.Pareto.SquarefreeSampling
