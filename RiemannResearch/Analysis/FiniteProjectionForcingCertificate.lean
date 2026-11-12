/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramBackwardError
import RiemannResearch.Analysis.FiniteGramTrialCertificate
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Complete certificates for two successive projection solves

Source: Pareto-first research agenda, Priority 2, 11 November 2026.
A trial first fit changes the forcing source. This file propagates that
error through a bounded operator and a second inexact Gram solve.
Every defect uses the complete Hilbert Gram, including all signed terms.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteProjectionForcingCertificate
open FiniteHilbertGram FiniteGramCapacity FiniteGramBackwardError

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projection_energy {v : ι → E} (hv : LinearIndependent ℝ v) (x : E) :
    ‖(synthesisSpan v).starProjection x‖ ^ 2 = capacity hv (cross v x) := by
  rw [← synthesis_inverseCoeff_eq_projection hv, gram_quadratic]
  change (∑ i, inverseCoeff hv x i * inner ℝ (v i)
    (Fintype.linearCombination ℝ v (inverseCoeff hv x))) = _
  simp_rw [inverseCoeff_normal]
  rfl

theorem projection_energy_inverseGram [DecidableEq ι] {v : ι → E}
    (hv : LinearIndependent ℝ v) (x : E) :
    ‖(synthesisSpan v).starProjection x‖ ^ 2 =
      dotProduct (cross v x) ((gramMatrix v)⁻¹.mulVec (cross v x)) := by
  rw [projection_energy hv, capacity_eq_inverseGram hv]

theorem defectEnergy_eq_projection_error {v : ι → E}
    (hv : LinearIndependent ℝ v) (x : E) (c : ι → ℝ) :
    defectEnergy hv x c =
      ‖Fintype.linearCombination ℝ v c - (synthesisSpan v).starProjection x‖ ^ 2 := by
  rw [defectEnergy_eq_norm_sq, map_sub, synthesis_inverseCoeff_eq_projection hv]

theorem sqrt_defectEnergy {v : ι → E} (hv : LinearIndependent ℝ v)
    (x : E) (c : ι → ℝ) :
    Real.sqrt (defectEnergy hv x c) =
      ‖Fintype.linearCombination ℝ v c - (synthesisSpan v).starProjection x‖ := by
  rw [defectEnergy_eq_projection_error, Real.sqrt_sq (norm_nonneg _)]

/-- Error in a second solve, including the change caused by an inexact first solve. -/
theorem two_solve_error {v : ι → E} (hv : LinearIndependent ℝ v)
    (D : E →L[ℝ] E) (L : ℝ) (hD : ∀ x, ‖D x‖ ≤ L * ‖x‖)
    (x : E) (c t : ι → ℝ) :
    ‖(synthesisSpan v).starProjection (D (x - (synthesisSpan v).starProjection x)) -
        Fintype.linearCombination ℝ v t‖ ≤
      Real.sqrt (defectEnergy hv
        (D (x - Fintype.linearCombination ℝ v c)) t) +
      L * Real.sqrt (defectEnergy hv x c) := by
  let P := (synthesisSpan v).starProjection
  let y := Fintype.linearCombination ℝ v c
  let z := Fintype.linearCombination ℝ v t
  have hsource : P (D (x - P x)) - P (D (x - y)) = P (D (y - P x)) := by
    rw [← map_sub, ← map_sub]
    congr 2
    abel
  have hchange :
      ‖P (D (x - P x)) - P (D (x - y))‖ ≤ L * ‖y - P x‖ := by
    rw [hsource]
    exact (Submodule.norm_starProjection_apply_le _ _).trans (hD _)
  have htriangle : ‖P (D (x - P x)) - z‖ ≤
      ‖P (D (x - P x)) - P (D (x - y))‖ + ‖P (D (x - y)) - z‖ := by
    calc
      _ = ‖(P (D (x - P x)) - P (D (x - y))) + (P (D (x - y)) - z)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_add_le _ _
  rw [sqrt_defectEnergy hv, sqrt_defectEnergy hv]
  change ‖P (D (x - P x)) - z‖ ≤ ‖z - P (D (x - y))‖ + L * ‖y - P x‖
  rw [norm_sub_rev z]
  linarith

/-- The signed six-term backward budgets may be used without splitting their cross terms. -/
theorem two_solve_error_backward {v : ι → E} (hv : LinearIndependent ℝ v)
    (D : E →L[ℝ] E) (L : ℝ) (hD : ∀ x, ‖D x‖ ≤ L * ‖x‖)
    (x : E) (A B : Matrix ι ι ℝ) (b z c t : ι → ℝ) :
    ‖(synthesisSpan v).starProjection (D (x - (synthesisSpan v).starProjection x)) -
        Fintype.linearCombination ℝ v t‖ ≤
      Real.sqrt (backwardBudget hv
        (D (x - Fintype.linearCombination ℝ v c)) B z t) +
      L * Real.sqrt (backwardBudget hv x A b c) := by
  simp only [backwardBudget_eq_defectEnergy]
  exact two_solve_error hv D L hD x c t

/-- Independently checked bounds for both normal residuals give a forcing endpoint. -/
theorem two_solve_upper {v : ι → E} (hv : LinearIndependent ℝ v)
    (D : E →L[ℝ] E) (L : ℝ) (hL : 0 ≤ L)
    (hD : ∀ x, ‖D x‖ ≤ L * ‖x‖) (x : E) (c t : ι → ℝ)
    (e₁ e₂ : ℝ) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hfirst : defectEnergy hv x c ≤ e₁ ^ 2)
    (hsecond : defectEnergy hv (D (x - Fintype.linearCombination ℝ v c)) t ≤ e₂ ^ 2) :
    ‖(synthesisSpan v).starProjection (D (x - (synthesisSpan v).starProjection x))‖ ≤
      ‖Fintype.linearCombination ℝ v t‖ + e₂ + L * e₁ := by
  have h₁ : Real.sqrt (defectEnergy hv x c) ≤ e₁ := by
    exact (Real.sqrt_le_iff).mpr ⟨he₁, hfirst⟩
  have h₂ : Real.sqrt (defectEnergy hv
      (D (x - Fintype.linearCombination ℝ v c)) t) ≤ e₂ := by
    exact (Real.sqrt_le_iff).mpr ⟨he₂, hsecond⟩
  have h := two_solve_error hv D L hD x c t
  have hmul := mul_le_mul_of_nonneg_left h₁ hL
  have ht := norm_le_norm_add_norm_sub
    (Fintype.linearCombination ℝ v t)
    ((synthesisSpan v).starProjection (D (x - (synthesisSpan v).starProjection x)))
  rw [norm_sub_rev (Fintype.linearCombination ℝ v t)] at ht
  linarith

/-- Trial-energy and full normal-defect intervals enclose the true minimum error. -/
theorem minimum_error_interval {v : ι → E} (hv : LinearIndependent ℝ v)
    (x : E) (c : ι → ℝ) (elo ehi dlo dhi : ℝ)
    (helo : elo ≤ ‖x - Fintype.linearCombination ℝ v c‖ ^ 2)
    (hehi : ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 ≤ ehi)
    (hdlo : dlo ≤ defectEnergy hv x c) (hdhi : defectEnergy hv x c ≤ dhi) :
    elo - dhi ≤ ‖x - (synthesisSpan v).starProjection x‖ ^ 2 ∧
      ‖x - (synthesisSpan v).starProjection x‖ ^ 2 ≤ ehi - dlo := by
  have h := residual_error_defect_identity hv x c
  rw [synthesis_inverseCoeff_eq_projection hv] at h
  constructor <;> linarith

end RiemannResearch.Analysis.FiniteProjectionForcingCertificate
