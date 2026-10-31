/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import RiemannResearch.Analysis.DenseProjectionTesting
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coercivity, exact inverse-Gram deficits, and head-null screening

Source: SquarefreeShortHeadSchurResearch20261030.md, sections 2--3, for
the research application. These are general finite Hilbert-space results.
The inverse is the existing actual Gram inverse. The input coercivity
estimate must be supplied in each application; no arithmetic estimate is
postulated here. Both deficit terms are retained before the upper bound.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramCoercivity
open FiniteHilbertGram FiniteGramCapacity ResidualizedProjectionKernel

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem linearIndependent_of_coercive (v : ι → E) (C : ℝ)
    (hc : ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤ C * ‖Fintype.linearCombination ℝ v c‖ ^ 2) :
    LinearIndependent ℝ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hzero i
  have hz : Fintype.linearCombination ℝ v c = 0 := by
    simpa only [Fintype.linearCombination_apply] using hzero
  have hb := hc c
  rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at hb
  have hi : (c i) ^ 2 ≤ ∑ j, (c j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp (le_antisymm (hi.trans hb) (sq_nonneg _))

theorem inverseSource_synthesis_energy {v : ι → E}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    ‖Fintype.linearCombination ℝ v (inverseSource hv b)‖ ^ 2 = capacity hv b := by
  rw [gram_quadratic]
  simp only [inverseSource_normal, capacity]

/-- The complete deficit consists of a coefficient square and the coercivity
slack. Neither signed mixed source term has been discarded in this equality. -/
theorem inverse_coercivity_deficit {v : ι → E}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (C : ℝ) :
    C^2 * (∑ i, (b i) ^ 2) - C * capacity hv b =
      (∑ i, (inverseSource hv b i - C * b i) ^ 2) +
      (C * ‖Fintype.linearCombination ℝ v (inverseSource hv b)‖ ^ 2 -
        ∑ i, (inverseSource hv b i) ^ 2) := by
  have he : (∑ i, (inverseSource hv b i - C * b i) ^ 2) =
      (∑ i, (inverseSource hv b i) ^ 2) - 2*C*capacity hv b +
        C^2*(∑ i, (b i) ^ 2) := by
    calc
      _ = ∑ i, ((inverseSource hv b i) ^ 2 -
          (2*C) * (inverseSource hv b i * b i) + C^2*(b i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, capacity]
  rw [he, inverseSource_synthesis_energy]
  ring

theorem capacity_le_of_coercive {v : ι → E}
    (hv : LinearIndependent ℝ v) (C : ℝ) (hC : 0 < C)
    (hc : ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤ C * ‖Fintype.linearCombination ℝ v c‖ ^ 2)
    (b : ι → ℝ) :
    capacity hv b ≤ C * (∑ i, (b i) ^ 2) := by
  have hslack := sub_nonneg.mpr (hc (inverseSource hv b))
  have hsquares : 0 ≤ ∑ i, (inverseSource hv b i - C*b i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hprod : 0 ≤ C^2 * (∑ i, (b i) ^ 2) - C * capacity hv b := by
    rw [inverse_coercivity_deficit hv b C]
    exact add_nonneg hsquares hslack
  by_contra hbad
  have hp := mul_pos hC (sub_pos.mpr (lt_of_not_ge hbad))
  nlinarith

theorem inverseSource_sq_sum_le {v : ι → E}
    (hv : LinearIndependent ℝ v) (C : ℝ) (hC : 0 < C)
    (hc : ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤ C * ‖Fintype.linearCombination ℝ v c‖ ^ 2)
    (b : ι → ℝ) :
    (∑ i, (inverseSource hv b i) ^ 2) ≤ C^2 * (∑ i, (b i) ^ 2) := by
  have h := hc (inverseSource hv b)
  rw [inverseSource_synthesis_energy] at h
  calc
    _ ≤ C * capacity hv b := h
    _ ≤ C * (C * (∑ i, (b i) ^ 2)) :=
      mul_le_mul_of_nonneg_left (capacity_le_of_coercive hv C hC hc b) hC.le
    _ = _ := by ring

theorem inverseGram_quadratic_le [DecidableEq ι] {v : ι → E}
    (hv : LinearIndependent ℝ v) (C : ℝ) (hC : 0 < C)
    (hc : ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤ C * ‖Fintype.linearCombination ℝ v c‖ ^ 2)
    (b : ι → ℝ) :
    dotProduct b ((gramMatrix v)⁻¹.mulVec b) ≤ C * (∑ i, (b i) ^ 2) := by
  calc
    _ = capacity hv b := by
      rw [gramMatrix_inverseSource hv]
      unfold dotProduct capacity
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ ≤ _ := capacity_le_of_coercive hv C hC hc b

variable (W : Submodule ℝ E) [W.HasOrthogonalProjection]

def screened (v : ι → E) (i : ι) : E := v i - W.starProjection (v i)

theorem synthesis_screened (v : ι → E) (c : ι → ℝ) :
    Fintype.linearCombination ℝ (screened W v) c =
      Fintype.linearCombination ℝ v c -
        W.starProjection (Fintype.linearCombination ℝ v c) := by
  simp only [Fintype.linearCombination_apply, screened, smul_sub,
    Finset.sum_sub_distrib, map_sum, map_smul]

omit [Fintype ι] in
theorem screened_gram_exact (v : ι → E) (i j : ι) :
    inner ℝ (screened W v i) (screened W v j) =
      inner ℝ (v i) (v j) -
        inner ℝ (W.starProjection (v i)) (W.starProjection (v j)) := by
  have ho : inner ℝ (v i - W.starProjection (v i))
      (W.starProjection (v j)) = 0 :=
    orthogonal_inner_projection W
      (Submodule.sub_starProjection_mem_orthogonal (v i)) (v j)
  unfold screened
  rw [inner_sub_right, ho, sub_zero, inner_sub_left,
    DenseProjectionTesting.inner_eq_projected_test W
      (W.starProjection_apply_mem (v i)) (v j)]

/-- A contractive head observation that is unchanged by screening transfers
its coercivity to the complete screened Gram. -/
theorem screened_coercive (head : E → E)
    (hcontract : ∀ x, ‖head x‖ ≤ ‖x‖)
    (hstable : ∀ x, head (x - W.starProjection x) = head x)
    (v : ι → E) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤ C * ‖head (Fintype.linearCombination ℝ v c)‖ ^ 2) :
    ∀ c : ι → ℝ,
      (∑ i, (c i) ^ 2) ≤ C * ‖Fintype.linearCombination ℝ (screened W v) c‖ ^ 2 := by
  intro c
  have he : head (Fintype.linearCombination ℝ (screened W v) c) =
      head (Fintype.linearCombination ℝ v c) := by
    rw [synthesis_screened]
    exact hstable _
  have hn : ‖head (Fintype.linearCombination ℝ (screened W v) c)‖ ^ 2 ≤
      ‖Fintype.linearCombination ℝ (screened W v) c‖ ^ 2 := by
    have h := hcontract (Fintype.linearCombination ℝ (screened W v) c)
    nlinarith [norm_nonneg (head (Fintype.linearCombination ℝ (screened W v) c)),
      norm_nonneg (Fintype.linearCombination ℝ (screened W v) c)]
  calc
    _ ≤ C * ‖head (Fintype.linearCombination ℝ v c)‖ ^ 2 := hc c
    _ = C * ‖head (Fintype.linearCombination ℝ (screened W v) c)‖ ^ 2 := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hn hC

end RiemannResearch.Analysis.FiniteGramCoercivity
