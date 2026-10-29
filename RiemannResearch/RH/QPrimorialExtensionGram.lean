/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimorialEnergyTransition
import RiemannResearch.Analysis.AdjointConstraintMinimum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Complete-Q observation Gram for actual primorial head extensions

Source: user-provided Minimum Energy Optimizer Research Agenda, 29 October
2026, Section 6 (the physical observation map and Gram formulation).

The observation map below evaluates the new physical sites on the actual
enlarged zero-old-head tangent. Its domain inherits the complete Q inner
product, not a truncated coordinate metric. Dependent observations are
allowed. Feasibility gives an actual Gram multiplier; every such multiplier
recovers the already-defined least-norm extension correction and its exact
energy. No cofinal bound on these energies is proved here.
-/

noncomputable section
namespace RiemannResearch.RH.QPrimorialExtensionGram

open ZetaTwoHilbert QSquarefreeCanonicalFeasibility
open QPrimorialOptimizerCoalescence QPrimorialEnergyTransition
open RiemannResearch.Analysis.AdjointConstraintMinimum

/-- Physical evaluation on the new sites `H+1,...,J`, with Euclidean output. -/
def observationLinear (H J : ℕ) :
    enlargedTangent H J →ₗ[ℝ] EuclideanSpace ℝ (Fin (J - H)) where
  toFun x := WithLp.toLp 2 (fun i => qSequence (x : QHilbert) (H + i.val + 1))
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    funext i
    change qSequenceLinear ((x : QHilbert) + (y : QHilbert)) (H + i.val + 1) =
      qSequenceLinear (x : QHilbert) (H + i.val + 1) +
        qSequenceLinear (y : QHilbert) (H + i.val + 1)
    simp only [map_add, Pi.add_apply]
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    funext i
    change qSequenceLinear (c • (x : QHilbert)) (H + i.val + 1) =
      c * qSequenceLinear (x : QHilbert) (H + i.val + 1)
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]

/-- The finite-dimensional tangent supplies continuity with its complete Q norm. -/
def observation (H J : ℕ) :
    enlargedTangent H J →L[ℝ] EuclideanSpace ℝ (Fin (J - H)) :=
  (observationLinear H J).toContinuousLinearMap

theorem observation_apply (H J : ℕ) (x : enlargedTangent H J)
    (i : Fin (J - H)) :
    (observation H J x).ofLp i = qSequence (x : QHilbert) (H + i.val + 1) := rfl

/-- New physical data remaining after old-head reoptimization. -/
def mismatch (H J : ℕ) : EuclideanSpace ℝ (Fin (J - H)) :=
  WithLp.toLp 2 (fun i => 1 - qSequence (enlargedMinimum H J) (H + i.val + 1))

/-- The already-constructed least-norm extension, as a tangent vector. -/
def correction (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1)) : enlargedTangent H J :=
  ⟨extensionCorrection H J, extensionCorrection_mem H J hHJ hH hJ⟩

theorem correction_observation (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1)) :
    observation H J (correction H J hHJ hH hJ) = mismatch H J := by
  apply WithLp.ofLp_injective 2
  funext i
  change qSequence (extensionCorrection H J) (H + i.val + 1) =
    1 - qSequence (enlargedMinimum H J) (H + i.val + 1)
  exact extensionCorrection_new_head H J _ (by omega) (by have := i.isLt; omega)

/-- Equal new observations identify exactly a zero-full-head difference. -/
theorem sub_mem_tangent_of_observation_eq (H J : ℕ)
    (x y : enlargedTangent H J) (hxy : observation H J x = observation H J y) :
    (x : QHilbert) - (y : QHilbert) ∈ tangent J := by
  refine ⟨Submodule.sub_mem _ x.property.1 y.property.1, ?_⟩
  intro n hn hnJ
  change qSequenceLinear ((x : QHilbert) - (y : QHilbert)) n = 0
  simp only [map_sub, Pi.sub_apply]
  change qSequence (x : QHilbert) n - qSequence (y : QHilbert) n = 0
  by_cases hnH : n ≤ H
  · rw [x.property.2 n hn hnH, y.property.2 n hn hnH, sub_self]
  · let i : Fin (J - H) := ⟨n - H - 1, by omega⟩
    have he := congrArg (fun z : EuclideanSpace ℝ (Fin (J - H)) => z.ofLp i) hxy
    change qSequence (x : QHilbert) (H + i.val + 1) =
      qSequence (y : QHilbert) (H + i.val + 1) at he
    have hi : H + i.val + 1 = n := by dsimp [i]; omega
    rw [hi] at he
    exact sub_eq_zero.mpr he

/-- The physical tangent minimum is also the minimum for this actual map. -/
theorem correction_minimizes_observation (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1))
    (x : enlargedTangent H J) (hx : observation H J x = mismatch H J) :
    ‖correction H J hHJ hH hJ‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have hsame : observation H J x = observation H J (correction H J hHJ hH hJ) :=
    hx.trans (correction_observation H J hHJ hH hJ).symm
  have hd := sub_mem_tangent_of_observation_eq H J x (correction H J hHJ hH hJ) hsame
  have hm := extensionCorrection_minimizes H J hHJ
    ((x : QHilbert) - extensionCorrection H J) hd
  have he : extensionCorrection H J + ((x : QHilbert) - extensionCorrection H J) =
      (x : QHilbert) := by abel
  change ‖extensionCorrection H J‖ ^ 2 ≤ ‖(x : QHilbert)‖ ^ 2
  simpa only [he] using hm

/-- Feasibility discharges Gram-solvability even with dependent head rows. -/
theorem exists_multiplier (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1)) :
    ∃ y : EuclideanSpace ℝ (Fin (J - H)),
      observation H J ((observation H J).adjoint y) = mismatch H J :=
  exists_gram_solution_of_feasible (observation H J) (mismatch H J)
    (correction H J hHJ hH hJ) (correction_observation H J hHJ hH hJ)

/-- Every solved complete-Q Gram system recovers the actual extension vector. -/
theorem correction_eq_adjoint (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1))
    (y : EuclideanSpace ℝ (Fin (J - H)))
    (hy : observation H J ((observation H J).adjoint y) = mismatch H J) :
    correction H J hHJ hH hJ = (observation H J).adjoint y := by
  have hfeas := correction_observation H J hHJ hH hJ
  have hlow := correction_minimizes_observation H J hHJ hH hJ
    ((observation H J).adjoint y) hy
  have hhigh := gram_solution_minimizes (observation H J) (mismatch H J) y hy
    (correction H J hHJ hH hJ) hfeas
  exact (gram_solution_equal_iff (observation H J) (mismatch H J) y hy
    (correction H J hHJ hH hJ) hfeas).mp (le_antisymm hlow hhigh)

theorem extension_energy_of_gram_solution (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1))
    (y : EuclideanSpace ℝ (Fin (J - H)))
    (hy : observation H J ((observation H J).adjoint y) = mismatch H J) :
    ‖extensionCorrection H J‖ ^ 2 = inner ℝ (mismatch H J) y := by
  change ‖correction H J hHJ hH hJ‖ ^ 2 = _
  rw [correction_eq_adjoint H J hHJ hH hJ y hy]
  exact gram_solution_energy (observation H J) (mismatch H J) y hy

/-- Matrix-form signed transition for the actual physical dictionaries. -/
theorem optimizer_transition_of_gram_solution (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1))
    (y : EuclideanSpace ℝ (Fin (J - H)))
    (hy : observation H J ((observation H J).adjoint y) = mismatch H J) :
    ‖qOptimizer J‖ ^ 2 - ‖qOptimizer H‖ ^ 2 =
      inner ℝ (mismatch H J) y - ‖enlargementVector H J‖ ^ 2 := by
  rw [optimizer_energy_transition H J hHJ hH hJ,
    extension_energy_of_gram_solution H J hHJ hH hJ y hy]

end RiemannResearch.RH.QPrimorialExtensionGram
