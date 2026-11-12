/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimorialResolvent
import RiemannResearch.RH.QPrimorialSchurEnergy
import RiemannResearch.RH.QPrimorialResidualCertificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Q-only forcing certificates for canonical primorial Schur energies

Source: user-requested investigation of the canonical primorial Schur
iteration, 11 November 2026. Completion of the square gives an upper
bound for the actual energy using only the Q projection and the bounded
reciprocal multiplier. The equality retains the carry energy, a complete
Q square, and the arithmetic reciprocal gap. The new bound can be
combined with either existing iterative endpoint.

Finite certificates do not supply cofinal decay. The RH consumer below
is explicitly conditional on decay of the Q-only correction.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimorialSchurForcing
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QSquarefreePrimorialCofinality QPrimorialMatchedDisplacement
open QPrimorialResolvent QPrimorialPrimeCarry QShiftedReciprocal
open QParetoClosedProjectionComparison

/-- Exact complete Gram forcing: no Pareto inverse solve is used. -/
theorem correction_pairing (n : ℕ) {v : QHilbert} (hv : v ∈ primorialStage n) :
    zetaTwo * inner ℝ v (correction n) =
      inner ℝ (toPareto v) (toPareto (primorialOptimizer n)) -
        inner ℝ (toPareto v) (toPareto qOne) := by
  have hp := Submodule.inner_right_of_mem_orthogonal hv
    (Submodule.sub_starProjection_mem_orthogonal (K := primorialStage n)
      (B (qOne - primorialOptimizer n)))
  change inner ℝ v (B (qOne - primorialOptimizer n) - correction n) = 0 at hp
  rw [inner_sub_right] at hp
  have hq := Submodule.inner_right_of_mem_orthogonal hv
    (Submodule.sub_starProjection_mem_orthogonal (K := primorialStage n) qOne)
  change inner ℝ v (qOne - primorialOptimizer n) = 0 at hq
  have hm := pareto_inner_identity v (qOne - primorialOptimizer n)
  rw [toPareto_sub, inner_sub_right, hq, zero_sub] at hm
  rw [sub_eq_zero.mp hp] at hm
  linarith

theorem displacement_pareto_energy (n : ℕ) :
    ‖toPareto (stageDisplacement n)‖ ^ 2 =
      zetaTwo * inner ℝ (stageDisplacement n) (correction n) := by
  have ho := Submodule.inner_right_of_mem_orthogonal (stageDisplacement_mem n)
    (Submodule.sub_starProjection_mem_orthogonal (K := primorialStage n)
      (B (stageDisplacement n)))
  rw [inner_sub_right] at ho
  have he := congrArg (fun z : QHilbert => inner ℝ (stageDisplacement n) z)
    (displacement_fixed_point n)
  rw [inner_add_right, real_inner_self_eq_norm_sq] at he
  have hm := pareto_inner_identity (stageDisplacement n) (stageDisplacement n)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hm
  rw [hm]
  congr 1
  linarith only [ho, he]

theorem displacement_schur_energy (n : ℕ) :
    ‖toPareto (stageDisplacement n)‖ ^ 2 = selfForcing n +
      ‖toPareto (stageDisplacement n - schurLift n (primeComponent n))‖ ^ 2 := by
  have h1 := metricGap_exact n
  have h2 := metricGap_schur_exact n
  linarith

theorem displacement_reciprocal_gap_nonneg (n : ℕ) :
    0 ≤ (983 / 2000 : ℝ) * ‖stageDisplacement n‖ ^ 2 -
      inner ℝ (stageDisplacement n) (B (stageDisplacement n)) := by
  apply sub_nonneg.mpr
  apply QSquarefreeDisplacementEnergy.B_inner_le_four_site_983_2000
  apply QSquarefreeBoundary.fourSiteFunctional_zero_on_closure
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact qSquarefreeCRTSpan.le_topologicalClosure
    (primorialStage_le_squarefreeSpan n (stageDisplacement_mem n))

def forcingUpper (n : ℕ) : ℝ :=
  (2000 / 1017 : ℝ) * zetaTwo * ‖correction n‖ ^ 2

theorem forcingUpper_exact (n : ℕ) :
    forcingUpper n = selfForcing n +
      ‖toPareto (stageDisplacement n - schurLift n (primeComponent n))‖ ^ 2 +
      (2000 / 1017 : ℝ) * zetaTwo *
        ‖correction n - (1017 / 2000 : ℝ) • stageDisplacement n‖ ^ 2 +
      zetaTwo * ((983 / 2000 : ℝ) * ‖stageDisplacement n‖ ^ 2 -
        inner ℝ (stageDisplacement n) (B (stageDisplacement n))) := by
  have he := displacement_pareto_energy n
  have hs := displacement_schur_energy n
  have hm := pareto_inner_identity (stageDisplacement n) (stageDisplacement n)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hm
  unfold forcingUpper
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1017 / 2000),
    real_inner_smul_right]
  rw [real_inner_comm (correction n) (stageDisplacement n)] at he
  nlinarith only [he, hs, hm]

theorem selfForcing_le_forcingUpper (n : ℕ) :
    selfForcing n ≤ forcingUpper n := by
  rw [forcingUpper_exact]
  have h1 := sq_nonneg ‖toPareto (stageDisplacement n -
    schurLift n (primeComponent n))‖
  have h2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000 / 1017)
    zetaTwo_pos.le) (sq_nonneg ‖correction n -
      (1017 / 2000 : ℝ) • stageDisplacement n‖)
  have h3 := mul_nonneg zetaTwo_pos.le (displacement_reciprocal_gap_nonneg n)
  linarith


/-- The Q-only forcing gives a direct finite bound for the limiting error. -/
theorem limiting_pError_cube_le_forcing (n : ℕ) :
    (‖toPareto QSquarefreeDisplacementRigidity.pResidual‖ ^ 2)^3 ≤
      max ((8 / ((n : ℝ) + 3))^3)
        ((128000 / 1017 : ℝ) * forcingUpper n) :=
  QPrimorialResidualCertificate.limiting_pError_cube_le_upper n _
    (selfForcing_le_forcingUpper n)

/-- Take the best of the forcing certificate and both iterative certificates. -/
theorem three_upper_certified (n k : ℕ) :
    selfForcing n ≤ min (forcingUpper n)
      (min (QPrimorialSchurEndpoints.upper n (k + 1))
        (QPrimorialSchurEndpoints.posteriorUpper n k)) :=
  le_min (selfForcing_le_forcingUpper n)
    (QPrimorialSchurEndpoints.min_upper_certified n k)

/-- This remains a conditional arithmetic reduction: no decay provider is proved. -/
theorem riemannHypothesis_of_correction_tendsto_zero
    (h : Tendsto correction atTop (𝓝 0)) : RiemannHypothesis := by
  have ht := (h.norm.pow 2).const_mul ((2000 / 1017 : ℝ) * zetaTwo)
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at ht
  apply riemannHypothesis_of_cofinal_selfForcing
  intro ε hε
  exact (ht.eventually (Iio_mem_nhds hε)).frequently.mono fun n hn =>
    (selfForcing_le_forcingUpper n).trans hn.le

/-- The signed cross term is indispensable in comparing two prime-admission stages. -/
theorem selfForcing_transition_exact (n m : ℕ) :
    selfForcing m = selfForcing n +
      2 * inner ℝ (toPareto (schurLift n (primeComponent n)))
        (toPareto (schurLift m (primeComponent m)) -
          toPareto (schurLift n (primeComponent n))) +
      ‖toPareto (schurLift m (primeComponent m)) -
        toPareto (schurLift n (primeComponent n))‖ ^ 2 := by
  rw [selfForcing_exact, selfForcing_exact, inner_sub_right,
    norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_comm
      (toPareto (schurLift m (primeComponent m)))
      (toPareto (schurLift n (primeComponent n)))]
  ring

end RiemannResearch.RH.QPrimorialSchurForcing
