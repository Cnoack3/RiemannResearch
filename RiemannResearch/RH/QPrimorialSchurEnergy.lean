/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimorialPrimeCarry
import RiemannResearch.RH.QSquarefreeDisplacementEnergy
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Arithmetic Schur energy and the complete metric gap

Source: user-provided *Squarefree projection displacement and infinite CRT
carries*, 9 November 2026, Sections 11 and 12.2--12.4. The checked four-site
bound from QSquarefreeDisplacementEnergy improves coercivity. Testing the
exact Schur equation on the actual prime component reduces the uniform-test
condition to one scalar energy. Its vanishing is still an open arithmetic
obligation. The gap decomposition retains both nonnegative remainders.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimorialPrimeCarry
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoClosedProjectionComparison QSquarefreePrimorialCofinality
open QSquarefreeDisplacementRigidity QPrimeCarryProjection QPrimorialMatchedDisplacement

theorem schurForm_upper (n : ℕ) (x : QHilbert) :
    schurForm n x x ≤ zetaTwo * ‖x‖ ^ 2 := by
  have he : toPareto (schurLift n x) =
      (paretoCarryStage n)ᗮ.starProjection (toPareto x) := by
    rw [schurLift, toPareto_sub, toPareto_pFit, Submodule.starProjection_orthogonal]
    rfl
  have hn : ‖toPareto (schurLift n x)‖ ≤ ‖toPareto x‖ := by
    rw [he]
    calc
      _ ≤ ‖(paretoCarryStage n)ᗮ.starProjection‖ * ‖toPareto x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖toPareto x‖ := mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le _) (norm_nonneg _)
      _ = _ := one_mul _
  have hn2 : ‖toPareto (schurLift n x)‖ ^ 2 ≤ ‖toPareto x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  simpa only [schurForm, real_inner_self_eq_norm_sq] using
    hn2.trans (toPareto_norm_sq_le x)

/-- The squarefree arithmetic constraint improves the generic constant 1/2
to 30/59 while retaining the complete Pareto carry solve. -/
theorem schurForm_coercive_arithmetic (n : ℕ) {x : QHilbert}
    (hx : x ∈ primeStage n) :
    (30 / 59 : ℝ) * zetaTwo * ‖x‖ ^ 2 ≤ schurForm n x x := by
  have hfit : pFit (paretoCarryStage n) x ∈ carryStage n :=
    pFit_mem _ _ (toPareto_mem_paretoCarryStage_iff n) x
  have ho := Submodule.inner_right_of_mem_orthogonal hx hfit.2
  have ho' : inner ℝ (pFit (paretoCarryStage n) x) x = 0 := by
    rw [real_inner_comm]
    exact ho
  have hnorm : ‖schurLift n x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖pFit (paretoCarryStage n) x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, schurLift, inner_sub_left,
      inner_sub_right, inner_sub_right, ho, ho',
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hlegal : schurLift n x ∈ ZetaTwoOptimizerStage.closure := by
    rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
    exact qSquarefreeCRTSpan.le_topologicalClosure
      (primorialStage_le_squarefreeSpan n (schurLift_mem n hx))
  have hb := QSquarefreeDisplacementEnergy.B_inner_le_four_site_29_59
    (QSquarefreeBoundary.fourSiteFunctional_zero_on_closure hlegal)
  have hmetric := QShiftedReciprocal.pareto_inner_identity (schurLift n x) (schurLift n x)
  simp only [real_inner_self_eq_norm_sq] at hmetric
  have hbZ := mul_le_mul_of_nonneg_left hb zetaTwo_pos.le
  rw [schurForm, real_inner_self_eq_norm_sq]
  have hp := mul_nonneg zetaTwo_pos.le (sq_nonneg ‖pFit (paretoCarryStage n) x‖)
  have hnZ := congrArg (fun t : ℝ => zetaTwo * t) hnorm
  nlinarith only [hmetric, hbZ, hp, hnZ]

/-- One scalar, with the actual canonical prime component as its test. -/
def selfForcing (n : ℕ) : ℝ := schurForcing n (primeComponent n)

theorem selfForcing_exact (n : ℕ) :
    selfForcing n = ‖toPareto (schurLift n (primeComponent n))‖ ^ 2 := by
  have hm : primeComponent n ∈ primeStage n := (primeStage n).starProjection_apply_mem _
  rw [selfForcing, ← schur_equation n hm]
  exact real_inner_self_eq_norm_sq _

theorem selfForcing_bounds (n : ℕ) :
    (30 / 59 : ℝ) * zetaTwo * ‖primeComponent n‖ ^ 2 ≤ selfForcing n ∧
      selfForcing n ≤ zetaTwo * ‖primeComponent n‖ ^ 2 := by
  have hm : primeComponent n ∈ primeStage n := (primeStage n).starProjection_apply_mem _
  rw [selfForcing, ← schur_equation n hm]
  exact ⟨schurForm_coercive_arithmetic n hm, schurForm_upper n _⟩

/-- A single cofinal signed-energy test suffices; no estimate uniform over
all prime test vectors is required. The scalar upper bound remains open. -/
theorem displacement_zero_of_cofinal_selfForcing
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, selfForcing n ≤ ε) :
    displacement = 0 := by
  apply primeDisplacement_eq_zero_iff.mp
  by_contra hne
  have hc : 0 < (30 / 59 : ℝ) * zetaTwo * ‖primeDisplacement‖ ^ 2 := by
    exact mul_pos (mul_pos (by norm_num) zetaTwo_pos) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne))
  have ht := (primeComponent_tendsto.norm.pow 2).const_mul ((30 / 59 : ℝ) * zetaTwo)
  have hh : ((30 / 59 : ℝ) * zetaTwo * ‖primeDisplacement‖ ^ 2) / 2 <
      (30 / 59 : ℝ) * zetaTwo * ‖primeDisplacement‖ ^ 2 := by linarith
  have he := ht.eventually (Ioi_mem_nhds hh)
  obtain ⟨n, hn, hn'⟩ := ((h (((30 / 59 : ℝ) * zetaTwo * ‖primeDisplacement‖ ^ 2) / 2)
    (half_pos hc)).and_eventually he).exists
  exact (not_lt_of_ge ((selfForcing_bounds n).1.trans hn)) hn'

theorem selfForcing_tendsto_zero_iff :
    Tendsto selfForcing atTop (𝓝 0) ↔ displacement = 0 := by
  constructor
  · intro h
    apply displacement_zero_of_cofinal_selfForcing
    intro ε hε
    exact (h.eventually (Iio_mem_nhds hε)).frequently.mono (fun _ h => h.le)
  · intro hd
    have hp := primeDisplacement_eq_zero_iff.mpr hd
    have ht := (primeComponent_tendsto.norm.pow 2).const_mul zetaTwo
    rw [hp, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at ht
    apply squeeze_zero (fun n => ?_) (fun n => (selfForcing_bounds n).2) ht
    rw [selfForcing_exact]
    positivity

theorem displacement_sub_schurLift_mem_carry (n : ℕ) :
    stageDisplacement n - schurLift n (primeComponent n) ∈ carryStage n := by
  have hd : stageDisplacement n - primeComponent n ∈ carryStage n := by
    refine ⟨(primorialStage n).sub_mem (stageDisplacement_mem n)
      (primeStage_le n ((primeStage n).starProjection_apply_mem _)), ?_⟩
    exact Submodule.sub_starProjection_mem_orthogonal _
  have he : stageDisplacement n - schurLift n (primeComponent n) =
      (stageDisplacement n - primeComponent n) +
        pFit (paretoCarryStage n) (primeComponent n) := by
    unfold schurLift
    abel
  rw [he]
  exact (carryStage n).add_mem hd
    (pFit_mem _ _ (toPareto_mem_paretoCarryStage_iff n) _)

/-- Complete gap decomposition after exact carry elimination. Both
nonnegative remainders remain in the equality. -/
theorem metricGap_schur_exact (n : ℕ) :
    metricGap n = selfForcing n +
      ‖toPareto (stageDisplacement n - schurLift n (primeComponent n))‖ ^ 2 +
      QParetoMetric.metricCorrection (qOne - primorialOptimizer n) := by
  let s := schurLift n (primeComponent n)
  let k := stageDisplacement n - s
  have hk : k ∈ carryStage n := displacement_sub_schurLift_mem_carry n
  have ho : inner ℝ (toPareto k) (toPareto s) = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      ((toPareto_mem_paretoCarryStage_iff n k).mpr hk) (schurLift_orthogonal n _)
  have ho' : inner ℝ (toPareto s) (toPareto k) = 0 := by
    rw [real_inner_comm]
    exact ho
  have he : toPareto (stageDisplacement n) = toPareto s + toPareto k := by
    change toParetoLinear (stageDisplacement n) = toParetoLinear s + toParetoLinear k
    rw [← map_add]
    congr 1
    dsimp [k]
    abel
  have hn : ‖toPareto (stageDisplacement n)‖ ^ 2 =
      ‖toPareto s‖ ^ 2 + ‖toPareto k‖ ^ 2 := by
    rw [he, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      inner_add_right, ho, ho', real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  rw [metricGap_exact, hn, selfForcing_exact]


/-- Conditional RH consumer. Cofinal smallness of this scalar is Open. -/
theorem riemannHypothesis_of_cofinal_selfForcing
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, selfForcing n ≤ ε) :
    RiemannHypothesis := by
  have hd := displacement_zero_of_cofinal_selfForcing h
  apply riemannHypothesis_of_displacement_bounded 0
  intro k
  rw [hd]
  cases k <;> simp [qSequence]

end RiemannResearch.RH.QPrimorialPrimeCarry
