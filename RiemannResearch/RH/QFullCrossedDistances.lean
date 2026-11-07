/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalDistanceBound
import RiemannResearch.RH.QParetoSquareRootEnergy
import RiemannResearch.RH.QParetoIsometricTransport
import RiemannResearch.RH.QFullIsometricTransport
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullCofinalHarmonic
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Two crossed distances for the actual full-conductor displacement

Source: user-provided Isometric_Transport_Lean_Handoff_2026-11-06.md,
Section 5 and priorities 1--5. This checks the proposed signed identity,
positive two-distance bound, and linear trial-error estimate. The exact
polarization identity also gives a quadratic approximation penalty with
the nonnegative trial energy retained.

The corrected target rootDefect permits explicit legal correction
certificates with complete head-and-tail estimates. It does not provide
those corrections with vanishing errors. Every RH implication below is
a conditional research reduction with its distance, signed cancellation,
or second-inverse membership provider Open.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QFullCrossedDistances
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QShiftedReciprocal
open QParetoIsometricTransport QFullResidueProjection QFullDisplacement
open QFullIsometricTransport QParetoClosedProjectionComparison

def forwardDistance (g : QHilbert) : ℝ :=
  Metric.infDist (A g) (paretoClosure : Set ThresholdHilbert)
def inverseDistance (g : QHilbert) : ℝ :=
  Metric.infDist (toPareto g) (transportedClosure : Set ThresholdHilbert)
def crossedBudget (g : QHilbert) : ℝ :=
  ‖toPareto pResidual‖ * forwardDistance g + ‖qResidual‖ * inverseDistance g
def signedTest (g : QHilbert) : ℝ :=
  inner ℝ (toPareto pResidual) (A g) - inner ℝ qResidual (inversePhysical g)

theorem pResidual_orthogonal : toPareto pResidual ∈ paretoClosureᗮ := by
  rw [pResidual, toPareto_sub, toPareto_pFit]
  exact Submodule.sub_starProjection_mem_orthogonal (K := paretoClosure) (toPareto qOne)

/-- Exact signed identity for every trial, before either residual term is estimated. -/
theorem signedTest_eq (g : QHilbert) :
    signedTest g = inner ℝ displacement (inversePhysical g) := by
  rw [signedTest, toPareto_A_inner, pResidual_eq_residual_add_displacement,
    inner_add_left]
  ring

theorem signedTest_le_budget (g : QHilbert) : signedTest g ≤ crossedBudget g := by
  have hp := paretoClosure.abs_real_inner_le_norm_mul_infDist_of_mem_orthogonal
    pResidual_orthogonal (A g)
  have hq := closure.abs_real_inner_le_norm_mul_infDist_of_mem_orthogonal
    qResidual_mem_orthogonal (inversePhysical g)
  have hd : Metric.infDist (inversePhysical g) (closure : Set QHilbert) =
      inverseDistance g := (infDist_same_sequence_image closure g).symm
  rw [hd] at hq
  change |inner ℝ (toPareto pResidual) (A g)| ≤
    ‖toPareto pResidual‖ * forwardDistance g at hp
  unfold signedTest crossedBudget
  linarith [(le_abs_self (inner ℝ (toPareto pResidual) (A g))),
    (neg_le_abs (inner ℝ qResidual (inversePhysical g)))]

theorem two_distance_bound :
    Real.sqrt (zetaTwo / 2) * ‖displacement‖ ^ 2 ≤ crossedBudget displacement :=
  (inverseEnergy_lower displacement).trans (by
    simpa only [signedTest_eq, inverseEnergy] using signedTest_le_budget displacement)

/-- Quadratic approximation penalty, with the positive trial energy retained. -/
theorem quadratic_two_distance_bound (g : QHilbert) :
    Real.sqrt (zetaTwo / 2) * ‖displacement‖ ^ 2 + inverseEnergy g ≤
      2 * crossedBudget g + Real.sqrt zetaTwo * ‖displacement - g‖ ^ 2 := by
  have h := inverseEnergy_polarization displacement g
  have hl := inverseEnergy_lower displacement
  have hu := inverseEnergy_upper (displacement - g)
  have hb := signedTest_le_budget g
  rw [signedTest_eq] at hb
  linarith

theorem displacement_eq_zero_of_budget_zero (h : crossedBudget displacement = 0) :
    displacement = 0 := by
  have hl := two_distance_bound
  have hm : 0 < Real.sqrt (zetaTwo / 2) := Real.sqrt_pos.mpr (div_pos zetaTwo_pos (by norm_num))
  rw [h] at hl
  have hz : ‖displacement‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖displacement‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

theorem displacement_eq_zero_iff_crossed_membership :
    displacement = 0 ↔
      A displacement ∈ paretoClosure ∧ toPareto displacement ∈ transportedClosure := by
  constructor
  · intro hd
    rw [hd]
    simp only [map_zero, show toPareto (0 : QHilbert) = 0 from toParetoLinear.map_zero]
    exact ⟨paretoClosure.zero_mem, transportedClosure.zero_mem⟩
  · rintro ⟨ha, hb⟩
    apply displacement_eq_zero_of_budget_zero
    simp only [crossedBudget, forwardDistance, inverseDistance,
      Metric.infDist_zero_of_mem ha, Metric.infDist_zero_of_mem hb, mul_zero, add_zero]

theorem forwardDistance_le_trial (g : QHilbert) :
    forwardDistance displacement ≤ forwardDistance g + ‖g - displacement‖ := by
  have h := Metric.infDist_le_infDist_add_dist
    (x := A displacement) (y := A g) (s := (paretoClosure : Set ThresholdHilbert))
  simpa only [forwardDistance, A.dist_map, dist_eq_norm,
    norm_sub_rev displacement g] using h

theorem inverseDistance_le_trial (g : QHilbert) :
    inverseDistance displacement ≤
      inverseDistance g + Real.sqrt zetaTwo * ‖g - displacement‖ := by
  have h := Metric.infDist_le_infDist_add_dist
    (x := toPareto displacement) (y := toPareto g)
    (s := (transportedClosure : Set ThresholdHilbert))
  have hn := toPareto_norm_le (displacement - g)
  rw [toPareto_sub, norm_sub_rev displacement g] at hn
  change inverseDistance displacement ≤ inverseDistance g +
    dist (toPareto displacement) (toPareto g) at h
  rw [dist_eq_norm] at h
  linarith

theorem two_distance_trial_bound (g : QHilbert) :
    Real.sqrt (zetaTwo / 2) * ‖displacement‖ ^ 2 ≤
      ‖toPareto pResidual‖ * (forwardDistance g + ‖g - displacement‖) +
      ‖qResidual‖ * (inverseDistance g +
        Real.sqrt zetaTwo * ‖g - displacement‖) := by
  apply two_distance_bound.trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (forwardDistance_le_trial g) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (inverseDistance_le_trial g) (norm_nonneg _))

theorem continuous_forwardDistance : Continuous forwardDistance :=
  (Metric.continuous_infDist_pt (paretoClosure : Set ThresholdHilbert)).comp A.continuous

theorem continuous_inverseDistance : Continuous inverseDistance :=
  (Metric.continuous_infDist_pt (transportedClosure : Set ThresholdHilbert)).comp
    toParetoCLM.continuous

theorem continuous_crossedBudget : Continuous crossedBudget :=
  (continuous_const.mul continuous_forwardDistance).add
    (continuous_const.mul continuous_inverseDistance)

theorem continuous_signedTest : Continuous signedTest :=
  (continuous_const.inner A.continuous).sub (continuous_const.inner inversePhysical.continuous)

@[simp] theorem crossedBudget_zero : crossedBudget 0 = 0 := by
  simp only [crossedBudget, forwardDistance, inverseDistance, map_zero,
    show toPareto (0 : QHilbert) = 0 from toParetoLinear.map_zero,
    Metric.infDist_zero_of_mem paretoClosure.zero_mem,
    Metric.infDist_zero_of_mem transportedClosure.zero_mem, mul_zero, add_zero]

/-- A weighted combined limit is enough; no individual distance limit is presumed. -/
theorem displacement_eq_zero_iff_budget_tendsto_zero {G : ℕ → QHilbert}
    (hG : Tendsto G atTop (𝓝 displacement)) :
    displacement = 0 ↔ Tendsto (fun M => crossedBudget (G M)) atTop (𝓝 0) := by
  have h := continuous_crossedBudget.continuousAt.tendsto.comp hG
  constructor
  · intro hd
    simpa only [hd, crossedBudget_zero, Function.comp_def] using h
  · intro hz
    exact displacement_eq_zero_of_budget_zero (tendsto_nhds_unique h hz)

/-- Conditional RH reduction: both actual crossed distances still need providers. -/
theorem riemannHypothesis_of_crossed_distance_limits {G : ℕ → QHilbert}
    (hG : Tendsto G atTop (𝓝 displacement))
    (ha : Tendsto (fun M => forwardDistance (G M)) atTop (𝓝 0))
    (hb : Tendsto (fun M => inverseDistance (G M)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_eq_zero
  apply (displacement_eq_zero_iff_budget_tendsto_zero hG).mpr
  have h := (ha.const_mul ‖toPareto pResidual‖).add (hb.const_mul ‖qResidual‖)
  simpa only [mul_zero, add_zero, crossedBudget] using h

/-- Exact signed cancellation suffices without separate bounds on both pairings. -/
theorem displacement_eq_zero_iff_signedTest_tendsto_zero {G : ℕ → QHilbert}
    (hG : Tendsto G atTop (𝓝 displacement)) :
    displacement = 0 ↔ Tendsto (fun M => signedTest (G M)) atTop (𝓝 0) := by
  have h := continuous_signedTest.continuousAt.tendsto.comp hG
  have he : signedTest displacement = inverseEnergy displacement := signedTest_eq displacement
  constructor
  · intro hd
    have hz : signedTest displacement = 0 := by
      rw [he, (inverseEnergy_eq_zero_iff displacement).mpr hd]
    simpa only [hz, Function.comp_def] using h
  · intro hz
    apply (inverseEnergy_eq_zero_iff displacement).mp
    exact he.symm.trans (tendsto_nhds_unique h hz)

/-- Conditional RH reduction retaining cancellation between the two residual pairings. -/
theorem riemannHypothesis_of_signedTest_limit {G : ℕ → QHilbert}
    (hG : Tendsto G atTop (𝓝 displacement))
    (hF : Tendsto (fun M => signedTest (G M)) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_displacement_eq_zero
    ((displacement_eq_zero_iff_signedTest_tendsto_zero hG).mpr hF)

/-- The second inverse application, rather than the first, is the reciprocal criterion. -/
theorem displacement_eq_zero_iff_second_inverse_mem :
    displacement = 0 ↔ inversePhysical (inversePhysical displacement) ∈ closure := by
  constructor
  · intro hd
    rw [hd, map_zero, map_zero]
    exact closure.zero_mem
  · intro h
    apply displacement_eq_zero_iff_reciprocal_mem.mpr
    rw [inversePhysical_square] at h
    have hm : displacement - B displacement ∈ closure :=
      (Submodule.smul_mem_iff closure zetaTwo_pos.ne').mp h
    have hh := closure.sub_mem displacement_mem hm
    have he : displacement - (displacement - B displacement) = B displacement := by abel
    rwa [he] at hh

/-- A target-specific second-step provider suffices; no global invariance is assumed. -/
theorem riemannHypothesis_of_second_inverse_mem
    (h : inversePhysical (inversePhysical displacement) ∈ closure) : RiemannHypothesis :=
  riemannHypothesis_of_displacement_eq_zero
    (displacement_eq_zero_iff_second_inverse_mem.mpr h)

/-- Full-norm error against an explicit legal Pareto correction. -/
theorem forwardDistance_le_rootDefect_trial (g h : QHilbert)
    (hg : g ∈ closure) (hh : h ∈ closure) :
    forwardDistance g ≤ ‖rootDefect g - inversePhysical h‖ := by
  have hm : toPareto ((Real.sqrt zetaTwo)⁻¹ • g + h) ∈ paretoClosure :=
    (toPareto_mem_iff _).mpr
      (closure.add_mem (closure.smul_mem _ hg) hh)
  have hd := Metric.infDist_le_dist_of_mem hm (x := A g)
  have he : A g - toPareto ((Real.sqrt zetaTwo)⁻¹ • g + h) =
      A (rootDefect g - inversePhysical h) := by
    change g - toParetoLinear ((Real.sqrt zetaTwo)⁻¹ • g + h) = _
    rw [map_add, map_smul]
    change g - ((Real.sqrt zetaTwo)⁻¹ • inversePhysical g + inversePhysical h) =
      (g - (Real.sqrt zetaTwo)⁻¹ • inversePhysical g) - inversePhysical h
    abel
  simpa only [forwardDistance, dist_eq_norm, he, A.norm_map] using hd

/-- The other crossed distance is certified against the same corrected target. -/
theorem inverseDistance_le_rootDefect_trial (g k : QHilbert)
    (hg : g ∈ closure) (hk : k ∈ closure) :
    inverseDistance g ≤ Real.sqrt zetaTwo * ‖rootDefect g - k‖ := by
  have hm : A (Real.sqrt zetaTwo • (g - k)) ∈ transportedClosure :=
    ⟨Real.sqrt zetaTwo • (g - k), closure.smul_mem _ (closure.sub_mem hg hk), rfl⟩
  have hd := Metric.infDist_le_dist_of_mem hm (x := toPareto g)
  have he : toPareto g - A (Real.sqrt zetaTwo • (g - k)) =
      A (Real.sqrt zetaTwo • (k - rootDefect g)) := by
    change inversePhysical g - Real.sqrt zetaTwo • (g - k) =
      Real.sqrt zetaTwo • (k - rootDefect g)
    rw [smul_sub, smul_sub, rootDefect_scale]
    abel
  simpa only [inverseDistance, dist_eq_norm, he, A.norm_map, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg zetaTwo), norm_sub_rev k] using hd


/-- A complete head-and-tail certificate with two legal corrections.
The head vector v need not itself be legal. No infinite tail is discarded. -/
theorem two_distance_head_certificate (g v h k : QHilbert) (N : ℕ)
    (hg : g ∈ closure) (hh : h ∈ closure) (hk : k ∈ closure)
    (hhead : ∀ n < N, g n = v n) :
    Real.sqrt (zetaTwo / 2) * ‖displacement‖ ^ 2 + inverseEnergy g ≤
      2 * (‖toPareto pResidual‖ *
          (‖rootDefect v - inversePhysical h‖ + ‖g - v‖ / ((N : ℝ)+2)) +
        ‖qResidual‖ * (Real.sqrt zetaTwo *
          (‖rootDefect v - k‖ + ‖g - v‖ / ((N : ℝ)+2)))) +
      Real.sqrt zetaTwo * ‖displacement - g‖ ^ 2 := by
  have ha := (forwardDistance_le_rootDefect_trial g h hg hh).trans
    (rootDefect_head_trial_bound g v (inversePhysical h) N hhead)
  have hb := (inverseDistance_le_rootDefect_trial g k hg hk).trans
    (mul_le_mul_of_nonneg_left (rootDefect_head_trial_bound g v k N hhead)
      (Real.sqrt_nonneg zetaTwo))
  have hbudget := add_le_add
    (mul_le_mul_of_nonneg_left ha (norm_nonneg (toPareto pResidual)))
    (mul_le_mul_of_nonneg_left hb (norm_nonneg qResidual))
  have hquad := quadratic_two_distance_bound g
  unfold crossedBudget at hquad
  linarith

end RiemannResearch.RH.QFullCrossedDistances
