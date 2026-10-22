/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.RealCofinalLimits
import RiemannResearch.RH.FirstCoordinateEndpoint
import RiemannResearch.RH.ParetoParityOptimizer
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.FiniteDyadicDefect
import RiemannResearch.RH.ResidueProjectionSchur
import RiemannResearch.RH.ThresholdHilbertL1
import RiemannResearch.RH.ParetoL1DualTest
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Complete-Pareto projection overshoot and relative defect bounds

Source: the user's Pareto parity overshoot continuation, 18 October 2026,
Sections 1 and 2, for the statements and proof strategy. No novelty claim is made.
Stage n uses g₂,...,g_(n+1). The complete infinite Pareto norm is retained.
The eventual relative upper estimates remain Open arithmetic hypotheses.
The RH consumer uses the existing project closure implication; the classical
converse in Bagchi (2006), Theorem 1, https://arxiv.org/abs/math/0607733,
is background and is not newly formalized here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative
open ParityOptimizer

/-- The explicit bounded sign test from the recovered publication continuation.
It equals +1 at the first point and even integers, and -1 at other odd integers. -/
def firstPointSignTest : ThresholdHilbert :=
  hilbertOne + (2 : ℝ) • paretoPointHilbert 0 - (4 : ℝ) • residueAtom 0

theorem firstPointSignTest_abs_le_one (k : ℕ) :
    |hilbertSequence firstPointSignTest k| ≤ 1 := by
  change |hilbertSequenceLinear (hilbertOne + (2 : ℝ) • paretoPointHilbert 0 -
    (4 : ℝ) • residueAtom 0) k| ≤ 1
  rw [map_sub, map_add, map_smul, map_smul]
  change |hilbertSequence hilbertOne k + 2 * hilbertSequence (paretoPointHilbert 0) k -
    4 * hilbertSequence (residueAtom 0) k| ≤ 1
  rw [hilbertOne_sequence, hilbertSequence_paretoPoint, residueAtom,
    normalizedResidueHilbert_sequence]
  by_cases hk0 : k = 0
  · subst k; norm_num [zeroAnchor, paretoPointSequence, residueFraction]
  by_cases hk1 : k = 1
  · subst k; norm_num [zeroAnchor, paretoPointSequence, residueFraction]
  rcases Nat.mod_two_eq_zero_or_one k with hm | hm
  all_goals norm_num [zeroAnchor, paretoPointSequence, residueFraction, hk0, hk1, hm]

theorem odd_orthogonal_first_le_negativeMass
    (f : ThresholdHilbert) (ho : inner ℝ f oddIndicator = 0) :
    hilbertSequence f 1 ≤ 2 * hilbertNegativeMass f := by
  have hb := inner_le_l1_of_sequence_abs_le_one f firstPointSignTest
    firstPointSignTest_abs_le_one
  have hz : inner ℝ f (residueAtom 0) = 0 := by
    have hh := ho
    rw [oddIndicator, inner_smul_right] at hh
    linarith
  rw [firstPointSignTest, inner_sub_right, inner_add_right,
    inner_smul_right, inner_smul_right, hz, mul_zero, sub_zero,
    inner_paretoPoint, hilbertGibbsPhysical_eq] at hb
  rw [show paretoWeight 0 = (1 / 2 : ℝ) by norm_num [paretoWeight]] at hb
  change inner ℝ f hilbertOne + 2 * ((1 / 2 : ℝ) * hilbertSequence f 1) ≤
    hilbertL1Norm f at hb
  rw [hilbertNegativeMass_eq]
  linarith

theorem limitResidual_odd_inner :
    inner ℝ limitResidual oddIndicator = 0 := by
  rw [real_inner_comm]
  exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
    (closedSpace.smul_mem 2 (atom_mem_closed 0))

theorem limitOvershoot_lower :
    (1 - Real.sqrt 2 / 2) * limitEnergy ≤ hilbertNegativeMass limitResidual := by
  have hfirst := firstCoordinate_energy_bounds.1
  have hneg := odd_orthogonal_first_le_negativeMass
    limitResidual limitResidual_odd_inner
  linarith

theorem overshoot_tendsto_iff_residual_zero :
    Tendsto (fun n => hilbertNegativeMass (hilbertOne - projection n))
      atTop (𝓝 0) ↔ limitResidual = 0 := by
  have ht : Tendsto (fun n => hilbertNegativeMass (hilbertOne - projection n))
      atTop (𝓝 (hilbertNegativeMass limitResidual)) :=
    hilbertNegativeMass_continuous.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub projection_tendsto)
  constructor
  · intro h
    have hz := tendsto_nhds_unique ht h
    have he := limitOvershoot_lower
    have hc : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hn : 0 ≤ limitEnergy := sq_nonneg _
    apply limitResidual_zero_iff_energy_zero.mpr
    nlinarith
  · intro h
    have hn : hilbertNegativeMass limitResidual = 0 := by
      rw [h]
      have hs : hilbertSequence (0 : ThresholdHilbert) = 0 :=
        hilbertSequenceLinear.map_zero
      simp [hilbertNegativeMass, hs]
    simpa only [hn] using ht

def projectionOvershoot (n : ℕ) : ℝ :=
  hilbertNegativeMass (hilbertOne - projection n)

def limitOvershoot : ℝ := hilbertNegativeMass limitResidual

theorem projectionOvershoot_eq (n : ℕ) :
    projectionOvershoot n =
      (hilbertL1Norm (hilbertOne - projection n) - energy n) / 2 := by
  have hmean : inner ℝ (hilbertOne - projection n) hilbertOne = energy n := by
    change inner ℝ (projectionResidual n) hilbertOne = energy n
    exact projectionResidual_inner_one n
  rw [projectionOvershoot, hilbertNegativeMass_eq, hmean]

theorem limitOvershoot_eq :
    limitOvershoot = (hilbertL1Norm limitResidual - limitEnergy) / 2 := by
  rw [limitOvershoot, hilbertNegativeMass_eq, limitResidual_inner_one]

theorem projectionOvershoot_tendsto :
    Tendsto projectionOvershoot atTop (𝓝 limitOvershoot) :=
  hilbertNegativeMass_continuous.continuousAt.tendsto.comp
    (tendsto_const_nhds.sub projection_tendsto)

theorem projectionResidual_odd_inner (n : ℕ) :
    inner ℝ (hilbertOne - projection (n + 1)) oddIndicator = 0 := by
  have hm : residueAtom 0 ∈ finiteSpace (n + 1) :=
    Submodule.subset_span ⟨⟨0, by omega⟩, rfl⟩
  rw [real_inner_comm]
  exact ((finiteSpace (n + 1)).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal hilbertOne) _
    ((finiteSpace (n + 1)).smul_mem 2 hm)

theorem projectionOvershoot_first_lower (n : ℕ) :
    max (hilbertSequence (hilbertOne - projection (n + 1)) 1) 0 / 2 ≤
      projectionOvershoot (n + 1) := by
  have h := odd_orthogonal_first_le_negativeMass
    (hilbertOne - projection (n + 1)) (projectionResidual_odd_inner n)
  have hn := hilbertNegativeMass_nonneg (hilbertOne - projection (n + 1))
  have hm : max (hilbertSequence (hilbertOne - projection (n + 1)) 1) 0 ≤
      2 * projectionOvershoot (n + 1) :=
    max_le h (by dsimp only [projectionOvershoot]; linarith)
  linarith

theorem limitOvershoot_upper :
    limitOvershoot ≤ (Real.sqrt limitEnergy - limitEnergy) / 2 := by
  have hn : Real.sqrt limitEnergy = ‖limitResidual‖ := by
    change Real.sqrt (‖limitResidual‖ ^ 2) = _
    exact Real.sqrt_sq (norm_nonneg _)
  rw [limitOvershoot_eq, hn]
  linarith [hilbertL1Norm_le_norm limitResidual]

theorem l1Excess_tendsto_zero_iff_residual_zero :
    Tendsto (fun n => hilbertL1Norm (hilbertOne - projection n) - energy n)
      atTop (𝓝 0) ↔ limitResidual = 0 := by
  rw [← overshoot_tendsto_iff_residual_zero]
  constructor
  · intro h
    change Tendsto (fun n => projectionOvershoot n) atTop (𝓝 0)
    simpa only [projectionOvershoot_eq, zero_div] using h.div_const 2
  · intro h
    have hh : (fun n => hilbertL1Norm (hilbertOne - projection n) - energy n) =
        (fun n => 2 * hilbertNegativeMass (hilbertOne - projection n)) := by
      funext n
      rw [← projectionOvershoot, projectionOvershoot_eq]
      ring
    rw [hh]
    simpa using tendsto_const_nhds.mul h

theorem riemannHypothesis_of_projectionOvershoot_tendsto_zero
    (h : Tendsto projectionOvershoot atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (overshoot_tendsto_iff_residual_zero.mp h))

theorem limitResidual_zero_of_relative_overshoot_bound
    (θ : ℝ) (hθ : θ < 1 - Real.sqrt 2 / 2)
    (j : ℕ → ℕ) (hj : Tendsto j atTop atTop)
    (β : ℕ → ℝ) (hβ : Tendsto β atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, projectionOvershoot (j n) ≤ θ * energy n + β n) :
    limitResidual = 0 := by
  have hb := le_of_tendsto_of_tendsto (projectionOvershoot_tendsto.comp hj)
    ((tendsto_const_nhds.mul energy_tendsto).add hβ) hbound
  simp only [add_zero] at hb
  have hl := limitOvershoot_lower
  change (1 - Real.sqrt 2 / 2) * limitEnergy ≤ limitOvershoot at hl
  have hm : ((1 - Real.sqrt 2 / 2) - θ) * limitEnergy ≤ 0 := by linarith
  have hn : limitEnergy ≤ 0 :=
    le_of_not_gt (fun he => (not_lt_of_ge hm) (mul_pos (sub_pos.mpr hθ) he))
  exact limitResidual_zero_iff_energy_zero.mpr (le_antisymm hn (sq_nonneg _))

theorem riemannHypothesis_of_relative_overshoot_bound
    (θ : ℝ) (hθ : θ < 1 - Real.sqrt 2 / 2)
    (j : ℕ → ℕ) (hj : Tendsto j atTop atTop)
    (β : ℕ → ℝ) (hβ : Tendsto β atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, projectionOvershoot (j n) ≤ θ * energy n + β n) :
    RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (limitResidual_zero_of_relative_overshoot_bound θ hθ j hj β hβ hbound))

theorem limitResidual_zero_of_relative_residual_first_bound
    (θ : ℝ) (hθ : θ < 2 - Real.sqrt 2)
    (j : ℕ → ℕ) (hj : Tendsto j atTop atTop)
    (β : ℕ → ℝ) (hβ : Tendsto β atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      hilbertSequence (hilbertOne - projection (j n)) 1 ≤ θ * energy n + β n) :
    limitResidual = 0 := by
  have ht : Tendsto (fun n => hilbertSequence (hilbertOne - projection n) 1)
      atTop (𝓝 (hilbertSequence limitResidual 1)) := by
    simpa only [Function.comp_def, anchoredEvaluationCLM_apply] using
      (anchoredEvaluationCLM 1).continuous.tendsto limitResidual |>.comp
        (tendsto_const_nhds.sub projection_tendsto)
  have hb := le_of_tendsto_of_tendsto (ht.comp hj)
    ((tendsto_const_nhds.mul energy_tendsto).add hβ) hbound
  simp only [add_zero] at hb
  have hl := firstCoordinate_energy_bounds.1
  have hm : ((2 - Real.sqrt 2) - θ) * limitEnergy ≤ 0 := by nlinarith
  have hn : limitEnergy ≤ 0 :=
    le_of_not_gt (fun he => (not_lt_of_ge hm) (mul_pos (sub_pos.mpr hθ) he))
  exact limitResidual_zero_iff_energy_zero.mpr (le_antisymm hn (sq_nonneg _))

open ProjectionSchur

theorem projectionOvershoot_one : projectionOvershoot 1 = 0 := by
  rw [projectionOvershoot, projection_one]
  change hilbertNegativeMass evenIndicator = 0
  unfold hilbertNegativeMass
  have hz (k : ℕ) :
      positiveWeight k * max (-hilbertSequence evenIndicator k) 0 = 0 := by
    rw [max_eq_right (neg_nonpos.mpr (even_sequence_nonneg k)), mul_zero]
  simp only [hz, tsum_zero]

theorem projectionEnergy_one_pos : 0 < energy 1 := by
  rw [energy_one]
  exact evenMass_pos

theorem projectionOvershoot_zero_iff_one_mem :
    Tendsto projectionOvershoot atTop (𝓝 0) ↔ hilbertOne ∈ closedSpace := by
  change Tendsto (fun n => hilbertNegativeMass (hilbertOne - projection n))
    atTop (𝓝 0) ↔ hilbertOne ∈ closedSpace
  exact overshoot_tendsto_iff_residual_zero.trans
    (limitResidual_zero_iff_energy_zero.trans limitEnergy_zero_iff_mem)

/-- The positive-index first coordinate of the actual finite residual. -/
theorem projectionResidual_first_eq_one_sub_projection (n : ℕ) :
    hilbertSequence (projectionResidual n) 1 =
      1 - hilbertSequence (projection n) 1 := by
  change hilbertSequenceLinear (hilbertOne - projection n) 1 = _
  rw [map_sub]
  change hilbertSequence hilbertOne 1 - hilbertSequence (projection n) 1 = _
  rw [hilbertOne_sequence]
  norm_num [zeroAnchor]

/-- The overshoot sum uses the complete infinite Pareto distribution. -/
theorem projectionOvershoot_eq_tsum_positive_projection (n : ℕ) :
    projectionOvershoot n =
      ∑' k, positiveWeight k * max (hilbertSequence (projection n) k - 1) 0 := by
  unfold projectionOvershoot hilbertNegativeMass
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · subst k
    simp [positiveWeight]
  · have he : hilbertSequence hilbertOne k = 1 := by
      rw [hilbertOne_sequence]
      simp [zeroAnchor, hk]
    have hs := congrFun (hilbertSequence_sub hilbertOne (projection n)) k
    simp only [Pi.sub_apply] at hs
    rw [hs, he]
    congr 2
    ring

/-- The critical coefficient is included, by the quadratic first-coordinate
detector. The cofinal upper estimate is an explicit arithmetic hypothesis.
Source: the previously checked Pareto parity publication continuation. -/
theorem projectionOvershoot_cofinal_endpoint_iff_residual_zero :
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      projectionOvershoot n ≤ (1 - Real.sqrt 2 / 2) * energy n + ε) ↔
      limitResidual = 0 := by
  have ht := projectionOvershoot_tendsto.sub
    (energy_tendsto.const_mul (1 - Real.sqrt 2 / 2))
  constructor
  · intro h
    have hb : limitOvershoot - (1 - Real.sqrt 2 / 2) * limitEnergy ≤ 0 := by
      apply RiemannResearch.Analysis.limit_le_of_cofinal_le_add ht
      intro ε hε N
      obtain ⟨n, hn, hb⟩ := h ε hε N
      exact ⟨n, hn, by linarith⟩
    have hx := odd_orthogonal_first_le_negativeMass
      limitResidual limitResidual_odd_inner
    change hilbertSequence limitResidual 1 ≤ 2 * limitOvershoot at hx
    apply limitResidual_zero_of_firstCoordinate_le_sharp_energy
    linarith
  · intro h ε hε N
    have he := limitResidual_zero_iff_energy_zero.mp h
    have ho : limitOvershoot = 0 := by
      unfold limitOvershoot
      rw [h]
      have hs : hilbertSequence (0 : ThresholdHilbert) = 0 :=
        hilbertSequenceLinear.map_zero
      simp [hilbertNegativeMass, hs]
    rw [ho, he, mul_zero, sub_zero] at ht
    obtain ⟨n, hn, hb⟩ :=
      RiemannResearch.Analysis.cofinal_le_add_of_tendsto ht ε hε N
    exact ⟨n, hn, by linarith⟩

theorem riemannHypothesis_of_projectionOvershoot_cofinal_endpoint
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      projectionOvershoot n ≤ (1 - Real.sqrt 2 / 2) * energy n + ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_firstCoordinate_zero
  exact firstCoordinate_zero_iff_residual_zero.mpr
    (projectionOvershoot_cofinal_endpoint_iff_residual_zero.mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization
