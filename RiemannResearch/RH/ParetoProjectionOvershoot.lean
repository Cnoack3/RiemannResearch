/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoParityOptimizer
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.FiniteDyadicDefect
import RiemannResearch.RH.ResidueProjectionSchur
import RiemannResearch.RH.ThresholdHilbertL1
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

theorem odd_orthogonal_first_le_negativeMass
    (f : ThresholdHilbert) (ho : inner ℝ f oddIndicator = 0) :
    hilbertSequence f 1 ≤ 2 * hilbertNegativeMass f := by
  have hs := weighted_summable_of_square (hilbertSequence_square_summable f)
  have hp := weighted_product_summable_of_square
    (hilbertSequence_square_summable f)
    (hilbertSequence_square_summable oddIndicator)
  have hi : Summable (fun k : ℕ => if k = 1 then hilbertSequence f 1 else 0) := by
    apply (summable_nat_add_iff 2).mp
    have he : (fun k : ℕ => if k + 2 = 1 then hilbertSequence f 1 else 0) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext k
      rw [if_neg (by omega)]
    rw [he]
    exact summable_zero
  have hb := Summable.tsum_le_tsum
    (f := fun k => positiveWeight k * hilbertSequence f k -
      2 * (positiveWeight k *
        (hilbertSequence f k * hilbertSequence oddIndicator k)) +
      (if k = 1 then hilbertSequence f 1 else 0))
    (g := fun k => positiveWeight k * |hilbertSequence f k|)
    (fun k => by
      rw [oddIndicator_sequence]
      by_cases hk : k = 1
      · subst k
        rw [if_pos (show (1 : ℕ) = 1 from rfl)]
        simp only [show 1 % 2 = (1 : ℕ) by norm_num, Nat.cast_one, mul_one]
        rw [show positiveWeight 1 = (1 / 2 : ℝ) by norm_num [positiveWeight]]
        linarith [le_abs_self (hilbertSequence f 1)]
      · simp only [if_neg hk, add_zero]
        have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rcases hmod with hmod | hmod
        · rw [hmod]
          simp only [Nat.cast_zero, mul_zero, sub_zero]
          exact mul_le_mul_of_nonneg_left (le_abs_self _)
            (positiveWeight_nonneg k)
        · rw [hmod]
          simp only [Nat.cast_one, mul_one]
          have hh := mul_le_mul_of_nonneg_left
            (neg_le_abs (hilbertSequence f k)) (positiveWeight_nonneg k)
          linarith)
    ((hs.sub (hp.mul_left 2)).add hi) (hilbertL1Norm_summable f)
  rw [(hs.sub (hp.mul_left 2)).tsum_add hi,
    hs.tsum_sub (hp.mul_left 2), tsum_mul_left] at hb
  have hh : (∑' k, positiveWeight k *
      (hilbertSequence f k * hilbertSequence oddIndicator k)) = 0 := by
    simpa only [hilbert_inner_weighted, paretoInner] using ho
  simp only [hh, mul_zero, sub_zero, tsum_ite_eq] at hb
  rw [hilbertNegativeMass_eq, hilbert_inner_one]
  unfold paretoMean hilbertL1Norm
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

end RiemannResearch.RH.Pareto.CoefficientStabilization
