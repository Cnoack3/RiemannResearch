/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QTriangularCharge
import RiemannResearch.RH.MobiusTriangularCharge
import RiemannResearch.RH.MobiusPrimitiveCharge
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.Analysis.FiniteWeightedVariance
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The arithmetic target of triangular charge

Source: Section 7 of BalazardTriangularResearch20261019.md, based on
Michel Balazard, arXiv:1812.04309, Propositions 6--7. The finite Abel
evaluation and Cesaro variance are elementary identities.
The target charge is evaluated without any RH or closure assumption.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto
theorem reciprocalChargeRiesz_inner_one (N : ℕ) :
    inner ℝ (reciprocalChargeRiesz N) hilbertOne = mobiusReciprocalSum N := by
  rw [reciprocalChargeRiesz_inner]
  unfold mobiusReciprocalSum
  apply Finset.sum_congr rfl
  intro m hm
  rw [mobius_coordinate_one m (Finset.mem_Icc.mp hm).1]
def reciprocalMobiusCesaroMean (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, mobiusReciprocalSum j
def reciprocalMobiusCesaroVariance (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, (mobiusReciprocalSum j - reciprocalMobiusCesaroMean N) ^ 2
theorem triangularChargeRiesz_inner_one (N : ℕ) :
    inner ℝ (triangularChargeRiesz N) hilbertOne = reciprocalMobiusCesaroMean N := by
  rw [triangularChargeRiesz, real_inner_smul_left, sum_inner]
  simp_rw [reciprocalChargeRiesz_inner_one]
  rfl
theorem reciprocalMobiusCesaroEnergy_eq_mean_sq_add_variance (N : ℕ) :
    reciprocalMobiusCesaroEnergy N =
      reciprocalMobiusCesaroMean N ^ 2 + reciprocalMobiusCesaroVariance N := by
  by_cases hz : N = 0
  · simp [hz, reciprocalMobiusCesaroEnergy, reciprocalMobiusCesaroMean,
      reciprocalMobiusCesaroVariance]
  · have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hz
    have ht := RiemannResearch.Analysis.FiniteWeightedVariance.translation_energy
      (Finset.range N) (fun _ => (1 : ℝ)) mobiusReciprocalSum 0
      (by simpa [RiemannResearch.Analysis.FiniteWeightedVariance.mass] using hN)
    have hmean :
        RiemannResearch.Analysis.FiniteWeightedVariance.mean
          (Finset.range N) (fun _ => (1 : ℝ)) mobiusReciprocalSum =
        reciprocalMobiusCesaroMean N := by
      simp [RiemannResearch.Analysis.FiniteWeightedVariance.mean,
        RiemannResearch.Analysis.FiniteWeightedVariance.mass,
        reciprocalMobiusCesaroMean, div_eq_mul_inv,
        mul_comm]
    rw [RiemannResearch.Analysis.FiniteWeightedVariance.variance, hmean] at ht
    simp only [add_zero, one_mul] at ht
    simp only [RiemannResearch.Analysis.FiniteWeightedVariance.mass,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at ht
    have hh := congrArg (fun x : ℝ => (N : ℝ)⁻¹ * x) ht
    unfold reciprocalMobiusCesaroEnergy reciprocalMobiusCesaroVariance
    rw [mul_add] at hh
    field_simp [hN] at hh ⊢
    nlinarith only [hh]
theorem reciprocalMobiusCesaroMean_sq_le (N : ℕ) :
    reciprocalMobiusCesaroMean N ^ 2 ≤ reciprocalMobiusCesaroEnergy N := by
  rw [reciprocalMobiusCesaroEnergy_eq_mean_sq_add_variance]
  have hv : 0 ≤ reciprocalMobiusCesaroVariance N := by
    unfold reciprocalMobiusCesaroVariance
    positivity
  linarith

theorem reciprocalMobiusCesaroMean_abel (N : ℕ) :
    reciprocalMobiusCesaroMean N = mobiusReciprocalSum N -
      (∑ m ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius m : ℝ)) / (N : ℝ) := by
  rw [← triangularChargeRiesz_inner_one, triangularChargeRiesz_eq_sub, inner_sub_left,
    reciprocalChargeRiesz_inner_one, primitiveChargeRiesz_inner]
  congr 2
  apply Finset.sum_congr rfl
  intro m hm
  exact mobius_coordinate_one m (Finset.mem_Icc.mp hm).1

theorem reciprocalMobiusCesaroVariance_nonneg (N : ℕ) :
    0 ≤ reciprocalMobiusCesaroVariance N := by
  unfold reciprocalMobiusCesaroVariance
  positivity

/-- This limit uses the existing unconditional PNT-based reciprocal cancellation. -/
theorem reciprocalMobiusCesaroMean_tendsto_zero :
    Tendsto reciprocalMobiusCesaroMean atTop (𝓝 0) := by
  exact mobiusReciprocalSum_tendsto_zero.cesaro

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer

/-- Exact target charge in the actual Q geometry. -/
theorem charge_qOne (N : ℕ) :
    charge N qOne = reciprocalMobiusCesaroMean N := by
  rw [charge, toPareto_qOne, triangularChargeRiesz_inner_one]

end RiemannResearch.RH.QTriangularCharge
