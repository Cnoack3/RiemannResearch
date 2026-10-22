/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ProjectionPairingVariation
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoParityOptimizer
import RiemannResearch.RH.ResidueProjectionSchur
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Absolutely summable signed Pareto Schur innovations

Source: Section 3 of the user's Pareto parity overshoot continuation,
18 October 2026. The signed numerator and positive Schur denominator
are retained. Stage n spans g₂,...,g_(n+1), so the sum from n=1 starts at M=2.
Absolute summability and the complete tail budget are unconditional.
Open: an arithmetic argument forcing the exact signed endpoint to vanish.
No RH conclusion follows here without that explicitly stated hypothesis.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionPairingVariation
open ParityOptimizer ProjectionSchur

def firstCoordinateRiesz : ThresholdHilbert := (2 : ℝ) • paretoPointHilbert 0

theorem inner_firstCoordinateRiesz (f : ThresholdHilbert) :
    inner ℝ f firstCoordinateRiesz = hilbertSequence f 1 := by
  rw [firstCoordinateRiesz, real_inner_smul_right, inner_paretoPoint,
    hilbertGibbsPhysical_eq]
  norm_num [paretoWeight]
  ring

theorem schurEta_eq_residual_pairing (n : ℕ) :
    schurEta n = inner ℝ (hilbertOne - projection n) (residueAtom n) := by
  calc
    _ = inner ℝ (residueAtom n) (hilbertOne - projection n) := by
      unfold schurEta innovation projection
      rw [inner_sub_left, inner_sub_right,
        (finiteSpace n).inner_starProjection_left_eq_right]
    _ = _ := real_inner_comm _ _

def firstInnovation (n : ℕ) : ℝ :=
  schurEta n * hilbertSequence (innovation n) 1 / schurSigma n

theorem firstInnovation_eq_increment (n : ℕ) :
    firstInnovation n =
      hilbertSequence (projection (n + 1)) 1 - hilbertSequence (projection n) 1 := by
  rw [projection_schur_step]
  change firstInnovation n =
    hilbertSequenceLinear (projection n + (schurEta n / schurSigma n) • innovation n) 1 -
      hilbertSequence (projection n) 1
  rw [map_add, map_smul]
  change schurEta n * hilbertSequence (innovation n) 1 / schurSigma n =
    hilbertSequence (projection n) 1 +
      (schurEta n / schurSigma n) * hilbertSequence (innovation n) 1 -
        hilbertSequence (projection n) 1
  ring

theorem firstInnovation_eq_pairing (n : ℕ) :
    firstInnovation n =
      inner ℝ (projection (n + 1) - projection n) firstCoordinateRiesz := by
  rw [inner_firstCoordinateRiesz, hilbertSequence_sub, Pi.sub_apply,
    firstInnovation_eq_increment]

theorem firstInnovation_abs_summable (k : ℕ) :
    Summable (fun n => |firstInnovation (n + k)|) := by
  have hW : Monotone (fun n => finiteSpace (n + k)) :=
    fun i j hij => walkSpan_mono residueAtom id (Nat.add_le_add_right hij k)
  have hs := step_pairing_abs_summable (fun n => finiteSpace (n + k)) hW
    hilbertOne firstCoordinateRiesz
  simp only [Nat.add_right_comm _ 1 k] at hs
  change Summable (fun n =>
    |inner ℝ (projection (n + k + 1) - projection (n + k)) firstCoordinateRiesz|) at hs
  simpa only [← firstInnovation_eq_pairing] using hs

theorem firstInnovation_abs_tsum_le (k : ℕ) :
    (∑' n, |firstInnovation (n + k)|) ≤ Real.sqrt (energy k - limitEnergy) *
      ‖closedSpace.starProjection firstCoordinateRiesz -
        (finiteSpace k).starProjection firstCoordinateRiesz‖ := by
  have hW : Monotone (fun n => finiteSpace (n + k)) :=
    fun i j hij => walkSpan_mono residueAtom id (Nat.add_le_add_right hij k)
  have hx := projection_tendsto.comp (tendsto_add_atTop_nat k)
  have hy := (walkProjection_tendsto residueAtom id Function.surjective_id
    firstCoordinateRiesz).comp (tendsto_add_atTop_nat k)
  have hb := tsum_abs_step_pairing_le (fun n => finiteSpace (n + k)) hW
    hilbertOne firstCoordinateRiesz limitProjection
    (closedSpace.starProjection firstCoordinateRiesz) hx hy
  have he := walkError_eq_limitingError_add residueAtom id firstCoordinateRiesz k
  change ‖firstCoordinateRiesz - (finiteSpace k).starProjection firstCoordinateRiesz‖ ^ 2 =
    ‖firstCoordinateRiesz - closedSpace.starProjection firstCoordinateRiesz‖ ^ 2 +
      ‖closedSpace.starProjection firstCoordinateRiesz -
        (finiteSpace k).starProjection firstCoordinateRiesz‖ ^ 2 at he
  have heq :
      ‖firstCoordinateRiesz - (finiteSpace k).starProjection firstCoordinateRiesz‖ ^ 2 -
        ‖firstCoordinateRiesz - closedSpace.starProjection firstCoordinateRiesz‖ ^ 2 =
      ‖closedSpace.starProjection firstCoordinateRiesz -
        (finiteSpace k).starProjection firstCoordinateRiesz‖ ^ 2 := by linarith
  simp only [Nat.zero_add, Nat.add_right_comm _ 1 k] at hb
  change (∑' n, |inner ℝ
      (projection (n + k + 1) - projection (n + k)) firstCoordinateRiesz|) ≤
    Real.sqrt (energy k - limitEnergy) *
      Real.sqrt (‖firstCoordinateRiesz -
        (finiteSpace k).starProjection firstCoordinateRiesz‖ ^ 2 -
        ‖firstCoordinateRiesz - closedSpace.starProjection firstCoordinateRiesz‖ ^ 2) at hb
  simpa only [← firstInnovation_eq_pairing, heq, Real.sqrt_sq (norm_nonneg _)] using hb

theorem firstInnovation_tsum :
    (∑' n, firstInnovation (n + 1)) = -hilbertSequence limitResidual 1 := by
  have hW : Monotone (fun n => finiteSpace (n + 1)) :=
    fun i j hij => walkSpan_mono residueAtom id (Nat.add_le_add_right hij 1)
  have hs := tsum_step_pairing (fun n => finiteSpace (n + 1)) hW
    hilbertOne firstCoordinateRiesz limitProjection
    (projection_tendsto.comp (tendsto_add_atTop_nat 1))
  change (∑' n, inner ℝ
      (projection (n + 1 + 1) - projection (n + 1)) firstCoordinateRiesz) =
    inner ℝ (limitProjection - projection 1) firstCoordinateRiesz at hs
  simp_rw [← firstInnovation_eq_pairing] at hs
  rw [inner_firstCoordinateRiesz, hilbertSequence_sub, Pi.sub_apply, projection_one] at hs
  have ho : hilbertSequence ((2 : ℝ) • residueAtom 0) 1 = 1 := by
    change hilbertSequence oddIndicator 1 = 1
    rw [oddIndicator_sequence]
    norm_num
  rw [ho] at hs
  have hr : hilbertSequence limitResidual 1 = 1 - hilbertSequence limitProjection 1 := by
    rw [limitResidual, hilbertSequence_sub, Pi.sub_apply, hilbertOne_sequence]
    norm_num [zeroAnchor]
  linarith

theorem firstInnovation_tsum_bounds :
    -(2 + Real.sqrt 2) * limitEnergy ≤ (∑' n, firstInnovation (n + 1)) ∧
      (∑' n, firstInnovation (n + 1)) ≤ -(2 - Real.sqrt 2) * limitEnergy := by
  rw [firstInnovation_tsum]
  constructor <;> nlinarith [firstCoordinate_energy_bounds.1, firstCoordinate_energy_bounds.2]

theorem firstInnovation_tsum_zero_iff :
    (∑' n, firstInnovation (n + 1)) = 0 ↔ limitResidual = 0 := by
  rw [firstInnovation_tsum, neg_eq_zero, firstCoordinate_zero_iff_residual_zero]

theorem riemannHypothesis_of_firstInnovation_tsum_zero
    (h : (∑' n, firstInnovation (n + 1)) = 0) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr (firstInnovation_tsum_zero_iff.mp h))

end RiemannResearch.RH.Pareto.CoefficientStabilization
