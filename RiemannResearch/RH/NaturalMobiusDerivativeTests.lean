/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.NaturalMobiusVariation
import RiemannResearch.NumberTheory.DivisorCountSummability
import RiemannResearch.RH.ResidueDerivativeCompatibility

/-!
# Unconditional signed derivative tests of the explicit Möbius approximants

The raw Möbius residual and the canonical projection residual are different
vectors. PNT and a summable divisor-count majorant prove vanishing against
every bounded physical derivative test for the raw approximants. The exact
comparison identity below retains the full canonical-minus-raw correction.
No vanishing of that correction is assumed or asserted.

Source: the user-directed vanishing attempt, continuing
`CRTPrimitiveTransferAudit20260929.md`, Section 6, and the existing
repository dyadic and arithmetic identities.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

def rawMobiusDerivativeResidual (N : ℕ) : ThresholdHilbert :=
  hilbertDifference (hilbertOne - rawMobiusHilbert N)

/-- The first-site boundary equals the reciprocal Möbius sum exactly. -/
theorem rawMobiusDerivativeResidual_first (N : ℕ) (hN : 0 < N) :
    hilbertSequence (rawMobiusDerivativeResidual N) 1 = mobiusReciprocalSum N := by
  rw [rawMobiusDerivativeResidual, hilbertDifference_sequence]
  simp only [PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift,
    Nat.sub_self, hilbertSequence_zero, sub_zero]
  simpa using rawMobiusResidual_head N 1 (by decide) hN

/-- Away from the first site, the entire truncated signed divisor sum survives. -/
theorem rawMobiusDerivativeResidual_succ (N k : ℕ) (hk : 0 < k) :
    hilbertSequence (rawMobiusDerivativeResidual N) (k + 1) =
      mobiusReciprocalSum N - ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d (k + 1) := by
  simpa only [rawMobiusDerivativeResidual, hilbertDifference_sequence,
    PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift, Nat.add_sub_cancel]
      using rawMobiusResidual_jump N k hk

/-- A single anchored majorant includes zero, the first site, and the full tail. -/
theorem rawMobiusDerivativeResidual_abs_le (N : ℕ) (hN : 0 < N) (k : ℕ) :
    |hilbertSequence (rawMobiusDerivativeResidual N) k| ≤
      1 + (k.divisors.card : ℝ) := by
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero =>
          rw [rawMobiusDerivativeResidual_first N hN]
          exact (mobiusReciprocalSum_abs_le_one N hN).trans
            (le_add_of_nonneg_right (Nat.cast_nonneg _))
      | succ k =>
          simpa only [rawMobiusDerivativeResidual, hilbertDifference_sequence,
            PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift,
            Nat.add_sub_cancel] using
              rawMobiusResidual_jump_abs_le N hN (k + 1) (Nat.succ_pos k)

theorem rawMobiusDerivativeResidual_coordinate_tendsto_zero (k : ℕ) :
    Tendsto (fun N => hilbertSequence (rawMobiusDerivativeResidual N) k)
      atTop (𝓝 0) := by
  simpa only [rawMobiusDerivativeResidual, hilbertDifference_sequence,
    PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift, sub_zero] using
      (rawMobiusResidual_coordinate_tendsto_zero k).sub
        (rawMobiusResidual_coordinate_tendsto_zero (k - 1))

theorem summable_weighted_one_add_divisor_count :
    Summable (fun k : ℕ => positiveWeight k * (1 + (k.divisors.card : ℝ))) := by
  apply (summable_nat_add_iff 1).mp
  apply RiemannResearch.NumberTheory.summable_divisor_count_successor_majorant.of_nonneg_of_le
  · intro k
    exact mul_nonneg (positiveWeight_nonneg _) (by positivity)
  · intro k
    have hd : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
    simp only [positiveWeight, Nat.cast_add, Nat.cast_one]
    rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
    rw [one_div, inv_mul_eq_div]
    apply div_le_div_of_nonneg_right _ hd.le
    linarith

/-- Dominated convergence for the full signed derivative pairing. The test
hypothesis is explicit and is met by every bounded physical sequence. -/
theorem rawMobiusDerivativeResidual_inner_tendsto_of_summable_test
    (f : ThresholdHilbert)
    (hf : Summable (fun k => positiveWeight k *
      (1 + (k.divisors.card : ℝ)) * |hilbertSequence f k|)) :
    Tendsto (fun N => inner ℝ (rawMobiusDerivativeResidual N) f) atTop (𝓝 0) := by
  have hp : ∀ k, Tendsto
      (fun N => positiveWeight k *
        (hilbertSequence (rawMobiusDerivativeResidual N) k * hilbertSequence f k))
      atTop (𝓝 0) := by
    intro k
    simpa using ((rawMobiusDerivativeResidual_coordinate_tendsto_zero k).mul_const
      (hilbertSequence f k)).const_mul (positiveWeight k)
  have hb : ∀ᶠ N : ℕ in atTop, ∀ k,
      ‖positiveWeight k *
        (hilbertSequence (rawMobiusDerivativeResidual N) k * hilbertSequence f k)‖ ≤
      positiveWeight k * (1 + (k.divisors.card : ℝ)) * |hilbertSequence f k| := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (positiveWeight_nonneg k)]
    calc
      _ ≤ positiveWeight k * ((1 + (k.divisors.card : ℝ)) * |hilbertSequence f k|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (rawMobiusDerivativeResidual_abs_le N hN k)
            (abs_nonneg _)) (positiveWeight_nonneg k)
      _ = _ := by ring
  have ht := tendsto_tsum_of_dominated_convergence hf hp hb
  simpa only [hilbert_inner_weighted, paretoInner, tsum_zero] using ht

/-- Every bounded physical test has vanishing raw derivative pairing,
unconditionally. No uniform Hilbert norm bound for the raw residual is used. -/
theorem rawMobiusDerivativeResidual_inner_tendsto_of_bounded
    (f : ThresholdHilbert) (C : ℝ) (hf : ∀ k, |hilbertSequence f k| ≤ C) :
    Tendsto (fun N => inner ℝ (rawMobiusDerivativeResidual N) f) atTop (𝓝 0) := by
  apply rawMobiusDerivativeResidual_inner_tendsto_of_summable_test f
  apply (summable_weighted_one_add_divisor_count.mul_right C).of_nonneg_of_le
  · intro k
    exact mul_nonneg (mul_nonneg (positiveWeight_nonneg _) (by positivity)) (abs_nonneg _)
  · intro k
    exact mul_le_mul_of_nonneg_left (hf k)
      (mul_nonneg (positiveWeight_nonneg _) (by positivity))

namespace CoefficientStabilization.DerivativeCompatibility

theorem derivativeAtom_physical_abs_le_two (i k : ℕ) :
    |hilbertSequence (derivativeAtom i) k| ≤ 2 := by
  rw [derivativeAtom, hilbertDifference_sequence, residueAtom,
    normalizedResidueHilbert_sequence]
  change |residueFraction (i + 2) k - residueFraction (i + 2) (k - 1)| ≤ 2
  calc
    _ ≤ |residueFraction (i + 2) k| + |residueFraction (i + 2) (k - 1)| :=
      abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (residueFraction_abs_le_one _ _ (by omega))
      (residueFraction_abs_le_one _ _ (by omega))
    _ = 2 := by norm_num

/-- The complete signed derivative normal defect of the explicit coefficients
-μ tends to zero for each fixed residue test. This concerns the raw coefficients. -/
theorem rawMobius_fixed_derivative_pairing_tendsto_zero (i : ℕ) :
    Tendsto (fun N => inner ℝ (derivativeAtom i) (rawMobiusDerivativeResidual N))
      atTop (𝓝 0) := by
  simpa only [real_inner_comm] using
    rawMobiusDerivativeResidual_inner_tendsto_of_bounded (derivativeAtom i) 2
      (derivativeAtom_physical_abs_le_two i)

/-- Exact comparison with the legal optimizer. The entire differentiated
canonical-minus-raw correction remains, with its sign unchanged. -/
theorem fixedMismatch_eq_raw_sub_correction (n i N : ℕ) :
    fixedMismatch n i =
      inner ℝ (derivativeAtom i) (rawMobiusDerivativeResidual N) -
      inner ℝ (derivativeAtom i)
        (hilbertDifference (projection n - rawMobiusHilbert N)) := by
  rw [fixedMismatch, derivativeResidual, ← inner_sub_right]
  congr 1
  change hilbertDifference (hilbertOne - projection n) =
    hilbertDifference (hilbertOne - rawMobiusHilbert N) -
      hilbertDifference (projection n - rawMobiusHilbert N)
  rw [← map_sub]
  congr 1
  abel

end CoefficientStabilization.DerivativeCompatibility
end RiemannResearch.RH.Pareto

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
open ArithmeticCumulative GramMobiusCorrection
open RiemannResearch.Analysis.FiniteHilbertGram

private theorem sum_Icc_one_eq_fin_shift (f : ℕ → ℝ) (h1 : f 1 = 0) (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 (n + 1), f d) = ∑ i : Fin n, f (i.val + 2) := by
  induction n with
  | zero => simp [h1]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Fin.sum_univ_castSucc, ih]
      rfl

/-- The raw cutoff n+1 is exactly the negative finite Möbius synthesis. -/
theorem rawMobiusHilbert_eq_neg_mobiusSynthesis (n : ℕ) :
    rawMobiusHilbert (n + 1) = -mobiusSynthesis n := by
  apply hilbertSequence_injective
  rw [rawMobiusHilbert_sequence]
  change _ = hilbertSequenceLinear (-∑ i : Fin n,
    mobiusVector n i • residueAtom i.val)
  rw [map_neg, map_sum]
  simp only [map_smul]
  funext k
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change -(∑ d ∈ Finset.Icc 1 (n + 1),
    (ArithmeticFunction.moebius d : ℝ) * residueFraction d k) =
      -(∑ i : Fin n, mobiusVector n i * hilbertSequence (residueAtom i.val) k)
  simp only [residueAtom, normalizedResidueHilbert_sequence, mobiusVector]
  congr 1
  exact sum_Icc_one_eq_fin_shift
    (fun d => (ArithmeticFunction.moebius d : ℝ) * residueFraction d k)
    (by simp [residueFraction, Nat.mod_one]) n

theorem rawMobiusDerivativeResidual_eq_mobiusResidual (n : ℕ) :
    rawMobiusDerivativeResidual (n + 1) = hilbertDifference (mobiusResidual n) := by
  rw [rawMobiusDerivativeResidual, rawMobiusHilbert_eq_neg_mobiusSynthesis,
    sub_neg_eq_add]
  rfl

theorem derivative_mobius_synthesis (n : ℕ) :
    hilbertDifference (mobiusSynthesis n) =
      Fintype.linearCombination ℝ (derivativeFamily n) (mobiusVector n) := by
  simp only [mobiusSynthesis, map_sum, map_smul,
    Fintype.linearCombination_apply, derivativeFamily, derivativeAtom]

theorem derivative_correction_synthesis (n : ℕ) :
    hilbertDifference (correctionSynthesis n) =
      Fintype.linearCombination ℝ (derivativeFamily n) (correctionVector n) := by
  simp only [correctionSynthesis, map_sum, map_smul,
    Fintype.linearCombination_apply, derivativeFamily, derivativeAtom]

/-- The raw derivative source is the entire signed vector d+Dμ. -/
theorem raw_derivative_source (n : ℕ) :
    cross (derivativeFamily n) (rawMobiusDerivativeResidual (n + 1)) =
      derivativeSource n + (derivativeGram n).mulVec (mobiusVector n) := by
  rw [rawMobiusDerivativeResidual_eq_mobiusResidual, mobiusResidual, map_add,
    hilbertDifference_hilbertOne, derivative_mobius_synthesis,
    derivativeGram, gramMatrix_mulVec]
  funext i
  exact inner_add_right _ _ _

/-- Exact full-matrix comparison with the original inverse-Gram correction. -/
theorem mismatchSource_eq_raw_sub_correction (n : ℕ) :
    mismatchSource n = derivativeSource n +
      (derivativeGram n).mulVec (mobiusVector n) -
      (derivativeGram n).mulVec (correctionVector n) := by
  rw [mismatchSource, correctionVector_eq, Matrix.mulVec_add]
  abel

/-- The same exact comparison expressed through actual Hilbert syntheses. -/
theorem fixedMismatch_eq_raw_sub_correctionSynthesis (n i : ℕ) :
    fixedMismatch n i =
      inner ℝ (derivativeAtom i) (rawMobiusDerivativeResidual (n + 1)) -
      inner ℝ (derivativeAtom i) (hilbertDifference (correctionSynthesis n)) := by
  rw [fixedMismatch_eq_raw_sub_correction n i (n + 1),
    rawMobiusHilbert_eq_neg_mobiusSynthesis, sub_neg_eq_add,
    ← correctionSynthesis_eq]

/-- The raw term vanishes at the legal stage indexing n+1. -/
theorem raw_stage_derivative_pairing_tendsto_zero (i : ℕ) :
    Tendsto (fun n => inner ℝ (derivativeAtom i)
      (rawMobiusDerivativeResidual (n + 1))) atTop (𝓝 0) := by
  exact (rawMobius_fixed_derivative_pairing_tendsto_zero i).comp
    (tendsto_add_atTop_nat 1)

/-- Every fixed row of d+Dμ vanishes. The correction D times the original
inverse-Gram correction remains outside this theorem. -/
theorem raw_derivative_signed_row_tendsto_zero (i : ℕ) :
    Tendsto (fun n => 1 / (2 * ((i + 2 : ℕ) : ℝ)) +
      ∑ j : Fin n, mobiusVector n j *
        inner ℝ (derivativeAtom i) (derivativeAtom j.val)) atTop (𝓝 0) := by
  have he (n : ℕ) :
      inner ℝ (derivativeAtom i) (rawMobiusDerivativeResidual (n + 1)) =
        1 / (2 * ((i + 2 : ℕ) : ℝ)) +
          ∑ j : Fin n, mobiusVector n j *
            inner ℝ (derivativeAtom i) (derivativeAtom j.val) := by
    rw [rawMobiusDerivativeResidual_eq_mobiusResidual, mobiusResidual,
      map_add, hilbertDifference_hilbertOne, derivative_mobius_synthesis,
      inner_add_right, derivativeAtom_inner_target,
      Fintype.linearCombination_apply, inner_sum]
    simp only [real_inner_smul_right, derivativeFamily]
  simpa only [he] using raw_stage_derivative_pairing_tendsto_zero i

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
