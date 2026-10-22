/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.RawMobiusFiniteWindowEnergy
import RiemannResearch.RH.NaturalMobiusResidualEscape

/-!
# A cofinal finite arithmetic budget suffices for RH

The finite-window budget is an explicit OPEN hypothesis. This module proves
the indexing bridge and the resulting conditional criterion, without asserting
that the budget is bounded. The energy localization itself is unconditional.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
namespace CoefficientStabilization.GramMobiusCorrection
open RiemannResearch.RH.ArithmeticCumulative

private theorem sum_Icc_one_eq_sum_Fin_shift (f : ℕ → ℝ)
    (hf : f 1 = 0) (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 (n+1), f d) = ∑ j : Fin n, f (j.val+2) := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => f (j+2))]
  induction n with
  | zero => simp [hf]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- The matrix-indexed natural residual and the physical raw residual coincide. -/
theorem naturalResidual_eq_rawMobiusResidual (n : ℕ) :
    naturalResidual n = hilbertOne - rawMobiusHilbert (n+1) := by
  apply hilbertSequence_injective
  funext k
  by_cases hk0 : k = 0
  · simp [hk0]
  rw [rawMobiusResidual_sequence (n+1) k (Nat.pos_of_ne_zero hk0)]
  change (hilbertSequenceLinear (naturalResidual n)) k = _
  simp only [naturalResidual, map_add, map_sum, map_smul,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change hilbertSequence hilbertOne k +
    (∑ j : Fin n, (mobiusVector n j) * hilbertSequence (residueAtom j.val) k) = _
  simp only [residueAtom, normalizedResidueHilbert_sequence, mobiusVector]
  rw [hilbertOne_sequence]
  simp only [zeroAnchor, if_neg hk0]
  congr 1
  exact (sum_Icc_one_eq_sum_Fin_shift
    (fun d => (ArithmeticFunction.moebius d : ℝ) * residueFraction d k)
    (by simp [residueFraction, Nat.mod_one]) n).symm

/-- The finite arithmetic budget must carry the actual nonvanishing residual
    pairing through the shrinking complete dual-projection error. -/
theorem residual_dual_error_le_raw_square_window (n : ℕ) :
    limitEnergy^2 ≤
      (((n+1 : ℕ) : ℝ)*(mobiusReciprocalSum (n+1))^2 +
        rawMobiusMiddleEnergy (n+1) ((n+1)^2) + 1) *
      ‖limitResidual-dualCoordinateProjection limitResidual n‖^2 := by
  have he := rawMobius_energy_le_square_window (n+1) (Nat.succ_pos n)
  have hb := naturalResidual_dual_error_bound n
  rw [naturalResidual_eq_rawMobiusResidual] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right he (sq_nonneg _))

/-- All coordinates beyond the square cutoff have a uniform total energy bound.
    The remaining finite arithmetic bound is the explicit missing hypothesis. -/
theorem riemannHypothesis_of_frequently_bounded_raw_square_window
    (C : ℝ)
    (hbudget : ∃ᶠ n : ℕ in atTop,
      ((n+1 : ℕ) : ℝ)*(mobiusReciprocalSum (n+1))^2 +
        rawMobiusMiddleEnergy (n+1) ((n+1)^2) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_bounded_naturalResidual (|C|+2)
  apply hbudget.mono
  intro n hn
  have he := rawMobius_energy_le_square_window (n+1) (Nat.succ_pos n)
  rw [naturalResidual_eq_rawMobiusResidual]
  have h1 := le_abs_self C
  have h2 := abs_nonneg C
  nlinarith [sq_nonneg (‖hilbertOne-rawMobiusHilbert (n+1)‖-1)]

end CoefficientStabilization.GramMobiusCorrection
end RiemannResearch.RH.Pareto
