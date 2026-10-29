/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QConductorGapEnergy
import RiemannResearch.RH.MobiusReciprocalNonvanishing

/-!
# Finite Möbius heads impose a maximum delay on every bounded repair block

Source: the user's symbolic CRT continuation, 28 October 2026. The elementary
nonvanishing arithmetic is reused from MobiusReciprocalNonvanishing. All new
conductors and all coefficient signs are arbitrary. Squarefree repair blocks
are included as a special case; no convergence or RH hypothesis is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QMobiusDelayedBlock
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QResidueHeadSpace
open QConductorGapEnergy

def mobiusBase (H : ℕ) : QHilbert :=
  -(∑ d ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius d : ℝ) • qResidue d)

theorem mobiusBase_sequence (H n : ℕ) :
    qSequence (mobiusBase H) n =
      -(∑ d ∈ Finset.Icc 1 H,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) := by
  change qSequenceLinear (-(∑ d ∈ Finset.Icc 1 H,
    (ArithmeticFunction.moebius d : ℝ) • qResidue d)) n = _
  rw [map_neg]
  change -(qSequence (∑ d ∈ Finset.Icc 1 H,
    (ArithmeticFunction.moebius d : ℝ) • qResidue d) n) = _
  rw [synthesis_sequence]

/-- The entire forced prefix of any delayed block is a truncated divisor sum. -/
theorem block_prefix (H M : ℕ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hgap : ∀ d ∈ s, M < d)
    (hslope : (∑ d ∈ s, c d / (d : ℝ)) = Pareto.mobiusReciprocalSum H)
    (n : ℕ) (hnM : n ≤ M) :
    qSequence (mobiusBase H + ∑ d ∈ s, c d • qResidue d) n =
      ∑ d ∈ Finset.Icc 1 H,
        (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
  have he : (∑ d ∈ Finset.Icc 1 H,
      (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) =
      (n : ℝ) * Pareto.mobiusReciprocalSum H -
        ∑ d ∈ Finset.Icc 1 H,
          (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 H,
          ((n : ℝ) * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) -
            (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Pareto.residueFraction_eq_div_sub_floor d n (Finset.mem_Icc.mp hd).1]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
  change qSequenceLinear (mobiusBase H + ∑ d ∈ s, c d • qResidue d) n = _
  simp only [map_add, Pi.add_apply]
  change qSequence (mobiusBase H) n +
    qSequence (∑ d ∈ s, c d • qResidue d) n = _
  rw [mobiusBase_sequence, block_sequence_below_gap s c M n hgap hnM, hslope, he]
  ring

/-- Every such block is a genuine constant-head interpolant. -/
theorem block_exact_head (H M : ℕ) (hHM : H ≤ M) (s : Finset ℕ) (c : ℕ → ℝ)
    (hgap : ∀ d ∈ s, M < d)
    (hslope : (∑ d ∈ s, c d / (d : ℝ)) = Pareto.mobiusReciprocalSum H)
    (n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (mobiusBase H + ∑ d ∈ s, c d • qResidue d) n = 1 := by
  rw [block_prefix H M s c hgap hslope n (hnH.trans hHM)]
  exact Pareto.finite_mobius_floor_sum H n hn hnH

/-- Every complete-energy ceiling permits only an explicitly bounded delay.
The denominator is nonzero by the existing unconditional Bertrand argument. -/
theorem delay_le_of_norm_le (H : ℕ) (hH : 0 < H) (M : ℕ)
    (s : Finset ℕ) (c : ℕ → ℝ) (hgap : ∀ d ∈ s, M < d)
    (hslope : (∑ d ∈ s, c d / (d : ℝ)) = Pareto.mobiusReciprocalSum H)
    (C : ℝ) (hC : ‖mobiusBase H + ∑ d ∈ s, c d • qResidue d‖ ≤ C) :
    (M : ℝ) ≤ zetaTwo * (C + ‖mobiusBase H‖) ^ 2 /
      (Pareto.mobiusReciprocalSum H) ^ 2 := by
  have h := block_gap_budget (mobiusBase H) s c M hgap ‖mobiusBase H‖ C le_rfl hC
  rw [hslope] at h
  exact (le_div_iff₀ (sq_pos_of_ne_zero (Pareto.mobiusReciprocalSum_ne_zero hH))).mpr h

/-- Crossing that delay threshold forces energy above the prescribed ceiling,
for every signed repair block, with no coefficient-size premise. -/
theorem norm_gt_of_delay_gt (H : ℕ) (hH : 0 < H) (M : ℕ)
    (s : Finset ℕ) (c : ℕ → ℝ) (hgap : ∀ d ∈ s, M < d)
    (hslope : (∑ d ∈ s, c d / (d : ℝ)) = Pareto.mobiusReciprocalSum H)
    (C : ℝ) (hM : zetaTwo * (C + ‖mobiusBase H‖) ^ 2 /
      (Pareto.mobiusReciprocalSum H) ^ 2 < (M : ℝ)) :
    C < ‖mobiusBase H + ∑ d ∈ s, c d • qResidue d‖ := by
  by_contra h
  have hb := delay_le_of_norm_le H hH M s c hgap hslope C (le_of_not_gt h)
  exact (not_lt_of_ge hb) hM

end RiemannResearch.RH.QMobiusDelayedBlock
