/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ThresholdHilbertL1
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ParetoHeadMeanEnergy
import RiemannResearch.RH.ParetoHilbertPhysical
import RiemannResearch.RH.ParetoGibbsTailBasis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite negative-mass sums and their complete Pareto tails

Source: the user-directed attempt to prove the arithmetic overshoot estimate,
19 October 2026. The negative-part vector is elementary; the exact head/tail
split reuses the existing Pareto head and tail vectors. Cauchy--Schwarz controls
the entire omitted mass uniformly by the full norm. These results do not
establish a signed arithmetic estimate for any optimizer.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
set_option backward.isDefEq.respectTransparency false

/-- The full physical negative part, as an actual Hilbert vector. -/
def hilbertNegativePart (f : ThresholdHilbert) : ThresholdHilbert :=
  (1 / 2 : ℝ) • (hilbertAbs f - f)

theorem hilbertNegativePart_sequence (f : ThresholdHilbert) (k : ℕ) :
    hilbertSequence (hilbertNegativePart f) k = max (-hilbertSequence f k) 0 := by
  change hilbertSequenceLinear ((1 / 2 : ℝ) • (hilbertAbs f - f)) k = _
  rw [map_smul, map_sub]
  change (1 / 2 : ℝ) * (hilbertSequence (hilbertAbs f) k - hilbertSequence f k) = _
  rw [hilbertAbs_sequence]
  change (1 / 2 : ℝ) * (|hilbertSequence f k| - hilbertSequence f k) = _
  by_cases hx : 0 ≤ hilbertSequence f k
  · rw [abs_of_nonneg hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · have hx' : hilbertSequence f k ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

theorem hilbertNegativePart_norm_le (f : ThresholdHilbert) :
    ‖hilbertNegativePart f‖ ≤ ‖f‖ := by
  rw [hilbertNegativePart, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h := norm_sub_le (hilbertAbs f) f
  rw [hilbertAbs_norm] at h
  linarith

theorem hilbertNegativePart_inner_one (f : ThresholdHilbert) :
    inner ℝ (hilbertNegativePart f) hilbertOne = hilbertNegativeMass f := by
  rw [hilbert_inner_one]
  unfold paretoMean hilbertNegativeMass
  simp only [hilbertNegativePart_sequence]

/-- The literal first N physical sites of the complete negative mass. -/
def negativeMassHead (N : ℕ) (f : ThresholdHilbert) : ℝ :=
  paretoHeadMean N (hilbertNegativePart f)

theorem negativeMassHead_eq_sum (N : ℕ) (f : ThresholdHilbert) :
    negativeMassHead N f =
      ∑ k ∈ Finset.range N, paretoWeight k * max (-hilbertSequence f (k + 1)) 0 := by
  unfold negativeMassHead paretoHeadMean
  simp only [hilbertGibbsPhysical_eq, hilbertNegativePart_sequence]

/-- Exact split; the entire tail pairing is retained. -/
theorem negativeMassHead_tail_identity (N : ℕ) (f : ThresholdHilbert) :
    hilbertNegativeMass f = negativeMassHead N f +
      inner ℝ (hilbertNegativePart f) (paretoTail N) := by
  rw [paretoTail_inner, hilbertNegativePart_inner_one]
  unfold negativeMassHead
  ring

private theorem negativePart_tail_inner_nonneg (N : ℕ) (f : ThresholdHilbert) :
    0 ≤ inner ℝ (hilbertNegativePart f) (paretoTail N) := by
  rw [hilbert_inner_weighted]
  unfold paretoInner
  apply tsum_nonneg
  intro k
  cases k with
  | zero => simp [positiveWeight]
  | succ k =>
    have ht := paretoTail_physical N k
    rw [hilbertGibbsPhysical_eq] at ht
    rw [hilbertNegativePart_sequence, ht]
    have hw := positiveWeight_nonneg (k + 1)
    have hm := le_max_right (-hilbertSequence f (k + 1)) (0 : ℝ)
    split_ifs <;> positivity

theorem negativeMassHead_le (N : ℕ) (f : ThresholdHilbert) :
    negativeMassHead N f ≤ hilbertNegativeMass f := by
  linarith [negativeMassHead_tail_identity N f, negativePart_tail_inner_nonneg N f]

/-- Uniform tail control from the complete norm and the exact Pareto tail mass. -/
theorem negativeMassHead_truncation_upper (N : ℕ) (f : ThresholdHilbert) :
    hilbertNegativeMass f ≤ negativeMassHead N f +
      ‖f‖ * Real.sqrt (1 / ((N : ℝ) + 1)) := by
  have ht : ‖paretoTail N‖ = Real.sqrt (1 / ((N : ℝ) + 1)) := by
    rw [← paretoTail_norm_sq N, Real.sqrt_sq (norm_nonneg _)]
  have h := real_inner_le_norm (hilbertNegativePart f) (paretoTail N)
  have hb := mul_le_mul_of_nonneg_right (hilbertNegativePart_norm_le f)
    (norm_nonneg (paretoTail N))
  rw [ht] at h hb
  linarith [negativeMassHead_tail_identity N f]

/-- All positive sites have positive mass, so zero total negative mass is a pointwise sign test. -/
theorem negativeMass_eq_zero_iff (f : ThresholdHilbert) :
    hilbertNegativeMass f = 0 ↔ ∀ n : ℕ, 0 < n → 0 ≤ hilbertSequence f n := by
  constructor
  · intro hz n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    by_contra! hneg
    have hp : 0 < paretoWeight k * max (-hilbertSequence f (k+1)) 0 :=
      mul_pos (paretoWeight_pos k) ((neg_pos.mpr hneg).trans_le (le_max_left _ _))
    have hsite : paretoWeight k * max (-hilbertSequence f (k+1)) 0 ≤
        negativeMassHead (k+1) f := by
      rw [negativeMassHead_eq_sum]
      exact Finset.single_le_sum (f := fun j => paretoWeight j * max (-hilbertSequence f (j+1)) 0)
        (fun j _ => mul_nonneg (paretoWeight_pos j).le (le_max_right _ _))
        (Finset.mem_range.mpr (Nat.lt_succ_self k))
    have hh := hp.trans_le (hsite.trans (negativeMassHead_le (k+1) f))
    rw [hz] at hh
    exact lt_irrefl _ hh
  · intro h
    have hz (n : ℕ) : max (-hilbertSequence f n) 0 = 0 := by
      cases n with
      | zero => simp
      | succ n => exact max_eq_right (neg_nonpos.mpr (h _ (Nat.succ_pos _)))
    simp only [hilbertNegativeMass, hz, mul_zero, tsum_zero]

end RiemannResearch.RH.Pareto
