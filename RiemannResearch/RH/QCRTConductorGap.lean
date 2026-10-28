/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.QCRTMinimumEnergy
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Exact head rigidity across gaps in the conductor dictionary

Source: the user-provided minimum-energy exact-head research agenda,
28 October 2026, priorities 3 and 4. Finite-stage exploration suggested
the bounds below; the proof uses exact finite sums and the complete norm.
No uniform upper bound is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTConductorGap
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets
open QResidueHeadSpace QSquarefreeAffineHead QCRTCoprimeApproximation
open QPrimePowerSieve QFiniteEnergyBounds

/-- With no dictionary conductor between the old and new cutoff,
agreement propagates through the entire gap. The common head is arbitrary. -/
theorem dictionary_head_agreement_of_gap (s : Finset ℕ)
    (hs : ∀ d ∈ s, 1 < d) (H K r : ℕ) (hH : 0 < H)
    (hr : r ∈ s) (hHr : H < r)
    (hgap : ∀ d ∈ s, H < d → K < d)
    (f g : QHilbert) (hf : f ∈ dictionary s) (hg : g ∈ dictionary s)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = qSequence g n) :
    ∀ n, 0 < n → n ≤ K → qSequence f n = qSequence g n := by
  have hsub : f - g ∈ dictionary s ⊓ headNull H := by
    refine ⟨(dictionary s).sub_mem hf hg, ?_⟩
    intro n hn hnH
    change qSequenceLinear (f - g) n = 0
    simp only [map_sub, Pi.sub_apply]
    change qSequence f n - qSequence g n = 0
    exact sub_eq_zero.mpr (hh n hn hnH)
  rw [inf_headNull_eq_zeroHeadSpan s hs H r hH hr hHr] at hsub
  have hle : zeroHeadSpan s H r ≤ headNull K := by
    apply Submodule.span_le.mpr
    rintro x ⟨d, rfl⟩ n hn hnK
    have hd := Finset.mem_filter.mp d.property
    have hKd := hgap d hd.1 hd.2.1
    have hKr := hgap r hr hHr
    exact compensatedResidue_head d r n (by omega) (by omega) (by omega) (by omega)
  intro n hn hnK
  have he := hle hsub n hn hnK
  change qSequenceLinear (f - g) n = 0 at he
  simp only [map_sub, Pi.sub_apply] at he
  change qSequence f n - qSequence g n = 0 at he
  exact sub_eq_zero.mp he

/-- Divisor-stage form of head agreement across a gap. -/
theorem divisorStage_head_agreement_of_gap (L H K : ℕ)
    (hL : 0 < L) (hH : 0 < H) (hHL : H < L)
    (hgap : ∀ d, d ∣ L → H < d → K < d)
    (f g : QHilbert) (hf : f ∈ divisorStage L) (hg : g ∈ divisorStage L)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = qSequence g n) :
    ∀ n, 0 < n → n ≤ K → qSequence f n = qSequence g n := by
  rw [divisorStage_eq_dictionary L hL] at hf hg
  apply dictionary_head_agreement_of_gap (conductors L) (conductor_gt_one L)
    H K L hH _ hHL _ f g hf hg hh
  · exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨dvd_refl _, ne_of_gt hL⟩, by omega⟩
  · intro d hd hdH
    exact hgap d (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1 hdH

/-- A forced finite head lower-bounds the entire, infinite norm. -/
theorem finite_raw_energy_le (f : QHilbert) (K : ℕ) :
    (1 / zetaTwo) *
      (∑ n ∈ Finset.range K, (qSequence f (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) ≤ ‖f‖ ^ 2 := by
  have hs := SquarefreeRadicalDifference.qNormalized_square_summable f
  simp only [div_pow] at hs
  have hs' : Summable (fun n : ℕ => (qSequence f (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  rw [norm_sq_unweighted]
  apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr zetaTwo_pos).le
  exact hs'.sum_le_tsum (Finset.range K) (fun n hn =>
    div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- A generic finite obstruction certificate. The numeric sum contains
only natural gcd counts and rational arithmetic. -/
theorem norm_sq_gt_one_of_coprime_gap (L H K : ℕ)
    (hL : 0 < L) (hH : 0 < H) (hHK : H ≤ K) (hKL : K < L)
    (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L)
    (hgap : ∀ d, d ∣ L → H < d → K < d)
    (hnum : (329 : ℚ) / 200 <
      ∑ n ∈ Finset.range K,
        (((Finset.Icc 1 (n + 1)).filter (fun a => Nat.gcd a L = 1)).card : ℚ) ^ 2 /
          (n + 1 : ℚ) ^ 2)
    (f : QHilbert) (hf : f ∈ divisorStage L)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    1 < ‖f‖ ^ 2 := by
  have he := divisorStage_head_agreement_of_gap L H K hL hH
    (lt_of_le_of_lt hHK hKL) hgap f (coprimeApprox L) hf
    (coprimeApprox_mem_divisorStage L) (by
      intro n hn hnH
      rw [hh n hn hnH, coprimeApprox_exact_head L H n hL hcover
        (lt_of_le_of_lt hHK hKL) hn hnH])
  have hval (n : ℕ) (hn : n ∈ Finset.range K) :
      qSequence f (n + 1) =
        (((Finset.Icc 1 (n + 1)).filter (fun a => Nat.gcd a L = 1)).card : ℝ) := by
    have hnK : n + 1 ≤ K := by have := Finset.mem_range.mp hn; omega
    rw [he (n + 1) (by omega) hnK, coprimeApprox_sequence L (n + 1) hL,
      Nat.div_eq_of_lt (lt_of_le_of_lt hnK hKL), Nat.cast_zero,
      mul_zero, sub_zero, sieveCount_eq_card]
  have hreal : (329 : ℝ) / 200 <
      ∑ n ∈ Finset.range K,
        (((Finset.Icc 1 (n + 1)).filter (fun a => Nat.gcd a L = 1)).card : ℝ) ^ 2 /
          (n + 1 : ℝ) ^ 2 := by
    have hc : (((329 : ℚ) / 200) : ℝ) <
        ((∑ n ∈ Finset.range K,
          (((Finset.Icc 1 (n + 1)).filter (fun a => Nat.gcd a L = 1)).card : ℚ) ^ 2 /
            (n + 1 : ℚ) ^ 2 : ℚ) : ℝ) := by
      exact_mod_cast hnum
    push_cast at hc
    exact hc
  have heq : (∑ n ∈ Finset.range K, (qSequence f (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) =
      ∑ n ∈ Finset.range K,
        (((Finset.Icc 1 (n + 1)).filter (fun a => Nat.gcd a L = 1)).card : ℝ) ^ 2 /
          (n + 1 : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hval n hn]
  have hzlt : zetaTwo <
      ∑ n ∈ Finset.range K, (qSequence f (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2 := by
    rw [heq]
    exact zetaTwo_rational_bounds.2.trans hreal
  have hgt : 1 < (1 / zetaTwo) *
      (∑ n ∈ Finset.range K, (qSequence f (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) := by
    rw [one_div_mul_eq_div]
    exact (lt_div_iff₀ zetaTwo_pos).mpr (by simpa using hzlt)
  exact hgt.trans_le (finite_raw_energy_le f K)

-- The exact finite rational sums are evaluated by kernel reduction.
set_option maxRecDepth 100000 in
theorem period210_head10_energy_gt_one (f : QHilbert)
    (hf : f ∈ divisorStage 210)
    (hh : ∀ n, 0 < n → n ≤ 10 → qSequence f n = 1) :
    1 < ‖f‖ ^ 2 := by
  apply norm_sq_gt_one_of_coprime_gap 210 10 13 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _ _ _ f hf hh
  · intro p hp hpH
    interval_cases p <;> norm_num at *
  · intro d hd hdH
    by_contra hnot
    have hdK : d ≤ 13 := by omega
    interval_cases d <;> norm_num at hd
  · decide +kernel

-- The exact finite rational sums are evaluated by kernel reduction.
set_option maxRecDepth 100000 in
theorem period30030_head15_energy_gt_one (f : QHilbert)
    (hf : f ∈ divisorStage 30030)
    (hh : ∀ n, 0 < n → n ≤ 15 → qSequence f n = 1) :
    1 < ‖f‖ ^ 2 := by
  apply norm_sq_gt_one_of_coprime_gap 30030 15 20 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _ _ _ f hf hh
  · intro p hp hpH
    interval_cases p <;> norm_num at *
  · intro d hd hdH
    by_contra hnot
    have hdK : d ≤ 20 := by omega
    interval_cases d <;> norm_num at hd
  · decide +kernel

/-- The canonical diagonal already exceeds one at j=14. This refutes
the special bound C = 1, not a bound by an arbitrary finite C. -/
theorem minimumEnergyApproximant_fourteen_gt_one :
    1 < ‖QCRTMinimumEnergy.minimumEnergyApproximant 14‖ ^ 2 := by
  apply period30030_head15_energy_gt_one
  · have hp : primorial (14 + 2) = 30030 := by decide +kernel
    have hm := QCRTMinimumEnergy.minimumEnergyApproximant_mem_dictionary 14
    rw [← divisorStage_eq_dictionary _ (primorial_pos _), hp] at hm
    exact hm
  · exact QCRTMinimumEnergy.minimumEnergyApproximant_exact_head 14

end RiemannResearch.RH.QCRTConductorGap
