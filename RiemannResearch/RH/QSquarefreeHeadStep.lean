/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.NormalizedResidueExactHeadCharges
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.RH.QFiniteEnergyBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact complete-Q cost of one more physical head constraint

Source: user-provided squarefree profinite lattice research agenda,
16 October 2026, Targets 2 and 3, for the head-cost/period-gain strategy.
The scalar inverse-Gram specialization is developed here using the actual
compensated residue dictionary and the established finite Gram theorems.

At the new site n, every old zero-head direction except conductor n
vanishes. Its observation vector is therefore exactly minus the n-th
coordinate vector. The entire inverse Gram matrix determines the least
cost of repairing that observation; no other large conductor is omitted.
The resulting equality and single-direction estimate do not establish
a uniform cumulative cost bound or prove RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeHeadStep
open ZetaTwoHilbert ArithmeticCumulative QSquarefreeLatticePackets QResidueHeadSpace
open QSquarefreeAffineHead
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity

private theorem sequence_linearCombination {ι : Type*} [Fintype ι]
    (v : ι → QHilbert) (c : ι → ℝ) (n : ℕ) :
    qSequence (Fintype.linearCombination ℝ v c) n =
      ∑ i, c i * qSequence (v i) n := by
  change qSequenceLinear (Fintype.linearCombination ℝ v c) n =
    ∑ i, c i * qSequenceLinear (v i) n
  simp only [Fintype.linearCombination_apply, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The first newly observed physical value sees exactly the conductor n.
Every larger compensated conductor has value zero there. -/
theorem compensatedResidue_next (n d r : ℕ) (hn : 0 < n)
    (hd : n ≤ d) (hr : n < r) :
    qSequence (compensatedResidue d r) n = if d = n then -1 else 0 := by
  by_cases he : d = n
  · subst d
    rw [if_pos rfl, compensatedResidue_sequence]
    simp only [residueFraction, Nat.mod_self, Nat.cast_zero, zero_div,
      Nat.mod_eq_of_lt hr, zero_sub]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
    field_simp [hnR, hrR]
  · rw [if_neg he]
    exact compensatedResidue_head d r n (by omega) (by omega) (by omega) hr

def stepSource (n L r : ℕ) : freeConductors (conductors L) (n - 1) r → ℝ :=
  fun d => if (d : ℕ) = n then -1 else 0

def stepCapacity (n L r : ℕ) (hr : r ∈ conductors L) : ℝ :=
  capacity (compensated_linearIndependent (conductors L) (conductor_gt_one L)
    (n - 1) r hr) (stepSource n L r)

def stepNormal (n L r : ℕ) (hr : r ∈ conductors L) : QHilbert :=
  minimumVector (compensated_linearIndependent (conductors L) (conductor_gt_one L)
    (n - 1) r hr) (stepSource n L r)

theorem stepSource_ne_zero (n L r : ℕ) (hn : 1 < n) (hL : 0 < L)
    (hnL : n ∣ L) (hrn : n < r) : stepSource n L r ≠ 0 := by
  have hmem : n ∈ freeConductors (conductors L) (n - 1) r := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, by omega, by omega⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hnL, ne_of_gt hL⟩, hn⟩
  intro hz
  have he := congrFun hz ⟨n, hmem⟩
  norm_num [stepSource] at he

theorem stepCapacity_pos (n L r : ℕ) (hn : 1 < n) (hL : 0 < L)
    (hnL : n ∣ L) (hr : r ∈ conductors L) (hrn : n < r) :
    0 < stepCapacity n L r hr :=
  capacity_pos _ _ (stepSource_ne_zero n L r hn hL hnL hrn)

theorem stepNormal_mem (n L r : ℕ) (hr : r ∈ conductors L) :
    stepNormal n L r hr ∈ zeroHeadSpan (conductors L) (n - 1) r := by
  unfold stepNormal minimumVector
  rw [Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun d _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, rfl⟩)

theorem step_sequence (n L r : ℕ) (hn : 0 < n) (hrn : n < r)
    (c : freeConductors (conductors L) (n - 1) r → ℝ) :
    qSequence (Fintype.linearCombination ℝ
      (fun d : freeConductors (conductors L) (n - 1) r =>
        compensatedResidue (d : ℕ) r) c) n =
      ∑ d, c d * stepSource n L r d := by
  rw [sequence_linearCombination]
  apply Finset.sum_congr rfl
  intro d _
  rw [compensatedResidue_next n d r hn
    (by have := (Finset.mem_filter.mp d.property).2.1; omega) hrn]
  rfl

theorem stepNormal_sequence (n L r : ℕ) (hn : 0 < n)
    (hr : r ∈ conductors L) (hrn : n < r) :
    qSequence (stepNormal n L r hr) n = stepCapacity n L r hr := by
  unfold stepNormal minimumVector
  rw [step_sequence n L r hn hrn]
  rfl

/-- The complete signed inverse Gram form is the exact cost of a physical
one-site correction in the whole old zero-head tangent space. -/
theorem correction_completion (n L r : ℕ) (hn : 1 < n) (hL : 0 < L)
    (hnL : n ∣ L) (hr : r ∈ conductors L) (hrn : n < r)
    (f : QHilbert) (hf : f ∈ zeroHeadSpan (conductors L) (n - 1) r)
    (δ : ℝ) (hδ : qSequence f n = δ) :
    ‖f‖ ^ 2 = δ ^ 2 / stepCapacity n L r hr +
      ‖f - (δ / stepCapacity n L r hr) • stepNormal n L r hr‖ ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
  change Fintype.linearCombination ℝ
    (fun d : freeConductors (conductors L) (n - 1) r =>
      compensatedResidue (d : ℕ) r) c = f at hc
  have he : (∑ d, c d * stepSource n L r d) = δ := by
    rw [← step_sequence n L r (by omega) hrn c, hc]
    exact hδ
  rw [← hc]
  exact constrained_value_completion
    (compensated_linearIndependent (conductors L) (conductor_gt_one L) (n - 1) r hr)
    _ c (stepSource_ne_zero n L r hn hL hnL hrn) δ he

/-- A legal one-site correction changes the exact head by its physical value. -/
theorem repaired_head (n L r : ℕ) (hn : 1 < n) (hL : 0 < L)
    (hr : r ∈ conductors L) (hrn : n < r)
    (hsmall : ∀ d, 1 < d → d ≤ n - 1 → Squarefree d → d ∣ L)
    (u : QHilbert) (hu : u ∈ zeroHeadSpan (conductors L) (n - 1) r)
    (huvalue : qSequence u n = 1 - qSequence (optimizer (n - 1) L r hr) n) :
    optimizer (n - 1) L r hr + u ∈ divisorStage L ∧
      ∀ k, 0 < k → k ≤ n →
        qSequence (optimizer (n - 1) L r hr + u) k = 1 := by
  have hf := optimizer_feasible (n - 1) L r (by omega) hL hr (by omega) hsmall
  refine ⟨(divisorStage L).add_mem hf.1 ?_, ?_⟩
  · rw [divisorStage_eq_dictionary L hL]
    exact zeroHeadSpan_le_dictionary _ _ _ hr hu
  · intro k hk hkn
    change qSequenceLinear (_ + _) k = 1
    simp only [map_add, Pi.add_apply]
    change qSequence (optimizer (n - 1) L r hr) k + qSequence u k = 1
    by_cases he : k = n
    · subst k
      rw [huvalue]
      ring
    · rw [hf.2 k hk (by omega),
        zeroHeadSpan_le_headNull _ _ _ (by omega) hu k hk (by omega), add_zero]

/-- The exact interpolation penalty for the actual finite-stage optimizer.
All conductors above the old head participate through the full Gram inverse. -/
theorem minimumError_single_head_cost (n L r : ℕ) (hn : 1 < n) (hL : 0 < L)
    (hnL : n ∣ L) (hr : r ∈ conductors L) (hrn : n < r)
    (hsmall : ∀ d, 1 < d → d ≤ n → Squarefree d → d ∣ L) :
    minimumError n L r hr = minimumError (n - 1) L r hr +
      (1 - qSequence (optimizer (n - 1) L r hr) n) ^ 2 /
        stepCapacity n L r hr := by
  let δ := 1 - qSequence (optimizer (n - 1) L r hr) n
  let u := (δ / stepCapacity n L r hr) • stepNormal n L r hr
  have hsmallOld : ∀ d, 1 < d → d ≤ n - 1 → Squarefree d → d ∣ L :=
    fun d hd hdn hdsf => hsmall d hd (by omega) hdsf
  have hu : u ∈ zeroHeadSpan (conductors L) (n - 1) r :=
    Submodule.smul_mem _ _ (stepNormal_mem n L r hr)
  have hcap := ne_of_gt (stepCapacity_pos n L r hn hL hnL hr hrn)
  have huvalue : qSequence u n = δ := by
    change qSequenceLinear ((_ : ℝ) • _) n = δ
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    change δ / stepCapacity n L r hr * qSequence (stepNormal n L r hr) n = δ
    rw [stepNormal_sequence n L r (by omega) hr hrn, div_mul_cancel₀ _ hcap]
  have huenergy : ‖u‖ ^ 2 = δ ^ 2 / stepCapacity n L r hr :=
    scaled_source_energy _ _ (stepSource_ne_zero n L r hn hL hnL hrn) δ
  have hrepair := repaired_head n L r hn hL hr hrn hsmallOld u hu huvalue
  have hupper := minimumError_le n L r (by omega) hL hr hrn hsmall
    _ hrepair.1 hrepair.2
  have hcompletion := minimumError_completion (n - 1) L r (by omega) hL hr
    (by omega) hsmallOld _ hrepair.1
    (fun k hk hkn => hrepair.2 k hk (by omega))
  simp only [add_sub_cancel_left] at hcompletion
  rw [huenergy] at hcompletion
  have hnew := optimizer_feasible n L r (by omega) hL hr hrn hsmall
  have hold := optimizer_feasible (n - 1) L r (by omega) hL hr (by omega) hsmallOld
  have hdiff : optimizer n L r hr - optimizer (n - 1) L r hr ∈
      zeroHeadSpan (conductors L) (n - 1) r := by
    apply (exact_head_iff_sub_mem_zeroHeadSpan (conductors L) (conductor_gt_one L)
      (n - 1) r (by omega) hr (by omega) (optimizer (n - 1) L r hr)
      (by simpa only [← divisorStage_eq_dictionary L hL] using hold.1) hold.2 _).mp
    exact ⟨by simpa only [← divisorStage_eq_dictionary L hL] using hnew.1,
      fun k hk hkn => hnew.2 k hk (by omega)⟩
  have hvalue : qSequence (optimizer n L r hr - optimizer (n - 1) L r hr) n = δ := by
    change qSequenceLinear (_ - _) n = δ
    simp only [map_sub, Pi.sub_apply]
    change qSequence (optimizer n L r hr) n - qSequence (optimizer (n - 1) L r hr) n = δ
    rw [hnew.2 n (by omega) le_rfl]
  have hcorr := correction_completion n L r hn hL hnL hr hrn _ hdiff δ hvalue
  have hcost := minimumError_head_cost (n - 1) n L r (by omega) (by omega)
    hL hr hrn hsmall
  change minimumError n L r hr = minimumError (n - 1) L r hr +
    δ ^ 2 / stepCapacity n L r hr
  apply le_antisymm
  · exact hupper.trans_eq hcompletion
  · rw [hcost, hcorr]
    have hp := sq_nonneg ‖optimizer n L r hr - optimizer (n - 1) L r hr -
      (δ / stepCapacity n L r hr) • stepNormal n L r hr‖
    linarith

/-- A single compensated legal direction bounds the reciprocal capacity,
while the exact capacity still permits every other high conductor. -/
theorem inverse_stepCapacity_le_trial_energy (n L r : ℕ) (hn : 1 < n)
    (hL : 0 < L) (hnL : n ∣ L) (hr : r ∈ conductors L) (hrn : n < r) :
    1 / stepCapacity n L r hr ≤ ‖compensatedResidue n r‖ ^ 2 := by
  have hmem : n ∈ freeConductors (conductors L) (n - 1) r := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, by omega, by omega⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hnL, ne_of_gt hL⟩, hn⟩
  have ho : inner ℝ (compensatedResidue n r) (stepNormal n L r hr) = -1 := by
    simpa only [stepNormal, stepSource, ↓reduceIte] using
      (minimumVector_observation
        (compensated_linearIndependent (conductors L) (conductor_gt_one L) (n - 1) r hr)
        (stepSource n L r) ⟨n, hmem⟩)
  have he : ‖stepNormal n L r hr‖ ^ 2 = stepCapacity n L r hr := by
    exact (capacity_eq_norm_sq _ _).symm
  have hcs := real_inner_mul_inner_self_le (compensatedResidue n r) (stepNormal n L r hr)
  rw [ho, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he] at hcs
  apply (div_le_iff₀ (stepCapacity_pos n L r hn hL hnL hr hrn)).mpr
  nlinarith

/-- Direct trial estimate for the actual complete-Q head cost. -/
theorem minimumError_single_head_trial_bound (n L r : ℕ) (hn : 1 < n) (hL : 0 < L)
    (hnL : n ∣ L) (hr : r ∈ conductors L) (hrn : n < r)
    (hsmall : ∀ d, 1 < d → d ≤ n → Squarefree d → d ∣ L) :
    minimumError n L r hr ≤ minimumError (n - 1) L r hr +
      (1 - qSequence (optimizer (n - 1) L r hr) n) ^ 2 *
        ‖compensatedResidue n r‖ ^ 2 := by
  rw [minimumError_single_head_cost n L r hn hL hnL hr hrn hsmall]
  apply add_le_add le_rfl
  calc
    _ = (1 - qSequence (optimizer (n - 1) L r hr) n) ^ 2 *
        (1 / stepCapacity n L r hr) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (inverse_stepCapacity_le_trial_energy n L r hn hL hnL hr hrn) (sq_nonneg _)

/-- The cancellation of reciprocal slopes gives a difference of residues,
not a sum of their absolute values. -/
theorem compensatedResidue_abs_le (n r : ℕ) (hn : 0 < n) (hnr : n ≤ r) (k : ℕ) :
    |qSequence (compensatedResidue n r) k| ≤ (r : ℝ) / n := by
  have hr : 0 < r := lt_of_lt_of_le hn hnr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hnle : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have haN : ((k % n : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.mod_lt k hn).le
  have ha : ((k % n : ℕ) : ℝ) ≤ r := haN.trans hnle
  have hb : ((k % r : ℕ) : ℝ) ≤ r := by exact_mod_cast (Nat.mod_lt k hr).le
  have he : qSequence (compensatedResidue n r) k =
      (((k % n : ℕ) : ℝ) - ((k % r : ℕ) : ℝ)) / n := by
    rw [compensatedResidue_sequence]
    unfold residueFraction
    field_simp [ne_of_gt hnR, hrR]
  rw [he, abs_div, abs_of_pos hnR]
  apply div_le_div_of_nonneg_right _ hnR.le
  exact abs_le.mpr ⟨by have := Nat.cast_nonneg (α := ℝ) (k % n); linarith,
    by have := Nat.cast_nonneg (α := ℝ) (k % r); linarith⟩

/-- Complete-Q energy of the explicit trial repair, including its whole tail. -/
theorem compensatedResidue_energy_le (n r : ℕ) (hn : 1 < n) (hnr : n ≤ r) :
    ‖compensatedResidue n r‖ ^ 2 ≤
      (1 / ZetaTwoProbability.zetaTwo) * (((r : ℝ) / n) ^ 2 / (n - 1 : ℕ)) := by
  have he := QFiniteEnergyBounds.norm_sq_le_head_tail (compensatedResidue n r)
    (n - 1) (by omega) ((r : ℝ) / n) (by positivity)
    (compensatedResidue_abs_le n r (by omega) hnr)
  have hz : (∑ k ∈ Finset.range (n - 1),
      (qSequence (compensatedResidue n r) (k + 1)) ^ 2 / (k + 1 : ℝ) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k + 1 < n := by have := Finset.mem_range.mp hk; omega
    rw [compensatedResidue_head n r (k + 1) (by omega) (by omega) hkn (by omega)]
    simp
  simpa only [hz, zero_add] using he

/-- A nearby anchor yields a reciprocal-head bound on the actual penalty.
The physical mismatch is retained exactly; no summability of it is assumed. -/
theorem minimumError_single_head_near_anchor_bound (n L r : ℕ) (hn : 1 < n)
    (hL : 0 < L) (hnL : n ∣ L) (hr : r ∈ conductors L)
    (hrn : n < r) (hrnear : r ≤ 2 * n)
    (hsmall : ∀ d, 1 < d → d ≤ n → Squarefree d → d ∣ L) :
    minimumError n L r hr ≤ minimumError (n - 1) L r hr +
      (1 - qSequence (optimizer (n - 1) L r hr) n) ^ 2 *
        ((1 / ZetaTwoProbability.zetaTwo) * (4 / (n - 1 : ℕ))) := by
  have hratio : (r : ℝ) / n ≤ 2 := by
    apply (div_le_iff₀ (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)).mpr
    exact_mod_cast hrnear
  have hsq : ((r : ℝ) / n) ^ 2 ≤ 4 := by
    nlinarith [show (0 : ℝ) ≤ (r : ℝ) / n by positivity]
  have henergy := (compensatedResidue_energy_le n r hn hrn.le).trans
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg (n - 1)))
      (one_div_nonneg.mpr ZetaTwoProbability.zetaTwo_pos.le))
  exact (minimumError_single_head_trial_bound n L r hn hL hnL hr hrn hsmall).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left henergy (sq_nonneg _)))

/-- Coefficient form of the concrete nearby-anchor penalty bound. The
coefficients are those of the actual old affine optimizer. -/
theorem minimumError_single_head_coefficient_bound (n L r : ℕ) (hn : 1 < n)
    (hL : 0 < L) (hnL : n ∣ L) (hr : r ∈ conductors L)
    (hrn : n < r) (hrnear : r ≤ 2 * n)
    (hsmall : ∀ d, 1 < d → d ≤ n → Squarefree d → d ∣ L)
    (c : ℕ → ℝ)
    (hc : (∑ d ∈ conductors L, c d • qResidue d) = optimizer (n - 1) L r hr) :
    minimumError n L r hr ≤ minimumError (n - 1) L r hr +
      (c n + (ArithmeticFunction.moebius n : ℝ)) ^ 2 *
        ((1 / ZetaTwoProbability.zetaTwo) * (4 / (n - 1 : ℕ))) := by
  have hold := optimizer_feasible (n - 1) L r (by omega) hL hr (by omega)
    (fun d hd hdn hdsf => hsmall d hd (by omega) hdsf)
  have hm := Pareto.residueFraction_exact_head_next_coefficient (conductors L) c n hn (by
    intro k hk hkn
    rw [← synthesis_sequence, hc]
    exact hold.2 k hk (by omega))
  have hnmem : n ∈ conductors L :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hnL, ne_of_gt hL⟩, hn⟩
  rw [← synthesis_sequence, hc, if_pos hnmem] at hm
  simpa only [hm] using
    minimumError_single_head_near_anchor_bound n L r hn hL hnL hr hrn hrnear hsmall

end RiemannResearch.RH.QSquarefreeHeadStep
