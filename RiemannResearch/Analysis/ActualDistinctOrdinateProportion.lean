/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualCriticalProportionDisplacement

/-!
# Distinct positive ordinates of actual zeta zeros

The projection to the imaginary coordinate identifies reflected off-line
zeros, repeated zeros and any other coincidence of ordinates. The denominator
in the cumulative proportion retains all analytic multiplicities.
-/

noncomputable section
open Filter Set Complex Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def distinctOrdinates (T : ℝ) : Finset ℝ := (cutoff T).image Complex.im

def CumulativeDistinctOrdinateProportion (κ : ℝ) : Prop :=
  ∀ ε > 0, ∃ H : ℝ, ∀ T ≥ H,
    (κ - ε) * (Ncount 0 T : ℝ) ≤ ((distinctOrdinates T).card : ℝ)

theorem distinctCritical_le_distinctOrdinates (T : ℝ) :
    N0star 0 T ≤ (distinctOrdinates T).card := by
  classical
  let s := (cutoff T).filter (fun ρ : ℂ => ρ.re = 1/2)
  have hs : (s : Set ℂ) = zerosIn 0 T ∩ {ρ : ℂ | ρ.re = 1/2} := by
    ext ρ
    simp only [s, Finset.mem_coe, Finset.mem_filter, mem_cutoff, Set.mem_inter_iff, zerosIn,
      Set.mem_setOf_eq]
  have hinj : Set.InjOn Complex.im (s : Set ℂ) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp (show x ∈ (cutoff T).filter _ from hx)).2
    have hy' := (Finset.mem_filter.mp (show y ∈ (cutoff T).filter _ from hy)).2
    exact Complex.ext (hx'.trans hy'.symm) hxy
  rw [N0star, ← hs, Set.ncard_coe_finset, ← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

theorem card_distinctOrdinates_le_count (T : ℝ) :
    (distinctOrdinates T).card ≤ Ncount 0 T := by
  classical
  rw [count_eq_sum]
  apply (Finset.card_image_le (s := cutoff T) (f := Complex.im)).trans
  calc
    (cutoff T).card = ∑ _ρ ∈ cutoff T, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun ρ hρ => multiplicity_pos hρ

theorem CumulativeDistinctOrdinateProportion.le_one {κ : ℝ}
    (h : CumulativeDistinctOrdinateProportion κ) : κ ≤ 1 := by
  by_contra! hk
  obtain ⟨H,hH⟩ := h ((κ-1)/2) (by linarith only [hk])
  obtain ⟨T,hTH,hN⟩ := ((eventually_ge_atTop H).and eventually_count_pos).exists
  have hl := (hH T hTH).trans (show ((distinctOrdinates T).card : ℝ) ≤ (Ncount 0 T : ℝ) by
    exact_mod_cast card_distinctOrdinates_le_count T)
  have hpos : (0 : ℝ) < (Ncount 0 T : ℝ) := by exact_mod_cast hN
  have hgt := mul_lt_mul_of_pos_right (show 1 < κ-(κ-1)/2 by linarith only [hk]) hpos
  linarith only [hl,hgt]

theorem CumulativeDistinctCriticalProportion.distinct_ordinates {κ : ℝ}
    (h : CumulativeDistinctCriticalProportion κ) : CumulativeDistinctOrdinateProportion κ := by
  intro ε hε
  obtain ⟨H,hH⟩ := h ε hε
  exact ⟨H, fun T hT => (hH T hT).trans (by exact_mod_cast distinctCritical_le_distinctOrdinates T)⟩

end RiemannResearch.Analysis.ActualZeroOrdinate
