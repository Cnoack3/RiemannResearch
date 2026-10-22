/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualConsecutiveOrdinates
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# Exact consecutive-gap criteria for actual zeta zeros

The chronological list retains every multiplicity copy and every distinct zero
with the same ordinate. Strict positivity of every genuine interior consecutive
gap is therefore equivalent to criticality and simplicity through the cutoff.
The artificial final gap to the cutoff height is expressly excluded.

The equivalence is a finite criterion, not a proof of its positivity hypothesis.
Source: the user's consecutive-ordinate research question, 2026-10-22; the proof
uses the existing chronological-list and reflection certificates.
-/

noncomputable section
open Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Strict positivity of every genuine adjacent gap is precisely criticality
and simplicity at that cutoff. Empty and singleton cutoffs are included. -/
theorem all_interior_cutoffGap_pos_iff (T : ℝ) :
    (∀ n : ℕ, n + 1 < Ncount 0 T → 0 < cutoffGap T n) ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  constructor
  · intro hgap
    apply (chronologicalList_strict_iff T).mp
    rw [List.sortedLT_iff_strictMono_get]
    intro i j hij
    have hij' : i.val < j.val := hij
    have hj : j.val < Ncount 0 T := by
      simpa only [chronologicalList_length] using j.isLt
    have hisucc : i.val + 1 < Ncount 0 T :=
      lt_of_le_of_lt (Nat.succ_le_of_lt hij') hj
    have hstep : cutoffOrdinate T i.val < cutoffOrdinate T (i.val + 1) :=
      sub_pos.mp (hgap i.val hisucc)
    have hbetween : cutoffOrdinate T (i.val + 1) ≤ cutoffOrdinate T j.val :=
      cutoffOrdinate_monotone T (Nat.succ_le_of_lt hij')
    have hlt := hstep.trans_le hbetween
    simpa only [cutoffOrdinate_eq_get i.isLt,
      cutoffOrdinate_eq_get j.isLt] using hlt
  · intro hall n hn
    have hi : n < (chronologicalList T).length := by
      rw [chronologicalList_length]
      omega
    have hj : n + 1 < (chronologicalList T).length := by
      simpa only [chronologicalList_length] using hn
    apply sub_pos.mpr
    rw [cutoffOrdinate_eq_get hi, cutoffOrdinate_eq_get hj]
    exact ((chronologicalList_strict_iff T).mpr hall).strictMono_get
      (show (⟨n, hi⟩ : Fin (chronologicalList T).length) < ⟨n + 1, hj⟩ from
        Nat.lt_succ_self n)

/-- Number of zero consecutive spacings strictly inside the cutoff. -/
def zeroInteriorGapCount (T : ℝ) : ℕ :=
  ((Finset.range (Ncount 0 T - 1)).filter (fun n => cutoffGap T n = 0)).card

/-- Nonnegative genuine gaps have no zero entries exactly when all are positive. -/
theorem zeroInteriorGapCount_eq_zero_iff_pos (T : ℝ) :
    zeroInteriorGapCount T = 0 ↔
      ∀ n : ℕ, n + 1 < Ncount 0 T → 0 < cutoffGap T n := by
  classical
  simp only [zeroInteriorGapCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, Finset.mem_range]
  constructor
  · intro h n hn
    have hne : cutoffGap T n ≠ 0 := h (by omega : n < Ncount 0 T - 1)
    rcases eq_or_lt_of_le (cutoffGap_nonneg T n) with hzero | hpos
    · exact False.elim (hne hzero.symm)
    · exact hpos
  · intro h n hn hzero
    have hpos := h n (by omega)
    exact (ne_of_gt hpos) hzero

/-- A vanishing zero-gap count is an exact finite-height certificate. -/
theorem zeroInteriorGapCount_eq_zero_iff (T : ℝ) :
    zeroInteriorGapCount T = 0 ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  rw [zeroInteriorGapCount_eq_zero_iff_pos, all_interior_cutoffGap_pos_iff]

/-- Cofinal adjacent-gap positivity suffices: every height need not itself be
one of the supplied cutoffs. This is equivalent to global positive-height
criticality and simplicity, rather than an unconditional proof of either. -/
theorem cofinal_interior_cutoffGap_pos_iff :
    (∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      ∀ n : ℕ, n + 1 < Ncount 0 T → 0 < cutoffGap T n) ↔
      (∀ H : ℝ, ∀ ρ ∈ cutoff H, ρ.re = 1 / 2 ∧ zeroMult ρ = 1) := by
  constructor
  · intro h H ρ hρ
    obtain ⟨T, hHT, hT⟩ := h H
    have hρT : ρ ∈ cutoff T := by
      obtain ⟨hz, hpos, hheight⟩ := mem_cutoff.mp hρ
      exact mem_cutoff.mpr ⟨hz, hpos, hheight.trans hHT⟩
    exact (all_interior_cutoffGap_pos_iff T).mp hT ρ hρT
  · intro h H
    exact ⟨H, le_rfl, (all_interior_cutoffGap_pos_iff H).mpr (h H)⟩

/-- Every actual positive zero is covered by the cofinal consecutive-gap
criterion, with no enumeration or simplicity premise hidden in the model. -/
theorem positive_zero_critical_and_simple_of_cofinal_interior_gap_pos
    (hgap : ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      ∀ n : ℕ, n + 1 < Ncount 0 T → 0 < cutoffGap T n)
    {ρ : ℂ} (hz : IsNontrivialZero ρ) (hpos : 0 < ρ.im) :
    ρ.re = 1 / 2 ∧ zeroMult ρ = 1 :=
  cofinal_interior_cutoffGap_pos_iff.mp hgap ρ.im ρ
    (mem_cutoff.mpr ⟨hz, hpos, le_rfl⟩)

end RiemannResearch.Analysis.ActualZeroOrdinate
