/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.Analysis.ResolventHorizontalDefect
import RiemannResearch.Analysis.DeterminantHorizontalDefect

/-!
# Exact resolvent and determinant defects on actual zeta cutoffs

Source: the user's Ordinate_Harmonic_Theory_20261010 report and the independently
derived scalar identities in the imported modules. All actual positive-height
zeros and analytic multiplicities are retained. The determinant criterion has
no low-height premise. The resolvent sign estimate explicitly requires a
height premise. No infinite xi-product or prime-series identity is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualZeroHorizontalDefect
open ActualZeroOrdinate Zeta23

def ordinateResolvent (T x : ℝ) : ℝ :=
  realSum T (fun ρ => 2 * x / (x ^ 2 + ρ.im ^ 2))

def fullResolvent (T x : ℝ) : ℝ :=
  realSum T (fun ρ => 2 * (x - (ρ.re - 1 / 2)) /
    ((x - (ρ.re - 1 / 2)) ^ 2 + ρ.im ^ 2))

def resolventGap (T x : ℝ) : ℝ :=
  realSum T (fun ρ => ResolventHorizontalDefect.gap x (ρ.re - 1 / 2) (ρ.im ^ 2))

def fourthEnergy (T : ℝ) : ℝ :=
  realSum T (fun ρ => (ρ.re - 1 / 2) ^ 2 / (1 + ρ.im ^ 2) ^ 2)

theorem resolventGap_exact (T x : ℝ) :
    resolventGap T x = realSum T (fun ρ =>
      (ρ.re - 1 / 2) ^ 2 * ResolventHorizontalDefect.weight x
        (ρ.re - 1 / 2) (ρ.im ^ 2)) := by
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hi := (mem_cutoff.mp hρ).2.1
  dsimp only
  rw [ResolventHorizontalDefect.gap_eq_square_mul_weight x _ (sq_pos_of_pos hi)]

/-- Horizontal reflection is performed before summands are estimated. -/
theorem ordinate_sub_full_eq_gap (T x : ℝ) :
    ordinateResolvent T x - fullResolvent T x = resolventGap T x := by
  let f : ℂ → ℝ := fun ρ => (x - (ρ.re - 1 / 2)) /
    ((x - (ρ.re - 1 / 2)) ^ 2 + ρ.im ^ 2)
  have hr := realSum_reflect T f
  have hf : (fun ρ => f (reflect ρ)) = (fun ρ =>
      (x + (ρ.re - 1 / 2)) / ((x + (ρ.re - 1 / 2)) ^ 2 + ρ.im ^ 2)) := by
    funext ρ
    dsimp [f]
    rw [reflect_re, reflect_im]
    congr 2 <;> ring
  rw [hf] at hr
  have hsum : realSum T (fun ρ => f ρ +
      (x + (ρ.re - 1 / 2)) / ((x + (ρ.re - 1 / 2)) ^ 2 + ρ.im ^ 2)) =
      fullResolvent T x := by
    rw [realSum_add, hr]
    unfold fullResolvent
    have he : (fun ρ : ℂ => 2 * (x - (ρ.re - 1 / 2)) /
        ((x - (ρ.re - 1 / 2)) ^ 2 + ρ.im ^ 2)) = (fun ρ => f ρ * 2) := by
      funext ρ; dsimp [f]; ring
    rw [he, realSum_mul_const]
    ring
  rw [← hsum]
  unfold ordinateResolvent resolventGap ResolventHorizontalDefect.gap
  simp only [realSum, mul_sub, Finset.sum_sub_distrib]
  rfl

theorem resolventGap_two_bounds (T : ℝ)
    (hheight : ∀ ρ ∈ cutoff T, 1 ≤ ρ.im ^ 2) :
    (1 / 5 : ℝ) * fourthEnergy T ≤ resolventGap T (3 / 2) ∧
      resolventGap T (3 / 2) ≤ 9 * fourthEnergy T := by
  have hlo := realSum_mono T _ _ (fun ρ hρ =>
    (ResolventHorizontalDefect.gap_two_bounds (displacement_lt_half hρ).le
      (hheight ρ hρ)).1)
  have hhi := realSum_mono T _ _ (fun ρ hρ =>
    (ResolventHorizontalDefect.gap_two_bounds (displacement_lt_half hρ).le
      (hheight ρ hρ)).2)
  have hleft : realSum T (fun ρ => (1 / 5 : ℝ) *
      ((ρ.re - 1 / 2) ^ 2 / (1 + ρ.im ^ 2) ^ 2)) = (1 / 5 : ℝ) * fourthEnergy T := by
    simp only [realSum, fourthEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ; ring
  have hright : realSum T (fun ρ => 9 *
      ((ρ.re - 1 / 2) ^ 2 / (1 + ρ.im ^ 2) ^ 2)) = 9 * fourthEnergy T := by
    simp only [realSum, fourthEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ; ring
  exact ⟨by simpa only [hleft, resolventGap] using hlo,
    by simpa only [hright, resolventGap] using hhi⟩

def determinantGap (T x : ℝ) : ℝ := realSum T (fun ρ =>
  DeterminantHorizontalDefect.ordinateFactor x (ρ.im ^ 2) -
    DeterminantHorizontalDefect.fullFactor x (ρ.re - 1 / 2) (ρ.im ^ 2))

theorem determinantGap_nonneg (T x : ℝ) : 0 ≤ determinantGap T x := by
  apply realSum_nonneg
  intro ρ hρ
  exact sub_nonneg.mpr (DeterminantHorizontalDefect.factor_le x _
    (sq_pos_of_pos (mem_cutoff.mp hρ).2.1))

/-- The finite determinant gap detects actual horizontal displacement without
RH, zero simplicity, or a lower bound on zero height. -/
theorem determinantGap_eq_zero_iff (T : ℝ) {x : ℝ} (hx : x ≠ 0) :
    determinantGap T x = 0 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  have hn : ∀ ρ ∈ cutoff T, 0 ≤ (zeroMult ρ : ℝ) *
      (DeterminantHorizontalDefect.ordinateFactor x (ρ.im ^ 2) -
        DeterminantHorizontalDefect.fullFactor x (ρ.re - 1 / 2) (ρ.im ^ 2)) := by
    intro ρ hρ
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr
      (DeterminantHorizontalDefect.factor_le x _
        (sq_pos_of_pos (mem_cutoff.mp hρ).2.1)))
  unfold determinantGap realSum
  rw [Finset.sum_eq_zero_iff_of_nonneg hn]
  constructor
  · intro h ρ hρ
    have hm : (zeroMult ρ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast multiplicity_pos hρ)
    have hz := (mul_eq_zero.mp (h ρ hρ)).resolve_left hm
    have hd := (DeterminantHorizontalDefect.factor_eq_iff hx
      (sq_pos_of_pos (mem_cutoff.mp hρ).2.1)).mp (sub_eq_zero.mp hz).symm
    linarith
  · intro h ρ hρ
    have he := (DeterminantHorizontalDefect.factor_eq_iff (d := ρ.re - 1 / 2) hx
      (sq_pos_of_pos (mem_cutoff.mp hρ).2.1)).mpr (by linarith [h ρ hρ])
    rw [he, sub_self, mul_zero]

/-- Cofinal cutoff vanishing controls every positive-height actual zero. -/
theorem cofinal_determinantGap_zero_iff {x : ℝ} (hx : x ≠ 0) :
    (∀ B : ℝ, ∃ T : ℝ, B ≤ T ∧ determinantGap T x = 0) ↔
      ∀ ρ : PositiveZero, ρ.1.re = 1 / 2 := by
  constructor
  · intro h ρ
    obtain ⟨T, hT, he⟩ := h ρ.1.im
    have hm : ρ.1 ∈ cutoff T := mem_cutoff_iff_zeta.mpr ⟨ρ.2.1, ρ.2.2, hT⟩
    exact (determinantGap_eq_zero_iff T hx).mp he ρ.1 hm
  · intro h B
    refine ⟨B, le_rfl, (determinantGap_eq_zero_iff B hx).mpr ?_⟩
    intro ρ hρ
    obtain ⟨hz, hi, _⟩ := mem_cutoff_iff_zeta.mp hρ
    exact h ⟨ρ, hz, hi⟩

end RiemannResearch.Analysis.ActualZeroHorizontalDefect
