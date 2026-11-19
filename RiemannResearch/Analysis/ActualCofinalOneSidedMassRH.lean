/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualOneSidedHorizontalDisplacement
import RiemannResearch.RH.HorizontalEnergyCriterion

/-! # Cofinal vanishing of the unnormalized one-sided displacement mass -/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- Cofinal smallness of the actual cumulative mass, including multiplicities. -/
def CofinalSmallOneSidedTotal : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, ∃ T : ℝ, B ≤ T ∧ T * oneSidedHeightMean T < ε

/-- Every positive-ordinate zero contributes its one-sided displacement at every later height. -/
theorem displacement_le_oneSidedHeightTotal {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hi : 0 < ρ.im) {T : ℝ} (hT : ρ.im ≤ T) :
    max (ρ.re - 1 / 2) 0 ≤ T * oneSidedHeightMean T := by
  classical
  have hm := mem_cutoff.mpr ⟨hρ, hi, hT⟩
  have hmult : (1 : ℝ) ≤ (zeroMult ρ : ℝ) := by exact_mod_cast multiplicity_pos hm
  have ht := hi.trans_le hT
  have he : T * oneSidedHeightMean T = realSum T (fun z => max (z.re - 1 / 2) 0) := by
    let q := realSum T (fun z => max (z.re - 1 / 2) 0)
    change T * (q / T) = q
    calc
      T * (q / T) = (q / T) * T := mul_comm _ _
      _ = q := div_mul_cancel₀ _ ht.ne'
  rw [he]
  exact (le_mul_of_one_le_left (le_max_right _ _) hmult).trans
    (Finset.single_le_sum (f := fun z : ℂ => (zeroMult z : ℝ) * max (z.re - 1 / 2) 0)
      (fun z _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)) hm)

private theorem positive_re_le_half_of_cofinal (h : CofinalSmallOneSidedTotal)
    {ρ : ℂ} (hρ : IsNontrivialZero ρ) (hi : 0 < ρ.im) : ρ.re ≤ 1 / 2 := by
  by_contra! hright
  obtain ⟨T, hT, hsmall⟩ := h (ρ.re - 1 / 2) (sub_pos.mpr hright) ρ.im
  have hle := (le_max_left _ _).trans (displacement_le_oneSidedHeightTotal hρ hi hT)
  exact (not_lt_of_ge hle) hsmall

private theorem re_le_half_of_cofinal (h : CofinalSmallOneSidedTotal)
    {ρ : ℂ} (hρ : IsNontrivialZero ρ) : ρ.re ≤ 1 / 2 := by
  rcases lt_trichotomy 0 ρ.im with hi | hi | hi
  · exact positive_re_le_half_of_cofinal h hρ hi
  · have he : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [hi.symm]
    exact False.elim (RiemannResearch.RH.riemannZeta_ofReal_ne_zero ρ.re hρ.2.1 hρ.2.2.ne
      ((congrArg riemannZeta he).symm.trans hρ.1))
  · have hc : IsNontrivialZero (conj ρ) := by
      refine ⟨?_, hρ.2.1, hρ.2.2⟩
      rw [_root_.riemannZeta_conj, hρ.1, map_zero]
    simpa only [Complex.conj_re] using positive_re_le_half_of_cofinal h hc
      (by simpa only [Complex.conj_im] using neg_pos.mpr hi)

/-- On RH the unnormalized one-sided mass vanishes at every height. -/
theorem oneSidedHeightTotal_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis) (T : ℝ) :
    T * oneSidedHeightMean T = 0 := by
  classical
  have hsum : realSum T (fun z => max (z.re - 1 / 2) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    have h := (mem_cutoff.mp hz).1
    have hr := RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mp hRH
      z h.1 h.2.1 h.2.2
    simp [hr]
  unfold oneSidedHeightMean
  rw [hsum, zero_div, mul_zero]

/-- Cofinal smallness of the cumulative total is exactly Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_iff_cofinalSmallOneSidedTotal :
    RiemannHypothesis ↔ CofinalSmallOneSidedTotal := by
  constructor
  · intro h ε hε B
    exact ⟨B, le_rfl, (oneSidedHeightTotal_eq_zero_of_riemannHypothesis h B).trans_lt hε⟩
  · intro h
    apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
    intro ρ hz hr0 hr1
    have hρ : IsNontrivialZero ρ := ⟨hz, hr0, hr1⟩
    have hi := re_le_half_of_cofinal h hρ
    have lo := re_le_half_of_cofinal h (zetaSeam.reflect_zero ρ hρ)
    rw [reflect_re] at lo
    linarith

end RiemannResearch.Analysis.ActualZeroOrdinate
