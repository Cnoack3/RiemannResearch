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


/-- The sharp boundary for a vanishing scaled first moment: RH is equivalent
to making T times the actual microscopic mean arbitrarily small at cofinal
heights. No Selberg density estimate enters the equivalence. -/
theorem riemannHypothesis_iff_cofinalSmallMicroscopicMean :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, ∃ T : ℝ, B ≤ T ∧
      T * (displacementMoment T 1 * Real.log T) < ε := by
  let X (T : ℝ) := T * (displacementMoment T 1 * Real.log T)
  let R (T : ℝ) := (Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))
  have hr : Tendsto R atTop (𝓝 1) := tendsto_count_div_mainTerm
  have hevent : ∀ᶠ T : ℝ in atTop, 0 < R T ∧ R T ≤ 2 ∧ 0 ≤ X T ∧
      X T * R T = (4 * Real.pi) * (T * oneSidedHeightMean T) := by
    filter_upwards [hr.eventually (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num)),
      hr.eventually_lt_const (show (1:ℝ) < 2 by norm_num),
      eventually_count_pos, eventually_gt_atTop (1:ℝ)] with T hlo hhi hN hT
    have ht : 0 < T := zero_lt_one.trans hT
    have id := firstMark_mul_countRatio_eq hT (by exact_mod_cast hN.ne')
    refine ⟨hlo, hhi.le, mul_nonneg ht.le
      (mul_nonneg (displacementMoment_nonneg _ _) (Real.log_pos hT).le), ?_⟩
    calc
      X T * R T = T * ((displacementMoment T 1 * Real.log T) * R T) := by dsimp [X]; ring
      _ = _ := by rw [show (displacementMoment T 1 * Real.log T) * R T = _ from id]; ring
  obtain ⟨t₀, H⟩ := eventually_atTop.1 hevent
  constructor
  · intro h ε hε B
    let T := max B t₀
    obtain ⟨hr, _, _, hid⟩ := H T (le_max_right _ _)
    rw [oneSidedHeightTotal_eq_zero_of_riemannHypothesis h T, mul_zero] at hid
    have hz : X T = 0 := (mul_eq_zero.mp hid).resolve_right hr.ne'
    exact ⟨T, le_max_left _ _, hz.trans_lt hε⟩
  · intro h
    apply riemannHypothesis_iff_cofinalSmallOneSidedTotal.mpr
    intro ε hε B
    obtain ⟨T, hT, hsmall⟩ := h (2 * Real.pi * ε) (by positivity) (max B t₀)
    obtain ⟨_, hr, hX, hid⟩ := H T ((le_max_right _ _).trans hT)
    change X T < 2 * Real.pi * ε at hsmall
    have hu := (mul_le_mul_of_nonneg_left hr hX).trans_lt (mul_lt_mul_of_pos_right hsmall (by norm_num : (0:ℝ) < 2))
    refine ⟨T, (le_max_left _ _).trans hT, ?_⟩
    by_contra! hle
    have hbad := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 4 * Real.pi)
    linarith only [hu, hid, hbad]

/-- A cofinal power saving beyond 1/T for the microscopic mean implies RH. -/
theorem riemannHypothesis_of_cofinal_microscopic_power {δ C : ℝ} (hδ : 0 < δ)
    (h : ∀ B : ℝ, ∃ T : ℝ, B ≤ T ∧
      displacementMoment T 1 * Real.log T ≤ C * T ^ (-1 - δ)) : RiemannHypothesis := by
  apply riemannHypothesis_iff_cofinalSmallMicroscopicMean.mpr
  intro ε hε B
  have htend : Tendsto (fun t : ℝ => C * t ^ (-δ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hδ).const_mul C
  obtain ⟨t₀, H⟩ := eventually_atTop.1 (htend.eventually_lt_const hε)
  obtain ⟨T, hT, hm⟩ := h (max (max B t₀) 1)
  have hB := (le_max_left (max B t₀) 1).trans hT
  have ht : 0 < T := zero_lt_one.trans_le ((le_max_right _ _).trans hT)
  refine ⟨T, (le_max_left _ _).trans hB, ?_⟩
  calc
    _ ≤ T * (C * T ^ (-1 - δ)) := mul_le_mul_of_nonneg_left hm ht.le
    _ = C * (T ^ (1 : ℝ) * T ^ (-1 - δ)) := by rw [Real.rpow_one]; ring
    _ = C * T ^ (-δ) := by rw [← Real.rpow_add ht, show (1:ℝ) + (-1 - δ) = -δ by ring]
    _ < ε := H T ((le_max_right _ _).trans hB)

end RiemannResearch.Analysis.ActualZeroOrdinate
