import RiemannResearch.RH.IntegerDPPWeightedHoles
import RiemannResearch.Analysis.ResidualHarmonicGain

/-!
# A finite-window weighted DPP condition sufficient for RH

Source: consequence of the all-site Mellin lower bound in the supplied
DPP argument, 2026-09-20. The rank used for each window may be chosen
independently. This module does not assume existence of an infinite DPP.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.IntegerDPP

theorem weighted_integer_hole_harmonic_lower
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) (n N : ℕ) :
    mellinHoleMassConstant s / ((n : ℝ) + 2) ≤
      ((n : ℝ) + 1) * (1 - integerKernel N n n) := by
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at h1
  have h := (mellinHoleMassConstant_mul_weight_le_site_floor n s hs h1.le).trans
    (siteMellinVacancyFloor_le_integerKernel_complement s hs hs1 hz n N)
  have ha : 0 < (n : ℝ) + 1 := by positivity
  have hb : 0 < (n : ℝ) + 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left h ha.le
  calc
    _ = ((n : ℝ) + 1) * (mellinHoleMassConstant s * paretoWeight n) := by
      unfold paretoWeight
      field_simp [ha.ne', hb.ne'] <;> ring
    _ ≤ _ := hm

/-- A uniform bound across arbitrarily long finite windows is enough.
There is no compatibility or monotonicity requirement on the selected ranks. -/
theorem riemannHypothesis_of_bounded_weighted_hole_windows (C : ℝ)
    (h : ∀ M : ℕ, ∃ N : ℕ,
      (∑ n ∈ Finset.range M, ((n : ℝ) + 1) * (1 - integerKernel N n n)) ≤ C) :
    RiemannHypothesis := by
  by_contra hn
  obtain ⟨s, ⟨hs, h1, hz⟩, _⟩ := exists_common_site_vacancy_floor_of_not_RH hn
  have hc := mellinHoleMassConstant_pos s hs
  have hsum : Summable (fun n : ℕ => mellinHoleMassConstant s / ((n : ℝ) + 2)) := by
    apply summable_of_sum_range_le (c := C) (fun n => by positivity)
    intro M
    obtain ⟨N, hN⟩ := h M
    exact (Finset.sum_le_sum (fun n _ =>
      weighted_integer_hole_harmonic_lower s hs h1 hz n N)).trans hN
  have hns : ¬ Summable (fun n : ℕ => mellinHoleMassConstant s / ((n : ℝ) + 2)) := by
    apply RiemannResearch.Analysis.ResidualGain.not_summable_of_harmonic_lower
      (c := mellinHoleMassConstant s / 2) (by positivity)
    intro n
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
    nlinarith [mul_nonneg hc.le (Nat.cast_nonneg (α := ℝ) n)]
  exact hns hsum

end RiemannResearch.RH.Pareto.IntegerDPP
