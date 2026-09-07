import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-! # Exact half-line decomposition for even integrable functions -/

open MeasureTheory Set
namespace RiemannResearch.Analysis

/-- An actual even integrable function has equal mass on the two half-lines.
The origin is handled by the complementary Iic/Ioi decomposition. -/
theorem integral_eq_two_smul_Ioi_of_even {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ → E) (hi : Integrable c) (heven : ∀ t, c (-t) = c t) :
    (∫ t, c t) = (2 : ℝ) • ∫ t in Ioi 0, c t := by
  have hreflect : (∫ t in Ioi 0, c t) = ∫ t in Iic 0, c t := by
    simpa only [heven, neg_zero] using integral_comp_neg_Ioi 0 c
  have hsplit := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hi
  simp only [compl_Iic] at hsplit
  rw [← hreflect] at hsplit
  rw [two_smul]
  exact hsplit.symm

/-- The real half-mass identity. -/
theorem integral_Ioi_zero_eq_half_of_even (c : ℝ → ℝ)
    (hi : Integrable c) (heven : ∀ t, c (-t) = c t) :
    (∫ t in Ioi 0, c t) = (∫ t, c t) / 2 := by
  have h := integral_eq_two_smul_Ioi_of_even c hi heven
  simp only [smul_eq_mul] at h
  linarith

end RiemannResearch.Analysis
