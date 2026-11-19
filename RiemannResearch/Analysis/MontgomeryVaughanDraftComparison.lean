/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryTransitionFrequency

/-!
# The RH-conditional Montgomery–Vaughan comparison in repository normalization

Volume III, chapter 30, Theorem 30.1, equation (30.8), author-posted draft.
Equation (30.3) displays the pair sum. The integral identity (30.4) and the
proof following (30.9) specify the normalization used in (30.8): the pair
sum is divided by (T/(2π)) log(T/(2π)). The repository instead divides the
same sum by (T/(2π)) log T. The source variable X corresponds to
α = log X / log T, and Theorem 30.1 assumes RH.
<https://personal.science.psu.edu/rcv4/Vol3/Vol3.pdf>
-/

noncomputable section
open Filter
namespace RiemannResearch.Analysis.MontgomeryVaughanDraftComparison
open MontgomeryFormFactor

def authorLog (T : ℝ) : ℝ := Real.log (T / (2*Real.pi))

def authorForm (T X : ℝ) : ℝ :=
  (Real.log T/authorLog T) * formFactor T (Real.log X/Real.log T)

def errorShape (T X : ℝ) : ℝ :=
  (Real.log (2*X))^3/(Real.sqrt X*Real.log T) +
    X*Real.log (Real.log (4*X))/(T*Real.log T)

/-- The two big-O constants of (30.8) can be replaced by a common one
because both error shapes are nonnegative at 1 ≤ X ≤ T and large T. -/
class Chapter30 : Prop where
  theorem₁ : RiemannHypothesis → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop,
    ∀ X : ℝ, 1 ≤ X → X ≤ T →
      |authorForm T X - ((authorLog T-2)/X^2 + Real.log X/authorLog T)| ≤ K*errorShape T X

/-- The author-posted conditional theorem with the repository's full
positive-ordinate cutoff and TL/(2π) denominator. -/
theorem normalized_chapter30 [h : Chapter30] (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ X : ℝ, 1 ≤ X → X ≤ T →
      |formFactor T (Real.log X/Real.log T) -
        (authorLog T*(authorLog T-2)/(Real.log T*X^2)+Real.log X/Real.log T)| ≤
      (authorLog T/Real.log T)* (K*errorShape T X) := by
  obtain ⟨K,hK,hbound⟩ := h.theorem₁ hRH
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound, eventually_gt_atTop (2*Real.pi), eventually_gt_atTop (1:ℝ)] with T hb hT hT₁
  intro X hX hXT
  have hL := Real.log_pos hT₁
  have hℓ : 0 < authorLog T :=
    Real.log_pos ((one_lt_div (by positivity : 0 < 2*Real.pi)).mpr hT)
  have hx : X ≠ 0 := (zero_lt_one.trans_le hX).ne'
  have hid : formFactor T (Real.log X/Real.log T) -
      (authorLog T*(authorLog T-2)/(Real.log T*X^2) + Real.log X/Real.log T) =
      (authorLog T/Real.log T) *
        (authorForm T X - ((authorLog T-2)/X^2+Real.log X/authorLog T)) := by
    unfold authorForm
    field_simp [hx,hℓ.ne',hL.ne'] <;> ring
  rw [hid,abs_mul,abs_of_pos (div_pos hℓ hL)]
  exact mul_le_mul_of_nonneg_left (hb X hX hXT) (div_nonneg hℓ.le hL.le)

end RiemannResearch.Analysis.MontgomeryVaughanDraftComparison
