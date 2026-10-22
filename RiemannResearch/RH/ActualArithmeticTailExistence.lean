import RiemannResearch.RH.NymanActualTailWeilAccounting
import RiemannResearch.RH.CompactPolarPotential

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Every compact polar test has an actual arithmetic tail beyond any gap

The potential is supplied by the actual compact Green inverse. The tail is
the explicit finite-inverse arithmetic completion, with proved support,
regularity, polar moments, and complete arithmetic Weil accounting.
-/

open MeasureTheory Set
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis

namespace RiemannResearch.RH

open SignedWeilCorrelation

theorem exists_actual_arithmetic_tail_after
    (n : ℕ) (hn : 2 ≤ n) {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (ha : ∀ x < a, f x = 0) (hb : ∀ x > b, f x = 0)
    (h0 : centeredTransform f 0 = 0) (h1 : centeredTransform f 1 = 0) (Y : ℝ) :
    ∃ (v : ℝ → ℂ) (M : ℕ), ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧ HasCompactSupport v ∧
      poleCancellationOperator v = f ∧
      SmoothSuperexponentialDecay (nymanCompletionTail n M hn v) ∧
      tsupport (nymanCompletionTail n M hn v) ⊆ Ici Y ∧
      centeredTransform (nymanCompletionTail n M hn v) 0 = 0 ∧
      centeredTransform (nymanCompletionTail n M hn v) 1 = 0 ∧
      infinitePrimePowerCorrelationValue
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
        (realAutocorrelation (nymanCompletionTail n M hn v)) =
      infinitePrimePowerCorrelationValue
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) (realAutocorrelation f) ∧
      arithmeticWeilPairing f (nymanCompletionTail n M hn v) =
        -(infinitePrimePowerCorrelationValue
          (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) (realAutocorrelation f) : ℂ) := by
  obtain ⟨v,hv,hvc,hvs,hvf⟩ := exists_compact_smooth_polarPotential hf ha hb h0 h1
  have hva : ∀ x < a, v x = 0 := by
    intro x hx
    by_contra h
    have hs : x ∈ tsupport v := subset_closure h
    linarith [(hvs hs).1]
  have hvb : ∀ x > b, v x = 0 := by
    intro x hx
    by_contra h
    have hs : x ∈ tsupport v := subset_closure h
    linarith [(hvs hs).2]
  obtain ⟨M,hM⟩ := exists_nat_gt (Real.exp (Y - a))
  have hexp : Real.exp (Y - a) < ((M + 1 : ℕ) : ℝ) := by
    exact hM.trans_le (by exact_mod_cast Nat.le_succ M)
  have hgap : Y ≤ a + Real.log (M + 1 : ℕ) := by
    have hlog := Real.log_lt_log (Real.exp_pos (Y - a)) hexp
    rw [Real.log_exp] at hlog
    linarith
  have hpolar := centeredTransform_nymanCompletionTail_polar n M hn hv hva hvb
  refine ⟨v,M,hv,hvc,hvf,smoothSuperexponentialDecay_nymanCompletionTail n M hn hv hva hvb,
    ?_,hpolar.1,hpolar.2,?_,?_⟩
  · intro y hy
    exact hgap.trans (nymanCompletionTail_tsupport n M hn hva hy)
  · simpa only [hvf] using
      infinitePrimePowerCorrelationValue_nymanCompletionTail_eq_head n M hn hv hva hvb
  · simpa only [hvf] using
      arithmeticWeilPairing_head_nymanCompletionTail_eq_neg_head n M hn hv hva hvb

end RiemannResearch.RH
