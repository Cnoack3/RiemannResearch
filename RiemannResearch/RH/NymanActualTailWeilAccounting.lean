import RiemannResearch.RH.WeilSpectralPairing
import RiemannResearch.RH.NymanTailTransform

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Exact full arithmetic head--tail accounting for the actual completion

Every spectral identity uses the proved transform of the concrete arithmetic
tail. The full explicit formula then identifies the actual arithmetic pairings
and quadratic values. No abstract null-channel hypothesis is left in the
final statements, and every zero retains its actual analytic multiplicity.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis
open scoped ComplexConjugate BigOperators

namespace RiemannResearch.RH

open SignedWeilCorrelation

private theorem completionTail_signature_on_actual_zeros
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    centeredTransform (nymanCompletionTail n M hn v) (ρ : ℂ) =
      -centeredTransform (poleCancellationOperator v) (ρ : ℂ) ∧
    centeredTransform (nymanCompletionTail n M hn v) (1 - conj (ρ : ℂ)) =
      -centeredTransform (poleCancellationOperator v) (1 - conj (ρ : ℂ)) := by
  have hρ : riemannZeta (ρ : ℂ) = 0 ∧ 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ρ.property
  have hr := Zeta23.zeta_reflect_zero ρ ρ.property
  have hne : (ρ : ℂ) ≠ 1 := by
    intro h
    have h1 := hρ.2.2
    rw [h] at h1
    norm_num at h1
  have hrne : (1 - conj (ρ : ℂ)) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith [hρ.2.1]
  exact ⟨centeredTransform_nymanCompletionTail_zeta_signature n M hn hv ha hb hne hρ.1,
    centeredTransform_nymanCompletionTail_zeta_signature n M hn hv ha hb hrne hr.1⟩

/-- The actual tail and compact head have the same full arithmetic quadratic
value, even though the tail can start beyond an arbitrarily large gap. -/
theorem infinitePrimePowerCorrelationValue_nymanCompletionTail_eq_head
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    infinitePrimePowerCorrelationValue
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
      (realAutocorrelation (nymanCompletionTail n M hn v)) =
    infinitePrimePowerCorrelationValue
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
      (realAutocorrelation (poleCancellationOperator v)) := by
  have ht := smoothSuperexponentialDecay_nymanCompletionTail n M hn hv ha hb
  have hf := (smoothSuperexponentialDecay_of_compact_interval hv ha hb).poleCancellationOperator
  have hp : arithmeticWeilPairing (nymanCompletionTail n M hn v) (nymanCompletionTail n M hn v) =
      arithmeticWeilPairing (poleCancellationOperator v) (poleCancellationOperator v) := by
    rw [arithmeticWeilPairing_eq_zero_sum ht ht, arithmeticWeilPairing_eq_zero_sum hf hf]
    apply tsum_congr
    intro ρ
    obtain ⟨hs, hr⟩ := completionTail_signature_on_actual_zeros n M hn hv ha hb ρ
    rw [hs, hr, map_neg]
    ring
  rw [arithmeticWeilPairing_self_eq ht, arithmeticWeilPairing_self_eq hf] at hp
  exact_mod_cast hp

/-- The complete mixed arithmetic pairing is the negative head value, with
the note's conjugate-linear-first-variable convention. -/
theorem arithmeticWeilPairing_head_nymanCompletionTail_eq_neg_head
    (n M : ℕ) (hn : 2 ≤ n) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    arithmeticWeilPairing (poleCancellationOperator v) (nymanCompletionTail n M hn v) =
      -(infinitePrimePowerCorrelationValue
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi))
        (realAutocorrelation (poleCancellationOperator v)) : ℂ) := by
  have ht := smoothSuperexponentialDecay_nymanCompletionTail n M hn hv ha hb
  have hf := (smoothSuperexponentialDecay_of_compact_interval hv ha hb).poleCancellationOperator
  rw [← arithmeticWeilPairing_self_eq hf, arithmeticWeilPairing_eq_zero_sum hf ht,
    arithmeticWeilPairing_eq_zero_sum hf hf, ← tsum_neg]
  apply tsum_congr
  intro ρ
  rw [(completionTail_signature_on_actual_zeros n M hn hv ha hb ρ).1]
  ring

end RiemannResearch.RH
