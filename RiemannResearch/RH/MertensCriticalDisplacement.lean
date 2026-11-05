/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensCriticalEstimate
import RiemannResearch.RH.MertensCriticalPairing
import RiemannResearch.RH.MertensBaezDuarteConverse
import RiemannResearch.RH.QHarmonicMomentComparison

/-!
# Displacement criteria at the critical second Lee–Leong coefficient

The forward implication uses Lee–Leong's explicit Mertens estimate
(arXiv:2208.06141v5, Theorem 1.1). Báez-Duarte's approximation under RH
(Rend. Lincei Mat. Appl. 14 (2003), Theorem 2) supplies the converse.
-/
noncomputable section
open Filter
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis ZetaTwoHilbert QSquarefreeDisplacementRigidity
open Pareto.BaezDuarte

/-- The critical leading and secondary rates with a free square-root coefficient. -/
def leeLeongCriticalExponent (t : ℝ) (n : ℕ) : ℝ :=
  leeLeongRate * vkProfile n + leeLeongSecondRate * vkSecondProfile n +
    t * Real.sqrt (vkProfile n)

/-- A pure harmonic first moment at the critical coefficient forces RH.
Every fixed nonnegative square-root correction may be included in the damping. -/
theorem riemannHypothesis_of_leeLeong_critical_moment
    (hLL : LeeLeongMertensEstimate) (t : ℝ) (ht : 0 ≤ t)
    (hd : Summable (fun n : ℕ => positiveQWeight n *
      ((n : ℝ) * Real.exp (-(leeLeongCriticalExponent t n))) * |qSequence displacement n|)) :
    RiemannHypothesis := by
  apply rh_of_zero_projection_residual
  apply residual_zero_of_critical_displacement_moment leeLeongRate leeLeongSecondRate t
    (Real.rpow_pos_of_pos (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _)
    leeLeongSecondRate_pos.le ht (mertens_critical_sqrt_of_leeLeong hLL (2 * (t + 2)))
  have hex (n : ℕ) : -(leeLeongCriticalExponent t n) =
      -leeLeongRate * vkProfile n - leeLeongSecondRate * vkSecondProfile n -
        t * Real.sqrt (vkProfile n) := by unfold leeLeongCriticalExponent; ring
  simpa only [hex] using hd

/-- The convergent critical moment is equivalent to RH under the two explicit
literature inputs. -/
theorem riemannHypothesis_iff_leeLeong_critical_moment
    (hLL : LeeLeongMertensEstimate) (hBD : BaezDuarteMobiusApproximation)
    (t : ℝ) (ht : 0 ≤ t) :
    RiemannHypothesis ↔ Summable (fun n : ℕ => positiveQWeight n *
      ((n : ℝ) * Real.exp (-(leeLeongCriticalExponent t n))) * |qSequence displacement n|) := by
  refine ⟨?_, riemannHypothesis_of_leeLeong_critical_moment hLL t ht⟩
  intro hRH
  rw [displacement_eq_zero_of_residual_eq_zero
    (residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH)]
  have hz (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by
    cases n <;> simp [qSequence]
  simp only [hz, abs_zero, mul_zero, summable_zero]

private theorem critical_exponent_gap {t s : ℝ} (hts : t < s) :
    ∀ᶠ n : ℕ in atTop, 2 * Real.log (Real.log (n : ℝ)) ≤
      leeLeongCriticalExponent s n - leeLeongCriticalExponent t n := by
  let c := (s - t) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (vkProfile_dominates_logLog_sq (c ^ 2) (sq_pos_of_pos hc)),
    hnat.eventually (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)))]
      with n hn hV
  have hl : Real.log (Real.log (n : ℝ)) ≤ c * Real.sqrt (vkProfile n) := by
    apply le_of_sq_le_sq _ (mul_nonneg hc.le (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hV] using hn
  dsimp only [leeLeongCriticalExponent]
  dsimp only [c] at hl
  linarith only [hl]

/-- Any fixed square-root growth coefficient is admissible at the exact
secondary coefficient. The multiplicative constant may be arbitrary. -/
theorem riemannHypothesis_of_leeLeong_critical_displacement
    (hLL : LeeLeongMertensEstimate) (t D : ℝ)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (leeLeongCriticalExponent t n)) : RiemannHypothesis := by
  let s := max t 0 + 1
  have hs : 0 ≤ s := by dsimp [s]; linarith only [le_max_right t 0]
  have hts : t < s := by dsimp [s]; linarith only [le_max_left t 0]
  exact riemannHypothesis_of_leeLeong_critical_moment hLL s hs
    (summable_harmonic_moment_of_exponent_gap _ _ _ D hd (critical_exponent_gap hts))

/-- Displacement can be uncontrolled on E when the squared damping factor
is summable there. The bound elsewhere may use any smaller square-root coefficient. -/
theorem riemannHypothesis_of_leeLeong_critical_displacement_off_exceptional
    (hLL : LeeLeongMertensEstimate) (t s D : ℝ) (hs : 0 ≤ s) (hts : t < s)
    (E : ℕ → Prop) [DecidablePred E]
    (hE : Summable (fun n : ℕ => if E n then
      (Real.exp (-(leeLeongCriticalExponent s n))) ^ 2 else 0))
    (hd : ∀ᶠ n : ℕ in atTop, ¬ E n → |qSequence displacement n| ≤
      D * Real.exp (leeLeongCriticalExponent t n)) : RiemannHypothesis := by
  exact riemannHypothesis_of_leeLeong_critical_moment hLL s hs
    (summable_harmonic_moment_of_exponent_gap_off_exceptional displacement _ _ D E hE hd
      (critical_exponent_gap hts))

end RiemannResearch.RH.QMertensFirstMoment
