/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensFullEnvelope
import RiemannResearch.RH.MertensFullProfile
import RiemannResearch.RH.MertensExponentialCutoffPairing
import RiemannResearch.RH.MertensVKFirstMoment
import RiemannResearch.RH.MertensBaezDuarteConverse
import RiemannResearch.RH.QHarmonicMomentComparison

/-!
# First moments at the full Lee–Leong exponent

Lee and Leong, arXiv:2208.06141v5, Theorem 1.1, supply the explicit Mertens
estimate. We transfer the full printed exponent with an arbitrarily small
square-root loss. Báez-Duarte's explicit Möbius approximation under RH
(Rend. Lincei Mat. Appl. 14 (2003), Theorem 2) supplies the converse.
-/

noncomputable section
open Filter
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis ZetaTwoHilbert QSquarefreeDisplacementRigidity
open Pareto.BaezDuarte

/-- The full printed exponent less a square-root margin. -/
def leeLeongFullDisplacementExponent (δ x : ℝ) : ℝ :=
  leeLeongFullProfile x - δ * Real.sqrt (vkProfile x)

private theorem neg_full_displacement_exponent (δ x : ℝ) :
    -(leeLeongFullDisplacementExponent δ x) =
      -leeLeongFullProfile x + δ * Real.sqrt (vkProfile x) := by
  unfold leeLeongFullDisplacementExponent
  ring

private theorem full_displacement_exponent_lower (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ᶠ x : ℝ in atTop, (leeLeongRate / 2) * vkProfile x ≤
      leeLeongFullDisplacementExponent δ x := by
  have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos
    (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _
  have hc : 0 < leeLeongRate / 2 := by positivity
  filter_upwards [leeLeongFullProfile_eventually_bounds, vkProfile_tendsto_atTop.eventually
    (eventually_ge_atTop ((δ / (leeLeongRate / 2)) ^ 2))] with x hx hv
  have hV : 0 ≤ vkProfile x := (sq_nonneg _).trans hv
  have hs := Real.sqrt_le_sqrt hv
  rw [Real.sqrt_sq (div_nonneg hδ hc.le)] at hs
  have hδ' : δ ≤ (leeLeongRate / 2) * Real.sqrt (vkProfile x) := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hs
  have hq := mul_le_mul_of_nonneg_right hδ' (Real.sqrt_nonneg (vkProfile x))
  rw [mul_assoc, ← pow_two, Real.sq_sqrt hV] at hq
  unfold leeLeongFullDisplacementExponent
  linarith only [hx.1, hq]

/-- A single absolute displacement moment at the full profile with any
positive square-root loss implies vanishing of the squarefree residual. -/
theorem residual_zero_of_leeLeong_full_moment (hLL : LeeLeongMertensEstimate)
    (δ : ℝ) (hδ : 0 < δ)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-(leeLeongFullDisplacementExponent δ n))) * |qSequence displacement n|)) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos
    (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _
  have hc : 0 < leeLeongRate / 2 := by positivity
  have hquarter : 0 < δ / 4 := by positivity
  let E (x : ℝ) := -(leeLeongFullDisplacementExponent (δ / 4) x)
  let W (n : ℕ) := (n : ℝ) * Real.exp (-(leeLeongFullDisplacementExponent δ n))
  refine residual_zero_of_exponential_cutoff_moment E W ?_ ?_ ?_ ?_ ?_ hd
  · apply tendsto_atBot.2
    intro B
    filter_upwards [full_displacement_exponent_lower (δ / 4) hquarter.le,
      (Tendsto.const_mul_atTop hc vkProfile_tendsto_atTop).eventually
        (eventually_ge_atTop (-B))] with x h1 h2
    change -B ≤ (leeLeongRate / 2) * vkProfile x at h2
    change -(leeLeongFullDisplacementExponent (δ / 4) x) ≤ B
    linarith only [h2, h1]
  · filter_upwards [leeLeongFullProfile_sub_sqrt_eventually_mono (δ / 4)] with x hx y hxy
    exact neg_le_neg (hx y hxy)
  · simpa only [E, neg_full_displacement_exponent] using
      mertens_fullProfile_of_leeLeong hLL (δ / 4) hquarter
  · simpa only [E, W, neg_full_displacement_exponent] using
      errorEnvelope_eventually_le_leeLeong_full δ hδ
  · apply (summable_vk_first_moment_constant (leeLeongRate / 2) hc).of_norm_bounded_eventually_nat
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hnat.eventually (full_displacement_exponent_lower δ hδ.le)] with n hn
    dsimp only [W]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (positiveQWeight_nonneg n)
      (mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le))]
    apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    exact Real.exp_le_exp.mpr (by linarith only [hn])

/-- The full-profile moment suffices for Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_leeLeong_full_moment (hLL : LeeLeongMertensEstimate)
    (δ : ℝ) (hδ : 0 < δ)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-(leeLeongFullDisplacementExponent δ n))) * |qSequence displacement n|)) :
    RiemannHypothesis :=
  rh_of_zero_projection_residual (residual_zero_of_leeLeong_full_moment hLL δ hδ hd)

/-- Under the stated literature inputs, each fixed full-profile absolute
displacement moment with a positive square-root loss is equivalent to RH. -/
theorem riemannHypothesis_iff_leeLeong_full_moment
    (hLL : LeeLeongMertensEstimate) (hBD : BaezDuarteMobiusApproximation)
    (δ : ℝ) (hδ : 0 < δ) :
    RiemannHypothesis ↔ Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-(leeLeongFullDisplacementExponent δ n))) * |qSequence displacement n|) := by
  refine ⟨?_, riemannHypothesis_of_leeLeong_full_moment hLL δ hδ⟩
  intro hRH
  rw [displacement_eq_zero_of_residual_eq_zero
    (residual_zero_of_baezDuarte_and_riemannHypothesis hBD hRH)]
  have hz (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by
    cases n <;> simp [qSequence]
  simp only [hz, abs_zero, mul_zero, summable_zero]

private theorem full_exponent_gap {δ η : ℝ} (hηδ : η < δ) :
    ∀ᶠ n : ℕ in atTop, 2 * Real.log (Real.log (n : ℝ)) ≤
      leeLeongFullDisplacementExponent η n - leeLeongFullDisplacementExponent δ n := by
  let c := (δ - η) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (vkProfile_dominates_logLog_sq (c ^ 2) (sq_pos_of_pos hc)),
    hnat.eventually (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)))]
      with n hn hV
  have hl : Real.log (Real.log (n : ℝ)) ≤ c * Real.sqrt (vkProfile n) := by
    apply le_of_sq_le_sq _ (mul_nonneg hc.le (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hV] using hn
  dsimp only [leeLeongFullDisplacementExponent]
  dsimp only [c] at hl
  linarith only [hl]

/-- Pointwise growth with any fixed positive square-root margin below the
full variable-coefficient Mertens exponent implies RH. -/
theorem riemannHypothesis_of_leeLeong_full_displacement
    (hLL : LeeLeongMertensEstimate) (δ D : ℝ) (hδ : 0 < δ)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (leeLeongFullDisplacementExponent δ n)) : RiemannHypothesis :=
  riemannHypothesis_of_leeLeong_full_moment hLL (δ / 2) (by positivity)
    (summable_harmonic_moment_of_exponent_gap _ _ _ D hd
      (full_exponent_gap (show δ / 2 < δ by linarith)))

/-- Growth control is needed only off E if the squared exponential damping
is summable on E at an intermediate margin. -/
theorem riemannHypothesis_of_leeLeong_full_displacement_off_exceptional
    (hLL : LeeLeongMertensEstimate) (δ η D : ℝ) (hη : 0 < η) (hηδ : η < δ)
    (E : ℕ → Prop) [DecidablePred E]
    (hE : Summable (fun n : ℕ => if E n then
      (Real.exp (-(leeLeongFullDisplacementExponent η n))) ^ 2 else 0))
    (hd : ∀ᶠ n : ℕ in atTop, ¬ E n → |qSequence displacement n| ≤
      D * Real.exp (leeLeongFullDisplacementExponent δ n)) : RiemannHypothesis := by
  exact riemannHypothesis_of_leeLeong_full_moment hLL η hη
    (summable_harmonic_moment_of_exponent_gap_off_exceptional displacement _ _ D E hE hd
      (full_exponent_gap hηδ))

end RiemannResearch.RH.QMertensFirstMoment
