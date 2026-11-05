/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensFullEnvelope
import RiemannResearch.RH.MertensExponentialCutoffPairing
import RiemannResearch.RH.MertensVKFirstMoment
import RiemannResearch.RH.QHarmonicMomentComparison

/-!
# An endpoint transfer using the implicit Lee–Leong truncation

The arithmetic hypothesis below is a consequence on paper of E. S. Lee and
N. Leong, arXiv:2208.06141v5, Proposition 5.2, (60), (62), and Section 5.4.
It refers to their implicit truncation before the last estimate in Theorem
1.1. The Lean statement keeps this external analytic input explicit.
-/
noncomputable section
open Filter
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert QSquarefreeDisplacementRigidity

/-- Every fixed multiple of the square-root scale can be saved relative to
the printed full exponent, using the implicit truncation of Proposition 5.2. -/
def LeeLeongTruncationReserve : Prop :=
  ∀ k : ℝ, ∀ᶠ x : ℝ in atTop, |M x| ≤
    Real.exp (-leeLeongFullProfile x - k * Real.sqrt (vkProfile x)) * x

private theorem sqrt_increment_le {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    Real.sqrt q - Real.sqrt p ≤ q - p := by
  have hp0 : 0 ≤ p := by linarith
  have hs : 1 ≤ Real.sqrt p := by
    simpa using Real.sqrt_le_sqrt hp
  have hd := sub_nonneg.mpr (Real.sqrt_le_sqrt hpq)
  have ht : 0 ≤ Real.sqrt q + Real.sqrt p - 1 := by
    linarith only [hs, Real.sqrt_nonneg q]
  nlinarith only [mul_nonneg hd ht, Real.sq_sqrt hp0, Real.sq_sqrt (hp0.trans hpq)]

/-- An absolute first moment at the printed endpoint, or above it by any
fixed nonnegative multiple of the square-root scale, suffices under the
arithmetic bound obtained from the implicit truncation. -/
theorem riemannHypothesis_of_truncationReserve_moment (hM : LeeLeongTruncationReserve)
    (a : ℝ) (ha : 0 ≤ a)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-(leeLeongFullProfile n + a * Real.sqrt (vkProfile n)))) *
      |qSequence displacement n|)) : RiemannHypothesis := by
  let G (x : ℝ) := leeLeongFullProfile x + (a + 1) * Real.sqrt (vkProfile x)
  let E (x : ℝ) := -leeLeongFullProfile x - (a + 3/4) * Real.sqrt (vkProfile x)
  let W (n : ℕ) := (n : ℝ) * Real.exp (-(leeLeongFullProfile n + a * Real.sqrt (vkProfile n)))
  let C := 2 * leeLeongRate + (a + 1)
  have hA : 0 < leeLeongRate := by unfold leeLeongRate; positivity
  have ha1 : 0 ≤ a + 1 := by linarith
  have hc : 0 < C := by dsimp [C]; linarith
  have hbound : ∀ᶠ x : ℝ in atTop, G x ≤ C * vkProfile x := by
    filter_upwards [leeLeongFullProfile_eventually_bounds,
      vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hv
    have hs : Real.sqrt (vkProfile x) ≤ vkProfile x := by
      simpa using sqrt_increment_le (p := 1) (q := vkProfile x) le_rfl hv
    dsimp only [G, C]
    linarith only [hx.2, mul_le_mul_of_nonneg_left hs ha1]
  have hinc : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      G y - G x ≤ C * (vkProfile y - vkProfile x) := by
    filter_upwards [leeLeongFullProfile_eventually_increment, vkProfile_eventually_mono,
      vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hm hv y hxy
    dsimp only [G, C]
    linarith only [hx y hxy, mul_le_mul_of_nonneg_left (sqrt_increment_le hv (hm y hxy)) ha1]
  obtain ⟨K, hK, hb⟩ := errorEnvelope_eventually_le_full_profile_of_increment
    G C 1 hc (by norm_num) hbound hinc
  apply rh_of_zero_projection_residual
  refine residual_zero_of_exponential_cutoff_moment E W ?_ ?_ (hM (a + 3/4)) ?_ ?_ hd
  · apply tendsto_atBot.2
    intro B
    filter_upwards [leeLeongFullProfile_eventually_bounds,
      (Tendsto.const_mul_atTop hA vkProfile_tendsto_atTop).eventually
        (eventually_ge_atTop (-B))] with x hx ht
    change -B ≤ leeLeongRate * vkProfile x at ht
    dsimp only [E]
    linarith only [hx.1, ht,
      mul_nonneg (show 0 ≤ a + 3/4 by linarith) (Real.sqrt_nonneg (vkProfile x))]
  · filter_upwards [leeLeongFullProfile_sub_sqrt_eventually_mono (-(a + 3/4))] with x hx y hxy
    dsimp only [E]
    linarith only [hx y hxy]
  · refine ⟨K, hK, ?_⟩
    filter_upwards [hb] with N h n
    have hleft : -G N + 1 / 4 * Real.sqrt (vkProfile N) = E N := by dsimp [G, E]; ring
    have hright : -G n + 1 * Real.sqrt (vkProfile n) =
        -(leeLeongFullProfile n + a * Real.sqrt (vkProfile n)) := by dsimp [G]; ring
    simpa only [W, hleft, hright] using h n
  · apply (summable_vk_first_moment_constant leeLeongRate hA).of_norm_bounded_eventually_nat
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hnat.eventually leeLeongFullProfile_eventually_bounds] with n hn
    dsimp only [W]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (positiveQWeight_nonneg n)
      (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le))]
    apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    exact Real.exp_le_exp.mpr (by
      linarith only [hn.1, mul_nonneg ha (Real.sqrt_nonneg (vkProfile n))])

/-- Relative to the printed Lee–Leong exponent, the pointwise criterion
admits every fixed signed square-root correction. -/
theorem riemannHypothesis_of_truncationReserve_pointwise (hM : LeeLeongTruncationReserve)
    (a D : ℝ) (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤ D *
      Real.exp (leeLeongFullProfile n + a * Real.sqrt (vkProfile n))) : RiemannHypothesis := by
  let b := max a 0 + 1
  have hb : 0 ≤ b := by dsimp [b]; linarith only [le_max_right a 0]
  apply riemannHypothesis_of_truncationReserve_moment hM b hb
  refine summable_harmonic_moment_of_exponent_gap _ _ _ D hd ?_
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (vkProfile_dominates_logLog_sq ((1/2 : ℝ)^2) (by norm_num)),
    hnat.eventually (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)))]
    with n hn hv
  have hl : Real.log (Real.log (n : ℝ)) ≤ (1/2 : ℝ) * Real.sqrt (vkProfile n) := by
    apply le_of_sq_le_sq _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hv] using hn
  dsimp only [b]
  linarith only [hl, mul_le_mul_of_nonneg_right (le_max_left a 0) (Real.sqrt_nonneg (vkProfile n))]

end RiemannResearch.RH.QMertensFirstMoment
