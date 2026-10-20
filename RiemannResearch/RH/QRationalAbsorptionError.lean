/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalSignedTailRatio
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QRationalSignedTailLimit
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The necessary additive error in signed absorption

Source: user-directed continuation of the 20 October 2026 CRT research agenda.
The unconditional signed ratio identifies the exact scale of every possible
absorption error. It rules out errors negligible relative to the actual minimum;
it does not rule out an absolute error tending to zero. Constant closure remains open.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoHilbert ZetaTwoProbability
open Pareto.SquarefreeStageExhaustion

/-- The exact least real additive error for a given signed absorption factor.
This quantity need not be nonnegative at small periods. -/
def rationalAbsorptionError (L : ℕ) (θ : ℝ) : ℝ :=
  -rationalSignedTail L - θ * rationalMinimum L

theorem rationalAbsorptionError_exact (L : ℕ) (hL : 0 < L) (θ : ℝ) :
    rationalAbsorptionError L θ = (1 - θ) * rationalMinimum L -
      5 * (Nat.totient L : ℝ) / (3 * (L : ℝ)^2) := by
  have h := rationalMinimum_signedTail_exact L hL
  unfold rationalAbsorptionError
  linarith

theorem signed_absorption_iff_error (L : ℕ) (θ ε : ℝ) :
    -θ * rationalMinimum L - ε ≤ rationalSignedTail L ↔
      rationalAbsorptionError L θ ≤ ε := by
  unfold rationalAbsorptionError
  constructor <;> intro h <;> linarith

theorem rationalAbsorptionError_div_exact (n : ℕ) (θ : ℝ) :
    rationalAbsorptionError (primorialPeriod n) θ /
        rationalMinimum (primorialPeriod n) =
      -(rationalSignedTail (primorialPeriod n) /
        rationalMinimum (primorialPeriod n)) - θ := by
  unfold rationalAbsorptionError
  field_simp [ne_of_gt (rationalMinimum_primorial_pos n)]

/-- The required error is asymptotic to `(1-theta)` times the actual minimum,
without assuming a positive limiting defect or RH. -/
theorem rationalAbsorptionError_div_tendsto (θ : ℝ) :
    Tendsto (fun n => rationalAbsorptionError (primorialPeriod n) θ /
      rationalMinimum (primorialPeriod n)) atTop (𝓝 (1 - θ)) := by
  simp only [rationalAbsorptionError_div_exact]
  simpa using rationalSignedTail_div_minimum_tendsto_unconditional.neg.sub_const θ

theorem rationalAbsorptionError_tendsto (θ : ℝ) :
    Tendsto (fun n => rationalAbsorptionError (primorialPeriod n) θ) atTop
      (𝓝 ((1 - θ) * (zetaTwo * ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2))) := by
  have h := (rationalMinimum_tendsto.const_mul (1 - θ)).sub
    rationalCoprimeBoundary_tendsto_zero
  simpa only [rationalAbsorptionError_exact _ (primorialPeriod_pos _), sub_zero] using h

/-- Every valid budget eventually pays any fixed fraction below `1-theta`
of the minimum. This pointwise implication also applies on arbitrary cofinal sets. -/
theorem signed_absorption_eventually_requires_relative_error (θ c : ℝ)
    (hc : c < 1 - θ) :
    ∀ᶠ n in atTop, ∀ ε : ℝ,
      -θ * rationalMinimum (primorialPeriod n) - ε ≤
        rationalSignedTail (primorialPeriod n) →
      c < ε / rationalMinimum (primorialPeriod n) := by
  have h := (tendsto_order.mp (rationalAbsorptionError_div_tendsto θ)).1 c hc
  filter_upwards [h] with n hn
  intro ε hε
  exact hn.trans_le ((div_le_div_iff_of_pos_right
    (rationalMinimum_primorial_pos n)).mpr
      ((signed_absorption_iff_error _ θ ε).mp hε))

/-- An error that is little-o of the actual minimum cannot supply absorption,
even along a cofinal subsequence. -/
theorem signed_absorption_eventually_fails_of_relative_error_zero
    (θ : ℝ) (hθ : θ < 1) (ε : ℕ → ℝ)
    (hε : Tendsto (fun n => ε n / rationalMinimum (primorialPeriod n))
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, rationalSignedTail (primorialPeriod n) <
      -θ * rationalMinimum (primorialPeriod n) - ε n := by
  have h := hε.eventually_lt (rationalAbsorptionError_div_tendsto θ)
    (by linarith : 0 < 1 - θ)
  filter_upwards [h] with n hn
  have he := (div_lt_div_iff_of_pos_right (rationalMinimum_primorial_pos n)).mp hn
  unfold rationalAbsorptionError at he
  linarith

theorem not_cofinal_signed_absorption_of_relative_error_zero
    (θ : ℝ) (hθ : θ < 1) (ε : ℕ → ℝ)
    (hε : Tendsto (fun n => ε n / rationalMinimum (primorialPeriod n))
      atTop (𝓝 0)) :
    ¬ (∀ N : ℕ, ∃ n, N ≤ n ∧
      -θ * rationalMinimum (primorialPeriod n) - ε n ≤
        rationalSignedTail (primorialPeriod n)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (signed_absorption_eventually_fails_of_relative_error_zero θ hθ ε hε)
  intro h
  obtain ⟨n, hn, hb⟩ := h N
  exact (not_lt_of_ge hb) (hN n hn)

/-- Any fixed multiple of the explicit arithmetic endpoint is too small
to repair fixed-factor absorption at all sufficiently large stages. -/
theorem signed_absorption_eventually_fails_with_boundary_error
    (θ : ℝ) (hθ : θ < 1) (C : ℝ) :
    ∀ᶠ n in atTop, rationalSignedTail (primorialPeriod n) <
      -θ * rationalMinimum (primorialPeriod n) -
        C * (5 * (Nat.totient (primorialPeriod n) : ℝ) /
          (3 * (primorialPeriod n : ℝ)^2)) := by
  apply signed_absorption_eventually_fails_of_relative_error_zero θ hθ
  have h := (rationalSignedTail_div_minimum_tendsto_unconditional.add_const 1).const_mul C
  simp only [neg_add_cancel, mul_zero] at h
  convert h using 1
  funext n
  rw [rationalSignedTail_ratio_exact, mul_div_assoc]

end RiemannResearch.RH.QRationalCoprimeTail
