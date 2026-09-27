/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Ordered power damping from signed vector prefixes

The only norms here are taken AFTER the signed vectors have been added.
The conclusion is convergence of naturally ordered partial sums. It does
not assert unconditional summability of the original vector series.

The power-growth application is a conditional analytic transfer theorem:
an arithmetic provider of the signed-prefix growth premise is separate.
The proof uses Mathlib's `Finset.sum_range_by_parts`, the mean-value
derivative bound, and the real p-series criterion. This is standard Abel
summation applied to vector prefixes; no mathematical novelty is claimed.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def signedVectorPrefix (u : ℕ → E) (N : ℕ) : E :=
  ∑ n ∈ Finset.range N, u n

/-- Exact finite Abel transformation retaining the complete signed prefix. -/
theorem signedVector_power_weight_identity (w : ℕ → ℝ) (u : ℕ → E) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), w n • u n) =
      w N • signedVectorPrefix u (N + 1) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) • signedVectorPrefix u (n + 1) := by
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel, signedVectorPrefix]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [← neg_smul, neg_sub]

variable [CompleteSpace E]

/-- The primitive variation may be absolutely summable although the
original arithmetic vector series is only convergent in its natural order. -/
theorem signedVector_weighted_partial_tendsto
    (w : ℕ → ℝ) (u : ℕ → E)
    (hvariation : Summable (fun n =>
      |w n - w (n + 1)| * ‖signedVectorPrefix u (n + 1)‖))
    (hboundary : Tendsto (fun N => w N • signedVectorPrefix u (N + 1))
      atTop (𝓝 0)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, w n • u n) atTop
      (𝓝 (∑' n, (w n - w (n + 1)) • signedVectorPrefix u (n + 1))) := by
  have hs : Summable (fun n => (w n - w (n + 1)) •
      signedVectorPrefix u (n + 1)) := by
    apply Summable.of_norm
    simpa only [norm_smul, Real.norm_eq_abs] using hvariation
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [signedVector_power_weight_identity, zero_add] using
    hboundary.add hs.hasSum.tendsto_sum_nat

/-- A precise variation estimate for the power weights, proved from the
derivative on the unit interval. -/
theorem abs_power_damping_step_le {ε : ℝ} (hε : 0 ≤ ε)
    {x : ℝ} (hx : 0 < x) :
    |x ^ (-ε) - (x + 1) ^ (-ε)| ≤ ε * x ^ (-ε - 1) := by
  have hd : ∀ y ∈ Icc x (x + 1),
      HasDerivWithinAt (fun t : ℝ => t ^ (-ε))
        ((-ε) * y ^ (-ε - 1)) (Icc x (x + 1)) y := by
    intro y hy
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hx.trans_le hy.1)))).hasDerivWithinAt
  have hb : ∀ y ∈ Ico x (x + 1),
      ‖(-ε) * y ^ (-ε - 1)‖ ≤ ε * x ^ (-ε - 1) := by
    intro y hy
    rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hε,
      Real.norm_of_nonneg (Real.rpow_nonneg (hx.trans_le hy.1).le _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx hy.1 (by linarith)) hε
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (x + 1)
    (show x + 1 ∈ Icc x (x + 1) by constructor <;> linarith)
  simpa only [Real.norm_eq_abs, add_sub_cancel_left, mul_one, abs_sub_comm] using h

/-- A signed prefix norm bound of exponent θ transfers to ordered power
damping at every ε > max(θ,0). The cancellation premise is inside the norm
of the full prefix, before any squaring or termwise absolute bound. -/
theorem signedVector_power_damped_tendsto_of_prefix_growth
    (u : ℕ → E) {C θ ε : ℝ} (_hC : 0 ≤ C) (hε : 0 < ε) (hθε : θ < ε)
    (hgrowth : ∀ n : ℕ,
      ‖signedVectorPrefix u (n + 1)‖ ≤ C * ((n + 1 : ℕ) : ℝ) ^ θ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      ((n + 1 : ℕ) : ℝ) ^ (-ε) • u n) atTop
      (𝓝 (∑' n, ((((n + 1 : ℕ) : ℝ) ^ (-ε)) -
        (((n + 2 : ℕ) : ℝ) ^ (-ε))) • signedVectorPrefix u (n + 1))) := by
  apply signedVector_weighted_partial_tendsto
  · have hp : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (θ - ε - 1)) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
    apply (hp.mul_left (ε * C)).of_nonneg_of_le
    · intro n
      exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
    · intro n
      have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hstep := abs_power_damping_step_le hε.le hx
      have hcast : (((n + 1 : ℕ) : ℝ) + 1) = ((n + 2 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast] at hstep
      calc
        _ ≤ (ε * ((n + 1 : ℕ) : ℝ) ^ (-ε - 1)) *
            (C * ((n + 1 : ℕ) : ℝ) ^ θ) :=
          mul_le_mul hstep (hgrowth n) (norm_nonneg _) (by positivity)
        _ = ε * C * ((n + 1 : ℕ) : ℝ) ^ (θ - ε - 1) := by
          rw [mul_mul_mul_comm, ← Real.rpow_add hx]
          congr 2
          ring
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hxlim : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hpow : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (θ - ε)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, show -(ε - θ) = θ - ε by ring] using
        (tendsto_rpow_neg_atTop (show 0 < ε - θ by linarith)).comp hxlim
    have hlim : Tendsto (fun n : ℕ => C * ((n + 1 : ℕ) : ℝ) ^ (θ - ε))
        atTop (𝓝 0) := by simpa using hpow.const_mul C
    apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
    intro n
    have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (-ε) *
          (C * ((n + 1 : ℕ) : ℝ) ^ θ) :=
        mul_le_mul_of_nonneg_left (hgrowth n) (Real.rpow_nonneg hx.le _)
      _ = C * ((n + 1 : ℕ) : ℝ) ^ (θ - ε) := by
        rw [← mul_assoc, mul_comm _ C, mul_assoc, ← Real.rpow_add hx]
        congr 2
        ring

end RiemannResearch.Analysis
