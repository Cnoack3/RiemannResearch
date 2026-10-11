import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Higher-power perturbation bounds for zero sampling

This module isolates the scalar inequality used to transfer a complex Fourier
coefficient error into a balanced convolution error.  It requires no facts about
zeta zeros, zero density, or RH.  The proof uses midpoint convexity of natural
powers and the elementary difference-of-powers estimate from Mathlib.

These declarations are proof candidates pending the coordinating agent's
serialized Lean verification.
-/

namespace RiemannResearch.ZeroSampling

/-- Midpoint convexity with its exact power of two. -/
theorem add_pow_le_two_pow_pred {b e : ℝ} (hb : 0 ≤ b) (he : 0 ≤ e)
    (n : ℕ) (hn : 1 ≤ n) :
    (b + e) ^ n ≤ (2 : ℝ) ^ (n - 1) * (b ^ n + e ^ n) := by
  have hc : ((1 / 2 : ℝ) * b + (1 / 2 : ℝ) * e) ^ n ≤
      (1 / 2 : ℝ) * b ^ n + (1 / 2 : ℝ) * e ^ n := by
    simpa only [smul_eq_mul] using
      (convexOn_pow (𝕜 := ℝ) n).2 hb he
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hhalf : ((b + e) / 2) ^ n ≤ (b ^ n + e ^ n) / 2 := by
    rw [show (b + e) / 2 = (1 / 2 : ℝ) * b + (1 / 2 : ℝ) * e by ring,
      show (b ^ n + e ^ n) / 2 =
        (1 / 2 : ℝ) * b ^ n + (1 / 2 : ℝ) * e ^ n by ring]
    exact hc
  have hn' : n = (n - 1) + 1 := by omega
  have htwo : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) :=
        congrArg (fun k : ℕ => (2 : ℝ) ^ k) hn'
      _ = (2 : ℝ) ^ (n - 1) * 2 := pow_succ _ _
  calc
    (b + e) ^ n = (2 : ℝ) ^ n * ((b + e) / 2) ^ n := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ n * ((b ^ n + e ^ n) / 2) :=
      mul_le_mul_of_nonneg_left hhalf (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (n - 1) * (b ^ n + e ^ n) := by
      rw [htwo]
      ring

/-- Generic natural-power error transfer, retaining the sparse linear term and
the dense error power separately. -/
theorem higher_power_error_transfer {s b e : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b)
    (he : 0 ≤ e) (q : ℕ) (hq : 2 ≤ q) (herror : |s - b| ≤ e) :
    |s ^ q - b ^ q| ≤
      (q : ℝ) * (2 : ℝ) ^ (q - 2) * (b ^ (q - 1) * e + e ^ q) := by
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hsle : s ≤ b + e := by
    have hsub : s - b ≤ e := (le_abs_self (s - b)).trans herror
    linarith
  have hmax : max s b ≤ b + e :=
    max_le hsle (le_add_of_nonneg_right he)
  have hmax0 : 0 ≤ max s b := hs.trans (le_max_left _ _)
  have hpow : (max s b) ^ (q - 1) ≤ (b + e) ^ (q - 1) :=
    pow_le_pow_left₀ hmax0 hmax _
  have hpred : 1 ≤ q - 1 := by omega
  have hmiddle := add_pow_le_two_pow_pred hb he (q - 1) hpred
  have hsubpred : (q - 1) - 1 = q - 2 := by omega
  rw [hsubpred] at hmiddle
  have hepow : e ^ q = e ^ (q - 1) * e := by
    calc
      e ^ q = e ^ ((q - 1) + 1) := by congr 1; omega
      _ = e ^ (q - 1) * e := pow_succ _ _
  calc
    |s ^ q - b ^ q| ≤ |s - b| * (q : ℝ) * (max s b) ^ (q - 1) := by
      simpa only [abs_of_nonneg hs, abs_of_nonneg hb] using
        (abs_pow_sub_pow_le s b q)
    _ ≤ e * (q : ℝ) * (b + e) ^ (q - 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_right herror hq0) hpow
        (pow_nonneg hmax0 _) (mul_nonneg he hq0)
    _ ≤ e * (q : ℝ) *
        ((2 : ℝ) ^ (q - 2) * (b ^ (q - 1) + e ^ (q - 1))) :=
      mul_le_mul_of_nonneg_left hmiddle (mul_nonneg he hq0)
    _ = (q : ℝ) * (2 : ℝ) ^ (q - 2) *
        (b ^ (q - 1) * e + e ^ q) := by
      rw [hepow]
      ring

/-- Balanced even powers are a direct specialization; `r` is fixed but any
positive order is allowed. -/
theorem balanced_even_power_error_transfer {s b e : ℝ}
    (hs : 0 ≤ s) (hb : 0 ≤ b) (he : 0 ≤ e) (r : ℕ) (hr : 1 ≤ r)
    (herror : |s - b| ≤ e) :
    |s ^ (2 * r) - b ^ (2 * r)| ≤
      ((2 * r : ℕ) : ℝ) * (2 : ℝ) ^ (2 * r - 2) *
        (b ^ (2 * r - 1) * e + e ^ (2 * r)) :=
  higher_power_error_transfer hs hb he (2 * r) (by omega) herror

/-- The normed-group interface includes complex Fourier amplitudes without
imposing a sign on the arithmetic main coefficient. -/
theorem norm_higher_power_error_transfer {E : Type*} [SeminormedAddCommGroup E]
    (s b : E) {e : ℝ} (he : 0 ≤ e) (q : ℕ) (hq : 2 ≤ q)
    (herror : ‖s - b‖ ≤ e) :
    |‖s‖ ^ q - ‖b‖ ^ q| ≤
      (q : ℝ) * (2 : ℝ) ^ (q - 2) * (‖b‖ ^ (q - 1) * e + e ^ q) :=
  higher_power_error_transfer (norm_nonneg s) (norm_nonneg b) he q hq
    ((abs_norm_sub_norm_le s b).trans herror)

end RiemannResearch.ZeroSampling
