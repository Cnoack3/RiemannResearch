/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.CoshTaylorRemainder
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import RiemannResearch.Analysis.ActualZeroTailDensityTransfer
import RiemannResearch.Analysis.ActualZeroFMZComparison
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Controlled horizontal-moment remainder for actual zeta-zero phases

All zeros and multiplicities are those of the actual Riemann zeta function.
Reflection gives the exact finite Taylor decomposition at every order before
any norm is taken. A positive comparison frequency then bounds the remainder.

The strategy extends the weight-removal comparison of Ford--Zaharescu,
Lemma 2, https://ford126.web.illinois.edu/wwwpapers/fz.pdf, and
Ford--Meng--Zaharescu, https://ford126.web.illinois.edu/wwwpapers/FMZ.pdf.
The higher-order deduction here uses the elementary cosh tail; no novelty
claim is made. Concrete RH consumer: prime-phase Fourier tests with retained
horizontal moments, which phase equidistribution alone cannot determine.

The exact identities need no density hypothesis. The quantitative conclusions
are conditional research reductions with an explicit SelbergDensityBound
input. Its classical mathematical theorem is unconditional, but the project
does not yet contain a checked provider. No RH hypothesis is introduced.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- Even horizontal moments of the actual zeros, with their ordinate phases. -/
def evenHorizontalMoment (T u : ℝ) (j : ℕ) : ℂ :=
  sum T (fun ρ => phase u ρ.im * ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ (2 * j))

/-- The exact finite Taylor head in the reflected Landau sum. -/
def horizontalTaylorPolynomial (T u : ℝ) (J : ℕ) : ℂ :=
  sum T (fun ρ => phase u ρ.im *
    (Real.coshTaylorHead J (u * (ρ.re - 1 / 2)) : ℂ))

/-- The signed remainder; the Taylor head is subtracted from the Landau sum
only after all even horizontal moments have been retained. -/
def horizontalTaylorError (T u : ℝ) (J : ℕ) : ℂ :=
  horizontalTaylorPolynomial T u J - landauSum T u

theorem evenHorizontalMoment_zero (T u : ℝ) :
    evenHorizontalMoment T u 0 = ordinateSum T u := by
  simp [evenHorizontalMoment, ordinateSum]

theorem horizontalTaylorPolynomial_eq_moments (T u : ℝ) (J : ℕ) :
    horizontalTaylorPolynomial T u J =
      ∑ j ∈ Finset.range (J + 1),
        ((u : ℂ) ^ (2 * j) / (Nat.factorial (2 * j) : ℂ)) *
          evenHorizontalMoment T u j := by
  unfold horizontalTaylorPolynomial Real.coshTaylorHead evenHorizontalMoment sum
  simp_rw [Complex.ofReal_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Real.coshTaylorTerm, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_natCast, mul_pow]
  ring

/-- Exact signed all-orders reflection identity, with no density assumption. -/
theorem horizontalTaylorError_eq_remainder (T u : ℝ) (J : ℕ) :
    horizontalTaylorError T u J =
      -sum T (fun ρ => phase u ρ.im *
        (Real.coshTaylorRemainder J (u * (ρ.re - 1 / 2)) : ℂ)) := by
  unfold horizontalTaylorError horizontalTaylorPolynomial
  rw [landauSum_eq_cosh, ← sum_sub]
  simp only [Real.coshTaylorRemainder, Complex.ofReal_sub, sum, mul_sub,
    Finset.sum_sub_distrib]
  ring

theorem horizontalTaylorError_one (T u : ℝ) :
    horizontalTaylorError T u 1 =
      ordinateSum T u - landauSum T u +
        ((u : ℂ) ^ 2 / 2) * evenHorizontalMoment T u 1 := by
  rw [horizontalTaylorError, horizontalTaylorPolynomial_eq_moments]
  norm_num [Finset.sum_range_succ, evenHorizontalMoment_zero]
  ring

theorem horizontalTaylorError_norm_le (T u : ℝ) (J : ℕ) :
    ‖horizontalTaylorError T u J‖ ≤
      realSum T (fun ρ => Real.coshTaylorRemainder J (u * (ρ.re - 1 / 2))) := by
  rw [horizontalTaylorError_eq_remainder, norm_neg]
  calc
    _ ≤ realSum T (fun ρ => ‖phase u ρ.im *
        (Real.coshTaylorRemainder J (u * (ρ.re - 1 / 2)) : ℂ)‖) := norm_sum_le _ _
    _ = _ := by
      congr 1
      funext ρ
      rw [norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.coshTaylorRemainder_nonneg _ _)]

/-- An arbitrary positive comparison frequency controls every Taylor order. -/
theorem horizontalTaylorError_le_coshSum
    (T u v : ℝ) (J : ℕ) (hv : 0 < v) (hu : |u| ≤ v) :
    ‖horizontalTaylorError T u J‖ ≤
      (|u| / v) ^ (2 * (J + 1)) *
        badWeightedSum T 0 (fun t => Real.cosh (v * t) - 1) := by
  apply (horizontalTaylorError_norm_le T u J).trans
  rw [badWeightedSum_eq_realSum]
  have hb (ρ : ℂ) :
      Real.coshTaylorRemainder J (u * (ρ.re - 1 / 2)) ≤
        (if 0 < |ρ.re - 1 / 2| then Real.cosh (v * |ρ.re - 1 / 2|) - 1 else 0) *
          (|u| / v) ^ (2 * (J + 1)) := by
    by_cases ha : ρ.re - 1 / 2 = 0
    · simp only [ha, mul_zero, abs_zero, lt_self_iff_false, if_false, zero_mul,
        Real.coshTaylorRemainder_zero, le_refl]
    · rw [if_pos (abs_pos.mpr ha)]
      have he : Real.coshTaylorRemainder J (u * (ρ.re - 1 / 2)) =
          Real.coshTaylorRemainder J (u * |ρ.re - 1 / 2|) := by
        rw [← Real.coshTaylorRemainder_abs J (u * (ρ.re - 1 / 2)),
          ← Real.coshTaylorRemainder_abs J (u * |ρ.re - 1 / 2|)]
        simp only [abs_mul, abs_abs]
      rw [he]
      simpa only [mul_comm] using
        Real.coshTaylorRemainder_frequency_le J u v _ hv hu (abs_nonneg (ρ.re - 1 / 2))
  calc
    _ ≤ realSum T (fun ρ =>
        (if 0 < |ρ.re - 1 / 2| then Real.cosh (v * |ρ.re - 1 / 2|) - 1 else 0) *
          (|u| / v) ^ (2 * (J + 1))) := realSum_mono T _ _ (fun ρ _ => hb ρ)
    _ = _ := by rw [realSum_mul_const, mul_comm]

/-- Uniform all-orders estimate from the actual strict-tail exponential bound. -/
theorem horizontalTaylorError_of_expTail
    (T u v K q : ℝ) (J : ℕ) (hv : 0 < v) (hu : |u| ≤ v)
    (hK : 0 ≤ K) (hvq : v < q)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T t ≤ K * Real.exp (-q * t)) :
    ‖horizontalTaylorError T u J‖ ≤
      (|u| / v) ^ (2 * (J + 1)) * (K * v ^ 2 / (q ^ 2 - v ^ 2)) := by
  have h := badCoshSum_le_of_expTail_closed T 0 v K q
    (by norm_num) (by norm_num) hv.le hvq htail
  have hb : badWeightedSum T 0 (fun t => Real.cosh (v * t) - 1) ≤
      K * v ^ 2 / (q ^ 2 - v ^ 2) := by
    calc
      _ ≤ K * ((v / 2) *
          ((1 - Real.exp (-(q - v) / 2)) / (q - v) -
            (1 - Real.exp (-(q + v) / 2)) / (q + v))) := by
        simpa only [mul_zero, Real.cosh_zero, sub_self, zero_mul, Real.exp_zero,
          zero_add, mul_assoc] using h
      _ ≤ K * (v ^ 2 / (q ^ 2 - v ^ 2)) :=
        mul_le_mul_of_nonneg_left (coshTail_closed_le_rational v q hv.le hvq) hK
      _ = _ := by ring
  exact (horizontalTaylorError_le_coshSum T u v J hv hu).trans
    (mul_le_mul_of_nonneg_left hb (by positivity))

/-- Explicit Selberg input gives a uniform growing band at every order. -/
theorem normalized_horizontalTaylorError_of_selberg
    (T u C a : ℝ) (J : ℕ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hu : |u| ≤ a * Real.log T / 2) (hD : SelbergDensityBound T C a) :
    ‖horizontalTaylorError T u J / (T : ℂ)‖ ≤
      (2 * |u| / (a * Real.log T)) ^ (2 * (J + 1)) *
        (2 * C * Real.log T / 3) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hq : 0 < a * Real.log T := mul_pos ha hL
  have h := horizontalTaylorError_of_expTail T u (a * Real.log T / 2)
    (2 * C * T * Real.log T) (a * Real.log T) J
    (by positivity) hu (by positivity) (by linarith)
    (fun t ht => strictTail_of_selbergDensity T C a t hT0 ht hD)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  apply (div_le_iff₀ hT0).mpr
  apply h.trans_eq
  have he : (a * Real.log T) ^ 2 - (a * Real.log T / 2) ^ 2 =
      3 * (a * Real.log T) ^ 2 / 4 := by ring
  rw [he]
  field_simp
  ring

/-- Quartic remainder after retaining the exact second horizontal moment. -/
theorem normalized_horizontalTaylorError_one_of_selberg
    (T u C a : ℝ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hu : |u| ≤ a * Real.log T / 2) (hD : SelbergDensityBound T C a) :
    ‖(ordinateSum T u - landauSum T u +
        ((u : ℂ) ^ 2 / 2) * evenHorizontalMoment T u 1) / (T : ℂ)‖ ≤
      (32 * C / (3 * a ^ 4)) * u ^ 4 / (Real.log T) ^ 3 := by
  rw [← horizontalTaylorError_one]
  have h := normalized_horizontalTaylorError_of_selberg T u C a 1 hT hC ha hu hD
  apply h.trans_eq
  have hu4 : |u| ^ 4 = u ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs, ← pow_mul]
  change (2 * |u| / (a * Real.log T)) ^ 4 * (2 * C * Real.log T / 3) = _
  simp only [div_pow, mul_pow, hu4]
  have hL : 0 < Real.log T := Real.log_pos hT
  field_simp
  ring

/-- Uniform finite Fourier synthesis: the signed quadratic moment remains
inside each summand; only the complete quartic remainder is estimated. -/
theorem finiteFourier_horizontalTaylorError_one_of_selberg
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (frequency : ι → ℝ)
    (T C a : ℝ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hu : ∀ i ∈ s, |frequency i| ≤ a * Real.log T / 2)
    (hD : SelbergDensityBound T C a) :
    ‖∑ i ∈ s, c i * (horizontalTaylorError T (frequency i) 1 / (T : ℂ))‖ ≤
      ((32 * C / (3 * a ^ 4)) / (Real.log T) ^ 3) *
        ∑ i ∈ s, ‖c i‖ * (frequency i) ^ 4 := by
  calc
    _ ≤ ∑ i ∈ s, ‖c i * (horizontalTaylorError T (frequency i) 1 / (T : ℂ))‖ :=
      _root_.norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ((32 * C / (3 * a ^ 4)) / (Real.log T) ^ 3) *
        (‖c i‖ * (frequency i) ^ 4) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      have hb := normalized_horizontalTaylorError_one_of_selberg T (frequency i) C a
        hT hC ha (hu i hi) hD
      rw [← horizontalTaylorError_one] at hb
      calc
        _ ≤ ‖c i‖ * ((32 * C / (3 * a ^ 4)) *
            (frequency i) ^ 4 / (Real.log T) ^ 3) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [← Finset.mul_sum]

end RiemannResearch.Analysis.ActualZeroOrdinate
