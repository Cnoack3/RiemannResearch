/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ActualZeroHorizontalRemainder

/-!
# All even horizontal moments from the explicit density input

Source: FRZ_Strengthening_2026-11-10, higher even corrections. Every actual
zero and multiplicity is retained. A single positive term of the cosh series
is dominated by its nonconstant part. The existing exact exponential-tail
integral therefore controls all even moments, uniformly in the phase
frequency. Constants depend on the fixed moment order; no growing-order
claim and no global density axiom is introduced.
-/

noncomputable section
open Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

theorem norm_evenHorizontalMoment_le_realSum (T u : ℝ) (j : ℕ) :
    ‖evenHorizontalMoment T u j‖ ≤
      realSum T (fun ρ => |ρ.re - 1 / 2| ^ (2 * j)) := by
  unfold evenHorizontalMoment
  calc
    _ ≤ realSum T (fun ρ => ‖phase u ρ.im *
        ((ρ.re - 1 / 2 : ℝ) : ℂ) ^ (2 * j)‖) := norm_sum_le _ _
    _ = _ := by
      congr 1
      funext ρ
      simp only [norm_mul, phase_norm, one_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs]

/-- A single positive cosh coefficient controls every phase-weighted moment. -/
theorem scaled_evenHorizontalMoment_le_coshSum (T u v : ℝ)
    (j : ℕ) (hv : 0 < v) :
    (v ^ (2 * (j + 1)) / (Nat.factorial (2 * (j + 1)) : ℝ)) *
      ‖evenHorizontalMoment T u (j + 1)‖ ≤
        badWeightedSum T 0 (fun t => Real.cosh (v * t) - 1) := by
  let c : ℝ := v ^ (2 * (j + 1)) / (Nat.factorial (2 * (j + 1)) : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hs : c * realSum T (fun ρ => |ρ.re - 1 / 2| ^ (2 * (j + 1))) =
      realSum T (fun ρ => c * |ρ.re - 1 / 2| ^ (2 * (j + 1))) := by
    rw [mul_comm, ← realSum_mul_const]
    congr 1
    funext ρ
    ring
  change c * ‖evenHorizontalMoment T u (j + 1)‖ ≤ _
  calc
    _ ≤ c * realSum T (fun ρ => |ρ.re - 1 / 2| ^ (2 * (j + 1))) :=
      mul_le_mul_of_nonneg_left (norm_evenHorizontalMoment_le_realSum T u (j + 1)) hc
    _ = _ := hs
    _ ≤ _ := by
      rw [badWeightedSum_eq_realSum]
      apply realSum_mono
      intro ρ _
      by_cases hb : 0 < |ρ.re - 1 / 2|
      · rw [if_pos hb]
        have h := Real.coshTaylorTerm_succ_le_cosh_sub_one j (v * |ρ.re - 1 / 2|)
        dsimp [c]
        simpa only [Real.coshTaylorTerm, mul_pow, div_mul_eq_mul_div] using h
      · have hz : |ρ.re - 1 / 2| = 0 := le_antisymm (le_of_not_gt hb) (abs_nonneg _)
        rw [if_neg hb, hz]
        simp

/-- All positive even moments from one comparison frequency and strict-tail
bound; the exact rational cosh-integral denominator is retained. -/
theorem norm_evenHorizontalMoment_le_expTail
    (T u v K q : ℝ) (j : ℕ) (hv : 0 < v) (hK : 0 ≤ K) (hvq : v < q)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T t ≤ K * Real.exp (-q * t)) :
    ‖evenHorizontalMoment T u (j + 1)‖ ≤
      ((Nat.factorial (2 * (j + 1)) : ℝ) / v ^ (2 * (j + 1))) *
        (K * v ^ 2 / (q ^ 2 - v ^ 2)) := by
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
  have hs := (scaled_evenHorizontalMoment_le_coshSum T u v j hv).trans hb
  have hf : (Nat.factorial (2 * (j + 1)) : ℝ) ≠ 0 := by positivity
  have hvp : v ^ (2 * (j + 1)) ≠ 0 := pow_ne_zero _ hv.ne'
  have hc : ((Nat.factorial (2 * (j + 1)) : ℝ) / v ^ (2 * (j + 1))) *
      (v ^ (2 * (j + 1)) / (Nat.factorial (2 * (j + 1)) : ℝ)) = 1 := by
    field_simp
  calc
    _ = ((Nat.factorial (2 * (j + 1)) : ℝ) / v ^ (2 * (j + 1))) *
        ((v ^ (2 * (j + 1)) / (Nat.factorial (2 * (j + 1)) : ℝ)) *
          ‖evenHorizontalMoment T u (j + 1)‖) := by rw [← mul_assoc, hc, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- Uniform in the phase frequency, at every fixed positive even order.
For order `2j+2` this is O((log T)^(-2j-1)). -/
theorem normalized_evenHorizontalMoment_of_selberg
    (T u C a : ℝ) (j : ℕ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hD : SelbergDensityBound T C a) :
    ‖evenHorizontalMoment T u (j + 1) / (T : ℂ)‖ ≤
      (Nat.factorial (2 * (j + 1)) : ℝ) *
        (2 / (a * Real.log T)) ^ (2 * (j + 1)) *
          (2 * C * Real.log T / 3) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have h := norm_evenHorizontalMoment_le_expTail T u (a * Real.log T / 2)
    (2 * C * T * Real.log T) (a * Real.log T) j
    (by positivity) (by positivity) (by nlinarith [mul_pos ha hL])
    (fun t ht => strictTail_of_selbergDensity T C a t hT0 ht hD)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  apply (div_le_iff₀ hT0).mpr
  apply h.trans_eq
  have he : (a * Real.log T) ^ 2 - (a * Real.log T / 2) ^ 2 =
      3 * (a * Real.log T) ^ 2 / 4 := by ring
  rw [he]
  simp only [div_pow, mul_pow]
  field_simp
  ring

/-- The factorial cancels exactly in the normalized Taylor coefficient.
There is no frequency-band restriction on this individual moment bound. -/
theorem normalized_evenHorizontalTaylorTerm_of_selberg
    (T u C a : ℝ) (j : ℕ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hD : SelbergDensityBound T C a) :
    ‖(((u : ℂ) ^ (2 * (j + 1)) / (Nat.factorial (2 * (j + 1)) : ℂ)) *
        (evenHorizontalMoment T u (j + 1) / (T : ℂ)))‖ ≤
      (2 * |u| / (a * Real.log T)) ^ (2 * (j + 1)) *
        (2 * C * Real.log T / 3) := by
  have h := normalized_evenHorizontalMoment_of_selberg T u C a j hT hC ha hD
  have hf : ‖(Nat.factorial (2 * (j + 1)) : ℂ)‖ =
      (Nat.factorial (2 * (j + 1)) : ℝ) := by simp
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, hf]
  apply (mul_le_mul_of_nonneg_left h (by positivity :
    0 ≤ |u| ^ (2 * (j + 1)) / (Nat.factorial (2 * (j + 1)) : ℝ))).trans_eq
  have hf0 : (Nat.factorial (2 * (j + 1)) : ℝ) ≠ 0 := by positivity
  simp only [div_pow, mul_pow]
  field_simp

end RiemannResearch.Analysis.ActualZeroOrdinate
