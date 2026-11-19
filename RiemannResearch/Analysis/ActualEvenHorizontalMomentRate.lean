/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ActualZeroHorizontalRemainder
import RiemannResearch.Analysis.ActualZeroDisplacementMoments

/-!
# All even horizontal moments from the explicit density input

Source: FRZ_Strengthening_2026-11-10, higher even corrections. Every actual
zero and multiplicity is retained. A single positive term of the cosh series
is dominated by its nonconstant part. The existing exact exponential-tail
integral therefore controls all even moments, uniformly in the phase
frequency. For the Selberg consequence, the absolute displacement Mellin bound gives
one factorial estimate in every order with one density constant. The factorial
cancels in each normalized Taylor coefficient.
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

/-- Triangle domination by the absolute moment and its Mellin bound.
One density provider works for every positive even order. The factorial
comes from integrating the exponential tail on the positive half-line. -/
theorem normalized_evenHorizontalMoment_of_selberg
    (T u C a : ℝ) (j : ℕ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hD : SelbergDensityBound T C a) :
    ‖evenHorizontalMoment T u (j + 1) / (T : ℂ)‖ ≤
      (Nat.factorial (2 * (j + 1)) : ℝ) *
        (1 / (a * Real.log T)) ^ (2 * (j + 1)) * (2 * C * Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hq : 0 < a * Real.log T := mul_pos ha (Real.log_pos hT)
  have hf := displacementSum_le_of_selberg (2 * j + 1) hT hC ha hD
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega] at hf
  have hn := norm_evenHorizontalMoment_le_realSum T u (j + 1)
  rw [realSum_eq_copies] at hn
  have hb := (mul_le_mul_of_nonneg_left hn (pow_nonneg hq.le (2 * (j + 1)))).trans hf
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0, div_pow, one_pow]
  have hqp : 0 < (a * Real.log T) ^ (2 * (j + 1)) := pow_pos hq _
  apply (div_le_iff₀ hT0).mpr
  calc
    _ ≤ (2 * C * T * Real.log T * ((2 * (j + 1)).factorial : ℝ)) /
        (a * Real.log T) ^ (2 * (j + 1)) := (le_div_iff₀ hqp).mpr (by simpa [mul_comm] using hb)
    _ = _ := by ring

/-- The factorial cancels exactly in the normalized Taylor coefficient.
There is no frequency-band restriction on this individual moment bound. -/
theorem normalized_evenHorizontalTaylorTerm_of_selberg
    (T u C a : ℝ) (j : ℕ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hD : SelbergDensityBound T C a) :
    ‖(((u : ℂ) ^ (2 * (j + 1)) / (Nat.factorial (2 * (j + 1)) : ℂ)) *
        (evenHorizontalMoment T u (j + 1) / (T : ℂ)))‖ ≤
      (|u| / (a * Real.log T)) ^ (2 * (j + 1)) * (2 * C * Real.log T) := by
  have h := normalized_evenHorizontalMoment_of_selberg T u C a j hT hC ha hD
  have hf : ‖(Nat.factorial (2 * (j + 1)) : ℂ)‖ =
      (Nat.factorial (2 * (j + 1)) : ℝ) := by simp
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, hf]
  apply (mul_le_mul_of_nonneg_left h (by positivity :
    0 ≤ |u| ^ (2 * (j + 1)) / (Nat.factorial (2 * (j + 1)) : ℝ))).trans_eq
  have hf0 : (Nat.factorial (2 * (j + 1)) : ℝ) ≠ 0 := by positivity
  simp only [div_pow, mul_pow, one_pow]
  field_simp

/-- Geometric majorant for the complete Taylor tail throughout the open
frequency band. The displacement Mellin estimate supplies one constant for
all coefficients, so the sum retains the true geometric ratio. -/
theorem normalized_horizontalTaylorError_geometric_of_selberg
    (T u C a : ℝ) (J : ℕ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hu : |u| < a * Real.log T) (hD : SelbergDensityBound T C a) :
    let r := |u| / (a * Real.log T)
    ‖horizontalTaylorError T u J / (T : ℂ)‖ ≤
      2 * C * Real.log T * r ^ (2 * (J + 1)) / (1 - r ^ 2) := by
  let q := a * Real.log T
  let r := |u| / q
  let K := 2 * C * T * Real.log T
  let term := fun (c : Copies T) (k : ℕ) =>
    Real.coshTaylorTerm (u * (c.1.1.re - 1/2)) (k + (J+1))
  have hT0 : 0 < T := by linarith
  have hq : 0 < q := mul_pos ha (Real.log_pos hT)
  have hr0 : 0 ≤ r := div_nonneg (abs_nonneg _) hq.le
  have hr1 : r < 1 := (div_lt_one hq).mpr hu
  have hg := hasSum_geometric_of_lt_one (sq_nonneg r)
    (show r ^ 2 < 1 by nlinarith [mul_pos (sub_pos.mpr hr1) (show 0 < 1+r by linarith)])
  have hterm (c : Copies T) : Summable (term c) := Real.summable_coshTaylorTail J _
  have hcoeff (k : ℕ) :
      (∑ c : Copies T, term c k) ≤ K * r ^ (2 * (J+1)) * (r^2)^k := by
    let m := k + (J+1)
    let n := 2*m
    have hp : 2*(k+J) + 1 + 1 = n := by dsimp [n,m]; omega
    have hf := displacementSum_le_of_selberg (2*(k+J)+1) hT hC ha hD
    rw [hp] at hf
    have hsum : (∑ c : Copies T, copyDisplacement T c ^ n) ≤
        K * (n.factorial : ℝ) / q ^ n :=
      (le_div_iff₀ (pow_pos hq n)).mpr (by simpa only [q, K, mul_comm] using hf)
    have hs : (∑ c : Copies T, term c k) =
        (∑ c : Copies T, copyDisplacement T c ^ n) * (|u|^n / (n.factorial : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      simp only [term, n, m, Real.coshTaylorTerm, copyDisplacement, mul_pow, pow_mul, sq_abs]
      ring
    rw [hs]
    have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
    calc
      _ ≤ (K * (n.factorial : ℝ) / q ^ n) * (|u|^n / (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = K * r ^ n := by
        dsimp [r]
        rw [div_pow]
        field_simp
      _ = _ := by
        dsimp [n,m]
        rw [Nat.mul_add, pow_add, pow_mul]
        ring
  have hrem := horizontalTaylorError_norm_le T u J
  rw [realSum_eq_copies] at hrem
  have heq : (∑ c : Copies T, Real.coshTaylorRemainder J (u * (c.1.1.re-1/2))) =
      ∑' k : ℕ, ∑ c : Copies T, term c k := by
    simp_rw [Real.coshTaylorRemainder_eq_tsum]
    exact (Summable.tsum_finsetSum (s := Finset.univ) (fun c _ => hterm c)).symm
  rw [heq] at hrem
  have hsum := Summable.tsum_le_tsum hcoeff (summable_sum (fun c _ => hterm c))
    (hg.summable.mul_left (K * r ^ (2 * (J+1))))
  rw [(hg.mul_left (K * r ^ (2 * (J+1)))).tsum_eq] at hsum
  change ‖horizontalTaylorError T u J / (T : ℂ)‖ ≤
    2 * C * Real.log T * r ^ (2 * (J+1)) / (1-r^2)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  apply (div_le_iff₀ hT0).mpr
  apply (hrem.trans hsum).trans_eq
  dsimp [K]
  ring

end RiemannResearch.Analysis.ActualZeroOrdinate
