/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPolylogTailEnergy

/-!
# Complete Q-tail energy under a general physical envelope
The integral comparison from QPolylogTailEnergy applies whenever the squared
envelope divided by the square root of the site is eventually decreasing.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QAnnihilatorTailEscape
open ZetaTwoHilbert ZetaTwoProbability QFiniteSupportDualCriterion
open RiemannResearch.Analysis.PolylogTail

/-- Complete physical-tail bound for every envelope whose square divided by
sqrt(n) is decreasing beyond the chosen cutoff. This is the same integral-test
calculation used for polylogarithmic envelopes, with its arithmetic profile
factored out. -/
theorem profile_tail_energy_le
    (u : QHilbert) (H : ℕ → ℝ) (C : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hprofile : ∀ n : ℕ, N < n →
      H n ^ 2 / Real.sqrt (n : ℝ) ≤ H N ^ 2 / Real.sqrt (N : ℝ))
    (hb : ∀ n : ℕ, N < n → |qSequence u n| ≤ C * H n) :
    ‖tail N u‖ ^ 2 ≤ (2 * C ^ 2 / zetaTwo) * H N ^ 2 / (N : ℝ) := by
  have hz := zetaTwo_pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let K : ℝ := (C ^ 2 / zetaTwo) * (H N ^ 2 / Real.sqrt (N : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsQ : Summable (fun j : ℕ => positiveQWeight (j + N + 1) *
      qSequence u (j + N + 1) ^ 2) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N + 1)).mpr (qSequence_square_summable u)
  have hsP : Summable (fun j : ℕ => ((j + N + 1 : ℕ) : ℝ) ^ (-(3/2 : ℝ))) := by
    have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-(3/2 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (N + 1)).mpr hp
  have hterm (j : ℕ) : positiveQWeight (j + N + 1) *
      qSequence u (j + N + 1) ^ 2 ≤
        K * ((j + N + 1 : ℕ) : ℝ) ^ (-(3/2 : ℝ)) := by
    let n : ℕ := j + N + 1
    have hnN : N < n := by dsimp [n]; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : qSequence u n ^ 2 ≤ C ^ 2 * H n ^ 2 := by
      have hh := mul_self_le_mul_self (abs_nonneg (qSequence u n)) (hb n hnN)
      nlinarith [sq_abs (qSequence u n)]
    have hw := mul_le_mul_of_nonneg_left hsq (positiveQWeight_nonneg n)
    calc
      _ ≤ positiveQWeight n * (C ^ 2 * H n ^ 2) := hw
      _ = (C ^ 2 / zetaTwo) * (H n ^ 2 / (n : ℝ) ^ 2) := by
        simp only [positiveQWeight]
        ring
      _ = (C ^ 2 / zetaTwo) *
          ((H n ^ 2 / Real.sqrt (n : ℝ)) * (n : ℝ) ^ (-(3/2 : ℝ))) := by
        rw [rpow_neg_three_halves hn0]
        field_simp [hn0.ne', (Real.sqrt_pos.mpr hn0).ne']
      _ ≤ (C ^ 2 / zetaTwo) *
          ((H N ^ 2 / Real.sqrt (N : ℝ)) * (n : ℝ) ^ (-(3/2 : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hprofile n hnN)
            (Real.rpow_nonneg hn0.le _)) (by positivity)
      _ = _ := by dsimp [K, n]; ring
  have ht : (∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ (-(3/2 : ℝ))) ≤
      (N : ℝ) ^ (-(1/2 : ℝ)) / (1/2 : ℝ) := by
    have h := Real.tsum_nat_rpow_tail_le (p := (3/2 : ℝ)) (by norm_num) hN
    convert h using 1 <;> norm_num
  rw [tail_energy_physical]
  calc
    _ ≤ ∑' j : ℕ, K * ((j + N + 1 : ℕ) : ℝ) ^ (-(3/2 : ℝ)) :=
      hsQ.tsum_le_tsum hterm (hsP.mul_left K)
    _ = K * ∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ (-(3/2 : ℝ)) := tsum_mul_left
    _ ≤ K * ((N : ℝ) ^ (-(1/2 : ℝ)) / (1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left ht hK
    _ = _ := by
      dsimp [K]
      rw [rpow_neg_half hN0]
      field_simp [hN0.ne', (Real.sqrt_pos.mpr hN0).ne', zetaTwo_pos.ne']
      ring_nf <;> simp [Real.sq_sqrt hN0.le] <;> ring

/-- A physical envelope is sufficient whenever its squared profile is
negligible against the chosen arithmetic decay. No projection property is used. -/
theorem profile_weighted_tail_tendsto_zero
    (u : QHilbert) (H : ℕ → ℝ) (C : ℝ)
    (hprofile : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N < n →
      H n ^ 2 / Real.sqrt (n : ℝ) ≤ H N ^ 2 / Real.sqrt (N : ℝ))
    (hb : ∀ᶠ n : ℕ in atTop, |qSequence u n| ≤ C * H n)
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (η : ℕ → ℝ)
    (hηnonneg : ∀ᶠ j : ℕ in atTop, 0 ≤ η j)
    (hsmall : Tendsto (fun j => η j * H (q j) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j => (q j : ℝ) * η j * ‖tail (q j) u‖ ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hb
  have hlim := hsmall.const_mul (2 * C ^ 2 / zetaTwo)
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hηnonneg] with j hj
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hj) (sq_nonneg _)
  · filter_upwards [hηnonneg, hq.eventually hprofile,
      hq.eventually (eventually_ge_atTop (max N0 1))] with j hηj hprofj hqj
    have hq1 : 1 ≤ q j := by omega
    have hq0 : (0 : ℝ) < q j := by exact_mod_cast (show 0 < q j by omega)
    have htail := profile_tail_energy_le u H C (q j) hq1 hprofj
      (fun n hn => hN0 n (by omega))
    have hw : 0 ≤ (q j : ℝ) * η j := mul_nonneg (Nat.cast_nonneg _) hηj
    calc
      _ ≤ ((q j : ℝ) * η j) *
          ((2 * C ^ 2 / zetaTwo) * H (q j) ^ 2 / (q j : ℝ)) :=
        mul_le_mul_of_nonneg_left htail hw
      _ = (2 * C ^ 2 / zetaTwo) * (η j * H (q j) ^ 2) := by
        field_simp [hq0.ne']
        <;> ring

/-- At the critical profile, boundedness of `η * H²` suffices when the
physical coordinates are little-o of the envelope `H`. -/
theorem profile_weighted_tail_tendsto_zero_of_little_o
    (u : QHilbert) (H : ℕ → ℝ)
    (hprofile : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N < n →
      H n ^ 2 / Real.sqrt (n : ℝ) ≤ H N ^ 2 / Real.sqrt (N : ℝ))
    (hu : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, |qSequence u n| ≤ δ * H n)
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (η : ℕ → ℝ)
    (hη : ∀ᶠ j : ℕ in atTop, 0 ≤ η j)
    (B : ℝ) (hB : 0 ≤ B)
    (hbounded : ∀ᶠ j : ℕ in atTop, η j * H (q j) ^ 2 ≤ B) :
    Tendsto (fun j => (q j : ℝ) * η j * ‖tail (q j) u‖ ^ 2) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro r hr
    filter_upwards [hη] with j hj
    exact hr.trans_le (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hj) (sq_nonneg _))
  · intro e he
    have hZ : 0 < zetaTwo := zetaTwo_pos
    have hBp : 0 < B + 1 := by linarith
    let δ : ℝ := Real.sqrt (e * zetaTwo / (4 * (B + 1)))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδsq : δ ^ 2 = e * zetaTwo / (4 * (B + 1)) :=
      Real.sq_sqrt (by positivity)
    have hid : (2 * δ ^ 2 / zetaTwo) * B = e * (B / (2 * (B + 1))) := by
      rw [hδsq]
      field_simp [hZ.ne', hBp.ne'] <;> ring
    have heff : (2 * δ ^ 2 / zetaTwo) * B < e := by
      rw [hid]
      calc
        _ < e * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 (by linarith)) he
        _ = _ := mul_one _
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hu δ hδ)
    filter_upwards [hη, hbounded, hq.eventually hprofile,
      hq.eventually (eventually_ge_atTop (max N₀ 1))] with j hηj hBj hprofj hqj
    have hq1 : 1 ≤ q j := by omega
    have hq0 : (0 : ℝ) < q j := by exact_mod_cast (show 0 < q j by omega)
    have ht := profile_tail_energy_le u H δ (q j) hq1 hprofj (fun n hn => hN₀ n (by omega))
    calc
      _ ≤ ((q j : ℝ) * η j) * ((2 * δ ^ 2 / zetaTwo) * H (q j) ^ 2 / (q j : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg (Nat.cast_nonneg _) hηj)
      _ = (2 * δ ^ 2 / zetaTwo) * (η j * H (q j) ^ 2) := by
        field_simp [hq0.ne'] <;> ring
      _ ≤ (2 * δ ^ 2 / zetaTwo) * B := mul_le_mul_of_nonneg_left hBj (by positivity)
      _ < e := heff

end RiemannResearch.RH.QAnnihilatorTailEscape
