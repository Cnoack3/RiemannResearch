/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTPositiveRemainder
import RiemannResearch.RH.CRTPeriodicEnergy

/-!
# Exact special-function energy and sign-aware finite enclosures

L is kept as an equality. Its occurrences in the linear and quadratic pieces
are combined before estimating the signed remainder. No growing-family
arithmetic bound is an assumption of, or a consequence claimed by, this module.
-/

open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
noncomputable section
open RiemannResearch.RH.ArithmeticCumulative (mixtureWeight)
open RiemannResearch.Probability.ConditionalIID (cesaro)

def regularSquare (Q r : ℝ) : ℝ := trigamma (r / Q) / Q^2 -
  (realDigamma ((r + 1) / Q) - realDigamma (r / Q)) / Q

def combinedLCoefficient (a b : ℝ) : ℝ := 2 * a * b - b^2 / 2

theorem regularSquare_pos {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    0 < regularSquare Q r := by
  have he := progressionM_eq_trigamma_digamma hQ hr
  have hm := progressionM_pos hQ hr
  have hl := progressionL_pos hQ hr
  unfold regularSquare
  linarith

theorem progression_energy_recombined (a b : ℝ) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) :
    2 * a * (progressionL Q r * b) + progressionM Q r * b^2 =
      regularSquare Q r * b^2 + combinedLCoefficient a b * progressionL Q r := by
  rw [progressionM_eq_trigamma_digamma hQ hr]
  unfold regularSquare combinedLCoefficient
  ring

/-- Exact energy with L retained and its two coefficients combined. -/
theorem periodic_error_exact_specialFunctions (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n + Q) = F n) (c : ℝ) :
    (∑' k : ℕ, mixtureWeight (k + 1) * (cesaro F (k + 1) - c)^2) =
      (periodMean F Q - c)^2 + ∑ r : Fin Q,
        (regularSquare Q (r.val + 1) * (periodDefect F Q (r.val + 1))^2 +
        combinedLCoefficient (periodMean F Q - c) (periodDefect F Q (r.val + 1)) *
          progressionL Q (r.val + 1)) := by
  rw [periodic_error_energy_identity F Q hQ hp c]
  rw [Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact progression_energy_recombined _ _ (by exact_mod_cast hQ) (by positivity)

def midpointEnergyCore (F : ℕ → ℝ) (Q : ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  (periodMean F Q - c)^2 + ∑ r : Fin Q,
    (regularSquare Q (r.val + 1) * (periodDefect F Q (r.val + 1))^2 +
    combinedLCoefficient (periodMean F Q - c) (periodDefect F Q (r.val + 1)) *
      lMidpointApprox Q (r.val + 1) N)

/-- Exact finite expansion, including the complete signed remainder. -/
theorem periodic_error_exact_signed_remainder (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n + Q) = F n) (c : ℝ) (N : ℕ) :
    (∑' k : ℕ, mixtureWeight (k + 1) * (cesaro F (k + 1) - c)^2) =
      midpointEnergyCore F Q c N + ∑ r : Fin Q,
        combinedLCoefficient (periodMean F Q - c) (periodDefect F Q (r.val + 1)) *
          lMidpointTail Q (r.val + 1) N := by
  rw [periodic_error_exact_specialFunctions F Q hQ hp c]
  unfold midpointEnergyCore
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [progressionL_midpoint_exact N (by exact_mod_cast hQ) (by positivity)]
  ring

theorem signed_remainder_interval (z R δ : ℝ) (hR : 0 ≤ R) (hδ : R ≤ δ) :
    min z 0 * δ ≤ z * R ∧ z * R ≤ max z 0 * δ := by
  by_cases hz : 0 ≤ z
  · rw [min_eq_right hz, max_eq_left hz, zero_mul]
    exact ⟨mul_nonneg hz hR, mul_le_mul_of_nonneg_left hδ hz⟩
  · have hz' : z ≤ 0 := le_of_not_ge hz
    rw [min_eq_left hz', max_eq_right hz', zero_mul]
    exact ⟨mul_le_mul_of_nonpos_left hδ hz', mul_nonpos_of_nonpos_of_nonneg hz' hR⟩

def midpointRemainderBudget (Q r : ℝ) (N : ℕ) : ℝ :=
  progressionL Q r / (r + 1)^(2 * N)

/-- A certified two-sided enclosure, with the side chosen by the actual coefficient sign. -/
theorem periodic_error_signed_enclosure (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n + Q) = F n) (c : ℝ) (N : ℕ) :
    midpointEnergyCore F Q c N + (∑ r : Fin Q,
      min (combinedLCoefficient (periodMean F Q - c) (periodDefect F Q (r.val + 1))) 0 *
        midpointRemainderBudget Q (r.val + 1) N) ≤
      (∑' k : ℕ, mixtureWeight (k + 1) * (cesaro F (k + 1) - c)^2) ∧
    (∑' k : ℕ, mixtureWeight (k + 1) * (cesaro F (k + 1) - c)^2) ≤
      midpointEnergyCore F Q c N + (∑ r : Fin Q,
      max (combinedLCoefficient (periodMean F Q - c) (periodDefect F Q (r.val + 1))) 0 *
        midpointRemainderBudget Q (r.val + 1) N) := by
  simp only [periodic_error_exact_signed_remainder F Q hQ hp c N]
  constructor
  · apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro r hr
    exact (signed_remainder_interval _ _ _
      (lMidpointTail_pos N (by exact_mod_cast hQ) (by positivity)).le
      (lMidpointTail_geometric_bound N (by exact_mod_cast hQ) (by positivity))).1
  · apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro r hr
    exact (signed_remainder_interval _ _ _
      (lMidpointTail_pos N (by exact_mod_cast hQ) (by positivity)).le
      (lMidpointTail_geometric_bound N (by exact_mod_cast hQ) (by positivity))).2

/-- A certified relative upper weight, not an independently perturbed Gram entry. -/
def midpointMUpper (Q r : ℝ) (N : ℕ) : ℝ :=
  regularSquare Q r - lMidpointApprox Q r N / 2

theorem midpointMUpper_exact (N : ℕ) {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r) :
    midpointMUpper Q r N = progressionM Q r + lMidpointTail Q r N / 2 := by
  have hM := progressionM_eq_trigamma_digamma hQ hr
  have hL := progressionL_midpoint_exact N hQ hr
  unfold midpointMUpper regularSquare
  linarith

theorem progressionM_midpoint_relative (N : ℕ) (hN : 0 < N) {Q r : ℝ}
    (hQ : 0 < Q) (hr : 1 ≤ r) :
    progressionM Q r ≤ midpointMUpper Q r N ∧
    midpointMUpper Q r N ≤ (1 + 1 / (2 * (4 : ℝ)^N)) * progressionM Q r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  rw [midpointMUpper_exact N hQ hr0]
  constructor
  · have hR := lMidpointTail_pos N hQ hr0
    linarith
  · have hR := lMidpointTail_le_M N hN hQ hr
    have he : (1 + 1 / (2 * (4 : ℝ)^N)) * progressionM Q r =
        progressionM Q r + (progressionM Q r / (4 : ℝ)^N) / 2 := by ring
    rw [he]
    linarith

def midpointZeroMeanUpper (F : ℕ → ℝ) (Q N : ℕ) : ℝ :=
  ∑ r : Fin Q, midpointMUpper Q (r.val + 1) N * (periodDefect F Q (r.val + 1))^2

/-- Uniform relative energy enclosure for every zero-period-mean periodic witness. -/
theorem zeroMean_energy_relative_enclosure (F : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (hp : ∀ n, F (n + Q) = F n) (hm : periodMean F Q = 0) (N : ℕ) (hN : 0 < N) :
    (∑' k : ℕ, mixtureWeight (k + 1) * (cesaro F (k + 1))^2) ≤
      midpointZeroMeanUpper F Q N ∧
    midpointZeroMeanUpper F Q N ≤ (1 + 1 / (2 * (4 : ℝ)^N)) *
      (∑' k : ℕ, mixtureWeight (k + 1) * (cesaro F (k + 1))^2) := by
  have he := periodic_error_energy_identity F Q hQ hp 0
  simp only [hm, sub_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul,
    zero_add] at he
  simp only [he]
  unfold midpointZeroMeanUpper
  constructor
  · apply Finset.sum_le_sum
    intro r hr
    exact mul_le_mul_of_nonneg_right
      (progressionM_midpoint_relative N hN (Q := (Q : ℝ)) (r := (r.val : ℝ) + 1)
        (by exact_mod_cast hQ)
        (by have h := Nat.cast_nonneg r.val (α := ℝ); linarith)).1 (sq_nonneg _)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hb := mul_le_mul_of_nonneg_right
      (progressionM_midpoint_relative N hN (Q := (Q : ℝ)) (r := (r.val : ℝ) + 1)
        (by exact_mod_cast hQ)
        (by have h := Nat.cast_nonneg r.val (α := ℝ); linarith)).2
      (sq_nonneg (periodDefect F Q (r.val + 1)))
    simpa only [mul_assoc] using hb

/-- Explicit eventual subpolynomial bound; no existence of such a bound is asserted. -/
def HasSubpolynomialEnergy (Y : ℕ → ℕ) (E : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ,
    ∀ j : ℕ, j₀ ≤ j → E j ≤ C * (Y j : ℝ)^ε

/-- At any fixed positive order the certified upper energy has precisely the
same subpolynomial-bound obligation as the actual energy, uniformly in periods. -/
theorem growing_zeroMean_subpolynomial_iff
    (F : ℕ → ℕ → ℝ) (Q Y : ℕ → ℕ)
    (hQ : ∀ j, 0 < Q j) (hp : ∀ j n, F j (n + Q j) = F j n)
    (hm : ∀ j, periodMean (F j) (Q j) = 0) (N : ℕ) (hN : 0 < N) :
    HasSubpolynomialEnergy Y
      (fun j => ∑' k : ℕ, mixtureWeight (k + 1) * (cesaro (F j) (k + 1))^2) ↔
    HasSubpolynomialEnergy Y (fun j => midpointZeroMeanUpper (F j) (Q j) N) := by
  have hb (j : ℕ) := zeroMean_energy_relative_enclosure (F j) (Q j)
    (hQ j) (hp j) (hm j) N hN
  let K : ℝ := 1 + 1 / (2 * (4 : ℝ)^N)
  have hK : 0 < K := by dsimp [K]; positivity
  constructor
  · intro h ε hε
    obtain ⟨C, hC, j₀, hbound⟩ := h ε hε
    refine ⟨K * C, mul_pos hK hC, j₀, ?_⟩
    intro j hj
    calc
      midpointZeroMeanUpper (F j) (Q j) N ≤
          K * (∑' k : ℕ, mixtureWeight (k + 1) * (cesaro (F j) (k + 1))^2) :=
        (hb j).2
      _ ≤ K * (C * (Y j : ℝ)^ε) :=
        mul_le_mul_of_nonneg_left (hbound j hj) hK.le
      _ = (K * C) * (Y j : ℝ)^ε := by ring
  · intro h ε hε
    obtain ⟨C, hC, j₀, hbound⟩ := h ε hε
    refine ⟨C, hC, j₀, ?_⟩
    intro j hj
    exact (hb j).1.trans (hbound j hj)

end
end RiemannResearch.RH.CRTBlock
