/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FrequencySensitiveGramBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact coefficient-profile and arithmetic budgets

Finite components of agenda item 3 in the user-provided
`Signed_Quadratic_Correction_Research_Note.pdf`, section 7.
These are elementary finite identities and inequalities. No phase-law,
zero-density, or RH hypothesis occurs. The reciprocal profile identities
retain the negative square in the variance rather than dropping it.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Fourier
variable {ι : Type*}

/-- Exact spread for a reciprocal coefficient profile on arbitrary nonzero
real frequency indices. For x_k=k this is the first harmonic profile. -/
theorem weightedFrequencySpread_reciprocal
    (s : Finset ι) (x : ι → ℝ) (L : ℝ)
    (hx : ∀ i ∈ s, x i ≠ 0) :
    weightedFrequencySpread s (fun i => 1 / x i) (fun i => L * x i) =
      2 * L ^ 2 * ((∑ i ∈ s, 1 / x i) * (∑ i ∈ s, x i) - (s.card : ℝ) ^ 2) := by
  have hsecond : (∑ i ∈ s, (1 / x i) * (L * x i) ^ 2) =
      L ^ 2 * ∑ i ∈ s, x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hx i hi] <;> ring
  have hfirst : (∑ i ∈ s, (1 / x i) * (L * x i)) = L * (s.card : ℝ) := by
    calc
      _ = ∑ _i ∈ s, L := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [hx i hi]
      _ = _ := by simp [mul_comm]
  rw [weightedFrequencySpread_eq, hsecond, hfirst]
  ring

/-- Exact inverse-square profile; the first moment is harmonic and the
second moment is exactly the cardinality. -/
theorem weightedFrequencySpread_reciprocal_sq
    (s : Finset ι) (x : ι → ℝ) (L : ℝ)
    (hx : ∀ i ∈ s, x i ≠ 0) :
    weightedFrequencySpread s (fun i => 1 / (x i) ^ 2) (fun i => L * x i) =
      2 * L ^ 2 * ((s.card : ℝ) * (∑ i ∈ s, 1 / (x i) ^ 2) -
        (∑ i ∈ s, 1 / x i) ^ 2) := by
  have hsecond : (∑ i ∈ s, (1 / (x i) ^ 2) * (L * x i) ^ 2) =
      L ^ 2 * (s.card : ℝ) := by
    calc
      _ = ∑ _i ∈ s, L ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [hx i hi] <;> ring
      _ = _ := by simp [mul_comm]
  have hfirst : (∑ i ∈ s, (1 / (x i) ^ 2) * (L * x i)) =
      L * ∑ i ∈ s, 1 / x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hx i hi] <;> ring
  rw [weightedFrequencySpread_eq, hsecond, hfirst]
  ring

/-- The arithmetic half-moment loses only the sum of frequencies, rather
than support-cardinality times their maximum. -/
theorem weighted_sqrt_mass_sq_le
    (s : Finset ι) (w x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i * Real.sqrt (x i)) ^ 2 ≤
      (∑ i ∈ s, w i ^ 2) * (∑ i ∈ s, x i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s w (fun i => Real.sqrt (x i))
  have hs : (∑ i ∈ s, (Real.sqrt (x i)) ^ 2) = ∑ i ∈ s, x i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (hx i hi)
  rwa [hs] at h

/-- A geometric prime tower has total frequency mass at most twice its
last frequency. This removes the extraneous tower-length factor. -/
theorem geometric_tower_sum_le_twice_last
    (p : ℝ) (hp : 2 ≤ p) (K : ℕ) :
    (∑ k ∈ Finset.range K, p ^ (k + 1)) ≤ 2 * p ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hp₀ : 0 ≤ p := by linarith
    have hpow : 0 ≤ p ^ K := pow_nonneg hp₀ K
    calc
      _ ≤ 2 * p ^ K + p ^ (K + 1) := add_le_add ih (le_refl _)
      _ ≤ 2 * p ^ (K + 1) := by
        rw [pow_succ]
        nlinarith [mul_nonneg hpow (sub_nonneg.mpr hp)]

/-- Combined weighted-Cauchy/geometric arithmetic budget for one tower. -/
theorem tower_weighted_sqrt_mass_sq_le
    (p : ℝ) (hp : 2 ≤ p) (K : ℕ) (w : ℕ → ℝ) :
    (∑ k ∈ Finset.range K, w k * Real.sqrt (p ^ (k + 1))) ^ 2 ≤
      2 * p ^ K * (∑ k ∈ Finset.range K, w k ^ 2) := by
  have hp₀ : 0 ≤ p := by linarith
  have h := weighted_sqrt_mass_sq_le (Finset.range K) w
    (fun k => p ^ (k + 1)) (fun k _ => pow_nonneg hp₀ _)
  calc
    _ ≤ (∑ k ∈ Finset.range K, w k ^ 2) *
        (∑ k ∈ Finset.range K, p ^ (k + 1)) := h
    _ ≤ (∑ k ∈ Finset.range K, w k ^ 2) * (2 * p ^ K) :=
      mul_le_mul_of_nonneg_left (geometric_tower_sum_le_twice_last p hp K)
        (Finset.sum_nonneg (fun k _ => sq_nonneg (w k)))
    _ = _ := by ring

#print axioms weightedFrequencySpread_reciprocal
#print axioms weightedFrequencySpread_reciprocal_sq
#print axioms weighted_sqrt_mass_sq_le
#print axioms geometric_tower_sum_le_twice_last
#print axioms tower_weighted_sqrt_mass_sq_le
end RiemannResearch.Fourier
