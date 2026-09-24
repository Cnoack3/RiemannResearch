/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.NaturalMobiusPhysicalTests
import RiemannResearch.Analysis.ReciprocalEnergyFromPrefix

/-!
# Finite-window localization of the complete raw Mobius energy

The raw family is used here, without the boundary correction in the canonical
family. The exact head and the entire infinite far tail are retained. The
arithmetic energy in the finite middle window is not asserted bounded.

Source: direct exact-head / bounded-tail calculation, motivated by the finite
window route in Gallardo--Seco, arXiv:2206.02654v6, Theorem 3.1.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto

def rawMobiusCoordinateEnergy (N k : ℕ) : ℝ :=
  positiveWeight k * hilbertSequence (hilbertOne - rawMobiusHilbert N) k ^ 2

def rawMobiusMiddleEnergy (N K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K-N), rawMobiusCoordinateEnergy N (k+(N+1))

def rawMobiusFarEnergy (N K : ℕ) : ℝ :=
  ∑' k : ℕ, rawMobiusCoordinateEnergy N (k+(K+1))

theorem rawMobiusCoordinateEnergy_summable (N : ℕ) :
    Summable (rawMobiusCoordinateEnergy N) :=
  hilbertSequence_square_summable (hilbertOne - rawMobiusHilbert N)

theorem rawMobiusCoordinateEnergy_nonneg (N k : ℕ) :
    0 ≤ rawMobiusCoordinateEnergy N k :=
  mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)

theorem rawMobiusMiddleEnergy_nonneg (N K : ℕ) :
    0 ≤ rawMobiusMiddleEnergy N K :=
  Finset.sum_nonneg (fun _ _ => rawMobiusCoordinateEnergy_nonneg N _)

/-- The entire middle budget is an explicit finite arithmetic sum. -/
theorem rawMobiusMiddleEnergy_finite_arithmetic (N K : ℕ) :
    rawMobiusMiddleEnergy N K =
      ∑ k ∈ Finset.range (K-N), positiveWeight (k+(N+1)) *
        (1 + ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * ArithmeticCumulative.residueFraction d (k+(N+1)))^2 := by
  unfold rawMobiusMiddleEnergy rawMobiusCoordinateEnergy
  apply Finset.sum_congr rfl
  intro k hk
  rw [rawMobiusResidual_sequence N (k+(N+1)) (by omega)]

theorem rawMobiusFarEnergy_nonneg (N K : ℕ) :
    0 ≤ rawMobiusFarEnergy N K :=
  tsum_nonneg (fun _ => rawMobiusCoordinateEnergy_nonneg N _)

/-- Every head coordinate has its exact reciprocal-Mobius value. -/
theorem rawMobius_head_energy_exact (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), rawMobiusCoordinateEnergy N k) =
      (mobiusReciprocalSum N)^2 *
        ∑ k ∈ Finset.range (N+1), (k : ℝ)/((k : ℝ)+1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0, rawMobiusCoordinateEnergy, positiveWeight]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  unfold rawMobiusCoordinateEnergy
  rw [rawMobiusResidual_head N k hkpos hkN]
  unfold positiveWeight
  field_simp

/-- Exact head / finite middle / complete far-tail decomposition. -/
theorem rawMobius_energy_three_regions (N K : ℕ) (hNK : N ≤ K) :
    ‖hilbertOne - rawMobiusHilbert N‖^2 =
      (mobiusReciprocalSum N)^2 *
        (∑ k ∈ Finset.range (N+1), (k : ℝ)/((k : ℝ)+1)) +
      rawMobiusMiddleEnergy N K + rawMobiusFarEnergy N K := by
  have hs := rawMobiusCoordinateEnergy_summable N
  have ht := (summable_nat_add_iff (N+1)).mpr hs
  have hidx (k : ℕ) : (k+(K-N))+(N+1) = k+(K+1) := by omega
  rw [hilbert_norm_weighted_sq]
  change (∑' k : ℕ, rawMobiusCoordinateEnergy N k) = _
  rw [← hs.sum_add_tsum_nat_add (N+1),
    rawMobius_head_energy_exact,
    ← ht.sum_add_tsum_nat_add (K-N)]
  simp_rw [hidx]
  unfold rawMobiusMiddleEnergy rawMobiusFarEnergy
  ring

/-- Uniform far-tail bound, valid at any chosen finite cutoff. -/
theorem rawMobiusFarEnergy_le (N K : ℕ) (hN : 0 < N) :
    rawMobiusFarEnergy N K ≤ (N : ℝ)^2/((K : ℝ)+1) := by
  have hf := (summable_nat_add_iff (K+1)).mpr
    (rawMobiusCoordinateEnergy_summable N)
  have hw := (summable_nat_add_iff (K+1)).mpr positiveWeight_summable
  calc
    _ ≤ ∑' k : ℕ, positiveWeight (k+(K+1))*(N : ℝ)^2 := by
      apply Summable.tsum_le_tsum _ hf (hw.mul_right _)
      intro k
      unfold rawMobiusCoordinateEnergy
      apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
      have h := mul_self_le_mul_self (abs_nonneg _)
        (rawMobiusResidual_abs_le_cutoff N hN (k+(K+1)))
      simpa only [← pow_two, sq_abs] using h
    _ = _ := by
      rw [tsum_mul_right, positiveWeight_tail_tsum (K+1) (Nat.succ_pos _)]
      push_cast
      ring

/-- The finite head budget is at most N times the squared reciprocal sum. -/
theorem rawMobius_head_energy_le (N : ℕ) :
    (mobiusReciprocalSum N)^2 *
      (∑ k ∈ Finset.range (N+1), (k : ℝ)/((k : ℝ)+1)) ≤
      (N : ℝ)*(mobiusReciprocalSum N)^2 := by
  have hh : (∑ k ∈ Finset.range (N+1), (k : ℝ)/((k : ℝ)+1)) ≤ (N : ℝ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_div, add_zero]
    calc
      _ ≤ ∑ k ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply (div_le_one (by positivity)).mpr
        linarith
      _ = _ := by simp
  have h := mul_le_mul_of_nonneg_left hh (sq_nonneg (mobiusReciprocalSum N))
  simpa only [mul_comm] using h

theorem rawMobius_energy_le_head_middle_far (N K : ℕ)
    (hN : 0 < N) (hNK : N ≤ K) :
    ‖hilbertOne - rawMobiusHilbert N‖^2 ≤
      (N : ℝ)*(mobiusReciprocalSum N)^2 + rawMobiusMiddleEnergy N K +
        (N : ℝ)^2/((K : ℝ)+1) := by
  rw [rawMobius_energy_three_regions N K hNK]
  exact add_le_add (add_le_add (rawMobius_head_energy_le N) le_rfl)
    (rawMobiusFarEnergy_le N K hN)

/-- For the square cutoff, all unbounded energy is localized to finite data. -/
theorem rawMobius_energy_le_square_window (N : ℕ) (hN : 0 < N) :
    ‖hilbertOne - rawMobiusHilbert N‖^2 ≤
      (N : ℝ)*(mobiusReciprocalSum N)^2 + rawMobiusMiddleEnergy N (N^2) + 1 := by
  have hNK : N ≤ N^2 := by nlinarith
  have ht := rawMobius_energy_le_head_middle_far N (N^2) hN hNK
  have hf : (N : ℝ)^2/((N^2 : ℕ)+1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    push_cast
    linarith
  linarith

/-- The infinite physical tail follows from an explicit finite-interval
mean-square provider. The classical large sieve can supply this premise,
but that provider is not assumed proved by this declaration. -/
theorem rawMobiusFarEnergy_le_of_prefix
    (N K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hp : ∀ L : ℕ, (∑ i ∈ Finset.range L,
      (hilbertSequence (hilbertOne-rawMobiusHilbert N) (i+(K+1)))^2) ≤
        C*((K : ℝ)+L)) :
    rawMobiusFarEnergy N K ≤ 2*C/((K : ℝ)+2) := by
  let a : ℕ → ℝ := fun i =>
    (hilbertSequence (hilbertOne-rawMobiusHilbert N) (i+(K+1)))^2
  have hid (i : ℕ) : a i / (((K : ℝ)+i+1)*((K : ℝ)+i+2)) =
      rawMobiusCoordinateEnergy N (i+(K+1)) := by
    dsimp [a, rawMobiusCoordinateEnergy, positiveWeight]
    push_cast
    ring
  have hs : Summable (fun i : ℕ =>
      a i / (((K : ℝ)+i+1)*((K : ℝ)+i+2))) := by
    simp_rw [hid]
    exact (summable_nat_add_iff (K+1)).mpr (rawMobiusCoordinateEnergy_summable N)
  have hb := RiemannResearch.Analysis.reciprocal_energy_tsum_le_of_prefix
    a K C (Nat.cast_nonneg K) hC hp hs
  simpa only [hid, rawMobiusFarEnergy] using hb

end RiemannResearch.RH.Pareto
