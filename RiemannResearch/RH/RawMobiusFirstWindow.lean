/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.RawMobiusSubpowerCriterion
import RiemannResearch.RH.CanonicalMobiusWindowCancellation

/-!
# Actual Mertens increments in the first raw Mobius middle window

Source: direct consequence of the local finite Mobius floor-tail identity,
developed for the user's directed RH attempt, September 24, 2026.
On N<k<=2N+1, the omitted quotient sum has exactly one term.
The exact identity identifies the actual residual with k*m_N+M(k)-M(N).
Its weighted increment-energy consequence is necessary for the proposed
subpower bound on the full square budget; this module does not prove that
subpower bound or an upper rate for the increment energy.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

def mobiusFirstWindowIncrement (N k : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 k, (ArithmeticFunction.moebius d : ℝ)) -
    ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)

theorem rawMobiusResidual_first_window (N k : ℕ)
    (hNk : N < k) (hk : k ≤ 2*N+1) :
    hilbertSequence (hilbertOne-rawMobiusHilbert N) k =
      (k : ℝ)*mobiusReciprocalSum N + mobiusFirstWindowIncrement N k := by
  have hqlo : 1 ≤ k/(N+1) :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos N)).mpr (by omega)
  have hqhi : k/(N+1) < 2 := by
    by_contra hh
    have hh' : 2 ≤ k/(N+1) := by omega
    have hm := Nat.mul_le_mul_right (N+1) hh'
    have hd := Nat.div_mul_le_self k (N+1)
    nlinarith
  have hq : k/(N+1) = 1 := by omega
  have ht := finite_mobius_floor_tail_identity N k (by omega) hNk.le
  rw [hq] at ht
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.div_one] at ht
  have hs : (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ)*residueFraction d k) =
      (k : ℝ)*mobiusReciprocalSum N -
      ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ)*((k/d : ℕ) : ℝ) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 N,
          ((k : ℝ)*((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) -
           (ArithmeticFunction.moebius d : ℝ)*((k/d : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [residueFraction_eq_div_sub_floor d k (Finset.mem_Icc.mp hd).1]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
  rw [rawMobiusResidual_sequence N k (by omega), hs]
  unfold mobiusFirstWindowIncrement
  linarith

def mobiusFirstWindowIncrementEnergy (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, positiveWeight (i+(N+1)) *
    mobiusFirstWindowIncrement N (i+(N+1))^2

theorem mobiusFirstWindowIncrementEnergy_le_square_budget (N : ℕ)
    (hN : 2 ≤ N) :
    mobiusFirstWindowIncrementEnergy N ≤ 2*rawMobiusSquareBudget N := by
  have hNN : 2*N ≤ N^2 := by nlinarith
  have hr : Finset.range N ⊆ Finset.range (N^2-N) :=
    Finset.range_mono (by omega)
  have hmid : (∑ i ∈ Finset.range N,
      rawMobiusCoordinateEnergy N (i+(N+1))) ≤ rawMobiusMiddleEnergy N (N^2) := by
    unfold rawMobiusMiddleEnergy
    apply Finset.sum_le_sum_of_subset_of_nonneg hr
    intro i hi hnot
    exact rawMobiusCoordinateEnergy_nonneg N _
  have hterm (i : ℕ) (hi : i ∈ Finset.range N) :
      positiveWeight (i+(N+1))*mobiusFirstWindowIncrement N (i+(N+1))^2 ≤
        2*rawMobiusCoordinateEnergy N (i+(N+1))+2*(mobiusReciprocalSum N)^2 := by
    have hi' := Finset.mem_range.mp hi
    let k := i+(N+1)
    have hk : 0 < k := by dsimp [k]; omega
    have hkN : N < k := by dsimp [k]; omega
    have hk2 : k ≤ 2*N+1 := by dsimp [k]; omega
    have hid := rawMobiusResidual_first_window N k hkN hk2
    have hsq : mobiusFirstWindowIncrement N k^2 ≤
        2*(hilbertSequence (hilbertOne-rawMobiusHilbert N) k)^2 +
        2*(k : ℝ)^2*(mobiusReciprocalSum N)^2 := by
      rw [hid]
      nlinarith [sq_nonneg (2*(k : ℝ)*mobiusReciprocalSum N +
        mobiusFirstWindowIncrement N k)]
    have hwk : positiveWeight k*(k : ℝ)^2 ≤ 1 := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have he : positiveWeight k*(k : ℝ)^2 = (k : ℝ)/((k : ℝ)+1) := by
        unfold positiveWeight
        field_simp
      rw [he]
      exact (div_le_one (by positivity)).mpr (by linarith)
    have hp := mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg k)
    have hp' := mul_le_mul_of_nonneg_right hwk (sq_nonneg (mobiusReciprocalSum N))
    change positiveWeight k*mobiusFirstWindowIncrement N k^2 ≤
      2*rawMobiusCoordinateEnergy N k+2*(mobiusReciprocalSum N)^2
    unfold rawMobiusCoordinateEnergy
    nlinarith
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (2*rawMobiusCoordinateEnergy N (i+(N+1))+2*(mobiusReciprocalSum N)^2) :=
      Finset.sum_le_sum hterm
    _ = 2*(∑ i ∈ Finset.range N, rawMobiusCoordinateEnergy N (i+(N+1))) +
        2*(N : ℝ)*(mobiusReciprocalSum N)^2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
      simp only [Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      unfold rawMobiusSquareBudget
      nlinarith

end RiemannResearch.RH.Pareto
