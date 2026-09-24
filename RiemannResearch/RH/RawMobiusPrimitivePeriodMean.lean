/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.RawMobiusPrimitiveEnergy
import RiemannResearch.RH.ParetoUniformJordanIdentification

/-!
# Exact period mean of the signed Mobius primitive remainder

Source: direct discrete product and telescoping calculation in the user's
directed RH attempt, 24 September 2026. Both signed remainder terms from
RawMobiusPrimitiveEnergy are retained. Their full-period sum is precisely
the centered square sum. At period N!, the existing Jordan variance and
upper-half prime-count lower bound therefore apply without assumptions.

Uniform period means are not Pareto-weighted middle-window energies. These
identities rule out simply discarding the combined remainder by a uniform
nonpositivity argument; they supply no RH-strength weighted bound.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto

open ArithmeticCumulative

/-- The centered raw residue combination, defined also at coordinate zero. -/
def rawMobiusCenteredValue (N k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)) *
    (residue d k - ((d : ℝ)-1)/2)

theorem rawMobiusCenteredPrimitive_step_all (N k : ℕ) :
    rawMobiusCenteredPrimitive N (k+1) - rawMobiusCenteredPrimitive N k =
      rawMobiusCenteredValue N k := by
  unfold rawMobiusCenteredPrimitive rawMobiusCenteredValue
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
      (centeredResiduePrimitive d (k+1)-centeredResiduePrimitive d k) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [centeredResiduePrimitive_step d k (Finset.mem_Icc.mp hd).1]
      ring

theorem rawMobiusCenteredValue_jump (N k : ℕ) :
    rawMobiusCenteredValue N (k+1)-rawMobiusCenteredValue N k =
      mobiusReciprocalSum N - ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ)*divisorIndicator d (k+1) := by
  have hres (d : ℕ) (hd : 0 < d) :
      residueFraction d (k+1)-residueFraction d k =
        1/(d : ℝ)-divisorIndicator d (k+1) := by
    have h := cumulative_balancedDivisor d (k+1) hd
    rw [cumulative_succ, cumulative_balancedDivisor d k hd] at h
    unfold balancedDivisor at h
    linarith
  unfold rawMobiusCenteredValue
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)*
        (residueFraction d (k+1)-residueFraction d k) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      unfold residueFraction residue
      ring
    _ = ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ)-
        (ArithmeticFunction.moebius d : ℝ)*divisorIndicator d (k+1)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hres d (Finset.mem_Icc.mp hd).1]
      ring
    _ = _ := by rw [Finset.sum_sub_distrib]; rfl

/-- Both terms of the signed primitive remainder must be retained. -/
theorem rawMobiusPrimitiveRemainder_point (N k : ℕ) :
    rawMobiusPrimitiveJumpCross N (k+1) -
      mobiusReciprocalSum N*rawMobiusCenteredPrimitive N (k+1) =
    (rawMobiusCenteredValue N k)^2 -
      (rawMobiusCenteredPrimitive N (k+1)*rawMobiusCenteredValue N (k+1)-
        rawMobiusCenteredPrimitive N k*rawMobiusCenteredValue N k) := by
  rw [rawMobiusPrimitiveJumpCross_eq_product]
  have hp := congrArg (fun x : ℝ => x*rawMobiusCenteredValue N k)
    (rawMobiusCenteredPrimitive_step_all N k)
  have hj := congrArg (fun x : ℝ => rawMobiusCenteredPrimitive N (k+1)*x)
    (rawMobiusCenteredValue_jump N k)
  nlinarith only [hp, hj]

theorem rawMobiusCenteredPrimitive_eq_zero_of_common_multiple (N Q : ℕ)
    (hperiod : ∀ d ∈ Finset.Icc 1 N, d ∣ Q) :
    rawMobiusCenteredPrimitive N Q = 0 := by
  unfold rawMobiusCenteredPrimitive
  apply Finset.sum_eq_zero
  intro d hd
  simp [centeredResiduePrimitive, residue, Nat.mod_eq_zero_of_dvd (hperiod d hd)]

/-- The signed remainder has exactly the centered square energy over a full
period. No estimate, cancellation assumption, or RH is used. -/
theorem rawMobiusPrimitiveRemainder_period_sum (N Q : ℕ)
    (hperiod : ∀ d ∈ Finset.Icc 1 N, d ∣ Q) :
    (∑ k ∈ Finset.range Q,
      (rawMobiusPrimitiveJumpCross N (k+1) -
        mobiusReciprocalSum N*rawMobiusCenteredPrimitive N (k+1))) =
      ∑ k ∈ Finset.range Q, (rawMobiusCenteredValue N k)^2 := by
  simp_rw [rawMobiusPrimitiveRemainder_point]
  have htel (L : ℕ) :
      (∑ k ∈ Finset.range L,
        (rawMobiusCenteredPrimitive N (k+1)*rawMobiusCenteredValue N (k+1)-
          rawMobiusCenteredPrimitive N k*rawMobiusCenteredValue N k)) =
        rawMobiusCenteredPrimitive N L*rawMobiusCenteredValue N L -
          rawMobiusCenteredPrimitive N 0*rawMobiusCenteredValue N 0 := by
    induction L with
    | zero => simp
    | succ L ih => rw [Finset.sum_range_succ, ih]; ring
  rw [Finset.sum_sub_distrib, htel Q]
  rw [rawMobiusCenteredPrimitive_eq_zero_of_common_multiple N Q hperiod,
    rawMobiusCenteredPrimitive_eq_zero_of_common_multiple N 0 (fun d _ => dvd_zero d)]
  ring

theorem rawMobiusPrimitiveRemainder_factorial_mean_eq_jordan (N : ℕ) :
    (∑ k ∈ Finset.range N.factorial,
      (rawMobiusPrimitiveJumpCross N (k+1) -
        mobiusReciprocalSum N*rawMobiusCenteredPrimitive N (k+1))) / (N.factorial : ℝ) =
      (∑ q ∈ Finset.Icc 2 N, jordanTwo q *
        (∑ d ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius d : ℝ)/(d : ℝ))*divisorIncidence d q)^2)/12 := by
  rw [rawMobiusPrimitiveRemainder_period_sum N N.factorial (fun d hd =>
    Nat.dvd_factorial (by have := (Finset.mem_Icc.mp hd).1; omega)
      (Finset.mem_Icc.mp hd).2)]
  exact centeredMobius_factorial_variance_eq_jordan N

/-- In the actual arithmetic family, the combined signed remainder has a
positive prime contribution to its uniform period mean. This is not a
Pareto-weighted middle-window bound. -/
theorem rawMobiusPrimitiveRemainder_factorial_mean_ge_prime_count
    (N : ℕ) (hN : 2 ≤ N) :
    (((Finset.Icc (N/2+1) N).filter Nat.Prime).card : ℝ)/16 ≤
    (∑ k ∈ Finset.range N.factorial,
      (rawMobiusPrimitiveJumpCross N (k+1) -
        mobiusReciprocalSum N*rawMobiusCenteredPrimitive N (k+1))) / (N.factorial : ℝ) := by
  rw [rawMobiusPrimitiveRemainder_period_sum N N.factorial (fun d hd =>
    Nat.dvd_factorial (by have := (Finset.mem_Icc.mp hd).1; omega)
      (Finset.mem_Icc.mp hd).2)]
  exact centeredMobius_factorial_variance_ge_top_half_prime_count N hN

end RiemannResearch.RH.Pareto
