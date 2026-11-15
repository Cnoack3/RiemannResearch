/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullTriangularMobiusRepair
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.NumberTheory.FinitePositiveHyperbola
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import RiemannResearch.Analysis.ReciprocalSquareRootSum
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Explicit Möbius coefficients and reciprocal slope of the triangular repair

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 2.
The finite divisor/multiple rearrangement is exact. The scalar bounds retain
the actual anchored forward differences and introduce no research assumption.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFullTriangularMobiusRepair
open ZetaTwoHilbert ZetaTwoProbability Pareto
open RiemannResearch.NumberTheory RiemannResearch.Analysis

def mobiusHeadCoefficient (u : ℕ → ℝ) (m : ℕ) : ℝ := mobiusDifference m u

def reciprocalHeadSlope (N : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, mobiusHeadCoefficient u m / (m : ℝ)

/-- The actual Möbius coefficient is the finite convolution of the forward differences. -/
theorem mobiusHeadCoefficient_eq (u : ℕ → ℝ) (m : ℕ) :
    mobiusHeadCoefficient u m =
      ∑ k ∈ m.divisors, (ArithmeticFunction.moebius (m / k) : ℝ) *
        (u k - u (k - 1)) := rfl

/-- Exact reciprocal coefficient sum, with every finite Möbius partial sum retained. -/
theorem reciprocalHeadSlope_reindex (N : ℕ) (u : ℕ → ℝ) :
    reciprocalHeadSlope N u =
      ∑ k ∈ Finset.Icc 1 N, ((u k - u (k - 1)) / (k : ℝ)) *
        mobiusReciprocalSum (N / k) := by
  classical
  have hswap := sum_positive_hyperbola N (fun k j =>
    ((u k - u (k - 1)) * (ArithmeticFunction.moebius j : ℝ)) /
      ((k * j : ℕ) : ℝ))
  calc
    reciprocalHeadSlope N u =
        ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ m.divisors,
          ((u k - u (k - 1)) * (ArithmeticFunction.moebius (m / k) : ℝ)) /
            ((k * (m / k) : ℕ) : ℝ) := by
      unfold reciprocalHeadSlope mobiusHeadCoefficient mobiusDifference
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      have hp : k * (m / k) = m := by
        simpa only [Nat.mul_comm] using Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hk)
      rw [hp]
      ring
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 (N / k),
        ((u k - u (k - 1)) * (ArithmeticFunction.moebius j : ℝ)) /
          ((k * j : ℕ) : ℝ) := hswap.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold mobiusReciprocalSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring

/-- Absolute reciprocal slope before applying finite Cauchy--Schwarz. -/
theorem reciprocalHeadSlope_abs_le (N : ℕ) (u : ℕ → ℝ) :
    |reciprocalHeadSlope N u| ≤
      ∑ k ∈ Finset.Icc 1 N, |u k - u (k - 1)| / (k : ℝ) := by
  rw [reciprocalHeadSlope_reindex]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Finset.mem_Icc.mp hk).1
  have hmu : |mobiusReciprocalSum (N / k)| ≤ 1 := by
    by_cases h : N / k = 0
    · simp [h, mobiusReciprocalSum]
    · exact mobiusReciprocalSum_abs_le_one _ (Nat.pos_of_ne_zero h)
  rw [abs_mul, abs_div, abs_of_pos hkR]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hmu
    (div_nonneg (abs_nonneg _) hkR.le)

private theorem inverse_square_Icc_sum_le (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) ^ 2) ≤ zetaTwo := by
  have hs := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have h := hs.sum_le_tsum (Finset.Icc 1 N) (fun k _ => by positivity)
  rw [← zetaTwo_eq_nat_sum] at h
  simpa only [div_pow, one_pow] using h

/-- Complete inverse-square mass supplies the exact finite weighted ℓ¹ bound. -/
theorem forwardDifference_weighted_sum_le (N : ℕ) (u : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 N, |u k - u (k - 1)| / (k : ℝ)) ≤
      Real.sqrt zetaTwo * Real.sqrt
        (∑ k ∈ Finset.Icc 1 N, (u k - u (k - 1)) ^ 2) := by
  have hE : 0 ≤ ∑ k ∈ Finset.Icc 1 N, (u k - u (k - 1)) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
    (fun k => |u k - u (k - 1)|) (fun k => 1 / (k : ℝ))
  simp only [sq_abs, mul_one_div] at hCS
  apply (sq_le_sq₀ (Finset.sum_nonneg fun k _ => by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt zetaTwo_pos.le, Real.sq_sqrt hE]
  exact hCS.trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (inverse_square_Icc_sum_le N) hE)

theorem reciprocalHeadSlope_abs_le_difference_energy (N : ℕ) (u : ℕ → ℝ) :
    |reciprocalHeadSlope N u| ≤ Real.sqrt zetaTwo * Real.sqrt
      (∑ k ∈ Finset.Icc 1 N, (u k - u (k - 1)) ^ 2) :=
  (reciprocalHeadSlope_abs_le N u).trans (forwardDifference_weighted_sum_le N u)

private theorem floor_sqrt_weight_le (N k : ℕ) (hk : 0 < k) :
    (1 / Real.sqrt (k : ℝ)) * (2 * Real.sqrt ((N / k : ℕ) : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hM : 0 ≤ ((N / k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul : ((N / k : ℕ) : ℝ) * (k : ℝ) ≤ N := by
    exact_mod_cast (show (N / k) * k ≤ N by
      simpa only [Nat.mul_comm] using Nat.mul_div_le N k)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, div_pow, one_pow, Real.sq_sqrt hkR.le,
    Real.sq_sqrt hM, Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [show (1 / (k : ℝ)) * (2 ^ 2 * ((N / k : ℕ) : ℝ)) =
      4 * ((N / k : ℕ) : ℝ) / (k : ℝ) by ring,
    show (2 ^ 2 * (N : ℝ)) / (k : ℝ) ^ 2 =
      4 * (N : ℝ) / (k : ℝ) ^ 2 by ring]
  apply (div_le_div_iff₀ hkR (sq_pos_of_pos hkR)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ 4 * (k : ℝ))]

/-- Absolute coefficient mass with the inverse-square-root conductor weight,
before the final finite Cauchy--Schwarz step. -/
theorem mobiusHeadCoefficient_sqrt_mass_le (N : ℕ) (u : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 N, |mobiusHeadCoefficient u m| / Real.sqrt (m : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) *
        (∑ k ∈ Finset.Icc 1 N, |u k - u (k - 1)| / (k : ℝ)) := by
  have hswap := sum_positive_hyperbola N (fun k j =>
    |u k - u (k - 1)| / Real.sqrt ((k * j : ℕ) : ℝ))
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ m.divisors,
        |u k - u (k - 1)| / Real.sqrt (m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      unfold mobiusHeadCoefficient mobiusDifference
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius (m / k) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m / k)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ m.divisors,
        |u k - u (k - 1)| / Real.sqrt ((k * (m / k) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      exact_mod_cast (show m = k * (m / k) by
        simpa only [Nat.mul_comm] using (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hk)).symm)
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 (N / k),
        |u k - u (k - 1)| / Real.sqrt ((k * j : ℕ) : ℝ) := hswap.symm
    _ ≤ ∑ k ∈ Finset.Icc 1 N,
        (2 * Real.sqrt (N : ℝ)) * (|u k - u (k - 1)| / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
      calc
        (∑ j ∈ Finset.Icc 1 (N / k),
            |u k - u (k - 1)| / Real.sqrt ((k * j : ℕ) : ℝ)) =
            (|u k - u (k - 1)| / Real.sqrt (k : ℝ)) *
              (∑ j ∈ Finset.Icc 1 (N / k), 1 / Real.sqrt (j : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg k)]
          ring
        _ ≤ (|u k - u (k - 1)| / Real.sqrt (k : ℝ)) *
            (2 * Real.sqrt ((N / k : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inverse_sqrt_Icc_le _) (by positivity)
        _ ≤ (2 * Real.sqrt (N : ℝ)) * (|u k - u (k - 1)| / (k : ℝ)) := by
          have hh := mul_le_mul_of_nonneg_left (floor_sqrt_weight_le N k hk0)
            (abs_nonneg (u k - u (k - 1)))
          calc
            (|u k - u (k - 1)| / Real.sqrt (k : ℝ)) *
                (2 * Real.sqrt ((N / k : ℕ) : ℝ)) =
                |u k - u (k - 1)| *
                  ((1 / Real.sqrt (k : ℝ)) * (2 * Real.sqrt ((N / k : ℕ) : ℝ))) := by ring
            _ ≤ |u k - u (k - 1)| * (2 * Real.sqrt (N : ℝ) / (k : ℝ)) := hh
            _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]

theorem mobiusHeadCoefficient_sqrt_mass_le_difference_energy (N : ℕ) (u : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 N, |mobiusHeadCoefficient u m| / Real.sqrt (m : ℝ)) ≤
      (2 * Real.sqrt (N : ℝ) * Real.sqrt zetaTwo) * Real.sqrt
        (∑ k ∈ Finset.Icc 1 N, (u k - u (k - 1)) ^ 2) := by
  have h := (mobiusHeadCoefficient_sqrt_mass_le N u).trans
    (mul_le_mul_of_nonneg_left (forwardDifference_weighted_sum_le N u) (by positivity))
  simpa only [mul_assoc] using h

/-- The step synthesis is exactly the paper's Möbius-coefficient normal form,
including its common compensating atom and its signed reciprocal slope. -/
theorem triangularRepair_mobius_normal_form (N : ℕ) (u : ℕ → ℝ) :
    triangularRepair N u =
      -(∑ m ∈ Finset.Icc 1 N, mobiusHeadCoefficient u m • qResidue m) +
      (((N + 1 : ℕ) : ℝ) * reciprocalHeadSlope N u) • qResidue (N + 1) := by
  classical
  have houter : triangularRepair N u =
      ∑ k ∈ Finset.Icc 1 N, (u k - u (k - 1)) • triangularStep N (k - 1) := by
    unfold triangularRepair
    apply Finset.sum_bij (fun k _ => k + 1)
    · intro k hk
      exact Finset.mem_Icc.mpr ⟨Nat.succ_pos k, by
        have h := Finset.mem_range.mp hk
        omega⟩
    · intro k hk j hj hkj
      omega
    · intro j hj
      obtain ⟨hj1, hjN⟩ := Finset.mem_Icc.mp hj
      exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k hk
      simp only [Nat.add_sub_cancel]
  have hmain :
      (∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 (N / k),
        ((u k - u (k - 1)) * (ArithmeticFunction.moebius j : ℝ)) • qResidue (k * j)) =
      ∑ m ∈ Finset.Icc 1 N, mobiusHeadCoefficient u m • qResidue m := by
    rw [sum_positive_hyperbola]
    apply Finset.sum_congr rfl
    intro m hm
    calc
      (∑ k ∈ m.divisors,
          ((u k - u (k - 1)) * (ArithmeticFunction.moebius (m / k) : ℝ)) •
            qResidue (k * (m / k))) =
          ∑ k ∈ m.divisors,
            ((ArithmeticFunction.moebius (m / k) : ℝ) * (u k - u (k - 1))) • qResidue m := by
        apply Finset.sum_congr rfl
        intro k hk
        have hp : k * (m / k) = m := by
          simpa only [Nat.mul_comm] using Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hk)
        rw [hp, mul_comm (u k - u (k - 1))]
      _ = _ := by rw [← Finset.sum_smul]; rfl
  have hterm :
      (∑ k ∈ Finset.Icc 1 N,
        ((u k - u (k - 1)) *
          ((((N + 1 : ℕ) : ℝ) / (k : ℝ)) * mobiusReciprocalSum (N / k))) •
            qResidue (N + 1)) =
      (((N + 1 : ℕ) : ℝ) * reciprocalHeadSlope N u) • qResidue (N + 1) := by
    rw [← Finset.sum_smul, reciprocalHeadSlope_reindex, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [houter]
  calc
    (∑ k ∈ Finset.Icc 1 N, (u k - u (k - 1)) • triangularStep N (k - 1)) =
        ∑ k ∈ Finset.Icc 1 N,
          (-(∑ j ∈ Finset.Icc 1 (N / k),
            ((u k - u (k - 1)) * (ArithmeticFunction.moebius j : ℝ)) • qResidue (k * j)) +
          ((u k - u (k - 1)) *
            ((((N + 1 : ℕ) : ℝ) / (k : ℝ)) * mobiusReciprocalSum (N / k))) •
              qResidue (N + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold triangularStep
      rw [Nat.sub_add_cancel (Finset.mem_Icc.mp hk).1]
      simp only [smul_add, smul_neg, Finset.smul_sum, smul_smul]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hmain, hterm]

/-- Full physical formula, valid above the head as well as on it. -/
theorem triangularRepair_sequence_full (N : ℕ) (u : ℕ → ℝ) (n : ℕ) :
    qSequence (triangularRepair N u) n =
      (∑ m ∈ Finset.Icc 1 N, mobiusHeadCoefficient u m * ((n / m : ℕ) : ℝ)) -
        (((N + 1 : ℕ) : ℝ) * reciprocalHeadSlope N u) *
          ((n / (N + 1) : ℕ) : ℝ) := by
  rw [triangularRepair_mobius_normal_form]
  change qSequenceLinear (_ + _) n = _
  simp only [map_add, map_neg, map_sum, map_smul, Pi.add_apply, Pi.neg_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change -(∑ m ∈ Finset.Icc 1 N, mobiusHeadCoefficient u m * qSequence (qResidue m) n) +
    (((N + 1 : ℕ) : ℝ) * reciprocalHeadSlope N u) * qSequence (qResidue (N + 1)) n = _
  have hsum :
      (∑ m ∈ Finset.Icc 1 N, mobiusHeadCoefficient u m * qSequence (qResidue m) n) =
      (n : ℝ) * reciprocalHeadSlope N u -
        ∑ m ∈ Finset.Icc 1 N, mobiusHeadCoefficient u m * ((n / m : ℕ) : ℝ) := by
    calc
      _ = ∑ m ∈ Finset.Icc 1 N,
          ((n : ℝ) * (mobiusHeadCoefficient u m / (m : ℝ)) -
            mobiusHeadCoefficient u m * ((n / m : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [qSequence_qResidue,
          residueFraction_eq_div_sub_floor m n (Finset.mem_Icc.mp hm).1]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; rfl
  rw [hsum, qSequence_qResidue,
    residueFraction_eq_div_sub_floor (N + 1) n (Nat.succ_pos N)]
  have hr : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hr]
  <;> ring

end RiemannResearch.RH.QFullTriangularMobiusRepair
