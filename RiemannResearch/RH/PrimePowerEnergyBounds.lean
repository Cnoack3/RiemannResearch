import RiemannResearch.RH.PrimePowerEnumeration
import RiemannResearch.Analysis.PowerCellEnergy

/-!
# Unconditional bounds for the actual signed prime-power energy

Source: user-provided V_Zeta_Vector_Spaces_Research_2026-09-16.md,
Sections 15-18, for the target and its exact weights and charges.
The input Chebyshev upper bound is Mathlib's checked theorem
`Chebyshev.psi_le_const_mul_self`:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Chebyshev.html#Chebyshev.psi_le_const_mul_self
It supports the linear envelope, not an RH-strength error estimate.

The actual signed cumulative square is retained throughout, including the
critical reference mean. Changing damping does not recenter at a different
mean. `actual_damped_signed_abel_identity` retains every earlier-current
cross term and the terminal subtraction; `actual_damped_total_reset_cost`
identifies the same boundary-reset correction in every weight.

Established: A_N <= (log 4 + 4)^2 (q_N - 2), and the damped energy is bounded
by (log 4 + 4)^2 * 2^(2-s)/(s-2) for s > 2, with summability proved.
The two `SignedArithmetic...Bound` definitions are OPEN propositions, not
assumptions, axioms, or theorems. No proof for the range 1 < s <= 2 or for
all positive subpolynomial exponents is supplied. The analytic equivalence
with Mathlib's RiemannHypothesis is not formalized here.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.LinearAlgebra.CumulativeCellEnergy
open RiemannResearch.Analysis.ReciprocalCellEnergy
open RiemannResearch.Analysis.PowerCellEnergy

namespace RiemannResearch.RH.PrimePowerCriticalEnergy

theorem actual_critical_energy_le_linear (q : ℕ → ℕ) (hq : StrictMono q)
    (hpos : ∀ i, 0 < q i) (N : ℕ) :
    weightedPrefixEnergy (cellWeight q) (signedJump q) N ≤
      (Real.log 4 + 4) ^ 2 * ((q N : ℝ) - q 0) := by
  have hK : 1 ≤ Real.log 4 + 4 := by
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hcell (i : ℕ) :
      cellWeight q i * cumulative (signedJump q) (i + 1) ^ 2 ≤
        (Real.log 4 + 4) ^ 2 * ((q (i + 1) : ℝ) - q i) := by
    rw [cumulative_signedJump]
    change intervalWeight (q i) (q (i + 1)) *
      (cumulative (actualJump q) (i + 1) - intervalMean (q i) (q (i + 1))) ^ 2 ≤ _
    apply interval_excess_le_linear_of_level_bound (by exact_mod_cast hpos i)
      (by exact_mod_cast hq (Nat.lt_succ_self i)) hK
    · exact Finset.sum_nonneg (fun j hj => ArithmeticFunction.vonMangoldt_nonneg)
    · exact (actualCumulative_le_psi q hq i).trans
        (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (Real.log 4 + 4) ^ 2 * ((q (i + 1) : ℝ) - q i) :=
      Finset.sum_le_sum (fun i hi => hcell i)
    _ = _ := by rw [← Finset.mul_sum, cumulative_difference (fun i => (q i : ℝ))]

theorem enumerated_critical_energy_le_linear (N : ℕ) :
    weightedPrefixEnergy (cellWeight primePowerEnumeration)
      (signedJump primePowerEnumeration) N ≤
        (Real.log 4 + 4) ^ 2 * ((primePowerEnumeration N : ℝ) - 2) := by
  simpa [primePowerEnumeration_zero] using
    actual_critical_energy_le_linear primePowerEnumeration
      primePowerEnumeration_strictMono primePowerEnumeration_pos N

def SignedArithmeticSubpolynomialBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    weightedPrefixEnergy (cellWeight primePowerEnumeration)
      (signedJump primePowerEnumeration) N ≤ C * (primePowerEnumeration N : ℝ) ^ δ


theorem enumerated_discrepancy_sq_le (i : ℕ) :
    cumulative (signedJump primePowerEnumeration) (i + 1) ^ 2 ≤
      (Real.log 4 + 4) ^ 2 * (primePowerEnumeration i : ℝ) ^ 2 := by
  let a : ℝ := primePowerEnumeration i
  let b : ℝ := primePowerEnumeration (i + 1)
  let K : ℝ := Real.log 4 + 4
  have ha : 0 < a := by dsimp [a]; exact_mod_cast primePowerEnumeration_pos i
  have hab : a < b := by dsimp [a, b]; exact_mod_cast primePowerEnumeration_strictMono (Nat.lt_succ_self i)
  have hb : b ≤ 2 * a := by dsimp [a, b]; exact_mod_cast primePowerEnumeration_succ_le_twice i
  have hK : 2 ≤ K := by
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp [K]
    linarith
  have hc0 := Chebyshev.psi_nonneg a
  have hc : Chebyshev.psi a ≤ K * a := Chebyshev.psi_le_const_mul_self ha.le
  have hm0 := intervalMean_nonneg ha hab
  have hm : intervalMean a b ≤ K * a :=
    (intervalMean_le_right ha hab).trans (hb.trans (by nlinarith))
  rw [cumulative_signedJump, enumerated_cumulative_eq_psi]
  change (Chebyshev.psi a - intervalMean a b) ^ 2 ≤ K ^ 2 * a ^ 2
  have hs : (Chebyshev.psi a - intervalMean a b) ^ 2 ≤ (K * a) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  nlinarith

def dampedCellWeight (q : ℕ → ℕ) (s : ℝ) (i : ℕ) : ℝ :=
  powerIntervalWeight (q i) (q (i + 1)) s

theorem dampedCellWeight_one (q : ℕ → ℕ) : dampedCellWeight q 1 = cellWeight q := by
  funext i
  simp [dampedCellWeight, powerIntervalWeight, cellWeight, intervalWeight, one_div]
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
  simp

theorem actual_damped_total_reset_cost (q : ℕ → ℕ) (s : ℝ) (N : ℕ) :
    totalCumulativeEnergy (dampedCellWeight q s)
      (resetJump (optimalJumpCorrection (cellWeight q) (logMoment q) (actualJump q)) N) =
        weightedPrefixEnergy (dampedCellWeight q s) (signedJump q) N := by
  rw [reset_total_energy]
  unfold weightedPrefixEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [cumulative_optimalJumpCorrection, cumulative_signedJump]
  ring

theorem enumerated_damped_energy_le (s : ℝ) (hs : 2 < s) (N : ℕ) :
    weightedPrefixEnergy (dampedCellWeight primePowerEnumeration s)
      (signedJump primePowerEnumeration) N ≤
        (Real.log 4 + 4) ^ 2 * (2 : ℝ) ^ (2 - s) / (s - 2) := by
  let q := primePowerEnumeration
  let K : ℝ := Real.log 4 + 4
  have hcell (i : ℕ) :
      dampedCellWeight q s i * cumulative (signedJump q) (i + 1) ^ 2 ≤
        K ^ 2 / (s - 2) * ((q i : ℝ) ^ (2 - s) - (q (i + 1) : ℝ) ^ (2 - s)) := by
    have h := powerIntervalWeight_mul_sq_le
      (a := (primePowerEnumeration i : ℝ)) (b := (primePowerEnumeration (i + 1) : ℝ))
      (by exact_mod_cast primePowerEnumeration_pos i)
      (by exact_mod_cast primePowerEnumeration_strictMono (Nat.lt_succ_self i))
      hs (enumerated_discrepancy_sq_le i)
    convert h using 1 <;> dsimp [dampedCellWeight, q, K]
    ring
  have htel : (∑ i ∈ Finset.range N,
      ((q i : ℝ) ^ (2 - s) - (q (i + 1) : ℝ) ^ (2 - s))) =
        (q 0 : ℝ) ^ (2 - s) - (q N : ℝ) ^ (2 - s) := by
    have h := cumulative_difference (fun i => (q i : ℝ) ^ (2 - s)) N
    rw [Finset.sum_sub_distrib] at h ⊢
    linarith
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        K ^ 2 / (s - 2) * ((q i : ℝ) ^ (2 - s) - (q (i + 1) : ℝ) ^ (2 - s)) :=
      Finset.sum_le_sum (fun i hi => hcell i)
    _ = K ^ 2 / (s - 2) * ((2 : ℝ) ^ (2 - s) - (q N : ℝ) ^ (2 - s)) := by
      rw [← Finset.mul_sum, htel]
      simp [q, primePowerEnumeration_zero]
    _ ≤ K ^ 2 / (s - 2) * (2 : ℝ) ^ (2 - s) := by
      apply mul_le_mul_of_nonneg_left
        (sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (div_nonneg (sq_nonneg _) (by linarith))
    _ = _ := by dsimp [K]; ring

theorem enumerated_damped_energy_summable (s : ℝ) (hs : 2 < s) :
    Summable (fun i => dampedCellWeight primePowerEnumeration s i *
      cumulative (signedJump primePowerEnumeration) (i + 1) ^ 2) := by
  apply RiemannResearch.Analysis.NonnegativeEnergy.summable_of_nonnegative_prefix_bound
    _ _ _ (enumerated_damped_energy_le s hs)
  intro i
  apply mul_nonneg _ (sq_nonneg _)
  exact powerIntervalWeight_nonneg
    (by exact_mod_cast primePowerEnumeration_pos i)
    (by exact_mod_cast (primePowerEnumeration_strictMono (Nat.lt_succ_self i)).le)
    (by linarith)

theorem actual_damped_signed_abel_identity (q : ℕ → ℕ) (s : ℝ) (N : ℕ) :
    weightedPrefixEnergy (dampedCellWeight q s) (signedJump q) N =
      (∑ i ∈ Finset.range N, ((q i : ℝ) ^ (-s) / s) *
        ((signedJump q i) ^ 2 + 2 * signedJump q i * cumulative (signedJump q) i)) -
      ((q N : ℝ) ^ (-s) / s) * cumulative (signedJump q) N ^ 2 := by
  have he : dampedCellWeight q s =
      fun i => (q i : ℝ) ^ (-s) / s - (q (i + 1) : ℝ) ^ (-s) / s := by
    funext i
    exact sub_div _ _ _
  rw [he]
  exact weightedPrefixEnergy_signed_identity _ _ _

def SignedArithmeticDampedBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
    weightedPrefixEnergy (dampedCellWeight primePowerEnumeration (1 + ε))
      (signedJump primePowerEnumeration) N ≤ C


end RiemannResearch.RH.PrimePowerCriticalEnergy
