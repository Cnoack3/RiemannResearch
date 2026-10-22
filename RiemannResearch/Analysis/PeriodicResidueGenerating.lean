import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact finite generating function of a periodic residue charge

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 9, for the rational generating-function identity. The proof below
uses finite geometric sums and cancellation of the total residue charge.

This module proves the finite generating identity. It does not infer a Taylor
order from moments or invoke the Bernoulli expansion.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteResidueCharge

def geometricSum (q : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, q ^ j

def weightedGeometricSum (q : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (j : ℝ) * q ^ j

def periodicResidueSum (q : ℝ) (n L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L, ((j % n : ℕ) : ℝ) * q ^ j

private theorem geometricSum_succ (q : ℝ) (n : ℕ) :
    geometricSum q (n + 1) = geometricSum q n + q ^ n := by
  exact Finset.sum_range_succ _ _

private theorem weightedGeometricSum_succ (q : ℝ) (n : ℕ) :
    weightedGeometricSum q (n + 1) = weightedGeometricSum q n + (n : ℝ) * q ^ n := by
  exact Finset.sum_range_succ _ _

theorem geometricSum_identity (q : ℝ) (n : ℕ) :
    (1 - q) * geometricSum q n = 1 - q ^ n := by
  induction n with
  | zero => simp [geometricSum]
  | succ n ih =>
    rw [geometricSum_succ, pow_succ, mul_add, ih]
    ring

theorem weightedGeometricSum_identity (q : ℝ) (n : ℕ) :
    (1 - q) * weightedGeometricSum q n =
      q * geometricSum q n - (n : ℝ) * q ^ n := by
  induction n with
  | zero => simp [geometricSum, weightedGeometricSum]
  | succ n ih =>
    rw [weightedGeometricSum_succ, geometricSum_succ, Nat.cast_succ, pow_succ]
    calc
      (1 - q) * (weightedGeometricSum q n + (n : ℝ) * q ^ n) =
          (1 - q) * weightedGeometricSum q n +
            (n : ℝ) * q ^ n * (1 - q) := by ring
      _ = q * geometricSum q n - (n : ℝ) * q ^ n +
            (n : ℝ) * q ^ n * (1 - q) := by rw [ih]
      _ = _ := by ring

private theorem geometricSum_pos (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) :
    0 < geometricSum q n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [geometricSum_succ]
  have hs : 0 ≤ geometricSum q k :=
    Finset.sum_nonneg (fun j _ => (pow_pos hq j).le)
  exact add_pos_of_nonneg_of_pos hs (pow_pos hq k)

private theorem one_sub_pow_ne_zero (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℕ) (hn : 0 < n) : 1 - q ^ n ≠ 0 := by
  have hu : ∀ k : ℕ, q ^ k ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc
        q ^ k * q ≤ 1 * q := mul_le_mul_of_nonneg_right ih hq0.le
        _ ≤ 1 := by linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hp : q ^ (k + 1) ≤ q := by
    simpa [pow_succ] using mul_le_mul_of_nonneg_right (hu k) hq0.le
  simp only [Nat.succ_eq_add_one]
  exact ne_of_gt (by linarith)

theorem residue_generating_average (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℕ) (hn : 0 < n) :
    weightedGeometricSum q n / geometricSum q n =
      q / (1 - q) - (n : ℝ) * q ^ n / (1 - q ^ n) := by
  have hG : geometricSum q n ≠ 0 := ne_of_gt (geometricSum_pos q hq0 n hn)
  have hq : 1 - q ≠ 0 := ne_of_gt (by linarith)
  apply (div_eq_iff hG).mpr
  apply mul_left_cancel₀ hq
  calc
    (1 - q) * weightedGeometricSum q n =
        q * geometricSum q n - (n : ℝ) * q ^ n := weightedGeometricSum_identity q n
    _ = (1 - q) *
        ((q / (1 - q) - (n : ℝ) * q ^ n / (1 - q ^ n)) * geometricSum q n) := by
      rw [← geometricSum_identity q n]
      field_simp [hq, hG]

private theorem geometricSum_add (q : ℝ) (a b : ℕ) :
    geometricSum q (a + b) = geometricSum q a + q ^ a * geometricSum q b := by
  unfold geometricSum
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact pow_add q a j

private theorem periodicResidueSum_add_block (q : ℝ) (n k : ℕ) :
    periodicResidueSum q n (k * n + n) =
      periodicResidueSum q n (k * n) + q ^ (k * n) * weightedGeometricSum q n := by
  unfold periodicResidueSum
  rw [Finset.sum_range_add]
  congr 1
  unfold weightedGeometricSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hmod : (k * n + j) % n = j := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
  rw [hmod, pow_add]
  ring

/-- Repeating an integral number of periods leaves the normalized generating
average unchanged. This form does not divide by possibly zero polynomials. -/
theorem periodicResidueSum_block_identity (q : ℝ) (n k : ℕ) :
    periodicResidueSum q n (k * n) * geometricSum q n =
      weightedGeometricSum q n * geometricSum q (k * n) := by
  induction k with
  | zero => simp [periodicResidueSum, geometricSum]
  | succ k ih =>
    rw [Nat.succ_mul, periodicResidueSum_add_block, geometricSum_add]
    calc
      (periodicResidueSum q n (k * n) +
          q ^ (k * n) * weightedGeometricSum q n) * geometricSum q n =
        periodicResidueSum q n (k * n) * geometricSum q n +
          q ^ (k * n) * weightedGeometricSum q n * geometricSum q n := by ring
      _ = weightedGeometricSum q n * geometricSum q (k * n) +
          q ^ (k * n) * weightedGeometricSum q n * geometricSum q n := by rw [ih]
      _ = _ := by ring

theorem periodic_residue_generating_average (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n L : ℕ) (hn : 0 < n) (hL : 0 < L) (hdiv : n ∣ L) :
    periodicResidueSum q n L / geometricSum q L =
      q / (1 - q) - (n : ℝ) * q ^ n / (1 - q ^ n) := by
  rw [← residue_generating_average q hq0 hq1 n hn]
  apply (div_eq_div_iff (ne_of_gt (geometricSum_pos q hq0 L hL))
    (ne_of_gt (geometricSum_pos q hq0 n hn))).mpr
  obtain ⟨k, rfl⟩ := hdiv
  simpa [Nat.mul_comm] using periodicResidueSum_block_identity q n k

variable {ι : Type*} [Fintype ι]

def periodicChargeAverage (b : ι → ℝ) (n : ι → ℕ) (q : ℝ) (L : ℕ) : ℝ :=
  (∑ j ∈ Finset.range L, (1 - ∑ i, b i * ((j % n i : ℕ) : ℝ)) * q ^ j) /
    geometricSum q L

/-- The exact common-period generating identity for a charge of total mass
zero. All conductors divide the selected positive common period. -/
theorem periodicChargeAverage_eq (b : ι → ℝ) (n : ι → ℕ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (L : ℕ) (hL : 0 < L)
    (hn : ∀ i, 0 < n i) (hdiv : ∀ i, n i ∣ L) (hzero : ∑ i, b i = 0) :
    periodicChargeAverage b n q L =
      1 + ∑ i, b i * ((n i : ℝ) * q ^ n i / (1 - q ^ n i)) := by
  classical
  have hnum :
      (∑ j ∈ Finset.range L, (1 - ∑ i, b i * ((j % n i : ℕ) : ℝ)) * q ^ j) =
        geometricSum q L - ∑ i, b i * periodicResidueSum q (n i) L := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
    congr 1
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    unfold periodicResidueSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold periodicChargeAverage
  rw [hnum, sub_div, div_self (ne_of_gt (geometricSum_pos q hq0 L hL)), Finset.sum_div]
  simp_rw [mul_div_assoc, periodic_residue_generating_average q hq0 hq1 _ L
    (hn _) hL (hdiv _), mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul]
  simp only [zero_sub, sub_neg_eq_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

end RiemannResearch.Analysis.FiniteResidueCharge
