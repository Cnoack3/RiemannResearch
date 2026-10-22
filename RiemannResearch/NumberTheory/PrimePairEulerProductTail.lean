import RiemannResearch.NumberTheory.PrimePairEulerProduct
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Effective approximation of the actual twin-prime product

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

All natural cutoffs are
retained. No assertion about counts of twin primes is used or obtained.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.NumberTheory.PrimePairEulerProduct

def partialProduct (N : ℕ) : ℝ :=
  ∏ p ∈ Finset.range N, primePairEulerFactor p

theorem partialProduct_pos (N : ℕ) : 0 < partialProduct N :=
  Finset.prod_pos (fun p _ => primePairEulerFactor_pos p)

theorem partialProduct_le_one (N : ℕ) : partialProduct N ≤ 1 :=
  Finset.prod_le_one (fun p _ => (primePairEulerFactor_pos p).le)
    (fun p _ => primePairEulerFactor_le_one p)

theorem eulerDefect_le_telescoping (p : ℕ) (hp : 3 ≤ p) :
    1 - primePairEulerFactor p ≤ 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hd1 : 0 < (p : ℝ) - 1 := by linarith
  have hd2 : 0 < (p : ℝ) - 2 := by linarith
  have ht : 1 / ((p : ℝ) - 2) - 1 / ((p : ℝ) - 1) =
      1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
    field_simp [ne_of_gt hd1, ne_of_gt hd2]
    ring
  rw [ht]
  by_cases hprime : Nat.Prime p ∧ 2 < p
  · have he : 1 - primePairEulerFactor p = 1 / ((p : ℝ) - 1) ^ 2 := by
      simp only [primePairEulerFactor, if_pos hprime]
      ring
    rw [he]
    apply (div_le_div_iff₀ (sq_pos_of_pos hd1) (mul_pos hd2 hd1)).2
    nlinarith
  · simp only [primePairEulerFactor, if_neg hprime, sub_self]
    positivity

private theorem finite_tail_defect (N K : ℕ) (hN : 3 ≤ N) :
    partialProduct N - partialProduct (N + K) ≤
      1 / ((N : ℝ) - 2) - 1 / (((N + K : ℕ) : ℝ) - 2) := by
  induction K with
  | zero => simp
  | succ K hK =>
      have hp : 3 ≤ N + K := by omega
      have hq := eulerDefect_le_telescoping (N + K) hp
      have hnonneg : 0 ≤ 1 - primePairEulerFactor (N + K) :=
        sub_nonneg.mpr (primePairEulerFactor_le_one (N + K))
      have hm := mul_le_mul_of_nonneg_right
        (partialProduct_le_one (N + K)) hnonneg
      simp only [one_mul] at hm
      have hstep : partialProduct (N + (K + 1)) =
          partialProduct (N + K) * primePairEulerFactor (N + K) := by
        unfold partialProduct
        rw [show N + (K + 1) = (N + K) + 1 by omega, Finset.prod_range_succ]
      have hcast : ((N + (K + 1) : ℕ) : ℝ) - 2 =
          ((N + K : ℕ) : ℝ) - 1 := by
        push_cast
        ring
      rw [hstep, hcast]
      nlinarith

theorem partialProduct_sub_constant_le (N : ℕ) (hN : 3 ≤ N) :
    partialProduct N - twinPrimeConstant ≤ 1 / ((N : ℝ) - 2) := by
  have hlim : Tendsto (fun M : ℕ => partialProduct N - partialProduct M)
      atTop (𝓝 (partialProduct N - twinPrimeConstant)) :=
    tendsto_const_nhds.sub primePairEulerFactor_multipliable.hasProd.tendsto_prod_nat
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with M hM
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hM
  have htail := finite_tail_defect N K hN
  have hz : 0 ≤ 1 / (((N + K : ℕ) : ℝ) - 2) := by
    have hp : (3 : ℝ) ≤ ((N + K : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ N + K by omega)
    exact (one_div_pos.mpr (by linarith)).le
  linarith

theorem partialProduct_certified_interval (N : ℕ) (hN : 3 ≤ N) :
    partialProduct N - 1 / ((N : ℝ) - 2) ≤ twinPrimeConstant ∧
      twinPrimeConstant ≤ partialProduct N := by
  have h := partialProduct_sub_constant_le N hN
  exact ⟨by linarith, twinPrimeConstant_le_finite_product (Finset.range N)⟩

end RiemannResearch.NumberTheory.PrimePairEulerProduct
