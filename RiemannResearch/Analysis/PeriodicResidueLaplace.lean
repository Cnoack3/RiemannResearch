import RiemannResearch.Analysis.PeriodicResidueGenerating
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exact finite periodic Laplace identity

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 9, for the identity. This module substitutes `q = exp(-t)` into the
proved finite generating identity. It applies to `t > 0`; it makes no claim
about the removable value or Taylor coefficients at zero.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteResidueCharge

private theorem exp_neg_nat_pow (t : ℝ) (n : ℕ) :
    Real.exp (-t) ^ n = Real.exp (-((n : ℝ) * t)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    rw [show -(((n : ℝ) + 1) * t) = -((n : ℝ) * t) + (-t) by ring,
      Real.exp_add]

private theorem exp_neg_ratio (a : ℝ) (ha : 0 < a) :
    Real.exp (-a) / (1 - Real.exp (-a)) = 1 / (Real.exp a - 1) := by
  have he : 0 < Real.exp a := Real.exp_pos a
  have he1 : 1 < Real.exp a := Real.one_lt_exp_iff.mpr ha
  have hsub : 1 - (Real.exp a)⁻¹ ≠ 0 := by
    intro hz
    have hi : (Real.exp a)⁻¹ = 1 := by linarith
    have hh := congrArg (fun x : ℝ => x⁻¹) hi
    simp only [inv_inv, inv_one] at hh
    linarith
  simp only [Real.exp_neg]
  field_simp [ne_of_gt he, ne_of_gt (sub_pos.mpr he1), hsub]

variable {ι : Type*} [Fintype ι]

/-- The finite periodic average of the residual `1 - ∑ bᵢ rₙᵢ`. -/
def periodicLaplaceAverage (b : ι → ℝ) (n : ι → ℕ) (t : ℝ) (L : ℕ) : ℝ :=
  (∑ j ∈ Finset.range L,
    (1 - ∑ i, b i * ((j % n i : ℕ) : ℝ)) * Real.exp (-((j : ℝ) * t))) /
  (∑ j ∈ Finset.range L, Real.exp (-((j : ℝ) * t)))

/-- Exact positive-parameter Laplace formula with all residue charges retained.
The zero-total-charge condition cancels the common geometric contribution. -/
theorem periodicLaplaceAverage_eq (b : ι → ℝ) (n : ι → ℕ)
    (t : ℝ) (ht : 0 < t) (L : ℕ) (hL : 0 < L)
    (hn : ∀ i, 0 < n i) (hdiv : ∀ i, n i ∣ L) (hzero : ∑ i, b i = 0) :
    periodicLaplaceAverage b n t L =
      1 + ∑ i, b i * ((n i : ℝ) / (Real.exp ((n i : ℝ) * t) - 1)) := by
  classical
  have hq0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hk : periodicLaplaceAverage b n t L =
      periodicChargeAverage b n (Real.exp (-t)) L := by
    unfold periodicLaplaceAverage periodicChargeAverage geometricSum
    simp_rw [exp_neg_nat_pow]
  rw [hk, periodicChargeAverage_eq b n _ hq0 hq1 L hL hn hdiv hzero]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [exp_neg_nat_pow, mul_div_assoc,
    exp_neg_ratio ((n i : ℝ) * t) (mul_pos (Nat.cast_pos.mpr (hn i)) ht)]
  ring

end RiemannResearch.Analysis.FiniteResidueCharge
