import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Algebraic independence of normalized residue atoms

Source: user-provided atom/carry CRT argument (2026-11-17).
The proof uses the existing exact Möbius difference functional from
`ParetoResidueDuality`. It is purely algebraic and does not assume any
Hilbert-space density, orthogonality, or convergence.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.Pareto

private theorem mobiusDifference_fintype {ι : Type*} [Fintype ι]
    (m : ℕ) (c : ι → ℝ) (f : ι → ℕ → ℝ) :
    mobiusDifference m (fun k => ∑ i, c i * f i k) =
      ∑ i, c i * mobiusDifference m (f i) := by
  unfold mobiusDifference
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Every finite family of distinct conductors greater than one has independent
normalized atoms. In particular this applies to every finite CRT divisor stage. -/
theorem residueFraction_linearIndependent {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    LinearIndependent ℝ (fun i => residueFraction (d i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hz (k : ℕ) : ∑ j, (c j / (d j : ℝ)) * residue (d j) k = 0 := by
    have h := congrFun hc k
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, residueFraction,
      residue, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hsum : (∑ j, (c j / (d j : ℝ)) *
      mobiusDifference (d i) (residue (d j))) = 0 := by
    rw [← mobiusDifference_fintype]
    simp [mobiusDifference, hz]
  have heq (j : ι) : d i = d j ↔ i = j := hinj.eq_iff
  simp_rw [mobiusDifference_residue _ _ (hd i), heq] at hsum
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hsum
  have hdi : (d i : ℝ) ≠ 0 := by exact_mod_cast (show d i ≠ 0 by have := hd i; omega)
  have hcancel : c i / (d i : ℝ) * (-(d i : ℝ)) = -c i := by
    field_simp
  rw [hcancel] at hsum
  exact neg_eq_zero.mp hsum

end RiemannResearch.RH.ArithmeticCumulative
