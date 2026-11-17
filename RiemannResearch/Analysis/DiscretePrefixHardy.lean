import RiemannResearch.Analysis.DiscreteTailHardy
import Mathlib.Tactic

/-!
# Finite prefix Hardy inequality
Finite duality applied to the repository's adjoint Hardy inequality.
RH consumer: occurrence-to-atom compression in `sdf_modified.pdf`, (143).
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.DiscretePrefixHardy

def prefixSum (a : ℕ → ℝ) (r : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 r, a n

theorem finite_hardy_sq (a : ℕ → ℝ) (T : ℕ) :
    (∑ r ∈ Finset.Icc 1 T, (prefixSum a r / r) ^ 2) ≤
      4 * ∑ n ∈ Finset.Icc 1 T, a n ^ 2 := by
  let b : ℕ → ℝ := fun r => prefixSum a r / (r : ℝ) ^ 2
  let S : ℝ := ∑ r ∈ Finset.Icc 1 T, (prefixSum a r / r) ^ 2
  let D : ℝ := ∑ n ∈ Finset.Icc 1 T, a n ^ 2
  have hswap : (∑ n ∈ Finset.Icc 1 T, a n * (∑ r ∈ Finset.Icc n T, b r)) = S := by
    have ht (n : ℕ) (hn : n ∈ Finset.Icc 1 T) :
        (∑ r ∈ Finset.Icc n T, b r) =
          ∑ r ∈ Finset.Icc 1 T, if n ≤ r then b r else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc]
      have := Finset.mem_Icc.mp hn
      omega
    calc
      _ = ∑ n ∈ Finset.Icc 1 T, ∑ r ∈ Finset.Icc 1 T,
          a n * (if n ≤ r then b r else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [ht n hn, Finset.mul_sum]
      _ = ∑ r ∈ Finset.Icc 1 T, b r * prefixSum a r := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        have hf : (Finset.Icc 1 T).filter (fun n => n ≤ r) = Finset.Icc 1 r := by
          ext n
          simp only [Finset.mem_filter, Finset.mem_Icc]
          have := Finset.mem_Icc.mp hr
          omega
        simp_rw [mul_ite, mul_zero]
        rw [← Finset.sum_filter, hf, ← Finset.sum_mul]
        exact mul_comm _ _
      _ = S := by
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [b]
        ring
  have hb : (∑ r ∈ Finset.Icc 1 T, ((r : ℝ) * b r) ^ 2) = S := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr0 : (r : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Finset.mem_Icc.mp hr).1 : r ≠ 0)
    dsimp [b]
    field_simp
  have htail := DiscreteTailHardy.finite_adjoint_hardy_sq b T
  rw [hb] at htail
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 T) a
    (fun n => ∑ r ∈ Finset.Icc n T, b r)
  rw [hswap] at hcs
  have hS : 0 ≤ S := Finset.sum_nonneg (fun r hr => sq_nonneg _)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun r hr => sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_left htail hD
  change S ≤ 4 * D
  by_cases hz : S = 0
  · rw [hz]
    positivity
  · have hp : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    change S ^ 2 ≤ D * _ at hcs
    nlinarith

end RiemannResearch.Analysis.DiscretePrefixHardy
