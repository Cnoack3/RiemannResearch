import Mathlib.Algebra.BigOperators.Field
import RiemannResearch.Analysis.TriadicRotationSeparation
import RiemannResearch.Analysis.LogarithmicPacking
import RiemannResearch.Analysis.BlockPrefixAssembly
import RiemannResearch.Analysis.AbelPrefixBound

/-!
# Logarithmic prefixes of the actual irrational rotation

Source: user-provided argument, sections 3--4 of
RH/Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md, September 10, 2026.
The minimum denominator, centered orbit points, logarithmic packing, and
integer exponential separation are assembled here. No prefix estimate is
assumed for the actual log 3 / log 2 rotation.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators
noncomputable section

theorem rotation_log_inverse_prefix_le {α : ℝ} (hα : Irrational α)
    (C : ℝ) (hC : 0 ≤ C)
    (hlog : ∀ h : ℕ, 0 < h → Real.log (1 / rotationNearestDistance α h) ≤ C * h)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, Real.log (1 / rotationNearestDistance α (i+1))) ≤
      2 * (C + 1 + Real.log 4) * N := by
  by_cases hN : N = 0
  · simp [hN]
  obtain ⟨q, hq, hqN, hmin⟩ :=
    exists_rotationNearestDistance_minimum α (Nat.pos_of_ne_zero hN)
  have hL : 0 ≤ C + 1 + Real.log 4 := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  apply Finset.sum_range_le_two_mul_of_block_bound
    (fun i => Real.log (1 / rotationNearestDistance α (i+1))) N q hq hqN
    (C + 1 + Real.log 4) hL
  intro b s hs hend
  apply Finset.sum_log_inv_abs_le_of_block_spacing
    (Finset.range s) (fun i => rotationCenteredError α (q*b+i+1))
    q hq (by simpa using hs) C hC
  · intro i hi
    exact rotationNearestDistance_pos hα (by omega)
  · intro i hi
    have hiN : q*b+i+1 ≤ N := by
      have := Finset.mem_range.mp hi
      omega
    have hm := hmin (q*b+i+1) (by omega) hiN
    have hδ := rotationNearestDistance_pos hα hq
    have hinv : 1 / rotationNearestDistance α (q*b+i+1) ≤
        1 / rotationNearestDistance α q := one_div_le_one_div_of_le hδ hm
    exact le_trans (Real.log_le_log (by
      exact one_div_pos.mpr (rotationNearestDistance_pos hα (by omega))) hinv)
      (hlog q hq)
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hminimum : ∀ h : ℕ, 0 < h → h < q →
        rotationNearestDistance α q ≤ rotationNearestDistance α h := by
      intro h hh hhq
      exact hmin h hh (by omega)
    rcases lt_or_gt_of_ne hij with h | h
    · have hz := rotationCenteredError_block_spacing hα hminimum
        (i := q*b+i+1) (j := q*b+j+1) (by omega) (by omega)
      rw [abs_sub_comm] at hz
      exact hz.le
    · exact (rotationCenteredError_block_spacing hα hminimum
        (i := q*b+j+1) (j := q*b+i+1) (by omega) (by omega)).le

/-- The explicit logarithmic prefix bound for the actual triadic rotation. -/
theorem triadicRotation_log_inverse_prefix_le (N : ℕ) :
    (∑ i ∈ Finset.range N,
      Real.log (1 / rotationNearestDistance triadicRotation (i+1))) ≤
      2 * (1 + Real.log 24) * N := by
  have h := rotation_log_inverse_prefix_le triadicRotation_irrational
    (Real.log 6) (Real.log_nonneg (by norm_num))
    (fun q hq => by simpa only [mul_comm] using triadicRotation_log_inverse_distance_le hq) N
  have he : Real.log 24 = Real.log 6 + Real.log 4 := by
    rw [show (24 : ℝ) = 6 * 4 by norm_num,
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
  rw [he]
  nlinarith

/-- Candidate raw-Gram majorant; the prefix estimate is proved below, while
its application to actual step pairings is a separate geometric theorem. -/
def triadicLogGramMajorant : ℕ → ℝ
  | 0 => 0
  | n+1 => 5/4 + (Real.log (1 / Real.log 2) +
      Real.log (1 / rotationNearestDistance triadicRotation (n+1))) / (4 * Real.log 2)

def triadicLogGramPrefixConstant : ℝ :=
  5/4 + (Real.log (1 / Real.log 2) + 2 * (1 + Real.log 24)) / (4 * Real.log 2)

theorem triadicLogGramMajorant_nonneg (n : ℕ) : 0 ≤ triadicLogGramMajorant n := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hbase : 0 ≤ Real.log (1 / Real.log 2) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ h2).mpr (by simpa using h2le)
  cases n with
  | zero => simp [triadicLogGramMajorant]
  | succ n =>
    have hδ := triadicRotation_distance_pos (by omega : 0 < n+1)
    have hδhalf := rotationNearestDistance_le_half triadicRotation (n+1)
    have hdlog : 0 ≤ Real.log (1 / rotationNearestDistance triadicRotation (n+1)) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ hδ).mpr
      linarith
    dsimp [triadicLogGramMajorant]
    positivity

theorem triadicLogGramMajorant_shifted_prefix_le (N : ℕ) :
    (∑ i ∈ Finset.range N, triadicLogGramMajorant (i+1)) ≤
      triadicLogGramPrefixConstant * N := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := triadicRotation_log_inverse_prefix_le N
  simp only [triadicLogGramMajorant]
  rw [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  dsimp [triadicLogGramPrefixConstant]
  have hh := div_le_div_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ 4 * Real.log 2)
  calc
    _ = (5/4 : ℝ)*N + Real.log (1 / Real.log 2)*N / (4*Real.log 2) +
        (∑ i ∈ Finset.range N,
          Real.log (1 / rotationNearestDistance triadicRotation (i+1))) / (4*Real.log 2) := by ring
    _ ≤ (5/4 : ℝ)*N + Real.log (1 / Real.log 2)*N / (4*Real.log 2) +
        (2*(1+Real.log 24)*N) / (4*Real.log 2) := by linarith only [hh]
    _ = _ := by ring

theorem triadicLogGramMajorant_prefix_le (N : ℕ) :
    prefixSum triadicLogGramMajorant N ≤ triadicLogGramPrefixConstant * N := by
  have he := Finset.sum_range_succ' triadicLogGramMajorant N
  rw [Finset.sum_range_succ] at he
  rw [show triadicLogGramMajorant 0 = 0 from rfl, add_zero] at he
  have hN := triadicLogGramMajorant_nonneg N
  have hs := triadicLogGramMajorant_shifted_prefix_le N
  unfold prefixSum
  linarith

theorem triadicLogGramPrefixConstant_nonneg : 0 ≤ triadicLogGramPrefixConstant := by
  have h := triadicLogGramMajorant_shifted_prefix_le 1
  norm_num only [Finset.sum_range_one, mul_one] at h
  exact le_trans (triadicLogGramMajorant_nonneg 1) h

end
end RiemannResearch.Analysis
