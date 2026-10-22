import RiemannResearch.RH.ParetoCompressedMellinNorm
import Mathlib.Algebra.Order.Floor.Semiring

/-! A uniform full-tail compressed Mellin energy bound. The proof splits the
actual nonnegative cosine series at floor(t), retaining every term. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CompressedMellin

private theorem paretoWeight_tail (N : ℕ) :
    (∑' n : ℕ, paretoWeight (n + N)) = 1 / ((N : ℝ) + 1) := by
  have h := paretoWeight_hasSum.summable.sum_add_tsum_nat_add N
  rw [paretoWeight_hasSum.tsum_eq, paretoWeight_partial_sum] at h
  linarith

/-- Complete cosine mass admits an elementary linear bound at every nonnegative frequency. -/
theorem cosineMass_le_linear (t : ℝ) (ht : 0 ≤ t) :
    cosineMass t ≤ 1 + 6 * t := by
  let N : ℕ := ⌊t⌋₊
  have hN : (N : ℝ) ≤ t := Nat.floor_le ht
  have hNt : t < (N : ℝ) + 1 := Nat.lt_floor_add_one t
  have hhead : (∑ n ∈ Finset.range N, cosineDeficit t n) ≤ 2 * (N : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range N, (2 : ℝ) :=
        Finset.sum_le_sum (fun n _ => cosineDeficit_le_two t n)
      _ = _ := by simp; ring
  have htail : (∑' n, cosineDeficit t (n + N)) ≤ t ^ 2 / ((N : ℝ) + 1) := by
    have h := ((summable_nat_add_iff N).mpr (cosineDeficit_summable t)).tsum_le_tsum
      (fun n => cosineDeficit_le_weight t (n + N))
      (((summable_nat_add_iff N).mpr paretoWeight_hasSum.summable).mul_left (t ^ 2))
    simpa only [tsum_mul_left, paretoWeight_tail, div_eq_mul_inv, one_mul] using! h
  have htail' : t ^ 2 / ((N : ℝ) + 1) ≤ t := by
    rw [div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)]
    nlinarith
  have hsplit := (cosineDeficit_summable t).sum_add_tsum_nat_add N
  unfold cosineMass
  nlinarith

/-- The entire complexified Riesz energy is at most two at every frequency. -/
theorem compressedMellinEnergy_le_two (t : ℝ) : compressedMellinEnergy t ≤ 2 := by
  rw [compressedMellinEnergy_eq, div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  nlinarith [cosineMass_le_quadratic t]

/-- Uniform bound with exactly the constant required by the phase-centered provider. -/
theorem compressedMellinEnergy_le_seven_div (t : ℝ) (ht : 1 ≤ t) :
    compressedMellinEnergy t ≤ 7 / t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [compressedMellinEnergy_eq,
    div_le_div_iff₀ (by positivity : 0 < 1 + t ^ 2) ht0]
  have h := mul_le_mul_of_nonneg_right (cosineMass_le_linear t ht0.le) ht0.le
  nlinarith [sq_nonneg (t - 1)]

end RiemannResearch.RH.Pareto.CompressedMellin
