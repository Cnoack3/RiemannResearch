import RiemannResearch.RH.RoughProfileBounds

/-!
# The unconditional diagonal-energy limit in series form

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 8, equation (40). This proves the actual diagonal-profile limit
before evaluation of its squarefree Euler product. The majorant is a
constant multiple of the original summable Pareto weight.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators Topology
open Filter OneBoundaryRepair

noncomputable section

/-- Normalized diagonal contribution of one positive rough core. -/
def roughDiagonalTerm (N q : ℕ) : ℝ :=
  if 0 < q ∧ Nat.Coprime q 6 then
    (ArithmeticFunction.moebius q : ℝ) ^ 2 * roughComponentAverage q N else 0

/-- The limiting squarefree rough-core series, not yet evaluated using ζ-values. -/
def roughDiagonalSeries : ℝ :=
  ∑' q : ℕ, if 0 < q ∧ Nat.Coprime q 6 then
    (ArithmeticFunction.moebius q : ℝ) ^ 2 / (9 * (q : ℝ) ^ 2) else 0

private theorem moebius_real_square_le_one (q : ℕ) :
    (ArithmeticFunction.moebius q : ℝ) ^ 2 ≤ 1 := by
  have hmu : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hm := mul_self_le_mul_self (abs_nonneg (ArithmeticFunction.moebius q : ℝ)) hmu
  simpa only [← pow_two, sq_abs, one_pow] using hm

private theorem reciprocal_square_le_pareto (q : ℕ) :
    4 / (q : ℝ) ^ 2 ≤ 8 * positiveWeight q := by
  by_cases hq : q = 0
  · simp [hq, positiveWeight]
  have hqR : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
  unfold positiveWeight
  rw [mul_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hqR) (by positivity)).mpr
  nlinarith

theorem roughDiagonalTerm_norm_bound (N q : ℕ) :
    ‖roughDiagonalTerm N q‖ ≤ 8 * positiveWeight q := by
  unfold roughDiagonalTerm
  split_ifs with hq
  · have havg := roughComponentAverage_bounds q N hq.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) havg.1)]
    calc
      _ ≤ 1 * roughComponentAverage q N :=
        mul_le_mul_of_nonneg_right (moebius_real_square_le_one q) havg.1
      _ ≤ 4 / (q : ℝ) ^ 2 := by simpa using havg.2
      _ ≤ 8 * positiveWeight q := reciprocal_square_le_pareto q
  · simp only [norm_zero]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (positiveWeight_nonneg q)

theorem roughDiagonalTerm_summable (N : ℕ) : Summable (roughDiagonalTerm N) :=
  (positiveWeight_summable.mul_left 8).of_norm_bounded (roughDiagonalTerm_norm_bound N)

/-- Cesàro and dominated convergence prove the actual unconditional series-form limit. -/
theorem roughDiagonalSeries_tendsto :
    Tendsto (fun N : ℕ => ∑' q : ℕ, roughDiagonalTerm N q) atTop (𝓝 roughDiagonalSeries) := by
  unfold roughDiagonalSeries
  apply tendsto_tsum_of_dominated_convergence (positiveWeight_summable.mul_left 8)
  · intro q
    by_cases hq : 0 < q ∧ Nat.Coprime q 6
    · simp only [roughDiagonalTerm, if_pos hq]
      simpa only [mul_one_div] using
        tendsto_const_nhds.mul (roughComponentAverage_tendsto q hq.1)
    · simp only [roughDiagonalTerm, if_neg hq]
      exact tendsto_const_nhds
  · exact Eventually.of_forall roughDiagonalTerm_norm_bound

theorem roughHeadProfile_eq_zero_of_lt (q k : ℕ) (hk : k < q) :
    roughHeadProfile q k = 0 := by
  have h2 : k < 2 * q := by omega
  have h3 : k < 3 * q := by omega
  have h6 : k < 6 * q := by omega
  simp [roughHeadProfile, floorBlock, Nat.div_eq_of_lt hk,
    Nat.div_eq_of_lt h2, Nat.div_eq_of_lt h3, Nat.div_eq_of_lt h6]

theorem roughComponentAverage_eq_zero_of_lt (q N : ℕ) (hN : N < q) :
    roughComponentAverage q N = 0 := by
  unfold roughComponentAverage
  have hs : (∑ k ∈ Finset.range N,
      positiveWeight (k + 1) * (roughHeadProfile q (k + 1)) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hq : k + 1 < q := by have := Finset.mem_range.mp hk; omega
    rw [roughHeadProfile_eq_zero_of_lt q (k + 1) hq]
    simp
  rw [hs, mul_zero]

/-- The finite arithmetic diagonal D_N from the report, with its genuine profile. -/
def roughDiagonalHead (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (N + 1), if 0 < q ∧ Nat.Coprime q 6 then
    (ArithmeticFunction.moebius q : ℝ) ^ 2 *
      ∑ k ∈ Finset.range N,
        positiveWeight (k + 1) * (roughHeadProfile q (k + 1)) ^ 2 else 0

/-- No tail in q was discarded: all cores beyond N contribute identically zero. -/
theorem roughDiagonalTerm_tsum_exact (N : ℕ) :
    (∑' q : ℕ, roughDiagonalTerm N q) = roughDiagonalHead N / (N : ℝ) := by
  have hs : (∑' q : ℕ, roughDiagonalTerm N q) =
      ∑ q ∈ Finset.range (N + 1), roughDiagonalTerm N q := by
    apply tsum_eq_sum
    intro q hq
    have hN : N < q := by have hh : ¬ q < N + 1 := fun h => hq (Finset.mem_range.mpr h); omega
    simp [roughDiagonalTerm, roughComponentAverage_eq_zero_of_lt q N hN]
  rw [hs]
  unfold roughDiagonalHead
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  unfold roughDiagonalTerm roughComponentAverage
  split_ifs <;> ring

/-- Equation (40) before the separate evaluation of the squarefree Euler product. -/
theorem roughDiagonalHead_div_tendsto :
    Tendsto (fun N : ℕ => roughDiagonalHead N / (N : ℝ)) atTop (𝓝 roughDiagonalSeries) := by
  simpa only [roughDiagonalTerm_tsum_exact] using roughDiagonalSeries_tendsto

end
end RiemannResearch.RH.Pareto
