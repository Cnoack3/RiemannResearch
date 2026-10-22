import RiemannResearch.Analysis.ActualL2Norm
import RiemannResearch.RH.NymanActualTailEnergy
import RiemannResearch.RH.NymanInverseCoefficientBound

/-!
# The explicit crude single-conductor tail bound

Equation (9.8) follows from the actual finite-translate identity for the
completed test, the ordinary L2 triangle inequality, and the independently
proved Möbius coefficient bound (9.7). This upper bound has exponential rate
one-half at a remote support gap. It is not the subexponential RH target.
-/

open MeasureTheory
open scoped BigOperators Topology
open RiemannResearch.Analysis

namespace RiemannResearch.RH

/-- The finite inverse synthesis commutes with the full arithmetic return. -/
theorem nymanFullReturn_inversePotential_commute (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a : ℝ} (ha : ∀ x < a, v x = 0) :
    nymanFullReturn n (nymanInversePotential n M hn v) =
      nymanInversePotential n M hn (nymanFullReturn n v) := by
  simp only [nymanFullReturn, nymanInversePotential_eq_return]
  rw [← arithmeticReturn_mul _ _ ha, mul_comm, arithmeticReturn_mul _ _ ha]

/-- Actual differentiation commutes with the finite inverse synthesis. -/
theorem poleCancellationOperator_nymanInversePotential (n M : ℕ) (hn : 2 ≤ n)
    {u : ℝ → ℂ} {a : ℝ} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) :
    poleCancellationOperator (nymanInversePotential n M hn u) =
      nymanInversePotential n M hn (poleCancellationOperator u) := by
  have hd2 := arithmeticReturn_iteratedDeriv (nymanConductorInversePrefix n M hn) hu ha 2
  rw [← nymanInversePotential_eq_return, ← nymanInversePotential_eq_return] at hd2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hd2
  funext y
  change deriv (deriv (nymanInversePotential n M hn u)) y -
    (1 / 4 : ℝ) • nymanInversePotential n M hn u y = _
  rw [hd2]
  simp only [nymanInversePotential, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [poleCancellationOperator, smul_sub, smul_smul, mul_comm]

/-- The literal finite translated-channel identity preceding (9.8). -/
theorem nymanCompletedTest_eq_finite_translates (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a : ℝ} (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) :
    nymanCompletedTest n M hn v =
      ∑ k ∈ Finset.Icc 1 M, (nymanConductorInverse n hn k / Real.sqrt k : ℝ) •
        (fun y => poleCancellationOperator (nymanFullReturn n v) (y - Real.log k)) := by
  have hcont : ContDiff ℝ (↑(⊤ : ℕ∞)) (nymanFullReturn n v) :=
    arithmeticReturn_contDiff _ hv ha
  have hzero : ∀ y < a, nymanFullReturn n v y = 0 :=
    fun y hy => arithmeticReturn_zero_below _ ha hy
  rw [nymanCompletedTest, nymanFullReturn_inversePotential_commute n M hn ha,
    poleCancellationOperator_nymanInversePotential n M hn hcont hzero]
  funext y
  simp only [nymanInversePotential, Finset.sum_apply, Pi.smul_apply]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro k hk hnot
    have hk0 : k = 0 := by
      simp only [Finset.mem_range, Finset.mem_Icc] at *
      omega
    simp [hk0]

private theorem memLp_two_of_smoothSuperexponential {u : ℝ → ℂ}
    (hu : SmoothSuperexponentialDecay u) : MemLp u 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hu.1.continuous.aestronglyMeasurable).mpr
  have hi := (hu.decay.integrable_crossCorrelation hu.decay
    hu.1.continuous hu.1.continuous 0).norm
  simpa only [add_zero, norm_mul, norm_star, pow_two] using hi

/-- The exact coefficient-norm bound before inserting the crude arithmetic
estimate. Every function and L2 precondition is supplied by the construction. -/
theorem nymanCompletedTest_actualL2Norm_le (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    actualL2Norm (nymanCompletedTest n M hn v) ≤
      (∑ k ∈ Finset.Icc 1 M, |nymanConductorInverse n hn k| / Real.sqrt k) *
        actualL2Norm (poleCancellationOperator (nymanFullReturn n v)) := by
  letI : NeZero n := ⟨by omega⟩
  have hbase := (smoothSuperexponentialDecay_nymanFullReturn hv ha hb n).poleCancellationOperator
  rw [nymanCompletedTest_eq_finite_translates n M hn hv ha]
  have h := actualL2Norm_sum_smul_translate_le (Finset.Icc 1 M)
    (fun k => nymanConductorInverse n hn k / Real.sqrt k)
    (fun k : ℕ => Real.log k) (memLp_two_of_smoothSuperexponential hbase) hbase.1.continuous
  have habs (k : ℕ) : |nymanConductorInverse n hn k / Real.sqrt k| =
      |nymanConductorInverse n hn k| / Real.sqrt k := by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg k)]
  simpa only [habs] using h

/-- Equation (9.8), for the actual arithmetic tail and actual square-integral
L2 norms. The explicit coefficient estimate is proved in (9.7). -/
theorem nymanCompletionTail_actualL2Norm_crude_upper_bound (n M : ℕ)
    (hn : 2 ≤ n) (hM : 1 ≤ M) {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    actualL2Norm (nymanCompletionTail n M hn v) ≤
      actualL2Norm (poleCancellationOperator v) +
        2 * (n : ℝ) * actualL2Norm (poleCancellationOperator (nymanFullReturn n v)) *
          Real.sqrt M * (1 + (Nat.log n M : ℝ)) := by
  have hG := smoothSuperexponentialDecay_nymanCompletedTest n M hn hv ha hb
  have hf := (smoothSuperexponentialDecay_of_compact_interval hv ha hb).poleCancellationOperator
  have htri := actualL2Norm_sub_le (memLp_two_of_smoothSuperexponential hG)
    (memLp_two_of_smoothSuperexponential hf)
  have hcoeff := sum_abs_nymanConductorInverse_div_sqrt_le n M hn hM
  have hsize := (nymanCompletedTest_actualL2Norm_le n M hn hv ha hb).trans
    (mul_le_mul_of_nonneg_right hcoeff (actualL2Norm_nonneg _))
  change actualL2Norm (nymanCompletedTest n M hn v - poleCancellationOperator v) ≤ _
  exact htri.trans (by nlinarith [hsize])

end RiemannResearch.RH
