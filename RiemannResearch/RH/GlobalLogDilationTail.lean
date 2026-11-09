import RiemannResearch.RH.GlobalLogDilation
import RiemannResearch.NumberTheory.MangoldtPowerTail
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Quantitative tails for the global logarithmic dilation

The cutoff after N terms includes conductors 2 through N+1.
The explicit tail bound is O_s((N+1)^(1-s)/log(N+1)).
For floorLog sigma this is O_sigma(N^(1/2-sigma)/log N).
The critical series is not absolutely summable, by the prime reciprocal
subseries. This does not by itself exclude conditional operator convergence.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.GlobalLogDilation
open RiemannResearch.NumberTheory.MangoldtPowerTail
open Filter
open scoped Topology

theorem logTerm_norm_le_arithmetic (s : ℝ) (n : ℕ) :
    ‖logTerm s n‖ ≤ logWeight n * ((n+2:ℕ):ℝ)^(-s) := by
  rw [logTerm, norm_smul, Real.norm_of_nonneg
    (mul_nonneg (logWeight_nonneg n) (Real.rpow_nonneg (by positivity) _))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (normalizedDilation_norm_le n)
    (mul_nonneg (logWeight_nonneg n) (Real.rpow_nonneg (by positivity) _))

theorem logTail_partial_bound {s : ℝ} (hs : 1 < s) {N : ℕ}
    (hN : 1 ≤ N) (K : ℕ) :
    ‖∑ i ∈ Finset.range K, logTerm s (i+N)‖ ≤
      chebyshevConstant * (1+s/(s-1)) * ((N+1:ℕ):ℝ)^(1-s) /
        Real.log ((N+1:ℕ):ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range K, ‖logTerm s (i+N)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range K,
        ArithmeticFunction.vonMangoldt (i+N+2) / Real.log ((i+N+2:ℕ):ℝ) *
          ((i+N+2:ℕ):ℝ)^(-s) := by
      apply Finset.sum_le_sum
      intro i hi
      exact logTerm_norm_le_arithmetic s (i+N)
    _ = ∑ k ∈ Finset.Ioc (N+1) (N+K+1),
        ArithmeticFunction.vonMangoldt k / Real.log (k:ℝ) * (k:ℝ)^(-s) := by
      apply Finset.sum_bij (fun i _ => i+N+2)
      · intro i hi
        simp only [Finset.mem_range, Finset.mem_Ioc] at *
        omega
      · intro i hi j hj hij
        omega
      · intro k hk
        refine ⟨k-(N+2), ?_, ?_⟩
        · simp only [Finset.mem_Ioc, Finset.mem_range] at *
          omega
        · simp only [Finset.mem_Ioc] at hk
          omega
      · intro i hi
        rfl
    _ ≤ _ := log_power_tail_finite_bound hs (by omega) (by omega)

theorem globalLog_tail_bound {s : ℝ} (hs : 1 < s) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖globalLog s - ∑ n ∈ Finset.range N, logTerm s n‖ ≤
      chebyshevConstant * (1+s/(s-1)) * ((N+1:ℕ):ℝ)^(1-s) /
        Real.log ((N+1:ℕ):ℝ) := by
  have hsum := (summable_nat_add_iff N).mpr (summable_logTerm hs)
  have ht := hsum.hasSum.tendsto_sum_nat.norm
  have hb := le_of_tendsto ht (Filter.Eventually.of_forall (logTail_partial_bound hs hN))
  have he := (summable_logTerm hs).sum_add_tsum_nat_add N
  change (∑ n ∈ Finset.range N, logTerm s n) +
    (∑' n, logTerm s (n+N)) = globalLog s at he
  have he' : globalLog s - ∑ n ∈ Finset.range N, logTerm s n =
      ∑' n, logTerm s (n+N) := by rw [← he]; abel
  rw [he']
  exact hb

theorem floorLog_tail_bound {σ : ℝ} (hσ : 1/2 < σ) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖floorLog σ - ∑ n ∈ Finset.range N, logTerm (σ+1/2) n‖ ≤
      chebyshevConstant * (1+(σ+1/2)/(σ-1/2)) *
        ((N+1:ℕ):ℝ)^(1/2-σ) / Real.log ((N+1:ℕ):ℝ) := by
  have h := globalLog_tail_bound (s:=σ+1/2) (by linarith) hN
  convert h using 1 <;> congr 1 <;> ring

theorem normalizedDilation_norm_eq_one (n : ℕ) : ‖normalizedDilation n‖ = 1 := by
  apply le_antisymm (normalizedDilation_norm_le n)
  have hone : ‖hilbertOne‖ = 1 := by
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  have hu : ‖normalizedDilation n hilbertOne‖ = ‖hilbertOne‖ :=
    (hilbertNormalizedDilation (n+2) (by omega)).norm_map _
  have h := (normalizedDilation n).le_opNorm hilbertOne
  simpa only [hu, hone, mul_one] using h

theorem logTerm_norm_eq_arithmetic (s : ℝ) (n : ℕ) :
    ‖logTerm s n‖ = logWeight n * ((n+2:ℕ):ℝ)^(-s) := by
  rw [logTerm, norm_smul, Real.norm_of_nonneg
    (mul_nonneg (logWeight_nonneg n) (Real.rpow_nonneg (by positivity) _)),
    normalizedDilation_norm_eq_one, mul_one]

theorem not_summable_critical_logTerm_norm :
    ¬ Summable (fun n => ‖logTerm 1 n‖) := by
  intro h
  have hA : Summable (fun k : ℕ =>
      ArithmeticFunction.vonMangoldt k / Real.log (k:ℝ) * (k:ℝ)^(-(1:ℝ))) := by
    apply (summable_nat_add_iff 2).mp
    exact h.congr (fun n => logTerm_norm_eq_arithmetic 1 n)
  apply not_summable_one_div_on_primes
  apply Summable.of_nonneg_of_le _ _ hA
  · intro n
    exact Set.indicator_nonneg (fun k hk => by positivity) n
  · intro n
    by_cases hp : Nat.Prime n
    · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hp]
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp,
        div_self (Real.log_pos (by exact_mod_cast hp.one_lt)).ne',
        one_mul, Real.rpow_neg_one, one_div]
    · simp only [Set.indicator, Set.mem_setOf_eq, if_neg hp]
      by_cases hn : n = 0
      · subst n
        simp
      · exact mul_nonneg
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end RiemannResearch.RH.Pareto.GlobalLogDilation
