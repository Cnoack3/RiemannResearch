import RiemannResearch.RH.ParetoWeights
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Tactic.Linarith

/-!
# Exact positive Pareto multiplicative benchmark

Source: the user-provided DPP/Fredholm conversation, 20 September 2026,
for the benchmark formula. The proof reduces the finite Pareto product to
Euler's sine product and then invokes Mathlib's checked Euler product theorem.
This is a scalar infinite-product computation, independent of RH and of any
operator Fredholm determinant identification.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

def paretoProductRoot : ℝ := (Real.sqrt 5 - 1) / 2

theorem paretoProductRoot_bounds : 0 < paretoProductRoot ∧ paretoProductRoot < 1 := by
  have hs : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  dsimp [paretoProductRoot]
  constructor <;> nlinarith

theorem paretoProductRoot_quadratic : paretoProductRoot ^ 2 + paretoProductRoot = 1 := by
  have hs : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  dsimp [paretoProductRoot]
  nlinarith

def paretoProductBenchmark : ℝ := Real.sin (Real.pi * paretoProductRoot) / Real.pi

theorem paretoProductBenchmark_pos : 0 < paretoProductBenchmark := by
  apply div_pos _ Real.pi_pos
  apply Real.sin_pos_of_mem_Ioo
  exact ⟨mul_pos Real.pi_pos paretoProductRoot_bounds.1,
    by simpa using mul_lt_mul_of_pos_left paretoProductRoot_bounds.2 Real.pi_pos⟩

theorem one_sub_paretoWeight_factorization (n : ℕ) :
    1 - paretoWeight n =
      (1 - paretoProductRoot / ((n : ℝ) + 1)) *
        (1 + paretoProductRoot / ((n : ℝ) + 2)) := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hq := paretoProductRoot_quadratic
  unfold paretoWeight
  field_simp [h1, h2]
  nlinarith

/-- Exact finite comparison to Euler's sine product, including the end factor. -/
theorem pareto_product_eq_euler_product (N : ℕ) :
    (1 + paretoProductRoot) * (∏ j ∈ Finset.range N, (1 - paretoWeight j)) =
      (1 + paretoProductRoot / ((N : ℝ) + 1)) *
        (∏ j ∈ Finset.range N, (1 - paretoProductRoot ^ 2 / ((j : ℝ) + 1) ^ 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs :
        (1 + paretoProductRoot / ((N : ℝ) + 1)) * (1 - paretoWeight N) =
          (1 + paretoProductRoot / ((N : ℝ) + 2)) *
            (1 - paretoProductRoot ^ 2 / ((N : ℝ) + 1) ^ 2) := by
      rw [one_sub_paretoWeight_factorization]
      field_simp [show (N : ℝ) + 1 ≠ 0 by positivity,
        show (N : ℝ) + 2 ≠ 0 by positivity]
      ring
    simp only [Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]
    rw [show ((N : ℝ) + 1) + 1 = (N : ℝ) + 2 by ring]
    calc
      _ = ((1 + paretoProductRoot) *
          (∏ j ∈ Finset.range N, (1 - paretoWeight j))) * (1 - paretoWeight N) := by ring
      _ = ((1 + paretoProductRoot / ((N : ℝ) + 1)) *
          (∏ j ∈ Finset.range N,
            (1 - paretoProductRoot ^ 2 / ((j : ℝ) + 1) ^ 2))) *
          (1 - paretoWeight N) := by rw [ih]
      _ = (∏ j ∈ Finset.range N,
            (1 - paretoProductRoot ^ 2 / ((j : ℝ) + 1) ^ 2)) *
          ((1 + paretoProductRoot / ((N : ℝ) + 1)) * (1 - paretoWeight N)) := by ring
      _ = _ := by rw [hs]; ring

/-- The complete scalar benchmark is sin(π(√5−1)/2)/π, and it is positive. -/
theorem pareto_product_tendsto_benchmark :
    Tendsto (fun N => ∏ j ∈ Finset.range N, (1 - paretoWeight j)) atTop
      (𝓝 paretoProductBenchmark) := by
  have hr := paretoProductRoot_bounds.1
  have hr1 : 1 + paretoProductRoot ≠ 0 := by linarith
  have hp : Real.pi * paretoProductRoot ≠ 0 := mul_ne_zero Real.pi_ne_zero hr.ne'
  have heuler : Tendsto
      (fun N => ∏ j ∈ Finset.range N,
        (1 - paretoProductRoot ^ 2 / ((j : ℝ) + 1) ^ 2)) atTop
      (𝓝 (Real.sin (Real.pi * paretoProductRoot) / (Real.pi * paretoProductRoot))) := by
    have h := (Real.tendsto_euler_sin_prod paretoProductRoot).div_const
      (Real.pi * paretoProductRoot)
    simpa only [mul_div_cancel_left₀ _ hp] using h
  have hdiv : Tendsto (fun N : ℕ => paretoProductRoot / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul paretoProductRoot
  have hend : Tendsto (fun N : ℕ => 1 + paretoProductRoot / ((N : ℝ) + 1))
      atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hdiv
  have h := (hend.mul heuler).div_const (1 + paretoProductRoot)
  have hq : paretoProductRoot * (1 + paretoProductRoot) = 1 := by
    nlinarith [paretoProductRoot_quadratic]
  have hlimit :
      (1 * (Real.sin (Real.pi * paretoProductRoot) / (Real.pi * paretoProductRoot))) /
        (1 + paretoProductRoot) = paretoProductBenchmark := by
    rw [one_mul, div_div, mul_assoc, hq, mul_one]
    rfl
  rw [hlimit] at h
  convert h using 1
  funext N
  rw [← pareto_product_eq_euler_product]
  exact (mul_div_cancel_left₀ _ hr1).symm

end RiemannResearch.RH.Pareto
