import RiemannResearch.RH.ParetoGibbsSchurEnergy
import Mathlib.Analysis.PSeries

/-!
# Gamma weights giving approximate extremizers of the pi/4 bound

The weights have a divergent square sum but a uniformly bounded total Schur
defect after truncation. All sums defining each row remain infinite, and the
omitted part is controlled by the exact Pareto tail, not a finite experiment.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter
noncomputable section

private theorem gamma_succ_one (n : ℕ) :
    Real.Gamma ((n : ℝ)+2) = ((n : ℝ)+1)*Real.Gamma ((n : ℝ)+1) := by
  convert Real.Gamma_add_one (by positivity : (n : ℝ)+1 ≠ 0) using 1 <;> congr 1 <;> ring

private theorem gamma_succ_half (n : ℕ) :
    Real.Gamma ((n : ℝ)+5/2) = ((n : ℝ)+3/2)*Real.Gamma ((n : ℝ)+3/2) := by
  convert Real.Gamma_add_one (by positivity : (n : ℝ)+3/2 ≠ 0) using 1 <;> congr 1 <;> ring

private theorem gamma_half_midpoint (n : ℕ) :
    Real.Gamma ((n : ℝ)+3/2)^2 ≤
      Real.Gamma ((n : ℝ)+1)*Real.Gamma ((n : ℝ)+2) := by
  have hg := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    (s := (n : ℝ)+1) (t := (n : ℝ)+2) (a := (1/2 : ℝ)) (b := (1/2 : ℝ))
    (by positivity) (by positivity) (by norm_num) (by norm_num) (by norm_num)
  rw [show (1/2 : ℝ)*((n : ℝ)+1)+(1/2 : ℝ)*((n : ℝ)+2) = (n : ℝ)+3/2 by ring] at hg
  simp only [← Real.sqrt_eq_rpow] at hg
  have hp : 0 ≤ Real.Gamma ((n : ℝ)+3/2) := Real.Gamma_nonneg_of_nonneg (by positivity)
  have hs : 0 ≤ Real.sqrt (Real.Gamma ((n : ℝ)+1))*Real.sqrt (Real.Gamma ((n : ℝ)+2)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : Real.Gamma ((n : ℝ)+3/2)^2 ≤
      (Real.sqrt (Real.Gamma ((n : ℝ)+1))*Real.sqrt (Real.Gamma ((n : ℝ)+2)))^2 := by
    simpa only [← pow_two] using mul_le_mul hg hg hp hs
  rw [mul_pow,
    Real.sq_sqrt (Real.Gamma_nonneg_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity)),
    Real.sq_sqrt (Real.Gamma_nonneg_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)+2 by positivity))] at hsq
  exact hsq

theorem gibbsSchurWeight_square_lower (n : ℕ) :
    1 / ((n : ℝ)+3/2) ≤ gibbsSchurWeight n ^ 2 := by
  unfold gibbsSchurWeight
  rw [div_pow]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)+3/2)
    (sq_pos_of_pos (Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ)+2 by positivity)))).2
  have h := gibbsSchurGamma_midpoint n
  rw [gamma_succ_half] at h
  nlinarith

theorem gibbsSchurWeight_square_upper (n : ℕ) :
    gibbsSchurWeight n ^ 2 ≤ 1 / ((n : ℝ)+1) := by
  unfold gibbsSchurWeight
  rw [div_pow]
  apply (div_le_div_iff₀
    (sq_pos_of_pos (Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ)+2 by positivity)))
    (by positivity : (0 : ℝ) < (n : ℝ)+1)).2
  have h := mul_le_mul_of_nonneg_right (gamma_half_midpoint n)
    (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity)
  have hr := gamma_succ_one n
  have he : Real.Gamma ((n : ℝ)+1) * Real.Gamma ((n : ℝ)+2) * ((n : ℝ)+1) =
      Real.Gamma ((n : ℝ)+2)^2 := by
    calc
      _ = (((n : ℝ)+1)*Real.Gamma ((n : ℝ)+1))*Real.Gamma ((n : ℝ)+2) := by ring
      _ = _ := by rw [← hr, pow_two]
  simpa only [he, one_mul] using h

theorem gibbsSchurWeight_scaled_square (n : ℕ) :
    (((n : ℝ)+1)*gibbsSchurWeight n)^2 ≤ (n : ℝ)+1 := by
  have h := (le_div_iff₀ (show (0 : ℝ) < (n : ℝ)+1 by positivity)).mp
    (gibbsSchurWeight_square_upper n)
  have hh := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity)
  nlinarith

/-- A simple Pareto bound controls the entire omitted part of every Schur row. -/
theorem gibbsSchur_pair_le_weight (n m : ℕ) :
    gibbsComplementKernel n m * gibbsSchurWeight n * gibbsSchurWeight m ≤ paretoWeight m := by
  have hnum : 2 * (((n : ℝ)+1)*gibbsSchurWeight n) *
      (((m : ℝ)+1)*gibbsSchurWeight m) ≤ (n : ℝ)+m+2 := by
    nlinarith [sq_nonneg ((((n : ℝ)+1)*gibbsSchurWeight n) -
      (((m : ℝ)+1)*gibbsSchurWeight m)),
      gibbsSchurWeight_scaled_square n, gibbsSchurWeight_scaled_square m]
  calc
    _ = (2 * (((n : ℝ)+1)*gibbsSchurWeight n) * (((m : ℝ)+1)*gibbsSchurWeight m)) /
      (((n : ℝ)+m+1)*((n : ℝ)+m+2)*((n : ℝ)+m+3)) := by
        unfold gibbsComplementKernel geometricKernel
        ring
    _ ≤ ((n : ℝ)+m+2) / (((n : ℝ)+m+1)*((n : ℝ)+m+2)*((n : ℝ)+m+3)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 / (((n : ℝ)+m+1)*((n : ℝ)+m+3)) := by field_simp
    _ ≤ _ := by
      unfold paretoWeight
      apply one_div_le_one_div_of_le (by positivity)
      gcongr <;> nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

/-- Multiplying the exact Gamma row by its weight cancels all Gamma functions. -/
theorem gibbsSchur_weight_mul_row (n : ℕ) :
    gibbsSchurWeight n * gibbsSchurRow n = (Real.pi/4) / ((n : ℝ)+3/2) := by
  unfold gibbsSchurRow
  rw [(gibbsSchurGamma_row_hasSum n).tsum_eq]
  unfold gibbsSchurWeight
  rw [gamma_succ_half]
  have h1 : Real.Gamma ((n : ℝ)+3/2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have h2 : Real.Gamma ((n : ℝ)+2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hn : (n : ℝ)+3/2 ≠ 0 := by positivity
  field_simp

theorem gibbsSchur_internal_defect_le (n : ℕ) :
    (Real.pi/4)*gibbsSchurWeight n^2 - gibbsSchurWeight n*gibbsSchurRow n ≤
      (Real.pi/4)*paretoWeight n := by
  rw [gibbsSchur_weight_mul_row, paretoWeight_eq_inv_sub]
  have hq : 0 ≤ Real.pi/4 := by positivity
  have h1 := mul_le_mul_of_nonneg_left (gibbsSchurWeight_square_upper n) hq
  have h2 := mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le (show (0 : ℝ) < (n : ℝ)+3/2 by positivity)
      (show (n : ℝ)+3/2 ≤ (n : ℝ)+2 by norm_num)) hq
  simp only [div_eq_mul_inv, one_mul] at h1 h2 ⊢
  nlinarith

def gibbsSchurSquareSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, gibbsSchurWeight n ^ 2

def gibbsSchurQuadraticSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
    gibbsSchurWeight n * gibbsSchurWeight m * gibbsComplementKernel n m

/-- The norms of the truncated Schur vectors are unbounded. -/
theorem gibbsSchurSquareSum_unbounded (M : ℝ) : ∃ N : ℕ, M < gibbsSchurSquareSum N := by
  have hterm (n : ℕ) : 1 / ((n : ℝ)+1) ≤ 2*gibbsSchurWeight n^2 := by
    have hl := mul_le_mul_of_nonneg_left (gibbsSchurWeight_square_lower n) (by norm_num : (0 : ℝ) ≤ 2)
    have hr : 1 / ((n : ℝ)+1) ≤ 2 / ((n : ℝ)+3/2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    simp only [div_eq_mul_inv, one_mul] at hl hr ⊢
    nlinarith
  have hev : ∀ᶠ N : ℕ in atTop, 2*M < ∑ n ∈ Finset.range N, 1/((n : ℝ)+1) :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop (eventually_gt_atTop (2*M))
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨N, ?_⟩
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => hterm n)
  rw [← Finset.mul_sum] at hs
  change (∑ n ∈ Finset.range N, 1 / ((n : ℝ)+1)) ≤ 2*gibbsSchurSquareSum N at hs
  nlinarith

end
end RiemannResearch.RH.Pareto
