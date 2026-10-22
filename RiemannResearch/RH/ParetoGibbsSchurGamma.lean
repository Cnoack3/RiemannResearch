import RiemannResearch.RH.ParetoGibbsSchur

/-!
# The complete Schur row and its sharp pi/4 upper bound

The row value is derived from the exact boundary-controlled recurrence proved
in `ParetoGibbsSchur`. The upper bound then follows from Gamma log convexity.
No spectral theorem or arithmetic approximation hypothesis is assumed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

private theorem schur_gamma_one : Real.Gamma (1 : ℝ) = 1 := by
  simpa using Real.Gamma_nat_eq_factorial 0

private theorem schur_gamma_two : Real.Gamma (2 : ℝ) = 1 := by
  simpa using Real.Gamma_nat_eq_factorial 1

private theorem schur_gamma_five_halves :
    Real.Gamma (5/2 : ℝ) = (3/2 : ℝ) * Real.Gamma (3/2 : ℝ) := by
  convert Real.Gamma_add_one (by norm_num : (3/2 : ℝ) ≠ 0) using 1 <;> norm_num

theorem schur_gamma_three_halves_sq : Real.Gamma (3/2 : ℝ) ^ 2 = Real.pi / 4 := by
  have hg : Real.Gamma (3/2 : ℝ) = (1/2 : ℝ) * Real.Gamma (1/2 : ℝ) := by
    convert Real.Gamma_add_one (by norm_num : (1/2 : ℝ) ≠ 0) using 1 <;> norm_num
  rw [hg, Real.Gamma_one_half_eq, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  ring

def gibbsSchurIntegralValue (n : ℕ) : ℝ :=
  Real.Gamma (3/2 : ℝ) ^ 2 * Real.Gamma ((n : ℝ) + 1) /
    Real.Gamma ((n : ℝ) + 5/2)

theorem gibbsSchurIntegralValue_initial :
    gibbsSchurIntegralValue 0 = (2/3 : ℝ) * gibbsSchurWeight 0 := by
  unfold gibbsSchurIntegralValue gibbsSchurWeight
  norm_num only [Nat.cast_zero, zero_add]
  rw [schur_gamma_one, schur_gamma_two, schur_gamma_five_halves]
  have hg : Real.Gamma (3/2 : ℝ) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  field_simp
  <;> ring

theorem gibbsSchurIntegralValue_recurrence (n : ℕ) :
    ((n : ℝ) + 5/2) * gibbsSchurIntegralValue (n+1) =
      ((n : ℝ) + 1) * gibbsSchurIntegralValue n := by
  unfold gibbsSchurIntegralValue
  push_cast
  rw [show (n : ℝ)+1+5/2 = ((n : ℝ)+5/2)+1 by ring,
    Real.Gamma_add_one (by positivity : (n : ℝ)+5/2 ≠ 0),
    Real.Gamma_add_one (by positivity : (n : ℝ)+1 ≠ 0)]
  have hn : (n : ℝ)+5/2 ≠ 0 := by positivity
  field_simp

/-- Exact evaluation of every complete infinite normalized row. -/
theorem gibbsSchurTerm_tsum_eq (n : ℕ) :
    (∑' m, gibbsSchurTerm n m) = gibbsSchurIntegralValue n := by
  induction n with
  | zero => rw [gibbsSchurTerm_initial_hasSum.tsum_eq, gibbsSchurIntegralValue_initial]
  | succ n ih =>
      apply mul_left_cancel₀ (by positivity : (n : ℝ) + 5/2 ≠ 0)
      rw [gibbsSchurTerm_tsum_recurrence, gibbsSchurIntegralValue_recurrence, ih]

theorem gibbsSchurTerm_hasSum (n : ℕ) :
    HasSum (gibbsSchurTerm n) (gibbsSchurIntegralValue n) := by
  rw [← gibbsSchurTerm_tsum_eq]
  exact (gibbsSchurTerm_summable n).hasSum

theorem gibbsComplementKernel_weight_eq (n m : ℕ) :
    gibbsComplementKernel n m * gibbsSchurWeight m =
      ((n : ℝ) + 1) * gibbsSchurTerm n m := by
  unfold gibbsComplementKernel geometricKernel gibbsSchurTerm
  ring

/-- The complete Gamma row identity, with actual convergence proved. -/
theorem gibbsSchurGamma_row_hasSum (n : ℕ) :
    HasSum (fun m => gibbsComplementKernel n m * gibbsSchurWeight m)
      ((Real.pi / 4) * Real.Gamma ((n : ℝ)+2) / Real.Gamma ((n : ℝ)+5/2)) := by
  have h := (gibbsSchurTerm_hasSum n).mul_left ((n : ℝ)+1)
  simp only [← gibbsComplementKernel_weight_eq] at h
  have hv : ((n : ℝ)+1) * gibbsSchurIntegralValue n =
      (Real.pi / 4) * Real.Gamma ((n : ℝ)+2) / Real.Gamma ((n : ℝ)+5/2) := by
    unfold gibbsSchurIntegralValue
    rw [schur_gamma_three_halves_sq,
      show (n : ℝ)+2 = ((n : ℝ)+1)+1 by ring,
      Real.Gamma_add_one (by positivity : (n : ℝ)+1 ≠ 0)]
    ring
  rw [hv] at h
  exact h

/-- The midpoint Gamma inequality used by the exact positive Schur weight. -/
theorem gibbsSchurGamma_midpoint (n : ℕ) :
    Real.Gamma ((n : ℝ)+2) ^ 2 ≤
      Real.Gamma ((n : ℝ)+3/2) * Real.Gamma ((n : ℝ)+5/2) := by
  have hg := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
    (s := (n : ℝ)+3/2) (t := (n : ℝ)+5/2) (a := (1/2 : ℝ)) (b := (1/2 : ℝ))
    (by positivity) (by positivity) (by norm_num) (by norm_num) (by norm_num)
  rw [show (1/2 : ℝ)*((n : ℝ)+3/2)+(1/2 : ℝ)*((n : ℝ)+5/2) = (n : ℝ)+2 by ring] at hg
  simp only [← Real.sqrt_eq_rpow] at hg
  have hp : 0 ≤ Real.Gamma ((n : ℝ)+2) := (Real.Gamma_pos_of_pos (by positivity)).le
  have hs : 0 ≤ Real.sqrt (Real.Gamma ((n : ℝ)+3/2)) *
      Real.sqrt (Real.Gamma ((n : ℝ)+5/2)) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : Real.Gamma ((n : ℝ)+2) ^ 2 ≤
      (Real.sqrt (Real.Gamma ((n : ℝ)+3/2)) * Real.sqrt (Real.Gamma ((n : ℝ)+5/2))) ^ 2 := by
    simpa only [← pow_two] using mul_le_mul hg hg hp hs
  rw [mul_pow,
    Real.sq_sqrt (Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ)+3/2 by positivity)).le,
    Real.sq_sqrt (Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ)+5/2 by positivity)).le] at hsq
  exact hsq

/-- Uniform Schur control with the exact constant pi/4. -/
theorem gibbsSchurGamma_row_le (n : ℕ) :
    (∑' m, gibbsComplementKernel n m * gibbsSchurWeight m) ≤
      (Real.pi / 4) * gibbsSchurWeight n := by
  rw [(gibbsSchurGamma_row_hasSum n).tsum_eq]
  unfold gibbsSchurWeight
  have hdiv : Real.Gamma ((n : ℝ)+2) / Real.Gamma ((n : ℝ)+5/2) ≤
      Real.Gamma ((n : ℝ)+3/2) / Real.Gamma ((n : ℝ)+2) := by
    apply (div_le_div_iff₀
      (Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ)+5/2 by positivity))
      (Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ)+2 by positivity))).2
    simpa only [pow_two] using gibbsSchurGamma_midpoint n
  calc
    _ = (Real.pi/4) * (Real.Gamma ((n : ℝ)+2) / Real.Gamma ((n : ℝ)+5/2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ Real.pi/4 by positivity)

end
end RiemannResearch.RH.Pareto
