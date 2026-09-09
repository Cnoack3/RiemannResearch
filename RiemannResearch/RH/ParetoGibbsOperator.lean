import RiemannResearch.RH.ParetoGeometricEnergy
import Mathlib.Tactic.Linarith

/-!
# The actual Pareto Gibbs operator on the full weighted square-summable space

Source: RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md.
The index n represents the positive integer n+1. All series below are infinite.
The kernel, convergence hypotheses, exact loss and contraction are derived here;
no spectral-gap or arithmetic-invariance hypothesis is used.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Transition probability of the geometric-mixture Gibbs sampler. -/
def gibbsKernel (n m : ℕ) : ℝ := geometricKernel n m / paretoWeight n

/-- The actual infinite Gibbs action in physical zero-indexed coordinates. -/
def gibbsAction (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑' m, geometricKernel n m * f m) / paretoWeight n

theorem gibbsKernel_pos (n m : ℕ) : 0 < gibbsKernel n m :=
  div_pos (geometricKernel_pos n m) (paretoWeight_pos n)

theorem gibbsKernel_formula (n m : ℕ) :
    gibbsKernel n m =
      2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) /
        (((n : ℝ) + m + 1) * ((n : ℝ) + m + 2) * ((n : ℝ) + m + 3)) := by
  unfold gibbsKernel geometricKernel paretoWeight
  field_simp
  <;> ring

theorem gibbsKernel_hasSum (n : ℕ) : HasSum (gibbsKernel n) 1 := by
  change HasSum (fun m => geometricKernel n m / paretoWeight n) 1
  have h := (geometricKernel_hasSum n).div_const (paretoWeight n)
  rw [div_self (ne_of_gt (paretoWeight_pos n))] at h
  exact h

theorem gibbsKernel_tsum (n : ℕ) : (∑' m, gibbsKernel n m) = 1 :=
  (gibbsKernel_hasSum n).tsum_eq

theorem gibbsKernel_detailed_balance (n m : ℕ) :
    paretoWeight n * gibbsKernel n m = paretoWeight m * gibbsKernel m n := by
  unfold gibbsKernel
  rw [geometricKernel_symm n m]
  field_simp [ne_of_gt (paretoWeight_pos n), ne_of_gt (paretoWeight_pos m)]

theorem gibbsAction_eq_tsum (f : ℕ → ℝ) (n : ℕ) :
    gibbsAction f n = ∑' m, gibbsKernel n m * f m := by
  unfold gibbsAction gibbsKernel
  rw [← tsum_div_const]
  apply tsum_congr
  intro m
  ring

theorem gibbsAction_const (c : ℝ) : gibbsAction (fun _ => c) = fun _ => c := by
  funext n
  unfold gibbsAction
  rw [(geometricKernel_hasSum n).summable.tsum_mul_right, geometricKernel_tsum]
  field_simp [ne_of_gt (paretoWeight_pos n)]

theorem geometricKernel_le_paretoWeight_right (n m : ℕ) :
    geometricKernel n m ≤ paretoWeight m := by
  rw [geometricKernel_symm]
  exact (geometricKernel_hasSum m).tsum_eq ▸
    (geometricKernel_hasSum m).summable.le_tsum n
      (fun j hj => (geometricKernel_pos m j).le)

private theorem abs_le_square_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

/-- The full Hilbert-space square condition implies absolute Pareto summability. -/
theorem pareto_abs_summable_of_square {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    Summable (fun n => paretoWeight n * |f n|) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (paretoWeight_pos n).le (abs_nonneg _))
    (fun n => ?_) (hf.add paretoWeight_hasSum.summable)
  nlinarith [mul_le_mul_of_nonneg_left (abs_le_square_add_one (f n))
    (paretoWeight_pos n).le]

/-- Each row converges absolutely for every weighted L1 input. -/
theorem gibbs_row_summable {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) (n : ℕ) :
    Summable (fun m => geometricKernel n m * f m) := by
  apply hf.of_norm_bounded
  intro m
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (geometricKernel_pos n m).le]
  exact mul_le_mul_of_nonneg_right (geometricKernel_le_paretoWeight_right n m)
    (abs_nonneg _)

/-- Absolute product-index summability follows from the exact actual marginal. -/
theorem gibbs_product_summable {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) :
    Summable (fun p : ℕ × ℕ => geometricKernel p.1 p.2 * f p.2) := by
  have hfirst : Summable (fun p : ℕ × ℕ => geometricKernel p.1 p.2 * |f p.1|) := by
    apply (summable_prod_of_nonneg
      (fun p => mul_nonneg (geometricKernel_pos p.1 p.2).le (abs_nonneg _))).mpr
    constructor
    · intro n
      exact (geometricKernel_hasSum n).summable.mul_right |f n|
    · simpa only [tsum_mul_right, geometricKernel_tsum] using hf
  have hswap := hfirst.comp_injective (Equiv.prodComm ℕ ℕ).injective
  change Summable (fun p : ℕ × ℕ => geometricKernel p.2 p.1 * |f p.2|) at hswap
  have hnorm : Summable (fun p : ℕ × ℕ => ‖geometricKernel p.1 p.2 * f p.2‖) := by
    apply hswap.congr
    intro p
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (geometricKernel_pos p.1 p.2).le,
      geometricKernel_symm p.2 p.1]
  exact hnorm.of_norm

/-- The full column marginal, with absolute convergence already discharged. -/
theorem gibbs_product_tsum {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) :
    (∑' p : ℕ × ℕ, geometricKernel p.1 p.2 * f p.2) =
      ∑' n, paretoWeight n * f n := by
  have hs := gibbs_product_summable hf
  rw [hs.tsum_prod, ← Summable.tsum_comm hs]
  apply tsum_congr
  intro m
  simp_rw [geometricKernel_symm (m := m), tsum_mul_right, geometricKernel_tsum]

theorem gibbsAction_weight_mul (f : ℕ → ℝ) (n : ℕ) :
    paretoWeight n * gibbsAction f n = ∑' m, geometricKernel n m * f m := by
  unfold gibbsAction
  field_simp [ne_of_gt (paretoWeight_pos n)]

/-- Exact preservation of the complete weighted mean. -/
theorem gibbsAction_mean {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|)) :
    (∑' n, paretoWeight n * gibbsAction f n) = ∑' n, paretoWeight n * f n := by
  simp_rw [gibbsAction_weight_mul]
  rw [← (gibbs_product_summable hf).tsum_prod]
  exact gibbs_product_tsum hf

theorem gibbsAction_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (n : ℕ) :
    0 ≤ gibbsAction f n := by
  unfold gibbsAction
  exact div_nonneg (tsum_nonneg (fun m =>
    mul_nonneg (geometricKernel_pos n m).le (hf m))) (paretoWeight_pos n).le

theorem gibbsAction_add {f g : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * |f n|))
    (hg : Summable (fun n => paretoWeight n * |g n|)) :
    gibbsAction (fun n => f n + g n) = fun n => gibbsAction f n + gibbsAction g n := by
  funext n
  simp only [gibbsAction, mul_add]
  rw [(gibbs_row_summable hf n).tsum_add (gibbs_row_summable hg n), add_div]

theorem gibbsAction_smul (c : ℝ) (f : ℕ → ℝ) :
    gibbsAction (fun n => c * f n) = fun n => c * gibbsAction f n := by
  funext n
  unfold gibbsAction
  simp_rw [mul_left_comm (geometricKernel n _) c, tsum_mul_left]
  ring

/-- Exact rowwise variance, for arbitrary weighted-square-summable inputs. -/
theorem gibbsAction_row_variance {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) (n : ℕ) :
    (∑' m, geometricKernel n m * (f m - gibbsAction f n) ^ 2) =
      (∑' m, geometricKernel n m * f m ^ 2) -
        paretoWeight n * gibbsAction f n ^ 2 := by
  have hs := gibbs_row_summable (pareto_abs_summable_of_square hf) n
  have hs2 := gibbs_row_summable (f := fun m => f m ^ 2)
    (by simpa only [abs_sq] using hf) n
  have hk := (geometricKernel_hasSum n).summable.mul_right (gibbsAction f n ^ 2)
  have he (m : ℕ) : geometricKernel n m * (f m - gibbsAction f n) ^ 2 =
      (geometricKernel n m * f m ^ 2 + geometricKernel n m * gibbsAction f n ^ 2) -
        (2 * gibbsAction f n) * (geometricKernel n m * f m) := by ring
  simp_rw [he]
  rw [(hs2.add hk).tsum_sub (hs.mul_left _), hs2.tsum_add hk,
    hs.tsum_mul_left, (geometricKernel_hasSum n).summable.tsum_mul_right,
    geometricKernel_tsum, ← gibbsAction_weight_mul f n]
  ring

theorem gibbsAction_weighted_square_le {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) (n : ℕ) :
    paretoWeight n * gibbsAction f n ^ 2 ≤
      ∑' m, geometricKernel n m * f m ^ 2 := by
  have hpos : 0 ≤ ∑' m, geometricKernel n m * (f m - gibbsAction f n) ^ 2 :=
    tsum_nonneg (fun m => mul_nonneg (geometricKernel_pos n m).le (sq_nonneg _))
  rw [gibbsAction_row_variance hf n] at hpos
  linarith

/-- The Gibbs action maps the entire weighted Hilbert space to itself. -/
theorem gibbsAction_square_summable {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    Summable (fun n => paretoWeight n * gibbsAction f n ^ 2) := by
  have hprod := gibbs_product_summable (f := fun n => f n ^ 2)
    (by simpa only [abs_sq] using hf)
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (paretoWeight_pos n).le (sq_nonneg _))
    (gibbsAction_weighted_square_le hf) hprod.prod

/-- Unconditional full-H contraction for the actual infinite kernel. -/
theorem gibbsAction_square_contraction {f : ℕ → ℝ}
    (hf : Summable (fun n => paretoWeight n * f n ^ 2)) :
    (∑' n, paretoWeight n * gibbsAction f n ^ 2) ≤
      ∑' n, paretoWeight n * f n ^ 2 := by
  have habs : Summable (fun n => paretoWeight n * |f n ^ 2|) := by
    simpa only [abs_sq] using hf
  have hprod := gibbs_product_summable habs
  calc
    _ ≤ ∑' n, ∑' m, geometricKernel n m * f m ^ 2 :=
      Summable.tsum_le_tsum (gibbsAction_weighted_square_le hf)
        (gibbsAction_square_summable hf) hprod.prod
    _ = _ := by rw [← hprod.tsum_prod, gibbs_product_tsum habs]

end
end RiemannResearch.RH.Pareto
