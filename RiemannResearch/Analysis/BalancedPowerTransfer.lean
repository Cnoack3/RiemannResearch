import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Exact transfer of Fourier coefficient errors to balanced powers

Source: user-supplied `Zeta_Zero_Harmonic_Analysis_20261011 (1)(1).md`,
Section 9.5, motivates the balanced-power application. The exact binomial
majorant below is an independently developed finite algebraic strengthening
of its coarse power estimate. No distribution law or RH premise is used.

Recovery status, 2026-10-11: the initial candidate submitted as
job_Yts5GqrQN8pd_vOlrU6c3mRGXajDyhLX terminated with an addition-monotonicity
proof error. The recovered candidate has been repaired; the complete six-module
integration still requires the final server checkpoint. No success is asserted here.
-/

namespace RiemannResearch.Analysis.BalancedPowerTransfer
theorem norm_pow_sub_pow_le_exact (z w : ℂ) (e : ℝ)
    (he : 0 ≤ e) (h : ‖z - w‖ ≤ e) (q : ℕ) :
    ‖z ^ q - w ^ q‖ ≤ (‖w‖ + e) ^ q - ‖w‖ ^ q := by
  have hz : ‖z‖ ≤ ‖w‖ + e := by
    calc
      ‖z‖ = ‖w + (z - w)‖ := by congr 1; ring
      _ ≤ ‖w‖ + ‖z - w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + e := add_le_add (le_refl ‖w‖) h
  induction q with
  | zero => simp
  | succ q ih =>
    calc
      ‖z ^ (q + 1) - w ^ (q + 1)‖ =
          ‖z * (z ^ q - w ^ q) + (z - w) * w ^ q‖ := by
            congr 1
            simp only [pow_succ]
            ring
      _ ≤ ‖z‖ * ‖z ^ q - w ^ q‖ + ‖z - w‖ * ‖w‖ ^ q := by
        simpa only [norm_mul, norm_pow] using
          norm_add_le (z * (z ^ q - w ^ q)) ((z - w) * w ^ q)
      _ ≤ (‖w‖ + e) * ‖z ^ q - w ^ q‖ + e * ‖w‖ ^ q :=
        add_le_add
          (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h (pow_nonneg (norm_nonneg _) q))
      _ ≤ (‖w‖ + e) * ((‖w‖ + e) ^ q - ‖w‖ ^ q) + e * ‖w‖ ^ q :=
        add_le_add
          (mul_le_mul_of_nonneg_left ih (add_nonneg (norm_nonneg _) he))
          (le_refl (e * ‖w‖ ^ q))
      _ = (‖w‖ + e) ^ (q + 1) - ‖w‖ ^ (q + 1) := by
        simp only [pow_succ]
        ring
theorem abs_norm_pow_sub_le_exact (z w : ℂ) (e : ℝ)
    (he : 0 ≤ e) (h : ‖z - w‖ ≤ e) (q : ℕ) :
    |‖z‖ ^ q - ‖w‖ ^ q| ≤ (‖w‖ + e) ^ q - ‖w‖ ^ q := by
  calc
    |‖z‖ ^ q - ‖w‖ ^ q| = |‖z ^ q‖ - ‖w ^ q‖| := by simp only [norm_pow]
    _ ≤ ‖z ^ q - w ^ q‖ := abs_norm_sub_norm_le _ _
    _ ≤ _ := norm_pow_sub_pow_le_exact z w e he h q
end RiemannResearch.Analysis.BalancedPowerTransfer
