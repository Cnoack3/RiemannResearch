import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Oscillating harmonic variation and logarithmic cutoff control

Source: continuation of the user-provided
FourierArithmeticContinuationVerification20260911(1).md, September 11, 2026.
These elementary estimates use Mathlib's unitary exponential and logarithm
bounds. The finite tail identity retains its terminal correction.
-/

open scoped BigOperators
noncomputable section

namespace RiemannResearch.Analysis

/-- The unitary exponential has its exact real Lipschitz constant. -/
theorem norm_exp_I_mul_sub_exp_I_mul_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ ≤
      |x - y| := by
  have he : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) *
        (Complex.exp (Complex.I * ((x-y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, norm_mul]
  have hn : ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  rw [hn, one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

/-- Exact logarithmic increment domination used for the physical harmonic weight. -/
theorem log_add_one_sub_log_le_inv {x : ℝ} (hx : 0 < x) :
    |Real.log (x+1) - Real.log x| ≤ 1/x := by
  have hmono : Real.log x ≤ Real.log (x+1) := Real.log_le_log hx (by linarith)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono), ← Real.log_div (by linarith : x+1 ≠ 0) hx.ne']
  calc
    Real.log ((x+1)/x) ≤ (x+1)/x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = 1/x := by field_simp; ring

/-- The oscillating harmonic weight has a summable variation majorant. -/
theorem norm_exp_log_harmonic_sub_le (ω x : ℝ) (hx : 0 < x) :
    ‖Complex.exp (Complex.I * ((ω * Real.log x : ℝ) : ℂ)) / (x : ℂ) -
      Complex.exp (Complex.I * ((ω * Real.log (x+1) : ℝ) : ℂ)) / ((x+1 : ℝ) : ℂ)‖ ≤
      (1 + |ω|) / (x*(x+1)) := by
  let u : ℂ := Complex.exp (Complex.I * ((ω * Real.log x : ℝ) : ℂ))
  let v : ℂ := Complex.exp (Complex.I * ((ω * Real.log (x+1) : ℝ) : ℂ))
  have hu : ‖u‖ = 1 := by simp [u, Complex.norm_exp]
  have hphase : ‖u-v‖ ≤ |ω| / x := by
    calc
      ‖u-v‖ ≤ |ω * Real.log x - ω * Real.log (x+1)| :=
        norm_exp_I_mul_sub_exp_I_mul_le _ _
      _ = |ω| * |Real.log (x+1) - Real.log x| := by
        rw [← mul_sub, abs_mul, abs_sub_comm]
      _ ≤ |ω| * (1/x) := mul_le_mul_of_nonneg_left
        (log_add_one_sub_log_le_inv hx) (abs_nonneg _)
      _ = |ω|/x := by ring
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hx1C : ((x+1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show x+1 ≠ 0 by linarith)
  have hid : u / (x : ℂ) - v / ((x+1 : ℝ) : ℂ) =
      (u-v) / ((x+1 : ℝ) : ℂ) + u / ((x*(x+1) : ℝ) : ℂ) := by
    push_cast at hx1C ⊢
    field_simp [hxC, hx1C]
    ring
  change ‖u / (x : ℂ) - v / ((x+1 : ℝ) : ℂ)‖ ≤ _
  rw [hid]
  calc
    ‖(u-v) / ((x+1 : ℝ) : ℂ) + u / ((x*(x+1) : ℝ) : ℂ)‖ ≤
        ‖(u-v) / ((x+1 : ℝ) : ℂ)‖ + ‖u / ((x*(x+1) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = ‖u-v‖ / (x+1) + 1 / (x*(x+1)) := by
      rw [norm_div, norm_div, hu]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < x+1 by linarith), abs_of_pos (show 0 < x*(x+1) by positivity)]
    _ ≤ (|ω|/x) / (x+1) + 1 / (x*(x+1)) := by
      gcongr
    _ = (1 + |ω|) / (x*(x+1)) := by field_simp; ring

end RiemannResearch.Analysis

namespace RiemannResearch.Analysis

/-- Exact reciprocal tail telescoping, retaining the terminal correction. -/
theorem sum_reciprocal_adjacent_tail (N M : ℕ) :
    (∑ j ∈ Finset.range M,
      1 / (((N+j+1 : ℕ) : ℝ) * ((N+j+2 : ℕ) : ℝ))) =
      1 / ((N+1 : ℕ) : ℝ) - 1 / ((N+M+1 : ℕ) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      have h1 : (N : ℝ)+1 ≠ 0 := by positivity
      have h2 : (N : ℝ)+M+1 ≠ 0 := by positivity
      have h3 : (N : ℝ)+M+2 ≠ 0 := by positivity
      have h4 : (N : ℝ)+(M+1)+1 ≠ 0 := by positivity
      field_simp
      ring

/-- A cutoff-free logarithmic bound from a harmonic head and summable variation tail. -/
theorem sum_range_harmonic_and_variation_le
    (u : ℕ → ℝ) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hhead : ∀ j, u j ≤ C / ((j+1 : ℕ) : ℝ))
    (htail : ∀ j, u j ≤ B / (((j+1 : ℕ) : ℝ)*((j+2 : ℕ) : ℝ)))
    (N K : ℕ) :
    (∑ j ∈ Finset.range K, u j) ≤
      C * (∑ j ∈ Finset.range N, 1 / ((j+1 : ℕ) : ℝ)) +
        B / ((N+1 : ℕ) : ℝ) := by
  have hheadK (k : ℕ) : (∑ j ∈ Finset.range k, u j) ≤
      C * (∑ j ∈ Finset.range k, 1 / ((j+1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_one_div] using hhead j
  by_cases hKN : K ≤ N
  · calc
      (∑ j ∈ Finset.range K, u j) ≤
          C * (∑ j ∈ Finset.range K, 1 / ((j+1 : ℕ) : ℝ)) := hheadK K
      _ ≤ C * (∑ j ∈ Finset.range N, 1 / ((j+1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hKN)
          (fun j hj hjK => by positivity)
      _ ≤ _ := le_add_of_nonneg_right (div_nonneg hB (by positivity))
  · have hNK : N ≤ K := by omega
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hNK
    rw [Finset.sum_range_add]
    have htailM : (∑ j ∈ Finset.range M, u (N+j)) ≤
        B * (1 / ((N+1 : ℕ) : ℝ) - 1 / ((N+M+1 : ℕ) : ℝ)) := by
      rw [← sum_reciprocal_adjacent_tail, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_one_div, Nat.add_assoc] using htail (N+j)
    calc
      _ ≤ C * (∑ j ∈ Finset.range N, 1 / ((j+1 : ℕ) : ℝ)) +
          B * (1 / ((N+1 : ℕ) : ℝ) - 1 / ((N+M+1 : ℕ) : ℝ)) :=
        add_le_add (hheadK N) htailM
      _ ≤ _ := by
        have hz : 0 ≤ B / ((N+M+1 : ℕ) : ℝ) := div_nonneg hB (by positivity)
        simp only [mul_sub, mul_one_div]
        linarith

end RiemannResearch.Analysis
