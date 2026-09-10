import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Banach-valued Abel assembly for signed arithmetic energy

Source: the September 10, 2026 conversation and
`FourierBridgeUniformSignedEnergy20260910.md`, Sections 9--10.

This file proves the analytic assembly step from an integer-dilation norm
estimate. It deliberately keeps that estimate and the identification with the
actual arithmetic remainder as hypotheses. It does not claim that a Mertens
estimate, the compensated shell construction, or their Fourier identification
has been formalized here. No finite-coordinate surrogate replaces the vector.
-/

namespace RiemannResearch.Analysis

open scoped BigOperators
noncomputable section

/-- The exact geometric first moment needed for the conductor majorant. -/
theorem abel_geometric_linear_majorant_hasSum
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (C D : ℝ) :
    HasSum (fun j : ℕ => q ^ j * (C + D * ((j : ℝ) + 1)))
      (C / (1 - q) + D / (1 - q) ^ 2) := by
  have hqn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hg : HasSum (fun j : ℕ => q ^ j) ((1 - q)⁻¹) :=
    hasSum_geometric_of_lt_one hq0 hq1
  have hm : HasSum (fun j : ℕ => ((j : ℝ) + 1) * q ^ j)
      (1 / (1 - q) ^ 2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one 1 hqn
  have hs := (hg.mul_left C).add (hm.mul_left D)
  have hp : (fun j : ℕ => C * q ^ j + D * (((j : ℝ) + 1) * q ^ j)) =
      (fun j : ℕ => q ^ j * (C + D * ((j : ℝ) + 1))) := by
    funext j
    ring
  have hv : C * (1 - q)⁻¹ + D * (1 / (1 - q) ^ 2) =
      C / (1 - q) + D / (1 - q) ^ 2 := by ring
  rw [hp, hv] at hs
  exact hs

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The complete signed Abel remainder of an integer-dilation family. -/
def signedIntegerDilationAbel (q : ℝ) (V : ℕ → E) : E :=
  V 1 - (1 - q) • ∑' j : ℕ, q ^ j • V (3 ^ (j + 1))

omit [CompleteSpace E] in
/-- A linear bound along the triadic orbit implies absolute Banach convergence. -/
theorem signedIntegerDilationAbel_summable_norm_of_linear
    {q C D : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (V : ℕ → E)
    (hV : ∀ j : ℕ, ‖V (3 ^ (j + 1))‖ ≤ C + D * ((j : ℝ) + 1)) :
    Summable (fun j : ℕ => ‖q ^ j • V (3 ^ (j + 1))‖) := by
  apply (abel_geometric_linear_majorant_hasSum hq0 hq1 C D).summable.of_norm_bounded
  intro j
  rw [norm_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 j)]
  exact mul_le_mul_of_nonneg_left (hV j) (pow_nonneg hq0 j)

omit [CompleteSpace E] in
/-- The signed expression is formed first; the bound concerns its full norm. -/
theorem signedIntegerDilationAbel_norm_le_of_linear
    {q C D : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (V : ℕ → E)
    (hV1 : ‖V 1‖ ≤ C)
    (hV : ∀ j : ℕ, ‖V (3 ^ (j + 1))‖ ≤ C + D * ((j : ℝ) + 1)) :
    ‖signedIntegerDilationAbel q V‖ ≤ 2 * C + D / (1 - q) := by
  have hs : ‖∑' j : ℕ, q ^ j • V (3 ^ (j + 1))‖ ≤
      C / (1 - q) + D / (1 - q) ^ 2 := by
    apply tsum_of_norm_bounded (abel_geometric_linear_majorant_hasSum hq0 hq1 C D)
    intro j
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 j)]
    exact mul_le_mul_of_nonneg_left (hV j) (pow_nonneg hq0 j)
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  calc
    ‖signedIntegerDilationAbel q V‖ ≤ ‖V 1‖ +
        ‖(1 - q) • ∑' j : ℕ, q ^ j • V (3 ^ (j + 1))‖ := norm_sub_le _ _
    _ = ‖V 1‖ + (1 - q) * ‖∑' j : ℕ, q ^ j • V (3 ^ (j + 1))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hden]
    _ ≤ C + (1 - q) * (C / (1 - q) + D / (1 - q) ^ 2) :=
      add_le_add hV1 (mul_le_mul_of_nonneg_left hs hden.le)
    _ = 2 * C + D / (1 - q) := by field_simp [ne_of_gt hden]; ring

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Logarithmic growth on integer conductors supplies the orbit majorant. -/
theorem integerDilation_log_bound_triadic
    {ε C : ℝ} (V : ℕ → E)
    (hV : ∀ A : ℕ, 1 ≤ A → ‖V A‖ ≤ C * (1 + ε * Real.log A))
    (j : ℕ) :
    ‖V (3 ^ (j + 1))‖ ≤ C + (C * ε * Real.log 3) * ((j : ℝ) + 1) := by
  calc
    _ ≤ C * (1 + ε * Real.log ((3 ^ (j + 1) : ℕ) : ℝ)) :=
      hV (3 ^ (j + 1)) (Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero _ (by decide : (3 : ℕ) ≠ 0)))
    _ = _ := by
      rw [Nat.cast_pow, Real.log_pow]
      push_cast
      ring

omit [CompleteSpace E] in
/-- The infinite triadic orbit is absolutely summable under the logarithmic estimate. -/
theorem signedIntegerDilationAbel_summable_norm_of_log
    {ε q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (V : ℕ → E)
    (hV : ∀ A : ℕ, 1 ≤ A → ‖V A‖ ≤ C * (1 + ε * Real.log A)) :
    Summable (fun j : ℕ => ‖q ^ j • V (3 ^ (j + 1))‖) := by
  apply signedIntegerDilationAbel_summable_norm_of_linear hq0 hq1 V
  exact integerDilation_log_bound_triadic V hV

omit [CompleteSpace E] in
/-- Exact dependence on damping, before replacing it by a uniform constant. -/
theorem signedIntegerDilationAbel_norm_le_of_log
    {ε q C : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (V : ℕ → E)
    (hV : ∀ A : ℕ, 1 ≤ A → ‖V A‖ ≤ C * (1 + ε * Real.log A)) :
    ‖signedIntegerDilationAbel q V‖ ≤
      C * (2 + ε * Real.log 3 / (1 - q)) := by
  have h1 : ‖V 1‖ ≤ C := by simpa using hV 1 le_rfl
  have h := signedIntegerDilationAbel_norm_le_of_linear hq0 hq1 V h1
    (integerDilation_log_bound_triadic V hV)
  calc
    _ ≤ 2 * C + (C * ε * Real.log 3) / (1 - q) := h
    _ = _ := by ring

end Banach

/-- A simple nonoptimal uniform bound for the geometric damping moment. -/
theorem damping_first_moment_le_two {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    u / (1 - Real.exp (-u)) ≤ 2 := by
  have hq : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : 0 < 1 - Real.exp (-u) := sub_pos.mpr hq
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp u)
    (Real.exp_pos (-u)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  have hlower : u ≤ (1 + u) * (1 - Real.exp (-u)) := by nlinarith
  have hupper : (1 + u) * (1 - Real.exp (-u)) ≤
      2 * (1 - Real.exp (-u)) := by
    apply mul_le_mul_of_nonneg_right _ hden.le
    linarith
  exact (div_le_iff₀ hden).mpr (hlower.trans hupper)


end
end RiemannResearch.Analysis
