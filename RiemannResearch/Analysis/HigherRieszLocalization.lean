import RiemannResearch.Analysis.CenteredResidualTransfer
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# All-order dyadic Fourier localization threshold

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The analytic shell estimate for a fixed r-th Riesz annular filter is
  X log X (X lambda)^(-(2*r+1)).
At lambda = X^(-1+eta), its dyadic exponent is eta*(2*r+1)-1.
This file proves the scalar summability threshold and the existence of
a sufficient fixed smoothing order for every eta > 0, conditional on
the actual Fourier estimate when specializing to primes.
-/

set_option autoImplicit false
noncomputable section

namespace RiemannResearch.Analysis.HigherRieszLocalization

open CenteredResidualTransfer

def decayExponent (r : ℕ) (η : ℝ) : ℝ := η * (2 * (r : ℝ) + 1) - 1

def shellRatio (r : ℕ) (η : ℝ) : ℝ :=
  Real.exp (-(decayExponent r η) * Real.log 2)

theorem decayExponent_pos_iff (r : ℕ) (η : ℝ) :
    0 < decayExponent r η ↔ 1 / (2 * (r : ℝ) + 1) < η := by
  have hd : 0 < 2 * (r : ℝ) + 1 := by positivity
  rw [div_lt_iff₀ hd]
  unfold decayExponent
  constructor <;> intro h <;> nlinarith

theorem shellRatio_pos (r : ℕ) (η : ℝ) : 0 < shellRatio r η :=
  Real.exp_pos _

theorem shellRatio_lt_one {r : ℕ} {η : ℝ}
    (h : 0 < decayExponent r η) : shellRatio r η < 1 := by
  unfold shellRatio
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num))

theorem summable_higher_order_envelope {r : ℕ} {η : ℝ}
    (h : 1 / (2 * (r : ℝ) + 1) < η) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) * shellRatio r η ^ j) :=
  summable_linear_geometric (shellRatio_pos r η).le
    (shellRatio_lt_one ((decayExponent_pos_iff r η).mpr h))

theorem exists_order_for_every_positive_window_exponent {η : ℝ}
    (hη : 0 < η) : ∃ r : ℕ, 0 < decayExponent r η := by
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / η)
  have hm := mul_lt_mul_of_pos_left hr hη
  have he : η * (1 / η) = 1 := by
    field_simp [ne_of_gt hη]
  rw [he] at hm
  refine ⟨r, ?_⟩
  unfold decayExponent
  have hn : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith

/-- A sufficient order can be chosen positive, as required by the analytic
Riesz spline construction. The order is fixed after η is chosen. -/
theorem exists_positive_order_for_every_positive_window_exponent {η : ℝ}
    (hη : 0 < η) : ∃ r : ℕ, 1 ≤ r ∧ 0 < decayExponent r η := by
  obtain ⟨r, hr⟩ := exists_order_for_every_positive_window_exponent hη
  refine ⟨r + 1, Nat.succ_le_succ (Nat.zero_le r), ?_⟩
  unfold decayExponent at hr ⊢
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith

/-- Any nonnegative actual shell energy with the proved scalar envelope is
summable. The actual Fourier estimate is an explicit hypothesis. -/
theorem actual_shell_summable_of_envelope
    {r : ℕ} {η C : ℝ} {E : ℕ → ℝ}
    (h : 1 / (2 * (r : ℝ) + 1) < η)
    (hE : ∀ j, 0 ≤ E j)
    (hbound : ∀ j, E j ≤ C * (((j : ℝ) + 1) * shellRatio r η ^ j)) :
    Summable E := by
  exact ((summable_higher_order_envelope h).mul_left C).of_nonneg_of_le hE hbound

end RiemannResearch.Analysis.HigherRieszLocalization
