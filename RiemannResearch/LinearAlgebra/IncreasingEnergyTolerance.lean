import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Energy buffers inherited under refinement

Source: user-provided argument,
`RH_Layer_Cake_Sublevel_Program_and_Next_Attack_2026-09-16_Continued.md`,
Section 40. The exact refinement identities and positivity of the old
shifted form are hypotheses. No RH-specific prime or archimedean bound is
asserted. Increasing the tolerance gives a coercive buffer on the inherited
space; it does not by itself control the new Schur block.
-/

namespace RiemannResearch.LinearAlgebra

/-- Exact change of a shifted quadratic value under a refinement preserving
both the original quadratic value and the reference energy. -/
theorem refined_energy_tolerance_identity
    {V W : Type*} (J : V → W) (q d : V → ℝ) (q' d' : W → ℝ)
    (hq : ∀ v, q' (J v) = q v) (hd : ∀ v, d' (J v) = d v)
    (τ τ' : ℝ) (v : V) :
    q' (J v) + τ' * d' (J v) =
      (q v + τ * d v) + (τ' - τ) * d v := by
  rw [hq v, hd v]
  ring

/-- A positive tolerance increment becomes a lower energy bound on the
inherited subspace. The new complement still requires its own certificate. -/
theorem refined_energy_tolerance_buffer
    {V W : Type*} (J : V → W) (q d : V → ℝ) (q' d' : W → ℝ)
    (hq : ∀ v, q' (J v) = q v) (hd : ∀ v, d' (J v) = d v)
    (τ τ' δ : ℝ) (hδ : δ ≤ τ' - τ)
    (henergy : ∀ v, 0 ≤ d v) (hold : ∀ v, 0 ≤ q v + τ * d v) :
    ∀ v, δ * d v ≤ q' (J v) + τ' * d' (J v) := by
  intro v
  rw [refined_energy_tolerance_identity J q d q' d' hq hd τ τ' v]
  have hmul := mul_le_mul_of_nonneg_right hδ (henergy v)
  linarith [hold v]

/-- Degree-one polynomial tolerances have the same positive increment at
every step. In combination with the refinement lemma, `C > 0` supplies a
uniform inherited coercivity constant. -/
theorem linear_energy_tolerance_increment (C : ℝ) (j : ℕ) :
    C * ((j : ℝ) + 2) - C * ((j : ℝ) + 1) = C := by
  ring

/-- Every positive integer power increases by at least one when its real
argument, already at least one, is increased by one. -/
theorem power_increment_ge_one (x : ℝ) (hx : 1 ≤ x) (n : ℕ) :
    1 ≤ (x + 1) ^ (n + 1) - x ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx0 : 0 ≤ x := by linarith
    have hx1 : 0 ≤ x + 1 := by linarith
    calc
      1 ≤ (x + 1) * 1 := by linarith
      _ ≤ (x + 1) * ((x + 1) ^ (n + 1) - x ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left ih hx1
      _ ≤ (x + 1) * ((x + 1) ^ (n + 1) - x ^ (n + 1)) + x ^ (n + 1) :=
        le_add_of_nonneg_right (pow_nonneg hx0 _)
      _ = (x + 1) ^ (n + 1 + 1) - x ^ (n + 1 + 1) := by
        rw [pow_succ (x + 1) (n + 1), pow_succ x (n + 1)]
        ring

/-- Natural polynomial degrees suffice for the research program's
polynomial-loss target. Their tolerance increments dominate the coefficient. -/
theorem polynomial_energy_tolerance_increment
    (C : ℝ) (hC : 0 ≤ C) (j A : ℕ) (hA : 1 ≤ A) :
    C ≤ C * (((j : ℝ) + 2) ^ A - ((j : ℝ) + 1) ^ A) := by
  cases A with
  | zero => simp at hA
  | succ n =>
    have hx : 1 ≤ (j : ℝ) + 1 := by
      have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hgap := power_increment_ge_one ((j : ℝ) + 1) hx n
    have hbase : ((j : ℝ) + 1) + 1 = (j : ℝ) + 2 := by ring
    simpa only [hbase, mul_one] using mul_le_mul_of_nonneg_left hgap hC

/-- Polynomial tolerance gives the uniform inherited buffer `C*d`.
This covers every natural degree at least one and every refinement step. -/
theorem refined_polynomial_energy_tolerance_buffer
    {V W : Type*} (J : V → W) (q d : V → ℝ) (q' d' : W → ℝ)
    (hq : ∀ v, q' (J v) = q v) (hd : ∀ v, d' (J v) = d v)
    (C : ℝ) (hC : 0 ≤ C) (j A : ℕ) (hA : 1 ≤ A)
    (henergy : ∀ v, 0 ≤ d v)
    (hold : ∀ v, 0 ≤ q v + (C * ((j : ℝ) + 1) ^ A) * d v) :
    ∀ v, C * d v ≤ q' (J v) + (C * ((j : ℝ) + 2) ^ A) * d' (J v) := by
  apply refined_energy_tolerance_buffer J q d q' d' hq hd
    (C * ((j : ℝ) + 1) ^ A) (C * ((j : ℝ) + 2) ^ A) C
  · calc
      C ≤ C * (((j : ℝ) + 2) ^ A - ((j : ℝ) + 1) ^ A) :=
        polynomial_energy_tolerance_increment C hC j A hA
      _ = C * ((j : ℝ) + 2) ^ A - C * ((j : ℝ) + 1) ^ A := by ring
  · exact henergy
  · exact hold

end RiemannResearch.LinearAlgebra
