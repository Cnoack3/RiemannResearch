import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith

/-!
# Scalar support-error budget for the physical-dual projection

Source: user-provided `Prime_Phases_Agenda_Proof_Attempts.tex`,
equation (qK-error). This module proves the harmonic/scalar bound only.
Identification of this scalar with the norm of the actual physical `q_K`
requires its separate finite-support projection construction.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.DualSupportError

def supportA (K : ℕ) : ℝ := (harmonic (K + 1) : ℝ) - 1

theorem supportA_eq_sum (K : ℕ) :
    supportA K = ∑ n ∈ Finset.range K, (1 : ℝ) / ((n : ℝ) + 2) := by
  induction K with
  | zero => norm_num [supportA, harmonic]
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [supportA, harmonic_succ, Rat.cast_add, Rat.cast_inv,
      Rat.cast_natCast, Nat.cast_add, Nat.cast_one, one_div]
    ring

theorem supportA_nonneg (K : ℕ) : 0 ≤ supportA K := by
  rw [supportA_eq_sum]
  exact Finset.sum_nonneg (fun n hn => by positivity)

theorem supportA_le_half (K : ℕ) : supportA K ≤ (K : ℝ) / 2 := by
  have hterm (n : ℕ) : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
    apply (div_le_iff₀ (show (0 : ℝ) < (n : ℝ) + 2 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    supportA K = ∑ n ∈ Finset.range K, (1 : ℝ) / ((n : ℝ) + 2) := supportA_eq_sum K
    _ ≤ ∑ n ∈ Finset.range K, (1 / 2 : ℝ) :=
      Finset.sum_le_sum (fun n hn => hterm n)
    _ = (K : ℝ) / 2 := by simp [div_eq_mul_inv]

theorem supportA_le_log (K : ℕ) : supportA K ≤ Real.log ((K : ℝ) + 1) := by
  have h := harmonic_le_one_add_log (K + 1)
  have hc : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by norm_cast
  rw [hc] at h
  unfold supportA
  linarith

def supportErrorSq (K : ℕ) : ℝ :=
  supportA K ^ 2 / ((K : ℝ) - supportA K) + 1 / ((K : ℝ) + 1)

/-- Pure scalar inequality; its denominator is positive under the displayed bounds. -/
theorem scalar_support_error_bound (k A L : ℝ) (hk : 0 < k)
    (hA0 : 0 ≤ A) (hAhalf : A ≤ k / 2) (hAL : A ≤ L) :
    A ^ 2 / (k - A) + 1 / (k + 1) ≤ (2 * L ^ 2 + 1) / k := by
  have hL : 0 ≤ L := hA0.trans hAL
  have hd : 0 < k - A := by linarith
  have hsq : A ^ 2 ≤ L ^ 2 := by nlinarith
  have hfirst : A ^ 2 / (k - A) ≤ 2 * L ^ 2 / k := by
    apply (div_le_div_iff₀ hd hk).mpr
    have hgap : 0 ≤ k - 2 * A := by linarith
    have hgapmul : 0 ≤ L ^ 2 * (k - 2 * A) := mul_nonneg (sq_nonneg L) hgap
    nlinarith [mul_le_mul_of_nonneg_right hsq (le_of_lt hk)]
  have hsecond : (1 : ℝ) / (k + 1) ≤ 1 / k := by
    apply (div_le_div_iff₀ (show 0 < k + 1 by linarith) hk).mpr
    linarith
  calc
    A ^ 2 / (k - A) + 1 / (k + 1) ≤ 2 * L ^ 2 / k + 1 / k :=
      add_le_add hfirst hsecond
    _ = (2 * L ^ 2 + 1) / k := by rw [add_div]

theorem supportErrorSq_log_bound (K : ℕ) (hK : 1 ≤ K) :
    supportErrorSq K ≤ (2 * Real.log ((K : ℝ) + 1) ^ 2 + 1) / (K : ℝ) := by
  exact scalar_support_error_bound (K : ℝ) (supportA K)
    (Real.log ((K : ℝ) + 1)) (by exact_mod_cast (show 0 < K by omega))
    (supportA_nonneg K) (supportA_le_half K) (supportA_le_log K)

theorem supportErrorSq_nonneg (K : ℕ) (hK : 1 ≤ K) :
    0 ≤ supportErrorSq K := by
  have hk : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hhalf := supportA_le_half K
  have hd : 0 < (K : ℝ) - supportA K := by linarith
  unfold supportErrorSq
  positivity

theorem supportError_sqrt_bound (K : ℕ) (hK : 1 ≤ K) :
    Real.sqrt (supportErrorSq K) ≤
      Real.sqrt ((2 * Real.log ((K : ℝ) + 1) ^ 2 + 1) / (K : ℝ)) :=
  Real.sqrt_le_sqrt (supportErrorSq_log_bound K hK)

end RiemannResearch.RH.Pareto.DualSupportError
