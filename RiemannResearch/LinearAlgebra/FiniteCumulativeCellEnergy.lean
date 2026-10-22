import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact finite cumulative-cell energy and boundary correction cost

Source: user-provided `V_Zeta_Vector_Spaces_Research_2026-09-16.md`, §7.
These are finite algebraic identities for prescribed interval moments `w,b,d`.
For the Chebyshev application, the moments are the integrals of
`x^(-s-1)`, `x^(-s)`, and `x^(1-s)` over each prime-power interval.
This module does not identify those integrals, prove bounds for the actual
von Mangoldt vector, or assert that the optimal finite corrections are legal
Nyman--Beurling corrections. The omitted initial interval contributes the same
constant to the actual and free energies, so it cancels from their difference.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.CumulativeCellEnergy

def cumulative (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i

/-- The first target level is zero; later levels are interval weighted means. -/
def targetLevel (w b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => b i / w i

def optimalJumpCorrection (w b a : ℕ → ℝ) (i : ℕ) : ℝ :=
  targetLevel w b (i + 1) - targetLevel w b i - a i

/-- The complete signed quadratic, including background cross terms. -/
def signedCellEnergy (n : ℕ) (w b d a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (w i * cumulative a (i + 1) ^ 2 -
      2 * b i * cumulative a (i + 1) + d i)

def freeCellEnergy (n : ℕ) (w b d : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (d i - b i ^ 2 / w i)

/-- The last cumulative correction persists beyond the window with mass `τ`. -/
def correctionEnergy (n : ℕ) (w a : ℕ → ℝ) (τ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, w i * cumulative a (i + 1) ^ 2) +
    τ * cumulative a n ^ 2

theorem cumulative_add (a b : ℕ → ℝ) (n : ℕ) :
    cumulative (fun i => a i + b i) n = cumulative a n + cumulative b n := by
  simp [cumulative, Finset.sum_add_distrib]

theorem cumulative_difference (m : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (m (i + 1) - m i)) = m n - m 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem cumulative_optimalJumpCorrection (w b a : ℕ → ℝ) (n : ℕ) :
    cumulative (optimalJumpCorrection w b a) n =
      targetLevel w b n - cumulative a n := by
  unfold cumulative optimalJumpCorrection
  rw [Finset.sum_sub_distrib, cumulative_difference]
  simp [targetLevel]

theorem corrected_cumulative (w b a : ℕ → ℝ) (n : ℕ) :
    cumulative (fun i => a i + optimalJumpCorrection w b a i) n =
      targetLevel w b n := by
  rw [cumulative_add, cumulative_optimalJumpCorrection]
  ring

theorem one_cell_square_completion (w b d c : ℝ) (hw : w ≠ 0) :
    w * c ^ 2 - 2 * b * c + d =
      w * (c - b / w) ^ 2 + (d - b ^ 2 / w) := by
  field_simp [hw]
  ring

/-- The arithmetic discrepancy and geometric remainder are retained exactly. -/
theorem signedCellEnergy_eq_excess_add_free (n : ℕ) (w b d a : ℕ → ℝ)
    (hw : ∀ i ∈ Finset.range n, w i ≠ 0) :
    signedCellEnergy n w b d a =
      (∑ i ∈ Finset.range n, w i * (cumulative a (i + 1) - b i / w i) ^ 2) +
        freeCellEnergy n w b d := by
  unfold signedCellEnergy freeCellEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact one_cell_square_completion (w i) (b i) (d i)
    (cumulative a (i + 1)) (hw i hi)

theorem freeCellEnergy_le (n : ℕ) (w b d a : ℕ → ℝ)
    (hw : ∀ i ∈ Finset.range n, 0 < w i) :
    freeCellEnergy n w b d ≤ signedCellEnergy n w b d a := by
  rw [signedCellEnergy_eq_excess_add_free n w b d a
    (fun i hi => ne_of_gt (hw i hi))]
  have h : 0 ≤ ∑ i ∈ Finset.range n,
      w i * (cumulative a (i + 1) - b i / w i) ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_of_lt (hw i hi)) (sq_nonneg _)
  linarith

/-- The telescoping jump correction attains the unrestricted finite minimum. -/
theorem correction_attains_free_energy (n : ℕ) (w b d a : ℕ → ℝ)
    (hw : ∀ i ∈ Finset.range n, w i ≠ 0) :
    signedCellEnergy n w b d (fun i => a i + optimalJumpCorrection w b a i) =
      freeCellEnergy n w b d := by
  rw [signedCellEnergy_eq_excess_add_free n w b d _ hw]
  have hz : (∑ i ∈ Finset.range n,
      w i * (cumulative (fun j => a j + optimalJumpCorrection w b a j) (i + 1) -
        b i / w i) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [corrected_cumulative]
    simp [targetLevel]
  rw [hz, zero_add]

/-- Removing excess window energy costs that excess plus the exact tail charge. -/
theorem correction_energy_exact (n : ℕ) (w b d a : ℕ → ℝ) (τ : ℝ)
    (hw : ∀ i ∈ Finset.range n, w i ≠ 0) :
    correctionEnergy n w (optimalJumpCorrection w b a) τ =
      signedCellEnergy n w b d a - freeCellEnergy n w b d +
        τ * (targetLevel w b n - cumulative a n) ^ 2 := by
  unfold correctionEnergy
  simp_rw [cumulative_optimalJumpCorrection]
  rw [signedCellEnergy_eq_excess_add_free n w b d a hw]
  have he : (∑ i ∈ Finset.range n,
      w i * (targetLevel w b (i + 1) - cumulative a (i + 1)) ^ 2) =
      ∑ i ∈ Finset.range n, w i * (cumulative a (i + 1) - b i / w i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [targetLevel]
    ring
  rw [he]
  ring

theorem excess_le_correction_energy (n : ℕ) (w b d a : ℕ → ℝ) (τ : ℝ)
    (hw : ∀ i ∈ Finset.range n, w i ≠ 0) (hτ : 0 ≤ τ) :
    signedCellEnergy n w b d a - freeCellEnergy n w b d ≤
      correctionEnergy n w (optimalJumpCorrection w b a) τ := by
  rw [correction_energy_exact n w b d a τ hw]
  have h := mul_nonneg hτ (sq_nonneg (targetLevel w b n - cumulative a n))
  linarith


/-! ## Finite boundary reset and exact signed Abel energy

Source: user-provided continuation, Sections 14-15. Resetting at the next
boundary makes the cumulative correction vanish outside the finite window.
-/

/-- Keep the first `N` jumps and reset their accumulated value at index `N`. -/
def resetJump (a : ℕ → ℝ) (N i : ℕ) : ℝ :=
  if i < N then a i else if i = N then -cumulative a N else 0

theorem cumulative_resetJump (a : ℕ → ℝ) (N n : ℕ) :
    cumulative (resetJump a N) n = if n ≤ N then cumulative a n else 0 := by
  induction n with
  | zero => simp [cumulative]
  | succ n ih =>
    have hc (f : ℕ → ℝ) : cumulative f (n + 1) = cumulative f n + f n := by
      simp [cumulative, Finset.sum_range_succ]
    rw [hc, ih]
    by_cases hn : n < N
    · simp [resetJump, hn, Nat.le_of_lt hn, Nat.succ_le_iff.mpr hn, hc]
    · by_cases he : n = N
      · subst n
        simp [resetJump]
      · have h1 : ¬ n ≤ N := by omega
        have h2 : ¬ n + 1 ≤ N := by omega
        simp [resetJump, hn, he, h1, h2]

theorem resetJump_tail_zero (a : ℕ → ℝ) (N n : ℕ) (hn : N < n) :
    cumulative (resetJump a N) n = 0 := by
  simp [cumulative_resetJump, Nat.not_le.mpr hn]

/-- Finite cumulative energy for arbitrary cell weights, with no tail mass. -/
def weightedPrefixEnergy (w a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, w i * cumulative a (i + 1) ^ 2

theorem weightedPrefixEnergy_reset (w a : ℕ → ℝ) (N M : ℕ) (hNM : N ≤ M) :
    weightedPrefixEnergy w (resetJump a N) M = weightedPrefixEnergy w a N := by
  unfold weightedPrefixEnergy
  calc
    _ = ∑ i ∈ Finset.range N, w i * cumulative (resetJump a N) (i + 1) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hNM)
      intro i hi hin
      have hiN : N ≤ i := by simpa using hin
      rw [resetJump_tail_zero a N (i + 1) (by omega)]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [cumulative_resetJump, if_pos (Nat.succ_le_of_lt (Finset.mem_range.mp hi))]

theorem reset_optimal_head (w b a : ℕ → ℝ) (N n : ℕ) (hn : n ≤ N) :
    cumulative (fun i => a i + resetJump (optimalJumpCorrection w b a) N i) n =
      targetLevel w b n := by
  rw [cumulative_add, cumulative_resetJump, if_pos hn,
    cumulative_optimalJumpCorrection]
  ring

theorem reset_correction_energy_exact (N M : ℕ) (w b d a : ℕ → ℝ) (τ : ℝ)
    (hNM : N < M) (hw : ∀ i ∈ Finset.range N, w i ≠ 0) :
    correctionEnergy M w (resetJump (optimalJumpCorrection w b a) N) τ =
      signedCellEnergy N w b d a - freeCellEnergy N w b d := by
  change weightedPrefixEnergy w (resetJump (optimalJumpCorrection w b a) N) M +
    τ * cumulative (resetJump (optimalJumpCorrection w b a) N) M ^ 2 = _
  rw [weightedPrefixEnergy_reset w _ N M hNM.le,
    resetJump_tail_zero _ N M hNM]
  simpa [correctionEnergy, weightedPrefixEnergy] using
    (correction_energy_exact N w b d a 0 hw)

/-- Abel's identity keeps all signed earlier-current cross terms and the endpoint. -/
theorem weightedPrefixEnergy_signed_identity (a v : ℕ → ℝ) (N : ℕ) :
    weightedPrefixEnergy (fun i => v i - v (i + 1)) a N =
      (∑ i ∈ Finset.range N,
        v i * (a i ^ 2 + 2 * a i * cumulative a i)) -
          v N * cumulative a N ^ 2 := by
  induction N with
  | zero => simp [weightedPrefixEnergy, cumulative]
  | succ N ih =>
    have hc : cumulative a (N + 1) = cumulative a N + a N := by
      simp [cumulative, Finset.sum_range_succ]
    have he : weightedPrefixEnergy (fun i => v i - v (i + 1)) a (N + 1) =
        weightedPrefixEnergy (fun i => v i - v (i + 1)) a N +
          (v N - v (N + 1)) * cumulative a (N + 1) ^ 2 := by
      simp [weightedPrefixEnergy, Finset.sum_range_succ]
    rw [he, ih, Finset.sum_range_succ, hc]
    ring

theorem weightedPrefixEnergy_nonneg (w a : ℕ → ℝ) (N : ℕ)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ weightedPrefixEnergy w a N := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)

theorem weightedPrefixEnergy_mono (w a : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Monotone (weightedPrefixEnergy w a) := by
  intro N M hNM
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
    (fun i _ _ => mul_nonneg (hw i) (sq_nonneg _))

end RiemannResearch.LinearAlgebra.CumulativeCellEnergy
