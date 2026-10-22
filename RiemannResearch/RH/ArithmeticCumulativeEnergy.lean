import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Tactic

/-!
# Arithmetic cumulative energy and balanced divisibility

All sums run over the positive integer arguments of a single arithmetic
function. No independence assumption is used. The energy formula retains the
signed cross terms and the terminal boundary contribution.
-/

namespace RiemannResearch.RH.ArithmeticCumulative
noncomputable section
open scoped BigOperators

def energyPrefix (f : ℕ → ℝ) (R : ℕ) : ℝ :=
  ∑ k ∈ Finset.range R, weight (k + 1) * (cumulative f (k + 1)) ^ 2

@[simp] theorem energyPrefix_zero (f : ℕ → ℝ) : energyPrefix f 0 = 0 := by
  simp [energyPrefix]

@[simp] theorem energyPrefix_succ (f : ℕ → ℝ) (R : ℕ) :
    energyPrefix f (R + 1) = energyPrefix f R +
      weight (R + 1) * (cumulative f (R + 1)) ^ 2 := by
  simp [energyPrefix, Finset.sum_range_succ]

theorem energyPrefix_nonneg (f : ℕ → ℝ) (R : ℕ) : 0 ≤ energyPrefix f R := by
  exact Finset.sum_nonneg fun k _ => mul_nonneg (weight_nonneg _) (sq_nonneg _)

/-- A triangular form of the full signed Green energy, including its boundary.
`2*f(k+1)*cumulative(f,k)` contains every earlier signed cross term. -/
theorem energyPrefix_signed_identity (f : ℕ → ℝ) (R : ℕ) :
    energyPrefix f R =
      (∑ k ∈ Finset.range R,
        (f (k + 1) ^ 2 + 2 * f (k + 1) * cumulative f k) / ((k : ℝ) + 1)) -
      (cumulative f R) ^ 2 / ((R : ℝ) + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [energyPrefix_succ, ih, Finset.sum_range_succ,
      weight_eq_sub (R + 1) (by omega), cumulative_succ]
    push_cast
    ring

/-- Pointwise balance on a repaired head follows from one scalar moment equation. -/
theorem coupled_head_repair (y n : ℕ) (s : Finset ℕ) (t : ℕ → ℝ)
    (R : ℕ → ℝ) (α : ℝ)
    (hn : n ≤ y) (hhead : R n = 1)
    (hs : ∀ d ∈ s, y < d)
    (hbalance : ∑ d ∈ s, t d / (d : ℝ) = -α) :
    R n - α * n - ∑ d ∈ s, t d * residueFraction d n = 1 := by
  have he : (∑ d ∈ s, t d * residueFraction d n) = (n : ℝ) * (-α) := by
    calc
      _ = ∑ d ∈ s, (n : ℝ) * (t d / (d : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [residueFraction, Nat.mod_eq_of_lt (lt_of_le_of_lt hn (hs d hd))]
        ring
      _ = (n : ℝ) * ∑ d ∈ s, t d / (d : ℝ) := by rw [Finset.mul_sum]
      _ = _ := by rw [hbalance]
  rw [he, hhead]
  ring

/-- Exact error decomposition for a real inner-product correction. -/
theorem scalar_correction_square (e w c : ℝ) :
    (e - c * w) ^ 2 = e ^ 2 - 2 * c * (e * w) + c ^ 2 * w ^ 2 := by ring

end
end RiemannResearch.RH.ArithmeticCumulative
