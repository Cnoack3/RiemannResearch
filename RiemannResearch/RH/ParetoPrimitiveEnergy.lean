import RiemannResearch.RH.ParetoCovariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exact full energy of anchored discrete primitives

Source: direct weighted-shift and parallelogram calculation for the user's
exact CRT primitive identity. The backward shift retains every Pareto mass. The shift defect and the
symmetric primitive square are displayed in the complete energy identity;
neither remainder is discarded. Boundedness discharges every summability
obligation. Anchoring at zero is needed for nonnegativity of the defect,
but not for the exact identities themselves.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PrimitiveEnergy

noncomputable section

def backwardShift (f : ℕ → ℝ) (n : ℕ) : ℝ := f (n - 1)

def difference (f : ℕ → ℝ) (n : ℕ) : ℝ := f n - backwardShift f n

def symmetricPrimitive (f : ℕ → ℝ) (n : ℕ) : ℝ := f n + backwardShift f n

def energy (f : ℕ → ℝ) : ℝ := paretoInner f f

def shiftDefect (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, (positiveWeight n - positiveWeight (n + 1)) * (f n * f n)

theorem backwardShift_bounded {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) : ∀ n, |backwardShift f n| ≤ C := by
  intro n
  exact hf (n - 1)

theorem energy_summable {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    Summable (fun n => positiveWeight n * (f n * f n)) :=
  weighted_summable_of_bounded (bounded_product hf hf)

theorem shifted_energy_summable {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    Summable (fun n => positiveWeight (n + 1) * (f n * f n)) := by
  have hs := energy_summable (backwardShift_bounded hf)
  have hs' := (summable_nat_add_iff 1).mpr hs
  simpa [backwardShift] using hs'

/-- Exact reindexing, including the anchored endpoint contribution. -/
theorem energy_backwardShift {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    energy (backwardShift f) =
      ∑' n : ℕ, positiveWeight (n + 1) * (f n * f n) := by
  have hs := energy_summable (backwardShift_bounded hf)
  unfold energy paretoInner
  rw [hs.tsum_eq_zero_add]
  simp [backwardShift, positiveWeight]

theorem shiftDefect_summable {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    Summable (fun n =>
      (positiveWeight n - positiveWeight (n + 1)) * (f n * f n)) := by
  simpa only [sub_mul] using (energy_summable hf).sub (shifted_energy_summable hf)

/-- Complete exact shift defect. No endpoint has been suppressed. -/
theorem energy_sub_backwardShift {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    energy f - energy (backwardShift f) = shiftDefect f := by
  rw [energy_backwardShift hf]
  unfold energy paretoInner shiftDefect
  simp only [sub_mul]
  exact ((energy_summable hf).tsum_sub (shifted_energy_summable hf)).symm

theorem positiveWeight_succ_le (n : ℕ) (hn : 0 < n) :
    positiveWeight (n + 1) ≤ positiveWeight n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold positiveWeight
  apply one_div_le_one_div_of_le
  · positivity
  · push_cast
    nlinarith

/-- The only exceptional weight is at zero; the anchor removes it exactly. -/
theorem shiftDefect_nonneg {f : ℕ → ℝ} (hf0 : f 0 = 0) :
    0 ≤ shiftDefect f := by
  apply tsum_nonneg
  intro n
  cases n with
  | zero => simp [hf0]
  | succ n =>
      exact mul_nonneg
        (sub_nonneg.mpr (positiveWeight_succ_le (n + 1) (Nat.succ_pos n)))
        (mul_self_nonneg _)

/-- Exact parallelogram identity with both the full symmetric square and
twice the full shift defect retained. -/
theorem full_primitive_energy_identity {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) :
    4 * energy f = energy (difference f) + energy (symmetricPrimitive f) +
      2 * shiftDefect f := by
  have hs := backwardShift_bounded hf
  have hm := paretoInner_residual_polynomial hf hs (1 : ℝ)
  have hp := paretoInner_residual_polynomial hf hs (-1 : ℝ)
  have hminus : energy (difference f) =
      energy f - 2 * paretoInner f (backwardShift f) + energy (backwardShift f) := by
    change paretoInner (fun k => f k - backwardShift f k)
      (fun k => f k - backwardShift f k) = _
    simpa [energy] using hm
  have hplus : energy (symmetricPrimitive f) =
      energy f + 2 * paretoInner f (backwardShift f) + energy (backwardShift f) := by
    change paretoInner (fun k => f k + backwardShift f k)
      (fun k => f k + backwardShift f k) = _
    simpa [energy] using hp
  have hd := energy_sub_backwardShift hf
  linarith

/-- The derivative contraction is a consequence of the exact full identity. -/
theorem difference_energy_le {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C) (hf0 : f 0 = 0) :
    energy (difference f) ≤ 4 * energy f := by
  have hid := full_primitive_energy_identity hf
  have hd := shiftDefect_nonneg hf0
  have hs : 0 ≤ energy (symmetricPrimitive f) := paretoInner_self_nonneg _
  linarith

end
end RiemannResearch.RH.Pareto.PrimitiveEnergy
