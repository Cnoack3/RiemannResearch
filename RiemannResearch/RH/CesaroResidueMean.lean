import RiemannResearch.Probability.ConditionalIIDUniformMoments
import RiemannResearch.RH.ArithmeticCumulativeEnergy
import Mathlib.Tactic

/-!
# Exact Cesaro means of the normalized residue generators

Source: `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 7. All definitions are the existing project definitions.
-/

namespace RiemannResearch.RH.ArithmeticCumulative.CesaroResidue
noncomputable section
open scoped BigOperators
open RiemannResearch.Probability.ConditionalIID (cesaro)

lemma cesaro_eq_cumulative (F : ℕ → ℝ) (t : ℕ) :
    cesaro F t = cumulative F t / (t : ℝ) := by
  unfold cesaro cumulative
  congr 1
  symm
  refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro n₁ hn₁ n₂ hn₂ h
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n hn
    rfl

lemma sum_range_real (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_range_successor_real (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  rw [Finset.sum_add_distrib, sum_range_real]
  simp
  ring

lemma residueFraction_period_shift (d k n : ℕ) :
    residueFraction d (k * d + n) = residueFraction d n := by
  simp [residueFraction, Nat.add_mod]

/-- A complete period has the exact unnormalized sum d(d−1)/2. -/
lemma sum_residue_first_period (d : ℕ) :
    (∑ n ∈ Finset.range d, (((n + 1) % d : ℕ) : ℝ)) =
      (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  have hshift := Finset.sum_range_succ' (fun n : ℕ => ((n % d : ℕ) : ℝ)) d
  rw [Finset.sum_range_succ] at hshift
  simp only [Nat.mod_self, Nat.zero_mod, Nat.cast_zero, add_zero, zero_add] at hshift
  calc
    _ = ∑ n ∈ Finset.range d, ((n % d : ℕ) : ℝ) := by linarith
    _ = ∑ n ∈ Finset.range d, (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
    _ = _ := sum_range_real d

/-- A complete normalized-residue period has sum (d−1)/2. -/
theorem cumulative_residue_complete_period (d : ℕ) (hd : 0 < d) :
    cumulative (residueFraction d) d = ((d : ℝ) - 1) / 2 := by
  have hdR : (d : ℝ) ≠ 0 := by positivity
  unfold cumulative residueFraction
  rw [← Finset.sum_div, sum_residue_first_period]
  field_simp
  <;> ring

lemma cumulative_residue_multiple_add (d k r : ℕ) :
    cumulative (residueFraction d) (k * d + r) =
      cumulative (residueFraction d) (k * d) + cumulative (residueFraction d) r := by
  unfold cumulative
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.add_assoc, residueFraction_period_shift]

/-- Exact sum over any number of complete periods. -/
theorem cumulative_residue_complete_periods (d k : ℕ) (hd : 0 < d) :
    cumulative (residueFraction d) (k * d) =
      (k : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, cumulative_residue_multiple_add,
      ih, cumulative_residue_complete_period d hd]
    push_cast
    ring

/-- Exact triangular sum before the first wrap. -/
theorem cumulative_residue_remainder (d r : ℕ) (hr : r < d) :
    cumulative (residueFraction d) r = (r : ℝ) * ((r : ℝ) + 1) / (2 * (d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := by
    have : 0 < d := by omega
    positivity
  have hs : (∑ n ∈ Finset.range r, (((n + 1) % d : ℕ) : ℝ)) =
      (r : ℝ) * ((r : ℝ) + 1) / 2 := by
    calc
      _ = ∑ n ∈ Finset.range r, ((n : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hn; omega)]
        simp only [Nat.cast_add, Nat.cast_one]
      _ = _ := sum_range_successor_real r
  unfold cumulative residueFraction
  rw [← Finset.sum_div, hs]
  field_simp
  <;> ring

/-- The handoff's exact complete-period plus remainder formula. -/
theorem cesaro_residue_period_remainder (d k r : ℕ) (hd : 0 < d) (hr : r < d) :
    cesaro (residueFraction d) (k * d + r) =
      ((k : ℝ) * ((d : ℝ) - 1) / 2 +
        (r : ℝ) * ((r : ℝ) + 1) / (2 * (d : ℝ))) / ((k * d + r : ℕ) : ℝ) := by
  rw [cesaro_eq_cumulative, cumulative_residue_multiple_add,
    cumulative_residue_complete_periods d k hd, cumulative_residue_remainder d r hr]

/-- Quotient/remainder form for any arithmetic endpoint. -/
theorem cesaro_residue_exact (d t : ℕ) (hd : 0 < d) :
    cesaro (residueFraction d) t =
      (((t / d : ℕ) : ℝ) * ((d : ℝ) - 1) / 2 +
        ((t % d : ℕ) : ℝ) * (((t % d : ℕ) : ℝ) + 1) / (2 * (d : ℝ))) / (t : ℝ) := by
  have he : (t / d) * d + t % d = t := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod t d
  have h := cesaro_residue_period_remainder d (t / d) (t % d) hd (Nat.mod_lt t hd)
  simpa only [he] using h

/-- Normalized residue conditional means are always nonnegative. -/
theorem cesaro_residue_nonneg (d t : ℕ) : 0 ≤ cesaro (residueFraction d) t := by
  unfold cesaro
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro n hn
    unfold residueFraction
    positivity
  · positivity

/-- The exact mean is at most one half, including endpoints before the first wrap. -/
theorem cesaro_residue_le_half (d t : ℕ) (hd : 0 < d) :
    cesaro (residueFraction d) t ≤ 1 / 2 := by
  by_cases ht : t = 0
  · subst t
    simp [cesaro]
  have htR : (0 : ℝ) < t := by exact_mod_cast (Nat.pos_of_ne_zero ht)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrD : ((t % d : ℕ) : ℝ) + 1 ≤ d := by
    exact_mod_cast (show t % d + 1 ≤ d by have := Nat.mod_lt t hd; omega)
  have hrem : ((t % d : ℕ) : ℝ) * (((t % d : ℕ) : ℝ) + 1) / (2 * (d : ℝ)) ≤
      ((t % d : ℕ) : ℝ) / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))).2
    have hm := mul_le_mul_of_nonneg_left hrD (Nat.cast_nonneg (t % d) : (0 : ℝ) ≤ _)
    nlinarith
  have hquot : ((t / d : ℕ) : ℝ) * ((d : ℝ) - 1) / 2 ≤
      ((t / d : ℕ) : ℝ) * (d : ℝ) / 2 := by
    nlinarith [show (0 : ℝ) ≤ ((t / d : ℕ) : ℝ) by positivity]
  have hdecomp : ((t / d : ℕ) : ℝ) * (d : ℝ) + ((t % d : ℕ) : ℝ) = (t : ℝ) := by
    exact_mod_cast (show (t / d) * d + t % d = t by
      simpa only [Nat.mul_comm] using Nat.div_add_mod t d)
  rw [cesaro_residue_exact d t hd]
  apply (div_le_iff₀ htR).2
  nlinarith

/-- The complete-period average is independent of the positive number of periods. -/
theorem cesaro_residue_complete_periods (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
    cesaro (residueFraction d) (k * d) = ((d : ℝ) - 1) / (2 * (d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by positivity
  rw [cesaro_eq_cumulative, cumulative_residue_complete_periods d k hd]
  push_cast
  field_simp
  <;> ring

end
end RiemannResearch.RH.ArithmeticCumulative.CesaroResidue
