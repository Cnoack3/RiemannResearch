/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Wiener
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Absolute harmonic moments under an exponent gap

A gap of twice the iterated logarithm pays for the summable factor
`1 / (n * log(n)^2)`. The displacement applications use the zeta-two
normalization of the physical weights.
-/
noncomputable section
open Filter

namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- An eventual bound with exponent V gives summability with damping U
whenever the difference pays for two powers of the logarithm. -/
theorem summable_harmonic_moment_of_exponent_gap (f U V : ℕ → ℝ) (D : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, |f n| ≤ D * Real.exp (V n))
    (hgap : ∀ᶠ n : ℕ in atTop, 2 * Real.log (Real.log (n : ℝ)) ≤ U n - V n) :
    Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) * Real.exp (-(U n))) * |f n|) := by
  apply (summable_inv_mul_log_sq.mul_left (|D| / zetaTwo)).of_norm_bounded_eventually_nat
  filter_upwards [hf, hgap, eventually_ge_atTop (2 : ℕ)] with n hn hdiff hn2
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hl := Real.log_pos hn1
  have he : Real.exp (-(U n)) * |f n| ≤ |D| * Real.exp (V n - U n) := by
    calc
      _ ≤ Real.exp (-(U n)) * (|D| * Real.exp (V n)) :=
        mul_le_mul_of_nonneg_left
          (hn.trans (mul_le_mul_of_nonneg_right (le_abs_self D) (Real.exp_pos _).le))
          (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hsave : Real.exp (V n - U n) ≤ 1 / (Real.log (n : ℝ)) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    have hlog : (Real.log (n : ℝ)) ^ 2 = Real.exp (2 * Real.log (Real.log (n : ℝ))) := by
      rw [two_mul, Real.exp_add, Real.exp_log hl, pow_two]
    rw [hlog, ← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hterm := he.trans (mul_le_mul_of_nonneg_left hsave (abs_nonneg D))
  change ‖positiveQWeight n * ((n : ℝ) * Real.exp (-(U n))) * |f n|‖ ≤
    (|D| / zetaTwo) * ((n : ℝ) * Real.log (n : ℝ) ^ 2)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (positiveQWeight_nonneg n)
    (mul_nonneg hn0.le (Real.exp_pos _).le)) (abs_nonneg _))]
  calc
    _ = (positiveQWeight n * (n : ℝ)) * (Real.exp (-(U n)) * |f n|) := by ring
    _ ≤ (positiveQWeight n * (n : ℝ)) * (|D| * (1 / Real.log (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hterm (mul_nonneg (positiveQWeight_nonneg n) hn0.le)
    _ = _ := by
      unfold positiveQWeight
      field_simp [zetaTwo_pos.ne', hn0.ne', hl.ne']

/-- Summability of a weighted first moment off E extends across E if the
weight has finite Q-energy there. The physical vector may be arbitrary. -/
theorem summable_physical_moment_off_exceptional (u : QHilbert) (W : ℕ → ℝ)
    (hW : ∀ n, 0 ≤ W n) (E : ℕ → Prop) [DecidablePred E]
    (hg : Summable (fun n : ℕ => if E n then 0 else positiveQWeight n * W n * |qSequence u n|))
    (he : Summable (fun n : ℕ => if E n then positiveQWeight n * (W n)^2 else 0)) :
    Summable (fun n : ℕ => positiveQWeight n * W n * |qSequence u n|) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (positiveQWeight_nonneg n) (hW n)) (abs_nonneg _))
    _ ((hg.add he).add (qSequence_square_summable u))
  intro n
  change _ ≤ ((if E n then 0 else positiveQWeight n * W n * |qSequence u n|) +
    (if E n then positiveQWeight n * (W n)^2 else 0)) + positiveQWeight n * qSequence u n^2
  by_cases hn : E n
  · simp only [if_pos hn, zero_add]
    rw [mul_assoc, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
    nlinarith only [sq_nonneg (W n - |qSequence u n|), sq_abs (qSequence u n),
      sq_nonneg (W n), sq_nonneg (qSequence u n)]
  · simp only [if_neg hn, add_zero]
    exact le_add_of_nonneg_right (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))

/-- In harmonic coordinates the condition on E is an ordinary unweighted
sum of F squared. Away from E, any eventual summable majorant g suffices. -/
theorem summable_harmonic_moment_off_exceptional (u : QHilbert) (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n) (E : ℕ → Prop) [DecidablePred E]
    (g : ℕ → ℝ) (hg : Summable g)
    (hgood : ∀ᶠ n : ℕ in atTop, ¬ E n →
      positiveQWeight n * ((n : ℝ) * F n) * |qSequence u n| ≤ g n)
    (hE : Summable (fun n : ℕ => if E n then (F n)^2 else 0)) :
    Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) * F n) * |qSequence u n|) := by
  apply summable_physical_moment_off_exceptional u _
    (fun n => mul_nonneg (Nat.cast_nonneg _) (hF n)) E
  · apply hg.abs.of_norm_bounded_eventually_nat
    filter_upwards [hgood] with n hn
    by_cases h : E n
    · simpa only [if_pos h, norm_zero] using abs_nonneg (g n)
    · rw [if_neg h, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (positiveQWeight_nonneg n) (mul_nonneg (Nat.cast_nonneg n) (hF n)))
          (abs_nonneg (qSequence u n)))]
      exact (hn h).trans (le_abs_self _)
  · apply (hE.mul_left (1 / zetaTwo)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    by_cases h : E n
    · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      simp only [if_pos h, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg ((n : ℝ) * F n)))]
      exact le_of_eq (by unfold positiveQWeight; field_simp [zetaTwo_pos.ne', hnR.ne'])
    · simp [h]

/-- A growth bound away from E suffices for the harmonic first moment
when the squared damping is summable on E. -/
theorem summable_harmonic_moment_of_exponent_gap_off_exceptional
    (u : QHilbert) (U V : ℕ → ℝ) (D : ℝ) (E : ℕ → Prop) [DecidablePred E]
    (hE : Summable (fun n : ℕ => if E n then (Real.exp (-(U n))) ^ 2 else 0))
    (hf : ∀ᶠ n : ℕ in atTop, ¬ E n → |qSequence u n| ≤ D * Real.exp (V n))
    (hgap : ∀ᶠ n : ℕ in atTop, 2 * Real.log (Real.log (n : ℝ)) ≤ U n - V n) :
    Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) * Real.exp (-(U n))) *
      |qSequence u n|) := by
  let f (n : ℕ) := if E n then 0 else qSequence u n
  have hbound : ∀ᶠ n : ℕ in atTop, |f n| ≤ |D| * Real.exp (V n) := by
    filter_upwards [hf] with n hn
    by_cases h : E n
    · simp only [f, if_pos h, abs_zero]
      exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    · simp only [f, if_neg h]
      exact (hn h).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  have hg := summable_harmonic_moment_of_exponent_gap f U V |D| hbound hgap
  apply summable_harmonic_moment_off_exceptional u _ (fun _ => (Real.exp_pos _).le) E _ hg _ hE
  exact Eventually.of_forall (fun n hn => by simp [f, hn])

end RiemannResearch.RH.ZetaTwoHilbert
