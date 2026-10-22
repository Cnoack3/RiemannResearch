/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArgumentSamplingClosure

/-!
# Exact modular-reversal defect

Source: the modular reversal discussion in Sections 8--9 of the user-provided
`RH_CRT_Orbit_Exhaustion_and_Doubling_Invariance_2026-09-20(3).md` and the
9 October 2026 continuation. The source supports the statement and strategy.

The equality retains the full divisibility-site correction. It applies at n = 0
as well, where d ∣ 0. The physical Pareto weight at zero vanishes.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

theorem reverseResidue_mod_complement (d n : ℕ) (hd : 0 < d) :
    ((d - 1) * n) % d = if d ∣ n then 0 else d - n % d := by
  by_cases hdn : d ∣ n
  · have hr : n % d = 0 := Nat.mod_eq_zero_of_dvd hdn
    simp [hdn, Nat.mul_mod, hr]
  · have hr : n % d ≠ 0 := by
      intro h
      exact hdn (Nat.dvd_of_mod_eq_zero h)
    have hm : (d - 1) * n + n = d * n := by
      calc
        _ = ((d - 1) + 1) * n := by ring
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
    have hz : (((d - 1) * n) % d + n % d) % d = 0 := by
      rw [← Nat.add_mod, hm]
      simp
    have hl : d ≤ ((d - 1) * n) % d + n % d := by
      by_contra h
      have ht : ((d - 1) * n) % d + n % d < d := by omega
      rw [Nat.mod_eq_of_lt ht] at hz
      omega
    have hs : ((d - 1) * n) % d + n % d - d < d := by
      have h₁ := Nat.mod_lt ((d - 1) * n) hd
      have h₂ := Nat.mod_lt n hd
      omega
    rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt hs] at hz
    simp only [if_neg hdn]
    omega

theorem reverseResidue_complement (d n : ℕ) (hd : 0 < d) :
    1 - residueFraction d ((d - 1) * n) =
      residueFraction d n + (if d ∣ n then 1 else 0) := by
  have hdR : (d : ℝ) ≠ 0 := by positivity
  by_cases hdn : d ∣ n
  · have hr : n % d = 0 := Nat.mod_eq_zero_of_dvd hdn
    simp [residueFraction, reverseResidue_mod_complement d n hd, hdn, hr]
  · have hr : n % d ≤ d := Nat.le_of_lt (Nat.mod_lt n hd)
    simp only [residueFraction, reverseResidue_mod_complement d n hd,
      if_neg hdn, add_zero]
    rw [Nat.cast_sub hr]
    field_simp
    ring

theorem reverseResidue_error_square (d n : ℕ) (hd : 0 < d) :
    (1 - residueFraction d ((d - 1) * n)) ^ 2 =
      residueFraction d n ^ 2 + (if d ∣ n then 1 else 0) := by
  rw [reverseResidue_complement d n hd]
  by_cases hdn : d ∣ n
  · simp [hdn, residueFraction, Nat.mod_eq_zero_of_dvd hdn]
  · simp [hdn]

theorem reverseResidue_weighted_error_square (d n : ℕ) (hd : 0 < d) :
    positiveWeight n * (1 - residueFraction d ((d - 1) * n)) ^ 2 =
      positiveWeight n * residueFraction d n ^ 2 +
        (if d ∣ n then positiveWeight n else 0) := by
  rw [reverseResidue_error_square d n hd]
  split_ifs <;> ring

/-- The correction mass is summable in the actual physical measure. -/
theorem divisibility_weight_summable (d : ℕ) :
    Summable (fun n => if d ∣ n then positiveWeight n else 0) := by
  apply positiveWeight_summable.of_norm_bounded
  intro n
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg (positiveWeight_nonneg _)]
  · simp only [norm_zero]
    exact positiveWeight_nonneg _

/-- Complete infinite error identity: every divisibility-site mass survives. -/
theorem reverseResidue_full_error (d : ℕ) (hd : 0 < d) :
    (∑' n, positiveWeight n * (1 - residueFraction d ((d - 1) * n))^2) =
      (∑' n, positiveWeight n * residueFraction d n^2) +
        (∑' n, if d ∣ n then positiveWeight n else 0) := by
  have hs : Summable (fun n => positiveWeight n * residueFraction d n^2) := by
    simpa only [normalizedResidueHilbert_sequence] using
      hilbertSequence_square_summable (normalizedResidueHilbert d hd)
  simp_rw [reverseResidue_weighted_error_square d _ hd]
  exact hs.tsum_add (divisibility_weight_summable d)

/-- The exact equality is also an identity of actual Hilbert norms. -/
theorem reverseResidue_hilbert_error (d : ℕ) (hd : 2 ≤ d) :
    ‖hilbertOne - hilbertArgumentSampling (d - 1) (by omega)
        (normalizedResidueHilbert d (by omega))‖^2 =
      ‖normalizedResidueHilbert d (by omega)‖^2 +
        (∑' n, if d ∣ n then positiveWeight n else 0) := by
  have hsub (f g : ThresholdHilbert) :
      hilbertSequence (f - g) = hilbertSequence f - hilbertSequence g :=
    hilbertSequenceLinear.map_sub f g
  rw [hilbert_norm_weighted_sq, hsub,
    hilbertArgumentSampling_sequence, normalizedResidueHilbert_sequence,
    hilbert_norm_weighted_sq, normalizedResidueHilbert_sequence]
  calc
    _ = ∑' n, positiveWeight n * (1 - residueFraction d ((d - 1) * n))^2 := by
      apply tsum_congr
      intro n
      cases n with
      | zero => norm_num [positiveWeight]
      | succ n => simp [hilbertOne_sequence, zeroAnchor]
    _ = _ := reverseResidue_full_error d (by omega)

/-- The nonsquarefree conductor-four coefficient has a finite coordinate dual. -/
def conductorFourFunctional (f : ℕ → ℝ) : ℝ :=
  -f 1 + f 2 + f 3 - f 4

theorem conductorFourFunctional_residue (d : ℕ) (hd : 2 ≤ d) :
    conductorFourFunctional (residueFraction d) = if d = 4 then 1 else 0 := by
  by_cases hlarge : 5 ≤ d
  · have hne : d ≠ 4 := by omega
    simp only [conductorFourFunctional, residueFraction, if_neg hne]
    rw [Nat.mod_eq_of_lt (by omega : 1 < d),
      Nat.mod_eq_of_lt (by omega : 2 < d),
      Nat.mod_eq_of_lt (by omega : 3 < d),
      Nat.mod_eq_of_lt (by omega : 4 < d)]
    norm_num
    ring
  · have hcases : d = 2 ∨ d = 3 ∨ d = 4 := by omega
    rcases hcases with rfl | rfl | rfl <;>
      norm_num [conductorFourFunctional, residueFraction]

theorem conductorFourFunctional_doubled_three :
    conductorFourFunctional (fun n => residueFraction 3 (2 * n)) = -1 := by
  norm_num [conductorFourFunctional, residueFraction]

theorem conductorFourFunctional_one : conductorFourFunctional (fun _ => 1) = 0 := by
  norm_num [conductorFourFunctional]

end RiemannResearch.RH.Pareto
