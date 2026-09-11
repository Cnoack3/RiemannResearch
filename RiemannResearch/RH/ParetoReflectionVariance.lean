/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.FinitePairVariance
import RiemannResearch.RH.ParetoReflectionWeightBounds
import RiemannResearch.RH.ParetoProgressionCalculus
import RiemannResearch.RH.ParetoLegalStructure

/-!
# Reflection-pair conditioning for the actual Pareto variance

Source: user discussion, 11 September 2026. We sum over every residue and
divide the paired expressions by two, so each unordered pair is counted once.
The weights are the full infinite progression masses. No conditional mean is
asserted to be a legal witness, and no approximating sequence is assumed to exist.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Full Pareto mass of a residue indexed from zero. -/
def residueMass (Q : ℕ) (r : Fin Q) : ℝ :=
  progressionWeight Q (if r.val = 0 then Q else r.val)

theorem residueMass_pos (Q : ℕ) (hQ : 0 < Q) (r : Fin Q) :
    0 < residueMass Q r := by
  unfold residueMass
  split_ifs with h
  · exact progressionWeight_pos Q Q hQ hQ
  · exact progressionWeight_pos Q r.val hQ (by omega)

theorem residueMass_ge_inv_sq (Q : ℕ) (hQ : 0 < Q) (r : Fin Q) :
    1 / (Q : ℝ)^2 ≤ residueMass Q r := by
  unfold residueMass
  split_ifs with h
  · exact progressionWeight_ge_inv_sq Q Q hQ hQ le_rfl
  · exact progressionWeight_ge_inv_sq Q r.val hQ (by omega) (Nat.le_of_lt r.isLt)

/-- Changing the representative of the zero class preserves a full-period sum. -/
theorem residueMass_sum (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ)
    (hzero : f Q = f 0) :
    (∑ r : Fin Q, residueMass Q r * f r.val) =
      ∑ r : Fin Q, progressionWeight Q (r.val+1) * f (r.val+1) := by
  cases Q with
  | zero => omega
  | succ k =>
    have hleft : (∑ r : Fin (k+1), residueMass (k+1) r * f r.val) =
        progressionWeight (k+1) (k+1) * f 0 +
          ∑ r : Fin k, progressionWeight (k+1) (r.val+1) * f (r.val+1) := by
      rw [Fin.sum_univ_succ]
      simp [residueMass]
    have hright : (∑ r : Fin (k+1), progressionWeight (k+1) (r.val+1) * f (r.val+1)) =
        (∑ r : Fin k, progressionWeight (k+1) (r.val+1) * f (r.val+1)) +
          progressionWeight (k+1) (k+1) * f (k+1) := by
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hleft, hright, hzero]
    ring

theorem residueMass_normalization (Q : ℕ) (hQ : 0 < Q) :
    (∑ r : Fin Q, residueMass Q r) = 1 := by
  have h := residueMass_sum Q hQ (fun _ => 1) rfl
  simpa only [mul_one, progressionWeight_normalization Q hQ] using h

theorem periodic_paretoMean_zero_residues (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) {B : ℝ} (hf : ∀ n, |f n| ≤ B)
    (hp : ∀ n, f (n+Q) = f n) :
    paretoMean f = ∑ r : Fin Q, residueMass Q r * f r.val := by
  rw [residueMass_sum Q hQ f (by simpa using hp 0)]
  exact periodic_paretoMean Q hQ f hf hp

/-- Full squared error about an arbitrary center, using zero-based residues. -/
def residueCenteredError (Q : ℕ) (f : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∑ r : Fin Q, residueMass Q r * (f r.val-a)^2

theorem periodic_paretoVariance_zero_residues (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) {B : ℝ} (hf : ∀ n, |f n| ≤ B)
    (hp : ∀ n, f (n+Q) = f n) :
    paretoVariance f = residueCenteredError Q f (paretoMean f) := by
  have hb : ∀ n, |f n-paretoMean f| ≤ B+|paretoMean f| := by
    intro n
    exact (abs_sub _ _).trans (add_le_add (hf n) le_rfl)
  rw [paretoVariance, periodic_paretoInner Q hQ _ hb (by intro n; rw [hp])]
  unfold residueCenteredError
  rw [residueMass_sum Q hQ (fun n => (f n-paretoMean f)^2)
    (by rw [show f Q = f 0 by simpa using hp 0])]

/-- Pair calibration, counted once per unordered reflection pair. -/
def reflectionCalibration (Q : ℕ) (f : ℕ → ℝ) (a : ℝ) : ℝ :=
  FinitePairVariance.calibration Finset.univ (residueMass Q)
    (fun r => residueMass Q r.rev) (fun r => f r.val)
    (fun r => f r.rev.val) a / 2

/-- Expected conditional variance, counted once per unordered pair. -/
def reflectionNoise (Q : ℕ) (f : ℕ → ℝ) (C : ℝ) : ℝ :=
  FinitePairVariance.noise Finset.univ (residueMass Q)
    (fun r => residueMass Q r.rev) (fun r => f r.val) C / 2

/-- Uniform full-period centered energy; under reflection its center is the mean. -/
def uniformReflectionVariance (Q : ℕ) (f : ℕ → ℝ) (C : ℝ) : ℝ :=
  (∑ r : Fin Q, (f r.val-C/2)^2) / Q

/-- The explicit upper objective used for the approximation problem. -/
def reflectionSurrogate (Q : ℕ) (f : ℕ → ℝ) (a C : ℝ) : ℝ :=
  reflectionCalibration Q f a + Real.pi^2 / Q * uniformReflectionVariance Q f C

private theorem sum_fin_rev (Q : ℕ) (h : Fin Q → ℝ) :
    (∑ r : Fin Q, h r.rev) = ∑ r : Fin Q, h r := by
  exact Equiv.sum_comp Fin.revPerm h

/-- Reflection forces the uniform residue mean to be exactly C/2. -/
theorem reflection_uniform_mean (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) (C : ℝ)
    (href : ∀ n, n < Q → f n + f (Q-1-n) = C) :
    (∑ r : Fin Q, f r.val) / Q = C/2 := by
  have hs : (∑ r : Fin Q, (f r.val + f r.rev.val)) = (Q : ℝ)*C := by
    calc
      _ = ∑ _r : Fin Q, C := by
        apply Finset.sum_congr rfl
        intro r _
        simpa [Fin.val_rev, Nat.sub_sub, Nat.add_comm] using href r.val r.isLt
      _ = _ := by simp
  rw [Finset.sum_add_distrib, sum_fin_rev Q (fun r => f r.val)] at hs
  have hq : (Q : ℝ) ≠ 0 := by positivity
  apply (div_eq_iff hq).mpr
  linarith

/-- The reflection-centered energy is the usual uniform variance. -/
theorem uniformReflectionVariance_eq_uniform_variance (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) (C : ℝ)
    (href : ∀ n, n < Q → f n + f (Q-1-n) = C) :
    uniformReflectionVariance Q f C =
      (∑ r : Fin Q, (f r.val - (∑ t : Fin Q, f t.val) / Q)^2) / Q := by
  rw [reflection_uniform_mean Q hQ f C href]
  rfl

private theorem reflection_fullError (Q : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    FinitePairVariance.fullError Finset.univ (residueMass Q)
      (fun r => residueMass Q r.rev) (fun r => f r.val)
      (fun r => f r.rev.val) a = 2 * residueCenteredError Q f a := by
  unfold FinitePairVariance.fullError residueCenteredError
  rw [Finset.sum_add_distrib]
  rw [sum_fin_rev Q (fun r => residueMass Q r * (f r.val-a)^2)]
  ring

theorem reflectionCalibration_nonneg (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) (a : ℝ) : 0 ≤ reflectionCalibration Q f a := by
  exact div_nonneg (FinitePairVariance.calibration_nonneg _ _ _ _ _ _
    (fun r _ => residueMass_pos Q hQ r)
    (fun r _ => residueMass_pos Q hQ r.rev)) (by norm_num)

theorem reflectionNoise_nonneg (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) (C : ℝ) : 0 ≤ reflectionNoise Q f C := by
  exact div_nonneg (FinitePairVariance.noise_nonneg _ _ _ _ _
    (fun r _ => residueMass_pos Q hQ r)
    (fun r _ => residueMass_pos Q hQ r.rev)) (by norm_num)

theorem uniformReflectionVariance_nonneg (Q : ℕ) (f : ℕ → ℝ) (C : ℝ) :
    0 ≤ uniformReflectionVariance Q f C := by
  unfold uniformReflectionVariance
  positivity

/-- Exact total variance in finite squared-error form, with the actual weights. -/
theorem residueCenteredError_eq_reflection (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) (a C : ℝ)
    (href : ∀ n, n < Q → f n + f (Q-1-n) = C) :
    residueCenteredError Q f a = reflectionCalibration Q f a + reflectionNoise Q f C := by
  have hr (r : Fin Q) : f r.val + f r.rev.val = C := by
    simpa [Fin.val_rev, Nat.sub_sub, Nat.add_comm] using href r.val r.isLt
  have h := FinitePairVariance.fullError_eq_calibration_add_noise
    Finset.univ (residueMass Q) (fun r => residueMass Q r.rev)
    (fun r => f r.val) (fun r => f r.rev.val) a C
    (fun r _ => residueMass_pos Q hQ r)
    (fun r _ => residueMass_pos Q hQ r.rev) (fun r _ => hr r)
  rw [reflection_fullError] at h
  unfold reflectionCalibration reflectionNoise
  linarith

/-- The finite identity is the complete infinite Pareto variance identity. -/
theorem paretoVariance_eq_reflection (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) {B : ℝ} (hf : ∀ n, |f n| ≤ B)
    (hp : ∀ n, f (n+Q) = f n) (C : ℝ)
    (href : ∀ n, n < Q → f n + f (Q-1-n) = C) :
    paretoVariance f = reflectionCalibration Q f (paretoMean f) + reflectionNoise Q f C := by
  rw [periodic_paretoVariance_zero_residues Q hQ f hf hp]
  exact residueCenteredError_eq_reflection Q hQ f _ C href

/-- In an even period at least one member of each pair has upper-half mass. -/
theorem residueMass_reflection_small (Q : ℕ) (hQ : 0 < Q) (heven : Even Q)
    (r : Fin Q) :
    residueMass Q r ≤ Real.pi^2 / (2*(Q : ℝ)^2) ∨
      residueMass Q r.rev ≤ Real.pi^2 / (2*(Q : ℝ)^2) := by
  have hh : Q ≤ 2*r.val ∨ Q ≤ 2*r.rev.val := by
    obtain ⟨k, hk⟩ := heven
    simp only [Fin.val_rev]
    omega
  rcases hh with hh | hh
  · left
    have hr : 0 < r.val := by omega
    simpa only [residueMass, if_neg (ne_of_gt hr)] using progressionWeight_upper_half Q r.val hQ hr hh
  · right
    have hr : 0 < r.rev.val := by omega
    simpa only [residueMass, if_neg (ne_of_gt hr)] using progressionWeight_upper_half Q r.rev.val hQ hr hh

/-- Uniform CRT energy controls the noise at the explicit pi-squared/Q scale. -/
theorem reflectionNoise_le_uniform (Q : ℕ) (hQ : 0 < Q) (heven : Even Q)
    (f : ℕ → ℝ) (C : ℝ) :
    reflectionNoise Q f C ≤ Real.pi^2 / Q * uniformReflectionVariance Q f C := by
  have h := FinitePairVariance.noise_le_four_mul_of_or Finset.univ
    (residueMass Q) (fun r => residueMass Q r.rev) (fun r => f r.val)
    C (Real.pi^2 / (2*(Q : ℝ)^2))
    (fun r _ => residueMass_pos Q hQ r)
    (fun r _ => residueMass_pos Q hQ r.rev)
    (fun r _ => residueMass_reflection_small Q hQ heven r)
  unfold reflectionNoise uniformReflectionVariance
  calc
    _ ≤ (4 * (Real.pi^2 / (2*(Q : ℝ)^2)) *
        ∑ r : Fin Q, (f r.val-C/2)^2) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by ring

theorem uniformReflectionVariance_div_le_error (Q : ℕ) (hQ : 0 < Q)
    (f : ℕ → ℝ) (a C : ℝ)
    (href : ∀ n, n < Q → f n + f (Q-1-n) = C) :
    uniformReflectionVariance Q f C / Q ≤ residueCenteredError Q f a := by
  have hr (r : Fin Q) : f r.val + f r.rev.val = C := by
    simpa [Fin.val_rev, Nat.sub_sub, Nat.add_comm] using href r.val r.isLt
  have h := FinitePairVariance.centered_energy_le_fullError Finset.univ
    (residueMass Q) (fun r => residueMass Q r.rev) (fun r => f r.val)
    (fun r => f r.rev.val) a C (1/(Q : ℝ)^2) (by positivity)
    (fun r _ => residueMass_ge_inv_sq Q hQ r)
    (fun r _ => residueMass_ge_inv_sq Q hQ r.rev) (fun r _ => hr r)
  rw [reflection_fullError] at h
  have he : uniformReflectionVariance Q f C / Q =
      (1/(Q : ℝ)^2) * ∑ r : Fin Q, (f r.val-C/2)^2 := by
    unfold uniformReflectionVariance
    ring
  rw [he]
  linarith

/-- Uniform comparison of the surrogate and the exact error. -/
theorem reflectionSurrogate_comparison (Q : ℕ) (hQ : 0 < Q) (heven : Even Q)
    (f : ℕ → ℝ) (a C : ℝ)
    (href : ∀ n, n < Q → f n + f (Q-1-n) = C) :
    residueCenteredError Q f a ≤ reflectionSurrogate Q f a C ∧
      reflectionSurrogate Q f a C ≤ (1+Real.pi^2)*residueCenteredError Q f a := by
  have hid := residueCenteredError_eq_reflection Q hQ f a C href
  have hn := reflectionNoise_le_uniform Q hQ heven f C
  have hn0 := reflectionNoise_nonneg Q hQ f C
  have hu := uniformReflectionVariance_div_le_error Q hQ f a C href
  have hmul := mul_le_mul_of_nonneg_left hu (sq_nonneg Real.pi)
  unfold reflectionSurrogate
  constructor
  · linarith
  · have he : Real.pi^2 / (Q : ℝ) * uniformReflectionVariance Q f C =
        Real.pi^2 * (uniformReflectionVariance Q f C / Q) := by ring
    rw [he]
    nlinarith

/-- The comparison specializes to the genuine infinite Pareto variance. -/
theorem paretoVariance_reflectionSurrogate_comparison (Q : ℕ) (hQ : 0 < Q)
    (heven : Even Q) (f : ℕ → ℝ) {B : ℝ} (hf : ∀ n, |f n| ≤ B)
    (hp : ∀ n, f (n+Q) = f n) (C : ℝ)
    (href : ∀ n, n < Q → f n + f (Q-1-n) = C) :
    paretoVariance f ≤ reflectionSurrogate Q f (paretoMean f) C ∧
      reflectionSurrogate Q f (paretoMean f) C ≤ (1+Real.pi^2)*paretoVariance f := by
  rw [periodic_paretoVariance_zero_residues Q hQ f hf hp]
  exact reflectionSurrogate_comparison Q hQ heven f _ C href

end
end RiemannResearch.RH.Pareto
