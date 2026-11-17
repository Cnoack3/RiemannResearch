import RiemannResearch.RH.ExactHeadOccurrenceProjection
import RiemannResearch.Analysis.FiniteWeightedSpan
import RiemannResearch.RH.ParetoPeriodicRegrouping
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Certificates and uniqueness for the actual occurrence coefficients

Source: exact finite normal equations already present in
`ExactHeadOccurrenceProjection`. The squared excess is retained before
taking inequalities. Normality is a finite checkable certificate; the
subsequent arithmetic cofinal estimates are separate obligations.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteProfileEnergy
open ExactHeadAtomOptimizer

/-- The jump of a step synthesis recovers each permitted coefficient. -/
theorem fit_jump (P x n : ℕ) (c : ℕ → ℝ) (hn : n ∈ freePositions P x) :
    fit P x c n - fit P x c (n - 1) = c n := by
  classical
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  unfold fit
  rw [← Finset.sum_sub_distrib]
  have hs (m : ℕ) :
      c m * step m n - c m * step m (n - 1) = if m = n then c n else 0 := by
    by_cases he : m = n
    · subst m
      simp [step, show ¬ n ≤ n - 1 by omega]
    · have hh : m ≤ n ↔ m ≤ n - 1 := by omega
      simp [step, hh, he]
  simp_rw [hs]
  simp [hn]

/-- Every occurrence trial has an exact squared excess over the actual optimum. -/
theorem occurrence_trial_identity (P x : ℕ) (c : ℕ → ℝ) :
    energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (target P - fit P x c) =
      occurrenceEnergy P x +
        energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (fit P x (occurrenceCoefficients P x) - fit P x c) := by
  have heq : target P - fit P x c = occurrenceResidual P x +
      (fit P x (occurrenceCoefficients P x) - fit P x c) := by
    funext r
    simp [occurrenceResidual]
  have hz : pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (occurrenceResidual P x)
      (fit P x (occurrenceCoefficients P x) - fit P x c) = 0 := by
    change (∑ r ∈ Finset.Icc 1 (P - 1), progressionWeight P r *
      occurrenceResidual P x r *
        (fit P x (occurrenceCoefficients P x) r - fit P x c r)) = 0
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((occurrence_normal_fit P x _).trans
      (occurrence_normal_fit P x _).symm)
  rw [heq, energy_add_exact, hz, mul_zero, add_zero]
  rfl

theorem occurrenceEnergy_le_trial (P x : ℕ) (c : ℕ → ℝ) :
    occurrenceEnergy P x ≤
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (target P - fit P x c) := by
  rw [occurrence_trial_identity]
  exact le_add_of_nonneg_right
    (energy_nonneg _ _ _ (fun r hr => progressionWeight_nonneg P r))

/-- A trial normal against every allowed step is normal against every synthesis. -/
theorem trial_normal_fit (P x : ℕ) (c d : ℕ → ℝ)
    (hc : ∀ n ∈ freePositions P x,
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (target P - fit P x c) (step n) = 0) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (target P - fit P x c) (fit P x d) = 0 := by
  calc
    _ = ∑ n ∈ freePositions P x, d n *
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (target P - fit P x c) (step n) := by
      unfold pairing fit
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = 0 := Finset.sum_eq_zero (fun n hn => by rw [hc n hn, mul_zero])

/-- Finite normal equations certify the actual chosen fitted values. -/
theorem occurrence_fit_eq_of_normal (P x : ℕ) (hP : 0 < P) (c : ℕ → ℝ)
    (hc : ∀ n ∈ freePositions P x,
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (target P - fit P x c) (step n) = 0)
    (r : ℕ) (hr : r ∈ Finset.Icc 1 (P - 1)) :
    fit P x (occurrenceCoefficients P x) r = fit P x c r := by
  let d := fit P x (occurrenceCoefficients P x) - fit P x c
  have hd : energy (Finset.Icc 1 (P - 1)) (progressionWeight P) d = 0 := by
    have hnormal := trial_normal_fit P x c (occurrenceCoefficients P x) hc
    have hnormal' := trial_normal_fit P x c c hc
    have hactual := occurrence_normal_fit P x (occurrenceCoefficients P x)
    have hactual' := occurrence_normal_fit P x c
    have hid : energy (Finset.Icc 1 (P - 1)) (progressionWeight P) d =
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (target P - fit P x c) (fit P x (occurrenceCoefficients P x)) -
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (target P - fit P x c) (fit P x c) -
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (occurrenceResidual P x) (fit P x (occurrenceCoefficients P x)) +
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (occurrenceResidual P x) (fit P x c) := by
      unfold energy pairing
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [d, Pi.sub_apply, occurrenceResidual]
      ring
    rw [hid, hnormal, hnormal', hactual, hactual']
    ring
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (hi : i ∈ Finset.Icc 1 (P - 1)) =>
      mul_nonneg (progressionWeight_nonneg P i) (sq_nonneg (d i)))).mp hd r hr
  have hw := progressionWeight_pos P r hP (Finset.mem_Icc.mp hr).1
  have hs : d r ^ 2 = 0 := (mul_eq_zero.mp hzero).resolve_left hw.ne'
  have hz : d r = 0 := sq_eq_zero_iff.mp hs
  exact sub_eq_zero.mp hz

/-- Unlike unused coefficients outside the support, every free coefficient is unique. -/
theorem occurrenceCoefficients_eq_of_normal (P x : ℕ) (hP : 0 < P) (c : ℕ → ℝ)
    (hc : ∀ n ∈ freePositions P x,
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (target P - fit P x c) (step n) = 0)
    (n : ℕ) (hn : n ∈ freePositions P x) :
    occurrenceCoefficients P x n = c n := by
  have hnI := (Finset.mem_filter.mp hn).1
  have hnow := occurrence_fit_eq_of_normal P x hP c hc n hnI
  have hprev : fit P x (occurrenceCoefficients P x) (n - 1) = fit P x c (n - 1) := by
    by_cases hn1 : n = 1
    · subst n
      have hz (d : ℕ → ℝ) : fit P x d 0 = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        have hm1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
        simp [step, show ¬ m ≤ 0 by omega]
      simp only [Nat.sub_self, hz]
    · apply occurrence_fit_eq_of_normal P x hP c hc (n - 1)
      obtain ⟨h1,hP'⟩ := Finset.mem_Icc.mp hnI
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← fit_jump P x n (occurrenceCoefficients P x) hn,
    ← fit_jump P x n c hn, hnow, hprev]

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
