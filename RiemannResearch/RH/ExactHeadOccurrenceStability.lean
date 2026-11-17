import RiemannResearch.RH.ExactHeadOccurrenceCertificates
import Mathlib.Tactic.Linarith

/-!
# Exact cutoff comparisons and stability of occurrence coefficients

Source: the repository's occurrence normal equations and complete weighted
trial identity. Cutoff comparisons keep the period fixed. They assert no
monotonicity along the changing primorial family and no asymptotic provider.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteProfileEnergy
open ExactHeadAtomOptimizer

theorem freePositions_antitone (P : ℕ) : Antitone (freePositions P) := by
  intro x y hxy n hn
  obtain ⟨hnI, hny⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hnI, lt_of_le_of_lt hxy hny⟩

/-- A larger-cutoff synthesis is represented exactly in the smaller-cutoff dictionary. -/
theorem fit_restrict_cutoff (P x y : ℕ) (hxy : x ≤ y) (c : ℕ → ℝ) :
    fit P x (fun n => if n ∈ freePositions P y then c n else 0) = fit P y c := by
  classical
  funext r
  unfold fit
  calc
    _ = ∑ n ∈ freePositions P y,
        (if n ∈ freePositions P y then c n else 0) * step n r := by
      symm
      exact Finset.sum_subset (freePositions_antitone P hxy)
        (fun n hn hnot => by simp [hnot])
    _ = _ := Finset.sum_congr rfl (fun n hn => by simp [hn])

/-- Exact nested-projection identity at a fixed period. The squared displacement is retained. -/
theorem occurrenceEnergy_cutoff_identity (P x y : ℕ) (hxy : x ≤ y) :
    occurrenceEnergy P y = occurrenceEnergy P x +
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (fit P x (occurrenceCoefficients P x) - fit P y (occurrenceCoefficients P y)) := by
  have h := occurrence_trial_identity P x
    (fun n => if n ∈ freePositions P y then occurrenceCoefficients P y n else 0)
  rw [fit_restrict_cutoff P x y hxy] at h
  exact h

/-- Tightening the allowed jumps cannot decrease the actual minimum at a fixed period. -/
theorem occurrenceEnergy_mono_cutoff (P : ℕ) : Monotone (occurrenceEnergy P) := by
  intro x y hxy
  rw [occurrenceEnergy_cutoff_identity P x y hxy]
  exact le_add_of_nonneg_right
    (energy_nonneg _ _ _ (fun r hr => progressionWeight_nonneg P r))

theorem fit_zero_at_zero (P x : ℕ) (c : ℕ → ℝ) : fit P x c 0 = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hn1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  simp [step, show ¬ n ≤ 0 by omega]

/-- Each sample controls its fitted-value error in the complete weighted norm. -/
theorem occurrence_fit_error_sq_le (P x : ℕ) (c : ℕ → ℝ)
    (r : ℕ) (hr : r ∈ Finset.Icc 1 (P - 1)) :
    progressionWeight P r *
      (fit P x (occurrenceCoefficients P x) r - fit P x c r) ^ 2 ≤
        energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (target P - fit P x c) -
          occurrenceEnergy P x := by
  rw [occurrence_trial_identity, add_sub_cancel_left]
  exact Finset.single_le_sum
    (f := fun i => progressionWeight P i *
      (fit P x (occurrenceCoefficients P x) i - fit P x c i)^2)
    (fun i hi => mul_nonneg (progressionWeight_nonneg P i) (sq_nonneg _)) hr

/-- An energy certificate bounds every active coefficient; no matrix inverse is needed. -/
theorem occurrence_coefficient_error_sq_le (P x : ℕ) (hP : 0 < P)
    (c : ℕ → ℝ) (n : ℕ) (hn : n ∈ freePositions P x) :
    (occurrenceCoefficients P x n - c n) ^ 2 ≤
      2 * ((progressionWeight P n)⁻¹ + (progressionWeight P (n - 1))⁻¹) *
        (energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (target P - fit P x c) -
          occurrenceEnergy P x) := by
  let E := energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (target P - fit P x c) -
    occurrenceEnergy P x
  let d := fun r => fit P x (occurrenceCoefficients P x) r - fit P x c r
  have hnI := (Finset.mem_filter.mp hn).1
  have hnow : d n ^ 2 ≤ (progressionWeight P n)⁻¹ * E := by
    have hw := progressionWeight_pos P n hP (Finset.mem_Icc.mp hnI).1
    have hh := occurrence_fit_error_sq_le P x c n hnI
    calc
      d n ^ 2 ≤ E / progressionWeight P n :=
        (le_div_iff₀ hw).mpr (by simpa [d, E, mul_comm] using hh)
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  have hprev : d (n - 1) ^ 2 ≤ (progressionWeight P (n - 1))⁻¹ * E := by
    by_cases hn1 : n = 1
    · subst n
      have hE : 0 ≤ E := sub_nonneg.mpr (occurrenceEnergy_le_trial P x c)
      simp only [d, Nat.sub_self, fit_zero_at_zero, sub_self, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (inv_nonneg.mpr (progressionWeight_nonneg P 0)) hE
    · have hpI : n - 1 ∈ Finset.Icc 1 (P - 1) := by
        have := Finset.mem_Icc.mp hnI
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hw := progressionWeight_pos P (n-1) hP (Finset.mem_Icc.mp hpI).1
      have hh := occurrence_fit_error_sq_le P x c (n-1) hpI
      calc
        d (n-1) ^ 2 ≤ E / progressionWeight P (n-1) :=
          (le_div_iff₀ hw).mpr (by simpa [d, E, mul_comm] using hh)
        _ = _ := by rw [div_eq_mul_inv, mul_comm]
  have hj : occurrenceCoefficients P x n - c n = d n - d (n-1) := by
    dsimp [d]
    rw [← fit_jump P x n (occurrenceCoefficients P x) hn, ← fit_jump P x n c hn]
    ring
  rw [hj]
  change (d n - d (n-1))^2 ≤ 2 * _ * E
  nlinarith [sq_nonneg (d n + d (n-1))]

theorem fit_jump_of_not_free (P x n : ℕ) (c : ℕ → ℝ)
    (hn : n ∉ freePositions P x) :
    fit P x c n - fit P x c (n-1) = 0 := by
  unfold fit
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro m hm
  have hmn : m ≠ n := by intro h; subst m; exact hn hm
  have hiff : m ≤ n ↔ m ≤ n-1 := by omega
  simp [step, hiff]

/-- No energy cost is equivalent to no movement of the actual fit at any sample. -/
theorem occurrence_fit_eq_of_energy_eq (P x y : ℕ) (hP : 0 < P) (hxy : x ≤ y)
    (he : occurrenceEnergy P x = occurrenceEnergy P y)
    (r : ℕ) (hr : r ∈ Finset.Icc 1 (P - 1)) :
    fit P x (occurrenceCoefficients P x) r = fit P y (occurrenceCoefficients P y) r := by
  let d := fit P x (occurrenceCoefficients P x) - fit P y (occurrenceCoefficients P y)
  have hzero : energy (Finset.Icc 1 (P - 1)) (progressionWeight P) d = 0 := by
    have h := occurrenceEnergy_cutoff_identity P x y hxy
    change occurrenceEnergy P y = occurrenceEnergy P x +
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) d at h
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (hi : i ∈ Finset.Icc 1 (P - 1)) =>
      mul_nonneg (progressionWeight_nonneg P i) (sq_nonneg (d i)))).mp hzero r hr
  have hw := progressionWeight_pos P r hP (Finset.mem_Icc.mp hr).1
  have hd : d r = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hw.ne')
  exact sub_eq_zero.mp hd

/-- Exact arithmetic criterion for a plateau as the allowed occurrence dictionary shrinks. -/
theorem occurrenceEnergy_eq_iff_removed_zero (P x y : ℕ) (hP : 0 < P) (hxy : x ≤ y) :
    occurrenceEnergy P x = occurrenceEnergy P y ↔
      ∀ n ∈ freePositions P x, n ∉ freePositions P y → occurrenceCoefficients P x n = 0 := by
  constructor
  · intro he n hn hny
    have hnI := (Finset.mem_filter.mp hn).1
    have hnow := occurrence_fit_eq_of_energy_eq P x y hP hxy he n hnI
    have hprev : fit P x (occurrenceCoefficients P x) (n-1) =
        fit P y (occurrenceCoefficients P y) (n-1) := by
      by_cases hn1 : n = 1
      · subst n
        simp only [Nat.sub_self, fit_zero_at_zero]
      · apply occurrence_fit_eq_of_energy_eq P x y hP hxy he (n-1)
        have := Finset.mem_Icc.mp hnI
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [← fit_jump P x n (occurrenceCoefficients P x) hn, hnow, hprev]
    exact fit_jump_of_not_free P y n (occurrenceCoefficients P y) hny
  · intro hc
    have hf : fit P x (occurrenceCoefficients P x) =
        fit P y (occurrenceCoefficients P x) := by
      funext r
      symm
      exact Finset.sum_subset (freePositions_antitone P hxy)
        (fun n hn hny => by rw [hc n hn hny, zero_mul])
    have hy := occurrenceEnergy_le_trial P y (occurrenceCoefficients P x)
    rw [← hf] at hy
    exact le_antisymm (occurrenceEnergy_mono_cutoff P hxy) hy

/-- A strict energy increase occurs exactly when a removed actual coefficient is nonzero. -/
theorem occurrenceEnergy_lt_iff_removed_nonzero (P x y : ℕ) (hP : 0 < P) (hxy : x ≤ y) :
    occurrenceEnergy P x < occurrenceEnergy P y ↔
      ∃ n ∈ freePositions P x, n ∉ freePositions P y ∧ occurrenceCoefficients P x n ≠ 0 := by
  classical
  constructor
  · intro hlt
    by_contra hn
    have hz : ∀ n ∈ freePositions P x,
        n ∉ freePositions P y → occurrenceCoefficients P x n = 0 := by
      intro n hnx hny
      by_contra hc
      exact hn ⟨n,hnx,hny,hc⟩
    exact (ne_of_lt hlt) ((occurrenceEnergy_eq_iff_removed_zero P x y hP hxy).mpr hz)
  · rintro ⟨n,hnx,hny,hc⟩
    rcases lt_or_eq_of_le (occurrenceEnergy_mono_cutoff P hxy) with hlt | he
    · exact hlt
    · exact (hc ((occurrenceEnergy_eq_iff_removed_zero P x y hP hxy).mp he n hnx hny)).elim

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
