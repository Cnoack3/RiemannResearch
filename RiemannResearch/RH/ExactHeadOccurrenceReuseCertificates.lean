import RiemannResearch.RH.ExactHeadOccurrenceCoefficientIntervals
import RiemannResearch.RH.ExactHeadOccurrenceStability
import RiemannResearch.RH.ExactHeadOccurrenceStageFive
import RiemannResearch.RH.ExactHeadAtomStageFive
import RiemannResearch.RH.ExactHeadGcdAtoms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact criteria and finite certificates for atom-reuse energy

Source: the actual occurrence/atom projection identity, coefficient stability,
and independently kernel-replayed cutoff-five energy intervals.
The cost vanishes exactly for fiberwise constant occurrence coefficients.
The positive cutoff-five cost is a finite obstruction, not an RH obstruction.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.ExactHeadGcdAtoms
open ExactHeadAtomOptimizer

/-- The complete actual atom fit is an occurrence trial with precisely the reuse excess. -/
theorem actual_atom_occurrence_trial_identity (P x : ℕ) :
    energy (Finset.Icc 1 (P-1)) (progressionWeight P)
      (target P - fit P x (fun n => atomNormalCoefficients P x (Nat.gcd n P))) =
        occurrenceEnergy P x + reuseEnergy P x := by
  rw [← atomEnergy_eq_occurrence_add_reuse]
  apply Finset.sum_congr rfl
  intro r hr
  have h := lift_synthesis P x (atomNormalCoefficients P x) r
    (by have := Finset.mem_Icc.mp hr; omega)
  simp only [Pi.sub_apply, h, atomResidual, synthesis]

/-- Quantitative control of the difference between occurrence and shared atom coefficients. -/
theorem occurrence_atom_coefficient_error_sq_le (P x : ℕ) (hP : 0 < P)
    (n : ℕ) (hn : n ∈ freePositions P x) :
    (occurrenceCoefficients P x n - atomNormalCoefficients P x (Nat.gcd n P))^2 ≤
      2 * ((progressionWeight P n)⁻¹ + (progressionWeight P (n-1))⁻¹) * reuseEnergy P x := by
  have h := occurrence_coefficient_error_sq_le P x hP
    (fun n => atomNormalCoefficients P x (Nat.gcd n P)) n hn
  rw [actual_atom_occurrence_trial_identity, add_sub_cancel_left] at h
  exact h

/-- Reuse costs zero exactly when occurrence coefficients are constant on every gcd fiber. -/
theorem reuseEnergy_eq_zero_iff_fiberwise (P x : ℕ) (hP : 0 < P) :
    reuseEnergy P x = 0 ↔
      ∀ n ∈ freePositions P x, ∀ m ∈ freePositions P x,
        Nat.gcd n P = Nat.gcd m P →
          occurrenceCoefficients P x n = occurrenceCoefficients P x m := by
  classical
  constructor
  · intro hz
    have he (n : ℕ) (hn : n ∈ freePositions P x) :
        occurrenceCoefficients P x n = atomNormalCoefficients P x (Nat.gcd n P) := by
      have h := occurrence_atom_coefficient_error_sq_le P x hP n hn
      rw [hz, mul_zero] at h
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _)))
    intro n hn m hm hnm
    rw [he n hn, he m hm, hnm]
  · intro hfiber
    let u : ℕ → ℝ := fun d =>
      if hd : ∃ n, n ∈ freePositions P x ∧ Nat.gcd n P = d then
        occurrenceCoefficients P x (Classical.choose hd) else 0
    have hu (n : ℕ) (hn : n ∈ freePositions P x) :
        occurrenceCoefficients P x n = u (Nat.gcd n P) := by
      have hex : ∃ m, m ∈ freePositions P x ∧ Nat.gcd m P = Nat.gcd n P := ⟨n,hn,rfl⟩
      dsimp [u]
      rw [dif_pos hex]
      exact hfiber n hn _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2.symm
    have hzero : energy (Finset.Icc 1 (P-1)) (progressionWeight P)
        (fit P x (occurrenceCoefficients P x) - synthesis P (upperDivisors P x) u) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hf : fit P x (occurrenceCoefficients P x) r =
          fit P x (fun n => u (Nat.gcd n P)) r :=
        Finset.sum_congr rfl (fun n hn => by rw [hu n hn])
      rw [Pi.sub_apply, hf, lift_synthesis P x u r (by have := Finset.mem_Icc.mp hr; omega),
        sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact le_antisymm ((reuseEnergy_le_trial P x u).trans_eq hzero) (reuseEnergy_nonneg P x)

theorem reuseEnergy_pos_of_fiber_discrepancy (P x : ℕ) (hP : 0 < P)
    (n m : ℕ) (hn : n ∈ freePositions P x) (hm : m ∈ freePositions P x)
    (hg : Nat.gcd n P = Nat.gcd m P)
    (hc : occurrenceCoefficients P x n ≠ occurrenceCoefficients P x m) :
    0 < reuseEnergy P x := by
  by_contra h
  have hz : reuseEnergy P x = 0 :=
    le_antisymm (le_of_not_gt h) (reuseEnergy_nonneg P x)
  exact hc ((reuseEnergy_eq_zero_iff_fiberwise P x hP).mp hz n hn m hm hg)


/-- Strictly positive reuse is equivalent to a finite rational separation certificate.
The certificate uses one common finite prefix depth for two actual gcd-fiber positions. -/
theorem reuseEnergy_pos_iff_rational_separation (P x : ℕ) (hP : 0 < P) :
    0 < reuseEnergy P x ↔
      ∃ K : ℕ, 1 ≤ K ∧ ∃ i < (freePositions P x).card, ∃ j < (freePositions P x).card,
        Nat.gcd (occurrenceBoundary P x i) P = Nat.gcd (occurrenceBoundary P x j) P ∧
        (rationalOccurrenceCoefficientInterval P x K i).hi <
          (rationalOccurrenceCoefficientInterval P x K j).lo := by
  classical
  constructor
  · intro hpos
    by_contra hnone
    have hconst : ∀ n ∈ freePositions P x, ∀ m ∈ freePositions P x,
        Nat.gcd n P = Nat.gcd m P →
          occurrenceCoefficients P x n = occurrenceCoefficients P x m := by
      intro n hn m hm hg
      obtain ⟨i,hi,rfl⟩ := exists_occurrenceBoundary P x n hn
      obtain ⟨j,hj,rfl⟩ := exists_occurrenceBoundary P x m hm
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hs := rationalOccurrenceCoefficientInterval_eventually_separated P x i j hP hi hj hlt
        obtain ⟨K,hK,hsep⟩ := ((Filter.eventually_ge_atTop 1).and hs).exists
        exact hnone ⟨K,hK,i,hi,j,hj,hg,hsep⟩
      · have hs := rationalOccurrenceCoefficientInterval_eventually_separated P x j i hP hj hi hlt
        obtain ⟨K,hK,hsep⟩ := ((Filter.eventually_ge_atTop 1).and hs).exists
        exact hnone ⟨K,hK,j,hj,i,hi,hg.symm,hsep⟩
    have hz := (reuseEnergy_eq_zero_iff_fiberwise P x hP).mpr hconst
    linarith
  · rintro ⟨K,hK,i,hi,j,hj,hg,hsep⟩
    have hI := rationalOccurrenceCoefficientInterval_contains P x K i hP hK hi
    have hJ := rationalOccurrenceCoefficientInterval_contains P x K j hP hK hj
    have hsepR := (Rat.cast_lt (K := ℝ)).2 hsep
    have hc := hI.2.trans_lt (hsepR.trans_le hJ.1)
    exact reuseEnergy_pos_of_fiber_discrepancy P x hP
      (occurrenceBoundary P x i) (occurrenceBoundary P x j)
      (occurrenceBoundary_mem P x i hi) (occurrenceBoundary_mem P x j hj) hg (ne_of_lt hc)

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection

namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceStageFive
open ExactHeadOccurrenceProjection ExactHeadAtomOptimizer

/-- Two actual coefficients in the same gcd-six fiber are quantitatively separated. -/
theorem gcd_six_coefficients_separated :
    (64 / 125 : ℝ) ≤ occurrenceCoefficients 30 5 12 - occurrenceCoefficients 30 5 6 := by
  have h6 := (coefficients_five_interval 0 (by norm_num)).2
  have h12 := (coefficients_five_interval 2 (by norm_num)).1
  norm_num [boundary, meanLower, meanUpper] at h6 h12
  linarith

/-- A complete finite certificate for the positive cost of reusing atom coefficients. -/
theorem reuse_energy_five_interval :
    (363 / 100000 : ℝ) ≤ reuseEnergy 30 5 ∧ reuseEnergy 30 5 ≤ (39 / 10000 : ℝ) := by
  have ha := ExactHeadAtomStageFive.primorial_five_energy_interval
  have hP : MobiusHeadGreen.greenPeriod 5 = 30 := by decide
  rw [hP] at ha
  have ho := occurrence_energy_five_interval
  have he := atomEnergy_eq_occurrence_add_reuse 30 5
  constructor <;> linarith [ha.1,ha.2,ho.1,ho.2]

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceStageFive
