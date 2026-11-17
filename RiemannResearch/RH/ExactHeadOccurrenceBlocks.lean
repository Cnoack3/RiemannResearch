import RiemannResearch.RH.ExactHeadOccurrenceProjection
import RiemannResearch.Analysis.FiniteWeightedVariance
import RiemannResearch.RH.ParetoPeriodicRegrouping
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Exact interval formulas for the actual occurrence optimizer

Source: independently assembled from the repository's actual normal equations
and finite weighted variance identities. This supplies the finite block
calculation required by the occurrence-compression agenda in the user's
CRT memorandum. It does not assume a smooth-gap or asymptotic bound.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedVariance
open RiemannResearch.RH.ExactHeadGcdAtoms
open ExactHeadAtomOptimizer

/-- A half-open interval is the difference of its two suffix steps. -/
theorem step_sub_eq_interval (a b r : ℕ) (hab : a ≤ b) :
    step a r - step b r = if r ∈ Finset.Ico a b then 1 else 0 := by
  simp only [step, Finset.mem_Ico]
  split_ifs <;> norm_num <;> omega

/-- The terminal endpoint is automatically normal: its step vanishes. -/
theorem occurrence_normal_endpoint (P x b : ℕ)
    (hb : b ∈ freePositions P x ∨ b = P) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (occurrenceResidual P x) (step b) = 0 := by
  rcases hb with hb | hb
  · exact occurrence_normal_step P x b hb
  · subst b
    apply Finset.sum_eq_zero
    intro r hr
    have hrP : ¬ P ≤ r := by
      have := Finset.mem_Icc.mp hr
      omega
    simp [step, hrP]

/-- Difference of two normal suffix equations; no interval terms are discarded. -/
theorem occurrence_block_sum_zero (P x a b : ℕ)
    (ha : a ∈ freePositions P x) (hab : a ≤ b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P) :
    (∑ r ∈ Finset.Ico a b, progressionWeight P r * occurrenceResidual P x r) = 0 := by
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  have he : pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (occurrenceResidual P x) (step a - step b) =
      ∑ r ∈ Finset.Ico a b, progressionWeight P r * occurrenceResidual P x r := by
    unfold pairing
    simp only [Pi.sub_apply, step_sub_eq_interval a b _ hab, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [← he]
  simp only [pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr ((occurrence_normal_step P x a ha).trans
    (occurrence_normal_endpoint P x b hb).symm)

/-- Between consecutive permitted jumps, every occurrence fit is constant. -/
theorem fit_constant_on_gap (P x a b : ℕ) (c : ℕ → ℝ)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False)
    (r : ℕ) (hr : r ∈ Finset.Ico a b) :
    fit P x c r = fit P x c a := by
  apply Finset.sum_congr rfl
  intro n hn
  have hiff : n ≤ r ↔ n ≤ a := by
    obtain ⟨har,hrb⟩ := Finset.mem_Ico.mp hr
    constructor
    · intro hnr
      by_contra hna
      exact hgap n hn (by omega) (by omega)
    · exact fun hna => hna.trans har
  simp only [step, hiff]

/-- Complete progression mass of a nonempty positive block is positive. -/
theorem occurrence_block_mass_pos (P a b : ℕ)
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ P) :
    0 < FiniteWeightedVariance.mass (Finset.Ico a b) (progressionWeight P) := by
  apply Finset.sum_pos
  · intro r hr
    exact progressionWeight_pos P r (by omega) (by have := Finset.mem_Ico.mp hr; omega)
  · exact ⟨a, Finset.mem_Ico.mpr ⟨le_rfl,hab⟩⟩

/-- The actual chosen normal fit equals the explicit weighted target mean. -/
theorem occurrence_fit_eq_block_mean (P x a b : ℕ)
    (ha : a ∈ freePositions P x) (hab : a < b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False) :
    fit P x (occurrenceCoefficients P x) a =
      mean (Finset.Ico a b) (progressionWeight P) (target P) := by
  have hz := occurrence_block_sum_zero P x a b ha hab.le hbP hb
  have he : (∑ r ∈ Finset.Ico a b, progressionWeight P r * occurrenceResidual P x r) =
      (∑ r ∈ Finset.Ico a b, progressionWeight P r * target P r) -
        FiniteWeightedVariance.mass (Finset.Ico a b) (progressionWeight P) *
          fit P x (occurrenceCoefficients P x) a := by
    simp only [occurrenceResidual]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [FiniteWeightedVariance.mass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [fit_constant_on_gap P x a b _ hgap r hr]
  rw [he] at hz
  have hm := occurrence_block_mass_pos P a b
    (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1 hab hbP
  unfold mean
  apply (eq_div_iff hm.ne').mpr
  nlinarith

/-- Actual block error is exactly a weighted variance, without a model replacement. -/
theorem occurrence_block_energy_eq_variance (P x a b : ℕ)
    (ha : a ∈ freePositions P x) (hab : a < b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False) :
    energy (Finset.Ico a b) (progressionWeight P) (occurrenceResidual P x) =
      variance (Finset.Ico a b) (progressionWeight P) (target P) := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [occurrenceResidual, fit_constant_on_gap P x a b _ hgap r hr,
    occurrence_fit_eq_block_mean P x a b ha hab hbP hb hgap]

/-- The exact nonnegative excess of any constant trial on a free block. -/
theorem occurrence_block_trial_identity (P x a b : ℕ)
    (ha : a ∈ freePositions P x) (hab : a < b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False) (z : ℝ) :
    (∑ r ∈ Finset.Ico a b, progressionWeight P r * (target P r - z) ^ 2) =
      energy (Finset.Ico a b) (progressionWeight P) (occurrenceResidual P x) +
        FiniteWeightedVariance.mass (Finset.Ico a b) (progressionWeight P) *
          (fit P x (occurrenceCoefficients P x) a - z) ^ 2 := by
  rw [occurrence_block_energy_eq_variance P x a b ha hab hbP hb hgap,
    occurrence_fit_eq_block_mean P x a b ha hab hbP hb hgap]
  exact translation_energy (Finset.Ico a b) (progressionWeight P) (target P) (-z)
    (occurrence_block_mass_pos P a b
      (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1 hab hbP).ne'

/-- Complete pairwise formula; all signed target differences remain in the square. -/
theorem occurrence_block_pairwise_identity (P x a b : ℕ)
    (ha : a ∈ freePositions P x) (hab : a < b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False) :
    (∑ r ∈ Finset.Ico a b, ∑ s ∈ Finset.Ico a b,
      progressionWeight P r * progressionWeight P s *
        (target P r - target P s) ^ 2) =
      2 * FiniteWeightedVariance.mass (Finset.Ico a b) (progressionWeight P) *
        energy (Finset.Ico a b) (progressionWeight P) (occurrenceResidual P x) := by
  rw [occurrence_block_energy_eq_variance P x a b ha hab hbP hb hgap]
  exact pairwise_identity _ _ _
    (occurrence_block_mass_pos P a b
      (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1 hab hbP).ne'

/-- The target is monotone because it is a cumulative count of coprime returns. -/
theorem occurrence_target_mono (P : ℕ) : Monotone (target P) := by
  intro a b hab
  apply sub_le_sub_right
  unfold atom
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hab) (fun n hn hnot => by split_ifs <;> norm_num)

/-- The actual target oscillation gives a quarter-range variance bound. -/
theorem occurrence_block_energy_le_oscillation (P x a b : ℕ)
    (ha : a ∈ freePositions P x) (hab : a < b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False) :
    energy (Finset.Ico a b) (progressionWeight P) (occurrenceResidual P x) ≤
      FiniteWeightedVariance.mass (Finset.Ico a b) (progressionWeight P) *
        (target P (b - 1) - target P a) ^ 2 / 4 := by
  rw [occurrence_block_energy_eq_variance P x a b ha hab hbP hb hgap]
  apply variance_le_of_bounds
    (Finset.Ico a b) (progressionWeight P) (target P)
    (fun r hr => progressionWeight_nonneg P r)
    (occurrence_block_mass_pos P a b
      (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1 hab hbP).ne'
  · intro r hr
    exact occurrence_target_mono P (Finset.mem_Ico.mp hr).1
  · intro r hr
    exact occurrence_target_mono P (by have := Finset.mem_Ico.mp hr; omega)

/-- A gap on which the coprime count is constant contributes exactly zero. -/
theorem occurrence_block_energy_zero_of_constant_target (P x a b : ℕ)
    (ha : a ∈ freePositions P x) (hab : a < b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False)
    (hc : target P (b - 1) = target P a) :
    energy (Finset.Ico a b) (progressionWeight P) (occurrenceResidual P x) = 0 := by
  have h := occurrence_block_energy_le_oscillation P x a b ha hab hbP hb hgap
  rw [hc, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div] at h
  exact le_antisymm h (energy_nonneg _ _ _ (fun r hr => progressionWeight_nonneg P r))

/-- Before the first free occurrence, the fit is fixed at zero, not at a free mean. -/
theorem occurrence_fit_zero_before_first (P x r : ℕ)
    (hfirst : ∀ n ∈ freePositions P x, r < n) :
    fit P x (occurrenceCoefficients P x) r = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  simp [step, not_le.mpr (hfirst n hn)]

/-- The initial constrained block retains the full target square. -/
theorem occurrence_initial_energy (P x a : ℕ)
    (hfirst : ∀ n ∈ freePositions P x, a ≤ n) :
    energy (Finset.Ico 1 a) (progressionWeight P) (occurrenceResidual P x) =
      energy (Finset.Ico 1 a) (progressionWeight P) (target P) := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [occurrenceResidual, occurrence_fit_zero_before_first P x r
    (fun n hn => (Finset.mem_Ico.mp hr).2.trans_le (hfirst n hn)), sub_zero]

/-- Any two distinct residues certify a lower bound for the actual block variance. -/
theorem occurrence_block_pair_lower (P x a b r s : ℕ)
    (ha : a ∈ freePositions P x) (hab : a < b) (hbP : b ≤ P)
    (hb : b ∈ freePositions P x ∨ b = P)
    (hgap : ∀ n ∈ freePositions P x, a < n → n < b → False)
    (hr : r ∈ Finset.Ico a b) (hs : s ∈ Finset.Ico a b) (hrs : r ≠ s) :
    progressionWeight P r * progressionWeight P s * (target P r - target P s) ^ 2 /
        (progressionWeight P r + progressionWeight P s) ≤
      energy (Finset.Ico a b) (progressionWeight P) (occurrenceResidual P x) := by
  rw [occurrence_block_energy_eq_variance P x a b ha hab hbP hb hgap]
  have ha1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
  have hw := progressionWeight_pos P r (by omega)
    (by have := Finset.mem_Ico.mp hr; omega)
  apply pair_lower _ _ _ r s hr hs hrs (fun n hn => progressionWeight_nonneg P n)
  exact add_pos_of_pos_of_nonneg hw (progressionWeight_nonneg P s)

/-- The complete total error retains every nonnegative block contribution. -/
theorem occurrence_block_energy_le_total (P x a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ P) :
    energy (Finset.Ico a b) (progressionWeight P) (occurrenceResidual P x) ≤
      occurrenceEnergy P x := by
  unfold occurrenceEnergy energy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    have := Finset.mem_Ico.mp hr
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro r hr hnot
    exact mul_nonneg (progressionWeight_nonneg P r) (sq_nonneg _)

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
