import RiemannResearch.RH.FirstCoordinateTailGap
import RiemannResearch.RH.IntegerDPPAllSiteObstruction

/-!
# Explicit signed tail barriers from one off-line zero

Source: user-requested RH proof/obstruction audit, 2026-09-21, assembled from
the existing exact Mellin vacancy and signed tail-gap theorems. All finite
Gram expressions retain their full signed mixed terms.

The positive barrier is conditional on an actual zeta zero, or on failure
of Mathlib RH in the existence theorem. No such zero is constructed.
The small-tail RH criterion has an explicit unresolved arithmetic input.
No RH-to-density provider is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.IntegerDPP

/-- The explicit upper bound supplied by a single right-half-plane zero. -/
def mellinTailCapacityBound (s : ℂ) : ℝ := 2 / mellinVacancyFloor s - 2

theorem tailCapacity_le_mellin_bound
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (n : ℕ) :
    tailCapacity n ≤ mellinTailCapacityBound s := by
  have h := capacity_bound_of_zeta_zero s hs hs1 hz n
  unfold mellinTailCapacityBound
  linarith

theorem mellinTailCapacityBound_pos
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : 0 < mellinTailCapacityBound s :=
  (tailCapacity_pos 1 (by omega)).trans_le (tailCapacity_le_mellin_bound s hs hs1 hz 1)

theorem firstCoordinateTailGap_ge_mellin_bound
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    1 / mellinTailCapacityBound s ≤ firstCoordinateTailGap := by
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨n, rfl⟩
  exact one_div_le_one_div_of_le (tailCapacity_pos (n + 1) (by omega))
    (tailCapacity_le_mellin_bound s hs hs1 hz (n + 1))

/-- Every signed finite trial obeys the same strictly positive barrier. -/
theorem signed_tail_barrier_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (n : ℕ) (c : Fin n → ℝ) :
    (1 / mellinTailCapacityBound s) * (∑ i, c i * reciprocalSource n i) ^ 2 ≤
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2 :=
  (mul_le_mul_of_nonneg_right (firstCoordinateTailGap_ge_mellin_bound s hs hs1 hz)
    (sq_nonneg _)).trans (firstCoordinateTailGap_controls_all n c)

/-- A finite signed Gram computation above this threshold excludes this zero. -/
theorem zeta_ne_zero_of_capacity_exceeds_mellin_bound
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (n : ℕ) (h : mellinTailCapacityBound s < tailCapacity n) : riemannZeta s ≠ 0 := by
  intro hz
  exact (not_lt_of_ge (tailCapacity_le_mellin_bound s hs hs1 hz n)) h

/-- One zero provides an explicit positive barrier simultaneously for every
dictionary size and every signed coefficient family. -/
theorem not_RH_common_signed_tail_barrier (hRH : ¬ RiemannHypothesis) :
    ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 ∧
      0 < mellinTailCapacityBound s ∧
      (∀ n, tailCapacity n ≤ mellinTailCapacityBound s) ∧
      1 / mellinTailCapacityBound s ≤ firstCoordinateTailGap ∧
      (∀ (n : ℕ) (c : Fin n → ℝ),
        (1 / mellinTailCapacityBound s) * (∑ i, c i * reciprocalSource n i) ^ 2 ≤
          ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2) := by
  obtain ⟨s, ⟨hs, h1, hz⟩, _⟩ := exists_common_site_vacancy_floor_of_not_RH hRH
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at h1
  exact ⟨s, hs, h1, hz, mellinTailCapacityBound_pos s hs hs1 hz,
    tailCapacity_le_mellin_bound s hs hs1 hz,
    firstCoordinateTailGap_ge_mellin_bound s hs hs1 hz,
    signed_tail_barrier_of_zeta_zero s hs hs1 hz⟩

/-- CONDITIONAL RESEARCH REDUCTION: existence of these arbitrarily small
full signed tail trials is the unresolved arithmetic input. -/
theorem riemannHypothesis_of_arbitrarily_small_signed_tails
    (h : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℝ),
      (∑ i, c i * reciprocalSource n i) = 1 ∧
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2 < ε) :
    RiemannHypothesis := by
  by_contra hRH
  have hg := not_RH_firstCoordinateTailGap_pos hRH
  obtain ⟨n, c, hc, he⟩ := h firstCoordinateTailGap hg
  exact (not_lt_of_ge (firstCoordinateTailGap_le_normalized_trial n c hc)) he

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
