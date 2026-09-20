import RiemannResearch.RH.IntegerDPPHazards
import RiemannResearch.RH.ResidueClosureDensity

/-!
Source: user-provided DPP and CRT/orbit Markdown handoffs (2026-09-20).
The vacancy definition is supplied by the hazards module:
`vacancy n = 2 * TailCapacity.pointError n`.

No abstract vacancy relation is assumed: limitingVacancy is the actual
normalized squared distance of the first physical point to the residue closure.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

def limitingVacancy : ℝ :=
  2 * limitingError residueAtom (paretoPointHilbert 0)

theorem vacancy_tendsto : Tendsto vacancy atTop (𝓝 limitingVacancy) := by
  change Tendsto
    (fun n => 2 * walkError residueAtom id (paretoPointHilbert 0) n) atTop
    (𝓝 (2 * limitingError residueAtom (paretoPointHilbert 0)))
  exact (walkError_tendsto residueAtom id Function.surjective_id
    (paretoPointHilbert 0)).const_mul 2

theorem limitingVacancy_nonneg : 0 ≤ limitingVacancy := by
  unfold limitingVacancy limitingError
  positivity

theorem limitingVacancy_le_vacancy (n : ℕ) : limitingVacancy ≤ vacancy n := by
  have h := walkError_eq_limitingError_add residueAtom id (paretoPointHilbert 0) n
  have hs := sq_nonneg
    ‖closedSpace.starProjection (paretoPointHilbert 0) -
      (finiteSpace n).starProjection (paretoPointHilbert 0)‖
  unfold vacancy TailCapacity.pointError limitingVacancy
  nlinarith

theorem limitingVacancy_zero_iff_one_mem :
    limitingVacancy = 0 ↔ hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    have he : limitingError residueAtom (paretoPointHilbert 0) = 0 := by
      unfold limitingVacancy at h
      linarith
    exact firstPoint_mem_iff_one_mem.mp ((limitingError_eq_zero_iff _ _).mp he)
  · intro h
    have he := (limitingError_eq_zero_iff residueAtom (paretoPointHilbert 0)).mpr
      (firstPoint_mem_iff_one_mem.mpr h)
    simp [limitingVacancy, he]

theorem limitingVacancy_zero_iff_top :
    limitingVacancy = 0 ↔ closedSpace = ⊤ :=
  limitingVacancy_zero_iff_one_mem.trans closedSpace_eq_top_iff_one_mem.symm

theorem limitingVacancy_zero_iff_odd_carry :
    limitingVacancy = 0 ↔
      (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d →
        doublingCarryHilbert d (by omega) ∈ closedSpace) :=
  limitingVacancy_zero_iff_top.trans odd_carry_iff_closedSpace_eq_top.symm

theorem vacancy_tendsto_zero_iff_limitingVacancy_zero :
    Tendsto vacancy atTop (𝓝 0) ↔ limitingVacancy = 0 := by
  constructor
  · intro h
    exact tendsto_nhds_unique vacancy_tendsto h
  · intro h
    simpa only [h] using vacancy_tendsto

theorem vacancy_tendsto_zero_iff_one_mem :
    Tendsto vacancy atTop (𝓝 0) ↔ hilbertOne ∈ closedSpace :=
  vacancy_tendsto_zero_iff_limitingVacancy_zero.trans limitingVacancy_zero_iff_one_mem

theorem vacancy_tendsto_zero_iff_top :
    Tendsto vacancy atTop (𝓝 0) ↔ closedSpace = ⊤ :=
  vacancy_tendsto_zero_iff_limitingVacancy_zero.trans limitingVacancy_zero_iff_top

theorem odd_carry_iff_vacancy_tendsto_zero :
    (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d →
      doublingCarryHilbert d (by omega) ∈ closedSpace) ↔
      Tendsto vacancy atTop (𝓝 0) :=
  odd_carry_iff_closedSpace_eq_top.trans vacancy_tendsto_zero_iff_top.symm

theorem limitingVacancy_pos_of_not_RH (h : ¬ RiemannHypothesis) :
    0 < limitingVacancy := by
  have hn : limitingVacancy ≠ 0 := by
    intro he
    exact h (riemannHypothesis_of_vacancy_tendsto_zero
      (vacancy_tendsto_zero_iff_limitingVacancy_zero.mpr he))
  rcases lt_or_eq_of_le limitingVacancy_nonneg with hp | hz
  · exact hp
  · exact (hn hz.symm).elim

theorem all_projections_tendsto_self_of_odd_carry
    (h : ∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d →
      doublingCarryHilbert d (by omega) ∈ closedSpace)
    (f : ThresholdHilbert) :
    Tendsto (fun n => (finiteSpace n).starProjection f) atTop (𝓝 f) := by
  have ht := walkProjection_tendsto residueAtom id Function.surjective_id f
  have hS := odd_carry_iff_closedSpace_eq_top.mp h
  change Tendsto (fun n => (finiteSpace n).starProjection f) atTop
    (𝓝 (closedSpace.starProjection f)) at ht
  have hs : closedSpace.starProjection f = f :=
    Submodule.starProjection_eq_self_iff.mpr (by rw [hS]; trivial)
  simpa only [hs] using ht

end RiemannResearch.RH.Pareto.IntegerDPP
