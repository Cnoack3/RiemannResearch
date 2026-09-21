import RiemannResearch.RH.ParetoFirstPointHeadObstruction
import RiemannResearch.RH.RHFalseEnergyConsequences
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# First-point head witnesses with small power-normalized full energy

Source: user-provided exact-head energy and Fredholm research targets,
21 September 2026 (research direction). The quantitative estimate is derived
from ParetoFirstPointHeadObstruction.

The first theorem quantifies the power obstruction uniformly over all exact
head vectors under not RH. The two RH endpoints are conditional research
reductions: existence of small-power witnesses, or subpower full energy,
remains Open. No RH-to-density input or new axiom is used.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open TailCapacity

/-- A single fixed positive power and coefficient obstruct every exact head
if RH is false. The lower bound retains the first-point energy. -/
theorem firstPoint_power_obstruction_of_not_RH
    (hRH : ¬ RiemannHypothesis) {a : ℝ} (ha : a ≠ 0) :
    ∃ p c : ℝ, 0 < p ∧ 0 < c ∧
      ∀ (N : ℕ) (f : ThresholdHilbert), 1 ≤ N → f ∈ closedSpace →
      (∀ k, 0 < k → k ≤ N →
        hilbertSequence f k = hilbertSequence (a • paretoPointHilbert 0) k) →
      a ^ 2 / 2 + c * ((N : ℝ) + 1) ^ p ≤ ‖f‖ ^ 2 := by
  obtain ⟨s, hz, hs, hs1⟩ := RiemannResearch.RH.exists_right_zero_of_not_RH hRH
  have hsne : s ≠ 1 := by intro he; simp [he] at hs1
  refine ⟨2 * s.re - 1, a ^ 2 * IntegerDPP.mellinVacancyFloor s / 2,
    by linarith, ?_, ?_⟩
  · exact div_pos (mul_pos (sq_pos_of_ne_zero ha)
      (IntegerDPP.mellinVacancyFloor_pos s hs)) (by norm_num)
  · intro N f hN hf hh
    have h := firstPoint_matching_head_energy_lower_bound s hs hsne hz hf hN hh
    rw [IntegerDPP.mellinVacancyFloor_eq s hs]
    convert h using 1 <;> ring

/-- Conditional research reduction. Different witnesses may be used for
each pair of positive constants; no compatibility is required.
Open obligation: construct these actual small-energy legal witnesses. -/
theorem riemannHypothesis_of_firstPoint_head_small_power_witnesses
    {a : ℝ} (ha : a ≠ 0)
    (hwitness : ∀ p : ℝ, 0 < p → ∀ c : ℝ, 0 < c →
      ∃ (N : ℕ) (f : ThresholdHilbert), 1 ≤ N ∧ f ∈ closedSpace ∧
        (∀ k, 0 < k → k ≤ N →
          hilbertSequence f k = hilbertSequence (a • paretoPointHilbert 0) k) ∧
        ‖f‖ ^ 2 < c * ((N : ℝ) + 1) ^ p) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨p, c, hp, hc, hbound⟩ := firstPoint_power_obstruction_of_not_RH hRH ha
  obtain ⟨N, f, hN, hf, hh, he⟩ := hwitness p hp c hc
  have hb := hbound N f hN hf hh
  nlinarith [sq_nonneg a]

/-- Conditional research reduction for first-point, rather than constant,
heads. Open obligation: subpower control of the complete squared norms. -/
theorem riemannHypothesis_of_firstPoint_head_subpower
    {a : ℝ} (ha : a ≠ 0) (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N →
      hilbertSequence (F N) k = hilbertSequence (a • paretoPointHilbert 0) k)
    (hsubpower : ∀ p : ℝ, 0 < p →
      Tendsto (fun N => ‖F N‖ ^ 2 / ((N : ℝ) + 1) ^ p) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_firstPoint_head_small_power_witnesses ha
  intro p hp c hc
  obtain ⟨N, hN, he⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and ((hsubpower p hp).eventually_lt_const hc)).exists
  refine ⟨N, F N, hN, hlegal N, hhead N, ?_⟩
  exact (div_lt_iff₀ (Real.rpow_pos_of_pos (by positivity) p)).mp he

end RiemannResearch.RH.Pareto.CoefficientStabilization
