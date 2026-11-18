import RiemannResearch.RH.QCRTCarryGoodPrimes
import RiemannResearch.RH.QCRTCarrySourceBudget
import RiemannResearch.Analysis.LogarithmicWeights
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The full one-divisor budget from prime threshold sets

The finite weighted layer-cake identity is the positive-function formula of
Lieb and Loss, *Analysis*, 2nd ed., §1.13, applied to the function
`p ↦ p * primeScore p` and reciprocal mass on the primes.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace RiemannResearch.RH.QCRTCarryPrimeLevels

open QCRTCarryGoodPrimes QCRTCarrySourceBudget
open RiemannResearch.Analysis.LogarithmicWeights

private theorem score_zero_of_ineligible (p : ℕ) (h : ¬ (p.Prime ∧ 3 ≤ p)) :
    primeScore p = 0 := by
  by_cases h4 : 4 ≤ p
  · have hn : ¬ p.Prime := fun hp => h ⟨hp, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 4 := ⟨p - 4, by omega⟩
    rw [primeScore_add_four]
    obtain ⟨s, _, hs⟩ := bestBudget_attained n
    rw [← hs, selectedBudget, if_neg hn]
  · have h3 : p ≠ 3 := by
      rintro rfl
      exact h ⟨by decide, by decide⟩
    simp [primeScore, h3, h4]

private def levelRectangle (p : ℕ) : ℝ → ℝ :=
  (Set.Ioc 0 ((p : ℝ) * primeScore p)).indicator (fun _ => 1 / (p : ℝ))

private theorem levelRectangle_eq (p : ℕ) (t : ℝ) :
    levelRectangle p t = if 0 < t then reciprocalOn (goodPrimes t) p else 0 := by
  classical
  by_cases ht : 0 < t
  · rw [if_pos ht]
    by_cases h : p.Prime ∧ 3 ≤ p
    · have hp : (0 : ℝ) < p := Nat.cast_pos.mpr h.1.pos
      have he : t ≤ (p : ℝ) * primeScore p ↔ t / (p : ℝ) ≤ primeScore p := by
        rw [div_le_iff₀ hp, mul_comm (primeScore p)]
      simp [levelRectangle, reciprocalOn, goodPrimes, Set.indicator_apply,
        Set.mem_Ioc, ht, h.1, h.2, he]
    · have hg : p ∉ goodPrimes t := fun hp => h ⟨hp.1, hp.2.1⟩
      simp [levelRectangle, score_zero_of_ineligible p h, reciprocalOn_notMem hg]
  · have hmem : t ∉ Set.Ioc 0 ((p : ℝ) * primeScore p) := fun h => ht h.1
    simp [levelRectangle, hmem, ht]

private theorem levelRectangle_integrable (p : ℕ) : Integrable (levelRectangle p) :=
  (continuous_const : Continuous (fun _ : ℝ => 1 / (p : ℝ))).integrableOn_Ioc.integrable_indicator
    measurableSet_Ioc

private theorem integral_levelRectangle (p : ℕ) : (∫ t : ℝ, levelRectangle p t) = primeScore p := by
  have hn := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (primeScore_nonneg p)
  rw [levelRectangle, integral_indicator measurableSet_Ioc, setIntegral_const,
    Real.volume_real_Ioc, sub_zero, max_eq_left hn, smul_eq_mul]
  by_cases hp : p = 0
  · subst p
    norm_num [primeScore]
  · field_simp [Nat.cast_ne_zero.mpr hp]

/-- Integrating reciprocal mass across all positive thresholds recovers the
entire finite score. Each prime contributes a rectangle of width `p * b_p`
and height `1 / p`. -/
theorem prime_level_integral (N : ℕ) :
    (∫ t in Set.Ioi (0 : ℝ), prefixMass (reciprocalOn (goodPrimes t)) N) =
      prefixMass primeScore N := by
  classical
  rw [← integral_indicator measurableSet_Ioi]
  have he : (Set.Ioi (0 : ℝ)).indicator
      (fun t => prefixMass (reciprocalOn (goodPrimes t)) N) =
      (fun t => ∑ p ∈ Finset.range N, levelRectangle p t) := by
    funext t
    by_cases ht : 0 < t <;>
      simp [Set.mem_Ioi, prefixMass, levelRectangle_eq, ht]
  rw [he, integral_finsetSum _ (fun p _ => levelRectangle_integrable p)]
  exact Finset.sum_congr rfl (fun p _ => integral_levelRectangle p)

/-- Conditional research reduction retaining every threshold and the full singleton score. -/
theorem riemannHypothesis_of_prime_level_integrals
    (h : Tendsto (fun N => ∫ t in Set.Ioi (0 : ℝ), prefixMass (reciprocalOn (goodPrimes t)) N)
      atTop atTop) : RiemannHypothesis := by
  simp only [prime_level_integral] at h
  by_contra hn
  exact (summable_iff_not_tendsto_nat_atTop_of_nonneg primeScore_nonneg).mp
    (summable_primeScore_of_not_RH hn) h

end RiemannResearch.RH.QCRTCarryPrimeLevels
