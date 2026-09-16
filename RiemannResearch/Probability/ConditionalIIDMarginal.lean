/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Probability.ConditionalIIDUniformMoments
import Mathlib.Probability.IdentDistrib

/-! The exact Pareto marginal and identical unconditional row distributions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID
open RH.ArithmeticCumulative

/-- The marginal event law is obtained from the constructed common probability measure. -/
theorem coordinate_event_integral (i : ℕ) (B : Set ℕ) :
    probability (coordinate i ⁻¹' B) = ∫⁻ k, uniformLaw k B ∂latentLaw := by
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  rw [probability, Measure.compProd_apply (hB.preimage (coordinate_measurable i))]
  apply lintegral_congr
  intro k
  change pathLaw k ((fun x : Path => x i) ⁻¹' B) = uniformLaw k B
  rw [← Measure.infinitePi_map_eval (fun _ : ℕ => uniformLaw k) i,
    Measure.map_apply (measurable_pi_apply i) hB]
  rfl

/-- All coordinate laws agree, not only their conditional distributions. -/
theorem coordinates_identDistrib (i j : ℕ) :
    IdentDistrib (coordinate i) (coordinate j) probability probability := by
  refine ⟨(coordinate_measurable i).aemeasurable, (coordinate_measurable j).aemeasurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (coordinate_measurable i) hB,
    Measure.map_apply (coordinate_measurable j) hB,
    coordinate_event_integral, coordinate_event_integral]

/-- A second-moment assumption at one row supplies it at every other row. -/
theorem coordinate_memLp_of_zero (F : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) (i : ℕ) :
    MemLp (fun ω => F (coordinate i ω)) 2 probability :=
  ((coordinates_identDistrib 0 i).comp (measurable_of_countable F)).memLp_snd hF

def marginalTerm (n k : ℕ) : ℝ :=
  if n ≤ k + 1 then mixtureWeight (k + 1) / ((k + 1 : ℕ) : ℝ) else 0

theorem marginalTerm_nonneg (n k : ℕ) : 0 ≤ marginalTerm n k := by
  unfold marginalTerm
  split_ifs
  · exact div_nonneg (mixtureWeight_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

/-- The shift is handled in real HasSum before converting to a probability mass. -/
theorem hasSum_marginalTerm (m : ℕ) : HasSum (marginalTerm (m + 1)) (weight (m + 1)) := by
  have he : (fun k => marginalTerm (m + 1) (k + m)) =
      (fun k => mixtureWeight ((m + 1) + k) / (((m + 1) + k : ℕ) : ℝ)) := by
    funext k
    unfold marginalTerm
    rw [if_pos (by omega)]
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have ht : HasSum (fun k => marginalTerm (m + 1) (k + m)) (weight (m + 1)) := by
    rw [he]
    exact hasSum_uniform_mixture_marginal _ (Nat.succ_pos _)
  have hs : Summable (marginalTerm (m + 1)) :=
    (summable_nat_add_iff m).mp ht.summable
  have hz : ∑ k ∈ Finset.range m, marginalTerm (m + 1) k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkm : k < m := Finset.mem_range.mp hk
    simp [marginalTerm, show ¬ m + 1 ≤ k + 1 by omega]
  have hsum := Summable.sum_add_tsum_nat_add m hs
  rw [hz, zero_add, ht.tsum_eq] at hsum
  simpa only [hsum.symm] using hs.hasSum

/-- A coordinate has no mass at zero. -/
theorem coordinate_zero_mass (i : ℕ) : probability (coordinate i ⁻¹' {0}) = 0 := by
  rw [coordinate_event_integral]
  simp [uniformLaw_singleton]

/-- The exact positive-coordinate marginal, now a theorem about actual random variables. -/
theorem coordinate_positive_mass (i m : ℕ) :
    probability (coordinate i ⁻¹' {m + 1}) = ENNReal.ofReal (weight (m + 1)) := by
  rw [coordinate_event_integral, lintegral_countable']
  have he : (fun k => uniformLaw k {m + 1} * latentLaw {k}) =
      (fun k => ENNReal.ofReal (marginalTerm (m + 1) k)) := by
    funext k
    rw [latentLaw_singleton, uniformLaw_singleton]
    by_cases hk : m + 1 ≤ k + 1
    · rw [if_pos ⟨by omega, hk⟩]
      unfold marginalTerm
      rw [if_pos hk, ENNReal.ofReal_div_of_pos (by positivity)]
      simp [div_eq_mul_inv, mul_comm, ENNReal.ofReal_add,
        Nat.cast_nonneg]
    · rw [if_neg (by omega)]
      simp [marginalTerm, hk]
  rw [he, ← ENNReal.ofReal_tsum_of_nonneg (marginalTerm_nonneg (m + 1))
    (hasSum_marginalTerm m).summable, (hasSum_marginalTerm m).tsum_eq]

/-- The support and finite-integer interpretation hold simultaneously across all rows. -/
theorem coordinates_positive_ae : ∀ᵐ ω ∂probability, ∀ i : ℕ, 0 < coordinate i ω := by
  apply ae_all_iff.mpr
  intro i
  rw [ae_iff]
  have he : {ω : Omega | ¬ 0 < coordinate i ω} = coordinate i ⁻¹' {0} := by
    ext ω
    simp
  rw [he, coordinate_zero_mass]

end RiemannResearch.Probability.ConditionalIID
