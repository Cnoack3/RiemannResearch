import RiemannResearch.RH.ParetoCoordinateEvaluation
import RiemannResearch.RH.RoughComponentProjection
import RiemannResearch.RH.SquarefreeDilationObstruction

/-!
# Arithmetic charge consequences of convergence in the actual Hilbert norm

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
sections 7--8. This module connects the arithmetic pointwise theorems to the
complete weighted Pareto Hilbert space via actual continuous evaluations.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators Topology
open Filter PositiveSeedCone FiniteSeedComponentCharge
noncomputable section

theorem hilbert_target_limit_implies_physical_pointwise
    (F : ℕ → ThresholdHilbert) (hF : Tendsto F atTop (𝓝 hilbertOne))
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun j => hilbertSequence (F j) n) atTop (𝓝 (1 : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have ht := ((physicalEvaluationCLM k).continuous.tendsto hilbertOne).comp hF
  simpa only [Function.comp_def, physicalEvaluationCLM_apply, hilbertOne_sequence, zeroAnchor,
    Nat.succ_ne_zero, ↓reduceIte] using ht

/-- Every fixed remainder coordinate is forced by convergence in the genuine
Pareto Hilbert norm. -/
theorem physicalRemainderCoefficient_tendsto_of_hilbert_limit
    (F : ℕ → ThresholdHilbert) (hF : Tendsto F atTop (𝓝 hilbertOne))
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun j => physicalRemainderCoefficient d (hilbertSequence (F j))) atTop
      (𝓝 (-(ArithmeticFunction.moebius d : ℝ) / (d : ℝ))) :=
  physicalRemainderCoefficient_tendsto (fun j => hilbertSequence_zero _)
    (hilbert_target_limit_implies_physical_pointwise F hF) d hd

/-- The arithmetic component norm divergence applies to every actual
Hilbert-norm approximating sequence of finite signed legal packets. -/
theorem twoSeed_roughComponent_energy_diverges_of_hilbert_limit {ι : Type*}
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (hmu : ArithmeticFunction.moebius q ≠ 0)
    (s : ℕ → Finset ι) (a m : ℕ → ι → ℕ) (c : ℕ → ι → ℝ)
    (ha : ∀ j i, i ∈ s j → a j i = 2 ∨ a j i = 3)
    (hm : ∀ j i, i ∈ s j → 0 < m j i)
    (F : ℕ → ThresholdHilbert)
    (hrep : ∀ j, hilbertSequence (F j) = seedCombination (s j) (a j) (m j) (c j))
    (hF : Tendsto F atTop (𝓝 hilbertOne)) :
    Tendsto (fun j => ∑' n : ℕ, positiveWeight (n + 1) *
      roughComponentProjection q (seedCombination (s j) (a j) (m j) (c j))
        (n + 1) ^ 2) atTop atTop := by
  apply twoSeed_roughComponent_energy_tendsto_atTop q hq hc hmu s a m c ha hm
  intro n hn
  simpa only [hrep] using hilbert_target_limit_implies_physical_pointwise F hF n hn

/-- Squarefree dilation indices cannot approximate the constant even if all
signed coefficients and both primitive seeds remain available. -/
theorem squarefree_seed_no_hilbert_target_limit {ι : Type*}
    (s : ℕ → Finset ι) (a m : ℕ → ι → ℕ) (c : ℕ → ι → ℝ)
    (ha : ∀ j i, i ∈ s j → a j i = 2 ∨ a j i = 3)
    (hm : ∀ j i, i ∈ s j → 0 < m j i)
    (hs : ∀ j i, i ∈ s j → Squarefree (m j i))
    (F : ℕ → ThresholdHilbert)
    (hrep : ∀ j, hilbertSequence (F j) = seedCombination (s j) (a j) (m j) (c j)) :
    ¬ Tendsto F atTop (𝓝 hilbertOne) := by
  intro hF
  apply closedComponent_no_pointwise_limit squarefreeChargeSet s a m c
    (fun n hn => (squarefreeChargeSet_pos_bound n hn).1)
    (by intro j i hi; rcases ha j i hi with h | h <;> omega) hm
    (fun j i hi => squarefreeChargeSet_closed (a j i) (m j i) (ha j i hi)
      (squarefree_not_four_dvd (hs j i hi)) (squarefree_not_nine_dvd (hs j i hi)))
    (by rw [squarefreeChargeSet_signal]; norm_num)
  intro n hn
  simpa only [hrep] using hilbert_target_limit_implies_physical_pointwise F hF n hn

/-- Under constant approximation, the algebraic arithmetic projection has
no bounded linear extension to the Pareto Hilbert space. -/
theorem roughComponent_no_continuous_extension_along_approximants
    (q : ℕ) (hq : 0 < q) (hc : Nat.Coprime q 6)
    (hmu : ArithmeticFunction.moebius q ≠ 0)
    (F : ℕ → ThresholdHilbert) (hF : Tendsto F atTop (𝓝 hilbertOne)) :
    ¬ ∃ T : ThresholdHilbert →L[ℝ] ThresholdHilbert,
      ∀ j, hilbertSequence (T (F j)) =
        roughComponentProjection q (hilbertSequence (F j)) := by
  rintro ⟨T, hT⟩
  apply roughMobiusProfile_not_in_paretoHilbert q hq hmu
  refine ⟨T hilbertOne, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have hproj := roughComponentProjection_tendsto_profile q hq hc
    (fun j => hilbertSequence (F j)) (fun j => hilbertSequence_zero _)
    (hilbert_target_limit_implies_physical_pointwise F hF) (k + 1)
  have hcont := ((physicalEvaluationCLM k).continuous.tendsto (T hilbertOne)).comp
    ((T.continuous.tendsto hilbertOne).comp hF)
  simp only [Function.comp_def, physicalEvaluationCLM_apply, hT] at hcont
  exact tendsto_nhds_unique hcont hproj

end
end RiemannResearch.RH.Pareto
