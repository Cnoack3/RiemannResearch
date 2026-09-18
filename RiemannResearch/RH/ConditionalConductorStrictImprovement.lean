import RiemannResearch.RH.ConditionalHeadStrictImprovement
import RiemannResearch.RH.ConditionalConductorExhaustion

/-!
# Strict finite-conductor improvement and escape of near-minimizers

Source: this continuation of the exact conditional matrix minimum.
Finite attainment and strict arithmetic improvement imply a positive gap for
each fixed conductor. These are qualitative results: no rate uniform in the
head length or conductor is supplied.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.ConditionalFiniteMinimum

/-- Every finite inverse-matrix minimum strictly exceeds the unrestricted infimum. -/
theorem conditionalHeadMinimum_lt_fullValue (N D : ℕ)
    (hN : 0 < N) (hND : N+1 ≤ D) :
    conditionalHeadMinimum N < fullValue N D hND := by
  obtain ⟨c, hc, he⟩ := (fullValue_isLeast N D hND).1
  rw [← he]
  exact conditionalHeadMinimum_lt_energy N hN _ (synthesis_headClass N D c hc)

/-- No finite conductor budget is the last improving budget. This does not say
that adding each individual next column gives a strict improvement. -/
theorem exists_larger_conductor_strict_improvement (N D : ℕ)
    (hN : 0 < N) (hND : N+1 ≤ D) :
    ∃ E : ℕ, ∃ hDE : D < E,
      fullValue N E (by omega) < fullValue N D hND := by
  obtain ⟨c, hc, he⟩ := (fullValue_isLeast N D hND).1
  obtain ⟨G, hG, hlt⟩ := exists_strict_conditionalHead_improvement N hN _
    (synthesis_headClass N D c hc)
  obtain ⟨L, hL⟩ := legal_mem_finiteResidueSubspace hG.1
  refine ⟨max (D+1) L, by omega, ?_⟩
  have hbound := fullValue_le_of_mem_finite N (max (D+1) L) (by omega) hG
    (finiteResidueSubspace_mono (le_max_right _ _) hL)
  rw [he] at hlt
  exact hbound.trans_lt hlt

/-- One enlarged budget gives a positive improvement, uniform over every
feasible old-budget witness. The new witness can be chosen once. -/
theorem exists_uniform_improvement_at_fixed_conductor (N D : ℕ)
    (hN : 0 < N) (hND : N+1 ≤ D) :
    ∃ E : ℕ, D < E ∧ ∃ G ∈ conditionalHeadClass N,
      G ∈ finiteResidueSubspace E ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ F ∈ conditionalHeadClass N, F ∈ finiteResidueSubspace D →
          conditionalMeanSquare G + δ ≤ conditionalMeanSquare F := by
  obtain ⟨E, hDE, hlt⟩ := exists_larger_conductor_strict_improvement N D hN hND
  obtain ⟨c, hc, he⟩ := (fullValue_isLeast N E (by omega)).1
  refine ⟨E, hDE, synthesis E c, synthesis_headClass N E c hc,
    synthesis_mem_finite E c, fullValue N D hND-fullValue N E (by omega),
    sub_pos.mpr hlt, ?_⟩
  intro F hF hD
  rw [he]
  have hh := fullValue_le_of_mem_finite N D hND hF hD
  linarith

/-- Approaching the unrestricted infimum forces escape from every fixed
finite residue dictionary, regardless of how the approximating family was built. -/
theorem near_minimizers_eventually_outside_finite
    (N : ℕ) (hN : 0 < N) (F : ℕ → ℕ → ℝ)
    (hF : ∀ j, F j ∈ conditionalHeadClass N)
    (hlim : Tendsto (fun j => conditionalMeanSquare (F j))
      atTop (𝓝 (conditionalHeadMinimum N))) (D : ℕ) :
    ∀ᶠ j in atTop, F j ∉ finiteResidueSubspace D := by
  let E := max (N+1) D
  have hNE : N+1 ≤ E := le_max_left _ _
  have hgap := conditionalHeadMinimum_lt_fullValue N E hN hNE
  filter_upwards [hlim.eventually (gt_mem_nhds hgap)] with j hj
  intro hjD
  have hh := fullValue_le_of_mem_finite N E hNE (hF j)
    (finiteResidueSubspace_mono (le_max_right (N+1) D) hjD)
  exact not_lt_of_ge hh hj

/-- In particular, any sequence of valid conductor budgets for near-minimizers
must tend to infinity. This is an escape theorem, not a quantitative energy bound. -/
theorem near_minimizer_conductors_tendsto
    (N : ℕ) (hN : 0 < N) (F : ℕ → ℕ → ℝ) (D : ℕ → ℕ)
    (hF : ∀ j, F j ∈ conditionalHeadClass N)
    (hD : ∀ j, F j ∈ finiteResidueSubspace (D j))
    (hlim : Tendsto (fun j => conditionalMeanSquare (F j))
      atTop (𝓝 (conditionalHeadMinimum N))) :
    Tendsto D atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [near_minimizers_eventually_outside_finite N hN F hF hlim B] with j hj
  by_contra h
  exact hj (finiteResidueSubspace_mono (by omega : D j ≤ B) (hD j))

end RiemannResearch.RH.Pareto.ConditionalFiniteMinimum
