import RiemannResearch.Analysis.ConsecutiveRatioGapLaw

/-! # Consecutive prime-ratio phases beyond every prescribed zero height

The individual-orbit density statement in the joint prime-phase research note
allows any lower height cutoff. For backward ratios, the existing weak limit
gives a positive lower limiting mass to each nonempty open window. To obtain
cofinal visits directly, remove the finitely many first coordinates seen at
zeros up to the chosen height. This closed cylinder has product Haar mass zero.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology ENNReal
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open ActualZeroOrdinate RatioChainHaar
open scoped RiemannResearch.Analysis.RatioChainHaar

private theorem ratioProduct_openPos : productHaar.IsOpenPosMeasure :=
  isOpenPosMeasure_of_mulLeftInvariant_of_compact (μ := productHaar) univ isCompact_univ
    (by simp)

theorem actual_ratio_open_lower_mass {U : Set Chain} (hU : IsOpen U) (hn : U.Nonempty) :
    0 < liminf (fun T : ℝ => (empiricalRatios T : Measure Chain) U) atTop := by
  have := ratioProduct_openPos
  exact (hU.measure_pos productHaar hn).trans_le
    (ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_empiricalRatios hU)

theorem dense_actual_ratio_phases_above (B : ℝ) :
    Dense {y : Chain | ∃ (T : ℝ) (i : Copies T),
      B < copyOrdinate T i ∧ primeRatios (phasePoint (copyOrdinate T i)) = y} := by
  classical
  have := circleHaar_nullSingleton
  have := ratioProduct_openPos
  let low : Finset Circle := (cutoff B).image fun ρ => primeRatios (phasePoint ρ.im) 0
  let C := (fun y : Chain => y 0) ⁻¹' (low : Set Circle)
  have hclosed : IsClosed C := low.finite_toSet.isClosed.preimage (continuous_apply 0)
  have hz : productHaar C = 0 := by
    change productHaar ((fun y : Chain => y 0) ⁻¹' (low : Set Circle)) = 0
    rw [← Measure.map_apply (measurable_pi_apply 0) low.finite_toSet.measurableSet, coordinate_map]
    exact low.finite_toSet.countable.measure_zero circleHaar
  apply dense_iff_inter_open.2
  intro U hu hn
  have hne : (U \ C).Nonempty := by
    by_contra he
    have hsub : U ⊆ C := by
      intro y hy
      by_contra hc
      exact he ⟨y,hy,hc⟩
    have hle := measure_mono (μ := productHaar) hsub
    rw [hz] at hle
    exact (hu.measure_pos productHaar hn).not_ge hle
  obtain ⟨_, ⟨hy,havoid⟩, T, i, rfl⟩ :=
    dense_iff_inter_open.mp dense_actual_ratio_phases _ (hu.sdiff hclosed) hne
  refine ⟨_,hy,T,i,?_,rfl⟩
  by_contra! hlow
  apply havoid
  change primeRatios (phasePoint (copyOrdinate T i)) 0 ∈ low
  have hroot := mem_cutoff.mp i.1.property
  exact Finset.mem_image.mpr ⟨i.1.val, mem_cutoff.mpr ⟨hroot.1,hroot.2.1,hlow⟩,rfl⟩

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
