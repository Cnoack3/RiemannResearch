/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Probability.DeterminantalProcess
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
/-!
# Finite-window occupation and gap budgets

Source: elementary union bounds applied to the standard DPP one-point laws.
The concrete RH consumer is QDivisorDPPArithmeticBounds. Moving dimensions
and locations are permitted; no inter-stage coupling is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace RiemannResearch.Probability.DPP
variable {ι α Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}
theorem IsDPP.window_occupation_lower_bound (h : IsDPP μ X K) (e : ι → α) :
    1 - ∑ i, (1 - K (e i) (e i)) ≤ μ.real {ω | ∀ i, e i ∈ X ω} := by
  have he : {ω | ∀ i, e i ∈ X ω} = (⋃ i, {ω | e i ∉ X ω})ᶜ := by ext ω; simp
  have hm (i : ι) : MeasurableSet {ω | e i ∉ X ω} := by
    simpa only [Set.compl_ofPred] using (h.measurable_occupancy (e i)).compl
  rw [he, probReal_compl_eq_one_sub (MeasurableSet.iUnion hm)]
  have hb := measureReal_iUnion_fintype_le (μ := μ) (fun i => {ω | e i ∉ X ω})
  simp only [h.vacancy] at hb
  linarith
theorem IsDPP.window_gap_lower_bound (h : IsDPP μ X K) (e : ι → α) :
    1 - ∑ i, K (e i) (e i) ≤ μ.real {ω | ∀ i, e i ∉ X ω} := by
  have he : {ω | ∀ i, e i ∉ X ω} = (⋃ i, {ω | e i ∈ X ω})ᶜ := by ext ω; simp
  rw [he, probReal_compl_eq_one_sub (MeasurableSet.iUnion (fun i => h.measurable_occupancy (e i)))]
  have hb := measureReal_iUnion_fintype_le (μ := μ) (fun i => {ω | e i ∈ X ω})
  simp only [h.occupation] at hb
  linarith
theorem moving_window_occupation_tendsto
    (μ : ℕ → Measure Ω) [∀ N, IsProbabilityMeasure (μ N)]
    (X : ℕ → Ω → Set α) (K : ℕ → α → α → ℝ)
    (h : ∀ N, IsDPP (μ N) (X N) (K N))
    (m : ℕ → ℕ) (e : (N : ℕ) → Fin (m N) → α)
    (hb : Tendsto (fun N => ∑ i, (1 - K N (e N i) (e N i))) atTop (𝓝 0)) :
    Tendsto (fun N => (μ N).real {ω | ∀ i, e N i ∈ X N ω}) atTop (𝓝 1) := by
  have hl : Tendsto (fun N => 1 - ∑ i, (1 - K N (e N i) (e N i)))
      atTop (𝓝 (1 - 0 : ℝ)) := tendsto_const_nhds.sub hb
  rw [sub_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro N
    exact (h N).window_occupation_lower_bound (e N)
  · intro N
    have hh : ((μ N) {ω | ∀ i, e N i ∈ X N ω}).toReal ≤
        ((μ N) Set.univ).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top (μ N) _)
        (measure_ne_top (μ N) Set.univ)).mpr (measure_mono (Set.subset_univ _))
    simpa [Measure.real] using hh
theorem moving_window_gap_tendsto
    (μ : ℕ → Measure Ω) [∀ N, IsProbabilityMeasure (μ N)]
    (X : ℕ → Ω → Set α) (K : ℕ → α → α → ℝ)
    (h : ∀ N, IsDPP (μ N) (X N) (K N))
    (m : ℕ → ℕ) (e : (N : ℕ) → Fin (m N) → α)
    (hb : Tendsto (fun N => ∑ i, K N (e N i) (e N i)) atTop (𝓝 0)) :
    Tendsto (fun N => (μ N).real {ω | ∀ i, e N i ∉ X N ω}) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using tendsto_const_nhds.sub hb) tendsto_const_nhds
  · intro N
    exact (h N).window_gap_lower_bound (e N)
  · intro N
    have hh : ((μ N) {ω | ∀ i, e N i ∉ X N ω}).toReal ≤
        ((μ N) Set.univ).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top (μ N) _)
        (measure_ne_top (μ N) Set.univ)).mpr (measure_mono (Set.subset_univ _))
    simpa [Measure.real] using hh
end RiemannResearch.Probability.DPP
