/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import RiemannResearch.Probability.DeterminantalWindow
import RiemannResearch.Probability.FiniteDeterminantalLaw
import Mathlib.Topology.Instances.Matrix
/-!
# Independent Bernoulli limits of finite determinantal configurations

Source: user-provided moving-window argument, Section 7 of
https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/QDPPMovingWindowsResearch20261014.md
supports the limit statement. The proof uses the existing exact finite DPP
law and determinant continuity, including all occupied/vacant patterns.
Marginal subsequences use compactness, with no arithmetic premise.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Topology
namespace RiemannResearch.Probability.DPP
variable {ι α Ω : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteBoolLaw_configuration (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (S : Finset ι) :
    (finiteBoolLaw K hpos).toMeasure.real
      {x | ∀ i, x i = decide (i ∈ S)} = exactWeight K S := by
  let : MeasurableSpace (Finset ι) := ⊤
  have he : (fun T : Finset ι => fun i => decide (i ∈ T)) ⁻¹'
      {x : ι → Bool | ∀ i, x i = decide (i ∈ S)} = ({S} : Set (Finset ι)) := by
    ext T
    change (∀ i, decide (i ∈ T) = decide (i ∈ S)) ↔ T = S
    constructor
    · intro h
      ext i
      simpa using h i
    · rintro rfl i
      rfl
  change (((finiteLaw K hpos).map (fun T i => decide (i ∈ T))).toMeasure
    {x | ∀ i, x i = decide (i ∈ S)}).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) (Set.toFinite _).measurableSet,
    he, (finiteLaw K hpos).toMeasure_apply_singleton S (measurableSet_singleton _)]
  change (ENNReal.ofReal (exactWeight K S)).toReal = _
  exact ENNReal.toReal_ofReal (hpos S)

open Classical in
theorem IsDPP.finite_configuration [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Set α} {K : α → α → ℝ}
    (h : IsDPP μ X K) (e : ι ↪ α)
    (hpos : ∀ S, 0 ≤ exactWeight (Matrix.of (fun i j : ι => K (e i) (e j))) S)
    (S : Finset ι) :
    μ.real {ω | ∀ i, decide (e i ∈ X ω) = decide (i ∈ S)} =
      exactWeight (Matrix.of (fun i j : ι => K (e i) (e j))) S := by
  classical
  let r : Ω → (ι → Bool) := fun ω i => decide (e i ∈ X ω)
  have hr : Measurable r := by
    apply measurable_pi_lambda
    intro i
    change Measurable (({ω | e i ∈ X ω} : Set Ω).piecewise
      (fun _ => true) (fun _ => false))
    exact measurable_const.piecewise (h.measurable_occupancy (e i)) measurable_const
  have hl := h.finite_restriction_law e hpos
  have hp := finiteBoolLaw_configuration (Matrix.of (fun i j : ι => K (e i) (e j))) hpos S
  rw [← hl] at hp
  change ((μ.map r) {x | ∀ i, x i = decide (i ∈ S)}).toReal = _ at hp
  rw [Measure.map_apply hr (Set.toFinite _).measurableSet] at hp
  exact hp

theorem exactWeight_diagonal (ρ : ι → ℝ) (S : Finset ι) :
    exactWeight (Matrix.diagonal ρ) S = ∏ i, if i ∈ S then ρ i else 1 - ρ i := by
  have he : mixedRows (Matrix.diagonal ρ) S =
      Matrix.diagonal (fun i => if i ∈ S then ρ i else 1 - ρ i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i ∈ S <;> simp [mixedRows, Finset.piecewise, Matrix.sub_apply, hi]
    · by_cases hi : i ∈ S <;>
        simp [mixedRows, Finset.piecewise, Matrix.sub_apply, hij, hi]
  rw [exactWeight, he, Matrix.det_diagonal]

theorem exactWeight_tendsto_of_diagonal (K : ℕ → Matrix ι ι ℝ) (ρ : ι → ℝ)
    (hK : ∀ i j, Tendsto (fun n => K n i j) atTop
      (𝓝 (if i = j then ρ i else 0))) (S : Finset ι) :
    Tendsto (fun n => exactWeight (K n) S) atTop
      (𝓝 (∏ i, if i ∈ S then ρ i else 1 - ρ i)) := by
  have hM : Tendsto (fun n => mixedRows (K n) S) atTop
      (𝓝 (mixedRows (Matrix.diagonal ρ) S)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hi : i ∈ S
    · simpa [mixedRows, Finset.piecewise, hi, Matrix.diagonal_apply] using hK i j
    · have h := (tendsto_const_nhds (x := (1 : Matrix ι ι ℝ) i j)).sub (hK i j)
      simpa [mixedRows, Finset.piecewise, Matrix.sub_apply, hi, Matrix.diagonal_apply] using h
  have hdet : Continuous (fun A : Matrix ι ι ℝ => A.det) := continuous_id.matrix_det
  have h := (hdet.tendsto _).comp hM
  change Tendsto (fun n => exactWeight (K n) S) atTop
    (𝓝 (exactWeight (Matrix.diagonal ρ) S)) at h
  rwa [exactWeight_diagonal] at h

omit [Fintype ι] [DecidableEq ι] in
theorem bounded_marginals_subsequence [Finite ι] (d : ℕ → ι → ℝ)
    (hd : ∀ N i, d N i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ρ : ι → ℝ, (∀ i, ρ i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ i, Tendsto (fun N => d (φ N) i) atTop (𝓝 (ρ i)) := by
  let : Fintype ι := Fintype.ofFinite ι
  have hc : IsCompact {ρ : ι → ℝ | ∀ i, ρ i ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨ρ, hρ, φ, hφ, ht⟩ := hc.isSeqCompact hd
  exact ⟨ρ, hρ, φ, hφ, fun i => (tendsto_pi_nhds.mp ht) i⟩

end RiemannResearch.Probability.DPP
