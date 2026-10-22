import RiemannResearch.Probability.DeterminantalProcess
import Mathlib.Topology.Instances.Matrix

/-!
# Monotone unions of determinantal processes

Source: continuity from below of probability measures and continuity of finite
determinants; see Lyons, arXiv:math/0204325, Section 7, for the limiting-law
context. This theorem identifies the union of an already supplied nested
coupling. It does not construct such a coupling from ordered kernels.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace RiemannResearch.Probability.DPP

def increasingUnion {α Ω : Type*} (Z : ℕ → Ω → Set α) (ω : Ω) : Set α :=
  ⋃ n, Z n ω

theorem inclusion_event_increasingUnion {α Ω : Type*}
    (Z : ℕ → Ω → Set α) (hmono : ∀ n ω, Z n ω ⊆ Z (n+1) ω)
    (m : ℕ) (e : Fin m ↪ α) :
    {ω | ∀ i, e i ∈ increasingUnion Z ω} =
      ⋃ n, {ω | ∀ i, e i ∈ Z n ω} := by
  classical
  ext ω
  constructor
  · intro h
    have hx : ∀ i, ∃ n, e i ∈ Z n ω := by
      intro i
      exact Set.mem_iUnion.mp (h i)
    choose k hk using hx
    refine Set.mem_iUnion.mpr ⟨Finset.univ.sup k, ?_⟩
    intro i
    exact (monotone_nat_of_le_succ (fun n => hmono n ω))
      (Finset.le_sup (Finset.mem_univ i)) (hk i)
  · intro h i
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨n, hn i⟩

theorem isDPP_increasingUnion {α Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → Set α) (K : ℕ → α → α → ℝ) (L : α → α → ℝ)
    (hZ : ∀ n, IsDPP μ (Z n) (K n))
    (hmono : ∀ n ω, Z n ω ⊆ Z (n+1) ω)
    (hK : ∀ i j, Tendsto (fun n => K n i j) atTop (𝓝 (L i j))) :
    IsDPP μ (increasingUnion Z) L := by
  classical
  constructor
  · intro i
    have he : {ω | i ∈ increasingUnion Z ω} = ⋃ n, {ω | i ∈ Z n ω} := by
      ext ω
      simp [increasingUnion]
    rw [he]
    exact MeasurableSet.iUnion fun n => (hZ n).measurable_occupancy i
  · intro m e
    let E : ℕ → Set Ω := fun n => {ω | ∀ i, e i ∈ Z n ω}
    have hm : Monotone E := by
      intro a b hab ω hω i
      exact (monotone_nat_of_le_succ (fun n => hmono n ω)) hab (hω i)
    have hp : Tendsto (fun n => μ.real (E n)) atTop
        (𝓝 (μ.real (⋃ n, E n))) :=
      (ENNReal.continuousAt_toReal (measure_ne_top μ _)).tendsto.comp
        (tendsto_measure_iUnion_atTop hm)
    have hd : Tendsto (fun n => Matrix.det (Matrix.of (fun i j : Fin m => K n (e i) (e j))))
        atTop (𝓝 (Matrix.det (Matrix.of (fun i j : Fin m => L (e i) (e j))))) :=
      (continuous_id.matrix_det.tendsto _).comp
        (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hK (e i) (e j))
    have he : (fun n => μ.real (E n)) =
        (fun n => Matrix.det (Matrix.of (fun i j : Fin m => K n (e i) (e j)))) :=
      funext fun n => (hZ n).correlation m e
    rw [← he] at hd
    rw [inclusion_event_increasingUnion Z hmono m e]
    exact tendsto_nhds_unique hp hd
end RiemannResearch.Probability.DPP

namespace RiemannResearch.Probability.DPP
variable {α Ω : Type*}
def pastUnion (Z : ℕ → Ω → Set α) (n : ℕ) (ω : Ω) : Set α :=
  ⋃ j ≤ n, Z j ω
theorem pastUnion_mono (Z : ℕ → Ω → Set α) (n : ℕ) (ω : Ω) :
    pastUnion Z n ω ⊆ pastUnion Z (n+1) ω := by
  intro i hi
  simp only [pastUnion, Set.mem_iUnion] at hi ⊢
  obtain ⟨j, hj, hi⟩ := hi
  exact ⟨j, hj.trans (Nat.le_succ n), hi⟩
theorem pastUnion_eq (Z : ℕ → Ω → Set α) (n : ℕ) (ω : Ω)
    (h : ∀ j, Z j ω ⊆ Z (j+1) ω) : pastUnion Z n ω = Z n ω := by
  ext i
  simp only [pastUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj, hi⟩
    exact (monotone_nat_of_le_succ h) hj hi
  · intro hi
    exact ⟨n, le_rfl, hi⟩
theorem isDPP_pastUnion [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → Set α) (K : ℕ → α → α → ℝ)
    (hZ : ∀ n, IsDPP μ (Z n) (K n))
    (hmono : ∀ᵐ ω ∂μ, ∀ n, Z n ω ⊆ Z (n+1) ω) (n : ℕ) :
    IsDPP μ (pastUnion Z n) (K n) := by
  constructor
  · intro i
    have he : {ω | i ∈ pastUnion Z n ω} =
        ⋃ j, ⋃ (_ : j ≤ n), {ω | i ∈ Z j ω} := by
      ext ω
      simp [pastUnion]
    rw [he]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
      (hZ j).measurable_occupancy i
  · intro m e
    rw [← (hZ n).correlation m e]
    apply measureReal_congr
    filter_upwards [hmono] with ω hω
    change (∀ i, e i ∈ pastUnion Z n ω) = (∀ i, e i ∈ Z n ω)
    rw [pastUnion_eq Z n ω hω]
end RiemannResearch.Probability.DPP
