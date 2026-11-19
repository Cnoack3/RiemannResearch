import RiemannResearch.Probability.DeterminantalExistence
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Instances.Matrix

/-!
# Weak convergence of discrete determinantal laws

On a countable Boolean product, coordinate inclusions are clopen and the
space of probability measures is compact. Entrywise kernel convergence
therefore gives weak convergence of the actual laws. Finite marginal
uniqueness follows from inclusion-exclusion and uniqueness of projective
limits. For the continuous-kernel setting see Soshnikov, *Determinantal
random point fields*, Theorem 5, https://arxiv.org/abs/math/0002099.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace RiemannResearch.Probability.DPP

variable {α : Type*}

/-- Restricting a canonical Boolean DPP to finitely many coordinates retains
the principal restriction of its kernel. -/
theorem IsDPP.restrict_bool {μ : Measure (α → Bool)} [IsProbabilityMeasure μ]
    {K : α → α → ℝ} (h : IsDPP μ (fun x => {i | x i = true}) K) (I : Finset α)
    [IsProbabilityMeasure (μ.map I.restrict)] :
    IsDPP (μ.map I.restrict) (fun x => {i | x i = true}) (fun i j : I => K i.val j.val) := by
  classical
  constructor
  · intro i
    exact (Set.toFinite _).measurableSet
  · intro m e
    let a := e.trans (Function.Embedding.subtype (fun i => i ∈ I))
    change (μ.map I.restrict {x | ∀ k, x (e k) = true}).toReal = _
    rw [Measure.map_apply (measurable_pi_lambda _ fun i => measurable_pi_apply i.val)
      (Set.toFinite _).measurableSet]
    exact h.correlation m a

/-- All principal inclusion probabilities determine the full Boolean law
on any discrete index set. -/
theorem boolLaw_unique {μ ν : Measure (α → Bool)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : α → α → ℝ} (hμ : IsDPP μ (fun x => {i | x i = true}) K)
    (hν : IsDPP ν (fun x => {i | x i = true}) K) : μ = ν := by
  classical
  let P := fun I : Finset α => μ.map I.restrict
  have hm (I : Finset α) : Measurable (I.restrict : (α → Bool) → (I → Bool)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  letI (I : Finset α) : IsProbabilityMeasure (μ.map I.restrict) :=
    Measure.isProbabilityMeasure_map (hm I).aemeasurable
  letI (I : Finset α) : IsProbabilityMeasure (ν.map I.restrict) :=
    Measure.isProbabilityMeasure_map (hm I).aemeasurable
  have hlim : IsProjectiveLimit (α := fun _ : α => Bool) μ P := fun _ => rfl
  have hlim' : IsProjectiveLimit (α := fun _ : α => Bool) ν P := by
    intro I
    exact boolMeasure_eq_of_isDPP _ _ _ (hν.restrict_bool I) (hμ.restrict_bool I)
  exact hlim.unique hlim'

private theorem continuousAt_inclusion [Countable α] (ν : ProbabilityMeasure (α → Bool))
    (m : ℕ) (e : Fin m ↪ α) :
    ContinuousAt (fun ρ : ProbabilityMeasure (α → Bool) =>
      (ρ : Measure (α → Bool)).real {x | ∀ k, x (e k) = true}) ν := by
  let E : Set (α → Bool) := {x | ∀ k, x (e k) = true}
  let r := fun x : α → Bool => fun k : Fin m => x (e k)
  let C : Set (Fin m → Bool) := {y | ∀ k, y k = true}
  have hr : Continuous r := continuous_pi (fun k => continuous_apply (e k))
  have hc : IsClosed E := (Set.toFinite C).isClosed.preimage hr
  have ho : IsOpen E := (isOpen_discrete C).preimage hr
  have hnull : (ν : Measure (α → Bool)) (frontier E) = 0 := by
    rw [frontier, hc.closure_eq, ho.interior_eq, sdiff_self, measure_empty]
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μs := fun ρ : ProbabilityMeasure (α → Bool) => ρ) (L := 𝓝 ν) tendsto_id hnull
  exact (ENNReal.continuousAt_toReal (measure_ne_top (ν : Measure _) E)).tendsto.comp h

/-- Entrywise convergence of real kernels yields weak convergence of the
Boolean laws, with no monotone coupling or projective consistency premise. -/
theorem tendsto_boolLaw_of_kernel [Countable α] {β : Type*} {l : Filter β}
    (μ : β → ProbabilityMeasure (α → Bool)) (ν : ProbabilityMeasure (α → Bool))
    (K : β → α → α → ℝ) (L : α → α → ℝ)
    (hμ : ∀ t, IsDPP (μ t : Measure (α → Bool)) (fun x => {i | x i = true}) (K t))
    (hν : IsDPP (ν : Measure (α → Bool)) (fun x => {i | x i = true}) L)
    (hK : ∀ i j, Tendsto (fun t => K t i j) l (𝓝 (L i j))) :
    Tendsto μ l (𝓝 ν) := by
  classical
  apply le_nhds_of_unique_clusterPt
  intro ρ hρ
  apply Subtype.ext
  change (ρ : Measure (α → Bool)) = (ν : Measure (α → Bool))
  haveI : IsProbabilityMeasure (ρ : Measure (α → Bool)) := ρ.property
  apply boolLaw_unique _ hν
  constructor
  · intro i
    exact (measurableSet_singleton true).preimage (measurable_pi_apply i)
  · intro m e
    let F := fun v : ProbabilityMeasure (α → Bool) =>
      (v : Measure (α → Bool)).real {x | ∀ i, x (e i) = true}
    let D := Matrix.det (Matrix.of (fun i j => L (e i) (e j)))
    have hd : Tendsto (fun t => Matrix.det (Matrix.of (fun i j => K t (e i) (e j)))) l (𝓝 D) :=
      (continuous_id.matrix_det.tendsto _).comp (tendsto_pi_nhds.mpr fun i =>
        tendsto_pi_nhds.mpr fun j => hK (e i) (e j))
    have ht : Tendsto F (Filter.map μ l) (𝓝 D) := by
      apply tendsto_map'_iff.mpr
      exact hd.congr (fun t => ((hμ t).correlation m e).symm)
    let l' := (𝓝 ρ) ⊓ Filter.map μ l
    haveI : l'.NeBot := hρ
    have h₁ : Tendsto F l' (𝓝 (F ρ)) :=
      (continuousAt_inclusion ρ m e).tendsto.mono_left inf_le_left
    have h₂ : Tendsto F l' (𝓝 D) := ht.mono_left inf_le_right
    exact tendsto_nhds_unique h₁ h₂

end RiemannResearch.Probability.DPP
