import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
/-!
# Compact probability convergence from a dense family of moments

Proof strategy: uniform approximation and compactness of probability measures,
using Mathlib's Prokhorov/Riesz-Markov-Kakutani infrastructure.
Source: Mathlib/MeasureTheory/Measure/Prokhorov.lean and
Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean.
Consumer: infinite prime-torus and compact Hilbert-orbit sampling laws.
No arithmetic estimate or independence assertion is included.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace MeasureTheory.ProbabilityMeasure
variable {X J I : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

def continuousIntegral (μ : ProbabilityMeasure X) : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add
    ((ContinuousMap.equivBoundedOfCompact X ℂ f).integrable _)
    ((ContinuousMap.equivBoundedOfCompact X ℂ g).integrable _)
  map_smul' c f := by
    simpa only [ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul] using
      integral_const_mul c (fun x => f x)

theorem continuousIntegral_bound (μ : ProbabilityMeasure X) (f : C(X, ℂ)) :
    ‖continuousIntegral μ f‖ ≤ ‖f‖ := by
  change ‖∫ x, f x ∂μ‖ ≤ ‖f‖
  simpa using
    (norm_integral_le_of_norm_le_const
      (μ := (μ : Measure X)) (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm x)))

theorem tendsto_of_dense_test_integrals {l : Filter I}
    (test : J → C(X, ℂ))
    (hdense : (Submodule.span ℂ (Set.range test)).topologicalClosure = ⊤)
    (μ : I → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (htest : ∀ j, Tendsto (fun i => ∫ x, test j x ∂μ i) l (𝓝 (∫ x, test j x ∂ν))) :
    Tendsto μ l (𝓝 ν) := by
  have hspan : ∀ g ∈ Submodule.span ℂ (Set.range test),
      Tendsto (fun i => continuousIntegral (μ i) g) l (𝓝 (continuousIntegral ν g)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg => obtain ⟨j,rfl⟩ := hg; exact htest j
    | zero =>
        simpa only [map_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℂ)) l (𝓝 0))
    | add g h hg hh ig ih => simpa only [map_add] using ig.add ih
    | smul c g hg ih => simpa only [map_smul] using ih.const_smul c
  apply (tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  change Tendsto (fun i => continuousIntegral (μ i) f.toContinuousMap) l
    (𝓝 (continuousIntegral ν f.toContinuousMap))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hf : f.toContinuousMap ∈ (Submodule.span ℂ (Set.range test)).topologicalClosure := by
    rw [hdense]; trivial
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε/4) (by positivity)
  have hnear := Metric.tendsto_nhds.mp (hspan g hg) (ε/2) (by positivity)
  filter_upwards [hnear] with i hi
  have hb1 : ‖continuousIntegral (μ i) f.toContinuousMap - continuousIntegral (μ i) g‖
      ≤ ‖f.toContinuousMap - g‖ := by
    rw [← map_sub]; exact continuousIntegral_bound _ _
  have hb2 : ‖continuousIntegral ν g - continuousIntegral ν f.toContinuousMap‖
      ≤ ‖f.toContinuousMap - g‖ := by
    rw [← map_sub]
    exact (continuousIntegral_bound _ _).trans_eq (norm_sub_rev _ _)
  have htri := norm_add_le
    (continuousIntegral (μ i) f.toContinuousMap - continuousIntegral (μ i) g)
    (continuousIntegral (μ i) g - continuousIntegral ν g)
  have htri2 := norm_add_le
    (continuousIntegral (μ i) f.toContinuousMap - continuousIntegral ν g)
    (continuousIntegral ν g - continuousIntegral ν f.toContinuousMap)
  simp only [sub_add_sub_cancel] at htri htri2
  rw [dist_eq_norm] at hfg hi ⊢
  linarith

theorem exists_limit_of_dense_test_integrals [T2Space X] [BorelSpace X]
    {l : Filter I} [NeBot l]
    (test : J → C(X, ℂ))
    (hdense : (Submodule.span ℂ (Set.range test)).topologicalClosure = ⊤)
    (μ : I → ProbabilityMeasure X) (c : J → ℂ)
    (htest : ∀ j, Tendsto (fun i => ∫ x, test j x ∂μ i) l (𝓝 (c j))) :
    ∃ ν : ProbabilityMeasure X,
      (∀ j, ∫ x, test j x ∂ν = c j) ∧ Tendsto μ l (𝓝 ν) := by
  let U := Ultrafilter.of l
  have hc := (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure X)))
  obtain ⟨ν, -, hν⟩ := hc.ultrafilter_le_nhds (U.map μ) (by simp)
  have hν' : Tendsto μ (U : Filter I) (𝓝 ν) := hν
  have hm (j : J) : ∫ x, test j x ∂ν = c j := by
    exact tendsto_nhds_unique
      ((tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hν'
        (ContinuousMap.equivBoundedOfCompact X ℂ (test j)))
      ((htest j).mono_left (Ultrafilter.of_le l))
  exact ⟨ν, hm, tendsto_of_dense_test_integrals test hdense μ ν (by
    intro j; rw [hm j]; exact htest j)⟩


/-- Character moments determine a probability measure when their span is dense. -/
theorem eq_of_dense_test_integrals [HasOuterApproxClosed X] [BorelSpace X]
    (test : J → C(X, ℂ))
    (hdense : (Submodule.span ℂ (Set.range test)).topologicalClosure = ⊤)
    (μ ν : ProbabilityMeasure X)
    (heq : ∀ j, ∫ x, test j x ∂μ = ∫ x, test j x ∂ν) : μ = ν := by
  have h : Tendsto (fun _ : ℕ => μ) atTop (𝓝 ν) :=
    tendsto_of_dense_test_integrals test hdense (fun _ => μ) ν (by
      intro j
      rw [heq j]
      exact tendsto_const_nhds)
  exact tendsto_nhds_unique tendsto_const_nhds h

/-- Pointwise limits of a dense family of moments have a unique positive
probability realization; positivity is supplied by compactness, not postulated. -/
theorem existsUnique_limit_of_dense_test_integrals [T2Space X]
    [HasOuterApproxClosed X] [BorelSpace X] {l : Filter I} [NeBot l]
    (test : J → C(X, ℂ))
    (hdense : (Submodule.span ℂ (Set.range test)).topologicalClosure = ⊤)
    (μ : I → ProbabilityMeasure X) (c : J → ℂ)
    (htest : ∀ j, Tendsto (fun i => ∫ x, test j x ∂μ i) l (𝓝 (c j))) :
    ∃! ν : ProbabilityMeasure X,
      (∀ j, ∫ x, test j x ∂ν = c j) ∧ Tendsto μ l (𝓝 ν) := by
  obtain ⟨ν, hm, hconv⟩ := exists_limit_of_dense_test_integrals test hdense μ c htest
  exact ⟨ν, ⟨hm, hconv⟩, fun η hη => tendsto_nhds_unique hη.2 hconv⟩

end MeasureTheory.ProbabilityMeasure
