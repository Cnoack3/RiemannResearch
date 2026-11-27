import RiemannResearch.Analysis.RatioChainHaar
import RiemannResearch.Analysis.ConsecutiveRatioGapDecoder
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # The actual infinite diagonal in consecutive prime-ratio coordinates

The input is the repository's prime Haar law and its diagonal copy. Each
ratio uses adjacent prime coordinates of one configuration. The normalized
empirical measures below count all actual positive zeta-zero occurrences.
The positivity of Haar measure on open sets gives density in the product
topology without choosing a rate of approximation.
-/

noncomputable section
open Filter MeasureTheory ProbabilityTheory Set Zeta23
open scoped Topology BigOperators ENNReal
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open CompactGaugeOrbitLaw ActualZeroOrdinate RatioChainHaar
open scoped RiemannResearch.Analysis.RatioChainHaar

local instance ratioOrbitTorusMeasurable : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance ratioOrbitTorusBorel : BorelSpace PrimeTorus := ⟨rfl⟩
local instance ratioOrbitPairMeasurable : MeasurableSpace (PrimeTorus × PrimeTorus) := borel _
local instance ratioOrbitPairBorel : BorelSpace (PrimeTorus × PrimeTorus) := ⟨rfl⟩

def enumerateCoordinates : PrimeTorus →* Chain where
  toFun x k := x (orderedPrime k)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem enumerateCoordinates_surjective : Function.Surjective enumerateCoordinates := by
  let e := Equiv.ofBijective orderedPrime orderedPrime_bijective
  intro y
  refine ⟨fun p => y (e.symm p), ?_⟩
  funext k
  change y (e.symm (e k)) = y k
  rw [e.symm_apply_apply]

def primeRatios : PrimeTorus →* Chain := ratios.comp enumerateCoordinates

theorem continuous_primeRatios : Continuous primeRatios :=
  continuous_ratios.comp (continuous_pi fun k => continuous_apply (orderedPrime k))

theorem primeRatios_surjective : Function.Surjective primeRatios :=
  ratios_surjective.comp enumerateCoordinates_surjective

theorem primeRatios_apply (x : PrimeTorus) (k : ℕ) :
    primeRatios x k = x (orderedPrime k) / x (orderedPrime (k+1)) := rfl

theorem primeRatios_map :
    (primeHaar : Measure PrimeTorus).map primeRatios = productHaar := by
  have : Measure.IsMulLeftInvariant (primeHaar : Measure PrimeTorus) := by
    constructor
    intro x
    exact congrArg ProbabilityMeasure.toMeasure (primeHaar_translation x)
  exact map_eq_productHaar _ _ continuous_primeRatios primeRatios_surjective

/-- The same product law comes from the infinite diagonal. -/
theorem diagonal_primeRatios_map :
    (diagonalHaar : Measure (PrimeTorus × PrimeTorus)).map
      (fun z => primeRatios z.1) = productHaar := by
  change ((primeHaar : Measure PrimeTorus).map (fun x => (x,x))).map
    (fun z => primeRatios z.1) = _
  have hf : Measurable (fun z : PrimeTorus × PrimeTorus => primeRatios z.1) :=
    (continuous_primeRatios.comp continuous_fst).measurable
  have hd : Measurable (fun x : PrimeTorus => (x,x)) :=
    (continuous_id.prodMk continuous_id).measurable
  rw [Measure.map_map hf hd]
  exact primeRatios_map

theorem diagonal_ratio_marginal (k : ℕ) :
    (diagonalHaar : Measure (PrimeTorus × PrimeTorus)).map
      (fun z => primeRatios z.1 k) = circleHaar := by
  calc
    _ = ((diagonalHaar : Measure (PrimeTorus × PrimeTorus)).map
      (fun z => primeRatios z.1)).map (fun y : Chain => y k) :=
      (Measure.map_map (measurable_pi_apply k)
        (continuous_primeRatios.comp continuous_fst).measurable).symm
    _ = _ := by rw [diagonal_primeRatios_map, coordinate_map]

theorem diagonal_ratios_independent :
    iIndepFun (fun k (z : PrimeTorus × PrimeTorus) => primeRatios z.1 k)
      (diagonalHaar : Measure (PrimeTorus × PrimeTorus)) := by
  have hm (k : ℕ) :
      Measurable (fun z : PrimeTorus × PrimeTorus => primeRatios z.1 k) :=
    ((continuous_apply k).comp (continuous_primeRatios.comp continuous_fst)).measurable
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map hm).2
  simp only [diagonal_ratio_marginal]
  exact diagonal_primeRatios_map

theorem diagonal_ratio_pair_map {k l : ℕ} (hkl : k ≠ l) :
    (diagonalHaar : Measure (PrimeTorus × PrimeTorus)).map
      (fun z => (primeRatios z.1 k, primeRatios z.1 l)) = circleHaar.prod circleHaar := by
  have hm (i : ℕ) : Measurable (fun z : PrimeTorus × PrimeTorus => primeRatios z.1 i) :=
    ((continuous_apply i).comp (continuous_primeRatios.comp continuous_fst)).measurable
  have h := (diagonal_ratios_independent.indepFun hkl).map_prod_eq_prod_map_map
    (hm k).aemeasurable (hm l).aemeasurable
  simpa only [diagonal_ratio_marginal] using h

def empiricalRatios (T : ℝ) : ProbabilityMeasure Chain :=
  (empiricalProbability T).map continuous_primeRatios.measurable.aemeasurable

theorem tendsto_empiricalRatios :
    Tendsto empiricalRatios atTop
      (𝓝 (⟨productHaar, inferInstance⟩ : ProbabilityMeasure Chain)) := by
  have he : primeHaar.map continuous_primeRatios.measurable.aemeasurable =
      (⟨productHaar, inferInstance⟩ : ProbabilityMeasure Chain) := Subtype.ext primeRatios_map
  rw [← he]
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    tendsto_primeHaar continuous_primeRatios

/-- All finite cylinder requirements can be approximated simultaneously by
the ratios at a genuine positive-height zero occurrence. -/
theorem dense_actual_ratio_phases :
    Dense {y : Chain | ∃ (T : ℝ) (i : Copies T),
      primeRatios (phasePoint (copyOrdinate T i)) = y} := by
  rw [dense_iff_inter_open]
  intro U hu hn
  by_contra he
  have hnone (T : ℝ) (i : Copies T) : primeRatios (phasePoint (copyOrdinate T i)) ∉ U := by
    intro hi
    exact he ⟨_, hi, T, i, rfl⟩
  have hU := (continuous_primeRatios.isOpen_preimage _ hu).measurableSet
  have hz : (fun T => (empiricalRatios T : Measure Chain) U) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_count_pos] with T hT
    rw [empiricalRatios, ProbabilityMeasure.map_apply' _ _ hu.measurableSet,
      empiricalProbability_eq_raw _ hT, rawEmpiricalMeasure, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hnpre : phasePoint (i.1.val.im) ∉ (primeRatios ⁻¹' U) := hnone T i
    rw [Measure.smul_apply, Measure.dirac_apply' _ hU, Set.indicator_of_notMem hnpre, smul_zero]
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_empiricalRatios hu
  rw [Filter.liminf_congr hz, Filter.liminf_const] at hlim
  have : productHaar.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact (μ := productHaar) univ isCompact_univ
      (by simp)
  exact (hu.measure_pos productHaar hn).not_ge hlim

theorem dense_primeRatio_orbit : DenseRange (fun t : ℝ => primeRatios (phasePoint t)) := by
  apply dense_actual_ratio_phases.mono
  rintro y ⟨T,i,rfl⟩
  exact ⟨copyOrdinate T i, rfl⟩

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
