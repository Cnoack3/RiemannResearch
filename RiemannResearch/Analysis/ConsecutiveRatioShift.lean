import RiemannResearch.Analysis.ConsecutiveRatioGapLaw
import RiemannResearch.Analysis.PrimeOrbitPairLawDistinction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! # A Haar ratio sequence has a dense coordinate-shift orbit almost surely

Group the coordinates into disjoint blocks of any fixed positive length.
These blocks retain product law. A positive-probability block is missed in
the first k trials with probability at most (1-p)^k. Every open set in the
sequence space contains such a finite-prefix cylinder. Second countability
allows the almost-sure conclusion for all open sets at once.
-/

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal BigOperators
namespace RiemannResearch.Analysis.RatioChainHaar

def shift (n : ℕ) (y : Chain) : Chain := fun i => y (n+i)

def consecutiveBlocks (m : ℕ) (y : Chain) (j : ℕ) (i : Fin (m + 1)) : Circle :=
  y (j*(m+1)+i)

private abbrev blockHaar (m : ℕ) : Measure (Fin (m+1) → Circle) :=
  Measure.infinitePi (fun _ => circleHaar)

theorem consecutiveBlocks_map (m : ℕ) :
    productHaar.map (consecutiveBlocks m) = Measure.infinitePi (fun _ : ℕ => blockHaar m) := by
  let d := Nat.divModEquiv (m+1)
  let e := MeasurableEquiv.piCongrLeft (fun _ : ℕ × Fin (m+1) => Circle) d
  let c := MeasurableEquiv.curry ℕ (Fin (m+1)) Circle
  have hblock : consecutiveBlocks m = c ∘ e := by
    funext y j i
    have h (u : ℕ × Fin (m+1)) : e y u = y (d.symm u) := by
      obtain ⟨k,rfl⟩ := d.surjective u
      rw [d.symm_apply_apply]
      exact MeasurableEquiv.piCongrLeft_apply_apply d (β := fun _ => Circle) y k
    exact (h (j,i)).symm
  rw [hblock]
  rw [← Measure.map_map c.measurable e.measurable]
  have he : productHaar.map e = Measure.infinitePi (fun _ : ℕ × Fin (m+1) => circleHaar) :=
    Measure.infinitePi_map_piCongrLeft (fun _ : ℕ × Fin (m+1) => circleHaar) (Nat.divModEquiv _)
  rw [he]
  exact Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin (m+1)) => circleHaar)

private theorem ae_iid_hit {B : Type*} [MeasurableSpace B] (μ : Measure B)
    [IsProbabilityMeasure μ] {U : Set B} (hU : MeasurableSet U) (hp : 0 < μ U) :
    ∀ᵐ b ∂Measure.infinitePi (fun _ : ℕ => μ), ∃ j, b j ∈ U := by
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  have hc : μ Uᶜ < 1 := by
    rw [measure_compl hU (measure_ne_top _ _), measure_univ]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp.ne'
  rw [ae_iff]
  apply bot_unique
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc)
  intro k
  calc
    P {x | ¬∃ j, x j ∈ U} ≤ P ((Finset.range k : Set ℕ).pi (fun _ => Uᶜ)) :=
      measure_mono fun x hx i _ hi => hx ⟨i,hi⟩
    _ = (μ Uᶜ)^k := by
      rw [Measure.infinitePi_pi _ (fun i _ => hU.compl)]
      simp

private theorem block_openPos (m : ℕ) : (blockHaar m).IsOpenPosMeasure := by
  have : (blockHaar m).IsMulLeftInvariant := by
    constructor
    intro y
    change (blockHaar m).map (fun x i => y i * x i) = blockHaar m
    rw [Measure.infinitePi_map_pi _ (fun i => measurable_const_mul (y i))]
    simp only [map_mul_left_eq_self]
  exact isOpenPosMeasure_of_mulLeftInvariant_of_compact (μ := blockHaar m)
    univ isCompact_univ (by simp)

private theorem ae_shift_hits {U : Set Chain} (hU : IsOpen U) (hn : U.Nonempty) :
    ∀ᵐ y ∂productHaar, ∃ j, shift j y ∈ U := by
  classical
  obtain ⟨x,hx⟩ := hn
  obtain ⟨_, ⟨V,F,hV,rfl⟩, hxF, hsub⟩ :=
    (isTopologicalBasis_pi fun _ : ℕ => isTopologicalBasis_opens).exists_subset_of_mem_open hx hU
  obtain ⟨m,hm⟩ := Finset.bddAbove F
  let W : Set (Fin (m+1) → Circle) :=
    (univ : Set (Fin (m+1))).pi (fun i => if i.val ∈ F then V i.val else univ)
  have hw : IsOpen W := by
    apply isOpen_set_pi finite_univ
    intro i _
    split_ifs with hi
    · exact hV _ hi
    · exact isOpen_univ
  have hne : W.Nonempty := by
    refine ⟨fun i => x i, fun i _ => ?_⟩
    change x i.val ∈ (if i.val ∈ F then V i.val else univ)
    split_ifs with hi
    · exact hxF _ hi
    · exact mem_univ _
  have := block_openPos m
  have hhit := ae_iid_hit (blockHaar m) hw.measurableSet (hw.measure_pos _ hne)
  rw [← consecutiveBlocks_map] at hhit
  have hc : Continuous (consecutiveBlocks m) :=
    continuous_pi fun j => continuous_pi fun i => continuous_apply (j*(m+1)+i)
  filter_upwards [ae_of_ae_map hc.measurable.aemeasurable hhit] with y hy
  obtain ⟨j,hj⟩ := hy
  refine ⟨j*(m+1), hsub (fun i hi => ?_)⟩
  let k : Fin (m+1) := ⟨i, Nat.lt_succ_of_le (hm hi)⟩
  have h := hj k (mem_univ _)
  change y (j*(m+1)+i) ∈ (if i ∈ F then V i else univ) at h
  simpa only [if_pos (show i ∈ F from hi), shift] using h

theorem ae_dense_shift_orbit : ∀ᵐ y ∂productHaar, DenseRange (fun j : ℕ => shift j y) := by
  obtain ⟨B,hc,he,hB⟩ := exists_countable_basis Chain
  have := hc.to_subtype
  have h : ∀ᵐ y ∂productHaar, ∀ V : B, ∃ j, shift j y ∈ V.val := by
    apply ae_all_iff.2
    intro V
    exact ae_shift_hits (hB.isOpen V.property)
      (Set.nonempty_iff_ne_empty.2 fun h => he (h ▸ V.property))
  filter_upwards [h] with y hy
  apply dense_iff_inter_open.2
  intro U hu hn
  obtain ⟨x,hx⟩ := hn
  obtain ⟨V,hV,_,hsub⟩ := hB.exists_subset_of_mem_open hx hu
  obtain ⟨j,hj⟩ := hy ⟨V,hV⟩
  exact ⟨_,hsub hj,j,rfl⟩

end RiemannResearch.Analysis.RatioChainHaar

namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open RatioChainHaar CompactGaugeOrbitLaw
open scoped RiemannResearch.Analysis.RatioChainHaar
local instance ratioShiftTorusMeasurable : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance ratioShiftTorusBorel : BorelSpace PrimeTorus := ⟨rfl⟩
local instance ratioShiftPairMeasurable : MeasurableSpace (PrimeTorus × PrimeTorus) := borel _
local instance ratioShiftPairBorel : BorelSpace (PrimeTorus × PrimeTorus) := ⟨rfl⟩

theorem diagonal_ratios_ae_dense_shift :
    ∀ᵐ z ∂(diagonalHaar : Measure (PrimeTorus × PrimeTorus)),
      DenseRange (fun j : ℕ => shift j (primeRatios z.1)) := by
  have h := ae_dense_shift_orbit
  rw [← diagonal_primeRatios_map] at h
  have hm : Measurable (fun z : PrimeTorus × PrimeTorus => primeRatios z.1) :=
    (continuous_primeRatios.comp continuous_fst).measurable
  exact ae_of_ae_map hm.aemeasurable h

/-- Along the prime index at one fixed height, adjacent prime phases become
equal in the limit since the ratio of successive numerical primes tends to one. -/
theorem fixed_height_ratio_tail (t : ℝ) :
    Tendsto (primeRatios (phasePoint t)) atTop (𝓝 1) := by
  have hstep (n : ℕ) :
      logPrimeStep (orderedPrime n) (orderedPrime (n+1)) =
        PrimeOrbitPairLawDistinction.primeLogStep n := by
    unfold PrimeOrbitPairLawDistinction.primeLogStep
    change Real.log (orderedPrime (n+1) : ℕ) - Real.log (orderedPrime n : ℕ) =
      Real.log ((orderedPrime (n+1) : ℕ) / (orderedPrime n : ℕ) : ℝ)
    exact (Real.log_div (by exact_mod_cast (orderedPrime (n+1)).property.ne_zero)
      (by exact_mod_cast (orderedPrime n).property.ne_zero)).symm
  have hs : Tendsto PrimeOrbitPairLawDistinction.primeLogStep atTop (𝓝 0) :=
    (continuous_fst.tendsto (0,0)).comp
      PrimeOrbitPairLawDistinction.consecutivePrimeLogSteps_tendsto
  change Tendsto (fun n => backwardPhase (orderedPrime n) (orderedPrime (n+1)) t) atTop (𝓝 1)
  simp only [backwardPhase_eq_exp, hstep]
  simpa only [Function.comp_def, zero_mul, neg_zero, Circle.exp_zero] using
    (Circle.exp.continuous.tendsto _).comp (hs.mul_const t).neg

theorem fixed_height_shift_tendsto (t : ℝ) :
    Tendsto (fun j : ℕ => shift j (primeRatios (phasePoint t))) atTop (𝓝 (1 : Chain)) :=
  tendsto_pi_nhds.2 fun k => (fixed_height_ratio_tail t).comp (tendsto_add_atTop_nat k)

theorem fixed_height_shift_not_dense (t : ℝ) :
    ¬ DenseRange (fun j : ℕ => shift j (primeRatios (phasePoint t))) := by
  intro hd
  have hev : Function.Surjective (fun y : Chain => y 0) := fun z => ⟨fun _ => z,rfl⟩
  have hr : DenseRange (primeRatios (phasePoint t)) := by
    simpa only [Function.comp_def, shift, Nat.add_zero] using
      hev.denseRange.comp hd (continuous_apply 0)
  let S := insert 1 (range (primeRatios (phasePoint t)))
  have hclosed : IsClosed S := (fixed_height_ratio_tail t).isCompact_insert_range.isClosed
  have hfull : univ ⊆ S := by
    rw [← hr.closure_eq]
    exact closure_minimal (subset_insert _ _) hclosed
  have := circleHaar_nullSingleton
  have hz : circleHaar S = 0 := ((countable_range _).insert _).measure_zero circleHaar
  have hle := measure_mono (μ := circleHaar) hfull
  rw [measure_univ, hz] at hle
  exact one_ne_zero (le_antisymm hle bot_le)

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
