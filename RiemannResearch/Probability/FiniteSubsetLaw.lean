import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Finset.Card

/-!
# Finite subset laws are determined by inclusion probabilities

The finite upper-set sum transform is injective by descending induction.
Transport through Boolean support gives the same uniqueness for finite Boolean
configurations. Source: elementary finite inclusion-exclusion principle;
consumer: consistency of finite determinantal probability laws.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace RiemannResearch.Probability.FiniteSubsetLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite upper-set zeta transform is injective, using descending induction.
This version deliberately lives in real functions to avoid ENNReal subtraction. -/
theorem eq_of_superset_sums_eq (p q : Finset ι → ℝ)
    (h : ∀ T : Finset ι,
      (∑ S : Finset ι, if T ⊆ S then p S else 0) =
        ∑ S : Finset ι, if T ⊆ S then q S else 0) : p = q := by
  have hz (T : Finset ι) :
      (∑ S : Finset ι, if T ⊆ S then p S - q S else 0) = 0 := by
    calc
      _ = (∑ S : Finset ι, if T ⊆ S then p S else 0) -
          ∑ S : Finset ι, if T ⊆ S then q S else 0 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hTS : T ⊆ S <;> simp [hTS]
      _ = 0 := sub_eq_zero.mpr (h T)
  have hpq (T : Finset ι) : p T - q T = 0 := by
    refine Finset.strongDownwardInduction (p := fun U => p U - q U = 0) (n := Fintype.card ι) ?_
      T (Finset.card_le_univ T)
    intro U ih hU
    have hsum :
        (∑ S : Finset ι, if U ⊆ S then p S - q S else 0) = p U - q U := by
      rw [Finset.sum_eq_single U]
      · simp
      · intro S hS hSU
        by_cases hUS : U ⊆ S
        · rw [if_pos hUS]
          exact ih (Finset.card_le_univ S)
            (Finset.ssubset_iff_subset_ne.mpr ⟨hUS, Ne.symm hSU⟩)
        · simp [hUS]
      · simp
    rw [← hsum]
    exact hz U
  funext T
  exact sub_eq_zero.mp (hpq T)

variable [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

theorem sum_singletons_superset (μ : Measure (Finset ι)) [SigmaFinite μ]
    (T : Finset ι) :
    (∑ S : Finset ι, if T ⊆ S then μ.real {S} else 0) =
      μ.real {S | T ⊆ S} := by
  simpa [Finset.sum_filter] using
    (sum_measureReal_singleton (μ := μ)
      (Finset.univ.filter fun S : Finset ι => T ⊆ S))

/-- A finite random subset law is determined by all inclusion probabilities. -/
theorem measure_eq_of_inclusion_eq (μ ν : Measure (Finset ι))
    [SigmaFinite μ] [SigmaFinite ν]
    (h : ∀ T : Finset ι, μ.real {S | T ⊆ S} = ν.real {S | T ⊆ S}) :
    μ = ν := by
  apply ext_iff_measureReal_singleton.mpr
  have hpq : (fun S : Finset ι => μ.real {S}) =
      (fun S : Finset ι => ν.real {S}) := by
    apply eq_of_superset_sums_eq
    intro T
    rw [sum_singletons_superset, sum_singletons_superset]
    exact h T
  intro S
  exact congrFun hpq S

end RiemannResearch.Probability.FiniteSubsetLaw

namespace RiemannResearch.Probability.FiniteSubsetLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Same uniqueness theorem for finite Boolean configurations, which is the
representation expected by Kolmogorov extension. -/
theorem boolMeasure_eq_of_inclusion_eq
    (μ ν : Measure (ι → Bool)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ T : Finset ι,
      μ.real {x | ∀ i ∈ T, x i = true} =
        ν.real {x | ∀ i ∈ T, x i = true}) : μ = ν := by
  letI : MeasurableSpace (Finset ι) := ⊤
  let c : (ι → Bool) → Finset ι := fun x => Finset.univ.filter (fun i => x i = true)
  let d : Finset ι → (ι → Bool) := fun S i => decide (i ∈ S)
  have hc : Measurable c := measurable_of_finite c
  have hd : Measurable d := measurable_of_finite d
  have hdc : d ∘ c = id := by
    funext x i
    cases hx : x i <;> simp [c, d, hx]
  have hevent (T : Finset ι) :
      c ⁻¹' {S : Finset ι | T ⊆ S} = {x | ∀ i ∈ T, x i = true} := by
    ext x
    simp [c, Finset.subset_iff]
  have hreal (ρ : Measure (ι → Bool)) (T : Finset ι) :
      (Measure.map c ρ).real {S | T ⊆ S} =
        ρ.real {x | ∀ i ∈ T, x i = true} := by
    rw [Measure.real, Measure.map_apply hc (Set.toFinite _).measurableSet, hevent]
    rfl
  have hmap : Measure.map c μ = Measure.map c ν := by
    apply measure_eq_of_inclusion_eq
    intro T
    rw [hreal, hreal]
    exact h T
  have hdmap := congrArg (Measure.map d) hmap
  simpa only [Measure.map_map hd hc, hdc, Measure.map_id] using hdmap

end RiemannResearch.Probability.FiniteSubsetLaw
