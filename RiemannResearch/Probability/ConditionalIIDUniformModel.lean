/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalUniformMixture
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Uniform

/-!
# A common probability space for the conditional iid uniform-interval model

The latent index `k : ℕ` represents the strictly positive endpoint `k + 1`.
In particular the scalar value `mixtureWeight 0` is never assigned probability.
The sequence coordinate is genuinely countably infinite.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace RiemannResearch.Probability.ConditionalIID

open RH.ArithmeticCumulative

abbrev Path := ℕ → ℕ
abbrev Omega := ℕ × Path

/-- The endpoint is encoded by its predecessor to avoid a spurious zero atom. -/
def latentPMF : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (mixtureWeight (k + 1)), by
    have h : (∑' k : ℕ, ENNReal.ofReal (mixtureWeight (k + 1))) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun k => mixtureWeight_nonneg (k + 1)) hasSum_mixtureWeight.summable,
        hasSum_mixtureWeight.tsum_eq]
      simp
    rw [← h]
    exact ENNReal.summable.hasSum⟩

def latentLaw : Measure ℕ := latentPMF.toMeasure

instance : IsProbabilityMeasure latentLaw := by
  unfold latentLaw
  infer_instance

def uniformPMF (k : ℕ) : PMF ℕ :=
  PMF.uniformOfFinset (Finset.Icc 1 (k + 1))
    ⟨1, by simp⟩

def uniformLaw (k : ℕ) : Measure ℕ := (uniformPMF k).toMeasure

instance (k : ℕ) : IsProbabilityMeasure (uniformLaw k) := by
  unfold uniformLaw
  infer_instance

def pathLaw (k : ℕ) : Measure Path :=
  Measure.infinitePi (fun _ : ℕ => uniformLaw k)

instance (k : ℕ) : IsProbabilityMeasure (pathLaw k) := by
  unfold pathLaw
  infer_instance

def pathKernel : Kernel ℕ Path :=
  ⟨pathLaw, measurable_of_countable _⟩

instance : IsMarkovKernel pathKernel := by
  constructor
  intro k
  change IsProbabilityMeasure (pathLaw k)
  infer_instance

def probability : Measure Omega := latentLaw.compProd pathKernel

instance : IsProbabilityMeasure probability := by
  unfold probability
  infer_instance

def latentIndex (ω : Omega) : ℕ := ω.1
def endpoint (ω : Omega) : ℕ := ω.1 + 1
abbrev coordinate (i : ℕ) (ω : Omega) : ℕ := ω.2 i

theorem endpoint_pos (ω : Omega) : 0 < endpoint ω := Nat.succ_pos _

theorem latentIndex_measurable : Measurable latentIndex := measurable_fst

theorem coordinate_measurable (i : ℕ) : Measurable (coordinate i) :=
  (measurable_pi_apply i).comp measurable_snd

abbrev latentSigma : MeasurableSpace Omega :=
  MeasurableSpace.comap latentIndex inferInstance

theorem latentSigma_le : latentSigma ≤ (inferInstance : MeasurableSpace Omega) :=
  latentIndex_measurable.comap_le

theorem latentLaw_singleton (k : ℕ) :
    latentLaw {k} = ENNReal.ofReal (mixtureWeight (k + 1)) := by
  exact PMF.toMeasure_apply_singleton latentPMF k (measurableSet_singleton k)

theorem map_latentIndex : Measure.map latentIndex probability = latentLaw := by
  change probability.fst = latentLaw
  exact Measure.fst_compProd latentLaw pathKernel

theorem uniformLaw_apply (k : ℕ) (s : Set ℕ) :
    uniformLaw k s =
      ((Finset.Icc 1 (k + 1)).filter (fun n => n ∈ s)).card / (k + 1 : ℝ≥0∞) := by
  classical
  simpa [uniformLaw, uniformPMF, Nat.card_Icc] using
    PMF.toMeasure_uniformOfFinset_apply
      (s := Finset.Icc 1 (k + 1)) ⟨1, by simp⟩ s (Set.to_countable s).measurableSet

theorem pathLaw_cylinder (k : ℕ) (I : Finset ℕ) (s : ℕ → Set ℕ) :
    pathLaw k ((I : Set ℕ).pi s) = ∏ i ∈ I, uniformLaw k (s i) := by
  exact Measure.infinitePi_pi _ (fun _ _ => (Set.to_countable _).measurableSet)

theorem pathLaw_iIndepFun (k : ℕ) :
    iIndepFun (fun i (x : Path) => x i) (pathLaw k) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

/-- A finite cylinder law on the actual common infinite product space. -/
theorem joint_latent_cylinder (k : ℕ) (I : Finset ℕ) (s : ℕ → Set ℕ) :
    probability ({k} ×ˢ (I : Set ℕ).pi s) =
      ENNReal.ofReal (mixtureWeight (k + 1)) * ∏ i ∈ I, uniformLaw k (s i) := by
  have hs : MeasurableSet ((I : Set ℕ).pi s) :=
    MeasurableSet.pi (I.countable_toSet) (fun _ _ => (Set.to_countable _).measurableSet)
  rw [probability, Measure.compProd_apply_prod (measurableSet_singleton k) hs,
    lintegral_singleton, latentLaw_singleton]
  change pathLaw k ((I : Set ℕ).pi s) * _ = _
  rw [pathLaw_cylinder, mul_comm]


/-- The conditional law of the entire infinite row sequence is the prescribed product law. -/
theorem conditional_path_law :
    (fun k => condDistrib (Prod.snd : Omega → Path) latentIndex probability k) =ᵐ[
      Measure.map latentIndex probability] pathLaw := by
  change ⇑(condDistrib (Prod.snd : Omega → Path) latentIndex probability)
    =ᵐ[Measure.map latentIndex probability] ⇑pathKernel
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := probability) (κ := pathKernel) latentIndex_measurable measurable_snd
  have hid : (fun x : Omega => (latentIndex x, x.2)) = id := rfl
  rw [hid, Measure.map_id, map_latentIndex]
  rfl

/-- Pull the kernel identity back to the common probability space. -/
theorem conditional_path_law_ae :
    (fun ω => condDistrib (Prod.snd : Omega → Path) latentIndex probability (latentIndex ω))
      =ᵐ[probability] (fun ω => pathLaw (latentIndex ω)) :=
  ae_of_ae_map latentIndex_measurable.aemeasurable conditional_path_law

/-- Conditional probabilities for arbitrary measurable events of the entire path. -/
theorem conditional_path_event (B : Set Path) (hB : MeasurableSet B) :
    probability[(Prod.snd ⁻¹' B).indicator (fun _ : Omega => (1 : ℝ)) | latentSigma]
      =ᵐ[probability] (fun ω => (pathLaw (latentIndex ω)).real B) := by
  have h := (condDistrib_ae_eq_condExp
    (μ := probability) latentIndex_measurable measurable_snd hB).symm
  filter_upwards [h, conditional_path_law_ae] with ω hω hk
  change _ = (pathLaw (latentIndex ω)).real B
  rw [hω, hk]

/-- Each coordinate has the same conditional uniform law. -/
theorem conditional_coordinate_event (i : ℕ) (B : Set ℕ) :
    probability[(coordinate i ⁻¹' B).indicator (fun _ : Omega => (1 : ℝ)) | latentSigma]
      =ᵐ[probability] (fun ω => (uniformLaw (latentIndex ω)).real B) := by
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  have h := conditional_path_event ((fun x : Path => x i) ⁻¹' B)
    (hB.preimage (measurable_pi_apply i))
  filter_upwards [h] with ω hω
  change probability[(Prod.snd ⁻¹' ((fun x : Path => x i) ⁻¹' B)).indicator
    (fun _ : Omega => (1 : ℝ)) | latentSigma] ω = _
  rw [hω]
  unfold Measure.real
  congr 1
  have he := Measure.infinitePi_map_eval (fun _ : ℕ => uniformLaw (latentIndex ω)) i
  rw [← he, Measure.map_apply (measurable_pi_apply i) hB]
  rfl

/-- Actual mathlib conditional independence, not an algebraic surrogate. -/
theorem coordinates_iCondIndepFun :
    iCondIndepFun latentSigma latentSigma_le coordinate probability := by
  apply (iCondIndepFun_iff_condExp_inter_preimage_eq_mul
    (fun _ : ℕ => inferInstance) coordinate coordinate_measurable).2
  intro I sets hsets
  have hB : MeasurableSet ((I : Set ℕ).pi sets) :=
    MeasurableSet.pi I.countable_toSet (fun i hi => hsets i hi)
  have he : (⋂ i ∈ I, coordinate i ⁻¹' sets i) =
      Prod.snd ⁻¹' ((I : Set ℕ).pi sets) := by
    ext ω
    simp [Set.mem_pi, coordinate]
  rw [he]
  have hcond := conditional_path_event ((I : Set ℕ).pi sets) hB
  have hsingle : ∀ᵐ ω ∂probability, ∀ i : ℕ,
      probability[(coordinate i ⁻¹' sets i).indicator (fun _ : Omega => (1 : ℝ)) |
        latentSigma] ω = (uniformLaw (latentIndex ω)).real (sets i) :=
    ae_all_iff.mpr (fun i => conditional_coordinate_event i (sets i))
  filter_upwards [hcond, hsingle] with ω hω hs
  rw [hω]
  simp only [Finset.prod_apply]
  simp_rw [hs]
  simp only [Measure.real, pathLaw_cylinder, ENNReal.toReal_prod]

/-- Measurable path observables have the actual conditional expectation prescribed by the kernel. -/
theorem conditional_path_expectation (F : Path → ℝ) (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω : Omega => F ω.2) probability) :
    probability[(fun ω : Omega => F ω.2) | latentSigma] =ᵐ[probability]
      (fun ω => ∫ x, F x ∂pathLaw (latentIndex ω)) := by
  have h := condExp_ae_eq_integral_condDistrib latentIndex_measurable
    measurable_snd.aemeasurable hF hFi
  filter_upwards [h, conditional_path_law_ae] with ω hω hk
  rw [hω, hk]

end RiemannResearch.Probability.ConditionalIID
