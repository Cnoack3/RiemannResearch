/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QUniformMixture
import RiemannResearch.Probability.ConditionalIIDUniformModel
import RiemannResearch.Probability.ConditionalIIDUniformMoments
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# The same conditional iid Cesàro model with inverse-square marginals

Source: the user's P/Q change-of-measure question, 1 November 2026.
Only the latent endpoint law changes. The conditional path kernel remains the
same infinite iid product of uniform laws on `1,...,t`. The Q marginal and
conditional independence are theorems about the constructed probability measure.
The cylinder identity retains the exact likelihood ratio.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.QConditionalIID
open ConditionalIID
open RH.QUniformMixture RH.ZetaTwoHilbert RH.ZetaTwoProbability

/-- The endpoint is encoded by its predecessor, as in the Pareto model. -/
def latentPMF : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (qMixtureWeight (k + 1)), by
    have h : (∑' k : ℕ, ENNReal.ofReal (qMixtureWeight (k + 1))) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun k => qMixtureWeight_nonneg (k + 1)) hasSum_qMixtureWeight.summable,
        hasSum_qMixtureWeight.tsum_eq]
      simp
    rw [← h]
    exact ENNReal.summable.hasSum⟩

def latentLaw : Measure ℕ := latentPMF.toMeasure

instance : IsProbabilityMeasure latentLaw := by
  unfold latentLaw
  infer_instance

/-- Reweight the endpoint, retaining the full existing conditional iid kernel. -/
def probability : Measure Omega := latentLaw.compProd pathKernel

instance : IsProbabilityMeasure probability := by
  unfold probability
  infer_instance

theorem latentLaw_singleton (k : ℕ) :
    latentLaw {k} = ENNReal.ofReal (qMixtureWeight (k + 1)) := by
  exact PMF.toMeasure_apply_singleton latentPMF k (measurableSet_singleton k)

/-- The likelihood ratio depends only on the latent endpoint, not on the rows. -/
def likelihoodRatio (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (qMixtureWeight (k + 1) /
    RH.ArithmeticCumulative.mixtureWeight (k + 1))

theorem likelihoodRatio_pos (k : ℕ) : 0 < likelihoodRatio k := by
  apply ENNReal.ofReal_pos.mpr
  have hZ := zetaTwo_pos
  unfold qMixtureWeight RH.ArithmeticCumulative.mixtureWeight
  positivity

/-- Uniform bounds on the true density, with no squarefree or arithmetic premise. -/
theorem likelihoodRatio_bounds (k : ℕ) :
    ENNReal.ofReal (1 / zetaTwo) ≤ likelihoodRatio k ∧
      likelihoodRatio k ≤ ENNReal.ofReal (9 / (4 * zetaTwo)) := by
  have hZ := zetaTwo_pos
  have hp : 0 < RH.ArithmeticCumulative.mixtureWeight (k + 1) := by
    unfold RH.ArithmeticCumulative.mixtureWeight
    positivity
  have hc := latent_weight_comparison (k + 1) (Nat.succ_pos k)
  have hlo : 1 / zetaTwo ≤ qMixtureWeight (k + 1) /
      RH.ArithmeticCumulative.mixtureWeight (k + 1) := by
    apply (div_le_div_iff₀ zetaTwo_pos hp).mpr
    nlinarith [hc.2]
  have hhi : qMixtureWeight (k + 1) /
      RH.ArithmeticCumulative.mixtureWeight (k + 1) ≤ 9 / (4 * zetaTwo) := by
    apply (div_le_div_iff₀ hp (by positivity : 0 < 4 * zetaTwo)).mpr
    nlinarith [hc.1]
  exact ⟨ENNReal.ofReal_le_ofReal hlo, ENNReal.ofReal_le_ofReal hhi⟩

/-- Exact Radon–Nikodym identity on the discrete latent space. -/
theorem latentLaw_eq_withDensity :
    latentLaw = ConditionalIID.latentLaw.withDensity likelihoodRatio := by
  apply Measure.ext_of_singleton
  intro k
  have hp : 0 < RH.ArithmeticCumulative.mixtureWeight (k + 1) := by
    unfold RH.ArithmeticCumulative.mixtureWeight
    positivity
  have hne : ENNReal.ofReal (RH.ArithmeticCumulative.mixtureWeight (k + 1)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  rw [latentLaw_singleton, withDensity_apply _ (measurableSet_singleton k),
    lintegral_singleton, ConditionalIID.latentLaw_singleton, likelihoodRatio,
    ENNReal.ofReal_div_of_pos hp, ENNReal.div_mul_cancel hne ENNReal.ofReal_ne_top]

/-- The actual full path law is obtained by tilting only the endpoint. -/
theorem probability_eq_withDensity :
    probability = ConditionalIID.probability.withDensity
      (fun ω => likelihoodRatio (latentIndex ω)) := by
  have hR : Measurable (fun ω : Omega => likelihoodRatio (latentIndex ω)) :=
    (measurable_of_countable likelihoodRatio).comp latentIndex_measurable
  apply Measure.ext
  intro s hs
  rw [probability, Measure.compProd_apply hs, latentLaw_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    ConditionalIID.probability, Measure.lintegral_compProd (hR.indicator hs)]
  apply lintegral_congr
  intro k
  change likelihoodRatio k * pathLaw k (Prod.mk k ⁻¹' s) =
    ∫⁻ x : Path, s.indicator (fun ω => likelihoodRatio (latentIndex ω)) (k, x) ∂pathLaw k
  have he : (fun x : Path =>
      s.indicator (fun ω => likelihoodRatio (latentIndex ω)) (k, x)) =
      (Prod.mk k ⁻¹' s).indicator (fun _ => likelihoodRatio k) := by
    funext x
    rfl
  rw [he, lintegral_indicator_const (hs.preimage measurable_prodMk_left)]

/-- The two full infinite-path laws have precisely the same almost-sure properties. -/
theorem probability_ae_iff (p : Omega → Prop) :
    (∀ᵐ ω ∂probability, p ω) ↔ ∀ᵐ ω ∂ConditionalIID.probability, p ω := by
  rw [probability_eq_withDensity]
  have hR : Measurable (fun ω : Omega => likelihoodRatio (latentIndex ω)) :=
    (measurable_of_countable likelihoodRatio).comp latentIndex_measurable
  rw [ae_withDensity_iff hR]
  constructor
  · intro h
    filter_upwards [h] with ω hω
    exact hω (ne_of_gt (likelihoodRatio_pos _))
  · intro h
    filter_upwards [h] with ω hω
    exact fun _ => hω


theorem map_latentIndex : Measure.map latentIndex probability = latentLaw := by
  change probability.fst = latentLaw
  exact Measure.fst_compProd latentLaw pathKernel

/-- The complete finite cylinder mass under Q. -/
theorem joint_latent_cylinder (k : ℕ) (I : Finset ℕ) (s : ℕ → Set ℕ) :
    probability ({k} ×ˢ (I : Set ℕ).pi s) =
      ENNReal.ofReal (qMixtureWeight (k + 1)) * ∏ i ∈ I, uniformLaw k (s i) := by
  have hs : MeasurableSet ((I : Set ℕ).pi s) :=
    MeasurableSet.pi I.countable_toSet (fun _ _ => (Set.to_countable _).measurableSet)
  rw [probability, Measure.compProd_apply_prod (measurableSet_singleton k) hs,
    lintegral_singleton, latentLaw_singleton]
  change pathLaw k ((I : Set ℕ).pi s) * _ = _
  rw [pathLaw_cylinder, mul_comm]

/-- Exact change of measure on every joint latent/path cylinder. -/
theorem joint_latent_cylinder_change_of_measure
    (k : ℕ) (I : Finset ℕ) (s : ℕ → Set ℕ) :
    probability ({k} ×ˢ (I : Set ℕ).pi s) =
      ENNReal.ofReal (qMixtureWeight (k + 1) /
        RH.ArithmeticCumulative.mixtureWeight (k + 1)) *
          ConditionalIID.probability ({k} ×ˢ (I : Set ℕ).pi s) := by
  have hp : 0 < RH.ArithmeticCumulative.mixtureWeight (k + 1) := by
    unfold RH.ArithmeticCumulative.mixtureWeight
    positivity
  rw [joint_latent_cylinder, ConditionalIID.joint_latent_cylinder,
    ENNReal.ofReal_div_of_pos hp]
  have hne : ENNReal.ofReal (RH.ArithmeticCumulative.mixtureWeight (k + 1)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  rw [← mul_assoc, ENNReal.div_mul_cancel hne ENNReal.ofReal_ne_top]

/-- The entire conditional path distribution is unchanged by this reweighting. -/
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

theorem conditional_path_law_ae :
    (fun ω => condDistrib (Prod.snd : Omega → Path) latentIndex probability (latentIndex ω))
      =ᵐ[probability] (fun ω => pathLaw (latentIndex ω)) :=
  ae_of_ae_map latentIndex_measurable.aemeasurable conditional_path_law

theorem conditional_path_event (B : Set Path) (hB : MeasurableSet B) :
    probability[(Prod.snd ⁻¹' B).indicator (fun _ : Omega => (1 : ℝ)) | latentSigma]
      =ᵐ[probability] (fun ω => (pathLaw (latentIndex ω)).real B) := by
  have h := (condDistrib_ae_eq_condExp
    (μ := probability) latentIndex_measurable measurable_snd hB).symm
  filter_upwards [h, conditional_path_law_ae] with ω hω hk
  rw [hω, hk]

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

/-- Actual Mathlib conditional independence under the Q common-space law. -/
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

theorem conditional_path_expectation (F : Path → ℝ) (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω : Omega => F ω.2) probability) :
    probability[(fun ω : Omega => F ω.2) | latentSigma] =ᵐ[probability]
      (fun ω => ∫ x, F x ∂pathLaw (latentIndex ω)) := by
  have h := condExp_ae_eq_integral_condDistrib latentIndex_measurable
    measurable_snd.aemeasurable hF hFi
  filter_upwards [h, conditional_path_law_ae] with ω hω hk
  rw [hω, hk]

/-- Ordinary Cesàro is the actual Q conditional mean as well as the P one. -/
theorem conditional_coordinate_expectation (i : ℕ) (F : ℕ → ℝ)
    (hF : Integrable (fun ω => F (coordinate i ω)) probability) :
    probability[(fun ω => F (coordinate i ω)) | latentSigma] =ᵐ[probability]
      (fun ω => cesaro F (endpoint ω)) := by
  have hm : StronglyMeasurable (fun x : Path => F (x i)) :=
    ((measurable_of_countable F).comp (measurable_pi_apply i)).stronglyMeasurable
  have h := conditional_path_expectation (fun x => F (x i)) hm hF
  filter_upwards [h] with ω hω
  rw [hω, path_integral_coordinate]
  rfl

theorem coordinate_event_integral (i : ℕ) (B : Set ℕ) :
    probability (coordinate i ⁻¹' B) = ∫⁻ k, uniformLaw k B ∂latentLaw := by
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  rw [probability, Measure.compProd_apply (hB.preimage (coordinate_measurable i))]
  apply lintegral_congr
  intro k
  change pathLaw k ((fun x : Path => x i) ⁻¹' B) = uniformLaw k B
  rw [← Measure.infinitePi_map_eval (fun _ : ℕ => uniformLaw k) i,
    Measure.map_apply (measurable_pi_apply i) hB]
  rfl

private def marginalTerm (n k : ℕ) : ℝ :=
  if n ≤ k + 1 then qMixtureWeight (k + 1) / ((k + 1 : ℕ) : ℝ) else 0

private theorem marginalTerm_nonneg (n k : ℕ) : 0 ≤ marginalTerm n k := by
  unfold marginalTerm
  split_ifs
  · exact div_nonneg (qMixtureWeight_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

private theorem hasSum_marginalTerm (m : ℕ) :
    HasSum (marginalTerm (m + 1)) (positiveQWeight (m + 1)) := by
  have he : (fun k => marginalTerm (m + 1) (k + m)) =
      (fun k => qMixtureWeight ((m + 1) + k) / (((m + 1) + k : ℕ) : ℝ)) := by
    funext k
    unfold marginalTerm
    rw [if_pos (by omega)]
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have ht : HasSum (fun k => marginalTerm (m + 1) (k + m))
      (positiveQWeight (m + 1)) := by
    rw [he]
    exact RH.QUniformMixture.hasSum_uniform_mixture_marginal _ (Nat.succ_pos _)
  have hs : Summable (marginalTerm (m + 1)) :=
    (summable_nat_add_iff m).mp ht.summable
  have hz : ∑ k ∈ Finset.range m, marginalTerm (m + 1) k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkm : k < m := Finset.mem_range.mp hk
    simp [marginalTerm, show ¬ m + 1 ≤ k + 1 by omega]
  have hsum := Summable.sum_add_tsum_nat_add m hs
  rw [hz, zero_add, ht.tsum_eq] at hsum
  simpa only [hsum.symm] using hs.hasSum

theorem coordinate_zero_mass (i : ℕ) : probability (coordinate i ⁻¹' {0}) = 0 := by
  rw [coordinate_event_integral]
  simp [uniformLaw_singleton]

/-- The exact Q marginal, including the entire latent tail. -/
theorem coordinate_positive_mass (i m : ℕ) :
    probability (coordinate i ⁻¹' {m + 1}) =
      ENNReal.ofReal (positiveQWeight (m + 1)) := by
  rw [coordinate_event_integral, lintegral_countable']
  have he : (fun k => uniformLaw k {m + 1} * latentLaw {k}) =
      (fun k => ENNReal.ofReal (marginalTerm (m + 1) k)) := by
    funext k
    rw [latentLaw_singleton, uniformLaw_singleton]
    by_cases hk : m + 1 ≤ k + 1
    · rw [if_pos ⟨by omega, hk⟩]
      unfold marginalTerm
      rw [if_pos hk, ENNReal.ofReal_div_of_pos (by positivity)]
      simp [div_eq_mul_inv, mul_comm, ENNReal.ofReal_add, Nat.cast_nonneg]
    · rw [if_neg (by omega)]
      simp [marginalTerm, hk]
  rw [he, ← ENNReal.ofReal_tsum_of_nonneg (marginalTerm_nonneg (m + 1))
    (hasSum_marginalTerm m).summable, (hasSum_marginalTerm m).tsum_eq]

theorem coordinate_mass_eq_Q_singleton (i m : ℕ) :
    probability (coordinate i ⁻¹' {m + 1}) =
      Q {⟨m + 1, Nat.succ_pos m⟩} := by
  rw [coordinate_positive_mass, measure_singleton]
  rfl

end RiemannResearch.Probability.QConditionalIID
