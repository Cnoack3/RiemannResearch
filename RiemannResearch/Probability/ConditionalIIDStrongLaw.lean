import RiemannResearch.Probability.ConditionalIIDLatentSupport
import RiemannResearch.Probability.ConditionalIIDSampleMean
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Strong laws and recovery of the shared latent endpoint

Source: user-provided `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 2; the proof is expanded in `ConditionalIIDExtensionsProof.md`.
All statements use the actual infinite product mixture. Fiberwise integrability
is automatic, so the pathwise strong law needs no global moment assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

theorem path_coordinates_identDistrib (k i j : ℕ) :
    IdentDistrib (fun x : Path => x i) (fun x : Path => x j) (pathLaw k) (pathLaw k) := by
  refine ⟨(measurable_pi_apply i).aemeasurable,
    (measurable_pi_apply j).aemeasurable, ?_⟩
  exact (Measure.infinitePi_map_eval (fun _ : ℕ => uniformLaw k) i).trans
    (Measure.infinitePi_map_eval (fun _ : ℕ => uniformLaw k) j).symm

/-- Every real arithmetic function satisfies the ordinary strong law on each finite fiber. -/
theorem pathAverage_strongLaw (k : ℕ) (F : ℕ → ℝ) :
    ∀ᵐ x ∂pathLaw k,
      Tendsto (fun r => pathAverage F r x) atTop (𝓝 (cesaro F (k + 1))) := by
  have hind := iIndepFun_infinitePi
    (P := fun _ : ℕ => uniformLaw k) (fun _ => measurable_of_countable F)
  have hid : ∀ i, IdentDistrib (fun x : Path => F (x i))
      (fun x : Path => F (x 0)) (pathLaw k) (pathLaw k) :=
    fun i => (path_coordinates_identDistrib k i 0).comp (measurable_of_countable F)
  have h := strong_law_ae_real (fun i (x : Path) => F (x i))
    ((path_coordinate_memLp_two k 0 F).integrable one_le_two)
    (fun i j hij => hind.indepFun hij) hid
  simpa only [path_integral_coordinate, pathAverage_apply, div_eq_mul_inv, mul_comm] using h

/-- The conditional-iid strong law on the single common probability space. -/
theorem observationAverage_strongLaw (F : ℕ → ℝ) :
    ∀ᵐ ω ∂probability,
      Tendsto (fun r => pathAverage F r ω.2) atTop (𝓝 (cesaro F (endpoint ω))) := by
  have hT : Measurable endpoint :=
    (measurable_of_countable (fun k : ℕ => k + 1)).comp latentIndex_measurable
  have hm : MeasurableSet {ω : Omega |
      Tendsto (fun r => pathAverage F r ω.2) atTop (𝓝 (cesaro F (endpoint ω)))} :=
    measurableSet_tendsto_fun
      (fun r => (pathAverage_measurable F r).comp measurable_snd)
      ((measurable_of_countable (cesaro F)).comp hT)
  unfold probability
  apply Measure.ae_compProd_of_ae_ae hm
  exact ae_of_all _ (fun k => pathAverage_strongLaw k F)

/-- One common event gives the strong law for all singleton indicators. -/
theorem all_empirical_frequencies_tendsto :
    ∀ᵐ ω ∂probability, ∀ n : ℕ,
      Tendsto (fun r => pathAverage (fun m => if m = n then 1 else 0) r ω.2)
        atTop (𝓝 (cesaro (fun m => if m = n then 1 else 0) (endpoint ω))) :=
  ae_all_iff.mpr (fun n => observationAverage_strongLaw (fun m => if m = n then 1 else 0))

theorem path_endpoint_is_observed (k : ℕ) :
    ∀ᵐ x ∂pathLaw k, ∃ i, x i = k + 1 := by
  filter_upwards [pathAverage_strongLaw k (fun n => if n = k + 1 then 1 else 0)] with x hx
  by_contra h
  have hne : ∀ i, x i ≠ k + 1 := by simpa using h
  have hz : ∀ r, pathAverage (fun n => if n = k + 1 then 1 else 0) r x = 0 := by
    intro r
    simp [pathAverage_apply, hne]
  simp_rw [hz] at hx
  have he : (0 : ℝ) = cesaro (fun n => if n = k + 1 then 1 else 0) (k + 1) :=
    tendsto_nhds_unique tendsto_const_nhds hx
  have hp : 0 < cesaro (fun n => if n = k + 1 then 1 else 0) (k + 1) := by
    have hsum : (∑ n ∈ Finset.Icc 1 (k + 1),
        (if n = k + 1 then (1 : ℝ) else 0)) = 1 := by simp
    unfold cesaro
    rw [hsum]
    positivity
  linarith

/-- The latent endpoint occurs among the rows almost surely. -/
theorem endpoint_is_observed :
    ∀ᵐ ω ∂probability, ∃ i, coordinate i ω = endpoint ω := by
  have hT : Measurable endpoint :=
    (measurable_of_countable (fun k : ℕ => k + 1)).comp latentIndex_measurable
  have hm : MeasurableSet {ω : Omega | ∃ i, coordinate i ω = endpoint ω} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun i => measurableSet_eq_fun (coordinate_measurable i) hT)
  unfold probability
  apply Measure.ae_compProd_of_ae_ae hm
  exact ae_of_all _ path_endpoint_is_observed

def runningMaximum (r : ℕ) (ω : Omega) : ℕ := (Finset.range r).sup (fun i => coordinate i ω)

/-- The running maximum recovers the actual shared endpoint after finitely many rows. -/
theorem runningMaximum_eventually_eq_endpoint :
    ∀ᵐ ω ∂probability, ∀ᶠ r in atTop, runningMaximum r ω = endpoint ω := by
  filter_upwards [all_coordinates_support, endpoint_is_observed] with ω hs he
  obtain ⟨i, hi⟩ := he
  filter_upwards [eventually_ge_atTop (i + 1)] with r hr
  apply le_antisymm
  · exact Finset.sup_le (fun j _ => (hs j).2)
  · rw [← hi]
    exact Finset.le_sup (f := fun j => coordinate j ω) (by simp; omega)

theorem cesaro_singleton_indicator (t n : ℕ) (hn : n ∈ Finset.Icc 1 t) :
    cesaro (fun m => if m = n then 1 else 0) t = 1 / (t : ℝ) := by
  simp [cesaro, hn]

/-- Finite support makes every arithmetic observation a finite combination of frequencies. -/
theorem pathAverage_eq_frequency_sum (F : ℕ → ℝ) (t r : ℕ) (x : Path)
    (hx : ∀ i, x i ∈ Finset.Icc 1 t) :
    pathAverage F r x = ∑ n ∈ Finset.Icc 1 t,
      F n * pathAverage (fun m => if m = n then 1 else 0) r x := by
  have hsplit (i : ℕ) : F (x i) = ∑ n ∈ Finset.Icc 1 t,
      F n * (if x i = n then (1 : ℝ) else 0) := by
    simp [mul_ite, hx i]
  calc
    _ = (r : ℝ)⁻¹ * ∑ i ∈ Finset.range r,
        ∑ n ∈ Finset.Icc 1 t, F n * (if x i = n then (1 : ℝ) else 0) := by
      rw [pathAverage_apply]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = _ := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [pathAverage_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- One probability-one event works for every real arithmetic observable at once.
The proof takes only a countable intersection (over singleton indicators).
-/
theorem observationAverage_strongLaw_simultaneous :
    ∀ᵐ ω ∂probability, ∀ F : ℕ → ℝ,
      Tendsto (fun r => pathAverage F r ω.2) atTop (𝓝 (cesaro F (endpoint ω))) := by
  filter_upwards [all_coordinates_support, all_empirical_frequencies_tendsto] with ω hs hf
  intro F
  have hs' : ∀ i, ω.2 i ∈ Finset.Icc 1 (endpoint ω) :=
    fun i => Finset.mem_Icc.mpr (hs i)
  have hlim := tendsto_finsetSum (Finset.Icc 1 (endpoint ω))
    (fun n hn => (hf n).const_mul (F n))
  have ht : (∑ n ∈ Finset.Icc 1 (endpoint ω),
      F n * cesaro (fun m => if m = n then 1 else 0) (endpoint ω)) =
      cesaro F (endpoint ω) := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 (endpoint ω), F n * (1 / (endpoint ω : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [cesaro_singleton_indicator _ _ hn]
      _ = _ := by simp only [cesaro, div_eq_mul_inv, one_mul, Finset.sum_mul]
  rw [ht] at hlim
  exact hlim.congr' (Filter.Eventually.of_forall (fun r =>
    (pathAverage_eq_frequency_sum F (endpoint ω) r ω.2 hs').symm))

end RiemannResearch.Probability.ConditionalIID
