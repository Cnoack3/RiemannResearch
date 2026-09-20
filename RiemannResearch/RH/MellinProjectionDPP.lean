import RiemannResearch.RH.MellinFrequencyMeasure
import RiemannResearch.RH.MellinProjectionKernel
import RiemannResearch.Probability.ContinuousProjectionKernel

/-!
# The actual finite-rank Mellin determinantal point process

Source: user-requested Mellin DPP construction, 20 September 2026, and the
finite projection density of Hough--Krishnapur--Peres--Virág, Probability
Surveys 3 (2006), Section 2, DOI 10.1214/154957806000000078.

For every rank n this constructs a probability measure on n labeled real
frequencies, symmetric under relabeling and almost surely consisting of n
distinct points. Its joint density relative to (dt/(2π))^n is the determinant
of the existing arithmetic inverse-Gram Mellin kernel divided by n!.
Orthonormality and normalization are proved from the actual Pareto space.
No RH hypothesis or unproved probability-law provider is used.

This is the finite-rank family. An infinite locally finite point process
would require additional local trace conditions and is not asserted here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.MellinFrequency
open ProbabilityTheory

def angularFeatures (n : ℕ) (i : Fin n) : ℝ → ℂ := modeFeature i.val

theorem angularFeatures_gram (n : ℕ) (i j : Fin n) :
    (∫ t, star (angularFeatures n i t) * angularFeatures n j t ∂frequencyMeasure) =
      if i = j then (1 : ℂ) else 0 := by
  simpa only [angularFeatures, Fin.val_inj] using frequencyMeasure_gram i.val j.val

theorem angularFeatures_kernel (n : ℕ) : ContinuousProjectionDPP.kernel (angularFeatures n) = kernel n := by
  funext t u
  exact (kernel_eq_mode_sum n t u).symm

/-- Actual labeled probability law of the rank-n Mellin process. -/
def mellinLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  ContinuousProjectionDPP.law frequencyMeasure (angularFeatures n)

instance mellinLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (mellinLaw n) :=
  ContinuousProjectionDPP.isProbabilityMeasure_law_of_orthonormal (angularFeatures n)
    (fun i => modeFeature_memLp i.val) (angularFeatures_gram n)

theorem mellinLaw_ae_distinct (n : ℕ) :
    ∀ᵐ x ∂mellinLaw n, Function.Injective x :=
  ContinuousProjectionDPP.ae_injective_law (ContinuousProjectionDPP.integrable_squaredDet (angularFeatures n)
    (fun i => modeFeature_memLp i.val))

/-- The unordered sampled set has exactly n frequencies almost surely. -/
theorem mellinLaw_cardinality (n : ℕ) :
    ∀ᵐ x ∂mellinLaw n, (ContinuousProjectionDPP.configuration x).card = n :=
  ContinuousProjectionDPP.ae_card_configuration (ContinuousProjectionDPP.integrable_squaredDet (angularFeatures n)
    (fun i => modeFeature_memLp i.val))

theorem mellinLaw_permutation_invariant (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Measure.map (fun x : Fin n → ℝ => x ∘ σ) (mellinLaw n) = mellinLaw n :=
  ContinuousProjectionDPP.map_law_permute frequencyMeasure (angularFeatures n) σ

def mellinJointDensity (n : ℕ) : (Fin n → ℝ) → ℝ := ContinuousProjectionDPP.density (angularFeatures n)

theorem mellinLaw_eq_withDensity (n : ℕ) :
    mellinLaw n = (Measure.pi fun _ : Fin n => frequencyMeasure).withDensity
      (fun x => ENNReal.ofReal (mellinJointDensity n x)) := rfl

/-- The joint law uses exactly the arithmetic kernel already in the project. -/
theorem mellinJointDensity_eq_kernelDet (n : ℕ) (x : Fin n → ℝ) :
    (mellinJointDensity n x : ℂ) =
      Matrix.det (fun i j => kernel n (x i) (x j)) / (n.factorial : ℂ) := by
  exact (ContinuousProjectionDPP.density_eq_det_kernelMatrix (angularFeatures n) x).trans
    (by rw [angularFeatures_kernel])

theorem mellinJointDensity_integral (n : ℕ) :
    (∫ x, mellinJointDensity n x ∂(Measure.pi fun _ : Fin n => frequencyMeasure)) = 1 :=
  ContinuousProjectionDPP.integral_density_eq_one (ContinuousProjectionDPP.integral_squaredDet (angularFeatures n)
    (fun i => modeFeature_memLp i.val) (angularFeatures_gram n))

theorem kernel_reproducing (n : ℕ) (t u : ℝ) :
    (∫ v, kernel n t v * kernel n v u ∂frequencyMeasure) = kernel n t u := by
  rw [← angularFeatures_kernel n]
  exact ContinuousProjectionDPP.kernel_reproducing (angularFeatures n) (fun i => modeFeature_memLp i.val)
    (angularFeatures_gram n) t u

theorem kernel_trace (n : ℕ) : (∫ t, kernel n t t ∂frequencyMeasure) = (n : ℂ) := by
  rw [← angularFeatures_kernel n]
  exact ContinuousProjectionDPP.kernel_trace (angularFeatures n) (fun i => modeFeature_memLp i.val)
    (angularFeatures_gram n)

end RiemannResearch.RH.Pareto.MellinFrequency
