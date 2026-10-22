import RiemannResearch.RH.RamanujanLaguerreResearchTargets
import RiemannResearch.RH.ThresholdLegalIntegrability
import RiemannResearch.RH.ParetoStepIsometry
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Continuous exponential realization of finite legal Pareto packets

Source: the user-provided Ramanujan--Laguerre continuation, Sections 3--7.
The proof uses the exponential change of variables and the established
discrete Pareto step isometry. It supplies the actual mean, full squared error,
and every ordinary-moment integrability requirement without an RH assumption.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre

theorem exponentialLift_measurable (F : ℕ → ℝ) : Measurable (exponentialLift F) :=
  (measurable_of_countable F).comp (Nat.measurable_floor.comp Real.measurable_exp)

theorem allMomentsIntegrable_of_bounded {F : ℕ → ℝ} {C : ℝ}
    (hF : ∀ k, |F k| ≤ C) : AllMomentsIntegrable F := by
  intro j
  have hgamma : IntegrableOn (fun t : ℝ => t ^ j * Real.exp (-t)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa using (integrableOn_rpow_mul_exp_neg_rpow
      (s := (j : ℝ)) (p := 1) (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
      (by norm_num))
  have hm : AEStronglyMeasurable
      (fun t => exponentialLift F t * t ^ j * Real.exp (-t))
      (volume.restrict (Set.Ici 0)) :=
    (((exponentialLift_measurable F).mul (measurable_id.pow_const j)).mul
      (Real.measurable_exp.comp measurable_id.neg)).aestronglyMeasurable
  apply (hgamma.const_mul C).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  have hj : 0 ≤ t ^ j := pow_nonneg ht j
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hj,
    abs_of_pos (Real.exp_pos (-t))]
  simpa only [mul_assoc, exponentialLift] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hF _) hj) (Real.exp_nonneg _)

theorem exponentialLift_square_identity (F : ℕ → ℝ)
    (hF : Summable (fun k => positiveWeight k * F k ^ 2)) :
    (∫ t in Set.Ici (0 : ℝ), exponentialLift F t ^ 2 * Real.exp (-t)) =
      ∑' k, positiveWeight k * F k ^ 2 := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := integral_comp_exp_Ioi (fun x : ℝ => F ⌊x⌋₊ ^ 2 / x ^ 2) 0
  have heq : (fun t : ℝ => Real.exp t • (F ⌊Real.exp t⌋₊ ^ 2 / Real.exp t ^ 2)) =
      (fun t : ℝ => exponentialLift F t ^ 2 * Real.exp (-t)) := by
    funext t
    simp only [smul_eq_mul, exponentialLift, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [heq, Real.exp_zero] at h
  exact h.trans (paretoStep_energy_identity F hF)

theorem exponentialLift_error_identity_of_bounded {F : ℕ → ℝ} {C : ℝ}
    (hF : ∀ k, |F k| ≤ C) :
    (∫ t in Set.Ici (0 : ℝ), (exponentialLift F t - 1) ^ 2 * Real.exp (-t)) =
      paretoError F := by
  have hs : Summable (fun k => positiveWeight k * (1 - F k) ^ 2) :=
    weighted_summable_of_bounded (error_square_bounded hF)
  have h := exponentialLift_square_identity (fun k => 1 - F k) hs
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ici
    intro t ht
    simp only [exponentialLift]
    ring
  · simp only [paretoError, paretoInner, pow_two]

theorem ordinaryMoment_zero_of_bounded {F : ℕ → ℝ} {C : ℝ}
    (hF : ∀ k, |F k| ≤ C) : ordinaryMoment F 0 = paretoMean F := by
  have hI := allMomentsIntegrable_of_bounded hF
  have hsqb : ∀ k, |F k ^ 2| ≤ C * C := by
    simpa only [pow_two] using bounded_product hF hF
  have hA : IntegrableOn (fun t => exponentialLift F t ^ 2 * Real.exp (-t))
      (Set.Ici 0) := by
    simpa [exponentialLift] using allMomentsIntegrable_of_bounded hsqb 0
  have hB : IntegrableOn (fun t => exponentialLift F t * Real.exp (-t))
      (Set.Ici 0) := by simpa using hI 0
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_neg_Ioi 0
  have hAE : (∫ t in Set.Ici (0 : ℝ), exponentialLift F t ^ 2 * Real.exp (-t)) =
      paretoInner F F := by
    simpa only [paretoInner, pow_two] using
      exponentialLift_square_identity F (weighted_summable_of_bounded hsqb)
  have hEE : (∫ t in Set.Ici (0 : ℝ), Real.exp (-t)) = 1 := by
    simpa [exponentialLift, positiveWeight_tsum] using
      exponentialLift_square_identity (fun _ => 1)
        (by simpa using positiveWeight_summable)
  have hInt : (∫ t in Set.Ici (0 : ℝ),
      (exponentialLift F t - 1) ^ 2 * Real.exp (-t)) =
      paretoInner F F - 2 * ordinaryMoment F 0 + 1 := by
    calc
      _ = ∫ t in Set.Ici (0 : ℝ),
          (exponentialLift F t ^ 2 * Real.exp (-t) -
            2 * (exponentialLift F t * Real.exp (-t))) + Real.exp (-t) := by
        apply setIntegral_congr_fun measurableSet_Ici
        intro t ht
        ring
      _ = _ := by
        have hDiff : IntegrableOn (fun t =>
            exponentialLift F t ^ 2 * Real.exp (-t) -
              2 * (exponentialLift F t * Real.exp (-t))) (Set.Ici 0) := by
          exact (hA.sub (hB.const_mul 2)).congr (Filter.Eventually.of_forall (fun t => by rfl))
        rw [integral_add hDiff hE,
          integral_sub hA (hB.const_mul 2), integral_const_mul, hAE, hEE]
        simp [ordinaryMoment]
  have hErr := paretoError_scale hF 1
  simp only [one_mul, one_pow] at hErr
  rw [paretoVariance_eq hF] at hErr
  have hEq := exponentialLift_error_identity_of_bounded hF
  rw [hEq] at hInt
  linarith

theorem continuousParetoRealizationTarget : ContinuousParetoRealizationTarget := by
  intro F hF
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded ({2, 3} : Set ℕ)
    (by intro a ha; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl <;> norm_num) hF
  exact ⟨allMomentsIntegrable_of_bounded hC,
    ordinaryMoment_zero_of_bounded hC, exponentialLift_error_identity_of_bounded hC⟩

end RiemannResearch.RH.Pareto.RamanujanLaguerre
