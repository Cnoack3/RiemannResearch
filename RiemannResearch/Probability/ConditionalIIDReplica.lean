/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Probability.ConditionalIIDWeightedEnergy
import Mathlib.Probability.Independence.Integration

/-! Two-replica identities preserve the full signed arithmetic Gram structure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

/-- Cross-row products factor within each conditional fiber, not unconditionally. -/
theorem path_cross_product (k i j : ℕ) (hij : i ≠ j) (F G : ℕ → ℝ) :
    (∫ x : Path, F (x i) * G (x j) ∂pathLaw k) =
      cesaro F (k + 1) * cesaro G (k + 1) := by
  have h := ((pathLaw_iIndepFun k).indepFun hij).integral_fun_comp_mul_comp
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    (measurable_of_countable F).stronglyMeasurable.aestronglyMeasurable
    (measurable_of_countable G).stronglyMeasurable.aestronglyMeasurable
  simpa only [path_integral_coordinate] using h

/-- Conditional iid copies retain the product of the conditional means. -/
theorem conditional_cross_product (i j : ℕ) (hij : i ≠ j) (F G : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate i ω)) 2 probability)
    (hG : MemLp (fun ω => G (coordinate j ω)) 2 probability) :
    probability[(fun ω => F (coordinate i ω) * G (coordinate j ω)) | latentSigma]
      =ᵐ[probability] (fun ω => cesaro F (endpoint ω) * cesaro G (endpoint ω)) := by
  have hm : Measurable (fun x : Path => F (x i) * G (x j)) :=
    ((measurable_of_countable F).comp (measurable_pi_apply i)).mul
      ((measurable_of_countable G).comp (measurable_pi_apply j))
  have hi : Integrable (fun ω => F (coordinate i ω) * G (coordinate j ω)) probability :=
    hF.integrable_mul hG
  have h := conditional_path_expectation (fun x => F (x i) * G (x j))
    hm.stronglyMeasurable hi
  filter_upwards [h] with ω hω
  rw [hω, path_cross_product _ i j hij]
  rfl

/-- Exact unconditional cross-replica product: the conditional-mean term does not disappear. -/
theorem cross_product_integral (i j : ℕ) (hij : i ≠ j) (F G : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate i ω)) 2 probability)
    (hG : MemLp (fun ω => G (coordinate j ω)) 2 probability) :
    (∫ ω, F (coordinate i ω) * G (coordinate j ω) ∂probability) =
      ∫ ω, cesaro F (endpoint ω) * cesaro G (endpoint ω) ∂probability := by
  calc
    _ = ∫ ω, probability[(fun ω => F (coordinate i ω) * G (coordinate j ω)) |
        latentSigma] ω ∂probability := (integral_condExp latentSigma_le).symm
    _ = _ := integral_congr_ae (conditional_cross_product i j hij F G hF hG)

/-- Conditional-mean products are globally integrable under the two marginal L2 assumptions. -/
theorem conditionalMean_product_integrable (F G : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability)
    (hG : MemLp (fun ω => G (coordinate 0 ω)) 2 probability) :
    Integrable (fun ω => cesaro F (endpoint ω) * cesaro G (endpoint ω)) probability :=
  (integrable_condExp (μ := probability) (m := latentSigma)
    (f := fun ω => F (coordinate 0 ω) * G (coordinate 1 ω))).congr
      (conditional_cross_product 0 1 (by omega) F G hF (coordinate_memLp_of_zero G hG 1))

/-- The complete signed Gram identity. No covariance or mixed term is discarded. -/
theorem signed_gram_identity (F G : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability)
    (hG : MemLp (fun ω => G (coordinate 0 ω)) 2 probability) :
    (∫ ω, F (coordinate 0 ω) * G (coordinate 0 ω) ∂probability) =
      (∫ ω, cesaro F (endpoint ω) * cesaro G (endpoint ω) ∂probability) +
      (1 / 2 : ℝ) * ∫ ω,
        (F (coordinate 0 ω) - F (coordinate 1 ω)) *
          (G (coordinate 0 ω) - G (coordinate 1 ω)) ∂probability := by
  have hF1 := coordinate_memLp_of_zero F hF 1
  have hG1 := coordinate_memLp_of_zero G hG 1
  have h00 := hF.integrable_mul hG
  have h01 := hF.integrable_mul hG1
  have h10 := hF1.integrable_mul hG
  have h11 := hF1.integrable_mul hG1
  have hsame := ((coordinates_identDistrib 0 1).comp
    (measurable_of_countable (fun n => F n * G n))).integral_eq
  have hsplit : (∫ ω,
      (F (coordinate 0 ω) - F (coordinate 1 ω)) *
        (G (coordinate 0 ω) - G (coordinate 1 ω)) ∂probability) =
      (∫ ω, F (coordinate 0 ω) * G (coordinate 0 ω) ∂probability) +
      (∫ ω, F (coordinate 1 ω) * G (coordinate 1 ω) ∂probability) -
      (∫ ω, F (coordinate 0 ω) * G (coordinate 1 ω) ∂probability) -
      (∫ ω, F (coordinate 1 ω) * G (coordinate 0 ω) ∂probability) := by
    calc
      _ = ∫ ω,
          ((F (coordinate 0 ω) * G (coordinate 0 ω) +
            F (coordinate 1 ω) * G (coordinate 1 ω)) -
              F (coordinate 0 ω) * G (coordinate 1 ω)) -
                F (coordinate 1 ω) * G (coordinate 0 ω) ∂probability := by
        apply integral_congr_ae
        exact ae_of_all _ (fun ω => by ring)
      _ = _ := by
        have e1 := integral_sub ((h00.add h11).sub h01) h10
        have e2 := integral_sub (h00.add h11) h01
        have e3 := integral_add h00 h11
        simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at e1 e2 e3
        rw [e1, e2, e3]
  rw [cross_product_integral 0 1 (by omega) F G hF hG1,
    cross_product_integral 1 0 (by omega) F G hF1 hG] at hsplit
  change (∫ ω, F (coordinate 0 ω) * G (coordinate 0 ω) ∂probability) =
    (∫ ω, F (coordinate 1 ω) * G (coordinate 1 ω) ∂probability) at hsame
  linarith

/-- Two replicas measure exactly the energy suppressed by conditional averaging. -/
theorem replica_energy_identity (F : ℕ → ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) :
    (∫ ω, F (coordinate 0 ω) ^ 2 ∂probability) =
      (∫ ω, cesaro F (endpoint ω) ^ 2 ∂probability) +
      (1 / 2 : ℝ) * ∫ ω,
        (F (coordinate 0 ω) - F (coordinate 1 ω)) ^ 2 ∂probability := by
  simpa only [pow_two] using signed_gram_identity F F hF hF

/-- Cesaro averaging fixes constants at each positive endpoint. -/
theorem cesaro_const_sub (F : ℕ → ℝ) (c : ℝ) (t : ℕ) (ht : 0 < t) :
    cesaro (fun n => c - F n) t = c - cesaro F t := by
  unfold cesaro
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  field_simp

/-- The target-error version of the two-replica full-energy formula. -/
theorem replica_error_identity (F : ℕ → ℝ) (c : ℝ)
    (hF : MemLp (fun ω => F (coordinate 0 ω)) 2 probability) :
    (∫ ω, (c - F (coordinate 0 ω)) ^ 2 ∂probability) =
      (∫ ω, (c - cesaro F (endpoint ω)) ^ 2 ∂probability) +
      (1 / 2 : ℝ) * ∫ ω,
        (F (coordinate 0 ω) - F (coordinate 1 ω)) ^ 2 ∂probability := by
  have h := replica_energy_identity (fun n => c - F n) ((memLp_const c).sub hF)
  simp_rw [cesaro_const_sub F c _ (endpoint_pos _)] at h
  have he : (∫ ω, ((c - F (coordinate 0 ω)) -
      (c - F (coordinate 1 ω))) ^ 2 ∂probability) =
      ∫ ω, (F (coordinate 0 ω) - F (coordinate 1 ω)) ^ 2 ∂probability := by
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => by ring)
  rw [he] at h
  exact h

end RiemannResearch.Probability.ConditionalIID
