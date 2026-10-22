import RiemannResearch.Analysis.WeightedMellinLogarithmicKernel
import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact signed lattice correction in critical weighted energy

Generic energy transfer under an explicit inverse-square correction bound.
The signed cross term and lattice square are retained.  The correction is
absolutely integrable, uniformly bounded at every real cutoff, and converges
to its genuine signed integral.  No arithmetic energy estimate is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.SignedLatticeEnergy
open MeasureTheory.WeightedMellin

def criticalEnergy (f : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∫ x in Icc (1 : ℝ) X, f x ^ 2 / x ^ 2

def signedCorrectionDensity (U δ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * U x * δ x + δ x ^ 2) / x ^ 2

def signedCorrectionCutoff (U δ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∫ x in Icc (1 : ℝ) X, signedCorrectionDensity U δ x

def correctionEnvelope (K C x : ℝ) : ℝ :=
  2 * K * C * (1 + Real.log x) * x ^ (-3 : ℝ) + C ^ 2 * x ^ (-6 : ℝ)

theorem continuousOn_Ioi_of_continuousOn_Icc {f : ℝ → ℝ}
    (hf : ∀ X : ℝ, ContinuousOn f (Icc (1 : ℝ) X)) :
    ContinuousOn f (Ioi (1 : ℝ)) := by
  intro x hx
  have hr : x < x + 1 := by linarith
  have hm : x ∈ Icc (1 : ℝ) (x + 1) := ⟨hx.le, hr.le⟩
  exact ((hf (x + 1) x hm).continuousAt (Icc_mem_nhds hx hr)).continuousWithinAt

theorem correctionEnvelope_integrableOn (K C : ℝ) :
    IntegrableOn (correctionEnvelope K C) (Ioi (1 : ℝ)) := by
  have h0 : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Ioi 1) := by
    convert log_moment_integrable 0 (δ := 2) (by norm_num) using 1
    all_goals norm_num
  have h1 : IntegrableOn (fun x : ℝ => Real.log x * x ^ (-3 : ℝ)) (Ioi 1) := by
    convert log_moment_integrable 1 (δ := 2) (by norm_num) using 1
    all_goals norm_num
  have h6 : IntegrableOn (fun x : ℝ => x ^ (-6 : ℝ)) (Ioi 1) := by
    convert log_moment_integrable 0 (δ := 5) (by norm_num) using 1
    all_goals norm_num
  apply (((h0.add h1).const_mul (2 * K * C)).add (h6.const_mul (C ^ 2))).congr
  exact Eventually.of_forall (fun _ => by dsimp [correctionEnvelope]; ring)

theorem correctionEnvelope_integral (K C : ℝ) :
    (∫ x in Ioi (1 : ℝ), correctionEnvelope K C x) =
      (3 / 2 : ℝ) * K * C + C ^ 2 / 5 := by
  have h0 : IntegrableOn (fun x : ℝ => x ^ (-3 : ℝ)) (Ioi 1) := by
    convert log_moment_integrable 0 (δ := 2) (by norm_num) using 1
    all_goals norm_num
  have h1 : IntegrableOn (fun x : ℝ => Real.log x * x ^ (-3 : ℝ)) (Ioi 1) := by
    convert log_moment_integrable 1 (δ := 2) (by norm_num) using 1
    all_goals norm_num
  have h6 : IntegrableOn (fun x : ℝ => x ^ (-6 : ℝ)) (Ioi 1) := by
    convert log_moment_integrable 0 (δ := 5) (by norm_num) using 1
    all_goals norm_num
  have e0 : (∫ x in Ioi (1 : ℝ), x ^ (-3 : ℝ)) = 1 / 2 := by
    convert log_moment_integral 0 (δ := 2) (by norm_num) using 1
    all_goals norm_num
  have e1 : (∫ x in Ioi (1 : ℝ), Real.log x * x ^ (-3 : ℝ)) = 1 / 4 := by
    convert log_moment_integral 1 (δ := 2) (by norm_num) using 1
    all_goals norm_num
  have e6 : (∫ x in Ioi (1 : ℝ), x ^ (-6 : ℝ)) = 1 / 5 := by
    convert log_moment_integral 0 (δ := 5) (by norm_num) using 1
    all_goals norm_num
  have he : correctionEnvelope K C = fun x : ℝ =>
      2 * K * C * (x ^ (-3 : ℝ) + Real.log x * x ^ (-3 : ℝ)) +
        C ^ 2 * x ^ (-6 : ℝ) := by
    funext x; dsimp [correctionEnvelope]; ring
  rw [he]
  calc
    _ = (∫ x in Ioi (1 : ℝ),
        2 * K * C * (x ^ (-3 : ℝ) + Real.log x * x ^ (-3 : ℝ))) +
      (∫ x in Ioi (1 : ℝ), C ^ 2 * x ^ (-6 : ℝ)) :=
      integral_add ((h0.add h1).const_mul _) (h6.const_mul _)
    _ = 2 * K * C * ((∫ x in Ioi (1 : ℝ), x ^ (-3 : ℝ)) +
        (∫ x in Ioi (1 : ℝ), Real.log x * x ^ (-3 : ℝ))) +
      C ^ 2 * (∫ x in Ioi (1 : ℝ), x ^ (-6 : ℝ)) := by
      rw [integral_const_mul, integral_const_mul]
      congr 1
      rw [integral_add h0 h1]
    _ = _ := by rw [e0, e1, e6]; ring

theorem signedCorrectionDensity_abs_le {U δ : ℝ → ℝ} {K C x : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hU : |U x| ≤ K * x * (1 + Real.log x))
    (hδ : |δ x| ≤ C / x ^ 2) :
    |signedCorrectionDensity U δ x| ≤ correctionEnvelope K C x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx0
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsquare : δ x ^ 2 ≤ (C / x ^ 2) ^ 2 := by
    have hδ0 : 0 ≤ C / x ^ 2 := div_nonneg hC hx2.le
    nlinarith [sq_abs (δ x), abs_nonneg (δ x)]
  have hcross : 2 * |U x| * |δ x| ≤
      2 * (K * x * (1 + Real.log x)) * (C / x ^ 2) := by
    gcongr
  have h3 : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
    norm_num [Real.rpow_neg hx0.le]
  have h6 : x ^ (-6 : ℝ) = (x ^ 6)⁻¹ := by
    norm_num [Real.rpow_neg hx0.le]
  unfold signedCorrectionDensity
  rw [abs_div, abs_of_nonneg hx2.le]
  calc
    _ ≤ (2 * |U x| * |δ x| + δ x ^ 2) / x ^ 2 := by
      apply div_le_div_of_nonneg_right _ hx2.le
      have h := abs_add_le (2 * U x * δ x) (δ x ^ 2)
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg (δ x))] at h
      exact h
    _ ≤ (2 * (K * x * (1 + Real.log x)) * (C / x ^ 2) +
        (C / x ^ 2) ^ 2) / x ^ 2 :=
      div_le_div_of_nonneg_right (add_le_add hcross hsquare) hx2.le
    _ = correctionEnvelope K C x := by
      rw [correctionEnvelope, h3, h6]
      field_simp

theorem signedCorrectionDensity_integrableOn {U δ : ℝ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hUcont : ContinuousOn U (Ioi (1 : ℝ)))
    (hδcont : ContinuousOn δ (Ioi (1 : ℝ)))
    (hU : ∀ x : ℝ, 1 ≤ x → |U x| ≤ K * x * (1 + Real.log x))
    (hδ : ∀ x : ℝ, 1 ≤ x → |δ x| ≤ C / x ^ 2) :
    IntegrableOn (signedCorrectionDensity U δ) (Ioi (1 : ℝ)) := by
  have hc : ContinuousOn (signedCorrectionDensity U δ) (Ioi (1 : ℝ)) := by
    apply ((continuousOn_const.mul hUcont).mul hδcont |>.add (hδcont.pow 2)).div
      (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (zero_lt_one.trans hx))
  apply (correctionEnvelope_integrableOn K C).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [Real.norm_eq_abs] using
    signedCorrectionDensity_abs_le hK hC hx.le (hU x hx.le) (hδ x hx.le)

theorem signedCorrectionCutoff_uniform_bound {U δ : ℝ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hf : IntegrableOn (signedCorrectionDensity U δ) (Ioi (1 : ℝ)))
    (hU : ∀ x : ℝ, 1 ≤ x → |U x| ≤ K * x * (1 + Real.log x))
    (hδ : ∀ x : ℝ, 1 ≤ x → |δ x| ≤ C / x ^ 2) (X : ℝ) :
    |signedCorrectionCutoff U δ X| ≤ (3 / 2 : ℝ) * K * C + C ^ 2 / 5 := by
  have he := correctionEnvelope_integrableOn K C
  have hsub : Ioc (1 : ℝ) X ⊆ Ioi (1 : ℝ) := fun _ hx => hx.1
  unfold signedCorrectionCutoff
  rw [integral_Icc_eq_integral_Ioc, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x in Ioc (1 : ℝ) X, ‖signedCorrectionDensity U δ x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioc (1 : ℝ) X, correctionEnvelope K C x := by
      apply setIntegral_mono_on (hf.mono_set hsub).norm (he.mono_set hsub) measurableSet_Ioc
      intro x hx
      simpa only [Real.norm_eq_abs] using
        signedCorrectionDensity_abs_le hK hC hx.1.le (hU x hx.1.le) (hδ x hx.1.le)
    _ ≤ ∫ x in Ioi (1 : ℝ), correctionEnvelope K C x := by
      apply setIntegral_mono_set he
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        dsimp [correctionEnvelope]
        have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
        have hx0 : 0 < x := zero_lt_one.trans hx
        have hp3 : 0 ≤ x ^ (-3 : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
        have hp6 : 0 ≤ x ^ (-6 : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
        positivity
      · exact Eventually.of_forall hsub
    _ = _ := correctionEnvelope_integral K C

theorem signedCorrectionCutoff_tendsto {U δ : ℝ → ℝ}
    (hf : IntegrableOn (signedCorrectionDensity U δ) (Ioi (1 : ℝ))) :
    Tendsto (signedCorrectionCutoff U δ) atTop
      (𝓝 (∫ x in Ioi (1 : ℝ), signedCorrectionDensity U δ x)) := by
  apply (intervalIntegral_tendsto_integral_Ioi 1 hf tendsto_id).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  simp only [id_eq, signedCorrectionCutoff, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hX]

theorem criticalEnergy_add_eq_energy_add_signedCorrection
    {U δ : ℝ → ℝ} (X : ℝ)
    (hU : ContinuousOn U (Icc (1 : ℝ) X))
    (hδ : ContinuousOn δ (Icc (1 : ℝ) X)) :
    criticalEnergy (fun x => U x + δ x) X =
      criticalEnergy U X + signedCorrectionCutoff U δ X := by
  have hden : ∀ x ∈ Icc (1 : ℝ) X, x ^ 2 ≠ 0 := by
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (zero_lt_one.trans_le hx.1))
  have hu : IntegrableOn (fun x => U x ^ 2 / x ^ 2) (Icc (1 : ℝ) X) :=
    ((hU.pow 2).div (continuousOn_id.pow 2) hden).integrableOn_Icc
  have hc : IntegrableOn (signedCorrectionDensity U δ) (Icc (1 : ℝ) X) :=
    ((((continuousOn_const.mul hU).mul hδ).add (hδ.pow 2)).div
      (continuousOn_id.pow 2) hden).integrableOn_Icc
  unfold criticalEnergy signedCorrectionCutoff
  rw [← integral_add hu hc]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by dsimp [signedCorrectionDensity]; ring)

end RiemannResearch.Analysis.SignedLatticeEnergy
