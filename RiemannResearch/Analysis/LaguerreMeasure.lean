import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Exponential measure for the ordinary Laguerre expansion

The actual RH Parseval target uses the probability measure exp(-t) dt on
the positive half-line. These transport and moment lemmas prepare its L2 space.
Source: the user's actual Parseval target and the exponential change of variables.
-/

noncomputable section
open MeasureTheory
namespace RiemannResearch.Analysis

def laguerreMeasure : Measure ℝ :=
  (volume.restrict (Set.Ici 0)).withDensity (fun t => ENNReal.ofReal (Real.exp (-t)))

theorem laguerreDensity_measurable :
    Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-t))) :=
  (Real.measurable_exp.comp measurable_id.neg).ennreal_ofReal

theorem integral_laguerreMeasure (g : ℝ → ℝ) :
    (∫ t, g t ∂laguerreMeasure) = ∫ t in Set.Ici (0 : ℝ), g t * Real.exp (-t) := by
  rw [laguerreMeasure, integral_withDensity_eq_integral_toReal_smul
    laguerreDensity_measurable (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, mul_comm]

theorem integrable_laguerreMeasure_iff (g : ℝ → ℝ) :
    Integrable g laguerreMeasure ↔
      IntegrableOn (fun t => g t * Real.exp (-t)) (Set.Ici 0) := by
  rw [laguerreMeasure, integrable_withDensity_iff_integrable_smul'
    laguerreDensity_measurable (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, mul_comm, IntegrableOn]

instance : IsFiniteMeasure laguerreMeasure := by
  apply isFiniteMeasure_withDensity
  apply (lintegral_ofReal_ne_top_iff_integrable
    (Real.measurable_exp.comp measurable_id.neg).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => Real.exp_nonneg (-t)))).2
  change IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ici 0)
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_neg_Ioi 0

theorem memLp_pow_laguerreMeasure (n : ℕ) :
    MemLp (fun t : ℝ => t ^ n) 2 laguerreMeasure := by
  apply (memLp_two_iff_integrable_sq (measurable_id.pow_const n).aestronglyMeasurable).2
  rw [integrable_laguerreMeasure_iff, integrableOn_Ici_iff_integrableOn_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_rpow
    (s := ((n * 2 : ℕ) : ℝ)) (p := 1)
    (by have := Nat.cast_nonneg (α := ℝ) (n * 2); linarith) (by norm_num)
  simpa only [Real.rpow_natCast, Real.rpow_one, pow_mul, id_eq] using h

theorem memLp_exp_mul_laguerreMeasure {s : ℝ} (hs : s < 1 / 2) :
    MemLp (fun t : ℝ => Real.exp (s * t)) 2 laguerreMeasure := by
  apply (memLp_two_iff_integrable_sq
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).aestronglyMeasurable).2
  rw [integrable_laguerreMeasure_iff, integrableOn_Ici_iff_integrableOn_Ioi]
  have heq : (fun t : ℝ => Real.exp (s * t) ^ 2 * Real.exp (-t)) =
      (fun t : ℝ => Real.exp ((2 * s - 1) * t)) := by
    funext t
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  simp only [Function.comp_apply, Pi.mul_apply, id_eq]
  rw [heq]
  exact integrableOn_exp_mul_Ioi (by linarith) 0

abbrev LaguerreL2 := Lp ℝ 2 laguerreMeasure

theorem inner_toLp_laguerreMeasure {f g : ℝ → ℝ}
    (hf : MemLp f 2 laguerreMeasure) (hg : MemLp g 2 laguerreMeasure) :
    inner ℝ (hf.toLp f) (hg.toLp g) =
      ∫ t in Set.Ici (0 : ℝ), f t * g t * Real.exp (-t) := by
  rw [L2.inner_def]
  calc
    _ = ∫ t, f t * g t ∂laguerreMeasure := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t ht ht'
      simp [ht, ht', mul_comm]
    _ = _ := integral_laguerreMeasure _

theorem norm_toLp_sq_laguerreMeasure {f : ℝ → ℝ}
    (hf : MemLp f 2 laguerreMeasure) :
    ‖hf.toLp f‖ ^ 2 = ∫ t in Set.Ici (0 : ℝ), f t ^ 2 * Real.exp (-t) := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_laguerreMeasure]
  simp only [pow_two]

end RiemannResearch.Analysis
