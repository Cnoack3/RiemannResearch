import RiemannResearch.Analysis.ActualInghamGabrielEndpoints
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Exact Gaussian form of the two actual Gabriel endpoint budgets

Tonelli's change of integration order identifies the positive half-line
Gaussian moment with the complete outer-integral budget of Corollary 6 of
Chourasiya and Simonič, https://arxiv.org/html/2507.15184v2. Integrability
is verified on the full product before changing integration order.
-/
noncomputable section
open MeasureTheory Set Filter Complex
namespace RiemannResearch.Analysis.InghamMollifier

private def gaussianRegion (L : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ p.2 ≤ L * Real.sqrt p.1}

private theorem measurableSet_gaussianRegion (L : ℝ) : MeasurableSet (gaussianRegion L) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd
      (measurable_const.mul (Real.continuous_sqrt.measurable.comp measurable_fst)))

/-- Exact change of integration order for the full endpoint budget, including
integrability of the resulting Gaussian vertical moment. -/
theorem gabrielEndpoint_eq_gaussian {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {T a : ℝ} (hT : 0 < T) (ha : 0 < a)
    (hbudget : IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t)
      (Ioi 0)) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t/(T*a))^2) * f t) (Ioi 0) ∧
    gabrielEndpoint f T a = ∫ t in Ioi (0 : ℝ), Real.exp (-(t/(T*a))^2) * f t := by
  let L := T*a
  have hL : 0 < L := mul_pos hT ha
  let K : ℝ × ℝ → ℝ := (gaussianRegion L).indicator fun p => Real.exp (-p.1) * f p.2
  have hK : Measurable K :=
    ((Real.continuous_exp.measurable.comp measurable_fst.neg).mul
      (hf.measurable.comp measurable_snd)).indicator (measurableSet_gaussianRegion L)
  have hK0 (p : ℝ × ℝ) : 0 ≤ K p :=
    indicator_nonneg (fun p _ => mul_nonneg (Real.exp_pos _).le (hf0 _)) _
  have hrow (u t : ℝ) : K (u,t) = (Ioc 0 (L*Real.sqrt u)).indicator
        (fun t => Real.exp (-u)*f t) t := by rfl
  have hrowInt (u : ℝ) : Integrable (fun t : ℝ => K (u,t)) := by
    simp only [hrow]
    apply (integrable_indicator_iff measurableSet_Ioc).2
    exact ((continuous_const.mul hf).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hrowVal (u : ℝ) : (∫ t : ℝ, K (u,t)) =
      Real.exp (-u) * ∫ t in 0..L*Real.sqrt u, f t := by
    simp only [hrow, integral_indicator measurableSet_Ioc]
    rw [intervalIntegral.integral_of_le (mul_nonneg hL.le (Real.sqrt_nonneg _)), integral_const_mul]
  have hprod : Integrable K ((volume.restrict (Ioi 0)).prod volume) := by
    refine (integrable_prod_iff hK.aestronglyMeasurable).2 ⟨ae_of_all _ hrowInt, ?_⟩
    simp only [Real.norm_eq_abs, abs_of_nonneg (hK0 _), hrowVal]
    exact hbudget
  have hcol (t : ℝ) : (∫ u in Ioi (0 : ℝ), K (u,t)) =
      (Ioi (0 : ℝ)).indicator (fun t => Real.exp (-(t/L)^2) * f t) t := by
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht)]
      have hp : 0 < t/L := div_pos ht hL
      have he (u : ℝ) (hu : 0 < u) :
          K (u,t) = (Ici ((t/L)^2)).indicator (fun u => Real.exp (-u)*f t) u := by
        have hiff : t ≤ L*Real.sqrt u ↔ (t/L)^2 ≤ u := by
          rw [mul_comm L, ← div_le_iff₀ hL, ← Real.le_sqrt (by positivity) hu.le]
        by_cases h : t ≤ L*Real.sqrt u
        · rw [indicator_of_mem (show u ∈ Ici ((t/L)^2) from hiff.mp h)]
          exact indicator_of_mem (show (u,t) ∈ gaussianRegion L from ⟨ht,h⟩) _
        · rw [indicator_of_notMem (show u ∉ Ici ((t/L)^2) from fun hu => h (hiff.mpr hu))]
          exact indicator_of_notMem (show (u,t) ∉ gaussianRegion L from fun h' => h h'.2) _
      rw [setIntegral_congr_fun measurableSet_Ioi he, integral_indicator measurableSet_Ici,
        Measure.restrict_restrict_of_subset (show Ici ((t/L)^2) ⊆ Ioi (0:ℝ) from
          fun u hu => lt_of_lt_of_le (sq_pos_of_pos hp) hu), integral_mul_const,
        integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi]
    · rw [indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht)]
      have hzero (u : ℝ) : K (u,t) = 0 :=
        indicator_of_notMem (show (u,t) ∉ gaussianRegion L from fun h' => ht h'.1) _
      simp [hzero]
  constructor
  · apply (integrable_indicator_iff measurableSet_Ioi).mp
    exact hprod.integral_prod_right.congr (ae_of_all _ hcol)
  · calc
      gabrielEndpoint f T a = ∫ u in Ioi (0:ℝ), ∫ t : ℝ, K (u,t) := by simp only [hrowVal]; rfl
      _ = ∫ t : ℝ, ∫ u in Ioi (0 : ℝ), K (u,t) :=
        (integral_prod K hprod).symm.trans (integral_prod_symm K hprod)
      _ = _ := by simp only [hcol, integral_indicator measurableSet_Ioi, L]

end RiemannResearch.Analysis.InghamMollifier
