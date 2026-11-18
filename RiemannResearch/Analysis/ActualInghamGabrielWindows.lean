import RiemannResearch.Analysis.ActualInghamGabrielGaussian
import RiemannResearch.Analysis.ActualInghamGabrielDamping
import RiemannResearch.Analysis.GabrielStripInterpolation
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-!
# Full-boundary and observation-window estimates for the actual smoothed error

These are the two comparisons on either side of the strip interpolation
inequality in Chourasiya--Simonič, https://arxiv.org/html/2507.15184v2,
Theorem 4 and Corollary 6.
-/
noncomputable section
open MeasureTheory Filter Set Complex
open RiemannResearch.Analysis.InghamInterpolation
namespace RiemannResearch.Analysis.InghamMollifier

/-- Reflection and Tonelli give the complete vertical Gaussian integral. -/
theorem gabrielEndpoint_full_even {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    (hev : ∀ t, f (-t)=f t) {T a : ℝ} (hT : 0 < T) (ha : 0 < a)
    (hbudget : IntegrableOn (fun u : ℝ => Real.exp (-u) * ∫ t in 0..T*a*Real.sqrt u, f t)
      (Ioi 0)) :
    let W := fun t : ℝ => Real.exp (-(t/(T*a))^2)*f t
    Integrable W ∧ (∫ t : ℝ, W t) = 2*gabrielEndpoint f T a := by
  let W := fun t : ℝ => Real.exp (-(t/(T*a))^2)*f t
  have H := gabrielEndpoint_eq_gaussian hf hf0 hT ha hbudget
  have hp : IntegrableOn W (Ioi 0) := H.1
  have hw (t : ℝ) : W (-t)=W t := by simp [W, neg_div, hev]
  have hpi : IntegrableOn W (Ici (-(0:ℝ))) := by
    simpa only [neg_zero, IntegrableOn, Measure.restrict_congr_set Ioi_ae_eq_Ici] using hp
  have hn : IntegrableOn W (Iic 0) := by
    simpa only [hw] using hpi.comp_neg_Iic
  have hv : (∫ t in Iic (0:ℝ), W t) = ∫ t in Ioi (0:ℝ), W t := by
    simpa only [hw, neg_zero] using integral_comp_neg_Iic 0 W
  change Integrable W ∧ _
  constructor
  · rw [← integrableOn_univ]
    simpa only [Iic_union_Ioi] using hn.union hp
  · change (∫ t : ℝ, W t) = _
    rw [← intervalIntegral.integral_Iic_add_Ioi hn hp, hv, ← H.2]
    ring

/-- A complete Gaussian budget bounds every translated finite window on its
boundary. Here `p*b = 1/(T*a)^2` identifies the physical smoothing scale. -/
theorem actual_gabriel_boundary_windows {X : ℕ} {x b p T a : ℝ}
    (hx : 1/2 ≤ x) (hx1 : x ≠ 1) (hp : 0 < p) (hT : 0 < T) (ha : 0 < a)
    (hscale : p*b = 1/(T*a)^2)
    (hev : ∀ t : ℝ, ‖mollifiedError X ((x:ℂ)+((-t:ℝ):ℂ)*I)‖ =
      ‖mollifiedError X ((x:ℂ)+(t:ℂ)*I)‖)
    (hbudget : IntegrableOn (fun u : ℝ => Real.exp (-u) *
      ∫ t in 0..T*a*Real.sqrt u, stripMomentDensity (mollifiedError X) x p t) (Ioi 0))
    {L : ℝ} (hL : 0 ≤ L) (y : ℝ) :
    (∫ t in y..y+L, stripMomentDensity (gabrielDampedError X b) x p t) ≤
      Real.exp (p*b*x^2) * (2*gabrielEndpoint (stripMomentDensity (mollifiedError X) x p) T a) := by
  let f := stripMomentDensity (mollifiedError X) x p
  let W := fun t : ℝ => Real.exp (-(t/(T*a))^2) * f t
  let K := Real.exp (p*b*x^2)
  have hfc : Continuous f := (vertical_error_continuous X hx1).rpow_const (fun _ => Or.inr hp.le)
  have hf0 (t : ℝ) : 0 ≤ f t := Real.rpow_nonneg (norm_nonneg _) _
  have hfe (t : ℝ) : f (-t)=f t := by dsimp only [f,stripMomentDensity]; rw [hev]
  have hW := gabrielEndpoint_full_even hfc hf0 hfe hT ha hbudget
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hpos (t : ℝ) : 0 ≤ W t := mul_nonneg (Real.exp_pos _).le (hf0 _)
  have hdom (t : ℝ) : stripMomentDensity (gabrielDampedError X b) x p t ≤ K*W t := by
    let s : ℂ := (x:ℂ)+(t:ℂ)*I
    have hs : s ≠ 1 := fun h => hx1 (by simpa [s] using congrArg Complex.re h)
    have h := Real.rpow_le_rpow (norm_nonneg _) (gabrielDampedError_gaussian_upper X b hs
      (by simpa [s] using hx)) hp.le
    change ‖gabrielDampedError X b s‖^p ≤ K*W t
    apply h.trans_eq
    rw [Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow (Real.exp_pos _).le
      (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_mul]
    have hsre : s.re=x := by simp [s]
    have hsim : s.im=t := by simp [s]
    rw [hsre,hsim]
    dsimp [K,W,f,stripMomentDensity,s]
    have he : -b*t^2*p = -(t/(T*a))^2 := by
      calc -b*t^2*p = -(p*b)*t^2 := by ring
           _ = _ := by rw [hscale]; ring
    rw [he, show b*x^2*p=p*b*x^2 by ring]
    ring
  have hkI : Integrable (fun t => K*W t) := hW.1.const_mul K
  rw [intervalIntegral.integral_of_le (show y ≤ y+L by linarith)]
  calc _ ≤ ∫ t in Ioc y (y+L), K*W t :=
        integral_mono_of_nonneg (ae_of_all _ (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
          hkI.integrableOn (ae_of_all _ hdom)
       _ ≤ ∫ t : ℝ, K*W t := setIntegral_le_integral hkI (ae_of_all _ (fun t => mul_nonneg hK (hpos t)))
       _ = _ := by rw [integral_const_mul, hW.2]

/-- Comparison in the opposite direction on the positive observation window.
The lower factor is kept explicit and uses the actual Gaussian time scale. -/
theorem actual_gabriel_observation_window {X : ℕ} {x b H T p : ℝ}
    (hb : 0 ≤ b) (hH : 1 ≤ H) (hHT : H ≤ T) (hp : 0 < p) :
    (Real.exp (b*(x^2-T^2))*(1-1/H))^p *
      (∫ t in H..T, stripMomentDensity (mollifiedError X) x p t) ≤
      ∫ t in H..T, stripMomentDensity (gabrielDampedError X b) x p t := by
  have hx : ∀ t ∈ Icc H T, (x:ℂ)+(t:ℂ)*I ≠ 0 := by
    intro t ht h
    have := congrArg Complex.im h
    simp at this
    linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => stripMomentDensity (gabrielDampedError X b) x p t)
      (Icc H T) := by
    apply ContinuousOn.rpow_const _ (fun t _ => Or.inr hp.le)
    apply ContinuousOn.norm
    intro t ht
    have hi : ContinuousAt (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) t := by fun_prop
    have hcont : ContinuousAt (gabrielDampedError X b ∘ (fun y : ℝ => (x:ℂ)+(y:ℂ)*I)) t :=
      (analyticAt_gabrielDampedError X b (hx t ht)).continuousAt.comp
        (f := fun y : ℝ => (x:ℂ)+(y:ℂ)*I) hi
    exact hcont.continuousWithinAt
  let K := Real.exp (b*(x^2-T^2))*(1-1/H)
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr
    (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hH))
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hHT,
    intervalIntegral.integral_of_le hHT]
  apply integral_mono_of_nonneg
  · exact ae_of_all _ (fun _ => mul_nonneg (Real.rpow_nonneg hK _) (Real.rpow_nonneg (norm_nonneg _) _))
  · exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    let s : ℂ := (x:ℂ)+(t:ℂ)*I
    have hr : s.re=x := by simp [s]
    have hi : s.im=t := by simp [s]
    have h := gabrielDampedError_window_lower X hb hH (T := T) (s := s)
       (by rw [hi,abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]; exact ht.1.le)
       (by rw [hi,abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]; exact ht.2)
    rw [hr] at h
    change K^p * ‖mollifiedError X s‖^p ≤ ‖gabrielDampedError X b s‖^p
    rw [← Real.mul_rpow hK (norm_nonneg _)]
    exact Real.rpow_le_rpow (mul_nonneg hK (norm_nonneg _)) h hp.le


/-- On a symmetric interpolation window, the two reflected observation
windows supply the same factor of two as the boundary Gaussian budgets. -/
theorem gabriel_symmetric_window {f : ℝ → ℝ} (hc : Continuous f) (hpos : ∀ t, 0 ≤ f t)
    (heven : ∀ t, f (-t)=f t) {H T : ℝ} (hH : 0 ≤ H) (hHT : H ≤ T) :
    2*(∫ t in H..T, f t) ≤ ∫ t in -T..T, f t := by
  have heq : (∫ t in -T..0, f t) = ∫ t in 0..T, f t := by
    simpa only [heven, neg_zero] using
      (intervalIntegral.integral_comp_neg (a := 0) (b := T) f).symm
  have h := intervalIntegral.integral_mono_interval (μ := volume) hH hHT (le_refl T)
    (ae_of_all _ hpos) (hc.intervalIntegrable 0 T)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-T) 0)
    (hc.intervalIntegrable 0 T), heq]
  linarith

end RiemannResearch.Analysis.InghamMollifier
