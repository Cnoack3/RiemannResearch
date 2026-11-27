import RiemannResearch.Probability.DPPContinuousSpectralRigidity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A sharp logarithmic number-variance test for spectral slope

With the Fourier convention `exp(2πixξ)`, the two-sided even spectrum gives
the window variance as twice the integral of `S(h) sin²(πRh) / (πh)²` over
positive frequencies. The estimates below use only the part between `1 / R`
and a fixed positive frequency. The arithmetic number-variance input in the
application is Fujii's theorem, as stated in Goldston--Lee--Schettler--Suriajaya,
Proposition 2, https://arxiv.org/html/2503.15449v4#S5 .
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.Analysis.DPPNumberVariance

private def lowerPrimitive (c x : ℝ) : ℝ :=
  (Real.log x + (1 - Real.sin (c * x)) / (c * x)) / 2

private def lowerDerivative (c x : ℝ) : ℝ :=
  (1 / x - Real.cos (c * x) / x + (Real.sin (c * x) - 1) / (c * x ^ 2)) / 2

private theorem lowerPrimitive_deriv {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    HasDerivAt (lowerPrimitive c) (lowerDerivative c x) x := by
  have hcx := (hasDerivAt_id x).const_mul c
  have hs := (Real.hasDerivAt_sin (c * x)).comp x hcx
  have hd := ((Real.hasDerivAt_log hx.ne').add
    (((hasDerivAt_const x (1 : ℝ)).sub hs).div hcx (mul_ne_zero hc.ne' hx.ne'))).div_const 2
  change HasDerivAt (lowerPrimitive c) _ x at hd
  apply hd.congr_deriv
  dsimp [lowerDerivative]
  field_simp [hc.ne', hx.ne']
  ring

private theorem lowerDerivative_le {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    lowerDerivative c x ≤ Real.sin (c * x / 2) ^ 2 / x := by
  have h := Real.cos_two_mul_eq_one_sub (c * x / 2)
  rw [show 2 * (c * x / 2) = c * x by ring] at h
  have hh : (Real.sin (c * x) - 1) / (c * x ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (Real.sin_le_one _)) (by positivity)
  unfold lowerDerivative
  have hh' : (1 / x - Real.cos (c * x) / x) / 2 = Real.sin (c * x / 2) ^ 2 / x := by
    rw [h]
    ring
  linarith

private theorem on_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {x : ℝ}
    (hx : x ∈ uIcc a b) : 0 < x := by
  rw [uIcc_of_le hab] at hx
  exact ha.trans_le hx.1

/-- Finite lower estimate on the logarithmic integral. The discarded
oscillatory endpoint costs at most `1 / (c * a)`. -/
theorem sin_sq_log_lower {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) :
    (Real.log b - Real.log a) / 2 - 1 / (c * a) ≤
      ∫ x in a..b, Real.sin (c * x / 2) ^ 2 / x := by
  have hi : IntervalIntegrable (lowerDerivative c) volume a b := by
    apply ContinuousOn.intervalIntegrable
    unfold lowerDerivative
    have hne (x) (hx : x ∈ uIcc a b) : x ≠ 0 := (on_pos ha hab hx).ne'
    have hden (x) (hx : x ∈ uIcc a b) : c * x ^ 2 ≠ 0 :=
      mul_ne_zero hc.ne' (pow_ne_zero _ (hne x hx))
    fun_prop (disch := first | exact hne | exact hden)
  have hi' : IntervalIntegrable (fun x => Real.sin (c * x / 2) ^ 2 / x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := intro x hx; exact (on_pos ha hab hx).ne')
  have hm := intervalIntegral.integral_mono_on hab hi hi' (fun x hx =>
    lowerDerivative_le hc (ha.trans_le hx.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => lowerPrimitive_deriv hc (on_pos ha hab hx)) hi] at hm
  have hA : (1 - Real.sin (c * a)) / (c * a) ≤ 2 / (c * a) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [Real.neg_one_le_sin (c * a)]
  have hb := ha.trans_le hab
  have hB : 0 ≤ (1 - Real.sin (c * b)) / (c * b) :=
    div_nonneg (sub_nonneg.mpr (Real.sin_le_one _)) (by positivity)
  unfold lowerPrimitive at hm
  rw [show 2 / (c * a) = 2 * (1 / (c * a)) by ring] at hA
  linarith only [hm, hA, hB]


/-- Twice the positive-frequency contribution, with the factor `π⁻²`
removed. Only integrable spectra are used by the variance theorem. -/
def windowEnergy (S : ℝ → ℝ) (R : ℝ) : ℝ :=
  2 * ∫ x in Ioi (0 : ℝ), S x * Real.sin (Real.pi * R * x) ^ 2 / x ^ 2

/-- A sharp logarithmic upper bound on the normalized spectral window energy
on cofinally many windows forces arbitrarily small frequencies of slope below
a prescribed `s` larger than the upper logarithmic coefficient `d`.
This is the sequence formulation of the upper bound on the lower slope. -/
theorem exists_small_slope_of_log_windowEnergy
    {S : ℝ → ℝ} (hpos : ∀ x, 0 ≤ S x)
    (hint : ∀ R > 0, IntegrableOn
      (fun x => S x * Real.sin (Real.pi * R * x) ^ 2 / x ^ 2) (Ioi (0 : ℝ)))
    {d s b : ℝ} (hupper : ∃ᶠ R : ℝ in atTop, windowEnergy S R ≤ d * Real.log R)
    (hs : 0 < s) (hds : d < s) (hb : 0 < b) :
    ∃ x, 0 < x ∧ x < b ∧ S x < s * x := by
  by_contra! hbad
  let t := b / 2
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨R, hu, hR, hRt, hlog⟩ := (hupper.and_eventually ((eventually_gt_atTop (0 : ℝ)).and
    ((eventually_ge_atTop (1 / t)).and (Real.tendsto_log_atTop.eventually_gt_atTop
      (s * (1 / Real.pi - Real.log t) / (s - d)))))).exists
  have ha : 0 < 1 / R := by positivity
  have hat : 1 / R ≤ t := by
    apply (div_le_iff₀ hR).2
    have hp := (div_le_iff₀ ht).1 hRt
    linarith
  have hk := sin_sq_log_lower ha hat (show 0 < 2 * Real.pi * R by positivity)
  change (Real.log t - Real.log (1 / R)) / 2 - 1 / ((2 * Real.pi * R) * (1 / R)) ≤
    ∫ x in 1 / R..t, Real.sin (2 * Real.pi * R * x / 2) ^ 2 / x at hk
  rw [Real.log_div one_ne_zero hR.ne', Real.log_one, zero_sub, sub_neg_eq_add] at hk
  rw [show 2 * Real.pi * R * (1 / R) = 2 * Real.pi by field_simp] at hk
  simp_rw [show ∀ x : ℝ, 2 * Real.pi * R * x / 2 = Real.pi * R * x by intro x; ring] at hk
  have hi : IntervalIntegrable (fun x => s * (Real.sin (Real.pi * R * x) ^ 2 / x))
      volume (1 / R) t := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := intro x hx; exact (on_pos ha hat hx).ne')
  let W := fun x => S x * Real.sin (Real.pi * R * x) ^ 2 / x ^ 2
  have hw := hint R hR
  have hsub : Ioc (1 / R) t ⊆ Ioi 0 := fun _ hx => ha.trans hx.1
  have hiw : IntervalIntegrable W volume (1 / R) t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).2 (hw.mono_set hsub)
  have hmono := intervalIntegral.integral_mono_on hat hi hiw (fun x hx => by
    have hx0 := ha.trans_le hx.1
    have hxb : x < b := lt_of_le_of_lt hx.2 (by dsimp [t]; linarith)
    have hv := mul_le_mul_of_nonneg_right (hbad x hx0 hxb)
      (sq_nonneg (Real.sin (Real.pi * R * x)))
    dsimp [W]
    calc
      s * (Real.sin (Real.pi * R * x) ^ 2 / x) =
          s * x * Real.sin (Real.pi * R * x) ^ 2 / x ^ 2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hv (sq_nonneg _))
  rw [intervalIntegral.integral_const_mul] at hmono
  have hfull : (∫ x in Ioc (1 / R) t, W x) ≤ ∫ x in Ioi (0 : ℝ), W x :=
    setIntegral_mono_set hw (Filter.Eventually.of_forall (fun x => by
      dsimp [W]; exact div_nonneg (mul_nonneg (hpos x) (sq_nonneg _)) (sq_nonneg _))) hsub.eventuallyLE
  have hsl := mul_le_mul_of_nonneg_left hk (show 0 ≤ s by linarith)
  have hcontra := (div_lt_iff₀ (sub_pos.mpr hds)).1 hlog
  change 2 * (∫ x in Ioi (0 : ℝ), W x) ≤ d * Real.log R at hu
  simp only [intervalIntegral.integral_of_le hat] at hmono hsl
  have bound := hsl.trans (hmono.trans hfull)
  have hpi := Real.pi_pos
  have hp2 : 2 * (1 / (2 * Real.pi)) = 1 / Real.pi := by field_simp
  rw [← hp2] at hcontra
  nlinarith only [bound, hu, hcontra]

/-- The same cofinal window bound supplies one sequence usable by the
spectral interval theorem. -/
theorem small_steps_of_log_windowEnergy {S : ℝ → ℝ} (hpos : ∀ x, 0 ≤ S x)
    (hint : ∀ R > 0, IntegrableOn
      (fun x => S x * Real.sin (Real.pi * R * x) ^ 2 / x ^ 2) (Ioi (0 : ℝ)))
    {d s : ℝ} (hupper : ∃ᶠ R : ℝ in atTop, windowEnergy S R ≤ d * Real.log R)
    (hs : 0 < s) (hds : d < s) :
    ∃ h : ℕ → ℝ, (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧ ∀ n, S (h n) ≤ s * h n := by
  have H (n : ℕ) := exists_small_slope_of_log_windowEnergy hpos hint hupper hs hds
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose h hp hsize hslope using H
  exact ⟨h, hp, squeeze_zero (fun n => (hp n).le) (fun n => (hsize n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat, fun n => (hslope n).le⟩

#print axioms small_steps_of_log_windowEnergy

end RiemannResearch.Analysis.DPPNumberVariance

namespace RiemannResearch.DPPSpectral

open scoped FourierTransform

/-- A cofinal logarithmic bound strictly below the two-component coefficient
in the normalized spectral variance forces the interval and sine pair law. -/
theorem sine_pair_of_log_window_bound {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hm : (∫ t, f t) = 1)
    (hi : ∀ R > 0, IntegrableOn (fun x => structureFactor f x *
        Real.sin (Real.pi * R * x) ^ 2 / x ^ 2) (Ioi (0 : ℝ)))
    {d : ℝ} (hd : 0 ≤ d) (hd2 : d < 2)
    (hv : ∃ᶠ R : ℝ in atTop, Analysis.DPPNumberVariance.windowEnergy (structureFactor f) R ≤
        d * Real.log R) :
    ∃ a : ℝ, f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ) ∧ ∀ x : ℝ,
      1 - ‖𝓕 (fun t ↦ (f t : ℂ)) (-x)‖ ^ 2 = 1 - Real.sinc (Real.pi * x) ^ 2 := by
  let c := (d + 2) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hdc : d < c := by dsimp [c]; linarith
  have hc2 : c < 2 := by dsimp [c]; linarith
  obtain ⟨h, hp, hz, hs⟩ := Analysis.DPPNumberVariance.small_steps_of_log_windowEnergy
    (structureFactor_nonneg hf hb hm) hi hv hc hdc
  obtain ⟨a, ha⟩ := interval_spectrum_of_small_slope hf hb hm hp hz hc2 (Eventually.of_forall hs)
  exact ⟨a, ha, fourier_pair_of_interval_ae ha⟩

/--
info: 'RiemannResearch.DPPSpectral.sine_pair_of_log_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sine_pair_of_log_window_bound

end RiemannResearch.DPPSpectral
