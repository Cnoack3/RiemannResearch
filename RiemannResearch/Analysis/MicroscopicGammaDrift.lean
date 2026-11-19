/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroDiscrepancy
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.StirlingVert
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Microscopic gamma drift in zero-count windows

Stirling's expansion for the logarithmic derivative of the gamma factor
controls the mean-square cost of replacing its exact increment by the
unfolded width. A finite-height estimate retains the square of the width,
so the gamma energy vanishes for every nonnegative width small relative
to the height logarithm, including growing mesoscopic windows.
For the count/argument comparison see GLSS, Proposition 2,
https://doi.org/10.1112/mtk.70127.
-/

open MeasureTheory Set Filter Zeta23
open scoped Topology Interval
noncomputable section

namespace RiemannResearch.Analysis.ActualZeroDiscrepancy

private theorem gamma_uniform_log_approx :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      |mu u - (1 / (2 * Real.pi)) * Real.log (1 + u)| ≤ C := by
  let k := 1 / (2 * Real.pi)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hcont : ContinuousOn (fun u : ℝ => mu u - k * Real.log (1+u)) (Icc 0 1) :=
    (RvM.mu_continuous gammaFacts).continuousOn.sub (continuousOn_const.mul
      ((continuous_const.add continuous_id).continuousOn.log (fun u hu => by
        change 1+u ≠ 0
        linarith [hu.1])))
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨A, hA⟩ := Zeta23.StirlingVert.mu_stirling
  refine ⟨|D| + |A| + k * (|Real.log (2 * Real.pi)| + 1), by positivity, ?_⟩
  intro u hu
  change |mu u - k * Real.log (1+u)| ≤ _
  by_cases hu1 : u ≤ 1
  · have he := hD u ⟨hu,hu1⟩
    rw [Real.norm_eq_abs] at he
    have hconst : 0 ≤ k * (|Real.log (2 * Real.pi)| + 1) := by positivity
    exact he.trans (by linarith only [le_abs_self D, abs_nonneg A, hconst])
  have hu' : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hb := hA u (by simpa [abs_of_nonneg hu] using hu')
  rw [abs_of_nonneg hu, Real.log_div hu0.ne' (by positivity)] at hb
  have ha' : A / u^2 ≤ |A| := by
    apply (div_le_iff₀ (by positivity : 0 < u^2)).2
    calc A ≤ |A| := le_abs_self _
      _ ≤ |A| * u^2 := le_mul_of_one_le_right (abs_nonneg _) (by nlinarith)
  have huplus : Real.log (1+u) - Real.log u ≤ 1 := by
    rw [← Real.log_div (by positivity) hu0.ne']
    have hi := Real.log_le_sub_one_of_pos (by positivity : 0 < (1+u)/u)
    have hr : (1+u)/u ≤ 2 := (div_le_iff₀ hu0).2 (by linarith)
    linarith
  have hlu := Real.log_le_log hu0 (show u ≤ 1+u by linarith)
  change |mu u - k * (Real.log u - Real.log (2 * Real.pi))| ≤ _ at hb
  rw [abs_le] at hb ⊢
  have hmul1 := mul_le_mul_of_nonneg_left huplus hk
  have hmul2 := mul_le_mul_of_nonneg_left hlu hk
  have hp1 := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (2 * Real.pi))) hk
  have hp2 := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log (2 * Real.pi))) hk
  constructor <;> nlinarith [abs_nonneg D, hb.1, hb.2]

/-- The second moment of the logarithmic drift admits a uniform linear bound.
The primitive at the lower endpoint is nonnegative. -/
private theorem integral_log_drift_sq_le {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (Real.log (1+t) - Real.log (1+T))^2) ≤ 2 * (1+T) := by
  let L := fun x : ℝ => Real.log (1+x) - Real.log (1+T)
  let P := fun x : ℝ => (1+x) * ((L x)^2 - 2 * L x + 2)
  have hD (x : ℝ) (hx : 0 ≤ x) : HasDerivAt P ((L x)^2) x := by
    have hp : 0 < 1+x := by linarith
    have h1 : HasDerivAt (fun y : ℝ => 1+y) 1 x := by simpa using (hasDerivAt_id x).const_add 1
    have hl : HasDerivAt L (1 / (1+x)) x := by
      simpa [L] using (h1.log hp.ne').sub_const (Real.log (1+T))
    have hh := h1.mul (((hl.pow 2).sub (hl.const_mul 2)).add_const 2)
    convert hh using 1 <;> first | rfl | (try dsimp [P]; field_simp [hp.ne']; ring)
  have hc : ContinuousOn L (uIcc 0 T) := by
    refine ((continuous_const.add continuous_id).continuousOn.log ?_).sub continuousOn_const
    rw [uIcc_of_le hT]
    intro x hx
    change 1+x ≠ 0; linarith [hx.1]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := P)
    (fun x hx => hD x (by rw [uIcc_of_le hT] at hx; exact hx.1))
    ((hc.pow 2).intervalIntegrable)
  change (∫ x in (0 : ℝ)..T, (L x)^2) ≤ _
  rw [hi]
  have hz : 0 ≤ P 0 := by dsimp [P]; nlinarith [sq_nonneg (L 0 - 1)]
  have hPT : P T = (1+T)*2 := by simp [P,L]
  linarith

/-- Exact gamma drift at the physical length corresponding to unfolded width R. -/
def microscopicGammaDrift (T R t : ℝ) : ℝ :=
  smoothCount (t + R / (Real.log T / (2 * Real.pi))) - smoothCount t - R

/-- A single finite-height constant controls every nonnegative unfolded width
whose physical window has length at most one. The width remains explicit,
so this estimate also applies when the unfolded width grows with height. -/
theorem microscopicGammaDrift_mean_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T R : ℝ, 1 < T → 0 ≤ R →
      R ≤ Real.log T / (2 * Real.pi) →
      (∫ t in (0 : ℝ)..T, microscopicGammaDrift T R t ^ 2) / T ≤
        C * R ^ 2 / (Real.log T)^2 := by
  obtain ⟨A,hA,happrox⟩ := gamma_uniform_log_approx
  let k := 1 / (2 * Real.pi)
  have hk : 0 < k := by dsimp [k]; positivity
  let D := A + 2*k
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨(2 * Real.pi)^2 * (2*D^2 + 8*k^2), by positivity, ?_⟩
  intro T R hT hR hRmax
  have hTp : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  let h := R / (Real.log T / (2 * Real.pi))
  have hh : 0 ≤ h := div_nonneg hR (by positivity)
  have heq : h = 2 * Real.pi * R / Real.log T := by dsimp [h]; field_simp [Real.pi_ne_zero,hL.ne'] <;> ring
  have h1 : h ≤ 1 := by
    change R / (Real.log T / (2 * Real.pi)) ≤ 1
    apply (div_le_iff₀ (by positivity : 0 < Real.log T / (2 * Real.pi))).2
    simpa only [one_mul] using hRmax
  have hc : Continuous (microscopicGammaDrift T R) := by
    exact ((smoothCount_continuous.comp (continuous_id.add continuous_const)).sub
      smoothCount_continuous).sub continuous_const
  let L := fun t : ℝ => Real.log (1+t) - Real.log (1+T)
  have hLc : ContinuousOn L (uIcc 0 T) := by
    refine ((continuous_const.add continuous_id).continuousOn.log ?_).sub continuousOn_const
    rw [uIcc_of_le hTp.le]; intro t ht; change 1+t ≠ 0; linarith [ht.1]
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 T) :
      microscopicGammaDrift T R t ^ 2 ≤ h^2 * (2*D^2 + 2*k^2*(L t)^2) := by
    have hlneg : L t ≤ 0 := sub_nonpos.mpr (Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2]))
    have hinc : microscopicGammaDrift T R t = ∫ u in t..(t+h), (mu u - k * Real.log T) := by
      change smoothCount (t+h) - smoothCount t - R = _
      rw [smoothCount_sub, intervalIntegral.integral_sub
        ((RvM.mu_continuous gammaFacts).intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const]
      dsimp [h,k]; field_simp [Real.pi_ne_zero,hL.ne'] <;> ring
    have habs := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t+h) (f := fun u => mu u - k * Real.log T) (C := D-k*L t) (by
        intro u hu
        rw [uIoc_of_le (by linarith)] at hu
        have hu0 : 0 ≤ u := ht.1.trans hu.1.le
        have ha := happrox u hu0
        change |mu u - k*Real.log (1+u)| ≤ A at ha
        have hlt := Real.log_le_log (by linarith [ht.1] : 0 < 1+t) (by linarith [hu.1] : 1+t ≤ 1+u)
        have hgu := Real.log_le_log (by linarith : 0 < 1+u)
          (show 1+u ≤ 3*T by linarith [hu.2,ht.2])
        rw [Real.log_mul (by norm_num) hTp.ne'] at hgu
        have hpos := Real.log_le_log hTp (by linarith : T ≤ 1+T)
        have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
        rw [Real.norm_eq_abs, abs_le]
        rw [abs_le] at ha
        dsimp [D,L]
        change Real.log (1+t) - Real.log (1+T) ≤ 0 at hlneg
        constructor <;> nlinarith [ha.1, ha.2,mul_le_mul_of_nonneg_left hlt hk.le,
          mul_le_mul_of_nonneg_left hgu hk.le, mul_le_mul_of_nonneg_left hpos hk.le,
          mul_le_mul_of_nonneg_left h3 hk.le, mul_nonpos_of_nonneg_of_nonpos hk.le hlneg])
    rw [← hinc, Real.norm_eq_abs, show t+h-t=h by ring, abs_of_nonneg hh] at habs
    have hs := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hs
    calc _ ≤ ((D-k*L t)*h)^2 := hs
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg h) (sq_nonneg (D+k*L t))]
  have hind := intervalIntegral.integral_mono_on (μ := volume) hTp.le ((hc.pow 2).intervalIntegrable _ _)
    ((continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul (hLc.pow 2)))).intervalIntegrable)
    hpoint
  change (∫ t in (0 : ℝ)..T, microscopicGammaDrift T R t ^ 2) ≤
    (∫ t in (0 : ℝ)..T, h^2 * (2*D^2 + 2*k^2*(L t)^2)) at hind
  have hil : IntervalIntegrable (fun t => 2*k^2*(L t)^2) volume (0 : ℝ) T :=
    (continuousOn_const.mul (hLc.pow 2)).intervalIntegrable
  rw [intervalIntegral.integral_const_mul (h^2) (fun t => 2*D^2 + 2*k^2*(L t)^2),
    intervalIntegral.integral_add intervalIntegrable_const hil,
    intervalIntegral.integral_const_mul (2*k^2) (fun t => (L t)^2),
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hind
  have hlInt := integral_log_drift_sq_le hTp.le
  change (∫ t in (0 : ℝ)..T, (L t)^2) ≤ 2*(1+T) at hlInt
  have hsum : (T*(2*D^2) + (2*k^2)*(∫ t in (0:ℝ)..T, (L t)^2)) ≤ T*(2*D^2+8*k^2) := by
    nlinarith [mul_le_mul_of_nonneg_left hlInt (by positivity : 0 ≤ 2*k^2),
      mul_nonneg (show 0 ≤ T-1 by linarith) (sq_nonneg k)]
  calc _ ≤ (h^2 * (T*(2*D^2+8*k^2))) / T := div_le_div_of_nonneg_right
        (hind.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg h))) hTp.le
    _ = h^2 * (2*D^2+8*k^2) := by field_simp [hTp.ne'] <;> ring
    _ = _ := by rw [heq, div_pow]; ring

/-- Uniform in bounded unfolded width: the mean-square gamma drift is
bounded by a constant times the inverse square of the height logarithm. -/
theorem microscopicGammaDrift_mean_sq_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ R ∈ Icc 0 B,
      (∫ t in (0 : ℝ)..T, microscopicGammaDrift T R t ^ 2) / T ≤
        C / (Real.log T)^2 := by
  obtain ⟨C, hC, hbound⟩ := microscopicGammaDrift_mean_sq_le
  refine ⟨C * B ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.pi * B)] with T hT hlog
  intro R hr
  have hRmax : R ≤ Real.log T / (2 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    calc
      R * (2 * Real.pi) ≤ B * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hr.2 (by positivity)
      _ ≤ Real.log T := by simpa only [mul_comm] using hlog
  exact (hbound T R hT hr.1 hRmax).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1 hr.2 2) hC)
      (sq_nonneg _))

/-- The gamma drift vanishes in normalized mean square for every eventually
nonnegative unfolded width that is small relative to the height logarithm.
The width need not remain bounded. -/
theorem microscopicGammaDrift_mean_sq_tendsto_zero {R : ℝ → ℝ}
    (hR : ∀ᶠ T : ℝ in atTop, 0 ≤ R T)
    (hRlog : Tendsto (fun T : ℝ => R T / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..T, microscopicGammaDrift T (R T) t ^ 2) / T)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := microscopicGammaDrift_mean_sq_le
  have hmajor : Tendsto (fun T : ℝ => C * (R T / Real.log T) ^ 2)
      atTop (𝓝 0) := by
    simpa using (hRlog.pow 2).const_mul C
  have hnonneg : ∀ᶠ T : ℝ in atTop,
      0 ≤ (∫ t in (0 : ℝ)..T, microscopicGammaDrift T (R T) t ^ 2) / T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact div_nonneg
      (intervalIntegral.integral_nonneg hT.le (fun _ _ => sq_nonneg _)) hT.le
  have hle : ∀ᶠ T : ℝ in atTop,
      (∫ t in (0 : ℝ)..T, microscopicGammaDrift T (R T) t ^ 2) / T ≤
        C * (R T / Real.log T) ^ 2 := by
    filter_upwards [hR, eventually_gt_atTop (1 : ℝ),
      hRlog.eventually_le_const (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
      with T hRT hT hsmall
    have hRmax : R T ≤ Real.log T / (2 * Real.pi) := by
      have hh := (div_le_iff₀ (Real.log_pos hT)).mp hsmall
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hh
    simpa only [div_pow, mul_div_assoc] using hbound T (R T) hT hRT hRmax
  exact squeeze_zero' hnonneg hle hmajor

/-- Uniform vanishing as an eventual upper envelope for the normalized gamma energy. -/
theorem microscopicGammaDrift_mean_sq_vanishes_uniformly (B : ℝ) (hB : 0 ≤ B) :
    ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ T : ℝ in atTop,
      ∀ R ∈ Icc 0 B, (∫ t in (0 : ℝ)..T, microscopicGammaDrift T R t ^ 2) / T ≤ e T := by
  obtain ⟨C, _, hC⟩ := microscopicGammaDrift_mean_sq_bound B hB
  refine ⟨fun T => C / (Real.log T)^2, ?_, hC⟩
  have hi := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).pow 2
  simpa [Function.comp_def,div_eq_mul_inv] using hi.const_mul C

end RiemannResearch.Analysis.ActualZeroDiscrepancy
