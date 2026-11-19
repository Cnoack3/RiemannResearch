/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSelbergDensityInterpolation
import RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs

/-!
# Exponential moments at the critical Selberg slope

An arbitrarily small fixed logarithmic loss permits a slightly steeper
decay slope than 8/7. Integrating the tilted tail at exactly 8/7 then
costs only that logarithmic power. The height threshold and constant can
depend on the chosen loss. The moment is taken over actual zero copies.
-/

noncomputable section
open Filter Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs
open ActualZeroOrdinate

/-- A log-loss density estimate gives a moment bound with the identical
surplus log power at every strictly smaller nonnegative tilt. -/
theorem exponential_moment_of_logLoss {a b e : ℝ} (hD : UniformLogLossDensity a (1+e))
    (hb : 0 ≤ b) (hba : b < a) (he : 0 ≤ e) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop,
      (∑ i : Copies T, (Ncount 0 T : ℝ)⁻¹ * Real.exp (b * mark T i)) ≤
        K * Real.log T ^ e := by
  obtain ⟨C, H, hC, hH, hD⟩ := hD
  let c : ℝ := 1/(16*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  let A := (2*C/c) * (b/(a-b))
  have hA : 0 ≤ A := mul_nonneg (div_nonneg (by positivity) hc.le)
    (div_nonneg hb (sub_pos.mpr hba).le)
  refine ⟨1+A, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop H, eventually_ge_atTop (Real.exp 1),
    eventually_count_ge_log] with T hT ht hN
  have hT' := hH.trans_le hT
  have hL := Real.log_pos hT'
  have hL1 : 1 ≤ Real.log T := by simpa using Real.log_le_log (Real.exp_pos 1) ht
  let p := Real.log T ^ e
  have hp : 1 ≤ p := Real.one_le_rpow hL1 he
  have hd : SelbergDensityBound T (C*p) a := by
    rw [selbergDensityBound_iff_exp T (C*p) a (zero_lt_one.trans hT')]
    intro σ hσ
    have h := hD T hT σ hσ
    rw [Real.rpow_add hL, Real.rpow_one] at h
    dsimp [p]
    linarith only [h]
  have hbound := normalized_exp_mark_le hT' hb hba (mul_nonneg hC (zero_le_one.trans hp))
    hc hd hN
  refine hbound.trans ?_
  have hfactor : (2*(C*p)/c)*(b/(a-b)) = A*p := by dsimp [A]; ring
  rw [hfactor]
  have hcut : 1 - Real.exp (-((a-b)*Real.log T)/2) ≤ 1 := sub_le_self _ (Real.exp_nonneg _)
  nlinarith only [hp, mul_le_mul_of_nonneg_left hcut (mul_nonneg hA (zero_le_one.trans hp))]

/-- Critical tilted exponential moments grow more slowly than every fixed
positive logarithmic power. This is the exact 8/7 tilt. -/
theorem critical_exponential_moment_log_loss (h : ConreyBaluyotDensityHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop,
      (∑ i : Copies T, (Ncount 0 T : ℝ)⁻¹ * Real.exp ((8/7) * mark T i)) ≤
        K * Real.log T ^ ε := by
  let r := min (ε/2) (1/2)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr' : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let a := 8/7 + (2/21)*r
  have hba : 8/7 < a := by dsimp [a]; linarith
  have hlim : a < (1-r)*(8/7) + r*(4/3) := by dsimp [a]; linarith
  have hd := (h.interpolated_profile hr hr' hlim).weaken (le_refl a)
    (show 1+2*r ≤ 1+ε by linarith only [show r ≤ ε/2 from min_le_left _ _])
  exact exponential_moment_of_logLoss hd (by norm_num) hba hε.le

end RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs
