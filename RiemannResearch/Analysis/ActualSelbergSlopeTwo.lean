/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualBGSTBDensity
import RiemannResearch.Analysis.ActualCriticalFarStrip
import RiemannResearch.Analysis.ActualHuxleyKorobovVinogradov

/-!
# Extension of the strong density hypothesis to Selberg slope two

Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh, Section 6,
<https://arxiv.org/abs/2306.04799>. We extend their moving strip using the
repository's explicit Tao–Bourgain, Huxley and Vinogradov–Korobov source bounds.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem unweight_two {n T σ ε : ℝ} (hT : 0 < T)
    (h : n * T ^ (2 * (σ - 1 / 2)) ≤ ε * T) :
    n ≤ ε * T ^ (2 * (1 - σ)) := by
  apply (le_of_mul_le_mul_right _ (Real.rpow_pos_of_pos hT (2 * (σ - 1 / 2))))
  calc
    _ ≤ ε * T := h
    _ = ε * T ^ (2 * (1 - σ)) * T ^ (2 * (σ - 1 / 2)) := by
      rw [mul_assoc, ← Real.rpow_add hT, show 2 * (1 - σ) + 2 * (σ - 1 / 2) = 1 by ring,
        Real.rpow_one]

/-- A fixed overlap beyond 25/32 suffices to extend the uniform little-o
estimate through 1, including abscissae that move with the height. -/
theorem bgstbStripDensity_one_of_far_density {b : ℝ} (hb : 25 / 32 < b)
    (hs : BGSTBStripDensity b) (hD : TaoBourgainFarDensityHypothesis)
    (hH : HuxleyDensityHypothesis) (hv : BellottiKorobovVinogradovCount) :
    BGSTBStripDensity 1 := by
  let lo := min b (7 / 8)
  have hlo : 25 / 32 < lo := lt_min hb (by norm_num)
  have hhi : lo ≤ 7 / 8 := min_le_right _ _
  let E := farWeightedExcessBudget lo (7 / 8)
  have hE : E < 0 := max_lt (farWeightedExcess_negative hlo hhi)
    (farWeightedExcess_negative (hlo.trans_le hhi) le_rfl)
  obtain ⟨C, _, hc⟩ := weighted_compact_count_of_farDensity hD hlo hhi le_rfl
    (show 0 < -E / 2 by linarith)
  obtain ⟨D, _, hd⟩ := weighted_huxley_count_superlog hH hv (σ₀ := (7 / 8 : ℝ))
    (by norm_num) 1 zero_le_one
  have hcp : Tendsto (fun T : ℝ => C * T ^ (E / 2)) atTop (𝓝 0) := by
    simpa only [neg_neg, mul_zero] using
      (tendsto_rpow_neg_atTop (show 0 < -(E / 2) by linarith)).const_mul C
  have hdp : Tendsto (fun T : ℝ => D * (Real.log T) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop zero_lt_one).comp Real.tendsto_log_atTop).const_mul D
  intro ε hε
  filter_upwards [hs ε hε, hc, hd, hcp.eventually (gt_mem_nhds hε),
    hdp.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with T hsT hcT hdT hcε hdε hT
  intro σ hσ
  by_cases hleft : σ ≤ b
  · exact hsT σ ⟨hσ.1, hleft⟩
  apply unweight_two hT
  by_cases hmid : σ ≤ 7 / 8
  · have hm := hcT σ ⟨(min_le_left _ _).trans (le_of_not_ge hleft), hmid⟩
    have hexp : 1 + farWeightedExcessBudget lo (7 / 8) + -E / 2 = E / 2 + 1 := by
      change 1 + E + -E / 2 = E / 2 + 1
      ring
    rw [hexp, Real.rpow_add hT, Real.rpow_one, ← mul_assoc] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right hcε.le hT.le)
  · have hh := hdT σ ⟨le_of_not_ge hmid, hσ.2⟩
    calc
      _ ≤ _ := hh
      _ = (D * (Real.log T) ^ (-(1 : ℝ))) * T := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdε.le hT.le

/-- Selberg's full-strip one-log estimate at the attained exponent 2,
from the paper's short-strip hypothesis and the named classical far inputs. -/
theorem uniformSelbergDensity_two_of_bgstb {b : ℝ} (hb : 25 / 32 < b)
    (hs : BGSTBStripDensity b) (hD : TaoBourgainFarDensityHypothesis)
    (hH : HuxleyDensityHypothesis) (hv : BellottiKorobovVinogradovCount) :
    UniformSelbergDensity 2 :=
  uniformSelbergDensity_two_of_full_bgstb (bgstbStripDensity_one_of_far_density hb hs hD hH hv)

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_two_of_bgstb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniformSelbergDensity_two_of_bgstb

end RiemannResearch.Analysis.ActualZeroOrdinate
