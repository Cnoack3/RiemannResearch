/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

open Complex MeasureTheory Set

namespace RiemannResearch.Analysis

/-- Both real endpoints of a vertical strip give an integrable dominating
function for every Mellin transform argument inside the strip. -/
theorem norm_mellin_le_integral_endpoint_norms {f : ℝ → ℂ}
    {a b : ℝ} {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b)
    (hfa : MellinConvergent f (a : ℂ)) (hfb : MellinConvergent f (b : ℂ))
    (hfs : MellinConvergent f s) :
    ‖mellin f s‖ ≤
      ∫ t : ℝ in Ioi 0,
        (‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖ + ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖) := by
  unfold mellin
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono_ae hfs.norm (hfa.norm.add hfb.norm)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  simp only [Pi.add_apply, norm_smul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re, ofReal_re]
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rcases le_or_gt 1 t with ht1 | ht1
  · exact (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : s.re - 1 ≤ b - 1)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ht0.le _))
  · exact
      (Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by linarith : a - 1 ≤ s.re - 1)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _))

/-- The pole-removed completed zeta function is uniformly bounded on each
fixed vertical strip, as a Mellin transform converging at both endpoints. -/
theorem completedRiemannZeta₀_bounded_on_strip (a b : ℝ) :
    ∃ K : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖completedRiemannZeta₀ s‖ ≤ K := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  let f := P.f_modif
  have hconv (z : ℂ) : MellinConvergent f z :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin z).1
  let K : ℝ := ∫ t : ℝ in Ioi 0,
    (‖(t : ℂ) ^ (((a / 2 : ℝ) : ℂ) - 1) • f t‖ +
      ‖(t : ℂ) ^ (((b / 2 : ℝ) : ℂ) - 1) • f t‖)
  refine ⟨K / 2, ?_⟩
  intro s ha hb
  have hr : (s / 2 : ℂ).re = s.re / 2 := by
    norm_num [Complex.div_re]
  have hlo : a / 2 ≤ (s / 2 : ℂ).re := by rw [hr]; linarith
  have hhi : (s / 2 : ℂ).re ≤ b / 2 := by rw [hr]; linarith
  have hm : ‖mellin f (s / 2)‖ ≤ K :=
    norm_mellin_le_integral_endpoint_norms hlo hhi (hconv _) (hconv _) (hconv _)
  change ‖mellin f (s / 2) / 2‖ ≤ K / 2
  rw [norm_div]
  norm_num
  linarith

end RiemannResearch.Analysis
