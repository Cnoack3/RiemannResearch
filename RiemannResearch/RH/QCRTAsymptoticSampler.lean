/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.GcdSamplePrimeTail
import RiemannResearch.RH.QCRTProjectedMellin
import RiemannResearch.RH.QCRTZeroGrowth
import RiemannResearch.RH.QCRTZeroObstruction
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Asymptotic factor one for the actual CRT Mellin detector

Source: the user's CRT collocation handoff, Section 7, and the sampler
continuation in CRTCollocationStabilityResearch20261107, Section 6.
Bagchi, Proc. Indian Acad. Sci. Math. Sci. 116 (2006), 137--146,
Theorems 2/5 (https://arxiv.org/abs/math/0607733), supports the underlying
Mellin zero-annihilator strategy, not the new arithmetic sampler estimates.

The complete sampled tail is negligible relative to the escape tail. This
sharpens the actual projected Mellin operator bound to every factor 1+epsilon
eventually. At a hypothetical zero the full endpoint and leakage remain in
the obstruction. The final RH implication is a conditional research reduction:
cofinal smallness of the actual canonical escape-energy product remains Open.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QCRTAsymptoticSampler
open ZetaTwoHilbert ZetaTwoProbability QMellinTransfer QDivisibilityDensity
open QCRTFiniteCollocation QCRTZeroObstruction QCRTProjectedMellin QCRTZeroGrowth
open RiemannResearch.NumberTheory.DivisorEscapeTail

/-- The actual projected Mellin operator has asymptotic sampler factor one.
This bounds the detector, not the norm of the moving canonical vectors. -/
theorem eventually_tailMellin_norm_le_one_add
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ‖tailMellin (Nat.lcmUpto M) s hs‖ ≤
      (1 + ε) * Real.sqrt (zetaTwo * tail (2 * s.re) (Nat.lcmUpto M)) := by
  have hsmall := eventually_sampleTail_le_mul_tail (2*s.re) (by linarith)
    (by linarith) (ε^2) (sq_pos_of_pos hε)
  filter_upwards [hsmall] with M hM
  have hroot : Real.sqrt (sampleTail (2*s.re) (Nat.lcmUpto M)) ≤
      ε * Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)) := by
    have hS := Real.sq_sqrt (sampleTail_nonneg (2*s.re) (Nat.lcmUpto M))
    have hD := Real.sq_sqrt (tail_nonneg (2*s.re) (Nat.lcmUpto M))
    have he : (ε * Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)))^2 =
        ε^2 * tail (2*s.re) (Nat.lcmUpto M) := by rw [mul_pow, hD]
    have hn : 0 ≤ ε * Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)) := by positivity
    nlinarith [Real.sqrt_nonneg (sampleTail (2*s.re) (Nat.lcmUpto M))]
  calc
    _ ≤ Real.sqrt zetaTwo * (Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)) +
        Real.sqrt (sampleTail (2*s.re) (Nat.lcmUpto M))) :=
      tailMellin_norm_le_separated s hs hs1.le _ (Nat.lcmUpto_pos M)
    _ ≤ Real.sqrt zetaTwo * (Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)) +
        ε * Real.sqrt (tail (2*s.re) (Nat.lcmUpto M))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hroot) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul zetaTwo_pos.le]; ring

/-- At an actual right-half-strip zero, the improved detector still retains
the complete multiples endpoint and the entire canonical leakage. -/
theorem eventually_canonical_obstruction
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, 1 / ‖s‖ ≤
      ‖qMellin (qDivisor (lcmStage M)) s‖ +
      ((1 + ε) * Real.sqrt (zetaTwo * tail (2*s.re) (lcmStage M))) *
        Real.sqrt (lcmLeakage M) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_tailMellin_norm_le_one_add s hs hs1 ε hε)
  filter_upwards [eventually_ge_atTop N] with M hM
  have hsne : s ≠ 1 := by intro h; norm_num [h] at hs1
  exact (canonical_mellin_obstruction (lcmStage M) (lcmStage_two_le M)
      s hs hsne hz).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (hN (M+2) (by omega)) (Real.sqrt_nonneg _)))

/-- Every hypothetical right-half-strip zero forces an explicit lower
budget in the actual complete leakage, with an arbitrarily small loss. -/
theorem eventually_escape_leakage_floor
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ M : ℕ in atTop,
      (1 - ε)^2 / ((1 + ε)^2 * zetaTwo * ‖s‖^2) ≤
        tail (2*s.re) (lcmStage M) * lcmLeakage M := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hZ := zetaTwo_pos
  have hE := (lcm_endpoint_tendsto_zero s hs).eventually
    (gt_mem_nhds (show 0 < ε / ‖s‖ by positivity))
  filter_upwards [eventually_canonical_obstruction s hs hs1 hz ε hε, hE] with M hM hEM
  let B := (1 + ε) * Real.sqrt (zetaTwo * tail (2*s.re) (lcmStage M)) *
    Real.sqrt (lcmLeakage M)
  have hgap : (1 - ε) / ‖s‖ ≤ B := by
    dsimp [B]
    have he : (1 - ε) / ‖s‖ = 1 / ‖s‖ - ε / ‖s‖ := by ring
    rw [he]
    linarith
  have hsq := pow_le_pow_left₀ (show 0 ≤ (1-ε)/‖s‖ by positivity) hgap 2
  have hB : B^2 = (1+ε)^2 * zetaTwo *
      (tail (2*s.re) (lcmStage M) * lcmLeakage M) := by
    dsimp [B]
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (mul_nonneg zetaTwo_pos.le (tail_nonneg _ _)),
      Real.sq_sqrt (lcmLeakage_nonneg M)]
    ring
  rw [hB] at hsq
  apply (div_le_iff₀ (show 0 < (1+ε)^2 * zetaTwo * ‖s‖^2 by positivity)).mpr
  calc
    _ = ((1-ε)/‖s‖)^2 * ‖s‖^2 := by field_simp
    _ ≤ ((1+ε)^2 * zetaTwo *
        (tail (2*s.re) (lcmStage M) * lcmLeakage M)) * ‖s‖^2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖s‖)
    _ = _ := by ring

/-- Conditional research reduction: cofinally arbitrarily small complete
escape-energy products imply Mathlib RH. The canonical growth condition
is explicit; no provider for it is assumed to have been established. -/
theorem riemannHypothesis_of_cofinal_escape_energy
    (hsmall : ∀ t : ℝ, 1 < t → t < 2 → ∀ c : ℝ, 0 < c →
      ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
        tail t (lcmStage M) * ‖lcmLift M‖^2 < c) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hs1 hz
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  let c : ℝ := (1-(1/2 : ℝ))^2 / ((1+(1/2 : ℝ))^2*zetaTwo*‖s‖^2)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by norm_num)
      (mul_pos (mul_pos (by norm_num) zetaTwo_pos) (sq_pos_of_pos hsn))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_escape_leakage_floor s hs hs1 hz (1/2) (by norm_num) (by norm_num))
  obtain ⟨M, hNM, hM⟩ := hsmall (2*s.re) (by linarith) (by linarith) c hc N
  have hle : c ≤ tail (2*s.re) (lcmStage M) * ‖lcmLift M‖^2 :=
    (hN M hNM).trans (mul_le_mul_of_nonneg_left
      (lcmLeakage_le_norm_sq M) (tail_nonneg _ _))
  exact (not_lt_of_ge hle) hM

/-- A quantitative version of asymptotic factor one, with no logarithmic loss
in the relative arithmetic sampler bound. -/
theorem eventually_tailMellin_norm_le_power
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re < 1) :
    ∀ᶠ M : ℕ in atTop, ‖tailMellin (Nat.lcmUpto M) s hs‖ ≤
      (1 + Real.sqrt (sampleRatioConstant (2*s.re)) * (M : ℝ)^(s.re-1)) *
        Real.sqrt (zetaTwo * tail (2*s.re) (Nat.lcmUpto M)) := by
  have ht : 1 < 2*s.re := by linarith
  have ht2 : 2*s.re ≤ 2 := by linarith
  filter_upwards [eventually_sampleTail_div_tail_le_power (2*s.re) ht ht2,
    eventually_ge_atTop (1 : ℕ)] with M hM hMpos
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsmall := (div_le_iff₀
    (tail_pos (2*s.re) ht ht2 _ (Nat.lcmUpto_pos M))).mp hM
  let e := Real.sqrt (sampleRatioConstant (2*s.re)) * (M : ℝ)^(s.re-1)
  have he : 0 ≤ e := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hMR.le _)
  have he2 : e^2 = sampleRatioConstant (2*s.re) * (M : ℝ)^(2*s.re-2) := by
    dsimp [e]
    rw [mul_pow, Real.sq_sqrt (sampleRatioConstant_pos (2*s.re) ht).le]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_mul hMR.le]
    congr 1
    ring
  have hroot : Real.sqrt (sampleTail (2*s.re) (Nat.lcmUpto M)) ≤
      e * Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)) := by
    have hS := Real.sq_sqrt (sampleTail_nonneg (2*s.re) (Nat.lcmUpto M))
    have hD := Real.sq_sqrt (tail_nonneg (2*s.re) (Nat.lcmUpto M))
    have heD : (e * Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)))^2 =
        sampleRatioConstant (2*s.re) * (M : ℝ)^(2*s.re-2) *
          tail (2*s.re) (Nat.lcmUpto M) := by rw [mul_pow, hD, he2]
    have hn : 0 ≤ e * Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)) :=
      mul_nonneg he (Real.sqrt_nonneg _)
    nlinarith [Real.sqrt_nonneg (sampleTail (2*s.re) (Nat.lcmUpto M))]
  calc
    _ ≤ Real.sqrt zetaTwo * (Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)) +
        Real.sqrt (sampleTail (2*s.re) (Nat.lcmUpto M))) :=
      tailMellin_norm_le_separated s hs hs1.le _ (Nat.lcmUpto_pos M)
    _ ≤ Real.sqrt zetaTwo * (Real.sqrt (tail (2*s.re) (Nat.lcmUpto M)) +
        e * Real.sqrt (tail (2*s.re) (Nat.lcmUpto M))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hroot) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul zetaTwo_pos.le]; dsimp [e]; ring

end RiemannResearch.RH.QCRTAsymptoticSampler
