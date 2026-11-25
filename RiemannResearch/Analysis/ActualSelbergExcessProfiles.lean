/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamLittlewoodDensity
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import RiemannResearch.Analysis.ActualSelbergDensityInterpolation
import RiemannResearch.Analysis.ActualSelbergNearExcessCriterion
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroDensityWindow
import RiemannResearch.Analysis.ActualZeroLogExcessIntegral
import RiemannResearch.Analysis.ActualZeroSublinearEnergy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform excess profiles in the Selberg transition window

Integration of the checked Ingham count preserves its local tangent and the
upper endpoint. Interpolating with the total count gives a uniform excess
bound at the quarter slope with a three-eighths power of the logarithm.

Baluyot, *On the Zeros of Riemann's Zeta-function* (2017), Theorem 1.2.1
and §3.6, supplies the open range of single-logarithm slopes used in the
final consequence. That analytic input is explicit in its Lean type.
<https://hdl.handle.net/1802/32855>
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Exact signed deviation of the Ingham exponent from its tangent at α. -/
theorem ingham_tangent_remainder {α σ : ℝ} (hα : α < 2) (hσ : σ < 2) :
    3 * (1 - σ) / (2 - σ) = 3 * (1 - α) / (2 - α) -
      3 / (2 - α) ^ 2 * (σ - α) -
      3 * (σ - α) ^ 2 / ((2 - α) ^ 2 * (2 - σ)) := by
  field_simp [ne_of_gt (sub_pos.mpr hα), ne_of_gt (sub_pos.mpr hσ)]
  ring

private theorem excess_le_of_anchored_count {H T α B k : ℝ}
    (hα : α ≤ 1) (hk : 0 < k)
    (hb : ∀ σ ∈ Icc α 1, rightInclusiveWindow H T σ ≤ B * Real.exp (-k * (σ - α))) :
    rightLogExcessWindow H T α ≤ B / k * (1 - Real.exp (-k * (1 - α))) := by
  let f (x : ℝ) := B * Real.exp (-k * (x - α))
  let F (x : ℝ) := -(B / k) * Real.exp (-k * (x - α))
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hd (x : ℝ) : HasDerivAt F (f x) x := by
    have hx : HasDerivAt (fun y : ℝ => -k * (y - α)) (-k) x := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id x).sub_const α).const_mul (-k)
    have he : HasDerivAt (fun y : ℝ => Real.exp (-k * (y - α)))
        (Real.exp (-k * (x - α)) * (-k)) x := (Real.hasDerivAt_exp _).comp x hx
    have hmul : -(B / k) * (Real.exp (-k * (x - α)) * (-k)) = f x := by
      dsimp [f]
      field_simp [hk.ne']
    have h := he.const_mul (-(B / k))
    rw [hmul] at h
    exact h
  rw [rightLogExcessWindow_eq_integral_rightInclusiveWindow H T α hα]
  calc
    _ ≤ ∫ x in α..(1 : ℝ), f x := intervalIntegral.integral_mono_on hα
      (intervalIntegrable_rightInclusiveWindow H T α 1) (hc.intervalIntegrable α 1) hb
    _ = F 1 - F α := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hd x) (hc.intervalIntegrable α 1)
    _ = _ := by simp only [F, sub_self, mul_zero, Real.exp_zero, mul_one]; ring

/-- Uniform, unconditional integrated Ingham bound. The tangent follows the
threshold α, and the right side vanishes at the endpoint α = 1. -/
theorem exists_ingham_tangent_logExcess :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 2 (Real.exp 1) ≤ T →
      ∀ H : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) 1,
        let L := Real.log T
        let q := 3 * (1 - α) / (2 - α)
        let k := 3 / (2 - α) ^ 2 * (L + Real.log L)
        rightLogExcessWindow H T α ≤ C * (T ^ q * L ^ (2 + q)) / k *
          (1 - Real.exp (-k * (1 - α))) := by
  obtain ⟨C, hC, hcount⟩ := exists_ingham_littlewood_density_all_heights
  refine ⟨C, hC, ?_⟩
  intro T hT H hHT α hα
  let L := Real.log T
  let K := L + Real.log L
  let q (x : ℝ) := 3 * (1 - x) / (2 - x)
  let s := 3 / (2 - α) ^ 2
  have ht2 := (le_max_left (2 : ℝ) (Real.exp 1)).trans hT
  have ht : 0 < T := by linarith
  have hL1 : 1 ≤ L := by
    simpa [L] using Real.log_le_log (Real.exp_pos 1) ((le_max_right 2 (Real.exp 1)).trans hT)
  have hL : 0 < L := by linarith
  have hK : 0 < K := add_pos_of_pos_of_nonneg hL (Real.log_nonneg hL1)
  have hα2 : α < 2 := by linarith only [hα.2]
  have hs : 0 < s := div_pos (by norm_num) (sq_pos_of_pos (sub_pos.mpr hα2))
  have hp (x : ℝ) : T ^ (q x) * L ^ (2 + q x) = L ^ (2 : ℕ) * Real.exp (K * q x) := by
    rw [Real.rpow_add hL, Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hL (q x),
      show K * q x = L * q x + Real.log L * q x by dsimp [K]; ring, Real.exp_add]
    norm_cast
    dsimp [L]
    ring
  apply excess_le_of_anchored_count hα.2 (mul_pos hs hK)
  intro σ hσ
  have hσ2 : σ < 2 := by linarith only [hσ.2]
  have hrem : 0 ≤ 3 * (σ - α) ^ 2 / ((2 - α) ^ 2 * (2 - σ)) :=
    div_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hσ2.le))
  have htan : q σ ≤ q α - s * (σ - α) := by
    dsimp [q, s]
    rw [ingham_tangent_remainder hα2 hσ2]
    exact sub_le_self _ hrem
  have hcurve : T ^ (q σ) * L ^ (2 + q σ) ≤
      T ^ (q α) * L ^ (2 + q α) * Real.exp (-(s * K) * (σ - α)) := by
    rw [hp σ, hp α, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg L)
    calc
      K * q σ ≤ K * (q α - s * (σ - α)) := mul_le_mul_of_nonneg_left htan hK.le
      _ = _ := by ring
  calc
    _ ≤ rightInclusiveCount T σ := by
      rw [rightInclusiveWindow_eq_sub hHT]
      exact sub_le_self _ (rightInclusiveCount_nonneg _ _)
    _ ≤ C * (T ^ (q σ) * L ^ (2 + q σ)) := (hcount T ht2 σ ⟨hα.1.trans hσ.1,hσ.2⟩).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
    _ ≤ C * (T ^ (q α) * L ^ (2 + q α) * Real.exp (-(s * K) * (σ - α))) :=
      mul_le_mul_of_nonneg_left hcurve hC.le
    _ = _ := by dsimp only [L, q, s, K]; ring

/-- Integrating a uniform log-loss count removes one logarithm and retains
the subtractive upper-endpoint term for every height window. -/
theorem UniformLogLossDensity.window_excess {a e : ℝ}
    (hD : UniformLogLossDensity a (1 + e)) (ha : 0 < a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop, ∀ H : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) 1,
      rightLogExcessWindow H T α ≤ D * T * Real.log T ^ e *
        (Real.exp (-(a * Real.log T) * (α - 1 / 2)) -
         Real.exp (-(a * Real.log T) * (1 - 1 / 2))) := by
  obtain ⟨C, T₀, hC, hT₀, hw⟩ := hD
  refine ⟨C / a, div_nonneg hC ha.le, ?_⟩
  filter_upwards [eventually_ge_atTop T₀] with T hT H hHT α hα
  have ht := hT₀.trans_le hT
  have hd : SelbergDensityBound T (C * Real.log T ^ e) a := by
    rw [selbergDensityBound_iff_exp T _ a (zero_lt_one.trans ht)]
    intro σ hσ
    have h := hw T hT σ hσ
    rw [Real.rpow_add (Real.log_pos ht), Real.rpow_one] at h
    linarith only [h]
  convert rightLogExcessWindow_le_of_selbergDensity hHT ht ha hα hd using 1
  ring

/-- The actual excess has surplus log power 3a/2 at every 0 < a ≤ 4/3;
in particular the uniform quarter-slope loss is only (log T)^(3/8). -/
theorem exists_interpolated_ingham_logExcess {a : ℝ} (ha : 0 < a) (ha' : a ≤ 4 / 3) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop, ∀ H : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) 1,
      rightLogExcessWindow H T α ≤ D * T * Real.log T ^ (3 * a / 2) *
        (Real.exp (-(a * Real.log T) * (α - 1 / 2)) -
         Real.exp (-(a * Real.log T) * (1 - 1 / 2))) := by
  have h := (uniformLogLossDensity_of_uniformSelberg 0 uniformSelbergDensity_zero).interpolate
    ingham_tangent_density_log_loss (r := 3 * a / 4) ⟨by linarith, by linarith⟩
  have hD : UniformLogLossDensity a (1 + 3 * a / 2) := by convert h using 1 <;> ring
  exact hD.window_excess ha

/-- A free split at β retains the total-count contribution on [α,β] and
integrates the unconditional Ingham tangent on [β,1]. -/
theorem exists_split_ingham_logExcess :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ H : ℝ, H ≤ T →
      ∀ α β : ℝ, 1 / 2 ≤ α → α ≤ β → β ≤ 1 →
      rightLogExcessWindow H T α ≤ C * T * ((β - α) * Real.log T +
        (Real.log T) ^ (2 : ℕ) * Real.exp (-((4 / 3 : ℝ) * Real.log T) * (β - 1 / 2))) := by
  obtain ⟨B, hB, hb⟩ := exists_count_le_height_log
  have hd : UniformLogLossDensity (4 / 3) (1 + 2) := by
    norm_num
    exact ingham_tangent_density_log_loss
  obtain ⟨D, hD, htail⟩ := hd.window_excess (by norm_num)
  refine ⟨max B D, hB.le.trans (le_max_left _ _), ?_⟩
  filter_upwards [htail, eventually_ge_atTop (9 : ℝ)] with T ht hT H hHT α β hα hab hβ
  have ht0 : 0 ≤ T := by linarith
  have hL : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  let f := rightInclusiveWindow H T
  have hcount (x : ℝ) : f x ≤ B * T * Real.log T := by
    dsimp [f]
    rw [rightInclusiveWindow_eq_sub hHT]
    exact (sub_le_self _ (rightInclusiveCount_nonneg _ _)).trans
      ((rightInclusiveCount_le_count T x).trans (hb T hT))
  have hleft : (∫ x in α..β, f x) ≤ (β - α) * (B * T * Real.log T) := by
    have h := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_rightInclusiveWindow H T α β)
      (continuous_const.intervalIntegrable α β (μ := volume))
      (fun x (_ : x ∈ Icc α β) => hcount x)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have hright := ht H hHT β ⟨hα.trans hab, hβ⟩
  have hcoef : 0 ≤ D * T * Real.log T ^ (2 : ℝ) :=
    mul_nonneg (mul_nonneg hD ht0) (Real.rpow_nonneg hL _)
  have hr := hright.trans (mul_le_mul_of_nonneg_left
    (sub_le_self _ (Real.exp_nonneg _)) hcoef)
  rw [Real.rpow_two] at hr
  have hparts : rightLogExcessWindow H T α =
      (∫ x in α..β, f x) + rightLogExcessWindow H T β := by
    rw [rightLogExcessWindow_eq_integral_rightInclusiveWindow H T α (hab.trans hβ),
      rightLogExcessWindow_eq_integral_rightInclusiveWindow H T β hβ]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_rightInclusiveWindow H T α β)
      (intervalIntegrable_rightInclusiveWindow H T β 1)).symm
  rw [hparts]
  apply (add_le_add hleft hr).trans
  let X := (β - α) * Real.log T
  let Y := (Real.log T)^2 * Real.exp (-((4/3 : ℝ)*Real.log T) * (β - 1/2))
  have hx : 0 ≤ T * X := mul_nonneg ht0 (mul_nonneg (sub_nonneg.mpr hab) hL)
  have hy : 0 ≤ T * Y := mul_nonneg ht0 (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
  calc
    _ = B * (T * X) + D * (T * Y) := by dsimp [X,Y]; ring
    _ ≤ max B D * (T * X) + max B D * (T * Y) := add_le_add
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hx)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hy)
    _ = _ := by dsimp [X,Y]; ring

/-- Optimizing the split gives linear excess below the crossover and
exponential decay above it, with a single unconditional constant. -/
theorem exists_ingham_logExcess_crossover :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ H : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) 1,
      let L := Real.log T
      let u := (α - 1 / 2) * L
      let w := (3 / 2 : ℝ) * Real.log L
      rightLogExcessWindow H T α ≤ C * T *
        (max 0 (w - u) + Real.exp (-(4 / 3 : ℝ) * max 0 (u - w))) := by
  obtain ⟨C, hC, hs⟩ := exists_split_ingham_logExcess
  refine ⟨C, hC, ?_⟩
  filter_upwards [hs, eventually_ge_atTop (Real.exp 24)] with T hsplit hT H hHT α hα
  let L := Real.log T
  let u := (α - 1 / 2) * L
  let w := (3 / 2 : ℝ) * Real.log L
  let m := 1 / 2 + w / L
  change rightLogExcessWindow H T α ≤
    C * T * (max 0 (w - u) + Real.exp (-(4 / 3 : ℝ) * max 0 (u - w)))
  have h24 : 24 ≤ L := by simpa [L] using Real.log_le_log (Real.exp_pos 24) hT
  have hL : 0 < L := by linarith
  have hcap : w / L ≤ 1 / 2 := by
    apply (div_le_iff₀ hL).mpr
    have hr := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num : (0 : ℝ) < 4))
    rw [Real.log_div hL.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hr
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    dsimp [w]
    linarith only [hr, h4, h24]
  have hscale : (m - 1 / 2) * L = w := by dsimp [m]; field_simp [hL.ne']; ring
  have hwexp (v : ℝ) : L ^ (2 : ℕ) * Real.exp (-(4 / 3 : ℝ) * v) =
      Real.exp (-(4 / 3 : ℝ) * (v - w)) := by
    rw [show -(4 / 3 : ℝ) * (v - w) =
      (Real.log L + Real.log L) + (-(4 / 3 : ℝ) * v) by dsimp [w]; ring,
      Real.exp_add, Real.exp_add, Real.exp_log hL, pow_two]
  by_cases near : u ≤ w
  · have hm : α ≤ m := by
      have h : α - 1 / 2 ≤ w / L := (le_div_iff₀ hL).mpr near
      dsimp [m]; linarith only [h]
    have hm1 : m ≤ 1 := by dsimp [m]; linarith only [hcap]
    have hx : (m - α) * L = w - u := by dsimp [u]; linarith only [hscale]
    have hb := hsplit H hHT α m hα.1 hm hm1
    change rightLogExcessWindow H T α ≤ C * T * ((m - α) * L +
      L ^ (2 : ℕ) * Real.exp (-((4 / 3 : ℝ) * L) * (m - 1 / 2))) at hb
    rw [show -((4 / 3 : ℝ) * L) * (m - 1 / 2) =
      -(4 / 3 : ℝ) * ((m - 1 / 2) * L) by ring, hscale, hwexp w,
      sub_self, mul_zero, Real.exp_zero, hx] at hb
    simpa only [max_eq_right (sub_nonneg.mpr near), max_eq_left (sub_nonpos.mpr near),
      mul_zero, Real.exp_zero] using hb
  · have far := le_of_not_ge near
    have hb := hsplit H hHT α α hα.1 le_rfl hα.2
    change rightLogExcessWindow H T α ≤ C * T * ((α - α) * L +
      L ^ (2 : ℕ) * Real.exp (-((4 / 3 : ℝ) * L) * (α - 1 / 2))) at hb
    rw [sub_self, zero_mul, zero_add, show -((4 / 3 : ℝ) * L) * (α - 1 / 2) =
      -(4 / 3 : ℝ) * u by dsimp [u]; ring, hwexp u] at hb
    simpa only [max_eq_left (sub_nonpos.mpr far), max_eq_right (sub_nonneg.mpr far),
      zero_add] using hb

/-- The subcritical published density range gives a uniform exponential
saving above any scaled displacement U, including every diverging threshold. -/
theorem ConreyBaluyotDensityHypothesis.window_excess_saving
    (h : ConreyBaluyotDensityHypothesis) {a b : ℝ} (ha : 0 < a) (hcap : a < 8 / 7)
    (hab : b ≤ a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop, ∀ H : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) 1,
      ∀ U : ℝ, U ≤ (α - 1 / 2) * Real.log T →
      rightLogExcessWindow H T α * Real.exp (b * ((α - 1 / 2) * Real.log T)) ≤
        D * T * Real.exp (-(a - b) * U) := by
  obtain ⟨C, T₀, hC, hT₀, hw⟩ := h a ha hcap
  refine ⟨C / a, div_nonneg hC ha.le, ?_⟩
  filter_upwards [eventually_ge_atTop T₀] with T hT H hHT α hα U hU
  have ht := hT₀.trans_le hT
  have hpos : 0 ≤ C / a * T := mul_nonneg (div_nonneg hC ha.le) (zero_lt_one.trans ht).le
  have he := rightLogExcessWindow_le_of_selbergDensity hHT ht ha hα (hw T hT)
  have hsingle := he.trans (mul_le_mul_of_nonneg_left
    (sub_le_self _ (Real.exp_nonneg _)) hpos)
  apply (mul_le_mul_of_nonneg_right hsingle (Real.exp_nonneg _)).trans
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hpos
  calc
    _ = -(a - b) * ((α - 1 / 2) * Real.log T) := by ring
    _ ≤ _ := mul_le_mul_of_nonpos_left hU (by linarith only [hab])

/-- info: 'RiemannResearch.Analysis.ActualZeroOrdinate.ingham_tangent_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ingham_tangent_remainder

/-- info: 'RiemannResearch.Analysis.ActualZeroOrdinate.exists_ingham_tangent_logExcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_ingham_tangent_logExcess

/-- info: 'RiemannResearch.Analysis.ActualZeroOrdinate.UniformLogLossDensity.window_excess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UniformLogLossDensity.window_excess

/-- info: 'RiemannResearch.Analysis.ActualZeroOrdinate.exists_interpolated_ingham_logExcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_interpolated_ingham_logExcess

/-- info: 'RiemannResearch.Analysis.ActualZeroOrdinate.exists_split_ingham_logExcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_split_ingham_logExcess

/-- info: 'RiemannResearch.Analysis.ActualZeroOrdinate.exists_ingham_logExcess_crossover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_ingham_logExcess_crossover

/-- info: 'RiemannResearch.Analysis.ActualZeroOrdinate.ConreyBaluyotDensityHypothesis.window_excess_saving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConreyBaluyotDensityHypothesis.window_excess_saving

end RiemannResearch.Analysis.ActualZeroOrdinate
