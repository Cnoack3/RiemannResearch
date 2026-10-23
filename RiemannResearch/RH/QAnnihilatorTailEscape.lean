/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteSupportDualEstimates
import RiemannResearch.RH.QMobiusStretchedEnergy
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact defect-tail identities for all complete-Q annihilators

Source: continuation of the user-provided uniform dual bound agenda,
22 October 2026. These are Hilbert-space consequences of the existing concrete
Möbius exact heads. The arithmetic residual-tail provider remains Open.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QAnnihilatorTailEscape
open ZetaTwoHilbert QFiniteSupportDualCriterion QFiniteSupportDualEstimates

def defect (M : ℕ) : QHilbert := qOne - QMobiusExactHead.exactHead M

def tail (M : ℕ) (u : QHilbert) : QHilbert := u - finiteHead M u

def actualResidual : QHilbert := qOne - QFullResidueProjection.closure.starProjection qOne

theorem tail_tendsto_zero (u : QHilbert) :
    Tendsto (fun M => tail M u) atTop (𝓝 0) := by
  simpa only [tail, sub_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u)).sub
      (finiteHead_tendsto u)

theorem defect_inner_finiteHead (M : ℕ) (u : QHilbert) :
    inner ℝ (defect M) (finiteHead M u) = 0 := by
  rw [defect, inner_sub_left, exactHead_finite_test_pairing, sub_self]

/-- Exact identity, with every signed summand retained. -/
theorem annihilator_defect_tail_identity (M : ℕ) (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ) :
    inner ℝ (defect M) (tail M u) = inner ℝ qOne u := by
  have he : QMobiusExactHead.exactHead M ∈ QFullResidueProjection.closure :=
    QFullResidueProjection.legalSpan.le_topologicalClosure
      (QMobiusExactHead.exactHead_mem_legalSpan M)
  have hz := Submodule.inner_right_of_mem_orthogonal he hu
  rw [tail, inner_sub_right, defect_inner_finiteHead, sub_zero,
    defect, inner_sub_left, hz, sub_zero]

theorem annihilator_defect_tail_bound (M : ℕ) (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ) :
    |inner ℝ qOne u| ≤ ‖defect M‖ * ‖tail M u‖ := by
  rw [← annihilator_defect_tail_identity M u hu]
  exact abs_real_inner_le_norm _ _

theorem annihilator_defect_tail_sq_bound (M : ℕ) (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ) :
    (inner ℝ qOne u) ^ 2 ≤ ‖defect M‖ ^ 2 * ‖tail M u‖ ^ 2 := by
  have h := annihilator_defect_tail_bound M u hu
  have hn := mul_nonneg (norm_nonneg (defect M)) (norm_nonneg (tail M u))
  have hs := mul_self_le_mul_self (abs_nonneg (inner ℝ qOne u)) h
  nlinarith [sq_abs (inner ℝ qOne u)]

theorem actualResidual_mem_orthogonal :
    actualResidual ∈ QFullResidueProjection.closureᗮ :=
  Submodule.sub_starProjection_mem_orthogonal (K := QFullResidueProjection.closure) qOne

theorem actualResidual_mean : inner ℝ qOne actualResidual = ‖actualResidual‖ ^ 2 := by
  have hz := Submodule.inner_right_of_mem_orthogonal
    (QFullResidueProjection.closure.starProjection_apply_mem qOne)
    actualResidual_mem_orthogonal
  have hh : inner ℝ actualResidual actualResidual = inner ℝ qOne actualResidual := by
    change inner ℝ (qOne - QFullResidueProjection.closure.starProjection qOne)
      actualResidual = _
    rw [inner_sub_left, hz, sub_zero]
  rw [← real_inner_self_eq_norm_sq, hh]

/-- A bound at every head, without an eventual quarter-constant loss. -/
theorem actualResidual_fourth_le (M : ℕ) :
    ‖actualResidual‖ ^ 4 ≤ ‖defect M‖ ^ 2 * ‖tail M actualResidual‖ ^ 2 := by
  have h := annihilator_defect_tail_sq_bound M actualResidual actualResidual_mem_orthogonal
  rw [actualResidual_mean] at h
  nlinarith

theorem defect_norm_sq_le (M : ℕ) :
    ‖defect M‖ ^ 2 ≤ 2 + 2 * dualHeadConstant M ^ 2 := by
  have h : ‖defect M‖ ≤ 1 + dualHeadConstant M := by
    simpa only [defect, dualHeadConstant, qOne_norm] using
      norm_sub_le qOne (QMobiusExactHead.exactHead M)
  have hn : 0 ≤ dualHeadConstant M := norm_nonneg _
  nlinarith [sq_nonneg (dualHeadConstant M - 1), norm_nonneg (defect M)]

theorem defect_sq_sublinear :
    Tendsto (fun M => ‖defect M‖ ^ 2 / (M : ℝ)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun M : ℕ => (1 : ℝ) / M) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hlim : Tendsto (fun M : ℕ => 2 / (M : ℝ) +
      2 * (dualHeadConstant M ^ 2 / (M : ℝ))) atTop (𝓝 0) := by
    have h := (hinv.const_mul 2).add (dualHeadConstant_sq_sublinear.const_mul 2)
    simpa only [mul_zero, zero_add, mul_one_div] using h
  apply squeeze_zero (fun M => div_nonneg (sq_nonneg _) (Nat.cast_nonneg M)) _ hlim
  intro M
  calc
    ‖defect M‖ ^ 2 / (M : ℝ) ≤ (2 + 2 * dualHeadConstant M ^ 2) / M :=
      div_le_div_of_nonneg_right (defect_norm_sq_le M) (Nat.cast_nonneg M)
    _ = _ := by ring

/- A positive weight permits sharper arithmetic envelopes as they become available. -/
theorem annihilator_weighted_tail_tendsto_atTop
    (u : QHilbert) (hu : u ∈ QFullResidueProjection.closureᗮ)
    (hm : inner ℝ qOne u ≠ 0) (w : ℕ → ℝ)
    (hw : ∀ᶠ M in atTop, 0 < w M)
    (hsmall : Tendsto (fun M => ‖defect M‖ ^ 2 / w M) atTop (𝓝 0)) :
    Tendsto (fun M => w M * ‖tail M u‖ ^ 2) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let b : ℝ := max B 0 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hBb : B < b := by dsimp [b]; linarith [le_max_left B 0]
  have hc : 0 < (inner ℝ qOne u) ^ 2 := sq_pos_of_ne_zero hm
  have heps : 0 < (inner ℝ qOne u) ^ 2 / b := div_pos hc hb
  have hupper := (tendsto_order.1 hsmall).2 _ heps
  filter_upwards [hw, hupper] with M hwM hs
  have hratio : 0 ≤ ‖defect M‖ ^ 2 / w M := div_nonneg (sq_nonneg _) hwM.le
  have hid : (‖defect M‖ ^ 2 / w M) * (w M * ‖tail M u‖ ^ 2) =
      ‖defect M‖ ^ 2 * ‖tail M u‖ ^ 2 := by
    field_simp
  have hp : (inner ℝ qOne u) ^ 2 ≤
      (‖defect M‖ ^ 2 / w M) * (w M * ‖tail M u‖ ^ 2) := by
    rw [hid]
    exact annihilator_defect_tail_sq_bound M u hu
  have hlt : (‖defect M‖ ^ 2 / w M) * b < (inner ℝ qOne u) ^ 2 :=
    (lt_div_iff₀ hb).mp hs
  by_contra h
  have hle : w M * ‖tail M u‖ ^ 2 ≤ b := le_trans (le_of_not_ge h) hBb.le
  have hmul := mul_le_mul_of_nonneg_left hle hratio
  linarith

theorem annihilator_scaled_tail_tendsto_atTop
    (u : QHilbert) (hu : u ∈ QFullResidueProjection.closureᗮ)
    (hm : inner ℝ qOne u ≠ 0) :
    Tendsto (fun M : ℕ => (M : ℝ) * ‖tail M u‖ ^ 2) atTop atTop := by
  apply annihilator_weighted_tail_tendsto_atTop u hu hm (fun M => (M : ℝ))
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with M hM
    exact_mod_cast hM
  · exact defect_sq_sublinear

theorem annihilator_mean_eq_zero_of_defect_tail_tendsto
    (u : QHilbert) (hu : u ∈ QFullResidueProjection.closureᗮ) (q : ℕ → ℕ)
    (h : Tendsto (fun j => ‖defect (q j)‖ ^ 2 * ‖tail (q j) u‖ ^ 2)
      atTop (𝓝 0)) : inner ℝ qOne u = 0 := by
  have hz : (inner ℝ qOne u) ^ 2 ≤ 0 :=
    ge_of_tendsto h (Filter.Eventually.of_forall (fun j =>
      annihilator_defect_tail_sq_bound (q j) u hu))
  nlinarith [sq_nonneg (inner ℝ qOne u)]

/-- Conditional RH consumer; the tail-product hypothesis is not supplied here. -/
theorem riemannHypothesis_of_residual_defect_tail_tendsto (q : ℕ → ℕ)
    (h : Tendsto (fun j => ‖defect (q j)‖ ^ 2 * ‖tail (q j) actualResidual‖ ^ 2)
      atTop (𝓝 0)) : RiemannHypothesis := by
  have hz := annihilator_mean_eq_zero_of_defect_tail_tendsto actualResidual
    actualResidual_mem_orthogonal q h
  rw [actualResidual_mean] at hz
  have hn : ‖actualResidual‖ = 0 := by nlinarith [norm_nonneg actualResidual]
  have he : qOne = QFullResidueProjection.closure.starProjection qOne :=
    sub_eq_zero.mp (norm_eq_zero.mp hn)
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  rw [he]
  exact QFullResidueProjection.closure.starProjection_apply_mem qOne


open ZetaTwoHilbert QFiniteSupportDualCriterion QMobiusStretchedEnergy

private theorem shiftedLog_pow_div_nat_tendsto_zero (k : ℕ) :
    Tendsto (fun N : ℕ => (6 + Real.log (N : ℝ)) ^ k / (N : ℝ)) atTop (𝓝 0) := by
  have hbase := (Real.tendsto_pow_log_div_pow_atTop 1 (k : ℝ) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [Function.comp_def, Real.rpow_one, Real.rpow_natCast] at hbase
  have hlim := hbase.const_mul ((2 : ℝ) ^ k)
  simp only [mul_zero] at hlim
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hlog.eventually (eventually_ge_atTop (6 : ℝ))] with N hN
    exact div_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg N)
  · filter_upwards [hlog.eventually (eventually_ge_atTop (6 : ℝ))] with N hN
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 6 + Real.log (N : ℝ))
      (by linarith : 6 + Real.log (N : ℝ) ≤ 2 * Real.log (N : ℝ)) k
    have hd := div_le_div_of_nonneg_right hp (Nat.cast_nonneg N)
    simpa only [mul_pow, mul_div_assoc] using hd

theorem defect_sq_log_weight_tendsto_zero (k : ℕ) :
    Tendsto (fun N : ℕ => ‖defect N‖ ^ 2 /
      ((N : ℝ) / (6 + Real.log (N : ℝ)) ^ k)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exactHead_error_eventual_log_power_energy (k + 1)
  have hs : Tendsto (fun N : ℕ => 6 + Real.log (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 6
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hi : Tendsto (fun N : ℕ => 1 / (6 + Real.log (N : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hlim := ((shiftedLog_pow_div_nat_tendsto_zero k).const_mul
    (16 / ZetaTwoProbability.zetaTwo)).add (hi.const_mul C)
  simp only [mul_zero, zero_add] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog := Real.log_nonneg hNR
    positivity
  · filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with N hb hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hL : 0 < 6 + Real.log (N : ℝ) := by linarith [Real.log_nonneg hN1]
    have hm := mul_le_mul_of_nonneg_right hb
      (div_nonneg (pow_nonneg hL.le k) hNR.le)
    calc
      _ = ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 *
          ((6 + Real.log (N : ℝ)) ^ k / (N : ℝ)) := by dsimp [defect]; field_simp
      _ ≤ (16 / ZetaTwoProbability.zetaTwo + C * (N : ℝ) /
          (6 + Real.log (N : ℝ)) ^ (k + 1)) *
          ((6 + Real.log (N : ℝ)) ^ k / (N : ℝ)) := hm
      _ = _ := by rw [pow_succ]; field_simp

/-- Nonzero-mean annihilators escape every fixed logarithmic tail scale. -/
theorem annihilator_log_scaled_tail_tendsto_atTop
    (u : QHilbert) (hu : u ∈ QFullResidueProjection.closureᗮ)
    (hm : inner ℝ qOne u ≠ 0) (k : ℕ) :
    Tendsto (fun N : ℕ => ((N : ℝ) / (6 + Real.log (N : ℝ)) ^ k) *
      ‖tail N u‖ ^ 2) atTop atTop := by
  apply annihilator_weighted_tail_tendsto_atTop u hu hm
    (fun N => (N : ℝ) / (6 + Real.log (N : ℝ)) ^ k)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog := Real.log_nonneg hN1
    positivity
  · exact defect_sq_log_weight_tendsto_zero k

/-- Conditional RH criterion allowing polylogarithmic scaled-tail growth
on an arbitrary cofinal subsequence. The residual bound remains Open. -/
theorem riemannHypothesis_of_cofinal_log_tail_bound
    (k : ℕ) (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (B : ℝ)
    (hbound : ∀ j, ((q j : ℝ) / (6 + Real.log (q j : ℝ)) ^ k) *
      ‖tail (q j) actualResidual‖ ^ 2 ≤ B) : RiemannHypothesis := by
  by_cases hm : inner ℝ qOne actualResidual = 0
  · rw [actualResidual_mean] at hm
    have hn : ‖actualResidual‖ = 0 := by nlinarith [norm_nonneg actualResidual]
    have he : qOne = QFullResidueProjection.closure.starProjection qOne :=
      sub_eq_zero.mp (norm_eq_zero.mp hn)
    apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    rw [he]
    exact QFullResidueProjection.closure.starProjection_apply_mem qOne
  · have ht := (annihilator_log_scaled_tail_tendsto_atTop actualResidual
      actualResidual_mem_orthogonal hm k).comp hq
    obtain ⟨j, hj⟩ := (ht.eventually (eventually_gt_atTop B)).exists
    exact False.elim (not_lt_of_ge (hbound j) hj)


end RiemannResearch.RH.QAnnihilatorTailEscape
