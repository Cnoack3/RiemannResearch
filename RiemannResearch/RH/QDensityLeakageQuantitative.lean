/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDensityLeakage
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Quantitative density leakage and its exact harmonic residual

Source: the user's projected-generator research question, 13 November 2026,
and the exact identities in QDensityLeakage. The proof uses the complete
inverse-square tail, projection contraction, and elementary p-series bounds.

Write Z = zetaTwo and r = qOne - projection(qOne). For k >= 2 the normalized
error has square norm at most 1/(Z*(k-1)). More precisely,
h_k = r/(Z*k) + centeredLeakage k, and the centered vectors are absolutely
summable with a cubic square bound. Their finite sums converge with the exact
signed harmonic term retained.

The uncentered leakage vectors are unconditionally square summable.
Absolute summability is equivalent to constant-target membership and implies
RH through the existing verified transfer theorem. That membership remains
Open; these estimates do not provide its vanishing.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QDensityLeakage
open ZetaTwoHilbert ZetaTwoProbability QFullResidueProjection QDensityMetric

theorem approximation_error_norm_sq_le (k : ℕ) (hk : 2 ≤ k) :
    ‖approximation k - qOne‖^2 ≤ 1 / (zetaTwo * ((k-1 : ℕ) : ℝ)) := by
  have hk0 : 0 < k := by omega
  have hhead : (∑ n ∈ Finset.range (k-1),
      qSequence (approximation k - qOne) (n+1)^2 / (n+1 : ℝ)^2) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnk : n+1 < k := by simp only [Finset.mem_range] at hn; omega
    rw [approximation_error_sequence k (n+1) hk0, Nat.mod_eq_of_lt hnk]
    simp [qOneSequence, ne_of_gt (show (0 : ℝ) < (n : ℝ)+1 by positivity)]
  have h := QFiniteEnergyBounds.norm_sq_le_head_tail (approximation k - qOne)
    (k-1) (by omega) 1 zero_le_one
    (fun n => approximation_error_abs_le_one k n hk0)
  simpa only [hhead, one_pow, zero_add, one_div_mul_one_div] using h

/-- Complete normalized error bound; the nonzero limiting residual is retained. -/
theorem scaled_residue_leakage_error_norm_sq_le (k : ℕ) (hk : 2 ≤ k) :
    ‖(zetaTwo * (k : ℝ)) • leakage (qResidue k) -
      (qOne - closure.starProjection qOne)‖^2 ≤
      1 / (zetaTwo * ((k-1 : ℕ) : ℝ)) := by
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (scaled_residue_leakage_error_norm_le k hk)).trans
      (approximation_error_norm_sq_le k hk)

theorem summable_residue_leakage_sq :
    Summable (fun n : ℕ => ‖leakage (qResidue (n+2))‖^2) := by
  have hZ := zetaTwo_pos
  have hs : Summable (fun n : ℕ => (1 / zetaTwo)^2 * (1 / ((n+2 : ℕ) : ℝ)^2)) :=
    ((summable_nat_add_iff 2).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))).mul_left _
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ hs
  intro n
  have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (residue_leakage_norm_le (n+2) (by omega))
  simpa only [div_pow, mul_pow, one_pow, one_div_mul_one_div] using h

/-- Nonzero constant residual forces a positive harmonic lower bound. -/
theorem eventually_residue_leakage_lower (hne : qOne ∉ closure) :
    ∀ᶠ k : ℕ in atTop,
      ‖qOne - closure.starProjection qOne‖ / (2*zetaTwo) * (1 / (k : ℝ)) ≤
        ‖leakage (qResidue k)‖ := by
  have hr : 0 < ‖qOne - closure.starProjection qOne‖ := by
    apply norm_pos_iff.mpr
    intro he
    exact hne (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm)
  have he := scaled_residue_leakage_norm_tendsto.eventually
    (lt_mem_nhds (show ‖qOne - closure.starProjection qOne‖ / 2 <
      ‖qOne - closure.starProjection qOne‖ by linarith))
  filter_upwards [he, eventually_ge_atTop (2 : ℕ)] with k hk hk2
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hZ := zetaTwo_pos
  have hh : ‖qOne - closure.starProjection qOne‖ / (2*zetaTwo*(k : ℝ)) ≤
      ‖leakage (qResidue k)‖ :=
    (div_le_iff₀ (by positivity : 0 < 2*zetaTwo*(k : ℝ))).mpr (by nlinarith)
  convert hh using 1
  ring


/-- Absolute summability is exactly the constant-target membership condition. -/
theorem summable_residue_leakage_norm_iff :
    Summable (fun n : ℕ => ‖leakage (qResidue (n+2))‖) ↔ qOne ∈ closure := by
  constructor
  · intro hs
    by_contra hne
    let c : ℝ := ‖qOne - closure.starProjection qOne‖ / (2*zetaTwo)
    have hc : 0 < c := by
      apply div_pos _ (by have hZ := zetaTwo_pos; positivity)
      apply norm_pos_iff.mpr
      intro he
      exact hne (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm)
    have hlow : ∀ᶠ n : ℕ in atTop,
        c * (1 / ((n+2 : ℕ) : ℝ)) ≤ ‖leakage (qResidue (n+2))‖ :=
      (tendsto_add_atTop_nat 2).eventually (eventually_residue_leakage_lower hne)
    have hh : Summable (fun n : ℕ => c * (1 / ((n+2 : ℕ) : ℝ))) := by
      apply Summable.of_norm_bounded_eventually hs
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [hlow] with n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hn
    have hseries : Summable (fun n : ℕ => 1 / ((n+2 : ℕ) : ℝ)) := by
      apply (hh.mul_left c⁻¹).congr
      intro n
      simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    have htotal : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 2).mp hseries
    have hbad : 1 < (1 : ℕ) := (Real.summable_one_div_nat_pow (p := 1)).mp
      (by simpa only [pow_one] using htotal)
    norm_num at hbad
  · intro hmem
    have hz := residue_leakage_vanishes_iff_one_mem.mpr hmem
    apply (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))).congr
    intro n
    rw [hz (n+2) (by omega), norm_zero]

theorem riemannHypothesis_of_summable_residue_leakage_norm
    (h : Summable (fun n : ℕ => ‖leakage (qResidue (n+2))‖)) : RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (summable_residue_leakage_norm_iff.mp h)

/-- If the target is missing, the total leakage length diverges. -/
theorem residue_leakage_norm_sum_tendsto_atTop (hne : qOne ∉ closure) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ‖leakage (qResidue (n+2))‖)
      atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => norm_nonneg _)).mp
    (fun hs => hne (summable_residue_leakage_norm_iff.mp hs))


/-- Subtract exactly the limiting harmonic residual, without discarding its sign. -/
def centeredLeakage (k : ℕ) : QHilbert :=
  leakage (qResidue k) -
    (1 / (zetaTwo * (k : ℝ))) • (qOne - closure.starProjection qOne)

theorem scaled_centeredLeakage (k : ℕ) (hk : 0 < k) :
    (zetaTwo * (k : ℝ)) • centeredLeakage k =
      (zetaTwo * (k : ℝ)) • leakage (qResidue k) -
        (qOne - closure.starProjection qOne) := by
  have hZ := zetaTwo_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [centeredLeakage, smul_sub, smul_smul,
    mul_one_div_cancel (ne_of_gt (mul_pos hZ hkR)), one_smul]

/-- The full residual after centering has an unconditional cubic square bound. -/
theorem centeredLeakage_norm_sq_le (n : ℕ) :
    ‖centeredLeakage (n+2)‖^2 ≤
      1 / (zetaTwo^3 * ((n : ℝ)+1)^3) := by
  have hZ := zetaTwo_pos
  have hx : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hk : (0 : ℝ) < (n : ℝ)+2 := by positivity
  have hb := scaled_residue_leakage_error_norm_sq_le (n+2) (by omega)
  rw [← scaled_centeredLeakage (n+2) (by omega), norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < zetaTwo*((n+2 : ℕ) : ℝ)),
    mul_pow] at hb
  have hsub : n+2-1 = n+1 := by omega
  simp only [hsub, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at hb
  apply (le_div_iff₀ (by positivity : 0 < zetaTwo^3 * ((n : ℝ)+1)^3)).mpr
  have hsq : ((n : ℝ)+1)^2 ≤ ((n : ℝ)+2)^2 :=
    (sq_le_sq₀ hx.le hk.le).mpr (by linarith)
  calc
    _ = (‖centeredLeakage (n+2)‖^2 * (zetaTwo^3 * ((n : ℝ)+1))) *
        ((n : ℝ)+1)^2 := by ring
    _ ≤ (‖centeredLeakage (n+2)‖^2 * (zetaTwo^3 * ((n : ℝ)+1))) *
        ((n : ℝ)+2)^2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = ((zetaTwo * ((n : ℝ)+2))^2 * ‖centeredLeakage (n+2)‖^2) *
        (zetaTwo * ((n : ℝ)+1)) := by ring
    _ ≤ 1 := (le_div_iff₀ (mul_pos hZ hx)).mp hb

/-- Harmonic centering leaves an absolutely summable vector error. -/
theorem summable_centeredLeakage_norm :
    Summable (fun n : ℕ => ‖centeredLeakage (n+2)‖) := by
  have hZ := zetaTwo_pos
  have hs : Summable (fun n : ℕ =>
      1 / (zetaTwo^(3 / 2 : ℝ) * ((n : ℝ)+1)^(3 / 2 : ℝ))) := by
    have h := ((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_rpow.mpr (by norm_num : 1 < (3 / 2 : ℝ)))).mul_left
        (1 / zetaTwo^(3 / 2 : ℝ))
    simpa only [Nat.cast_add, Nat.cast_one, one_div_mul_one_div] using h
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hs
  intro n
  have hx : (0 : ℝ) < (n : ℝ)+1 := by positivity
  apply (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ 1 / (zetaTwo^(3 / 2 : ℝ) * ((n : ℝ)+1)^(3 / 2 : ℝ)))).mp
  have he : (1 / (zetaTwo^(3 / 2 : ℝ) * ((n : ℝ)+1)^(3 / 2 : ℝ)))^2 =
      1 / (zetaTwo^3 * ((n : ℝ)+1)^3) := by
    rw [div_pow, one_pow, mul_pow,
      ← Real.rpow_mul_natCast hZ.le, ← Real.rpow_mul_natCast hx.le]
    norm_num only [Nat.cast_ofNat, show (3 / 2 : ℝ)*2 = 3 by norm_num, Real.rpow_ofNat]
  rw [he]
  exact centeredLeakage_norm_sq_le n

/-- Exact harmonic vector asymptotic, including the convergent centered remainder. -/
theorem centered_residue_leakage_partial_sums_tendsto :
    ∃ u : QHilbert, Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, leakage (qResidue (n+2))) -
        (∑ n ∈ Finset.range N, 1 / (zetaTwo * ((n+2 : ℕ) : ℝ))) •
          (qOne - closure.starProjection qOne)) atTop (𝓝 u) := by
  have hs : Summable (fun n : ℕ => centeredLeakage (n+2)) :=
    summable_centeredLeakage_norm.of_norm
  refine ⟨∑' n : ℕ, centeredLeakage (n+2), ?_⟩
  simpa only [centeredLeakage, Finset.sum_sub_distrib, Finset.sum_smul] using
    hs.hasSum.tendsto_sum_nat

#print axioms summable_residue_leakage_norm_iff
#print axioms summable_centeredLeakage_norm
end RiemannResearch.RH.QDensityLeakage
