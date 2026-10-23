/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QCanonicalMovingCovariance
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QFloorZetaEscape
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QMobiusExactHead
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Tail escape for every nonzero complete-Q annihilator

Source: independent deduction from the user-provided exact-head agenda and
the existing floor-dilation module, 22 October 2026. The exact dilated
defect-tail identity and the separating family of physical step functions
remove the nonzero-mean assumption from the earlier tail-escape theorem.
The actual residual-tail bound required to conclude RH remains Open.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QAnnihilatorDilationEscape
open ZetaTwoHilbert QFiniteSupportDualCriterion QAnnihilatorTailEscape
open QFloorDilation

theorem dilation_defect_head_zero (M d : ℕ) (hd : 0 < d)
    (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    qSequence (floorDilation d hd (defect M)) n = 0 := by
  rw [floorDilation_sequence]
  change qSequenceLinear (qOne - QMobiusExactHead.exactHead M) (n / d) = 0
  rw [map_sub]
  change qSequence qOne (n / d) -
    qSequence (QMobiusExactHead.exactHead M) (n / d) = 0
  by_cases hz : n / d = 0
  · have hzero (f : QHilbert) : qSequence f 0 = 0 := rfl
    rw [hz, hzero, hzero, sub_self]
  · rw [qSequence_qOne, QMobiusExactHead.exactHead_exact M (n / d)
      (Nat.pos_of_ne_zero hz) (le_trans (Nat.div_le_self n d) hnM)]
    simp only [qOneSequence, if_neg hz, sub_self]

theorem dilation_defect_inner_finiteHead (M d : ℕ) (hd : 0 < d) (u : QHilbert) :
    inner ℝ (floorDilation d hd (defect M)) (finiteHead M u) = 0 := by
  have h := inner_finiteHead_eq_of_matching_head M
    (floorDilation d hd (defect M)) 0 u (by
      intro n hn hnM
      change qSequence (floorDilation d hd (defect M)) n = qSequenceLinear 0 n
      rw [map_zero]
      exact dilation_defect_head_zero M d hd n hn hnM)
  simpa only [inner_zero_left] using h

/-- Exact signed identity before applying any norm estimate. -/
theorem dilation_defect_tail_identity (M d : ℕ) (hd : 0 < d) (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ) :
    inner ℝ (floorDilation d hd (defect M)) (tail M u) =
      inner ℝ (floorDilation d hd qOne) u := by
  have he : floorDilation d hd (QMobiusExactHead.exactHead M) ∈
      QFullResidueProjection.closure :=
    QFullResidueProjection.legalSpan.le_topologicalClosure
      (floorDilation_mem_legalSpan d hd _ (QMobiusExactHead.exactHead_mem_legalSpan M))
  have hz := Submodule.inner_right_of_mem_orthogonal he hu
  rw [tail, inner_sub_right, dilation_defect_inner_finiteHead, sub_zero,
    defect, map_sub, inner_sub_left, hz, sub_zero]

theorem dilation_defect_tail_sq_bound (M d : ℕ) (hd : 0 < d) (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ) :
    (inner ℝ (floorDilation d hd qOne) u) ^ 2 ≤
      ‖floorDilation d hd (defect M)‖ ^ 2 * ‖tail M u‖ ^ 2 := by
  rw [← dilation_defect_tail_identity M d hd u hu]
  have h := abs_real_inner_le_norm (floorDilation d hd (defect M)) (tail M u)
  have hs := mul_self_le_mul_self
    (abs_nonneg (inner ℝ (floorDilation d hd (defect M)) (tail M u))) h
  nlinarith [sq_abs (inner ℝ (floorDilation d hd (defect M)) (tail M u))]

/-- Successive dilated constants recover each physical coordinate indicator,
represented by its weighted coordinate atom in normalized Hilbert coordinates. -/
theorem step_difference_single (n : ℕ) :
    floorDilation (n + 1) (Nat.succ_pos _) qOne -
      floorDilation (n + 2) (by omega) qOne =
        lp.single 2 n (Real.sqrt (qWeight n)) := by
  ext k
  have hs : qSequence (floorDilation (n + 1) (Nat.succ_pos _) qOne -
      floorDilation (n + 2) (by omega) qOne) (k + 1) =
        if n = k then 1 else 0 := by
    change qSequenceLinear (_ - _) (k + 1) = _
    rw [map_sub]
    change qSequence (floorDilation (n + 1) (Nat.succ_pos _) qOne) (k + 1) -
      qSequence (floorDilation (n + 2) (by omega) qOne) (k + 1) = _
    rw [QFloorZetaEscape.floorDilation_qOne_sequence,
      QFloorZetaEscape.floorDilation_qOne_sequence]
    split_ifs <;> simp_all <;> omega
  have hne : Real.sqrt (qWeight k) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos k))
  rw [qSequence_succ] at hs
  have hv := (div_eq_iff hne).mp hs
  by_cases hnk : n = k
  · subst k
    simpa [lp.single_apply] using hv
  · simpa [lp.single_apply, hnk, Ne.symm hnk] using hv

theorem exists_nonzero_step_pairing (u : QHilbert) (hu : u ≠ 0) :
    ∃ d, ∃ hd : 0 < d, inner ℝ (floorDilation d hd qOne) u ≠ 0 := by
  by_contra h
  push Not at h
  apply hu
  ext n
  have hi : inner ℝ (lp.single 2 n (Real.sqrt (qWeight n))) u = 0 := by
    rw [← step_difference_single, inner_sub_left,
      h (n + 1) (Nat.succ_pos _), h (n + 2) (by omega), sub_self]
  have hi' : Real.sqrt (qWeight n) * u n = 0 := by
    simpa only [lp.inner_single_left, RCLike.inner_apply, conj_trivial, mul_comm] using hi
  exact (mul_eq_zero.mp hi').resolve_left
    (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))

/-- The missing mean assumption is removed by selecting a nonzero step pairing. -/
theorem nonzero_annihilator_weighted_tail_tendsto_atTop
    (u : QHilbert) (hu : u ∈ QFullResidueProjection.closureᗮ) (hne : u ≠ 0)
    (w : ℕ → ℝ) (hw : ∀ᶠ M in atTop, 0 < w M)
    (hsmall : Tendsto (fun M => ‖defect M‖ ^ 2 / w M) atTop (𝓝 0)) :
    Tendsto (fun M => w M * ‖tail M u‖ ^ 2) atTop atTop := by
  obtain ⟨d, hd, hm⟩ := exists_nonzero_step_pairing u hne
  have hsmallD : Tendsto (fun M => ‖floorDilation d hd (defect M)‖ ^ 2 / w M)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa using hsmall.const_mul (2 / (d : ℝ)))
    · filter_upwards [hw] with M hwM
      exact div_nonneg (sq_nonneg _) hwM.le
    · filter_upwards [hw] with M hwM
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (floorDilation_norm_sq_le d hd (defect M)) hwM.le
  apply tendsto_atTop.2
  intro B
  let b : ℝ := max B 0 + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hBb : B < b := by dsimp [b]; linarith [le_max_left B 0]
  have hc : 0 < (inner ℝ (floorDilation d hd qOne) u) ^ 2 := sq_pos_of_ne_zero hm
  have heps : 0 < (inner ℝ (floorDilation d hd qOne) u) ^ 2 / b := div_pos hc hb
  have hupper := (tendsto_order.1 hsmallD).2 _ heps
  filter_upwards [hw, hupper] with M hwM hs
  have hratio : 0 ≤ ‖floorDilation d hd (defect M)‖ ^ 2 / w M :=
    div_nonneg (sq_nonneg _) hwM.le
  have hid : (‖floorDilation d hd (defect M)‖ ^ 2 / w M) *
      (w M * ‖tail M u‖ ^ 2) =
        ‖floorDilation d hd (defect M)‖ ^ 2 * ‖tail M u‖ ^ 2 := by field_simp
  have hp : (inner ℝ (floorDilation d hd qOne) u) ^ 2 ≤
      (‖floorDilation d hd (defect M)‖ ^ 2 / w M) * (w M * ‖tail M u‖ ^ 2) := by
    rw [hid]
    exact dilation_defect_tail_sq_bound M d hd u hu
  have hlt : (‖floorDilation d hd (defect M)‖ ^ 2 / w M) * b <
      (inner ℝ (floorDilation d hd qOne) u) ^ 2 := (lt_div_iff₀ hb).mp hs
  by_contra h
  have hle : w M * ‖tail M u‖ ^ 2 ≤ b := le_trans (le_of_not_ge h) hBb.le
  have hmul := mul_le_mul_of_nonneg_left hle hratio
  linarith

theorem nonzero_annihilator_log_scaled_tail_tendsto_atTop
    (u : QHilbert) (hu : u ∈ QFullResidueProjection.closureᗮ) (hne : u ≠ 0) (k : ℕ) :
    Tendsto (fun N : ℕ => ((N : ℝ) / (6 + Real.log (N : ℝ)) ^ k) *
      ‖tail N u‖ ^ 2) atTop atTop := by
  apply nonzero_annihilator_weighted_tail_tendsto_atTop u hu hne
    (fun N => (N : ℝ) / (6 + Real.log (N : ℝ)) ^ k)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog := Real.log_nonneg hN1
    positivity
  · exact defect_sq_log_weight_tendsto_zero k

theorem annihilator_eq_zero_of_cofinal_log_tail_bound
    (u : QHilbert) (hu : u ∈ QFullResidueProjection.closureᗮ)
    (k : ℕ) (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (B : ℝ)
    (hbound : ∀ j, ((q j : ℝ) / (6 + Real.log (q j : ℝ)) ^ k) *
      ‖tail (q j) u‖ ^ 2 ≤ B) : u = 0 := by
  by_contra hne
  have ht := (nonzero_annihilator_log_scaled_tail_tendsto_atTop u hu hne k).comp hq
  obtain ⟨j, hj⟩ := (ht.eventually (eventually_gt_atTop B)).exists
  exact not_lt_of_ge (hbound j) hj

private theorem tail_norm_sq_eq_shift (N : ℕ) (u : QHilbert) :
    ‖tail N u‖ ^ 2 = ‖Pareto.hilbertTailShift u N‖ ^ 2 := by
  have hh : ‖finiteHead N u‖ ^ 2 =
      ∑ n ∈ Finset.range N, (u n) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, finiteHead_inner, finiteHead_idem,
      inner_finiteHead_eq_sum]
    simp only [pow_two]
  rw [Pareto.hilbertTailShift_norm_sq, ← hh]
  have hs := finiteHead_norm_sq_split N u
  change ‖u - finiteHead N u‖ ^ 2 = _
  linarith

/-- A full-span annihilator with uniformly bounded physical values is zero.
The bound is in the physical sup norm, not the complete Q Hilbert norm.
Source: the user's residual-divergence question, 23 October 2026. -/
theorem annihilator_eq_zero_of_bounded_physical
    (u : QHilbert) (hu : u ∈ QFullResidueProjection.closureᗮ)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n, 0 < n → |qSequence u n| ≤ A) : u = 0 := by
  let C : ℝ := (2 / ZetaTwoProbability.zetaTwo) * A ^ 2
  have hC : 0 ≤ C := by
    have hZ := ZetaTwoProbability.zetaTwo_pos
    dsimp [C]
    positivity
  apply QAnnihilatorDilationEscape.annihilator_eq_zero_of_cofinal_log_tail_bound
    u hu 0 id tendsto_id C
  intro N
  have hb := QCanonicalMovingCovariance.tail_norm_sq_le_of_bounded u N A hA hf
  have hs : (N : ℝ) * ‖tail N u‖ ^ 2 ≤ C := by
    rw [tail_norm_sq_eq_shift]
    calc
      _ ≤ (N : ℝ) * (C / ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N)
      _ ≤ C := by
        have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have hnum : (N : ℝ) * C ≤ C * ((N : ℝ) + 1) := by nlinarith
        simpa only [mul_div_assoc] using (div_le_iff₀ hden).mpr hnum
  simpa using hs

/-- A nonzero full-span annihilator has unbounded physical magnitude, even
though its complete Q norm is finite. This does not assert a signed limit. -/
theorem nonzero_annihilator_physical_unbounded
    (u : QHilbert) (hu : u ∈ QFullResidueProjection.closureᗮ)
    (hne : u ≠ 0) (A : ℝ) :
    ∃ n, 0 < n ∧ A < |qSequence u n| := by
  by_contra h
  have hf : ∀ n, 0 < n → |qSequence u n| ≤ A := by
    intro n hn
    exact le_of_not_gt (fun hlt => h ⟨n, hn, hlt⟩)
  have hA : 0 ≤ A := (abs_nonneg _).trans (hf 1 Nat.zero_lt_one)
  exact hne (annihilator_eq_zero_of_bounded_physical u hu A hA hf)

end RiemannResearch.RH.QAnnihilatorDilationEscape
