/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DiscreteTailHardy
import RiemannResearch.Analysis.ProjectionTrialEnergy
import RiemannResearch.RH.QFiniteEighthForcing
import RiemannResearch.RH.QHeadCrossMoments
import RiemannResearch.RH.QSquarefreeSchurCoercivity
import RiemannResearch.RH.ThresholdHilbertMean

/-! # Signed data for the squarefree Schur system

Source: the low/high split in the finite eighth-moment handoff. Anchoring all
normalized conductors above the retained input head gives signed floor rows.
The finite adjoint Hardy inequality controls their square sum, including the
anchor. For Hardy's inequality see E. T. Copson, J. London Math. Soc. (1927),
https://doi.org/10.1112/jlms/s1-2.1.9. Here the input is the actual Pareto residual.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QFiniteSupportDualCriterion QShiftedReciprocal QSquarefreeSchurCoercivity
open QHeadCrossMoments ArithmeticCumulative
open RiemannResearch.Analysis.FiniteHilbertGram

/-- A diagonal multiplier commutes with cutting off physical sites. -/
theorem B_finiteHead_eq (H : ℕ) (f : QHilbert) :
    B (finiteHead H f) = finiteHead H (B f) := by
  apply lp.ext
  funext k
  rw [B_apply]
  by_cases hk : k < H
  · rw [finiteHead_apply_of_lt _ _ _ hk, finiteHead_apply_of_lt _ _ _ hk, B_apply]
  · rw [finiteHead_apply_eq_zero _ _ _ (by omega),
      finiteHead_apply_eq_zero _ _ _ (by omega), zero_div]

/-- The signed RHS in the full Q Schur Gram system before applying its inverse. -/
def forcingSchurRHS (H d0 : ℕ) (f : QHilbert) :
    Option (lowConductors H) → ℝ :=
  cross (squarefreeHeadFamily H d0) (finiteHead H (B f))

theorem forcingSchurRHS_physical (H : ℕ) (f v : QHilbert) :
    zetaTwo * inner ℝ v (finiteHead H (B f)) =
      ∑ k ∈ Finset.range (H + 1),
        weight k * qSequence f k * (qSequence v k / (k : ℝ)) := by
  rw [← finiteHead_inner, ← headCross_eq_inner, headCross, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [qSequence_zero]
  · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
    have hp : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [qSequence_B]
    simp only [positiveQWeight, weight]
    field_simp [zetaTwo_pos.ne', hkR, hp]

private theorem qSequence_anchor (H d0 k : ℕ) (ha : H < d0) (hk : k ≤ H) :
    qSequence (squarefreeHeadFamily H d0 none) k = (k : ℝ) := by
  change qSequenceLinear ((d0 : ℝ) • qResidue d0) k = _
  rw [map_smul]
  change (d0 : ℝ) * qSequence (qResidue d0) k = _
  rw [qSequence_qResidue]
  simp only [residueFraction, Nat.mod_eq_of_lt (lt_of_le_of_lt hk ha)]
  have h0 : (d0 : ℝ) ≠ 0 := by exact_mod_cast (show d0 ≠ 0 by omega)
  field_simp [h0]

private theorem qSequence_low_contrast (H d0 k : ℕ) (d : lowConductors H)
    (ha : H < d0) (hk : k ≤ H) :
    qSequence (squarefreeHeadFamily H d0 (some d)) k =
      -((d.val : ℝ) * ((k / d.val : ℕ) : ℝ)) := by
  change qSequenceLinear
    ((d.val : ℝ) • qResidue d.val - (d0 : ℝ) • qResidue d0) k = _
  rw [map_sub, map_smul, map_smul]
  change (d.val : ℝ) * qSequence (qResidue d.val) k -
    (d0 : ℝ) * qSequence (qResidue d0) k = _
  rw [qSequence_qResidue, qSequence_qResidue]
  simp only [residueFraction, Nat.mod_eq_of_lt (lt_of_le_of_lt hk ha)]
  have hd := ((mem_lowConductors H d.val).mp d.property).1.1
  have hdR : (d.val : ℝ) ≠ 0 := by exact_mod_cast (show d.val ≠ 0 by omega)
  have haR : (d0 : ℝ) ≠ 0 := by exact_mod_cast (show d0 ≠ 0 by omega)
  have cancel (a b : ℝ) (hb : b ≠ 0) : b * (a / b) = a := by field_simp
  rw [cancel _ _ hdR, cancel _ _ haR]
  have decomp : ((k % d.val : ℕ) : ℝ) +
      (d.val : ℝ) * ((k / d.val : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Nat.mod_add_div k d.val
  linarith

/-- The only high-conductor coordinate is the signed truncated Pareto mean. -/
theorem forcingSchurRHS_anchor (H d0 : ℕ) (ha : H < d0) (f : QHilbert) :
    zetaTwo * forcingSchurRHS H d0 f none =
      ∑ k ∈ Finset.range (H + 1), weight k * qSequence f k := by
  change zetaTwo * inner ℝ (squarefreeHeadFamily H d0 none) (finiteHead H (B f)) = _
  rw [forcingSchurRHS_physical]
  apply Finset.sum_congr rfl
  intro k hk
  have hkH : k ≤ H := by have := Finset.mem_range.mp hk; omega
  rw [qSequence_anchor H d0 k ha hkH]
  by_cases hk0 : k = 0
  · subst k
    simp [qSequence_zero]
  · rw [div_self (Nat.cast_ne_zero.mpr hk0), mul_one]

/-- Anchoring the low row cancels the common reciprocal moment exactly. -/
theorem forcingSchurRHS_contrast (H d0 : ℕ) (ha : H < d0)
    (d : lowConductors H) (f : QHilbert) :
    zetaTwo * forcingSchurRHS H d0 f (some d) =
      -(∑ k ∈ Finset.range (H + 1), weight k * qSequence f k *
          ((d.val : ℝ) * ((k / d.val : ℕ) : ℝ) / (k : ℝ))) := by
  change zetaTwo * inner ℝ (squarefreeHeadFamily H d0 (some d)) (finiteHead H (B f)) = _
  rw [forcingSchurRHS_physical, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkH : k ≤ H := by have := Finset.mem_range.mp hk; omega
  rw [qSequence_low_contrast H d0 k d ha hkH]
  ring

/-- The absolute low row is bounded by the matched residual's Pareto tail. -/
theorem forcingSchurRHS_contrast_abs_le (H d0 : ℕ) (ha : H < d0)
    (d : lowConductors H) (f : QHilbert) :
    |zetaTwo * forcingSchurRHS H d0 f (some d)| ≤
      ∑ k ∈ Finset.range (H + 1),
        if d.val ≤ k then weight k * |qSequence f k| else 0 := by
  rw [forcingSchurRHS_contrast H d0 ha d f, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  by_cases hd : d.val ≤ k
  · have dpos := ((mem_lowConductors H d.val).mp d.property).1.1
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have wpos : 0 ≤ weight k := Pareto.positiveWeight_nonneg k
    have hbase : (d.val : ℝ) * ((k / d.val : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.mul_div_le k d.val
    have hc : (d.val : ℝ) * ((k / d.val : ℕ) : ℝ) / (k : ℝ) ≤ 1 :=
      (div_le_iff₀ hkR).mpr (by simpa only [one_mul] using hbase)
    have hc0 : 0 ≤ (d.val : ℝ) * ((k / d.val : ℕ) : ℝ) / (k : ℝ) := by positivity
    rw [if_pos hd, abs_mul, abs_mul, abs_of_nonneg wpos, abs_of_nonneg hc0]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hc (mul_nonneg wpos (abs_nonneg (qSequence f k)))
  · simp [if_neg hd, Nat.div_eq_of_lt (lt_of_not_ge hd)]

theorem finite_pareto_energy_le (N : ℕ) (s : Finset ℕ) :
    (∑ k ∈ s, weight k * qSequence (qOne - finitePFit N) k ^ 2) ≤ 1 := by
  let f := qOne - finitePFit N
  have hhead : (∑ k ∈ s, weight k * qSequence f k ^ 2) ≤ ‖toPareto f‖ ^ 2 := by
    rw [Pareto.hilbert_norm_weighted_sq, toPareto_sequence]
    exact (qSequence_pareto_square_summable f).sum_le_tsum s
      (fun k _ => mul_nonneg (Pareto.positiveWeight_nonneg k) (sq_nonneg _))
  apply hhead.trans
  dsimp only [f, finitePFit]
  rw [QParetoClosedProjectionComparison.toPareto_sub,
    QParetoClosedProjectionComparison.toPareto_pFit, toPareto_qOne]
  have h := RiemannResearch.Analysis.projection_trial_energy (paretoStage N)
    Pareto.hilbertOne 0 (Submodule.zero_mem _)
  rw [sub_zero, sub_zero, Pareto.hilbertOne_norm_sq] at h
  nlinarith [sq_nonneg ‖(paretoStage N).starProjection Pareto.hilbertOne‖]

open ZetaTwoHilbert ZetaTwoProbability
open QSquarefreeSchurCoercivity ArithmeticCumulative

private theorem forcingRangeTail (H d : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ Finset.range (H + 1), if d ≤ k then a k else 0) =
      ∑ k ∈ Finset.Icc d H, a k := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/-- The anchor occupies Hardy row 1; each low squarefree d occupies its own
row d ≥ 2.  The bound is uniform in both cutoffs and the anchor. -/
theorem forcingSchurRHS_energy_le (H d0 : ℕ) (ha : H < d0) (f : QHilbert) :
    (∑ i : Option (lowConductors H), (zetaTwo * forcingSchurRHS H d0 f i) ^ 2) ≤
      4 * ∑ k ∈ Finset.range (H + 1), weight k * (qSequence f k) ^ 2 := by
  classical
  by_cases hH : 1 ≤ H
  · let a : ℕ → ℝ := fun k => weight k * |qSequence f k|
    let A : ℕ → ℝ := fun d => ∑ k ∈ Finset.Icc d H, a k
    have hA (d : ℕ) : 0 ≤ A d := Finset.sum_nonneg (fun k _ =>
      mul_nonneg (Pareto.positiveWeight_nonneg k) (abs_nonneg _))
    have hsquare {x y : ℝ} (hy : 0 ≤ y) (h : |x| ≤ y) : x^2 ≤ y^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hy).mpr h
    have h0 : |zetaTwo * forcingSchurRHS H d0 f none| ≤ A 1 := by
      rw [forcingSchurRHS_anchor H d0 ha f]
      calc
        _ ≤ ∑ k ∈ Finset.range (H + 1), |weight k * qSequence f k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range (H + 1), if 1 ≤ k then a k else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hz : k = 0
          · subst k
            simp [qSequence_zero]
          · rw [if_pos (show 1 ≤ k by omega), abs_mul,
                abs_of_nonneg (show 0 ≤ weight k from Pareto.positiveWeight_nonneg k)]
        _ = A 1 := forcingRangeTail H 1 a
    have hd (d : lowConductors H) : |zetaTwo * forcingSchurRHS H d0 f (some d)| ≤ A d.val := by
      exact (forcingSchurRHS_contrast_abs_le H d0 ha d f).trans_eq (forcingRangeTail H d.val a)
    have h1 : 1 ∉ lowConductors H := by
      intro hm
      have hz := ((mem_lowConductors H 1).mp hm).1.1
      omega
    have hsub : insert 1 (lowConductors H) ⊆ Finset.Icc 1 H := by
      intro d h
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.mem_Icc.mpr ⟨le_rfl, hH⟩
      · have he := ((mem_lowConductors H d).mp h).1
        exact Finset.mem_Icc.mpr ⟨by omega, he.2⟩
    have hcoeff (k : ℕ) (hk : k ∈ Finset.Icc 1 H) :
        ((k : ℝ) * a k) ^ 2 ≤ weight k * (qSequence f k) ^ 2 := by
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hweight : (k : ℝ) ^ 2 * weight k ≤ 1 := by
        change (k : ℝ) ^ 2 * (1 / ((k : ℝ) * ((k : ℝ) + 1))) ≤ 1
        rw [one_div, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        nlinarith
      calc
        _ = ((k : ℝ) ^ 2 * weight k) * (weight k * (qSequence f k) ^ 2) := by
          dsimp only [a]
          rw [mul_pow, mul_pow, sq_abs]
          ring
        _ ≤ 1 * (weight k * (qSequence f k) ^ 2) := mul_le_mul_of_nonneg_right hweight
          (mul_nonneg (Pareto.positiveWeight_nonneg k) (sq_nonneg _))
        _ = _ := one_mul _
    have hrange : Finset.Icc 1 H ⊆ Finset.range (H + 1) := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
    calc
      _ ≤ (A 1) ^ 2 + ∑ d : lowConductors H, (A d.val) ^ 2 := by
        rw [Fintype.sum_option]
        exact add_le_add (hsquare (hA 1) h0)
          (Finset.sum_le_sum (fun d _ => hsquare (hA d.val) (hd d)))
      _ = (A 1) ^ 2 + ∑ d ∈ lowConductors H, (A d) ^ 2 := by
        congr 1
        exact Finset.sum_attach (lowConductors H) (fun d => (A d) ^ 2)
      _ = ∑ d ∈ insert 1 (lowConductors H), (A d) ^ 2 := by rw [Finset.sum_insert h1]
      _ ≤ ∑ d ∈ Finset.Icc 1 H, (A d) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => sq_nonneg _)
      _ ≤ 4 * ∑ k ∈ Finset.Icc 1 H, ((k : ℝ) * a k) ^ 2 :=
        RiemannResearch.Analysis.DiscreteTailHardy.finite_adjoint_hardy_sq a H
      _ ≤ 4 * ∑ k ∈ Finset.range (H + 1), weight k * (qSequence f k) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (Finset.sum_le_sum hcoeff).trans
          (Finset.sum_le_sum_of_subset_of_nonneg hrange (fun k _ _ =>
            mul_nonneg (Pareto.positiveWeight_nonneg k) (sq_nonneg _)))
  · have hz : H = 0 := by omega
    subst H
    simp [forcingSchurRHS, RiemannResearch.Analysis.FiniteHilbertGram.cross,
      QFiniteSupportDualCriterion.finiteHead, qSequence_zero]

/-- For the matched projection of the constant, all signed pre-inverse
Schur inputs have a stage- and cutoff-independent total square bound. -/
theorem finite_forcingSchurRHS_energy_le_four (N H d0 : ℕ) (ha : H < d0) :
    (∑ i : Option (lowConductors H),
      (zetaTwo * forcingSchurRHS H d0 (qOne - finitePFit N) i) ^ 2) ≤ 4 := by
  calc
    _ ≤ 4 * ∑ k ∈ Finset.range (H + 1), weight k *
        (qSequence (qOne - finitePFit N) k) ^ 2 :=
      forcingSchurRHS_energy_le H d0 ha _
    _ ≤ 4 * 1 := mul_le_mul_of_nonneg_left
      (finite_pareto_energy_le N (Finset.range (H + 1))) (by norm_num)
    _ = _ := by norm_num

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QSquarefreeSchurCoercivity QAnnihilatorTailEscape QFiniteSupportDualCriterion
open ArithmeticCumulative

/-- Squared mass of the signed low-conductor rows strictly beyond D.
    The single anchor row is kept separate at every cutoff. -/
def schurContrastTailSq (H d0 D : ℕ) (f : QHilbert) : ℝ :=
  ∑ d : lowConductors H, if D < d.val then
    (zetaTwo * forcingSchurRHS H d0 f (some d)) ^ 2 else 0

private theorem forcingSchurRHS_contrast_eq_tail (H d0 D : ℕ) (ha : H < d0)
    (d : lowConductors H) (hd : D < d.val) (f : QHilbert) :
    zetaTwo * forcingSchurRHS H d0 f (some d) =
      zetaTwo * forcingSchurRHS H d0 (tail D f) (some d) := by
  rw [forcingSchurRHS_contrast H d0 ha d f,
    forcingSchurRHS_contrast H d0 ha d (tail D f)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k < d.val
  · simp [Nat.div_eq_of_lt hk]
  · have hD : D < k := lt_of_lt_of_le hd (le_of_not_gt hk)
    have hpt : qSequence (tail D f) k = qSequence f k := by
      cases k with
      | zero => omega
      | succ j =>
        change (f j - finiteHead D f j) / Real.sqrt (qWeight j) = f j / Real.sqrt (qWeight j)
        rw [finiteHead_apply_eq_zero D f j (by omega), sub_zero]
    rw [hpt]

/-- The entire high-index part of the pre-inverse load is controlled by
    the actual input tail, uniformly in the retained head and in the anchor. -/
theorem forcingSchurRHS_tail_sq_le (H d0 D : ℕ) (ha : H < d0) (f : QHilbert) :
    schurContrastTailSq H d0 D f ≤ (4 * zetaTwo) * ‖tail D f‖ ^ 2 := by
  classical
  let g := tail D f
  have hrows : schurContrastTailSq H d0 D f ≤
      ∑ d : lowConductors H, (zetaTwo * forcingSchurRHS H d0 g (some d)) ^ 2 := by
    unfold schurContrastTailSq
    apply Finset.sum_le_sum
    intro d _
    by_cases hd : D < d.val
    · rw [if_pos hd, forcingSchurRHS_contrast_eq_tail H d0 D ha d hd f]
    · rw [if_neg hd]
      exact sq_nonneg _
  have he : (∑ k ∈ Finset.range (H + 1), weight k * (qSequence g k) ^ 2) ≤
      ‖toPareto g‖ ^ 2 := by
    rw [Pareto.hilbert_norm_weighted_sq, toPareto_sequence]
    exact (qSequence_pareto_square_summable g).sum_le_tsum _
      (fun k _ => mul_nonneg (Pareto.positiveWeight_nonneg k) (sq_nonneg _))
  calc
    _ ≤ ∑ d : lowConductors H, (zetaTwo * forcingSchurRHS H d0 g (some d)) ^ 2 := hrows
    _ ≤ ∑ i : Option (lowConductors H), (zetaTwo * forcingSchurRHS H d0 g i) ^ 2 := by
      rw [Fintype.sum_option]
      exact le_add_of_nonneg_left (sq_nonneg _)
    _ ≤ 4 * ∑ k ∈ Finset.range (H + 1), weight k * (qSequence g k) ^ 2 :=
      forcingSchurRHS_energy_le H d0 ha g
    _ ≤ 4 * (zetaTwo * ‖g‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (he.trans (toPareto_norm_sq_le g)) (by norm_num)
    _ = _ := by rw [mul_assoc]

/-- For the actual Pareto fits, no squared Schur input mass escapes to
    ever larger contrast indices. The retained cutoff H may vary arbitrarily. -/
theorem finite_forcingSchurRHS_tail_tendsto (H d0 D : ℕ → ℕ)
    (ha : ∀ N, H N < d0 N) (hD : Tendsto D atTop atTop) :
    Tendsto (fun N => schurContrastTailSq (H N) (d0 N) (D N) (qOne - finitePFit N))
      atTop (𝓝 0) := by
  have hnon (N : ℕ) : 0 ≤ schurContrastTailSq (H N) (d0 N) (D N) (qOne - finitePFit N) := by
    unfold schurContrastTailSq
    apply Finset.sum_nonneg
    intro d _
    split_ifs <;> positivity
  have ht : Tendsto (fun N => (4 * zetaTwo) * ‖tail (D N) (qOne - finitePFit N)‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
      ((finiteParetoResidual_tail_tendsto D hD).pow 2).const_mul (4 * zetaTwo)
  exact squeeze_zero hnon (fun N => forcingSchurRHS_tail_sq_le (H N) (d0 N) (D N) (ha N) _) ht

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
