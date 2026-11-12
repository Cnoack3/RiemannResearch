/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthForcing
import RiemannResearch.RH.AdjacentResidueHarmonic
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.Analysis.DiscreteTailHardy

/-! # Full high-conductor data of the matched projection

The finite eighth-moment handoff derived the full-data formula on paper.
Here the remainder is a physical Pareto pairing with a vector supported
on sites at least the conductor. -/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open Pareto ZetaTwoProbability ZetaTwoHilbert ZetaTwoOptimizerStage
open ZetaTwoParetoTransfer QParetoClosedProjectionComparison QShiftedReciprocal
open QAnnihilatorTailEscape QFiniteSupportDualCriterion

private def remRatio (m k : ℕ) : ℝ := ((k % m : ℕ) : ℝ) / k

private theorem remRatio_bounds (m k : ℕ) : 0 ≤ remRatio m k ∧ remRatio m k ≤ 1 := by
  unfold remRatio
  constructor
  · positivity
  · by_cases hk : k = 0
    · simp [hk]
    · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      apply (div_le_iff₀ hk').mpr
      simpa only [one_mul] using (show ((k % m : ℕ) : ℝ) ≤ k by exact_mod_cast Nat.mod_le k m)

/-- Pareto vector with physical coordinates (k mod m)/k. -/
def ratioVector (m : ℕ) : ThresholdHilbert :=
  sequenceHilbert (remRatio m) (by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
      _ positiveWeight_summable
    intro i
    have h := remRatio_bounds m i
    have hs : remRatio m i ^ 2 ≤ 1 := by nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (positiveWeight_nonneg i))

private theorem ratioVector_sequence (m : ℕ) : hilbertSequence (ratioVector m) = remRatio m :=
  hilbertSequence_sequenceHilbert _ _ (by simp [remRatio])

theorem ratioVector_pair_shifted (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    (zetaTwo * m) * inner ℝ (qResidue m) (B f) =
      inner ℝ (ratioVector m) (toPareto f) := by
  rw [qInner_weighted, ← tsum_mul_left, hilbert_inner_weighted, ratioVector_sequence,
    toPareto_sequence]
  unfold paretoInner
  apply tsum_congr
  intro k
  rw [qSequence_qResidue, qSequence_B]
  by_cases hk : k = 0
  · simp [hk, remRatio, positiveWeight, positiveQWeight]
  · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    unfold remRatio ArithmeticCumulative.residueFraction positiveWeight positiveQWeight
    field_simp [hk'.ne', hm'.ne', hp.ne', zetaTwo_pos.ne']

/-- The actual full Gram datum, with its signed residual at every site. -/
theorem full_conductor_forcing (N m : ℕ) (hm : 0 < m) (hv : qResidue m ∈ stage N) :
    (zetaTwo * m) * inner ℝ (qResidue m) (finiteDisplacement N) =
      ∑' k : ℕ, positiveWeight k *
        ((((k % m : ℕ) : ℝ) / k) * qSequence (qOne - finitePFit N) k) := by
  have h := Submodule.inner_right_of_mem_orthogonal hv (finite_witness_mem_orthogonal N)
  rw [inner_sub_right] at h
  rw [← sub_eq_zero.mp h, ratioVector_pair_shifted m hm, hilbert_inner_weighted,
    ratioVector_sequence, toPareto_sequence]
  rfl

private theorem defect_sequence (m : ℕ) :
    hilbertSequence (hilbertOne - ratioVector m) =
      fun k => zeroAnchor (fun _ => (1 : ℝ)) k - remRatio m k := by
  change hilbertSequenceLinear (hilbertOne - ratioVector m) = _
  rw [map_sub]
  change hilbertSequence hilbertOne - hilbertSequence (ratioVector m) = _
  rw [hilbertOne_sequence, ratioVector_sequence]
  rfl

private theorem defect_head_zero (m k : ℕ) (hk : k < m) :
    hilbertSequence (hilbertOne - ratioVector m) k = 0 := by
  rw [defect_sequence]
  by_cases hz : k = 0
  · simp [hz, zeroAnchor, remRatio]
  · simp [zeroAnchor, remRatio, hz, Nat.mod_eq_of_lt hk]

theorem ratioVector_error_norm_sq_le (m : ℕ) (hm : 0 < m) :
    ‖hilbertOne - ratioVector m‖ ^ 2 ≤ 1 / (m : ℝ) := by
  let z := hilbertOne - ratioVector m
  have hs := (hilbertSequence_square_summable z).sum_add_tsum_nat_add m
  have hh : (∑ k ∈ Finset.range m, positiveWeight k * (hilbertSequence z k) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [z, defect_head_zero m k (Finset.mem_range.mp hk)]
  rw [hh,zero_add] at hs
  change ‖z‖ ^ 2 ≤ _
  rw [hilbert_norm_weighted_sq, ← hs, ← positiveWeight_tail_tsum m hm]
  apply Summable.tsum_le_tsum _
    ((summable_nat_add_iff m).mpr (hilbertSequence_square_summable z))
    ((summable_nat_add_iff m).mpr positiveWeight_summable)
  intro k
  have hk : k + m ≠ 0 := by omega
  have h := remRatio_bounds m (k + m)
  have hs' : (1 - remRatio m (k + m)) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
  change positiveWeight (k + m) * (hilbertSequence (hilbertOne - ratioVector m) (k + m)) ^ 2 ≤ _
  rw [defect_sequence]
  simpa only [zeroAnchor, hk, if_false, mul_one] using
    (mul_le_mul_of_nonneg_left hs' (positiveWeight_nonneg (k + m)))

theorem defect_tail_pair (m : ℕ) (f : QHilbert) :
    inner ℝ (hilbertOne - ratioVector m) (toPareto f) =
      inner ℝ (hilbertOne - ratioVector m) (toPareto (tail (m - 1) f)) := by
  simp only [hilbert_inner_weighted, toPareto_sequence, paretoInner]
  apply tsum_congr
  intro k
  by_cases hk : k < m
  · simp [defect_head_zero m k hk]
  · cases k with
    | zero => simp
    | succ n =>
      have hq : qSequence (tail (m - 1) f) (n + 1) = qSequence f (n + 1) := by
        change (f n - finiteHead (m - 1) f n) / Real.sqrt (qWeight n) = _
        rw [finiteHead_apply_eq_zero _ _ _ (by omega), sub_zero]
        rfl
      rw [hq]

section MatchedProjection

variable (S : Submodule ℝ QHilbert) (T : Submodule ℝ ThresholdHilbert)
variable [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]

/-- The Pareto residual paired with the target gives its own squared norm. -/
theorem matched_pResidual_mean :
    inner ℝ hilbertOne (toPareto (qOne - pFit T qOne)) =
      ‖toPareto (qOne - pFit T qOne)‖ ^ 2 := by
  rw [toPareto_sub, toPareto_pFit, toPareto_qOne]
  have h := Submodule.inner_right_of_mem_orthogonal
    (T.starProjection_apply_mem hilbertOne)
    (Submodule.sub_starProjection_mem_orthogonal (K := T) hilbertOne)
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, h, sub_zero]

/-- A common test vector sees the displacement through the shifted reciprocal
of the Pareto residual. The dictionaries need only share this test vector. -/
theorem matched_displacement_pairing (v : QHilbert) (hv : v ∈ S)
    (hvp : toPareto v ∈ T) :
    inner ℝ v (qFit S qOne - pFit T qOne) =
      inner ℝ v (B (qOne - pFit T qOne)) := by
  have hq : inner ℝ v (qOne - qFit S qOne) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hv
      (Submodule.sub_starProjection_mem_orthogonal (K := S) qOne)
  have hp : inner ℝ (toPareto v) (toPareto (qOne - pFit T qOne)) = 0 := by
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.inner_right_of_mem_orthogonal hvp
      (Submodule.sub_starProjection_mem_orthogonal (K := T) (toPareto qOne))
  rw [pareto_inner_identity] at hp
  have hp' := (mul_eq_zero.mp hp).resolve_left zetaTwo_pos.ne'
  rw [inner_sub_right] at hq hp' ⊢
  linarith only [hq, hp']

/-- The complete signed forcing deficit for a conductor in both dictionaries. -/
theorem matched_conductor_forcing_deficit (m : ℕ) (hm : 0 < m)
    (hv : qResidue m ∈ S) (hvp : toPareto (qResidue m) ∈ T) :
    ‖toPareto (qOne - pFit T qOne)‖ ^ 2 -
      (zetaTwo * m) * inner ℝ (qResidue m) (qFit S qOne - pFit T qOne) =
      ∑' k : ℕ, positiveWeight k *
        ((1 - (((k % m : ℕ) : ℝ) / k)) * qSequence (qOne - pFit T qOne) k) := by
  rw [matched_displacement_pairing S T _ hv hvp, ratioVector_pair_shifted m hm,
    ← matched_pResidual_mean T, ← inner_sub_left, hilbert_inner_weighted,
    defect_sequence, toPareto_sequence]
  unfold paretoInner
  apply tsum_congr
  intro k
  by_cases hk : k = 0 <;> simp [hk, zeroAnchor, remRatio]

/-- Only the physical Pareto residual tail at and above the conductor enters
the forcing error. This estimate is uniform in the choice of dictionaries. -/
theorem matched_conductor_forcing_error (m : ℕ) (hm : 0 < m)
    (hv : qResidue m ∈ S) (hvp : toPareto (qResidue m) ∈ T) :
    |‖toPareto (qOne - pFit T qOne)‖ ^ 2 -
      (zetaTwo * m) * inner ℝ (qResidue m) (qFit S qOne - pFit T qOne)| ≤
      Real.sqrt (1 / (m : ℝ)) * ‖toPareto (tail (m - 1) (qOne - pFit T qOne))‖ := by
  rw [matched_displacement_pairing S T _ hv hvp, ratioVector_pair_shifted m hm,
    ← matched_pResidual_mean T, ← inner_sub_left, defect_tail_pair]
  apply (abs_real_inner_le_norm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (ratioVector_error_norm_sq_le m hm)

end MatchedProjection

theorem finitePResidual_mean (N : ℕ) :
    inner ℝ hilbertOne (toPareto (qOne - finitePFit N)) =
      ‖toPareto (qOne - finitePFit N)‖ ^ 2 :=
  matched_pResidual_mean (paretoStage N)

/-- The deficit is a full signed series with multiplier zero below the conductor. -/
theorem full_conductor_forcing_deficit (N m : ℕ) (hm : 0 < m) (hv : qResidue m ∈ stage N) :
    ‖toPareto (qOne - finitePFit N)‖ ^ 2 -
      (zetaTwo * m) * inner ℝ (qResidue m) (finiteDisplacement N) =
      ∑' k : ℕ, positiveWeight k *
        ((1 - (((k % m : ℕ) : ℝ) / k)) * qSequence (qOne - finitePFit N) k) :=
  matched_conductor_forcing_deficit (stage N) (paretoStage N) m hm hv
    ((toPareto_mem_paretoStage_iff N _).mpr hv)

/-- Conductor-normalized right-hand sides approach the same squared Pareto
residual norm. The output stage does not occur in the modulus of this estimate. -/
theorem full_conductor_forcing_error (N m : ℕ) (hm : 0 < m) (hv : qResidue m ∈ stage N) :
    |‖toPareto (qOne - finitePFit N)‖ ^ 2 -
      (zetaTwo * m) * inner ℝ (qResidue m) (finiteDisplacement N)| ≤
      Real.sqrt (1 / (m : ℝ)) * ‖toPareto (tail (m - 1) (qOne - finitePFit N))‖ :=
  matched_conductor_forcing_error (stage N) (paretoStage N) m hm hv
    ((toPareto_mem_paretoStage_iff N _).mpr hv)

/-- The signed defects for all conductors at once satisfy a Bessel bound.
The proof uses the discrete dual Hardy inequality (E. T. Copson, J. London
Math. Soc. 2 (1927), 9–12, https://doi.org/10.1112/jlms/s1-2.1.9).
Coordinates 0 and 1 vanish for every conductor in this family. -/
theorem forcing_deficit_bessel (x : ThresholdHilbert) (D : ℕ) :
    (∑ d ∈ Finset.range D, (inner ℝ (hilbertOne - ratioVector (d + 2)) x) ^ 2) ≤
      4 * ‖x‖ ^ 2 := by
  let a (n : ℕ) : ℝ := hilbertSequence x (n + 2) / ((n : ℝ) + 3)
  let K (d n : ℕ) : ℝ := (1 - remRatio (d + 2) (n + 2)) / ((n : ℝ) + 2)
  have hzero (d n : ℕ) (h : n < d) : K d n = 0 := by
    have ht : n + 2 < d + 2 := by omega
    have hh : (n + 2 : ℝ) ≠ 0 := by positivity
    simp [K, remRatio, Nat.mod_eq_of_lt ht, hh]
  have hbound (d n : ℕ) : |K d n| ≤ 1 / ((n : ℝ) + 2) := by
    have h := remRatio_bounds (d + 2) (n + 2)
    rw [show |K d n| = K d n from abs_of_nonneg (div_nonneg (sub_nonneg.mpr h.2) (by positivity))]
    exact div_le_div_of_nonneg_right (by linarith [h.1]) (by positivity)
  let e (k : ℕ) : ℝ := positiveWeight k * hilbertSequence x k ^ 2
  have hes : Summable e := hilbertSequence_square_summable x
  have he (k : ℕ) : 0 ≤ e k := mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)
  have ha (n : ℕ) : a n ^ 2 ≤ e (n + 2) := by
    simp only [a, e, positiveWeight, Nat.cast_add, Nat.cast_ofNat]
    generalize hilbertSequence x (n + 2) = y
    have h2 : 0 < (n : ℝ) + 2 := by positivity
    have h3 : 0 < (n : ℝ) + 2 + 1 := by positivity
    have hn3 : 0 < (n : ℝ) + 3 := by positivity
    field_simp
    nlinarith [sq_nonneg y, mul_nonneg (Nat.cast_nonneg n (α := ℝ)) (sq_nonneg y)]
  have hnorm (M : ℕ) : (∑ n ∈ Finset.range M, a n ^ 2) ≤ ‖x‖ ^ 2 := by
    have hs := (summable_nat_add_iff 2).mpr hes
    calc
      _ ≤ ∑ n ∈ Finset.range M, e (n + 2) := Finset.sum_le_sum (fun n _ => ha n)
      _ ≤ ∑' n, e (n + 2) := hs.sum_le_tsum _ (fun i _ => he _)
      _ ≤ ∑' n, e n := by
        rw [← hes.sum_add_tsum_nat_add 2]
        exact le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => he _))
      _ = _ := (hilbert_norm_weighted_sq x).symm
  have hlim (d : ℕ) : Filter.Tendsto (fun M => ∑ n ∈ Finset.range M, a n * K d n)
      Filter.atTop (nhds (inner ℝ (hilbertOne - ratioVector (d + 2)) x)) := by
    let t (k : ℕ) := positiveWeight k *
      (hilbertSequence (hilbertOne - ratioVector (d + 2)) k * hilbertSequence x k)
    have ht : Summable t := weighted_product_summable_of_square
      (hilbertSequence_square_summable _) (hilbertSequence_square_summable _)
    have hterm (n : ℕ) : a n * K d n = t (n + 2) := by
      dsimp only [a,K,t]
      rw [defect_sequence]
      simp only [zeroAnchor, show ∀ n : ℕ, n + 2 ≠ 0 by omega, if_false]
      simp only [positiveWeight, Nat.cast_add, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
      rw [show (n : ℝ) + 2 + 1 = n + 3 by ring]
      ring
    have hprefix : ∑ k ∈ Finset.range 2, t k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkd : k < d + 2 := by have := Finset.mem_range.mp hk; omega
      simp only [t, defect_head_zero (d + 2) k hkd, zero_mul, mul_zero]
    have heq : (∑' n, t (n + 2)) = inner ℝ (hilbertOne - ratioVector (d + 2)) x := by
      have h := ht.sum_add_tsum_nat_add 2
      rw [hprefix, zero_add] at h
      simpa only [hilbert_inner_weighted, paretoInner, t] using h
    simpa only [hterm, ← heq] using
      ((summable_nat_add_iff 2).mpr ht).hasSum.tendsto_sum_nat
  apply le_of_tendsto (tendsto_finsetSum _ (fun d _ => (hlim d).pow 2))
  filter_upwards [Filter.eventually_ge_atTop D] with M hM
  exact (RiemannResearch.Analysis.DiscreteTailHardy.triangular_matrix_bessel a K M D hM
    hzero hbound).trans (by linarith [hnorm M])

/-- Uniform bound for the actual scaled Gram errors, over any selection of
included conductors. Each selected index d represents conductor d + 2. -/
theorem full_conductor_forcing_bessel (N D : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.range D) (hv : ∀ d ∈ s, qResidue (d + 2) ∈ stage N) :
    (∑ d ∈ s, (‖toPareto (qOne - finitePFit N)‖ ^ 2 -
        (zetaTwo * (d + 2 : ℕ)) * inner ℝ (qResidue (d + 2)) (finiteDisplacement N)) ^ 2)
      ≤ 4 * ‖toPareto (qOne - finitePFit N)‖ ^ 2 := by
  calc
    _ = ∑ d ∈ s, (inner ℝ (hilbertOne - ratioVector (d + 2))
        (toPareto (qOne - finitePFit N))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      have h := Submodule.inner_right_of_mem_orthogonal (hv d hd) (finite_witness_mem_orthogonal N)
      rw [inner_sub_right] at h
      rw [← sub_eq_zero.mp h, ratioVector_pair_shifted _ (by omega), ← finitePResidual_mean,
        inner_sub_left]
    _ ≤ _ := (Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)).trans
      (forcing_deficit_bessel _ D)

/-- The adjacent full rows share their entire physical prefix below m.
The extra reciprocal physical coordinate converts the complete consecutive
residue harmonic estimate into a stronger bound on their difference. -/
theorem adjacent_full_data_difference (N m : ℕ) (hm : 0 < m)
    (hv : qResidue m ∈ stage N) (hw : qResidue (m + 1) ∈ stage N) :
    (m : ℝ) ^ 2 * ((zetaTwo * m) * inner ℝ (qResidue m) (finiteDisplacement N) -
      (zetaTwo * (m + 1 : ℕ)) * inner ℝ (qResidue (m + 1)) (finiteDisplacement N)) ^ 2 ≤
      (harmonic m : ℝ) * ‖toPareto (qOne - finitePFit N)‖ ^ 2 := by
  let v := ratioVector m - ratioVector (m + 1)
  have hseq (k : ℕ) : hilbertSequence v k =
      (Pareto.adjacentResidueDifference m k) / k := by
    change hilbertSequenceLinear (ratioVector m - ratioVector (m + 1)) k = _
    rw [map_sub]
    change hilbertSequence (ratioVector m) k - hilbertSequence (ratioVector (m + 1)) k = _
    rw [ratioVector_sequence, ratioVector_sequence]
    exact (sub_div _ _ _).symm
  have hnorm : (m : ℝ) ^ 2 * ‖v‖ ^ 2 ≤ (harmonic m : ℝ) := by
    rw [hilbert_norm_weighted_sq, ← tsum_mul_left]
    apply le_trans _ (Pareto.adjacentResidueDifference_energy_upper m hm)
    apply Summable.tsum_le_tsum _
      ((hilbertSequence_square_summable v).mul_left ((m : ℝ) ^ 2))
      (Pareto.adjacentResidueDifference_summable m hm)
    intro k
    rw [hseq]
    by_cases hkm : k < m
    · have hz : Pareto.adjacentResidueDifference m k = 0 := by
        simp [Pareto.adjacentResidueDifference, Pareto.residue, Nat.mod_eq_of_lt hkm,
          Nat.mod_eq_of_lt (by omega : k < m + 1)]
      simp [hz]
    · have hp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hle : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
        have hle' : (m : ℝ) ≤ k := by exact_mod_cast (show m ≤ k by omega)
        gcongr
      calc
        _ ≤ (k : ℝ) ^ 2 * (positiveWeight k *
            (Pareto.adjacentResidueDifference m k / k) ^ 2) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
        _ = _ := by field_simp [hp.ne']
  have h₁ := Submodule.inner_right_of_mem_orthogonal hv (finite_witness_mem_orthogonal N)
  have h₂ := Submodule.inner_right_of_mem_orthogonal hw (finite_witness_mem_orthogonal N)
  rw [inner_sub_right] at h₁ h₂
  rw [← sub_eq_zero.mp h₁, ← sub_eq_zero.mp h₂, ratioVector_pair_shifted m hm,
    ratioVector_pair_shifted (m + 1) (by omega), ← inner_sub_left]
  let r := toPareto (qOne - finitePFit N)
  change (m : ℝ) ^ 2 * (inner ℝ v r) ^ 2 ≤ _ * ‖r‖ ^ 2
  have hcs := abs_real_inner_le_norm v r
  have hsq : (inner ℝ v r) ^ 2 ≤ ‖v‖ ^ 2 * ‖r‖ ^ 2 := by
    simpa only [sq_abs, mul_pow] using
      (show |inner ℝ v r| ^ 2 ≤ (‖v‖ * ‖r‖) ^ 2 by gcongr)
  calc
    _ ≤ (m : ℝ) ^ 2 * (‖v‖ ^ 2 * ‖r‖ ^ 2) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
