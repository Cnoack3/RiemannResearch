/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LegalTailResidual
import RiemannResearch.RH.LegalTailNymanMesh
import RiemannResearch.RH.ParetoProjectionOvershoot
import RiemannResearch.RH.ParetoNegativeMassHead
import RiemannResearch.RH.ThresholdHilbertProjection

/-!
# Signed overshoot after reciprocal-block averaging

Source: Christian Noack, legal tail-capacity weak-star handoff, November 2026.
Within a stage, the dyadically dilated fit is still legal. Its cancellation
strengthens the deficit-squared lower bound to one linear in the deficit.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization ParityOptimizer FiniteHeadRepair

/-- Adjoint dilation averages the signed physical residual before taking its negative part. -/
def tailBlockResidual (K : ℕ) : ThresholdHilbert :=
  hilbertDilationAdjoint (K+1) (Nat.succ_pos _) (legalTailResidual K)

theorem tailBlockResidual_coordinate (K k : ℕ) (hk : 0 < k) :
    hilbertSequence (tailBlockResidual K) k =
      ((K+1 : ℕ) : ℝ) / positiveWeight k *
        ∑ j ∈ Finset.Ico ((K+1)*k) ((K+1)*(k+1)),
          positiveWeight j * (1 - hilbertSequence (legalTailMeanVector K) j) := by
  rw [tailBlockResidual, hilbertDilationAdjoint_coordinate _ _ _ hk]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hlow := (Finset.mem_Ico.mp hj).1
  have hjK : K < j := by
    have := Nat.mul_le_mul_left (K+1) (show 1 ≤ k from hk)
    simp only [Nat.mul_one] at this
    omega
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  rw [legalTailResidual, hilbertSequence_sub, Pi.sub_apply, ← hilbertGibbsPhysical_eq,
    paretoTail_physical, if_neg (by omega)]

private theorem block_pair (K : ℕ) (f : ThresholdHilbert) :
    inner ℝ (tailBlockResidual K) f =
      inner ℝ (legalTailResidual K) (hilbertDilation (K+1) (Nat.succ_pos _) f) :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

private theorem dilation_one_eq_scale_tail (K : ℕ) :
    hilbertDilation (K+1) (Nat.succ_pos _) hilbertOne = ((K : ℝ)+1) • paretoTail K := by
  rw [paretoTail_eq_scaled_dilation, hilbertTail, smul_smul]
  simp [Nat.cast_add, Nat.cast_one, show (K : ℝ)+1 ≠ 0 by positivity]

theorem tailBlockResidual_mean (K : ℕ) :
    inner ℝ (tailBlockResidual K) hilbertOne = tailCapacityDeficit K := by
  rw [block_pair, dilation_one_eq_scale_tail, real_inner_smul_right, legalTailResidual_inner_tail,
    legalTailResidual_scaled_energy]

theorem tailBlockResidual_norm_sq_le (K : ℕ) :
    ‖tailBlockResidual K‖ ^ 2 ≤ tailCapacityDeficit K := by
  let b := tailBlockResidual K
  let r := legalTailResidual K
  have hi := real_inner_le_norm r (hilbertDilation (K+1) (Nat.succ_pos _) b)
  rw [← block_pair K b, hilbertDilation_norm, real_inner_self_eq_norm_sq] at hi
  have hb : ‖b‖ ≤ Real.sqrt ((K+1 : ℕ) : ℝ) * ‖r‖ := by
    by_cases h : ‖b‖ = 0
    · rw [h]; positivity
    · by_contra! hlt
      have hp := mul_pos (sub_pos.mpr hlt) (lt_of_le_of_ne (norm_nonneg b) (Ne.symm h))
      change ‖b‖ ^ 2 ≤ ‖r‖ * (Real.sqrt ((K+1 : ℕ) : ℝ) * ‖b‖) at hi
      nlinarith only [hi, hp]
  have he := pow_le_pow_left₀ (norm_nonneg b) hb 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_add, Nat.cast_one] at he
  exact he.trans_eq (legalTailResidual_scaled_energy K)

/-- The actual rational residue trial at `d = (K+1)(i+2)`. -/
theorem tailBlockResidual_residue_cancellation (K i : ℕ) :
    inner ℝ (tailBlockResidual K) (residueAtom i) = 0 := by
  rw [block_pair, hilbertDilation_residueAtom]
  apply legalTailResidual_orthogonal
  let m := K+1
  have hm : 0 < m := Nat.succ_pos K
  have hi : 0 < i+2 := by omega
  have hd : m ≤ m*(i+2) := Nat.le_mul_of_pos_right _ hi
  have ht := (legalHeadKernel (m-1)).smul_mem (m : ℝ)
    (rational_residue_pair_mem_legalHeadKernel m (m*(i+2)) hm hd)
  have hc : (m : ℝ) * ((m : ℝ) / ((m*(i+2) : ℕ) : ℝ)) = (m : ℝ) / ((i+2 : ℕ) : ℝ) := by
    push_cast
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
  rw [smul_sub, smul_smul, hc] at ht
  simpa [m] using ht

private theorem residual_dilation_pair (K h : ℕ) (hh : 0 < h) :
    inner ℝ (legalTailResidual K) (hilbertDilation h hh (paretoTail K)) =
      inner ℝ (legalTailResidual K) (hilbertDilation h hh (legalTailResidual K)) := by
  have hL : h*(K+1)-1+1 = h*(K+1) := Nat.sub_add_cancel (Nat.mul_pos hh (Nat.succ_pos K))
  have hK : K ≤ h*(K+1)-1 := by
    have := Nat.le_mul_of_pos_left (K+1) hh
    omega
  have hv := legalHeadKernel_antitone hK
    (legalHeadKernel_dilation hh hL (legalTailMeanVector_mem K))
  change _ = inner ℝ _ (hilbertDilationContinuous h hh (paretoTail K - legalTailMeanVector K))
  rw [map_sub, inner_sub_right]
  rw [show inner ℝ (legalTailResidual K)
      (hilbertDilationContinuous h hh (legalTailMeanVector K)) = 0 from legalTailResidual_orthogonal hv,
    sub_zero]
  rfl

/-- The signed dyadic correlation is retained in the identity for the first block. -/
theorem tailBlockResidual_first_identity (K : ℕ) :
    hilbertSequence (tailBlockResidual K) 1 / 2 = tailCapacityDeficit K -
      (((K : ℝ)+1)/2) * inner ℝ (legalTailResidual K)
        (hilbertDilation 2 (by decide) (legalTailResidual K)) := by
  have hd : hilbertDilation (K+1) (Nat.succ_pos _) (hilbertDilation 2 (by decide) hilbertOne) =
      ((K : ℝ)+1) • hilbertDilation 2 (by decide) (paretoTail K) := by
    calc
      _ = hilbertDilation 2 (by decide) (hilbertDilation (K+1) (Nat.succ_pos _) hilbertOne) := by
        simp only [hilbertDilation_comp]
        congr 1
        omega
      _ = _ := by rw [dilation_one_eq_scale_tail, hilbertDilation_smul]
  have h := congrArg (fun f => inner ℝ (tailBlockResidual K) f) firstPoint_eq_dilation_difference
  rw [inner_paretoPoint, hilbertGibbsPhysical_eq, inner_sub_right, real_inner_smul_right,
    tailBlockResidual_mean, block_pair, hd, real_inner_smul_right, residual_dilation_pair,
    show paretoWeight 0 = (1/2 : ℝ) by norm_num [paretoWeight]] at h
  linarith only [h]

theorem tailBlockOvershoot_linear_lower (K : ℕ) :
    (1 - Real.sqrt 2 / 2) * tailCapacityDeficit K ≤ hilbertNegativeMass (tailBlockResidual K) := by
  let r := legalTailResidual K
  have ho : inner ℝ (tailBlockResidual K) oddIndicator = 0 := by
    rw [oddIndicator, real_inner_smul_right, tailBlockResidual_residue_cancellation, mul_zero]
  have hi := real_inner_le_norm r (hilbertDilation 2 (by decide) r)
  rw [hilbertDilation_norm] at hi
  have hb := mul_le_mul_of_nonneg_left hi (show 0 ≤ ((K : ℝ)+1)/2 by positivity)
  have he := legalTailResidual_scaled_energy K
  change ((K : ℝ)+1) * ‖r‖^2 = tailCapacityDeficit K at he
  have hx := odd_orthogonal_first_le_negativeMass (tailBlockResidual K) ho
  have hf := tailBlockResidual_first_identity K
  change _ = tailCapacityDeficit K - _ * inner ℝ r (hilbertDilation 2 _ r) at hf
  push_cast at hb
  nlinarith only [hb, hf, hx, congrArg (fun z : ℝ => Real.sqrt 2 * z) he]

theorem tailBlockOvershoot_quadratic_lower (K : ℕ) :
    (4/27 : ℝ) * tailCapacityDeficit K ^ 2 ≤ hilbertNegativeMass (tailBlockResidual K) := by
  obtain ⟨h0,h1⟩ := tailCapacityDeficit_bounds K
  have hs : Real.sqrt 2 ≤ 3/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact le_trans (by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1),
    mul_le_mul_of_nonneg_right hs h0]) (tailBlockOvershoot_linear_lower K)

theorem tailBlockOvershoot_head_lower (K N : ℕ) :
    (1 - Real.sqrt 2 / 2) * tailCapacityDeficit K -
      Real.sqrt (tailCapacityDeficit K / ((N : ℝ) + 1)) ≤
      negativeMassHead N (tailBlockResidual K) := by
  have hb : ‖tailBlockResidual K‖ ≤ Real.sqrt (tailCapacityDeficit K) :=
    (Real.le_sqrt (norm_nonneg _) (tailCapacityDeficit_bounds K).1).mpr
      (tailBlockResidual_norm_sq_le K)
  have h := negativeMassHead_truncation_upper N (tailBlockResidual K)
  have ht := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (1 / ((N : ℝ) + 1)))
  rw [← Real.sqrt_mul (tailCapacityDeficit_bounds K).1,
    show tailCapacityDeficit K * (1/((N : ℝ) + 1)) =
      tailCapacityDeficit K/((N : ℝ) + 1) by ring] at ht
  linarith [tailBlockOvershoot_linear_lower K]

theorem tailBlockOvershoot_head_upper (K N : ℕ) :
    negativeMassHead N (tailBlockResidual K) ≤
      (Real.sqrt (tailCapacityDeficit K) - tailCapacityDeficit K)/2 := by
  apply (negativeMassHead_le _ _).trans
  rw [hilbertNegativeMass_eq, tailBlockResidual_mean]
  have hb := (Real.le_sqrt (norm_nonneg (tailBlockResidual K)) (tailCapacityDeficit_bounds K).1).mpr
    (tailBlockResidual_norm_sq_le K)
  linarith [hilbertL1Norm_le_norm (tailBlockResidual K)]

/-- A deficit at least ε gives a fixed head with a positive lower bound.
The cutoff here grows as 1/ε. -/
theorem tailBlockOvershoot_finite_window {K N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hK : ε ≤ tailCapacityDeficit K) (hN : 64 ≤ ε * ((N : ℝ) + 1)) :
    tailCapacityDeficit K / 8 ≤ negativeMassHead N (tailBlockResidual K) := by
  let δ := tailCapacityDeficit K
  have hd : 0 < δ := hε.trans_le hK
  have h64 : 64 ≤ δ * ((N : ℝ) + 1) :=
    hN.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  have ht : Real.sqrt (δ/((N : ℝ) + 1)) ≤ δ/8 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, (div_le_iff₀ (by positivity)).mpr ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left h64 hd.le]
  have hs : Real.sqrt 2 ≤ 3/2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have h := tailBlockOvershoot_head_lower K N
  change (1-Real.sqrt 2/2)*δ - _ ≤ _ at h
  change δ/8 ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hs hd.le]

theorem tailBlockOvershoot_exists_block {K N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hK : ε ≤ tailCapacityDeficit K) (hN : 64 ≤ ε * ((N : ℝ) + 1)) :
    ∃ j < N, hilbertSequence (tailBlockResidual K) (j+1) ≤ -tailCapacityDeficit K/8 := by
  let δ := tailCapacityDeficit K
  have hd : 0 < δ := hε.trans_le hK
  by_contra! hn
  have hb := tailBlockOvershoot_finite_window hε hK hN
  rw [negativeMassHead_eq_sum] at hb
  have hu : (∑ j ∈ Finset.range N, paretoWeight j *
      max (-hilbertSequence (tailBlockResidual K) (j+1)) 0) ≤
      (∑ j ∈ Finset.range N, paretoWeight j) * (δ/8) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (paretoWeight_pos j).le
    apply max_le _ (by positivity)
    change -hilbertSequence (tailBlockResidual K) (j+1) ≤ tailCapacityDeficit K / 8
    linarith only [hn j (Finset.mem_range.mp hj)]
  rw [paretoWeight_partial_sum] at hu
  have hlt : 1 - 1/((N : ℝ)+1) < 1 := by
    have : 0 < 1/((N : ℝ)+1) := by positivity
    linarith
  have := mul_lt_mul_of_pos_right hlt (show 0 < δ/8 by positivity)
  change δ/8 ≤ _ at hb
  linarith

open Filter in
theorem fixedBlock_liminf_zero_iff_RH :
    (∀ N : ℕ, 0 < N → liminf (fun n : ℕ =>
      negativeMassHead N (tailBlockResidual ((n+1).factorial-1))) atTop = 0) ↔
      RiemannHypothesis := by
  let C := ⨆ k, normalizedLegalTailMeanCapacity k
  have hbd : BddAbove (Set.range normalizedLegalTailMeanCapacity) :=
    ⟨1, by rintro _ ⟨k,rfl⟩; exact (legalTailMeanCapacity_normalized_bounds k).2⟩
  constructor
  · intro h
    apply normalizedLegalTailMeanCapacity_iSup_eq_one_iff_RH.mp
    have hC : C ≤ 1 := ciSup_le (fun k => (legalTailMeanCapacity_normalized_bounds k).2)
    by_contra hne
    have hδ : 0 < 1-C := sub_pos.mpr (lt_of_le_of_ne hC hne)
    obtain ⟨n,hn⟩ := exists_nat_gt (64/(1-C))
    let N := n+1
    have hN : 64 ≤ (1-C) * ((N : ℝ)+1) := by
      have hh := (div_lt_iff₀ hδ).mp hn
      dsimp [N]; push_cast; nlinarith
    let B := fun j : ℕ => negativeMassHead N (tailBlockResidual ((j+1).factorial-1))
    have hK (K : ℕ) : 1-C ≤ tailCapacityDeficit K :=
      sub_le_sub_left (le_ciSup hbd K) 1
    have hfloor (j : ℕ) : (1-C)/8 ≤ B j :=
      (div_le_div_of_nonneg_right (hK _) (by norm_num)).trans
        (tailBlockOvershoot_finite_window hδ (hK _) hN)
    have hupper (j : ℕ) : B j ≤ 1 := by
      let k := (j+1).factorial-1
      have hs : Real.sqrt (tailCapacityDeficit k) ≤ 1 :=
        (Real.sqrt_le_iff).mpr ⟨zero_le_one, by simpa using (tailCapacityDeficit_bounds k).2⟩
      exact (tailBlockOvershoot_head_upper k N).trans
        (by linarith [(tailCapacityDeficit_bounds k).1])
    have hl : (1-C)/8 ≤ liminf B atTop := by
      rw [liminf_eq]
      apply le_csSup
      · refine ⟨1,fun a ha => ?_⟩
        obtain ⟨j,hj⟩ := (show ∀ᶠ j in atTop, a ≤ B j from ha).exists
        exact hj.trans (hupper j)
      · exact Eventually.of_forall hfloor
    have hz : liminf B atTop = 0 := h N (Nat.succ_pos n)
    linarith
  · intro h N _
    have he (K : ℕ) : tailCapacityDeficit K = 0 := by
      rw [tailCapacityDeficit,(normalizedLegalTailMeanCapacity_eq_one_iff_RH K).mpr h,sub_self]
    have hz (K : ℕ) : negativeMassHead N (tailBlockResidual K) = 0 := by
      apply le_antisymm
      · simpa [he] using tailBlockOvershoot_head_upper K N
      · rw [negativeMassHead_eq_sum]
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (paretoWeight_pos j).le (le_max_right _ _))
    simp [hz]

end RiemannResearch.RH.Pareto.PrimePowerSchur
