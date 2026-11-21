import RiemannResearch.RH.ParetoParityNormBounds
import RiemannResearch.RH.ActualDyadicAdjointDefect
import RiemannResearch.RH.DilationAdjointCriterion

/-!
# A single ambient adjoint image for the Pareto parity endpoint

For the scaled physical dilation, the adjoint at two sends parity to the
increasing profile `n / (2*n+1)`. Its first jump exceeds the sum of all later
jumps. Expanding the profile in physical tails gives a signed series and a
two-sided estimate for its pairing with the actual legal residual.

The all-adjoint criterion in Xue, Corollary 1.5 (https://arxiv.org/abs/1911.04029),
motivates testing ambient adjoints. The single parity vector and the bounds
here follow from the repository's physical block and residual identities.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The ambient adjoint for the scaled dyadic dilation, applied to parity. -/
def parityAdjointPacket : ThresholdHilbert :=
  hilbertDilationAdjoint 2 (by decide) (ramanujanPacketHilbert 2)

private def profile (n : ℕ) : ℝ := (n : ℝ) / (2*(n:ℝ)+1)

/-- The odd site in the two-site block contributes this exact weight. -/
theorem parityAdjointPacket_coordinate (n : ℕ) :
    hilbertSequence parityAdjointPacket n = (n : ℝ)/(2*(n:ℝ)+1) := by
  by_cases hz : n = 0
  · subst n
    simp [hilbertSequence_zero]
  have h := dyadicHalfAdjoint_coordinate (ramanujanPacketHilbert 2) n
    (Nat.pos_of_ne_zero hz)
  rw [dyadicHalfAdjoint_apply, hilbertSequence_smul] at h
  simp only [hilbertSequence_ramanujanPacketHilbert,
    ramanujanPacket_prime_eq_residue 2 Nat.prime_two,
    residue, show 2*n % 2 = 0 by omega, show (2*n+1) % 2 = 1 by omega,
    Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, zero_add] at h
  change (1/2 : ℝ) * hilbertSequence parityAdjointPacket n =
    (n:ℝ)/(2*(2*(n:ℝ)+1)) at h
  have hden : 2*(n:ℝ)+1 ≠ 0 := by positivity
  field_simp [hden] at h ⊢
  linarith

/-- Jump at the physical site `j + 2`. The first jump is `1 / 3`. -/
def parityAdjointIncrement (j : ℕ) : ℝ := profile (j+2) - profile (j+1)

theorem parityAdjointIncrement_eq (j : ℕ) :
    parityAdjointIncrement j = 1/((2*(j:ℝ)+3)*(2*(j:ℝ)+5)) := by
  unfold parityAdjointIncrement profile
  push_cast
  field_simp
  ring

private theorem increment_nonneg (j : ℕ) : 0 ≤ parityAdjointIncrement j := by
  rw [parityAdjointIncrement_eq]
  positivity

private theorem profile_le_half (n : ℕ) : profile n ≤ 1/2 := by
  unfold profile
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

private theorem sum_increments (N : ℕ) :
    ∑ j ∈ Finset.range N, parityAdjointIncrement j = profile (N+1) - 1/3 := by
  induction N with
  | zero => norm_num [profile]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, parityAdjointIncrement]
    change profile (N+1) - 1/3 + (profile (N+2) - profile (N+1)) =
      profile (N+2) - 1/3
    ring

private theorem tailPullback_norm_le (m : ℕ) (hm : 0 < m) (x : ThresholdHilbert) :
    ‖(1/(m:ℝ)) • hilbertDilation m hm x‖ ≤ ‖x‖ := by
  have h1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hs : Real.sqrt (m:ℝ) ≤ (m:ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) m), Real.sqrt_nonneg (m:ℝ),
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) (sub_nonneg.mpr h1)]
  have hscale : (1/(m:ℝ))*Real.sqrt (m:ℝ) ≤ 1 := by
    rw [one_div, ← div_eq_inv_mul]
    exact (div_le_one (by positivity)).mpr hs
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),hilbertDilation_norm,← mul_assoc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hscale (norm_nonneg x)

private def tailTerm (j : ℕ) : ThresholdHilbert :=
  parityAdjointIncrement j • hilbertTail (j+2) (by omega)

private theorem summable_tailTerm : Summable tailTerm := by
  have hc (N : ℕ) : ∑ j ∈ Finset.range N, parityAdjointIncrement j ≤ 1/6 := by
    rw [sum_increments]
    linarith [profile_le_half (N+1)]
  have hs : Summable parityAdjointIncrement := summable_of_sum_range_le increment_nonneg hc
  apply Summable.of_norm_bounded hs
  intro j
  have hone : ‖hilbertOne‖ = 1 := by nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  have hb := tailPullback_norm_le (j+2) (by omega) hilbertOne
  rw [hone] at hb
  rw [tailTerm,norm_smul,Real.norm_eq_abs,abs_of_nonneg (increment_nonneg j)]
  simpa only [hilbertTail, mul_one] using mul_le_mul_of_nonneg_left hb (increment_nonneg j)

private def partialPacket (N : ℕ) : ThresholdHilbert :=
  (1/3:ℝ) • hilbertOne + ∑ j ∈ Finset.range N, tailTerm j

private theorem partialPacket_coordinate (N k : ℕ) :
    hilbertSequence (partialPacket N) k = profile (min k (N+1)) := by
  induction N with
  | zero =>
    rw [partialPacket, Finset.range_zero, Finset.sum_empty, add_zero, hilbertSequence_smul,
      hilbertOne_sequence]
    change (1/3:ℝ) * (if k = 0 then 0 else 1) = profile (min k 1)
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst k
      norm_num [profile]
    · rw [if_neg (Nat.ne_of_gt hk), min_eq_right hk]
      norm_num [profile]
  | succ N ih =>
    have hstep : partialPacket (N+1) = partialPacket N + tailTerm N := by
      simp [partialPacket,Finset.sum_range_succ,add_assoc]
    rw [hstep, hilbertSequence_add, Pi.add_apply, ih, tailTerm, hilbertSequence_smul,
      hilbertTail_sequence]
    change profile (min k (N+1)) +
        parityAdjointIncrement N * (if N+2 ≤ k then 1 else 0) = profile (min k (N+2))
    by_cases h : N+2 ≤ k
    · rw [if_pos h,min_eq_right (by omega : N+1 ≤ k),min_eq_right h,mul_one,parityAdjointIncrement]
      ring
    · rw [if_neg h,min_eq_left (by omega : k ≤ N+1),min_eq_left (by omega : k ≤ N+2),
        mul_zero,add_zero]

/-- Exact complete-Hilbert-space expansion in the forward dilates of the constant. -/
theorem parityAdjointPacket_expansion :
    parityAdjointPacket = (1/3:ℝ) • hilbertOne +
      ∑' j : ℕ, parityAdjointIncrement j • hilbertTail (j+2) (by omega) := by
  have ht : Tendsto partialPacket atTop (𝓝 ((1/3:ℝ) • hilbertOne + ∑' j : ℕ, tailTerm j)) :=
    tendsto_const_nhds.add summable_tailTerm.hasSum.tendsto_sum_nat
  apply hilbertSequence_injective
  funext k
  have hlim := (anchoredEvaluationCLM k).continuous.continuousAt.tendsto.comp ht
  have hprofile : Tendsto (fun N => anchoredEvaluationCLM k (partialPacket N))
      atTop (𝓝 (profile k)) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop k] with N hN
    rw [anchoredEvaluationCLM_apply,partialPacket_coordinate,min_eq_left (by omega)]
  rw [parityAdjointPacket_coordinate]
  simpa only [profile, anchoredEvaluationCLM_apply, tailTerm] using
    (tendsto_nhds_unique hprofile hlim)

private theorem abs_residual_inner_tail (m : ℕ) (hm : 0 < m) :
    |inner ℝ limitResidual (hilbertTail m hm)| ≤ limitEnergy := by
  rw [hilbertTail,real_inner_smul_right,limitResidual_inner_dilation_one,← real_inner_smul_right]
  calc
    _ ≤ ‖limitResidual‖ * ‖(1/(m:ℝ)) • hilbertDilation m hm limitResidual‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖limitResidual‖ * ‖limitResidual‖ :=
      mul_le_mul_of_nonneg_left (tailPullback_norm_le m hm limitResidual) (norm_nonneg _)
    _ = limitEnergy := by rw [← pow_two]; rfl

/-- The signed remainder retains every dilation correlation of the actual residual. -/
theorem parityAdjointPacket_residual_series :
    inner ℝ limitResidual parityAdjointPacket = limitEnergy / 3 +
      ∑' j : ℕ, parityAdjointIncrement j *
        inner ℝ limitResidual (hilbertTail (j+2) (by omega)) := by
  rw [parityAdjointPacket_expansion,inner_add_right,real_inner_smul_right,limitResidual_inner_one]
  have ht := (innerSL ℝ limitResidual).map_tsum summable_tailTerm
  change inner ℝ limitResidual (∑' j : ℕ, tailTerm j) = _ at ht
  simp only [tailTerm, innerSL_apply_apply, real_inner_smul_right] at ht
  rw [ht]
  ring

/-- The tail pairings are correlations of the residual with its own forward pullbacks. -/
theorem parityAdjointPacket_residual_dilation_series :
    inner ℝ limitResidual parityAdjointPacket = limitEnergy / 3 +
      ∑' j : ℕ, parityAdjointIncrement j *
        inner ℝ limitResidual ((1 / ((j + 2 : ℕ) : ℝ)) •
          hilbertDilation (j + 2) (by omega) limitResidual) := by
  rw [parityAdjointPacket_residual_series]
  congr 1
  apply tsum_congr
  intro j
  rw [hilbertTail, real_inner_smul_right, real_inner_smul_right, limitResidual_inner_dilation_one]

/-- A one-sided test at the adjoint parity packet detects every positive residual. -/
theorem parityAdjointPacket_residual_bounds :
    limitEnergy/6 ≤ inner ℝ limitResidual parityAdjointPacket ∧
      inner ℝ limitResidual parityAdjointPacket ≤ limitEnergy/2 := by
  have ht : Tendsto partialPacket atTop (𝓝 parityAdjointPacket) := by
    rw [parityAdjointPacket_expansion]
    exact tendsto_const_nhds.add summable_tailTerm.hasSum.tendsto_sum_nat
  have hlim := (innerSL ℝ limitResidual).continuous.continuousAt.tendsto.comp ht
  have he : 0 ≤ limitEnergy := sq_nonneg _
  have hb (N : ℕ) :
      limitEnergy/6 ≤ inner ℝ limitResidual (partialPacket N) ∧
      inner ℝ limitResidual (partialPacket N) ≤ limitEnergy/2 := by
    have ha : |∑ j ∈ Finset.range N, parityAdjointIncrement j *
        inner ℝ limitResidual (hilbertTail (j+2) (by omega))| ≤ limitEnergy/6 := by
      calc
        _ ≤ ∑ j ∈ Finset.range N, |parityAdjointIncrement j *
            inner ℝ limitResidual (hilbertTail (j+2) (by omega))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range N, parityAdjointIncrement j * limitEnergy := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul,abs_of_nonneg (increment_nonneg j)]
          exact mul_le_mul_of_nonneg_left (abs_residual_inner_tail _ _) (increment_nonneg j)
        _ ≤ _ := by
          rw [← Finset.sum_mul,sum_increments]
          linarith [mul_le_mul_of_nonneg_right (profile_le_half (N+1)) he]
    rw [partialPacket,inner_add_right,real_inner_smul_right,limitResidual_inner_one,inner_sum]
    simp only [tailTerm,real_inner_smul_right]
    exact ⟨by linarith [(abs_le.mp ha).1], by linarith [(abs_le.mp ha).2]⟩
  exact ⟨ge_of_tendsto' hlim (fun N => (hb N).1), le_of_tendsto' hlim (fun N => (hb N).2)⟩

theorem normalizedParityCapture_eq_upper_iff_adjointPairing_nonpos :
    normalizedParityCapture = Real.sqrt (1/Real.log 2-1) ↔
      inner ℝ limitResidual parityAdjointPacket ≤ 0 := by
  rw [normalizedParityCapture_eq_upper_iff]
  obtain ⟨hl,hu⟩ := parityAdjointPacket_residual_bounds
  have he : 0 ≤ limitEnergy := sq_nonneg _
  constructor <;> intro h <;> linarith

theorem normalizedParityCapture_eq_upper_iff_adjointParity_mem :
    normalizedParityCapture = Real.sqrt (1/Real.log 2-1) ↔ parityAdjointPacket ∈ closedSpace := by
  constructor
  · intro h
    have htop := closedSpace_eq_top_iff_one_mem.mpr
      (limitEnergy_zero_iff_mem.mp (normalizedParityCapture_eq_upper_iff.mp h))
    simp [htop]
  · intro hg
    apply normalizedParityCapture_eq_upper_iff_adjointPairing_nonpos.mpr
    have ho := Submodule.inner_right_of_mem_orthogonal hg limitResidual_mem_orthogonal
    rw [real_inner_comm] at ho
    exact ho.le

/-- The projection and the ambient dyadic adjoint need commute only on parity. -/
theorem normalizedParityCapture_eq_upper_iff_adjoint_square_on_parity :
    normalizedParityCapture = Real.sqrt (1 / Real.log 2 - 1) ↔
      closedSpace.starProjection parityAdjointPacket =
        hilbertDilationAdjoint 2 (by decide)
          (closedSpace.starProjection (ramanujanPacketHilbert 2)) := by
  rw [Submodule.starProjection_eq_self_iff.mpr (packet_mem_closedSpace 2 (by decide))]
  exact normalizedParityCapture_eq_upper_iff_adjointParity_mem.trans
    Submodule.starProjection_eq_self_iff.symm

/-- The forward dilation on the residual is the signed test whose vanishing suffices. -/
theorem normalizedParityCapture_eq_upper_iff_dilatedResidual_parity_nonpos :
    normalizedParityCapture = Real.sqrt (1/Real.log 2-1) ↔
      inner ℝ (hilbertDilation 2 (by decide) limitResidual) (ramanujanPacketHilbert 2) ≤ 0 := by
  rw [normalizedParityCapture_eq_upper_iff_adjointPairing_nonpos]
  change (inner ℝ limitResidual ((hilbertDilationContinuous 2 (by decide)).adjoint _) ≤ 0) ↔ _
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem normalizedParityCapture_eq_upper_iff_dyadicAdjointInvariant :
    normalizedParityCapture = Real.sqrt (1/Real.log 2-1) ↔
      DilationAdjointCriterion.AdjointInvariant 2 (by decide) := by
  constructor
  · intro h
    have htop := closedSpace_eq_top_iff_one_mem.mpr
      (limitEnergy_zero_iff_mem.mp (normalizedParityCapture_eq_upper_iff.mp h))
    simp [DilationAdjointCriterion.AdjointInvariant,htop]
  · intro h
    exact normalizedParityCapture_eq_upper_iff_adjointParity_mem.mpr
      (h _ (packet_mem_closedSpace 2 (by decide)))

end RiemannResearch.RH.Pareto.PrimePowerSchur
