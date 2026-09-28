import RiemannResearch.RH.DyadicCarryOptimizationLimit
import RiemannResearch.RH.ExactHeadResidualTail

/-!
# Signed sparse transport for dyadic orbit optimization

Source: user-provided
RH_CRT_Orbit_Exhaustion_and_Doubling_Invariance_2026-09-20(1).md,
Sections 8--9, for the orbit construction and research direction.
The signed transport refinement is derived from the existing sparse-multiple
identity and Hilbert tail estimates; no novelty claim is made.
See CRTOrbitSignedTransport20260928.md for the proof and coverage audit.

Established without RH: scaled sparse indicators pair to zero against every
norm-convergent family, and the actual finite dyadic repair energy differs from
the original finite projection energy by o(1/(2^k+1)).

Conditional research reduction: cofinally nonpositive signed observations of
the actual limiting residual imply RH. The sign condition remains Open.
No infinite DPP or RH-to-density provider is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

theorem dyadicMultipleIndicator_head_zero (k n : ℕ) (hn : n < 2 ^ k) :
    dyadicMultipleIndicator k n = 0 := by
  have hdiv : ¬ (2 ^ k + 1) ∣ (n + 1) := by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < n + 1) h
    omega
  have hs := dyadicMultipleIndicator_sequence k (n + 1)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, hdiv] at hs
  rw [hilbertSequence_succ] at hs
  have hw : Real.sqrt (paretoWeight n) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    unfold paretoWeight
    positivity
  exact (div_eq_zero_iff.mp hs).resolve_right hw

theorem dyadicMultipleIndicator_scaled_pairing_sq_le (f : ThresholdHilbert) (k : ℕ) :
    (((2 ^ k + 1 : ℕ) : ℝ) * inner ℝ f (dyadicMultipleIndicator k)) ^ 2 ≤
      2 * ‖hilbertTailShift f (2 ^ k)‖ ^ 2 := by
  have h := hilbertTailShift_inner_sq_le f (dyadicMultipleIndicator k) (2 ^ k)
    (dyadicMultipleIndicator_head_zero k)
  have hb := dyadicMultipleIndicator_norm_sq_le k
  have hd : (0 : ℝ) < ((2 ^ k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hb' := (le_div_iff₀ hd).mp hb
  have hm := mul_le_mul_of_nonneg_left h (le_of_lt hd)
  have ht := mul_le_mul_of_nonneg_left hb' (sq_nonneg ‖hilbertTailShift f (2 ^ k)‖)
  rw [mul_pow]
  nlinarith

private theorem real_tendsto_zero_of_square {a : ℕ → ℝ}
    (h : Tendsto (fun k => a k ^ 2) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.norm_eq_abs,
    sub_zero, Real.sqrt_zero] using ht

theorem dyadicMultipleIndicator_scaled_pairing_tendsto_zero (f : ThresholdHilbert) :
    Tendsto (fun k => ((2 ^ k + 1 : ℕ) : ℝ) *
      inner ℝ f (dyadicMultipleIndicator k)) atTop (𝓝 0) := by
  apply real_tendsto_zero_of_square
  have hk : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self (n := k)).le) tendsto_id
  have ht := ((hilbertTailShift_energy_tendsto_zero f).comp hk).const_mul 2
  apply squeeze_zero (fun k => sq_nonneg _)
    (dyadicMultipleIndicator_scaled_pairing_sq_le f)
  simpa only [mul_zero, Function.comp_def] using ht

theorem dyadicMultipleIndicator_scaled_pairing_global_sq_le (f : ThresholdHilbert) (k : ℕ) :
    (((2 ^ k + 1 : ℕ) : ℝ) * inner ℝ f (dyadicMultipleIndicator k)) ^ 2 ≤
      2 * ‖f‖ ^ 2 := by
  have h := dyadicMultipleIndicator_scaled_pairing_sq_le f k
  have ht := hilbertTailShift_norm_sq f (2 ^ k)
  have hn : 0 ≤ ∑ n ∈ Finset.range (2 ^ k), (f n) ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  linarith

theorem dyadicMultipleIndicator_scaled_moving_pairing_tendsto_zero
    (f : ℕ → ThresholdHilbert) (g : ThresholdHilbert)
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun k => ((2 ^ k + 1 : ℕ) : ℝ) *
      inner ℝ (f k) (dyadicMultipleIndicator k)) atTop (𝓝 0) := by
  have hd : Tendsto (fun k => ((2 ^ k + 1 : ℕ) : ℝ) *
      inner ℝ (f k - g) (dyadicMultipleIndicator k)) atTop (𝓝 0) := by
    apply real_tendsto_zero_of_square
    have ht := ((hf.sub_const g).norm.pow 2).const_mul 2
    apply squeeze_zero (fun k => sq_nonneg _)
      (fun k => dyadicMultipleIndicator_scaled_pairing_global_sq_le (f k - g) k)
    simpa only [sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero] using ht
  have ht := hd.add (dyadicMultipleIndicator_scaled_pairing_tendsto_zero g)
  simpa only [inner_sub_left, mul_sub, sub_add_cancel, add_zero] using ht


/-- The finite projection can be removed from the signed covariance exactly. -/
theorem dyadicFiniteSparseResidual_pairing (k : ℕ) :
    inner ℝ (hilbertOne - projection (2 ^ k)) (dyadicFiniteSparseResidual k) =
      inner ℝ (hilbertOne - projection (2 ^ k)) (dyadicMultipleIndicator k) := by
  have ho : inner ℝ (hilbertOne - projection (2 ^ k))
      ((finiteSpace (2 ^ k)).starProjection (dyadicMultipleIndicator k)) = 0 :=
    Submodule.starProjection_inner_eq_zero hilbertOne _
      ((finiteSpace (2 ^ k)).starProjection_apply_mem (dyadicMultipleIndicator k))
  rw [dyadicFiniteSparseResidual, inner_sub_right, ho, sub_zero]

/-- The full signed energy difference is observed on the sparse physical multiples. -/
theorem dyadicRepairEnergy_zero_head_signed_multiples (k : ℕ) :
    dyadicRepairEnergy k 0 (2 ^ k) = energy (2 ^ k) -
      2 * inner ℝ (hilbertOne - projection (2 ^ k)) (dyadicMultipleIndicator k) +
      ‖dyadicFiniteSparseResidual k‖ ^ 2 := by
  rw [dyadicRepairEnergy_zero_head_signed, dyadicFiniteSparseResidual_pairing]

theorem dyadicFiniteSparseResidual_norm_sq_le (k : ℕ) :
    ‖dyadicFiniteSparseResidual k‖ ^ 2 ≤
      2 / ((2 ^ k + 1 : ℕ) : ℝ) ^ 2 :=
  (Real.le_sqrt (norm_nonneg _) (by positivity)).mp
    (dyadicFiniteSparseResidual_norm_le k)

/-- Explicit complete-tail control of the signed covariance before squaring the energy. -/
theorem dyadicRepairEnergy_signed_covariance_sq_le (k : ℕ) :
    (((2 ^ k + 1 : ℕ) : ℝ) *
      inner ℝ (hilbertOne - projection (2 ^ k)) (dyadicFiniteSparseResidual k)) ^ 2 ≤
      2 * ‖hilbertTailShift (hilbertOne - projection (2 ^ k)) (2 ^ k)‖ ^ 2 := by
  rw [dyadicFiniteSparseResidual_pairing]
  exact dyadicMultipleIndicator_scaled_pairing_sq_le _ k

theorem dyadicRepairEnergy_scaled_covariance_tendsto_zero :
    Tendsto (fun k => ((2 ^ k + 1 : ℕ) : ℝ) *
      inner ℝ (hilbertOne - projection (2 ^ k)) (dyadicMultipleIndicator k))
      atTop (𝓝 0) := by
  have hk : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.lt_two_pow_self (n := k)).le) tendsto_id
  apply dyadicMultipleIndicator_scaled_moving_pairing_tendsto_zero
    (fun k => hilbertOne - projection (2 ^ k)) limitResidual
  exact tendsto_const_nhds.sub (projection_tendsto.comp hk)

theorem dyadicFiniteSparseResidual_scaled_energy_tendsto_zero :
    Tendsto (fun k => ((2 ^ k + 1 : ℕ) : ℝ) *
      ‖dyadicFiniteSparseResidual k‖ ^ 2) atTop (𝓝 0) := by
  have hd : Tendsto (fun k : ℕ => ((2 ^ k + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_add
        (tendsto_const_nhds (x := (1 : ℝ)))
  have ht : Tendsto (fun k : ℕ => 2 / ((2 ^ k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp hd).const_mul 2
  apply squeeze_zero (fun k => by positivity) (fun k => ?_) ht
  calc
    _ ≤ ((2 ^ k + 1 : ℕ) : ℝ) *
        (2 / ((2 ^ k + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (dyadicFiniteSparseResidual_norm_sq_le k) (by positivity)
    _ = _ := by
      have hn : ((2 ^ k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp

/-- Unconditional first-order agreement of the two actual finite optimization energies.
This is o(1/(2^k+1)); it does not say either energy tends to zero. -/
theorem dyadicRepairEnergy_zero_head_scaled_difference_tendsto_zero :
    Tendsto (fun k => ((2 ^ k + 1 : ℕ) : ℝ) *
      (dyadicRepairEnergy k 0 (2 ^ k) - energy (2 ^ k))) atTop (𝓝 0) := by
  have he (k : ℕ) :
      ((2 ^ k + 1 : ℕ) : ℝ) *
        (dyadicRepairEnergy k 0 (2 ^ k) - energy (2 ^ k)) =
      (-2) * (((2 ^ k + 1 : ℕ) : ℝ) *
        inner ℝ (hilbertOne - projection (2 ^ k)) (dyadicMultipleIndicator k)) +
      ((2 ^ k + 1 : ℕ) : ℝ) * ‖dyadicFiniteSparseResidual k‖ ^ 2 := by
    rw [dyadicRepairEnergy_zero_head_signed_multiples]
    ring
  simp_rw [he]
  simpa only [mul_zero, add_zero] using
    (dyadicRepairEnergy_scaled_covariance_tendsto_zero.const_mul (-2)).add
      dyadicFiniteSparseResidual_scaled_energy_tendsto_zero


namespace CoefficientStabilization

/-- Exact residual observation of the reversed orbit, retaining its sign. -/
theorem dyadicSampledResidue_residual_pairing (k : ℕ) :
    inner ℝ limitResidual (dyadicSampledResidue k) =
      limitEnergy - inner ℝ limitResidual (dyadicMultipleIndicator k) := by
  have hg : inner ℝ limitResidual
      (normalizedResidueHilbert (2 ^ k + 1) (by positivity)) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
      (normalizedResidue_mem_closedSpace _ _)
  have he : inner ℝ limitResidual (dyadicMultipleIndicator k) =
      limitEnergy - inner ℝ limitResidual (dyadicSampledResidue k) := by
    rw [dyadicMultipleIndicator, inner_sub_right, inner_add_right,
      limitResidual_inner_one, hg, zero_add]
  linarith

/-- Even the signed residual observation agrees with the defect to o(1/d). -/
theorem dyadicSampledResidue_scaled_residual_pairing_tendsto :
    Tendsto (fun k => ((2 ^ k + 1 : ℕ) : ℝ) *
      (inner ℝ limitResidual (dyadicSampledResidue k) - limitEnergy))
      atTop (𝓝 0) := by
  have he (k : ℕ) :
      ((2 ^ k + 1 : ℕ) : ℝ) *
        (inner ℝ limitResidual (dyadicSampledResidue k) - limitEnergy) =
      -(((2 ^ k + 1 : ℕ) : ℝ) *
        inner ℝ limitResidual (dyadicMultipleIndicator k)) := by
    rw [dyadicSampledResidue_residual_pairing]
    ring
  simp_rw [he]
  simpa only [neg_zero] using
    (dyadicMultipleIndicator_scaled_pairing_tendsto_zero limitResidual).neg

theorem dyadicSampledResidue_residual_pairing_tendsto :
    Tendsto (fun k => inner ℝ limitResidual (dyadicSampledResidue k))
      atTop (𝓝 limitEnergy) := by
  have ht : Tendsto (fun k => inner ℝ limitResidual (dyadicSampledResidue k))
      atTop (𝓝 (inner ℝ limitResidual hilbertOne)) :=
    (tendsto_const_nhds (x := limitResidual)).inner dyadicSampledResidue_tendsto_one
  simpa only [limitResidual_inner_one] using ht

/-- Exact scalar reformulation; the cofinal sign assertion is not proved. -/
theorem dyadic_residual_pairing_cofinally_nonpos_iff :
    (∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
      inner ℝ limitResidual (dyadicSampledResidue k) ≤ 0) ↔
      hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    have hle : limitEnergy ≤ 0 := by
      by_contra hn
      have hp : 0 < limitEnergy := lt_of_not_ge hn
      have ht := dyadicSampledResidue_residual_pairing_tendsto.eventually_const_lt hp
      obtain ⟨K, hK⟩ := eventually_atTop.mp ht
      obtain ⟨k, hk, hnonpos⟩ := h K
      exact (not_lt_of_ge hnonpos) (hK k hk)
    have hz : limitEnergy = 0 := le_antisymm hle (sq_nonneg _)
    exact limitEnergy_zero_iff_mem.mp hz
  · intro h K
    have hz : limitResidual = 0 :=
      limitResidual_zero_iff_energy_zero.mpr (limitEnergy_zero_iff_mem.mpr h)
    exact ⟨K, le_rfl, by simp [hz]⟩

/-- Conditional research reduction: the cofinal arithmetic sign condition is Open. -/
theorem riemannHypothesis_of_dyadic_residual_pairing_cofinally_nonpos
    (h : ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
      inner ℝ limitResidual (dyadicSampledResidue k) ≤ 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr
      (dyadic_residual_pairing_cofinally_nonpos_iff.mp h))

end CoefficientStabilization


end RiemannResearch.RH.Pareto
