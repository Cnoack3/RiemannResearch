import RiemannResearch.RH.ParetoAffineHeadTower
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QSquarefreeCoordinates
import RiemannResearch.RH.QDivisorWaveletBounds
import RiemannResearch.RH.QShiftedReciprocal

/-!
# The affine head tower in zeta-two coordinates

The sequence-preserving equivalence transports the physical constraints and
the Pareto mean. Each stage has its own nearest point in the zeta-two norm.
The full Jordan wavelet transform computes its exact squared distance.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoAffineHeadTower

open Pareto Pareto.PrimePowerSchur Pareto.CoefficientStabilization
open ZetaTwoHilbert ZetaTwoProbability QParetoEquivalence ZetaTwoParetoTransfer
open QSquarefreeCoordinates QDivisorHilbert

/-- Riesz representer of the Pareto probability mean in the zeta-two metric. -/
def meanWeight : QHilbert := zetaTwo • (qOne - QShiftedReciprocal.B qOne)

theorem pareto_mean (v : QHilbert) :
    inner ℝ (paretoEquiv v) hilbertOne = inner ℝ v meanWeight := by
  have h := QShiftedReciprocal.pareto_inner_identity v qOne
  simpa only [paretoEquiv_apply, toPareto_qOne, meanWeight, real_inner_smul_right,
    inner_sub_right] using h

/-- Density dP/dQ evaluated at a positive physical site. -/
theorem meanWeight_value (k : ℕ) (hk : 0 < k) :
    qSequence meanWeight k = zetaTwo * (k : ℝ) / ((k : ℝ) + 1) := by
  change qSequenceLinear (zetaTwo • (qOne - QShiftedReciprocal.B qOne)) k = _
  rw [map_smul]
  change zetaTwo * (qSequenceLinear (qOne - QShiftedReciprocal.B qOne) k) = _
  rw [map_sub]
  change zetaTwo * (qSequence qOne k - qSequence (QShiftedReciprocal.B qOne) k) = _
  rw [QShiftedReciprocal.qSequence_B, qSequence_qOne]
  simp only [qOneSequence, if_neg (Nat.ne_of_gt hk)]
  have hden : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden] <;> ring

/-- The squared norm of the density is the explicit mean-one fiber constant. -/
theorem meanWeight_norm_sq : ‖meanWeight‖^2 = zetaTwo * (zetaTwo - 1) := by
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hz := hs.sum_add_tsum_nat_add 2
  have hfinite : (∑ k ∈ Finset.range 2, 1 / (k : ℝ)^2) = 1 := by
    norm_num [Finset.sum_range_succ]
  change (∑ k ∈ Finset.range 2, 1 / (k : ℝ)^2) +
    (∑' k : ℕ, 1 / (((k+2 : ℕ) : ℝ)^2)) = ∑' k : ℕ, 1 / (k : ℝ)^2 at hz
  rw [hfinite, ← zetaTwo_eq_nat_sum] at hz
  calc
    ‖meanWeight‖^2 = ∑' n : ℕ, (meanWeight n)^2 := qNorm_sq _
    _ = ∑' n : ℕ, zetaTwo * (1 / (((n+2 : ℕ) : ℝ)^2)) := by
      apply tsum_congr
      intro n
      rw [← qSequence_weighted_square, meanWeight_value _ (Nat.succ_pos _)]
      unfold positiveQWeight
      push_cast
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
      have h3 : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp [zetaTwo_pos.ne', h1, h2, h3] <;> ring
    _ = _ := by
      rw [tsum_mul_left]
      congr 1
      linarith only [hz]

/-- Physical tangent space with the zeta-two metric. -/
def kernel (n : ℕ) : Submodule ℝ QHilbert :=
  (AffineHeadTower.kernel n).comap paretoEquiv.toLinearEquiv.toLinearMap

theorem kernel_closed (n : ℕ) : IsClosed (kernel n : Set QHilbert) :=
  (AffineHeadTower.kernel_closed n).preimage paretoEquiv.continuous

instance (n : ℕ) : (kernel n).HasOrthogonalProjection := by
  let _ : CompleteSpace (kernel n) := (kernel_closed n).completeSpace_coe
  infer_instance

/-- Transport of the Pareto minimizer, used as one feasible point. -/
def anchor (n : ℕ) : QHilbert := paretoEquiv.symm (AffineHeadTower.patch n)

/-- All physical patches with Pareto mean one and the first n values one. -/
def fiber (n : ℕ) : Set QHilbert := paretoEquiv ⁻¹' AffineHeadTower.fiber n

theorem mem_fiber_iff (n : ℕ) (v : QHilbert) :
    v ∈ fiber n ↔ v - anchor n ∈ kernel n := by
  change paretoEquiv v ∈ AffineHeadTower.fiber n ↔
    paretoEquiv (v - paretoEquiv.symm (AffineHeadTower.patch n)) ∈ AffineHeadTower.kernel n
  rw [map_sub, paretoEquiv.apply_symm_apply, AffineHeadTower.mem_fiber_iff]

/-- The nearest point to the constant in the actual zeta-two metric. -/
def patch (n : ℕ) : QHilbert :=
  anchor n + (kernel n).starProjection (qOne - anchor n)

theorem patch_mem (n : ℕ) : patch n ∈ fiber n := by
  rw [mem_fiber_iff, patch, add_sub_cancel_left]
  exact (kernel n).starProjection_apply_mem _

theorem error_orthogonal (n : ℕ) : qOne - patch n ∈ (kernel n)ᗮ := by
  have h := (kernel n).sub_starProjection_mem_orthogonal (qOne - anchor n)
  simpa only [patch, ← sub_sub] using h

theorem feasible_error_sq (n : ℕ) {v : QHilbert} (hv : v ∈ fiber n) :
    ‖qOne - v‖^2 = ‖qOne - patch n‖^2 + ‖v - patch n‖^2 := by
  have hd : v - patch n ∈ kernel n := by
    have h := (kernel n).sub_mem ((mem_fiber_iff n v).mp hv)
      ((mem_fiber_iff n _).mp (patch_mem n))
    simpa only [sub_sub_sub_cancel_right] using h
  have ho := (error_orthogonal n) _ hd
  have hdiff : qOne - v = (qOne - patch n) - (v - patch n) := by abel
  rw [real_inner_comm] at ho
  rw [hdiff, norm_sub_sq_real, ho]
  ring

theorem nested_error_sq {n m : ℕ} (hnm : n ≤ m) :
    ‖qOne - patch m‖^2 = ‖qOne - patch n‖^2 + ‖patch m - patch n‖^2 := by
  have h := patch_mem m
  apply feasible_error_sq
  exact ⟨h.1, h.2.1, fun i hi => h.2.2 i (lt_of_lt_of_le hi hnm)⟩

theorem coordinate_energy (n : ℕ) :
    ‖qOne - patch n‖^2 = (1 - fullCoordinates (patch n) 1)^2 +
      nonconstantEnergy (fullCoordinates (patch n)) :=
  error_eq_mean_and_nonconstantEnergy _

theorem error_le_anchor (n : ℕ) :
    ‖qOne - patch n‖^2 ≤ (2 / zetaTwo) * ‖AffineHeadTower.patch n - hilbertOne‖^2 := by
  have ha : anchor n ∈ fiber n := by simp [fiber, anchor, (AffineHeadTower.patch_spec n).1]
  have he := feasible_error_sq n ha
  have ht := toQ_norm_sq_le (hilbertOne - AffineHeadTower.patch n)
  change ‖paretoEquiv.symm (hilbertOne - AffineHeadTower.patch n)‖^2 ≤ _ at ht
  rw [map_sub, paretoEquiv_symm_apply hilbertOne, toQ_hilbertOne, norm_sub_rev hilbertOne] at ht
  change ‖qOne - anchor n‖^2 ≤ _ at ht
  exact (le_trans (by linarith only [he, sq_nonneg ‖anchor n - patch n‖]) ht)

theorem error_sublinear :
    Tendsto (fun n : ℕ => ‖qOne - patch n‖^2 / (n : ℝ)) atTop (𝓝 0) := by
  have h := AffineHeadTower.patch_error_sublinear.const_mul (2 / zetaTwo)
  rw [mul_zero] at h
  apply squeeze_zero (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)) _ h
  intro n
  simpa only [mul_div_assoc] using
    div_le_div_of_nonneg_right (error_le_anchor n) (Nat.cast_nonneg n)

theorem cofinal_error_iff :
    (∃ C : ℝ, ∀ n : ℕ, ∃ m ≥ n, ‖qOne - patch m‖^2 ≤ C) ↔
      normalizedScreenedTwo = hilbertOne := by
  constructor
  · rintro ⟨C, hC⟩
    apply AffineHeadTower.cofinal_energy_iff.mp
    refine ⟨zetaTwo * C, fun n => ?_⟩
    obtain ⟨m, hm, hcost⟩ := hC n
    refine ⟨m, hm, ?_⟩
    have hf := AffineHeadTower.feasible_error_sq m (patch_mem m)
    have hb := toPareto_norm_sq_le (patch m - qOne)
    change ‖paretoEquiv (patch m - qOne)‖^2 ≤ _ at hb
    rw [map_sub, paretoEquiv_apply qOne, toPareto_qOne, norm_sub_rev (patch m)] at hb
    rw [AffineHeadTower.patch_error_sq] at hf
    have hc := mul_le_mul_of_nonneg_left hcost zetaTwo_pos.le
    linarith only [hf, hb, hc, sq_nonneg ‖normalizedScreenedTwo - hilbertOne‖,
      sq_nonneg ‖paretoEquiv (patch m) - AffineHeadTower.patch m‖]
  · intro hu
    have hV := one_mem_closedSpace_iff_normalizedScreenedTwo.mpr hu
    have hfeas (n : ℕ) : qOne ∈ fiber n := by
      change toPareto qOne ∈ AffineHeadTower.fiber n
      rw [toPareto_qOne]
      exact ⟨hV, by rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq],
        fun i _ => by rw [physicalEvaluationCLM_apply, hilbertOne_sequence]; simp [zeroAnchor]⟩
    refine ⟨0, fun n => ⟨n, le_rfl, ?_⟩⟩
    have h := feasible_error_sq n (hfeas n)
    rw [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith only [h]

/-- The physical error vanishes through site n. The encoded lp coordinates are zero there too. -/
theorem error_head (n : ℕ) (i : ℕ) (hi : i < n) : (qOne - patch n) i = 0 := by
  have he := (patch_mem n).2.2 i hi
  change physicalEvaluationCLM i (toPareto (patch n)) = 1 at he
  rw [physicalEvaluationCLM_apply, toPareto_sequence] at he
  have hq : qSequence (qOne - patch n) (i+1) = 0 := by
    change qSequenceLinear (qOne - patch n) (i+1) = 0
    rw [map_sub]
    change qSequence qOne (i+1) - qSequence (patch n) (i+1) = 0
    rw [he, qSequence_qOne]
    simp [qOneSequence]
  rw [qSequence_succ] at hq
  exact (div_eq_zero_iff.mp hq).resolve_right (Real.sqrt_pos.mpr (qWeight_pos i)).ne'

/-- On a physical tail the two metrics have an asymptotically constant ratio. -/
theorem tail_weight_comparison (n : ℕ) :
    zetaTwo * ((n : ℝ)+1) / ((n : ℝ)+2) * ‖qOne - patch n‖^2 ≤
        ‖toPareto (qOne - patch n)‖^2 ∧
      ‖toPareto (qOne - patch n)‖^2 ≤ zetaTwo * ‖qOne - patch n‖^2 := by
  refine ⟨?_, toPareto_norm_sq_le _⟩
  have hh : ∀ k < n+1, qSequence (qOne - patch n) k = 0 := by
    intro k hk
    cases k with
    | zero => exact qSequence_zero _
    | succ k =>
      rw [qSequence_succ, error_head n k (by omega), zero_div]
  have hl := toPareto_norm_sq_lower_of_head_zero _ (n+1) hh
  push_cast at hl
  convert hl using 1 <;> ring

/-- Explicit zeta-two tail estimate for a bounded physical test vector. -/
theorem bounded_test_tail (g : QHilbert) (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hg : ∀ k : ℕ, 0 < k → |qSequence g k| ≤ A) :
    ‖hilbertTailShift g n‖^2 ≤ (2 / zetaTwo * A^2) / ((n : ℝ) + 1) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k+n+1)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (n+1)).mpr positiveWeight_summable
  have hweight (k : ℕ) : positiveQWeight k ≤ (2 / zetaTwo) * positiveWeight k := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ zetaTwo_pos).mpr
    simpa only [mul_comm] using zetaTwo_mul_QWeight_le_two_mul_paretoWeight k
  calc
    ‖hilbertTailShift g n‖^2 = ∑' k : ℕ, (g (k+n))^2 := hilbert_norm_sq _
    _ ≤ ∑' k : ℕ, positiveWeight (k+n+1) * (2 / zetaTwo * A^2) := by
      apply Summable.tsum_le_tsum _
        ((summable_nat_add_iff n).mpr (qCoordinate_square_summable g)) (hw.mul_right _)
      intro k
      rw [← qSequence_weighted_square]
      have hs := (sq_le_sq₀ (abs_nonneg _) hA).2 (hg (k+n+1) (Nat.succ_pos _))
      rw [sq_abs] at hs
      calc
        _ ≤ positiveQWeight (k+n+1) * A^2 := mul_le_mul_of_nonneg_left hs (positiveQWeight_nonneg _)
        _ ≤ ((2 / zetaTwo) * positiveWeight (k+n+1)) * A^2 :=
          mul_le_mul_of_nonneg_right (hweight _) (sq_nonneg _)
        _ = _ := by ring
    _ = _ := by
      rw [tsum_mul_right]
      have ht : (∑' k : ℕ, positiveWeight (k+n+1)) = 1 / ((n+1 : ℕ) : ℝ) := by
        simpa only [Nat.add_assoc] using positiveWeight_tail_tsum (n+1) (Nat.succ_pos _)
      rw [ht]
      push_cast
      ring

/-- The cost on one bounded test is the full error divided by the physical head length. -/
theorem bounded_test_error_sq (g : QHilbert) (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hg : ∀ k : ℕ, 0 < k → |qSequence g k| ≤ A) :
    (inner ℝ (qOne - patch n) g)^2 ≤
      (2 / zetaTwo * A^2) / ((n : ℝ) + 1) * ‖qOne - patch n‖^2 := by
  rw [real_inner_comm]
  exact (hilbertTailShift_inner_sq_le g _ n (error_head n)).trans
    (mul_le_mul_of_nonneg_right (bounded_test_tail g n A hA hg) (sq_nonneg _))

/-- Sharp physical uniform envelope of the Jordan-normalized wavelet. -/
theorem normalized_wavelet_bound (r : ℕ+) (k : ℕ) (hk : 0 < k) :
    |qSequence (normalizedDivisorWavelet r) k| ≤ Real.sqrt (qJordanTwo (r : ℕ)) := by
  have hJ := qJordanTwo_pos (r : ℕ) r.pos
  have hS := Real.sqrt_pos.mpr hJ
  change |qSequenceLinear ((Real.sqrt (qJordanTwo (r : ℕ)))⁻¹ • divisorWavelet (r : ℕ)) k| ≤ _
  rw [map_smul]
  change |(Real.sqrt (qJordanTwo (r : ℕ)))⁻¹ * qSequence (divisorWavelet (r : ℕ)) k| ≤ _
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hS.le)]
  have h := qDivisorWavelet_abs_le_jordan (r : ℕ) (ne_of_gt r.pos) (⟨k,hk⟩ : ℕ+)
  have hv := qSequence_divisorWavelet (r : ℕ) (⟨k,hk⟩ : ℕ+)
  change qSequence (divisorWavelet (r : ℕ)) k = _ at hv
  rw [hv]
  calc
    _ ≤ (Real.sqrt (qJordanTwo (r : ℕ)))⁻¹ * qJordanTwo (r : ℕ) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hS.le)
    _ = _ := by
      nth_rw 2 [← Real.sq_sqrt hJ.le]
      field_simp [hS.ne']

/-- Quantitative coefficient estimate, simultaneously for every conductor. -/
theorem conductor_error_sq (r : ℕ+) (n : ℕ) :
    (fullCoordinates (patch n) r - (if r = 1 then 1 else 0))^2 ≤
      (2 / zetaTwo * qJordanTwo (r : ℕ)) / ((n : ℝ) + 1) * ‖qOne - patch n‖^2 := by
  have h := bounded_test_error_sq _ n _ (Real.sqrt_nonneg (qJordanTwo (r : ℕ)))
    (normalized_wavelet_bound r)
  rw [Real.sq_sqrt (qJordanTwo_pos (r : ℕ) r.pos).le, inner_sub_left,
    ← fullCoordinates_apply, ← fullCoordinates_apply, fullCoordinates_qOne_apply] at h
  rw [← neg_sub, neg_sq]
  exact h

/-- Every fixed arithmetic coordinate of the minimizing patches converges unconditionally. -/
theorem tendsto_conductor (r : ℕ+) :
    Tendsto (fun n => fullCoordinates (patch n) r) atTop
      (𝓝 (if r = 1 then 1 else 0)) := by
  let c : ℝ := 2 / zetaTwo * qJordanTwo (r : ℕ)
  have hc : 0 ≤ c := mul_nonneg (div_nonneg (by norm_num) zetaTwo_pos.le)
    (qJordanTwo_pos (r : ℕ) r.pos).le
  have ht := error_sublinear.const_mul c
  rw [mul_zero] at ht
  have hz : Tendsto (fun n => (fullCoordinates (patch n) r - (if r = 1 then 1 else 0))^2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) _ ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      _ ≤ c / ((n : ℝ)+1) * ‖qOne - patch n‖^2 := conductor_error_sq r n
      _ ≤ (c / (n : ℝ)) * ‖qOne - patch n‖^2 := by
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hc hn' (by linarith))
          (sq_nonneg _)
      _ = c * (‖qOne - patch n‖^2 / (n : ℝ)) := by ring
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Function.comp_def, Real.dist_eq, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hz

/-- The mean-one condition controls the first coefficient by the higher ones. -/
theorem nonconstant_controls_error {v : QHilbert} (hv : inner ℝ (paretoEquiv v) hilbertOne = 1) :
    ‖qOne - v‖^2 ≤ ‖meanWeight‖^2 * nonconstantEnergy (fullCoordinates v) := by
  have hw : inner ℝ qOne meanWeight = 1 := by
    rw [← pareto_mean, paretoEquiv_apply, toPareto_qOne, real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  have hw' : inner ℝ meanWeight qOne = 1 := by rw [real_inner_comm]; exact hw
  have hvm : inner ℝ v meanWeight = 1 := (pareto_mean v).symm.trans hv
  have hi : inner ℝ (centered v) (meanWeight - qOne) = 1 - fullCoordinates v 1 := by
    rw [centered, inner_sub_left, real_inner_smul_left, inner_sub_right, inner_sub_right,
      hvm, hw, real_inner_self_eq_norm_sq, qOne_norm_sq, fullCoordinates_first]
    ring
  have hn : ‖meanWeight - qOne‖^2 = ‖meanWeight‖^2 - 1 := by
    rw [norm_sub_sq_real, hw', qOne_norm_sq]
    ring
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    (abs_real_inner_le_norm (centered v) (meanWeight - qOne))
  rw [sq_abs, hi, mul_pow, hn] at h
  rw [error_eq_mean_and_nonconstantEnergy, centered_energy]
  nlinarith only [h]

/-- It suffices to bound the total energy of the nonconstant conductor coordinates cofinally. -/
theorem cofinal_nonconstant_iff :
    (∃ C : ℝ, ∀ n : ℕ, ∃ m ≥ n, nonconstantEnergy (fullCoordinates (patch m)) ≤ C) ↔
      normalizedScreenedTwo = hilbertOne := by
  rw [← cofinal_error_iff]
  constructor
  · rintro ⟨C,hC⟩
    refine ⟨‖meanWeight‖^2 * C, fun n => ?_⟩
    obtain ⟨m,hm,he⟩ := hC n
    exact ⟨m,hm,(nonconstant_controls_error (v := patch m) (patch_mem m).2.1).trans
      (mul_le_mul_of_nonneg_left he (sq_nonneg _))⟩
  · rintro ⟨C,hC⟩
    refine ⟨C, fun n => ?_⟩
    obtain ⟨m,hm,he⟩ := hC n
    rw [coordinate_energy] at he
    exact ⟨m,hm,le_trans (le_add_of_nonneg_left (sq_nonneg _)) he⟩

end RiemannResearch.RH.ZetaTwoAffineHeadTower
