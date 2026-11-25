import RiemannResearch.Analysis.AffineObservationProjection
import RiemannResearch.RH.ParetoMixedCenteredParityHeads
import RiemannResearch.RH.ParetoHeadMeanEnergy
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.ParetoFiniteHeadRepair
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.RH.ParetoConductor241Covariance
import RiemannResearch.RH.ScreenedParityPhysicalBounds
import RiemannResearch.RH.ThresholdHilbertL1
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Hilbert cost of imposing mean one after fitting a finite Pareto head

The projection of the tail indicator onto the full legal zero-head subspace
measures its capacity for correcting the mean. A delayed copy of the screened
unit bounds that capacity from below. Orthogonality to the *projected* tail
indicator bounds the exact additional cost of correcting the remaining mean.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Once all first K physical coordinates vanish, only the remaining
Pareto probability mass enters the L¹ versus L² comparison. -/
theorem hilbertL1Norm_head_zero_sq_le {K : ℕ} {f : ThresholdHilbert}
    (h : FiniteHeadRepair.headMap K f = 0) :
    (hilbertL1Norm f)^2 ≤ ‖f‖^2 / ((K : ℝ)+1) := by
  have hsum : (∑ k ∈ Finset.range (K+1), positiveWeight k * |hilbertSequence f k|) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    cases k with
    | zero => simp [hilbertSequence_zero]
    | succ j =>
      have hj := Finset.mem_range.mp hk
      have hval := congrFun h (⟨j, by omega⟩ : Fin K)
      rw [FiniteHeadRepair.headMap_apply] at hval
      simp only [show hilbertSequence f (j+1) = 0 from hval, abs_zero, mul_zero]
  have htail : hilbertL1Norm f = ∑' j : ℕ,
      positiveWeight (j+K+1) * |hilbertSequence f (j+K+1)| := by
    simpa only [hilbertL1Norm, hsum, zero_add, Nat.add_assoc] using
      ((hilbertL1Norm_summable f).sum_add_tsum_nat_add (K+1)).symm
  rw [htail]
  apply (pareto_absolute_tail_sq_le f K).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [hilbertTailShift_norm_sq]
  exact sub_le_self _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)

namespace PrimePowerSchur
open CoefficientStabilization FiniteHeadRepair
open RiemannResearch.Analysis.SingleObservationProjection

/-- Legal adjustments preserving the first K physical sites. -/
def legalHeadKernel (K : ℕ) : Submodule ℝ ThresholdHilbert :=
  closedSpace ⊓ (headMap K).ker

instance legalHeadKernel_complete (K : ℕ) : CompleteSpace (legalHeadKernel K) := by
  have : IsClosed (legalHeadKernel K : Set ThresholdHilbert) :=
    (Submodule.isClosed_topologicalClosure _).inter (headMap K).isClosed_ker
  exact this.completeSpace_coe

/-- The squared norm of the restricted tail-mean observation. -/
def legalTailMeanCapacity (K : ℕ) : ℝ :=
  ‖(legalHeadKernel K).starProjection (paretoTail K)‖ ^ 2

private theorem tail_eq_mean_of_head_zero {K : ℕ} {f : ThresholdHilbert}
    (hf : headMap K f = 0) : inner ℝ (paretoTail K) f = inner ℝ hilbertOne f := by
  rw [← real_inner_comm (paretoTail K) f, paretoTail_inner, ← real_inner_comm hilbertOne f]
  have he : paretoHeadMean K f = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := congrFun hf (⟨j, Finset.mem_range.mp hj⟩ : Fin K)
    rw [headMap_apply] at h
    rw [hilbertGibbsPhysical_eq, show hilbertSequence f (j+1) = 0 from h, mul_zero]
  rw [he, sub_zero]

/-- The lower estimate uses a delayed legal vector of mean one. The upper
estimate is the full ambient tail mass. Both hold for every cutoff. -/
theorem legalTailMeanCapacity_bounds (K : ℕ) :
    1 ≤ legalTailMeanCapacity K * (((K : ℝ)+1) * ‖normalizedScreenedTwo‖^2) ∧
      legalTailMeanCapacity K ≤ 1 / ((K : ℝ)+1) := by
  let u := normalizedScreenedTwo
  let d := hilbertDilation (K+1) (Nat.succ_pos _) u
  have hdK : headMap K d = 0 := by
    ext j
    rw [headMap_apply, show d = hilbertDilation (K+1) (Nat.succ_pos _) u from rfl,
      hilbertDilation_sequence]
    simp only [dilation, Nat.div_eq_of_lt (by omega : (j : ℕ)+1 < K+1),
      hilbertSequence_zero, mul_zero, Pi.zero_apply]
  have hd : d ∈ legalHeadKernel K := ⟨closedSpace_dilation
    (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure)
    (K+1) (Nat.succ_pos _), hdK⟩
  have hm : inner ℝ (paretoTail K) d = 1 := by
    rw [tail_eq_mean_of_head_zero hdK, real_inner_comm]
    change inner ℝ (hilbertDilation (K+1) (Nat.succ_pos _) u) hilbertOne = 1
    rw [hilbert_inner_one, hilbertDilation_mean, ← hilbert_inner_one]
    exact normalizedScreenedTwo_mean
  have hprod := abs_real_inner_le_norm ((legalHeadKernel K).starProjection (paretoTail K)) d
  rw [← projection_pairing (legalHeadKernel K) (paretoTail K) d hd, hm, abs_one] at hprod
  have hs := pow_le_pow_left₀ zero_le_one hprod 2
  rw [one_pow, mul_pow, show ‖d‖^2 = ((K : ℝ)+1)*‖u‖^2 by
    simpa only [d, Nat.cast_add, Nat.cast_one] using hilbertDilation_norm_sq (K+1) (Nat.succ_pos _) u] at hs
  refine ⟨hs, ?_⟩
  have h := projection_defect_energy (legalHeadKernel K) (paretoTail K)
  rw [paretoTail_norm_sq] at h
  change ‖(legalHeadKernel K).starProjection (paretoTail K)‖^2 ≤ _
  linarith only [h, sq_nonneg ‖paretoTail K - (legalHeadKernel K).starProjection (paretoTail K)‖]

theorem legalTailMeanCapacity_pos (K : ℕ) : 0 < legalTailMeanCapacity K := by
  have h := (legalTailMeanCapacity_bounds K).1
  have hq : 0 ≤ legalTailMeanCapacity K := sq_nonneg _
  by_contra! he
  rw [le_antisymm he hq, zero_mul] at h
  norm_num at h

/-- The screened line's global energy gives a uniform quantitative
lower endpoint for every normalized tail capacity. -/
theorem legalTailMeanCapacity_normalized_bounds (K : ℕ) :
    1-limitEnergy ≤ ((K : ℝ)+1)*legalTailMeanCapacity K ∧
      ((K : ℝ)+1)*legalTailMeanCapacity K ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := legalTailMeanCapacity_bounds K
  rw [normalizedScreenedTwo_norm_sq] at hlo
  have he : 1 ≤ (((K : ℝ)+1)*legalTailMeanCapacity K)/(1-limitEnergy) := by
    convert hlo using 1 <;> ring
  constructor
  · simpa only [one_mul] using (le_div_iff₀ one_sub_limitEnergy_pos).mp he
  · have hh := (le_div_iff₀ (by positivity : 0 < (K : ℝ)+1)).mp hhi
    simpa only [mul_comm] using hh

/-- The optimal full-energy repair of the tail mean using legal directions
which vanish through K. -/
def legalTailMeanRepair (K : ℕ) (r : ThresholdHilbert) : ThresholdHilbert :=
  affineObservationOptimizer (legalHeadKernel K) (paretoTail K) r (inner ℝ (paretoTail K) r)

/-- Orthogonal completion for the actual repaired residual. -/
theorem legalTailMeanRepair_energy (K : ℕ) (r : ThresholdHilbert) :
    let e := r - (legalHeadKernel K).starProjection r
    ‖r - legalTailMeanRepair K r‖^2 =
      ‖e‖^2 + (inner ℝ (paretoTail K) e)^2 / legalTailMeanCapacity K := by
  simpa only [legalTailMeanRepair, legalTailMeanCapacity, inner_sub_right] using
    affineObservationOptimizer_energy (legalHeadKernel K) (paretoTail K) r
      (inner ℝ (paretoTail K) r) (legalTailMeanCapacity_pos K).ne'

/-- The repair attains the least complete error among legal perturbations
preserving a zero head and matching the actual mean of the residual. -/
theorem legalTailMeanRepair_isLeast {K : ℕ} {r : ThresholdHilbert} (hr : headMap K r = 0) :
    IsLeast {b : ℝ | ∃ x ∈ legalHeadKernel K,
      inner ℝ hilbertOne x = inner ℝ hilbertOne r ∧ ‖r-x‖^2 = b}
      (‖r-legalTailMeanRepair K r‖^2) := by
  let S := legalHeadKernel K
  let t := paretoTail K
  have he (x : ThresholdHilbert) (hx : x ∈ S) :
      inner ℝ hilbertOne x = inner ℝ hilbertOne r ↔ inner ℝ t x = inner ℝ t r := by
    rw [tail_eq_mean_of_head_zero (show headMap K x = 0 from hx.2), tail_eq_mean_of_head_zero hr]
  have hset : {b : ℝ | ∃ x ∈ S, inner ℝ hilbertOne x = inner ℝ hilbertOne r ∧ ‖r-x‖^2 = b} =
      {b : ℝ | ∃ x ∈ S, inner ℝ t x = inner ℝ t r ∧ ‖r-x‖^2 = b} := by
    ext b
    constructor
    · rintro ⟨x,hx,hm,hn⟩
      exact ⟨x,hx,(he x hx).mp hm,hn⟩
    · rintro ⟨x,hx,hm,hn⟩
      exact ⟨x,hx,(he x hx).mpr hm,hn⟩
  rw [hset, legalTailMeanRepair_energy, inner_sub_right]
  exact affine_observation_error_isLeast S t r (inner ℝ t r) (legalTailMeanCapacity_pos K).ne'

/-- Correcting the mean inflates even the *optimized* uncentered error by
at most the squared norm of the minimum-norm screened section. -/
theorem legalTailMeanRepair_energy_le (K : ℕ) (r : ThresholdHilbert) :
    ‖r - legalTailMeanRepair K r‖^2 ≤
      ‖normalizedScreenedTwo‖^2 * ‖r - (legalHeadKernel K).starProjection r‖^2 := by
  let S := legalHeadKernel K
  let t := paretoTail K
  let q := legalTailMeanCapacity K
  let e := r - S.starProjection r
  have hq : 0 < q := legalTailMeanCapacity_pos K
  have hm : inner ℝ t e = inner ℝ (t - S.starProjection t) e := by
    have ho : inner ℝ (S.starProjection t) e = 0 :=
      (S.mem_orthogonal e).mp (Submodule.sub_starProjection_mem_orthogonal r)
        _ (S.starProjection_apply_mem t)
    rw [inner_sub_left, ho, sub_zero]
  have hc := abs_real_inner_le_norm (t-S.starProjection t) e
  rw [← hm] at hc
  have hsq := pow_le_pow_left₀ (abs_nonneg (inner ℝ t e)) hc 2
  rw [sq_abs, mul_pow, projection_defect_energy S t, show ‖t‖^2 = 1 / ((K : ℝ)+1)
    from paretoTail_norm_sq K] at hsq
  change (inner ℝ t e)^2 ≤ (1/((K : ℝ)+1)-q)*‖e‖^2 at hsq
  have hcap : 1 / ((K : ℝ)+1) ≤ q * ‖normalizedScreenedTwo‖^2 := by
    apply (div_le_iff₀ (by positivity : 0 < (K : ℝ)+1)).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using (legalTailMeanCapacity_bounds K).1
  have hb := mul_le_mul_of_nonneg_right hcap (sq_nonneg ‖e‖)
  rw [legalTailMeanRepair_energy]
  change ‖e‖^2 + (inner ℝ t e)^2 / q ≤ ‖normalizedScreenedTwo‖^2 * ‖e‖^2
  calc
    _ = (‖e‖^2 * q + (inner ℝ t e)^2) / q := by
      rw [add_div, mul_div_cancel_right₀ _ hq.ne']
    _ ≤ _ := (div_le_iff₀ hq).mpr (by nlinarith only [hsq, hb])

/-- The checked conductor-241 covariance certificate limits the extra squared
cost of the mean correction to nine parts per thousand of the unrestricted
optimum, at every exact head. -/
theorem legalTailMeanRepair_energy_le_covariance241 (K : ℕ) (r : ThresholdHilbert) :
    ‖r - legalTailMeanRepair K r‖^2 ≤ (1009 : ℝ)/1000 *
      ‖r - (legalHeadKernel K).starProjection r‖^2 := by
  have h := RiemannResearch.RH.GroupedResidueMass.Conductor241.screenedTwo_squared_distance_le_covariance
  rw [norm_sub_sq_real, ← real_inner_comm hilbertOne normalizedScreenedTwo,
    normalizedScreenedTwo_mean, hilbertOne_norm_sq] at h
  exact (legalTailMeanRepair_energy_le K r).trans
    (mul_le_mul_of_nonneg_right (by linarith only [h]) (sq_nonneg _))

/-- A finite mixed fit of any centered legal mean-one target. The same
screened factor applies to every target and every legal constant-head fit. -/
theorem finite_mixed_centered_head_screened_bound (K : ℕ) (z f : ThresholdHilbert)
    (hz : z ∈ closedSpace) (hz1 : inner ℝ z hilbertOne = 1) (hf : f ∈ closedSpace)
    (hhead : headMap K f = headMap K hilbertOne) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∃ v ∈ mixedSpace (Finset.Icc 2 M),
      headMap K v = headMap K (z-hilbertOne) ∧
      ‖(z-hilbertOne)-v‖ < ‖normalizedScreenedTwo‖ * ‖hilbertOne-f‖ + ε := by
  let S := legalHeadKernel K
  let r := hilbertOne-f
  let x := legalTailMeanRepair K r
  have hx : x ∈ legalHeadKernel K :=
    affineObservationOptimizer_mem S (paretoTail K) r _
  have hr : headMap K r = 0 := by
    change headMap K (hilbertOne-f) = 0
    rw [map_sub, hhead, sub_self]
  have hxK : headMap K x = 0 := hx.2
  have hxmean : inner ℝ hilbertOne x = inner ℝ hilbertOne r := by
    rw [← tail_eq_mean_of_head_zero hxK, ← tail_eq_mean_of_head_zero hr]
    exact affineObservationOptimizer_observation S (paretoTail K) r _ (legalTailMeanCapacity_pos K).ne'
  let w := z-(f+x)
  have hw : w ∈ mixedClosure := by
    apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
    refine ⟨closedSpace.sub_mem hz (closedSpace.add_mem hf hx.1), ?_⟩
    change inner ℝ (z-(f+x)) hilbertOne = 0
    rw [inner_sub_left, hz1, ← real_inner_comm (f+x) hilbertOne, inner_add_right, hxmean,
      show r = hilbertOne-f from rfl, inner_sub_right, real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
    ring
  have hwhead : headMap K w = headMap K (z-hilbertOne) := by
    simp only [w, map_sub, map_add, hxK, add_zero, hhead]
  have he : ‖r-S.starProjection r‖^2 ≤ ‖r‖^2 := by
    rw [projection_defect_energy]
    exact sub_le_self _ (sq_nonneg _)
  have hbound : ‖r-x‖ ≤ ‖normalizedScreenedTwo‖ * ‖r‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow]
    exact (legalTailMeanRepair_energy_le K r).trans
      (mul_le_mul_of_nonneg_left he (sq_nonneg _))
  obtain ⟨M, v, hv, hcoord, hd⟩ := finite_mixed_approximate_fixed_head K w hw ε hε
  refine ⟨M, v, hv, ?_, ?_⟩
  · rw [← hwhead]
    ext i
    rw [headMap_apply, headMap_apply]
    exact hcoord _ (Nat.succ_pos _) (by omega)
  · have hdiff : (z-hilbertOne)-w = -(r-x) := by dsimp [w, r]; abel
    have htri := norm_sub_le_norm_sub_add_norm_sub (z-hilbertOne) w v
    rw [hdiff, norm_neg, norm_sub_rev w v] at htri
    exact htri.trans_lt (add_lt_add_of_le_of_lt hbound hd)

/-- Stretched cancellation bounds both complete Hilbert error and the
complete L¹ error of the same finite mixed fit, uniformly over legal
mean-one targets. -/
theorem finite_mixed_centered_heads_screened_stretched :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ K : ℕ in atTop, ∀ z : ThresholdHilbert,
      z ∈ closedSpace → inner ℝ z hilbertOne = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, ∃ v ∈ mixedSpace (Finset.Icc 2 M),
        headMap K v = headMap K (z-hilbertOne) ∧
        (hilbertL1Norm ((z-hilbertOne)-v))^2 ≤ ‖(z-hilbertOne)-v‖^2 / ((K : ℝ)+1) ∧
        ‖(z-hilbertOne)-v‖ < ‖normalizedScreenedTwo‖ *
          Real.sqrt (8 + C * (K : ℝ) * Real.exp
            (-a * RiemannResearch.Analysis.logProductPower (1 / 11) (6 + Real.log (K : ℝ)))) + ε := by
  obtain ⟨a, ha, C, hC, hbound⟩ := canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨a, ha, C, hC, ?_⟩
  filter_upwards [hbound] with K hK
  intro z hz hm ε hε
  have hhead : headMap K (canonicalMobiusHilbert K) = headMap K hilbertOne := by
    ext j
    rw [headMap_apply, headMap_apply, canonicalMobiusHilbert_exact K _ (Nat.succ_pos _) (by omega),
      hilbertOne_sequence]
    simp [zeroAnchor]
  obtain ⟨M, v, hv, hfit, hnear⟩ := finite_mixed_centered_head_screened_bound K z _
    hz hm (canonicalMobiusHilbert_mem_closedSpace K) hhead ε hε
  have h0 : headMap K ((z-hilbertOne)-v) = 0 := by rw [map_sub, hfit, sub_self]
  exact ⟨M, v, hv, hfit, hilbertL1Norm_head_zero_sq_le h0,
    hnear.trans_le (add_le_add (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hK)
      (norm_nonneg _)) le_rfl)⟩

end PrimePowerSchur
end RiemannResearch.RH.Pareto
