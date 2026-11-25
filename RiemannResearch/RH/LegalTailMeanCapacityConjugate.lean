import RiemannResearch.RH.LegalTailMeanCapacityMellin
import RiemannResearch.RH.ParetoMellinZeroPairObstruction

/-! The conjugate-pair Mellin obstruction on every Pareto tail. -/

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.RH.Pareto

/-- Multiplying the two Mellin coefficients by the scale powers transports
the entire test, including its cross-term, to the rescaled half-line. -/
private theorem twoKernel_scaled_energy (m : ℝ) (hm : 0 < m) (s t c d : ℂ) :
    (∫ x in Ioi m, ‖mellinTwoKernel s t ((m : ℂ)^s*c) ((m : ℂ)^t*d) x‖^2) =
      m * ∫ x in Ioi (1 : ℝ), ‖mellinTwoKernel s t c d x‖^2 := by
  let T := mellinTwoKernel s t ((m : ℂ)^s*c) ((m : ℂ)^t*d)
  let U := mellinTwoKernel s t c d
  have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hscale {x : ℝ} (hx : 0 < x) (z a : ℂ) :
      ((m : ℂ)^z*a) * paretoMellinKernel z (m*x) = a * paretoMellinKernel z x := by
    have hpow := Complex.mul_cpow_ofReal_nonneg hm.le hx.le (-z)
    have hcancel : (m : ℂ)^z*(m : ℂ)^(-z) = 1 := by
      rw [← Complex.cpow_add _ _ hmC, add_neg_cancel, Complex.cpow_zero]
    unfold paretoMellinKernel
    rw [Complex.ofReal_mul, hpow]
    linear_combination (a * (x : ℂ)^(-z)) * hcancel
  have hpoint (x : ℝ) :
      (Ioi m).indicator (fun y => ‖T y‖^2) (m*x) =
        (Ioi (1 : ℝ)).indicator (fun y => ‖U y‖^2) x := by
    have hiff : m < m*x ↔ 1 < x := by
      simpa only [mul_one] using (mul_lt_mul_iff_right₀ hm : m*1 < m*x ↔ 1 < x)
    by_cases hx : 1 < x
    · rw [Set.indicator_of_mem (show m*x ∈ Ioi m from hiff.mpr hx),
        Set.indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx)]
      have hTU : T (m*x) = U x := by
        change _ * paretoMellinKernel s (m*x) + _ * paretoMellinKernel t (m*x) = _
        rw [hscale (lt_trans zero_lt_one hx), hscale (lt_trans zero_lt_one hx)]
        rfl
      rw [hTU]
    · rw [Set.indicator_of_notMem (show m*x ∉ Ioi m from fun h => hx (hiff.mp h)),
        Set.indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from hx)]
  have h := Measure.integral_comp_mul_left ((Ioi m).indicator (fun y => ‖T y‖^2)) m
  simp_rw [hpoint] at h
  rw [integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi,
    abs_of_pos (inv_pos.mpr hm), smul_eq_mul] at h
  change (∫ x in Ioi m, ‖T x‖ ^ 2) = m * ∫ x in Ioi (1 : ℝ), ‖U x‖ ^ 2
  rw [h, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]

/-- The sharp conjugate-pair charge for every physical zero-head vector
whose Mellin signature is that of the tail indicator. -/
private theorem scaled_pair_charge_le (e : ThresholdHilbert) (n : ℕ) (hn : 0 < n)
    (hhead : ∀ k, 0 < k → k < n → hilbertSequence e k = 0)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0)
    (hval : paretoMellin e s = (n : ℂ)^(-s)/s)
    (hconj : paretoMellin e (starRingEnd ℂ s) =
      (n : ℂ)^(-(starRingEnd ℂ s))/(starRingEnd ℂ s)) :
    mellinZeroPairCharge s ≤ (n : ℝ) * ‖e‖^2 := by
  let t := starRingEnd ℂ s
  let c := mellinZeroPairCoefficient s
  let d := starRingEnd ℂ c
  let A := (n : ℂ)^s * c
  let B := (n : ℂ)^t * d
  let T := mellinTwoKernel s t A B
  have ht : (1 / 2 : ℝ) < t.re := by simpa [t] using hs
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hscaled (z a : ℂ) :
      ((n : ℂ)^z*a) * ((n : ℂ)^(-z)/z) = a/z := by
    have hcancel : (n : ℂ)^z*(n : ℂ)^(-z) = 1 := by
      rw [← Complex.cpow_add _ _ hnC, add_neg_cancel, Complex.cpow_zero]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (a*z⁻¹) * hcancel
  have hsig : A * paretoMellin e s + B * paretoMellin e t =
      (mellinZeroPairCharge s : ℂ) := by
    change ((n : ℂ)^s*c) * paretoMellin e s +
      ((n : ℂ)^t*d) * paretoMellin e t = _
    rw [hval, hconj, hscaled, hscaled]
    exact mellinZeroPairCoefficient_target s hs hi
  have hT : MemLp T 2 (volume.restrict (Ioi (1 : ℝ))) :=
    mellinTwoKernel_memLp s t A B hs ht
  have hprod : IntegrableOn (fun x => mellinWeightedStep e x * T x) (Ioi (1 : ℝ)) :=
    (mellinWeightedStep_memLp e).integrable_mul hT
  have hzero : (∫ x in (1 : ℝ)..(n : ℝ), mellinWeightedStep e x * T x) = 0 := by
    rw [intervalIntegral.integral_of_le hb, ← integral_Ico_eq_integral_Ioc]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx.1
    have hlo : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx.1)
    have hhi : ⌊x⌋₊ < n := (Nat.floor_lt hx0).2 (by exact_mod_cast hx.2)
    simp [mellinWeightedStep, hhead _ (by omega) hhi]
  have hsub := Ioi_subset_Ioi hb
  have hcut := intervalIntegral.integral_interval_add_Ioi hprod (hprod.mono_set hsub)
  change (∫ x in (1 : ℝ)..(n : ℝ), mellinWeightedStep e x * T x) +
    (∫ x in Ioi (n : ℝ), mellinWeightedStep e x * T x) =
      ∫ x in Ioi (1 : ℝ), mellinWeightedStep e x * T x at hcut
  rw [hzero, zero_add, show (∫ x in Ioi (1 : ℝ), mellinWeightedStep e x * T x) =
    A * paretoMellin e s + B * paretoMellin e t from mellinTwoKernel_pairing e s t A B hs ht,
    hsig] at hcut
  have hmass : (∫ x in Ioi (n : ℝ), ‖T x‖^2) = (n : ℝ) * mellinZeroPairCharge s := by
    have h := twoKernel_scaled_energy (n : ℝ) hnR s t c d
    simp only [Complex.ofReal_natCast] at h
    change (∫ x in Ioi (n : ℝ), ‖mellinTwoKernel s t ((n : ℂ)^s*c) ((n : ℂ)^t*d) x‖^2) = _
    rw [h, show (∫ x in Ioi (1 : ℝ), ‖mellinTwoKernel s t c d x‖^2) =
      mellinZeroPairCharge s from mellinZeroPairCoefficient_energy s hs hi]
  have hμ : volume.restrict (Ioi (n : ℝ)) ≤ volume.restrict (Ioi (1 : ℝ)) :=
    Measure.restrict_mono hsub le_rfl
  have hCS := RemoteLaplaceTail.norm_integral_mul_sq_le
    (MemLp.mono_measure hμ (mellinWeightedStep_memLp e)) (MemLp.mono_measure hμ hT)
  rw [hcut, Complex.norm_real, Real.norm_eq_abs, sq_abs, hmass] at hCS
  have hE : (∫ x in Ioi (n : ℝ), ‖mellinWeightedStep e x‖^2) ≤ ‖e‖^2 := by
    rw [← mellinWeightedStep_energy]
    exact integral_mono_measure hμ (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (mellinWeightedStep_memLp e).norm.integrable_sq
  have hq := mellinZeroPairCharge_pos s hs hi
  have hbound := hCS.trans (mul_le_mul_of_nonneg_right hE (mul_nonneg hnR.le hq.le))
  apply (le_of_mul_le_mul_right _ hq)
  simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hbound

namespace PrimePowerSchur
open CoefficientStabilization FiniteHeadRepair RiemannResearch.Analysis.SingleObservationProjection

/-- A nonreal right zero imposes the conjugate-pair capacity gap at every stage. -/
theorem legalTailMeanCapacity_conjugate_zero_gap (K : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hi : s.im ≠ 0) (hz : riemannZeta s = 0) :
    ((K : ℝ)+1) * legalTailMeanCapacity K ≤ 1 - mellinZeroPairCharge s := by
  let S := legalHeadKernel K
  let t := paretoTail K
  let v := S.starProjection t
  have hmem : v ∈ legalHeadKernel K := S.starProjection_apply_mem t
  have hs1 : s ≠ 1 := by intro h; apply hi; simp [h]
  have hv := paretoMellin_zero_on_legalClosure_of_zeta {j : ℕ | 0 < j}
    (fun _ hj => hj) s hs hs1 hz (closedSpace_le_legalClosure hmem.1)
  have hsig (z : ℂ) (hz' : (1 / 2 : ℝ) < z.re) (hvz : paretoMellin v z = 0) :
      paretoMellin (t-v) z = ((K+1 : ℕ) : ℂ)^(-z)/z := by
    change paretoMellinContinuous z hz' (t-v) = _
    rw [map_sub]
    change paretoMellin (paretoTail K) z - paretoMellin v z = _
    rw [paretoTail_mellin K z hz', hvz, sub_zero]
  have hv' : paretoMellin v (starRingEnd ℂ s) = 0 := by rw [paretoMellin_conj, hv, map_zero]
  have hhead (j : ℕ) (hj : 0 < j) (hjK : j < K+1) : hilbertSequence (t-v) j = 0 := by
    cases j with
    | zero => omega
    | succ i =>
      have hi' : i < K := by omega
      have hh := congrFun (show headMap K v = 0 from hmem.2) (⟨i,hi'⟩ : Fin K)
      rw [headMap_apply] at hh
      rw [hilbertSequence_sub, Pi.sub_apply, show hilbertSequence v (i+1) = 0 from hh,
        sub_zero, ← hilbertGibbsPhysical_eq, show t = paretoTail K from rfl,
        paretoTail_physical, if_pos hi']
  have h := scaled_pair_charge_le (t-v) (K+1) (Nat.succ_pos _) hhead s hs hi
    (hsig s hs hv) (hsig _ (by simpa using hs) hv')
  rw [show ‖t-v‖^2 = ‖t‖^2 - ‖v‖^2 from projection_defect_energy S t,
    show ‖t‖^2 = 1/((K : ℝ)+1) from paretoTail_norm_sq K] at h
  change mellinZeroPairCharge s ≤ ((K+1 : ℕ) : ℝ) *
    (1/((K : ℝ)+1) - legalTailMeanCapacity K) at h
  rw [Nat.cast_add, Nat.cast_one, mul_sub, mul_one_div_cancel (by positivity : (K : ℝ)+1 ≠ 0)] at h
  linarith

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.legalTailMeanCapacity_conjugate_zero_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms legalTailMeanCapacity_conjugate_zero_gap

end PrimePowerSchur
end RiemannResearch.RH.Pareto
