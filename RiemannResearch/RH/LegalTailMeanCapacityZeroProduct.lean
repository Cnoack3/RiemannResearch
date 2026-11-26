import RiemannResearch.RH.LegalTailMeanCapacityConjugate
import RiemannResearch.RH.RamanujanMellinProduct

/-!
# Finite zero-product obstructions for legal tail capacity

The single-zero and conjugate-pair tail estimates extend to every finite
family of distinct right-half-plane zeros. The proof rescales the complete
Cauchy--Mellin optimizer, so all Gram cross-terms are retained.

This is a finite distinct-zero theorem. It does not identify the legal
closed span with Burnol's continuous Nyman space, and it does not encode
analytic multiplicity. The latter requires confluent derivative-jet
Mellin kernels rather than the nonsingular Cauchy matrix used here.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

variable {ι : Type*} [Fintype ι]

private theorem finiteMellinKernel_scaled_energy (m : ℝ) (hm : 0 < m)
    (s c : ι → ℂ) :
    (∫ x in Ioi m, ‖finiteMellinKernel s
      (fun i => starRingEnd ℂ ((m : ℂ) ^ (s i)) * c i) x‖ ^ 2) =
      m * ∫ x in Ioi (1 : ℝ), ‖finiteMellinKernel s c x‖ ^ 2 := by
  classical
  let T := finiteMellinKernel s
    (fun i => starRingEnd ℂ ((m : ℂ) ^ (s i)) * c i)
  let U := finiteMellinKernel s c
  have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
    change star (star z) = z
    exact star_star z
  have hscale {x : ℝ} (hx : 0 < x) (z a : ℂ) :
      ((m : ℂ) ^ z * a) * paretoMellinKernel z (m * x) =
        a * paretoMellinKernel z x := by
    have hpow := Complex.mul_cpow_ofReal_nonneg hm.le hx.le (-z)
    have hcancel : (m : ℂ) ^ z * (m : ℂ) ^ (-z) = 1 := by
      rw [← Complex.cpow_add _ _ hmC, add_neg_cancel, Complex.cpow_zero]
    unfold paretoMellinKernel
    rw [Complex.ofReal_mul, hpow]
    linear_combination (a * (x : ℂ) ^ (-z)) * hcancel
  have hpoint (x : ℝ) :
      (Ioi m).indicator (fun y => ‖T y‖ ^ 2) (m * x) =
        (Ioi (1 : ℝ)).indicator (fun y => ‖U y‖ ^ 2) x := by
    have hiff : m < m * x ↔ 1 < x := by
      simpa only [mul_one] using
        (mul_lt_mul_iff_right₀ hm : m * 1 < m * x ↔ 1 < x)
    by_cases hx : 1 < x
    · rw [Set.indicator_of_mem (show m * x ∈ Ioi m from hiff.mpr hx),
          Set.indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx)]
      have hTU : T (m * x) = U x := by
        dsimp only [T, U, finiteMellinKernel]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [map_mul, hconj]
        exact hscale (lt_trans zero_lt_one hx) (s i) (starRingEnd ℂ (c i))
      rw [hTU]
    · rw [Set.indicator_of_notMem
            (show m * x ∉ Ioi m from fun h => hx (hiff.mp h)),
          Set.indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from hx)]
  have h :=
    Measure.integral_comp_mul_left ((Ioi m).indicator (fun y => ‖T y‖ ^ 2)) m
  simp_rw [hpoint] at h
  rw [integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi,
      abs_of_pos (inv_pos.mpr hm), smul_eq_mul] at h
  change (∫ x in Ioi m, ‖T x‖ ^ 2) =
    m * ∫ x in Ioi (1 : ℝ), ‖U x‖ ^ 2
  rw [h, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]

private theorem scaled_finite_charge_le [DecidableEq ι]
    (e : ThresholdHilbert) (n : ℕ) (hn : 0 < n)
    (hhead : ∀ k, 0 < k → k < n → hilbertSequence e k = 0)
    (s : ι → ℂ) (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hinj : Function.Injective s)
    (hval : ∀ i, paretoMellin e (s i) = (n : ℂ) ^ (-(s i)) / s i) :
    mellinInverseCapacity s (fun i => 1 / s i) ≤ (n : ℝ) * ‖e‖ ^ 2 := by
  classical
  let b : ι → ℂ := fun i => 1 / s i
  let c := mellinInverseCoefficients s b
  let A : ι → ℂ := fun i => starRingEnd ℂ ((n : ℂ) ^ (s i)) * c i
  let T := finiteMellinKernel s A
  let q := mellinInverseCapacity s b
  let Z : ℂ := ∑ i, starRingEnd ℂ (c i) * b i
  have hdet : (mellinCauchyGram s).det ≠ 0 :=
    (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
    change star (star z) = z
    exact star_star z
  have hscaled (z a : ℂ) :
      ((n : ℂ) ^ z * a) * ((n : ℂ) ^ (-z) / z) = a / z := by
    have hcancel : (n : ℂ) ^ z * (n : ℂ) ^ (-z) = 1 := by
      rw [← Complex.cpow_add _ _ hnC, add_neg_cancel, Complex.cpow_zero]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (a * z⁻¹) * hcancel
  have hsig :
      (∑ i, starRingEnd ℂ (A i) * paretoMellin e (s i)) = Z := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [A, Z, b]
    simp only [map_mul, hconj, hval]
    simpa only [div_eq_mul_inv, one_mul] using
      hscaled (s i) (starRingEnd ℂ (c i))
  have hT : MemLp T 2 (volume.restrict (Ioi (1 : ℝ))) :=
    finiteMellinKernel_memLp s A hs
  have hprod :
      IntegrableOn (fun x => mellinWeightedStep e x * T x) (Ioi (1 : ℝ)) :=
    (mellinWeightedStep_memLp e).integrable_mul hT
  have hzero :
      (∫ x in (1 : ℝ)..(n : ℝ), mellinWeightedStep e x * T x) = 0 := by
    rw [intervalIntegral.integral_of_le hb, ← integral_Ico_eq_integral_Ioc]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx.1
    have hlo : 1 ≤ ⌊x⌋₊ :=
      (Nat.le_floor_iff hx0).2 (by simpa using hx.1)
    have hhi : ⌊x⌋₊ < n :=
      (Nat.floor_lt hx0).2 (by exact_mod_cast hx.2)
    simp [mellinWeightedStep, hhead _ (by omega) hhi]
  have hsub := Ioi_subset_Ioi hb
  have hcut :=
    intervalIntegral.integral_interval_add_Ioi hprod (hprod.mono_set hsub)
  change (∫ x in (1 : ℝ)..(n : ℝ), mellinWeightedStep e x * T x) +
      (∫ x in Ioi (n : ℝ), mellinWeightedStep e x * T x) =
        ∫ x in Ioi (1 : ℝ), mellinWeightedStep e x * T x at hcut
  rw [hzero, zero_add,
      show (∫ x in Ioi (1 : ℝ), mellinWeightedStep e x * T x) =
        ∑ i, starRingEnd ℂ (A i) * paretoMellin e (s i) from
          finiteMellinKernel_pairing e s A hs,
      hsig] at hcut
  have hmass :
      (∫ x in Ioi (n : ℝ), ‖T x‖ ^ 2) = (n : ℝ) * q := by
    have h := finiteMellinKernel_scaled_energy (n : ℝ) hnR s c
    simp only [Complex.ofReal_natCast] at h
    change (∫ x in Ioi (n : ℝ), ‖finiteMellinKernel s
      (fun i => starRingEnd ℂ ((n : ℂ) ^ (s i)) * c i) x‖ ^ 2) = _
    rw [h, ← mellinInverseCapacity_eq_kernel_energy s b hs hdet]
  have hμ :
      volume.restrict (Ioi (n : ℝ)) ≤ volume.restrict (Ioi (1 : ℝ)) :=
    Measure.restrict_mono hsub le_rfl
  have hCS := RemoteLaplaceTail.norm_integral_mul_sq_le
    (MemLp.mono_measure hμ (mellinWeightedStep_memLp e))
    (MemLp.mono_measure hμ hT)
  rw [hcut, hmass] at hCS
  have hE :
      (∫ x in Ioi (n : ℝ), ‖mellinWeightedStep e x‖ ^ 2) ≤ ‖e‖ ^ 2 := by
    rw [← mellinWeightedStep_energy]
    exact integral_mono_measure hμ
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (mellinWeightedStep_memLp e).norm.integrable_sq
  have hq : 0 ≤ q := mellinInverseCapacity_nonneg s b hs hdet
  have hbound :=
    hCS.trans (mul_le_mul_of_nonneg_right hE (mul_nonneg hnR.le hq))
  have hqZ : q = Z.re := by rfl
  have hqnorm : q ^ 2 ≤ ‖Z‖ ^ 2 := by
    rw [hqZ, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg Z.im]
  change q ≤ (n : ℝ) * ‖e‖ ^ 2
  by_cases hq0 : q = 0
  · rw [hq0]
    exact mul_nonneg hnR.le (sq_nonneg ‖e‖)
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    nlinarith [hqnorm, hbound]

namespace PrimePowerSchur
open CoefficientStabilization FiniteHeadRepair
  RiemannResearch.Analysis.SingleObservationProjection

/-- Every finite family of distinct actual right zeros imposes its full
finite Blaschke-product obstruction on every normalized legal tail stage. -/
theorem legalTailMeanCapacity_finite_zero_product_gap
    (K : ℕ) (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1)
    (hzero : ∀ i, riemannZeta (z i) = 0) :
    ((K : ℝ) + 1) * legalTailMeanCapacity K ≤ mellinZeroProduct z := by
  classical
  let S := legalHeadKernel K
  let t := paretoTail K
  let v := S.starProjection t
  have hmem : v ∈ legalHeadKernel K := S.starProjection_apply_mem t
  have hv (i : ι) : paretoMellin v (z i) = 0 :=
    paretoMellin_zero_on_legalClosure_of_zeta {j : ℕ | 0 < j}
      (fun _ hj => hj) (z i) (hzre i) (hz1 i) (hzero i)
      (closedSpace_le_legalClosure hmem.1)
  have hsig (i : ι) :
      paretoMellin (t - v) (z i) =
        ((K + 1 : ℕ) : ℂ) ^ (-(z i)) / z i := by
    change paretoMellinContinuous (z i) (hzre i) (t - v) = _
    rw [map_sub]
    change paretoMellin (paretoTail K) (z i) - paretoMellin v (z i) = _
    rw [paretoTail_mellin K (z i) (hzre i), hv i, sub_zero]
  have hhead (j : ℕ) (hj : 0 < j) (hjK : j < K + 1) :
      hilbertSequence (t - v) j = 0 := by
    cases j with
    | zero => omega
    | succ i =>
      have hi' : i < K := by omega
      have hh :=
        congrFun (show headMap K v = 0 from hmem.2) (⟨i, hi'⟩ : Fin K)
      rw [headMap_apply] at hh
      rw [hilbertSequence_sub, Pi.sub_apply,
        show hilbertSequence v (i + 1) = 0 from hh, sub_zero,
        ← hilbertGibbsPhysical_eq, show t = paretoTail K from rfl,
        paretoTail_physical, if_pos hi']
  have h := scaled_finite_charge_le (t - v) (K + 1) (Nat.succ_pos _)
    hhead z hzre hinj hsig
  rw [mellinInverseCapacity_zeroSource_product z hzre hinj,
      show ‖t - v‖ ^ 2 = ‖t‖ ^ 2 - ‖v‖ ^ 2 from
        projection_defect_energy S t,
      show ‖t‖ ^ 2 = 1 / ((K : ℝ) + 1) from paretoTail_norm_sq K] at h
  change 1 - mellinZeroProduct z ≤ ((K + 1 : ℕ) : ℝ) *
    (1 / ((K : ℝ) + 1) - legalTailMeanCapacity K) at h
  rw [Nat.cast_add, Nat.cast_one, mul_sub,
    mul_one_div_cancel (by positivity : (K : ℝ) + 1 ≠ 0)] at h
  linarith

/-- The full stage supremum obeys every finite distinct-zero product
obstruction.  No passage to an infinite product is used here. -/
theorem normalizedLegalTailMeanCapacity_iSup_le_finite_zero_product
    (z : ι → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re)
    (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1)
    (hzero : ∀ i, riemannZeta (z i) = 0) :
    (⨆ K : ℕ, ((K : ℝ) + 1) * legalTailMeanCapacity K) ≤
      mellinZeroProduct z := by
  exact ciSup_le fun K =>
    legalTailMeanCapacity_finite_zero_product_gap K z hzre hinj hz1 hzero

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.legalTailMeanCapacity_finite_zero_product_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms legalTailMeanCapacity_finite_zero_product_gap

end PrimePowerSchur
end RiemannResearch.RH.Pareto
