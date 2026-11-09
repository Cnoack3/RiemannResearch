import RiemannResearch.NumberTheory.DyadicAdditiveRigidity
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.MixedConductorCovariance
import RiemannResearch.RH.MixedConductorDilation
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ResidueConductorVariation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reduction to one fully screened packet

I. Kátai, On additive functions (1978), equations (1.1) and (1.2),
https://doi.org/10.5486/PMD.1978.25.3-4.10, states the classical rigidity result
for additive functions with vanishing mean absolute adjacent differences,
and attributes the short-interval version to E. Wirsing. The dyadic case
is proved in DyadicAdditiveRigidity. Applied to mixed annihilators, it makes
the full-screened legal space one-dimensional and gives a fixed-seed test.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

theorem residuePairing_eq_log
    {h : ThresholdHilbert} (hh : h ∈ mixedClosureᗮ) :
    ∃ c : ℝ, ∀ n : ℕ, 0 < n → residuePairing h n = c * Real.log (n : ℝ) := by
  apply RiemannResearch.NumberTheory.eq_log_of_coprime_additive_of_dyadic_variation
    (residuePairing h) _ (residuePairing_dyadic_variation_tendsto h)
  intro a b ha hb hc
  by_cases ha' : a = 1
  · subst a
    simp [residuePairing]
  by_cases hb' : b = 1
  · subst b
    simp [residuePairing]
  have ha1 : 1 < a := by omega
  have hb1 : 1 < b := by omega
  have hab : 1 < a * b := ha1.trans_le (Nat.le_mul_of_pos_right _ hb)
  simpa only [residuePairing, if_pos hab, if_pos ha1, if_pos hb1] using
    mixed_orthogonal_rawResidue_mul_of_coprime hh a b ha1 hb1 hc

private theorem packet_pairing_eq_of_residue_log {h : ThresholdHilbert} {c : ℝ}
    (hlog : ∀ n : ℕ, 0 < n → residuePairing h n = c * Real.log (n : ℝ))
    (q : ℕ) (hq : 1 < q) :
    inner ℝ (ramanujanPacketHilbert q) h = c * ArithmeticFunction.vonMangoldt q := by
  have hsrc (n : ℕ) (_hn : 0 < n) :
      (∑ d ∈ n.divisors, c * ArithmeticFunction.vonMangoldt d) = c * Real.log (n : ℝ) := by
    rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
  have hμ := (mobius_inversion (fun n => c * ArithmeticFunction.vonMangoldt n)
    (fun n => c * Real.log (n : ℝ))).mp hsrc q (by omega)
  rw [← hμ, ramanujanPacketHilbert_eq_divisor_sum q hq, sum_inner]
  calc
    _ = ∑ d ∈ q.divisors.filter (fun d => 1 < d),
        (ArithmeticFunction.moebius (q / d) : ℝ) * (c * Real.log (d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' := (Finset.mem_filter.mp hd).2
      have he := hlog d (by omega)
      rw [residuePairing, if_pos hd'] at he
      rw [real_inner_smul_left, he]
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnd
      have hpos := Nat.pos_of_mem_divisors hd
      have hn : ¬ 1 < d := fun h => hnd (Finset.mem_filter.mpr ⟨hd, h⟩)
      have hd1 : d = 1 := by omega
      simp [hd1]

def normalizedScreenedTwo : ThresholdHilbert :=
  (Real.log 2)⁻¹ • limitScreenedPacket 2

theorem normalizedScreenedTwo_mean : inner ℝ normalizedScreenedTwo hilbertOne = 1 := by
  rw [normalizedScreenedTwo, real_inner_smul_left, limitScreenedPacket_inner_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  exact inv_mul_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

theorem normalizedScreenedTwo_mem_screenedPrimeClosure :
    normalizedScreenedTwo ∈ screenedPrimeClosure :=
  screenedPrimeClosure.smul_mem _ (Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨⟨2, by norm_num, Nat.prime_two.isPrimePow⟩, rfl⟩))

theorem fullScreening_packet_eq_mangoldt_smul
    (q : ℕ) (hq : 1 < q) :
    fullScreening (ramanujanPacketHilbert q) =
      ArithmeticFunction.vonMangoldt q • normalizedScreenedTwo := by
  let v := fullScreening (ramanujanPacketHilbert q) -
    ArithmeticFunction.vonMangoldt q • normalizedScreenedTwo
  have hv : v ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.sub_mem (fullScreening_mem_orthogonal _)
      (mixedClosure.orthogonal.smul_mem _ (mixedClosure.orthogonal.smul_mem _
        (fullScreening_mem_orthogonal (ramanujanPacketHilbert 2))))
  obtain ⟨c, hc⟩ := residuePairing_eq_log hv
  have he : inner ℝ v v = 0 := by
    change inner ℝ (fullScreening (ramanujanPacketHilbert q) -
      ArithmeticFunction.vonMangoldt q • normalizedScreenedTwo) v = 0
    rw [inner_sub_left, real_inner_smul_left, normalizedScreenedTwo, real_inner_smul_left,
      ← fullScreening_packet, fullScreening_inner_right_of_orthogonal _ _ hv,
      fullScreening_inner_right_of_orthogonal _ _ hv, packet_pairing_eq_of_residue_log hc q hq,
      packet_pairing_eq_of_residue_log hc 2 (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp he)

theorem screenedPrimeClosure_eq_span_two :
    screenedPrimeClosure = Submodule.span ℝ {normalizedScreenedTwo} := by
  apply le_antisymm
  · unfold screenedPrimeClosure
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      change limitScreenedPacket q.val ∈ _
      rw [← fullScreening_packet,
        fullScreening_packet_eq_mangoldt_smul q.val q.property.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · exact Submodule.closed_of_finiteDimensional _
  · apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact normalizedScreenedTwo_mem_screenedPrimeClosure

theorem one_mem_closedSpace_iff_normalizedScreenedTwo
    :
    hilbertOne ∈ closedSpace ↔ normalizedScreenedTwo = hilbertOne := by
  rw [← one_mem_screenedPrimeClosure_iff, screenedPrimeClosure_eq_span_two]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have he := congrArg (fun x : ThresholdHilbert => inner ℝ x hilbertOne) ha
    have ha' : a = 1 := by
      simpa only [real_inner_smul_left, normalizedScreenedTwo_mean, mul_one,
        real_inner_self_eq_norm_sq, hilbertOne_norm_sq] using he
    simpa [ha'] using ha
  · intro h
    rw [h]
    exact Submodule.subset_span (Set.mem_singleton _)

theorem riemannHypothesis_of_normalizedScreenedTwo (h : normalizedScreenedTwo = hilbertOne) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_one_mem_screenedPrimeClosure
  rw [← h]
  exact normalizedScreenedTwo_mem_screenedPrimeClosure

/-- On the legal closure, full screening keeps just the mean, in the
normalized direction of the screened conductor 2. -/
theorem fullScreening_eq_mean_smul {x : ThresholdHilbert} (hx : x ∈ closedSpace) :
    fullScreening x = inner ℝ x hilbertOne • normalizedScreenedTwo := by
  have hm := fullScreening_closedSpace_mem hx
  rw [screenedPrimeClosure_eq_span_two] at hm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have hp := congrArg (fun z : ThresholdHilbert => inner ℝ z hilbertOne) ha
  have he : a = inner ℝ x hilbertOne := by
    simpa only [real_inner_smul_left, normalizedScreenedTwo_mean, mul_one,
      fullScreening_inner_right_of_orthogonal x hilbertOne one_mem_mixedClosure_orthogonal]
      using hp
  rw [← ha, he]

theorem mem_mixedClosure_iff_mem_closedSpace_and_mean_zero (x : ThresholdHilbert) :
    x ∈ mixedClosure ↔ x ∈ closedSpace ∧ inner ℝ x hilbertOne = 0 := by
  constructor
  · intro hx
    exact ⟨mixedClosure_le_closedSpace hx,
      (mixedClosure.mem_orthogonal hilbertOne).mp one_mem_mixedClosure_orthogonal x hx⟩
  · rintro ⟨hx, hm⟩
    have hz := fullScreening_eq_mean_smul hx
    rw [hm, zero_smul] at hz
    change x - mixedClosure.starProjection x = 0 at hz
    rw [sub_eq_zero.mp hz]
    exact mixedClosure.starProjection_apply_mem _

/-- The limiting fixed-seed error is the canonical legal projection error
rescaled by the squared norm of its projection. -/
theorem normalizedScreenedTwo_error_sq_eq_limitEnergy :
    ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 = limitEnergy / (1 - limitEnergy) := by
  have hP : limitProjection ∈ closedSpace := closedSpace.starProjection_apply_mem _
  have hU := screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
  have hPmean : inner ℝ limitProjection hilbertOne = 1 - limitEnergy := by
    have h := limitResidual_inner_one
    rw [limitResidual, inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq] at h
    linarith
  have hPorth : limitProjection ∈ mixedClosureᗮ := by
    apply (mixedClosure.mem_orthogonal _).mpr
    intro x hx
    have h₁ := (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal x
      (mixedClosure_le_closedSpace hx)
    have h₂ := (mixedClosure.mem_orthogonal _).mp one_mem_mixedClosure_orthogonal x hx
    rw [limitResidual, inner_sub_right, h₂, zero_sub, neg_eq_zero] at h₁
    exact h₁
  have hPproj : mixedClosure.starProjection limitProjection = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff mixedClosure).mpr hPorth
  have hPu : limitProjection = (1 - limitEnergy) • normalizedScreenedTwo := by
    have h := fullScreening_eq_mean_smul hP
    change limitProjection - mixedClosure.starProjection limitProjection = _ at h
    rwa [hPproj, sub_zero, hPmean] at h
  have hprod : (1 - limitEnergy) * ‖normalizedScreenedTwo‖ ^ 2 = 1 := by
    have h := (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hU
    rw [limitResidual, inner_sub_right, normalizedScreenedTwo_mean, hPu, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at h
    linarith
  have hn : 1 - limitEnergy ≠ 0 := by intro he; simp [he] at hprod
  apply (eq_div_iff hn).mpr
  rw [norm_sub_sq_real, normalizedScreenedTwo_mean, hilbertOne_norm_sq]
  nlinarith

/-- The prime input is fixed at conductor 2 while the mixed cutoff grows. -/
def fixedTwoTrial (M : ℕ) : ThresholdHilbert :=
  (Real.log 2)⁻¹ • screenedPacket (Finset.Icc 2 M) 2

theorem fixedTwoTrial_tendsto :
    Tendsto fixedTwoTrial atTop (𝓝 normalizedScreenedTwo) :=
  (screenedPacket_tendsto 2).const_smul (Real.log 2)⁻¹

theorem fixedTwoTrial_tendsto_one_iff :
    Tendsto fixedTwoTrial atTop (𝓝 hilbertOne) ↔ hilbertOne ∈ closedSpace := by
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo]
  exact ⟨tendsto_nhds_unique fixedTwoTrial_tendsto, fun h => h ▸ fixedTwoTrial_tendsto⟩

theorem ramanujanPacketHilbert_two_norm_sq :
    ‖ramanujanPacketHilbert 2‖ ^ 2 = Real.log 2 := by
  rw [hilbert_norm_weighted_sq, hilbertSequence_ramanujanPacketHilbert]
  have hs (n : ℕ) : ramanujanPacket 2 n ^ 2 = ramanujanPacket 2 n := by
    rw [ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
    have hn := Nat.mod_lt n (by norm_num : 0 < 2)
    have he : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases he with h | h <;> norm_num [residue, h]
  simp_rw [hs]
  change paretoMean (ramanujanPacket 2) = _
  rw [paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]

private theorem fixedTwo_error_eq_capture (K : Submodule ℝ ThresholdHilbert)
    [K.HasOrthogonalProjection] (hK : hilbertOne ∈ Kᗮ) :
    ‖hilbertOne - (Real.log 2)⁻¹ •
      (ramanujanPacketHilbert 2 - K.starProjection (ramanujanPacketHilbert 2))‖ ^ 2 =
      (Real.log 2 - (Real.log 2) ^ 2 - ‖K.starProjection (ramanujanPacketHilbert 2)‖ ^ 2) /
        (Real.log 2) ^ 2 := by
  let z := ramanujanPacketHilbert 2
  let p := K.starProjection z
  have hp : p ∈ K := K.starProjection_apply_mem z
  have ho : z - p ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal z
  have hzp : inner ℝ z p = ‖p‖ ^ 2 := by
    have h := (K.mem_orthogonal _).mp ho p hp
    rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_eq_zero] at h
    rwa [real_inner_comm]
  have hzmean : inner ℝ z hilbertOne = Real.log 2 := by
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
  have hpmean : inner ℝ p hilbertOne = 0 := (K.mem_orthogonal _).mp hK p hp
  have hnorm : ‖z - p‖ ^ 2 = Real.log 2 - ‖p‖ ^ 2 := by
    rw [norm_sub_sq_real, hzp, ramanujanPacketHilbert_two_norm_sq]
    ring
  change ‖hilbertOne - (Real.log 2)⁻¹ • (z - p)‖ ^ 2 =
    (Real.log 2 - (Real.log 2) ^ 2 - ‖p‖ ^ 2) / (Real.log 2) ^ 2
  have hmean : inner ℝ hilbertOne (z - p) = Real.log 2 := by
    rw [real_inner_comm, inner_sub_left, hzmean, hpmean, sub_zero]
  rw [norm_sub_sq_real, hilbertOne_norm_sq, real_inner_smul_right, hmean,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnorm]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

theorem fixedTwoTrial_error_eq_capture (M : ℕ) :
    ‖hilbertOne - fixedTwoTrial M‖ ^ 2 =
      (Real.log 2 - (Real.log 2) ^ 2 -
        ‖(mixedSpace (Finset.Icc 2 M)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2) /
        (Real.log 2) ^ 2 :=
  fixedTwo_error_eq_capture _ (one_mem_mixed_orthogonal _)

theorem full_capture_saturation_iff :
    ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 =
        Real.log 2 - (Real.log 2) ^ 2 ↔ hilbertOne ∈ closedSpace := by
  have he : ‖hilbertOne - normalizedScreenedTwo‖ ^ 2 =
      (Real.log 2 - (Real.log 2) ^ 2 -
        ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2) / (Real.log 2) ^ 2 :=
    fixedTwo_error_eq_capture _ one_mem_mixedClosure_orthogonal
  have hn := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo]
  constructor
  · intro h
    rw [h, sub_self, zero_div] at he
    rw [pow_two, mul_eq_zero, or_self] at he
    exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm
  · intro h
    rw [h, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at he
    exact (sub_eq_zero.mp ((div_eq_zero_iff.mp he.symm).resolve_right (pow_ne_zero _ hn))).symm

theorem fixed_capture_tendsto_saturation_iff :
    Tendsto (fun M : ℕ =>
      ‖(mixedSpace (Finset.Icc 2 M)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2)
      atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2)) ↔ hilbertOne ∈ closedSpace := by
  have hmono : Monotone (fun M : ℕ => mixedSpace (Finset.Icc 2 M)) :=
    fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
  have h := (Submodule.starProjection_tendsto_closure_iSup
    (fun M => mixedSpace (Finset.Icc 2 M)) hmono (ramanujanPacketHilbert 2)).norm.pow 2
  rw [← full_capture_saturation_iff]
  exact ⟨tendsto_nhds_unique h, fun he => he ▸ h⟩

theorem fixed_capture_tendsto_saturation_iff_naturalApproximation :
    Tendsto (fun M : ℕ =>
      ‖(mixedSpace (Finset.Icc 2 M)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2)
      atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2)) ↔ BaezDuarte.NaturalApproximation :=
  fixed_capture_tendsto_saturation_iff.trans BaezDuarte.naturalApproximation_iff_one_mem.symm

theorem riemannHypothesis_of_fixed_capture_saturation
    (h : Tendsto (fun M : ℕ =>
      ‖(mixedSpace (Finset.Icc 2 M)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2)
      atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2))) : RiemannHypothesis :=
  riemannHypothesis_of_one_mem_screenedPrimeClosure
    (one_mem_screenedPrimeClosure_iff.mpr (fixed_capture_tendsto_saturation_iff.mp h))

end RiemannResearch.RH.Pareto.PrimePowerSchur

namespace RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
open PrimePowerSchur RiemannResearch.LinearAlgebra

theorem fullScreening_centeredInput (N : ℕ) :
    fullScreening (centeredInput N) =
      Chebyshev.psi (N : ℝ) • (normalizedScreenedTwo - hilbertOne) := by
  have hp : fullScreening (primeCombination (window N) (fun _ => 1)) =
      Chebyshev.psi (N : ℝ) • normalizedScreenedTwo := by
    unfold primeCombination finiteSchurCombination
    simp only [one_smul, map_sum]
    rw [← prime_source_eq_psi, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro q _
    exact fullScreening_packet_eq_mangoldt_smul q.val (by
      have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp q.property).1).1
      omega)
  rw [centeredInput, map_sub, map_smul, fullScreening_one, hp, smul_sub]

theorem fullCovarianceMass_eq_fixed_error (N : ℕ) :
    fullCovarianceMass N =
      (Chebyshev.psi (N : ℝ)) ^ 2 * ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  rw [fullCovarianceMass, fullScreening_centeredInput, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem fullCovarianceMass_normalized_tendsto_fixed_error
    :
    Tendsto (fun N => fullCovarianceMass N / (N : ℝ) ^ 2) atTop
      (𝓝 (‖normalizedScreenedTwo - hilbertOne‖ ^ 2)) := by
  have h : Tendsto (fun N : ℕ => (Chebyshev.psi (N : ℝ) / (N : ℝ)) ^ 2 *
      ‖normalizedScreenedTwo - hilbertOne‖ ^ 2) atTop
      (𝓝 (‖normalizedScreenedTwo - hilbertOne‖ ^ 2)) := by
    simpa only [one_pow, one_mul] using
      (psi_div_nat_tendsto.pow 2).mul_const (‖normalizedScreenedTwo - hilbertOne‖ ^ 2)
  apply h.congr
  intro N
  rw [fullCovarianceMass_eq_fixed_error N, div_pow]
  ring

theorem fullCovarianceMass_subquadratic_iff_one_mem :
    Tendsto (fun N => fullCovarianceMass N / (N : ℝ) ^ 2) atTop (𝓝 0) ↔
      hilbertOne ∈ CoefficientStabilization.closedSpace := by
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo]
  constructor
  · intro h
    have he := tendsto_nhds_unique fullCovarianceMass_normalized_tendsto_fixed_error h
    rw [pow_two, mul_eq_zero, or_self] at he
    exact sub_eq_zero.mp (norm_eq_zero.mp he)
  · intro h
    simpa only [h, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      fullCovarianceMass_normalized_tendsto_fixed_error

theorem riemannHypothesis_of_fullCovarianceMass_subquadratic
    (h : Tendsto (fun N => fullCovarianceMass N / (N : ℝ) ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo
    (one_mem_closedSpace_iff_normalizedScreenedTwo.mp
      (fullCovarianceMass_subquadratic_iff_one_mem.mp h))

theorem covarianceMass_eq_fixed_error_add_diagonal_tail (N : ℕ) :
    covarianceMass N =
      (Chebyshev.psi (N : ℝ)) ^ 2 *
          (CoefficientStabilization.limitEnergy / (1 - CoefficientStabilization.limitEnergy)) +
        ‖mixedClosure.starProjection (centeredInput N) -
          (mixedSpace (Finset.Icc 2 N)).starProjection (centeredInput N)‖ ^ 2 := by
  rw [← offDiagonalCovarianceMass_diagonal, offDiagonalCovarianceMass_split,
    fullCovarianceMass_eq_fixed_error, normalizedScreenedTwo_error_sq_eq_limitEnergy]

end RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
