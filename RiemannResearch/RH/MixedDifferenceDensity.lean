import RiemannResearch.RH.ScreenedPrimePowerTelescope
import RiemannResearch.RH.ThresholdHilbertDifference
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.RamanujanWeakConvergence

/-! # Density of the anchored differences of the mixed Pareto subspace

Divisibility is total under the equivalent inverse-square measure. An unscaled
residue has bounded first difference and logarithmically increasing mean.
Removing that mean in the mixed kernel leaves all the divisor tests.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization QParetoEquivalence ZetaTwoParetoTransfer
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QPhysicalDifference

private def jumpQ := paretoEquiv.symm.toContinuousLinearMap.comp hilbertDifference

private theorem jumpQ_raw (d : ℕ) (hd : 1 < d) :
    jumpQ (rawResidueAtom (d-2)) = qOne - (d : ℝ) • qDivisor d := by
  have commute (x : ThresholdHilbert) : jumpQ x = differenceCLM (paretoEquiv.symm x) := by
    apply qSequence_injective
    funext k
    change qSequence (toQ (hilbertDifference x)) k = _
    rw [toQ_sequence, hilbertDifference_sequence, qSequence_differenceCLM]
    simp only [PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift,
      SquarefreeRadicalDifference.qDifference, paretoEquiv_symm_apply, toQ_sequence]
  have hi : d - 2 + 2 = d := by omega
  have hat : paretoEquiv.symm (residueAtom (d-2)) = qResidue d := by
    rw [← toPareto_residueAtom, paretoEquiv_symm_apply, toQ_toPareto, hi]
  have hreal : (d : ℝ) ≠ 0 := by positivity
  rw [commute, rawResidueAtom, map_smul, hi, hat, map_smul,
    QCRTFiniteCollocation.difference_residue d hd, smul_sub, smul_smul]
  simp [hreal]

private theorem scaled_divisor_norm {d : ℕ} (hd : 0 < d) :
    ‖(d : ℝ) • qDivisor d‖ = 1 := by
  have hn : (d : ℝ) ≠ 0 := by positivity
  have hs : ‖(d : ℝ) • qDivisor d‖ ^ 2 = 1 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, qDivisor_norm_sq d hd]
    field_simp
  nlinarith [norm_nonneg ((d : ℝ) • qDivisor d)]

private theorem scaled_divisor_inner_tendsto (h : QHilbert) :
    Tendsto (fun d : ℕ => inner ℝ h ((d : ℝ) • qDivisor d)) atTop (𝓝 0) := by
  have hw := RamanujanWeakConvergence.q_innerWeak_of_bounded_pointwise
    (l := atTop) (fun d : ℕ => (d : ℝ) • qDivisor d) 0 (by
      intro k hk
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop k] with d hd
      have hn : ¬ d ∣ k := fun h => (not_le.mpr hd) (Nat.le_of_dvd hk h)
      change qSequence (0 : QHilbert) k = qSequenceLinear ((d : ℝ) • qDivisor d) k
      rw [show qSequence (0 : QHilbert) k = 0 from congrFun qSequenceLinear.map_zero k, map_smul]
      simp [qSequence_qDivisor, positiveDivisor, hn, hk.ne', qSequenceLinear])
    1 (by
      filter_upwards [eventually_gt_atTop 0] with d hd
      rw [scaled_divisor_norm hd]
      norm_num)
  simpa using hw h

private theorem log_corrected_mixed (d : ℕ) (hd : 1 < d) :
    rawResidueAtom (d-2) - Real.log d • logNormalizedResidue 2 ∈ mixedClosure := by
  have h0 : fullScreening (rawResidueAtom (d-2) - Real.log d • logNormalizedResidue 2) = 0 := by
    rw [map_sub, map_smul, fullScreening_rawResidue_eq_log_smul d hd,
      fullScreening_logNormalizedResidue 2 (by decide), sub_self]
  change _ - mixedClosure.starProjection _ = 0 at h0
  exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp h0).symm

private theorem q_orthogonal_jumps (h : QHilbert)
    (hzero : ∀ m ∈ mixedClosure, inner ℝ h (jumpQ m) = 0) : h = 0 := by
  let a := inner ℝ h (jumpQ (logNormalizedResidue 2))
  have hpair (d : ℕ) (hd : 1 < d) :
      inner ℝ h (qOne - (d : ℝ) • qDivisor d) = Real.log d * a := by
    have he := hzero _ (log_corrected_mixed d hd)
    rw [map_sub, map_smul, inner_sub_right, real_inner_smul_right, jumpQ_raw d hd] at he
    exact sub_eq_zero.mp he
  have ha : a = 0 := by
    by_contra hne
    have hpos := abs_pos.mpr hne
    let C := ‖h‖ * (‖qOne‖ + 1)
    obtain ⟨d, hd⟩ := exists_nat_gt (max 2 (Real.exp (C / |a|)))
    have hd' : 1 < d := by
      have := (le_max_left (2:ℝ) (Real.exp (C / |a|))).trans_lt hd
      exact_mod_cast (lt_trans (by norm_num : (1:ℝ) < 2) this)
    have hlog := (Real.lt_log_iff_exp_lt (by positivity : (0:ℝ) < d)).2
      ((le_max_right (2:ℝ) _).trans_lt hd)
    have big : C < Real.log d * |a| := (div_lt_iff₀ hpos).mp hlog
    have small := abs_real_inner_le_norm h (qOne - (d:ℝ) • qDivisor d)
    rw [hpair d hd',abs_mul,abs_of_pos (Real.log_pos (by exact_mod_cast hd'))] at small
    have bound := norm_sub_le qOne ((d : ℝ) • qDivisor d)
    rw [scaled_divisor_norm (by omega : 0 < d)] at bound
    exact (not_lt_of_ge (small.trans (mul_le_mul_of_nonneg_left bound (norm_nonneg _)))) big
  have he (d : ℕ) (hd : 1 < d) :
      inner ℝ h ((d : ℝ) • qDivisor d) = inner ℝ h qOne := by
    have hh := hpair d hd
    rw [ha,mul_zero,inner_sub_right] at hh
    exact (sub_eq_zero.mp hh).symm
  have one : inner ℝ h qOne = 0 := by
    have hc : Tendsto (fun d : ℕ => inner ℝ h ((d : ℝ) • qDivisor d)) atTop
        (𝓝 (inner ℝ h qOne)) := tendsto_const_nhds.congr'
      ((eventually_gt_atTop 1).mono fun d hd => (he d hd).symm)
    exact tendsto_nhds_unique hc (scaled_divisor_inner_tendsto h)
  apply eq_zero_of_orthogonal_qDivisor h
  intro d hd
  rcases eq_or_lt_of_le (show 1 ≤ d by omega) with rfl | hd'
  · simpa only [QCRTFiniteCollocation.qDivisor_one] using one
  · have he' := he d hd'
    rw [real_inner_smul_right, one] at he'
    exact (mul_eq_zero.mp he').resolve_left (by positivity)

/-- The anchored differences of the closed mixed space are dense in the entire
physical Pareto space. The hypothesis of RH is absent. -/
theorem mixedDifference_dense : DenseRange (fun m : mixedClosure => hilbertDifference m.val) := by
  let T := jumpQ.comp mixedClosure.subtypeL
  have horth : (LinearMap.range T.toLinearMap)ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro h hh
    apply (Submodule.mem_bot ℝ).mpr
    apply q_orthogonal_jumps h
    intro m hm
    exact inner_eq_zero_symm.mp (hh _ ⟨⟨m,hm⟩, rfl⟩)
  have hc : (LinearMap.range T.toLinearMap).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,horth,Submodule.bot_orthogonal_eq_top]
  have hq : DenseRange T := by
    intro y
    change y ∈ (LinearMap.range T.toLinearMap).topologicalClosure
    rw [hc]
    exact Submodule.mem_top
  intro y
  have hy := mem_closure_image paretoEquiv.continuous.continuousAt (hq (paretoEquiv.symm y))
  rw [paretoEquiv.apply_symm_apply] at hy
  apply closure_mono _ hy
  rintro _ ⟨_,⟨m,rfl⟩,rfl⟩
  exact ⟨m, (paretoEquiv.apply_symm_apply _).symm⟩

/-- The constant is in the closure of the differenced mixed space, but even
on the full Hilbert space it has no anchored primitive. -/
theorem one_not_mem_difference_range :
    hilbertOne ∉ LinearMap.range hilbertDifference.toLinearMap := by
  rintro ⟨f, hf⟩
  have coords (n : ℕ) : hilbertSequence f n = (n : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have he := congrArg (fun x => hilbertSequence x (n+1)) hf
      change hilbertSequence (hilbertDifference f) (n+1) = _ at he
      rw [hilbertDifference_sequence, hilbertOne_sequence] at he
      simp only [PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift, Nat.add_sub_cancel,
        zeroAnchor, Nat.succ_ne_zero, if_false] at he
      rw [ih] at he
      push_cast
      linarith
  have hlim := (hilbertSequence_square_summable f).tendsto_atTop_zero
  have small := (tendsto_order.mp hlim).2 (1/2 : ℝ) (by norm_num)
  obtain ⟨n, hn, hn'⟩ := ((eventually_gt_atTop 0).and small).exists
  rw [coords, positiveWeight] at hn'
  have hpos : (0:ℝ) < n := by exact_mod_cast hn
  have hone : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hden : 0 < (n:ℝ) * (n+1) := by positivity
  field_simp [hden] at hn'
  nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hone)]

end RiemannResearch.RH.Pareto.PrimePowerSchur
