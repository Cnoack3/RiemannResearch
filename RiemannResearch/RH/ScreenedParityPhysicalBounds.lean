import RiemannResearch.RH.ScreenedParityOneSided
import RiemannResearch.RH.ScreenedPrimePowerTelescope
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.ParetoCoordinateBounds
import RiemannResearch.RH.CanonicalMobiusSignedAverages
import RiemannResearch.RH.ParetoAnnihilatorTail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Physical coordinates and one-sided tails of the screened parity packet

The coordinate estimate uses its exact mean. The first-moment estimate retains
the complete remaining square energy. Orthogonality fixes the signed average
on each dilated parity support. The one-sided absolute-tail condition below is
an open input for the actual projection residual. -/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- Removing the constant direction saves one unit in the squared norm of a
physical coordinate functional on the mean-zero subspace. -/
theorem mean_zero_coordinate_sq_le (f : ThresholdHilbert) (hmean : inner ℝ f hilbertOne = 0)
    (k : ℕ) (hk : 0 < k) :
    (hilbertSequence f k)^2 ≤ ((k : ℝ) * ((k : ℝ) + 1) - 1) * ‖f‖^2 := by
  let H : ℝ := (k : ℝ) * ((k : ℝ) + 1)
  let x := hilbertSequence f k
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hH : 1 < H := by dsimp [H]; nlinarith
  let t := x / (H - 1)
  have ht : t * (H - 1) = x := div_mul_cancel₀ x (sub_ne_zero.mpr hH.ne')
  have hnorm : ‖f + t • hilbertOne‖^2 = ‖f‖^2 + t^2 := by
    rw [norm_add_sq_real, real_inner_smul_right, hmean, mul_zero, mul_zero, add_zero,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hilbertOne_norm_sq, mul_one]
  have hev : hilbertSequence (f + t • hilbertOne) k = x + t := by
    simp [x, hilbertSequence_add, hilbertSequence_smul, hilbertOne_sequence, zeroAnchor, hk.ne']
  have h := hilbertSequence_sq_le_norm_sq (f + t • hilbertOne) k
  rw [hev, hnorm] at h
  change (x+t)^2 ≤ H * (‖f‖^2 + t^2) at h
  have hm := mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hH.le)
  change x^2 ≤ (H-1) * ‖f‖^2
  apply (mul_le_mul_iff_right₀ (lt_trans zero_lt_one hH)).mp
  rw [← ht] at hm ⊢
  linarith only [hm]

/-- The complete absolute tail past site N, including its actual energy factor. -/
theorem pareto_absolute_tail_sq_le (f : ThresholdHilbert) (N : ℕ) :
    (∑' k : ℕ, positiveWeight (k+N+1) * |hilbertSequence f (k+N+1)|)^2 ≤
      ‖hilbertTailShift f N‖^2 / ((N : ℝ)+1) := by
  have hA : ‖hilbertTailShift (hilbertAbs f) N‖^2 = ‖hilbertTailShift f N‖^2 := by
    simp only [CoefficientStabilization.hilbertTailShift_energy_eq_weighted, hilbertAbs_sequence, sq_abs]
  have hOne : ‖hilbertTailShift hilbertOne N‖^2 = 1 / ((N : ℝ)+1) := by
    rw [CoefficientStabilization.hilbertTailShift_energy_eq_weighted]
    simp only [hilbertOne_sequence, zeroAnchor, Nat.succ_ne_zero, if_false, one_pow, mul_one]
    simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
      positiveWeight_tail_tsum (N+1) (Nat.succ_pos N)
  have hpair : (∑' k : ℕ, positiveWeight (k+N+1) * |hilbertSequence f (k+N+1)|) =
      inner ℝ (hilbertTailShift (hilbertAbs f) N) (hilbertTailShift hilbertOne N) := by
    rw [hilbertTailShift_inner_weighted]
    simp only [hilbertAbs_sequence, hilbertOne_sequence, zeroAnchor, Nat.succ_ne_zero,
      if_false, mul_one]
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm (hilbertTailShift (hilbertAbs f) N) (hilbertTailShift hilbertOne N))
  rw [sq_abs, mul_pow, hA, hOne] at h
  simpa only [hpair, one_div, div_eq_mul_inv, one_mul] using h

namespace PrimePowerSchur
open CoefficientStabilization

/-- The exact residual pairing with the doubled dilation gives a first-site
estimate proportional to the squared error. -/
theorem screenedTwo_first_coordinate_bounds :
    -(1 + Real.sqrt 2) * limitEnergy ≤
        (1 - limitEnergy) * (hilbertSequence normalizedScreenedTwo 1 - 1) ∧
      (1 - limitEnergy) * (hilbertSequence normalizedScreenedTwo 1 - 1) ≤
        (Real.sqrt 2 - 1) * limitEnergy := by
  obtain ⟨hl, hu⟩ := firstCoordinate_energy_bounds
  rw [limitResidual_at_pos_eq_screenedTwo 1 (by decide)] at hl hu
  constructor <;> linarith

/-- The normalized screened packet has unit mean, so the centered coordinate
bound applies at every positive physical site. -/
theorem screenedTwo_coordinate_sq_le (k : ℕ) (hk : 0 < k) :
    (hilbertSequence normalizedScreenedTwo k - 1)^2 ≤
      ((k : ℝ) * ((k : ℝ) + 1) - 1) * ‖normalizedScreenedTwo - hilbertOne‖^2 := by
  have hmean : inner ℝ (normalizedScreenedTwo - hilbertOne) hilbertOne = 0 := by
    rw [inner_sub_left, normalizedScreenedTwo_mean, real_inner_self_eq_norm_sq,
      hilbertOne_norm_sq, sub_self]
  simpa only [hilbertSequence_sub, Pi.sub_apply, hilbertOne_sequence,
    zeroAnchor, if_neg hk.ne'] using
    mean_zero_coordinate_sq_le (normalizedScreenedTwo - hilbertOne) hmean k hk

/-- Every alternating block support has the same normalized screened mean.
The factor N is already included in the dilation. -/
theorem screenedTwo_dilated_parity_pairing (N : ℕ) (hN : 0 < N) :
    (1 - limitEnergy) *
      inner ℝ (hilbertDilation N hN (ramanujanPacketHilbert 2)) normalizedScreenedTwo =
      Real.log 2 := by
  let d := hilbertDilation N hN (ramanujanPacketHilbert 2)
  have hm : inner ℝ d hilbertOne = Real.log 2 := by
    rw [hilbert_inner_one, hilbertDilation_mean, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have ho : inner ℝ d limitResidual = 0 :=
    limitResidual_mem_orthogonal d
      (closedSpace_dilation (packet_mem_closedSpace 2 (by norm_num)) N hN)
  rw [limitResidual, limitProjection_eq_scaled_screenedTwo, inner_sub_right,
    real_inner_smul_right, hm] at ho
  linarith

/-- A complete one-sided first-moment tail of order 1/N suffices. The
controlled sign may vary with the physical cutoff. -/
theorem screenedTwo_eq_one_of_oneSidedResidualTail
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, 0 < N →
      (∑' k : ℕ, positiveWeight (k+N) * max (hilbertSequence limitResidual (k+N)) 0) ≤ C / (N : ℝ) ∨
      (∑' k : ℕ, positiveWeight (k+N) * max (-hilbertSequence limitResidual (k+N)) 0) ≤ C / (N : ℝ)) :
    normalizedScreenedTwo = hilbertOne := by
  apply one_mem_closedSpace_iff_normalizedScreenedTwo.mp
  apply limitEnergy_zero_iff_mem.mp
  rw [← limitResidual_inner_one]
  exact annihilator_mean_zero_of_absolute_tail limitResidual limitResidual_mem_orthogonal _
    (by positivity) (annihilator_absolute_tail_le_of_oneSided_tails limitResidual
      limitResidual_mem_orthogonal C hb)

/-- Every finite mixed-screened trial vanishes at an explicit positive site. -/
theorem fixedTwoTrial_at_common_factorial (m : ℕ) :
    hilbertSequence (fixedTwoTrial m) (2 * (m + 1).factorial) = 0 := by
  let L := 2 * (m + 1).factorial
  let K := mixedSpace (Finset.Icc 2 m)
  have hdiv (q : ℕ) (hq : q ∈ mixedConductors (Finset.Icc 2 m)) : q ∣ L := by
    obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    exact dvd_mul_of_dvd_right (Nat.dvd_factorial (by omega) (by omega)) 2
  have hc := mixedSpace_evaluation_eq_zero_of_common_multiple _ L hdiv
    (K.starProjection_apply_mem (ramanujanPacketHilbert 2))
  have hz : anchoredEvaluationCLM L (ramanujanPacketHilbert 2) = 0 := by
    rw [anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert,
      ramanujanPacket_eq_zero_of_dvd (show 2 ∣ L from dvd_mul_right 2 _)]
  change hilbertSequence (fixedTwoTrial m) L = 0
  rw [← anchoredEvaluationCLM_apply, fixedTwoTrial, map_smul, screenedPacket,
    map_sub, hc, hz, sub_zero, smul_zero]

/-- A common upper or lower constant may be tested along cofinal mixed
cutoffs separately at each fixed site. -/
theorem screenedTwo_eq_one_of_cofinal_trial_bounds
    (hb : (∃ C : ℝ, ∀ k : ℕ, 0 < k →
        ∃ᶠ m : ℕ in atTop, C ≤ hilbertSequence (fixedTwoTrial m) k) ∨
      (∃ C : ℝ, ∀ k : ℕ, 0 < k →
        ∃ᶠ m : ℕ in atTop, hilbertSequence (fixedTwoTrial m) k ≤ C)) :
    normalizedScreenedTwo = hilbertOne := by
  have ht (k : ℕ) : Tendsto (fun m => hilbertSequence (fixedTwoTrial m) k)
      atTop (𝓝 (hilbertSequence normalizedScreenedTwo k)) := by
    simpa only [Function.comp_def, anchoredEvaluationCLM_apply] using
      (anchoredEvaluationCLM k).continuous.continuousAt.tendsto.comp fixedTwoTrial_tendsto
  apply normalizedScreenedTwo_eq_one_of_oneSidedBound
  rcases hb with ⟨C, hC⟩ | ⟨C, hC⟩
  · refine Or.inl ⟨C, fun k hk => ?_⟩
    by_contra! h
    obtain ⟨m, hm, hm'⟩ := ((hC k hk).and_eventually ((ht k).eventually_lt_const h)).exists
    exact (not_lt_of_ge hm) hm'
  · refine Or.inr ⟨C, fun k hk => ?_⟩
    by_contra! h
    obtain ⟨m, hm, hm'⟩ := ((hC k hk).and_eventually ((ht k).eventually_const_lt h)).exists
    exact (not_lt_of_ge hm) hm'

end PrimePowerSchur
end RiemannResearch.RH.Pareto
