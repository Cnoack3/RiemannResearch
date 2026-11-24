import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.DyadicFiniteCriticalNorm
import RiemannResearch.RH.FiniteEndpointGram
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ThresholdJointAdjointRigidity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Physical dilation tests for the screened mean section

Forward dilation preserves the pairing of legal vectors with the mean-one
screened section. The growth of its squared norm under the adjoints at scales
two and three detects equality with the constant line. The half dilation at
two gives a quantitative estimate for the distance to the constant using
the first physical coordinate and the full squared norm.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- Forward dilation preserves the pairing of every legal vector with the screened section. -/
theorem inner_dilation_screenedTwo {v : ThresholdHilbert} (hv : v ∈ closedSpace)
    (m : ℕ) (hm : 0 < m) :
    inner ℝ (hilbertDilation m hm v) normalizedScreenedTwo =
      inner ℝ v normalizedScreenedTwo := by
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  have h := Submodule.inner_right_of_mem_orthogonal
    (hilbertDilation_sub_self_mem_mixedClosure m hm hv) hu.2
  rwa [inner_sub_left, sub_eq_zero] at h

/-- The adjoint increment is perpendicular to the full legal space. -/
theorem adjoint_screenedTwo_sub_mem_orthogonal (m : ℕ) (hm : 0 < m) :
    hilbertDilationAdjoint m hm normalizedScreenedTwo - normalizedScreenedTwo ∈
      closedSpaceᗮ := by
  intro v hv
  rw [inner_sub_right]
  change inner ℝ v ((hilbertDilationContinuous m hm).adjoint normalizedScreenedTwo) - _ = 0
  rw [ContinuousLinearMap.adjoint_inner_right, hilbertDilationContinuous_apply,
    inner_dilation_screenedTwo hv, sub_self]

/-- Exact squared norm growth of each prime or composite dilation adjoint. -/
theorem adjoint_screenedTwo_norm_sq (m : ℕ) (hm : 0 < m) :
    ‖hilbertDilationAdjoint m hm normalizedScreenedTwo‖ ^ 2 =
      ‖normalizedScreenedTwo‖ ^ 2 +
        ‖hilbertDilationAdjoint m hm normalizedScreenedTwo - normalizedScreenedTwo‖ ^ 2 := by
  have h := Submodule.inner_right_of_mem_orthogonal
    (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure)
    (adjoint_screenedTwo_sub_mem_orthogonal m hm)
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at h
  rw [norm_sub_sq_real]
  linarith only [h, real_inner_comm normalizedScreenedTwo
    (hilbertDilationAdjoint m hm normalizedScreenedTwo)]

/-- Nonincrease in the combined squared norm at scales two and three detects the constant line. -/
theorem screenedLine_eq_one_line_iff_two_three_adjoint_norms :
    Submodule.span ℝ {normalizedScreenedTwo} = Submodule.span ℝ {hilbertOne} ↔
      ‖hilbertDilationAdjoint 2 (by decide) normalizedScreenedTwo‖ ^ 2 +
        ‖hilbertDilationAdjoint 3 (by decide) normalizedScreenedTwo‖ ^ 2 ≤
        2 * ‖normalizedScreenedTwo‖ ^ 2 := by
  rw [CenteredMeanSnake.screenedLine_eq_one_line_iff_one_mem,
    one_mem_closedSpace_iff_normalizedScreenedTwo]
  constructor
  · intro h
    rw [h, hilbertDilationAdjoint_one, hilbertDilationAdjoint_one, two_mul]
  · intro h
    rw [adjoint_screenedTwo_norm_sq, adjoint_screenedTwo_norm_sq] at h
    have hzero (a b : ℝ) (hab : a^2 + b^2 ≤ 0) : a = 0 ∧ b = 0 := by
      exact ⟨sq_eq_zero_iff.mp (by linarith only [hab, sq_nonneg a, sq_nonneg b]),
        sq_eq_zero_iff.mp (by linarith only [hab, sq_nonneg a, sq_nonneg b])⟩
    obtain ⟨h2, h3⟩ := hzero
      ‖hilbertDilationAdjoint 2 (by decide) normalizedScreenedTwo - normalizedScreenedTwo‖
      ‖hilbertDilationAdjoint 3 (by decide) normalizedScreenedTwo - normalizedScreenedTwo‖
      (by linarith only [h])
    obtain ⟨c, hc⟩ := (hilbertDilationAdjoint_two_three_fixed_iff _).mp
      ⟨sub_eq_zero.mp (norm_eq_zero.mp h2), sub_eq_zero.mp (norm_eq_zero.mp h3)⟩
    have hmean := normalizedScreenedTwo_mean
    rw [hc, real_inner_smul_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq, mul_one] at hmean
    simpa only [hmean, one_smul] using hc

/-- Removing the first site and comparing to the half dilation gives an exact norm defect. -/
theorem screenedTwo_first_site_dilation_identity :
    let b := hilbertSequence normalizedScreenedTwo 1
    let z := normalizedScreenedTwo - b • hilbertOne
    2 * ‖z - dyadicHalfDilation z‖ ^ 2 = ‖normalizedScreenedTwo‖ ^ 2 - b ^ 2 := by
  let u := normalizedScreenedTwo
  let b := hilbertSequence u 1
  change 2 * ‖(u - b • hilbertOne) - dyadicHalfDilation (u - b • hilbertOne)‖ ^ 2 =
    ‖u‖ ^ 2 - b ^ 2
  have hp : hilbertOne - dyadicHalfDilation hilbertOne = paretoPointHilbert 0 :=
    firstPoint_eq_dilation_difference.symm
  have hv : (u - b • hilbertOne) - dyadicHalfDilation (u - b • hilbertOne) =
      (u - b • paretoPointHilbert 0) - dyadicHalfDilation u := by
    rw [← hp, map_sub, map_smul, smul_sub]
    abel
  have hlegal : u ∈ closedSpace :=
    screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
  have hinner : inner ℝ u (hilbertDilation 2 (by decide) u) = ‖u‖^2 := by
    rw [real_inner_comm, inner_dilation_screenedTwo hlegal, real_inner_self_eq_norm_sq]
  have hpoint : inner ℝ (paretoPointHilbert 0) (hilbertDilation 2 (by decide) u) = 0 :=
    (real_inner_comm ..).trans (doubleDilation_inner_firstPoint u)
  rw [hv, norm_sub_sq_real, remove_firstPoint_norm_sq, dyadicHalfDilation_norm_sq,
    dyadicHalfDilation_apply, real_inner_smul_right, inner_sub_left, real_inner_smul_left,
    hinner, hpoint]
  dsimp only [b]
  ring

/-- The first-site deficit quantitatively controls the distance to the ambient constant. -/
theorem screenedTwo_distance_le_first_site_deficit :
    (Real.sqrt 2 - 1)^2 * ‖normalizedScreenedTwo - hilbertOne‖^2 ≤
      ‖normalizedScreenedTwo‖^2 - (hilbertSequence normalizedScreenedTwo 1)^2 := by
  let u := normalizedScreenedTwo
  let b := hilbertSequence u 1
  let z := u - b • hilbertOne
  have hmean : inner ℝ u hilbertOne = 1 := normalizedScreenedTwo_mean
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith only [hs, Real.sqrt_nonneg 2]
  have hhalf : Real.sqrt 2 * ‖dyadicHalfDilation z‖ = ‖z‖ := by
    have hsq : (Real.sqrt 2 * ‖dyadicHalfDilation z‖)^2 = ‖z‖^2 := by
      rw [mul_pow, hs, dyadicHalfDilation_norm_sq]
      ring
    nlinarith only [hsq, mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg (dyadicHalfDilation z)),
      norm_nonneg z]
  have hle : (Real.sqrt 2 - 1) * ‖z‖ ≤ Real.sqrt 2 * ‖z - dyadicHalfDilation z‖ := by
    have hh := mul_le_mul_of_nonneg_left (norm_sub_norm_le z (dyadicHalfDilation z))
      (Real.sqrt_nonneg 2)
    linarith only [hh, hhalf]
  have hsq := mul_self_le_mul_self (mul_nonneg (sub_nonneg.mpr hs1) (norm_nonneg z)) hle
  simp only [← pow_two, mul_pow, hs] at hsq
  have hdist : ‖u - hilbertOne‖^2 ≤ ‖z‖^2 := by
    dsimp only [z]
    rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, hilbertOne_norm_sq, hmean]
    nlinarith only [sq_nonneg (b - 1)]
  have hid : 2 * ‖z - dyadicHalfDilation z‖^2 = ‖u‖^2 - b^2 :=
    screenedTwo_first_site_dilation_identity
  exact (mul_le_mul_of_nonneg_left hdist (sq_nonneg _)).trans (hsq.trans_eq hid)

/-- Equality of the screened and constant lines is equivalent to a one-sided
comparison between the first physical coordinate squared and the full squared norm. -/
theorem screenedLine_eq_one_line_iff_first_site_norm :
    Submodule.span ℝ {normalizedScreenedTwo} = Submodule.span ℝ {hilbertOne} ↔
      ‖normalizedScreenedTwo‖ ^ 2 ≤ (hilbertSequence normalizedScreenedTwo 1) ^ 2 := by
  rw [CenteredMeanSnake.screenedLine_eq_one_line_iff_one_mem,
    one_mem_closedSpace_iff_normalizedScreenedTwo]
  constructor
  · intro h
    rw [h, hilbertOne_sequence, hilbertOne_norm_sq]
    norm_num [zeroAnchor]
  · intro h
    have hs : 1 < Real.sqrt 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hp : 0 < (Real.sqrt 2 - 1)^2 := pow_pos (sub_pos.mpr hs) 2
    have hle := screenedTwo_distance_le_first_site_deficit.trans (sub_nonpos.mpr h)
    have hsq := nonpos_of_mul_nonpos_right hle hp
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))))

end RiemannResearch.RH.Pareto.PrimePowerSchur
