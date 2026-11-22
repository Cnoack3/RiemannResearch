import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.RH.ParetoFiniteCertificates
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Möbius coordinates of the projected parity packet

For the sign convention d = 1 - u, each coordinate of d measures the difference
between a genuine coordinate of the mixed projection of J₂ and the corresponding
target charge. The coordinates of indices greater than one determine d in the
complete Pareto space. At conductor six the existing finite separator yields a
quantitative error estimate. The simultaneous charge identities for the actual
mixed projection remain an arithmetic hypothesis.

The Hilbert-space closure criterion motivating this calculation is Theorem 1 of
B. Bagchi, *On Nyman, Beurling and Báez-Duarte's Hilbert space reformulation
of the Riemann hypothesis* (2006), https://arxiv.org/abs/math/0607733.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur

/-- Signed defect at any conductor above one. The term at two is the only
Möbius coordinate of the raw parity residue at those conductors. -/
theorem mixed_projection_parity_charge_defect (b : ℕ) (hb : 1 < b) :
    mobiusDifferenceCLM b (mixedClosure.starProjection (ramanujanPacketHilbert 2)) +
        (if b = 2 then 2 else 0) + Real.log 2 * (ArithmeticFunction.moebius b : ℝ) =
      Real.log 2 * mobiusDifferenceCLM b (hilbertOne - normalizedScreenedTwo) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hsplit : (Real.log 2) • normalizedScreenedTwo =
      ramanujanPacketHilbert 2 - mixedClosure.starProjection (ramanujanPacketHilbert 2) := by
    change (Real.log 2) • ((Real.log 2)⁻¹ • _) = _
    rw [smul_smul, mul_inv_cancel₀ hlog, one_smul]
    rfl
  have hmap := congrArg (mobiusDifferenceCLM b) hsplit
  rw [map_smul, map_sub, smul_eq_mul] at hmap
  have hraw : mobiusDifferenceCLM b (ramanujanPacketHilbert 2) =
      (if b = 2 then -2 else 0) := by
    rw [mobiusDifferenceCLM_apply, hilbertSequence_ramanujanPacketHilbert,
      ramanujanPacket_prime_eq_residue 2 Nat.prime_two, mobiusDifference_residue b 2 hb]
    norm_num
  rw [hraw] at hmap
  rw [map_sub, mobius_coordinate_one b (by omega)]
  split_ifs at hmap ⊢ <;> linarith only [hmap]

/-- Vanishing of d is equivalent to the full system of exact coordinates of
the mixed projection. The index one is unnecessary by Pareto square summability. -/
theorem screenedTwo_eq_one_iff_mixed_projection_charges :
    normalizedScreenedTwo = hilbertOne ↔
      ∀ b : ℕ, 1 < b →
        mobiusDifferenceCLM b (mixedClosure.starProjection (ramanujanPacketHilbert 2)) =
          -(if b = 2 then 2 else 0) - Real.log 2 * (ArithmeticFunction.moebius b : ℝ) := by
  constructor
  · intro hu b hb
    have h := mixed_projection_parity_charge_defect b hb
    rw [hu, sub_self, map_zero, mul_zero] at h
    linarith only [h]
  · intro h
    apply Eq.symm
    apply sub_eq_zero.mp
    apply eq_zero_of_mobius_coordinates_zero
    intro b hb
    have e := mixed_projection_parity_charge_defect b hb
    rw [h b hb] at e
    have hz : Real.log 2 * mobiusDifferenceCLM b (hilbertOne - normalizedScreenedTwo) = 0 := by
      linarith only [e]
    exact (mul_eq_zero.mp hz).resolve_left (Real.log_pos (by norm_num)).ne'

/-- The four-site separator of conductor six certifies an error in the mixed
projection through the complete squared Pareto discrepancy. -/
theorem mixed_projection_six_charge_error_bound :
    (mobiusDifferenceCLM 6 (mixedClosure.starProjection (ramanujanPacketHilbert 2)) +
        Real.log 2) ^ 2 ≤
      (Real.log 2) ^ 2 * (91 * ‖hilbertOne - normalizedScreenedTwo‖ ^ 2) := by
  have he := mixed_projection_parity_charge_defect 6 (by decide)
  simp only [if_neg (by decide : ¬ (6 : ℕ) = 2), add_zero, moebius_six,
    Int.cast_one, mul_one] at he
  have hn : ‖mobiusDifferenceCLM 6‖ ^ 2 = 92 := by
    rw [mobiusDifferenceCLM_norm_sq 6 (by decide)]
    have hz : (∑ j ∈ Finset.Icc (1 : ℕ) 6,
        (j : ℤ) * (j + 1) * dualCoeff 6 j ^ 2) = 92 := by decide +kernel
    exact_mod_cast hz
  let d := hilbertOne - normalizedScreenedTwo
  let r := mobiusRieszHilbert 6 - hilbertOne
  have hd : inner ℝ hilbertOne d = 0 := by
    rw [real_inner_comm]
    change inner ℝ (hilbertOne - normalizedScreenedTwo) hilbertOne = 0
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
      normalizedScreenedTwo_mean, sub_self]
  have hr : ‖r‖ ^ 2 = 91 := by
    change ‖mobiusRieszHilbert 6 - hilbertOne‖ ^ 2 = 91
    rw [norm_sub_sq_real, mobiusRieszHilbert_inner, mobius_coordinate_one 6 (by decide),
      moebius_six, mobiusRieszHilbert_norm, hn, hilbertOne_norm_sq]
    norm_num
  have hp : inner ℝ r d = mobiusDifferenceCLM 6 d := by
    change inner ℝ (mobiusRieszHilbert 6 - hilbertOne) d = _
    rw [inner_sub_left, hd, sub_zero, mobiusRieszHilbert_inner]
  have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm r d)
  rw [sq_abs, hp, mul_pow, hr] at hsq
  rw [he, mul_pow]
  exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)

end RiemannResearch.RH.Pareto.PrimePowerSchur
