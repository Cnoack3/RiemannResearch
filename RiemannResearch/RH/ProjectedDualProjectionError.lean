import RiemannResearch.RH.ProjectedDualStretchedTail
import RiemannResearch.RH.MobiusResidualFirstCoordinate
/-!
# Finite projection error controlled by inverse-column mass

Source: the user's request to prove the inverse-column concentration provider,
28 September 2026. These independently derived finite estimates use only
orthogonality, exact integer dilation and the complete canonical error.
The second and third coefficient duals have short threshold syntheses, giving
fourth-power error bounds with constants 270 and 530.

These are unconditional inequalities, not upper growth estimates on column
mass and not a proof of RH. The companion audit explains a critical-line
Mellin obstruction on paper. That obstruction's boundary estimate, critical
zero existence, and final asymptotic assembly are not formalized here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Integer dilation of the canonical exact-head approximant has explicit finite conductor. -/
theorem canonicalMobiusHilbert_dilation_mem_finiteSpace
    (n N m : ℕ) (hm : 0 < m) (hcut : m * (N+1) ≤ n+1) :
    hilbertDilation m hm (canonicalMobiusHilbert N) ∈ finiteSpace n := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion N (canonicalMobiusHilbert N)
    (canonicalMobiusHilbert_mem_finiteSpace N)
  change (hilbertDilationContinuous m hm) (canonicalMobiusHilbert N) ∈ finiteSpace n
  rw [ha, map_sum]
  apply (finiteSpace n).sum_mem
  intro i hi
  rw [map_smul]
  apply (finiteSpace n).smul_mem
  change hilbertDilation m hm (residueAtom i.val) ∈ finiteSpace n
  rw [hilbertDilation_residueAtom]
  apply (finiteSpace n).sub_mem
  · apply (finiteSpace n).smul_mem
    exact normalizedResidueHilbert_mem_finiteSpace n (m * (i.val+2)) (by positivity)
      ((Nat.mul_le_mul_left m (by omega : i.val+2 ≤ N+1)).trans hcut)
  · apply (finiteSpace n).smul_mem
    exact normalizedResidueHilbert_mem_finiteSpace n m hm
      ((Nat.le_mul_of_pos_right m (Nat.succ_pos N)).trans hcut)

namespace CorrectionTail
/-- The column mass controls a tail at any cutoff, independently of stage n. -/
theorem projectedDualTail_any_cutoff_le_mass (n d N : ℕ) :
    ‖hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) N‖ ^ 2 ≤
      projectedDualCoefficientMass n d ^ 2 / ((N : ℝ)+1) := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion n
    ((finiteSpace n).starProjection (coefficientRiesz d))
    ((finiteSpace n).starProjection_apply_mem _)
  have hc (i : Fin n) : coefficientCLM (i.val+2)
      ((finiteSpace n).starProjection (coefficientRiesz d)) = a i := by
    rw [ha, coefficient_finite_sum]
  unfold projectedDualCoefficientMass
  simp only [hc]
  rw [ha]
  exact finite_residue_tail_energy_le_coefficient_mass n N a

/-- Beyond its finite support, the dual projection error is exactly minus the projected tail. -/
theorem projectedDualError_tail_le_mass (n d N : ℕ) (hd : 0 < d) (hdN : d ≤ N) :
    ‖hilbertTailShift
      (coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)) N‖ ^ 2 ≤
      projectedDualCoefficientMass n d ^ 2 / ((N : ℝ)+1) := by
  have hz : hilbertTailShift (coefficientRiesz d) N = 0 := by
    ext k
    have hs := coefficientRiesz_sequence_zero d (k+N+1) hd (by omega)
    rw [hilbertSequence_succ] at hs
    exact (div_eq_zero_iff.mp hs).resolve_right
      (ne_of_gt (Real.sqrt_pos.mpr (paretoWeight_pos (k+N))))
  change ‖hilbertTailShiftLinear N
    (coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d))‖ ^ 2 ≤ _
  rw [map_sub]
  change ‖hilbertTailShift (coefficientRiesz d) N -
    hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) N‖ ^ 2 ≤ _
  rw [hz, zero_sub, norm_neg]
  exact projectedDualTail_any_cutoff_le_mass n d N

/-- An unconditional finite bound for every threshold pairing of the dual
projection error. All tails and conductor requirements remain explicit. -/
theorem projectedDualError_dilation_pairing_sq_le
    (n d N m : ℕ) (hd : 0 < d) (hdN : d ≤ N) (hm : 0 < m)
    (hcut : m * (N+1) ≤ n+1) :
    (inner ℝ (coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d))
      (hilbertDilation m hm hilbertOne)) ^ 2 ≤
      (m : ℝ) * projectedDualCoefficientMass n d ^ 2 * ‖tailError N‖ ^ 2 / ((N : ℝ)+1) := by
  let q := coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)
  have ho : inner ℝ q (hilbertDilation m hm (canonicalMobiusHilbert N)) = 0 :=
    Submodule.starProjection_inner_eq_zero (coefficientRiesz d) _
      (canonicalMobiusHilbert_dilation_mem_finiteSpace n N m hm hcut)
  have he : inner ℝ q (hilbertDilation m hm (tailError N)) =
      inner ℝ q (hilbertDilation m hm hilbertOne) := by
    change inner ℝ q ((hilbertDilationContinuous m hm)
      (hilbertOne - canonicalMobiusHilbert N)) = _
    rw [map_sub, inner_sub_right]
    change inner ℝ q (hilbertDilation m hm hilbertOne) -
      inner ℝ q (hilbertDilation m hm (canonicalMobiusHilbert N)) = _
    rw [ho, sub_zero]
  have hz : ∀ k < N, hilbertDilation m hm (tailError N) k = 0 := by
    intro k hk
    have hs : hilbertSequence (hilbertDilation m hm (tailError N)) (k+1) = 0 := by
      rw [hilbertDilation_sequence]
      change (m : ℝ) * hilbertSequence (tailError N) ((k+1)/m) = 0
      by_cases hj : (k+1)/m = 0
      · simp [hj, hilbertSequence_zero]
      · rw [tailError_head N ((k+1)/m) (Nat.pos_of_ne_zero hj)
          ((Nat.div_le_self (k+1) m).trans (by omega)), mul_zero]
    rw [hilbertSequence_succ] at hs
    exact (div_eq_zero_iff.mp hs).resolve_right
      (ne_of_gt (Real.sqrt_pos.mpr (paretoWeight_pos k)))
  have hc := hilbertTailShift_inner_sq_le q (hilbertDilation m hm (tailError N)) N hz
  rw [he, hilbertDilation_norm_sq] at hc
  calc
    _ ≤ ‖hilbertTailShift q N‖ ^ 2 * ((m : ℝ) * ‖tailError N‖ ^ 2) := hc
    _ ≤ (projectedDualCoefficientMass n d ^ 2 / ((N : ℝ)+1)) *
        ((m : ℝ) * ‖tailError N‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (projectedDualError_tail_le_mass n d N hd hdN)
        (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg _))
    _ = _ := by ring


/-- Exact short threshold synthesis of the second coefficient dual. -/
theorem coefficientRiesz_two_eq_dilations :
    coefficientRiesz 2 = (4 : ℝ) • hilbertOne -
      (5 : ℝ) • hilbertDilation 2 (by decide) hilbertOne +
      (2 : ℝ) • hilbertDilation 3 (by decide) hilbertOne := by
  unfold coefficientRiesz
  apply hilbertSequence_injective
  change hilbertSequenceLinear (-mobiusRieszHilbert 2) =
    hilbertSequenceLinear (_ + _)
  simp only [map_neg, map_sub, map_smul, map_add]
  change -hilbertSequence (mobiusRieszHilbert 2) =
    (4 : ℝ) • hilbertSequence hilbertOne -
      (5 : ℝ) • hilbertSequence (hilbertDilation 2 (by decide) hilbertOne) +
      (2 : ℝ) • hilbertSequence (hilbertDilation 3 (by decide) hilbertOne)
  rw [hilbertDilation_sequence, hilbertDilation_sequence, hilbertOne_sequence]
  funext j
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
    mobiusRieszHilbert_sequence 2 j (by decide)]
  by_cases hj : j ≤ 2
  · interval_cases j <;> norm_num [dualCoeff, dilation, zeroAnchor,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  · have h2 : 2 < j := by omega
    have hz : j ≠ 0 := by omega
    have hd2 : j / 2 ≠ 0 := by omega
    have hd3 : j / 3 ≠ 0 := by omega
    simp [dualCoeff_eq_zero_of_lt (by decide : 0 < 2) h2,
      dilation, zeroAnchor, hz, hd2, hd3] <;> norm_num

/-- Exact short threshold synthesis of the third coefficient dual. -/
theorem coefficientRiesz_three_eq_dilations :
    coefficientRiesz 3 = (2 : ℝ) • hilbertOne +
      (2 : ℝ) • hilbertDilation 2 (by decide) hilbertOne -
      (6 : ℝ) • hilbertDilation 3 (by decide) hilbertOne +
      (3 : ℝ) • hilbertDilation 4 (by decide) hilbertOne := by
  unfold coefficientRiesz
  apply hilbertSequence_injective
  change hilbertSequenceLinear (-mobiusRieszHilbert 3) =
    hilbertSequenceLinear (_ + _)
  simp only [map_neg, map_sub, map_smul, map_add]
  change -hilbertSequence (mobiusRieszHilbert 3) =
    (2 : ℝ) • hilbertSequence hilbertOne +
      (2 : ℝ) • hilbertSequence (hilbertDilation 2 (by decide) hilbertOne) -
      (6 : ℝ) • hilbertSequence (hilbertDilation 3 (by decide) hilbertOne) +
      (3 : ℝ) • hilbertSequence (hilbertDilation 4 (by decide) hilbertOne)
  rw [hilbertDilation_sequence, hilbertDilation_sequence,
    hilbertDilation_sequence, hilbertOne_sequence]
  funext j
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
    mobiusRieszHilbert_sequence 3 j (by decide)]
  by_cases hj : j ≤ 3
  · interval_cases j <;> norm_num [dualCoeff, dilation, zeroAnchor,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  · have h3 : 3 < j := by omega
    have hz : j ≠ 0 := by omega
    have hd2 : j / 2 ≠ 0 := by omega
    have hd3 : j / 3 ≠ 0 := by omega
    have hd4 : j / 4 ≠ 0 := by omega
    simp [dualCoeff_eq_zero_of_lt (by decide : 0 < 3) h3,
      dilation, zeroAnchor, hz, hd2, hd3, hd4] <;> norm_num

/-- Orthogonal projection turns pairing with the target into squared error. -/
theorem projectedDualError_inner_self (n d : ℕ) :
    inner ℝ (coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d))
      (coefficientRiesz d) =
      ‖coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d)‖ ^ 2 := by
  have ho := Submodule.starProjection_inner_eq_zero (coefficientRiesz d)
    ((finiteSpace n).starProjection (coefficientRiesz d))
    ((finiteSpace n).starProjection_apply_mem _)
  have h := real_inner_self_eq_norm_sq
    (coefficientRiesz d - (finiteSpace n).starProjection (coefficientRiesz d))
  rw [inner_sub_right, ho, sub_zero] at h
  exact h

/-- Small mass would force fast approximation of the actual second dual. -/
theorem projectedDualError_two_fourth_le_mass (n N : ℕ)
    (hN : 2 ≤ N) (hcut : 3 * (N+1) ≤ n+1) :
    ‖coefficientRiesz 2 - (finiteSpace n).starProjection (coefficientRiesz 2)‖ ^ 4 ≤
      270 * projectedDualCoefficientMass n 2 ^ 2 * ‖tailError N‖ ^ 2 / ((N:ℝ)+1) := by
  let q := coefficientRiesz 2 - (finiteSpace n).starProjection (coefficientRiesz 2)
  let x := inner ℝ q hilbertOne
  let y := inner ℝ q (hilbertDilation 2 (by decide) hilbertOne)
  let z := inner ℝ q (hilbertDilation 3 (by decide) hilbertOne)
  let W := projectedDualCoefficientMass n 2 ^ 2 * ‖tailError N‖ ^ 2 / ((N:ℝ)+1)
  have hx : x^2 ≤ W := by
    simpa only [hilbertDilation_one, Nat.cast_one, one_mul] using
      projectedDualError_dilation_pairing_sq_le n 2 N 1 (by decide) hN (by decide) (by omega)
  have hy : y^2 ≤ 2 * W := by
    have h := projectedDualError_dilation_pairing_sq_le n 2 N 2
      (by decide) hN (by decide) (by omega)
    dsimp [W, y, q]
    convert h using 1 <;> push_cast <;> ring
  have hz : z^2 ≤ 3 * W := by
    have h := projectedDualError_dilation_pairing_sq_le n 2 N 3
      (by decide) hN (by decide) hcut
    dsimp [W, z, q]
    convert h using 1 <;> push_cast <;> ring
  have he : ‖q‖^2 = 4*x-5*y+2*z := by
    have h := congrArg (fun f => inner ℝ q f) coefficientRiesz_two_eq_dilations
    simp only [inner_add_right, inner_sub_right, inner_smul_right] at h
    rw [projectedDualError_inner_self] at h
    exact h
  have hc : (4*x-5*y+2*z)^2 ≤ 45 * (x^2+y^2+z^2) := by
    nlinarith [sq_nonneg (5*x+4*y), sq_nonneg (2*x-4*z), sq_nonneg (2*y+5*z)]
  have hp : ‖q‖^4 = (‖q‖^2)^2 := by ring
  have hb : ‖q‖^4 ≤ 270 * W := by
    rw [hp, he]
    nlinarith
  calc
    _ ≤ 270 * W := hb
    _ = _ := by dsimp [W]; ring

/-- The same quantitative statement for the third dual, with an explicit constant. -/
theorem projectedDualError_three_fourth_le_mass (n N : ℕ)
    (hN : 3 ≤ N) (hcut : 4 * (N+1) ≤ n+1) :
    ‖coefficientRiesz 3 - (finiteSpace n).starProjection (coefficientRiesz 3)‖ ^ 4 ≤
      530 * projectedDualCoefficientMass n 3 ^ 2 * ‖tailError N‖ ^ 2 / ((N:ℝ)+1) := by
  let q := coefficientRiesz 3 - (finiteSpace n).starProjection (coefficientRiesz 3)
  let x := inner ℝ q hilbertOne
  let y := inner ℝ q (hilbertDilation 2 (by decide) hilbertOne)
  let z := inner ℝ q (hilbertDilation 3 (by decide) hilbertOne)
  let t := inner ℝ q (hilbertDilation 4 (by decide) hilbertOne)
  let W := projectedDualCoefficientMass n 3 ^ 2 * ‖tailError N‖ ^ 2 / ((N:ℝ)+1)
  have hx : x^2 ≤ W := by
    simpa only [hilbertDilation_one, Nat.cast_one, one_mul] using
      projectedDualError_dilation_pairing_sq_le n 3 N 1 (by decide) hN (by decide) (by omega)
  have hy : y^2 ≤ 2 * W := by
    have h := projectedDualError_dilation_pairing_sq_le n 3 N 2
      (by decide) hN (by decide) (by omega)
    dsimp [W, y, q]
    convert h using 1 <;> push_cast <;> ring
  have hz : z^2 ≤ 3 * W := by
    have h := projectedDualError_dilation_pairing_sq_le n 3 N 3
      (by decide) hN (by decide) (by omega)
    dsimp [W, z, q]
    convert h using 1 <;> push_cast <;> ring
  have ht : t^2 ≤ 4 * W := by
    have h := projectedDualError_dilation_pairing_sq_le n 3 N 4
      (by decide) hN (by decide) hcut
    dsimp [W, t, q]
    convert h using 1 <;> push_cast <;> ring
  have he : ‖q‖^2 = 2*x+2*y-6*z+3*t := by
    have h := congrArg (fun f => inner ℝ q f) coefficientRiesz_three_eq_dilations
    simp only [inner_add_right, inner_sub_right, inner_smul_right] at h
    rw [projectedDualError_inner_self] at h
    exact h
  have hc : (2*x+2*y-6*z+3*t)^2 ≤ 53*(x^2+y^2+z^2+t^2) := by
    nlinarith [sq_nonneg (2*x-2*y), sq_nonneg (6*x+2*z),
      sq_nonneg (3*x-2*t), sq_nonneg (6*y+2*z), sq_nonneg (3*y-2*t),
      sq_nonneg (3*z+6*t)]
  have hp : ‖q‖^4 = (‖q‖^2)^2 := by ring
  have hb : ‖q‖^4 ≤ 530 * W := by
    rw [hp, he]
    nlinarith
  calc
    _ ≤ 530 * W := hb
    _ = _ := by dsimp [W]; ring


end CorrectionTail
end RiemannResearch.RH.Pareto.CoefficientStabilization
