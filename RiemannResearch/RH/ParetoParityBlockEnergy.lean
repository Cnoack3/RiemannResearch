import RiemannResearch.RH.ParetoFullContrastEnergy
import RiemannResearch.RH.DyadicKernelJumpEnergy

/-!
# Exact identification of the full remaining parity energy

Source: the user's Pareto parity-closure supplement, 21 September 2026,
for the geometric statement; the proof reuses the project's dyadic kernel identity.

The infinite contrast sum is identified with the genuine dyadic kernel
projection.  For a vector with zero first coordinate, its complementary
energy is exactly twice the full norm of its half-adjoint block means.
This does not make the remaining legal approximation estimate automatic.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization.TailCapacity

private theorem fullOddPairContrast_summand_odd (f : ThresholdHilbert) (n : ℕ) :
    coprimePairMass 2 (2*(n+1)+1) *
      (inner ℝ (differenceCertificate (2*(n+1)+1-2)) f)^2/2 =
    (hilbertSequence f (2*(n+1)+1)-hilbertSequence f (2*(n+1)))^2 /
      (2*(2*((n : ℝ)+1)+1)^2) := by
  have hp : coprimePairIndex 2 (2*(n+1)+1) := by
    refine ⟨by omega, by omega, ?_⟩
    exact ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)).symm
  rw [coprimePairMass, if_pos hp, differenceCertificate_inner,
    hilbertGibbsPhysical_eq, hilbertGibbsPhysical_eq]
  rw [show 2*(n+1)+1-2+1+1=2*(n+1)+1 by omega,
    show 2*(n+1)+1-2+1=2*(n+1) by omega]
  push_cast
  field_simp

theorem fullOddPairContrastEnergy_eq_jump_series (f : ThresholdHilbert) :
    fullOddPairContrastEnergy f =
    ∑' n : ℕ,
      (hilbertSequence f (2*(n+1)+1)-hilbertSequence f (2*(n+1)))^2 /
        (2*(2*((n : ℝ)+1)+1)^2) := by
  unfold fullOddPairContrastEnergy
  let jump : ℕ → ℝ := fun n =>
    (hilbertSequence f (2*(n+1)+1)-hilbertSequence f (2*(n+1)))^2 /
      (2*(2*((n : ℝ)+1)+1)^2)
  change (∑' p, coprimePairMass 2 p *
    (inner ℝ (differenceCertificate (p-2)) f)^2/2) = ∑' n, jump n
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun a : Function.support jump => 2*(a.val+1)+1)
  · intro a b hab
    apply Subtype.ext
    change 2*(a.val+1)+1=2*(b.val+1)+1 at hab
    omega
  · intro p hp
    have hi : coprimePairIndex 2 p := by
      by_contra hi
      simpa only [Function.mem_support, coprimePairMass, if_neg hi,
        zero_mul, zero_div, ne_eq, not_true_eq_false] using hp
    have hp3 := hi.1
    have hpo := hi.2.1
    have hpn : 2*((p-3)/2+1)+1=p := by omega
    refine ⟨⟨(p-3)/2, ?_⟩, hpn⟩
    change jump ((p-3)/2) ≠ 0
    dsimp only [jump]
    rw [← fullOddPairContrast_summand_odd, hpn]
    exact hp
  · intro a
    exact fullOddPairContrast_summand_odd f a.val

theorem dyadicKernelDefect_norm_sq_eq_fullOddPairContrast (f : ThresholdHilbert) :
    ‖dyadicKernelDefect f‖^2 =
      (hilbertSequence f 1)^2/2 + fullOddPairContrastEnergy f := by
  rw [dyadicKernelDefect_norm_sq_jumps, fullOddPairContrastEnergy_eq_jump_series]

/-- Exact geometric meaning of the complete complementary energy. -/
theorem fullParityRemainingEnergy_eq_blockProjection (f : ThresholdHilbert) :
    fullParityRemainingEnergy f = (hilbertSequence f 1)^2/2 +
      ‖hilbertBlockProjection 2 (by norm_num) f‖^2 := by
  have hp := hilbertBlockProjection_pythagoras 2 (by norm_num) f
  have hk := dyadicKernelDefect_norm_sq_eq_fullOddPairContrast f
  rw [dyadicKernelDefect_apply] at hk
  unfold fullParityRemainingEnergy
  linarith

theorem dyadic_blockProjection_norm_sq (f : ThresholdHilbert) :
    ‖hilbertBlockProjection 2 (by norm_num) f‖^2 =
      2*‖dyadicHalfAdjoint f‖^2 := by
  rw [hilbertBlockProjection_apply, dyadicHalfAdjoint_apply,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, hilbertDilation_norm_sq]
  norm_num
  ring

/-- At zero first coordinate the still-open energy is precisely the full
block-mean norm, with its exact scale multiplier two. -/
theorem fullParityRemainingEnergy_eq_halfAdjoint (f : ThresholdHilbert)
    (hfirst : hilbertSequence f 1 = 0) :
    fullParityRemainingEnergy f = 2*‖dyadicHalfAdjoint f‖^2 := by
  rw [fullParityRemainingEnergy_eq_blockProjection, hfirst,
    zero_pow (by omega : 2 ≠ 0), zero_div, zero_add,
    dyadic_blockProjection_norm_sq]

theorem zero_head_fullParity_energy_completion (f : ThresholdHilbert)
    (hfirst : hilbertSequence f 1 = 0) :
    ‖f‖^2 = fullOddPairContrastEnergy f + 2*‖dyadicHalfAdjoint f‖^2 := by
  rw [fullParity_energy_completion, fullParityRemainingEnergy_eq_halfAdjoint f hfirst]

end RiemannResearch.RH.Pareto
