import RiemannResearch.RH.ParetoParityAdjointCriterion
import RiemannResearch.RH.FiniteEndpointGram
import Mathlib.NumberTheory.ZetaValues

/-! # Moments of the physical dyadic parity adjoint

The mean and squared norm of the profile are explicit. The isometric image projection identity expresses the energy in an arbitrary dyadic tail. -/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

def dyadicMomentProfile : ThresholdHilbert := hilbertOne - (2 : ℝ) • parityAdjointPacket

theorem dyadicMomentProfile_coordinate {n : ℕ} (hn : n ≠ 0) :
    hilbertSequence dyadicMomentProfile n = 1 / (2 * (n : ℝ) + 1) := by
  rw [dyadicMomentProfile, hilbertSequence_sub, hilbertSequence_smul,
    hilbertOne_sequence]
  change (if n = 0 then 0 else (1 : ℝ)) - 2 * hilbertSequence parityAdjointPacket n = _
  rw [if_neg hn, parityAdjointPacket_coordinate]
  field_simp
  ring

theorem dyadicMomentProfile_mean :
    inner ℝ dyadicMomentProfile hilbertOne = 3 - 4 * Real.log 2 := by
  let p := ramanujanPacketHilbert 2
  have hp : inner ℝ p hilbertOne = Real.log 2 := by
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
  have hat : inner ℝ (hilbertAtom 1 (by decide)) p = 1/2 := by
    rw [hilbertAtom_inner]
    change positiveWeight 1 * hilbertSequence (ramanujanPacketHilbert 2) 1 = 1 / 2
    rw [hilbertSequence_ramanujanPacketHilbert, ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
    norm_num [positiveWeight, residue]
  have hd : hilbertDilation 2 (by decide) hilbertOne =
      (2 : ℝ) • (hilbertOne - hilbertAtom 1 (by decide)) := by
    apply hilbertSequence_injective
    rw [hilbertDilation_sequence, hilbertSequence_smul, hilbertSequence_sub,
        hilbertOne_sequence, hilbertAtom_sequence]
    funext n
    change 2 * (if n/2 = 0 then 0 else (1 : ℝ)) =
      2 * ((if n = 0 then 0 else (1 : ℝ)) - (if n = 1 then 1 else 0))
    split_ifs <;> first | omega | norm_num
  have hm : inner ℝ hilbertOne parityAdjointPacket = 2*(Real.log 2-1/2) := by
    change inner ℝ hilbertOne ((hilbertDilationContinuous 2 (by decide)).adjoint p) = _
    rw [ContinuousLinearMap.adjoint_inner_right, hilbertDilationContinuous_apply, hd,
        real_inner_smul_left, inner_sub_left, hat,
        (real_inner_comm _ _ : inner ℝ hilbertOne p = inner ℝ p hilbertOne), hp]
  rw [dyadicMomentProfile, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hilbertOne_norm_sq,
      (real_inner_comm _ _ : inner ℝ parityAdjointPacket hilbertOne =
        inner ℝ hilbertOne parityAdjointPacket), hm]
  ring

private theorem oddSquares :
    HasSum (fun n : ℕ => 1 / ((2 : ℝ) * n + 1)^2) (Real.pi^2/8) := by
  let f : ℕ → ℝ := fun n => 1/(n:ℝ)^2
  have hfull : HasSum f (Real.pi^2/6) := hasSum_zeta_two
  have he := hfull.summable.comp_injective (i := fun k : ℕ => 2*k)
    (by intro a b h; change 2*a = 2*b at h; omega)
  have ho := hfull.summable.comp_injective (i := fun k : ℕ => 2*k+1)
    (by intro a b h; change 2*a+1 = 2*b+1 at h; omega)
  have hev : (∑' k : ℕ, f (2*k)) = Real.pi^2/24 := by
    have hfun : (fun k : ℕ => f (2*k)) = fun k => 1/4 * f k := by
      funext k
      simp [f, mul_pow]
      ring
    rw [hfun,tsum_mul_left,hfull.tsum_eq]
    ring
  have h := tsum_even_add_odd (f := f) he ho
  rw [hev, hfull.tsum_eq] at h
  have hov : (∑' k : ℕ, f (2*k+1)) = Real.pi^2/8 := by linarith
  have hh : HasSum (fun k : ℕ => f (2*k+1)) (Real.pi^2/8) := hov ▸ ho.hasSum
  simpa [f, Function.comp_def] using hh

theorem dyadicMomentProfile_second :
    ‖dyadicMomentProfile‖^2 = 5 - Real.pi^2/2 := by
  let c : ℕ → ℝ := fun n => if n = 0 then 4 else 0
  have hc : HasSum c 4 := by
    simpa [c] using (hasSum_ite_eq (0 : ℕ) (4 : ℝ))
  have hh := (positiveWeight_summable.hasSum.sub (oddSquares.mul_left 4)).add hc
  rw [positiveWeight_tsum] at hh
  rw [hilbert_norm_weighted_sq]
  have hfun : (fun n => positiveWeight n * hilbertSequence dyadicMomentProfile n ^ 2) =
      (fun n => positiveWeight n - 4 * (1 / ((2 : ℝ)*n+1)^2) + c n) := by
    funext n
    by_cases hn : n = 0
    · subst n
      norm_num [positiveWeight,c]
    · rw [dyadicMomentProfile_coordinate hn]
      simp only [c,if_neg hn,add_zero,positiveWeight]
      have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      field_simp <;> ring
  rw [hfun]
  calc
    _ = 1 - 4 * (Real.pi^2 / 8) + 4 := hh.tsum_eq
    _ = _ := by ring

/-- The first two moments of the reciprocal profile determine the squared
norm of the uncentered adjoint parity packet exactly. -/
theorem parityAdjointPacket_norm_sq :
    ‖parityAdjointPacket‖^2 = 2*Real.log 2 - Real.pi^2/8 := by
  have hmean := dyadicMomentProfile_mean
  rw [dyadicMomentProfile,inner_sub_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,hilbertOne_norm_sq] at hmean
  have hnorm := dyadicMomentProfile_second
  rw [dyadicMomentProfile,norm_sub_sq_real,hilbertOne_norm_sq,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),mul_pow,
    real_inner_smul_right] at hnorm
  linarith only [hmean, hnorm, real_inner_comm hilbertOne parityAdjointPacket]

/-- Subtracting any doubled ambient vector from parity off the first site
has an explicit positive cost. Equality is attained at one half of the
adjoint parity packet. -/
theorem parity_off_first_site_dyadic_distance (v : ThresholdHilbert) :
    ‖(ramanujanPacketHilbert 2 - paretoPointHilbert 0) - doubleDilation v‖^2 =
      Real.pi^2/16 - 1/2 + 2*‖v - (1/2 : ℝ) • parityAdjointPacket‖^2 := by
  have hfirst : hilbertSequence (ramanujanPacketHilbert 2) 1 = 1 := by
    rw [hilbertSequence_ramanujanPacketHilbert, ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
    norm_num [residue]
  have hq : ‖ramanujanPacketHilbert 2 - paretoPointHilbert 0‖^2 = Real.log 2-1/2 := by
    simpa only [hfirst,one_smul,one_pow,ramanujanPacketHilbert_two_norm_sq] using
      remove_firstPoint_norm_sq (ramanujanPacketHilbert 2)
  have hd : ‖doubleDilation v‖^2 = 2*‖v‖^2 := by
    rw [← real_inner_self_eq_norm_sq, doubleDilation_inner, real_inner_self_eq_norm_sq]
  have hp : inner ℝ (paretoPointHilbert 0) (doubleDilation v) = 0 :=
    (real_inner_comm ..).trans (doubleDilation_inner_firstPoint _)
  have hqv : inner ℝ (ramanujanPacketHilbert 2 - paretoPointHilbert 0) (doubleDilation v) =
      inner ℝ v parityAdjointPacket := by
    rw [inner_sub_left,hp,sub_zero,real_inner_comm]
    exact (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous 2 (by decide))
      v (ramanujanPacketHilbert 2)).symm
  rw [norm_sub_sq_real, hq,hd,hqv,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2),mul_pow,parityAdjointPacket_norm_sq,
    real_inner_smul_right]
  ring

/-- The exact dyadic cost floor is positive, uniformly over the full ambient space. -/
theorem parity_off_first_site_dyadic_floor (v : ThresholdHilbert) :
    0 < Real.pi^2/16 - 1/2 ∧ Real.pi^2/16 - 1/2 ≤
      ‖(ramanujanPacketHilbert 2 - paretoPointHilbert 0) - doubleDilation v‖^2 := by
  constructor
  · nlinarith only [mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 3) Real.pi_gt_three]
  · rw [parity_off_first_site_dyadic_distance]
    linarith only [sq_nonneg ‖v - (1/2 : ℝ) • parityAdjointPacket‖]

/-- The ambient projection to any isometric image can be computed by pulling
the input back by the adjoint, projecting, and applying the isometry. -/
theorem starProjection_isometric_image
    (S : ThresholdHilbert →ₗᵢ[ℝ] ThresholdHilbert)
    (K : Submodule ℝ ThresholdHilbert) [K.HasOrthogonalProjection]
    [(K.map S.toLinearMap).HasOrthogonalProjection] (z : ThresholdHilbert) :
    (K.map S.toLinearMap).starProjection z =
      S (K.starProjection (S.toContinuousLinearMap.adjoint z)) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨_, K.starProjection_apply_mem _, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    change inner ℝ (z - S (K.starProjection (S.toContinuousLinearMap.adjoint z))) (S w) = 0
    rw [inner_sub_left, S.inner_map_map]
    have h := Submodule.starProjection_inner_eq_zero
      (K := K) (S.toContinuousLinearMap.adjoint z) w hw
    rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left] at h
    exact h

theorem norm_starProjection_isometric_image
    (S : ThresholdHilbert →ₗᵢ[ℝ] ThresholdHilbert)
    (K : Submodule ℝ ThresholdHilbert) [K.HasOrthogonalProjection]
    [(K.map S.toLinearMap).HasOrthogonalProjection] (z : ThresholdHilbert) :
    ‖(K.map S.toLinearMap).starProjection z‖ =
      ‖K.starProjection (S.toContinuousLinearMap.adjoint z)‖ := by
  rw [starProjection_isometric_image, S.norm_map]

#print axioms dyadicMomentProfile_mean
#print axioms dyadicMomentProfile_second
#print axioms starProjection_isometric_image

end RiemannResearch.RH.Pareto.PrimePowerSchur
