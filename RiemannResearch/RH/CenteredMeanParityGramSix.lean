import RiemannResearch.RH.DyadicParityGramRow
import RiemannResearch.RH.ParetoParityAdjointSix
import RiemannResearch.RH.ScreenedPrimePowerTelescope

/-! # Three signed Gram observations and the conductor-six correction

The doubled mixed conductor six is orthogonal to both the optimal projection
direction and the Gram remainder. Its nonzero parity correlation separates the
three-coordinate Gram determinant strictly from zero whenever the residual
energy is positive. The finite test evaluates the limiting polynomial on
three observed coordinates from one inverse Gram vector. The two-stage
physical remainder carries its own finite correlation identity.
-/

noncomputable section
open Filter
open scoped Topology Matrix
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The Schur complement inequality, cleared of denominators. -/
def projectedParityGramDefect (e b B : ℝ) : ℝ :=
  let L := Real.log 2 - 1/2
  e * firstSiteGramGap e b * (2*(1-e)*L-(2*L-B)^2) - (1-e)*(e*b+(2*e-b)*B)^2

/-- A single mean-zero mixed packet certifies positive capture of the
dyadic parity adjoint in the complete mixed subspace. -/
theorem parityAdjointPacket_mixed_capture_lower :
    (2*Real.log 2-(1-1/Real.sqrt 3)*Real.pi)^2/(Real.pi/Real.sqrt 3) ≤
      ‖mixedClosure.starProjection parityAdjointPacket‖^2 := by
  let v := mixedClosure.starProjection parityAdjointPacket
  have ho := Submodule.inner_right_of_mem_orthogonal
    (mixed_packet_mem_closure 6 (by decide) (by decide))
    (Submodule.sub_starProjection_mem_orthogonal (K:=mixedClosure) parityAdjointPacket)
  change inner ℝ (ramanujanPacketHilbert 6) (parityAdjointPacket-v) = 0 at ho
  rw [inner_sub_right,parityAdjointPacket_inner_six,sub_eq_zero] at ho
  have h := RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le (ramanujanPacketHilbert 6) v
  rw [← ho,packet_two_six_inner_and_norm.2] at h
  exact (div_le_iff₀ (show 0 < Real.pi/Real.sqrt 3 by positivity)).mpr
    (h.trans_eq (mul_comm _ _))

theorem parityAdjointPacket_mixed_projection_ne_zero :
    mixedClosure.starProjection parityAdjointPacket ≠ 0 := by
  intro h
  have hc := parityAdjointPacket_mixed_capture_lower
  rw [h,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hc
  have hp := parityAdjointPacket_inner_six_pos
  rw [parityAdjointPacket_inner_six] at hp
  exact (not_le_of_gt (div_pos (sq_pos_of_pos hp) (by positivity))) hc

/-- The full mixed capture cannot exceed the whole mean-zero variance. -/
theorem parityAdjointPacket_mixed_capture_upper :
    ‖mixedClosure.starProjection parityAdjointPacket‖^2 ≤
      2*Real.log 2-Real.pi^2/8-(2*Real.log 2-1)^2 := by
  let m := 2*Real.log 2-1
  have hm : inner ℝ parityAdjointPacket hilbertOne = m := by
    have h := dyadicMomentProfile_mean
    rw [dyadicMomentProfile,inner_sub_left,real_inner_smul_left,
      real_inner_self_eq_norm_sq,hilbertOne_norm_sq] at h
    dsimp only [m]; linarith only [h]
  have hz : mixedClosure.starProjection hilbertOne = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr one_mem_mixedClosure_orthogonal
  have h := mixedClosure.norm_starProjection_apply_le (parityAdjointPacket-m • hilbertOne)
  rw [map_sub,map_smul,hz,smul_zero,sub_zero] at h
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
  rw [norm_sub_sq_real,parityAdjointPacket_norm_sq,real_inner_smul_right,hm,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hilbertOne_norm_sq] at hs
  change _ ≤ 2*Real.log 2-Real.pi^2/8-m^2
  linarith only [hs]

/-- Conductor six alone captures strictly more than half of the entire
ambient mean-zero variance of the parity adjoint. -/
theorem parityAdjointPacket_six_captures_half_variance :
    (2*Real.log 2-Real.pi^2/8-(2*Real.log 2-1)^2)/2 <
      (inner ℝ (ramanujanPacketHilbert 6) parityAdjointPacket)^2 / ‖ramanujanPacketHilbert 6‖^2 := by
  rw [parityAdjointPacket_inner_six,packet_two_six_inner_and_norm.2]
  let l := Real.log 2
  let p := Real.pi
  let s := Real.sqrt 3
  let T := 2*l-(1-1/s)*p
  let V := 2*l-p^2/8-(2*l-1)^2
  have hl : (69314/100000:ℝ) ≤ l ∧ l ≤ 69315/100000 := by
    dsimp [l]; constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9]
  have hp : (31415/10000:ℝ) ≤ p ∧ p ≤ 31416/10000 := by
    dsimp [p]; constructor <;> linarith only [Real.pi_gt_d20,Real.pi_lt_d20]
  have hs : (1732/1000:ℝ) ≤ s ∧ s ≤ 1733/1000 :=
    ⟨(Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num),
      Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩⟩
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hi : (1000/1733:ℝ) ≤ 1/s := by
    apply (le_div_iff₀ hs0).mpr
    linarith only [hs.2]
  have hprod := (mul_le_mul_of_nonneg_right
    (show 1-1/s ≤ 1-1000/1733 by linarith only [hi]) Real.pi_pos.le).trans
    (mul_le_mul_of_nonneg_left hp.2 (by norm_num : (0:ℝ) ≤ 1-1000/1733))
  have ht : (57/1000:ℝ) < T := by dsimp [T]; linarith only [hl.1,hprod]
  have hsq₁ := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 31415/10000) Real.pi_pos.le).mpr hp.1
  have hsq₂ := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 2*(69314/100000)-1)
    (by linarith only [hl.1] : 0 ≤ 2*l-1)).mpr (by linarith only [hl.1])
  have hv : V < 7/2000 := by dsimp [V]; linarith only [hl.2,hsq₁,hsq₂]
  have hh : p/s ≤ 182/100 := by
    apply (div_le_iff₀ hs0).mpr
    linarith only [hp.2,hs.1]
  have hh0 : 0 < p/s := div_pos Real.pi_pos hs0
  have hval := (mul_le_mul_of_nonneg_right
    (show V/2 ≤ 7/4000 by linarith only [hv]) hh0.le).trans
    (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 7/4000))
  change V/2 < T^2/(p/s)
  apply (lt_div_iff₀ hh0).mpr
  have hsqt := (sq_lt_sq₀ (by norm_num : (0:ℝ) ≤ 57/1000)
    (by linarith only [ht] : 0 ≤ T)).mpr ht
  linarith only [hval,hsqt]

private theorem projection_inner_mixed {y : ThresholdHilbert} (hy : y ∈ mixedClosure) :
    inner ℝ limitProjection y = 0 := by
  have h := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp hy
  have hr := Submodule.inner_right_of_mem_orthogonal h.1 limitResidual_mem_orthogonal
  rw [limitResidual,inner_sub_right,h.2,zero_sub,neg_eq_zero] at hr
  exact (real_inner_comm ..).trans hr

/-- The signed parity observation of the probe on the doubled mixed packet
does not depend on the coefficient of the optimal projection. -/
theorem firstSiteParityProbe_inner_double_mixed (t : ℝ) {y : ThresholdHilbert} (hy : y ∈ mixedClosure) :
    inner ℝ (firstSiteParityProbe t) (doubleDilation y) = inner ℝ y parityAdjointPacket := by
  have h := ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous 2 (by decide))
    y (ramanujanPacketHilbert 2)
  rw [firstSiteParityProbe,inner_sub_left,inner_sub_left,real_inner_smul_left,doubleDilation_inner,
    projection_inner_mixed hy,mul_zero,mul_zero,sub_zero,
    (real_inner_comm ..).trans (doubleDilation_inner_firstPoint y),
    sub_zero,real_inner_comm]
  exact h.symm

/-- After both signed orthogonal corrections, the unspent part of the
three-coordinate determinant is exactly the remaining Hilbert Gram determinant. -/
theorem limit_projectedParityGramDefect_mixed_identity {y : ThresholdHilbert} (hy : y ∈ mixedClosure)
    (hy0 : y ≠ 0) :
    let E := limitEnergy
    let b := hilbertSequence limitResidual 1
    let B := inner ℝ limitResidual parityAdjointPacket
    let T := inner ℝ y parityAdjointPacket
    let L := Real.log 2 - 1/2
    let z := firstSiteDyadicRemainder limitResidual
    let p := firstSiteParityProbe ((2*L-B)/(2*(1-E))) - (T/(2*‖y‖^2)) • doubleDilation y
    projectedParityGramDefect E b B = (1-E)*E*firstSiteGramGap E b*T^2/‖y‖^2 +
      (1-E)*(‖z‖^2*‖p‖^2 - (inner ℝ z p)^2) := by
  let E := limitEnergy
  let b := hilbertSequence limitResidual 1
  let B := inner ℝ limitResidual parityAdjointPacket
  let T := inner ℝ y parityAdjointPacket
  let G := firstSiteGramGap E b
  let S := E*b+(2*E-b)*B
  let L := Real.log 2-1/2
  let H := ‖y‖^2
  let t := (2*L-B)/(2*(1-E))
  let u := T/(2*H)
  let w := doubleDilation y
  let z := firstSiteDyadicRemainder limitResidual
  have hE : 0 < 1-E := one_sub_limitEnergy_pos
  have hH : 0 < H := sq_pos_of_pos (norm_pos_iff.mpr hy0)
  have hw : ‖w‖^2 = 2*H := by
    rw [← real_inner_self_eq_norm_sq, doubleDilation_inner,real_inner_self_eq_norm_sq]
  have hzw : inner ℝ z w = 0 :=
    firstSiteDyadicRemainder_inner_double_legal (mixedClosure_le_closedSpace hy)
  have hp : inner ℝ z (firstSiteParityProbe t) = -S := (firstSiteParityProbe_pair_and_norm t).1
  have hn : ‖firstSiteParityProbe t‖^2 = L-2*t*(2*L-B)+2*t^2*(1-E) :=
    (firstSiteParityProbe_pair_and_norm t).2
  have hcorr : inner ℝ (firstSiteParityProbe t) w = T := firstSiteParityProbe_inner_double_mixed t hy
  have hpp : inner ℝ z (firstSiteParityProbe t-u • w) = -S := by
    rw [inner_sub_right,real_inner_smul_right,hzw,mul_zero,sub_zero,hp]
  have hnn : ‖firstSiteParityProbe t-u • w‖^2 =
      (L-2*t*(2*L-B)+2*t^2*(1-E))-2*(u*T)+u^2*(2*H) := by
    rw [norm_sub_sq_real,hn,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hw,real_inner_smul_right,hcorr] <;> ring
  have hq : 2*(1-E)*((L-2*t*(2*L-B)+2*t^2*(1-E))-2*(u*T)+u^2*(2*H)) =
      2*(1-E)*L-(2*L-B)^2-(1-E)*T^2/H := by
    dsimp only [t,u]
    field_simp [hE.ne',hH.ne'] <;> ring
  change E*G*(2*(1-E)*L-(2*L-B)^2)-(1-E)*S^2 = (1-E)*E*G*T^2/H +
    (1-E)*(‖firstSiteDyadicRemainder limitResidual‖^2*‖firstSiteParityProbe t-u • w‖^2 -
      (inner ℝ z (firstSiteParityProbe t-u • w))^2)
  rw [limit_firstSiteGramGap_identity,hnn,hpp,neg_sq]
  change E*G*(2*(1-E)*L-(2*L-B)^2)-(1-E)*S^2 = (1-E)*E*G*T^2/H + (1-E)*(2*E*G*_-S^2)
  have hz := congrArg (fun x : ℝ => E*G*x) hq
  linear_combination -hz

/-- Every mean-zero legal packet provides a quantitative lower bound on the
three-coordinate determinant, through its squared normalized parity correlation. -/
theorem limit_projectedParityGramDefect_ge_mixed {y : ThresholdHilbert} (hy : y ∈ mixedClosure)
    (hy0 : y ≠ 0) :
    let E := limitEnergy
    let b := hilbertSequence limitResidual 1
    let B := inner ℝ limitResidual parityAdjointPacket
    let T := inner ℝ y parityAdjointPacket
    (1-E)*E*firstSiteGramGap E b*T^2/‖y‖^2 ≤ projectedParityGramDefect E b B := by
  have he := one_sub_limitEnergy_pos
  have h := limit_projectedParityGramDefect_mixed_identity hy hy0
  dsimp only at h ⊢
  rw [h]
  exact le_add_of_nonneg_right (mul_nonneg he.le
    (sub_nonneg.mpr (RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le _ _)))

/-- The explicit mixed-conductor certificate. -/
theorem limit_projectedParityGramDefect_ge_six :
    let E := limitEnergy
    let b := hilbertSequence limitResidual 1
    let B := inner ℝ limitResidual parityAdjointPacket
    let T := inner ℝ (ramanujanPacketHilbert 6) parityAdjointPacket
    (1-E)*E*firstSiteGramGap E b*T^2/(Real.pi/Real.sqrt 3) ≤ projectedParityGramDefect E b B := by
  have hy : ramanujanPacketHilbert 6 ≠ 0 := by
    intro hz
    simpa [hz] using parityAdjointPacket_inner_six_pos
  simpa only [packet_two_six_inner_and_norm.2] using
    limit_projectedParityGramDefect_ge_mixed (mixed_packet_mem_closure 6 (by decide) (by decide)) hy

/-- Projection onto the complete mixed space takes the optimal normalized
correlation in the family of all mixed vectors. -/
theorem limit_projectedParityGramDefect_ge_mixed_projection :
    let E := limitEnergy
    let b := hilbertSequence limitResidual 1
    let B := inner ℝ limitResidual parityAdjointPacket
    (1-E)*E*firstSiteGramGap E b * ‖mixedClosure.starProjection parityAdjointPacket‖^2 ≤
      projectedParityGramDefect E b B := by
  let y := mixedClosure.starProjection parityAdjointPacket
  have hy : y ∈ mixedClosure := mixedClosure.starProjection_apply_mem _
  have hr := Submodule.inner_right_of_mem_orthogonal hy
    (mixedClosure.sub_starProjection_mem_orthogonal parityAdjointPacket)
  have hp : inner ℝ y parityAdjointPacket = ‖y‖^2 := by
    change inner ℝ y (parityAdjointPacket-y) = 0 at hr
    simpa only [inner_sub_right,real_inner_self_eq_norm_sq,sub_eq_zero] using hr
  have hy0 : y ≠ 0 := parityAdjointPacket_mixed_projection_ne_zero
  have h := limit_projectedParityGramDefect_ge_mixed hy hy0
  dsimp only at h ⊢
  rw [hp] at h
  have hh : ‖y‖^2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hy0)).ne'
  convert h using 1
  change _ * ‖y‖^2 = _ * (‖y‖^2)^2 / ‖y‖^2
  field_simp [hh]

theorem limit_projectedParityGramDefect_pos (hE : 0 < limitEnergy) :
    0 < projectedParityGramDefect limitEnergy (hilbertSequence limitResidual 1)
      (inner ℝ limitResidual parityAdjointPacket) := by
  have hL : 0 < Real.log 2-1/2 := by linarith [Real.log_two_gt_d9]
  have hG : 0 < firstSiteGramGap limitEnergy (hilbertSequence limitResidual 1) :=
    pos_of_mul_pos_right
      ((show 0 ≤ firstSiteParitySeparation^2/2*limitEnergy^3 from by positivity).trans_lt
        (limit_firstSiteGramGap_coupled_strict hE)) hL.le
  have hP := one_sub_limitEnergy_pos
  have hT := parityAdjointPacket_inner_six_pos
  apply lt_of_lt_of_le _ limit_projectedParityGramDefect_ge_six
  positivity

namespace CenteredMeanSnake
open MixedConductorBasis
open scoped LegalMeanAlgebra

/-- Arbitrarily late small evaluations of the limiting Gram polynomial on the
actual finite energy, first site, and parity row characterize the centered unit. -/
theorem stageUnit_zero_iff_cofinal_three_coordinate_parity_gram (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      projectedParityGramDefect (firstSiteGramCoordinates n).1 (firstSiteGramCoordinates n).2
        (finiteAdjointParityResidual n) ≤ ε := by
  let F (p : (ℝ × ℝ) × ℝ) := projectedParityGramDefect p.1.1 p.1.2 p.2
  have hc : Continuous F := by dsimp [F,projectedParityGramDefect,firstSiteGramGap]; fun_prop
  have ht := (hc.tendsto _).comp (firstSiteGramCoordinates_tendsto.prodMk_nhds finiteAdjointParityResidual_tendsto)
  rw [stageUnit_zero_iff_boundary, boundary_eq_zero_iff_one_mem, ← limitEnergy_zero_iff_mem]
  constructor
  · intro he
    have hz := limitResidual_zero_iff_energy_zero.mpr he
    have hlim : F ((limitEnergy,hilbertSequence limitResidual 1),inner ℝ limitResidual parityAdjointPacket) = 0 := by
      simp [F,projectedParityGramDefect,hz,he]
    rw [hlim] at ht
    simpa only [Function.comp_apply,F,zero_add] using RiemannResearch.Analysis.cofinal_le_add_of_tendsto ht
  · intro h
    have hle := RiemannResearch.Analysis.limit_le_of_cofinal_le_add (L:=0) ht
      (by simpa only [Function.comp_apply,F,zero_add] using h)
    by_contra hn
    exact (not_le_of_gt (limit_projectedParityGramDefect_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)))) hle

end CenteredMeanSnake
end RiemannResearch.RH.Pareto.PrimePowerSchur
