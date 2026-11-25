import Mathlib.Analysis.Complex.ExponentialBounds
import RiemannResearch.Analysis.CorrelationNormalizedCorrection
import RiemannResearch.Analysis.RealCofinalLimits
import RiemannResearch.RH.CenteredMeanRHCriteria
import RiemannResearch.RH.FiniteDyadicDefect
import RiemannResearch.RH.FiniteEndpointGram
import RiemannResearch.RH.FirstCoordinateEndpoint
import RiemannResearch.RH.MixedConductorGramSites
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.OptimalTwoCoefficientCriterion
import RiemannResearch.RH.ParetoParityAdjointCriterion
import RiemannResearch.RH.ParetoParityDyadicMoments
import RiemannResearch.RH.ParetoSignedSchurRemainder
import RiemannResearch.RH.PrimeSupportAlgebraDescent
import RiemannResearch.RH.RamanujanCoefficientLimits
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A cubic first-site Gram bound for the centered mean snake

Remove the first physical site from the constant residual and project the
remainder onto its dyadic dilation. Pair the resulting vector with the parity
packet with its first site removed. The known two-sided estimate for adjoint
parity gives a strict cubic lower bound whenever the ambient residual is nonzero.
Both inputs of the resulting finite test come from one raw packet Gram solve.

The one-site removal follows the original one-site carry construction. Bagchi,
Theorem 1 (https://arxiv.org/abs/math/0607733), gives the discrete Hilbert-space
criterion underlying the application to RH.
-/

noncomputable section
open Filter
open scoped Topology Matrix

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The two-by-two Gram determinant after substituting the limiting dyadic
pairing. Its signed finite-stage correction is given below. -/
def firstSiteGramGap (e b : ℝ) : ℝ :=
  2 * e^2 - e * b^2 - (2*e - b)^2

/-- The component left after removing the first site and the dyadic direction,
scaled by the squared norm of the dilation to include the zero vector. -/
def firstSiteDyadicRemainder (x : ThresholdHilbert) : ThresholdHilbert :=
  (2 * ‖x‖^2) • (x - hilbertSequence x 1 • paretoPointHilbert 0) -
    inner ℝ x (doubleDilation x) • doubleDilation x

/-- Exact Gram identity for an arbitrary physical vector. -/
theorem firstSiteDyadicRemainder_norm_sq (x : ThresholdHilbert) :
    ‖firstSiteDyadicRemainder x‖^2 = 2 * ‖x‖^2 *
      (2 * (‖x‖^2)^2 - ‖x‖^2 * (hilbertSequence x 1)^2 -
        (inner ℝ x (doubleDilation x))^2) := by
  have hd : ‖doubleDilation x‖^2 = 2 * ‖x‖^2 := by
    rw [← real_inner_self_eq_norm_sq, doubleDilation_inner, real_inner_self_eq_norm_sq]
  have hz : inner ℝ (paretoPointHilbert 0) (doubleDilation x) = 0 :=
    (real_inner_comm ..).trans (doubleDilation_inner_firstPoint x)
  rw [firstSiteDyadicRemainder, norm_sub_sq_real, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
    remove_firstPoint_norm_sq, hd, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, real_inner_smul_left, hz]
  ring

/-- The signed defect of the finite projection enters twice, linearly and
quadratically, before the limiting Gram formula can be used. -/
theorem finite_firstSiteGramGap_identity (n : ℕ) :
    let e := energy n
    let b := hilbertSequence (projectionResidual n) 1
    let d := finiteDyadicDefect n
    ‖firstSiteDyadicRemainder (projectionResidual n)‖^2 =
      2 * e * (firstSiteGramGap e b + 2 * (2*e - b) * d - d^2) := by
  dsimp only
  have hd := finite_firstCoordinate_dyadic_identity n
  have hp : inner ℝ (projectionResidual n) (doubleDilation (projectionResidual n)) =
      2 * energy n - hilbertSequence (projectionResidual n) 1 - finiteDyadicDefect n := by
    linarith only [hd]
  rw [firstSiteDyadicRemainder_norm_sq, hp]
  change 2 * energy n * _ = _
  unfold firstSiteGramGap
  change 2 * energy n * (2 * (energy n)^2 - energy n * _ - _) = _
  ring

private theorem limit_dyadic_pairing :
    inner ℝ limitResidual (doubleDilation limitResidual) =
      2*limitEnergy - hilbertSequence limitResidual 1 := by
  have h := firstCoordinate_energy_identity
  change hilbertSequence limitResidual 1 / 2 = limitEnergy -
    inner ℝ limitResidual (doubleDilation limitResidual) / 2 at h
  linarith only [h]

theorem limit_firstSiteGramGap_identity :
    ‖firstSiteDyadicRemainder limitResidual‖^2 =
      2 * limitEnergy * firstSiteGramGap limitEnergy (hilbertSequence limitResidual 1) := by
  rw [firstSiteDyadicRemainder_norm_sq, limit_dyadic_pairing]
  rfl

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.PrimePowerSchur

open CoefficientStabilization

private theorem parity_first_site : hilbertSequence (ramanujanPacketHilbert 2) 1 = 1 := by
  rw [hilbertSequence_ramanujanPacketHilbert, ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
  norm_num [residue]

private theorem remainder_parity_pairing :
    inner ℝ (firstSiteDyadicRemainder limitResidual)
        (ramanujanPacketHilbert 2 - paretoPointHilbert 0) =
      -(limitEnergy * hilbertSequence limitResidual 1 +
        (2*limitEnergy - hilbertSequence limitResidual 1) *
          inner ℝ limitResidual parityAdjointPacket) := by
  let p := paretoPointHilbert 0
  let q := ramanujanPacketHilbert 2
  have hpq : inner ℝ (paretoPointHilbert 0) q = 1/2 := by
    rw [real_inner_comm]
    change inner ℝ (ramanujanPacketHilbert 2) (paretoPointHilbert 0) = _
    rw [paretoPoint_zero_inner, parity_first_site, mul_one]
  have hpp : inner ℝ (paretoPointHilbert 0) p = 1/2 := (real_inner_self_eq_norm_sq _).trans paretoPoint_zero_norm_sq
  have hrq : inner ℝ limitResidual q = 0 :=
    (real_inner_comm ..).trans (Submodule.inner_right_of_mem_orthogonal
      (packet_mem_closedSpace 2 (by decide)) limitResidual_mem_orthogonal)
  have hdrq : inner ℝ (doubleDilation limitResidual) q = inner ℝ limitResidual parityAdjointPacket :=
    (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous 2 (by decide))
      limitResidual q).symm
  have hdp : inner ℝ (doubleDilation limitResidual) p = 0 :=
    doubleDilation_inner_firstPoint limitResidual
  have hrp : inner ℝ limitResidual p = (1/2 : ℝ) * hilbertSequence limitResidual 1 :=
    paretoPoint_zero_inner _
  change inner ℝ (firstSiteDyadicRemainder limitResidual) (q - p) = _
  simp only [firstSiteDyadicRemainder, inner_sub_left, real_inner_smul_left, inner_sub_right,
    hpq, hpp, hrq, hdrq, hdp, hrp, CoefficientStabilization.limit_dyadic_pairing]
  rw [show ‖limitResidual‖^2 = limitEnergy from rfl]
  ring

/-- At positive residual energy, testing the Gram remainder against parity
off the first site gives a strict cubic gap, including the displayed endpoint. -/
theorem limit_firstSiteGramGap_strict (hE : 0 < limitEnergy) :
    ((2 - 5 * Real.sqrt 2 / 6)^2 / 2) * limitEnergy^3 <
      (Real.log 2 - 1/2) * firstSiteGramGap limitEnergy (hilbertSequence limitResidual 1) := by
  let E := limitEnergy
  let b := hilbertSequence limitResidual 1
  let B := inner ℝ limitResidual parityAdjointPacket
  let C := 2 - 5 * Real.sqrt 2 / 6
  have hpair : E/6 ≤ B ∧ B ≤ E/2 := parityAdjointPacket_residual_bounds
  have hr : limitResidual ≠ 0 := fun h => hE.ne' (limitResidual_zero_iff_energy_zero.mp h)
  have hb : 2*E-b < Real.sqrt 2 * E := by
    have h := firstCoordinate_energy_strict_of_residual_ne_zero hr
    change (2 - Real.sqrt 2) * E < b at h
    linarith only [h]
  have hEB : 0 < E-B := by change 0 < E at hE; linarith only [hE, hpair.2]
  have hs : 0 ≤ Real.sqrt 2 * E := mul_nonneg (Real.sqrt_nonneg _) hE.le
  have hprod := (mul_lt_mul_of_pos_right hb hEB).trans_le
    (mul_le_mul_of_nonneg_left (show E-B ≤ 5*E/6 by linarith only [hpair.1]) hs)
  have hsep : C * E^2 < E*b + (2*E-b)*B := by
    dsimp only [C]
    nlinarith only [hprod]
  have hroot : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hC : 0 ≤ C := by dsimp only [C]; linarith only [hroot]
  have hsq := mul_self_lt_mul_self (mul_nonneg hC (sq_nonneg E)) hsep
  let q := ramanujanPacketHilbert 2 - paretoPointHilbert 0
  have hq : ‖q‖^2 = Real.log 2 - 1/2 := by
    simpa only [parity_first_site, one_smul, one_pow, ramanujanPacketHilbert_two_norm_sq, q] using
      remove_firstPoint_norm_sq (ramanujanPacketHilbert 2)
  have hcs := RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le
    (firstSiteDyadicRemainder limitResidual) q
  rw [show inner ℝ (firstSiteDyadicRemainder limitResidual) q = -(E*b+(2*E-b)*B) from
    remainder_parity_pairing, neg_sq, limit_firstSiteGramGap_identity, hq] at hcs
  change (E*b+(2*E-b)*B)^2 ≤ 2*E * firstSiteGramGap E b * (Real.log 2 - 1/2) at hcs
  have hscaled : (C^2/2 * E^3) * (2*E) <
      ((Real.log 2 - 1/2) * firstSiteGramGap E b) * (2*E) := by
    calc
      _ = (C*E^2)*(C*E^2) := by ring
      _ < (E*b + (2*E-b)*B)^2 := by simpa only [pow_two] using hsq
      _ ≤ _ := hcs.trans_eq (by ring)
  exact (mul_lt_mul_iff_left₀ (show 0 < 2*E by positivity)).mp hscaled


/-- The additional quadratic allowance in the one-sided first-site test. -/
def firstSiteQuadraticAllowance : ℝ :=
  ((2 - Real.sqrt 2)^2 + ((2 - 5 * Real.sqrt 2 / 6)^2 / 2) / (Real.log 2 - 1/2)) /
    (2 * Real.sqrt 2)

theorem half_lt_firstSiteQuadraticAllowance : (1/2 : ℝ) < firstSiteQuadraticAllowance := by
  let s := Real.sqrt 2
  let L := Real.log 2 - 1/2
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hs' : s < 3/2 := by
    change Real.sqrt 2 < 3/2
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_two_gt_d9]
  have hL' : L < 1/5 := by dsimp [L]; linarith [Real.log_two_lt_d9]
  have ha := mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 1/2)
    (show 1/2 < 2-s by linarith only [hs'])
  have hC := mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 3/4)
    (show 3/4 < 2-5*s/6 by linarith only [hs'])
  have hk : (45/32 : ℝ) < ((2-5*s/6)^2 / 2)/L := by
    apply (lt_div_iff₀ hL).mpr
    nlinarith only [hC, hL']
  change 1/2 < ((2-s)^2 + ((2-5*s/6)^2/2)/L)/(2*s)
  apply (lt_div_iff₀ (mul_pos (by norm_num) hs)).mpr
  nlinarith only [hs', ha, hk]

/-- The cubic inequality gives a strictly positive quadratic improvement
to the linear first-coordinate endpoint at every positive limiting energy. -/
theorem limit_firstSite_quadratic_strict (hE : 0 < limitEnergy) :
    (2 - Real.sqrt 2) * limitEnergy + firstSiteQuadraticAllowance * limitEnergy^2 <
      hilbertSequence limitResidual 1 := by
  let E := limitEnergy
  let b := hilbertSequence limitResidual 1
  let s := Real.sqrt 2
  let a := 2 - s
  let L := Real.log 2 - 1/2
  let K := (2 - 5*s/6)^2 / 2
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hs2 : s^2 = 2 := Real.sq_sqrt (by norm_num)
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_two_gt_d9]
  have ha : 0 ≤ a := by
    dsimp only [a]
    nlinarith only [hs2, hs]
  have hab : a*E < b := firstCoordinate_energy_strict_of_residual_ne_zero
    (fun h => hE.ne' (limitResidual_zero_iff_energy_zero.mp h))
  have hsq := mul_self_lt_mul_self (mul_nonneg ha hE.le) hab
  have hgap : firstSiteGramGap E b = 2*s*E*(b-a*E) - (b-a*E)^2 - E*b^2 := by
    dsimp only [firstSiteGramGap, a]
    nlinarith only [congrArg (fun y : ℝ => y * E^2) hs2]
  have hup : firstSiteGramGap E b ≤ 2*s*E*(b-a*E) - a^2*E^3 := by
    rw [hgap]
    nlinarith only [sq_nonneg (b-a*E), mul_le_mul_of_nonneg_left hsq.le hE.le]
  have hstrict : K*E^3 < L*(2*s*E*(b-a*E) - a^2*E^3) :=
    (limit_firstSiteGramGap_strict hE).trans_le (mul_le_mul_of_nonneg_left hup hL.le)
  have hc : 2*s*firstSiteQuadraticAllowance = a^2 + K/L := by
    change 2*s*((a^2 + K/L)/(2*s)) = a^2 + K/L
    field_simp [hs.ne']
  have hcoef : L * (2*s*firstSiteQuadraticAllowance - a^2) = K := by
    rw [hc]
    field_simp [hL.ne']
    <;> ring
  have hscaled : (a*E + firstSiteQuadraticAllowance*E^2) * (2*s*E*L) <
      b * (2*s*E*L) := by
    nlinarith only [hstrict, congrArg (fun y : ℝ => y * E^3) hcoef]
  exact (mul_lt_mul_iff_left₀ (mul_pos (mul_pos (mul_pos (by norm_num) hs) hE) hL)).mp hscaled

/-- The cross Gram remainder is orthogonal to every doubled legal vector:
the removed point lies outside the dyadic image and the residual is legal-orthogonal. -/
theorem firstSiteDyadicRemainder_inner_double_legal {v : ThresholdHilbert} (hv : v ∈ closedSpace) :
    inner ℝ (firstSiteDyadicRemainder limitResidual) (doubleDilation v) = 0 := by
  have hr : inner ℝ limitResidual v = 0 := (real_inner_comm ..).trans
    (Submodule.inner_right_of_mem_orthogonal hv limitResidual_mem_orthogonal)
  have hd : inner ℝ limitResidual (doubleDilation v) = 0 := (real_inner_comm ..).trans
    (Submodule.inner_right_of_mem_orthogonal
      (closedSpace_dilation hv 2 (by decide)) limitResidual_mem_orthogonal)
  have hp : inner ℝ (paretoPointHilbert 0) (doubleDilation v) = 0 :=
    (real_inner_comm ..).trans (doubleDilation_inner_firstPoint v)
  simp only [firstSiteDyadicRemainder,inner_sub_left,real_inner_smul_left,
    doubleDilation_inner,hr,hd,hp,mul_zero,sub_self]

/-- Subtract a signed multiple of the doubled legal projection from parity
after removing its first physical site. -/
def firstSiteParityProbe (t : ℝ) : ThresholdHilbert :=
  ramanujanPacketHilbert 2 - paretoPointHilbert 0 - t • doubleDilation limitProjection

theorem firstSiteParityProbe_pair_and_norm (t : ℝ) :
    let E := limitEnergy
    let b := hilbertSequence limitResidual 1
    let B := inner ℝ limitResidual parityAdjointPacket
    let L := Real.log 2-1/2
    inner ℝ (firstSiteDyadicRemainder limitResidual) (firstSiteParityProbe t) =
        -(E*b+(2*E-b)*B) ∧
      ‖firstSiteParityProbe t‖^2 = L-2*t*(2*L-B)+2*t^2*(1-E) := by
  let E := limitEnergy
  let b := hilbertSequence limitResidual 1
  let B := inner ℝ limitResidual parityAdjointPacket
  let L := Real.log 2-1/2
  let q := ramanujanPacketHilbert 2 - paretoPointHilbert 0
  let v := doubleDilation limitProjection
  let z := firstSiteDyadicRemainder limitResidual
  have hq : ‖q‖^2 = L := by
    simpa only [parity_first_site, one_smul, one_pow, ramanujanPacketHilbert_two_norm_sq, q,L] using
      remove_firstPoint_norm_sq (ramanujanPacketHilbert 2)
  have hv : ‖v‖^2 = 2*(1-E) := by
    dsimp only [v]
    rw [← real_inner_self_eq_norm_sq, doubleDilation_inner, real_inner_self_eq_norm_sq,
      limitProjection_norm_sq]
  have hzv : inner ℝ z v = 0 :=
    firstSiteDyadicRemainder_inner_double_legal (closedSpace.starProjection_apply_mem hilbertOne)
  have hmean : inner ℝ hilbertOne parityAdjointPacket = 2*L := by
    have hh := dyadicMomentProfile_mean
    rw [dyadicMomentProfile,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
      hilbertOne_norm_sq] at hh
    dsimp only [L]
    linarith only [hh, real_inner_comm hilbertOne parityAdjointPacket]
  have hqv : inner ℝ q v = 2*L-B := by
    dsimp only [q,v]
    have hp : inner ℝ (paretoPointHilbert 0) (doubleDilation limitProjection) = 0 :=
      (real_inner_comm ..).trans (doubleDilation_inner_firstPoint limitProjection)
    rw [inner_sub_left, hp, sub_zero, real_inner_comm]
    have ha : inner ℝ (doubleDilation limitProjection) (ramanujanPacketHilbert 2) =
        inner ℝ limitProjection parityAdjointPacket :=
      (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous 2 (by decide))
        limitProjection (ramanujanPacketHilbert 2)).symm
    rw [ha]
    have hh : B = inner ℝ hilbertOne parityAdjointPacket -
        inner ℝ limitProjection parityAdjointPacket := by
      dsimp only [B,limitResidual]
      rw [inner_sub_left]
    linarith only [hh,hmean]
  have hzq : inner ℝ z q = -(E*b+(2*E-b)*B) := remainder_parity_pairing
  have hyd : ‖q-t • v‖^2 = L-2*t*(2*L-B)+2*t^2*(1-E) := by
    rw [norm_sub_sq_real,hq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hv,
      real_inner_smul_right,hqv]
    ring
  change inner ℝ z (q-t • v) = _ ∧ ‖q-t • v‖^2 = _
  rw [inner_sub_right,real_inner_smul_right,hzv,mul_zero,sub_zero]
  exact ⟨hzq,hyd⟩

/-- Every signed subtraction of the doubled optimal approximation to one
preserves the parity observation of the Gram remainder. The right hand
quadratic is the exact squared norm of the corrected probe. -/
theorem limit_firstSiteGram_parity_pencil (t : ℝ) :
    let E := limitEnergy
    let b := hilbertSequence limitResidual 1
    let B := inner ℝ limitResidual parityAdjointPacket
    let L := Real.log 2 - 1/2
    (E*b+(2*E-b)*B)^2 ≤ 2*E*firstSiteGramGap E b *
      (L - 2*t*(2*L-B) + 2*t^2*(1-E)) := by
  have h := RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le
    (firstSiteDyadicRemainder limitResidual) (firstSiteParityProbe t)
  rw [(firstSiteParityProbe_pair_and_norm t).1,neg_sq,limit_firstSiteGramGap_identity,
    (firstSiteParityProbe_pair_and_norm t).2] at h
  exact h

/-- Optimizing the signed parity pencil subtracts the actual squared
correlation with the doubled optimal projection, at every energy. -/
theorem limit_firstSiteGram_projected_parity_bound :
    let E := limitEnergy
    let b := hilbertSequence limitResidual 1
    let B := inner ℝ limitResidual parityAdjointPacket
    let L := Real.log 2-1/2
    (1-E)*(E*b+(2*E-b)*B)^2 ≤
      E*firstSiteGramGap E b * (2*(1-E)*L-(2*L-B)^2) := by
  dsimp only
  let E := limitEnergy
  let b := hilbertSequence limitResidual 1
  let B := inner ℝ limitResidual parityAdjointPacket
  let L := Real.log 2-1/2
  let t := (2*L-B)/(2*(1-E))
  have h := limit_firstSiteGram_parity_pencil t
  change (E*b+(2*E-b)*B)^2 ≤ 2*E*firstSiteGramGap E b *
    (L-2*t*(2*L-B)+2*t^2*(1-E)) at h
  have he : 0 < 1-E := one_sub_limitEnergy_pos
  have hq : (1-E)*(2*(L-2*t*(2*L-B)+2*t^2*(1-E))) =
      2*(1-E)*L-(2*L-B)^2 := by
    dsimp only [t]
    field_simp [he.ne']
    ring
  change (1-E)*(E*b+(2*E-b)*B)^2 ≤ _
  apply (mul_le_mul_of_nonneg_left h he.le).trans_eq
  calc
    _ = E*firstSiteGramGap E b * ((1-E)*(2*(L-2*t*(2*L-B)+2*t^2*(1-E)))) := by ring
    _ = _ := by rw [hq]

/-- Separation coefficient after keeping the dyadic term of the adjoint parity
series and its signed covariance with the first-site coordinate. -/
def firstSiteParitySeparation : ℝ :=
  2 + 1/15 - (2/3 + 1/(10*Real.sqrt 3))*Real.sqrt 2

theorem one_lt_firstSiteParitySeparation : 1 < firstSiteParitySeparation := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have ht := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hs' : Real.sqrt 2 ≤ 17/12 := by
    nlinarith only [hs, sq_nonneg (Real.sqrt 2 - 17/12)]
  have ht' : (5/3 : ℝ) ≤ Real.sqrt 3 := by
    by_contra! hc
    have h := mul_self_lt_mul_self (Real.sqrt_nonneg _) hc
    nlinarith only [ht, h]
  have hx : 1/(10*Real.sqrt 3) ≤ 3/50 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [ht']
  have hh : (2/3+1/(10*Real.sqrt 3))*Real.sqrt 2 ≤ (2/3+3/50)*(17/12) :=
    mul_le_mul (by linarith only [hx]) hs' (Real.sqrt_nonneg _) (by norm_num)
  unfold firstSiteParitySeparation
  linarith only [hh]

/-- The signed first-site pairing of the parity Gram remainder has a strictly
positive lower separation already exceeding the square of the energy. -/
theorem limit_firstSite_coupled_separation (hE : 0 < limitEnergy) :
    let E := limitEnergy
    let b := hilbertSequence limitResidual 1
    let B := inner ℝ limitResidual parityAdjointPacket
    firstSiteParitySeparation*E^2 < E*b + (2*E-b)*B := by
  dsimp only
  let E := limitEnergy
  let b := hilbertSequence limitResidual 1
  let B := inner ℝ limitResidual parityAdjointPacket
  let x := 2*E-b
  let s := Real.sqrt 2
  let c := 1/(10*Real.sqrt 3)
  let δ := B - 2*E/5 + b/30
  have hδ : |δ| ≤ c*E := by
    simpa only [δ, c, E, b, B, one_div, div_eq_inv_mul, mul_one] using
      parityAdjointPacket_first_site_coupling
  have hs : s^2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 ≤ s := Real.sqrt_nonneg _
  have hs' : s < 2 := by nlinarith only [hs, hspos, sq_nonneg (s-2)]
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hab := firstCoordinate_energy_bounds
  have hxabs : |x| ≤ s*E := by
    apply abs_le.mpr
    dsimp only [x,E,b,s]
    constructor <;> linarith only [hab.1, hab.2]
  have hb := firstCoordinate_energy_strict_of_residual_ne_zero
    (fun hz => hE.ne' (limitResidual_zero_iff_energy_zero.mp hz))
  have hx : x < s*E := by dsimp only [x,E,b,s]; linarith only [hb]
  have hxd : -(s*E*(c*E)) ≤ x*δ := by
    have hu : |x*δ| ≤ s*E*(c*E) := by
      rw [abs_mul]
      exact mul_le_mul hxabs hδ (abs_nonneg _) (mul_nonneg hspos hE.le)
    exact (abs_le.mp hu).1
  have hcoef : 0 < (2/3-s/15)*E := by
    exact mul_pos (by linarith only [hs']) hE
  have hstrict := mul_lt_mul_of_pos_left hx hcoef
  have hscale := congrArg (fun t : ℝ => t*E^2) hs
  have hpair : E*b + (2*E-b)*B = 2*E^2 - (2/3)*E*x + x^2/30 + x*δ := by
    dsimp only [δ, x]
    ring
  change firstSiteParitySeparation * E^2 < E*b + (2*E-b)*B
  rw [hpair]
  change (2+1/15 - (2/3+c)*s)*E^2 < _
  nlinarith only [hscale, hstrict, hxd, sq_nonneg (x-s*E)]

/-- Keeping the signed dyadic term in the adjoint series strengthens the
cubic lower bound at every positive limiting energy. -/
theorem limit_firstSiteGramGap_coupled_strict (hE : 0 < limitEnergy) :
    firstSiteParitySeparation^2 / 2 * limitEnergy^3 <
      (Real.log 2 - 1/2) * firstSiteGramGap limitEnergy (hilbertSequence limitResidual 1) := by
  let E := limitEnergy
  let b := hilbertSequence limitResidual 1
  let B := inner ℝ limitResidual parityAdjointPacket
  let C := firstSiteParitySeparation
  have hpair : C*E^2 < E*b + (2*E-b)*B := limit_firstSite_coupled_separation hE
  have hC : 0 ≤ C := le_trans zero_le_one one_lt_firstSiteParitySeparation.le
  have hCE : 0 ≤ C*E^2 := mul_nonneg hC (sq_nonneg E)
  have hsq := (sq_lt_sq₀ hCE (hCE.trans hpair.le)).mpr hpair
  let q := ramanujanPacketHilbert 2 - paretoPointHilbert 0
  have hq : ‖q‖^2 = Real.log 2 - 1/2 := by
    simpa only [parity_first_site, one_smul, one_pow, ramanujanPacketHilbert_two_norm_sq, q] using
      remove_firstPoint_norm_sq (ramanujanPacketHilbert 2)
  have hcs := RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le
    (firstSiteDyadicRemainder limitResidual) q
  rw [show inner ℝ (firstSiteDyadicRemainder limitResidual) q = -(E*b+(2*E-b)*B) from
    remainder_parity_pairing, neg_sq, limit_firstSiteGramGap_identity, hq] at hcs
  change (E*b+(2*E-b)*B)^2 ≤ 2*E * firstSiteGramGap E b * (Real.log 2 - 1/2) at hcs
  apply (mul_lt_mul_iff_left₀ (show 0 < 2*E by positivity)).mp
  change (C^2/2 * E^3) * (2*E) < ((Real.log 2-1/2) * firstSiteGramGap E b) * (2*E)
  nlinarith only [hsq.trans_le hcs]

/-- The observable polynomial upper bound for the corrected parity-probe
weight, after using the signed adjoint upper bound. -/
def projectedParityGramWeight (e : ℝ) : ℝ :=
  let L := Real.log 2 - 1/2
  2*(1-e)*L - (2*L-e/2)^2

/-- For the projected parity bound, the linear term in energy cancels exactly. -/
theorem projectedParityGramWeight_eq (e : ℝ) :
    let L := Real.log 2-1/2
    projectedParityGramWeight e = 2*L*(1-2*L)-e^2/4 := by
  unfold projectedParityGramWeight
  ring

/-- Every positive residual satisfies a strict polynomial inequality whose
two inputs are exactly the limiting finite Gram coordinates. -/
theorem limit_projected_parity_gram_strict (hE : 0 < limitEnergy) :
    (1-limitEnergy)*firstSiteParitySeparation^2*limitEnergy^3 <
      firstSiteGramGap limitEnergy (hilbertSequence limitResidual 1) *
        projectedParityGramWeight limitEnergy := by
  let E := limitEnergy
  let b := hilbertSequence limitResidual 1
  let B := inner ℝ limitResidual parityAdjointPacket
  let L := Real.log 2-1/2
  let C := firstSiteParitySeparation
  let G := firstSiteGramGap E b
  let S := E*b+(2*E-b)*B
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_two_gt_d9]
  have hG : 0 < G := pos_of_mul_pos_right
    ((show 0 ≤ C^2/2*E^3 from by positivity).trans_lt (limit_firstSiteGramGap_coupled_strict hE))
    hL.le
  have hE1 : 0 < 1-E := one_sub_limitEnergy_pos
  have hsep : C*E^2 < S := limit_firstSite_coupled_separation hE
  have hCE : 0 ≤ C*E^2 := mul_nonneg (le_trans zero_le_one one_lt_firstSiteParitySeparation.le)
    (sq_nonneg E)
  have hs := mul_lt_mul_of_pos_left ((sq_lt_sq₀ hCE (hCE.trans hsep.le)).mpr hsep) hE1
  have hproj : (1-E)*S^2 ≤ E*G*(2*(1-E)*L-(2*L-B)^2) := limit_firstSiteGram_projected_parity_bound
  have hBL : B ≤ E/2 := parityAdjointPacket_residual_bounds.2
  have hLE : 0 ≤ 2*L-E/2 := by
    dsimp only [E,L]
    linarith only [Real.log_two_gt_d9, limitEnergy_lt_period5040_bound]
  have hSq := (sq_le_sq₀ hLE (show 0 ≤ 2*L-B by linarith only [hBL,hLE])).mpr
    (show 2*L - E/2 ≤ 2*L-B by linarith only [hBL])
  have hw : 2*(1-E)*L-(2*L-B)^2 ≤ projectedParityGramWeight E := by
    change _ ≤ 2*(1-E)*L-(2*L-E/2)^2
    linarith only [hSq]
  have hfinal := (hs.trans_le hproj).trans_le
    (mul_le_mul_of_nonneg_left hw (mul_nonneg hE.le hG.le))
  have hscaled : ((1-E)*C^2*E^3)*E < (G*projectedParityGramWeight E)*E := by
    nlinarith only [hfinal]
  exact (mul_lt_mul_iff_left₀ hE).mp hscaled

/-- The discriminant obtained by solving the parity-tested cubic Gram
inequality for the signed first-site coordinate. -/
def firstSiteRootDiscriminant (e : ℝ) : ℝ :=
  let A := (firstSiteParitySeparation^2 / 2) / (Real.log 2 - 1/2)
  2 - (2+A)*e - A*e^2

/-- Exact completion of the square in the cubic parity test. -/
theorem firstSiteRootDiscriminant_identity (e b : ℝ) :
    e^2 * firstSiteRootDiscriminant e - ((1+e)*b - 2*e)^2 =
      (1+e) * (firstSiteGramGap e b -
        ((firstSiteParitySeparation^2 / 2) / (Real.log 2 - 1/2)) * e^3) := by
  unfold firstSiteRootDiscriminant firstSiteGramGap
  ring

/-- Positive limiting energy puts the actual signed coordinate strictly
above the lower root of the full cubic Gram inequality. -/
theorem limit_firstSite_lower_root_strict (hE : 0 < limitEnergy) :
    2*limitEnergy - limitEnergy*Real.sqrt (firstSiteRootDiscriminant limitEnergy) <
      (1+limitEnergy) * hilbertSequence limitResidual 1 := by
  let e := limitEnergy
  let b := hilbertSequence limitResidual 1
  let L := Real.log 2 - 1/2
  let K := firstSiteParitySeparation^2 / 2
  have hL : 0 < L := by dsimp only [L]; linarith [Real.log_two_gt_d9]
  have hg : K*e^3 < L*firstSiteGramGap e b := limit_firstSiteGramGap_coupled_strict hE
  have hgap : (K/L)*e^3 < firstSiteGramGap e b := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hL]
    simpa only [mul_comm L] using hg
  have hp := mul_pos (show 0 < 1+e by dsimp [e]; linarith) (sub_pos.mpr hgap)
  have hi := firstSiteRootDiscriminant_identity e b
  change e^2 * firstSiteRootDiscriminant e - ((1+e)*b - 2*e)^2 =
    (1+e)*(firstSiteGramGap e b - (K/L)*e^3) at hi
  have hsq : ((1+e)*b - 2*e)^2 < e^2 * firstSiteRootDiscriminant e := by
    linarith only [hi, hp]
  have hd : 0 < firstSiteRootDiscriminant e :=
    pos_of_mul_pos_right (lt_of_le_of_lt (sq_nonneg _) hsq) (sq_nonneg e)
  have hab : |2*e - (1+e)*b| < e*Real.sqrt (firstSiteRootDiscriminant e) := by
    apply (sq_lt_sq₀ (abs_nonneg _) (mul_nonneg hE.le (Real.sqrt_nonneg _))).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt hd.le]
    simpa only [sub_sq_comm] using hsq
  have hlin := (le_abs_self _).trans_lt hab
  change 2*e - e*Real.sqrt (firstSiteRootDiscriminant e) < (1+e)*b
  linarith only [hlin]

end RiemannResearch.RH.Pareto.PrimePowerSchur

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

open CoefficientStabilization MixedConductorBasis RamanujanCanonicalOptimizer PacketGramBoundary
open scoped LegalMeanAlgebra

/-- Compute the squared residual energy and the signed first-site residual
using the same inverse Gram vector. -/
def firstSiteGramCoordinates (n : ℕ) : ℝ × ℝ :=
  let c := (finitePacketGram n)⁻¹.mulVec (meanVector n)
  (1 - dotProduct (meanVector n) c, 1 + dotProduct (finiteMoebiusSource n) c)

theorem firstSiteGramCoordinates_eq (n : ℕ) :
    firstSiteGramCoordinates n = (energy n, 1 - hilbertSequence (projection n) 1) := by
  have h := (det_siteGram n 1).symm.trans (first_site_det_as_one_solve n)
  have hs := mul_left_cancel₀ (finitePacketGram_det_pos n).ne' h
  have hb : 1 + dotProduct (finiteMoebiusSource n)
      ((finitePacketGram n)⁻¹.mulVec (meanVector n)) = 1 - hilbertSequence (projection n) 1 := by
    linarith only [hs]
  have hm : dotProduct (meanVector n) ((finitePacketGram n)⁻¹.mulVec (meanVector n)) =
      packetMass n := (packetMass_eq_inverseGram n).symm
  simp only [firstSiteGramCoordinates, hb, hm, packet_energy_eq_original]

theorem firstSiteGramCoordinates_tendsto :
    Tendsto firstSiteGramCoordinates atTop (𝓝 (limitEnergy, hilbertSequence limitResidual 1)) := by
  rw [show firstSiteGramCoordinates =
      fun n => (energy n, 1 - hilbertSequence (projection n) 1) from funext firstSiteGramCoordinates_eq]
  exact energy_tendsto.prodMk_nhds one_sub_projection_first_tendsto

private theorem stageUnit_zero_iff_cofinal_firstSite_test (s : ℕ) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) (hzero : f (0, 0) = 0)
    (hpos : 0 < limitEnergy → 0 < f (limitEnergy, hilbertSequence limitResidual 1)) :
    stageMeanBoundary s 1 = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, f (firstSiteGramCoordinates n) ≤ ε := by
  rw [stageUnit_zero_iff_boundary, boundary_eq_zero_iff_one_mem, ← limitEnergy_zero_iff_mem]
  have ht := (hf.tendsto _).comp firstSiteGramCoordinates_tendsto
  constructor
  · intro he
    have hb := firstCoordinate_zero_iff_residual_zero.mpr (limitResidual_zero_iff_energy_zero.mpr he)
    rw [he, hb, hzero] at ht
    simpa only [Function.comp_apply, zero_add] using
      RiemannResearch.Analysis.cofinal_le_add_of_tendsto ht
  · intro h
    have hle := RiemannResearch.Analysis.limit_le_of_cofinal_le_add
      (L := 0) ht (by simpa only [Function.comp_apply, zero_add] using h)
    by_contra hn
    exact (not_le_of_gt (hpos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)))) hle

/-- At any support stage the centered unit dies exactly when the finite
two-by-two Gram gap meets the cubic endpoint cofinally. -/
theorem stageUnit_zero_iff_cofinal_cubic_gram_bound (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      let p := firstSiteGramCoordinates n
      (Real.log 2 - 1/2) * firstSiteGramGap p.1 p.2 ≤
        ((2 - 5 * Real.sqrt 2 / 6)^2 / 2) * p.1^3 + ε := by
  let f (p : ℝ × ℝ) := (Real.log 2 - 1/2) * firstSiteGramGap p.1 p.2 -
    ((2 - 5 * Real.sqrt 2 / 6)^2 / 2) * p.1^3
  have h := stageUnit_zero_iff_cofinal_firstSite_test s f
    (by dsimp [f, firstSiteGramGap]; fun_prop)
    (by norm_num [f, firstSiteGramGap])
    (fun he => sub_pos.mpr (limit_firstSiteGramGap_strict he))
  simpa only [f, sub_le_iff_le_add', add_comm] using h

/-- The previous first-site Gram solve admits a positive quadratic energy
allowance at every finite index. The cofinal assertion remains the arithmetic input. -/
theorem stageUnit_zero_iff_cofinal_quadratic_gram_solve (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      let c := (finitePacketGram n)⁻¹.mulVec (meanVector n)
      let e := 1 - dotProduct (meanVector n) c
      1 + dotProduct (finiteMoebiusSource n) c ≤
        (2 - Real.sqrt 2) * e + firstSiteQuadraticAllowance * e^2 + ε := by
  let f (p : ℝ × ℝ) := p.2 - ((2 - Real.sqrt 2) * p.1 + firstSiteQuadraticAllowance * p.1^2)
  have h := stageUnit_zero_iff_cofinal_firstSite_test s f
    (by dsimp [f]; fun_prop) (by simp [f])
    (fun he => sub_pos.mpr (limit_firstSite_quadratic_strict he))
  simpa only [f, firstSiteGramCoordinates, sub_le_iff_le_add', add_comm] using h

theorem riemannHypothesis_of_cofinal_quadratic_gram_solve
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      let c := (finitePacketGram n)⁻¹.mulVec (meanVector n)
      let e := 1 - dotProduct (meanVector n) c
      1 + dotProduct (finiteMoebiusSource n) c ≤
        (2 - Real.sqrt 2) * e + firstSiteQuadraticAllowance * e^2 + ε) :
    RiemannHypothesis :=
  riemannHypothesis_of_stageUnit_zero ((stageUnit_zero_iff_cofinal_quadratic_gram_solve 0).2 h)

/-- A cofinal upper bound at the lower root of the full parity Gram quadratic
kills the centered unit. Every coordinate in the test uses one finite solve. -/
theorem stageUnit_zero_iff_cofinal_lower_root_gram_solve (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      let p := firstSiteGramCoordinates n
      (1+p.1)*p.2 ≤ 2*p.1 - p.1*Real.sqrt (firstSiteRootDiscriminant p.1) + ε := by
  let f (p : ℝ × ℝ) :=
    (1+p.1)*p.2 - (2*p.1 - p.1*Real.sqrt (firstSiteRootDiscriminant p.1))
  have h := stageUnit_zero_iff_cofinal_firstSite_test s f
    (by dsimp [f, firstSiteRootDiscriminant]; fun_prop) (by simp [f])
    (fun he => sub_pos.mpr (limit_firstSite_lower_root_strict he))
  simpa only [f, sub_le_iff_le_add', add_comm] using h

/-- Vanishing of the centered unit is equivalent to the cofinal projected
parity Gram test, evaluated at the actual two coordinates of one solve. -/
theorem stageUnit_zero_iff_cofinal_projected_parity_gram (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      let p := firstSiteGramCoordinates n
      firstSiteGramGap p.1 p.2 * projectedParityGramWeight p.1 ≤
        (1-p.1)*firstSiteParitySeparation^2*p.1^3 + ε := by
  let f (p : ℝ × ℝ) :=
    firstSiteGramGap p.1 p.2 * projectedParityGramWeight p.1 -
      (1-p.1)*firstSiteParitySeparation^2*p.1^3
  have h := stageUnit_zero_iff_cofinal_firstSite_test s f
    (by dsimp [f, firstSiteGramGap, projectedParityGramWeight]; fun_prop)
    (by simp [f, firstSiteGramGap])
    (fun he => sub_pos.mpr (limit_projected_parity_gram_strict he))
  simpa only [f, sub_le_iff_le_add', add_comm] using h

/-- A cofinal certificate at one tolerance in the original cubic test bounds
the actual limiting energy. The coefficient is positive because the dyadic
pairing improves the separation above one. -/
theorem limitEnergy_cube_le_of_frequently_cubic_gram_budget (τ : ℝ)
    (hτ : ∃ᶠ n : ℕ in atTop,
      let p := firstSiteGramCoordinates n
      (Real.log 2 - 1/2)*firstSiteGramGap p.1 p.2 ≤
        ((2 - 5*Real.sqrt 2/6)^2/2)*p.1^3 + τ) :
    ((firstSiteParitySeparation^2 - (2 - 5*Real.sqrt 2/6)^2)/2) * limitEnergy^3 ≤ τ := by
  let f (p : ℝ × ℝ) := (Real.log 2 - 1/2)*firstSiteGramGap p.1 p.2 -
    ((2 - 5*Real.sqrt 2/6)^2/2)*p.1^3
  have hcont : Continuous f := by dsimp [f, firstSiteGramGap]; fun_prop
  have hlim := (hcont.tendsto _).comp firstSiteGramCoordinates_tendsto
  have hupper : f (limitEnergy, hilbertSequence limitResidual 1) ≤ τ :=
    le_of_tendsto_of_frequently hlim (hτ.mono (fun n hn => by
      change f (firstSiteGramCoordinates n) ≤ τ
      dsimp only [f]
      dsimp only at hn
      linarith only [hn]))
  by_cases hE : limitEnergy = 0
  · have hb := firstCoordinate_zero_iff_residual_zero.mpr (limitResidual_zero_iff_energy_zero.mpr hE)
    have hz : f (0, 0) = 0 := by norm_num [f, firstSiteGramGap]
    rw [hE, hb, hz] at hupper
    simpa only [hE, zero_pow (by decide : 3 ≠ 0), mul_zero] using hupper
  have hpos : 0 < limitEnergy := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hE)
  dsimp only [f] at hupper
  nlinarith only [hupper, limit_firstSiteGramGap_coupled_strict hpos]

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
