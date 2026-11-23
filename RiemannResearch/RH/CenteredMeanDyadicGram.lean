import Mathlib.Analysis.Complex.ExponentialBounds
import RiemannResearch.Analysis.CorrelationNormalizedCorrection
import RiemannResearch.Analysis.RealCofinalLimits
import RiemannResearch.RH.CenteredMeanRHCriteria
import RiemannResearch.RH.FiniteDyadicDefect
import RiemannResearch.RH.FiniteEndpointGram
import RiemannResearch.RH.FirstCoordinateEndpoint
import RiemannResearch.RH.MixedConductorGramSites
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.OptimalTwoCoefficientCriterion
import RiemannResearch.RH.ParetoParityAdjointCriterion
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

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
