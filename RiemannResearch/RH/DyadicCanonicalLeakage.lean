import RiemannResearch.RH.ActualDyadicAdjointDefect
import RiemannResearch.RH.CompensatedTwoCoefficientCriterion
import RiemannResearch.RH.ParetoResidualDilation
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ResidueProjectionSchur
import RiemannResearch.Analysis.DyadicAdjointDefect

/-!
# Exact canonical projection leakage for the fixed signed coefficient defect

Source: FixedGramAdjointContinuation20261006.md, equations (24)--(29).
The actual operator identity, closed legal-span invariance, and canonical
projection prove the scalar energy premise. Both orthogonal remainder squares
and the infinite paired-variance series are retained. No cofinal arithmetic
lower provider or unconditional RH conclusion is supplied.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.DyadicCanonicalLeakage
open CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative

set_option backward.isDefEq.respectTransparency false

def polynomial (x : ThresholdHilbert) : ThresholdHilbert :=
  (14 : ℝ) • x - (26 : ℝ) • dyadicHalfDilation x +
    (12 : ℝ) • dyadicHalfDilation (dyadicHalfDilation x)

def vector : ThresholdHilbert := polynomial hilbertOne
def moment : ℝ := inner ℝ limitResidual vector
def first : ℝ := hilbertSequence limitResidual 1
def fullMiddle (x : ThresholdHilbert) : ThresholdHilbert :=
  dyadicHalfDilation x + dyadicHalfAdjoint x - (13/12 : ℝ) • x

def perpendicular : ThresholdHilbert :=
  fullMiddle limitResidual -
    ((11 * limitEnergy / 12 - first) / limitEnergy) • limitResidual -
    (((first - limitEnergy) / 2) / (1-limitEnergy)) • limitProjection

theorem half_dilation_mem_closed {x : ThresholdHilbert}
    (hx : x ∈ closedSpace) : dyadicHalfDilation x ∈ closedSpace := by
  rw [dyadicHalfDilation_apply]
  exact closedSpace.smul_mem _ (closedSpace_dilation hx 2 (by norm_num))

theorem residual_projection_orthogonal :
    inner ℝ limitResidual limitProjection = 0 := by
  rw [real_inner_comm]
  exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
    (closedSpace.starProjection_apply_mem hilbertOne)

theorem residual_norm_sq : ‖limitResidual‖^2 = limitEnergy := rfl

theorem projection_norm_sq : ‖limitProjection‖^2 = 1-limitEnergy := by
  have hOne : hilbertOne = limitResidual + limitProjection := by
    unfold limitResidual
    abel
  have h := norm_add_sq_real limitResidual limitProjection
  rw [← hOne, hilbertOne_norm_sq, residual_projection_orthogonal,
    residual_norm_sq] at h
  linarith

theorem energy_lt_one : limitEnergy < 1 := by
  have h := energy_eq_limit_add 1
  rw [ProjectionSchur.energy_one] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [sq_nonneg ‖limitProjection - projection 1‖]

theorem residual_half_dilation_inner :
    inner ℝ limitResidual (dyadicHalfDilation limitResidual) =
      limitEnergy - first/2 := by
  have h := firstCoordinate_energy_identity
  rw [dyadicHalfDilation_apply, real_inner_smul_right]
  dsimp only [first]
  linarith

theorem one_half_dilation_residual_inner :
    inner ℝ hilbertOne (dyadicHalfDilation limitResidual) = limitEnergy/2 := by
  calc
    _ = inner ℝ (dyadicHalfDilation limitResidual) hilbertOne := real_inner_comm _ _
    _ = inner ℝ limitResidual (dyadicHalfAdjoint hilbertOne) :=
      (dyadicHalf_inner_adjoint _ _).symm
    _ = limitEnergy/2 := by
      rw [dyadicHalfAdjoint_one, real_inner_smul_right, limitResidual_inner_one]
      ring

theorem projection_half_adjoint_residual_inner :
    inner ℝ limitProjection (dyadicHalfAdjoint limitResidual) = 0 := by
  rw [dyadicHalf_inner_adjoint]
  exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _
    (half_dilation_mem_closed (closedSpace.starProjection_apply_mem hilbertOne))

theorem projection_half_dilation_residual_inner :
    inner ℝ limitProjection (dyadicHalfDilation limitResidual) =
      (first-limitEnergy)/2 := by
  have hF : limitProjection = hilbertOne - limitResidual := by
    unfold limitResidual
    abel
  rw [hF, inner_sub_left, one_half_dilation_residual_inner,
    residual_half_dilation_inner]
  ring

theorem residual_middle_inner :
    inner ℝ limitResidual (fullMiddle limitResidual) =
      11*limitEnergy/12-first := by
  have ha : inner ℝ limitResidual (dyadicHalfAdjoint limitResidual) =
      inner ℝ limitResidual (dyadicHalfDilation limitResidual) := by
    rw [dyadicHalf_inner_adjoint, real_inner_comm]
  simp only [fullMiddle, inner_sub_right, inner_add_right,
    real_inner_smul_right, ha, residual_half_dilation_inner,
    real_inner_self_eq_norm_sq, residual_norm_sq]
  ring

theorem projection_middle_inner :
    inner ℝ limitProjection (fullMiddle limitResidual) =
      (first-limitEnergy)/2 := by
  have hFr : inner ℝ limitProjection limitResidual = 0 := by
    rw [real_inner_comm, residual_projection_orthogonal]
  simp only [fullMiddle, inner_sub_right, inner_add_right,
    real_inner_smul_right, projection_half_dilation_residual_inner,
    projection_half_adjoint_residual_inner, hFr]
  ring

private theorem norm_sq_two_orthogonal_components
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r F U : E) (e q a b : ℝ)
    (hr : inner ℝ r r = e) (hF : inner ℝ F F = q)
    (hrF : inner ℝ r F = 0)
    (hrU : inner ℝ r U = a) (hFU : inner ℝ F U = b)
    (he : e ≠ 0) (hq : q ≠ 0) :
    ‖U‖^2 = a^2/e+b^2/q+‖U-(a/e)•r-(b/q)•F‖^2 := by
  have hFr : inner ℝ F r = 0 := by rw [real_inner_comm, hrF]
  have hUr : inner ℝ U r = a := by rw [real_inner_comm, hrU]
  have hUF : inner ℝ U F = b := by rw [real_inner_comm, hFU]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hr, hF, hrF, hFr, hrU, hFU, hUr, hUF]
  field_simp [he, hq]
  ring

theorem middle_norm_sq (he : 0 < limitEnergy) :
    ‖fullMiddle limitResidual‖^2 =
      (11*limitEnergy/12-first)^2 / limitEnergy +
      ((first-limitEnergy)/2)^2 / (1-limitEnergy) + ‖perpendicular‖^2 := by
  apply norm_sq_two_orthogonal_components
    limitResidual limitProjection (fullMiddle limitResidual)
    limitEnergy (1-limitEnergy) (11*limitEnergy/12-first) ((first-limitEnergy)/2)
  · rw [real_inner_self_eq_norm_sq, residual_norm_sq]
  · rw [real_inner_self_eq_norm_sq, projection_norm_sq]
  · exact residual_projection_orthogonal
  · exact residual_middle_inner
  · exact projection_middle_inner
  · exact ne_of_gt he
  · exact ne_of_gt (sub_pos.mpr energy_lt_one)

theorem polynomial_add (x y : ThresholdHilbert) :
    polynomial (x+y) = polynomial x + polynomial y := by
  simp only [polynomial, map_add]
  module

theorem moment_eq_polynomial_residual :
    moment = inner ℝ limitResidual (polynomial limitResidual) := by
  have hF : limitProjection ∈ closedSpace :=
    closedSpace.starProjection_apply_mem hilbertOne
  have hSF := half_dilation_mem_closed hF
  have hS2F := half_dilation_mem_closed hSF
  have hInner (x : ThresholdHilbert) (hx : x ∈ closedSpace) :
      inner ℝ limitResidual x = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal x hx
  have hp : inner ℝ limitResidual (polynomial limitProjection) = 0 := by
    simp only [polynomial, inner_add_right, inner_sub_right, real_inner_smul_right,
      hInner _ hF, hInner _ hSF, hInner _ hS2F, mul_zero, zero_sub, add_zero, neg_zero]
  have hOne : hilbertOne = limitResidual + limitProjection := by
    unfold limitResidual
    abel
  unfold moment vector
  rw [hOne, polynomial_add, inner_add_right, hp, add_zero]

theorem actual_polynomial_square (x : ThresholdHilbert) :
    inner ℝ x (polynomial x) =
      (23/24 : ℝ)*‖x‖^2 + 6*‖fullMiddle x‖^2 +
      (3/2 : ℝ)*(hilbertSequence x 1)^2 + (3/2 : ℝ)*dyadicPairVariance x := by
  exact dyadicHalf_square_identity x

theorem moment_orthogonal_decomposition (he : 0 < limitEnergy) :
    moment = (23/24 : ℝ)*limitEnergy +
      6*(11*limitEnergy/12-first)^2 / limitEnergy +
      6*((first-limitEnergy)/2)^2 / (1-limitEnergy) +
      (3/2 : ℝ)*first^2 + 6*‖perpendicular‖^2 +
      (3/2 : ℝ)*dyadicPairVariance limitResidual := by
  rw [moment_eq_polynomial_residual, actual_polynomial_square,
    residual_norm_sq, middle_norm_sq he]
  dsimp only [first]
  ring

private theorem scalar_leakage_completion {e z : ℝ} (he : 0 < e) (he1 : e < 1) :
    (23/24 : ℝ)*e+6*(11*e/12-z)^2/e+
      6*((z-e)/2)^2/(1-e)+(3/2 : ℝ)*z^2 =
    e*(23+19*e-27*e^2)/(6*(4-2*e-e^2))+
      (3*(4-2*e-e^2)/(2*e*(1-e)))*
        (z-e*(11-8*e)/(3*(4-2*e-e^2)))^2 := by
  have he0 : e ≠ 0 := ne_of_gt he
  have hq0 : 1-e ≠ 0 := ne_of_gt (sub_pos.mpr he1)
  have hd0 : 4-2*e-e^2 ≠ 0 := by
    have hd : 0 < 4-2*e-e^2 := by nlinarith
    exact ne_of_gt hd
  -- Keep this denominator as one atom while clearing fractions. Otherwise
  -- normalization of the inner square can reorder 2*e to e*2 and retain
  -- an inverse whose nonzero proof no longer matches syntactically.
  generalize hD : 4-2*e-e^2 = D
  have hD0 : D ≠ 0 := by
    rw [← hD]
    exact hd0
  field_simp [he0, hq0, hD0]
  rw [← hD]
  ring

/-- Actual equation (28), with its two orthogonal leakage remainders combined
into one exact full-space perpendicular remainder. All paired contrasts remain. -/
theorem canonical_completed_leakage (he : 0 < limitEnergy) :
    moment =
      limitEnergy*(23+19*limitEnergy-27*limitEnergy^2)/
        (6*(4-2*limitEnergy-limitEnergy^2))+
      (3*(4-2*limitEnergy-limitEnergy^2)/(2*limitEnergy*(1-limitEnergy)))*
        (first-limitEnergy*(11-8*limitEnergy)/
          (3*(4-2*limitEnergy-limitEnergy^2)))^2+
      6*‖perpendicular‖^2+(3/2 : ℝ)*dyadicPairVariance limitResidual := by
  rw [moment_orthogonal_decomposition he]
  have hs := scalar_leakage_completion (z := first) he energy_lt_one
  linarith

/-- The scalar energy hypothesis used by the checked algebra is proved here
from the actual operator, canonical projection, and nonnegative remainders. -/
theorem actual_leakage_energy_premise (he : 0 < limitEnergy) :
    23*limitEnergy^2*(1-limitEnergy)+
      (1-limitEnergy)*(12*first-11*limitEnergy)^2+
      36*limitEnergy*(1-limitEnergy)*first^2+
      36*limitEnergy*(first-limitEnergy)^2 ≤
      24*limitEnergy*(1-limitEnergy)*moment := by
  have hq : 0 < 1-limitEnergy := sub_pos.mpr energy_lt_one
  have hdrop : (23/24 : ℝ)*limitEnergy+
      6*(11*limitEnergy/12-first)^2/limitEnergy+
      6*((first-limitEnergy)/2)^2/(1-limitEnergy)+(3/2 : ℝ)*first^2 ≤ moment := by
    rw [moment_orthogonal_decomposition he]
    nlinarith [sq_nonneg ‖perpendicular‖,
      dyadicPairVariance_nonneg limitResidual]
  have hm := mul_le_mul_of_nonneg_left hdrop
    (show 0 ≤ 24*limitEnergy*(1-limitEnergy) by positivity)
  have hmul : (24*limitEnergy*(1-limitEnergy))*
      ((23/24 : ℝ)*limitEnergy+
      6*(11*limitEnergy/12-first)^2/limitEnergy+
      6*((first-limitEnergy)/2)^2/(1-limitEnergy)+(3/2 : ℝ)*first^2) =
    23*limitEnergy^2*(1-limitEnergy)+
      (1-limitEnergy)*(12*first-11*limitEnergy)^2+
      36*limitEnergy*(1-limitEnergy)*first^2+
      36*limitEnergy*(first-limitEnergy)^2 := by
    have he0 : limitEnergy ≠ 0 := ne_of_gt he
    have hq0 : 1-limitEnergy ≠ 0 := ne_of_gt hq
    field_simp [he0, hq0]
    ring
  rwa [hmul] at hm

theorem actual_leakage_lower_bound (he : 0 < limitEnergy) :
    limitEnergy*(23+19*limitEnergy-27*limitEnergy^2) ≤
      6*(4-2*limitEnergy-limitEnergy^2)*moment :=
  RiemannResearch.Analysis.DyadicAdjointDefect.leakage_lower_bound
    he energy_lt_one (actual_leakage_energy_premise he)

def leakage : ThresholdHilbert :=
  closedSpace.starProjection (dyadicHalfDilation limitResidual)

def compressedMiddle : ThresholdHilbert :=
  residualDilation 2 (by norm_num) limitResidual + dyadicHalfAdjoint limitResidual -
    (13/12 : ℝ) • limitResidual

def residualPerpendicular : ThresholdHilbert :=
  compressedMiddle -
    ((11*limitEnergy/12-first)/limitEnergy) • limitResidual

def projectionPerpendicular : ThresholdHilbert :=
  leakage - (((first-limitEnergy)/2)/(1-limitEnergy)) • limitProjection

/-- The actual adjoint preserves the orthogonal complement of the legal closure,
because the actual half-dilation preserves that closure. -/
theorem half_adjoint_mem_orthogonal {x : ThresholdHilbert}
    (hx : x ∈ closedSpaceᗮ) : dyadicHalfAdjoint x ∈ closedSpaceᗮ := by
  apply (closedSpace.mem_orthogonal _).mpr
  intro y hy
  rw [dyadicHalf_inner_adjoint]
  exact (closedSpace.mem_orthogonal _).mp hx _ (half_dilation_mem_closed hy)

theorem compressedMiddle_eq :
    compressedMiddle = fullMiddle limitResidual - leakage := by
  have hR : residualDilation 2 (by norm_num) limitResidual =
      dyadicHalfDilation limitResidual -
        closedSpace.starProjection (dyadicHalfDilation limitResidual) := by
    rw [residualDilation_apply, Submodule.starProjection_orthogonal]
    change ((2 : ℝ)⁻¹) • hilbertDilation 2 (by norm_num) limitResidual -
      closedSpace.starProjection
        (((2 : ℝ)⁻¹) • hilbertDilation 2 (by norm_num) limitResidual) = _
    norm_num [dyadicHalfDilation_apply]
  unfold compressedMiddle fullMiddle leakage
  rw [hR]
  abel

theorem residualPerpendicular_mem_orthogonal :
    residualPerpendicular ∈ closedSpaceᗮ := by
  unfold residualPerpendicular compressedMiddle
  exact closedSpaceᗮ.sub_mem
    (closedSpaceᗮ.sub_mem
      (closedSpaceᗮ.add_mem
        (residualDilation_mem_orthogonal 2 (by norm_num) limitResidual)
        (half_adjoint_mem_orthogonal limitResidual_mem_orthogonal))
      (closedSpaceᗮ.smul_mem _ limitResidual_mem_orthogonal))
    (closedSpaceᗮ.smul_mem _ limitResidual_mem_orthogonal)

theorem projectionPerpendicular_mem_closed :
    projectionPerpendicular ∈ closedSpace := by
  unfold projectionPerpendicular leakage
  exact closedSpace.sub_mem (closedSpace.starProjection_apply_mem _)
    (closedSpace.smul_mem _ (closedSpace.starProjection_apply_mem hilbertOne))

theorem perpendicular_eq_two_remainders :
    perpendicular = residualPerpendicular + projectionPerpendicular := by
  unfold perpendicular residualPerpendicular projectionPerpendicular
  rw [compressedMiddle_eq]
  abel

/-- The single full-space square is exactly the sum of the two paper squares;
neither projection leakage nor the compressed middle remainder is discarded. -/
theorem perpendicular_norm_sq_split :
    ‖perpendicular‖^2 =
      ‖residualPerpendicular‖^2+‖projectionPerpendicular‖^2 := by
  have ho : inner ℝ residualPerpendicular projectionPerpendicular = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp residualPerpendicular_mem_orthogonal _
      projectionPerpendicular_mem_closed
  rw [perpendicular_eq_two_remainders, norm_add_sq_real, ho]
  ring

/-- Actual equation (28), with its original two distinct norm squares and the
full summable pair-variance series. The cofinal arithmetic provider is separate. -/
theorem canonical_completed_leakage_two_remainders (he : 0 < limitEnergy) :
    moment =
      limitEnergy*(23+19*limitEnergy-27*limitEnergy^2)/
        (6*(4-2*limitEnergy-limitEnergy^2))+
      (3*(4-2*limitEnergy-limitEnergy^2)/(2*limitEnergy*(1-limitEnergy)))*
        (first-limitEnergy*(11-8*limitEnergy)/
          (3*(4-2*limitEnergy-limitEnergy^2)))^2+
      6*‖residualPerpendicular‖^2+6*‖projectionPerpendicular‖^2+
      (3/2 : ℝ)*dyadicPairVariance limitResidual := by
  rw [canonical_completed_leakage he, perpendicular_norm_sq_split]
  ring

/-- The canonical moment in equation (28) is the defect of the actual two
optimal coefficients, whose finite versions come from the complete inverse. -/
theorem moment_eq_coefficient_defect :
    moment = 4 - 3 * limitCoefficient 2 - limitCoefficient 3 := by
  have hhalf (x : ThresholdHilbert) :
      dyadicHalfDilation x = (1/2:ℝ) • doubleDilation x := rfl
  have hv : vector = (-3:ℝ) • mobiusRieszHilbert 2 - mobiusRieszHilbert 3 := by
    rw [twoThreeRiesz_eq_dilation]
    unfold vector polynomial
    simp only [hhalf, map_smul, smul_smul]
    module
  unfold moment
  rw [hv, inner_sub_right, real_inner_smul_right]
  have hi (m : ℕ) : inner ℝ limitResidual (mobiusRieszHilbert m) =
      mobiusDifferenceCLM m limitResidual := by
    rw [real_inner_comm]
    exact mobiusRieszHilbert_inner m limitResidual
  rw [hi 2, hi 3]
  have h2 := limitCoefficient_eq_residual 2 (by decide)
  have h3 := limitCoefficient_eq_residual 3 (by decide)
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three] at h2 h3
  simp only [mobiusDifferenceCLM_apply]
  linarith

/-- The actual Hilbert-to-scalar energy premise, now including the zero-energy
case. It contains no supplied analytic or arithmetic cancellation hypothesis. -/
theorem limiting_twoThree_leakage_energy_budget :
    23*limitEnergy^2*(1-limitEnergy)+
      (1-limitEnergy)*(12*first-11*limitEnergy)^2+
      36*limitEnergy*(1-limitEnergy)*first^2+
      36*limitEnergy*(first-limitEnergy)^2 ≤
      24*limitEnergy*(1-limitEnergy)*
        (4-3*limitCoefficient 2-limitCoefficient 3) := by
  by_cases hz : limitEnergy = 0
  · have hr := limitResidual_zero_iff_energy_zero.mpr hz
    have hfirst : first = 0 := by
      unfold first
      rw [hr]
      exact congrFun (hilbertSequenceLinear.map_zero) 1
    simp [hz, hfirst]
  · have he : 0 < limitEnergy := lt_of_le_of_ne (sq_nonneg ‖limitResidual‖) (Ne.symm hz)
    have h := actual_leakage_energy_premise he
    rwa [moment_eq_coefficient_defect] at h

/-- The verified scalar compensated contradiction is instantiated with the
proved actual canonical energy premise, rather than a supplied energy bound. -/
theorem energy_zero_of_compensated_upper
    (hc : 24*moment ≤ 23*limitEnergy) : limitEnergy = 0 := by
  by_cases hz : limitEnergy = 0
  · exact hz
  · have hn : 0 ≤ limitEnergy := sq_nonneg ‖limitResidual‖
    have he : 0 < limitEnergy := lt_of_le_of_ne hn (Ne.symm hz)
    exact RiemannResearch.Analysis.DyadicAdjointDefect.zero_of_compensated_upper
      hn energy_lt_one (actual_leakage_lower_bound he) hc

/-- Equation (32): the actual compensated limit retains a strict quadratic
surplus whenever the actual canonical energy is positive. -/
theorem compensatedLimit_le_negative_surplus (he : 0 < limitEnergy) :
    twoThreeCompensatedLimit ≤
      -(limitEnergy^2*(122-85*limitEnergy)/
        (24*(4-2*limitEnergy-limitEnergy^2))) := by
  have hJ := actual_leakage_lower_bound he
  have hd : 0 < 4-2*limitEnergy-limitEnergy^2 := by
    have h1 := energy_lt_one
    nlinarith
  have ht : twoThreeCompensatedLimit = (23/24:ℝ)*limitEnergy - moment := by
    rw [moment_eq_coefficient_defect]
    unfold twoThreeCompensatedLimit
    ring
  rw [ht]
  rw [← neg_div]
  apply (le_div_iff₀ (show 0 < 24*(4-2*limitEnergy-limitEnergy^2) by positivity)).mpr
  nlinarith [hJ]

end RiemannResearch.RH.Pareto.DyadicCanonicalLeakage
