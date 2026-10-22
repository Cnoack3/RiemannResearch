import RiemannResearch.RH.DyadicKernelJumpEnergy
import RiemannResearch.Analysis.DyadicAdjointDefect

/-!
# The actual dyadic adjoint defect in the complete Pareto space

Source: FixedGramAdjointContinuation20261006.md, equations (21), (22), and
(37). Bagchi's Pareto-space dilation setting motivates these statements:
https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf .
The proofs reuse the project's actual bounded dilation, adjoint, block
projection, and summable infinite jump energy. No operator, summability,
or scalar energy provider is assumed. No approximation or RH is proved.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- The full physical weighted pair-variance series, indexed by m=n+1. -/
def dyadicPairVariance (x : ThresholdHilbert) : ℝ :=
  ∑' n : ℕ,
    (hilbertSequence x (2*(n+1)+1)-hilbertSequence x (2*(n+1)))^2 /
      (2*((n:ℝ)+1)+1)^2

theorem dyadicPairVariance_eq_kernel_series (x : ThresholdHilbert) :
    dyadicPairVariance x = 2 * ∑' n : ℕ,
      (hilbertSequence x (2*(n+1)+1)-hilbertSequence x (2*(n+1)))^2 /
        (2*(2*((n:ℝ)+1)+1)^2) := by
  rw [dyadicPairVariance, ← tsum_mul_left]
  apply tsum_congr
  intro n
  field_simp

theorem dyadicPairVariance_summable (x : ThresholdHilbert) :
    Summable (fun n : ℕ =>
      (hilbertSequence x (2*(n+1)+1)-hilbertSequence x (2*(n+1)))^2 /
        (2*((n:ℝ)+1)+1)^2) := by
  apply ((dyadicKernelDefect_jump_energy_summable x).mul_left (2:ℝ)).congr
  intro n
  field_simp

theorem dyadicPairVariance_nonneg (x : ThresholdHilbert) :
    0 ≤ dyadicPairVariance x := by
  exact tsum_nonneg (fun n => div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Equation (21), specialized from the actual weighted adjoint block law. -/
theorem dyadicHalfAdjoint_coordinate (x : ThresholdHilbert) (m : ℕ) (hm : 0 < m) :
    hilbertSequence (dyadicHalfAdjoint x) m =
      ((m:ℝ)+1)/(2*(2*(m:ℝ)+1))*hilbertSequence x (2*m) +
      (m:ℝ)/(2*(2*(m:ℝ)+1))*hilbertSequence x (2*m+1) := by
  have hI : Finset.Ico (2*m) (2*(m+1)) = {2*m, 2*m+1} := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [dyadicHalfAdjoint_apply, hilbertSequence_smul]
  change (1/2:ℝ) * hilbertSequence (hilbertDilationAdjoint 2 (by norm_num) x) m = _
  rw [hilbertDilationAdjoint_coordinate 2 m (by norm_num) hm,
    hI, Finset.sum_pair (by omega : 2*m ≠ 2*m+1)]
  unfold positiveWeight
  push_cast
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hm1 : (m:ℝ)+1 ≠ 0 := by positivity
  have h2m : 2*(m:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem dyadicHalf_inner_adjoint (x y : ThresholdHilbert) :
    inner ℝ x (dyadicHalfAdjoint y) = inner ℝ (dyadicHalfDilation x) y := by
  rw [dyadicHalfAdjoint_apply, dyadicHalfDilation_apply,
    real_inner_smul_right, real_inner_smul_left]
  congr 1
  exact ContinuousLinearMap.adjoint_inner_right
    (hilbertDilationContinuous 2 (by norm_num)) x y

theorem dyadicHalfAdjoint_one :
    dyadicHalfAdjoint hilbertOne = (1/2:ℝ) • hilbertOne := by
  rw [dyadicHalfAdjoint_apply, hilbertDilationAdjoint_one]

/-- Equation (22): both the first-site square and the whole convergent series
are retained, in the actual complete Hilbert space. -/
theorem dyadicHalfAdjoint_defect (x : ThresholdHilbert) :
    (1/2:ℝ)*‖x‖^2 - ‖dyadicHalfAdjoint x‖^2 =
      (hilbertSequence x 1)^2/4 + (1/4:ℝ)*dyadicPairVariance x := by
  have hb : ‖hilbertBlockProjection 2 (by norm_num) x‖^2 =
      2*‖dyadicHalfAdjoint x‖^2 := by
    rw [hilbertBlockProjection_apply, dyadicHalfAdjoint_apply,
      norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, hilbertDilation_norm_sq]
    norm_num
    ring
  have hp := hilbertBlockProjection_pythagoras 2 (by norm_num) x
  rw [hb, ← dyadicKernelDefect_apply, dyadicKernelDefect_norm_sq_jumps] at hp
  have hv := dyadicPairVariance_eq_kernel_series x
  linarith

/-- Equation (37), obtained by instantiating the verified adjoint-square
algebra with the actual operator and its actual infinite norm defect. -/
theorem dyadicHalf_square_identity (x : ThresholdHilbert) :
    inner ℝ x ((14:ℝ) • x - (26:ℝ) • dyadicHalfDilation x +
      (12:ℝ) • dyadicHalfDilation (dyadicHalfDilation x)) =
      (23/24:ℝ)*‖x‖^2 +
      6*‖dyadicHalfDilation x+dyadicHalfAdjoint x-(13/12:ℝ) • x‖^2 +
      (3/2:ℝ)*(hilbertSequence x 1)^2 +
      (3/2:ℝ)*dyadicPairVariance x := by
  have h1 : inner ℝ x (dyadicHalfDilation x) = inner ℝ x (dyadicHalfAdjoint x) := by
    rw [dyadicHalf_inner_adjoint, real_inner_comm]
  have h2 : inner ℝ x (dyadicHalfDilation (dyadicHalfDilation x)) =
      inner ℝ (dyadicHalfDilation x) (dyadicHalfAdjoint x) := by
    rw [dyadicHalf_inner_adjoint]
    exact real_inner_comm _ _
  have h := RiemannResearch.Analysis.DyadicAdjointDefect.adjoint_square_identity
    x (dyadicHalfDilation x) (dyadicHalfAdjoint x)
      (dyadicHalfDilation (dyadicHalfDilation x)) h1 h2
  have hd := dyadicHalfAdjoint_defect x
  have hs := dyadicHalfDilation_norm_sq x
  linarith

end RiemannResearch.RH.Pareto
