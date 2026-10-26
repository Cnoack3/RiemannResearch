/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeFirstCoordinate
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QParityConditionalTarget
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Complete reciprocal remainders and actual squarefree parity bounds

Source: the user-provided moving-head research handoff, 26 October 2026.
The argument combines the exact centered reciprocal identity with the two
parity moments of an orthogonal projection residual. The full nonnegative
tail is retained before the norm estimates; no RH or head bound is assumed.
-/

noncomputable section
namespace RiemannResearch.RH.QParityReciprocalBounds
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QShiftedReciprocal QSquarefreeSmoothedProjection
open QSquarefreeFirstCoordinate QDivisibilityDensity QDivisorLegality

private def oddVector : QHilbert := (2 : ℝ) • qResidue 2

private theorem oddVector_eq : oddVector = qOne - qDivisor 2 := by
  rw [qDivisor_two_eq]
  unfold oddVector
  abel

private theorem oddVector_first : qSequence oddVector 1 = 1 := by
  change qSequenceLinear ((2 : ℝ) • qResidue 2) 1 = 1
  rw [map_smul]
  change 2 * qSequence (qResidue 2) 1 = 1
  rw [qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

private theorem oddVector_norm_sq : ‖oddVector‖^2 = (3 / 4 : ℝ) := by
  have heo : inner ℝ qOne (qDivisor 2) = (1 / 4 : ℝ) := by
    rw [qOne_inner_qDivisor 2 (by decide)]
    norm_num
  have hoe : inner ℝ (qDivisor 2) qOne = (1 / 4 : ℝ) := by
    rw [real_inner_comm]
    exact heo
  rw [oddVector_eq, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
    qOne_norm_sq, qDivisor_norm_sq 2 (by decide), heo, hoe]
  norm_num

/-- The first physical coordinate after imposing the complete odd-mean equation. -/
theorem first_sq_le_of_odd_orthogonal (r : QHilbert)
    (hr : inner ℝ r ((2 : ℝ) • qResidue 2) = 0) :
    (qSequence r 1)^2 ≤ (zetaTwo - 4 / 3) * ‖r‖^2 := by
  let k : QHilbert := firstEvaluationVector - (4 / 3 : ℝ) • oddVector
  have hfirst : inner ℝ firstEvaluationVector oddVector = 1 := by
    rw [real_inner_comm, inner_firstEvaluationVector, oddVector_first]
  have hfirst' : inner ℝ oddVector firstEvaluationVector = 1 := by
    rw [inner_firstEvaluationVector, oddVector_first]
  have hk : ‖k‖^2 = zetaTwo - 4 / 3 := by
    change ‖firstEvaluationVector - (4 / 3 : ℝ) • oddVector‖^2 = _
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    rw [firstEvaluationVector_norm_sq, oddVector_norm_sq]
    nlinarith [hfirst, hfirst']
  have hrk : inner ℝ r k = qSequence r 1 := by
    change inner ℝ r (firstEvaluationVector - (4 / 3 : ℝ) • oddVector) = _
    rw [inner_sub_right, real_inner_smul_right, inner_firstEvaluationVector]
    change qSequence r 1 - (4 / 3 : ℝ) *
      inner ℝ r ((2 : ℝ) • qResidue 2) = qSequence r 1
    rw [hr]
    ring
  have hcs := abs_real_inner_le_norm r k
  have hs := mul_self_le_mul_self (abs_nonneg (inner ℝ r k)) hcs
  have hs' : (inner ℝ r k)^2 ≤ ‖r‖^2 * ‖k‖^2 := by
    simpa only [← pow_two, sq_abs, mul_pow] using hs
  rw [hrk, hk] at hs'
  nlinarith

private theorem oneSixth_defect_scalar (x d : ℝ) (hd : d ≠ 0) :
    (1 / (3*d) - 1 / d^2) * x^2 =
      (1/36 : ℝ) * x^2 - (x/d - (1/6 : ℝ)*x)^2 := by
  field_simp [hd] <;> ring

/-- The full nonnegative defect after isolating physical site one. -/
def B_oneSixth_tailDefect (f : QHilbert) : ℝ :=
  ∑' n : ℕ, (1 / (3*((n:ℝ)+3)) - 1 / ((n:ℝ)+3)^2) * (f (n+1))^2

private theorem oneSixth_tailDefect_term (f : QHilbert) (n : ℕ) :
    (1 / (3*((n:ℝ)+3)) - 1 / ((n:ℝ)+3)^2) * (f (n+1))^2 =
      (1/36 : ℝ) * (f (n+1))^2 -
        ((B f - (1/6 : ℝ) • f) (n+1))^2 := by
  change (1 / (3*((n:ℝ)+3)) - 1 / ((n:ℝ)+3)^2) * (f (n+1))^2 =
    (1/36 : ℝ) * (f (n+1))^2 -
      (f (n+1) / (((n+1 : ℕ) : ℝ)+2) - (1/6 : ℝ)*f (n+1))^2
  have hcast : (((n+1 : ℕ) : ℝ)+2) = (n:ℝ)+3 := by
    push_cast <;> ring
  rw [hcast]
  exact oneSixth_defect_scalar (f (n+1)) ((n:ℝ)+3) (by positivity)

theorem B_oneSixth_tailDefect_summable (f : QHilbert) :
    Summable (fun n : ℕ =>
      (1 / (3*((n:ℝ)+3)) - 1 / ((n:ℝ)+3)^2) * (f (n+1))^2) := by
  have hf : Summable (fun n : ℕ => (1/36 : ℝ) * (f (n+1))^2) :=
    ((summable_nat_add_iff 1).mpr (qCoordinate_square_summable f)).mul_left _
  have hb : Summable (fun n : ℕ => ((B f - (1/6 : ℝ) • f) (n+1))^2) :=
    (summable_nat_add_iff 1).mpr
      (qCoordinate_square_summable (B f - (1/6 : ℝ) • f))
  apply (hf.sub hb).congr
  intro n
  exact (oneSixth_tailDefect_term f n).symm

theorem B_oneSixth_tailDefect_nonneg (f : QHilbert) :
    0 ≤ B_oneSixth_tailDefect f := by
  apply tsum_nonneg
  intro n
  have hd : 0 < (n:ℝ)+3 := by positivity
  have hlo : 0 ≤ 1 / ((n:ℝ)+3) := by positivity
  have hhi : 1 / ((n:ℝ)+3) ≤ (1/3 : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : 1 / (3*((n:ℝ)+3)) - 1 / ((n:ℝ)+3)^2 =
      (1 / ((n:ℝ)+3)) * (1/3 - 1 / ((n:ℝ)+3)) := by
    field_simp [ne_of_gt hd] <;> ring
  rw [he]
  exact mul_nonneg (mul_nonneg hlo (sub_nonneg.mpr hhi)) (sq_nonneg _)

/-- Exact complete-tail decomposition before the centered estimate. -/
theorem B_centered_oneSixth_exact (f : QHilbert) :
    ‖B f - (1/6 : ℝ) • f‖^2 =
      (1/36 : ℝ) * ‖f‖^2 + (1/12 : ℝ) * (f 0)^2 -
        B_oneSixth_tailDefect f := by
  let h : QHilbert := B f - (1/6 : ℝ) • f
  have hf : Summable (fun n : ℕ => (1/36 : ℝ) * (f (n+1))^2) :=
    ((summable_nat_add_iff 1).mpr (qCoordinate_square_summable f)).mul_left _
  have hb : Summable (fun n : ℕ => (h (n+1))^2) :=
    (summable_nat_add_iff 1).mpr (qCoordinate_square_summable h)
  have hdef : B_oneSixth_tailDefect f =
      (1/36 : ℝ) * (∑' n : ℕ, (f (n+1))^2) -
        ∑' n : ℕ, (h (n+1))^2 := by
    unfold B_oneSixth_tailDefect
    simp_rw [oneSixth_tailDefect_term]
    change (∑' n : ℕ, ((1/36 : ℝ) * (f (n+1))^2 - (h (n+1))^2)) = _
    rw [hf.tsum_sub hb, tsum_mul_left]
  have hzero : h 0 = (1/3 : ℝ) * f 0 := by
    change f 0 / (((0:ℕ):ℝ)+2) - (1/6 : ℝ)*f 0 = _
    norm_num <;> ring
  have hn : ‖h‖^2 = (h 0)^2 + ∑' n : ℕ, (h (n+1))^2 := by
    rw [qNorm_sq, (qCoordinate_square_summable h).tsum_eq_zero_add]
  have fn : ‖f‖^2 = (f 0)^2 + ∑' n : ℕ, (f (n+1))^2 := by
    rw [qNorm_sq, (qCoordinate_square_summable f).tsum_eq_zero_add]
  change ‖h‖^2 = _
  rw [hzero] at hn
  nlinarith [hdef, hn, fn]

/-- The centered estimate drops only the named nonnegative complete tail. -/
theorem B_centered_oneSixth_norm_sq (f : QHilbert) :
    ‖B f - (1 / 6 : ℝ) • f‖^2 ≤
      (1 / 36 : ℝ) * ‖f‖^2 + (1 / 12 : ℝ) * (f 0)^2 := by
  have he := B_centered_oneSixth_exact f
  have hn := B_oneSixth_tailDefect_nonneg f
  nlinarith

/-- Division-free parity improvement of the centered multiplier estimate. -/
theorem B_centered_parity_energy_bound (r : QHilbert)
    (hr : inner ℝ r ((2 : ℝ) • qResidue 2) = 0) :
    9 * zetaTwo * ‖B r - (1/6 : ℝ) • r‖^2 ≤ (zetaTwo-1) * ‖r‖^2 := by
  have hf := first_sq_le_of_odd_orthogonal r hr
  have hc := B_centered_oneSixth_norm_sq r
  have hw := qSequence_weighted_square r 0
  norm_num only [positiveQWeight, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
    zero_add, one_pow, mul_one] at hw
  have hzero : zetaTwo * (r 0)^2 = (qSequence r 1)^2 := by
    calc
      zetaTwo * (r 0)^2 = zetaTwo * ((1 / zetaTwo) * (qSequence r 1)^2) := by rw [hw]
      _ = (qSequence r 1)^2 := by field_simp [ne_of_gt zetaTwo_pos]
  have hm := mul_le_mul_of_nonneg_left hc zetaTwo_pos.le
  nlinarith [hf, hm, hzero]

/-- Every projection containing the parity atom obeys a stronger off-diagonal
bound than the unrestricted 1/4 estimate. -/
theorem projected_B_parity_energy_bound (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (h2 : qResidue 2 ∈ S)
    {r : QHilbert} (hr : r ∈ Sᗮ) :
    9 * zetaTwo * ‖S.starProjection (B r)‖^2 ≤ (zetaTwo-1) * ‖r‖^2 := by
  have h2r := Submodule.inner_right_of_mem_orthogonal h2 hr
  have hodd : inner ℝ r ((2 : ℝ) • qResidue 2) = 0 := by
    rw [real_inner_smul_right, real_inner_comm, h2r]
    ring
  have hz : S.starProjection r = 0 := by
    have h1 := Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem r) hr
    have h2' := Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem r)
      (Submodule.sub_starProjection_mem_orthogonal (K := S) r)
    rw [inner_sub_right, h1, real_inner_self_eq_norm_sq] at h2'
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (S.starProjection r)]
  have he : S.starProjection (B r - (1/6 : ℝ) • r) = S.starProjection (B r) := by
    simp only [map_sub, map_smul, hz, smul_zero, sub_zero]
  have hp : ‖S.starProjection (B r)‖ ≤ ‖B r - (1/6 : ℝ) • r‖ := by
    rw [← he]
    calc
      _ ≤ ‖S.starProjection‖ * ‖B r - (1/6 : ℝ) • r‖ := S.starProjection.le_opNorm _
      _ ≤ ‖B r - (1/6 : ℝ) • r‖ := by
        simpa using mul_le_mul_of_nonneg_right
          (Submodule.starProjection_norm_le S) (norm_nonneg _)
  have hp2 := mul_self_le_mul_self (norm_nonneg (S.starProjection (B r))) hp
  have hm := mul_le_mul_of_nonneg_left hp2 (show (0 : ℝ) ≤ 9 * zetaTwo from
    mul_nonneg (by norm_num) zetaTwo_pos.le)
  nlinarith [B_centered_parity_energy_bound r hodd, hm]

theorem movingCorrection_parity_energy_bound (N : ℕ) (hN : 0 < N) :
    9 * zetaTwo * ‖movingCorrection N‖^2 ≤ (zetaTwo-1) * error N := by
  exact projected_B_parity_energy_bound (stage N)
    (QParityConditionalTarget.qResidue_two_mem_stage N hN)
    (residual_mem_orthogonal N)


/-- The actual projection residual has an extra exact even-mean constraint. -/
theorem first_sq_le_of_parity_moments (r : QHilbert)
    (hodd : inner ℝ r ((2 : ℝ) • qResidue 2) = 0)
    (heven : inner ℝ r (qDivisor 2) = ‖r‖^2) :
    (qSequence r 1)^2 ≤ (zetaTwo - 4/3) * (‖r‖^2 - 4 * (‖r‖^2)^2) := by
  let w : QHilbert := r - (4 * ‖r‖^2) • qDivisor 2
  have heo : inner ℝ (qDivisor 2) ((2 : ℝ) • qResidue 2) = 0 := by
    rw [real_inner_smul_right, real_inner_comm]
    rw [qResidue_inner_qDivisor_eq_zero 2 2 (by decide) (dvd_refl _)]
    ring
  have hwo : inner ℝ w ((2 : ℝ) • qResidue 2) = 0 := by
    change inner ℝ (r - (4 * ‖r‖^2) • qDivisor 2) _ = 0
    rw [inner_sub_left, real_inner_smul_left, hodd, heo]
    ring
  have hwn : ‖w‖^2 = ‖r‖^2 - 4 * (‖r‖^2)^2 := by
    change ‖r - (4 * ‖r‖^2) • qDivisor 2‖^2 = _
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right, heven, qDivisor_norm_sq 2 (by decide)]
    norm_num
    ring
  have hwfirst : qSequence w 1 = qSequence r 1 := by
    change qSequenceLinear (r - (4 * ‖r‖^2) • qDivisor 2) 1 = _
    rw [map_sub, map_smul]
    change qSequence r 1 - (4 * ‖r‖^2) * qSequence (qDivisor 2) 1 = _
    rw [qSequence_qDivisor]
    norm_num [positiveDivisor]
  have h := first_sq_le_of_odd_orthogonal w hwo
  rwa [hwfirst, hwn] at h

theorem B_centered_actual_parity_energy_bound (r : QHilbert)
    (hodd : inner ℝ r ((2 : ℝ) • qResidue 2) = 0)
    (heven : inner ℝ r (qDivisor 2) = ‖r‖^2) :
    9 * zetaTwo * ‖B r - (1/6 : ℝ) • r‖^2 ≤
      (zetaTwo-1) * ‖r‖^2 - (3*zetaTwo-4) * (‖r‖^2)^2 := by
  have hf := first_sq_le_of_parity_moments r hodd heven
  have hc := B_centered_oneSixth_norm_sq r
  have hw := qSequence_weighted_square r 0
  norm_num only [positiveQWeight, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
    zero_add, one_pow, mul_one] at hw
  have hzero : zetaTwo * (r 0)^2 = (qSequence r 1)^2 := by
    calc
      zetaTwo * (r 0)^2 = zetaTwo * ((1 / zetaTwo) * (qSequence r 1)^2) := by rw [hw]
      _ = (qSequence r 1)^2 := by field_simp [ne_of_gt zetaTwo_pos]
  have hm := mul_le_mul_of_nonneg_left hc zetaTwo_pos.le
  nlinarith [hf, hm, hzero]

/-- The two exact parity moments of a projection-of-one residual. -/
theorem projectionResidual_parity_moments (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (h2 : qResidue 2 ∈ S) :
    inner ℝ (qOne - S.starProjection qOne) ((2 : ℝ) • qResidue 2) = 0 ∧
    inner ℝ (qOne - S.starProjection qOne) (qDivisor 2) =
      ‖qOne - S.starProjection qOne‖^2 := by
  let r : QHilbert := qOne - S.starProjection qOne
  have hr : r ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal qOne
  have h2r : inner ℝ (qResidue 2) r = 0 :=
    Submodule.inner_right_of_mem_orthogonal h2 hr
  have hro : inner ℝ r (qResidue 2) = 0 := by
    rw [real_inner_comm]
    exact h2r
  have hodd : inner ℝ r ((2 : ℝ) • qResidue 2) = 0 := by
    rw [real_inner_smul_right, hro]
    ring
  have hp : inner ℝ r (S.starProjection qOne) = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (S.starProjection_apply_mem qOne) hr
  have hmean : inner ℝ r qOne = ‖r‖^2 := by
    calc
      inner ℝ r qOne = inner ℝ r r := by
        change inner ℝ r qOne = inner ℝ r (qOne - S.starProjection qOne)
        rw [inner_sub_right, hp, sub_zero]
      _ = _ := real_inner_self_eq_norm_sq r
  have heven : inner ℝ r (qDivisor 2) = ‖r‖^2 := by
    rw [qDivisor_two_eq, inner_sub_right, real_inner_smul_right, hmean, hro]
    ring
  exact ⟨hodd, heven⟩

/-- Projection contraction after a scalar shift of the annihilated residual. -/
theorem projected_B_centered_norm_sq_le (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] {r : QHilbert} (hr : r ∈ Sᗮ) :
    ‖S.starProjection (B r)‖^2 ≤ ‖B r - (1/6 : ℝ) • r‖^2 := by
  have hz : S.starProjection r = 0 := by
    have h1 := Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem r) hr
    have h2' := Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem r)
      (Submodule.sub_starProjection_mem_orthogonal (K := S) r)
    rw [inner_sub_right, h1, real_inner_self_eq_norm_sq] at h2'
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (S.starProjection r)]
  have he : S.starProjection (B r - (1/6 : ℝ) • r) = S.starProjection (B r) := by
    simp only [map_sub, map_smul, hz, smul_zero, sub_zero]
  have hp : ‖S.starProjection (B r)‖ ≤ ‖B r - (1/6 : ℝ) • r‖ := by
    rw [← he]
    calc
      _ ≤ ‖S.starProjection‖ * ‖B r - (1/6 : ℝ) • r‖ := S.starProjection.le_opNorm _
      _ ≤ ‖B r - (1/6 : ℝ) • r‖ := by
        simpa using mul_le_mul_of_nonneg_right
          (Submodule.starProjection_norm_le S) (norm_nonneg _)
  have hp2 := mul_self_le_mul_self (norm_nonneg (S.starProjection (B r))) hp
  simpa only [← pow_two] using hp2

/-- The actual source gives a quadratic improvement beyond parity orthogonality
alone. The displayed energies retain the entire infinite Q-weighted tail. -/
theorem projected_actual_B_parity_energy_bound (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (h2 : qResidue 2 ∈ S) :
    9 * zetaTwo * ‖S.starProjection (B (qOne - S.starProjection qOne))‖^2 ≤
      (zetaTwo-1) * ‖qOne - S.starProjection qOne‖^2 -
        (3*zetaTwo-4) * (‖qOne - S.starProjection qOne‖^2)^2 := by
  let r : QHilbert := qOne - S.starProjection qOne
  have hr : r ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal qOne
  obtain ⟨hodd, heven⟩ := projectionResidual_parity_moments S h2
  have hc := B_centered_actual_parity_energy_bound r hodd heven
  have hp := projected_B_centered_norm_sq_le S hr
  have hm := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 9 * zetaTwo from
    mul_nonneg (by norm_num) zetaTwo_pos.le)
  change 9 * zetaTwo * ‖S.starProjection (B r)‖^2 ≤
    (zetaTwo-1) * ‖r‖^2 - (3*zetaTwo-4) * (‖r‖^2)^2
  exact hm.trans hc

/-- All nonempty masked squarefree stages, including unchanged masked stages. -/
theorem movingCorrection_actual_parity_energy_bound (N : ℕ) (hN : 0 < N) :
    9 * zetaTwo * ‖movingCorrection N‖^2 ≤
      (zetaTwo-1) * error N - (3*zetaTwo-4) * (error N)^2 := by
  simpa only [movingCorrection, error, ZetaTwoOptimizerStage.residual, optimizer] using
    projected_actual_B_parity_energy_bound (stage N)
      (QParityConditionalTarget.qResidue_two_mem_stage N hN)

/-- The same unconditional estimate holds for the actual limiting correction. -/
theorem correction_actual_parity_energy_bound :
    9 * zetaTwo * ‖correction‖^2 ≤
      (zetaTwo-1) * ‖limitingResidual‖^2 -
        (3*zetaTwo-4) * (‖limitingResidual‖^2)^2 := by
  simpa only [correction, limitingResidual] using
    projected_actual_B_parity_energy_bound ZetaTwoOptimizerStage.closure
      QParityConditionalTarget.qResidue_two_mem_closure

theorem residual_first_sq_actual_parity_bound (N : ℕ) (hN : 0 < N) :
    (qSequence (residual N) 1)^2 ≤
      (zetaTwo - 4/3) * (error N - 4 * (error N)^2) := by
  obtain ⟨hodd, heven⟩ := projectionResidual_parity_moments (stage N)
    (QParityConditionalTarget.qResidue_two_mem_stage N hN)
  simpa only [error, ZetaTwoOptimizerStage.residual, optimizer] using
    first_sq_le_of_parity_moments (qOne - (stage N).starProjection qOne) hodd heven

theorem limitingResidual_first_sq_actual_parity_bound :
    (qSequence limitingResidual 1)^2 ≤
      (zetaTwo - 4/3) * (‖limitingResidual‖^2 - 4 * (‖limitingResidual‖^2)^2) := by
  obtain ⟨hodd, heven⟩ := projectionResidual_parity_moments ZetaTwoOptimizerStage.closure
    QParityConditionalTarget.qResidue_two_mem_closure
  exact first_sq_le_of_parity_moments limitingResidual hodd heven

end RiemannResearch.RH.QParityReciprocalBounds
