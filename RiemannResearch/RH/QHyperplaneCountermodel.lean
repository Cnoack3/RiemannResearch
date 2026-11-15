/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QHeadProjectedResidual
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A matched Q/Pareto hyperplane countermodel

Source: the reciprocal-head investigation, 7 November 2026, Section 7.
The measures, complete physical sequences, and reciprocal multiplier are the
actual repository objects. Only the legal subspace is changed, to Q mean zero.
The explicit residuals are certified as the actual two orthogonal projections.
The existing identifier QShiftedReciprocal.B is the multiplier R, not dQ/dP.
-/

noncomputable section
open scoped Topology
namespace RiemannResearch.RH.QHyperplaneCountermodel
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto
open QFiniteSupportDualCriterion

/-- The inverse-cube Q moment, equal to zeta(3)/zeta(2). -/
def alpha : ℝ := inner ℝ qOne (QReciprocalMetric.D qOne)

theorem alpha_weighted_tsum : alpha = ∑' k : ℕ, positiveQWeight k / (k : ℝ) := by
  unfold alpha
  rw [qInner_weighted]
  apply tsum_congr
  intro k
  rw [QReciprocalMetric.qSequence_D, qSequence_qOne]
  cases k with
  | zero => simp [qOneSequence, positiveQWeight]
  | succ n => simp [qOneSequence, div_eq_mul_inv]

/-- The paper's alpha is the actual inverse-cube series divided by zeta(2). -/
theorem alpha_inverseCube_tsum :
    alpha = (∑' k : ℕ, 1 / (k : ℝ) ^ 3) / zetaTwo := by
  rw [alpha_weighted_tsum, ← tsum_div_const]
  apply tsum_congr
  intro k
  unfold positiveQWeight
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul, inv_pow]
  ring

theorem alpha_nonneg : 0 ≤ alpha := by
  unfold alpha
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro n
  change 0 ≤ (qOne n / ((n : ℝ) + 1)) * qOne n
  have he : (qOne n / ((n : ℝ) + 1)) * qOne n =
      (qOne n) ^ 2 / ((n : ℝ) + 1) := by ring
  rw [he]
  positivity

theorem denominator_pos : 0 < 1 + alpha := by linarith [alpha_nonneg]

def c : ℝ := (1 + alpha)⁻¹

theorem c_pos : 0 < c := inv_pos.mpr denominator_pos

def pResidual : QHilbert := c • (qOne + QReciprocalMetric.D qOne)

def displacement : QHilbert := pResidual - qOne

def reciprocalTarget : QHilbert := QShiftedReciprocal.B displacement

/-- The legal Q hyperplane is specified by its actual complete expectation. -/
def meanZero : Submodule ℝ QHilbert where
  carrier := {f | inner ℝ qOne f = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq] at *; rw [inner_add_right, hx, hy]; simp
  smul_mem' := by intro a x hx; simp only [Set.mem_setOf_eq] at *; rw [real_inner_smul_right, hx]; simp

@[simp] theorem mem_meanZero (f : QHilbert) :
    f ∈ meanZero ↔ inner ℝ qOne f = 0 := Iff.rfl

instance meanZero_completeSpace : CompleteSpace meanZero :=
  (show IsClosed (meanZero : Set QHilbert) from
    isClosed_eq (continuous_const.inner continuous_id) continuous_const).completeSpace_coe

instance meanZero_hasOrthogonalProjection : meanZero.HasOrthogonalProjection := by
  infer_instance

theorem pResidual_mean : inner ℝ qOne pResidual = 1 := by
  unfold pResidual c
  rw [real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, qOne_norm_sq]
  change (1 + alpha)⁻¹ * (1 + alpha) = 1
  exact inv_mul_cancel₀ (ne_of_gt denominator_pos)

theorem displacement_mem : displacement ∈ meanZero := by
  rw [mem_meanZero]
  unfold displacement
  rw [inner_sub_right, pResidual_mean, real_inner_self_eq_norm_sq, qOne_norm_sq]
  ring

/-- Exact inverse-metric normal equation, with the reciprocal multiplier R. -/
theorem pResidual_sub_reciprocal :
    pResidual - QShiftedReciprocal.B pResidual = c • qOne := by
  have hd := QReciprocalMetric.D_sub_B_D qOne
  unfold pResidual
  rw [map_smul, map_add]
  rw [← smul_sub]
  congr 1
  rw [← hd]
  abel

/-- The P normal equation is a constant multiple of complete Q expectation. -/
theorem pareto_residual_pairing (f : QHilbert) :
    inner ℝ (toPareto pResidual) (toPareto f) =
      zetaTwo * c * inner ℝ qOne f := by
  rw [QShiftedReciprocal.pareto_inner_identity,
    ← QShiftedReciprocal.B_symmetric, ← inner_sub_left,
    pResidual_sub_reciprocal, real_inner_smul_left]
  ring

/-- The corresponding P hyperplane, represented in the actual Pareto Hilbert space. -/
def paretoMeanZero : Submodule ℝ ThresholdHilbert where
  carrier := {f | inner ℝ (toPareto pResidual) f = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq] at *; rw [inner_add_right, hx, hy]; simp
  smul_mem' := by intro a x hx; simp only [Set.mem_setOf_eq] at *; rw [real_inner_smul_right, hx]; simp

@[simp] theorem mem_paretoMeanZero (f : ThresholdHilbert) :
    f ∈ paretoMeanZero ↔ inner ℝ (toPareto pResidual) f = 0 := Iff.rfl

instance paretoMeanZero_completeSpace : CompleteSpace paretoMeanZero :=
  (show IsClosed (paretoMeanZero : Set ThresholdHilbert) from
    isClosed_eq (continuous_const.inner continuous_id) continuous_const).completeSpace_coe

instance paretoMeanZero_hasOrthogonalProjection : paretoMeanZero.HasOrthogonalProjection := by
  infer_instance

/-- Both hyperplanes contain exactly the same complete physical legal sequences. -/
theorem toPareto_mem_iff (f : QHilbert) :
    toPareto f ∈ paretoMeanZero ↔ f ∈ meanZero := by
  rw [mem_paretoMeanZero, mem_meanZero, pareto_residual_pairing]
  exact mul_eq_zero_iff_left (mul_ne_zero (ne_of_gt zetaTwo_pos) (ne_of_gt c_pos))

/-- The entire P hyperplane is exactly the same complete physical Q legal space. -/
theorem paretoMeanZero_eq_image :
    (paretoMeanZero : Set ThresholdHilbert) = toPareto '' (meanZero : Set QHilbert) := by
  ext p
  constructor
  · intro hp
    refine ⟨QFloorDilation.fromPareto p, ?_, QFloorDilation.toPareto_fromPareto p⟩
    apply (toPareto_mem_iff _).mp
    rw [QFloorDilation.toPareto_fromPareto]
    exact hp
  · rintro ⟨f, hf, rfl⟩
    exact (toPareto_mem_iff f).mpr hf

theorem q_projection : meanZero.starProjection qOne = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (meanZero.zero_mem)
  intro w hw
  simpa only [sub_zero] using (mem_meanZero w).mp hw

theorem p_fit_mem : qOne - pResidual ∈ meanZero := by
  have h := meanZero.neg_mem displacement_mem
  simpa only [displacement, neg_sub] using h

/-- The P fit is the actual orthogonal projection, not an arbitrary trial vector. -/
theorem p_projection :
    paretoMeanZero.starProjection (toPareto qOne) = toPareto (qOne - pResidual) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((toPareto_mem_iff _).mpr p_fit_mem)
  intro w hw
  have he : toPareto qOne - toPareto (qOne - pResidual) = toPareto pResidual := by
    change toParetoLinear qOne - toParetoLinear (qOne - pResidual) = toParetoLinear pResidual
    rw [map_sub]
    abel
  rw [he]
  exact (mem_paretoMeanZero w).mp hw

/-- The explicit d is precisely the difference of the two matched fits. -/
theorem displacement_eq_fit_difference :
    toPareto displacement =
      toPareto (meanZero.starProjection qOne) -
        paretoMeanZero.starProjection (toPareto qOne) := by
  rw [q_projection, p_projection]
  change toParetoLinear (pResidual - qOne) = toParetoLinear 0 - toParetoLinear (qOne - pResidual)
  rw [map_sub, map_sub, map_zero]
  abel

theorem pResidual_physical (k : ℕ) (hk : 0 < k) :
    qSequence pResidual k = c * (1 + 1 / (k : ℝ)) := by
  change qSequenceLinear (c • (qOne + QReciprocalMetric.D qOne)) k = _
  rw [map_smul, map_add]
  change c * (qSequence qOne k + qSequence (QReciprocalMetric.D qOne) k) = _
  rw [QReciprocalMetric.qSequence_D, qSequence_qOne]
  simp [qOneSequence, Nat.ne_of_gt hk]

theorem displacement_physical (k : ℕ) (hk : 0 < k) :
    qSequence displacement k = (1 / (k : ℝ) - alpha) / (1 + alpha) := by
  change qSequenceLinear (pResidual - qOne) k = _
  rw [map_sub]
  change qSequence pResidual k - qSequence qOne k = _
  rw [pResidual_physical k hk, qSequence_qOne]
  simp only [qOneSequence, if_neg (Nat.ne_of_gt hk)]
  unfold c
  field_simp [ne_of_gt denominator_pos]
  ring

theorem displacement_ne_zero : displacement ≠ 0 := by
  intro hd
  have hp : pResidual = qOne := sub_eq_zero.mp hd
  have h1 := congrArg (fun f : QHilbert => qSequence f 1) hp
  have h2 := congrArg (fun f : QHilbert => qSequence f 2) hp
  rw [pResidual_physical 1 (by norm_num), qSequence_qOne] at h1
  rw [pResidual_physical 2 (by norm_num), qSequence_qOne] at h2
  norm_num [qOneSequence] at h1 h2
  linarith

theorem displacement_physical_abs_le (k : ℕ) : |qSequence displacement k| ≤ 1 := by
  cases k with
  | zero => simp
  | succ n =>
    have hk : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hk1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hinv0 : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
    have hinv1 : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hk).mpr hk1
    rw [displacement_physical (n + 1) (by omega), abs_div,
      abs_of_pos denominator_pos]
    apply (div_le_iff₀ denominator_pos).mpr
    rw [one_mul, abs_le]
    constructor <;> linarith [alpha_nonneg]

/-- The actual matched reciprocal target has physical decay O(1/n). -/
theorem reciprocalTarget_physical_decay (k : ℕ) :
    |qSequence reciprocalTarget k| ≤ 1 / ((k : ℝ) + 1) := by
  unfold reciprocalTarget
  rw [QShiftedReciprocal.qSequence_B, abs_div,
    abs_of_pos (by positivity : 0 < (k : ℝ) + 1)]
  exact div_le_div_of_nonneg_right (displacement_physical_abs_le k) (by positivity)

/-- The same matched Pareto-energy identity holds in this nonarithmetic model. -/
theorem matched_energy :
    ‖toPareto displacement‖ ^ 2 = zetaTwo * inner ℝ qOne reciprocalTarget := by
  have hn : inner ℝ (toPareto pResidual) (toPareto displacement) = 0 := by
    rw [pareto_residual_pairing, (mem_meanZero displacement).mp displacement_mem]
    ring
  have hp : toPareto pResidual = toPareto qOne + toPareto displacement := by
    change toParetoLinear pResidual = toParetoLinear qOne + toParetoLinear (pResidual - qOne)
    rw [map_sub]
    abel
  rw [hp, inner_add_left, real_inner_self_eq_norm_sq] at hn
  have hm := QShiftedReciprocal.pareto_inner_identity qOne displacement
  rw [(mem_meanZero displacement).mp displacement_mem] at hm
  change inner ℝ (toPareto qOne) (toPareto displacement) =
    zetaTwo * (0 - inner ℝ qOne reciprocalTarget) at hm
  linarith

theorem pareto_displacement_ne_zero : toPareto displacement ≠ 0 := by
  intro h
  apply displacement_ne_zero
  apply qSequence_injective
  have hs := congrArg hilbertSequence h
  rw [toPareto_sequence] at hs
  have hz : hilbertSequence (0 : ThresholdHilbert) = qSequence (0 : QHilbert) := by
    change hilbertSequenceLinear 0 = qSequenceLinear 0
    simp only [map_zero]
  exact hs.trans hz

theorem target_mean_pos : 0 < inner ℝ qOne reciprocalTarget := by
  have hn := norm_pos_iff.mpr pareto_displacement_ne_zero
  have he := matched_energy
  have hz := zetaTwo_pos
  nlinarith [sq_pos_of_pos hn]

/-- The signed obstruction is strictly positive for an explicitly matched d. -/
theorem target_mean_formula : inner ℝ qOne reciprocalTarget = 1 / zetaTwo - c := by
  have hp := pareto_residual_pairing qOne
  have hm := QShiftedReciprocal.pareto_inner_identity pResidual qOne
  rw [← real_inner_comm pResidual qOne, pResidual_mean] at hm
  have hi := QShiftedReciprocal.pareto_inner_identity qOne qOne
  rw [toPareto_qOne, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
    real_inner_self_eq_norm_sq, qOne_norm_sq] at hi
  have ht : inner ℝ qOne reciprocalTarget =
      inner ℝ pResidual (QShiftedReciprocal.B qOne) -
        inner ℝ qOne (QShiftedReciprocal.B qOne) := by
    unfold reciprocalTarget displacement
    rw [map_sub, inner_sub_right, ← QShiftedReciprocal.B_symmetric, real_inner_comm]
  rw [real_inner_self_eq_norm_sq, qOne_norm_sq] at hp
  rw [ht]
  apply (eq_sub_iff_add_eq).mpr
  apply (eq_div_iff (ne_of_gt zetaTwo_pos)).mpr
  nlinarith

end RiemannResearch.RH.QHyperplaneCountermodel
