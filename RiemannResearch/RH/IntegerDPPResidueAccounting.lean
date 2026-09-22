import RiemannResearch.RH.IntegerDPPResidueSmallValues
import RiemannResearch.RH.ParetoCRTWeightLimits
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Direct gain and loss accounting for the residue-class DPP recurrence

Source: user-provided request, September 2026, for an analytic recurrence
argument starting from q_1 = 1. The kernel-increment formula uses the actual
finite DPP; the limit proof uses only summable nonnegative entry/loss terms.

All sums in the budget statements start with transition N=1 to N=2.
Both total entry and total loss are bounded by log(2 * log 2).
The exact limit is one plus total entry minus total loss. Equality of those
totals is not proved. The retention-only comparison sequence shows that the
initial value, retention factors, and sign/budget bounds alone are insufficient;
it is not identified with the arithmetic DPP.
-/

open Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization CoefficientStabilization.TailCapacity

def firstClassWeight (n : ℕ) : ℝ := progressionWeight (residueModulus n) 1
def classRetention (n : ℕ) : ℝ := firstClassWeight (n+1) / firstClassWeight n
def classEntry (n : ℕ) : ℝ :=
  firstClassWeight (n+1) * (anchoredEvaluationCLM 1 (residueMode n))^2
def classLoss (n : ℕ) : ℝ := (1 - classRetention n) * qN n

theorem firstClassWeight_pos (n : ℕ) : 0 < firstClassWeight n :=
  progressionWeight_pos _ _ (residueModulus_pos n) (by omega)

theorem firstClassWeight_ge_half (n : ℕ) : (1/2 : ℝ) ≤ firstClassWeight n := by
  have h := progressionWeight_split (residueModulus n) 1 (residueModulus_pos n)
  have hp := progressionWeight_nonneg (residueModulus n) (1 + residueModulus n)
  norm_num [positiveWeight] at h
  change (1/2 : ℝ) ≤ progressionWeight (residueModulus n) 1
  linarith

theorem firstClassWeight_one : firstClassWeight 1 = Real.log 2 := by
  norm_num [firstClassWeight, residueModulus, progressionWeight_two_one]

theorem firstClassWeight_next_le (n : ℕ) :
    firstClassWeight (n+1) ≤ firstClassWeight n := by
  have hm : residueModulus n ≤ residueModulus (n+1) :=
    Nat.le_lcm_left _ (by omega)
  apply Summable.tsum_le_tsum _ (progressionWeight_summable _ _ (residueModulus_pos _))
    (progressionWeight_summable _ _ (residueModulus_pos _))
  intro j
  exact positiveWeight_strictAntiOn.antitoneOn (by simp) (by simp)
    (Nat.add_le_add_left (Nat.mul_le_mul_right j hm) 1)

theorem classRetention_pos (n : ℕ) : 0 < classRetention n :=
  div_pos (firstClassWeight_pos _) (firstClassWeight_pos _)

theorem classRetention_le_one (n : ℕ) : classRetention n ≤ 1 :=
  (div_le_one (firstClassWeight_pos n)).mpr (firstClassWeight_next_le n)

theorem classEntry_nonneg (n : ℕ) : 0 ≤ classEntry n :=
  mul_nonneg (firstClassWeight_pos _).le (sq_nonneg _)

theorem qN_nonneg (n : ℕ) : 0 ≤ qN n := by
  exact measureReal_nonneg

theorem qN_le_one (n : ℕ) : qN n ≤ 1 := by
  exact measureReal_le_one

theorem classLoss_nonneg (n : ℕ) : 0 ≤ classLoss n :=
  mul_nonneg (sub_nonneg.mpr (classRetention_le_one n)) (qN_nonneg n)

theorem qN_succ_entry_loss (n : ℕ) :
    qN (n+1) = qN n + classEntry n - classLoss n := by
  have h := qN_succ n
  change qN (n+1) = classRetention n * qN n + classEntry n at h
  rw [h, classLoss]
  ring


theorem qN_eq_weighted_first_kernel (n : ℕ) :
    qN n = 2 * firstClassWeight n * integerKernel n 0 0 := by
  have hv := vacancy_eq_fullCapacity n
  rw [vacancy_eq_kernel_complement] at hv
  have he : fullCapacity n = 2 * integerKernel n 0 0 := by linarith
  rw [qN_eq_fullCapacity, he]
  change firstClassWeight n * (2 * integerKernel n 0 0) = _
  ring

/-- DPP insertion term, expressed without orthonormal coordinates. -/
theorem classEntry_eq_kernel_increment (n : ℕ) :
    classEntry n = 2 * firstClassWeight (n+1) *
      (integerKernel (n+1) 0 0 - integerKernel n 0 0) := by
  have hs := qN_succ n
  change qN (n+1) = classRetention n * qN n + classEntry n at hs
  rw [qN_eq_weighted_first_kernel, qN_eq_weighted_first_kernel] at hs
  have hr : classRetention n * (2 * firstClassWeight n * integerKernel n 0 0) =
      2 * firstClassWeight (n+1) * integerKernel n 0 0 := by
    unfold classRetention
    field_simp [ne_of_gt (firstClassWeight_pos n)]
  rw [hr] at hs
  nlinarith only [hs]

theorem qN_succ_retention (n : ℕ) :
    qN (n+1) = classRetention n * qN n + classEntry n :=
  qN_succ n

theorem classLoss_le_log_drop (n : ℕ) :
    classLoss n ≤ Real.log (firstClassWeight n) -
      Real.log (firstClassWeight (n+1)) := by
  have h₁ : classLoss n ≤ 1 - classRetention n := by
    unfold classLoss
    exact mul_le_of_le_one_right (sub_nonneg.mpr (classRetention_le_one n)) (qN_le_one n)
  have h₂ := Real.log_le_sub_one_of_pos (classRetention_pos n)
  have hlog : Real.log (classRetention n) =
      Real.log (firstClassWeight (n+1)) - Real.log (firstClassWeight n) :=
    Real.log_div (ne_of_gt (firstClassWeight_pos _)) (ne_of_gt (firstClassWeight_pos _))
  linarith

theorem qN_entry_loss_telescope (m : ℕ) :
    qN (m+1) = 1 + (∑ n ∈ Finset.range m, classEntry (n+1)) -
      ∑ n ∈ Finset.range m, classLoss (n+1) := by
  induction m with
  | zero => simpa using qN_one
  | succ m ih =>
    rw [qN_succ_entry_loss, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

theorem entry_sum_le_loss_sum (m : ℕ) :
    (∑ n ∈ Finset.range m, classEntry (n+1)) ≤
      ∑ n ∈ Finset.range m, classLoss (n+1) := by
  have h := qN_entry_loss_telescope m
  have hb := qN_le_one (m+1)
  linarith

theorem loss_sum_le_log_drop (m : ℕ) :
    (∑ n ∈ Finset.range m, classLoss (n+1)) ≤
      Real.log (Real.log 2) - Real.log (firstClassWeight (m+1)) := by
  induction m with
  | zero => simp [firstClassWeight_one]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h := classLoss_le_log_drop (m+1)
    linarith


theorem class_log_two_pos : 0 < Real.log 2 := by
  simpa only [firstClassWeight_one] using firstClassWeight_pos 1

theorem class_log_two_lt_one : Real.log 2 < 1 := by
  have h := progressionWeight_pos 2 2 (by omega) (by omega)
  rw [progressionWeight_two_two] at h
  linarith

theorem loss_sum_le_log_budget (m : ℕ) :
    (∑ n ∈ Finset.range m, classLoss (n+1)) ≤ Real.log (2 * Real.log 2) := by
  have h := loss_sum_le_log_drop m
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2)
    (firstClassWeight_ge_half (m+1))
  have he : Real.log (Real.log 2) - Real.log (1/2 : ℝ) =
      Real.log (2 * Real.log 2) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one, Real.log_mul (by norm_num) (ne_of_gt class_log_two_pos)]
    ring
  rw [← he]
  linarith

theorem log_budget_lt_log_two : Real.log (2 * Real.log 2) < Real.log 2 := by
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt class_log_two_pos)]
  have h := Real.log_neg class_log_two_pos class_log_two_lt_one
  linarith

theorem entry_sum_le_log_budget (m : ℕ) :
    (∑ n ∈ Finset.range m, classEntry (n+1)) ≤ Real.log (2 * Real.log 2) :=
  (entry_sum_le_loss_sum m).trans (loss_sum_le_log_budget m)

theorem classEntry_summable : Summable (fun n => classEntry (n+1)) :=
  summable_of_sum_range_le (fun n => classEntry_nonneg (n+1)) entry_sum_le_log_budget

theorem classLoss_summable : Summable (fun n => classLoss (n+1)) :=
  summable_of_sum_range_le (fun n => classLoss_nonneg (n+1)) loss_sum_le_log_budget

theorem qN_tendsto_entry_loss :
    Tendsto qN atTop
      (𝓝 (1 + (∑' n, classEntry (n+1)) - ∑' n, classLoss (n+1))) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add
    classEntry_summable.hasSum.tendsto_sum_nat).sub
      classLoss_summable.hasSum.tendsto_sum_nat
  simpa only [← qN_entry_loss_telescope] using h

theorem qN_liminf_eq_entry_loss :
    Filter.liminf qN atTop =
      1 + (∑' n, classEntry (n+1)) - ∑' n, classLoss (n+1) :=
  qN_tendsto_entry_loss.liminf_eq

theorem qN_liminf_eq_one_iff_entry_eq_loss :
    Filter.liminf qN atTop = 1 ↔
      (∑' n, classEntry (n+1)) = ∑' n, classLoss (n+1) := by
  rw [qN_liminf_eq_entry_loss]
  constructor <;> intro h <;> linarith

theorem entry_tsum_le_loss_tsum :
    (∑' n, classEntry (n+1)) ≤ ∑' n, classLoss (n+1) := by
  exact le_of_tendsto_of_tendsto classEntry_summable.hasSum.tendsto_sum_nat
    classLoss_summable.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall entry_sum_le_loss_sum)

theorem loss_tsum_le_log_budget :
    (∑' n, classLoss (n+1)) ≤ Real.log (2 * Real.log 2) :=
  classLoss_summable.tsum_le_of_sum_range_le loss_sum_le_log_budget

/-- The scalar recurrence with zero insertion does not force saturation. -/
def retentionOnly (n : ℕ) : ℝ := firstClassWeight (n+1) / Real.log 2

theorem retentionOnly_zero : retentionOnly 0 = 1 := by
  simp [retentionOnly, firstClassWeight_one, ne_of_gt class_log_two_pos]

theorem retentionOnly_succ (n : ℕ) :
    retentionOnly (n+1) = classRetention (n+1) * retentionOnly n := by
  unfold retentionOnly classRetention
  field_simp [ne_of_gt (firstClassWeight_pos (n+1))]

theorem retentionOnly_pos (n : ℕ) : 0 < retentionOnly n :=
  div_pos (firstClassWeight_pos _) class_log_two_pos

theorem retentionOnly_le_one (n : ℕ) : retentionOnly n ≤ 1 := by
  apply (div_le_one class_log_two_pos).mpr
  have ha : Antitone firstClassWeight := antitone_nat_of_succ_le firstClassWeight_next_le
  simpa only [firstClassWeight_one] using ha (by omega : 1 ≤ n+1)

theorem firstClassWeight_tendsto_half :
    Tendsto firstClassWeight atTop (𝓝 (1/2 : ℝ)) := by
  change Tendsto (fun n => progressionWeight (residueModulus n) 1) atTop (𝓝 (1/2 : ℝ))
  have hm (n : ℕ) : n+1 ≤ residueModulus n := by
    cases n with
    | zero => norm_num [residueModulus]
    | succ n => exact Nat.le_lcm_right (n+2) (residueModulus_pos n)
  have hp : Tendsto (fun n => residueModulus n - 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; have := hm n; omega) tendsto_id
  have he (n : ℕ) : residueModulus n - 1 + 1 = residueModulus n :=
    Nat.sub_add_cancel (residueModulus_pos n)
  simpa only [firstClassWeight, Function.comp_def, he, positiveWeight, Nat.cast_one,
    one_add_one_eq_two, one_mul] using (progressionWeight_tendsto_atom 1).comp hp

theorem retentionOnly_tendsto :
    Tendsto retentionOnly atTop (𝓝 (1 / (2 * Real.log 2))) := by
  change Tendsto (fun n => firstClassWeight (n+1) / Real.log 2) atTop
    (𝓝 (1 / (2 * Real.log 2)))
  have hw := (tendsto_add_atTop_iff_nat 1).mpr firstClassWeight_tendsto_half
  have ht := hw.div_const (Real.log 2)
  simpa only [retentionOnly, div_div] using ht

theorem retentionOnly_limit_lt_one : 1 / (2 * Real.log 2) < 1 := by
  have h := progressionWeight_split 2 1 (by omega)
  rw [progressionWeight_two_one] at h
  norm_num [positiveWeight] at h
  have hp := progressionWeight_pos 2 3 (by omega) (by omega)
  apply (div_lt_one (mul_pos (by norm_num) class_log_two_pos)).mpr
  linarith

theorem retentionOnly_liminf_lt_one : Filter.liminf retentionOnly atTop < 1 := by
  rw [retentionOnly_tendsto.liminf_eq]
  exact retentionOnly_limit_lt_one


end RiemannResearch.RH.Pareto.IntegerDPP
