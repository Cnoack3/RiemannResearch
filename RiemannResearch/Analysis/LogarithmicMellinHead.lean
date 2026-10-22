import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite logarithmic head control, using only compact-interval calculus. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.Analysis

private def logHead (t x : ℝ) : ℝ := (Real.log t - Real.log x) ^ 2
private def logHeadPrimitive (t x : ℝ) : ℝ :=
  x * ((Real.log t - Real.log x) ^ 2 + 2 * (Real.log t - Real.log x) + 2)

private theorem logHeadPrimitive_deriv (t x : ℝ) (hx : 0 < x) :
    HasDerivAt (logHeadPrimitive t) (logHead t x) x := by
  have hl := (hasDerivAt_const x (Real.log t)).sub (Real.hasDerivAt_log (ne_of_gt hx))
  have hd := (hasDerivAt_id x).mul (((hl.pow 2).add (hl.const_mul 2)).add_const 2)
  convert! hd using 1 <;>
    simp only [logHeadPrimitive, logHead, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply, id_eq] <;>
    field_simp [ne_of_gt hx] <;> ring

private theorem logHead_continuous (t : ℝ) : ContinuousOn (logHead t) (Icc 1 t) := by
  apply (continuousOn_const.sub (continuousOn_id.log ?_)).pow 2
  intro x hx
  exact ne_of_gt (zero_lt_one.trans_le hx.1)

private theorem logHead_integral (t : ℝ) (ht : 1 ≤ t) :
    (∫ x in (1 : ℝ)..t, logHead t x) =
      2 * t - (Real.log t ^ 2 + 2 * Real.log t + 2) := by
  have hi : IntervalIntegrable (logHead t) volume 1 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht (logHead_continuous t)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := logHeadPrimitive t) (f' := logHead t)
    (fun x hx => logHeadPrimitive_deriv t x (by
      rw [uIcc_of_le ht] at hx
      exact zero_lt_one.trans_le hx.1)) hi
  convert! h using 1 <;> simp [logHeadPrimitive] <;> ring

private theorem logHead_antitone (t : ℝ) : AntitoneOn (logHead t) (Icc 1 t) := by
  intro x hx y hy hxy
  have hx0 := zero_lt_one.trans_le hx.1
  have hy0 := zero_lt_one.trans_le hy.1
  have hxylog := Real.log_le_log hx0 hxy
  have hxt := Real.log_le_log hx0 hx.2
  have hyt := Real.log_le_log hy0 hy.2
  exact (sq_le_sq₀ (sub_nonneg.mpr hyt) (sub_nonneg.mpr hxt)).mpr (by linarith)

private theorem sum_logHead_le (t : ℝ) (ht : 1 ≤ t) (N : ℕ) (hN : (N : ℝ) ≤ t) :
    (∑ i ∈ Finset.range N, logHead t ((i : ℝ) + 1)) ≤ 2 * t := by
  cases N with
  | zero => simp; linarith
  | succ m =>
    have hm : 1 + (m : ℝ) ≤ t := by simpa [Nat.cast_add, Nat.cast_one, add_comm] using hN
    have hmono : AntitoneOn (logHead t) (Icc (1 : ℝ) (1 + (m : ℝ))) :=
      (logHead_antitone t).mono (Icc_subset_Icc le_rfl hm)
    have hs := AntitoneOn.sum_le_integral (x₀ := (1 : ℝ)) (a := m) hmono
    have hi := intervalIntegral.integral_mono_interval
      (a := (1 : ℝ)) (b := 1 + (m : ℝ)) (c := (1 : ℝ)) (d := t)
      (μ := volume) (f := logHead t) le_rfl
      (by nlinarith [Nat.cast_nonneg (α := ℝ) m]) hm
      (Filter.Eventually.of_forall (fun x => sq_nonneg (Real.log t - Real.log x)))
      (ContinuousOn.intervalIntegrable_of_Icc ht (logHead_continuous t))
    have he : (∑ i ∈ Finset.range (m + 1), logHead t ((i : ℝ) + 1)) =
        (∑ i ∈ Finset.range m, logHead t (1 + ((i + 1 : ℕ) : ℝ))) + logHead t 1 := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      push_cast
      ring
    rw [he]
    rw [logHead_integral t ht] at hi
    have hl : 0 ≤ Real.log t := Real.log_nonneg ht
    have hone : logHead t 1 = Real.log t ^ 2 := by simp [logHead]
    rw [hone]
    nlinarith

/-- The exact finite head estimate required for the centered cell derivative. -/
theorem logSquare_head_sum_le (t : ℝ) (ht : 1 ≤ t) (N : ℕ) (hN : (N : ℝ) ≤ t) :
    (∑ i ∈ Finset.range N, Real.log (t / ((i : ℝ) + 1)) ^ 2) ≤ 2 * t := by
  have ht0 := zero_lt_one.trans_le ht
  have he : (∑ i ∈ Finset.range N, Real.log (t / ((i : ℝ) + 1)) ^ 2) =
      ∑ i ∈ Finset.range N, logHead t ((i : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.log_div (ne_of_gt ht0) (by positivity)]
    rfl
  rw [he]
  exact sum_logHead_le t ht N hN

end RiemannResearch.Analysis
