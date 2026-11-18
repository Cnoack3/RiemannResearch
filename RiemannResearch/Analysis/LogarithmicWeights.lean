import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Logarithmic weights for divergent series

The finite identity below gives the logarithmic case of Abel's and Dini's
series comparison. See K. Knopp, *Theory and Application of Infinite Series*,
§39, Theorem 173. The RH application uses nonnegative terms with possible
zeros and a unit offset to include empty prefixes.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.Analysis.LogarithmicWeights

/-- Sum strictly before index `N`. -/
def prefixMass (w : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, w n

/-- Increment of the logarithm of one plus the cumulative mass. -/
def logWeight (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (1 + prefixMass w (n + 1)) - Real.log (1 + prefixMass w n)

@[simp] theorem prefixMass_zero (w : ℕ → ℝ) : prefixMass w 0 = 0 := by simp [prefixMass]

@[simp] theorem prefixMass_succ (w : ℕ → ℝ) (n : ℕ) :
    prefixMass w (n + 1) = prefixMass w n + w n := Finset.sum_range_succ _ _

theorem prefixMass_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (N : ℕ) :
    0 ≤ prefixMass w N := Finset.sum_nonneg (fun n _ => hw n)

theorem logWeight_sum (w : ℕ → ℝ) (N : ℕ) :
    prefixMass (logWeight w) N = Real.log (1 + prefixMass w N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [prefixMass_succ, ih, logWeight]
    ring

theorem logWeight_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (n : ℕ) :
    0 ≤ logWeight w n := by
  rw [logWeight, sub_nonneg, prefixMass_succ]
  apply Real.log_le_log (by linarith [prefixMass_nonneg hw n])
  linarith [hw n]

theorem logWeight_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (n : ℕ) :
    logWeight w n ≤ w n / (1 + prefixMass w n) := by
  have ha : 0 < 1 + prefixMass w n := by linarith [prefixMass_nonneg hw n]
  have hb : 0 < 1 + prefixMass w (n + 1) := by linarith [prefixMass_nonneg hw (n+1)]
  rw [logWeight, ← Real.log_div hb.ne' ha.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hb ha)).trans_eq ?_
  rw [prefixMass_succ]
  field_simp
  <;> ring

theorem not_summable_logWeight {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (hd : ¬ Summable w) :
    ¬ Summable (logWeight w) := by
  have h : Tendsto (prefixMass w) atTop atTop := by
    by_contra hn
    exact hd ((summable_iff_not_tendsto_nat_atTop_of_nonneg hw).mpr hn)
  have hl := Real.tendsto_log_atTop.comp (tendsto_atTop_mono
    (show ∀ n, prefixMass w n ≤ 1 + prefixMass w n by intro n; linarith) h)
  intro hs
  apply (summable_iff_not_tendsto_nat_atTop_of_nonneg (logWeight_nonneg hw)).mp hs
  change Tendsto (prefixMass (logWeight w)) atTop atTop
  rw [show prefixMass (logWeight w) = (fun n => Real.log (1 + prefixMass w n)) from
    funext (logWeight_sum w)]
  exact hl

/-- Each iteration replaces cumulative mass `x` by `log (1+x)`. -/
def iteratedLogWeight : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, w => w
  | k + 1, w => logWeight (iteratedLogWeight k w)

theorem iteratedLogWeight_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (k : ℕ) :
    ∀ n, 0 ≤ iteratedLogWeight k w n := by
  induction k with
  | zero => exact hw
  | succ k ih => exact logWeight_nonneg ih

theorem iteratedLogWeight_sum (w : ℕ → ℝ) (k N : ℕ) :
    prefixMass (iteratedLogWeight k w) N =
      (fun x : ℝ => Real.log (1 + x))^[k] (prefixMass w N) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iteratedLogWeight, logWeight_sum, ih, Function.iterate_succ_apply']

theorem not_summable_iteratedLogWeight {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hd : ¬ Summable w) (k : ℕ) : ¬ Summable (iteratedLogWeight k w) := by
  induction k with
  | zero => exact hd
  | succ k ih => exact not_summable_logWeight (iteratedLogWeight_nonneg hw k) ih

end RiemannResearch.Analysis.LogarithmicWeights
