import RiemannResearch.RH.ParetoProgressionDigamma
import RiemannResearch.RH.ParetoZetaSeries
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Actual digamma Laurent expansion with a positive exact remainder

The function used throughout is the real part of `Complex.digamma`, the
logarithmic derivative of the actual Gamma function.  The coefficient series
and the remainder are convergent arithmetic sums.  There is no assumed
digamma expansion or asymptotic provider in these statements.

The first three regular coefficients give a rigorous small-positive-argument
expansion with a global remainder bound.  The expansion is particularly useful
for the CRT weights, whose arguments tend to zero at every fixed residue.
The standard coefficient formula is recorded in NIST DLMF 5.7.4
(https://dlmf.nist.gov/5.7.E4); the proof here derives it from the proved
Gamma logarithmic-derivative partial-fraction series.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto.DigammaSmallArgument

noncomputable section

def remainderTerm (z : ℝ) (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) ^ 4 * ((n : ℝ) + 1 + z))

def smallRemainder (z : ℝ) : ℝ := ∑' n : ℕ, remainderTerm z n

theorem remainderTerm_pos {z : ℝ} (hz : 0 < z) (n : ℕ) :
    0 < remainderTerm z n := by unfold remainderTerm; positivity

theorem remainderTerm_le {z : ℝ} (hz : 0 < z) (n : ℕ) :
    remainderTerm z n ≤ 1 / (((n : ℝ) + 1) ^ 5) := by
  unfold remainderTerm
  apply one_div_le_one_div_of_le (by positivity)
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem summable_remainderTerm {z : ℝ} (hz : 0 < z) :
    Summable (remainderTerm z) := by
  exact (positivePSeries_summable 5 (by norm_num)).of_nonneg_of_le
    (fun n => (remainderTerm_pos hz n).le) (remainderTerm_le hz)

theorem smallRemainder_pos {z : ℝ} (hz : 0 < z) : 0 < smallRemainder z := by
  exact (summable_remainderTerm hz).tsum_pos
    (fun n => (remainderTerm_pos hz n).le) 0 (remainderTerm_pos hz 0)

theorem smallRemainder_le {z : ℝ} (hz : 0 < z) :
    smallRemainder z ≤ positivePSeries 5 := by
  exact Summable.tsum_le_tsum (remainderTerm_le hz) (summable_remainderTerm hz)
    (positivePSeries_summable 5 (by norm_num))

theorem reciprocal_difference_three_terms {z : ℝ} (hz : 0 < z) (n : ℕ) :
    1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + z) =
      z * (1 / ((n : ℝ) + 1) ^ 2) -
      z ^ 2 * (1 / ((n : ℝ) + 1) ^ 3) +
      z ^ 3 * (1 / ((n : ℝ) + 1) ^ 4) - z ^ 4 * remainderTerm z n := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 1 + z ≠ 0 := by positivity
  unfold remainderTerm
  field_simp
  ring

/-- Exact Laurent truncation of the Gamma logarithmic derivative.
The remaining coefficient is a positive, convergent sum. -/
theorem digamma_three_terms_exact {z : ℝ} (hz : 0 < z) :
    (Complex.digamma (z : ℂ)).re =
      -Real.eulerMascheroniConstant - 1 / z +
      z * positivePSeries 2 - z ^ 2 * positivePSeries 3 +
      z ^ 3 * positivePSeries 4 - z ^ 4 * smallRemainder z := by
  have hs := (hasSum_reciprocal_difference_positive
    (show 0 < z + 1 by positivity)).neg
  have hd := re_digamma_add_one hz
  have ht := (((positivePSeries_summable 2 (by norm_num)).hasSum.mul_left z).sub
    ((positivePSeries_summable 3 (by norm_num)).hasSum.mul_left (z ^ 2))).add
      ((positivePSeries_summable 4 (by norm_num)).hasSum.mul_left (z ^ 3))
  have hsum := ht.sub ((summable_remainderTerm hz).hasSum.mul_left (z ^ 4))
  have he : (fun n : ℕ =>
      z * (1 / ((n : ℝ) + 1) ^ 2) - z ^ 2 * (1 / ((n : ℝ) + 1) ^ 3) +
      z ^ 3 * (1 / ((n : ℝ) + 1) ^ 4) - z ^ 4 * remainderTerm z n) =
      (fun n : ℕ => -(1 / ((n : ℝ) + (z + 1)) - 1 / ((n : ℝ) + 1))) := by
    funext n
    rw [← reciprocal_difference_three_terms hz]
    ring
  rw [he] at hsum
  have hv := hsum.unique hs
  change z * positivePSeries 2 - z ^ 2 * positivePSeries 3 +
    z ^ 3 * positivePSeries 4 - z ^ 4 * smallRemainder z =
    -(-(Complex.digamma ((z + 1 : ℝ) : ℂ)).re - Real.eulerMascheroniConstant) at hv
  linarith

/-- A rigorous coefficient-level remainder bound, without a big-O assertion. -/
theorem digamma_three_terms_error {z : ℝ} (hz : 0 < z) :
    0 ≤ (-Real.eulerMascheroniConstant - 1 / z +
      z * positivePSeries 2 - z ^ 2 * positivePSeries 3 +
      z ^ 3 * positivePSeries 4) - (Complex.digamma (z : ℂ)).re ∧
    (-Real.eulerMascheroniConstant - 1 / z +
      z * positivePSeries 2 - z ^ 2 * positivePSeries 3 +
      z ^ 3 * positivePSeries 4) - (Complex.digamma (z : ℂ)).re ≤
        z ^ 4 * positivePSeries 5 := by
  rw [digamma_three_terms_exact hz]
  have he : (-Real.eulerMascheroniConstant - 1 / z +
      z * positivePSeries 2 - z ^ 2 * positivePSeries 3 +
      z ^ 3 * positivePSeries 4) -
      (-Real.eulerMascheroniConstant - 1 / z +
      z * positivePSeries 2 - z ^ 2 * positivePSeries 3 +
      z ^ 3 * positivePSeries 4 - z ^ 4 * smallRemainder z) =
      z ^ 4 * smallRemainder z := by ring
  rw [he]
  exact ⟨mul_nonneg (by positivity) (smallRemainder_pos hz).le,
    mul_le_mul_of_nonneg_left (smallRemainder_le hz) (by positivity)⟩

/-- The same signed fourth-order expansion, stated for the actual digamma
increment rather than for an independently named weight.  Its arithmetic
remainder is the literal progression remainder. -/
theorem digamma_crt_increment_fourth (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hrQ : r ≤ Q) :
    1 / (Q : ℝ) *
      ((Complex.digamma (((r + 1 : ℝ) / Q : ℝ) : ℂ)).re -
       (Complex.digamma (((r : ℝ) / Q : ℝ) : ℂ)).re) =
      positiveWeight r + Real.pi ^ 2 / (6 * (Q : ℝ) ^ 2) -
      (2 * (r : ℝ) + 1) * positivePSeries 3 / (Q : ℝ) ^ 3 +
      (3 * (r : ℝ) ^ 2 + 3 * r + 1) * Real.pi ^ 4 / (90 * (Q : ℝ) ^ 4) -
      progressionTaylorSecondRemainder Q r ∧
    0 < progressionTaylorSecondRemainder Q r ∧
    progressionTaylorSecondRemainder Q r ≤
      (4 * (r : ℝ) ^ 3 + 6 * r ^ 2 + 4 * r + 1) *
        positivePSeries 5 / (Q : ℝ) ^ 5 := by
  rw [← progressionWeight_eq_digamma Q r hQ hr hrQ]
  exact progressionWeight_signed_taylor_fourth Q r hQ

end
end RiemannResearch.RH.Pareto.DigammaSmallArgument
